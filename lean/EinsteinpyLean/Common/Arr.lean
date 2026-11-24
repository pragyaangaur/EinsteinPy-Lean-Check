/-!
# Dense rational arrays, mirroring `sympy.Array`

einsteinpy stores every tensor as a `sympy.Array` and manipulates it with three
sympy functions: `tensorproduct`, `tensorcontraction` and `permutedims`. This file
mirrors those three on dense row-major arrays of exact rationals, which is all the
difftests need once every symbol has been replaced by a rational number.

This file uses only core Lean, so the `epdiff` executable does not link Mathlib.
-/

namespace EinsteinpyLean

/-- A dense array of rationals in row-major (C) order, like `sympy.Array`. -/
structure Arr where
  shape : List Nat
  data : Array Rat
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Arr

/-- Number of entries implied by a shape. The empty shape is a scalar with one entry. -/
def size (shape : List Nat) : Nat := shape.foldl (· * ·) 1

/-- Row-major strides of a shape. -/
def strides : List Nat → List Nat
  | [] => []
  | _ :: rest => size rest :: strides rest

/-- Flat offset of a multi-index. -/
def offset (shape : List Nat) (idx : List Nat) : Nat :=
  (List.zipWith (· * ·) (strides shape) idx).foldl (· + ·) 0

/-- Multi-index of a flat offset. -/
def unflatten (shape : List Nat) (k : Nat) : List Nat :=
  (strides shape).zip shape |>.map fun (s, n) => (k / s) % n

def get (a : Arr) (idx : List Nat) : Rat := a.data.getD (offset a.shape idx) 0

def ofFn (shape : List Nat) (f : List Nat → Rat) : Arr :=
  ⟨shape, (Array.range (size shape)).map fun k => f (unflatten shape k)⟩

def rank (a : Arr) : Nat := a.shape.length

/-- `sympy.tensorproduct(a, b)`: shape `a.shape ++ b.shape`. -/
def tensorproduct (a b : Arr) : Arr :=
  ofFn (a.shape ++ b.shape) fun idx =>
    a.get (idx.take a.rank) * b.get (idx.drop a.rank)

/-- Insert `x` at position `i` of a list. -/
def insertAt (l : List Nat) (i : Nat) (x : Nat) : List Nat := l.take i ++ x :: l.drop i

/-- Python's error classes, as far as the mirrored sympy code raises them. -/
inductive PyErr where
  | indexError
  | valueError
  deriving Repr, BEq, DecidableEq

/-- Python `seq[k]` for a possibly negative `k`. -/
def pyGet (l : List Nat) (k : Int) : Except PyErr Nat :=
  let n : Int := l.length
  let k' := if k < 0 then k + n else k
  if 0 ≤ k' ∧ k' < n then .ok l[k'.toNat]! else .error .indexError

/-- `sympy.tensorcontraction(a, (p, q))`, mirrored from
`sympy/tensor/array/arrayop.py` (`_util_contraction_diagonal` and `tensorcontraction`,
sympy 1.14.0) including what it does with negative axes. sympy never normalises a
negative axis: the dimension check reads `shape[d]` with Python indexing, the set of
taken axes holds the raw integers, so a negative axis is never removed from the
result, and the summation stride is read as `cum_shape[d]`, again with Python
indexing. Flat positions past the end wrap, because `_get_tuple_index` reduces each
digit modulo the shape. The result is a scalar when no axis remains. -/
def tensorcontraction (a : Arr) (p q : Int) : Except PyErr Arr := do
  let dim ← pyGet a.shape p
  -- the loop over the group `(p, q)`
  let dp ← pyGet a.shape p
  if dim != dp then throw .valueError
  if q == p then throw .valueError
  let dq ← pyGet a.shape q
  if dim != dq then throw .valueError
  let r := a.rank
  let cum := strides a.shape
  let remaining : List Nat := (List.range r).filter fun (i : Nat) => (i : Int) != p && (i : Int) != q
  let remShape := remaining.map fun (i : Nat) => a.shape[i]!
  let sp ← pyGet cum p
  let sq ← pyGet cum q
  let total := size a.shape
  let at_ (pos : Nat) : Rat := if total = 0 then 0 else a.data.getD (pos % total) 0
  return ofFn remShape fun idx =>
    let base := (List.zipWith (fun (i j : Nat) => cum[i]! * j) remaining idx).foldl (· + ·) 0
    (List.range dim).foldl (init := 0) fun acc js => acc + at_ (base + (sp + sq) * js)

/-- `sympy.permutedims(a, dest)`: output axis `k` is input axis `dest[k]`.
(sympy's convention: `permutedims(A, perm)[i_0..] = A[i_{perm^-1(0)}..]`.) -/
def permutedims (a : Arr) (perm : List Nat) : Arr :=
  -- sympy: new shape[k] = old shape[perm[k]] and new[idx] = old[idx'] with idx'[perm[k]] = idx[k]
  let newShape := perm.map fun k => a.shape[k]!
  ofFn newShape fun idx =>
    let old := (List.range a.rank).map fun j =>
      match perm.idxOf? j with
      | some k => idx[k]!
      | none => 0
    a.get old

/-- Exact rational rendering used on both sides of every difftest. -/
def ratStr (q : Rat) : String :=
  if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

def render (a : Arr) : String :=
  s!"{a.shape} " ++ " ".intercalate (a.data.toList.map ratStr)

/-- Parse `3/4`, `-2` and the like. -/
def parseRat (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [n] => (n.toInt?).map (fun i => (i : Rat))
  | [n, d] => do
      let n ← n.toInt?
      let d ← d.toNat?
      if d = 0 then none else some ((n : Rat) / (d : Rat))
  | _ => none

/-- Square matrix inverse by Gauss-Jordan elimination over ℚ (none when singular),
standing in for `sympy.Matrix.inv`. Exact arithmetic makes the method irrelevant:
an inverse is unique. -/
def matInv (m : Arr) : Option Arr := Id.run do
  let n := m.shape.headD 0
  if m.shape != [n, n] then return none
  let mut a : Array (Array Rat) := (Array.range n).map fun i =>
    ((Array.range n).map fun j => m.get [i, j]) ++
    ((Array.range n).map fun j => if i = j then 1 else 0)
  for c in [0:n] do
    let some p := (List.range' c (n - c)).find? (fun r => a[r]![c]! != 0) | return none
    let rowp := a[p]!
    a := (a.set! p a[c]!).set! c rowp
    let piv := a[c]![c]!
    a := a.set! c (a[c]!.map (· / piv))
    for r in [0:n] do
      if r != c then
        let f := a[r]![c]!
        if f != 0 then
          let rc := a[c]!
          a := a.set! r ((a[r]!.zip rc).map fun (x, y) => x - f * y)
  return some (ofFn [n, n] fun idx => a[idx[0]!]![n + idx[1]!]!)

end Arr
end EinsteinpyLean
