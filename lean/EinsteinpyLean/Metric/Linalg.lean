import EinsteinpyLean.Utils.Constants

/-!
# Small NumPy and LAPACK pieces for the Metric model

Core Lean only. The metric classes call `np.linalg.inv` and the `@` operator on 4 by 4 float64 arrays. NumPy
hands both to OpenBLAS on this machine, and the order in which BLAS adds the products decides the last bit.
The orders below were found by comparing with NumPy on thousands of matrices and are stated here so a reader
can see what the difftests rely on:

* `matmul4` (`dgemm`): each entry is `fma(a2, b2, a0 * b0 + 0) + fma(a3, b3, a1 * b1 + 0)`. The accumulators
  start at `+0`, so a product `-0` becomes `+0`.
* `matvec4` (`dgemv`): each entry is `(a0 * v0 + a2 * v2) + (a1 * v1 + a3 * v3)`, no fused multiply-add, and a product `-0`
  stays `-0`.
* `inv4` (`dgesv` against the identity): the recursive LU of `dgetrf2` with partial pivoting and row
  swaps, multipliers found with the reciprocal of the pivot, then forward substitution without fused
  multiply-add and back substitution with the reciprocal of the diagonal and a fused multiply-add.

The orders were confirmed for matrices of Kerr shape, where only the entries `00 03 30 11 22 33` are
nonzero, and for the matrices that the metric classes build (see `difftest/metric_*_diff.py`). Dense
matrices follow other kernels and are not claimed.
-/

namespace EinsteinpyLean.Metric

/-- A 4 by 4 array in row-major order, or a rank 3 array of shape 4,4,4 with entry `[i,j,k]` at `16 i + 4 j + k`. -/
abbrev Arr := Array Float

def zeros (n : Nat) : Arr := Array.replicate n 0.0

/-- Entry `[i, j]` of a 4 by 4 array. -/
def Arr.at2 (a : Arr) (i j : Nat) : Float := a[i * 4 + j]!

/-- Entry `[i, j, k]` of an array of shape 4,4,4. -/
def Arr.at3 (a : Arr) (i j k : Nat) : Float := a[i * 16 + j * 4 + k]!

def Arr.set2 (a : Arr) (i j : Nat) (v : Float) : Arr := a.set! (i * 4 + j) v

def Arr.set3 (a : Arr) (i j k : Nat) (v : Float) : Arr := a.set! (i * 16 + j * 4 + k) v

/-- `A @ B` for 4 by 4 float64 arrays (`dgemm`). -/
def matmul4 (a b : Arr) : Arr := Id.run do
  let mut c := zeros 16
  for i in [0:4] do
    for j in [0:4] do
      let s0 := Float.fma (a.at2 i 2) (b.at2 2 j) ((a.at2 i 0 * b.at2 0 j) + 0.0)
      let s1 := Float.fma (a.at2 i 3) (b.at2 3 j) ((a.at2 i 1 * b.at2 1 j) + 0.0)
      c := c.set2 i j (s0 + s1)
  return c

/-- `A @ v` for a 4 by 4 array and a vector of length 4 (`dgemv`). -/
def matvec4 (a : Arr) (v : Array Float) : Array Float := Id.run do
  let mut c := zeros 4
  for i in [0:4] do
    let s0 := a.at2 i 0 * v[0]! + a.at2 i 2 * v[2]!
    let s1 := a.at2 i 1 * v[1]! + a.at2 i 3 * v[3]!
    c := c.set! i (s0 + s1)
  return c

/-- State of the LU factorisation: the matrix, the row permutation and whether a pivot was exactly zero. -/
structure LU where
  a : Arr
  perm : Array Nat
  sing : Bool

/-- `dgetrf2` on one column: choose the pivot (`idamax`, first maximum), swap rows, scale by the reciprocal. -/
def pivStep (s : LU) (k : Nat) : LU := Id.run do
  let mut a := s.a
  let mut perm := s.perm
  let mut sing := s.sing
  let mut p := k
  let mut best := (a.at2 k k).abs
  for i in [k + 1:4] do
    let v := (a.at2 i k).abs
    if v > best then
      best := v
      p := i
  if a.at2 p k != 0.0 then
    if p != k then
      for j in [0:4] do
        let t := a.at2 k j
        a := a.set2 k j (a.at2 p j)
        a := a.set2 p j t
      let t := perm[k]!
      perm := perm.set! k perm[p]!
      perm := perm.set! p t
    let piv := a.at2 k k
    if piv.abs >= 2.2250738585072014e-308 then
      let rk := 1.0 / piv
      for i in [k + 1:4] do
        a := a.set2 i k (a.at2 i k * rk)
    else
      for i in [k + 1:4] do
        a := a.set2 i k (a.at2 i k / piv)
  else
    sing := true
  return ⟨a, perm, sing⟩

/-- The recursive LU of a 4 by 4 array (`dgetrf2`): split 2 and 2, then 1 and 1 inside each half. -/
def luFactor (g : Arr) : LU := Id.run do
  let mut s : LU := ⟨g, #[0, 1, 2, 3], false⟩
  s := pivStep s 0
  let mut a := s.a
  for i in [1:4] do
    a := a.set2 i 1 (a.at2 i 1 - a.at2 i 0 * a.at2 0 1)
  s := pivStep ⟨a, s.perm, s.sing⟩ 1
  a := s.a
  for j in [2:4] do
    a := a.set2 1 j (a.at2 1 j - a.at2 1 0 * a.at2 0 j)
  for i in [2:4] do
    for j in [2:4] do
      let acc := Float.fma (a.at2 i 1) (a.at2 1 j) (a.at2 i 0 * a.at2 0 j)
      a := a.set2 i j (a.at2 i j - acc)
  s := pivStep ⟨a, s.perm, s.sing⟩ 2
  a := s.a
  a := a.set2 3 3 (a.at2 3 3 - a.at2 3 2 * a.at2 2 3)
  s := pivStep ⟨a, s.perm, s.sing⟩ 3
  return s

/-- `np.linalg.inv` of a 4 by 4 array. `none` is `LinAlgError`, raised when a pivot of `dgetrf` is exactly zero. -/
def inv4 (g : Arr) : Option Arr :=
  let s := luFactor g
  if s.sing then none else
  some <| Id.run do
    let a := s.a
    let mut inv := zeros 16
    for col in [0:4] do
      let mut b : Array Float := Array.ofFn (n := 4) fun i => if s.perm[i.val]! == col then 1.0 else 0.0
      for k in [0:4] do
        for i in [k + 1:4] do
          b := b.set! i (b[i]! - b[k]! * a.at2 i k)
      for kk in [0:4] do
        let k := 3 - kk
        b := b.set! k (b[k]! * (1.0 / a.at2 k k))
        for i in [0:k] do
          b := b.set! i (Float.fma (-b[k]!) (a.at2 i k) b[i]!)
      for i in [0:4] do
        inv := inv.set2 i col b[i]!
    return inv

end EinsteinpyLean.Metric
