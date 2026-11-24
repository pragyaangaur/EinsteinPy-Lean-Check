import EinsteinpyLean.Common.Arr

/-!
# Model of `einsteinpy.symbolic.tensor`

Mirrors `src/einsteinpy/symbolic/tensor.py` of einsteinpy at commit `63e1c54`
line by line, on rational arrays. Every line reference below is to that file.
-/

namespace EinsteinpyLean.Tensor
open Arr

/-- Errors, one constructor per raise site. -/
inductive Err where
  /-- tensor.py:47 `_change_config`: `raise ValueError` (bare, no message) when the
  new config has the wrong length or a character other than `u` and `l`. -/
  | changeConfigBad
  /-- tensor.py:101 `tensor_product`: "Index summation not allowed between %s and %s indices". -/
  | sameKindSum
  /-- `tensor1.config[None]`: `TypeError: string indices must be integers`, reached when
  exactly one of `i`, `j` is `None` and the other is a nonzero integer. -/
  | noneIndex
  /-- `config[i]` with `i` out of range: `IndexError: string index out of range`. -/
  | indexOutOfRange
  /-- sympy raised inside `tensorcontraction`: `IndexError` for an axis out of range. -/
  | sympyIndex
  /-- sympy raised `ValueError` inside `tensorcontraction` ("dimension specified more
  than once" or "cannot contract or diagonalize between axes of different dimension"). -/
  | sympyValue
  /-- tensor.py:162 `Tensor.__init__`: "invalid shape of array for tensor of order
  implied by config", raised when `tensor_product` builds its result. -/
  | badShape
  deriving Repr, BEq, DecidableEq

def Err.tag : Err → String
  | .changeConfigBad => "ValueError"
  | .sameKindSum => "ValueError:summation"
  | .noneIndex => "TypeError"
  | .indexOutOfRange => "IndexError"
  | .sympyIndex => "IndexError"
  | .sympyValue => "ValueError"
  | .badShape => "ValueError"

/-- tensor.py:12-25 `_config_checker`. -/
def configChecker (config : String) : Bool :=
  config.toList.all fun ch => ch == 'l' || ch == 'u'

/-- tensor.py:28-41 `_difference_list`: `0` where the characters agree, `1` where the
new character is `u`, `-1` otherwise. `zip` stops at the shorter string. -/
def differenceList (newconfig oldconfig : String) : List Int :=
  (newconfig.toList.zip oldconfig.toList).map fun (n, o) =>
    if n == o then 0 else if n == 'u' then 1 else -1

/-- The destination permutation built at tensor.py:79-81 and tensor.py:449-451:
`dest = list(range(r)); dest.remove(0); dest.insert(i, 0)`. -/
def moveFrontTo (r i : Nat) : List Nat := insertAt ((List.range r).erase 0) i 0

/-- One step of `chain_config_change` (tensor.py:72-82): contract the metric's second
axis with axis `i` of `t`, then move the new axis from the front back to position `i`.
`simplify` is the identity on rationals. -/
def ofPy : PyErr → Err
  | .indexError => .sympyIndex
  | .valueError => .sympyValue

def raiseLowerAt (m t : Arr) (i : Nat) : Except Err Arr := do
  let c ← (tensorcontraction (tensorproduct m t) 1 (2 + i)).mapError ofPy
  return permutedims c (moveFrontTo c.rank i)

/-- tensor.py:44-84 `_change_config`. `gLower` is `metric.lower_config().tensor()` and
`gUpper` its inverse. -/
def changeConfig (t : Arr) (config newconfig : String) (gLower gUpper : Arr) :
    Except Err Arr := do
  unless newconfig.length == config.length && configChecker newconfig do
    throw .changeConfigBad
  let mut cur := t
  for (action, i) in (differenceList newconfig config).zipIdx do
    if action == 0 then continue
    let m := if action == -1 then gLower else gUpper
    cur ← raiseLowerAt m cur i
  return cur

/-- Python truthiness of an optional integer argument. -/
def truthy : Option Int → Bool
  | none => false
  | some k => k != 0

/-- Python `(i or j)`: `i` when truthy, else `j`. -/
def pyOr (i j : Option Int) : Option Int := if truthy i then i else j

/-- Python string indexing `s[k]` with negative indices. -/
def pyIndex (s : String) (k : Int) : Except Err Char :=
  let n : Int := s.length
  let k' := if k < 0 then k + n else k
  if 0 ≤ k' ∧ k' < n then .ok (s.toList[k'.toNat]!) else .error .indexOutOfRange

/-- Python's normalisation of a slice bound: negative bounds count from the end and
everything is clamped to `[0, n]`. -/
def sliceBound (n : Nat) (k : Int) : Nat :=
  let k' := if k < 0 then k + n else k
  (max 0 (min k' n)).toNat

/-- Python `s[:k] + s[k+1:]`, literally. For `k = -1` this is `s[:-1] + s[0:]`, which
does not remove anything: it drops the last character and then appends the whole
string again. -/
def dropAt (s : String) (k : Int) : String :=
  let l := s.toList
  String.ofList (l.take (sliceBound l.length k) ++ l.drop (sliceBound l.length (k + 1)))

/-- tensor.py:89-118 `tensor_product`. Returns the new config and array. -/
def tensorProduct (a1 : Arr) (c1 : String) (a2 : Arr) (c2 : String)
    (i j : Option Int) : Except Err (String × Arr) := do
  let product := tensorproduct a1 a2
  if pyOr i j == none then
    return (c1 ++ c2, product)
  -- `tensor1.config[i] == tensor2.config[j]`: `config[None]` is a TypeError.
  let some i' := i | throw .noneIndex
  let ci ← pyIndex c1 i'
  let some j' := j | throw .noneIndex
  let cj ← pyIndex c2 j'
  if ci == cj then throw .sameKindSum
  -- tensor.py:104: the axes go to sympy as `(i, len(tensor1.config) + j)`, unnormalised.
  let c ← (tensorcontraction product i' (c1.length + j')).mapError ofPy
  let newconfig := dropAt c1 i' ++ dropAt c2 j'
  -- tensor.py:111 builds a `BaseRelativityTensor`, whose constructor checks the rank.
  if c.rank != newconfig.length then throw .badShape
  return (newconfig, c)

/-- tensor.py:424-459 `BaseRelativityTensor.lorentz_transform`: an upper index is
contracted with axis 1 of the matrix, a lower index with axis 0. -/
def lorentzTransform (t : Arr) (config : String) (tm : Arr) : Except Err Arr := do
  let mut cur := t
  for (ch, i) in config.toList.zipIdx do
    let axis : Int := if ch == 'u' then 1 else 0
    let c ← (tensorcontraction (tensorproduct tm cur) axis (2 + i)).mapError ofPy
    cur := permutedims c (moveFrontTo c.rank i)
  return cur

/-- The rule of einsteinpy PR #708: a lower index is contracted with axis 0 of the
inverse matrix. Used to check the fix, not part of einsteinpy main. -/
def lorentzTransformFixed (t : Arr) (config : String) (tm : Arr) : Except Err Arr := do
  let some inv := matInv tm | throw .sympyValue
  let mut cur := t
  for (ch, i) in config.toList.zipIdx do
    let (m, axis) : Arr × Int := if ch == 'u' then (tm, 1) else (inv, 0)
    let c ← (tensorcontraction (tensorproduct m cur) axis (2 + i)).mapError ofPy
    cur := permutedims c (moveFrontTo c.rank i)
  return cur

end EinsteinpyLean.Tensor
