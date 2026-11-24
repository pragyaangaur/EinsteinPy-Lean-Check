import EinsteinpyLean.Common.Arr

/-!
# Model of `einsteinpy.symbolic.helpers.TransformationMatrix`

Mirrors `src/einsteinpy/symbolic/helpers.py` at commit `63e1c54`. The difftest feeds
linear coordinate maps `old_i = Σ_j c_ij new_j` with rational `c`, so every
derivative is a rational number and sympy is exact.
-/

namespace EinsteinpyLean.Helpers

/-- A sympy number that is either rational or complex infinity `zoo`, the value of
`1/0` in sympy. -/
inductive Num where
  | rat (q : Rat)
  | zoo
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `np.reciprocal` on an object array calls `1 / x` on each sympy number:
`1/0 = zoo` and `1/zoo = 0`. -/
def Num.recip : Num → Num
  | .rat q => if q = 0 then .zoo else .rat q⁻¹
  | .zoo => .rat 0

def Num.render : Num → String
  | .rat q => Arr.ratStr q
  | .zoo => "zoo"

/-- `derive_by_array(new2old, new_coords)` (helpers.py:155) for a linear map with
coefficients `c` (`c[i][j] = ∂ old_i / ∂ new_j`): entry `[i][j]` is
`∂ new2old[j] / ∂ new_coords[i] = c[j][i]`, the transpose. -/
def deriveByArray (c : List (List Rat)) : List (List Num) :=
  (List.range c.length).map fun i =>
    (List.range c.length).map fun j => .rat ((c[j]!)[i]!)

/-- helpers.py:136-165 `from_new2old`: the element-wise reciprocal of the derivative
array (helpers.py:157 `np.reciprocal`). -/
def fromNew2old (c : List (List Rat)) : List (List Num) :=
  (deriveByArray c).map (·.map Num.recip)

/-- helpers.py:171-190 `inv`: again the element-wise reciprocal. -/
def inv (t : List (List Num)) : List (List Num) := t.map (·.map Num.recip)

def renderMat (m : List (List Num)) : String :=
  " ".intercalate (m.flatten.map Num.render)

end EinsteinpyLean.Helpers
