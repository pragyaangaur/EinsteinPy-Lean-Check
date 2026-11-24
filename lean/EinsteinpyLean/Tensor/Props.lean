import EinsteinpyLean.Tensor.Model

/-!
# Properties of the `einsteinpy.symbolic.tensor` model

Statements about the executable model of `Model.lean`. The general statements about
Lorentz transforms over the real numbers, which use Physlib's Lorentz group, are in
`Spec.lean`.

`native_decide` is used below because the kernel would have to reduce `Rat`
arithmetic (gcd) inside `Array` code, which `decide` cannot finish. Each use
evaluates one concrete case of the compiled model, the same code that the
difftests check against einsteinpy.
-/

namespace EinsteinpyLean.Tensor
open Arr

/-- `e` succeeded with exactly `x`. A `Bool`, so concrete cases can be evaluated. -/
def okIs {α : Type} [DecidableEq α] (e : Except Err α) (x : α) : Bool :=
  match e with
  | .ok y => decide (y = x)
  | .error _ => false

/-- The 1+1 boost with velocity 3/5, so γ = 5/4 and γ v = 3/4. -/
def boost35 : Arr := ⟨[2, 2], #[5/4, 3/4, 3/4, 5/4]⟩
/-- Minkowski metric diag(-1, 1), einsteinpy's sign convention. -/
def eta2 : Arr := ⟨[2, 2], #[-1, 0, 0, 1]⟩
def vec12 : Arr := ⟨[2], #[1, 2]⟩

/-- PROP tensor.config_checker.accepts_only_ul : PROVEN
Source: tensor.py:12-25 docstring, "config ... contains characters other than 'l' or 'u'". -/
theorem configChecker_iff (c : String) :
    configChecker c = true ↔ ∀ ch ∈ c.toList, ch = 'l' ∨ ch = 'u' := by
  simp [configChecker, List.all_eq_true]

/-- PROP tensor.config_checker.empty_string : PROVEN
Source: Python semantics, an empty config is valid and describes a scalar. -/
theorem configChecker_empty : configChecker "" = true := by decide

/-- PROP tensor.difference_list.zero_iff_equal : PROVEN
Source: tensor.py:28-41, the entries are 0 exactly where the configs agree. -/
theorem differenceList_self (c : String) :
    differenceList c c = c.toList.map (fun _ => 0) := by
  unfold differenceList
  generalize c.toList = l
  induction l with
  | nil => rfl
  | cons x xs ih => simp_all

/-- PROP tensor.tensor_product.index_given_means_contracted : REFUTED
Source: tensor.py:89-104 docstring, "i : contract ``i``th index of ``tensor1``". With
`i = 0` and `j = None` the test `(i or j) is None` is true because `0` is falsy, so
the call silently returns the uncontracted product instead of contracting or
raising. -/
theorem tensorProduct_i0_jNone_not_contracted :
    okIs (tensorProduct vec12 "u" vec12 "l" (some 0) none) ("ul", tensorproduct vec12 vec12) := by
  native_decide

/-- PROP tensor.tensor_product.negative_index_contracts : REFUTED
Source: tensor.py:101-110. The config lookup `config[i]` accepts a negative `i`, but
the axis pair `(i, len(config1) + j)` goes to `sympy.tensorcontraction` unnormalised.
sympy keeps the negative axis in the result, so for `i = -1, j = 0` with configs
`u` and `lu` the result has rank 2 and config `uu` where a contraction of a rank 3
product must have rank 1. The values are sums over a wrapped flat index. -/
theorem tensorProduct_negative_index_wrong_rank :
    okIs ((tensorProduct vec12 "u" ⟨[2, 2], #[0, 0, -2, -3]⟩ "lu" (some (-1)) (some 0)).map
      (fun r => (r.1, r.2.rank))) ("uu", 2) := by
  native_decide

/-- Example, not a property: lowering then raising returns the vector. The general
statement is `Spec.lean`, `lower_raise`. -/
theorem changeConfig_roundtrip_example :
    okIs (do
      let l ← changeConfig vec12 "u" "l" eta2 eta2
      changeConfig l "l" "u" eta2 eta2) vec12 := by
  native_decide

/-- PROP tensor.lorentz_transform.commutes_with_lowering : REFUTED
Source: tensor.py:424-459 docstring, "Performs a Lorentz transform on the tensor".
A Lorentz transform must commute with lowering an index by the Minkowski metric.
For the 3/5 boost, the metric diag(-1, 1) and v = (1, 2), lowering then boosting
gives (1/4, 7/4) and boosting then lowering gives (-11/4, 13/4). The cause is that a lower index is
contracted with the matrix itself (axis 0) instead of its inverse. Known upstream as
einsteinpy issue #374 / #355, fixed by PR #708 (not merged on 63e1c54). -/
theorem lorentz_lower_then_boost_ne_boost_then_lower :
    okIs (do let l ← changeConfig vec12 "u" "l" eta2 eta2; lorentzTransform l "l" boost35)
      ⟨[2], #[1/4, 7/4]⟩ ∧
    okIs (do let b ← lorentzTransform vec12 "u" boost35; changeConfig b "u" "l" eta2 eta2)
      ⟨[2], #[-11/4, 13/4]⟩ := by
  native_decide

/-- Example, not a property: the rule of PR #708 on the same input gives the
boost-then-lower answer. The general proof over Physlib's Lorentz group is
`Spec.lean`, `fixed_lower_comm`. -/
theorem lorentzFixed_example :
    okIs (do let l ← changeConfig vec12 "u" "l" eta2 eta2; lorentzTransformFixed l "l" boost35)
      ⟨[2], #[-11/4, 13/4]⟩ := by
  native_decide

end EinsteinpyLean.Tensor
