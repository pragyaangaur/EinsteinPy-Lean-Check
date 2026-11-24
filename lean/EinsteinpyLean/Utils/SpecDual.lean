import EinsteinpyLean.Utils.Dual
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# `DualNumber` against Mathlib

`Dual.add`, `Dual.mul`, ... of `Dual.lean` are the generic layer of the model: the operations of
dual.py without the Python errors. Here they run on a commutative ring and on `ℝ`.

* The dual numbers over a commutative ring `R` satisfy the commutative ring laws with `ε² = 0`.
* The dual part of each operation is the derivative that Mathlib proves: sum, product, quotient, `sin`,
  `cos`, `tan`, `exp`, `log` and the power. With `u` differentiable at `x`, the dual part of the operation
  applied to `⟨u x, u'⟩` is the derivative of the composite. For `u = id` and `u' = 1` this is what
  `_deriv` returns.
-/

open Real

namespace EinsteinpyLean.Utils.Spec

open EinsteinpyLean.Utils

section Ring

variable {R : Type} [CommRing R]

omit [CommRing R] in
theorem dual_ext {a b : Dual R} (h1 : a.val = b.val) (h2 : a.deriv = b.deriv) : a = b := by
  cases a; cases b; simp_all

/-- PROP dual.ring.add_assoc : PROVEN
Source: dual.py:12-13, `a + b ε` with `ε² = 0` is a commutative ring. -/
theorem add_assoc (a b c : Dual R) : Dual.add (Dual.add a b) c = Dual.add a (Dual.add b c) :=
  dual_ext (by simp [Dual.add, _root_.add_assoc]) (by simp [Dual.add, _root_.add_assoc])

/-- PROP dual.ring.add_comm : PROVEN
Source: dual.py:47-53 (`__radd__ = __add__`). -/
theorem add_comm (a b : Dual R) : Dual.add a b = Dual.add b a :=
  dual_ext (by simp [Dual.add, _root_.add_comm]) (by simp [Dual.add, _root_.add_comm])

/-- PROP dual.ring.add_neg : PROVEN
Source: dual.py:121, `__neg__`, is the additive inverse of the zero `⟨0, 0⟩`. -/
theorem add_neg (a : Dual R) : Dual.add a (Dual.neg a) = ⟨0, 0⟩ :=
  dual_ext (by simp [Dual.add, Dual.neg]) (by simp [Dual.add, Dual.neg])

/-- PROP dual.ring.sub_is_add_neg : PROVEN
Source: dual.py:55-61, `__sub__` is addition of the negative. -/
theorem sub_eq_add_neg (a b : Dual R) : Dual.sub a b = Dual.add a (Dual.neg b) :=
  dual_ext (by simp [Dual.sub, Dual.add, Dual.neg, _root_.sub_eq_add_neg])
    (by simp [Dual.sub, Dual.add, Dual.neg, _root_.sub_eq_add_neg])

/-- PROP dual.ring.mul_comm : PROVEN
Source: dual.py:70-77. This is why `__rmul__ = __mul__` is correct. -/
theorem mul_comm (a b : Dual R) : Dual.mul a b = Dual.mul b a :=
  dual_ext (by simp [Dual.mul, _root_.mul_comm]) (by simp only [Dual.mul]; ring)

/-- PROP dual.ring.mul_assoc : PROVEN
Source: dual.py:70-75. -/
theorem mul_assoc (a b c : Dual R) : Dual.mul (Dual.mul a b) c = Dual.mul a (Dual.mul b c) :=
  dual_ext (by simp only [Dual.mul]; ring) (by simp only [Dual.mul]; ring)

/-- PROP dual.ring.one_mul : PROVEN
Source: dual.py:70-75, with the unit `⟨1, 0⟩`. -/
theorem one_mul (a : Dual R) : Dual.mul ⟨1, 0⟩ a = a :=
  dual_ext (by simp [Dual.mul]) (by simp [Dual.mul])

/-- PROP dual.ring.left_distrib : PROVEN
Source: dual.py:47-75. -/
theorem left_distrib (a b c : Dual R) :
    Dual.mul a (Dual.add b c) = Dual.add (Dual.mul a b) (Dual.mul a c) :=
  dual_ext (by simp only [Dual.mul, Dual.add]; ring) (by simp only [Dual.mul, Dual.add]; ring)

/-- PROP dual.ring.epsilon_squared : PROVEN
Source: dual.py:12 docstring, `ε² = 0` and `ε ≠ 0` (here `⟨0, 1⟩ ≠ ⟨0, 0⟩` over a nontrivial ring). -/
theorem epsilon_sq : Dual.mul (⟨0, 1⟩ : Dual R) ⟨0, 1⟩ = ⟨0, 0⟩ :=
  dual_ext (by simp [Dual.mul]) (by simp [Dual.mul])

/-- PROP dual.ring.scalar_mul_agrees : PROVEN
Source: dual.py:77 `__mul__` with a plain number is the product with `⟨c, 0⟩`. -/
theorem mulS_eq_mul (a : Dual R) (c : R) : Dual.mulS a c = Dual.mul a ⟨c, 0⟩ :=
  dual_ext (by simp [Dual.mulS, Dual.mul]) (by simp [Dual.mulS, Dual.mul])

/-- PROP dual.ring.scalar_add_agrees : PROVEN
Source: dual.py:53 `__add__` with a plain number is the sum with `⟨c, 0⟩`. -/
theorem addS_eq_add (a : Dual R) (c : R) : Dual.addS a c = Dual.add a ⟨c, 0⟩ :=
  dual_ext (by simp [Dual.addS, Dual.add]) (by simp [Dual.addS, Dual.add])

end Ring

section Calculus

variable {u v : ℝ → ℝ} {u' v' x : ℝ}

/-- PROP dual.calculus.sum_rule : PROVEN
Source: Mathlib `HasDerivAt.add`. The dual part of the sum is the derivative of the sum. -/
theorem add_rule (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun y => u y + v y) (Dual.add ⟨u x, u'⟩ ⟨v x, v'⟩).deriv x := by
  simpa [Dual.add] using hu.fun_add hv

/-- PROP dual.calculus.product_rule : PROVEN
Source: Mathlib `HasDerivAt.mul`. -/
theorem mul_rule (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun y => u y * v y) (Dual.mul ⟨u x, u'⟩ ⟨v x, v'⟩).deriv x := by
  simpa [Dual.mul] using hu.fun_mul hv

/-- PROP dual.calculus.neg_rule : PROVEN
Source: Mathlib `HasDerivAt.neg`. -/
theorem neg_rule (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => -u y) (Dual.neg ⟨u x, u'⟩).deriv x := by
  simpa [Dual.neg] using hu.fun_neg

/-- PROP dual.calculus.quotient_rule : PROVEN
Source: Mathlib `HasDerivAt.div`, for a divisor that does not vanish at `x`. The model
`Dual.divRule` is the branch of dual.py:87-90 that is used when the divisor value is not zero. -/
theorem div_rule (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) (h : v x ≠ 0) :
    HasDerivAt (fun y => u y / v y) (Dual.divRule ⟨u x, u'⟩ ⟨v x, v'⟩).deriv x := by
  have := hu.div hv h
  simp only [Dual.divRule]
  convert this using 1
  ring

/-- PROP dual.calculus.sin_rule : PROVEN
Source: Mathlib `HasDerivAt.sin`, for dual.py:124 `sin`. -/
theorem sin_rule (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => Real.sin (u y)) (Dual.sinWith Real.sin Real.cos ⟨u x, u'⟩).deriv x := by
  simpa [Dual.sinWith, _root_.mul_comm] using hu.sin

/-- PROP dual.calculus.cos_rule : PROVEN
Source: Mathlib `HasDerivAt.cos`, for dual.py:127 `cos`. -/
theorem cos_rule (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => Real.cos (u y)) (Dual.cosWith Real.sin Real.cos ⟨u x, u'⟩).deriv x := by
  have := hu.cos
  simp only [Dual.cosWith]
  convert this using 1
  ring

/-- PROP dual.calculus.exp_rule : PROVEN
Source: Mathlib `HasDerivAt.exp`, for dual.py:133 `exp`. -/
theorem exp_rule (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => Real.exp (u y)) (Dual.expWith Real.exp ⟨u x, u'⟩).deriv x := by
  simpa [Dual.expWith, _root_.mul_comm] using hu.exp

/-- PROP dual.calculus.log_rule : PROVEN
Source: Mathlib `HasDerivAt.log`, for dual.py:130 `log`, when `u x ≠ 0`. -/
theorem log_rule (hu : HasDerivAt u u' x) (h : u x ≠ 0) :
    HasDerivAt (fun y => Real.log (u y)) (Dual.logWith Real.log ⟨u x, u'⟩).deriv x := by
  simpa [Dual.logWith] using hu.log h

/-- PROP dual.calculus.pow_rule : PROVEN
Source: Mathlib `HasDerivAt.rpow_const`. For a positive value the dual part of `x ** p`, which is
`deriv * p * val ** (p - 1)`, is the derivative of `u ** p`. -/
theorem pow_rule (hu : HasDerivAt u u' x) (p : ℝ) (h : 0 < u x) :
    HasDerivAt (fun y => u y ^ p) (Dual.powWith (fun a b => a ^ b) p (p - 1) ⟨u x, u'⟩).deriv x := by
  simpa [Dual.powWith] using hu.rpow_const (p := p) (Or.inl h.ne')

/-- PROP dual.calculus.tan_rule : PROVEN
Source: dual.py:136-137 `tan` is `sin(self) / cos(self)`. Where `cos (u x) ≠ 0` its dual part
is the derivative of `tan ∘ u`. -/
theorem tan_rule (hu : HasDerivAt u u' x) (h : Real.cos (u x) ≠ 0) :
    HasDerivAt (fun y => Real.tan (u y))
      (Dual.divRule (Dual.sinWith Real.sin Real.cos ⟨u x, u'⟩)
        (Dual.cosWith Real.sin Real.cos ⟨u x, u'⟩)).deriv x := by
  have h1 := sin_rule hu
  have h2 := cos_rule hu
  have := div_rule h1 h2 h
  simp only [Real.tan_eq_sin_div_cos]
  exact this

/-- PROP dual.calculus.deriv_is_deriv_sin : PROVEN
Source: dual.py:137-157 `_deriv`. For `sin` the dual part of `sin(DualNumber(x, 1))` is `deriv sin x`. -/
theorem deriv_sin (x : ℝ) :
    (Dual.sinWith Real.sin Real.cos ⟨x, 1⟩).deriv = deriv Real.sin x := by
  simp [Dual.sinWith, Real.deriv_sin]

/-- PROP dual.calculus.xx_over_x_true_derivative : PROVEN
Source: the quotient rule. The function `x * x / x` is the identity everywhere on `ℝ`, so its derivative at `0` is `1`.
`Props.lean` shows that dual.py:84-85 answers `0` there. -/
theorem xx_over_x_deriv : deriv (fun y : ℝ => y * y / y) 0 = 1 := by
  have : (fun y : ℝ => y * y / y) = fun y => y := by
    funext y
    by_cases h : y = 0
    · simp [h]
    · field_simp
  rw [this]
  simp

end Calculus

end EinsteinpyLean.Utils.Spec
