import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The integrators over the reals

`integrators/fantasy.py` composes the symplectic scheme of Christian and Chan from three exact flows
(`_flow_A`, `_flow_B`, `_flow_mixed`) into a second order step, and lifts it to orders 4, 6 and 8 with
Yoshida's triple jump (`_Z`). `integrators/runge_kutta.py` has the classical fourth order Runge-Kutta step.

This file proves, over `ℝ`:

* the triple jump constants: they sum to one, the outermost level of `_ord_n` has the order condition, and the
  inner levels of orders 6 and 8 do not, because the code reads `_Z(self.order)` there;
* the mixed flow is a rotation of the differences, conserves the sums, is its own inverse for the opposite step
  and preserves the symplectic form;
* `_flow_A` and `_flow_B` are exact one parameter groups (flows of `H_A` and `H_B`);
* the palindromic composition `A B C B A` and the triple jump are time symmetric, for any maps with the
  inverse property;
* the Butcher tableau of `RK4naive` has order four, and one step of the linear test equation is the Taylor
  polynomial of degree four;
* the direction expression of `RK4naive` is identically zero.

Physlib has no symplectic integrators (its `HamiltonianMechanics` is about Hamilton's equations on manifolds),
so the statements are over Mathlib's reals.
-/

open Real

namespace EinsteinpyLean.Geodesic.SpecIntegrator

/-! ## Yoshida's triple jump -/

/-- integrators/utils.py:`_Z`: `(Z0, Z1) = (-x / (2 - x), 1 / (2 - x))` for the jump constant `x`. -/
noncomputable def zc (x : ℝ) : ℝ × ℝ := (-x / (2 - x), 1 / (2 - x))

/-- `x = 2 ** (1 / (2 n + 1))` with `n = (order - 2) / 2`, so `2 n + 1 = order - 1 = m`. -/
noncomputable def jumpX (m : ℕ) : ℝ := (2 : ℝ) ^ ((m : ℝ)⁻¹)

/-- PROP geodesic.Z.sum_one : PROVEN
Source: Yoshida 1990, the three steps `Z1 h`, `Z0 h`, `Z1 h` of a triple jump must add up to the step `h`:
`2 Z1 + Z0 = 1`. It holds for every `x ≠ 2`, so for every order that `_Z` is called with. -/
theorem z_sum_one (x : ℝ) (hx : x ≠ 2) : (zc x).1 + 2 * (zc x).2 = 1 := by
  have h : 2 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  simp only [zc]
  field_simp
  ring

/-- The order condition of a triple jump for the exponent `m`, in closed form. -/
theorem z_cond (x : ℝ) (m : ℕ) (hm : Odd m) :
    2 * (zc x).2 ^ m + (zc x).1 ^ m = (2 - x ^ m) / (2 - x) ^ m := by
  simp only [zc, div_pow, one_pow, Odd.neg_pow hm]
  ring

theorem jumpX_pow (m : ℕ) (hm : m ≠ 0) : jumpX m ^ m = 2 := by
  unfold jumpX
  exact Real.rpow_inv_natCast_pow (by norm_num) hm

theorem jumpX_lt_two (m : ℕ) (h : 2 ≤ m) : jumpX m < 2 := by
  unfold jumpX
  have hm : (2 : ℝ) ≤ m := by exact_mod_cast h
  calc (2 : ℝ) ^ ((m : ℝ)⁻¹) < (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        rw [inv_lt_one₀ (by linarith)]
        linarith
    _ = 2 := Real.rpow_one 2

/-- PROP geodesic.Z.outer_condition : PROVEN
Source: Yoshida 1990, eq. (4.?), and Hairer, Lubich and Wanner, Geometric Numerical Integration II.4. A
triple jump with `x = 2^(1/m)` for odd `m` satisfies `2 Z1^m + Z0^m = 0`: it lifts a symmetric method of order
`m - 1` to order `m + 1`. `_Z(order)` has `m = order - 1`, so the outermost level of `_ord_{order}` has the
right constants. -/
theorem z_outer_condition (m : ℕ) (hm : Odd m) (h3 : 3 ≤ m) :
    2 * (zc (jumpX m)).2 ^ m + (zc (jumpX m)).1 ^ m = 0 := by
  rw [z_cond _ m hm, jumpX_pow m (by omega)]
  simp

/-- For `x = 2^(1/m)` and an exponent `k < m`, the order condition is not satisfied. -/
theorem z_inner_condition_ne (m k : ℕ) (_hm : Odd m) (hk : Odd k) (hkm : k < m) (h3 : 3 ≤ k) :
    2 * (zc (jumpX m)).2 ^ k + (zc (jumpX m)).1 ^ k ≠ 0 := by
  have hx2 : jumpX m < 2 := jumpX_lt_two m (by omega)
  have hxk : jumpX m ^ k < 2 := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have : jumpX m ^ k = (2 : ℝ) ^ ((k : ℝ) / m) := by
      unfold jumpX
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      field_simp
    rw [this]
    calc (2 : ℝ) ^ ((k : ℝ) / m) < (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
          rw [div_lt_one hmpos]
          exact_mod_cast hkm
      _ = 2 := Real.rpow_one 2
  rw [z_cond _ k hk]
  have h1 : 0 < 2 - jumpX m := by linarith
  have h2 : 0 < 2 - jumpX m ^ k := by linarith
  exact (div_pos h2 (pow_pos h1 k)).ne'

/-- PROP geodesic.Z.inner_condition : REFUTED
Source: fantasy.py:192-260. `_ord_6` calls `_ord_4`, a jump from order 2 to order 4 that needs
`2 Z1^3 + Z0^3 = 0`, with the constants `_Z(6)`, which are the jump for `x = 2^(1/5)`. They give
`(2 - 2^(3/5)) / (2 - 2^(1/5))^3 ≠ 0`. The same happens for the order 4 and 6 levels inside `_ord_8`.
(`z_inner_condition_ne` is the general statement.) -/
theorem z6_cubic_condition_fails : ¬ (2 * (zc (jumpX 5)).2 ^ 3 + (zc (jumpX 5)).1 ^ 3 = 0) :=
  fun h => z_inner_condition_ne 5 3 (by decide) (by decide) (by norm_num) le_rfl h

/-- PROP geodesic.Z.inner_condition_order8 : REFUTED
Source: as above, for the sixth order level inside `_ord_8`: `_Z(8)` has `x = 2^(1/7)`, and the condition of
a jump to order 6 is `2 Z1^5 + Z0^5 = 0`. -/
theorem z8_quintic_condition_fails : ¬ (2 * (zc (jumpX 7)).2 ^ 5 + (zc (jumpX 7)).1 ^ 5 = 0) :=
  fun h => z_inner_condition_ne 7 5 (by decide) (by decide) (by norm_num) (by norm_num) h

/-! ## The mixed flow -/

/-- integrators/utils.py:`_flow_mixed` for one component of the four vectors. -/
noncomputable def mixedFlow (δ ω q1 p1 q2 p2 : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  let c := cos (2 * ω * δ)
  let s := sin (2 * ω * δ)
  (1 / 2 * ((q1 + q2) + (q1 - q2) * c + (p1 - p2) * s),
   1 / 2 * ((p1 + p2) + (p1 - p2) * c - (q1 - q2) * s),
   1 / 2 * ((q1 + q2) - (q1 - q2) * c - (p1 - p2) * s),
   1 / 2 * ((p1 + p2) - (p1 - p2) * c + (q1 - q2) * s))

/-- PROP geodesic.mixed.sums_conserved : PROVEN
Source: utils.py:`_flow_mixed`, the flow of `H̃ = ω (|q1 - q2|² + |p1 - p2|²)`. The sums `q1 + q2` and
`p1 + p2` do not change, and the differences are rotated by the angle `2 ω δ`. -/
theorem mixed_sums_and_rotation (δ ω q1 p1 q2 p2 : ℝ) :
    let r := mixedFlow δ ω q1 p1 q2 p2
    r.1 + r.2.2.1 = q1 + q2 ∧ r.2.1 + r.2.2.2 = p1 + p2 ∧
    r.1 - r.2.2.1 = (q1 - q2) * cos (2 * ω * δ) + (p1 - p2) * sin (2 * ω * δ) ∧
    r.2.1 - r.2.2.2 = (p1 - p2) * cos (2 * ω * δ) - (q1 - q2) * sin (2 * ω * δ) := by
  simp only [mixedFlow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- PROP geodesic.mixed.norm_conserved : PROVEN
Source: as above. The rotation keeps `(q1 - q2)² + (p1 - p2)²`. -/
theorem mixed_norm_conserved (δ ω q1 p1 q2 p2 : ℝ) :
    let r := mixedFlow δ ω q1 p1 q2 p2
    (r.1 - r.2.2.1) ^ 2 + (r.2.1 - r.2.2.2) ^ 2 = (q1 - q2) ^ 2 + (p1 - p2) ^ 2 := by
  simp only [mixedFlow]
  have h := sin_sq_add_cos_sq (2 * ω * δ)
  linear_combination ((q1 - q2) ^ 2 + (p1 - p2) ^ 2) * h

/-- PROP geodesic.mixed.inverse : PROVEN
Source: as above. A step with `-δ` undoes a step with `δ`. -/
theorem mixed_inverse (δ ω q1 p1 q2 p2 : ℝ) :
    let r := mixedFlow δ ω q1 p1 q2 p2
    mixedFlow (-δ) ω r.1 r.2.1 r.2.2.1 r.2.2.2 = (q1, p1, q2, p2) := by
  have h := sin_sq_add_cos_sq (2 * ω * δ)
  have hc : cos (2 * ω * -δ) = cos (2 * ω * δ) := by rw [mul_neg, cos_neg]
  have hs : sin (2 * ω * -δ) = - sin (2 * ω * δ) := by rw [mul_neg, sin_neg]
  simp only [mixedFlow, hc, hs]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · linear_combination ((q1 - q2) / 2) * h
  · linear_combination ((p1 - p2) / 2) * h
  · linear_combination (-(q1 - q2) / 2) * h
  · linear_combination (-(p1 - p2) / 2) * h

/-- The symplectic form `dq1 ∧ dp1 + dq2 ∧ dp2` on two tangent vectors. -/
noncomputable def omega (u v : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  u.1 * v.2.1 - u.2.1 * v.1 + u.2.2.1 * v.2.2.2 - u.2.2.2 * v.2.2.1

/-- PROP geodesic.mixed.symplectic : PROVEN
Source: Christian and Chan 2021, the mixed flow is the flow of a quadratic Hamiltonian, so it is symplectic.
`mixedFlow` is linear in `(q1, p1, q2, p2)`, and it preserves the form `dq1 ∧ dp1 + dq2 ∧ dp2` on any two
vectors: the map `u ↦ mixedFlow δ ω u` satisfies `ω(M u, M v) = ω(u, v)`. -/
theorem mixed_symplectic (δ ω : ℝ) (u v : ℝ × ℝ × ℝ × ℝ) :
    omega (mixedFlow δ ω u.1 u.2.1 u.2.2.1 u.2.2.2) (mixedFlow δ ω v.1 v.2.1 v.2.2.1 v.2.2.2) = omega u v := by
  have h := sin_sq_add_cos_sq (2 * ω * δ)
  simp only [omega, mixedFlow]
  linear_combination ((u.1 - u.2.2.1) * (v.2.1 - v.2.2.2) - (u.2.1 - u.2.2.2) * (v.1 - v.2.2.1)) / 2 * h

/-! ## The flows A and B -/

/-- `_flow_A` for one degree of freedom: `H_A(q1, p2) = 1/2 G(q1) p2²` has the partials `Hq = 1/2 G' p2²` (the
code's `0.5 * _PartHamFlow`) and `Hp = G p2` (`g(q1) @ p2`). The map moves `p1` and `q2` and keeps `q1`, `p2`. -/
def flowA (Hq Hp : ℝ → ℝ → ℝ) (δ : ℝ) (z : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (z.1, z.2.1 - δ * Hq z.1 z.2.2.2, z.2.2.1 + δ * Hp z.1 z.2.2.2, z.2.2.2)

/-- PROP geodesic.flowA.group : PROVEN
Source: utils.py:`_flow_A`, "Overall flow of Hamiltonian, `H_A`". The step is an exact flow: because the
right hand sides `Hq` and `Hp` depend on `q1` and `p2` only, and those two do not change, the maps form a
one parameter group `A_a ∘ A_b = A_(a + b)` and `A_(-δ)` is the inverse of `A_δ`. -/
theorem flowA_group (Hq Hp : ℝ → ℝ → ℝ) (a b : ℝ) (z : ℝ × ℝ × ℝ × ℝ) :
    flowA Hq Hp a (flowA Hq Hp b z) = flowA Hq Hp (a + b) z := by
  simp only [flowA]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> simp only [] <;> ring

theorem flowA_inverse (Hq Hp : ℝ → ℝ → ℝ) (δ : ℝ) (z : ℝ × ℝ × ℝ × ℝ) :
    flowA Hq Hp (-δ) (flowA Hq Hp δ z) = z := by
  rw [flowA_group]
  simp only [flowA, neg_add_cancel, zero_mul, sub_zero, add_zero]

/-- `_flow_B` is the same map with the roles of the two copies swapped: it moves `q1` and `p2`, and keeps
`p1`, `q2`. -/
def flowB (Hq Hp : ℝ → ℝ → ℝ) (δ : ℝ) (z : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (z.1 + δ * Hp z.2.2.1 z.2.1, z.2.1, z.2.2.1, z.2.2.2 - δ * Hq z.2.2.1 z.2.1)

/-- PROP geodesic.flowB.group : PROVEN
Source: utils.py:`_flow_B`. As for `_flow_A`: `B_a ∘ B_b = B_(a + b)`, so `B_(-δ)` inverts `B_δ`. -/
theorem flowB_group (Hq Hp : ℝ → ℝ → ℝ) (a b : ℝ) (z : ℝ × ℝ × ℝ × ℝ) :
    flowB Hq Hp a (flowB Hq Hp b z) = flowB Hq Hp (a + b) z := by
  simp only [flowB]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl ?_)) <;> simp only [] <;> ring

theorem flowB_inverse (Hq Hp : ℝ → ℝ → ℝ) (δ : ℝ) (z : ℝ × ℝ × ℝ × ℝ) :
    flowB Hq Hp (-δ) (flowB Hq Hp δ z) = z := by
  rw [flowB_group]
  simp only [flowB, neg_add_cancel, zero_mul, sub_zero, add_zero]

/-- PROP geodesic.flowA.partials : PROVEN
Source: utils.py:`_PartHamFlow` and `_flow_A`: for `H(q, p) = 1/2 G(q) p²` the partial derivative in `p` is
`G(q) p` (the code's `g(q1) @ p2`) and the partial in `q` is `1/2 G'(q) p²` (the code's
`0.5 * (jac @ p @ p)`), so `_flow_A` is the Euler step of Hamilton's equations for `H_A`, which is exact. -/
theorem halfG_partials (G G' : ℝ → ℝ) (q p : ℝ) (hG : HasDerivAt G (G' q) q) :
    HasDerivAt (fun x => 1 / 2 * G x * p ^ 2) (1 / 2 * G' q * p ^ 2) q ∧
    HasDerivAt (fun y => 1 / 2 * G q * y ^ 2) (G q * p) p := by
  constructor
  · have := (hG.const_mul (1 / 2)).mul_const (p ^ 2)
    simpa using this
  · have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * p) p := by simpa using hasDerivAt_pow 2 p
    have := h2.const_mul (1 / 2 * G q)
    convert this using 1
    ring

/-- The tangent map of `flowA` at a point where the second derivatives of `H_A` are `Hqq = H_{q1 q1}`,
`Hqp = H_{q1 p2}`, `Hpq = H_{p2 q1}`, `Hpp = H_{p2 p2}`. -/
def tangentA (δ Hqq Hqp Hpq Hpp : ℝ) (u : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (u.1, u.2.1 - δ * (Hqq * u.1 + Hqp * u.2.2.2), u.2.2.1 + δ * (Hpq * u.1 + Hpp * u.2.2.2), u.2.2.2)

/-- PROP geodesic.flowA.symplectic : PROVEN
Source: Christian and Chan 2021, `H_A` is a Hamiltonian in the extended phase space, so its flow `_flow_A` is
symplectic. The tangent map of the Euler step preserves `dq1 ∧ dp1 + dq2 ∧ dp2` exactly when the mixed second
derivatives agree, `H_{q1 p2} = H_{p2 q1}`, which is the symmetry of the Hessian of any `C²` function. -/
theorem tangentA_symplectic (δ Hqq Hqp Hpq Hpp : ℝ) (h : Hqp = Hpq) (u v : ℝ × ℝ × ℝ × ℝ) :
    omega (tangentA δ Hqq Hqp Hpq Hpp u) (tangentA δ Hqq Hqp Hpq Hpp v) = omega u v := by
  subst h
  simp only [omega, tangentA]
  ring

/-- The tangent map of `flowB` (the copies swapped): `H_B(q2, p1)`. -/
def tangentB (δ Hqq Hqp Hpq Hpp : ℝ) (u : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (u.1 + δ * (Hpq * u.2.2.1 + Hpp * u.2.1), u.2.1, u.2.2.1, u.2.2.2 - δ * (Hqq * u.2.2.1 + Hqp * u.2.1))

/-- PROP geodesic.flowB.symplectic : PROVEN
Source: as for `_flow_A`, for `H_B(q2, p1)` and `_flow_B`. -/
theorem tangentB_symplectic (δ Hqq Hqp Hpq Hpp : ℝ) (h : Hqp = Hpq) (u v : ℝ × ℝ × ℝ × ℝ) :
    omega (tangentB δ Hqq Hqp Hpq Hpp u) (tangentB δ Hqq Hqp Hpq Hpp v) = omega u v := by
  subst h
  simp only [omega, tangentB]
  ring

/-! ## Time symmetry of the compositions -/

section Symmetry

variable {X : Type*}

/-- fantasy.py:`_ord_2`: `A(δ/2)`, `B(δ/2)`, `C(δ)`, `B(δ/2)`, `A(δ/2)`, applied in this order. -/
noncomputable def strang (A B C : ℝ → X → X) (δ : ℝ) (z : X) : X :=
  A (δ / 2) (B (δ / 2) (C δ (B (δ / 2) (A (δ / 2) z))))

/-- PROP geodesic.ord2.time_symmetric : PROVEN
Source: fantasy.py:154-190 and the paper: the second order scheme is palindromic, so a step with `-δ` undoes
a step with `δ`, whenever each of the three flows has the inverse property (which `flowA_inverse`,
`flowB_inverse` and `mixed_inverse` give). -/
theorem strang_reversible (A B C : ℝ → X → X) (hA : ∀ d z, A (-d) (A d z) = z)
    (hB : ∀ d z, B (-d) (B d z) = z) (hC : ∀ d z, C (-d) (C d z) = z) (δ : ℝ) (z : X) :
    strang A B C (-δ) (strang A B C δ z) = z := by
  have e : -δ / 2 = -(δ / 2) := by ring
  simp only [strang, e, hA, hB, hC]

/-- fantasy.py:`_ord_4` and the next ones: `S(Z1 δ)`, `S(Z0 δ)`, `S(Z1 δ)`, applied in this order. -/
noncomputable def tripleJump (S : ℝ → X → X) (z0 z1 δ : ℝ) (z : X) : X :=
  S (z1 * δ) (S (z0 * δ) (S (z1 * δ) z))

/-- PROP geodesic.ordN.time_symmetric : PROVEN
Source: fantasy.py:192-290. The triple jump of a reversible method is reversible, for every pair of
constants, so also for the wrong constants of the inner levels. -/
theorem tripleJump_reversible (S : ℝ → X → X) (hS : ∀ d z, S (-d) (S d z) = z) (z0 z1 δ : ℝ) (z : X) :
    tripleJump S z0 z1 (-δ) (tripleJump S z0 z1 δ z) = z := by
  simp only [tripleJump, mul_neg, hS]

end Symmetry

/-! ## The classical Runge-Kutta step -/

/-- The Butcher tableau of `RK4naive` (runge_kutta.py:39-60): `k1 = f(t + h/2, y + h/2 k0)`,
`k2 = f(t + h/2, y + h/2 k1)`, `k3 = f(t + h, y + h k2)`, weights `1/6, 1/3, 1/3, 1/6`. -/
noncomputable def rkA : Fin 4 → Fin 4 → ℝ := ![![0, 0, 0, 0], ![1 / 2, 0, 0, 0], ![0, 1 / 2, 0, 0], ![0, 0, 1, 0]]
noncomputable def rkB : Fin 4 → ℝ := ![1 / 6, 1 / 3, 1 / 3, 1 / 6]
noncomputable def rkC : Fin 4 → ℝ := ![0, 1 / 2, 1 / 2, 1]

/-- PROP geodesic.rk4.butcher_order4 : PROVEN
Source: the class docstring "Runge-Kutta 4th Order". The eight order conditions up to order four (Hairer,
Nørsett, Wanner I.2) hold for the tableau, and the row sums of `A` are `c`. -/
theorem rk4_order_conditions :
    (∑ i, rkB i = 1) ∧ (∑ i, rkB i * rkC i = 1 / 2) ∧ (∑ i, rkB i * rkC i ^ 2 = 1 / 3) ∧
    (∑ i, ∑ j, rkB i * rkA i j * rkC j = 1 / 6) ∧ (∑ i, rkB i * rkC i ^ 3 = 1 / 4) ∧
    (∑ i, ∑ j, rkB i * rkC i * rkA i j * rkC j = 1 / 8) ∧
    (∑ i, ∑ j, rkB i * rkA i j * rkC j ^ 2 = 1 / 12) ∧
    (∑ i, ∑ j, ∑ k, rkB i * rkA i j * rkA j k * rkC k = 1 / 24) ∧ (∀ i, ∑ j, rkA i j = rkC i) := by
  simp only [rkA, rkB, rkC, Fin.sum_univ_four, Fin.forall_fin_succ]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- One step of `RK4naive` for the linear test equation `y' = λ y`. -/
noncomputable def rkStepLin (lam h y : ℝ) : ℝ :=
  let k0 := lam * y
  let k1 := lam * (y + h / 2 * k0)
  let k2 := lam * (y + h / 2 * k1)
  let k3 := lam * (y + h * k2)
  y + h / 6 * (k0 + 2 * k1 + 2 * k2 + k3)

/-- PROP geodesic.rk4.linear_step : PROVEN
Source: runge_kutta.py:57-60. For `y' = λ y` one step multiplies `y` by the Taylor polynomial of
`exp (h λ)` of degree four, `1 + z + z²/2 + z³/6 + z⁴/24` with `z = h λ`. -/
theorem rk4_linear_step (lam h y : ℝ) :
    rkStepLin lam h y = y * (1 + h * lam + (h * lam) ^ 2 / 2 + (h * lam) ^ 3 / 6 + (h * lam) ^ 4 / 24) := by
  simp only [rkStepLin]
  ring

/-- runge_kutta.py:37 `self.direction = 1 * (t_bound >= t0) - 1 * (not t_bound < t0)` over the reals. -/
noncomputable def direction (t0 tb : ℝ) : ℤ := (if tb ≥ t0 then 1 else 0) - (if ¬ tb < t0 then 1 else 0)

/-- PROP geodesic.rk4.direction_zero_real : PROVEN
Source: the line above. The two Booleans are the same, so the direction is `0` for all real `t0`, `t_bound`. -/
theorem direction_zero_real (t0 tb : ℝ) : direction t0 tb = 0 := by
  unfold direction
  by_cases h : tb < t0
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

/-- PROP geodesic.rk4.direction_is_sign_real : REFUTED
Source: the docstring of `t_bound` ("It also determines the direction of the integration") and scipy's
`np.sign(t_bound - t0)`. The expression is `0` also when `t_bound > t0`. -/
theorem direction_is_not_sign_real : ¬ (∀ t0 tb : ℝ, t0 < tb → direction t0 tb = 1) := by
  intro h
  have := h 0 1 one_pos
  rw [direction_zero_real] at this
  exact absurd this (by norm_num)

end EinsteinpyLean.Geodesic.SpecIntegrator
