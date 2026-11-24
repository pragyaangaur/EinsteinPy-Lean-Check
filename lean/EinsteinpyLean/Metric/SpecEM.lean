import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import EinsteinpyLean.Metric.SpecMetric

/-!
# The Kerr-Newman potential and field tensor

`kerrnewman.py:376-496`. The potential `A` and the tensor `F` are in geometrized units with `x^0 = c t`
(see the comment at `kerrnewman.py:343-347`). `F = dA`, `F_{ab} = d_a A_b - d_b A_a`, is the definition in Physlib's
`Physlib/Electromagnetism/Kinematics/FieldStrength.lean` (not in the prebuilt cache, so the formula is restated).

Here `rQ` is the geometrized charge `Q sqrt(G Cc) / c^2` and `al` the rotational length. The potential does not depend
on `t` and `phi`, so only the `r` and `theta` derivatives of `A_0` and `A_3` appear.
-/

open Real

namespace EinsteinpyLean.Metric.Spec

/-- kerrnewman.py:398-399 `A[0]`. -/
noncomputable def potT (rQ al r th : ℝ) : ℝ := r * rQ / sig r th al
/-- kerrnewman.py:400 `A[3]`. -/
noncomputable def potP (rQ al r th : ℝ) : ℝ := -r * al * rQ * sin th ^ 2 / sig r th al

/-- kerrnewman.py:487-494, with `rho2 = sig`, `drho2_dr = 2 r`, `drho2_dtheta = -(alpha^2 sin 2 th)`. -/
noncomputable def f01 (rQ al r th : ℝ) : ℝ := -(rQ * (sig r th al - 2 * r * r)) / sig r th al ^ 2
noncomputable def f02 (rQ al r th : ℝ) : ℝ := (r * rQ * (-(al ^ 2 * sin (2 * th)))) / sig r th al ^ 2
noncomputable def f13 (rQ al r th : ℝ) : ℝ :=
  -(1 / sig r th al ^ 2) * (al * rQ * sin th ^ 2) * (sig r th al - 2 * r ^ 2)
noncomputable def f23 (rQ al r th : ℝ) : ℝ :=
  -((1 / sig r th al ^ 2) * (al * rQ * r * sin (2 * th)) * (sig r th al + (al * sin th) ^ 2))

/-- Derivative of `sigma` in `r`. -/
private theorem hasDerivAt_sig_r (al th r : ℝ) :
    HasDerivAt (fun r => sig r th al) (2 * r) r := by
  have := ((hasDerivAt_pow 2 r).add_const ((al * cos th) ^ 2))
  simpa [sig] using this

/-- Derivative of `sigma` in `theta`. -/
private theorem hasDerivAt_sig_th (al r th : ℝ) :
    HasDerivAt (fun th => sig r th al) (-(al ^ 2 * sin (2 * th))) th := by
  have h1 : HasDerivAt (fun th => al * cos th) (al * (-sin th)) th := (hasDerivAt_cos th).const_mul al
  have h2 := (h1.pow 2).const_add (r ^ 2)
  convert h2 using 1
  · simp [sig]
  · rw [sin_two_mul]; simp; ring

/-- PROP metric.kerrnewman.potential.field_is_exterior_derivative : PROVEN
Source: kerrnewman.py:376-496 `em_potential_covariant`, `em_tensor_covariant`, and `F_{ab} = d_a A_b - d_b A_a`
(Physlib `FieldStrength`). The four independent components of `em_tensor_covariant` are the derivatives of the
potential: `F_01 = - d_r A_0`, `F_02 = - d_th A_0`, `F_13 = d_r A_3`, `F_23 = d_th A_3`, for `sigma ≠ 0`. -/
theorem field_is_dA (rQ al r th : ℝ) (hs : sig r th al ≠ 0) :
    HasDerivAt (fun r => potT rQ al r th) (-f01 rQ al r th) r ∧
    HasDerivAt (fun th => potT rQ al r th) (-f02 rQ al r th) th ∧
    HasDerivAt (fun r => potP rQ al r th) (f13 rQ al r th) r ∧
    HasDerivAt (fun th => potP rQ al r th) (f23 rQ al r th) th := by
  have hr := hasDerivAt_sig_r al th r
  have ht := hasDerivAt_sig_th al r th
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := ((hasDerivAt_id r).mul_const rQ).div hr hs
    refine this.congr_deriv ?_
    simp only [f01, id]
    field_simp
  · have := ((hasDerivAt_const th (r * rQ)).div ht hs)
    refine this.congr_deriv ?_
    simp only [f02]
    field_simp
    ring
  · have := ((((hasDerivAt_id r).neg.mul_const al).mul_const rQ).mul_const (sin th ^ 2)).div hr hs
    refine this.congr_deriv ?_
    simp only [f13, id, Pi.neg_apply]
    field_simp
    ring
  · have h3 : HasDerivAt (fun th => sin th ^ 2) (2 * sin th * cos th) th := by
      have := (hasDerivAt_sin th).pow 2
      refine this.congr_deriv ?_
      simp
    have := (h3.const_mul (-r * al * rQ)).div ht hs
    refine this.congr_deriv ?_
    simp only [f23]
    rw [sin_two_mul]
    field_simp
    ring

/-- The antisymmetric tensor with the six entries that `em_tensor_covariant` stores (kerrnewman.py:487-494). -/
noncomputable def fTensor (rQ al r th : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, f01 rQ al r th, f02 rQ al r th, 0],
    ![-f01 rQ al r th, 0, 0, f13 rQ al r th],
    ![-f02 rQ al r th, 0, 0, f23 rQ al r th],
    ![0, -f13 rQ al r th, -f23 rQ al r th, 0]]

/-- PROP metric.kerrnewman.em_tensor_covariant.antisymmetric : PROVEN
Source: kerrnewman.py:487-494. The stored tensor satisfies `F_{ab} = - F_{ba}`; the code writes `F[1, 0] = -F[0, 1]`
and so on. -/
theorem fTensor_antisymm (rQ al r th : ℝ) (a b : Fin 4) :
    fTensor rQ al r th a b = - fTensor rQ al r th b a := by
  fin_cases a <;> fin_cases b <;> simp [fTensor]

/-! ## The contravariant forms mix two time coordinates

`metric_covariant` is in the coordinate `t` (`g_tt = c^2 (...)`), while `em_potential_covariant` and `em_tensor_covariant`
use `x^0 = c t`. The two contravariant methods (kerrnewman.py:433-454 and 498-520) raise the indices with the inverse
metric of `t`, so the result is neither a tensor in `t` nor one in `c t`. For a Reissner-Nordstrom hole (`al = 0`) the
metric is diagonal, with `g_tt = c^2 f`, `g_rr = -1/f` and `f = Delta / r^2`, and the code's contravariant objects can be
written out. A Lorentz scalar such as `F_{ab} F^{ab}` or `A_a A^a` should not depend on `c`. -/

/-- With `al = 0`, `f01` is the Coulomb field `rQ / r^2`. -/
theorem f01_spin_zero (rQ r th : ℝ) (hr : r ≠ 0) : f01 rQ 0 r th = rQ / r ^ 2 := by
  simp only [f01, sig]
  field_simp
  ring

/-- `F_{ab} F^{ab}` from `em_tensor_covariant` and `em_tensor_contravariant` for `al = 0`: `2 F_01 F^01` with
`F^01 = g^tt F_01 g^rr`, `g^tt = 1 / (c^2 f)`, `g^rr = -f`. -/
noncomputable def rnInvCode (c rs rQ2 rQ r th : ℝ) : ℝ :=
  let f := del r rs 0 rQ2 / r ^ 2
  2 * f01 rQ 0 r th * ((1 / (c ^ 2 * f)) * f01 rQ 0 r th * (-f))

/-- `A_a A^a` from `em_potential_covariant` and `em_potential_contravariant` for `al = 0`: `g^tt A_0 A_0`. -/
noncomputable def rnPotCode (c rs rQ2 rQ r th : ℝ) : ℝ :=
  let f := del r rs 0 rQ2 / r ^ 2
  potT rQ 0 r th * ((1 / (c ^ 2 * f)) * potT rQ 0 r th)

/-- PROP metric.kerrnewman.em_tensor_contravariant.invariant : REFUTED
Source: kerrnewman.py:498-520 and the Lorentz scalar `F_{ab} F^{ab} = -2 E^2`, which does not depend on the units of the
time coordinate. For a Reissner-Nordstrom hole the field is `E = rQ / r^2`, and the code's value is `-2 E^2 / c^2`.
Here `c = 2`, `r = 1`, `rQ = 1`, `rs = 0`, `rQ2 = 0`: the code gives `-1/2`, the scalar is `-2`. -/
theorem em_tensor_contravariant_invariant_wrong :
    ¬ ∀ (c rs rQ2 rQ r th : ℝ), r ≠ 0 → del r rs 0 rQ2 ≠ 0 →
      rnInvCode c rs rQ2 rQ r th = -2 * (rQ / r ^ 2) ^ 2 := by
  intro h
  have := h 2 0 0 1 1 0 one_ne_zero (by simp [del])
  norm_num [rnInvCode, f01, sig, del] at this

/-- PROP metric.kerrnewman.em_potential_contravariant.invariant : REFUTED
Source: kerrnewman.py:433-454 and the Lorentz scalar `A_a A^a`. With `al = 0` the code gives `A_0^2 / (c^2 f)` while the
scalar in the coordinate `c t` (where `A_0` lives) is `A_0^2 / f`. Here `c = 2`, `r = 1`, `rQ = 1`, `rs = 0`, `rQ2 = 0`
(`f = 1`, `A_0 = 1`): the code gives `1/4`, the scalar is `1`. -/
theorem em_potential_contravariant_invariant_wrong :
    ¬ ∀ (c rs rQ2 rQ r th : ℝ), r ≠ 0 → del r rs 0 rQ2 ≠ 0 →
      rnPotCode c rs rQ2 rQ r th = potT rQ 0 r th ^ 2 / (del r rs 0 rQ2 / r ^ 2) := by
  intro h
  have := h 2 0 0 1 1 0 one_ne_zero (by simp [del])
  norm_num [rnPotCode, potT, sig, del] at this

end EinsteinpyLean.Metric.Spec
