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
    try ring
  · have := ((hasDerivAt_const th (r * rQ)).div ht hs)
    refine this.congr_deriv ?_
    simp only [f02]
    field_simp
    ring
  · have := ((((hasDerivAt_id r).neg.mul_const al).mul_const rQ).mul_const (sin th ^ 2)).div hr hs
    refine this.congr_deriv ?_
    simp only [f13, id, Pi.neg_apply]
    field_simp
    try ring
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

end EinsteinpyLean.Metric.Spec
