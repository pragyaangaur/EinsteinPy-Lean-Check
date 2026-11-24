import Physlib.Relativity.MinkowskiMatrix
import Physlib.Cosmology.FLRW.DeSitter

/-!
# The predefined metrics against Physlib

Three comparisons with Physlib, all over the reals.

1. Signature. Physlib's `minkowskiMatrix` is `diag(1, -1, ..., -1)`. einsteinpy's Minkowski
   metric is `diag(-1, 1/c^2, ...)` and so has the opposite signature, while its Schwarzschild
   family (`vacuum_solutions.py`) is `(+, -, -, -)` like Physlib.
2. Schwarzschild. `PhyslibAlpha/Relativity/General/Schwarzschild/IncompressibleSphere.lean`
   (lines 331 and 334, not in the prebuilt cache, so the two formulas are restated here) has
   exterior `g_tt = 1 - r_s / r` and `g_rr = 1 / (1 - r_s / r)`.
3. Cosmology. `Physlib.Cosmology.FLRW` has the Friedmann equations, the de Sitter scale factor
   and the spatial geometry with its curvature `K`.

What is not stated here: Ricci flatness of Schwarzschild, Kerr and Bessel, `R_ab = Lambda g_ab`
for de Sitter, and the Einstein-Maxwell equations for Kerr-Newman, Reissner-Nordstrom,
Kerr-Newman-de Sitter and Ernst. Neither Mathlib nor Physlib has a Ricci tensor for a metric
given by components, so those were checked numerically in einsteinpy at 40 digits (the
scripts are `bugs/repro/predefined-*.py`) and are not Lean theorems.
-/

open Matrix minkowskiMatrix Cosmology Cosmology.FLRW.FriedmannEquation

namespace EinsteinpyLean.Predefined.Spec

variable {d : ℕ}

/-! ### Signature -/

/-- einsteinpy `MinkowskiCartesian(c = 1)` in `1 + d` dimensions (minkowski.py:19). -/
def epMinkowski : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ := diagonal (Sum.elim (-1) 1)

/-- PROP predefined.minkowski.is_minus_eta : PROVEN
Source: Physlib `minkowskiMatrix` (`diag(1, -1, ..., -1)`) and minkowski.py:19. einsteinpy's
Minkowski metric at `c = 1` is exactly `-η`. -/
theorem epMinkowski_eq_neg_eta : (epMinkowski : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) = -η := by
  rw [epMinkowski, as_diagonal]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [diagonal_apply] <;> split_ifs <;> simp

/-- PROP predefined.minkowski.equals_eta : REFUTED
Source: Physlib `minkowskiMatrix` and minkowski.py:19. One might expect einsteinpy's flat
metric to be Physlib's `η`. It is `-η`, so for `d = 3` it is different. -/
theorem epMinkowski_ne_eta : (epMinkowski : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) ≠ η := by
  intro h
  have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
  simp [epMinkowski] at this
  norm_num at this

/-! ### Schwarzschild -/

/-- einsteinpy `Schwarzschild` time-time component (vacuum_solutions.py:24-26). -/
noncomputable def epSchwTT (sch r : ℝ) : ℝ := 1 - sch / r

/-- einsteinpy `Schwarzschild` radial component (vacuum_solutions.py:26). -/
noncomputable def epSchwRR (c sch r : ℝ) : ℝ := -1 / ((1 - sch / r) * c ^ 2)

/-- Physlib `Schwarzschild.gttOut` (PhyslibAlpha IncompressibleSphere.lean:331),
`rs` is `S.rs`. -/
noncomputable def gttOut (rs r : ℝ) : ℝ := 1 - rs / r

/-- Physlib `Schwarzschild.grrOut` (PhyslibAlpha IncompressibleSphere.lean:334). -/
noncomputable def grrOut (rs r : ℝ) : ℝ := 1 / (1 - rs / r)

/-- PROP predefined.schwarzschild.matches_physlib_exterior : PROVEN
Source: PhyslibAlpha IncompressibleSphere.lean:331-334 (restated). einsteinpy's `g_tt` is
Physlib's `gttOut`, and at `c = 1` its `g_rr` is `-grrOut`: the same metric with the
opposite sign convention for the spatial part, which is Physlib's `(+, -, -, -)` as a
whole. -/
theorem schwarzschild_matches_physlib (sch r : ℝ) :
    epSchwTT sch r = gttOut sch r ∧ epSchwRR 1 sch r = -grrOut sch r := by
  refine ⟨rfl, ?_⟩
  simp [epSchwRR, grrOut, neg_div]

/-- PROP predefined.schwarzschild.flat_limit_is_eta : PROVEN
Source: Physlib `minkowskiMatrix` and vacuum_solutions.py:24-26. With `r_s = 0` and `c = 1`
the time and radial entries are those of Physlib's `η`. -/
theorem schwarzschild_flat_limit (r : ℝ) :
    epSchwTT 0 r = (η : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) (Sum.inl 0) (Sum.inl 0) ∧
    epSchwRR 1 0 r = (η : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) (Sum.inr 0) (Sum.inr 0) := by
  constructor <;> simp [epSchwTT, epSchwRR]

/-! ### de Sitter -/

/-- The speed of light equal to one. -/
def cOne : SpeedOfLight := ⟨1, one_pos⟩

/-- PROP predefined.de_sitter.scale_factor_squared : PROVEN
Source: Physlib `deSitterScaleFactor` (`a(t) = a₀ exp(σ √(Λ/3) c t)`) and de_sitter.py:47-48.
With `a₀ = 1`, `σ = 1`, `c = 1` and `Λ = 3 / α²` the square of Physlib's scale factor is
einsteinpy's `exp(2 t / α)`, the coefficient of `dx²`, `dy²`, `dz²`. -/
theorem deSitter_scale_factor_sq (α : ℝ) (hα : 0 < α) (t : Time) :
    (deSitterScaleFactor 1 1 (3 / α ^ 2) cOne t) ^ 2 = Real.exp (2 * t.val / α) := by
  have hs : √(3 / α ^ 2 / 3) = 1 / α := by
    rw [show 3 / α ^ 2 / 3 = (1 / α) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  simp only [deSitterScaleFactor, hs, one_mul, ← Real.exp_nat_mul]
  congr 1
  simp [cOne]
  field_simp

/-- PROP predefined.de_sitter.solves_friedmann : PROVEN
Source: Physlib `deSitterScaleFactor_firstOrderFriedmann`. The scale factor of einsteinpy's
`DeSitter` solves the first-order Friedmann equation with no matter, flat slices and
`Λ = 3 / α²`. Together with `R_ab = (3 / α²) g_ab`, which einsteinpy confirms (checked with
its Ricci tensor), this fixes the meaning of the parameter `α`. -/
theorem deSitter_friedmann (α G : ℝ) (hα : 0 < α) (t : Time) :
    FirstOrderFriedmann (deSitterScaleFactor 1 1 (3 / α ^ 2) cOne) (fun _ => 0) 0
      (3 / α ^ 2) G cOne t :=
  deSitterScaleFactor_firstOrderFriedmann (by positivity) one_ne_zero (Or.inl rfl) t

/-! ### FLRW spatial part -/

/-- einsteinpy FLRW `g_rr = a² / (1 - k r²)` (friedmann_lemaitre_robertson_walker.py:28). -/
noncomputable def epFlrwGrr (a k r : ℝ) : ℝ := a ^ 2 / (1 - k * r ^ 2)

/-- PROP predefined.flrw.radial_profile : PROVEN
Source: Physlib `SpatialGeometry.S` and `curvature`. In Physlib's radial coordinate `χ` the
profile `S` satisfies `(S')² = 1 - K S²`, which is what makes `dr² / (1 - K r²) = dχ²` for
`r = S χ`. So einsteinpy's `g_rr dr²` with `k = K` and `r = S χ` is `a² dχ²`. -/
theorem flrw_radial_profile (s : SpatialGeometry) (χ : ℝ) :
    (deriv s.S χ) ^ 2 = 1 - s.curvature * (s.S χ) ^ 2 := by
  cases s with
  | Flat =>
    have h : SpatialGeometry.Flat.S = fun r => r := rfl
    rw [h]
    simp [SpatialGeometry.curvature]
  | Spherical k h =>
    have hk : k ≠ 0 := h.ne
    have hd : HasDerivAt (SpatialGeometry.S (.Spherical k h)) (Real.cos (χ / k)) χ := by
      have := (((hasDerivAt_id χ).div_const k).sin).const_mul k
      have e : k * (Real.cos (χ / k) * (1 / k)) = Real.cos (χ / k) := by field_simp
      simp only [id] at this
      rw [e] at this
      exact this
    rw [hd.deriv]
    simp only [SpatialGeometry.S, SpatialGeometry.curvature]
    have e2 : -1 / k ^ 2 = -(1 / k ^ 2) := by ring
    have e3 : 1 / k ^ 2 * (k * Real.sin (χ / k)) ^ 2 = Real.sin (χ / k) ^ 2 := by
      field_simp
    rw [e3]
    linarith [Real.sin_sq_add_cos_sq (χ / k)]
  | Saddle k h =>
    have hk : k ≠ 0 := h.ne'
    have hd : HasDerivAt (SpatialGeometry.S (.Saddle k h)) (Real.cosh (χ / k)) χ := by
      have := (((hasDerivAt_id χ).div_const k).sinh).const_mul k
      have e : k * (Real.cosh (χ / k) * (1 / k)) = Real.cosh (χ / k) := by field_simp
      simp only [id] at this
      rw [e] at this
      exact this
    rw [hd.deriv]
    simp only [SpatialGeometry.S, SpatialGeometry.curvature]
    have e3 : -1 / k ^ 2 * (k * Real.sinh (χ / k)) ^ 2 = -Real.sinh (χ / k) ^ 2 := by
      field_simp
    rw [e3]
    linarith [Real.cosh_sq_sub_sinh_sq (χ / k)]

/-- PROP predefined.flrw.metric_is_physlib_geometry : PROVEN
Source: as above. In Physlib's coordinate, einsteinpy's `g_rr (dr/dχ)²` is `a²` whenever the
denominator `1 - K r²` does not vanish. -/
theorem flrw_grr_matches (s : SpatialGeometry) (a χ : ℝ)
    (h : 1 - s.curvature * (s.S χ) ^ 2 ≠ 0) :
    epFlrwGrr a s.curvature (s.S χ) * (deriv s.S χ) ^ 2 = a ^ 2 := by
  rw [flrw_radial_profile, epFlrwGrr]
  field_simp

end EinsteinpyLean.Predefined.Spec
