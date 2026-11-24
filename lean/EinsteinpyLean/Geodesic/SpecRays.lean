import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The shadow and the embedding over the reals

`rays/shadow.py` computes the shadow of a Schwarzschild black hole from light rays with impact parameter `b`.
The turning point `r_tp` of a ray solves `r / sqrt (1 - 2 M / r) = b` (`_root_equation`), and the critical
impact parameter is `b_crit = 3 sqrt 3 M`. This file proves the closed forms: the left side of the root equation
has its minimum `3 sqrt 3 M` exactly at the photon sphere `r = 3 M`.

`hypersurface/schwarzschildembedding.py` embeds the optical geometry of the Schwarzschild solution,
`dr² / f² + r² dφ² / f` with `f = 1 - 2 M / r`, whose circumference radius is `R = r / sqrt f`. The class says the
embedding "breaks at `r < 9 m / 4`", which is the radicand `4 M r - 9 M²` of the slope `dz/dr`. The slope
that the isometry `dR² + dz² = dr² / f²` requires is derived here, the code's `gradient` is shown to be that
slope times an extra factor `sqrt R`, and the Flamm paraboloid of the spatial slice (a different surface, which
the module does not contain) is checked for comparison.

Physlib has no Schwarzschild exterior geodesics or embeddings. Its `PhyslibAlpha` has the interior solution, and
`Spec.lean` connects the metric functions to its exterior coefficients.
-/

open Real

namespace EinsteinpyLean.Geodesic.SpecRays

/-! ## The impact parameter of a turning point -/

/-- shadow.py:46-51: the left side of the root equation, `r / sqrt (1 - 2 M / r)`. -/
noncomputable def impact (M r : ℝ) : ℝ := r / √(1 - 2 * M / r)

theorem one_sub_pos {M r : ℝ} (h : 2 * M < r) (hM : 0 < M) : 0 < 1 - 2 * M / r := by
  have hr : 0 < r := by linarith
  rw [sub_pos, div_lt_one hr]
  exact h

theorem impact_pos {M r : ℝ} (hM : 0 < M) (h : 2 * M < r) : 0 < impact M r := by
  have hr : 0 < r := by linarith
  unfold impact
  exact div_pos hr (Real.sqrt_pos.mpr (one_sub_pos h hM))

theorem impact_sq {M r : ℝ} (hM : 0 < M) (h : 2 * M < r) : impact M r ^ 2 = r ^ 3 / (r - 2 * M) := by
  have hr : 0 < r := by linarith
  have hf := one_sub_pos h hM
  unfold impact
  rw [div_pow, Real.sq_sqrt hf.le]
  have : r - 2 * M ≠ 0 := by linarith
  field_simp

/-- `3 sqrt 3 M`, the critical impact parameter `b_crit` of shadow.py:17. -/
noncomputable def bCrit (M : ℝ) : ℝ := 3 * √3 * M

theorem bCrit_sq (M : ℝ) : bCrit M ^ 2 = 27 * M ^ 2 := by
  unfold bCrit
  have : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  calc (3 * √3 * M) ^ 2 = 9 * √(3 : ℝ) ^ 2 * M ^ 2 := by ring
    _ = 27 * M ^ 2 := by rw [this]; ring

/-- PROP geodesic.shadow.b_crit_minimum : PROVEN
Source: rays/shadow.py:17 `b_crit = 3 * np.sqrt(3) * self.mass`, and the physics of the Schwarzschild shadow
(Bambi, PRD 87, 107501): `b² = r³ / (r - 2M)` is minimal at the photon sphere `r = 3M` with value `27 M²`. For
every `r > 2M` the left side of the root equation is at least `3 sqrt 3 M`, with the factorisation
`r³ - 27 M² (r - 2M) = (r - 3M)² (r + 6M)`. -/
theorem impact_ge_bCrit {M r : ℝ} (hM : 0 < M) (h : 2 * M < r) : bCrit M ≤ impact M r := by
  have hpos := impact_pos hM h
  have hsq : bCrit M ^ 2 ≤ impact M r ^ 2 := by
    rw [bCrit_sq, impact_sq hM h, le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sq_nonneg (r - 3 * M)) (by linarith : 0 ≤ r + 6 * M)]
  have hb : 0 ≤ bCrit M := by unfold bCrit; positivity
  calc bCrit M = √(bCrit M ^ 2) := (Real.sqrt_sq hb).symm
    _ ≤ √(impact M r ^ 2) := Real.sqrt_le_sqrt hsq
    _ = impact M r := Real.sqrt_sq hpos.le

/-- PROP geodesic.shadow.photon_sphere : PROVEN
Source: as above. The value `3 sqrt 3 M` is attained at `r = 3 M` and only there: the photon sphere radius is
`3 M`. -/
theorem impact_eq_bCrit_iff {M r : ℝ} (hM : 0 < M) (h : 2 * M < r) : impact M r = bCrit M ↔ r = 3 * M := by
  have hb : 0 ≤ bCrit M := by unfold bCrit; positivity
  have key : impact M r = bCrit M ↔ impact M r ^ 2 = bCrit M ^ 2 :=
    (pow_left_inj₀ (impact_pos hM h).le hb two_ne_zero).symm
  rw [key, impact_sq hM h, bCrit_sq]
  have hr : r - 2 * M ≠ 0 := by linarith
  have hr' : 0 < r - 2 * M := by linarith
  rw [div_eq_iff hr]
  constructor
  · intro e
    have h0 : (r - 3 * M) ^ 2 * (r + 6 * M) = 0 := by nlinarith [e]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      linarith
    · linarith
  · intro e
    subst e
    ring

/-- PROP geodesic.shadow.no_root_below_b_crit : PROVEN
Source: shadow.py:46-51 and `_compute_B` (starting at `b_crit`). No turning point exists for `b < b_crit`:
the root equation has no solution outside the horizon. -/
theorem no_turning_point_below_bCrit {M r b : ℝ} (hM : 0 < M) (h : 2 * M < r) (hb : b < bCrit M) :
    impact M r ≠ b := by
  intro e
  have := impact_ge_bCrit hM h
  linarith

/-- PROP geodesic.shadow.radicand : PROVEN
Source: shadow.py:55-76. The square root `KRKText` of the integrands has the radicand
`(GTT / GRR) (1 - b² GTT / r²)` with `GTT = 1 - 2M/r` and `GRR = 1 / GTT`. Its second factor is
`1 - b² / impact(r)²`, so it is nonnegative exactly where the ray with impact parameter `b ≥ 0` can be:
`b ≤ r / sqrt (1 - 2M/r)`. -/
theorem radicand_nonneg_iff {M r b : ℝ} (hM : 0 < M) (h : 2 * M < r) (hb : 0 ≤ b) :
    0 ≤ 1 - b ^ 2 * (1 - 2 * M / r) / r ^ 2 ↔ b ≤ impact M r := by
  have hr : 0 < r := by linarith
  have hf := one_sub_pos h hM
  have hI := impact_pos hM h
  have hI2 : impact M r ^ 2 = r ^ 2 / (1 - 2 * M / r) := by
    unfold impact
    rw [div_pow, Real.sq_sqrt hf.le]
  have e : 1 - b ^ 2 * (1 - 2 * M / r) / r ^ 2 = 1 - b ^ 2 / impact M r ^ 2 := by
    rw [hI2]
    field_simp
  rw [e, sub_nonneg, div_le_one (by positivity), sq_le_sq₀ hb hI.le]

/-! ## The embedding -/

/-- schwarzschildembedding.py:70-92 `gradient`, over the reals: the code's `num_one * num_two / deno` with
`R = r / sqrt (1 - 2M/r)`. -/
noncomputable def codeGrad (M r : ℝ) : ℝ :=
  (1 - 3 * M / r) * √(((4 * M * r - 9 * M * M) * (r / √(1 - 2 * M / r))) / (r - 3 * M) ^ 2) /
    √(1 - 2 * M / r) ^ 3

/-- The slope `dz/dr` of an isometric embedding of the optical geometry in Euclidean space. -/
noncomputable def optSlope (M r : ℝ) : ℝ := √(4 * M * r - 9 * M * M) / (r * √(1 - 2 * M / r) ^ 3)

theorem four_Mr_pos {M r : ℝ} (hM : 0 < M) (h : 3 * M < r) : 0 < 4 * M * r - 9 * M * M := by
  nlinarith

/-- PROP geodesic.embedding.gradient_factor : PROVEN
Source: schwarzschildembedding.py:70-92. For `r > 3M` the code's gradient is the slope of the optical
geometry times `sqrt R`, where `R = r / sqrt (1 - 2M/r)` is the radius of the embedding (a length). -/
theorem codeGrad_eq {M r : ℝ} (hM : 0 < M) (h : 3 * M < r) :
    codeGrad M r = √(impact M r) * optSlope M r := by
  have hr : 0 < r := by linarith
  have hf := one_sub_pos (by linarith : 2 * M < r) hM
  have hs : 0 < √(1 - 2 * M / r) := Real.sqrt_pos.mpr hf
  have hX := four_Mr_pos hM h
  have hR : 0 < impact M r := impact_pos hM (by linarith)
  have hd : 0 < r - 3 * M := by linarith
  have e1 : √(((4 * M * r - 9 * M * M) * (r / √(1 - 2 * M / r))) / (r - 3 * M) ^ 2) =
      √(4 * M * r - 9 * M * M) * √(impact M r) / (r - 3 * M) := by
    have : r / √(1 - 2 * M / r) = impact M r := rfl
    rw [this, Real.sqrt_div (mul_pos hX hR).le, Real.sqrt_mul hX.le, Real.sqrt_sq hd.le]
  rw [codeGrad, optSlope, e1]
  have e2 : 1 - 3 * M / r = (r - 3 * M) / r := by field_simp
  rw [e2]
  field_simp

theorem codeGrad_pos {M r : ℝ} (hM : 0 < M) (h : 3 * M < r) : 0 < codeGrad M r := by
  rw [codeGrad_eq hM h]
  have hr : 0 < r := by linarith
  have hf := one_sub_pos (by linarith : 2 * M < r) hM
  have hX := four_Mr_pos hM h
  have hR : 0 < impact M r := impact_pos hM (by linarith)
  unfold optSlope
  have hs : 0 < √(1 - 2 * M / r) := Real.sqrt_pos.mpr hf
  positivity

theorem impact_scale {M r l : ℝ} (hl : 0 < l) : impact (l * M) (l * r) = l * impact M r := by
  unfold impact
  have : 1 - 2 * (l * M) / (l * r) = 1 - 2 * M / r := by
    rw [show 2 * (l * M) = l * (2 * M) by ring, mul_div_mul_left _ _ hl.ne']
  rw [this]
  ring

theorem optSlope_scale {M r l : ℝ} (hl : 0 < l) (hM : 0 < M) (h : 3 * M < r) :
    optSlope (l * M) (l * r) = optSlope M r := by
  unfold optSlope
  have e : 1 - 2 * (l * M) / (l * r) = 1 - 2 * M / r := by
    rw [show 2 * (l * M) = l * (2 * M) by ring, mul_div_mul_left _ _ hl.ne']
  have hX := four_Mr_pos hM h
  have e2 : 4 * (l * M) * (l * r) - 9 * (l * M) * (l * M) = l ^ 2 * (4 * M * r - 9 * M * M) := by ring
  rw [e, e2, Real.sqrt_mul (by positivity), Real.sqrt_sq hl.le]
  have hr : 0 < r := by linarith
  have hf := one_sub_pos (by linarith : 2 * M < r) hM
  have hs : 0 < √(1 - 2 * M / r) := Real.sqrt_pos.mpr hf
  field_simp

/-- PROP geodesic.embedding.gradient_scaling : PROVEN
Source: as above. Scaling `M` and `r` by `l > 0` (a change of the unit of length) multiplies the code's gradient by
`sqrt l`. -/
theorem codeGrad_scale {M r l : ℝ} (hl : 0 < l) (hM : 0 < M) (h : 3 * M < r) :
    codeGrad (l * M) (l * r) = √l * codeGrad M r := by
  rw [codeGrad_eq (by positivity) (by nlinarith), codeGrad_eq hM h, impact_scale hl, optSlope_scale hl hM h,
    Real.sqrt_mul hl.le]
  ring

/-- PROP geodesic.embedding.gradient_dimensionless : REFUTED
Source: a slope `dz/dr` is dimensionless, so it must not change when `M` and `r` are measured in another unit
of length. The code's gradient at `(4 M, 4 r)` is twice its value at `(M, r)` (`M = 1`, `r = 4`). -/
theorem codeGrad_not_scale_invariant :
    ¬ (∀ M r l : ℝ, 0 < M → 3 * M < r → 0 < l → codeGrad (l * M) (l * r) = codeGrad M r) := by
  intro hall
  have h := hall 1 4 4 one_pos (by norm_num) (by norm_num)
  rw [codeGrad_scale (by norm_num) one_pos (by norm_num)] at h
  have hp := codeGrad_pos (M := 1) (r := 4) one_pos (by norm_num)
  have h2 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h2] at h
  linarith

/-- The derivative of the radius `R(r) = r / sqrt (1 - 2M/r)` of the embedding. -/
theorem hasDerivAt_impact {M r : ℝ} (hM : 0 < M) (h : 2 * M < r) :
    HasDerivAt (fun x => x / √(1 - 2 * M / x)) ((r - 3 * M) / (r * √(1 - 2 * M / r) ^ 3)) r := by
  have hr : 0 < r := by linarith
  have hf := one_sub_pos h hM
  have hs : 0 < √(1 - 2 * M / r) := Real.sqrt_pos.mpr hf
  have c1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 r := hasDerivAt_const r (1 : ℝ)
  have c2 : HasDerivAt (fun _ : ℝ => 2 * M) 0 r := hasDerivAt_const r (2 * M)
  have i1 : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id' r
  have d1 : HasDerivAt (fun x : ℝ => 2 * M / x) ((0 * r - 2 * M * 1) / r ^ 2) r := HasDerivAt.div c2 i1 hr.ne'
  have hg0 : HasDerivAt (fun x : ℝ => 1 - 2 * M / x) (0 - (0 * r - 2 * M * 1) / r ^ 2) r := HasDerivAt.sub c1 d1
  have hg : HasDerivAt (fun x : ℝ => 1 - 2 * M / x) (2 * M / r ^ 2) r :=
    hg0.congr_deriv (by ring)
  have hq := hg.sqrt hf.ne'
  have h3 := HasDerivAt.div i1 hq hs.ne'
  refine h3.congr_deriv ?_
  have hs2 : √(1 - 2 * M / r) ^ 2 = 1 - 2 * M / r := Real.sq_sqrt hf.le
  generalize √(1 - 2 * M / r) = s at *
  have hM2 : M = r * (1 - s ^ 2) / 2 := by
    rw [hs2]; field_simp; ring
  subst hM2
  field_simp
  ring

/-- PROP geodesic.embedding.isometry : PROVEN
Source: the embedding condition `dR² + dz² = dr² / f²` for the optical geometry. With `dR/dr = (r - 3M) / (r f^(3/2))`
(`hasDerivAt_impact`), the slope `optSlope` satisfies it, so it is the gradient that `SchwarzschildEmbedding.gradient`
should return. The code's value is `sqrt R` times too large (`codeGrad_eq`). -/
theorem optSlope_isometry {M r : ℝ} (hM : 0 < M) (h : 3 * M < r) :
    ((r - 3 * M) / (r * √(1 - 2 * M / r) ^ 3)) ^ 2 + optSlope M r ^ 2 = 1 / (1 - 2 * M / r) ^ 2 := by
  have hr : 0 < r := by linarith
  have hf := one_sub_pos (by linarith : 2 * M < r) hM
  have hs : 0 < √(1 - 2 * M / r) := Real.sqrt_pos.mpr hf
  have hX := four_Mr_pos hM h
  have hs2 : √(1 - 2 * M / r) ^ 2 = 1 - 2 * M / r := Real.sq_sqrt hf.le
  have hX2 : √(4 * M * r - 9 * M * M) ^ 2 = 4 * M * r - 9 * M * M := Real.sq_sqrt hX.le
  unfold optSlope
  have e3 : (√(1 - 2 * M / r) ^ 3) ^ 2 = (1 - 2 * M / r) ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, hs2]
  simp only [div_pow, mul_pow, hX2, e3]
  have hf0 : 1 - 2 * M / r ≠ 0 := hf.ne'
  have hrr : r ≠ 0 := hr.ne'
  have hnum : (r - 3 * M) ^ 2 + (4 * M * r - 9 * M * M) = r ^ 2 * (1 - 2 * M / r) := by
    field_simp
    ring
  rw [← add_div, hnum]
  field_simp

/-! ## The Flamm paraboloid, for comparison -/

/-- The Flamm paraboloid `z(r) = 2 sqrt (rs (r - rs))`, the embedding of the spatial slice `t = const` of
Schwarzschild, with `rs = 2M`. -/
noncomputable def flamm (rs r : ℝ) : ℝ := 2 * √(rs * (r - rs))

/-- PROP geodesic.embedding.flamm_slope : PROVEN
Source: the task of `hypersurface/`, "Schwarzschild Embedding". The slope of the Flamm paraboloid is
`rs / sqrt (rs (r - rs))`, and `1 + z'² = 1 / (1 - rs/r)`, the radial metric of the slice: the factor 2 and the
units (`rs = 2M`) are right. The module does not contain this surface, it embeds the optical geometry (`impact`,
`optSlope`). -/
theorem flamm_slope {rs r : ℝ} (hrs : 0 < rs) (h : rs < r) :
    HasDerivAt (flamm rs) (rs / √(rs * (r - rs))) r ∧
    1 + (rs / √(rs * (r - rs))) ^ 2 = 1 / (1 - rs / r) := by
  have hp : 0 < rs * (r - rs) := mul_pos hrs (by linarith)
  have hr : 0 < r := by linarith
  constructor
  · have i1 : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id' r
    have i2 : HasDerivAt (fun x : ℝ => x - rs) 1 r := HasDerivAt.sub_const rs i1
    have h1 : HasDerivAt (fun x : ℝ => rs * (x - rs)) rs r := by
      simpa using HasDerivAt.const_mul rs i2
    have := (h1.sqrt hp.ne').const_mul 2
    unfold flamm
    convert this using 1
    field_simp
  · rw [div_pow, Real.sq_sqrt hp.le]
    have : r - rs ≠ 0 := by linarith
    have : 1 - rs / r ≠ 0 := by
      rw [sub_ne_zero, ne_comm]
      exact (div_lt_one hr |>.mpr h).ne
    field_simp
    ring

/-- PROP geodesic.embedding.no_embedding_inside : PROVEN
Source: the class docstring, "the embedding breaks at r < 9m/4" for the optical geometry, and the same for the
Flamm paraboloid at `r < rs`: the squared slope `rs / (r - rs)` is negative for `0 < r < rs`, so no real slope exists. -/
theorem no_flamm_slope_inside {rs r : ℝ} (hrs : 0 < rs) (h : r < rs) :
    ¬ ∃ w : ℝ, w ^ 2 = rs / (r - rs) := by
  rintro ⟨w, hw⟩
  have : rs / (r - rs) < 0 := div_neg_of_pos_of_neg hrs (by linarith)
  nlinarith [sq_nonneg w]

end EinsteinpyLean.Geodesic.SpecRays
