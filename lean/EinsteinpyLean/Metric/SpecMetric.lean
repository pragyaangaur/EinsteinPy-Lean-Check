import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Physlib.Relativity.MinkowskiMatrix

/-!
# The metric components against their definitions

The formulas of `schwarzschild.py`, `kerr.py`, `kerrnewman.py` and the helpers `sigma`, `delta` of `base_metric.py`
restated over the reals, with `c` the speed of light, `rs` the Schwarzschild radius, `al` the rotational length
`alpha = a G M / c^2` and `rQ2 = Q^2 G Cc / c^4` the squared geometrized charge.

The numerical code uses the signature `(+, -, -, -)` and the metric `ds^2 = c^2 d tau^2`, so its components are
`c^2` times those of `symbolic/predefined/vacuum_solutions.py`, which is also `(+, -, -, -)` (checked numerically in
`difftest/metric_symbolic_diff.py`). Physlib's `minkowskiMatrix` is `diag(1, -1, -1, -1)` as well.
-/

open Real Matrix minkowskiMatrix

namespace EinsteinpyLean.Metric.Spec

/-- base_metric.py:93-117 `sigma`. -/
noncomputable def sig (r th al : ℝ) : ℝ := r ^ 2 + (al * cos th) ^ 2

/-- base_metric.py:119-155 `delta`. -/
noncomputable def del (r rs al rQ2 : ℝ) : ℝ := r ^ 2 - rs * r + al ^ 2 + rQ2

/-! ## Schwarzschild (schwarzschild.py:63-81) -/

noncomputable def schwTT (c rs r : ℝ) : ℝ := (1 - rs / r) * c ^ 2
noncomputable def schwRR (rs r : ℝ) : ℝ := -1 / (1 - rs / r)
noncomputable def schwThTh (r : ℝ) : ℝ := -(r ^ 2)
noncomputable def schwPP (r th : ℝ) : ℝ := -((r * sin th) ^ 2)

/-! ## Kerr (kerr.py:101-130) -/

noncomputable def kerrTT (c rs al r th : ℝ) : ℝ := (1 - rs * r / sig r th al) * c ^ 2
noncomputable def kerrRR (rs al r th : ℝ) : ℝ := -(sig r th al / del r rs al 0)
noncomputable def kerrThTh (al r th : ℝ) : ℝ := -(sig r th al)
noncomputable def kerrPP (rs al r th : ℝ) : ℝ :=
  -(((r ^ 2) + al ^ 2 + (rs * r * (al * sin th) ^ 2 / sig r th al)) * sin th ^ 2)
noncomputable def kerrTP (c rs al r th : ℝ) : ℝ := c * rs * r * al * sin th ^ 2 / sig r th al

/-! ## Kerr-Newman (kerrnewman.py:146-181) -/

noncomputable def knTT (c rs al rQ2 r th : ℝ) : ℝ :=
  c ^ 2 * ((del r rs al rQ2 - (al * sin th) ^ 2) / sig r th al)
noncomputable def knRR (rs al rQ2 r th : ℝ) : ℝ := -sig r th al / del r rs al rQ2
noncomputable def knPP (rs al rQ2 r th : ℝ) : ℝ :=
  -(sin th ^ 2 * (((r ^ 2 + al ^ 2) ^ 2 - del r rs al rQ2 * (al * sin th) ^ 2) / sig r th al))
noncomputable def knTP (c rs al rQ2 r th : ℝ) : ℝ :=
  c * ((-al * sin th ^ 2 * (del r rs al rQ2 - r ^ 2 - al ^ 2)) / sig r th al)

/-- `cos^2 = 1 - sin^2`, used to turn the identities into polynomial ones. -/
private theorem sig_eq (r th al : ℝ) : sig r th al = r ^ 2 + al ^ 2 * (1 - sin th ^ 2) := by
  rw [sig, mul_pow, cos_sq' th]

/-- PROP metric.kerrnewman.charge_zero.is_kerr : PROVEN
Source: kerrnewman.py:146-181 against kerr.py:101-130. With `rQ2 = 0` the four distinct components of the
Kerr-Newman metric are those of the Kerr metric, when `sigma ≠ 0`. -/
theorem kn_charge_zero_is_kerr (c rs al r th : ℝ) (hs : sig r th al ≠ 0) :
    knTT c rs al 0 r th = kerrTT c rs al r th ∧ knRR rs al 0 r th = kerrRR rs al r th ∧
    knPP rs al 0 r th = kerrPP rs al r th ∧ knTP c rs al 0 r th = kerrTP c rs al r th := by
  have hs' := hs
  rw [sig_eq] at hs'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [knTT, kerrTT, del, add_zero, sig_eq]
    rw [sig_eq] at hs
    field_simp
    ring
  · simp only [knRR, kerrRR, neg_div]
  · simp only [knPP, kerrPP, del, add_zero, sig_eq]
    rw [sig_eq] at hs
    field_simp
    ring
  · simp only [knTP, kerrTP, del, add_zero, sig_eq]
    rw [sig_eq] at hs
    field_simp
    ring

/-- PROP metric.kerr.spin_zero.is_schwarzschild : PROVEN
Source: kerr.py:101-130 against schwarzschild.py:63-81. With `alpha = 0`, and `r ≠ 0`, `r ≠ rs` so nothing
divides by zero, the Kerr components are the Schwarzschild components and `g_{t phi} = 0`. -/
theorem kerr_spin_zero_is_schwarzschild (c rs r th : ℝ) (hr : r ≠ 0) (hrs : r - rs ≠ 0) :
    kerrTT c rs 0 r th = schwTT c rs r ∧ kerrRR rs 0 r th = schwRR rs r ∧ kerrThTh 0 r th = schwThTh r ∧
    kerrPP rs 0 r th = schwPP r th ∧ kerrTP c rs 0 r th = 0 := by
  have h1 : (1 - rs / r) ≠ 0 := by
    intro h
    apply hrs
    field_simp at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [kerrTT, schwTT, sig]
    field_simp
    ring
  · simp only [kerrRR, schwRR, sig, del]
    field_simp
    ring
  · simp [kerrThTh, schwThTh, sig]
  · simp only [kerrPP, schwPP, sig]
    field_simp
    ring
  · simp [kerrTP]

/-- Horizons: base_metric.py:276-285 `singularities`. -/
noncomputable def rHor (rs al rQ2 : ℝ) (s : ℝ) : ℝ := (rs + s * Real.sqrt (rs ^ 2 - 4 * al ^ 2 - 4 * rQ2)) / 2

/-- PROP metric.singularities.horizons_are_roots_of_delta : PROVEN
Source: base_metric.py:276-285 against `delta` (base_metric.py:119-155). When the discriminant is not negative,
`inner_horizon` and `outer_horizon` (`s = -1` and `s = 1`) are the roots of `Delta = r^2 - rs r + alpha^2 + rQ^2`. -/
theorem horizons_are_roots (rs al rQ2 : ℝ) (h : 0 ≤ rs ^ 2 - 4 * al ^ 2 - 4 * rQ2) (s : ℝ) (hs : s ^ 2 = 1) :
    del (rHor rs al rQ2 s) rs al rQ2 = 0 := by
  have h2 := Real.sq_sqrt h
  unfold del rHor
  have : (rs + s * Real.sqrt (rs ^ 2 - 4 * al ^ 2 - 4 * rQ2)) ^ 2 =
      rs ^ 2 + 2 * rs * s * Real.sqrt (rs ^ 2 - 4 * al ^ 2 - 4 * rQ2) + s ^ 2 * (rs ^ 2 - 4 * al ^ 2 - 4 * rQ2) := by
    rw [add_sq, mul_pow, h2]; ring
  nlinarith [this, hs, h2]

/-- Ergospheres: base_metric.py:262-274, `(rs ± sqrt(rs^2 - 4 (alpha cos th)^2 - 4 rQ2)) / 2`. -/
noncomputable def rErgo (rs al rQ2 th s : ℝ) : ℝ :=
  (rs + s * Real.sqrt (rs ^ 2 - 4 * (al * cos th) ^ 2 - 4 * rQ2)) / 2

/-- PROP metric.singularities.ergosphere_is_where_gtt_vanishes : PROVEN
Source: base_metric.py:262-274 `_in_ergo`, `_out_ergo` against kerrnewman.py:146-181 `g_tt`. At the radius they
return, when the discriminant is not negative and `sigma ≠ 0`, the Kerr-Newman `g_tt` is zero. -/
theorem ergosphere_gtt_zero (c rs al rQ2 th s : ℝ) (h : 0 ≤ rs ^ 2 - 4 * (al * cos th) ^ 2 - 4 * rQ2)
    (hs : s ^ 2 = 1) :
    knTT c rs al rQ2 (rErgo rs al rQ2 th s) th = 0 := by
  have h2 := Real.sq_sqrt h
  have hc : (al * sin th) ^ 2 = al ^ 2 - (al * cos th) ^ 2 := by
    have := sin_sq_add_cos_sq th
    nlinarith [this]
  have num : del (rErgo rs al rQ2 th s) rs al rQ2 - (al * sin th) ^ 2 = 0 := by
    unfold del rErgo
    set q := Real.sqrt (rs ^ 2 - 4 * (al * cos th) ^ 2 - 4 * rQ2) with hq
    linear_combination (1 / 4 * q ^ 2) * hs + (1 / 4) * h2 - hc
  unfold knTT
  rw [num]
  simp

/-- PROP metric.kerr.block_determinant : PROVEN
Source: kerrnewman.py:146-181. The `(t, phi)` block of the Kerr-Newman metric has determinant
`-c^2 Delta sin^2 th`, for `sigma ≠ 0`. With `g_rr = -sigma/Delta` and `g_th_th = -sigma` the full determinant is
`-c^2 sigma^2 sin^2 th`, negative outside the horizons, so the signature is `(+, -, -, -)`. -/
theorem block_determinant (c rs al rQ2 r th : ℝ) (hs : sig r th al ≠ 0) :
    knTT c rs al rQ2 r th * knPP rs al rQ2 r th - knTP c rs al rQ2 r th ^ 2
      = -(c ^ 2 * del r rs al rQ2 * sin th ^ 2) := by
  rw [sig_eq] at hs
  simp only [knTT, knPP, knTP, sig_eq]
  field_simp
  ring

/-- PROP metric.schwarzschild.signature_matches_physlib : PROVEN
Source: Physlib `minkowskiMatrix` (`Physlib/Relativity/MinkowskiMatrix.lean`) and schwarzschild.py:63-81. At
`rs = 0`, `c = 1`, `r = 1`, `th = pi / 2` the diagonal of the Schwarzschild metric is the diagonal of `η`, so
einsteinpy's numerical metric has Physlib's signature. -/
theorem schwarzschild_flat_point_is_eta (μ : Fin 1 ⊕ Fin 3) :
    (minkowskiMatrix : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) μ μ =
      Sum.elim (fun _ => schwTT 1 0 1)
        (fun i => ![schwRR 0 1, schwThTh 1, schwPP 1 (π / 2)] i) μ := by
  rcases μ with i | i
  · fin_cases i
    simp [schwTT]
  · fin_cases i <;> simp [schwRR, schwThTh, schwPP]

end EinsteinpyLean.Metric.Spec
