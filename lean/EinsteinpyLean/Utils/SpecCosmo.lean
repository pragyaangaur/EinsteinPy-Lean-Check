import Physlib.Cosmology.FLRW.SpecificCases.EinsteinDeSitter
import Physlib.Cosmology.FLRW.SpecificCases.RadiationDominated
import Physlib.Cosmology.FLRW.DeSitter
import Mathlib.Tactic.NormNum

/-!
# `scalar_factor` and the constants against Physlib's FLRW cosmology

einsteinpy's `scalar_factor(t, era, tuning_param)` is, with `T` the time in seconds and `tp` the
tuning parameter,

* `md`:  `tp * T ^ (2/3)`,
* `rd`:  `tp * T ^ (1/2)`,
* `ded`: `tp * exp(H T)` with `H = sqrt(Cosmo_Const / 3)`,

and `scalar_factor_derivative` is the derivative in `T`. Physlib has the Einstein-de Sitter scale factor
`(t/t₀)^(2/3)`, the radiation scale factor `(t/t₀)^(1/2)` and the de Sitter scale factor
`a₀ exp(σ √(Λ/3) c t)`, with `Λ` in inverse length squared and each proved to solve the Friedmann
equations. The unit normalisation is `t₀ = 1 s` and `a₀ = tp`. `Cosmo_Const` is `Λ c²` in s⁻², which is the
convention under which the three agree.
-/

open Cosmology Cosmology.FLRW.FriedmannEquation Real

namespace EinsteinpyLean.Utils.SpecCosmo

/-- `scalar_factor(·, "md", tp)` on the reals, `T` in seconds. -/
noncomputable def epMd (tp T : ℝ) : ℝ := tp * T ^ (2 / 3 : ℝ)
/-- `scalar_factor(·, "rd", tp)`. -/
noncomputable def epRd (tp T : ℝ) : ℝ := tp * T ^ (1 / 2 : ℝ)
/-- `scalar_factor(·, "ded", tp)` with `lam = Cosmo_Const`. `np.e ** y` is `exp y` on the reals. -/
noncomputable def epDed (tp lam T : ℝ) : ℝ := tp * Real.exp (√(lam / 3) * T)

/-- PROP scalar_factor.md.is_einstein_de_sitter : PROVEN
Source: Physlib `einsteinDeSitterScaleFactor`, `a = (t/t₀)^(2/3)`. With `t₀ = 1 s` the matter era is
`tp` times it. -/
theorem md_eq (tp T : ℝ) : epMd tp T = tp * einsteinDeSitterScaleFactor ⟨1⟩ ⟨T⟩ := by
  simp [epMd, einsteinDeSitterScaleFactor]

/-- PROP scalar_factor.rd.is_radiation_dominated : PROVEN
Source: Physlib `radiationScaleFactor`, `a = (t/t₀)^(1/2)`. -/
theorem rd_eq (tp T : ℝ) : epRd tp T = tp * radiationScaleFactor ⟨1⟩ ⟨T⟩ := by
  simp [epRd, radiationScaleFactor]

/-- PROP scalar_factor.ded.is_de_sitter : PROVEN
Source: Physlib `deSitterScaleFactor`, `a₀ exp(σ √(Λ/3) c t)`. With `Cosmo_Const = Λ c²` the dark energy
era is the expanding de Sitter solution with `a₀ = tp`. -/
theorem ded_eq (tp T Λ : ℝ) (c : SpeedOfLight) (hΛ : 0 ≤ Λ) :
    epDed tp (Λ * (c : ℝ) ^ 2) T = deSitterScaleFactor tp 1 Λ c ⟨T⟩ := by
  have h : Λ * (c : ℝ) ^ 2 / 3 = Λ / 3 * (c : ℝ) ^ 2 := by ring
  have hs : √(Λ * (c : ℝ) ^ 2 / 3) = √(Λ / 3) * (c : ℝ) := by
    rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq c.pos.le]
  simp only [epDed, deSitterScaleFactor, hs]
  ring_nf

/-- PROP scalar_factor.md.derivative : PROVEN
Source: scalar_factor.py:64-66. The code's `(2/3) * tp * T ** (-1/3)` is the derivative of the
scale factor for `T > 0`. -/
theorem md_deriv (tp : ℝ) {T : ℝ} (hT : 0 < T) :
    HasDerivAt (epMd tp) ((2 / 3) * tp * T ^ (-1 / 3 : ℝ)) T := by
  have h := (Real.hasDerivAt_rpow_const (x := T) (p := 2 / 3) (Or.inl hT.ne')).const_mul tp
  unfold epMd
  convert h using 1
  rw [show (2 / 3 : ℝ) - 1 = -1 / 3 by norm_num]
  ring

/-- PROP scalar_factor.rd.derivative : PROVEN
Source: scalar_factor.py:67-68, `0.5 * tp * T ** (-0.5)`. -/
theorem rd_deriv (tp : ℝ) {T : ℝ} (hT : 0 < T) :
    HasDerivAt (epRd tp) ((1 / 2) * tp * T ^ (-1 / 2 : ℝ)) T := by
  have h := (Real.hasDerivAt_rpow_const (x := T) (p := 1 / 2) (Or.inl hT.ne')).const_mul tp
  unfold epRd
  convert h using 1
  rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num]
  ring

/-- PROP scalar_factor.ded.derivative : PROVEN
Source: scalar_factor.py:69-71, `tp * (H * exp(H T))`. -/
theorem ded_deriv (tp lam T : ℝ) :
    HasDerivAt (epDed tp lam) (tp * (√(lam / 3) * Real.exp (√(lam / 3) * T))) T := by
  have h := (((hasDerivAt_id T).const_mul (√(lam / 3))).exp).const_mul tp
  simp only [id] at h
  unfold epDed
  convert h using 1
  ring

/-- PROP scalar_factor.ded.hubble_parameter : PROVEN
Source: Physlib `hubbleConstant_deSitterScaleFactor`. The Hubble parameter of the dark energy era is
the constant `√(Λ/3) c`, which is `sqrt(Cosmo_Const / 3)` of einsteinpy. -/
theorem ded_hubble (tp Λ : ℝ) (c : SpeedOfLight) (hΛ : 0 ≤ Λ) (htp : tp ≠ 0) (t : Time) :
    hubbleConstant (fun s : Time => epDed tp (Λ * (c : ℝ) ^ 2) s.val) t = √(Λ / 3) * (c : ℝ) := by
  have : (fun s : Time => epDed tp (Λ * (c : ℝ) ^ 2) s.val) = deSitterScaleFactor tp 1 Λ c := by
    funext s
    exact ded_eq tp s.val Λ c hΛ
  rw [this, hubbleConstant_deSitterScaleFactor htp]
  ring

/-- PROP scalar_factor.md.is_dust : PROVEN
Source: Physlib `FLRW.friedmannSolution_powerLaw`, which needs `1 + 3 w = 2 (1 - n) / n`. For the
exponent `n = 2/3` of the matter era the only equation of state is `w = 0`, dust. -/
theorem md_is_dust (w : ℝ) : 1 + 3 * w = 2 * (1 - 2 / 3) / (2 / 3) ↔ w = 0 := by
  constructor <;> intro h <;> [skip; subst h] <;> linarith

/-- PROP scalar_factor.rd.is_radiation : PROVEN
Source: the same condition with the exponent `n = 1/2` of the radiation era gives `w = 1/3`. -/
theorem rd_is_radiation (w : ℝ) : 1 + 3 * w = 2 * (1 - 1 / 2) / (1 / 2) ↔ w = 1 / 3 := by
  constructor <;> intro h <;> [skip; subst h] <;> linarith

/-- PROP scalar_factor.md.solves_friedmann : PROVEN
Source: Physlib `FLRW.friedmannSolution_einsteinDeSitter`. The model whose scale factor is einsteinpy's
matter era (with `tp = 1`) solves both Friedmann equations, filled with dust. -/
theorem md_solves_friedmann {G : ℝ} {c : SpeedOfLight} (hG : 0 < G) :
    (FLRW.einsteinDeSitter ⟨1⟩ one_pos).a = (fun t : Time => epMd 1 t.val) ∧
    (FLRW.einsteinDeSitter ⟨1⟩ one_pos).FriedmannSolution (CosmicFluid.powerLaw (2 / 3) 0 G c) 0 G c := by
  refine ⟨?_, FLRW.friedmannSolution_einsteinDeSitter one_pos hG⟩
  funext t
  simp [FLRW.einsteinDeSitter_a, epMd, einsteinDeSitterScaleFactor]

/-- PROP scalar_factor.rd.solves_friedmann : PROVEN
Source: Physlib `FLRW.friedmannSolution_radiationDominated`, as above with radiation. -/
theorem rd_solves_friedmann {G : ℝ} {c : SpeedOfLight} (hG : 0 < G) :
    (FLRW.radiationDominated ⟨1⟩ one_pos).a = (fun t : Time => epRd 1 t.val) ∧
    (FLRW.radiationDominated ⟨1⟩ one_pos).FriedmannSolution (CosmicFluid.powerLaw (1 / 2) (1 / 3) G c) 0 G c := by
  refine ⟨?_, FLRW.friedmannSolution_radiationDominated one_pos hG⟩
  funext t
  simp [FLRW.radiationDominated_a, epRd, radiationScaleFactor]

/-- PROP scalar_factor.ded.solves_friedmann : PROVEN
Source: Physlib `FLRW.friedmannSolution_deSitter`. With `Cosmo_Const = Λ c²` and `Λ > 0` the dark energy era
solves the Friedmann equations with empty matter. -/
theorem ded_solves_friedmann {Λ G : ℝ} (c : SpeedOfLight) (hΛ : 0 < Λ) :
    (FLRW.deSitter 1 1 Λ c one_pos).FriedmannSolution CosmicFluid.empty Λ G c :=
  FLRW.friedmannSolution_deSitter G c hΛ one_pos (Or.inl rfl)

/-- PROP scalar_factor.ded.rate_squared : PROVEN
Source: scalar_factor.py:36. `H = sqrt(Cosmo_Const / 3)` squares to `Cosmo_Const / 3`. -/
theorem ded_rate_sq {lam : ℝ} (h : 0 ≤ lam) : √(lam / 3) ^ 2 = lam / 3 :=
  Real.sq_sqrt (by linarith)

/-! ## Constants -/

/-- PROP constant.cosmo_const.is_planck18_lambda : PROVEN
Source: constant.py:22-25, `Lambda c² = 3 H0² Omega_Lambda` for Planck 2018 with `H0 = 67.66 km/s/Mpc`,
`Omega_Lambda = 0.6888463055445441` and one Mpc equal to `3.0856775814913673e19 km`. The stored value
`9.935883363094694e-36 s⁻²` agrees to a relative `1e-15`. -/
theorem cosmo_const_planck18 :
    |3 * (67.66 / 3.0856775814913673e19 : ℚ) ^ 2 * 0.6888463055445441 - 9.935883363094694e-36|
      ≤ 1e-15 * 9.935883363094694e-36 := by
  rw [abs_le]
  constructor <;> norm_num

/-- PROP constant.solar_mass.is_iau_gm : PROVEN
Source: constant.py:39-40. `Solar_Mass * G` with the stored `1.988409870698051e30 kg` and CODATA
`G = 6.6743e-11` is the IAU 2015 `GM_sun = 1.3271244e20 m³/s²` to a relative `1e-12`. -/
theorem solar_mass_gm :
    |(1.988409870698051e30 : ℚ) * 6.6743e-11 - 1.3271244e20| ≤ 1e-12 * 1.3271244e20 := by
  rw [abs_le]
  constructor <;> norm_num

end EinsteinpyLean.Utils.SpecCosmo
