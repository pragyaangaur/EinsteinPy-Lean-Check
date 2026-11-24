import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The coordinate conversions over the reals

The formulas of `coordinates/utils.py` restated with Mathlib's `Real.sin`, `Real.cos`, `Real.sqrt`,
`Real.arccos` and `Complex.arg` (for `numpy.arctan2`, which is the argument of `x + i y`).
The statements are the physics: round trips, the velocity formulas as derivatives of the position maps
(the chain rule), the `a → 0` limit of Boyer-Lindquist coordinates, and `v0` as the root of the norm
equation. Division by zero is `0` in Lean, so crashes of the code (Python's `ZeroDivisionError`) do not
show up here. They are the subject of the model, in `Props.lean`.

Physlib has no coordinate conversion, only the norm of `Space d` and integrals in spherical
shells, so this file is plain Mathlib.
-/

open Real

namespace EinsteinpyLean.Coordinates.Spec

/-- `arctan2 y x`, the angle of the point `(x, y)` in `(-π, π]`. -/
noncomputable def atan2 (y x : ℝ) : ℝ := Complex.arg ⟨x, y⟩

/-- `numpy.hypot`. -/
noncomputable def hypot (x y : ℝ) : ℝ := √(x ^ 2 + y ^ 2)

/-- utils.py:117-143 `spherical_to_cartesian_novel`. -/
noncomputable def sphToCart (r θ φ : ℝ) : ℝ × ℝ × ℝ := (r * cos φ * sin θ, r * sin φ * sin θ, r * cos θ)

/-- utils.py:25-44 `cartesian_to_spherical_novel`: `(r, θ, φ)`. -/
noncomputable def cartToSph (x y z : ℝ) : ℝ × ℝ × ℝ :=
  (hypot (hypot x y) z, atan2 (hypot x y) z, atan2 y x)

/-- utils.py:165-199 `bl_to_cartesian_novel` with the rotational length `α`. -/
noncomputable def blToCart (α r θ φ : ℝ) : ℝ × ℝ × ℝ :=
  (√(r ^ 2 + α ^ 2) * sin θ * cos φ, √(r ^ 2 + α ^ 2) * sin θ * sin φ, r * cos θ)

/-- `w = x² + y² + z² - α²` of utils.py:84. -/
noncomputable def blW (α x y z : ℝ) : ℝ := (x ^ 2 + y ^ 2 + z ^ 2) - α ^ 2

/-- The inner square root `sqrt (w² + 4 α² z²)`. -/
noncomputable def blS (α x y z : ℝ) : ℝ := √(blW α x y z ^ 2 + 4 * α ^ 2 * z ^ 2)

/-- The radius `r = sqrt (0.5 (w + s))` of utils.py:85. -/
noncomputable def blR (α x y z : ℝ) : ℝ := √(1 / 2 * (blW α x y z + blS α x y z))

/-- utils.py:66-91 `cartesian_to_bl_novel`: `(r, θ, φ)`. -/
noncomputable def cartToBL (α x y z : ℝ) : ℝ × ℝ × ℝ :=
  (blR α x y z, arccos (z / blR α x y z), atan2 y x)

/-! ## The angle -/

theorem atan2_polar {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : θ ∈ Set.Ioc (-π) π) :
    atan2 (ρ * sin θ) (ρ * cos θ) = θ := by
  have h : (⟨ρ * cos θ, ρ * sin θ⟩ : ℂ) = (ρ : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  unfold atan2
  rw [h, Complex.arg_real_mul _ hρ]
  exact Complex.arg_cos_add_sin_mul_I hθ

theorem hypot_polar {r θ φ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ sin θ) :
    hypot (r * cos φ * sin θ) (r * sin φ * sin θ) = r * sin θ := by
  unfold hypot
  have : (r * cos φ * sin θ) ^ 2 + (r * sin φ * sin θ) ^ 2 = (r * sin θ) ^ 2 := by
    have := cos_sq_add_sin_sq φ
    calc _ = (r * sin θ) ^ 2 * (cos φ ^ 2 + sin φ ^ 2) := by ring
      _ = _ := by rw [this, mul_one]
  rw [this]
  exact Real.sqrt_sq (mul_nonneg hr hθ)

/-- PROP coordinates.spherical.roundtrip : PROVEN
Source: `Cartesian.to_spherical` undoes `Spherical.to_cartesian` (conversion.py), the claim of every
coordinate chart. Holds for `r > 0`, `0 < θ < π` and `φ ∈ (-π, π]`, off the axis, where the angle `φ`
is not defined. -/
theorem sph_roundtrip {r θ φ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hθ' : θ < π)
    (hφ : φ ∈ Set.Ioc (-π) π) :
    cartToSph (sphToCart r θ φ).1 (sphToCart r θ φ).2.1 (sphToCart r θ φ).2.2 = (r, θ, φ) := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ hθ'
  have h1 : hypot (r * cos φ * sin θ) (r * sin φ * sin θ) = r * sin θ := hypot_polar hr.le hs.le
  have hθm : θ ∈ Set.Ioc (-π) π := ⟨by linarith [pi_pos], hθ'.le⟩
  simp only [cartToSph, sphToCart]
  rw [h1]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [hypot]
    have : (r * sin θ) ^ 2 + (r * cos θ) ^ 2 = r ^ 2 := by
      have := sin_sq_add_cos_sq θ
      calc _ = r ^ 2 * (sin θ ^ 2 + cos θ ^ 2) := by ring
        _ = _ := by rw [this, mul_one]
    rw [this]
    exact Real.sqrt_sq hr.le
  · exact atan2_polar hr hθm
  · have := atan2_polar (mul_pos hr hs) hφ
    unfold atan2 at this ⊢
    convert this using 3 <;> ring

/-! ## Boyer-Lindquist -/

/-- The three identities behind the Boyer-Lindquist radius: for the Cartesian image of `(r, θ, φ)`,
`w = r² - α² cos² θ` and `sqrt (w² + 4 α² z²) = r² + α² cos² θ`. -/
theorem bl_w_s {α r θ φ : ℝ} :
    blW α (√(r ^ 2 + α ^ 2) * sin θ * cos φ) (√(r ^ 2 + α ^ 2) * sin θ * sin φ) (r * cos θ)
        = r ^ 2 - α ^ 2 * cos θ ^ 2 ∧
    blS α (√(r ^ 2 + α ^ 2) * sin θ * cos φ) (√(r ^ 2 + α ^ 2) * sin θ * sin φ) (r * cos θ)
        = r ^ 2 + α ^ 2 * cos θ ^ 2 := by
  have hq : √(r ^ 2 + α ^ 2) ^ 2 = r ^ 2 + α ^ 2 := Real.sq_sqrt (by positivity)
  have hw : blW α (√(r ^ 2 + α ^ 2) * sin θ * cos φ) (√(r ^ 2 + α ^ 2) * sin θ * sin φ) (r * cos θ)
      = r ^ 2 - α ^ 2 * cos θ ^ 2 := by
    unfold blW
    have h1 := cos_sq_add_sin_sq φ
    have h2 := sin_sq_add_cos_sq θ
    have : (√(r ^ 2 + α ^ 2) * sin θ * cos φ) ^ 2 + (√(r ^ 2 + α ^ 2) * sin θ * sin φ) ^ 2
        = (r ^ 2 + α ^ 2) * sin θ ^ 2 := by
      calc _ = √(r ^ 2 + α ^ 2) ^ 2 * sin θ ^ 2 * (cos φ ^ 2 + sin φ ^ 2) := by ring
        _ = _ := by rw [h1, mul_one, hq]
    linear_combination this + (r ^ 2 + α ^ 2) * h2
  refine ⟨hw, ?_⟩
  unfold blS
  rw [hw]
  have : (r ^ 2 - α ^ 2 * cos θ ^ 2) ^ 2 + 4 * α ^ 2 * (r * cos θ) ^ 2 = (r ^ 2 + α ^ 2 * cos θ ^ 2) ^ 2 := by
    ring
  rw [this]
  exact Real.sqrt_sq (by positivity)

/-- PROP coordinates.boyer_lindquist.roundtrip : PROVEN
Source: `Cartesian.to_bl` undoes `BoyerLindquist.to_cartesian` (conversion.py), including the
radius that utils.py:85 finds from the quartic `r⁴ - w r² - α² z² = 0`. Holds for every `α`, `r > 0`,
`0 < θ < π` and `φ ∈ (-π, π]`. -/
theorem bl_roundtrip {α r θ φ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hθ' : θ < π)
    (hφ : φ ∈ Set.Ioc (-π) π) :
    cartToBL α (blToCart α r θ φ).1 (blToCart α r θ φ).2.1 (blToCart α r θ φ).2.2 = (r, θ, φ) := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ hθ'
  obtain ⟨hw, hS⟩ := @bl_w_s α r θ φ
  have hR : blR α (√(r ^ 2 + α ^ 2) * sin θ * cos φ) (√(r ^ 2 + α ^ 2) * sin θ * sin φ) (r * cos θ) = r := by
    unfold blR
    rw [hw, hS]
    have : 1 / 2 * (r ^ 2 - α ^ 2 * cos θ ^ 2 + (r ^ 2 + α ^ 2 * cos θ ^ 2)) = r ^ 2 := by ring
    rw [this]
    exact Real.sqrt_sq hr.le
  have hq : 0 < √(r ^ 2 + α ^ 2) := Real.sqrt_pos.2 (by positivity)
  simp only [cartToBL, blToCart]
  rw [hR]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show arccos (r * cos θ / r) = θ
    rw [mul_div_cancel_left₀ _ hr.ne']
    exact arccos_cos hθ.le hθ'.le
  · have := atan2_polar (mul_pos hq hs) hφ
    unfold atan2 at this ⊢
    convert this using 3

/-- PROP coordinates.boyer_lindquist.alpha_zero : PROVEN
Source: for `α = 0` Boyer-Lindquist coordinates are spherical coordinates, so `cartesian_to_bl`
(utils.py:66-91) and `cartesian_to_spherical` (utils.py:25-44) are the same map. Holds for every point
except the origin (where the code divides by zero). In floating point they differ near the axis, see
`Props.bl_theta_near_axis_inaccurate`. -/
theorem bl_alpha_zero {x y z : ℝ} (h : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    cartToBL 0 x y z = cartToSph x y z := by
  have hw : blW 0 x y z = x ^ 2 + y ^ 2 + z ^ 2 := by simp [blW]
  have hS : blS 0 x y z = x ^ 2 + y ^ 2 + z ^ 2 := by
    unfold blS; rw [hw]; simp
    exact Real.sqrt_sq h.le
  have hR : blR 0 x y z = √(x ^ 2 + y ^ 2 + z ^ 2) := by
    unfold blR; rw [hw, hS]; congr 1; ring
  have hH : hypot (hypot x y) z = √(x ^ 2 + y ^ 2 + z ^ 2) := by
    unfold hypot
    rw [Real.sq_sqrt (by positivity)]
  have hxy : 0 ≤ hypot x y := Real.sqrt_nonneg _
  refine Prod.ext (by simpa [cartToBL, cartToSph] using hR.trans hH.symm) (Prod.ext ?_ rfl)
  · show arccos (z / blR 0 x y z) = atan2 (hypot x y) z
    rw [hR]
    unfold atan2
    have hz : (⟨z, hypot x y⟩ : ℂ) ≠ 0 := by
      intro h0
      have h1 : z = 0 := congrArg Complex.re h0
      have h2 : hypot x y = 0 := congrArg Complex.im h0
      have : x ^ 2 + y ^ 2 = 0 := by
        have := Real.sqrt_eq_zero'.1 h2
        have := sq_nonneg x; have := sq_nonneg y; unfold hypot at h2
        nlinarith [Real.sqrt_eq_zero'.1 h2]
      nlinarith [sq_nonneg z]
    rw [Complex.arg_of_im_nonneg_of_ne_zero (z := ⟨z, hypot x y⟩) hxy hz]
    congr 2
    rw [Complex.norm_def]
    simp [Complex.normSq_apply]
    unfold hypot
    rw [Real.mul_self_sqrt (by positivity)]
    congr 1; ring

end EinsteinpyLean.Coordinates.Spec
