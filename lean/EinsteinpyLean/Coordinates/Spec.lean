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

/-! ## Velocities are the derivatives of the position maps

Each velocity formula of utils.py is the chain rule applied to the position map. A curve is a function
of `t`, and `HasDerivAt f f' t` says that its derivative at `t` is `f'`. The formulas are copied from
the source in the same order of factors. -/

/-- PROP coordinates.spherical_to_cartesian.velocity : PROVEN
Source: utils.py:117-143 `spherical_to_cartesian`. The three velocity formulas are the derivatives of
`x = r cos φ sin θ`, `y = r sin φ sin θ` and `z = r cos θ`. -/
theorem sph_to_cart_velocity {r θ φ : ℝ → ℝ} {r' θ' φ' t : ℝ}
    (hr : HasDerivAt r r' t) (hθ : HasDerivAt θ θ' t) (hφ : HasDerivAt φ φ' t) :
    HasDerivAt (fun s => r s * cos (φ s) * sin (θ s))
      (sin (θ t) * cos (φ t) * r' - r t * sin (θ t) * sin (φ t) * φ'
        + r t * cos (θ t) * cos (φ t) * θ') t ∧
    HasDerivAt (fun s => r s * sin (φ s) * sin (θ s))
      (sin (θ t) * sin (φ t) * r' + r t * cos (θ t) * sin (φ t) * θ'
        + r t * sin (θ t) * cos (φ t) * φ') t ∧
    HasDerivAt (fun s => r s * cos (θ s)) (cos (θ t) * r' - r t * sin (θ t) * θ') t := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((hr.mul hφ.cos).mul hθ.sin).congr_deriv (by (try simp only [Pi.mul_apply]); ring)
  · exact ((hr.mul hφ.sin).mul hθ.sin).congr_deriv (by (try simp only [Pi.mul_apply]); ring)
  · exact (hr.mul hθ.cos).congr_deriv (by (try simp only [Pi.mul_apply]); ring)

/-- PROP coordinates.boyer_lindquist_to_cartesian.velocity : PROVEN
Source: utils.py:165-199 `bl_to_cartesian`. With `xa = sqrt (r² + α²)` the formulas are the derivatives
of `xa sin θ cos φ`, `xa sin θ sin φ` and `r cos θ`, for every curve with `r² + α² ≠ 0`
(the code divides by `xa`, so it needs exactly that). -/
theorem bl_to_cart_velocity {α : ℝ} {r θ φ : ℝ → ℝ} {r' θ' φ' t : ℝ}
    (hr : HasDerivAt r r' t) (hθ : HasDerivAt θ θ' t) (hφ : HasDerivAt φ φ' t)
    (hq : r t ^ 2 + α ^ 2 ≠ 0) :
    HasDerivAt (fun s => √(r s ^ 2 + α ^ 2) * sin (θ s) * cos (φ s))
      (r t * r' * sin (θ t) * cos (φ t) / √(r t ^ 2 + α ^ 2)
        + √(r t ^ 2 + α ^ 2) * cos (θ t) * cos (φ t) * θ'
        - √(r t ^ 2 + α ^ 2) * sin (θ t) * sin (φ t) * φ') t ∧
    HasDerivAt (fun s => √(r s ^ 2 + α ^ 2) * sin (θ s) * sin (φ s))
      (r t * r' * sin (θ t) * sin (φ t) / √(r t ^ 2 + α ^ 2)
        + √(r t ^ 2 + α ^ 2) * cos (θ t) * sin (φ t) * θ'
        + √(r t ^ 2 + α ^ 2) * sin (θ t) * cos (φ t) * φ') t ∧
    HasDerivAt (fun s => r s * cos (θ s)) (r' * cos (θ t) - r t * sin (θ t) * θ') t := by
  have hs : √(r t ^ 2 + α ^ 2) ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne (by positivity) (Ne.symm hq))).ne'
  have hxa : HasDerivAt (fun s => √(r s ^ 2 + α ^ 2)) (r t * r' / √(r t ^ 2 + α ^ 2)) t := by
    refine (((hr.pow 2).add_const (α ^ 2)).sqrt hq).congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine ((hxa.mul hθ.sin).mul hφ.cos).congr_deriv ?_
    (try simp only [Pi.mul_apply])
    field_simp
    try ring
  · refine ((hxa.mul hθ.sin).mul hφ.sin).congr_deriv ?_
    (try simp only [Pi.mul_apply])
    field_simp
    try ring
  · exact (hr.mul hθ.cos).congr_deriv (by (try simp only [Pi.mul_apply]); ring)

/-- The derivative of `arccos (z / R)` for curves `z` and `R`. -/
theorem arccos_div_velocity {z R : ℝ → ℝ} {vz R' t : ℝ} (hz : HasDerivAt z vz t)
    (hR : HasDerivAt R R' t) (h0 : R t ≠ 0) (h1 : z t / R t ≠ -1) (h2 : z t / R t ≠ 1) :
    HasDerivAt (fun s => arccos (z s / R s))
      ((-1 / √(1 - (z t / R t) ^ 2)) * ((vz * R t - R' * z t) / R t ^ 2)) t := by
  have h := (Real.hasDerivAt_arccos h1 h2).comp t (hz.div hR h0)
  exact h.congr_deriv (by ring)

/-- The derivative of `arctan (y / x)` for curves `x` and `y` with `x ≠ 0`. -/
theorem arctan_div_velocity {x y : ℝ → ℝ} {vx vy t : ℝ} (hx : HasDerivAt x vx t)
    (hy : HasDerivAt y vy t) (h0 : x t ≠ 0) :
    HasDerivAt (fun s => arctan (y s / x s))
      ((1 / (1 + (y t / x t) ^ 2)) * ((vy * x t - vx * y t) / x t ^ 2)) t := by
  have h := (hy.div hx h0).arctan
  exact h.congr_deriv (by simp only [Pi.div_apply]; ring)

/-- PROP coordinates.cartesian_to_spherical.velocity_phi : PROVEN
Source: utils.py:25-44, `v_p = -1 * (v_x * y - x * v_y) / n1` with `n1 = x² + y²`. It is the derivative of
`arctan (y / x)`, that is of `φ` on each side of the plane `x = 0` (`φ` and `arctan (y / x)` differ by a
constant there, see `atan2_eq_arctan`), and unlike the Boyer-Lindquist form of the same derivative
(`arctan_div_velocity`) it needs only `(x, y) ≠ (0, 0)`. -/
theorem sph_vp_formula {x y vx vy : ℝ} (h0 : x ≠ 0) :
    (1 / (1 + (y / x) ^ 2)) * ((vy * x - vx * y) / x ^ 2)
      = -1 * (vx * y - x * vy) / (x ^ 2 + y ^ 2) := by
  have : x ^ 2 + y ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- For `x > 0`, `arctan2 y x = arctan (y / x)`. -/
theorem atan2_eq_arctan {x y : ℝ} (hx : 0 < x) : atan2 y x = arctan (y / x) := by
  unfold atan2
  have hre : (0 : ℝ) < (⟨x, y⟩ : ℂ).re := hx
  have h1 : |Complex.arg ⟨x, y⟩| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
  have h2 : tan (Complex.arg ⟨x, y⟩) = y / x := Complex.tan_arg _
  rw [← h2]
  exact (arctan_tan (by linarith [(abs_lt.1 h1).1]) (by linarith [(abs_lt.1 h1).2])).symm

end EinsteinpyLean.Coordinates.Spec
