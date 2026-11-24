import EinsteinpyLean.Curvature.Model

/-!
# Properties of the curvature model

Statements about the executable model of `Model.lean`. The general identities over the
real numbers (Christoffel symmetry, Bianchi, Weyl trace, and so on) are in `Spec.lean`.

`native_decide` is used for concrete evaluations only. The kernel cannot reduce `Rat`
arithmetic inside `Array` code, so each use evaluates one case of the compiled model,
the same code that the difftests check against einsteinpy.
-/

namespace EinsteinpyLean.Curvature
open Arr

/-- The Ricci scalar of a computed pipeline equals `x`. -/
def scalarIs (config : String) (j : Jet) (x : Rat) : Bool :=
  match fromMetric config j with
  | .ok (p, _) => decide (p.R = x)
  | .error _ => false

/-- Every entry of an array computed by `f` is zero. -/
def allZero (r : Except Err Arr) : Bool :=
  match r with
  | .ok a => a.data.all (· == 0)
  | .error _ => false

/-- The round unit sphere in the conformal chart `4 (dx² + dy²) / (1 + r²)²`, at the origin:
`g = 4 I`, `∂g = 0` and `∂_k ∂_l g_ij = -16 δ_kl δ_ij`. -/
def sphereJet : Jet :=
  ⟨2, ⟨[2, 2], #[4, 0, 0, 4]⟩, ⟨[2, 2, 2], Array.replicate 8 0⟩,
   ⟨[2, 2, 2, 2], #[-16, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, -16]⟩⟩

/-- The 2D Minkowski metric `diag(-1, 1)` at any point: `∂g = ∂∂g = 0`. -/
def flatJet : Jet :=
  ⟨2, ⟨[2, 2], #[-1, 0, 0, 1]⟩, ⟨[2, 2, 2], Array.replicate 8 0⟩, ⟨[2, 2, 2, 2], Array.replicate 16 0⟩⟩

/-- PROP curvature.ricci_scalar.unit_sphere : PROVEN
Source: textbook, the unit 2-sphere has Gaussian curvature 1, so `R = 2 K = 2`. The jet is
that of the stereographic chart, whose second derivatives come from `4 (1 + r²)⁻²`. -/
theorem ricci_scalar_unit_sphere : scalarIs "ll" sphereJet 2 = true := by
  -- native_decide: concrete evaluation of the compiled model, see the file header
  native_decide

/-- PROP curvature.einstein.vanishes_in_two_dimensions_sphere : PROVEN
Source: textbook, the Einstein tensor is identically zero in two dimensions. Evaluated
for the unit sphere. -/
theorem einstein_sphere_zero :
    allZero ((fromMetric "ll" sphereJet).map fun (p, _) => einsteinOf p) = true := by
  -- native_decide: concrete evaluation of the compiled model, see the file header
  native_decide

/-- Example, not a property: flat space has zero Riemann tensor in the model. The general
statement over Physlib's Minkowski matrix is `Spec.lean`, `minkowski_riemann_zero`. -/
theorem flat_riemann_zero :
    allZero ((fromMetric "ll" flatJet).map fun (p, _) => p.riemann) = true := by
  -- native_decide: concrete evaluation of the compiled model, see the file header
  native_decide

/-- The metric `diag(-1, 1 + x²/3, 1 + t x/5)` in the coordinates `(t, x, y)`, at `t = 1/3`,
`x = 1/2`. It is the metric of `bugs/repro/curvature-einstein-float-half.py`. -/
def einsteinJet : Jet :=
  ⟨3, ⟨[3, 3], #[-1, 0, 0, 0, 13/12, 0, 0, 0, 31/30]⟩,
   ⟨[3, 3, 3], (Array.replicate 27 (0 : Rat)).set! 13 (1/3) |>.set! 8 (1/10) |>.set! 17 (1/15)⟩,
   ⟨[3, 3, 3, 3], (Array.replicate 81 (0 : Rat)).set! 40 (2/3) |>.set! 17 (1/5) |>.set! 35 (1/5)⟩⟩

/-- PROP curvature.einstein.exact_zero_component : PROVEN
Source: arithmetic. At this rational point the `yy` component of `Ric - ½ R g` is exactly
zero. The model computes it on rationals and gets `0`. einsteinpy takes the factor from the
Python float `1 / 2` (einstein.py:55) and returns `-4.3e-19` for the same component, see
`bugs/curvature-einstein-float-half.yaml`. -/
theorem einstein_exact_zero_component :
    (match fromMetric "ll" einsteinJet with
      | .ok (p, _) => decide ((einsteinOf p).get [2, 2] = 0)
      | .error _ => false) = true := by
  -- native_decide: concrete evaluation of the compiled model, see the file header
  native_decide

/-- PROP curvature.schouten.dimension_below_three_raises : PROVEN
Source: schouten.py:59-62 docstring, "Raised when the dimension of the tensor is less than
3". The model raises for every pipeline of dimension 1 or 2. -/
theorem schouten_small_dim (p : Pipeline) (h : p.jet.d < 3) : schoutenOf p = .error .dimTooSmall := by
  unfold schoutenOf
  have : ¬ p.jet.d ≥ 3 := by omega
  simp [this]
  rfl

/-- PROP curvature.weyl.dimension_below_three_raises : PROVEN
Source: weyl.py:59-62 docstring, "Raised when the dimension of the tensor is less than 3". -/
theorem weyl_small_dim (p : Pipeline) (m : Met) (h : p.jet.d < 3) :
    weylOf p m = .error .dimTooSmall := by
  unfold weylOf
  have h1 : ¬ p.jet.d > 3 := by omega
  have h2 : ¬ p.jet.d == 3 := by simp; omega
  simp [h1, h2]
  rfl

/-- PROP curvature.weyl.dimension_three_is_zero : PROVEN
Source: textbook, the Weyl tensor vanishes identically in three dimensions; weyl.py:101-107
returns an array of zeros. -/
theorem weyl_dim_three (p : Pipeline) (m : Met) (h : p.jet.d = 3) :
    weylOf p m = .ok (ofFn [3, 3, 3, 3] fun _ => 0) := by
  unfold weylOf
  simp [h]
  rfl

/-- PROP curvature.stress_energy.change_config_keeps_class : REFUTED
Source: stress_energy_momentum.py:81-82 docstring, "Returns StressEnergyMomentumTensor ...
New tensor with new configuration". Every other class returns its own class from
`change_config` (`Kind.changeClass k = Kind.ltClass k`), but the stress-energy tensor
returns an `EinsteinTensor` (stress_energy_momentum.py:95). -/
theorem stress_change_config_wrong_class :
    Kind.changeClass .stress ≠ Kind.ltClass .stress := by decide

/-- PROP curvature.change_config.class_consistent_with_lorentz_transform : REFUTED
Source: the docstrings of `change_config` and `lorentz_transform`, which name the same
class. The only class where the two methods disagree is `StressEnergyMomentumTensor`. -/
theorem change_class_ne_lt_class_only_stress :
    (∀ k : Kind, k ≠ .stress → k ≠ .scalar → k.changeClass = k.ltClass) ∧
      Kind.changeClass .stress ≠ Kind.ltClass .stress := by
  refine ⟨?_, by decide⟩
  intro k h1 h2
  cases k <;> simp_all [Kind.changeClass, Kind.ltClass]

/-- Example, not a property: `RicciScalar` has no `change_config`, so the call is an
`AttributeError` before any metric is looked at. -/
theorem scalar_change_config_attribute_error (arr : Arr) (c n : String) (k : Nat)
    (pm am : Option Met) : changeConfig .scalar arr c n k pm am = .error .noAttr := by
  simp [changeConfig]
  rfl

end EinsteinpyLean.Curvature
