import EinsteinpyLean.Metric.Model

/-!
# Properties of the Metric model

Core Lean only. Statements about floating point evaluate the model, so they use `native_decide`: Lean's kernel cannot
unfold `Float` operations, and the compiled evaluation of the model is exactly what `epdiff_metric` ran against
einsteinpy (`difftest/metric_*_diff.py`). The statements over the reals are in `Spec.lean`, `SpecMetric.lean`,
`SpecEM.lean` and `SpecChristoffel.lean`. Each refuted property was rerun in real einsteinpy, see `bugs/metric-*.yaml`
and `bugs/repro/metric-*.py`.
-/

namespace EinsteinpyLean.Metric

open EinsteinpyLean.Utils

/-- Relative closeness of two floats. -/
def relClose (a b tol : Float) : Bool := (a - b).abs ≤ tol * b.abs

/-- The value of a successful `R Float`, `NaN` for an error. -/
def val : R Float → Float
  | .ok x => x
  | .error _ => 0.0 / 0.0

/-! ## Constructors and units -/

/-- PROP metric.ctor.mass_unit_ignored : REFUTED
Source: schwarzschild.py:22-33 and base_metric.py:101-103. `u.quantity_input` checks that `M` is a mass and does not
convert it, and `schwarzschild_radius` takes `.value`. So `Schwarzschild(coords, 1 * u.Msun)` has the radius of one
kilogram, `1.5e-27 m`, and not `2953 m`. In the model a mass in solar masses is the pair `(mass, 1)`. -/
theorem solar_mass_quantity_has_radius_of_one_kilogram :
    (match ctorRad .schw (some .mass, 1.0) (some .dimless, 0.0) (some .charge, 0.0) (some .chargePerMass, 0.0) with
     | .ok x => relClose x (schRad solarMass) 1e-3
     | .error _ => true) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP metric.ctor.units_are_checked : PROVEN
Source: base_metric.py:48 `@u.quantity_input(M=u.kg, a=u.one, Q=u.C)`. A plain mass is a `TypeError`, a time is a
`UnitsError`, and a plain spin is accepted because the target is dimensionless. -/
theorem constructor_unit_checks :
    (match ctorRad .schw (none, 1.0) (none, 0.0) (none, 0.0) (none, 0.0) with | .error .type => true | _ => false) = true ∧
    (match ctorRad .schw (some .time, 1.0) (none, 0.0) (none, 0.0) (none, 0.0) with | .error .units => true | _ => false) = true ∧
    (match ctorRad .kerr (some .mass, 1.0) (none, 0.5) (none, 0.0) (none, 0.0) with | .ok _ => true | _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Helpers -/

/-- PROP metric.base.alpha.spin_range : PROVEN
Source: base_metric.py:225-243. `alpha` raises `ValueError` for `a < 0` and `a > 1` and is `0` for `a = 0`. -/
theorem alpha_range :
    (match alphaOf 1e30 1.5 with | .error (.value _) => true | _ => false) = true ∧
    (match alphaOf 1e30 (-0.1) with | .error (.value _) => true | _ => false) = true ∧
    (val (alphaOf 1e30 0.0) == 0.0) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP metric.base.schwarzschild_radius.sun : PROVEN
Source: base_metric.py:193-209. The radius of one solar mass is `2953.25 m` (IAU 2015 `GM_sun`). -/
theorem sun_radius : relClose (schRad solarMass) 2953.25 1e-5 = true := by
  -- native_decide: evaluates Float arithmetic
  native_decide

/-- PROP metric.base.singularities.coordinate_message_spacing : REFUTED
Source: base_metric.py:303-310. The `CoordinateError` message is two string literals with no space between them, so it
reads `available inBoyer-Lindquist Coordinates.` and `available inSpherical Polar Coordinates.`. A message should contain
`in Boyer-Lindquist` and `in Spherical Polar`. -/
theorem singularities_message_has_no_space :
    (singKerrMsg.splitOn "in Boyer-Lindquist").length = 1 ∧ (singSchwMsg.splitOn "in Spherical Polar").length = 1 := by
  -- native_decide: evaluates string functions
  native_decide

/-! ## Christoffel symbols -/

/-- PROP metric.kerr.nonzero_christoffels.list_matches_algorithm : PROVEN
Source: kerr.py:48-81 and 344-390. The precomputed list of 32 index triples in `__init__` and the list that
`nonzero_christoffels()` finds by propagating the sparsity pattern contain the same triples. -/
theorem nonzero_lists_agree :
    nonzeroList.length = 32 ∧ nonzeroComputed.length = 32 ∧
    (∀ t ∈ nonzeroList, t ∈ nonzeroComputed) ∧ (∀ t ∈ nonzeroComputed, t ∈ nonzeroList) := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP metric.kerr.christoffel.symmetric_in_lower_indices : PROVEN
Source: Christoffel symbols of the Levi-Civita connection are symmetric in the lower indices. The model writes every
entry of the 32 triples together with its mirror, so at a sample point of each class the array is symmetric.
The general statement over the reals is `Spec.recipe_is_complete`. -/
theorem kerr_christoffel_symmetric_at_sample :
    (match christoffels ⟨.kerr, .bl, 1.0e30, 0.6, 0.0, 0.0⟩ 5000.0 1.1 with
     | .ok c => (List.range 64).all fun n =>
         c[n]! == c[(n / 16) * 16 + (n % 4) * 4 + (n / 4) % 4]!
     | .error _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Horizons -/

/-- PROP metric.kerr.extremal_horizon : PROVEN
Source: base_metric.py:276-285. For `a = 1` and `Q = 0` the two horizons coincide at `G M / c^2 = r_s / 2`. -/
theorem extremal_horizons_coincide :
    (match singularities "Kerr Metric" .bl 1.0e30 1.0 0.0 0.5 with
     | .ok [_, .flt ri, .flt ro, _] => relClose ri (schRad 1.0e30 / 2.0) 1e-12 && relClose ro (schRad 1.0e30 / 2.0) 1e-12
     | _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP metric.kerr.horizon.delta_vanishes : PROVEN
Source: base_metric.py:119-155 and 276-285. The outer horizon returned by `singularities` is a zero of `delta`, to
rounding, for a spin of `0.6` and a mass of `1e30 kg`. The statement over the reals is `Spec.horizons_are_roots`. -/
theorem outer_horizon_is_root_of_delta :
    (match singularities "Kerr Metric" .bl 1.0e30 0.6 0.0 0.5 with
     | .ok [_, _, .flt ro, _] => (val (delta false ro 1.0e30 0.6 0.0)).abs ≤ 1e-12 * ro * ro
     | _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Linear algebra -/

/-- PROP metric.base.metric_contravariant.diagonal_inverse : PROVEN
Source: base_metric.py:354-355 `np.linalg.inv`. The model's inverse of `diag(2, 4, 8, 16)` is `diag(1/2, 1/4, 1/8, 1/16)`. -/
theorem inv4_diagonal :
    (inv4 #[2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 8, 0, 0, 0, 0, 16]
      == some #[0.5, 0, 0, 0, 0, 0.25, 0, 0, 0, 0, 0.125, 0, 0, 0, 0, 0.0625]) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP metric.base.metric_contravariant.singular_raises : PROVEN
Source: base_metric.py:354-355. A zero row makes `np.linalg.inv` raise `LinAlgError`, and the model returns `none`. -/
theorem inv4_singular : (inv4 #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]).isNone = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Kerr-Newman electrodynamics -/

/-- PROP metric.kerrnewman.f_vec.coulomb_limit : PROVEN
Source: kerrnewman.py:324-374 and issue einsteinpy#144 (fixed by PR #687). A test charge `q / m = 1 C/kg` at rest `1000 m`
from a body of `1e-3 C` and `1 kg` (spin zero) accelerates radially at `q Q Cc / r^2`, to 9 digits. The scaling of the
Lorentz force holds in the model. -/
theorem coulomb_limit :
    (match knF ⟨.kn, .bl, 1.0, 0.0, 1.0e-3, 1.0⟩ #[0, 1000.0, 1.5707963267948966, 0, 1, 0, 0, 0] with
     | .ok v => relClose v[5]! (1.0 * 1.0e-3 * coulombsConst / (1000.0 * 1000.0)) 1e-9
     | .error _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- A concrete evaluation behind `Spec.em_tensor_contravariant_invariant_wrong`, with no `PROP` line of its own. For a
Reissner-Nordstrom hole the model's `F_{ab} F^{ab}`, with `F_cov` from `em_tensor_covariant` and `F^{ab}` from
`em_tensor_contravariant`, is `-2 (rQ / r^2)^2 / c^2` and not `-2 (rQ / r^2)^2`. -/
theorem contravariant_invariant_is_off_by_c_squared :
    (match emTensorCov ⟨.kn, .bl, 1.0e30, 0.0, 1.0e19, 0.0⟩ 5.0e3 1.2,
           emTensorContra ⟨.kn, .bl, 1.0e30, 0.0, 1.0e19, 0.0⟩ 5.0e3 1.2 with
     | .ok f, .ok fu =>
         let inv := (List.range 16).foldl (fun s n => s + f[n]! * fu[n]!) 0.0
         let e := geomCharge 1.0e19 / (5.0e3 * 5.0e3)
         relClose inv (-2.0 * e * e / cSq) 1e-6 && !relClose inv (-2.0 * e * e) 1e-6
     | _, _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

end EinsteinpyLean.Metric
