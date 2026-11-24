import EinsteinpyLean.Coordinates.Model

/-!
# Properties of the Coordinates model

Core Lean only. Statements about floating point evaluate the model, so they use `native_decide`:
Lean's kernel cannot unfold `Float` operations, and the compiled evaluation is exactly what
`epdiff_coordinates` ran against einsteinpy (50,000 agreeing cases on each of three seeds). Every refuted
property was rerun in real einsteinpy, see `bugs/coordinates-*.yaml` and `bugs/repro/coordinates-*.py`.
The statements over the reals (round trips, velocities as derivatives, `v0` as a root of the norm
equation) are in `Spec.lean`.

The model needs the C library functions as a record. Here Lean's own `Float.sin`, `Float.cos`,
`Float.acos` and `Float.atan2` are used, and `hypot` is `sqrt (a*a + b*b)`. Each property below is
true or false for any sensible C library, and each refutation is rerun in Python on the real library.
-/

namespace EinsteinpyLean.Coordinates

/-- Lean's own C library calls, for evaluating the model. -/
def nativeLibm : Libm :=
  ⟨fun a b => Float.sqrt (a * a + b * b), Float.atan2, Float.acos, Float.sin, Float.cos⟩

/-- `|a - b| ≤ tol * |b|`. -/
def relClose (a b tol : Float) : Bool := (a - b).abs ≤ tol * b.abs

/-- The `theta` of a converted state. -/
def theta? (r : Except Err State) : Option Float := r.toOption.map (·.p2)

/-! ## Cartesian to Boyer-Lindquist -/

/-- PROP coordinates.cartesian_to_bl.disc_total : REFUTED
Source: the Boyer-Lindquist chart covers the whole space, so `cartesian_to_bl` (utils.py:66-91)
should answer for every point. On the equatorial disc inside the ring, `z = 0` and `x² + y² < α²`,
`w < 0` makes `r = sqrt(0.5 * (w + |w|)) = 0`, and `theta = arccos(z / r)` divides by zero. The point
`(0.5, 0, 0)` with `α = 1` raises `ZeroDivisionError`. -/
theorem bl_disc_not_total :
    ¬ ∀ x : Float, (cartesianToBL nativeLibm 1 ⟨0, x, 0, 0, none⟩).toOption.isSome = true := by
  intro h
  have := h 0.5
  revert this
  -- native_decide: evaluates the compiled model, whose Float code the difftest checks
  native_decide

/-- PROP coordinates.cartesian_to_bl.near_disc_total : REFUTED
Source: as above. A point off the disc has `r > 0`, but `0.5 * (w + sqrt (w² + 4 α² z²))` cancels
when `w < 0`: at `(0.5, 0, 1e-9)` with `α = 1` the square root equals `|w|` in floating point,
so `r` is `0` (the true value is `1.15e-9`) and the conversion raises `ZeroDivisionError`. -/
theorem bl_near_disc_not_total :
    ¬ ∀ z : Float, (z == 0) = false →
      (cartesianToBL nativeLibm 1 ⟨0, 0.5, 0, z, none⟩).toOption.isSome = true := by
  intro h
  have := h 1e-9 (by native_decide)
  revert this
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP coordinates.cartesian_to_bl.near_disc_accuracy : REFUTED
Source: the same cancellation loses digits long before it fails. With `α = 1` the exact radius at
`(0.5, 0, 1e-7)` is `1.1547005383792489e-07`, and the model gives `1.1542389828584841e-07`,
which is wrong in the fourth digit. This property says the answer is within `1e-6` relative. -/
theorem bl_near_disc_radius_inaccurate :
    ¬ ∀ z : Float, (z == 0) = false →
      (match cartesianToBL nativeLibm 1 ⟨0, 0.5, 0, z, none⟩ with
        | .ok s => relClose s.p1 (z / Float.sqrt 0.75) 1e-6
        | .error _ => false) = true := by
  intro h
  have := h 1e-7 (by native_decide)
  revert this
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP coordinates.cartesian_to_bl.theta_near_axis : REFUTED
Source: for `α = 0` Boyer-Lindquist is spherical, and `cartesian_to_spherical` finds `theta` with
`arctan2`, which is accurate near the axis. `cartesian_to_bl` uses `arccos (z / r)`, and `z / r` rounds
to `1.0` for `x < 1.5e-8 z`, so at `(1e-9, 0, 1)` it answers `theta = 0` where the spherical
conversion answers `1e-9`. This property says the two agree to `1e-6` relative. -/
theorem bl_theta_near_axis_inaccurate :
    ¬ ∀ x : Float, 0 < x →
      (match theta? (cartesianToBL nativeLibm 0 ⟨0, x, 0, 1, none⟩),
          theta? (cartesianToSpherical nativeLibm ⟨0, x, 0, 1, none⟩) with
        | some a, some b => relClose a b 1e-6
        | _, _ => false) = true := by
  intro h
  have := h 1e-9 (by native_decide)
  revert this
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP coordinates.cartesian_to_bl.velocity_plane_x0 : REFUTED
Source: the Boyer-Lindquist velocity conversion (utils.py:49-62) should be defined where the position
conversion is, because `phi = arctan2 (y, x)` is smooth for `(x, y) ≠ (0, 0)`. It computes
`v_p` from `1 / (1 + (y / x)²) * (...) / x²`, which divides by `x`, so every point of the plane `x = 0`
raises `ZeroDivisionError`: here `(0, 2, 1)` with `α = 0.5` and any velocity. -/
theorem bl_velocity_not_total_on_x0 :
    ¬ ∀ y : Float, y ≠ 0 →
      (cartesianToBL nativeLibm 0.5 ⟨0, 0, y, 1, some (1, 1, 1)⟩).toOption.isSome = true := by
  intro h
  have := h 2 (by native_decide)
  revert this
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Boyer-Lindquist to Cartesian -/

/-- PROP coordinates.bl_to_cartesian.alpha_zero_negative_r : REFUTED
Source: with `α = 0` Boyer-Lindquist coordinates are spherical coordinates, so `bl_to_cartesian`
(utils.py:165-199) and `spherical_to_cartesian` should agree for every `r`. `bl_to_cartesian` takes
`sqrt (r² + α²)`, which is `|r|`, for the horizontal part and `r` for `z`. At `r = -1` the `x` of the two
differ in sign. A negative `r` is outside the physical domain of a spherical radius, so this is no bug
record, it only bounds the property (see `Spec.bl_alpha_zero` for `0 ≤ r`). -/
theorem bl_alpha_zero_fails_for_negative_r :
    ¬ ∀ r : Float,
      (match blToCartesian nativeLibm 0 ⟨0, r, 1.5, 0.25, none⟩,
          sphericalToCartesian nativeLibm ⟨0, r, 1.5, 0.25, none⟩ with
        | .ok a, .ok b => a.p1 == b.p1
        | _, _ => false) = true := by
  intro h
  have := h (-1)
  revert this
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## The conversion classes -/

/-- PROP coordinates.conversion.partial_velocities_dropped : REFUTED
Source: conversion.py:35-37 `_velocities_provided = not ((v_x is None) or (v_y is None) or (v_z is None))`.
The constructor documents each of `v_x`, `v_y`, `v_z` as optional, but a velocity that is given next to a
missing one is dropped without a word: with `v_y = None` the object holds position data only,
and `values()` and every conversion return the 4-tuple. This property says that a given `v_x` survives. -/
theorem partial_velocities_dropped :
    ¬ ∀ v : Float, ((mkState 0 1 2 3 (some v, none, some 3)).vel.isSome) = true := by
  intro h
  have := h 1
  revert this
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Time component of the 4-velocity -/

private def secs : Unit' := ⟨0, 0, 1, 0, false, 1.0⟩
private def metres : Unit' := ⟨1, 0, 0, 0, false, 1.0⟩
private def rads : Unit' := ⟨0, 0, 0, 1, false, 1.0⟩
private def mps : Unit' := ⟨1, 0, -1, 0, false, 1.0⟩
private def radps : Unit' := ⟨0, 0, -1, 1, false, 1.0⟩

/-- A particle at rest at `r = 10`, `θ = π/2` in spherical coordinates. -/
private def restArgs : List Quantity :=
  [⟨some secs, 0⟩, ⟨some metres, 10⟩, ⟨some rads, 1.5707963267948966⟩, ⟨some rads, 0⟩,
   ⟨some mps, 0⟩, ⟨some radps, 0⟩, ⟨some radps, 0⟩]

/-- The Schwarzschild metric of metric/schwarzschild.py:`_g_cov_s` at `r = 10` and `r_s = 2`, with `g_tt`
carrying `c²`. -/
private def schwarzschildG : Array Float :=
  let f := 0.8
  #[f * (cLight * cLight), 0, 0, 0,
    0, -1 / f, 0, 0,
    0, 0, -100, 0,
    0, 0, 0, -100]

/-- PROP coordinates.velocity.rest_value_is_speed : REFUTED
Source: differential.py:131-135 tags `v_t = v0(...)` as `m / s` (`self._v_t = v_t * u.m / u.s`), and
the docstrings call the other three components 3-velocities. With the Schwarzschild metric, whose
`g_tt` carries `c²`, `v0` solves `g_μν u^μ u^ν = c²` and returns `dt/dτ`, a pure number: a particle at
rest at `r = 10`, `r_s = 2` gets `v_t = 1.118`, not a speed of the order of `c`. The same function
returns `c` for `diag(1, -1, -1, -1)`. This is the unit mismatch that the author
commented on in einsteinpy issue 528. -/
theorem rest_v_t_is_not_a_speed :
    ¬ ((match velocity .spherical "Spherical" schwarzschildG restArgs with
        | .ok (vt :: _) => decide (vt > 1e8)
        | _ => false) = true) := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP coordinates.velocity.boyer_lindquist_message : REFUTED
Source: differential.py:525-527. The `CoordinateError` message of the Boyer-Lindquist class lacks the
`f` prefix of the other two classes, so it prints the text `{g.coords.system}` instead of the name of
the metric's system. This property says that the message names the system of the metric. -/
theorem bl_error_message_names_system :
    ¬ ∀ name : String, name ≠ "BoyerLindquist" →
      (match velocity .boyerLindquist name schwarzschildG
          [⟨some secs, 0⟩, ⟨some metres, 10⟩, ⟨some rads, 1⟩, ⟨some rads, 0⟩,
           ⟨some mps, 0⟩, ⟨some radps, 0⟩, ⟨some radps, 0⟩] with
        | .error (.coordinateError m) => (m.splitOn name).length > 1
        | _ => false) = true := by
  intro h
  have := h "Cartesian" (by decide)
  revert this
  -- native_decide: evaluates the compiled model
  native_decide

end EinsteinpyLean.Coordinates
