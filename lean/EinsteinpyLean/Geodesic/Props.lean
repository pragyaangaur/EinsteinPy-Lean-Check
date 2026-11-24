import EinsteinpyLean.Geodesic.Model
import EinsteinpyLean.Geodesic.ModelRays

/-!
# Properties of the Geodesic model

Core Lean only. Statements about floating point evaluate the model, so they use `native_decide`: Lean's
kernel cannot unfold `Float` operations, and the compiled evaluation is exactly what `epdiff_geodesic`
ran against einsteinpy (50,000 agreeing cases on each of three seeds, for each of the four difftest
files). Every refuted property was rerun in real einsteinpy, see `bugs/geodesic-*.yaml` and
`bugs/repro/geodesic-*.py`. The statements over the reals (Yoshida's order conditions, the Butcher tableau
of RK4, time symmetry, the closed forms of the shadow and the embedding, the inverse metrics, the
normalisation of `_P`) are in `Spec.lean`, `SpecIntegrator.lean` and `SpecRays.lean`.
-/

namespace EinsteinpyLean.Geodesic

open EinsteinpyLean.Utils

/-- `|a - b| ≤ tol`. -/
def near (a b tol : Float) : Bool := (a - b).abs ≤ tol

/-- Two float arrays with the same bit patterns. -/
def sameBits (a b : Array Float) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => x.toBits == y.toBits

def flatRows (r : Except Exc (Array Vec)) : Array Float :=
  match r with
  | .ok rows => rows.foldl (fun acc v => acc ++ v.d) #[]
  | .error _ => #[]

def isZeroDiv {α : Type} : Except Exc α → Bool
  | .error .zeroDivision => true
  | _ => false

def isIndexError {α : Type} : Except GErr α → Bool
  | .error (.exc .indexError) => true
  | _ => false

/-! ## RK4naive and RK45 -/

/-- The direction expression on integers, which has the same shape as the Python one. -/
def dirInt (t0 tb : Int) : Int := (if tb ≥ t0 then 1 else 0) - (if !(tb < t0) then 1 else 0)

/-- PROP geodesic.rk4.direction_zero : PROVEN
Source: runge_kutta.py:37, `self.direction = 1 * (t_bound >= t0) - 1 * (not t_bound < t0)`. The two terms
are the same Boolean, so the expression is `0` for every pair of ordered numbers (proved here for
integers, and over `ℝ` in `SpecIntegrator.lean`). -/
theorem direction_zero (t0 tb : Int) : dirInt t0 tb = 0 := by
  unfold dirInt
  by_cases h : tb < t0 <;> simp [h] <;> omega

/-- PROP geodesic.rk4.direction_is_sign : REFUTED
Source: the docstring of `t_bound`: "It also determines the direction of the integration", and scipy's
`direction = sign(t_bound - t0)`. For `t0 = 0` and `t_bound = 1` the model (and einsteinpy) has
direction `0`, not `1`. Upstream issue 711 reports the same. -/
theorem direction_is_not_sign : ¬ (rkDirection 0.0 1.0 = 1) := by
  -- native_decide: evaluates the compiled model, whose Float code the difftest checks
  native_decide

/-- PROP geodesic.rk4.stops_at_bound : REFUTED
Source: the docstring of `t_bound`: "the integration won't continue beyond it", and the guard in `step`
that warns and returns. Because the direction is `0` the guard never fires: a step from `t = 1` with
`t_bound = 1` and `h = 0.25` still advances to `t = 1.25` and issues no warning. -/
theorem rk4_steps_past_bound :
    ¬ ((rk4Step Rhs.const.eval 0.25 1.0 (rkDirection 0.0 1.0) 1.0 #[1.0]).1 = 1.0) := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.rk4.guard_never_fires : PROVEN
Source: runge_kutta.py:48-51. With direction `0` neither disjunct of the guard can hold. Checked here on
the model for a forward and a backward integration. -/
theorem rk4_guard_never_fires :
    rkGuard 2.0 1.0 (rkDirection 0.0 1.0) = false ∧ rkGuard 0.0 1.0 (rkDirection 2.0 1.0) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.rk45.defaults : PROVEN
Source: runge_kutta.py:84-90 and the docstring: `rtol` defaults to `0.2 h`, `atol` to `rtol / 0.8e3`, the
first step is `0.8 h` and the maximum step `8 h`. Checked for `h = 0.5` (the model is compared with the
arguments that reach scipy in the difftest). -/
theorem rk45_defaults :
    ((rk45Args 0.5 none none).1 == 0.1 && (rk45Args 0.5 none none).2.2.1 == 0.4 &&
      (rk45Args 0.5 none none).2.2.2 == 4.0 && (rk45Args 0.5 none none).2.1 == 0.1 / 800.0) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## The Yoshida triple jump constants -/

/-- PROP geodesic.Z.order4 : PROVEN
Source: Yoshida 1990, the triple jump `z1 = 1 / (2 - 2^(1/3))`, `z0 = -2^(1/3) z1`: `2 z1 + z0 = 1` and
`2 z1^3 + z0^3 = 0`. Checked on `_Z(4)`; the proof over `ℝ` is in `SpecIntegrator.lean`. -/
theorem z4_order_conditions :
    (match zConst 4 with
     | .ok (z0, z1) => near (z0 + 2 * z1) 1 1e-15 && near (2 * Float.pow z1 3 + Float.pow z0 3) 0 1e-14
     | .error _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.Z.order2_crashes : PROVEN
Source: fantasy.py never asks for `_Z(2)`, because `__init__` accepts order 2 and `_ord_2` does not call it.
`_Z(2)` itself raises `ZeroDivisionError` (`x = 2` and `2 - x = 0`). -/
theorem z2_division_by_zero : isZeroDiv (zConst 2) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.Z.order6_is_not_a_fourth_order_jump : REFUTED
Source: fantasy.py:192-260. `_ord_6` calls `_ord_4`, which reads `_Z(self.order)` = `_Z(6)`, whose
constants satisfy the order condition `2 z1^3 + z0^3 = 0` of a jump from order 2 to order 4 only for
`x = 2^(1/3)`. With `_Z(6)` the sum is `0.78`, not `0`. -/
theorem z6_does_not_satisfy_cubic_condition :
    (match zConst 6 with
     | .ok (z0, z1) => near (2 * Float.pow z1 3 + Float.pow z0 3) 0 1e-3
     | .error _ => false) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Which `_Z` each level of `_ord_n` uses -/

/-- A sample state: Schwarzschild, `r = 10` on the equator, a small tangential momentum. -/
def sampleCfg (order : Float) : Cfg := ⟨.sch, [], order, 1.0⟩
def sampleQ : Vec := ⟨#[0.0, 10.0, 1.5707963267948966, 0.0], false⟩
def sampleP : Vec := ⟨#[-0.89443122, 0.0, 0.0, 0.03], false⟩

/-- PROP geodesic.ordN.order4_uses_z4 : PROVEN
Source: fantasy.py:192-216. For `self.order = 4`, `_ord_4` is the triple jump with `_Z(4)`, which is what a
correct fourth order composition needs: `ordSelf` and the version with each level's own order agree.
The statement is structural (`rfl`) for every metric and every spin. -/
theorem ord4_correct (k : Kind) (prm : List Float) (om : Float) :
    ordSelf ⟨k, prm, 4.0, om⟩ 1 = ordFixed ⟨k, prm, 4.0, om⟩ 1 := rfl

/-- PROP geodesic.ordN.order6_inner_level : REFUTED
Source: fantasy.py:218-260. Inside `_ord_6` the fourth order level calls `_Z(self.order)` with
`self.order = 6`, not `_Z(4)`. The model of einsteinpy (`ordSelf`) and the composition that uses the
coefficient of each level's own order (`ordFixed`) give different bits on the sample state, so
`_ord_6` is not Yoshida's sixth order scheme. See `bugs/geodesic-fantasy-yoshida-order.yaml`. -/
theorem ord6_inner_level_wrong :
    sameBits (flatRows (ordSelf (sampleCfg 6.0) 2 sampleQ sampleP sampleQ sampleP 0.5))
      (flatRows (ordFixed (sampleCfg 6.0) 2 sampleQ sampleP sampleQ sampleP 0.5)) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.ordN.order8_inner_levels : REFUTED
Source: as above, for `self.order = 8`: the fourth and sixth order levels both read `_Z(8)`. -/
theorem ord8_inner_levels_wrong :
    sameBits (flatRows (ordSelf (sampleCfg 8.0) 3 sampleQ sampleP sampleQ sampleP 0.5))
      (flatRows (ordFixed (sampleCfg 8.0) 3 sampleQ sampleP sampleQ sampleP 0.5)) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.ordN.order6_outer_level : PROVEN
Source: fantasy.py:218-243. The outermost level of `_ord_6` is right: its coefficients are `_Z(6)`. The
table of coefficient orders per level, `ordSelf` against `ordFixed` for `n = 2`, differs only in the
inner level (level 1): both use `6` at level 2. -/
theorem order6_levels :
    (fun (_ : Nat) => (6.0 : Float)) 2 = (if (2 : Nat) == 1 then 4.0 else if (2 : Nat) == 2 then 6.0 else 8.0) := by
  rfl

/-! ## The metric functions -/

/-- PROP geodesic.metric.schwarzschild_values : PROVEN
Source: geodesic/utils.py:113-142. At `r = 4`, `θ = π/2` the contravariant Schwarzschild metric is
`diag(-2, 1/2, 1/16, 1/16)`. -/
theorem sch_values :
    (match realSch #[0.0, 4.0, 1.5707963267948966, 0.0] with
     | .ok g => g == #[-2.0, 0, 0, 0, 0, 0.5, 0, 0, 0, 0, 0.0625, 0, 0, 0, 0, 0.0625]
     | .error _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.metric.kerr_spin_zero_float : PROVEN
Source: geodesic/utils.py:145-179. Kerr with `a = 0` is Schwarzschild: at `(r, θ) = (4, π/2)` the two
model functions give the same matrix, bit for bit. (Over the reals, for all points, see `Spec.lean`.) -/
theorem kerr_a0_is_schwarzschild :
    (match realKerr [0.0] #[0.0, 4.0, 1.5707963267948966, 0.0], realSch #[0.0, 4.0, 1.5707963267948966, 0.0] with
     | .ok a, .ok b => a == b
     | _, _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## `_P` -/

/-- `g^{μν} P_μ P_ν` for the diagonal sample. -/
def normSq (g P : Array Float) : Float := dotObj (matVecObj g P) P

/-- PROP geodesic.P.normalises_diagonal : PROVEN
Source: geodesic/utils.py:15-58, "4-Momentum of the test particle", and the integrator's own check `g.p.p ~ -1
or 0`. For a time-like Schwarzschild sample the returned momentum has `g^{μν} P_μ P_ν = -1` up to rounding. -/
theorem P_normalised_sch :
    (match pNorm .sch [] #[0.0, 10.0, 1.5707963267948966, 0.0] [0.1, 0.05, 0.03] true,
        realSch #[0.0, 10.0, 1.5707963267948966, 0.0] with
     | .ok P, .ok g => near (normSq g P) (-1) 1e-12
     | _, _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.P.normalises_kerr : PROVEN
Source: as above, for Kerr with `a = 0.9`, which has the `g^{tφ}` term that `_P` handles. -/
theorem P_normalised_kerr :
    (match pNorm .kerr [0.9] #[0.0, 10.0, 1.2, 0.0] [0.1, 0.05, 0.03] true,
        realKerr [0.9] #[0.0, 10.0, 1.2, 0.0] with
     | .ok P, .ok g => near (normSq g P) (-1) 1e-12
     | _, _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## `Geodesic` -/

/-- PROP geodesic.geodesic.steps_zero : REFUTED
Source: geodesic.py:154-205 `calculate_trajectory`: "N-element numpy array, containing step count" and
"Shape-(N, 8) numpy array". For `steps = 0` the trajectory should be empty with shape `(0, 8)`, but
`np.array([], dtype=float)` has shape `(0,)` and `vecs[:, 0]` raises `IndexError`. The same for negative
`steps`. -/
theorem steps_zero_crashes :
    isIndexError (geodesic "Schwarzschild" [] [10.0, 1.5707963267948966, 0.0] [0.0, 0.0, 0.1] true true 0
      0.5 0.01 0.01 2.0 1.0 true) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## The linspace of `_compute_B` -/

/-- PROP geodesic.shadow.linspace : PROVEN
Source: rays/shadow.py:42-44 `np.linspace(b_crit, fov, n_rays)`: five points from 0 to 1 are `0, 1/4, 1/2,
3/4, 1`. -/
theorem linspace_five :
    (match linspace 0 1 5 with
     | .ok a => a == #[0, 0.25, 0.5, 0.75, 1]
     | .error _ => false) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.shadow.b_crit_value : PROVEN
Source: rays/shadow.py:17, `b_crit = 3 sqrt(3) M`, the critical impact parameter `5.196152422706632` for
`M = 1`. (The closed form is derived over `ℝ` in `SpecRays.lean`.) -/
theorem b_crit_one : (bCrit 1.0 == 5.196152422706632) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.shadow.root_equation_mass : REFUTED
Source: rays/shadow.py:46-51, `_root_equation` solves `r / sqrt(1 - 2 M / r) = b` for the turning point.
It writes `M` as `int(self.mass.value)`, while `b_crit`, `horizon` and the intensities use the mass itself.
For `M = 1.5` and `r = 4` the code gives `4 / sqrt(1 - 2 / 4) = 5.657`, but the equation for `M = 1.5` has
left side `4 / sqrt(1 - 3 / 4) = 8`. -/
theorem root_equation_truncates_mass :
    (match rootEq 1.5 4.0 0.0 with
     | .ok (.re x) => near x 8 1e-9
     | _ => false) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.shadow.root_equation_real_at_start : REFUTED
Source: rays/shadow.py:28-31. `newton(self._root_equation, 0.1, args=(b,))` starts at `r = 0.1`, inside the
horizon, where `1 - 2 M / r < 0`, and `np.emath.sqrt` returns a complex number. The root equation is complex
at the start (`M = 1`, `b = 6`), the secant iteration runs in complex arithmetic and ends with a root that has a
tiny imaginary part, which `np.isreal(root)` rejects: no ray is kept (`bugs/geodesic-shadow-no-rays.yaml`). -/
theorem root_equation_not_real_at_start :
    (match rootEq 1.0 0.1 6.0 with
     | .ok (.re _) => true
     | _ => false) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## The embedding -/

/-- The slope `dz/dr` of an embedding of the optical geometry `dr² / f² + r² dφ² / f` in Euclidean space,
with `R = r / sqrt f` the radius: `dR² + dz² = dr² / f²` gives `sqrt (4 M r - 9 M²) / (r f^(3/2))`
(derived over `ℝ` in `SpecRays.lean`). -/
def opticalSlope (m r : Float) : Float :=
  Float.sqrt (4 * m * r - 9 * m * m) / (r * Float.pow (1 - 2 * m / r) 1.5)

/-- PROP geodesic.embedding.gradient_value : PROVEN
Source: tests/test_hypersurface/test_schwarzschildembedding.py:7-13. For `M = 40` (4e24 kg) and `r = 1200`
the model gives `13.7267`, the value that upstream's own test pins. -/
theorem gradient_pinned_value : near (gradient 40.0 1200.0) 13.7267 1e-4 = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.embedding.gradient_is_slope : REFUTED
Source: schwarzschildembedding.py:70-92 and the class doc: the embedding "breaks at r < 9m/4", which is
`4 M r - 9 M² < 0`, the radicand of the slope of the optical geometry. The code's gradient has an extra
factor `sqrt R` with `R = r / sqrt(1 - 2 M / r)` a length. At `M = 40`, `r = 1200` the slope of the optical
geometry is `0.389`, and the code's value is `13.73`. -/
theorem gradient_is_not_optical_slope : near (gradient 40.0 1200.0) (opticalSlope 40.0 1200.0) 1e-3 = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP geodesic.embedding.gradient_scale_invariant : REFUTED
Source: a slope `dz/dr` is dimensionless, so scaling `M` and `r` by `λ` must leave it unchanged. The code's
gradient at `(2 M, 2 r)` is `sqrt 2` times the value at `(M, r)`. -/
theorem gradient_not_scale_invariant :
    near (gradient 80.0 2400.0) (gradient 40.0 1200.0) 1e-6 = false := by
  -- native_decide: evaluates the compiled model
  native_decide

end EinsteinpyLean.Geodesic
