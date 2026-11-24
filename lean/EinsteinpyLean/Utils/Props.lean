import EinsteinpyLean.Utils.Dual
import EinsteinpyLean.Utils.DualMetrics
import EinsteinpyLean.Utils.Constants
import EinsteinpyLean.Utils.Exceptions

/-!
# Properties of the Utils model

Core Lean only. Statements about floating point evaluate the model, so they use `native_decide`:
Lean's kernel cannot unfold `Float` operations, and the compiled evaluation of the model is exactly what
`epdiff_utils` ran against einsteinpy. Each refuted property was rerun in real einsteinpy, see
`bugs/utils-*.yaml` and `bugs/repro/utils-*.py`. The statements over the reals are in `Spec.lean`.
-/

namespace EinsteinpyLean.Utils

/-! ## `DualNumber` -/

/-- PROP dual.pow.zero_power_at_zero : REFUTED
Source: the derivative of the constant `x ** 0` is `0`, and dual.py:118-119 `__pow__` is meant to
differentiate any power. At `val = 0` it evaluates `0.0 ** (0 - 1)` and raises `ZeroDivisionError`,
so `x ** 0` is not defined for every dual number. -/
theorem pow_zero_not_total :
    ¬ ∀ a : Dual Float, (Py.powS a (.int 0)).toOption.isSome = true := by
  intro h
  have := h ⟨0, 1⟩
  revert this
  -- native_decide: evaluates the compiled model, whose Float code the difftest checks
  native_decide

/-- PROP dual.truediv.quotient_overflow : REFUTED
Source: dual.py:87-91. The quotient `a / a` of a nonzero dual number should be `1 + 0 ε`. The code
squares the divisor with `other.val ** 2`, which raises `OverflowError` for `1e200`, although
`1e200 / 1e200` is `1.0`. -/
theorem div_self_not_total :
    ¬ ∀ a : Float, (a == 0) = false → (Py.divD ⟨a, 1⟩ ⟨a, 1⟩).toOption.isSome = true := by
  intro h
  have := h 1e200 (by native_decide)
  revert this
  native_decide

/-- PROP dual.truediv.zero_over_zero_derivative : REFUTED
Source: the quotient rule. `x * x / x` equals `x`, whose derivative is `1`. At `x = 0`
dual.py:84-85 answers `(0, 0)`, with derivative `0`, because it returns `self.deriv / other.deriv` as the value
and `0.0` as the derivative. -/
theorem xx_over_x_derivative_wrong :
    ((Py.divD (Py.mulD ⟨0, 1⟩ ⟨0, 1⟩) ⟨0, 1⟩).toOption.map (·.deriv) == some 1) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP dual.eq.plain_number_raises : REFUTED
Source: dual.py:112-113 `__eq__`. Equality with a plain number, `DualNumber(1, 0) == 1`, reads
`other.val` and raises `AttributeError` instead of answering a Boolean. -/
theorem eq_plain_number_not_boolean : ¬ ∃ b : Bool, Py.eqS = .ok b := by
  rintro ⟨b, h⟩
  cases h

/-- PROP dual.jacobian.diagonal_overflow : REFUTED
Source: dual.py:238 `J + J.T - np.diag(np.diag(J))`. A diagonal entry `x` becomes `(x + x) - x`,
which is `inf` when `2 x` overflows, although the derivative `1e308` is finite. -/
theorem jacobian_diagonal_not_exact :
    ((Py.jacobianG Py.scaled [1e308] [1, 1, 1, 1] (.int 0)).toOption.map (·[0]!) == some 1e308) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP dual.rsub.is_sub_of_literal : PROVEN
Source: dual.py:66-68 `__rsub__`. For a plain number the result is `DualNumber(c, 0) - self`, so the value
is `c - val` and the derivative is `0 - deriv`. This is the correct sign, for any number type. -/
theorem rsub_is_sub {α : Type} [Add α] [Sub α] [Mul α] [Neg α] (a : Dual α) (c z : α) :
    Dual.rsubS a c z = ⟨c - a.val, z - a.deriv⟩ := rfl

/-- PROP dual.add.comm : PROVEN
Source: dual.py:47-53, the ring structure of the dual numbers, here on exact rationals. -/
theorem add_comm (a b : Dual Rat) : Dual.add a b = Dual.add b a := by
  simp [Dual.add, Rat.add_comm]

/-- PROP dual.mul.comm : PROVEN
Source: dual.py:70-77. Multiplication commutes on exact rationals, so `__rmul__ = __mul__` is right. -/
theorem mul_comm (a b : Dual Rat) : Dual.mul a b = Dual.mul b a := by
  simp only [Dual.mul]
  rw [Rat.mul_comm a.val b.val, Rat.add_comm (a.deriv * b.val) (a.val * b.deriv),
    Rat.mul_comm a.deriv b.val, Rat.mul_comm a.val b.deriv]

/-- PROP dual.mul.epsilon_squared_zero : PROVEN
Source: dual.py:12 docstring, `ε² = 0` with `ε ≠ 0`. -/
theorem epsilon_sq : Dual.mul (⟨0, 1⟩ : Dual Rat) ⟨0, 1⟩ = ⟨0, 0⟩ := by
  -- native_decide: Rat arithmetic does not reduce under decide
  native_decide

/-- PROP dual.sin.at_zero : PROVEN
Source: `d/dx sin x = cos x` at `0`: the model gives value `0` and derivative `1`. -/
theorem sin_at_zero : Py.sinD ⟨0, 1⟩ = ⟨0, 1⟩ := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Exceptions and `primitive` -/

/-- PROP exceptions.base_error.no_args_message : PROVEN
Source: exceptions.py:23-24. With no arguments the message is empty and `str` is `ClassName : `. -/
theorem errorRepr_nil (cls : String) : errorRepr cls [] = cls ++ " : " := by
  simp [errorRepr, message, toString, String.append_empty]

/-- PROP units.primitive.idempotent : PROVEN
Source: units.py:20-26. Stripping units twice changes nothing. -/
theorem primitive_idem (l : List PrimArg) : primitive (primitive l) = primitive l := by
  simp only [primitive, List.map_map]
  congr 1
  funext a
  cases a <;> rfl

/-- The first number of a list of arguments. -/
def firstNum : List PrimArg → Option Float
  | .npFloat x :: _ => some x
  | _ => none

/-- PROP units.primitive.keeps_the_given_unit : PROVEN
Source: units.py:8-26. `primitive` takes `.value` in whatever unit the quantity has, with no
conversion to SI. One kilometre and one thousand metres are the same length and give different numbers. -/
theorem primitive_depends_on_unit :
    (firstNum (primitive [.quantity 1 "km"]) == firstNum (primitive [.quantity 1000 "m"])) = false := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Scale factor -/

/-- PROP scalar_factor.md.normalised_at_one_second : PROVEN
Source: scalar_factor.py:28-29. `a(1 s) = tuning_param` for the matter and radiation eras, and
`a(0 s) = tuning_param` for the dark energy era. -/
theorem scale_factor_normalisation :
    ((scalarFactor (some "md") 2 1).toOption == some 2) = true ∧
    ((scalarFactor (some "rd") 2 1).toOption == some 2) = true ∧
    ((scalarFactor (some "ded") 2 0).toOption == some 2) = true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-- PROP scalar_factor.derivative.infinite_at_big_bang : PROVEN
Source: `d/dt t^(2/3) = (2/3) t^(-1/3)` diverges at `t = 0`, and the model gives `inf` like numpy. -/
theorem derivative_at_zero_is_inf :
    ((scalarFactorDerivative (some "md") 1 0).toOption.map Float.isInf) = some true := by
  -- native_decide: evaluates the compiled model
  native_decide

/-! ## Constants and bodies -/

/-- Relative closeness of two floats. -/
def relClose (a b tol : Float) : Bool := (a - b).abs ≤ tol * b.abs

/-- PROP constant.solar_mass.gm_over_g : PROVEN
Source: constant.py:39-40, the IAU 2015 nominal `GM_sun = 1.3271244e20 m³/s²`. `Solar_Mass * G`
returns it to 12 digits. -/
theorem solar_mass_gm : relClose (solarMass * gravConst) 1.3271244e20 1e-12 = true := by
  -- native_decide: evaluates Float multiplication
  native_decide

/-- PROP constant.coulombs_const.value : PROVEN
Source: `1 / (4 π ε0)` with CODATA 2022 `ε0` is `8.9875517923e9 N m²/C²`. -/
theorem coulomb_value : relClose coulombsConst 8.9875517923e9 1e-9 = true := by
  -- native_decide: evaluates Float arithmetic
  native_decide

/-- PROP constant.cosmo_const.planck_lambda : PROVEN
Source: Planck 2018 `Λ = 1.1056e-52 m⁻²`. `Cosmo_Const / c²` agrees to 0.1 percent, so the
`Cosmo_Const = Λ c²` convention used by `scalar_factor` is dimensionally consistent. -/
theorem cosmo_const_planck : relClose (cosmoConst / (speedOfLight * speedOfLight)) 1.1056e-52 1e-3 = true := by
  -- native_decide: evaluates Float arithmetic
  native_decide

/-- PROP scalar_factor.ded.hubble_squared : PROVEN
Source: scalar_factor.py:36. The dark energy rate `H = sqrt(Cosmo_Const / 3)` satisfies `H² = Λ c² / 3`. -/
theorem hubble_squared : relClose (hubbleConst * hubbleConst) (cosmoConst / 3) 1e-14 = true := by
  -- native_decide: evaluates Float arithmetic
  native_decide

/-- Surface gravity `G M / R²` in m/s² of a body row, with the radius in km. -/
def surfaceGravity (b : BodyRow) : Float := gravConst * b.mass / (b.radius * 1000 * (b.radius * 1000))

/-- PROP bodies.surface_gravity.earth_moon : PROVEN
Source: textbook values `g = 9.80665` m/s² on Earth and `1.62` m/s² on the Moon. The tabulated
mass and radius reproduce them to 1 percent. -/
theorem earth_moon_gravity :
    (bodies.find? (·.name == "Earth")).map (fun b => relClose (surfaceGravity b) 9.80665 1e-2) = some true ∧
    (bodies.find? (·.name == "Moon")).map (fun b => relClose (surfaceGravity b) 1.62 1e-2) = some true := by
  -- native_decide: evaluates Float arithmetic
  native_decide

/-- PROP bodies.table.parents : PROVEN
Source: bodies.py:105-131. Moon orbits Earth, Earth and every other planet orbit the Sun, the Sun has no parent. -/
theorem body_parents :
    (bodies.map fun b => (b.name, b.parent)) =
      [("Sun", none), ("Earth", some "Sun"), ("Moon", some "Earth"), ("Mercury", some "Sun"),
       ("Venus", some "Sun"), ("Mars", some "Sun"), ("Jupiter", some "Sun"), ("Saturn", some "Sun"),
       ("Uranus", some "Sun"), ("Neptune", some "Sun"), ("Pluto", some "Sun")] := by
  rfl

end EinsteinpyLean.Utils
