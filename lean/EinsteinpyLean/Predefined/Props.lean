import EinsteinpyLean.Predefined.Model

/-!
# Properties of the Predefined model

Concrete properties of the executable model, on exact rationals. Every `native_decide`
below only evaluates the model on specific numbers (`Rat` arithmetic and `Except`), so the
compiler is trusted for nothing more than running that evaluation.

The physics (Ricci flatness of the vacuum metrics, `R_ab = Lambda g_ab`, the
Einstein-Maxwell checks) cannot be stated in core Lean. It was checked with einsteinpy
itself, see `bugs/repro/` and the notes in `Spec.lean`.
-/

namespace EinsteinpyLean.Predefined.Props
open Arr EinsteinpyLean.Predefined

/-- The model result as an `Option`, to compare with `==`. -/
def val (m : M Arr) : Option Arr := m.toOption

/-- Negate every entry of a metric. -/
def neg (a : Arr) : Arr := ⟨a.shape, a.data.map (- ·)⟩

/-- PROP predefined.minkowski.c_one_signature : PROVEN
Source: minkowski.py:19. With `c = 1` the Cartesian Minkowski metric is
`diag(-1, 1, 1, 1)`, signature `(-, +, +, +)`. -/
theorem mink_c_one : val (minkowskiCartesian 1) = some (diag4 (-1) 1 1 1) := by
  -- native_decide: evaluates the model at c = 1.
  native_decide

/-- PROP predefined.minkowski.c_zero_fails : PROVEN
Source: minkowski.py:19, `1 / c**2` at `c = 0`. -/
theorem mink_c_zero : val (minkowskiCartesian 0) = none := by
  -- native_decide: evaluates the model at c = 0.
  native_decide

/-- PROP predefined.schwarzschild.flat_limit_signature : PROVEN
Source: vacuum_solutions.py:25-27. With `r_s = 0`, `c = 1` the Schwarzschild metric is
the flat metric in polar coordinates with signature `(+, -, -, -)`, here at `r = 2`,
`sin theta = 3/5`. -/
theorem schw_flat_limit :
    val (schwarzschild 1 0 2 (3 / 5)) = some (diag4 1 (-1) (-4) (-(4 * (9 / 25)))) := by
  -- native_decide: evaluates the model at concrete numbers.
  native_decide

/-- PROP predefined.signature.minkowski_matches_schwarzschild_flat : REFUTED
Source: both functions describe flat spacetime (minkowski.py docstring, and
vacuum_solutions.py with `sch = 0`), so one expects the same time-time component. They have
opposite signs: Minkowski is `(-, +, +, +)` and Schwarzschild, Kerr, Kerr-Newman and
Reissner-Nordstrom are `(+, -, -, -)`. This states the negation with a counterexample. -/
theorem signature_mismatch :
    ∃ r s : Rat, (val (minkowskiCartesian 1)).map (·.get [0, 0]) ≠
      (val (schwarzschild 1 0 r s)).map (·.get [0, 0]) :=
  ⟨2, 0, by native_decide⟩

/-- Not a property: at `c = 1` the model of JNW with `gam = 1` is minus the model of
Schwarzschild with `r_s = 2 G M`, so the two agree up to the signature. -/
theorem jnw_gamma_one_c_one :
    val (jnw 1 1 1 (1 / 2) 5 (3 / 5)) = (val (schwarzschild 1 1 5 (3 / 5))).map neg := by
  -- native_decide: evaluates the model at concrete numbers.
  native_decide

/-- PROP predefined.jnw.gamma_one_is_schwarzschild : REFUTED
Source: janis_newman_winicour.py docstring, "for gamma=1 this will return the Schwarzschild
metric", with `r_s = 2 G M / c**2` (janis_newman_winicour.py:26). Even after allowing for the
opposite signature, the angular components are not divided by `c**2` (lines 33-34) while
`g_rr` is, so for `c = 2` the two differ. This is the bug that einsteinpy PR 710 fixes. -/
theorem jnw_gamma_one_not_schwarzschild :
    ∃ c g m r s : Rat, val (jnw c g 1 m r s) ≠
      (val (schwarzschild c (2 * g * m / (c * c)) r s)).map neg :=
  ⟨2, 1, 1, 5, 3 / 5, by native_decide⟩

/-- PROP predefined.alcubierre.far_field_is_flat : PROVEN
Source: alcubierre_warp.py:44-50. Where the two `tanh` values agree, `f = 0` and the metric
is `diag(-1, 1, 1, 1)` whatever `v` is. -/
theorem alcubierre_far_field : val (alcubierre (7 / 10) (1 / 3) (1 / 3) (1 / 2)) =
    some (diag4 (-1) 1 1 1) := by
  -- native_decide: evaluates the model at concrete numbers.
  native_decide

/-- PROP predefined.kerr.zero_spin_is_schwarzschild : PROVEN
Source: vacuum_solutions.py:50-65. With `a = 0` Kerr gives the Schwarzschild components, here
for `c = 3/2`, `r_s = 2/5`, `r = 7/3`, `sin theta = 3/5`, `cos theta = 4/5`. -/
theorem kerr_zero_spin : val (kerr (3 / 2) (2 / 5) 0 (7 / 3) (3 / 5) (4 / 5)) =
    val (schwarzschild (3 / 2) (2 / 5) (7 / 3) (3 / 5)) := by
  -- native_decide: evaluates the model at concrete numbers.
  native_decide

/-- PROP predefined.kerr_newman.zero_charge_is_kerr : PROVEN
Source: vacuum_solutions.py:99-115. With `Q = 0` Kerr-Newman gives the Kerr components,
here for `pi = 22/7`. -/
theorem kn_zero_charge : val (kerrNewman (3 / 2) 1 2 (2 / 5) (1 / 3) 0 (22 / 7) (7 / 3) (3 / 5) (4 / 5)) =
    val (kerr (3 / 2) (2 / 5) (1 / 3) (7 / 3) (3 / 5) (4 / 5)) := by
  -- native_decide: evaluates the model at concrete numbers.
  native_decide

/-- PROP predefined.reissner_nordstrom.zero_charge_is_schwarzschild : PROVEN
Source: vacuum_solutions.py:147-156. With `Q = 0` the metric is the Schwarzschild one. -/
theorem rn_zero_charge : val (reissnerNordstrom (3 / 2) 1 2 (2 / 5) 0 (22 / 7) (7 / 3) (3 / 5)) =
    val (schwarzschild (3 / 2) (2 / 5) (7 / 3) (3 / 5)) := by
  -- native_decide: evaluates the model at concrete numbers.
  native_decide

/-- The Python parameter list of `BertottiKasner` (bertotti_kasner.py:7). -/
def bkSignature : List String := ["c", "k", "lambd"]

/-- The parameters its docstring documents (bertotti_kasner.py:15-19). -/
def bkDocumented : List String := ["c", "lambd"]

/-- PROP predefined.bertotti_kasner.docstring_matches_signature : REFUTED
Source: bertotti_kasner.py:7 and :15-19. The signature has a second parameter `k` that no line
uses and the docstring does not mention, so `BertottiKasner(c, 2)` silently sets `k`, not the
cosmological constant. The model has no `k` because the formula never reads it
(`bertottiKasner` takes `c lambd e s`). -/
theorem bk_docstring_mismatch : bkSignature ≠ bkDocumented := by decide

/-- PROP predefined.find.kerr_family : PROVEN
Source: find.py:19-25. Searching `kerr` returns the three Kerr functions, in `dir` order. -/
theorem find_kerr : find "kerr" = ["Kerr", "KerrNewman", "KerrNewmanDeSitter"] := by
  -- native_decide: evaluates the model.
  native_decide

/-- PROP predefined.find.correct_spelling_of_reissner_nordstrom : REFUTED
Source: find.py:19-25 and `ReissnerNordstorm` in `predefined/__init__.py:15`. The function is
spelled `ReissnerNordstorm` (an `o` for the `ö`), so searching the usual spelling
`nordstrom` finds nothing. The same holds for `BarriolaVilekin` and `vilenkin`. -/
theorem find_nordstrom : find "nordstrom" ≠ ["ReissnerNordstorm"] := by
  -- native_decide: evaluates the model.
  native_decide

/-- PROP predefined.constants.get_constant_lambda_key : PROVEN
Source: constants.py:61-62. The constant called `Lambda` is only reachable with the key
`Cosmo_Const`; the key `Lambda` is a `KeyError`. -/
theorem get_constant_lambda_key :
    getConstant initialTable "Lambda" = none ∧
    getConstant initialTable "Cosmo_Const" = some ("Lambda", some "Cosmological Constant") := by
  -- native_decide: evaluates the model.
  native_decide

/-- PROP predefined.constants.new_constant_keeps_global : REFUTED
Source: constants.py:10-28. One expects `SymbolicConstant("c")` to build a fresh object and
leave `constants.c` alone. sympy caches `Symbol.__new__` by name, so it returns the same
object and line 27 overwrites its descriptive name. After the call `get_constant("c")` has
no descriptive name any more. -/
theorem new_constant_overwrites_global :
    getConstant (construct initialTable "c" none) "c" ≠ getConstant initialTable "c" := by
  -- native_decide: evaluates the model.
  native_decide

end EinsteinpyLean.Predefined.Props
