/-!
# Model of `einsteinpy.constant`, `scalar_factor.py`, `units.py`, `exceptions.py`, `bodies.py`

Mirrors `src/einsteinpy/constant.py`, `utils/scalar_factor.py`, `units.py`, `utils/exceptions.py`
and `bodies.py` at commit `63e1c54`. Core Lean only. The constants are the doubles that astropy 8.0.3
(CODATA 2022, Planck18, IAU 2015) gives, written as IEEE bit patterns with the decimal in a comment.
-/

namespace EinsteinpyLean.Utils

/-! ## Constants (constant.py) -/

/-- constant.py:15 `c = constants.c`, in m/s (exact). -/
def speedOfLight : Float := Float.ofBits 0x41b1de784a000000
/-- constant.py:16 `G`, 6.6743e-11 m³ kg⁻¹ s⁻² (CODATA 2022). -/
def gravConst : Float := Float.ofBits 0x3dd2589effed8acc
/-- constant.py:17 `eps0`, 8.8541878188e-12 F/m (CODATA 2022). -/
def eps0 : Float := Float.ofBits 0x3da37876f1591150
/-- `numpy.pi`. -/
def npPi : Float := Float.ofBits 0x400921fb54442d18
/-- constant.py:18 `coulombs_const = 1 / (4 * np.pi * eps0)`. -/
def coulombsConst : Float := 1 / (4 * npPi * eps0)
/-- constant.py:27-31 `Cosmo_Const` in s⁻², 9.935883363094694e-36, which is Λ c² = 3 H0² Ω_Λ for
Planck18 (H0 = 67.66 km/s/Mpc, Ω_Λ = 0.6888463...). -/
def cosmoConst : Float := Float.ofBits 0x38aa6a030667c78c
/-- constant.py:40 `Solar_Mass` in kg, 1.988409870698051e30 (IAU 2015 GM and CODATA 2022 G). -/
def solarMass : Float := Float.ofBits 0x463918e618481f55
/-- constant.py:41 `R_sun` in km, exactly 695700. -/
def rSun : Float := Float.ofBits 0x41253b2800000000

/-- Values by name, as `constant.<name>.value`. -/
def constByName : String → Option Float
  | "c" => some speedOfLight
  | "G" => some gravConst
  | "eps0" => some eps0
  | "coulombs_const" => some coulombsConst
  | "Cosmo_Const" => some cosmoConst
  | "Solar_Mass" => some solarMass
  | "R_sun" => some rSun
  | _ => none

/-! ## Units -/

/-- Dimension of a unit, as far as `u.quantity_input` cares. -/
inductive Dim where
  | time | mass | charge | length | other
  deriving Repr, BEq, DecidableEq

/-- The units the difftests use, with the dimension and the factor to the SI-like base unit that
astropy uses in `Quantity.to`: seconds for time, kg, C, km. The base unit has factor 1. -/
def unitInfo : String → Option (Dim × Float)
  | "s" => some (.time, 1)
  | "ms" => some (.time, Float.ofBits 0x3f50624dd2f1a9fc)
  | "us" => some (.time, Float.ofBits 0x3eb0c6f7a0b5ed8d)
  | "ks" => some (.time, 1000)
  | "min" => some (.time, 60)
  | "h" => some (.time, 3600)
  | "d" => some (.time, 86400)
  | "yr" => some (.time, 31557600)
  | "Myr" => some (.time, Float.ofBits 0x42bcb39389b80000)
  | "Gyr" => some (.time, Float.ofBits 0x435c075e147db000)
  | "kg" => some (.mass, 1)
  | "g" => some (.mass, 1)
  | "Msun" => some (.mass, 1)
  | "C" => some (.charge, 1)
  | "mC" => some (.charge, 1)
  | "km" => some (.length, 1)
  | "m" => some (.length, 1)
  | "au" => some (.length, 1)
  | "pc" => some (.length, 1)
  | "Hz" => some (.other, 1)
  | "deg" => some (.other, 1)
  | "dimless" => some (.other, 1)
  | "statC" => some (.other, 1)
  | _ => none

/-- astropy's message when an argument has no `unit` attribute. -/
def noUnitMsg (arg fn : String) : String :=
  s!"Argument '{arg}' to function '{fn}' has no 'unit' attribute. You should pass in an astropy Quantity instead."

/-- astropy's message when the units do not convert. -/
def badUnitMsg (arg fn target : String) : String :=
  s!"Argument '{arg}' to function '{fn}' must be in units convertible to '{target}'."

/-- A checked argument of `quantity_input`: a plain value, or a quantity with a unit name. -/
inductive Arg where
  | plain
  | quantity (v : Float) (unit : String)

/-- `u.quantity_input(arg=target)` on one argument: `TypeError` without a unit, `UnitsError` when
the dimension differs. -/
def checkUnit (a : Arg) (arg fn : String) (dim : Dim) (target : String) : Except String Float :=
  match a with
  | .plain => throw ("TypeError:" ++ noUnitMsg arg fn)
  | .quantity v u =>
    match unitInfo u with
    | some (d, f) => if d == dim then pure (if u == "s" then v else v * f) else throw ("UnitsError:" ++ badUnitMsg arg fn target)
    | none => throw ("UnitsError:" ++ badUnitMsg arg fn target)

/-! ## Scale factor (scalar_factor.py) -/

/-- `np.e`. -/
def npE : Float := Float.ofBits 0x4005bf0a8b145769

/-- scalar_factor.py:30-31 `hubble_const.value = (Cosmo_Const / 3) ** 0.5`, a square root. -/
def hubbleConst : Float := Float.sqrt (cosmoConst / 3)

/-- scalar_factor.py:28-38. `T` in seconds, `tp` the tuning parameter, `era` a Python object
that is a string or not (`none`). -/
def scalarFactor (era : Option String) (tp T : Float) : Except String Float :=
  if era == some "md" then pure (tp * Float.pow T (2 / 3))
  else if era == some "rd" then pure (tp * Float.pow T 0.5)
  else if era == some "ded" then pure (tp * Float.pow npE (hubbleConst * T))
  else throw "ValueError:Passed era should be either 'md', 'rd' or 'ded' "

/-- scalar_factor.py:64-74. -/
def scalarFactorDerivative (era : Option String) (tp T : Float) : Except String Float :=
  if era == some "md" then pure ((2 / 3) * tp * Float.pow T (-1 / 3))
  else if era == some "rd" then pure (0.5 * tp * Float.pow T (-0.5))
  else if era == some "ded" then pure (tp * (hubbleConst * Float.pow npE (hubbleConst * T)))
  else throw "ValueError:Passed era should be either 'md', 'rd' or 'ded' "

/-! ## Bodies (bodies.py) -/

/-- A predefined body: name, mass in kg, radius in km, parent. -/
structure BodyRow where
  name : String
  mass : Float
  radius : Float
  parent : Option String

/-- bodies.py:105-131. -/
def bodies : List BodyRow :=
  [ ⟨"Sun", solarMass, rSun, none⟩,
    ⟨"Earth", 5.97219e24, 6371.0, some "Sun"⟩,
    ⟨"Moon", 7.34767309e22, 1737.5, some "Earth"⟩,
    ⟨"Mercury", 3.285e23, 2439.7, some "Sun"⟩,
    ⟨"Venus", 4.867e24, 6051.8, some "Sun"⟩,
    ⟨"Mars", 6.39e23, 3389.5, some "Sun"⟩,
    ⟨"Jupiter", 1.89813e27, 69911.0, some "Sun"⟩,
    ⟨"Saturn", 5.683e26, 58232.0, some "Sun"⟩,
    ⟨"Uranus", 8.681e25, 25362.0, some "Sun"⟩,
    ⟨"Neptune", 1.024e26, 24622.0, some "Sun"⟩,
    ⟨"Pluto", 1.309e22, 1188.3, some "Sun"⟩ ]

/-- textwrap.dedent: blank lines become empty, then the common leading whitespace goes. -/
def dedent (s : String) : String :=
  let ws (c : Char) := c == ' ' || c == '\t'
  let lines := s.splitOn "\n"
  let lines := lines.map fun l => if !l.isEmpty && l.toList.all ws then "" else l
  let indent (l : String) : Option (List Char) :=
    if l.toList.all (fun c => ws c || c == '\n') then none else some (l.toList.takeWhile ws)
  let rec common : List Char → List Char → List Char
    | a :: as, b :: bs => if a == b then a :: common as bs else []
    | _, _ => []
  let margin : Option (List Char) := lines.foldl (fun acc l =>
    match indent l with
    | none => acc
    | some i => match acc with | none => some i | some m => some (common m i)) none
  let m := (margin.getD [])
  "\n".intercalate (lines.map fun l =>
    if !m.isEmpty && l.toList.take m.length == m then String.ofList (l.toList.drop m.length) else l)

/-- bodies.py:85-96 `Body.__str__`: the f-string of the source, then `dedent`. The Quantity
texts `mass`, `q`, `R` and the coordinate text come from Python's own formatting. -/
def bodyStr (name : String) (parent : Option String) (mass q r coords : String) : String :=
  dedent s!"\n                 Body(\n                    {name},\n                    {parent.getD "None"},\n                    {mass}, {q}, {r},\n                    {coords}\n                )"

/-- bodies.py:75-82: which coordinate objects set `pos_vec` and `vel_vec`. -/
inductive CoordKind where
  | none | falsy | cartesian | spherical | boyerLindquist | other
  deriving Repr, BEq

def hasPosVec : CoordKind → Bool
  | .cartesian | .spherical | .boyerLindquist => true
  | _ => false

/-- bodies.py:69-72 `check_units(mass, q, R)`. -/
def checkBody (m q r : Arg) : Except String Unit := do
  let _ ← checkUnit m "mass" "check_units" .mass "kg"
  let _ ← checkUnit q "q" "check_units" .charge "C"
  let _ ← checkUnit r "R" "check_units" .length "km"
  pure ()

end EinsteinpyLean.Utils
