/-!
# Model of `einsteinpy.coordinates`

Mirrors `src/einsteinpy/coordinates/utils.py`, `conversion.py`, `core.py` and `differential.py` at
commit `63e1c54`. Core Lean only.

## What is exact and what is passed in

Everything is `Float`, so the model is compared with einsteinpy bit for bit. The position and
velocity formulas in `utils.py` are `@jit` functions, and numba is installed in the pinned
environment, so the model follows numba, not plain NumPy:

* numba's default error model is Python's, so every float division by zero raises
  `ZeroDivisionError` (plain NumPy would give `inf` or `nan` with a warning). `div` below is that division.
* `x ** 2` is `x * x`, and `np.sqrt` is correctly rounded like `Float.sqrt`.
* `np.hypot`, `np.arctan2`, `np.arccos`, `np.sin` and `np.cos` come from the C library. Lean's `Float`
  has no `hypot`, and the C library of the test machine need not be the one Lean links, so the model takes
  these five functions as a record `Libm`. The difftest fills `Libm` from a table that the Python side
  recorded while running the same code, keyed by the exact arguments.

The error classes are the Python ones. `UnitsError` and `TypeError` from `astropy.units.quantity_input`
are mirrored with their messages, `KeyError` with its message, `CoordinateError` with `str(e)`.
-/

namespace EinsteinpyLean.Coordinates

/-! ## Errors -/

/-- The exceptions that the coordinates code can raise. -/
inductive Err where
  /-- A float division by zero in a `@jit` function (numba's Python error model). -/
  | zeroDivision
  /-- `KeyError` with the given message (the repr of the message is its `str`). -/
  | keyError (msg : String)
  /-- conversion.py `raise KeyError("Two keyword arguments are expected ...")`. -/
  | keyErrorMA
  /-- metric/base_metric.py:258-259 `ValueError`. -/
  | spinRange
  /-- astropy `quantity_input` with an argument that has no `unit` attribute. -/
  | typeNoUnit (arg : String)
  /-- astropy `quantity_input` with a unit of the wrong dimension. -/
  | unitsError (arg unit : String)
  /-- differential.py `CoordinateError`, with the message that was built. -/
  | coordinateError (msg : String)
  deriving Repr, BEq, Inhabited

def Err.render : Err → String
  | .zeroDivision => "E:ZeroDivisionError"
  | .keyError m => s!"E:KeyError:'{m}'"
  | .keyErrorMA => "E:KeyError:\"Two keyword arguments are expected: Mass, 'M' and Spin Parameter, 'a'.\""
  | .spinRange => "E:ValueError:Spin Parameter, a, should be between 0 and 1."
  | .typeNoUnit a => s!"E:TypeError:Argument '{a}' to function '__init__' has no 'unit' attribute. You should pass in an astropy Quantity instead."
  | .unitsError a u => s!"E:UnitsError:Argument '{a}' to function '__init__' must be in units convertible to '{u}'."
  | .coordinateError m => s!"E:CoordinateError:CoordinateError : {m}"

/-- numba's float division, which raises on a zero divisor. -/
def div (a b : Float) : Except Err Float :=
  if b == 0 then .error .zeroDivision else .ok (a / b)

/-! ## The C library -/

/-- The C library functions that `utils.py` calls through NumPy. -/
structure Libm where
  hypot : Float → Float → Float
  atan2 : Float → Float → Float
  acos : Float → Float
  sin : Float → Float
  cos : Float → Float

/-! ## Position and velocity conversions (`utils.py`) -/

/-- A time, three coordinates and, if velocities are provided, their rates. -/
structure State where
  t : Float
  p1 : Float
  p2 : Float
  p3 : Float
  vel : Option (Float × Float × Float)

/-- utils.py:25-44 `cartesian_to_spherical` and `cartesian_to_spherical_novel`, chosen by the
`velocities_provided` flag of `cartesian_to_spherical_fast` (utils.py:8-13). -/
def cartesianToSpherical (L : Libm) (s : State) : Except Err State := do
  let x := s.p1
  let y := s.p2
  let z := s.p3
  let hxy := L.hypot x y
  let r := L.hypot hxy z
  let theta := L.atan2 hxy z
  let phi := L.atan2 y x
  match s.vel with
  | none => pure ⟨s.t, r, theta, phi, none⟩
  | some (vx, vy, vz) =>
    let n1 := x * x + y * y
    let n2 := n1 + z * z
    let v_r ← div (x * vx + y * vy + z * vz) (Float.sqrt n2)
    let v_th ← div (z * (x * vx + y * vy) - n1 * vz) (n2 * Float.sqrt n1)
    let v_p ← div (-1 * (vx * y - x * vy)) n1
    pure ⟨s.t, r, theta, phi, some (v_r, v_th, v_p)⟩

/-- utils.py:66-91 `cartesian_to_bl` and `cartesian_to_bl_novel`. `alpha` is the rotational length. -/
def cartesianToBL (L : Libm) (alpha : Float) (s : State) : Except Err State := do
  let x := s.p1
  let y := s.p2
  let z := s.p3
  let a2 := alpha * alpha
  let w := (x * x + y * y + z * z) - a2
  let r := Float.sqrt (0.5 * (w + Float.sqrt (w * w + 4 * a2 * (z * z))))
  let theta := L.acos (← div z r)
  let phi := L.atan2 y x
  match s.vel with
  | none => pure ⟨s.t, r, theta, phi, none⟩
  | some (vx, vy, vz) =>
    let dw := 2 * (x * vx + y * vy + z * vz)
    let k ← div 1 (2 * r)
    let q ← div (w * dw + 4 * a2 * z * vz) (2 * Float.sqrt (w * w + 4 * a2 * (z * z)))
    let v_r := k * (dw / 2 + q)
    let zr ← div z r
    let d1 ← div (-1) (Float.sqrt (1 - zr * zr))
    let d2 ← div (vz * r - v_r * z) (r * r)
    let v_th := d1 * d2
    let yx ← div y x
    let e1 ← div 1 (1 + yx * yx)
    let e2 ← div (vy * x - vx * y) (x * x)
    let v_p := e1 * e2
    pure ⟨s.t, r, theta, phi, some (v_r, v_th, v_p)⟩

/-- utils.py:117-143 `spherical_to_cartesian` and `spherical_to_cartesian_novel`. -/
def sphericalToCartesian (L : Libm) (s : State) : Except Err State := do
  let r := s.p1
  let th := s.p2
  let p := s.p3
  let x := r * L.cos p * L.sin th
  let y := r * L.sin p * L.sin th
  let z := r * L.cos th
  match s.vel with
  | none => pure ⟨s.t, x, y, z, none⟩
  | some (vr, vth, vp) =>
    let v_x := L.sin th * L.cos p * vr - r * L.sin th * L.sin p * vp + r * L.cos th * L.cos p * vth
    let v_y := L.sin th * L.sin p * vr + r * L.cos th * L.sin p * vth + r * L.sin th * L.cos p * vp
    let v_z := L.cos th * vr - r * L.sin th * vth
    pure ⟨s.t, x, y, z, some (v_x, v_y, v_z)⟩

/-- utils.py:165-199 `bl_to_cartesian` and `bl_to_cartesian_novel`. -/
def blToCartesian (L : Libm) (alpha : Float) (s : State) : Except Err State := do
  let r := s.p1
  let th := s.p2
  let p := s.p3
  let xa := Float.sqrt (r * r + alpha * alpha)
  let sinNorm := xa * L.sin th
  let x := sinNorm * L.cos p
  let y := sinNorm * L.sin p
  let z := r * L.cos th
  match s.vel with
  | none => pure ⟨s.t, x, y, z, none⟩
  | some (vr, vth, vp) =>
    let v_x := (← div (r * vr * L.sin th * L.cos p) xa) + xa * L.cos th * L.cos p * vth
      - xa * L.sin th * L.sin p * vp
    let v_y := (← div (r * vr * L.sin th * L.sin p) xa) + xa * L.cos th * L.sin p * vth
      + xa * L.sin th * L.cos p * vp
    let v_z := vr * L.cos th - r * L.sin th * vth
    pure ⟨s.t, x, y, z, some (v_x, v_y, v_z)⟩

/-! ## Constants and `BaseMetric.alpha` -/

/-- `constant.c.value`, the speed of light in m/s. -/
def cLight : Float := 299792458.0
/-- `constant.G.value`, 6.6743e-11 (the double with this bit pattern). -/
def gConst : Float := Float.ofBits 0x3dd2589effed8acc

/-- metric/base_metric.py:235-267 `BaseMetric.alpha`: `a * (G M / c²)`, after the range check on `a`. -/
def alpha (M a : Float) : Except Err Float :=
  if a < 0 || a > 1 then .error .spinRange else .ok (a * (gConst * M / (cLight * cLight)))

/-! ## `conversion.py`: the plain conversion classes -/

/-- The three coordinate systems. -/
inductive Sys where
  | cartesian | spherical | boyerLindquist
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The keyword arguments `M` and `a`, each present or absent. -/
structure Kw where
  M : Option Float
  a : Option Float

/-- conversion.py:117-124 `try: M, a = kwargs["M"], kwargs["a"] except KeyError: raise KeyError(...)`. -/
def kwMA (kw : Kw) : Except Err (Float × Float) :=
  match kw.M, kw.a with
  | some M, some a => .ok (M, a)
  | _, _ => .error .keyErrorMA

/-- core.py:`M, a = kwargs["M"], kwargs["a"]`: the bare `KeyError('M')` or `KeyError('a')`. -/
def kwMAbare (kw : Kw) : Except Err (Float × Float) :=
  match kw.M with
  | none => .error (.keyError "M")
  | some M => match kw.a with
    | none => .error (.keyError "a")
    | some a => .ok (M, a)

/-- `_velocities_provided = not ((v_x is None) or (v_y is None) or (v_z is None))` and the state that
the conversion functions get: conversion.py:35-37 and the `velocities_provided` flag. -/
def mkState (t p1 p2 p3 : Float) (v : Option Float × Option Float × Option Float) : State :=
  match v with
  | (some a, some b, some c) => ⟨t, p1, p2, p3, some (a, b, c)⟩
  | _ => ⟨t, p1, p2, p3, none⟩

/-- `values()`: the 4-tuple, or the 7-tuple when velocities are provided. -/
def State.values (s : State) : List Float :=
  match s.vel with
  | none => [s.t, s.p1, s.p2, s.p3]
  | some (a, b, c) => [s.t, s.p1, s.p2, s.p3, a, b, c]

/-- `convert_cartesian`, `convert_spherical` and `convert_bl` of the three conversion classes, from
`src` to `dst`. When `src = dst` the class has no such method, which the caller excludes. A conversion
that goes through Cartesian coordinates (`SphericalConversion.convert_bl`,
`BoyerLindquistConversion.convert_spherical`) builds a `CartesianConversion` from the 4- or 7-tuple and
converts again, and the `KeyError` check comes first (conversion.py:268-277, 440-449). -/
def convert (L : Libm) (src dst : Sys) (kw : Kw) (s : State) : Except Err State :=
  match src, dst with
  | .cartesian, .spherical => cartesianToSpherical L s
  | .cartesian, .boyerLindquist => do
    let (M, a) ← kwMA kw
    cartesianToBL L (← alpha M a) s
  | .spherical, .cartesian => sphericalToCartesian L s
  | .spherical, .boyerLindquist => do
    let (M, a) ← kwMA kw
    let c ← sphericalToCartesian L s
    let (M, a) ← kwMA ⟨some M, some a⟩
    cartesianToBL L (← alpha M a) c
  | .boyerLindquist, .cartesian => do
    let (M, a) ← kwMA kw
    blToCartesian L (← alpha M a) s
  | .boyerLindquist, .spherical => do
    let (M, a) ← kwMA kw
    let c ← blToCartesian L (← alpha M a) s
    cartesianToSpherical L c
  | _, _ => .error (.keyError "no such method")

/-! ## `core.py` and `differential.py`: the classes with units -/

/-- A unit as astropy's `decompose` gives it: the integer powers of m, kg, s and rad, a flag for any
other base unit, and the factor `unit.si.scale`. -/
structure Unit' where
  m : Int
  kg : Int
  s : Int
  rad : Int
  other : Bool
  scale : Float

/-- An argument of a class constructor: a plain number or a `Quantity` with its unit. -/
structure Quantity where
  unit : Option Unit'
  value : Float

/-- What a constructor argument must be convertible to. -/
structure Need where
  name : String
  m : Int
  kg : Int
  s : Int
  rad : Int
  text : String

def needT : Need := ⟨"t", 0, 0, 1, 0, "s"⟩
def needLen (n : String) : Need := ⟨n, 1, 0, 0, 0, "m"⟩
def needAng (n : String) : Need := ⟨n, 0, 0, 0, 1, "rad"⟩
def needSpeed (n : String) : Need := ⟨n, 1, 0, -1, 0, "m / s"⟩
def needAngSpeed (n : String) : Need := ⟨n, 0, 0, -1, 1, "rad / s"⟩

/-- astropy `quantity_input`: the arguments are checked in the order of the signature, and the first
failure is raised. A passing argument is turned into `.si.value`, which is `value * scale`. -/
def checkArgs : List Need → List Quantity → Except Err (List Float)
  | n :: ns, q :: qs =>
    match q.unit with
    | none => .error (.typeNoUnit n.name)
    | some u =>
      if u.m == n.m && u.kg == n.kg && u.s == n.s && u.rad == n.rad && !u.other then do
        let rest ← checkArgs ns qs
        pure (q.value * u.scale :: rest)
      else .error (.unitsError n.name n.text)
  | _, _ => .ok []

/-- The constructor signature of a class: positions only (`Cartesian`, `Spherical`,
`BoyerLindquist`) or with velocities (the `*Differential` classes). -/
def needs (sys : Sys) (diff : Bool) : List Need :=
  let pos := match sys with
    | .cartesian => [needT, needLen "x", needLen "y", needLen "z"]
    | .spherical => [needT, needLen "r", needAng "theta", needAng "phi"]
    | .boyerLindquist => [needT, needLen "r", needAng "theta", needAng "phi"]
  if diff then
    pos ++ (match sys with
      | .cartesian => [needSpeed "v_x", needSpeed "v_y", needSpeed "v_z"]
      | .spherical => [needSpeed "v_r", needAngSpeed "v_th", needAngSpeed "v_p"]
      | .boyerLindquist => [needSpeed "v_r", needAngSpeed "v_th", needAngSpeed "v_p"])
  else pos

/-- The state of an object built by a `Cartesian`, `Spherical`, ... constructor. -/
def stateOfSI : List Float → Option State
  | [t, a, b, c] => some ⟨t, a, b, c, none⟩
  | [t, a, b, c, d, e, f] => some ⟨t, a, b, c, some (d, e, f)⟩
  | _ => none

/-- The tuple `position()`: `c * t`, then the three coordinates. -/
def State.position (s : State) : List Float := [cLight * s.t, s.p1, s.p2, s.p3]

/-- The name of the method of `core.py` or `differential.py` that converts to `dst`:
`to_<dst>` or `<dst>_differential`. -/
inductive Method where
  | values | position | convert (dst : Sys) | to (dst : Sys)
  deriving Repr, BEq

/-- `Cartesian.to_bl(**kwargs)` and its siblings: the bare `KeyError` first, then the conversion
(core.py:116-140, differential.py `bl_differential`). The methods that need no keyword arguments
(`to_spherical` of `Cartesian`, `to_cartesian` of `Spherical`) never look at `kwargs`. -/
def callMethod (L : Libm) (src : Sys) (kw : Kw) (s : State) : Method → Except Err (List Float)
  | .values => .ok s.values
  | .position => .ok s.position
  | .convert dst => (convert L src dst kw s).map State.values
  | .to dst => do
    let kw' ← match src, dst with
      | .cartesian, .spherical => pure kw
      | .spherical, .cartesian => pure kw
      | _, _ => do
        let (M, a) ← kwMAbare kw
        pure ⟨some M, some a⟩
    (convert L src dst kw' s).map State.values

/-- A class with units: validate the constructor arguments, then call the method. -/
def classCall (L : Libm) (src : Sys) (diff : Bool) (args : List Quantity) (kw : Kw) (m : Method) :
    Except Err (List Float) := do
  let vals ← checkArgs (needs src diff) args
  match stateOfSI vals with
  | some s => callMethod L src kw s m
  | none => .error (.keyError "bad arity")

/-! ## `utils.py`: `lorentz_factor` and `v0` -/

/-- utils.py:225-229 `lorentz_factor`, not jitted: plain NumPy, so a zero divisor gives `inf` and a
negative square root `nan` without an exception. `v_vec.dot(v_vec)` of three floats. -/
def lorentzFactor (v1 v2 v3 : Float) : Float :=
  let n2 := v1 * v1 + v2 * v2 + v3 * v3
  1 / Float.sqrt (1 - n2 / (cLight * cLight))

/-- utils.py:253-264 `v0`, jitted, for the timelike component of a 4-velocity. `g` is the 4x4
covariant metric, row by row. The positive root of `g00 v0^2 + 2 g0i vi v0 + gij vi vj = c^2`
(the constant `-c^2` is added to `C`). -/
def v0 (g : Array Float) (v1 v2 v3 : Float) : Except Err Float :=
  let G := fun i j => g[i * 4 + j]!
  let fac := -1 * (cLight * cLight)
  let A := G 0 0
  let B := 2 * (G 0 1 * v1 + G 0 2 * v2 + G 0 3 * v3)
  let C := (G 1 1 * (v1 * v1) + G 2 2 * (v2 * v2) + G 3 3 * (v3 * v3))
    + 2 * v1 * (G 1 2 * v2 + G 1 3 * v3) + 2 * v2 * G 2 3 * v3 + fac
  let D := B * B - 4 * A * C
  match div (-B + Float.sqrt D) (2 * A) with
  | .ok v => .ok v
  | .error e => .error e

/-- differential.py `v_t` setter and `velocity(metric)`: the coordinate system of the metric must be
that of the class, otherwise `CoordinateError`. `sysName` is the system of the metric (`g.coords.system`),
`own` the system of the class. The message of the Boyer-Lindquist class is a plain string without the
`f` prefix (differential.py:525-527), so it keeps the text `{g.coords.system}`. Returns `v_t` and the
three velocity components in SI. -/
def velocity (src : Sys) (sysName : String) (g : Array Float) (args : List Quantity) :
    Except Err (List Float) := do
  let vals ← checkArgs (needs src true) args
  match vals with
  | [_, _, _, _, a, b, c] =>
    let ownName := match src with
      | .cartesian => "Cartesian" | .spherical => "Spherical" | .boyerLindquist => "BoyerLindquist"
    if ownName != sysName then
      let msg := match src with
        | .cartesian => s!"Metric object has been instantiated with a coordinate system, ( {sysName} ) other than Cartesian Coordinates."
        | .spherical => s!"Metric object has been instantiated with a coordinate system, ( {sysName} ) other than Spherical Polar Coordinates."
        | .boyerLindquist => "Metric object has been instantiated with a coordinate system, ( {g.coords.system} ) other than Boyer-Lindquist Coordinates."
      .error (.coordinateError msg)
    else
      let vt ← v0 g a b c
      pure [vt, a, b, c]
  | _ => .error (.keyError "bad arity")

end EinsteinpyLean.Coordinates
