import EinsteinpyLean.Common.Handler
import EinsteinpyLean.Coordinates.Model

/-!
# `epdiff_coordinates` handlers

A float travels as the 16 hex digits of its IEEE bit pattern, every NaN as `nan`. Answers are the
hex floats joined by commas, or an error `E:<class>[:<message>]`.

The C library table `<libm>` is `-` or a comma list of entries `H:a:b:r` (hypot), `T:a:b:r` (atan2),
`O:a:r` (acos), `S:a:r` (sin), `C:a:r` (cos), recorded by the Python side while it ran the same code.
A call that is not in the table gives `nan`, so a missing entry shows up as a mismatch.
-/

namespace EinsteinpyLean.Coordinates

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def parseHex (s : String) : Option Nat :=
  s.toList.foldlM (fun acc c => (hexDigit c).map (fun d => acc * 16 + d)) 0

def parseF (s : String) : Option Float :=
  if s == "nan" then some (0.0 / 0.0) else (parseHex s).map (fun n => Float.ofBits n.toUInt64)

def hex16 (x : Float) : String :=
  let ds := Nat.toDigits 16 x.toBits.toNat
  String.ofList (List.replicate (16 - ds.length) '0' ++ ds)

def renderF (x : Float) : String := if x.isNaN then "nan" else hex16 x

def renderList (l : List Float) : String := ",".intercalate (l.map renderF)

def renderR : Except Err (List Float) → String
  | .ok l => renderList l
  | .error e => e.render

/-- Two floats are the same table key: equal bit patterns, or both `nan`. -/
def sameF (a b : Float) : Bool := (a.isNaN && b.isNaN) || a.toBits == b.toBits

structure Entry where
  kind : Char
  a : Float
  b : Float
  r : Float

def parseEntry (s : String) : Option Entry :=
  match s.splitOn ":" with
  | [k, a, r] => do
    let c ← k.toList.head?
    pure ⟨c, ← parseF a, 0, ← parseF r⟩
  | [k, a, b, r] => do
    let c ← k.toList.head?
    pure ⟨c, ← parseF a, ← parseF b, ← parseF r⟩
  | _ => none

def parseLibm (s : String) : Option Libm :=
  if s == "-" then some ⟨fun _ _ => 0.0 / 0.0, fun _ _ => 0.0 / 0.0, fun _ => 0.0 / 0.0, fun _ => 0.0 / 0.0, fun _ => 0.0 / 0.0⟩
  else do
    let es ← (s.splitOn ",").mapM parseEntry
    let nan := 0.0 / 0.0
    let find1 (k : Char) (a : Float) : Float :=
      match es.find? (fun e => e.kind == k && sameF e.a a) with | some e => e.r | none => nan
    let find2 (k : Char) (a b : Float) : Float :=
      match es.find? (fun e => e.kind == k && sameF e.a a && sameF e.b b) with | some e => e.r | none => nan
    pure ⟨find2 'H', find2 'T', find1 'O', find1 'S', find1 'C'⟩

def parseSys : String → Option Sys
  | "cart" => some .cartesian
  | "sph" => some .spherical
  | "bl" => some .boyerLindquist
  | _ => none

def parseOptF (s : String) : Option (Option Float) :=
  if s == "-" then some none else (parseF s).map some

/-- A quantity `<m>_<kg>_<s>_<rad>_<other>_<scale>:<value>`, or `none:<value>` for a plain number. -/
def parseQuantity (s : String) : Option Quantity :=
  match s.splitOn ":" with
  | ["none", v] => (parseF v).map fun v => ⟨none, v⟩
  | [u, sc, v] =>
    match u.splitOn "_" with
    | [m, kg, t, r, o] => do
      pure ⟨some ⟨← m.toInt?, ← kg.toInt?, ← t.toInt?, ← r.toInt?, o == "1", ← parseF sc⟩, ← parseF v⟩
    | _ => none
  | _ => none

def parseMethod (s : String) : Option Method :=
  match s.splitOn ":" with
  | ["values"] => some .values
  | ["position"] => some .position
  | ["convert", d] => (parseSys d).map .convert
  | ["to", d] => (parseSys d).map .to
  | _ => none

def bad : String := "BADINPUT"

/-- `coord.fast <src> <dst> <libm> <alpha|-> <t> <p1> <p2> <p3> <vel>` with `vel` = `-` or `a,b,c`:
the four `*_fast` functions of utils.py. -/
def hFast : List String → String
  | [src, dst, lm, al, t, p1, p2, p3, vel] =>
    match parseSys src, parseSys dst, parseLibm lm, parseOptF al, parseF t, parseF p1, parseF p2, parseF p3 with
    | some src, some dst, some L, some al, some t, some p1, some p2, some p3 =>
      let v := if vel == "-" then some none else
        match (vel.splitOn ",").mapM parseF with
        | some [a, b, c] => some (some (a, b, c))
        | _ => none
      match v with
      | none => bad
      | some vv =>
        let s : State := ⟨t, p1, p2, p3, vv⟩
        let r : Except Err State := match src, dst, al with
          | .cartesian, .spherical, _ => cartesianToSpherical L s
          | .cartesian, .boyerLindquist, some a => cartesianToBL L a s
          | .spherical, .cartesian, _ => sphericalToCartesian L s
          | .boyerLindquist, .cartesian, some a => blToCartesian L a s
          | _, _, _ => .error (.keyError "bad")
        renderR (r.map State.values)
    | _, _, _, _, _, _, _, _ => bad
  | _ => bad

/-- `coord.conv <src> <dst> <libm> <M|-> <a|-> <t> <p1> <p2> <p3> <v1|-> <v2|-> <v3|->`: the
`convert_*` methods of the conversion classes, `values` when `dst` equals `src`. -/
def hConv : List String → String
  | [src, dst, lm, M, a, t, p1, p2, p3, v1, v2, v3] =>
    match parseSys src, parseSys dst, parseLibm lm, parseOptF M, parseOptF a, parseF t, parseF p1,
      parseF p2, parseF p3, parseOptF v1, parseOptF v2, parseOptF v3 with
    | some src, some dst, some L, some M, some a, some t, some p1, some p2, some p3, some v1, some v2, some v3 =>
      let s := mkState t p1 p2 p3 (v1, v2, v3)
      if src == dst then renderList s.values
      else renderR ((convert L src dst ⟨M, a⟩ s).map State.values)
    | _, _, _, _, _, _, _, _, _, _, _, _ => bad
  | _ => bad

/-- `coord.cls <sys> <diff 0|1> <method> <libm> <M|-> <a|-> <arg>...`: a core.py or differential.py
class with units, and one of its methods. -/
def hCls : List String → String
  | sys :: diff :: m :: lm :: M :: a :: args =>
    match parseSys sys, parseMethod m, parseLibm lm, parseOptF M, parseOptF a, args.mapM parseQuantity with
    | some sys, some m, some L, some M, some a, some qs =>
      renderR (classCall L sys (diff == "1") qs ⟨M, a⟩ m)
    | _, _, _, _, _, _ => bad
  | _ => bad

/-- `coord.alpha <M> <a>`: `BaseMetric.alpha`. -/
def hAlpha : List String → String
  | [M, a] => match parseF M, parseF a with
    | some M, some a => renderR ((alpha M a).map fun x => [x])
    | _, _ => bad
  | _ => bad

/-- `coord.lorentz <v1> <v2> <v3>`. -/
def hLorentz : List String → String
  | [a, b, c] => match parseF a, parseF b, parseF c with
    | some a, some b, some c => renderList [lorentzFactor a b c]
    | _, _, _ => bad
  | _ => bad

/-- `coord.v0 <g, 16 floats comma separated> <v1> <v2> <v3>`. -/
def hV0 : List String → String
  | [g, a, b, c] => match (g.splitOn ",").mapM parseF, parseF a, parseF b, parseF c with
    | some g, some a, some b, some c =>
      if g.length != 16 then bad else renderR ((v0 g.toArray a b c).map fun x => [x])
    | _, _, _, _ => bad
  | _ => bad

/-- `coord.vel <sys> <metric system name> <g> <arg>x7`: `velocity(metric)` of a `*Differential` class. -/
def hVel : List String → String
  | sys :: name :: g :: args =>
    match parseSys sys, (g.splitOn ",").mapM parseF, args.mapM parseQuantity with
    | some sys, some g, some qs =>
      if g.length != 16 then bad else renderR (velocity sys name g.toArray qs)
    | _, _, _ => bad
  | _ => bad

def handlers : List (String × (List String → String)) :=
  [("coord.fast", hFast), ("coord.conv", hConv), ("coord.cls", hCls), ("coord.alpha", hAlpha),
   ("coord.lorentz", hLorentz), ("coord.v0", hV0), ("coord.vel", hVel)]

end EinsteinpyLean.Coordinates
