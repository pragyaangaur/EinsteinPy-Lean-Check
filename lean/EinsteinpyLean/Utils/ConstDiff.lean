import EinsteinpyLean.Utils.Codec
import EinsteinpyLean.Utils.Constants
import EinsteinpyLean.Utils.Exceptions

/-! `epdiff` handlers for constants, scalar factor, exceptions, `primitive` and bodies. -/

namespace EinsteinpyLean.Utils

/-- UTF-8 text from hex digits. -/
def unhexStr (s : String) : Option String := do
  if s.length % 2 != 0 then none
  let cs := s.toList
  let rec go : List Char → Option (List UInt8)
    | a :: b :: rest => do
      let x ← hexDigit a
      let y ← hexDigit b
      let r ← go rest
      pure ((x * 16 + y).toUInt8 :: r)
    | _ => some []
  String.fromUTF8? (ByteArray.mk (← go cs).toArray)

def hexStr (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b =>
    let d := Nat.toDigits 16 b.toNat
    String.ofList (List.replicate (2 - d.length) '0' ++ d))

def hexAnswer (s : String) : String := "H" ++ hexStr s

def parseOptStr (s : String) : Option (Option String) :=
  if s == "N" then some none
  else if s.startsWith "s" then (unhexStr (s.drop 1).toString).map some
  else none

/-- `q<hex>:<unit>` or `p`. -/
def parseArg (s : String) : Option Arg :=
  if s == "p" then some .plain
  else if s.startsWith "q" then
    match (s.drop 1).toString.splitOn ":" with
    | [v, u] => (parseFloat v).map fun v => .quantity v u
    | _ => none
  else none

def errAnswer (e : String) : String := "E:" ++ e

/-- `sf.eval <f|d> <era> <tuning> <t>`: `scalar_factor` or `scalar_factor_derivative`. -/
def hSf : Handler
  | [fd, era, tp, t] =>
    match parseOptStr era, parseScalar tp, parseArg t with
    | some era, some tp, some t =>
      let fn := if fd == "f" then "scalar_factor" else "scalar_factor_derivative"
      let r : Except String Float := do
        let T ← checkUnit t "t" fn .time "s"
        let tpf ← match tp.toFloat with | .ok x => pure x | .error _ => throw "OverflowError:"
        if fd == "f" then scalarFactor era tpf T else scalarFactorDerivative era tpf T
      match r with
      | .ok x => "F" ++ renderFloat x
      | .error e => errAnswer e
    | _, _, _ => badInput
  | _ => badInput

def parseItem (s : String) : Option PyVal :=
  if s == "N" then some .none
  else if s == "bT" then some (.bool true)
  else if s == "bF" then some (.bool false)
  else if s.startsWith "s" then (unhexStr (s.drop 1).toString).map .str
  else if s.startsWith "i" then (s.drop 1).toString.toInt?.map .int
  else none

def parseVal (s : String) : Option PyVal :=
  let body (t : String) : Option (List PyVal) :=
    if t.isEmpty then some [] else (t.splitOn "/").mapM parseItem
  if s.startsWith "L" then (body (s.drop 1).toString).map .list
  else if s.startsWith "T" then (body (s.drop 1).toString).map .tuple
  else parseItem s

/-- `exc.repr <BaseError|CoordinateError> <args>`: `repr(e)`, which is also `str(e)`. -/
def hExc : Handler
  | [cls, args] =>
    match (if args == "-" then some [] else (args.splitOn ",").mapM parseVal) with
    | some l => hexAnswer (errorRepr cls l)
    | none => badInput
  | _ => badInput

def primItem : String → Option PrimArg := fun s =>
  if s == "N" then some .none
  else if s.startsWith "i" then (s.drop 1).toString.toInt?.map .int
  else if s.startsWith "f" then (parseFloat (s.drop 1).toString).map .pyFloat
  else if s.startsWith "n" then (parseFloat (s.drop 1).toString).map .npFloat
  else if s.startsWith "s" then (unhexStr (s.drop 1).toString).map .str
  else if s.startsWith "u" then some (.unit (s.drop 1).toString)
  else if s.startsWith "q" then
    match (s.drop 1).toString.splitOn ":" with
    | [v, u] => (parseFloat v).map fun v => .quantity v u
    | _ => none
  else none

def renderPrim : PrimArg → String
  | .none => "N"
  | .int n => s!"i{n}"
  | .pyFloat x => "f" ++ renderFloat x
  | .npFloat x => "n" ++ renderFloat x
  | .str s => "s" ++ hexStr s
  | .unit u => "u" ++ u
  | .quantity x u => "q" ++ renderFloat x ++ ":" ++ u

/-- `units.prim <args>`: `primitive(*args)`. -/
def hPrim : Handler
  | [args] =>
    match (if args == "-" then some [] else (args.splitOn ",").mapM primItem) with
    | some l => "[" ++ ",".intercalate ((primitive l).map renderPrim) ++ "]"
    | none => badInput
  | _ => badInput

/-- `const.get <name>`. -/
def hConst : Handler
  | [n] => match constByName n with
    | some x => "F" ++ renderFloat x
    | none => badInput
  | _ => badInput

/-- `body.row <name>`: mass, radius, parent of a predefined body. -/
def hRow : Handler
  | [n] => match bodies.find? (·.name == n) with
    | some b => s!"F{renderFloat b.mass} F{renderFloat b.radius} {b.parent.getD "N"}"
    | none => "NONE"
  | _ => badInput

def parseKind : String → Option CoordKind
  | "none" => some .none | "falsy" => some .falsy | "cart" => some .cartesian
  | "sph" => some .spherical | "bl" => some .boyerLindquist | "other" => some .other
  | _ => none

/-- `body.new <mass> <q> <R> <coords kind>`: `Body(...)` runs `check_units`, then `__post_init__`. -/
def hNew' : Handler
  | [m, q, r, k] =>
    match parseArg m, parseArg q, parseArg r, parseKind k with
    | some m, some q, some r, some k =>
      match checkBody m q r with
      | .ok _ => if hasPosVec k then "ok:posvec" else "ok:noposvec"
      | .error e => errAnswer e
    | _, _, _, _ => badInput
  | _ => badInput

/-- `body.str <name> <parent|N> <mass> <q> <R> <coords>`, text arguments in hex. -/
def hBodyStr : Handler
  | [n, p, m, q, r, c] =>
    match unhexStr (n.drop 0).toString, parseOptStr p, unhexStr m, unhexStr q, unhexStr r, unhexStr c with
    | some n, some p, some m, some q, some r, some c => hexAnswer (bodyStr n p m q r c)
    | _, _, _, _, _, _ => badInput
  | _ => badInput

def constHandlers : List (String × Handler) :=
  [("sf.eval", hSf), ("exc.repr", hExc), ("units.prim", hPrim), ("const.get", hConst),
   ("body.row", hRow), ("body.new", hNew'), ("body.str", hBodyStr)]

end EinsteinpyLean.Utils
