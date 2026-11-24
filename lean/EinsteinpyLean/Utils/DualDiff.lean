import EinsteinpyLean.Utils.Codec
import EinsteinpyLean.Utils.DualMetrics

/-! `epdiff` handlers for `utils/dual.py`. -/

namespace EinsteinpyLean.Utils

open Py

/-- `dual.new <scalar|dual> <scalar|dual>`: `DualNumber(a, b)`. A dual argument is a `TypeError`. -/
def hNew : Handler
  | [a, b] =>
    let conv (t : String) : Option (Except Exc Scalar) :=
      match parseScalar t with
      | some s => some (pure s)
      | none => (parseDual t).map fun _ => throw .typeError
    match conv a, conv b with
    | some a, some b => renderDualR (do mk (← a) (← b))
    | _, _ => badInput
  | _ => badInput

/-- `dual.bin <op> <dual> <operand>`: the operators and the reflected operators. -/
def hBin : Handler
  | [op, a, b] =>
    match parseDual a with
    | none => badInput
    | some a =>
      let bd := parseDual b
      let bs := parseScalar b
      if bd.isNone && bs.isNone then badInput else
      match op with
      | "add" => match bd, bs with
        | some b, _ => renderDualR (pure (addD a b))
        | _, some c => renderDualR (addS a c)
        | _, _ => badInput
      | "radd" => match bd, bs with
        | some b, _ => renderDualR (pure (addD b a))
        | _, some c => renderDualR (addS a c)
        | _, _ => badInput
      | "sub" => match bd, bs with
        | some b, _ => renderDualR (pure (subD a b))
        | _, some c => renderDualR (subS a c)
        | _, _ => badInput
      | "rsub" => match bd, bs with
        | some b, _ => renderDualR (pure (subD b a))
        | _, some c => renderDualR (rsubS a c)
        | _, _ => badInput
      | "drsub" => match bd, bs with
        | some b, _ => renderDualR (pure (rsubD a b))
        | _, some c => renderDualR (rsubS a c)
        | _, _ => badInput
      | "mul" => match bd, bs with
        | some b, _ => renderDualR (pure (mulD a b))
        | _, some c => renderDualR (mulS a c)
        | _, _ => badInput
      | "rmul" => match bd, bs with
        | some b, _ => renderDualR (pure (mulD b a))
        | _, some c => renderDualR (mulS a c)
        | _, _ => badInput
      | "div" => match bd, bs with
        | some b, _ => renderDualR (divD a b)
        | _, some c => renderDualR (divS a c)
        | _, _ => badInput
      | "rdiv" => match bd, bs with
        | some b, _ => renderDualR (divD b a)
        | _, some c => renderDualR (rdivS a c)
        | _, _ => badInput
      | "drdiv" => match bd, bs with
        | some b, _ => renderDualR (rdivD a b)
        | _, some c => renderDualR (rdivS a c)
        | _, _ => badInput
      | "pow" => match bd, bs with
        | some _, _ => errStr .typeError
        | _, some c => renderDualR (powS a c)
        | _, _ => badInput
      | "eq" | "ne" =>
        let r : Except Exc Bool := match bd, bs with
          | some b, _ => pure (eqD a b)
          | _, _ => eqS
        match r with
        | .ok v => s!"B:{if (if op == "eq" then v else !v) then 1 else 0}"
        | .error e => errStr e
      | _ => badInput
  | _ => badInput

/-- `dual.un <op> <dual>`: `neg`, `sin`, `cos`, `tan`, `log`, `exp`. -/
def hUn : Handler
  | [op, a] =>
    match parseDual a with
    | none => badInput
    | some a =>
      match op with
      | "neg" => renderDualR (pure (negD a))
      | "sin" => renderDualR (pure (sinD a))
      | "cos" => renderDualR (pure (cosD a))
      | "tan" => renderDualR (tanD a)
      | "log" => renderDualR (logD a)
      | "exp" => renderDualR (pure (expD a))
      | _ => badInput
  | _ => badInput

def parseInstr (s : String) : Option Instr :=
  match s.splitOn "=" with
  | [n] => match n with
    | "dup" => some .dup | "add" => some .add | "sub" => some .sub | "mul" => some .mul
    | "div" => some .div | "neg" => some .neg | "sin" => some .sin | "cos" => some .cos
    | "tan" => some .tan | "log" => some .log | "exp" => some .exp
    | _ => none
  | [n, c] => do
    let c ← parseScalar c
    match n with
    | "pow" => some (.pow c) | "addc" => some (.addc c) | "raddc" => some (.raddc c)
    | "subc" => some (.subc c) | "rsubc" => some (.rsubc c) | "mulc" => some (.mulc c)
    | "rmulc" => some (.rmulc c) | "divc" => some (.divc c) | "rdivc" => some (.rdivc c)
    | "retc" => some (.retc c)
    | _ => none
  | _ => none

/-- `dual.prog <d|v> <x> <instr,instr,...>`: `_deriv(func, x)` (`d`) or `func(DualNumber(x, 1.0))` (`v`). -/
def hProg : Handler
  | [mode, x, prog] =>
    match parseFloat x, (prog.splitOn ",").mapM parseInstr with
    | some x, some prog =>
      if mode == "d" then renderFloatR (derivOf prog x)
      else match run prog ⟨x, 1⟩ with
        | .ok (.dual d) => renderDual d
        | .ok (.num v) => "F" ++ renderFloat v
        | .error e => errStr e
    | _, _ => badInput
  | _ => badInput

def parseFloats (s : String) : Option (List Float) :=
  if s == "-" then some [] else (s.splitOn ",").mapM parseFloat

def parseIdx (s : String) : Option Idx :=
  let body (t : String) : Option (List Int) :=
    if t.isEmpty then some [] else (t.splitOn "/").mapM String.toInt?
  if s.startsWith "t" then (body (s.drop 1).toString).map .tuple
  else if s.startsWith "l" then (body (s.drop 1).toString).map .list
  else none

def parseWrt (s : String) : Option Wrt :=
  if s.startsWith "i" then (s.drop 1).toString.toInt?.map .int
  else if s.startsWith "f" then (parseFloat (s.drop 1).toString).map .flt
  else none

/-- `dual.diffg <metric> <params> <coords> <indices> <wrt>`. -/
def hDiffG : Handler
  | [m, prm, coords, idx, wrt] =>
    match metricByName m, parseFloats prm, parseFloats coords, parseIdx idx, parseWrt wrt with
    | some g, some prm, some coords, some idx, some wrt => renderFloatR (diffG g prm coords idx wrt)
    | _, _, _, _, _ => badInput
  | _ => badInput

/-- `dual.jacg <metric> <params> <coords> <wrt>`: the 16 entries of the Jacobian. -/
def hJacG : Handler
  | [m, prm, coords, wrt] =>
    match metricByName m, parseFloats prm, parseFloats coords, parseWrt wrt with
    | some g, some prm, some coords, some wrt =>
      match jacobianG g prm coords wrt with
      | .ok j => "J" ++ " ".intercalate (j.toList.map renderFloat)
      | .error e => errStr e
    | _, _, _, _ => badInput
  | _ => badInput

/-- A dual with rational parts, `p/q:p/q`. -/
def parseRatDual (s : String) : Option (Dual Rat) :=
  match s.splitOn ":" with
  | [a, b] => do pure ⟨← Arr.parseRat a, ← Arr.parseRat b⟩
  | _ => none

def renderRatDual (d : Dual Rat) : String := s!"{Arr.ratStr d.val}:{Arr.ratStr d.deriv}"

/-- `dual.rat <op1> <op2> <a> <b> <c>`: `(a op1 b) op2 c` on exact rationals with the generic layer. -/
def hRat : Handler
  | [o1, o2, a, b, c] =>
    let ap (o : String) (x y : Dual Rat) : Option (Dual Rat) :=
      match o with
      | "add" => some (Dual.add x y) | "sub" => some (Dual.sub x y) | "mul" => some (Dual.mul x y)
      | _ => none
    match parseRatDual a, parseRatDual b, parseRatDual c with
    | some a, some b, some c =>
      match ap o1 a b with
      | some ab => match ap o2 ab c with
        | some r => renderRatDual r
        | none => badInput
      | none => badInput
    | _, _, _ => badInput
  | _ => badInput

def dualHandlers : List (String × Handler) :=
  [("dual.new", hNew), ("dual.bin", hBin), ("dual.un", hUn), ("dual.prog", hProg),
   ("dual.diffg", hDiffG), ("dual.jacg", hJacG), ("dual.rat", hRat)]

end EinsteinpyLean.Utils
