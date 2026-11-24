import EinsteinpyLean.Common.Handler
import EinsteinpyLean.Utils.Dual

/-!
# Encoding of floats and operands for the Utils difftests

A float travels as the 16 hex digits of its IEEE bit pattern, so the comparison is exact. Every NaN
is written `nan`, because the sign and payload of a NaN differ between machines.

- Python float `f<hex>`, Python int `i<decimal>`, `numpy.float64` `n<hex>`.
- Dual number `d<hex>:<hex>`.
- Answers: dual `D<hex>:<hex>`, float `F<hex>`, boolean `B:1` or `B:0`, error `E:<tag>`.
-/

namespace EinsteinpyLean.Utils

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def parseHex (s : String) : Option Nat :=
  s.toList.foldlM (fun acc c => (hexDigit c).map (fun d => acc * 16 + d)) 0

def parseFloat (s : String) : Option Float :=
  if s == "nan" then some (0.0 / 0.0) else (parseHex s).map (fun n => Float.ofBits n.toUInt64)

def hex16 (x : Float) : String :=
  let ds := Nat.toDigits 16 x.toBits.toNat
  String.ofList (List.replicate (16 - ds.length) '0' ++ ds)

def renderFloat (x : Float) : String := if x.isNaN then "nan" else hex16 x

def renderDual (d : Dual Float) : String := s!"D{renderFloat d.val}:{renderFloat d.deriv}"

def parseDual (s : String) : Option (Dual Float) :=
  if s.startsWith "d" then
    match (s.drop 1).toString.splitOn ":" with
    | [a, b] => do pure ⟨← parseFloat a, ← parseFloat b⟩
    | _ => none
  else none

/-- A scalar operand `f<hex>`, `i<int>` or `n<hex>`. -/
def parseScalar (s : String) : Option Py.Scalar :=
  if s.startsWith "f" then (parseFloat (s.drop 1).toString).map .py
  else if s.startsWith "n" then (parseFloat (s.drop 1).toString).map .np
  else if s.startsWith "i" then (s.drop 1).toString.toInt?.map .int
  else none

def errStr (e : Exc) : String := "E:" ++ e.tag

def renderDualR : Except Exc (Dual Float) → String
  | .ok d => renderDual d
  | .error e => errStr e

def renderFloatR : Except Exc Float → String
  | .ok x => "F" ++ renderFloat x
  | .error e => errStr e

end EinsteinpyLean.Utils
