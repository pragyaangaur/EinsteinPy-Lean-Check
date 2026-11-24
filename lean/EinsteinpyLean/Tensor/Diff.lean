import EinsteinpyLean.Common.Handler
import EinsteinpyLean.Tensor.Model

/-! `epdiff` handlers for the Tensor area. -/

namespace EinsteinpyLean.Tensor
open Arr

private def showResult : Except Err Arr → String
  | .ok a => a.render
  | .error e => s!"ERR {e.tag}"

/-- `tensor.chk <config>` → `True` or `False`. -/
def hChk : Handler
  | [c] => if configChecker (parseConfig c) then "True" else "False"
  | _ => badInput

/-- `tensor.cc <arr> <config> <newconfig> <gLower>`: `_change_config`. -/
def hChangeConfig : Handler
  | [a, c, nc, g] => match parseArr a, parseArr g with
    | some a, some g => match matInv g with
      | some gi => showResult (changeConfig a (parseConfig c) (parseConfig nc) g gi)
      | none => badInput
    | _, _ => badInput
  | _ => badInput

/-- `tensor.tp <a1> <c1> <a2> <c2> <i> <j>`: `tensor_product`. -/
def hTensorProduct : Handler
  | [a1, c1, a2, c2, i, j] =>
    match parseArr a1, parseArr a2, parseOptInt i, parseOptInt j with
    | some a1, some a2, some i, some j =>
      match tensorProduct a1 (parseConfig c1) a2 (parseConfig c2) i j with
      | .ok (c, r) => s!"{if c.isEmpty then "-" else c} {r.render}"
      | .error e => s!"ERR {e.tag}"
    | _, _, _, _ => badInput
  | _ => badInput

/-- `tensor.lt <arr> <config> <matrix>`: `lorentz_transform`. -/
def hLorentz : Handler
  | [a, c, m] => match parseArr a, parseArr m with
    | some a, some m => showResult (lorentzTransform a (parseConfig c) m)
    | _, _ => badInput
  | _ => badInput

def handlers : List (String × Handler) :=
  [("tensor.chk", hChk), ("tensor.cc", hChangeConfig),
   ("tensor.tp", hTensorProduct), ("tensor.lt", hLorentz)]

end EinsteinpyLean.Tensor
