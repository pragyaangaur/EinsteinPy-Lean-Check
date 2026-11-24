import EinsteinpyLean.Common.Handler
import EinsteinpyLean.Helpers.Model

/-! `epdiff` handlers for the Helpers area. -/

namespace EinsteinpyLean.Helpers

/-- Coefficients `n:c00,c01,...` (row-major, `n × n`). -/
def parseCoeffs (s : String) : Option (List (List Rat)) := do
  let a ← parseArr s
  let [n, m] := a.shape | none
  if n != m then none
  some <| (List.range n).map fun i => (List.range n).map fun j => a.get [i, j]

/-- `helpers.tm <coeffs>` → `from_new2old` entries, then `|`, then `inv()` entries. -/
def hTM : Handler
  | [c] => match parseCoeffs c with
    | some c => let t := fromNew2old c; s!"{renderMat t} | {renderMat (inv t)}"
    | none => badInput
  | _ => badInput

def handlers : List (String × Handler) := [("helpers.tm", hTM)]

end EinsteinpyLean.Helpers
