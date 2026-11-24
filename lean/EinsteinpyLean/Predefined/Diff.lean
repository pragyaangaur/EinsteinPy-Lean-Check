import EinsteinpyLean.Common.Handler
import EinsteinpyLean.Predefined.Model

/-! `epdiff` handlers for the Predefined area.

Metric lines are `predef.<name> <rational> ...` and answer with the rendered 4 by 4 array or
`ERR zerodiv`. The argument order of each handler is the order of the Lean function. -/

namespace EinsteinpyLean.Predefined
open Arr

private def show' : M Arr → String
  | .ok a => a.render
  | .error e => s!"ERR {e.tag}"

/-- Parse every argument as a rational. -/
private def rats (xs : List String) : Option (List Rat) := xs.mapM parseRat

/-- Wrap a function of `n` rationals: all arguments parse as rationals and there are exactly
`n` of them. -/
private def hn (n : Nat) (f : List Rat → M Arr) : Handler := fun xs =>
  if xs.length != n then badInput else
  match rats xs with
  | some l => show' (f l)
  | none => badInput

private def h1 (f : Rat → M Arr) : Handler := hn 1 fun
  | [a] => f a
  | _ => .ok (mat4 [])
private def h3 (f : Rat → Rat → Rat → M Arr) : Handler := hn 3 fun
  | [a, b, c] => f a b c
  | _ => .ok (mat4 [])
private def h4 (f : Rat → Rat → Rat → Rat → M Arr) : Handler := hn 4 fun
  | [a, b, c, d] => f a b c d
  | _ => .ok (mat4 [])
private def h6 (f : Rat → Rat → Rat → Rat → Rat → Rat → M Arr) : Handler := hn 6 fun
  | [a, b, c, d, e, g] => f a b c d e g
  | _ => .ok (mat4 [])
private def h8 (f : Rat → Rat → Rat → Rat → Rat → Rat → Rat → Rat → M Arr) : Handler := hn 8 fun
  | [a, b, c, d, e, g, h, i] => f a b c d e g h i
  | _ => .ok (mat4 [])
private def h10 (f : Rat → Rat → Rat → Rat → Rat → Rat → Rat → Rat → Rat → Rat → M Arr) :
    Handler := hn 10 fun
  | [a, b, c, d, e, g, h, i, j, k] => f a b c d e g h i j k
  | _ => .ok (mat4 [])

def hFind : Handler
  | [s] => let r := find (parseConfig s); if r.isEmpty then "-" else ",".intercalate r
  | _ => badInput

/-- One step of the constants scenario: `new:<name>:<desc>`, `get:<key>`. A description of
`_` is `None`. Returns the new table and the printed answer. -/
private def step (t : Table) (op : String) : Table × String :=
  let showD : Option String → String | none => "None" | some d => d
  match op.splitOn ":" with
  | ["new", n, d] =>
    let d' := if d == "_" then none else some d
    let t' := construct t n d'
    (t', s!"{n}/{showD d'}")
  | ["get", k] => match getConstant t k with
    | some (n, d) => (t, s!"{n}/{showD d}")
    | none => (t, "ERR KeyError")
  | _ => (t, "BADINPUT")

/-- `predef.consts <op> <op> ...`: run the operations in order from the initial table and
print the answers joined by commas. -/
def hConsts (ops : List String) : String :=
  let (_, outs) := ops.foldl (fun (t, acc) op => let (t', o) := step t op; (t', acc ++ [o]))
    (initialTable, [])
  ",".intercalate outs

def handlers : List (String × Handler) :=
  [("predef.mink", h1 minkowskiCartesian),
   ("predef.minkp", h3 minkowskiPolar),
   ("predef.schw", h4 schwarzschild),
   ("predef.kerr", h6 kerr),
   ("predef.kn", h10 kerrNewman),
   ("predef.rn", h8 reissnerNordstrom),
   ("predef.ads", h3 fun a b c => .ok (antiDeSitter a b c)),
   ("predef.adss", h3 fun a b c => .ok (antiDeSitterStatic a b c)),
   ("predef.ds", h1 fun a => .ok (deSitter a)),
   ("predef.alc", h4 alcubierre),
   ("predef.bv", h4 barriolaVilenkin),
   ("predef.bk", h4 bertottiKasner),
   ("predef.bessel", h3 besselWave),
   ("predef.cm", h4 cMetric),
   ("predef.dav", h3 davidson),
   ("predef.ernst", h4 ernst),
   ("predef.godel", h1 fun a => .ok (godel a)),
   ("predef.flrw", h4 flrw),
   ("predef.jnw", fun
      | [c, g, gam, m, r, s] =>
        match parseRat c, parseRat g, gam.toInt?, parseRat m, parseRat r, parseRat s with
        | some c, some g, some gam, some m, some r, some s => show' (jnw c g gam m r s)
        | _, _, _, _, _, _ => badInput
      | _ => badInput),
   ("predef.knds", h6 kerrNewmanDeSitter),
   ("predef.find", hFind),
   ("predef.consts", hConsts)]

end EinsteinpyLean.Predefined
