import EinsteinpyLean.Common.Handler
import EinsteinpyLean.Curvature.Model

/-!
`epdiff` handlers for the Curvature area.

Argument encodings, on top of those in `Common/Handler.lean`:

- metric object: `<arr>@<config>`, or `-` for `None`.
- jet: three arrays `g`, `dg` (`[k,i,j]`) and `ddg` (`[k,l,i,j]`).
-/

namespace EinsteinpyLean.Curvature
open Arr

private def showErr (e : Err) : String := s!"ERR {e.tag}"

private def showArr : Except Err Arr → String
  | .ok a => a.render
  | .error e => showErr e

private def showClassArr : Except Err (String × Arr) → String
  | .ok (c, a) => s!"{c} {a.render}"
  | .error e => showErr e

/-- `<arr>@<config>` → a metric description (not yet constructed). -/
private def parseMetTok (s : String) : Option (Arr × String) :=
  match s.splitOn "@" with
  | [a, c] => do
    let arr ← parseArr a
    some (arr, parseConfig c)
  | _ => none

/-- `-` is `None`; otherwise a parsed metric description. -/
private def parseOptMet (s : String) : Option (Option (Arr × String)) :=
  if s == "-" then some none else (parseMetTok s).map some

/-- Construct the optional metric objects in Python's order (`pm`, then `am`). -/
private def mkOptMet (nsyms : Nat) : Option (Arr × String) → Except Err (Option Met)
  | none => pure none
  | some (a, c) => (some ·) <$> mkMet a c nsyms

private def jetOf (d : Nat) (g dg ddg : Arr) : Option Jet :=
  if g.shape == [d, d] && dg.shape == [d, d, d] && ddg.shape == [d, d, d, d] then
    some ⟨d, g, dg, ddg⟩
  else none

/-- `curv.ctor <kind> <arr> <config> <nsyms>`: the constructor checks. -/
def hCtor : Handler
  | [k, a, c, n] =>
    match Kind.ofString? k, parseArr a, n.toNat? with
    | some k, some a, some n =>
      match construct k a.shape (parseConfig c) n with
      | .ok () => "OK"
      | .error e => showErr e
    | _, _, _ => badInput
  | _ => badInput

/-- `curv.mcc <arr> <config> <newconfig> <nsyms>`, `curv.minv` and `curv.mlow`
(`<arr> <config> <nsyms>`): the metric's own methods. -/
private def metOp (f : Met → Nat → Except Err Met) (a c : String) (n : Nat) : String :=
  match parseArr a with
  | none => badInput
  | some a =>
    match mkMet a (parseConfig c) n >>= fun m => f m n with
    | .ok m => s!"{if m.config.isEmpty then "-" else m.config} {m.arr.render}"
    | .error e => showErr e

def hMcc : Handler
  | [a, c, nc, n] => match n.toNat? with
    | some n => metOp (fun m n => m.changeConfig (parseConfig nc) n) a c n
    | none => badInput
  | _ => badInput

def hMinv : Handler
  | [a, c, n] => match n.toNat? with
    | some n => metOp (fun m n => m.inv n) a c n
    | none => badInput
  | _ => badInput

def hMlow : Handler
  | [a, c, n] => match n.toNat? with
    | some n => metOp (fun m n => m.lower n) a c n
    | none => badInput
  | _ => badInput

/-- `curv.cc <kind> <arr> <config> <newconfig> <nsyms> <pm> <am>`: `change_config` of a
class (not the metric). The metric objects are built first, then the tensor. -/
def hCc : Handler
  | [k, a, c, nc, n, pm, am] =>
    match Kind.ofString? k, parseArr a, n.toNat?, parseOptMet pm, parseOptMet am with
    | some k, some a, some n, some pm, some am =>
      showClassArr (do
        let pm ← mkOptMet n pm
        let am ← mkOptMet n am
        construct k a.shape (parseConfig c) n
        changeConfig k a (parseConfig c) (parseConfig nc) n pm am)
    | _, _, _, _, _ => badInput
  | _ => badInput

/-- `curv.lt <kind> <arr> <config> <tm> <nsyms>`: `lorentz_transform` of a class. -/
def hLt : Handler
  | [k, a, c, tm, n] =>
    match Kind.ofString? k, parseArr a, parseArr tm, n.toNat? with
    | some k, some a, some tm, some n =>
      showClassArr (do
        construct k a.shape (parseConfig c) n
        lorentz k a (parseConfig c) tm n)
    | _, _, _, _ => badInput
  | _ => badInput

/-- `curv.fm <op> <config> <d> <g> <dg> <ddg>`: `X.from_metric` for `op` one of `chr`,
`riem`, `ric`, `sca`, `ein`, `sch`, `weyl`. -/
def hFromMetric : Handler
  | [op, c, d, g, dg, ddg] =>
    match d.toNat?, parseArr g, parseArr dg, parseArr ddg with
    | some d, some g, some dg, some ddg =>
      match jetOf d g dg ddg with
      | none => badInput
      | some j => showArr (do
          let cfg := parseConfig c
          -- the chain for `chr` stops at the Christoffel symbols
          -- schouten.py:65 and weyl.py:65-101 look at the dimension before anything else
          if op == "sch" && d < 3 then throw .dimTooSmall
          if op == "weyl" && d < 3 then throw .dimTooSmall
          if op == "weyl" && d == 3 then return ofFn [3, 3, 3, 3] fun _ => 0
          let lj ← lowerJet cfg j
          if op == "chr" then return (← christoffelOf lj)
          let (p, m) ← fromMetric cfg j
          match op with
          | "riem" => return p.riemann
          | "ric" => return p.ricci
          | "sca" => return p.scalar
          | "ein" => return einsteinOf p
          | "sch" => schoutenOf p
          | "weyl" => weylOf p m
          | _ => throw .noAttr)
    | _, _, _, _ => badInput
  | _ => badInput

/-- `curv.stress <config> <d> <g> <dg> <ddg> <lambda>`: `G_ij - Λ g_ij`. -/
def hStress : Handler
  | [c, d, g, dg, ddg, lam] =>
    match d.toNat?, parseArr g, parseArr dg, parseArr ddg, parseRat lam with
    | some d, some g, some dg, some ddg, some lam =>
      match jetOf d g dg ddg with
      | none => badInput
      | some j => showArr (do
          let (p, _) ← fromMetric (parseConfig c) j
          return stressCore p lam)
    | _, _, _, _, _ => badInput
  | _ => badInput
where parseRat (s : String) : Option Rat := Arr.parseRat s

/-- `curv.fch <target> <config> <gam> <dgam> <nsyms> <pm> <am>`: `from_christoffels`
for `riem`, `ric` or `sca`, on `Γ` and `∂Γ` (`[r,t,s,n]`) at a point. -/
def hFromChristoffels : Handler
  | [op, c, gam, dgam, n, pm, am] =>
    match parseArr gam, parseArr dgam, n.toNat?, parseOptMet pm, parseOptMet am with
    | some gam, some dgam, some n, some pm, some am =>
      showArr (do
        let pm ← mkOptMet n pm
        let am ← mkOptMet n am
        let cfg := parseConfig c
        construct .chris gam.shape cfg n
        let (rm, eff) ← riemannFromChristoffels gam dgam cfg n pm am
        match op with
        | "riem" => return rm
        | "ric" =>
          let (ric, _) ← ricciFromRiemann rm "ulll" n eff none
          return ric
        | "sca" =>
          let (ric, eff') ← ricciFromRiemann rm "ulll" n eff none
          scalarFromRicciTensor ric "ll" n eff' none
        | _ => throw .noAttr)
    | _, _, _, _, _ => badInput
  | _ => badInput

/-- `curv.fri <target> <riemann> <config> <nsyms> <pm> <am>`: `from_riemann` for `ric`
or `sca`. -/
def hFromRiemann : Handler
  | [op, r, c, n, pm, am] =>
    match parseArr r, n.toNat?, parseOptMet pm, parseOptMet am with
    | some r, some n, some pm, some am =>
      showArr (do
        let pm ← mkOptMet n pm
        let am ← mkOptMet n am
        let cfg := parseConfig c
        construct .riemann r.shape cfg n
        let (ric, eff) ← ricciFromRiemann r cfg n pm am
        match op with
        | "ric" => return ric
        | "sca" => scalarFromRicciTensor ric "ll" n eff none
        | _ => throw .noAttr)
    | _, _, _, _ => badInput
  | _ => badInput

/-- `curv.frt <ricci> <config> <nsyms> <pm> <am>`: `RicciScalar.from_riccitensor`. -/
def hFromRicci : Handler
  | [r, c, n, pm, am] =>
    match parseArr r, n.toNat?, parseOptMet pm, parseOptMet am with
    | some r, some n, some pm, some am =>
      showArr (do
        let pm ← mkOptMet n pm
        let am ← mkOptMet n am
        let cfg := parseConfig c
        construct .ricci r.shape cfg n
        scalarFromRicciTensor r cfg n pm am)
    | _, _, _, _ => badInput
  | _ => badInput

def handlers : List (String × Handler) :=
  [("curv.ctor", hCtor), ("curv.mcc", hMcc), ("curv.minv", hMinv), ("curv.mlow", hMlow),
   ("curv.cc", hCc), ("curv.lt", hLt), ("curv.fm", hFromMetric), ("curv.stress", hStress),
   ("curv.fch", hFromChristoffels), ("curv.fri", hFromRiemann), ("curv.frt", hFromRicci)]

end EinsteinpyLean.Curvature
