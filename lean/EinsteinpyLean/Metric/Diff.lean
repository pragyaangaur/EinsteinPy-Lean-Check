import EinsteinpyLean.Common.Handler
import EinsteinpyLean.Utils.Codec
import EinsteinpyLean.Metric.Model

/-!
# `epdiff` handlers of the Metric area

Line protocol, one case per line. Floats travel as the 16 hex digits of the IEEE bit pattern, every NaN as `nan`
(`Utils.Codec`). Tokens:

* class `s` (Schwarzschild), `k` (Kerr), `n` (Kerr-Newman); system `S` (Spherical), `B` (BoyerLindquist), `C` (anything else);
  flag `0` or `1`.
* Answers: an array `A:<hex> <hex> ...`, a float `F<hex>`, an error `E:<tag>`.
-/

namespace EinsteinpyLean.Metric

open EinsteinpyLean.Utils

def hexOf (x : Float) : String := renderFloat x

def renderArr (a : Arr) : String := "A:" ++ " ".intercalate (a.toList.map hexOf)

def renderR : R Arr → String
  | .ok a => renderArr a
  | .error e => "E:" ++ e.tag

def renderF : R Float → String
  | .ok x => "F" ++ hexOf x
  | .error e => "E:" ++ e.tag

def parseSys : String → Option Sys
  | "S" => some .spherical
  | "B" => some .bl
  | "C" => some .cartesian
  | _ => none

def parseCls : String → Option Cls
  | "s" => some .schw
  | "k" => some .kerr
  | "n" => some .kn
  | _ => none

def parseFlag : String → Option Bool
  | "0" => some false
  | "1" => some true
  | _ => none

def floats (l : List String) : Option (List Float) := l.mapM parseFloat

/-- A body from `cls sys M a Q`. -/
def mkBody (cls sys M a Q : String) (q : Float := 0.0) : Option Body := do
  pure ⟨← parseCls cls, ← parseSys sys, ← parseFloat M, ← parseFloat a, ← parseFloat Q, q⟩

def hAlpha : Handler
  | [M, a] => match parseFloat M, parseFloat a with
    | some M, some a => renderF (alphaOf M a)
    | _, _ => badInput
  | _ => badInput

def hSigma : Handler
  | [py, r, th, M, a] => match parseFlag py, floats [r, th, M, a] with
    | some py, some [r, th, M, a] => renderF (sigma py r th M a)
    | _, _ => badInput
  | _ => badInput

def hDelta : Handler
  | [py, r, M, a, Q] => match parseFlag py, floats [r, M, a, Q] with
    | some py, some [r, M, a, Q] => renderF (delta py r M a Q)
    | _, _ => badInput
  | _ => badInput

def hRho : Handler
  | [py, r, th, M, a] => match parseFlag py, floats [r, th, M, a] with
    | some py, some [r, th, M, a] => renderF (rho py r th M a)
    | _, _ => badInput
  | _ => badInput

def hSchRad : Handler
  | [M] => match parseFloat M with
    | some M => "F" ++ hexOf (schRad M)
    | none => badInput
  | _ => badInput

def renderSv : Sv → String
  | .int n => s!"I{n}"
  | .flt x => "F" ++ hexOf x

/-- `m.sing <name> <sys> M a Q th`. -/
def hSing : Handler
  | [nm, sys, M, a, Q, th] =>
    let name := match nm with
      | "schw" => some "Schwarzschild Metric"
      | "kerr" => some "Kerr Metric"
      | "kn" => some "Kerr-Newman Metric"
      | "base" => some "Base Metric"
      | _ => none
    match name, parseSys sys, floats [M, a, Q, th] with
    | some name, some sys, some [M, a, Q, th] =>
      match singularities name sys M a Q th with
      | .ok l => "S:" ++ " ".intercalate (l.map renderSv)
      | .error e => "E:" ++ e.tag
    | _, _, _ => badInput
  | _ => badInput

/-- `m.<op> <cls> <sys> M a Q r th`: `g`, `gi`, `dg`, `ch`. -/
def hTensor (op : String) : Handler
  | [cls, sys, M, a, Q, r, th] =>
    match mkBody cls sys M a Q, floats [r, th] with
    | some b, some [r, th] =>
      match op with
      | "g" => renderR (metricCov b r th)
      | "gi" => renderR (metricContra b r th)
      | "dg" =>
        match b.cls with
        | .schw => badInput
        | .kerr => if b.sys == .bl then renderR (kerrDg b.M b.a r th) else "E:CoordinateError"
        | .kn => if b.sys == .bl then renderR (knDg b.M b.a b.Q r th) else "E:CoordinateError"
      | "ch" => renderR (christoffels b r th)
      | _ => badInput
    | _, _ => badInput
  | _ => badInput

/-- `m.f <cls> <sys> M a Q q v0 .. v7`: `_f_vec`. -/
def hF : Handler
  | cls :: sys :: M :: a :: Q :: q :: vs =>
    match parseFloat q, floats vs with
    | some q, some vs =>
      if vs.length != 8 then badInput else
      match mkBody cls sys M a Q q with
      | some b =>
        let v := vs.toArray
        let res : R (Array Float) := match b.cls with
          | .schw => do let chl ← christoffels b v[1]! v[2]!; pure (schwF chl v)
          | .kerr => do
              if b.sys != .bl then throw .coordinate
              let chl ← christoffels b v[1]! v[2]!
              pure (kerrF chl v)
          | .kn => knF b v
        renderR res
      | none => badInput
    | _, _ => badInput
  | _ => badInput

/-- `m.em <op> <sys> M a Q q r th`: the Kerr-Newman fields. -/
def hEm (op : String) : Handler
  | [sys, M, a, Q, r, th] =>
    match mkBody "n" sys M a Q, floats [r, th] with
    | some b, some [r, th] =>
      match op with
      | "pc" => renderR (emPotCov b r th)
      | "pu" => renderR (emPotContra b r th)
      | "fc" => renderR (emTensorCov b r th)
      | "fu" => renderR (emTensorContra b r th)
      | _ => badInput
    | _, _ => badInput
  | _ => badInput

def renderTriples (l : List (Nat × Nat × Nat)) : String :=
  "L:" ++ ";".intercalate (l.map fun (i, j, k) => s!"{i},{j},{k}")

/-- A constructor argument `plain=<hex>` (no unit) or `<unit>=<hex>`. -/
def parseSpec (s : String) : Option (Option UDim × Float) :=
  match s.splitOn "=" with
  | [u, v] => do
      let x ← parseFloat v
      if u == "plain" then some (none, x) else some ((← unitDim u), x)
  | _ => none

/-- `m.ctor <cls> <Mspec> <aspec> <Qspec> <qspec>`: the `u.quantity_input` check of `__init__`, in signature order,
and then `sch_rad` from the raw `.value` of the mass. The decorator checks units but does not convert. -/
def hCtor : Handler
  | [cls, ms, as, qs, qq] =>
    match parseCls cls, parseSpec ms, parseSpec as, parseSpec qs, parseSpec qq with
    | some cls, some ms, some as, some qs, some qq =>
      let res : R Float := ctorRad cls ms as qs qq
      renderF res
    | _, _, _, _, _ => badInput
  | _ => badInput

/-- `m.base <mode> <sys> G(16) P(16)`: `BaseMetric` with a user supplied `metric_cov` and `perturbation`.
Mode `n`: no `metric_cov` (`TypeError`), `p`: no perturbation, `q`: with a perturbation. -/
def hBase : Handler
  | mode :: gs =>
    match floats gs with
    | some fs =>
      if fs.length != 32 then badInput else
      let G := (fs.take 16).toArray
      let P := (fs.drop 16).toArray
      match mode with
      | "n" => "E:TypeError|E:TypeError"
      | "p" | "q" =>
        let g := if mode == "q" then Array.ofFn (n := 16) fun i => G[i.val]! + P[i.val]! else G
        let gi := match inv4 g with
          | some x => renderArr x
          | none => "E:LinAlgError"
        renderArr g ++ "|" ++ gi
      | _ => badInput
    | none => badInput
  | _ => badInput

def handlers : List (String × Handler) :=
  [ ("m.alpha", hAlpha), ("m.sigma", hSigma), ("m.delta", hDelta), ("m.rho", hRho), ("m.schrad", hSchRad),
    ("m.sing", hSing),
    ("m.g", hTensor "g"), ("m.gi", hTensor "gi"), ("m.dg", hTensor "dg"), ("m.ch", hTensor "ch"),
    ("m.f", hF),
    ("m.pc", hEm "pc"), ("m.pu", hEm "pu"), ("m.fc", hEm "fc"), ("m.fu", hEm "fu"),
    ("m.nzc", fun _ => renderTriples nonzeroComputed), ("m.nzp", fun _ => renderTriples nonzeroList),
    ("m.ctor", hCtor), ("m.base", hBase),
    ("m.traj", fun _ => "NONE+DeprecationWarning") ]

end EinsteinpyLean.Metric
