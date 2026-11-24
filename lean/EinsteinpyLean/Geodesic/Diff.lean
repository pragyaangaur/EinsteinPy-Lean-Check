import EinsteinpyLean.Common.Handler
import EinsteinpyLean.Utils.Codec
import EinsteinpyLean.Geodesic.Model
import EinsteinpyLean.Geodesic.ModelRays

/-!
# `epdiff_geodesic` handlers

Floats travel as 16 hex digits (every NaN as `nan`), as in `Utils.Codec`. A float list is comma
separated, `-` is the empty list. An error answer is `E:<tag>`. Kinds are `sch`, `kerr` and `kn`.
Masks are four characters `0`/`1` that tell which of `q1 p1 q2 p2` have `dtype=object`.
-/

namespace EinsteinpyLean.Geodesic

open EinsteinpyLean.Utils
open EinsteinpyLean.Utils.Py

def pFloats (s : String) : Option (List Float) :=
  if s == "-" then some [] else (s.splitOn ",").mapM parseFloat

def pKind : String → Option Kind
  | "sch" => some .sch
  | "kerr" => some .kerr
  | "kn" => some .kerrnewman
  | _ => none

def pBool : String → Option Bool
  | "1" => some true
  | "0" => some false
  | _ => none

def pMask (s : String) : Option (List Bool) :=
  if s.length != 4 then none else s.toList.mapM fun c => if c == '1' then some true else if c == '0' then some false else none

def pOptF (s : String) : Option (Option Float) :=
  if s == "-" then some none else (parseFloat s).map some

def rF (l : List Float) : String := if l.isEmpty then "-" else ",".intercalate (l.map renderFloat)

/-- The class of the exception, without its message. -/
def rErr (e : Exc) : String := "E:" ++ (e.tag.splitOn ":").head!

def rGErr (e : GErr) : String := "E:" ++ (e.tag.splitOn ":").head!

def mkVec (l : List Float) (o : Bool) : Option Vec :=
  if l.length != 4 then none else some ⟨l.toArray, o⟩

/-- `geo.metric <kind> <params> <q>`: `g(q, *params)` on a `float64` array, 16 floats. -/
def hMetric : Handler
  | [k, prm, q] =>
    match pKind k, pFloats prm, pFloats q with
    | some k, some prm, some q =>
      match realMetric k prm q.toArray with
      | .ok g => rF g.toList
      | .error e => rErr e
    | _, _, _ => badInput
  | _ => badInput

def renderElem : Elem → String
  | .dual d => renderFloat d.val ++ ":" ++ renderFloat d.deriv
  | _ => "z"

/-- `geo.dmetric <kind> <params> <q4> <wrt>`: the metric on dual coordinates as `_diff_g` builds them. -/
def hDMetric : Handler
  | [k, prm, q, w] =>
    match pKind k, pFloats prm, pFloats q, w.toNat? with
    | some k, some prm, some q, some w =>
      if q.length != 4 || w > 3 then badInput else
      let dc : Array (Dual Float) := q.toArray.map fun x => ⟨x, 0⟩
      let dc := dc.set! w ⟨q[w]!, 1⟩
      match dualMetric k dc prm with
      | .ok m => " ".intercalate (m.toList.map fun row => ",".intercalate (row.toList.map renderElem))
      | .error e => rErr e
    | _, _, _, _ => badInput
  | _ => badInput

/-- `geo.jac <kind> <params> <q> <wrt>`: `_jacobian_g` of the einsteinpy metric function. -/
def hJac : Handler
  | [k, prm, q, w] =>
    match pKind k, pFloats prm, pFloats q, w.toNat? with
    | some k, some prm, some q, some w =>
      match jacobianG (dualMetric k) prm q (.int (w : Int)) with
      | .ok j => rF j.toList
      | .error e => rErr e
    | _, _, _, _ => badInput
  | _ => badInput

/-- `geo.sigma <np|py> <r> <th> <a>`: `sigma(r, theta, a)`; `py` is a Python float `r`. -/
def hSigma : Handler
  | [rk, r, th, a] =>
    match parseFloat r, parseFloat th, parseFloat a with
    | some r, some th, some a =>
      if rk == "np" then "F" ++ renderFloat (sigmaR r th a)
      else if rk == "py" then
        match powReal r 2 with
        | .ok r2 => "F" ++ renderFloat (r2 + sq (a * Float.cos th))
        | .error e => rErr e
      else badInput
    | _, _, _ => badInput
  | _ => badInput

/-- `geo.delta <np|py> <r> <a> <Q|->`: `delta(r, a, Q)`. -/
def hDelta : Handler
  | [rk, r, a, q] =>
    match parseFloat r, parseFloat a, pOptF q with
    | some r, some a, some q =>
      let Q := q.getD 0
      if rk == "np" then
        match deltaR r a Q with
        | .ok v => "F" ++ renderFloat v
        | .error e => rErr e
      else if rk == "py" then
        match powReal r 2, powReal a 2, powReal Q 2 with
        | .ok r2, .ok a2, .ok q2 => "F" ++ renderFloat (((r2 - (2 * r)) + a2) + q2)
        | .error e, _, _ => rErr e
        | _, .error e, _ => rErr e
        | _, _, .error e => rErr e
      else badInput
    | _, _, _ => badInput
  | _ => badInput

/-- `geo.P <kind> <params> <q> <p> <tl>`: `_P`. -/
def hP : Handler
  | [k, prm, q, p, tl] =>
    match pKind k, pFloats prm, pFloats q, pFloats p, pBool tl with
    | some k, some prm, some q, some p, some tl =>
      match pNorm k prm q.toArray p tl with
      | .ok P => rF P.toList
      | .error e => rErr e
    | _, _, _, _, _ => badInput
  | _ => badInput

/-- `geo.z <order>`: `_Z(order)`. -/
def hZ : Handler
  | [o] =>
    match parseFloat o with
    | some o =>
      match zConst o with
      | .ok (a, b) => rF [a, b]
      | .error e => rErr e
    | none => badInput
  | _ => badInput

/-- `geo.flow <A|B> <kind> <params> <delta> <q1> <p1> <q2> <p2> <mask>`. -/
def hFlow : Handler
  | [ab, k, prm, d, q1, p1, q2, p2, m] =>
    match pKind k, pFloats prm, parseFloat d, pFloats q1, pFloats p1, pFloats q2, pFloats p2, pMask m with
    | some k, some prm, some d, some q1, some p1, some q2, some p2, some [a, b, c, e] =>
      match mkVec q1 a, mkVec p1 b, mkVec q2 c, mkVec p2 e with
      | some q1, some p1, some q2, some p2 =>
        let r := if ab == "A" then flowA k prm q1 p1 q2 p2 d else flowB k prm q1 p1 q2 p2 d
        match r with
        | .ok (u, v) => rF (u.d.toList ++ v.d.toList)
        | .error e => rErr e
      | _, _, _, _ => badInput
    | _, _, _, _, _, _, _, _ => badInput
  | _ => badInput

/-- `geo.mixed <delta> <omega> <q1> <p1> <q2> <p2>`. -/
def hMixed : Handler
  | [d, o, q1, p1, q2, p2] =>
    match parseFloat d, parseFloat o, pFloats q1, pFloats p1, pFloats q2, pFloats p2 with
    | some d, some o, some q1, some p1, some q2, some p2 =>
      match mkVec q1 false, mkVec p1 false, mkVec q2 false, mkVec p2 false with
      | some q1, some p1, some q2, some p2 =>
        let r := flowMixed q1 p1 q2 p2 d o
        rF (r.toList.flatMap fun v => v.d.toList)
      | _, _, _, _ => badInput
    | _, _, _, _, _, _ => badInput
  | _ => badInput

/-- `geo.step <kind> <params> <order> <omega> <delta> <q1> <p1> <q2> <p2> <mask>`: one `_ord_n` call. -/
def hStep : Handler
  | [k, prm, o, om, d, q1, p1, q2, p2, m] =>
    match pKind k, pFloats prm, parseFloat o, parseFloat om, parseFloat d, pFloats q1, pFloats p1,
      pFloats q2, pFloats p2, pMask m with
    | some k, some prm, some o, some om, some d, some q1, some p1, some q2, some p2, some [a, b, c, e] =>
      match orderIndex o with
      | none => "E:NotImplementedError"
      | some oi =>
        match mkVec q1 a, mkVec p1 b, mkVec q2 c, mkVec p2 e with
        | some q1, some p1, some q2, some p2 =>
          match ordSelf ⟨k, prm, o, om⟩ oi q1 p1 q2 p2 d with
          | .ok r => rF (r.toList.flatMap fun v => v.d.toList)
          | .error e => rErr e
        | _, _, _, _ => badInput
    | _, _, _, _, _, _, _, _, _, _ => badInput
  | _ => badInput

def renderRun (r : RunResult) : String :=
  let flat := r.rows.toList.flatMap fun rs => rs.toList.flatMap fun v => v.d.toList
  s!"R{rF flat};W{";".intercalate (r.warned.toList.map toString)}"

/-- `geo.run <kind> <params> <order> <omega> <delta> <steps> <rtol> <atol> <sw> <tl> <q0> <p0>`:
`GeodesicIntegrator` stepped `steps` times. -/
def hRun : Handler
  | [k, prm, o, om, d, n, rt, atl, sw, tl, q0, p0] =>
    match pKind k, pFloats prm, parseFloat o, parseFloat om, parseFloat d, n.toNat?, parseFloat rt,
      parseFloat atl, pBool sw, pBool tl, pFloats q0, pFloats p0 with
    | some k, some prm, some o, some om, some d, some n, some rt, some atl, some sw, some tl, some q0, some p0 =>
      match runSteps ⟨k, prm, o, om⟩ tl n d rt atl sw q0.toArray p0.toArray with
      | .ok r => renderRun r
      | .error e => rGErr e
    | _, _, _, _, _, _, _, _, _, _, _, _ => badInput
  | _ => badInput

/-- `geo.geodesic <cls> <name> <params> <pos> <mom> <cart> <tl> <steps|-> <delta|-> <rtol|-> <atol|->
<order|-> <omega|-> <sw|->`: `Geodesic`, `Timelike` or `Nulllike`. -/
def hGeodesic : Handler
  | [cls, name, prm, pos, mom, cart, tl, n, d, rt, atl, o, om, sw] =>
    match pFloats prm, pFloats pos, pFloats mom, pBool cart, pBool tl, pOptF d, pOptF rt, pOptF atl,
      pOptF o, pOptF om, (if sw == "-" then some none else (pBool sw).map some) with
    | some prm, some pos, some mom, some cart, some tl, some d, some rt, some atl, some o, some om, some sw =>
      let steps : Option Int := if n == "-" then some 50 else n.toInt?
      let timeLike := if cls == "Timelike" then true else if cls == "Nulllike" then false else tl
      match steps with
      | none => badInput
      | some steps =>
        match geodesic name prm pos mom timeLike cart steps (d.getD 0.5) (rt.getD 0.01) (atl.getD 0.01)
          (o.getD 2) (om.getD 1) (sw.getD false) with
        | .ok g =>
          s!"P{rF g.momentum.toList};T{rF (g.traj.toList.flatMap (·.toList))};W{";".intercalate (g.warned.toList.map toString)}"
        | .error e => rGErr e
    | _, _, _, _, _, _, _, _, _, _, _ => badInput
  | _ => badInput

def pRhs : String → Option Rhs
  | "exp" => some .exp
  | "osc" => some .osc
  | "poly" => some .poly
  | "lorenz" => some .lorenz
  | "const" => some .const
  | _ => none

/-- `geo.rk4 <rhs> <t0> <tb> <h> <y0> <n>`: `RK4naive` after `n` steps: `t`, `y`, direction and warnings. -/
def hRk4 : Handler
  | [f, t0, tb, h, y0, n] =>
    match pRhs f, parseFloat t0, parseFloat tb, parseFloat h, pFloats y0, n.toNat? with
    | some f, some t0, some tb, some h, some y0, some n =>
      let dir := rkDirection t0 tb
      let (t, y, warns) := Id.run do
        let mut t := t0
        let mut y := y0.toArray
        let mut warns := 0
        for _ in List.range n do
          let (t', y', w) := rk4Step f.eval h tb dir t y
          t := t'
          y := y'
          if w then warns := warns + 1
        pure (t, y, warns)
      s!"{rF (t :: y.toList)};D{dir};W{warns}"
    | _, _, _, _, _, _ => badInput
  | _ => badInput

/-- `geo.rk45 <h> <rtol|-> <atol|-> <y0 float|other>`: the arguments given to scipy. -/
def hRk45 : Handler
  | [h, rt, atl, kind] =>
    match parseFloat h, pOptF rt, pOptF atl with
    | some h, some rt, some atl =>
      let (a, b, c, d) := rk45Args h rt atl
      rF [a, b, c, d] ++ s!";V{if kind == "float" then 0 else 1}"
    | _, _, _ => badInput
  | _ => badInput

/-- `geo.sh.consts <m>`: `b_crit` and `horizon`. -/
def hShConsts : Handler
  | [m] => match parseFloat m with
    | some m => rF [bCrit m, horizon m]
    | none => badInput
  | _ => badInput

/-- `geo.sh.b <m> <fov> <n>`: `_compute_B`. -/
def hShB : Handler
  | [m, f, n] => match parseFloat m, parseFloat f, n.toInt? with
    | some m, some f, some n =>
      match linspace (bCrit m) f n with
      | .ok a => rF a.toList
      | .error e => rErr e
    | _, _, _ => badInput
  | _ => badInput

/-- `geo.sh.int <blue|red> <m> <b> <r list>`: the integrands on an array of nodes. -/
def hShInt : Handler
  | [c, m, b, rs] => match parseFloat m, parseFloat b, pFloats rs with
    | some m, some b, some rs =>
      if c == "blue" || c == "red" then rF (rs.map (intensity (c == "blue") m b)) else badInput
    | _, _, _ => badInput
  | _ => badInput

/-- `geo.sh.root <m> <r> <i>`: `_root_equation`. -/
def hShRoot : Handler
  | [m, r, i] => match parseFloat m, parseFloat r, parseFloat i with
    | some m, some r, some i =>
      match rootEq m r i with
      | .ok (.re x) => "F" ++ renderFloat x
      | .ok (.cx a b) => "C" ++ renderFloat a ++ "," ++ renderFloat b
      | .error e => rErr e
    | _, _, _ => badInput
  | _ => badInput

/-- `geo.emb.ctor <m kg>`: `self.M.value` and `self.r_init.value`. -/
def hEmbCtor : Handler
  | [m] => match parseFloat m with
    | some m => let M := embMass m; rF [M, embRInit M]
    | none => badInput
  | _ => badInput

/-- `geo.emb.f <M> <r>`: `radial_coord` and `gradient` for a mass value `M`. -/
def hEmbF : Handler
  | [m, r] => match parseFloat m, parseFloat r with
    | some m, some r => rF [radialCoord m r, gradient m r]
    | _, _ => badInput
  | _ => badInput

/-- `geo.emb.vals <m kg> <alpha>`: `get_values(alpha)`, x axis then y axis. -/
def hEmbVals : Handler
  | [m, a] => match parseFloat m, parseFloat a with
    | some m, some a =>
      let (xs, ys) := getValues (embMass m) a
      s!"{rF xs.toList};{rF ys.toList}"
    | _, _ => badInput
  | _ => badInput

def handlers : List (String × Handler) :=
  [("geo.metric", hMetric), ("geo.dmetric", hDMetric), ("geo.jac", hJac), ("geo.sigma", hSigma),
   ("geo.delta", hDelta), ("geo.P", hP), ("geo.z", hZ), ("geo.flow", hFlow), ("geo.mixed", hMixed),
   ("geo.step", hStep), ("geo.run", hRun), ("geo.geodesic", hGeodesic), ("geo.rk4", hRk4),
   ("geo.rk45", hRk45),
   ("geo.sh.consts", hShConsts), ("geo.sh.b", hShB), ("geo.sh.int", hShInt), ("geo.sh.root", hShRoot),
   ("geo.emb.ctor", hEmbCtor), ("geo.emb.f", hEmbF), ("geo.emb.vals", hEmbVals)]

end EinsteinpyLean.Geodesic
