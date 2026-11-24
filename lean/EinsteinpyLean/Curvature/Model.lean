import EinsteinpyLean.Common.Arr
import EinsteinpyLean.Tensor.Model

/-!
# Model of the curvature classes of `einsteinpy.symbolic`

Mirrors `metric.py`, `christoffel.py`, `riemann.py`, `ricci.py`, `einstein.py`,
`weyl.py`, `schouten.py`, `stress_energy_momentum.py` and `vector.py` of einsteinpy at
commit `63e1c54`, on exact rationals. Line references are to those files, relative to
`src/einsteinpy/symbolic/`.

Symbolic differentiation cannot run on rationals, so every derivative is replaced by a
2-jet at one rational point. A metric is given by `g`, `∂g` and `∂∂g` at the point. Then
`sympy.diff` of a Christoffel symbol is computed from `∂(g⁻¹) = -g⁻¹ (∂g) g⁻¹`.
`sympy.simplify` is the identity on the values at a point, so it does not appear.

The generic tensor machinery (`_change_config`, `lorentz_transform`) is the model of
`Tensor/Model.lean`, which this file reuses.
-/

namespace EinsteinpyLean.Curvature
open Arr

/-! ## Errors -/

/-- Errors, one constructor per raise site. The `tag` is the Python exception class. -/
inductive Err where
  /-- tensor.py:156-160 `Tensor.__init__`: `TypeError` for a config with a character
  other than `u` and `l`. -/
  | badConfig
  /-- tensor.py:162 `Tensor.__init__`: `ValueError`, rank of the array differs from the
  length of the config. -/
  | badRank
  /-- tensor.py:`BaseRelativityTensor.__init__`: `ValueError`, first axis of the array
  differs from the number of symbols. -/
  | badSyms
  /-- The `ValueError("config should be of length n")` of every subclass constructor
  (metric.py:42-43, christoffel.py:46-47, riemann.py:52-53, ricci.py:48-49, and so on). -/
  | badOrder
  /-- vector.py:45 `GenericVector.__init__`: "Dimension should be equal to 1". -/
  | notVector
  /-- metric.py:78 `MetricTensor.change_config`: "Configuration can't have one upper and
  one lower index in Metric Tensor." -/
  | metricConfig
  /-- sympy `NonSquareMatrixError` (a `ValueError`) from `Matrix.inv()`. -/
  | nonSquare
  /-- sympy `NonInvertibleMatrixError` (a `ValueError`) from `Matrix.inv()`. -/
  | singular
  /-- `Exception("Parent Metric not found, can't do configuration change")`, for example
  christoffel.py:108, riemann.py:136, ricci.py:138. -/
  | noParent
  /-- tensor.py:47 `_change_config`: bare `ValueError` for a bad new config. -/
  | changeBad
  /-- sympy `IndexError` raised inside `tensorcontraction`. -/
  | sympyIndex
  /-- sympy `ValueError` raised inside `tensorcontraction`. -/
  | sympyValue
  /-- weyl.py:108 and schouten.py:74: "Dimension of the space/space-time should be 3 or
  more". -/
  | dimTooSmall
  /-- `AttributeError`: a method that the class does not have. -/
  | noAttr
  deriving Repr, BEq, DecidableEq

def Err.tag : Err → String
  | .badConfig => "TypeError"
  | .badRank => "ValueError"
  | .badSyms => "ValueError"
  | .badOrder => "ValueError"
  | .notVector => "ValueError"
  | .metricConfig => "ValueError"
  | .nonSquare => "NonSquareMatrixError"
  | .singular => "NonInvertibleMatrixError"
  | .noParent => "Exception"
  | .changeBad => "ValueError"
  | .sympyIndex => "IndexError"
  | .sympyValue => "ValueError"
  | .dimTooSmall => "ValueError"
  | .noAttr => "AttributeError"

def ofTensor : Tensor.Err → Err
  | .changeConfigBad => .changeBad
  | .sympyIndex => .sympyIndex
  | .sympyValue => .sympyValue
  | .sameKindSum => .sympyValue
  | .noneIndex => .sympyValue
  | .indexOutOfRange => .sympyIndex
  | .badShape => .badRank

/-! ## The classes -/

/-- The classes of this area. `scalar` is `RicciScalar`. -/
inductive Kind where
  | metric | chris | riemann | ricci | scalar | einstein | weyl | schouten | stress | vector
  deriving Repr, BEq, DecidableEq

def Kind.ofString? : String → Option Kind
  | "metric" => some .metric | "chris" => some .chris | "riemann" => some .riemann
  | "ricci" => some .ricci | "scalar" => some .scalar | "einstein" => some .einstein
  | "weyl" => some .weyl | "schouten" => some .schouten | "stress" => some .stress
  | "vector" => some .vector | _ => none

/-- The order each constructor insists on (`self._order = ...`). -/
def Kind.order : Kind → Nat
  | .metric => 2 | .chris => 3 | .riemann => 4 | .ricci => 2 | .scalar => 0
  | .einstein => 2 | .weyl => 4 | .schouten => 2 | .stress => 2 | .vector => 1

/-- Python class name of the object `change_config` returns. stress_energy_momentum.py:95
builds an `EinsteinTensor`, not a `StressEnergyMomentumTensor`. -/
def Kind.changeClass : Kind → String
  | .metric => "MetricTensor" | .chris => "ChristoffelSymbols"
  | .riemann => "RiemannCurvatureTensor" | .ricci => "RicciTensor"
  | .scalar => "RicciScalar" | .einstein => "EinsteinTensor" | .weyl => "WeylTensor"
  | .schouten => "SchoutenTensor" | .stress => "EinsteinTensor"
  | .vector => "GenericVector"

/-- Python class name of the object `lorentz_transform` returns. `RicciScalar` has no
override, so it returns the base class. -/
def Kind.ltClass : Kind → String
  | .scalar => "BaseRelativityTensor"
  | .stress => "StressEnergyMomentumTensor"
  | k => k.changeClass

/-- The constructor checks, in the order Python runs them: `Tensor.__init__`
(tensor.py:156-165), `BaseRelativityTensor.__init__`, then the subclass. -/
def construct (k : Kind) (shape : List Nat) (config : String) (nsyms : Nat) : Except Err Unit := do
  unless Tensor.configChecker config do throw .badConfig
  if shape.length != config.length then throw .badRank
  if !shape.isEmpty && shape.head! != nsyms then throw .badSyms
  match k with
  | .vector => if shape.length != 1 then throw .notVector
  | .scalar => pure ()
  | _ => if config.length != k.order then throw .badOrder

/-! ## Small matrix helpers -/

def sumTo (n : Nat) (f : Nat → Rat) : Rat := (List.range n).foldl (fun a i => a + f i) 0

def g2 (a : Arr) (i j : Nat) : Rat := a.get [i, j]
def g3 (a : Arr) (i j k : Nat) : Rat := a.get [i, j, k]
def g4 (a : Arr) (i j k l : Nat) : Rat := a.get [i, j, k, l]

def mk2 (d : Nat) (f : Nat → Nat → Rat) : Arr := ofFn [d, d] fun x => f x[0]! x[1]!
def mk3 (d : Nat) (f : Nat → Nat → Nat → Rat) : Arr := ofFn [d, d, d] fun x => f x[0]! x[1]! x[2]!
def mk4 (d : Nat) (f : Nat → Nat → Nat → Nat → Rat) : Arr :=
  ofFn [d, d, d, d] fun x => f x[0]! x[1]! x[2]! x[3]!

/-- `sympy.Matrix(a.tolist()).inv()`: `NonSquareMatrixError` before
`NonInvertibleMatrixError`. -/
def invMat (a : Arr) : Except Err Arr :=
  match a.shape with
  | [n, m] =>
    if n != m then throw .nonSquare
    else match matInv a with
      | some r => pure r
      | none => throw .singular
  | _ => throw .nonSquare

/-! ## Metric objects -/

/-- A `MetricTensor` object: array and config. -/
structure Met where
  arr : Arr
  config : String
  deriving Repr, BEq

/-- Build a `MetricTensor` (metric.py:12-43). -/
def mkMet (arr : Arr) (config : String) (nsyms : Nat) : Except Err Met := do
  construct .metric arr.shape config nsyms
  return ⟨arr, config⟩

/-- `MetricTensor.change_config` (metric.py:66-80). -/
def Met.changeConfig (m : Met) (new : String) (nsyms : Nat) : Except Err Met := do
  if new == m.config then return m
  if new == "uu" || new == "ll" then
    let r ← invMat m.arr
    mkMet r new nsyms
  else throw .metricConfig

/-- `MetricTensor.inv` (metric.py:93-98), starting from an empty cache. -/
def Met.inv (m : Met) (nsyms : Nat) : Except Err Met :=
  if m.config == "ll" then m.changeConfig "uu" nsyms else m.changeConfig "ll" nsyms

/-- `MetricTensor.lower_config` (metric.py:111-113). -/
def Met.lower (m : Met) (nsyms : Nat) : Except Err Met :=
  if m.config == "ll" then pure m else m.inv nsyms

/-- `metric.lower_config().tensor()` and `metric.lower_config().inv().tensor()`, the two
arrays of `_change_config` (tensor.py:37-42), computed in that order. The inverse of the
lowered metric is the cached original when the metric was not lower. -/
def Met.lowerUpper (m : Met) : Except Err (Arr × Arr) := do
  if m.config == "ll" then
    let up ← invMat m.arr
    return (m.arr, up)
  else
    let lo ← invMat m.arr
    return (lo, m.arr)

/-! ## Config change and Lorentz transform on any class -/

/-- The generic body of every `change_config` (christoffel.py:105-117 and the same in
riemann, ricci, einstein, weyl, schouten, stress-energy and vector). `pm` is the object's
own parent metric, `am` the `metric` argument. Returns the class name and new config. -/
def changeConfig (k : Kind) (arr : Arr) (config new : String) (nsyms : Nat)
    (pm am : Option Met) : Except Err (String × Arr) := do
  if k == .scalar then throw .noAttr
  let some m := (match am with | some m => some m | none => pm) | throw .noParent
  -- `_change_config` checks the new config before it touches the metric
  unless new.length == config.length && Tensor.configChecker new do throw .changeBad
  let (lo, up) ← m.lowerUpper
  let r ← (Tensor.changeConfig arr config new lo up).mapError ofTensor
  construct k r.shape new nsyms
  return (k.changeClass, r)

/-- `lorentz_transform` of any class (tensor.py:424-459 and the wrappers). -/
def lorentz (k : Kind) (arr : Arr) (config : String) (tm : Arr) (nsyms : Nat) :
    Except Err (String × Arr) := do
  let r ← (Tensor.lorentzTransform arr config tm).mapError ofTensor
  construct k r.shape config nsyms
  return (k.ltClass, r)

/-! ## 2-jets of a metric -/

/-- The 2-jet of a metric at one point. `dg[k,i,j] = ∂_k g_ij` and
`ddg[k,l,i,j] = ∂_k ∂_l g_ij`. -/
structure Jet where
  d : Nat
  g : Arr
  dg : Arr
  ddg : Arr
  deriving Repr

/-- The jet of the lowered metric `metric.lower_config()`. For a lower metric it is the
jet itself. Otherwise the given jet is that of the upper metric `G` and `g = G⁻¹`, with
`∂g = -g (∂G) g` and `∂∂g = -(∂_l g)(∂_k G) g - g (∂_l ∂_k G) g - g (∂_k G)(∂_l g)`. -/
def lowerJet (config : String) (j : Jet) : Except Err Jet := do
  if config == "ll" then return j
  let g ← invMat j.g
  let d := j.d
  let mm (a b : Nat → Nat → Rat) : Nat → Nat → Rat := fun i k => sumTo d fun m => a i m * b m k
  let gf := g2 g
  let dG (k : Nat) : Nat → Nat → Rat := fun i m => g3 j.dg k i m
  let ddG (k l : Nat) : Nat → Nat → Rat := fun i m => g4 j.ddg k l i m
  let dgf (k : Nat) : Nat → Nat → Rat := fun i m => -(mm (mm gf (dG k)) gf i m)
  let ddgf (k l : Nat) : Nat → Nat → Rat := fun i m =>
    -(mm (mm (dgf l) (dG k)) gf i m) - (mm (mm gf (ddG k l)) gf i m)
      - (mm (mm gf (dG k)) (dgf l) i m)
  return ⟨d, g, mk3 d fun k i m => dgf k i m, mk4 d fun k l i m => ddgf k l i m⟩

/-- christoffel.py:60-79 `ChristoffelSymbols.from_metric`, on the lowered jet. Returns
the `ull` array. The code fills only `k <= j` and mirrors. -/
def christoffelOf (j : Jet) : Except Err Arr := do
  let d := j.d
  let ginv ← invMat j.g
  let f (i jj k : Nat) : Rat :=
    sumTo d fun n => g2 ginv i n / 2 *
      (g3 j.dg k n jj + g3 j.dg jj n k - g3 j.dg n jj k)
  return mk3 d fun i jj k => if k ≤ jj then f i jj k else f i k jj

/-- `∂_r Γ^t_{sn}` of the Christoffel symbols of a jet, indexed `[r,t,s,n]`. -/
def dChristoffelOf (j : Jet) : Except Err Arr := do
  let d := j.d
  let ginv ← invMat j.g
  let dginv (r t m : Nat) : Rat :=
    -(sumTo d fun a => sumTo d fun b => g2 ginv t a * g3 j.dg r a b * g2 ginv b m)
  let tt (m s n : Nat) : Rat := g3 j.dg n m s + g3 j.dg s m n - g3 j.dg m s n
  let dtt (r m s n : Nat) : Rat := g4 j.ddg r n m s + g4 j.ddg r s m n - g4 j.ddg r m s n
  return mk4 d fun r t s n => sumTo d fun m =>
    dginv r t m / 2 * tt m s n + g2 ginv t m / 2 * dtt r m s n

/-- riemann.py:79-93, the loop of `RiemannCurvatureTensor.from_christoffels`, on the
`ull` array `gam` and its derivative `dgam[r,t,s,n]`. Gives `R[t][s][r][n]`. -/
def riemannOf (d : Nat) (gam dgam : Arr) : Arr :=
  mk4 d fun t s r n =>
    g4 dgam r t s n - g4 dgam n t s r +
      sumTo d fun p => g3 gam p s n * g3 gam t p r - g3 gam p s r * g3 gam t p n

/-- `tensorcontraction(riemann, (0, 2))` (ricci.py:71). -/
def ricciOfRiemann (r : Arr) : Except Err Arr :=
  (tensorcontraction r 0 2).mapError fun
    | .indexError => .sympyIndex
    | .valueError => .sympyValue

/-- ricci.py:231-237 `RicciScalar.from_riccitensor` after the config change: the trace of
a mixed `ul` Ricci tensor. -/
def traceOf (r : Arr) : Except Err Arr :=
  (tensorcontraction r 0 1).mapError fun
    | .indexError => .sympyIndex
    | .valueError => .sympyValue

/-- Ricci scalar of a lower Ricci tensor and a metric (`change_config("ul")` then the
trace). -/
def ricciScalarLower (ric : Arr) (m : Met) (nsyms : Nat) : Except Err Arr := do
  let (_, r) ← changeConfig .ricci ric "ll" "ul" nsyms none (some m)
  traceOf r

structure Pipeline where
  jet : Jet
  christoffel : Arr
  riemann : Arr
  ricci : Arr
  scalar : Arr

/-- Everything `from_metric` computes on the way, for a jet of the lowered metric. The
Ricci scalar uses `lower_config().inv()`, which for a jet is `g⁻¹`. -/
def pipeline (j : Jet) (m : Met) : Except Err Pipeline := do
  let chr ← christoffelOf j
  let dchr ← dChristoffelOf j
  let riem := riemannOf j.d chr dchr
  let ric ← ricciOfRiemann riem
  let sc ← ricciScalarLower ric m j.d
  return ⟨j, chr, riem, ric, sc⟩

/-- The scalar `r_scalar.expr` as a rational. -/
def Pipeline.R (p : Pipeline) : Rat := p.scalar.get []

/-- einstein.py:54-56: `Ric - (1/2) g R`, with `1/2` taken as exact. (In Python it is the
float `0.5`, see `Diff.lean`.) -/
def einsteinOf (p : Pipeline) : Arr :=
  mk2 p.jet.d fun i k => g2 p.ricci i k - (1 / 2) * g2 p.jet.g i k * p.R

/-- schouten.py:65-74. -/
def schoutenOf (p : Pipeline) : Except Err Arr := do
  let d := p.jet.d
  unless d ≥ 3 do throw .dimTooSmall
  return mk2 d fun i k =>
    (g2 p.ricci i k - p.R * g2 p.jet.g i k / (2 * ((d : Rat) - 1))) / ((d : Rat) - 2)

/-- weyl.py:65-108. `m` is the metric object of the call (for the config change of the
Riemann tensor). -/
def weylOf (p : Pipeline) (m : Met) : Except Err Arr := do
  let d := p.jet.d
  if d > 3 then
    let (lo, up) ← m.lowerUpper
    let rcov ← (Tensor.changeConfig p.riemann "ulll" "llll" lo up).mapError ofTensor
    let g := p.jet.g
    let dd : Rat := d
    return mk4 d fun i k l mm =>
      g4 rcov i k l mm +
        (g2 p.ricci i mm * g2 g k l - g2 p.ricci i l * g2 g k mm
          + g2 p.ricci k l * g2 g i mm - g2 p.ricci k mm * g2 g i l) / (dd - 2) +
        p.R * (g2 g i l * g2 g k mm - g2 g i mm * g2 g k l) / ((dd - 1) * (dd - 2))
  else if d == 3 then return ofFn [3, 3, 3, 3] fun _ => 0
  else throw .dimTooSmall

/-- stress_energy_momentum.py:59-64 without the constant factor `c^4/(8 π G)`:
`G_ij - Λ g_ij`. -/
def stressCore (p : Pipeline) (lam : Rat) : Arr :=
  mk2 p.jet.d fun i k => g2 (einsteinOf p) i k - lam * g2 p.jet.g i k

/-- Run `from_metric` for a metric given by `config` and a jet of its array. -/
def fromMetric (config : String) (j : Jet) : Except Err (Pipeline × Met) := do
  let lj ← lowerJet config j
  let m : Met := ⟨mk2 j.d (g2 j.g), config⟩
  let p ← pipeline lj m
  return (p, m)

/-! ## `from_christoffels`, `from_riemann`, `from_riccitensor` on given arrays -/

/-- The first step of `RiemannCurvatureTensor.from_christoffels` (riemann.py:75-93):
changes `chris` to `ull` when needed, then runs the loop. The derivative array transforms
slab by slab because the metric is constant. Returns the array and the parent metric the
Riemann tensor ends up with. -/
def riemannFromChristoffels (gam dgam : Arr) (config : String) (nsyms : Nat)
    (pm am : Option Met) : Except Err (Arr × Option Met) := do
  let mut gam := gam
  let mut dgam := dgam
  if config != "ull" then
    let (_, g') ← changeConfig .chris gam config "ull" nsyms pm am
    let slabs ← (List.range nsyms).mapM fun r => do
      let sl : Arr := ofFn (gam.shape) fun x => dgam.get (r :: x)
      let (_, s') ← changeConfig .chris sl config "ull" nsyms pm am
      pure s'
    gam := g'
    dgam := ofFn (nsyms :: gam.shape) fun x =>
      (slabs[x.head!]!).get x.tail
  let eff := match am with | some m => some m | none => pm
  return (riemannOf nsyms gam dgam, eff)

/-- ricci.py:66-75 `RicciTensor.from_riemann`. -/
def ricciFromRiemann (r : Arr) (config : String) (nsyms : Nat) (pm am : Option Met) :
    Except Err (Arr × Option Met) := do
  let mut r := r
  if config != "ulll" then
    let (_, r') ← changeConfig .riemann r config "ulll" nsyms pm am
    r := r'
  let eff := match am with | some m => some m | none => pm
  let ric ← ricciOfRiemann r
  return (ric, eff)

/-- ricci.py:231-242 `RicciScalar.from_riccitensor`. -/
def scalarFromRicciTensor (r : Arr) (config : String) (nsyms : Nat) (pm am : Option Met) :
    Except Err Arr := do
  let mut r := r
  if config != "ul" then
    let (_, r') ← changeConfig .ricci r config "ul" nsyms pm am
    r := r'
  traceOf r

end EinsteinpyLean.Curvature
