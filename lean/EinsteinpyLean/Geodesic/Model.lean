import EinsteinpyLean.Utils.Dual

/-!
# Model of `einsteinpy.geodesic` and `einsteinpy.integrators`

Mirrors `geodesic/utils.py`, `geodesic/geodesic.py`, `integrators/utils.py`, `integrators/fantasy.py` and
`integrators/runge_kutta.py` at commit `63e1c54`. Core Lean only. Every `Float` operation is the same
IEEE operation that NumPy or Python performs, so the difftests compare bit patterns.

## What the Python code really computes

The FANTASY integrator mixes three kinds of arithmetic. The model copies each one.

* The metric functions `_sch`, `_kerr` and `_kerrnewman` are called in two ways. The integrator calls them
  on a `float64` array (`g(q, *g_prms)`), and every number is a `numpy.float64`, so a division by zero
  gives `inf` or `nan` and never an exception. The Jacobian `_jacobian_g` calls them on `DualNumber`
  coordinates, where every number is a Python float, so a division by zero raises `ZeroDivisionError`
  and `a ** 2` raises `OverflowError`. `realSch`, `realKerr`, `realKerrNewman` are the first mode, `dualSch`,
  `dualKerr`, `dualKerrNewman` (with `Utils.Py.jacobianG`) the second.
  A scalar `x ** 2` of NumPy is `pow(x, 2.0)` (not `x * x`).
* A matrix product depends on the dtype. `J @ p` with a `float64` Jacobian and a `float64` vector goes to
  BLAS (Apple Accelerate on the pinned machine), where a dot product of four numbers is
  `(a0 b0 + a2 b2) + (a1 b1 + a3 b3)` and each matrix row is the same dot product (`dotBlas`). The metric
  array `g(q)` has dtype `object`, so every product with it, and every product with an `object` vector, is
  done in Python, summing from the integer `0` in order (`dotObj`). A `Vec` carries the dtype flag `obj`.
  Only the very first `_flow_A` of a run sees `float64` vectors, because every flow result is an `object`
  array.
* The scheme is composed from `_ord_2` with Yoshida triple jumps. `_ord_4`, `_ord_6` and `_ord_8` all read
  the coefficients from `_Z(self.order)`, the order of the whole integrator, not their own order. This is
  mirrored (`ordN`), and it is the bug of `bugs/geodesic-fantasy-yoshida-order.yaml`. `ordN` takes the
  order that `_Z` is called with as an argument, so `Props.lean` and `Spec.lean` can state what the
  correct code would do.

Elements of the `object` arrays are assumed to be `numpy.float64`. An element that is a Python float
(possible only for a zero product) would make `2 / r` raise at `r = 0` instead of giving `inf`; the
difftests keep `r` and `sin theta` away from exact zeros inside an integration, and test the metric
functions at such points on a plain `float64` array.

Error classes are the Python ones, as `Utils.Exc`. `NotImplementedError` is added here.
-/

namespace EinsteinpyLean.Geodesic

open EinsteinpyLean.Utils
open EinsteinpyLean.Utils.Py

/-- Python errors of this area: the arithmetic ones of `Utils.Exc` and `NotImplementedError`. -/
inductive GErr where
  | exc (e : Exc)
  /-- `raise NotImplementedError(...)` of `Geodesic.__init__` or `GeodesicIntegrator.__init__`. -/
  | notImplemented
  deriving Repr, BEq, Inhabited

def GErr.tag : GErr → String
  | .exc e => e.tag
  | .notImplemented => "NotImplementedError"

abbrev GR := Except GErr

def lift {α : Type} (x : Except Exc α) : GR α :=
  match x with
  | .ok v => .ok v
  | .error e => .error (.exc e)

/-! ## The three metrics -/

inductive Kind where
  | sch | kerr | kerrnewman
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `params[i]` of a tuple: `IndexError` when it is too short. -/
def param (prm : List Float) (i : Nat) : Except Exc Float :=
  match prm[i]? with
  | some x => pure x
  | none => throw .indexError

/-- `x_vec[1], x_vec[2]`. -/
def rth (q : Array Float) : Except Exc (Float × Float) :=
  if q.size < 3 then throw .indexError else pure (q[1]!, q[2]!)

/-- `x ** 2` of a `numpy.float64`: the C library `pow`. -/
def sq (x : Float) : Float := Float.pow x 2

/-- geodesic/utils.py:61-83 `sigma` on `numpy.float64` inputs: `r**2 + (a * cos(theta))**2`. -/
def sigmaR (r th a : Float) : Float := sq r + sq (a * Float.cos th)

/-- geodesic/utils.py:86-110 `delta` on a `numpy.float64` `r`, Python floats `a` and `Q`
(`Q = 0` is the integer zero, which adds `+0.0`). `a ** 2` is a Python float power, so it can raise. -/
def deltaR (r a Q : Float) : Except Exc Float := do
  let a2 ← powReal a 2
  let q2 ← powReal Q 2
  pure ((((sq r) - (2 * r)) + a2) + q2)

/-- geodesic/utils.py:113-142 `_sch` on a `float64` array, row-major 4 x 4 (the integer zeros are `0.0`). -/
def realSch (q : Array Float) : Except Exc (Array Float) := do
  let (r, th) ← rth q
  let tmp := 1.0 - (2 / r)
  let g00 := -1 / tmp
  let g11 := tmp
  let g22 := 1 / sq r
  let g33 := 1 / sq (r * Float.sin th)
  pure #[g00, 0, 0, 0,  0, g11, 0, 0,  0, 0, g22, 0,  0, 0, 0, g33]

/-- geodesic/utils.py:145-179 `_kerr` on a `float64` array. -/
def realKerr (prm : List Float) (q : Array Float) : Except Exc (Array Float) := do
  let a ← param prm 0
  let (r, th) ← rth q
  let sg := sigmaR r th a
  let dl ← deltaR r a 0
  let a2 ← powReal a 2
  let g00 := -(((sq r + a2) + ((2 * r) * sq (a * Float.sin th)) / sg) / dl)
  let g11 := dl / sg
  let g22 := 1 / sg
  let g33 := (1 / (dl * sq (Float.sin th))) * (1 - (2 * r) / sg)
  let g03 := (-((2 * r) * a)) / (sg * dl)
  pure #[g00, 0, 0, g03,  0, g11, 0, 0,  0, 0, g22, 0,  g03, 0, 0, g33]

/-- geodesic/utils.py:182-224 `_kerrnewman` on a `float64` array. -/
def realKerrNewman (prm : List Float) (q : Array Float) : Except Exc (Array Float) := do
  let a ← param prm 0
  let Q ← param prm 1
  let (r, th) ← rth q
  let sg := sigmaR r th a
  let dl ← deltaR r a Q
  let a2 ← powReal a 2
  let r2 := sq r
  let sint2 := sq (Float.sin th)
  let csct2 := 1 / sint2
  let csct4 := 1 / sq sint2
  let denom := dl * sq ((a2 + 2 * r2) + a2 * Float.cos (2 * th))
  let g00 := -(((4 * sg) * (sq (a2 + r2) - (a2 * dl) * sint2)) / denom)
  let g11 := dl / sg
  let g22 := 1 / sg
  let g33 := ((sg * csct4) * (-a2 + dl * csct2)) / (dl * sq (a2 - (a2 + r2) * csct2))
  let g03 := -((((4 * a) * ((a2 - dl) + r2)) * sg) / denom)
  pure #[g00, 0, 0, g03,  0, g11, 0, 0,  0, 0, g22, 0,  g03, 0, 0, g33]

def realMetric : Kind → List Float → Array Float → Except Exc (Array Float)
  | .sch, _, q => realSch q
  | .kerr, prm, q => realKerr prm q
  | .kerrnewman, prm, q => realKerrNewman prm q

/-! ## The same metrics on `DualNumber` coordinates -/

private def z0 : Elem := .int 0

/-- `sigma(r, theta, a)` on duals: `r**2 + (a * np.cos(theta))**2`. -/
def sigmaD (r th : Dual Float) (a : Float) : Except Exc (Dual Float) := do
  let r2 ← powS r (.int 2)
  let ac ← mulS (cosD th) (.py a)
  let ac2 ← powS ac (.int 2)
  pure (addD r2 ac2)

/-- `delta(r, a, Q)` on duals: `(r**2) - (2*r) + (a**2) + Q**2`. `Q = 0` is the integer zero. -/
def deltaD (r : Dual Float) (a : Float) (Q : Option Float) : Except Exc (Dual Float) := do
  let r2 ← powS r (.int 2)
  let tr ← mulS r (.int 2)
  let a2 ← powReal a 2
  let d1 ← addS (subD r2 tr) (.py a2)
  match Q with
  | none => addS d1 (.int 0)
  | some Q => do addS d1 (.py (← powReal Q 2))

def dualSch : Metric := fun q _ => do
  let r := q[1]!
  let th := q[2]!
  let t2 ← rdivS r (.int 2)
  let tmp ← rsubS t2 (.py 1.0)
  let g00 ← rdivS tmp (.int (-1))
  let r2 ← powS r (.int 2)
  let g22 ← rdivS r2 (.int 1)
  let rs ← powS (mulD r (sinD th)) (.int 2)
  let g33 ← rdivS rs (.int 1)
  pure #[#[.dual g00, z0, z0, z0], #[z0, .dual tmp, z0, z0], #[z0, z0, .dual g22, z0],
    #[z0, z0, z0, .dual g33]]

def dualKerr : Metric := fun q prm => do
  let a ← param prm 0
  let r := q[1]!
  let th := q[2]!
  let sg ← sigmaD r th a
  let dl ← deltaD r a none
  let r2 ← powS r (.int 2)
  let a2 ← powReal a 2
  let tr ← mulS r (.int 2)
  let as ← mulS (sinD th) (.py a)
  let as2 ← powS as (.int 2)
  let num ← divD (mulD tr as2) sg
  let g00 ← divD (negD (addD (← addS r2 (.py a2)) num)) dl
  let g11 ← divD dl sg
  let g22 ← rdivS sg (.int 1)
  let s2 ← powS (sinD th) (.int 2)
  let inv ← rdivS (mulD dl s2) (.int 1)
  let fr ← divD tr sg
  let om ← rsubS fr (.int 1)
  let g33 := mulD inv om
  let t3 ← mulS (← mulS r (.int 2)) (.py a)
  let g03 ← divD (negD t3) (mulD sg dl)
  pure #[#[.dual g00, z0, z0, .dual g03], #[z0, .dual g11, z0, z0], #[z0, z0, .dual g22, z0],
    #[.dual g03, z0, z0, .dual g33]]

def dualKerrNewman : Metric := fun q prm => do
  let a ← param prm 0
  let Q ← param prm 1
  let r := q[1]!
  let th := q[2]!
  let sg ← sigmaD r th a
  let dl ← deltaD r a (some Q)
  let a2 ← powReal a 2
  let r2 ← powS r (.int 2)
  let sint2 ← powS (sinD th) (.int 2)
  let csct2 ← rdivS sint2 (.int 1)
  let csct4 ← rdivS (← powS sint2 (.int 2)) (.int 1)
  let t1 ← addS (← mulS r2 (.int 2)) (.py a2)
  let t2 ← mulS (cosD (← mulS th (.int 2))) (.py a2)
  let denom := mulD dl (← powS (addD t1 t2) (.int 2))
  let u1 ← powS (← addS r2 (.py a2)) (.int 2)
  let u2 := mulD (← mulS dl (.py a2)) sint2
  let g00 := negD (← divD (mulD (← mulS sg (.int 4)) (subD u1 u2)) denom)
  let g11 ← divD dl sg
  let g22 ← rdivS sg (.int 1)
  let n1 ← addS (mulD dl csct2) (.py (-a2))
  let num := mulD (mulD sg csct4) n1
  let w1 ← rsubS (mulD (← addS r2 (.py a2)) csct2) (.py a2)
  let den := mulD dl (← powS w1 (.int 2))
  let g33 ← divD num den
  let v1 ← rsubS dl (.py a2)
  let v2 := addD v1 r2
  let v3 ← mulS v2 (.py (4 * a))
  let g03 := negD (← divD (mulD v3 sg) denom)
  pure #[#[.dual g00, z0, z0, .dual g03], #[z0, .dual g11, z0, z0], #[z0, z0, .dual g22, z0],
    #[.dual g03, z0, z0, .dual g33]]

def dualMetric : Kind → Metric
  | .sch => dualSch
  | .kerr => dualKerr
  | .kerrnewman => dualKerrNewman

/-! ## Vectors and products with the NumPy dtype rules -/

/-- A length 4 array with its dtype: `obj = true` for `dtype=object`, `false` for `float64`. -/
structure Vec where
  d : Array Float
  obj : Bool
  deriving Inhabited

def Vec.get (v : Vec) (i : Nat) : Float := v.d[i]!

/-- BLAS dot of four numbers (Accelerate, checked by the difftest). -/
def dotBlas (a b : Array Float) : Float :=
  (a[0]! * b[0]! + a[2]! * b[2]!) + (a[1]! * b[1]! + a[3]! * b[3]!)

/-- A Python level dot product of four numbers: the sum starts from the integer `0`. -/
def dotObj (a b : Array Float) : Float :=
  (((0.0 + a[0]! * b[0]!) + a[1]! * b[1]!) + a[2]! * b[2]!) + a[3]! * b[3]!

/-- Row `i` of a row-major 4 x 4 array. -/
def row4 (m : Array Float) (i : Nat) : Array Float := #[m[4 * i]!, m[4 * i + 1]!, m[4 * i + 2]!, m[4 * i + 3]!]

/-- `m @ v` for a `float64` matrix and a vector: BLAS when `v` is `float64`, Python otherwise. -/
def matVec (m : Array Float) (v : Vec) : Array Float :=
  (List.range 4).toArray.map fun i => if v.obj then dotObj (row4 m i) v.d else dotBlas (row4 m i) v.d

/-- `g(q) @ v`: the metric array has dtype `object`. -/
def matVecObj (m : Array Float) (v : Array Float) : Array Float :=
  (List.range 4).toArray.map fun i => dotObj (row4 m i) v

/-- `vec @ p`, a dot product of two vectors: BLAS only if `p` is `float64`. -/
def dotVec (u : Array Float) (p : Vec) : Float := if p.obj then dotObj u p.d else dotBlas u p.d

/-- `x + delta * dx` and the like: element wise, the result is an `object` array if either is. -/
def Vec.zipWith (f : Float → Float → Float) (u v : Vec) : Vec :=
  ⟨(List.range 4).toArray.map fun i => f (u.d[i]!) (v.d[i]!), u.obj || v.obj⟩

/-! ## Integrator utilities (`integrators/utils.py`) -/

/-- utils.py:`_PartHamFlow`: `_jacobian_g(g, g_prms, q, wrt) @ p @ p`. -/
def partHamFlow (k : Kind) (prm : List Float) (q p : Vec) (wrt : Nat) : Except Exc Float := do
  let j ← jacobianG (dualMetric k) prm q.d.toList (.int (wrt : Int))
  let jp := matVec j p
  pure (dotVec jp p)

/-- `np.array([0.5 * _PartHamFlow(...) for i in range(4)])` as a `float64` array. -/
def dH (k : Kind) (prm : List Float) (q p : Vec) : Except Exc (Array Float) := do
  let mut out : Array Float := #[]
  for i in List.range 4 do
    out := out.push (0.5 * (← partHamFlow k prm q p i))
  pure out

/-- utils.py:`_flow_A(g, g_prms, q1, p1, q2, p2, delta)`, returns `(q2_next, p1_next)`. -/
def flowA (k : Kind) (prm : List Float) (q1 p1 q2 p2 : Vec) (delta : Float) : Except Exc (Vec × Vec) := do
  let dp1 ← dH k prm q1 p2
  let p1n : Vec := ⟨(List.range 4).toArray.map fun i => p1.d[i]! - delta * dp1[i]!, p1.obj⟩
  let gm ← realMetric k prm q1.d
  let dq2 := matVecObj gm p2.d
  let q2n : Vec := ⟨(List.range 4).toArray.map fun i => q2.d[i]! + delta * dq2[i]!, true⟩
  pure (q2n, p1n)

/-- utils.py:`_flow_B`, returns `(q1_next, p2_next)`. -/
def flowB (k : Kind) (prm : List Float) (q1 p1 q2 p2 : Vec) (delta : Float) : Except Exc (Vec × Vec) := do
  let dp2 ← dH k prm q2 p1
  let p2n : Vec := ⟨(List.range 4).toArray.map fun i => p2.d[i]! - delta * dp2[i]!, p2.obj⟩
  let gm ← realMetric k prm q2.d
  let dq1 := matVecObj gm p1.d
  let q1n : Vec := ⟨(List.range 4).toArray.map fun i => q1.d[i]! + delta * dq1[i]!, true⟩
  pure (q1n, p2n)

/-- utils.py:`_flow_mixed(q1, p1, q2, p2, delta, omega)`. -/
def flowMixed (q1 p1 q2 p2 : Vec) (delta omega : Float) : Array Vec :=
  let c := Float.cos (2.0 * omega * delta)
  let s := Float.sin (2.0 * omega * delta)
  let ob := q1.obj || p1.obj || q2.obj || p2.obj
  let mk (f : Nat → Float) : Vec := ⟨(List.range 4).toArray.map f, ob⟩
  let qs i := q1.d[i]! + q2.d[i]!
  let qd i := q1.d[i]! - q2.d[i]!
  let ps i := p1.d[i]! + p2.d[i]!
  let pd i := p1.d[i]! - p2.d[i]!
  #[mk fun i => 0.5 * ((qs i + qd i * c) + pd i * s),
    mk fun i => 0.5 * ((ps i + pd i * c) - qd i * s),
    mk fun i => 0.5 * ((qs i - qd i * c) - pd i * s),
    mk fun i => 0.5 * ((ps i - pd i * c) + qd i * s)]

/-- utils.py:`_Z(order)`: the Yoshida triple jump constants `(Z0, Z1)`. -/
def zConst (order : Float) : Except Exc (Float × Float) := do
  let n := (order - 2) / 2
  let e ← fdiv 1 (2 * n + 1)
  let x ← powReal 2 e
  let z0 ← fdiv (-x) (2 - x)
  let z1 ← fdiv 1 (2 - x)
  pure (z0, z1)

/-! ## The integrator (`integrators/fantasy.py`) -/

structure Cfg where
  kind : Kind
  prm : List Float
  /-- `self.order`, which `_Z` reads. -/
  order : Float
  omega : Float
  deriving Inhabited

/-- `np.array([a, b, c, d])` of four vectors: one dtype for all rows. -/
def stack (a b c d : Vec) : Array Vec :=
  let ob := a.obj || b.obj || c.obj || d.obj
  #[⟨a.d, ob⟩, ⟨b.d, ob⟩, ⟨c.d, ob⟩, ⟨d.d, ob⟩]

/-- fantasy.py:154-190 `_ord_2`. -/
def ord2 (c : Cfg) (q1 p1 q2 p2 : Vec) (dl : Float) : Except Exc (Array Vec) := do
  let (qa, pa) ← flowA c.kind c.prm q1 p1 q2 p2 (0.5 * dl)
  let ha1 := stack q1 pa qa p2
  let (qb, pb) ← flowB c.kind c.prm ha1[0]! ha1[1]! ha1[2]! ha1[3]! (0.5 * dl)
  let hb1 := stack qb ha1[1]! ha1[2]! pb
  let hc := flowMixed hb1[0]! hb1[1]! hb1[2]! hb1[3]! dl c.omega
  let (qb2, pb2) ← flowB c.kind c.prm hc[0]! hc[1]! hc[2]! hc[3]! (0.5 * dl)
  let hb2 := stack qb2 hc[1]! hc[2]! pb2
  let (qa2, pa2) ← flowA c.kind c.prm hb2[0]! hb2[1]! hb2[2]! hb2[3]! (0.5 * dl)
  pure (stack hb2[0]! pa2 qa2 hb2[3]!)

/-- Compose three steps of the next lower scheme: `step1 = f(dl*Z1)`, `step2 = f(dl*Z0)`,
`step3 = f(dl*Z1)`. -/
def triple (zOrder : Float) (f : Vec → Vec → Vec → Vec → Float → Except Exc (Array Vec))
    (q1 p1 q2 p2 : Vec) (dl : Float) : Except Exc (Array Vec) := do
  let (z0, z1) ← zConst zOrder
  let s1 ← f q1 p1 q2 p2 (dl * z1)
  let s2 ← f s1[0]! s1[1]! s1[2]! s1[3]! (dl * z0)
  f s2[0]! s2[1]! s2[2]! s2[3]! (dl * z1)

/-- `_ord_4`, `_ord_6`, `_ord_8` of fantasy.py (lines 192 to 260): `n` is the order of the method, and
`zOrder` the argument of `_Z`. The Python code always passes `self.order`, see `ordSelf`. -/
def ordN (c : Cfg) (zOrder : Nat → Float) : Nat → Vec → Vec → Vec → Vec → Float → Except Exc (Array Vec)
  | 0 => ord2 c
  | n + 1 => triple (zOrder (n + 1)) (ordN c zOrder n)

/-- `_ord_{2k}` of the integrator `c` exactly as einsteinpy has it: every level reads `_Z(self.order)`. -/
def ordSelf (c : Cfg) (n : Nat) : Vec → Vec → Vec → Vec → Float → Except Exc (Array Vec) :=
  ordN c (fun _ => c.order) n

/-- What `_ord_{2k}` should be if each level read `_Z` of its own order `2k`. -/
def ordFixed (c : Cfg) (n : Nat) : Vec → Vec → Vec → Vec → Float → Except Exc (Array Vec) :=
  ordN c (fun k => 2 * (Float.ofNat k) + 2) n

/-- fantasy.py:123-129 `ORDERS`: `order in ORDERS` for a number. -/
def orderIndex (order : Float) : Option Nat :=
  if order == 2 then some 0 else if order == 4 then some 1 else if order == 6 then some 2
  else if order == 8 then some 3 else none

/-- `np.allclose(x, const, rtol=rtol, atol=atol)` for a scalar `x` and an integer `const`. -/
def allclose (x const rtol atol : Float) : Bool :=
  x.isFinite && ((x - const).abs ≤ atol + rtol * const.abs)

structure RunResult where
  /-- `results`: for each step the four rows (q1, p1, q2, p2). -/
  rows : Array (Array Vec)
  /-- step numbers at which the numerical error warning was issued. -/
  warned : Array Nat

/-- fantasy.py:262-290 `step`, `steps` times, starting from `res_list = [q0, p0, q0, p0]`. -/
def runSteps (c : Cfg) (timeLike : Bool) (steps : Nat) (delta rtol atol : Float) (suppress : Bool)
    (q0 p0 : Array Float) : GR RunResult := do
  let some oi := orderIndex c.order | throw .notImplemented
  let mut rl : Array Vec := #[⟨q0, false⟩, ⟨p0, false⟩, ⟨q0, false⟩, ⟨p0, false⟩]
  let mut rows : Array (Array Vec) := #[]
  let mut warned : Array Nat := #[]
  for i in List.range steps do
    let arr ← lift (ordSelf c oi rl[0]! rl[1]! rl[2]! rl[3]! delta)
    rl := arr
    if !suppress then
      let gm ← lift (realMetric c.kind c.prm arr[0]!.d)
      let gp := matVecObj gm arr[1]!.d
      let val := dotObj gp arr[1]!.d
      let const : Float := if timeLike then -1 else 0
      if !allclose val const rtol atol then warned := warned.push (i + 1)
    rows := rows.push rl
  pure ⟨rows, warned⟩

/-! ## `_P` and the `Geodesic` constructor -/

/-- geodesic/utils.py:15-58 `_P`: the 4-momentum from the 3-momentum `p`. `q` is a `float64` array. -/
def pNorm (k : Kind) (prm : List Float) (q : Array Float) (p : List Float) (timeLike : Bool) :
    Except Exc (Array Float) := do
  let g ← realMetric k prm q
  let P : Array Float := (0.0 :: p).toArray
  if P.size < 4 then throw .indexError
  let A := g[0]!
  let B := (2.0 * g[3]!) * P[3]!
  let C := ((((g[5]! * P[1]!) * P[1]! + (g[10]! * P[2]!) * P[2]!) + (g[15]! * P[3]!) * P[3]!)
    + (if timeLike then 1.0 else 0.0))
  let P0 := (-B + Float.sqrt (sq B - (4.0 * A) * C)) / (2.0 * A)
  pure (P.set! 0 P0)

/-- The kinds of `Geodesic.__init__`'s `metric` string. -/
def kindOfName : String → Option Kind
  | "Schwarzschild" => some .sch
  | "Kerr" => some .kerr
  | "KerrNewman" => some .kerrnewman
  | _ => none

structure GeodesicOut where
  momentum : Array Float
  /-- `(N, 8)` rows `(q, p)` in Cartesian or spherical form. -/
  traj : Array (Array Float)
  warned : Array Nat

/-- geodesic.py:100-330 `Geodesic.__init__` and `calculate_trajectory` with `kwargs` already
defaulted. `steps` is `kwargs.get("steps", 50)`. -/
def geodesic (name : String) (prm : List Float) (position momentum : List Float) (timeLike cart : Bool)
    (steps : Int) (delta rtol atol : Float) (order omega : Float) (sw : Bool) : GR GeodesicOut := do
  let some k := kindOfName name | throw .notImplemented
  let q0 := (0.0 :: position).toArray
  let P ← lift (pNorm k prm q0 momentum timeLike)
  let n : Nat := steps.toNat
  let c : Cfg := ⟨k, prm, order, omega⟩
  let r ← runSteps c timeLike n delta rtol atol sw q0 P
  if n == 0 then throw (.exc .indexError)
  let traj := r.rows.map fun rs =>
    let q := rs[0]!.d
    let p := rs[1]!.d
    if cart then
      let st := q[1]! * Float.sin q[2]!
      #[q[0]!, st * Float.cos q[3]!, st * Float.sin q[3]!, q[1]! * Float.cos q[2]!, p[0]!, p[1]!, p[2]!, p[3]!]
    else #[q[0]!, q[1]!, q[2]!, q[3]!, p[0]!, p[1]!, p[2]!, p[3]!]
  pure ⟨P, traj, r.warned⟩

/-! ## `RK4naive` and `RK45` (`integrators/runge_kutta.py`) -/

/-- runge_kutta.py:37 `self.direction = 1 * (t_bound >= t0) - 1 * (not t_bound < t0)`. -/
def rkDirection (t0 tb : Float) : Int :=
  (if tb ≥ t0 then 1 else 0) - (if !(tb < t0) then 1 else 0)

/-- The out of bounds guard of `RK4naive.step`: `(t >= t_bound and direction == 1) or
(t <= t_bound and direction == -1)`. -/
def rkGuard (t tb : Float) (dir : Int) : Bool :=
  (t ≥ tb && dir == 1) || (t ≤ tb && dir == -1)

/-- Right hand sides used by the difftest. -/
inductive Rhs where
  | exp | osc | poly | lorenz | const
  deriving Repr, BEq, Inhabited

def Rhs.eval : Rhs → Float → Array Float → Array Float
  | .exp, _, y => #[y[0]!]
  | .osc, _, y => #[y[1]!, -y[0]!]
  | .poly, t, y => #[t - y[0]! * y[0]!]
  | .lorenz, _, y => #[10.0 * (y[1]! - y[0]!), y[0]! * (28.0 - y[2]!) - y[1]!, y[0]! * y[1]! - (8.0 / 3.0) * y[2]!]
  | .const, _, _ => #[1.0]

/-- runge_kutta.py:39-60 `RK4naive.step`: the new `(t, y)` and whether the warning fired. -/
def rk4Step (f : Float → Array Float → Array Float) (h tb : Float) (dir : Int) (t : Float) (y : Array Float) :
    Float × Array Float × Bool :=
  if rkGuard t tb dir then (t, y, true)
  else
    let k0 := f t y
    let ax (a : Array Float) (s : Float) : Array Float := (List.range y.size).toArray.map fun i => y[i]! + s * a[i]!
    let k1 := f (t + h / 2.0) (ax k0 (h / 2.0))
    let k2 := f (t + h / 2.0) (ax k1 (h / 2.0))
    let k3 := f (t + h) (ax k2 h)
    let ny := (List.range y.size).toArray.map fun i =>
      y[i]! + ((h / 6.0) * (((k0[i]! + 2.0 * k1[i]!) + 2.0 * k2[i]!) + k3[i]!))
    (t + h, ny, false)

/-- runge_kutta.py:84-100 the arguments that `RK45.__init__` hands to `scipy.integrate.RK45`:
`(rtol, atol, first_step, max_step)`. -/
def rk45Args (h : Float) (rtol atol : Option Float) : Float × Float × Float × Float :=
  let rt := match rtol with | some r => r | none => 0.2 * h
  let atl := match atol with | some a => a | none => rt / 0.8e3
  (rt, atl, 0.8 * h, 8.0 * h)

end EinsteinpyLean.Geodesic
