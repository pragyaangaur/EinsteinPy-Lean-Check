import EinsteinpyLean.Metric.Linalg

/-!
# Model of `metric/base_metric.py`, `schwarzschild.py`, `kerr.py` and `kerrnewman.py`

Mirrors the sources under `src/einsteinpy/metric/` at commit `63e1c54`, with `Float` arithmetic in the order
that NumPy evaluates each expression, so that the difftests can compare the bit patterns. Core Lean only.

* Every `**` is `Float.pow`, which calls libm `pow`, as Python's float power and NumPy's scalar power do.
  On this machine `pow(x, 2)` is not always `x * x`, so the model never replaces one by the other.
* `sin`, `cos`, `tan`, `sqrt` are libm, and they agree with NumPy on this machine (checked on 200000 points).
* Positions and parameters are NumPy `float64` scalars (`x_vec[1]`, `Quantity.value`), so overflow gives `inf`
  and division by zero gives `inf` or `nan` without an exception. The static helpers `alpha`, `sigma`,
  `delta`, `rho` can also be called with plain Python floats. Then `x ** 2` raises `OverflowError` when the
  result is out of range, and the flag `py` selects that behaviour.
* `np.linalg.inv`, `@`: see `Linalg.lean`.
* A coordinate object is only its `system` string, so the model is the dispatch on that string.
-/

namespace EinsteinpyLean.Metric

open EinsteinpyLean.Utils

/-! ## Errors -/

/-- The exceptions the metric code can raise. -/
inductive Err where
  /-- `ValueError` with the message of base_metric.py:239. -/
  | value (msg : String)
  /-- `CoordinateError` (utils/exceptions.py:39). -/
  | coordinate
  /-- `numpy.linalg.LinAlgError("Singular matrix")` from `np.linalg.inv`. -/
  | linalg
  /-- `OverflowError` from Python's float power. -/
  | overflow
  /-- `TypeError`: a missing unit, or calling `None`. -/
  | type
  /-- `astropy.units.UnitsError` from `u.quantity_input`. -/
  | units
  deriving Repr, BEq

def Err.tag : Err → String
  | .value m => "ValueError:" ++ m
  | .coordinate => "CoordinateError"
  | .linalg => "LinAlgError"
  | .overflow => "OverflowError"
  | .type => "TypeError"
  | .units => "UnitsError"

abbrev R := Except Err

/-! ## Constants -/

/-- `_c`, `_G`, `_Cc` of base_metric.py:24-26. -/
def cC : Float := speedOfLight
def gG : Float := gravConst
def cc : Float := coulombsConst

/-- `_c**2`, Python float power. -/
def cSq : Float := Float.pow cC 2
/-- `_c**4`. -/
def cQ4 : Float := Float.pow cC 4
/-- kerrnewman.py:11 `_m_per_C_geom = np.sqrt(_G * _Cc) / _c**2`. -/
def mPerC : Float := Float.sqrt (gG * cc) / cSq
/-- kerrnewman.py:12 `_kg_per_C_geom = np.sqrt(_Cc / _G)`. -/
def kgPerC : Float := Float.sqrt (cc / gG)

/-- `x ** e` with a plain Python float `x` (flag `py`) or a NumPy scalar. Python raises `OverflowError` when a
finite float overflows. In `sigma` and `delta` only the arguments `r` and `Q` can be Python floats: every other
quantity involves `_G`, `_c` or `_Cc`, which are `numpy.float64` (constant.py gives `numpy` scalars). -/
def pw (py : Bool) (x e : Float) : R Float :=
  let y := Float.pow x e
  if py && x.isFinite && y.isInf then throw .overflow else pure y

/-- A pure power on NumPy scalars. -/
def p2 (x : Float) : Float := Float.pow x 2

/-! ## The static helpers of `BaseMetric` -/

/-- base_metric.py:193-209 `schwarzschild_radius`: `2 * _G * M / _c**2`. -/
def schRad (M : Float) : Float := 2.0 * gG * M / cSq

/-- base_metric.py:225-243 `alpha`. -/
def alphaOf (M a : Float) : R Float :=
  if a < 0.0 || a > 1.0 then throw (.value "Spin Parameter, a, should be between 0 and 1.")
  else pure (a * (gG * M / cSq))

/-- base_metric.py:93-117 `sigma`: `r**2 + (alpha * cos(theta))**2`. -/
def sigma (py : Bool) (r th M a : Float) : R Float := do
  let al ← alphaOf M a
  let r2 ← pw py r 2.0
  pure (r2 + p2 (al * Float.cos th))

/-- base_metric.py:119-155 `delta`: `r**2 - r_s*r + alpha**2 + r_Q2`. -/
def delta (py : Bool) (r M a Q : Float) : R Float := do
  let rs := 2.0 * M * gG / cSq
  let al ← alphaOf M a
  let q2 ← pw py Q 2.0
  let rQ2 := q2 * gG * cc / cQ4
  let r2 ← pw py r 2.0
  let a2 := p2 al -- `alpha` is a NumPy scalar even for Python inputs, because `_G` is a `numpy.float64`
  pure (r2 - rs * r + a2 + rQ2)

/-- base_metric.py:157-190 `rho`: `np.sqrt(sigma)`. -/
def rho (py : Bool) (r th M a : Float) : R Float := do
  pure (Float.sqrt (← sigma py r th M a))

/-! ## Bodies and coordinate systems -/

inductive Sys where
  | spherical | bl | cartesian
  deriving BEq, Repr

inductive Cls where
  | schw | kerr | kn
  deriving BEq, Repr

/-- A metric object: its class, the coordinate system and the numbers `M.value`, `a.value`, `Q.value`,
`q.value`. -/
structure Body where
  cls : Cls
  sys : Sys
  M : Float
  a : Float
  Q : Float
  q : Float

/-- The name that `__init__` stores (`name="Kerr Metric"` and so on). -/
def Cls.name : Cls → String
  | .schw => "Schwarzschild Metric"
  | .kerr => "Kerr Metric"
  | .kn => "Kerr-Newman Metric"

/-! ## Schwarzschild (schwarzschild.py) -/

/-- schwarzschild.py:63-81 `_g_cov_s`. -/
def schwG (M r th : Float) : Arr :=
  let rs := schRad M
  let tmp := 1.0 - rs / r
  let g := zeros 16
  let g := g.set2 0 0 (tmp * cSq)
  let g := g.set2 1 1 (-1.0 / tmp)
  let g := g.set2 2 2 (-(Float.pow r 2.0))
  g.set2 3 3 (-(Float.pow (r * Float.sin th) 2.0))

/-- schwarzschild.py:115-139 `_ch_sym_s`. -/
def schwCh (M r th : Float) : Arr :=
  let rs := schRad M
  let c := zeros 64
  let c := c.set3 1 0 0 (0.5 * rs * (r - rs) * cSq / Float.pow r 3.0)
  let c111 := 0.5 * rs / (rs * r - Float.pow r 2.0)
  let c := c.set3 1 1 1 c111
  let c := c.set3 1 2 2 (rs - r)
  let c := c.set3 1 3 3 ((rs - r) * Float.pow (Float.sin th) 2.0)
  let c := c.set3 0 0 1 (-c111)
  let c := c.set3 0 1 0 (-c111)
  let o := 1.0 / r
  let c := c.set3 2 2 1 o
  let c := c.set3 2 1 2 o
  let c := c.set3 3 3 1 o
  let c := c.set3 3 1 3 o
  let c := c.set3 2 3 3 (-Float.cos th * Float.sin th)
  let t := 1.0 / Float.tan th
  let c := c.set3 3 3 2 t
  c.set3 3 2 3 t

/-- schwarzschild.py:178-224 `_f_vec_s`, from the Christoffel symbols and the vector. -/
def schwF (chl : Arr) (v : Array Float) : Array Float :=
  let v4 := v[4]!; let v5 := v[5]!; let v6 := v[6]!; let v7 := v[7]!
  let vals := v
  let vals := vals.set! 0 v4 |>.set! 1 v5 |>.set! 2 v6 |>.set! 3 v7
  let vals := vals.set! 4 (-2.0 * chl.at3 0 0 1 * v4 * v5)
  let vals := vals.set! 5 (-1.0 * (chl.at3 1 0 0 * Float.pow v4 2.0 + chl.at3 1 1 1 * Float.pow v5 2.0
      + chl.at3 1 2 2 * Float.pow v6 2.0 + chl.at3 1 3 3 * Float.pow v7 2.0))
  let vals := vals.set! 6 (-2.0 * chl.at3 2 2 1 * v6 * v5 - 1.0 * chl.at3 2 3 3 * Float.pow v7 2.0)
  vals.set! 7 (-2.0 * (chl.at3 3 3 1 * v7 * v5 + chl.at3 3 3 2 * v7 * v6))

/-! ## Kerr (kerr.py) -/

/-- kerr.py:101-130 `_g_cov_bl`. -/
def kerrG (M a r th : Float) : R Arr := do
  let rs := schRad M
  let al ← alphaOf M a
  let sg ← sigma false r th M a
  let dl ← delta false r M a 0.0
  let s := Float.sin th
  let g := zeros 16
  let g := g.set2 0 0 ((1.0 - (rs * r / sg)) * cSq)
  let g := g.set2 1 1 (-(sg / dl))
  let g := g.set2 2 2 (-sg)
  let g := g.set2 3 3 (-(((Float.pow r 2.0 + Float.pow al 2.0 + ((rs * r * Float.pow (al * s) 2.0) / sg))
      * Float.pow s 2.0)))
  let x := (cC * rs * r * al * Float.pow s 2.0) / sg
  pure ((g.set2 0 3 x).set2 3 0 x)

/-- kerr.py:132-190 `_dg_dx_bl`. -/
def kerrDg (M a r th : Float) : R Arr := do
  let rs := schRad M
  let al ← alphaOf M a
  let sg ← sigma false r th M a
  let dl ← delta false r M a 0.0
  let s := Float.sin th
  let mut dg := zeros 64
  -- due_to_r
  let dsdr := 2.0 * r
  let dddr := 2.0 * r - rs
  let tmp := rs * (sg - r * dsdr) / Float.pow sg 2.0
  dg := dg.set3 1 0 0 (-tmp * cSq)
  dg := dg.set3 1 1 1 (-(dsdr - (sg * (dddr / dl))) / dl)
  dg := dg.set3 1 2 2 (-dsdr)
  dg := dg.set3 1 3 3 ((-2.0 * r + Float.pow (al * s) 2.0 * tmp) * Float.pow s 2.0)
  let x := cC * al * Float.pow s 2.0 * tmp
  dg := (dg.set3 1 0 3 x).set3 1 3 0 x
  -- due_to_theta
  let dsdth := -(Float.pow al 2.0) * Float.sin (2.0 * th)
  let tmp2 := Float.pow (cC / sg) 2.0 * rs * r * dsdth
  dg := dg.set3 2 0 0 tmp2
  dg := dg.set3 2 1 1 (-(dsdth / dl))
  dg := dg.set3 2 2 2 (-dsdth)
  dg := dg.set3 2 3 3 (-Float.sin (2.0 * th) * (Float.pow r 2.0 + Float.pow al 2.0)
    - (rs * r * Float.pow al 2.0) * Float.pow (s / sg) 2.0
      * (2.0 * sg * Float.sin (2.0 * th) - Float.pow s 2.0 * dsdth))
  let y := ((cC * al * rs * r) / Float.pow sg 2.0) * (sg * Float.sin (2.0 * th) - dsdth * Float.pow s 2.0)
  dg := (dg.set3 2 0 3 y).set3 2 3 0 y
  pure dg

/-! ## Kerr-Newman (kerrnewman.py) -/

/-- kerrnewman.py:146-181 `_g_cov_bl`. `Q` is the charge in coulombs. -/
def knG (M a Q r th : Float) : R Arr := do
  let al ← alphaOf M a
  let rho2 := Float.pow (← rho false r th M a) 2.0
  let dl ← delta false r M a Q
  let s := Float.sin th
  let g := zeros 16
  let g := g.set2 0 0 (cSq * ((dl - Float.pow (al * s) 2.0) / rho2))
  let g := g.set2 1 1 (-rho2 / dl)
  let g := g.set2 2 2 (-rho2)
  let g := g.set2 3 3 (-(Float.pow s 2.0
    * ((Float.pow (Float.pow r 2.0 + Float.pow al 2.0) 2.0 - dl * Float.pow (al * s) 2.0) / rho2)))
  let x := cC * ((-al * Float.pow s 2.0 * (dl - Float.pow r 2.0 - Float.pow al 2.0)) / rho2)
  pure ((g.set2 0 3 x).set2 3 0 x)

/-- kerrnewman.py:183-282 `_dg_dx_bl`. -/
def knDg (M a Q r th : Float) : R Arr := do
  let al ← alphaOf M a
  let rho2 := Float.pow (← rho false r th M a) 2.0
  let dl ← delta false r M a Q
  let s := Float.sin th
  let mut dg := zeros 64
  -- due_to_r
  let drh2dr := 2.0 * r
  let dddr := 2.0 * r - schRad M
  dg := dg.set3 1 0 0 (cSq * (dddr * rho2 - drh2dr * (dl - Float.pow (al * s) 2.0)) / Float.pow rho2 2.0)
  dg := dg.set3 1 1 1 ((-1.0 / Float.pow dl 2.0) * (drh2dr * dl - dddr * rho2))
  dg := dg.set3 1 2 2 (-drh2dr)
  dg := dg.set3 1 3 3 (Float.pow (s / rho2) 2.0 *
    (((Float.pow (al * s) 2.0 * dddr - 4.0 * Float.pow r 3.0 - 4.0 * (r * Float.pow al 2.0)) * rho2)
      - (drh2dr * (Float.pow (al * s) 2.0 * dl - Float.pow (Float.pow r 2.0 + Float.pow al 2.0) 2.0))))
  let x := (cC * (-al) * Float.pow s 2.0 / Float.pow rho2 2.0)
    * ((dddr - 2.0 * r) * rho2 - drh2dr * (dl - Float.pow r 2.0 - Float.pow al 2.0))
  dg := (dg.set3 1 0 3 x).set3 1 3 0 x
  -- due_to_theta
  let drh2dth := -(Float.pow al 2.0) * Float.sin (2.0 * th)
  dg := dg.set3 2 0 0 ((-(Float.pow (cC / rho2) 2.0)) *
    ((drh2dth * (dl - Float.pow (al * s) 2.0)) + (Float.pow al 2.0 * rho2 * Float.sin (2.0 * th))))
  dg := dg.set3 2 1 1 (-drh2dth / dl)
  dg := dg.set3 2 2 2 (-drh2dth)
  dg := dg.set3 2 3 3 ((1.0 / Float.pow rho2 2.0) *
    ((dl * Float.pow (al * s) 2.0) * (2.0 * rho2 * Float.sin (2.0 * th) - drh2dth * Float.pow s 2.0)
      - (Float.pow (Float.pow r 2.0 + Float.pow al 2.0) 2.0
          * (rho2 * Float.sin (2.0 * th) - drh2dth * Float.pow s 2.0))))
  let y := ((-al * cC * (dl - Float.pow r 2.0 - Float.pow al 2.0)) / Float.pow rho2 2.0)
    * ((Float.sin (2.0 * th) * rho2) - (drh2dth * Float.pow s 2.0))
  dg := (dg.set3 2 0 3 y).set3 2 3 0 y
  pure dg

/-! ## Christoffel symbols of Kerr and Kerr-Newman (identical code in both files) -/

/-- kerr.py:48-81 and kerrnewman.py:60-93, the precomputed list of nonzero index triples. -/
def nonzeroList : List (Nat × Nat × Nat) :=
  [(0, 0, 1), (0, 0, 2), (0, 1, 3), (0, 2, 3), (0, 1, 0), (0, 2, 0), (0, 3, 1), (0, 3, 2),
   (1, 0, 0), (1, 1, 1), (1, 2, 2), (1, 3, 3), (2, 0, 0), (2, 1, 1), (2, 2, 2), (2, 3, 3),
   (1, 0, 3), (1, 1, 2), (2, 0, 3), (2, 1, 2), (1, 2, 1), (1, 3, 0), (2, 2, 1), (2, 3, 0),
   (3, 0, 1), (3, 0, 2), (3, 1, 0), (3, 1, 3), (3, 2, 0), (3, 2, 3), (3, 3, 1), (3, 3, 2)]

/-- kerr.py:240-264 `_ch_sym_bl` after `metric_contravariant` and `_dg_dx_bl` have been computed. -/
def chFrom (gi dg : Arr) : Arr := Id.run do
  let mut chl := zeros 64
  for (_, k, l) in (nonzeroList.drop 0).take 4 do
    let val1 := dg.at3 l 0 k + dg.at3 k 0 l
    let val2 := dg.at3 l 3 k + dg.at3 k 3 l
    let x := 0.5 * (gi.at2 0 0 * val1 + gi.at2 0 3 * val2)
    chl := (chl.set3 0 k l x).set3 0 l k x
    let y := 0.5 * (gi.at2 3 0 * val1 + gi.at2 3 3 * val2)
    chl := (chl.set3 3 k l y).set3 3 l k y
  for (i, k, l) in (nonzeroList.drop 8).take 8 do
    chl := chl.set3 i k l (0.5 * (gi.at2 i i * (dg.at3 l i k + dg.at3 k i l - dg.at3 i k l)))
  for (i, k, l) in (nonzeroList.drop 16).take 4 do
    let x := 0.5 * (gi.at2 i i * (dg.at3 l i k + dg.at3 k i l - dg.at3 i k l))
    chl := (chl.set3 i k l x).set3 i l k x
  return chl

/-- kerr.py:266-342 `_f_vec_bl`, from the Christoffel symbols and the vector. -/
def kerrF (chl : Arr) (v : Array Float) : Array Float :=
  let v4 := v[4]!; let v5 := v[5]!; let v6 := v[6]!; let v7 := v[7]!
  let vals := ((((v.set! 0 v4).set! 1 v5).set! 2 v6).set! 3 v7)
  let vals := vals.set! 4 (-2.0 * (chl.at3 0 0 1 * v4 * v5 + chl.at3 0 0 2 * v4 * v6
      + chl.at3 0 1 3 * v5 * v7 + chl.at3 0 2 3 * v6 * v7))
  let vals := vals.set! 5 (-1.0 * (chl.at3 1 0 0 * v4 * v4 + 2.0 * chl.at3 1 0 3 * v4 * v7
      + chl.at3 1 1 1 * v5 * v5 + 2.0 * chl.at3 1 1 2 * v5 * v6 + chl.at3 1 2 2 * v6 * v6
      + chl.at3 1 3 3 * v7 * v7))
  let vals := vals.set! 6 (-1.0 * (chl.at3 2 0 0 * v4 * v4 + 2.0 * chl.at3 2 0 3 * v4 * v7
      + chl.at3 2 1 1 * v5 * v5 + 2.0 * chl.at3 2 1 2 * v5 * v6 + chl.at3 2 2 2 * v6 * v6
      + chl.at3 2 3 3 * v7 * v7))
  vals.set! 7 (-2.0 * (chl.at3 3 0 1 * v4 * v5 + chl.at3 3 0 2 * v4 * v6
      + chl.at3 3 1 3 * v5 * v7 + chl.at3 3 2 3 * v6 * v7))

/-- kerr.py:344-390 `nonzero_christoffels`: the index triples found by propagating the sparsity pattern of the
inverse metric and of its derivatives. -/
def nonzeroComputed : List (Nat × Nat × Nat) := Id.run do
  let mut gc : Array Bool := Array.replicate 16 false
  let mut dg : Array Bool := Array.replicate 64 false
  let gi2 (i j : Nat) := i * 4 + j
  let d3 (i j k : Nat) := i * 16 + j * 4 + k
  gc := (gc.set! (gi2 3 0) true).set! (gi2 0 3) true
  dg := ((dg.set! (d3 1 3 0) true).set! (d3 1 0 3) true)
  dg := ((dg.set! (d3 2 0 3) true).set! (d3 2 3 0) true)
  gc := (((gc.set! (gi2 0 0) true).set! (gi2 1 1) true).set! (gi2 2 2) true).set! (gi2 3 3) true
  dg := (((dg.set! (d3 1 0 0) true).set! (d3 1 1 1) true).set! (d3 1 2 2) true).set! (d3 1 3 3) true
  dg := (((dg.set! (d3 2 0 0) true).set! (d3 2 1 1) true).set! (d3 2 2 2) true).set! (d3 2 3 3) true
  let mut vcl : List (Nat × Nat × Nat) := []
  for t in [0:64] do
    let i := (t / 16) % 4
    let j := (t / 4) % 4
    let k := t % 4
    let mut hit := false
    for idx in [0:4] do
      if gc[gi2 i idx]! && (dg[d3 k idx j]! || dg[d3 j idx k]! || dg[d3 idx j k]!) then hit := true
    if hit then vcl := vcl ++ [(i, j, k)]
  return vcl

/-! ## Dispatch on the class and the coordinate system -/

/-- `metric_covariant(x_vec)` of the three classes, with the `CoordinateError` of each. -/
def metricCov (b : Body) (r th : Float) : R Arr :=
  match b.cls with
  | .schw => if b.sys == .spherical then pure (schwG b.M r th) else throw .coordinate
  | .kerr => if b.sys == .bl then kerrG b.M b.a r th else throw .coordinate
  | .kn => if b.sys == .bl then knG b.M b.a b.Q r th else throw .coordinate

/-- `BaseMetric.metric_contravariant` without a perturbation: `np.linalg.inv`. -/
def metricContra (b : Body) (r th : Float) : R Arr := do
  let g ← metricCov b r th
  match inv4 g with
  | some gi => pure gi
  | none => throw .linalg

/-- `christoffels(x_vec)` of the three classes. -/
def christoffels (b : Body) (r th : Float) : R Arr :=
  match b.cls with
  | .schw => if b.sys == .spherical then pure (schwCh b.M r th) else throw .coordinate
  | .kerr => if b.sys == .bl then do
      let gi ← metricContra b r th
      let dg ← kerrDg b.M b.a r th
      pure (chFrom gi dg)
    else throw .coordinate
  | .kn => if b.sys == .bl then do
      let gi ← metricContra b r th
      let dg ← knDg b.M b.a b.Q r th
      pure (chFrom gi dg)
    else throw .coordinate

/-! ## Kerr-Newman electromagnetism -/

/-- kerrnewman.py:424-431 `geometrized_charge`. -/
def geomCharge (Q : Float) : Float := Q * mPerC

/-- kerrnewman.py:376-402 `em_potential_covariant`. No coordinate check. -/
def emPotCov (b : Body) (r th : Float) : R (Array Float) := do
  let al ← alphaOf b.M b.a
  let rQ := geomCharge b.Q
  let rho2 := Float.pow (← rho false r th b.M b.a) 2.0
  let A := zeros 4
  let A := A.set! 0 (r * rQ / rho2)
  pure (A.set! 3 (-r * al * rQ * Float.pow (Float.sin th) 2.0 / rho2))

/-- kerrnewman.py:433-454 `em_potential_contravariant`. -/
def emPotContra (b : Body) (r th : Float) : R (Array Float) := do
  let A ← emPotCov b r th
  let gi ← metricContra b r th
  pure (matvec4 gi A)

/-- kerrnewman.py:456-496 `em_tensor_covariant`. No coordinate check. -/
def emTensorCov (b : Body) (r th : Float) : R Arr := do
  let al ← alphaOf b.M b.a
  let rQ := geomCharge b.Q
  let rho2 := Float.pow (← rho false r th b.M b.a) 2.0
  let drho2dr := 2.0 * r
  let drho2dth := -(Float.pow al 2.0 * Float.sin (2.0 * th))
  let s := Float.sin th
  let f := zeros 16
  let f01 := -(rQ * (rho2 - drho2dr * r)) / Float.pow rho2 2.0
  let f := (f.set2 0 1 f01).set2 1 0 (-f01)
  let f02 := (r * rQ * drho2dth) / Float.pow rho2 2.0
  let f := (f.set2 0 2 f02).set2 2 0 (-f02)
  let f13 := -(1.0 / Float.pow rho2 2.0) * (al * rQ * Float.pow s 2.0) * (rho2 - 2.0 * Float.pow r 2.0)
  let f := (f.set2 1 3 f13).set2 3 1 (-f13)
  let f23 := -((1.0 / Float.pow rho2 2.0) * (al * rQ * r * Float.sin (2.0 * th))
    * (rho2 + Float.pow (al * s) 2.0))
  pure ((f.set2 2 3 f23).set2 3 2 (-f23))

/-- kerrnewman.py:498-520 `em_tensor_contravariant`: `g_contra @ F_cov @ g_contra`. -/
def emTensorContra (b : Body) (r th : Float) : R Arr := do
  let F ← emTensorCov b r th
  let gi ← metricContra b r th
  pure (matmul4 (matmul4 gi F) gi)

/-- kerrnewman.py:324-374 `_f_vec_bl` for Kerr-Newman. -/
def knF (b : Body) (v : Array Float) : R (Array Float) := do
  let r := v[1]!
  let th := v[2]!
  let chl ← christoffels b r th
  let gi ← metricContra b r th
  let F0 ← emTensorCov b r th
  let mut F := F0
  for j in [0:4] do
    F := F.set2 0 j (F.at2 0 j * cC)
  for i in [0:4] do
    F := F.set2 i 0 (F.at2 i 0 * cC)
  let k := cC * kgPerC
  F := F.map (· * k)
  let base := kerrF chl v
  let u : Array Float := #[v[4]!, v[5]!, v[6]!, v[7]!]
  let lor := matvec4 (matmul4 gi F) u
  let mut out := base
  for i in [0:4] do
    out := out.set! (4 + i) (out[4 + i]! + b.q * lor[i]!)
  pure out

/-! ## `singularities` (base_metric.py:245-315) -/

/-- A value of the dictionary: a Python `int` or a `float`. -/
inductive Sv where
  | int (n : Int)
  | flt (x : Float)

/-- The four entries `inner_ergosphere(θ)`, `inner_horizon`, `outer_horizon`, `outer_ergosphere(θ)`. `name` is
the stored name of the object. -/
def singularities (name : String) (sys : Sys) (M a Q th : Float) : R (List Sv) := do
  let rs := 2.0 * M * gG / cSq
  let al ← alphaOf M a
  let rQ2 := Float.pow Q 2.0 * gG * cc / cQ4
  let disc := Float.pow rs 2.0 - 4.0 * Float.pow (al * Float.cos th) 2.0 - 4.0 * rQ2
  let inErgo := (rs - Float.sqrt disc) / 2.0
  let outErgo := (rs + Float.sqrt disc) / 2.0
  if name == "Kerr Metric" || name == "Kerr-Newman Metric" then
    if sys == .bl then
      let d2 := Float.pow rs 2.0 - 4.0 * Float.pow al 2.0 - 4.0 * rQ2
      pure [.flt inErgo, .flt ((rs - Float.sqrt d2) / 2.0), .flt ((rs + Float.sqrt d2) / 2.0), .flt outErgo]
    else throw .coordinate
  else if sys == .spherical then
    pure [.int 0, .int 0, .flt rs, .flt rs]
  else throw .coordinate

/-- Units, as far as `u.quantity_input` cares: the dimension class of a unit name. -/
inductive UDim where
  | mass | time | charge | dimless | angle | chargePerMass
  deriving BEq

def unitDim : String → Option UDim
  | "kg" | "g" | "Msun" => some .mass
  | "s" => some .time
  | "C" | "mC" => some .charge
  | "one" | "percent" => some .dimless
  | "rad" => some .angle
  | "Ckg" | "mCkg" => some .chargePerMass
  | _ => none

/-- `u.quantity_input` accepts a plain number when the target unit is dimensionless, and raises `TypeError`
otherwise. -/
def checkSpec (s : Option UDim × Float) (want : UDim) : R Float :=
  match s.1 with
  | none => if want == .dimless then pure s.2 else throw .type
  | some d => if d == want then pure s.2 else throw .units

/-- The constructors (schwarzschild.py:22-33, kerr.py:21-44, kerrnewman.py:36-69): `u.quantity_input` checks the units
of `M`, `a`, `Q`, `q` in signature order, and `__init__` stores `sch_rad = schwarzschild_radius(M)` from the raw
`.value` of the mass. The decorator checks the unit and does not convert it. -/
def ctorRad (cls : Cls) (ms as qs qq : Option UDim × Float) : R Float := do
  let M ← checkSpec ms .mass
  match cls with
  | .schw => pure (schRad M)
  | .kerr => do let _ ← checkSpec as .dimless; pure (schRad M)
  | .kn => do
      let _ ← checkSpec as .dimless
      let _ ← checkSpec qs .charge
      let _ ← checkSpec qq .chargePerMass
      pure (schRad M)

/-- base_metric.py:303-310 and 311-315: the two `CoordinateError` messages of `singularities`. The source writes the
sentence as two adjacent string literals, with no space between them. -/
def singKerrMsg : String := "Singularities for Kerr solutions are only available in" ++ "Boyer-Lindquist Coordinates."
def singSchwMsg : String := "Singularities for Schwarzschild Metric are only available in" ++ "Spherical Polar Coordinates."

end EinsteinpyLean.Metric
