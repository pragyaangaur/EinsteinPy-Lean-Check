import EinsteinpyLean.Common.Arr

/-!
# Model of `einsteinpy.symbolic.predefined` and `einsteinpy.symbolic.constants`

Mirrors the component formulas of every predefined metric at commit `63e1c54`, on exact
rationals. All line references are to files under `src/einsteinpy/symbolic/`.

How the symbols are handled in the difftest (see `difftest/predefined_metrics_diff.py`):

- Rational symbols (`c`, `G`, `eps_0`, `sch`, `a`, `Q`, `r`, `k`, `M`, `B`, `omega`...) are
  replaced by random rationals in the real einsteinpy metric.
- `sin(theta)` and `cos(theta)` are replaced by two given rationals `s` and `co` with
  `s^2 + co^2 = 1` (a Pythagorean pair). The same is done for `cos(t)` (AntiDeSitter) and
  for `sinh`, `cosh` (a hyperbolic Pythagorean pair).
- Other transcendental values are passed as extra rational inputs and substituted for the
  function call in the real metric: `exp(...)` in DeSitter, BertottiKasner, Godel and
  BesselGravitationalWave, `tanh(...)` in AlcubierreWarp, `besselj(0, rho)` and
  `besselj(1, rho)`, `pi` in KerrNewman and ReissnerNordstorm, and the fractional powers in
  Davidson (given as `t^(1/3)` and `(1+r^2)^(1/5)`).
- Every division by zero is one error, `zeroDiv`. In sympy the same case gives `zoo` or
  `nan` (a zero numerator does not help: `0 * zoo` is `nan`), which the test maps to the
  same class.
-/

namespace EinsteinpyLean.Predefined
open Arr

/-- Errors, one constructor per way a formula can fail. -/
inductive Err where
  /-- A denominator is zero. sympy returns `zoo` or `nan` for the component. -/
  | zeroDiv
  deriving Repr, BEq, DecidableEq

def Err.tag : Err → String
  | .zeroDiv => "zerodiv"

abbrev M := Except Err

/-- `a / b`, failing when `b = 0` (sympy: `zoo`). -/
def dv (a b : Rat) : M Rat := if b == 0 then .error .zeroDiv else .ok (a / b)

/-- `b ** n` for a natural `n` (`0 ** 0 = 1`, as in sympy). -/
def npow (b : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => npow b n * b

/-- `b ** n` for an integer `n`; a negative power of zero is `zoo` in sympy. -/
def ipow (b : Rat) (n : Int) : M Rat :=
  if n ≥ 0 then .ok (npow b n.toNat) else dv 1 (npow b (-n).toNat)

/-- A 4 by 4 array from its 16 entries in row-major order. -/
def mat4 (l : List Rat) : Arr := ⟨[4, 4], l.toArray⟩

/-- `sympy.diag(a, b, c, d)`. -/
def diag4 (a b c d : Rat) : Arr :=
  mat4 [a, 0, 0, 0,  0, b, 0, 0,  0, 0, c, 0,  0, 0, 0, d]

/-- Set the entries `(i, j)` and `(j, i)`, like `metric[i][j] = metric[j][i] = v`. -/
def setSym (m : Arr) (i j : Nat) (v : Rat) : Arr :=
  ⟨m.shape, (m.data.set! (4 * i + j) v).set! (4 * j + i) v⟩

/-! ### minkowski.py -/

/-- minkowski.py:19 `MinkowskiCartesian(c)`, also the alias `Minkowski`. -/
def minkowskiCartesian (c : Rat) : M Arr := do
  let a ← dv 1 (c * c)
  return diag4 (-1) a a a

/-- minkowski.py:37-40 `MinkowskiPolar(c)` at the point `r`, with `s = sin theta`. -/
def minkowskiPolar (c r s : Rat) : M Arr := do
  let c2 := c * c
  return diag4 (-1) (← dv 1 c2) (← dv (r * r) c2) (← dv (r * r * (s * s)) c2)

/-! ### vacuum_solutions.py -/

/-- vacuum_solutions.py:22-28 `Schwarzschild(c, sch)`. Signature `(+, -, -, -)`. -/
def schwarzschild (c sch r s : Rat) : M Arr := do
  let val1 := 1 - (← dv sch r)
  let c2 := c * c
  return diag4 val1 (-(← dv 1 (val1 * c2))) (-(← dv (r * r) c2))
    (-(← dv ((r * s) * (r * s)) c2))

/-- vacuum_solutions.py:48-65 `Kerr(c, sch, a)`; `co = cos theta`. -/
def kerr (c sch a r s co : Rat) : M Arr := do
  let sigma := r * r + (a * a * (co * co))
  let delta := r * r - sch * r + a * a
  let c2 := c * c
  let g00 := 1 - (← dv (sch * r) sigma)
  let g11 := ← dv (-sigma) (delta * c2)
  let g22 := ← dv (-sigma) c2
  let inner := r * r + a * a + (← dv (sch * r * (a * a) * (s * s)) sigma)
  let g33 := ← dv (-(inner * (s * s))) c2
  let g03 := ← dv (sch * r * a * (s * s)) (sigma * c)
  return setSym (diag4 g00 g11 g22 g33) 0 3 g03

/-- `rQsq = Q^2 G / (4 pi eps_0 c^4)` (vacuum_solutions.py:102 and :149), with `pi` given. -/
def rQsq (c g eps0 q pi : Rat) : M Rat := dv (q * q * g) (4 * pi * eps0 * npow c 4)

/-- vacuum_solutions.py:99-115 `KerrNewman(c, G, eps_0, sch, a, Q)`. -/
def kerrNewman (c g eps0 sch a q pi r s co : Rat) : M Arr := do
  let sigma := r * r + (a * a * (co * co))
  let rq ← rQsq c g eps0 q pi
  let delta := r * r - sch * r + a * a + rq
  let c2 := c * c
  let g00 := 1 + (← dv (rq - sch * r) sigma)
  let g11 := ← dv (-sigma) (delta * c2)
  let g22 := ← dv (-sigma) c2
  let g33 := ← dv ((delta * (a * a) * (s * s) - (r * r + a * a) * (r * r + a * a)) * (s * s))
    (sigma * c2)
  let g03 := ← dv ((sch * r - rq) * a * (s * s)) (sigma * c)
  return setSym (diag4 g00 g11 g22 g33) 0 3 g03

/-- vacuum_solutions.py:147-156 `ReissnerNordstorm(c, G, eps_0, sch, Q)`. -/
def reissnerNordstrom (c g eps0 sch q pi r s : Rat) : M Arr := do
  let rq ← rQsq c g eps0 q pi
  let arn := 1 - (← dv sch r) + (← dv rq (r * r))
  let c2 := c * c
  return diag4 arn (-(← dv 1 (arn * c2))) (-(← dv (r * r) c2))
    (-(← dv (r * r * (s * s)) c2))

/-! ### de_sitter.py -/

/-- de_sitter.py:13-21 `AntiDeSitter`, given `ct = cos t`, `sh = sinh chi`, `s = sin theta`. -/
def antiDeSitter (ct sh s : Rat) : Arr :=
  diag4 (-1) (ct * ct) (ct * ct * (sh * sh)) (ct * ct * (sh * sh) * (s * s))

/-- de_sitter.py:31-34 `AntiDeSitterStatic`, given `ch = cosh r`, `sh = sinh r`. -/
def antiDeSitterStatic (ch sh s : Rat) : Arr :=
  diag4 (-(ch * ch)) 1 (sh * sh) (sh * sh * (s * s))

/-- de_sitter.py:44-48 `DeSitter`, given `e = exp(2 t / alpha)`. -/
def deSitter (e : Rat) : Arr := diag4 (-1) e e e

/-! ### alcubierre_warp.py -/

/-- alcubierre_warp.py:43-50 `AlcubierreWarp(x_s, sigma, R, v)`, given the three values
`t1 = tanh(sigma (r_s + R))`, `t2 = tanh(sigma (r_s - R))` and `t3 = tanh(sigma R)`. -/
def alcubierre (v t1 t2 t3 : Rat) : M Arr := do
  let f ← dv (t1 - t2) (2 * t3)
  let m := diag4 (v * v * (f * f) - 1) 1 1 1
  return setSym m 0 1 (-v * f)

/-! ### barriola_vilenkin.py, bertotti_kasner.py -/

/-- barriola_vilenkin.py:25-27 `BarriolaVilekin(c, k)`. -/
def barriolaVilenkin (c k r s : Rat) : M Arr := do
  let c2 := c * c
  return diag4 (-1) (← dv 1 c2) (← dv ((k * r) * (k * r)) c2)
    (← dv ((k * r * s) * (k * r * s)) c2)

/-- bertotti_kasner.py:24-29 `BertottiKasner(c, k, lambd)`; the argument `k` is unused.
`e = exp(2 sqrt(lambd) c t)`. -/
def bertottiKasner (c lambd e s : Rat) : M Arr := do
  let c2 := c * c
  return diag4 (-1) (← dv e c2) (← dv 1 (lambd * c2)) (← dv (s * s) (lambd * c2))

/-! ### bessel_gravitational_wave.py -/

/-- bessel_gravitational_wave.py:39-44. `eu = exp(U)` and `ek = exp(K)` are given, so
`exp(-2U) exp(2K) = ek^2 / eu^2`, `exp(-2U) = 1 / eu^2`, `exp(2U) = eu^2`. -/
def besselWave (rho eu ek : Rat) : M Arr := do
  let w ← dv (ek * ek) (eu * eu)
  return diag4 (-w) w (← dv (rho * rho) (eu * eu)) (eu * eu)

/-! ### cmetric.py, davidson.py, ernst.py, godel.py -/

/-- cmetric.py:15-20 `CMetric`, given `fv = f(x)` and `hv = h(y)`. -/
def cMetric (fv hv x y : Rat) : M Arr := do
  let s := (x + y) * (x + y)
  return diag4 (← dv (-hv) s) (← dv 1 (s * fv)) (← dv 1 (s * hv)) (← dv fv s)

/-- davidson.py:13-19 `Davidson`, given `t3 = t^(1/3)` and `w = (1 + r^2)^(1/5)`, so that
`expr = w^2`, `t^(4/3) = t3^4`, `t^(-2/3) = 1 / t3^2`. -/
def davidson (r t3 w : Rat) : M Arr := do
  let x := w * w
  return diag4 (-(x * x * x)) (npow t3 4 * x) (← dv 1 (t3 * t3 * x)) (← dv (npow t3 4 * (r * r)) x)

/-- ernst.py:24-33 `Ernst(B, M)`. -/
def ernst (b m r s : Rat) : M Arr := do
  let lam := 1 + ((b * r * s) * (b * r * s))
  let w := 1 - (← dv (2 * m) r)
  return diag4 (-1 * (lam * lam) * w) (← dv (lam * lam) w) ((r * lam) * (r * lam))
    ((← dv (r * s) lam) * (← dv (r * s) lam))

/-- godel.py:16-17 `Godel`, given `e = exp(sqrt 2 omega x)`. -/
def godel (e : Rat) : Arr :=
  setSym (diag4 (-1) 1 (-(1 / 2) * (e * e)) 1) 0 2 (-e)

/-! ### friedmann_lemaitre_robertson_walker.py, janis_newman_winicour.py, kerr_newman_desitter.py -/

/-- friedmann_lemaitre_robertson_walker.py:27-32, given `a = a(t)`. -/
def flrw (a k r s : Rat) : M Arr := do
  return diag4 (-1) (← dv (a * a) (1 - k * (r * r))) (a * a * (r * r)) (a * a * (r * r) * (s * s))

/-- janis_newman_winicour.py:26-35 `JanisNewmanWinicour(c, G, gam, M)` for an integer `gam`
(a non-integer exponent is not rational). -/
def jnw (c g : Rat) (gam : Int) (m r s : Rat) : M Arr := do
  let rs ← dv (2 * g * m) (c * c)
  let alpha := 1 - (← dv rs (gam * r))
  let a1 ← ipow alpha gam
  let a2 ← ipow alpha (-gam)
  let a3 ← ipow alpha (-gam + 1)
  return diag4 (-1 * a1) (← dv a2 (c * c)) (r * r * a3) (r * r * a3 * (s * s))

/-- kerr_newman_desitter.py:24-47 `KerrNewmanDeSitter()`; its symbols `a`, `Q`, `Lambda`
and `r` are all free. -/
def kerrNewmanDeSitter (a q lam0 r s co : Rat) : M Arr := do
  let lam := lam0 / 3
  let chi := 1 + lam * (a * a)
  let sigma := r * r + a * a * (co * co)
  let deltaR := (1 - lam * (r * r)) * (r * r + a * a) - 2 * r + q * q
  let deltaT := 1 + lam * (a * a) * (co * co)
  let den ← dv 1 (chi * chi * sigma)
  let gtt := (a * a * (s * s) * deltaT - deltaR) * den
  let grr ← dv sigma deltaR
  let gth ← dv sigma deltaT
  let gtp := a * (s * s) * (deltaR - (r * r + a * a) * deltaT) * den
  let gpp := (s * s) * ((r * r + a * a) * (r * r + a * a) * deltaT - a * a * (s * s) * deltaR) * den
  return setSym (diag4 gtt grr gth gpp) 0 3 gtp

/-! ### find.py -/

/-- `dir(einsteinpy.symbolic.predefined)` at the pinned commit (alphabetical, as Python
sorts it). Obtained by running `dir` on the installed package. -/
def moduleNames : List String :=
  ["AlcubierreWarp", "AntiDeSitter", "AntiDeSitterStatic", "BarriolaVilekin", "BertottiKasner",
   "BesselGravitationalWave", "CMetric", "Davidson", "DeSitter", "Ernst",
   "FriedmannLemaitreRobertsonWalker", "Godel", "JanisNewmanWinicour", "Kerr", "KerrNewman",
   "KerrNewmanDeSitter", "Minkowski", "MinkowskiCartesian", "MinkowskiPolar",
   "ReissnerNordstorm", "Schwarzschild", "__builtins__", "__doc__", "__file__", "__loader__",
   "__name__", "__package__", "__path__", "__spec__", "alcubierre_warp", "barriola_vilenkin",
   "bertotti_kasner", "bessel_gravitational_wave", "cmetric", "davidson", "de_sitter", "ernst",
   "find", "friedmann_lemaitre_robertson_walker", "godel", "janis_newman_winicour",
   "kerr_newman_desitter", "minkowski", "vacuum_solutions"]

/-- Python `str.islower` on ASCII: at least one cased character and no uppercase one. -/
def pyIsLower (s : String) : Bool :=
  s.toList.any Char.isLower && !s.toList.any Char.isUpper

/-- Substring test, Python `a in b`. -/
def pyIn (a b : String) : Bool := (b.splitOn a).length > 1

/-- find.py:19-25 `find`: names containing the lowercased search string that are not all
lowercase. ASCII only (`str.lower` and `String.toLower` differ on other scripts). -/
def find (search : String) : List String :=
  let q := search.toLower
  moduleNames.filter fun f => pyIn q f.toLower && !pyIsLower f

/-! ### constants.py -/

/-- constants.py:4-36 `SymbolicConstant`: sympy caches `Symbol.__new__` by name and
assumptions, so building `SymbolicConstant(name, d)` returns the existing object for that
name and then overwrites its `_descriptive_name` (constants.py:27). The model is the table
of live objects by name. -/
abbrev Table := List (String × Option String)

/-- constants.py:39-42, the four module level constants. -/
def initialTable : Table :=
  [("c", some "Speed Of Light"), ("G", some "Gravitational Constant"),
   ("Lambda", some "Cosmological Constant"), ("eps_0", some "Permittivity of free space")]

/-- `SymbolicConstant(name, d)`: set the descriptive name of the cached object. -/
def construct (t : Table) (name : String) (d : Option String) : Table :=
  if t.any (·.1 == name) then t.map fun e => if e.1 == name then (name, d) else e
  else t ++ [(name, d)]

/-- constants.py:61-62 `get_constant`: the dictionary key is the Python name, which is
`Cosmo_Const` for the symbol called `Lambda`. The result is the symbol name and its
current descriptive name. A key outside the four is a `KeyError`. -/
def getConstant (t : Table) (key : String) : Option (String × Option String) :=
  let sym? : Option String :=
    if key == "c" then some "c" else if key == "G" then some "G"
    else if key == "Cosmo_Const" then some "Lambda" else if key == "eps_0" then some "eps_0"
    else none
  sym?.bind fun n => (t.find? (·.1 == n)).map fun e => (n, e.2)

end EinsteinpyLean.Predefined
