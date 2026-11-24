import EinsteinpyLean.Utils.Dual

/-!
# Model of `einsteinpy.rays.shadow` and `einsteinpy.hypersurface.schwarzschildembedding`

Mirrors `rays/shadow.py` and `hypersurface/schwarzschildembedding.py` at commit `63e1c54`. Core Lean only.
Only einsteinpy's own formulas are modelled. The root finder (`scipy.optimize.newton`), the quadrature
(`scipy.integrate.fixed_quad`) and the interpolation belong to scipy.

NumPy decides how a power is computed, and the model follows it:

* `array ** 2` is `x * x`, `array ** 0.5` is `sqrt`, `array ** (-1)` is `1 / x` and `array ** 3` is `pow`;
* `scalar ** 2`, `scalar ** 3` and `scalar ** 0.5` are all `pow`.

The integrands of `Shadow` are called by `fixed_quad` with an array of nodes and a scalar `b`, so they use the
array rules for `r` and the scalar rules for `b`. The embedding functions are called with a scalar `r` and a
`numpy.float64` mass, so they use the scalar rules.
-/

namespace EinsteinpyLean.Geodesic

open EinsteinpyLean.Utils
open EinsteinpyLean.Utils.Py

/-! ## `Shadow` -/

/-- rays/shadow.py:17 `self.b_crit = 3 * np.sqrt(3) * self.mass`, the value. -/
def bCrit (m : Float) : Float := (3 * Float.sqrt 3) * m

/-- rays/shadow.py:16 `self.horizon = 2 * self.mass.value`. -/
def horizon (m : Float) : Float := 2 * m

/-- `np.linspace(start, stop, num)` for two floats with `endpoint=True` (numpy 2.5). -/
def linspace (start stop : Float) (num : Int) : Except Exc (Array Float) := do
  if num < 0 then throw (.valueError "Number of samples must be non-negative.")
  let n := num.toNat
  let div : Int := num - 1
  let delta := stop - start
  let ys : Array Float :=
    if div > 0 then
      let dv := Float.ofInt div
      let step := delta / dv
      (List.range n).toArray.map fun i =>
        let yi := Float.ofNat i
        (if step == 0 then (yi / dv) * delta else yi * step) + start
    else (List.range n).toArray.map fun i => Float.ofNat i * delta + start
  if num > 1 then pure (ys.set! (n - 1) stop) else pure ys

/-- rays/shadow.py:55-64 and 66-76 `_intensity_blue_sch` and `_intensity_red_sch` for one node `r`,
given the mass value `m` and the impact parameter `b`. `blue` selects the sign of the Doppler term. -/
def intensity (blue : Bool) (m b r : Float) : Float :=
  let gtt := 1 - (2 * m) / r
  let grr := 1 / gtt
  let krk := Float.sqrt ((gtt / grr) * (1 - ((Float.pow b 2 * gtt) / (r * r))))
  let term := (krk * (grr / gtt)) * Float.sqrt ((1 - gtt) / (gtt * grr))
  let g := 1 / (if blue then 1 / gtt - term else 1 / gtt + term)
  let g3 := Float.pow g 3
  if blue then ((-g3) * (gtt / (r * r))) * (1 / krk) else (g3 * (gtt / (r * r))) * (1 / krk)

/-- Python `int(x)` of a float: `ValueError` for `nan`, `OverflowError` for infinities. -/
def pyInt (x : Float) : Except Exc Float :=
  if x.isNaN then throw (.valueError "cannot convert float NaN to integer")
  else if x.isInf then throw .overflow
  else pure (if x < 0 then x.ceil else x.floor)

/-- A real or complex answer of `_root_equation`. -/
inductive Num where
  | re (x : Float)
  | cx (re im : Float)

/-- rays/shadow.py:46-51 `_root_equation(r_tp, i)`:
`r_tp / np.emath.sqrt(1 - 2 * int(mass) / r_tp) - i`, with a `numpy.float64` `r_tp`.
A negative radicand makes `np.emath.sqrt` return a complex number, `0 + sqrt(-x) j`, and the quotient is
NumPy's complex division (Smith's algorithm). -/
def rootEq (m r i : Float) : Except Exc Num := do
  let k ← pyInt m
  -- the integer `2 * int(m)` becomes a float in the division, and `OverflowError` if it is too large
  if (2 * k).isInf then throw .overflow
  let x := 1 - (2 * k) / r
  if x < 0 then
    let s := Float.sqrt (-x)
    -- complex division (r + 0j) / (0 + s j); |0| < |s| so the second branch of Smith's algorithm
    let rat := 0 / s
    let scl := 1 / (s + 0 * rat)
    let re := (r * rat + 0) * scl
    let im := (0 * rat - r) * scl
    pure (.cx (re - i) im)
  else pure (.re (r / Float.sqrt x - i))

/-! ## `SchwarzschildEmbedding` -/

/-- hypersurface/schwarzschildembedding.py:40 `self.M.value`: `M.to(1e23 kg).value`, a multiplication by
`1 / 1e23`. -/
def embMass (mKg : Float) : Float := mKg * (1 / 1e23)

/-- schwarzschildembedding.py:41-43 `self.r_init.value`: `(((3 M + 0.0001) / M) * u.m).to(u.m / M)`. -/
def embRInit (m : Float) : Float := ((3 * m + 0.0001) / m) * (1 / (1 / m))

/-- schwarzschildembedding.py:94-109 `radial_coord`: `r / sqrt(1 - 2 M / r)`. -/
def radialCoord (m r : Float) : Float := r / Float.sqrt (1 - (2 * m) / r)

/-- schwarzschildembedding.py:70-92 `gradient`. -/
def gradient (m r : Float) : Float :=
  let R := r / Float.sqrt (1 - (2 * m) / r)
  let numOne := 1 - (3 * m) / r
  let numTwo := Float.sqrt ((((4 * m) * r - (9 * m) * m) * R) / Float.pow (r - 3 * m) 2)
  let deno := Float.pow (Float.sqrt (1 - (2 * m) / r)) 3
  (numOne * numTwo) / deno

/-- schwarzschildembedding.py:111-148 `get_values(alpha)`: `(x_axis, y_axis)`. -/
def getValues (m alpha : Float) : Array Float × Array Float := Id.run do
  let rInit := embRInit m
  let rStep := m / alpha
  let mut xs : Array Float := #[]
  let mut ys : Array Float := #[]
  let mut z : Float := 0
  let mut r := rInit
  let mut fuel := 100000
  while r < 9 * m && fuel > 0 do
    xs := xs.push (radialCoord m r)
    ys := ys.push z
    z := z + gradient m r * rStep
    r := r + rStep
    fuel := fuel - 1
  z := 0
  r := rInit
  while r > (9 * m) / 4 && fuel > 0 do
    xs := xs.push (radialCoord m r)
    ys := ys.push z
    z := z + gradient m r * rStep
    r := r - rStep
    fuel := fuel - 1
  pure (xs, ys)

end EinsteinpyLean.Geodesic
