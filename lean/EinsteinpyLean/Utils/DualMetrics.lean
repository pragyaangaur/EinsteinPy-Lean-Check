import EinsteinpyLean.Utils.Dual

/-!
# Test metrics for `_diff_g` and `_jacobian_g`

`_diff_g` takes a contravariant metric function that works on `DualNumber` coordinates. These are
the metric functions the difftest uses. `difftest/utils_dual_diff.py` has the same functions written
with the real `DualNumber`, using the same operators in the same order, so that every reflected
operator (`float / dual`, `int - dual`, `float * dual`) is exercised. Zero entries are plain
numbers, as in a metric written as a numpy object array.
-/

namespace EinsteinpyLean.Utils.Py

private def z : Elem := .flt 0

/-- Inverse Schwarzschild metric in `(t, r, θ, φ)`, parameter `M` in geometric units. -/
def schw : Metric := fun q prm => do
  let m := prm[0]!
  let r := q[1]!
  let th := q[2]!
  let t2 ← rdivS r (.py (2 * m))
  let f ← rsubS t2 (.int 1)
  let gtt ← rdivS f (.int (-1))
  let r2 ← powS r (.int 2)
  let gthth ← rdivS r2 (.int 1)
  let s := sinD th
  let s2 ← powS s (.int 2)
  let gpp ← rdivS (mulD r2 s2) (.int 1)
  pure #[#[.dual gtt, z, z, z], #[z, .dual f, z, z], #[z, z, .dual gthth, z], #[z, z, z, .dual gpp]]

/-- Inverse Kerr metric in Boyer-Lindquist coordinates, parameters `a` and `M`. -/
def kerr : Metric := fun q prm => do
  let a := prm[0]!
  let m := prm[1]!
  let r := q[1]!
  let th := q[2]!
  let c := cosD th
  let s := sinD th
  let a2 ← powReal a 2
  let r2 ← powS r (.int 2)
  let c2 ← powS c (.int 2)
  let s2 ← powS s (.int 2)
  let sig := addD r2 (← mulS c2 (.py a2))
  let delta ← addS (subD r2 (← mulS r (.py (2 * m)))) (.py a2)
  let big ← powS (← addS r2 (.py a2)) (.int 2)
  let t ← mulS delta (.py a2)
  let gtt ← divD (negD (subD big (mulD t s2))) (mulD sig delta)
  let k := (-2 * m) * a
  let gtp ← divD (← mulS r (.py k)) (mulD sig delta)
  let grr ← divD delta sig
  let gthth ← rdivS sig (.int 1)
  let gpp ← divD (subD delta (← mulS s2 (.py a2))) (mulD (mulD sig delta) s2)
  pure #[#[.dual gtt, z, z, .dual gtp], #[z, .dual grr, z, z], #[z, z, .dual gthth, z],
    #[.dual gtp, z, z, .dual gpp]]

/-- A non-symmetric polynomial metric: `g[i][j] = q[i] * (j + 1) + q[j] ** 2 * (i - 1)`. -/
def poly : Metric := fun q _ => do
  let mut rows : Array (Array Elem) := #[]
  for i in List.range 4 do
    let mut row : Array Elem := #[]
    for j in List.range 4 do
      let a ← mulS q[i]! (.int ((j : Int) + 1))
      let b ← mulS (← powS q[j]! (.int 2)) (.int ((i : Int) - 1))
      row := row.push (.dual (addD a b))
    rows := rows.push row
  pure rows

/-- Every entry is `q[0] * s`. With `s = 1e308` the Jacobian diagonal overflows. -/
def scaled : Metric := fun q prm => do
  let s := prm[0]!
  let mut rows : Array (Array Elem) := #[]
  for _ in List.range 4 do
    let mut row : Array Elem := #[]
    for _ in List.range 4 do
      row := row.push (.dual (← mulS q[0]! (.py s)))
    rows := rows.push row
  pure rows

/-- A constant metric of plain numbers: floats on the diagonal, ints elsewhere. -/
def const : Metric := fun _ _ => do
  let mut rows : Array (Array Elem) := #[]
  for i in List.range 4 do
    let mut row : Array Elem := #[]
    for j in List.range 4 do
      row := row.push (if i == j then .flt (if i == 0 then -1 else 1) else .int 0)
    rows := rows.push row
  pure rows

def metricByName : String → Option Metric
  | "schw" => some schw
  | "kerr" => some kerr
  | "poly" => some poly
  | "scaled" => some scaled
  | "const" => some const
  | _ => none

end EinsteinpyLean.Utils.Py
