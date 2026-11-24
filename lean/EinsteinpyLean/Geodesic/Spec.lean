import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import PhyslibAlpha.Relativity.General.Schwarzschild.IncompressibleSphere
import EinsteinpyLean.Geodesic.SpecIntegrator
import EinsteinpyLean.Geodesic.SpecRays

/-!
# The geodesic metric functions and the momentum normaliser over the reals

`geodesic/utils.py` writes the three contravariant metrics in `M`-units (`c = G = M = k_e = 1`), signature
`(-, +, +, +)`. This file restates them with Mathlib's `Real.sin` and `Real.cos` and proves that they are the
inverses of the covariant metrics of Schwarzschild, Kerr and Kerr-Newman in Boyer-Lindquist coordinates, and
that `_P` returns a normalised four-momentum for them (and does not for a general metric, which is issue 664
and pull request 690 of einsteinpy).

Physlib has no geodesic integrator, no symplectic map and no Kerr metric. The one neighbour is
`PhyslibAlpha`'s exterior Schwarzschild solution (`gttOut`, `grrOut` of Schwarzschild's incompressible
sphere, with `α = rs` the Schwarzschild radius): `schwarzschild_matches_physlib` shows that the code's
`g^{tt}` and `g^{rr}` are `1 / gttOut` (with a minus sign) and `1 / grrOut` when `rs = 2`, which is `M = 1`.
Division by zero is `0` in Lean, so the crashes of the code are not visible here; they are the subject of
`Model.lean` and `Props.lean`. The integrators are in `SpecIntegrator.lean` and the shadow and the embedding in
`SpecRays.lean`; this file imports both, so the target `EinsteinpyLean.Geodesic.Spec` builds all of the Spec layer.
-/

open Real

namespace EinsteinpyLean.Geodesic.Spec

/-! ## The components of geodesic/utils.py -/

/-- utils.py:61-83 `sigma`. -/
noncomputable def sigma (r th a : ℝ) : ℝ := r ^ 2 + (a * cos th) ^ 2

/-- utils.py:86-110 `delta` with `Q`. -/
noncomputable def delta (r a Q : ℝ) : ℝ := r ^ 2 - 2 * r + a ^ 2 + Q ^ 2

/-- `_sch` (utils.py:113-142): the diagonal `g^{tt}, g^{rr}, g^{θθ}, g^{φφ}`. -/
noncomputable def schG (r th : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (-1 / (1 - 2 / r), 1 - 2 / r, 1 / r ^ 2, 1 / (r * sin th) ^ 2)

/-- `_kerr` (utils.py:145-179): `g^{tt}, g^{rr}, g^{θθ}, g^{φφ}, g^{tφ}`. -/
noncomputable def kerrG (r th a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  let sg := sigma r th a
  let dl := delta r a 0
  (-(r ^ 2 + a ^ 2 + (2 * r * (a * sin th) ^ 2) / sg) / dl, dl / sg, 1 / sg,
    (1 / (dl * sin th ^ 2)) * (1 - 2 * r / sg), -(2 * r * a) / (sg * dl))

/-- `_kerrnewman` (utils.py:182-224). -/
noncomputable def kerrnewmanG (r th a Q : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  let sg := sigma r th a
  let dl := delta r a Q
  let a2 := a ^ 2
  let r2 := r ^ 2
  let sint2 := sin th ^ 2
  let csct2 := 1 / sint2
  let csct4 := 1 / sint2 ^ 2
  let denom := dl * (a2 + 2 * r2 + a2 * cos (2 * th)) ^ 2
  (-(4 * sg * ((a2 + r2) ^ 2 - a2 * dl * sint2) / denom), dl / sg, 1 / sg,
    (sg * csct4 * (-a2 + dl * csct2)) / (dl * (a2 - (a2 + r2) * csct2) ^ 2),
    -(4 * a * (a2 - dl + r2) * sg / denom))

/-! ## The covariant metrics, `M = 1` -/

/-- Covariant Kerr-Newman in Boyer-Lindquist coordinates (`M = 1`, `Σ = r² + a² cos² θ`,
`Δ = r² - 2 r + a² + Q²`): `(g_tt, g_rr, g_θθ, g_φφ, g_tφ)`. With `Q = 0` it is Kerr, with `a = Q = 0`
Schwarzschild. -/
noncomputable def covKN (r th a Q : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  let sg := sigma r th a
  let dl := delta r a Q
  (-(1 - (2 * r - Q ^ 2) / sg), sg / dl, sg,
    sin th ^ 2 * (r ^ 2 + a ^ 2 + a ^ 2 * sin th ^ 2 * (2 * r - Q ^ 2) / sg),
    -(a * sin th ^ 2 * (2 * r - Q ^ 2) / sg))

/-! ## Schwarzschild -/

/-- PROP geodesic.metric.schwarzschild_inverse : PROVEN
Source: utils.py:113-142 documents `_sch` as the contravariant Schwarzschild metric. Its product with the
covariant metric `diag(-(1 - 2/r), 1/(1 - 2/r), r², r² sin² θ)` is the identity (the `t t`, `r r`, `θ θ`
and `φ φ` entries), for `r ≠ 0`, `r ≠ 2` and `sin θ ≠ 0`. -/
theorem schwarzschild_inverse (r th : ℝ) (hr : r ≠ 0) (hr2 : r ≠ 2) (hs : sin th ≠ 0) :
    -(1 - 2 / r) * (schG r th).1 = 1 ∧ 1 / (1 - 2 / r) * (schG r th).2.1 = 1 ∧
      r ^ 2 * (schG r th).2.2.1 = 1 ∧ r ^ 2 * sin th ^ 2 * (schG r th).2.2.2 = 1 := by
  have h1 : 1 - 2 / r ≠ 0 := by
    intro h
    apply hr2
    field_simp at h
    linarith
  simp only [schG]
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · field_simp
  · field_simp

/-- PROP geodesic.metric.schwarzschild_physlib : PROVEN
Source: PhyslibAlpha `IncompressibleSphere.gttOut` and `grrOut`, the exterior Schwarzschild coefficients
`g_tt = 1 - α/r` and `g_rr = 1/(1 - α/r)`. With `α = 2` (`M = 1`) the code's `g^{tt}` is `-1 / g_tt` and
its `g^{rr}` is `1 / g_rr`: the code is the inverse of Physlib's exterior metric (signature `(-, +, +, +)`
here, `(+, -, ...)` there). -/
theorem schwarzschild_matches_physlib (S : GeneralRelativity.IncompressibleSphere) (hS : S.rs = 2)
    (r th : ℝ) :
    (schG r th).1 = -1 / S.gttOut r ∧ (schG r th).2.1 = 1 / S.grrOut r := by
  constructor
  · simp [schG, GeneralRelativity.IncompressibleSphere.gttOut, hS]
  · simp [schG, GeneralRelativity.IncompressibleSphere.grrOut, hS]

/-! ## Kerr and Kerr-Newman -/

/-- PROP geodesic.metric.kerr_inverse : PROVEN
Source: utils.py:145-179, "Contravariant Kerr Metric in Boyer-Lindquist coordinates". With
`Σ = r² + a² cos² θ`, `Δ = r² - 2r + a²` nonzero and `sin θ ≠ 0`, the code's components are the inverse of
the covariant Kerr metric: the `(t, φ)` block, `g^{rr} g_{rr} = 1` and `g^{θθ} g_{θθ} = 1`. -/
theorem kerr_inverse (r th a : ℝ) (hS : sigma r th a ≠ 0) (hD : delta r a 0 ≠ 0) (hs : sin th ≠ 0) :
    (covKN r th a 0).1 * (kerrG r th a).1 + (covKN r th a 0).2.2.2.2 * (kerrG r th a).2.2.2.2 = 1 ∧
    (covKN r th a 0).1 * (kerrG r th a).2.2.2.2 + (covKN r th a 0).2.2.2.2 * (kerrG r th a).2.2.2.1 = 0 ∧
    (covKN r th a 0).2.2.2.2 * (kerrG r th a).1 + (covKN r th a 0).2.2.2.1 * (kerrG r th a).2.2.2.2 = 0 ∧
    (covKN r th a 0).2.2.2.2 * (kerrG r th a).2.2.2.2 + (covKN r th a 0).2.2.2.1 * (kerrG r th a).2.2.2.1 = 1 ∧
    (covKN r th a 0).2.1 * (kerrG r th a).2.1 = 1 ∧ (covKN r th a 0).2.2.1 * (kerrG r th a).2.2.1 = 1 := by
  have hc : cos th ^ 2 = 1 - sin th ^ 2 := cos_sq' th
  simp only [sigma, delta, mul_pow, hc] at hS hD
  simp only [kerrG, covKN, sigma, delta, mul_pow, hc]
  generalize sin th = s at *
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, sub_zero] at *
  set D := r ^ 2 - 2 * r + a ^ 2 with hDdef
  set S := r ^ 2 + a ^ 2 * (1 - s ^ 2) with hSdef
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> simp only [hDdef, hSdef] <;> ring

/-- PROP geodesic.metric.kerrnewman_inverse : PROVEN
Source: utils.py:182-224, "Contravariant Kerr-Newman Metric in Boyer-Lindquist coordinates", with
`Δ = r² - 2r + a² + Q²`. The code writes `a² + 2r² + a² cos 2θ` (which is `2Σ`) and powers of `csc θ`; its
components are the inverse of the covariant Kerr-Newman metric (`(t, φ)` block, `rr`, `θθ`). -/
theorem kerrnewman_inverse (r th a Q : ℝ) (hS : sigma r th a ≠ 0) (hD : delta r a Q ≠ 0) (hs : sin th ≠ 0) :
    (covKN r th a Q).1 * (kerrnewmanG r th a Q).1 + (covKN r th a Q).2.2.2.2 * (kerrnewmanG r th a Q).2.2.2.2 = 1 ∧
    (covKN r th a Q).1 * (kerrnewmanG r th a Q).2.2.2.2 + (covKN r th a Q).2.2.2.2 * (kerrnewmanG r th a Q).2.2.2.1 = 0 ∧
    (covKN r th a Q).2.2.2.2 * (kerrnewmanG r th a Q).1 + (covKN r th a Q).2.2.2.1 * (kerrnewmanG r th a Q).2.2.2.2 = 0 ∧
    (covKN r th a Q).2.2.2.2 * (kerrnewmanG r th a Q).2.2.2.2 + (covKN r th a Q).2.2.2.1 * (kerrnewmanG r th a Q).2.2.2.1 = 1 ∧
    (covKN r th a Q).2.1 * (kerrnewmanG r th a Q).2.1 = 1 ∧
    (covKN r th a Q).2.2.1 * (kerrnewmanG r th a Q).2.2.1 = 1 := by
  have hc : cos th ^ 2 = 1 - sin th ^ 2 := cos_sq' th
  have h2 : cos (2 * th) = 2 * (1 - sin th ^ 2) - 1 := by rw [cos_two_mul, hc]
  simp only [sigma, delta, mul_pow, hc] at hS hD
  simp only [kerrnewmanG, covKN, sigma, delta, mul_pow, hc, h2]
  generalize sin th = s at *
  set D := r ^ 2 - 2 * r + a ^ 2 + Q ^ 2 with hDdef
  set S := r ^ 2 + a ^ 2 * (1 - s ^ 2) with hSdef
  have e1 : a ^ 2 + 2 * r ^ 2 + a ^ 2 * (2 * (1 - s ^ 2) - 1) = 2 * S := by simp only [hSdef]; ring
  have e2 : a ^ 2 - (a ^ 2 + r ^ 2) * (1 / s ^ 2) = -S / s ^ 2 := by
    simp only [hSdef]; field_simp; ring
  have e3 : (2 * S) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hS)
  have e4 : (-S / s ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (div_ne_zero (neg_ne_zero.mpr hS) (pow_ne_zero 2 hs))
  rw [e1, e2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> simp only [hDdef, hSdef] <;> ring

/-- PROP geodesic.metric.kerr_is_kerrnewman_q0 : PROVEN
Source: utils.py:145-224. The two functions are different code for the same tensor: `_kerr` and
`_kerrnewman` with `Q = 0` have the same components, for `Σ ≠ 0`, `Δ ≠ 0` and `sin θ ≠ 0` (the `tt`, `rr`,
`θθ`, `φφ` and `tφ` entries). -/
theorem kerr_is_kerrnewman_q0 (r th a : ℝ) (hS : sigma r th a ≠ 0) (hD : delta r a 0 ≠ 0) (hs : sin th ≠ 0) :
    kerrG r th a = kerrnewmanG r th a 0 := by
  have hc : cos th ^ 2 = 1 - sin th ^ 2 := cos_sq' th
  have h2 : cos (2 * th) = 2 * (1 - sin th ^ 2) - 1 := by rw [cos_two_mul, hc]
  simp only [sigma, delta, mul_pow, hc] at hS hD
  simp only [kerrG, kerrnewmanG, sigma, delta, mul_pow, hc, h2]
  generalize sin th = s at *
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at *
  set D := r ^ 2 - 2 * r + a ^ 2 with hDdef
  set S := r ^ 2 + a ^ 2 * (1 - s ^ 2) with hSdef
  have e1 : a ^ 2 + 2 * r ^ 2 + a ^ 2 * (2 * (1 - s ^ 2) - 1) = 2 * S := by simp only [hSdef]; ring
  have e2 : a ^ 2 - (a ^ 2 + r ^ 2) * (1 / s ^ 2) = -S / s ^ 2 := by
    simp only [hSdef]; field_simp; ring
  have e3 : (2 * S) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hS)
  have e4 : (-S / s ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (div_ne_zero (neg_ne_zero.mpr hS) (pow_ne_zero 2 hs))
  rw [e1, e2]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp only [] <;> field_simp <;>
    simp only [hDdef, hSdef] <;> ring

/-- PROP geodesic.metric.kerr_spin_zero : PROVEN
Source: utils.py:113-179. At `a = 0` the Kerr components are the Schwarzschild components (`tt`, `rr`, `θθ`,
`φφ`), and `g^{tφ} = 0`, for `r ≠ 0`, `r ≠ 2`, `sin θ ≠ 0`. -/
theorem kerr_a0_is_schwarzschild (r th : ℝ) (hr : r ≠ 0) (hr2 : r ≠ 2) (hs : sin th ≠ 0) :
    (kerrG r th 0).1 = (schG r th).1 ∧ (kerrG r th 0).2.1 = (schG r th).2.1 ∧
    (kerrG r th 0).2.2.1 = (schG r th).2.2.1 ∧ (kerrG r th 0).2.2.2.1 = (schG r th).2.2.2 ∧
    (kerrG r th 0).2.2.2.2 = 0 := by
  have h1 : 1 - 2 / r ≠ 0 := by
    intro h
    apply hr2
    field_simp at h
    linarith
  have h2 : r - 2 ≠ 0 := sub_ne_zero.mpr hr2
  simp only [kerrG, schG, sigma, delta]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-! ## The momentum normaliser `_P` -/

/-- A symmetric contravariant metric at a point, by its ten independent components. -/
structure SymG where
  g00 : ℝ
  g01 : ℝ
  g02 : ℝ
  g03 : ℝ
  g11 : ℝ
  g12 : ℝ
  g13 : ℝ
  g22 : ℝ
  g23 : ℝ
  g33 : ℝ

/-- `g^{μν} P_μ P_ν` for a covariant four-momentum `(p0, p1, p2, p3)`. -/
def SymG.quad (g : SymG) (p0 p1 p2 p3 : ℝ) : ℝ :=
  g.g00 * p0 ^ 2 + g.g11 * p1 ^ 2 + g.g22 * p2 ^ 2 + g.g33 * p3 ^ 2 +
    2 * (g.g01 * p0 * p1 + g.g02 * p0 * p2 + g.g03 * p0 * p3 + g.g12 * p1 * p2 + g.g13 * p1 * p3 +
      g.g23 * p2 * p3)

/-- The linear coefficient of the quadratic equation for `p0`, in general. -/
def SymG.B (g : SymG) (p1 p2 p3 : ℝ) : ℝ := 2 * (g.g01 * p1 + g.g02 * p2 + g.g03 * p3)

/-- The constant coefficient: `g^{ij} p_i p_j + ε` over the spatial indices, `ε = 1` time-like, `0` null. -/
def SymG.C (g : SymG) (p1 p2 p3 ε : ℝ) : ℝ :=
  g.g11 * p1 ^ 2 + g.g22 * p2 ^ 2 + g.g33 * p3 ^ 2 +
    2 * (g.g12 * p1 * p2 + g.g13 * p1 * p3 + g.g23 * p2 * p3) + ε

/-- The root `(-B + sqrt (B² - 4AC)) / (2A)` that `_P` assigns to `P_0` (utils.py:55). -/
noncomputable def pRoot (A B C : ℝ) : ℝ := (-B + √(B ^ 2 - 4 * A * C)) / (2 * A)

/-- PROP geodesic.P.quadratic_form : PROVEN
Source: utils.py:15-58. The normalisation `g^{μν} P_μ P_ν = -ε` is the quadratic equation
`A p0² + B p0 + C = 0` with `A = g^{00}`, `B = 2 Σ_i g^{0i} p_i` and `C = Σ g^{ij} p_i p_j + ε`. -/
theorem quad_eq (g : SymG) (p0 p1 p2 p3 ε : ℝ) :
    g.quad p0 p1 p2 p3 + ε = g.g00 * p0 ^ 2 + g.B p1 p2 p3 * p0 + g.C p1 p2 p3 ε := by
  simp only [SymG.quad, SymG.B, SymG.C]
  ring

/-- The root of a quadratic with a nonnegative discriminant solves it. -/
theorem pRoot_solves (A B C : ℝ) (hA : A ≠ 0) (hd : 0 ≤ B ^ 2 - 4 * A * C) :
    A * pRoot A B C ^ 2 + B * pRoot A B C + C = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, t = √(B ^ 2 - 4 * A * C) := ⟨_, rfl⟩
  have hs : t ^ 2 = B ^ 2 - 4 * A * C := by rw [ht]; exact Real.sq_sqrt hd
  unfold pRoot
  rw [← ht]
  have key : A * ((-B + t) / (2 * A)) ^ 2 + B * ((-B + t) / (2 * A)) + C
      = (t ^ 2 - (B ^ 2 - 4 * A * C)) / (4 * A) := by
    field_simp
    ring
  rw [key, hs]
  simp

/-- PROP geodesic.P.pr690_normalises : PROVEN
Source: pull request 690 of einsteinpy (fixes issue 664), which sets `B = 2 Σ_i g^{0i} p_i` and
`C = Σ_{ij} g^{ij} p_i p_j + ε` (with `np.sum` over the blocks). For every symmetric contravariant metric with
`g^{00} ≠ 0` and a nonnegative discriminant, the returned `P_0` gives `g^{μν} P_μ P_ν = -ε`. -/
theorem P690_normalises (g : SymG) (p1 p2 p3 ε : ℝ) (hA : g.g00 ≠ 0)
    (hd : 0 ≤ (g.B p1 p2 p3) ^ 2 - 4 * g.g00 * g.C p1 p2 p3 ε) :
    g.quad (pRoot g.g00 (g.B p1 p2 p3) (g.C p1 p2 p3 ε)) p1 p2 p3 = -ε := by
  have h := quad_eq g (pRoot g.g00 (g.B p1 p2 p3) (g.C p1 p2 p3 ε)) p1 p2 p3 ε
  have h2 := pRoot_solves g.g00 (g.B p1 p2 p3) (g.C p1 p2 p3 ε) hA hd
  linarith

/-- The coefficients that the pinned `_P` uses: `B = 2 g^{03} p_3` and
`C = g^{11} p_1² + g^{22} p_2² + g^{33} p_3² + ε`. -/
def SymG.Bcode (g : SymG) (_p1 _p2 p3 : ℝ) : ℝ := 2 * g.g03 * p3
def SymG.Ccode (g : SymG) (p1 p2 p3 ε : ℝ) : ℝ := g.g11 * p1 ^ 2 + g.g22 * p2 ^ 2 + g.g33 * p3 ^ 2 + ε

/-- PROP geodesic.P.code_normalises_kerr_like : PROVEN
Source: utils.py:41-55. For a metric whose only off-diagonal component is `g^{03}` (Schwarzschild, Kerr and
Kerr-Newman, the three metrics that `Geodesic` knows) the pinned `_P` computes the same `B` and `C` as the
general formula, so it normalises correctly. -/
theorem code_matches_general_for_kerr_like (g : SymG)
    (h01 : g.g01 = 0) (h02 : g.g02 = 0) (h12 : g.g12 = 0) (h13 : g.g13 = 0) (h23 : g.g23 = 0)
    (p1 p2 p3 ε : ℝ) :
    g.Bcode p1 p2 p3 = g.B p1 p2 p3 ∧ g.Ccode p1 p2 p3 ε = g.C p1 p2 p3 ε := by
  simp only [SymG.Bcode, SymG.B, SymG.Ccode, SymG.C, h01, h02, h12, h13, h23]
  constructor <;> ring

/-- A flat metric with one cross term `g^{01} = 1/2`. -/
noncomputable def crossMetric : SymG := ⟨-1, 1 / 2, 0, 0, 1, 0, 0, 1, 0, 1⟩

/-- PROP geodesic.P.code_normalises_general : REFUTED
Source: utils.py:41-55 and the docstring "Utility function to compute 4-Momentum of the test particle", used
by `Geodesic` for any user-supplied callable metric. With `g^{01} = 1/2` (otherwise flat, `p = (1, 0, 0)`,
time-like) the root that the pinned code computes does not satisfy `g^{μν} P_μ P_ν = -1`: the left side is
`-1 - √2`. This is issue 664 of einsteinpy (open) and pull request 690 (open) fixes it; it is stated here
so that `P690_normalises` has the failing case next to it. -/
theorem code_not_normalising_general :
    crossMetric.quad (pRoot crossMetric.g00 (crossMetric.Bcode 1 0 0) (crossMetric.Ccode 1 0 0 1)) 1 0 0
      ≠ -1 := by
  have h8 : √(8 : ℝ) = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √(2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  simp only [crossMetric, SymG.Bcode, SymG.Ccode, pRoot, SymG.quad]
  norm_num [h8]
  nlinarith [h2, hp]

end EinsteinpyLean.Geodesic.Spec
