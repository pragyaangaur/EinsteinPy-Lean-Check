import Physlib.Relativity.MinkowskiMatrix

/-!
# The curvature formulas of einsteinpy over the reals

einsteinpy computes, with `sympy.diff`, the Christoffel symbols
`Γ^i_{jk} = ½ g^{in} (∂_k g_{nj} + ∂_j g_{nk} - ∂_n g_{jk})` (christoffel.py:73-77), the
Riemann tensor `R^t_{srn} = ∂_r Γ^t_{sn} - ∂_n Γ^t_{sr} + Γ^p_{sn} Γ^t_{pr} - Γ^p_{sr} Γ^t_{pn}`
(riemann.py:87-89), the Ricci tensor `Ric_{sn} = R^t_{stn}` (ricci.py:71), the Ricci scalar
`g^{ab} Ric_{ab}`, the Einstein tensor `Ric - ½ R g` (einstein.py:54-56) and the Weyl tensor
(weyl.py:83-98).

Here the same formulas are stated for arrays of real numbers (the derivatives are given as
input arrays, which is what a 2-jet is) over any finite index type, and the classical
identities are proved. The index type can be `Fin n` or Physlib's `Fin 1 ⊕ Fin d`, so the
statements about flat space use Physlib's `minkowskiMatrix`.

The executable model of `Model.lean` computes the same formulas on rationals and is checked
against einsteinpy by `difftest/curvature_jet_diff.py` and `difftest/curvature_from_diff.py`.
-/

open Finset Matrix

set_option linter.unusedSectionVars false

namespace EinsteinpyLean.Curvature.Spec

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- christoffel.py:73-77. `ginv` is `g⁻¹` and `dg k i j = ∂_k g_ij`. -/
def chris (ginv : ι → ι → ℝ) (dg : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  ∑ m, ginv i m / 2 * (dg k m j + dg j m k - dg m j k)

/-- riemann.py:87-89, `R[t][s][r][n]`. `dΓ r t s n = ∂_r Γ^t_{sn}`. -/
def riem (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) (t s r n : ι) : ℝ :=
  dΓ r t s n - dΓ n t s r + ∑ p, (Γ p s n * Γ t p r - Γ p s r * Γ t p n)

/-- ricci.py:71, `tensorcontraction(riemann, (0, 2))`. -/
def ric (R : ι → ι → ι → ι → ℝ) (s n : ι) : ℝ := ∑ t, R t s t n

/-- The Ricci scalar `g^{ab} Ric_{ab}` (ricci.py:231-237). -/
def scal (ginv : ι → ι → ℝ) (Ric : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, ginv i j * Ric i j

/-- einstein.py:54-56. -/
def einstein (Ric : ι → ι → ℝ) (R : ℝ) (g : ι → ι → ℝ) (i j : ι) : ℝ :=
  Ric i j - 1 / 2 * R * g i j

/-- weyl.py:83-98, with `d` the dimension, `R4` the Riemann tensor with all indices lower. -/
def weyl (g : ι → ι → ℝ) (R4 : ι → ι → ι → ι → ℝ) (Ric : ι → ι → ℝ) (R : ℝ)
    (i k l m : ι) : ℝ :=
  R4 i k l m +
    (Ric i m * g k l - Ric i l * g k m + Ric k l * g i m - Ric k m * g i l) /
      ((Fintype.card ι : ℝ) - 2) +
    R * (g i l * g k m - g i m * g k l) /
      (((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2))

/-- PROP curvature.christoffel.symmetric_in_lower_indices : PROVEN
Source: textbook, the Levi-Civita connection is torsion free, so `Γ^i_{jk} = Γ^i_{kj}` when `g` is symmetric (`∂g` symmetric in its last two indices);
christoffel.py:78 fills both `[i][j][k]` and `[i][k][j]`. -/
theorem chris_symm (ginv : ι → ι → ℝ) (dg : ι → ι → ι → ℝ)
    (hdg : ∀ k i j, dg k i j = dg k j i) (i j k : ι) :
    chris ginv dg i j k = chris ginv dg i k j := by
  unfold chris
  exact sum_congr rfl fun m _ => by rw [hdg m j k]; ring

/-- PROP curvature.riemann.antisymmetric_in_last_two : PROVEN
Source: textbook, `R^t_{srn} = -R^t_{snr}`, for the formula of riemann.py:87-89 with any
`Γ` and `∂Γ`. -/
theorem riem_antisymm (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) (t s r n : ι) :
    riem Γ dΓ t s r n = - riem Γ dΓ t s n r := by
  unfold riem
  simp only [sum_sub_distrib]
  ring

/-- PROP curvature.riemann.first_bianchi_identity : PROVEN
Source: textbook, `R^t_{srn} + R^t_{rns} + R^t_{nsr} = 0` for a torsion free connection.
Here `Γ` and `∂Γ` are symmetric in the two lower indices, which `chris_symm` gives for
every Levi-Civita connection. -/
theorem riem_bianchi (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ)
    (hΓ : ∀ t s n, Γ t s n = Γ t n s) (hdΓ : ∀ r t s n, dΓ r t s n = dΓ r t n s)
    (t s r n : ι) :
    riem Γ dΓ t s r n + riem Γ dΓ t r n s + riem Γ dΓ t n s r = 0 := by
  unfold riem
  have e1 : ∑ p, Γ p r s * Γ t p n = ∑ p, Γ p s r * Γ t p n :=
    sum_congr rfl fun p _ => by rw [hΓ p r s]
  have e2 : ∑ p, Γ p n r * Γ t p s = ∑ p, Γ p r n * Γ t p s :=
    sum_congr rfl fun p _ => by rw [hΓ p n r]
  have e3 : ∑ p, Γ p n s * Γ t p r = ∑ p, Γ p s n * Γ t p r :=
    sum_congr rfl fun p _ => by rw [hΓ p n s]
  simp only [sum_sub_distrib]
  rw [e1, e2, e3, hdΓ r t s n, hdΓ n t r s, hdΓ s t n r]
  ring

/-- PROP curvature.einstein.trace : PROVEN
Source: textbook, the trace of the Einstein tensor is `(1 - d/2) R`, which is `-R` in four
dimensions. For einsteinpy's formula (einstein.py:54-56), which uses `1/2` in every
dimension. `ginv` is a symmetric inverse of `g`. -/
theorem einstein_trace (g ginv : Matrix ι ι ℝ) (hg : gᵀ = g) (hgi : g * ginv = 1)
    (Ric : ι → ι → ℝ) :
    ∑ i, ∑ j, ginv i j * einstein Ric (scal ginv Ric) g i j =
      (1 - (Fintype.card ι : ℝ) / 2) * scal ginv Ric := by
  have h3 : ∑ i, ∑ j, ginv i j * g i j = (Fintype.card ι : ℝ) := by
    have := congrArg Matrix.trace hgi
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.one_apply_eq] at this
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    have hs : ∀ i j, g j i = g i j := fun i j => by
      simpa using congrFun (congrFun hg i) j
    rw [← this, sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [mul_comm, hs]
  unfold einstein
  have h2 : ∑ i, ∑ j, ginv i j * (1 / 2 * scal ginv Ric * g i j) =
      1 / 2 * scal ginv Ric * ∑ i, ∑ j, ginv i j * g i j := by
    generalize scal ginv Ric = R
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  have h1 : ∑ i, ∑ j, ginv i j * Ric i j = scal ginv Ric := rfl
  simp only [mul_sub, sum_sub_distrib]
  rw [h1, h2, h3]
  ring

/-- Flat space. For Physlib's Minkowski matrix `η` as the metric all derivatives vanish, and
then the Christoffel symbols, the Riemann tensor, the Ricci tensor, the Ricci scalar and the
Einstein tensor are zero. -/
theorem minkowski_chris_zero (d : ℕ) (i j k : Fin 1 ⊕ Fin d) :
    chris (fun a b => (minkowskiMatrix (d := d))⁻¹ a b) (fun _ _ _ => 0) i j k = 0 := by
  simp [chris]

/-- PROP curvature.riemann.minkowski_flat : PROVEN
Source: textbook, Minkowski space is flat. With `Γ = 0` and `∂Γ = 0` (the Christoffel
symbols of `η` by `minkowski_chris_zero`), the Riemann, Ricci, scalar and Einstein
expressions of einsteinpy are all zero. -/
theorem minkowski_riemann_zero (d : ℕ) (t s r n : Fin 1 ⊕ Fin d) :
    riem (fun _ _ _ => (0 : ℝ)) (fun _ _ _ _ => (0 : ℝ)) t s r n = 0 := by
  simp [riem]

theorem minkowski_einstein_zero (d : ℕ) (i j : Fin 1 ⊕ Fin d) :
    einstein (ric (riem (fun _ _ _ => (0 : ℝ)) (fun _ _ _ _ => (0 : ℝ))))
      (scal (fun a b => (minkowskiMatrix (d := d))⁻¹ a b)
        (ric (riem (fun _ _ _ => (0 : ℝ)) (fun _ _ _ _ => (0 : ℝ)))))
      (fun a b => minkowskiMatrix (d := d) a b) i j = 0 := by
  simp [einstein, scal, ric, riem]

end

end EinsteinpyLean.Curvature.Spec
