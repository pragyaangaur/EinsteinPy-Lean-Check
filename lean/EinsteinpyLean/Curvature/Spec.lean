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

/-- PROP curvature.weyl.traceless : PROVEN
Source: textbook, the Weyl tensor is trace free, `g^{il} C_{iklm} = 0`, in every dimension
`d ≥ 3`; weyl.py:83-98 builds it for `d > 3` (and returns zeros for `d = 3`). Here `R4` is any
tensor, `Ric` its contraction `g^{il} R4_{iklm}` (which is the Ricci tensor of ricci.py:71 when
`R4` is the Riemann tensor lowered with `g`) and `R` the scalar `g^{km} Ric_{km}`. The statement
uses only that `ginv` is a symmetric inverse of the symmetric `g` and that `d ≠ 1, 2`. -/
theorem weyl_traceless (g ginv : Matrix ι ι ℝ) (hg : gᵀ = g) (hgi' : ginvᵀ = ginv)
    (hgi : g * ginv = 1) (R4 : ι → ι → ι → ι → ℝ) (Ric : ι → ι → ℝ) (R : ℝ)
    (hRic : ∀ k m, Ric k m = ∑ i, ∑ l, ginv i l * R4 i k l m) (hR : R = scal ginv Ric)
    (h1 : (Fintype.card ι : ℝ) ≠ 1) (h2 : (Fintype.card ι : ℝ) ≠ 2) (k m : ι) :
    ∑ i, ∑ l, ginv i l * weyl g R4 Ric R i k l m = 0 := by
  have hs : ∀ i j, g j i = g i j := fun i j => by simpa using congrFun (congrFun hg i) j
  have hcomm : ginv * g = 1 := mul_eq_one_comm.mp hgi
  have F1 : ∀ i k, ∑ l, ginv i l * g k l = if i = k then 1 else 0 := fun i k => by
    have := congrFun (congrFun hcomm i) k
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact sum_congr rfl fun l _ => by rw [hs]
  have F2 : ∀ l m, ∑ i, ginv i l * g i m = if l = m then 1 else 0 := fun l m => by
    have := congrFun (congrFun hcomm l) m
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact sum_congr rfl fun i _ => by
      have := congrFun (congrFun hgi' l) i
      simp only [Matrix.transpose_apply] at this
      rw [this]
  have F3 : ∑ i, ∑ l, ginv i l * g i l = (Fintype.card ι : ℝ) := by
    have := congrArg Matrix.trace hgi
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.one_apply_eq] at this
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [← this, sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [mul_comm, hs]
  have B1 : ∑ i, ∑ l, ginv i l * (Ric i m * g k l) = Ric k m := by
    calc _ = ∑ i, Ric i m * (∑ l, ginv i l * g k l) := by
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun l _ => by ring
      _ = ∑ i, Ric i m * (if i = k then 1 else 0) := by simp_rw [F1]
      _ = Ric k m := by simp
  have B2 : ∑ i, ∑ l, ginv i l * (Ric i l * g k m) = R * g k m := by
    rw [hR]
    simp only [scal]
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    exact sum_congr rfl fun l _ => by ring
  have B3 : ∑ i, ∑ l, ginv i l * (Ric k l * g i m) = Ric k m := by
    calc _ = ∑ l, Ric k l * (∑ i, ginv i l * g i m) := by
          rw [sum_comm]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun i _ => by ring
      _ = ∑ l, Ric k l * (if l = m then 1 else 0) := by simp_rw [F2]
      _ = Ric k m := by simp
  have B4 : ∑ i, ∑ l, ginv i l * (Ric k m * g i l) = Ric k m * (Fintype.card ι : ℝ) := by
    rw [← F3, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun l _ => by ring
  have C1 : ∑ i, ∑ l, ginv i l * (R * (g i l * g k m)) = R * g k m * (Fintype.card ι : ℝ) := by
    rw [← F3, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun l _ => by ring
  have C2 : ∑ i, ∑ l, ginv i l * (R * (g i m * g k l)) = R * g k m := by
    calc _ = ∑ i, R * g i m * (∑ l, ginv i l * g k l) := by
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun l _ => by ring
      _ = ∑ i, R * g i m * (if i = k then 1 else 0) := by simp_rw [F1]
      _ = R * g k m := by simp
  have A : ∑ i, ∑ l, ginv i l * R4 i k l m = Ric k m := (hRic k m).symm
  have expand : ∀ i l, ginv i l * weyl g R4 Ric R i k l m =
      ginv i l * R4 i k l m +
        (ginv i l * (Ric i m * g k l) - ginv i l * (Ric i l * g k m)
          + ginv i l * (Ric k l * g i m) - ginv i l * (Ric k m * g i l)) *
          ((Fintype.card ι : ℝ) - 2)⁻¹ +
        (ginv i l * (R * (g i l * g k m)) - ginv i l * (R * (g i m * g k l))) *
          (((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2))⁻¹ := by
    intro i l
    unfold weyl
    ring
  simp_rw [expand]
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_mul]
  rw [A, B1, B2, B3, B4, C1, C2]
  have h2' : (Fintype.card ι : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr h2
  have h1' : (Fintype.card ι : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
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

/-- `∂_r Γ^t_{sn}` for the Christoffel symbols of a metric jet (`Gi = g⁻¹`, `D k i j = ∂_k g_ij`,
`DD k l i j = ∂_k ∂_l g_ij`), using `∂(g⁻¹) = -g⁻¹ (∂g) g⁻¹`. -/
def dchris (Gi : Matrix ι ι ℝ) (D : ι → Matrix ι ι ℝ) (DD : ι → ι → Matrix ι ι ℝ)
    (r t s n : ι) : ℝ :=
  ∑ m, ((-(Gi * D r * Gi)) t m / 2 * (D n m s + D s m n - D m s n) +
    Gi t m / 2 * (DD r n m s + DD r s m n - DD r m s n))

lemma sum_sym (X A : ι → ι → ℝ) (hX : ∀ a b, X a b = X b a) :
    ∑ t, ∑ m, X t m * A m t = ∑ t, ∑ m, X t m * A t m := by
  rw [sum_comm]
  exact sum_congr rfl fun t _ => sum_congr rfl fun m _ => by rw [hX m t]


lemma cancel3 (X P S Q : ι → ι → ℝ) (hX : ∀ a b, X a b = X b a) (hPQ : ∀ t m, Q t m = P m t) :
    ∑ t, ∑ m, X t m / 2 * (P t m + S t m - Q t m) = ∑ t, ∑ m, X t m / 2 * S t m := by
  have h := sum_sym (fun a b => X a b / 2) P (fun a b => by rw [hX a b])
  have e : ∀ t m, X t m / 2 * (P t m + S t m - Q t m) =
      X t m / 2 * P t m + X t m / 2 * S t m - X t m / 2 * P m t := fun t m => by
    rw [hPQ t m]; ring
  simp only [e, sum_sub_distrib, sum_add_distrib]
  rw [h]
  ring

variable (Gi : Matrix ι ι ℝ) (D : ι → Matrix ι ι ℝ) (DD : ι → ι → Matrix ι ι ℝ)
  (hGi : ∀ a b, Gi a b = Gi b a) (hD : ∀ k a b, D k a b = D k b a)
  (hDD : ∀ k l a b, DD k l a b = DD k l b a) (hDDs : ∀ k l a b, DD k l a b = DD l k a b)

include hGi hD in
lemma dGi_symm (r t m : ι) : (-(Gi * D r * Gi)) t m = (-(Gi * D r * Gi)) m t := by
  have hGiT : Giᵀ = Gi := by ext a b; exact (hGi b a)
  have hDT : (D r)ᵀ = D r := by ext a b; exact (hD r b a)
  have : (Gi * D r * Gi)ᵀ = Gi * D r * Gi := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hGiT, hDT, Matrix.mul_assoc]
  have h2 := congrFun (congrFun this m) t
  simp only [Matrix.transpose_apply] at h2
  simp [h2]

include hD hDD in
lemma dchris_symm (r t s n : ι) : dchris Gi D DD r t s n = dchris Gi D DD r t n s := by
  unfold dchris
  refine sum_congr rfl fun m _ => ?_
  rw [hD m n s, hDD r m n s]
  ring

include hGi hD hDD in
lemma sum_dchris (n s : ι) : ∑ t, dchris Gi D DD n t s t =
    1 / 2 * ∑ t, ∑ m, (-(Gi * D n * Gi)) t m * D s m t +
      1 / 2 * ∑ t, ∑ m, Gi t m * DD n s m t := by
  unfold dchris
  simp only [sum_add_distrib]
  rw [cancel3 (fun t m => (-(Gi * D n * Gi)) t m) (fun t m => D t m s) (fun t m => D s m t)
      (fun t m => D m s t) (dGi_symm Gi D hGi hD n) (fun t m => by simp only [hD m s t]),
    cancel3 (fun t m => Gi t m) (fun t m => DD n t m s) (fun t m => DD n s m t)
      (fun t m => DD n m s t) hGi (fun t m => by simp only [hDD n m s t])]
  simp only [mul_sum, div_eq_mul_inv]
  refine congrArg₂ _ ?_ ?_ <;> refine sum_congr rfl fun t _ => sum_congr rfl fun m _ => by ring

include hGi hD in
lemma tr_sym (n s : ι) : ∑ t, ∑ m, (-(Gi * D n * Gi)) t m * D s m t =
    ∑ t, ∑ m, (-(Gi * D s * Gi)) t m * D n m t := by
  have h : ∀ A B : Matrix ι ι ℝ, Matrix.trace (A * B) = ∑ t, ∑ m, A t m * B m t := by
    intro A B; simp [Matrix.trace, Matrix.mul_apply]
  rw [← h, ← h, Matrix.neg_mul, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_neg]
  congr 1
  calc Matrix.trace (Gi * D n * Gi * D s)
      = Matrix.trace (D s * (Gi * D n * Gi)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((D s * Gi * D n) * Gi) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Gi * (D s * Gi * D n)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Gi * D s * Gi * D n) := by simp only [Matrix.mul_assoc]

include hGi hD hDD hDDs in
lemma sum_dchris_symm (n s : ι) :
    ∑ t, dchris Gi D DD n t s t = ∑ t, dchris Gi D DD s t n t := by
  rw [sum_dchris Gi D DD hGi hD hDD, sum_dchris Gi D DD hGi hD hDD, tr_sym Gi D hGi hD n s]
  have : ∀ t m, DD n s m t = DD s n m t := fun t m => hDDs n s m t
  simp only [this]

include hGi hD hDD hDDs in
/-- PROP curvature.ricci.symmetric : PROVEN
Source: textbook, the Ricci tensor of a Levi-Civita connection is symmetric. For the Ricci
tensor of ricci.py:71 built from the Riemann tensor of riemann.py:87-89 and the Christoffel
symbols of christoffel.py:73-77 of any metric jet: `Gi` is a symmetric `g⁻¹`, `D k i j = ∂_k g_ij`
and `DD k l i j = ∂_k ∂_l g_ij` are symmetric in the metric indices, and `DD` is symmetric in the
derivative indices. -/
theorem ricci_symm (s n : ι) :
    ric (riem (chris (fun a b => Gi a b) (fun k i j => D k i j)) (dchris Gi D DD)) s n =
      ric (riem (chris (fun a b => Gi a b) (fun k i j => D k i j)) (dchris Gi D DD)) n s := by
  have hΓ : ∀ t s n, chris (fun a b => Gi a b) (fun k i j => D k i j) t s n =
      chris (fun a b => Gi a b) (fun k i j => D k i j) t n s :=
    fun t s n => chris_symm _ _ (fun k i j => hD k i j) t s n
  unfold ric riem
  simp only [sum_add_distrib, sum_sub_distrib]
  have a1 : ∑ t, dchris Gi D DD t t s n = ∑ t, dchris Gi D DD t t n s :=
    sum_congr rfl fun t _ => dchris_symm Gi D DD hD hDD t t s n
  have a3 : ∑ t, ∑ p, chris (fun a b => Gi a b) (fun k i j => D k i j) p s n *
        chris (fun a b => Gi a b) (fun k i j => D k i j) t p t =
      ∑ t, ∑ p, chris (fun a b => Gi a b) (fun k i j => D k i j) p n s *
        chris (fun a b => Gi a b) (fun k i j => D k i j) t p t :=
    sum_congr rfl fun t _ => sum_congr rfl fun p _ => by rw [hΓ p s n]
  have a4 : ∑ t, ∑ p, chris (fun a b => Gi a b) (fun k i j => D k i j) p s t *
        chris (fun a b => Gi a b) (fun k i j => D k i j) t p n =
      ∑ t, ∑ p, chris (fun a b => Gi a b) (fun k i j => D k i j) p n t *
        chris (fun a b => Gi a b) (fun k i j => D k i j) t p s := by
    rw [sum_comm (f := fun t p => chris (fun a b => Gi a b) (fun k i j => D k i j) p n t *
        chris (fun a b => Gi a b) (fun k i j => D k i j) t p s)]
    refine sum_congr rfl fun t _ => sum_congr rfl fun p _ => ?_
    rw [hΓ t n p, hΓ p t s, mul_comm]
  rw [a1, sum_dchris_symm Gi D DD hGi hD hDD hDDs n s, a3, a4]

end

end EinsteinpyLean.Curvature.Spec
