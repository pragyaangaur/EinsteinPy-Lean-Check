import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# The hand-coded Christoffel symbols of Kerr and Kerr-Newman against the general formula

`kerr.py:240-264` and `kerrnewman.py:285-325` do not evaluate `Gamma^i_{kl} = 1/2 g^{im}(d_l g_{mk} + d_k g_{ml} - d_m g_{kl})`
in full. They loop over a precomputed list of 32 index triples and, for each group, drop terms that vanish for a
metric of Kerr shape. A dropped term that does not vanish would be a silent bug. Here the recipe is stated over the
reals for any inverse metric and any derivative array of the Kerr sparsity pattern, and it is proved equal to the
full formula at all 64 index triples.

Sparsity: `g^{im}` is nonzero only at `00 03 30 33 11 22`; `d_k g_{mn}` is nonzero only for `k = 1, 2` (the metric does
not depend on `t` or `phi`) and `(m, n)` in `00 03 30 11 22 33`.
-/

namespace EinsteinpyLean.Metric.Spec

/-- The textbook Christoffel symbol from the inverse metric `gi` and `dg k m n = d_k g_{mn}`. -/
noncomputable def chFull (gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (i k l : Fin 4) : ℝ :=
  (1 / 2) * ∑ m, gi i m * (dg l m k + dg k m l - dg m k l)

/-- Index pairs `(k, l)` of the first loop (`kerr.py:246-254`), both orders. -/
def pairs03 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 3), (3, 1), (2, 3), (3, 2)}

/-- The triples `(i, k, l)` with `i = 1` written by the second and third loops (`kerr.py:255-262`). -/
def set1 : Finset (Fin 4 × Fin 4) := {(0, 0), (1, 1), (2, 2), (3, 3), (0, 3), (3, 0), (1, 2), (2, 1)}

/-- The triples with `i = 2`. -/
def set2 : Finset (Fin 4 × Fin 4) := {(0, 0), (1, 1), (2, 2), (3, 3), (0, 3), (3, 0), (1, 2), (2, 1)}

/-- The values the code stores, zero where it stores nothing. Rows `0` and `3` use only the `t` and `phi` terms. -/
noncomputable def chRec (gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (i k l : Fin 4) : ℝ :=
  if i = 0 ∨ i = 3 then
    if (k, l) ∈ pairs03 then
      (1 / 2) * (gi i 0 * (dg l 0 k + dg k 0 l) + gi i 3 * (dg l 3 k + dg k 3 l))
    else 0
  else if i = 1 then
    if (k, l) ∈ set1 then (1 / 2) * (gi 1 1 * (dg l 1 k + dg k 1 l - dg 1 k l)) else 0
  else
    if (k, l) ∈ set2 then (1 / 2) * (gi 2 2 * (dg l 2 k + dg k 2 l - dg 2 k l)) else 0

/-- Sparsity of the inverse metric. -/
def SparseGi (gi : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ i m, (i, m) ∉ ({(0, 0), (0, 3), (3, 0), (3, 3), (1, 1), (2, 2)} : Finset (Fin 4 × Fin 4)) → gi i m = 0

/-- Sparsity and symmetry of the derivatives of a metric of Kerr shape. -/
def SparseDg (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ k m n, (k, m, n) ∉ ({(1, 0, 0), (1, 1, 1), (1, 2, 2), (1, 3, 3), (1, 0, 3), (1, 3, 0),
      (2, 0, 0), (2, 1, 1), (2, 2, 2), (2, 3, 3), (2, 0, 3), (2, 3, 0)} : Finset (Fin 4 × Fin 4 × Fin 4)) →
      dg k m n = 0) ∧ dg 1 3 0 = dg 1 0 3 ∧ dg 2 3 0 = dg 2 0 3

/-- PROP metric.kerr.christoffel.recipe_is_complete : PROVEN
Source: kerr.py:240-264 and kerrnewman.py:285-325 `_ch_sym_bl` against the definition of the Christoffel symbol. For
every inverse metric and derivative array of Kerr shape, the 32 stored entries are the full Christoffel symbol and
the 32 entries never written are zero in the full formula. So no hand-dropped term is lost. -/
theorem recipe_is_complete (gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hg : SparseGi gi) (hd : SparseDg dg) (i k l : Fin 4) : chRec gi dg i k l = chFull gi dg i k l := by
  obtain ⟨hd0, h13, h23⟩ := hd
  have z : ∀ i m, (i, m) ∉ ({(0, 0), (0, 3), (3, 0), (3, 3), (1, 1), (2, 2)} : Finset (Fin 4 × Fin 4)) → gi i m = 0 := hg
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp (disch := decide) [chRec, chFull, Fin.sum_univ_four, pairs03, set1, set2, z, hd0, h13, h23] <;> ring

end EinsteinpyLean.Metric.Spec
