import Physlib.Relativity.LorentzGroup.Basic

/-!
# `lorentz_transform` against Physlib's Lorentz group

`BaseRelativityTensor.lorentz_transform` (tensor.py:424-459) contracts an upper index
with axis 1 of the matrix and a lower index with axis 0. On vectors that is
`v' = Λ v` and `w' = Λᵀ w`. Here those two rules are stated over the reals and
compared with Physlib's `LorentzGroup d`, the matrices with `Λᵀ η Λ = η`.

The executable model in `Model.lean` computes exactly these contractions on
rationals and is checked against einsteinpy by `difftest/tensor_index_diff.py`.
-/

open Matrix minkowskiMatrix

namespace EinsteinpyLean.Tensor.Spec

variable {d : ℕ}

/-- Vectors on `1 + d` dimensional spacetime, as in Physlib. -/
abbrev V (d : ℕ) := Fin 1 ⊕ Fin d → ℝ

/-- einsteinpy main, upper index: contract axis 1 of the matrix, `v'^a = Λ^a_b v^b`. -/
def epUpper (Λ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : V d) : V d := Λ *ᵥ v

/-- einsteinpy main, lower index: contract axis 0 of the matrix, `w'_b = Λ^a_b w_a`. -/
def epLower (Λ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (w : V d) : V d := Λᵀ *ᵥ w

/-- The rule of einsteinpy PR #708: contract axis 0 of the inverse, `w'_b = (Λ⁻¹)^a_b w_a`. -/
noncomputable def fixedLower (Λ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (w : V d) : V d :=
  (Λ⁻¹)ᵀ *ᵥ w

/-- PROP tensor.lorentz_transform.fixed_preserves_contraction : PROVEN
Source: definition of a (1,0) and a (0,1) tensor; `v^a w_a` is a scalar. With the
PR #708 rule the contraction of a transformed vector with a transformed covector is
unchanged, for every Lorentz transformation of Physlib. -/
theorem fixed_preserves_contraction (Λ : LorentzGroup d) (v w : V d) :
    epUpper Λ.1 v ⬝ᵥ fixedLower Λ.1 w = v ⬝ᵥ w := by
  unfold epUpper fixedLower
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec,
    LorentzGroup.subtype_inv_mul, one_mulVec, dotProduct_comm]

/-- PROP tensor.lorentz_transform.fixed_commutes_with_lowering : PROVEN
Source: index lowering by the metric is Lorentz covariant. Lowering with Physlib's
`η` and then applying the PR #708 rule equals boosting and then lowering. -/
theorem fixed_lower_comm (Λ : LorentzGroup d) (v : V d) :
    η *ᵥ epUpper Λ.1 v = fixedLower Λ.1 (η *ᵥ v) := by
  unfold epUpper fixedLower
  rw [mulVec_mulVec, mulVec_mulVec, LorentzGroup.minkowskiMatrix_comm,
    LorentzGroup.transpose_val, LorentzGroup.coe_inv]

/-- PROP tensor.change_config.lower_raise_roundtrip : PROVEN
Source: tensor.py:44-84 uses `g` to lower and `g⁻¹` to raise; for an invertible metric
the round trip is the identity. -/
theorem lower_raise {n : Type} [Fintype n] [DecidableEq n]
    (g : Matrix n n ℝ) (hg : IsUnit g.det) (v : n → ℝ) : g⁻¹ *ᵥ (g *ᵥ v) = v := by
  rw [mulVec_mulVec, nonsing_inv_mul g hg, one_mulVec]

/-- The 1+1 boost with velocity 3/5: γ = 5/4, γ v = 3/4. -/
noncomputable def boost35 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.of fun i j => if i = j then 5 / 4 else 3 / 4

lemma boost35_mem : boost35 ∈ LorentzGroup 1 := by
  rw [LorentzGroup.mem_iff_transpose_mul_minkowskiMatrix_mul_self]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [boost35, Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.inl_0_inl_0,
      minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.off_diag_zero] <;> norm_num

/-- PROP tensor.lorentz_transform.main_preserves_contraction : REFUTED
Source: same as `fixed_preserves_contraction`, for the rule on einsteinpy main
(63e1c54). For the 3/5 boost and `v = w = e₀` the contraction `v^a w_a = 1`
becomes `(5/4)² + (3/4)² = 17/8`. -/
theorem main_not_preserves_contraction :
    ¬ ∀ (Λ : LorentzGroup 1) (v w : V 1), epUpper Λ.1 v ⬝ᵥ epLower Λ.1 w = v ⬝ᵥ w := by
  intro h
  have := h ⟨boost35, boost35_mem⟩ (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inl 0) 1)
  simp [epUpper, epLower, boost35, dotProduct, mulVec, Fintype.sum_sum_type,
    Pi.single_apply] at this
  norm_num at this

end EinsteinpyLean.Tensor.Spec
