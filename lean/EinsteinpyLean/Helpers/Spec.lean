import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum

/-!
# `TransformationMatrix` against the inverse Jacobian

The basis change of a vector under `old = f(new)` needs the Jacobian `∂old/∂new` and
its matrix inverse `∂new/∂old`. `from_new2old` and `inv` both return the element-wise
reciprocal instead (helpers.py:157, helpers.py:187). Over Mathlib's matrices the
element-wise reciprocal is not the inverse even for the simplest invertible linear
map with no zero entries.
-/

open Matrix

namespace EinsteinpyLean.Helpers.Spec

/-- The element-wise reciprocal that `np.reciprocal` computes. -/
def recip {n : Type} (J : Matrix n n ℚ) : Matrix n n ℚ := Matrix.of fun i j => (J i j)⁻¹

/-- PROP helpers.transformation_matrix.inv_is_matrix_inverse : REFUTED
Source: helpers.py:171-180 docstring, "Returns inverse of the transformation matrix".
For the map `x = 2u + v, y = u + v` the Jacobian is `!![2, 1; 1, 1]` with
determinant 1, and its element-wise reciprocal times itself is not the identity. -/
theorem recip_not_inverse :
    ¬ ∀ J : Matrix (Fin 2) (Fin 2) ℚ, IsUnit J.det → (∀ i j, J i j ≠ 0) → recip J * J = 1 := by
  intro h
  have := congrFun (congrFun (h !![2, 1; 1, 1] (by simp [det_fin_two]; norm_num) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp)) 0) 0
  simp [recip, Matrix.mul_apply, Fin.sum_univ_two] at this

end EinsteinpyLean.Helpers.Spec
