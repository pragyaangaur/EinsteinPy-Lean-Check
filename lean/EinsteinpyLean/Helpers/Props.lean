import EinsteinpyLean.Helpers.Model

/-! # Properties of the `TransformationMatrix` model -/

namespace EinsteinpyLean.Helpers

/-- PROP helpers.transformation_matrix.inv_is_involution_off_zero : PROVEN
Source: helpers.py:171-190. `inv` undoes `from_new2old` on every nonzero entry, so
`inv()` returns the derivative array itself, never the inverse matrix. -/
theorem recip_recip (q : Rat) (h : q ≠ 0) : (Num.rat q).recip.recip = .rat q := by
  have h' : q⁻¹ ≠ 0 := fun h0 => h (by rw [← Rat.inv_inv q, h0, Rat.inv_zero])
  simp [Num.recip, h, h', Rat.inv_inv]

/-- PROP helpers.transformation_matrix.zero_derivative_gives_zoo : PROVEN
Source: helpers.py:157. A zero partial derivative becomes sympy's complex infinity. -/
theorem recip_zero : (Num.rat 0).recip = .zoo := by simp [Num.recip]

end EinsteinpyLean.Helpers
