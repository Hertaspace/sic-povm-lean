import SICLean.L5.FiniteFourier

set_option autoImplicit false

noncomputable section

open Classical
open scoped MatrixGroups

namespace SICLean.L5.FiniteProductPentagonAux

open L4 FiniteFourier

/-- Multiplication by the actual Gaussian preserves the zero indicator. -/
theorem gaussian_mul_delta (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    specialValueGaussian M hM x * delta M x = delta M x := by
  by_cases hx : x = 0
  · subst x
    simp [delta, L3.M74.gaussian_zero]
  · simp [delta, hx]

end SICLean.L5.FiniteProductPentagonAux
