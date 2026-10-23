import SICLean.L4.M74Equations

set_option autoImplicit false

/-!
# Arithmetic algebraicity of the prescribed positive square root

Only the explicit radical formula for the period is used here; no pentagon
identity or algebraicity of a nonzero-class special value is an input.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L4.M78SpecializationsAux

theorem sqrt_isAlgebraic {x : ℝ} (hx : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ (Real.sqrt x) := by
  rcases le_or_gt 0 x with h | h
  · apply IsAlgebraic.of_pow (n := 2) (by norm_num)
    rwa [Real.sq_sqrt h]
  · rw [Real.sqrt_eq_zero_of_nonpos h.le]
    exact isAlgebraic_zero

theorem period_sqrt_isAlgebraic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    IsAlgebraic ℚ (Real.sqrt (specialValueEpsilon M) : ℂ) := by
  have hN : IsAlgebraic ℚ (specialValueOrder M : ℝ) :=
    isAlgebraic_intCast (R := ℚ) (A := ℝ) _
  have h2 : IsAlgebraic ℚ (2 : ℝ) := isAlgebraic_natCast 2
  have h4 : IsAlgebraic ℚ (4 : ℝ) := isAlgebraic_natCast 4
  have hs := sqrt_isAlgebraic ((hN.pow 2).add (h4.mul hN))
  have he : IsAlgebraic ℚ (specialValueEpsilon M) := by
    rw [specialValueEpsilon_formula M hM, div_eq_mul_inv]
    exact ((hN.add h2).add hs).mul h2.inv
  exact (sqrt_isAlgebraic he).algebraMap

end SICLean.L4.M78SpecializationsAux
