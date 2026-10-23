import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace SICLean.L5.Prop7FinalConjugationAux

/-- A complex number whose square is a positive real number is real. -/
theorem im_eq_zero_of_sq_eq_pos_real (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hz : z ^ 2 = (r : ℂ)) : z.im = 0 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.ofReal_re] at hre
  simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at him
  have hprod : z.re * z.im = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hre0 | him0
  · nlinarith [sq_nonneg z.im]
  · exact him0

/-- Conjugation agreeing with inversion forces unit complex norm. -/
theorem norm_eq_one_of_conj_eq_inv (z : ℂ) (hz : z ≠ 0)
    (hconj : star z = z⁻¹) : ‖z‖ = 1 := by
  have hmul : z * star z = 1 := by rw [hconj, mul_inv_cancel₀ hz]
  have hnormsq : ‖z‖ ^ 2 = 1 := by
    simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re,
      Complex.normSq_eq_norm_sq] using congrArg Complex.re hmul
  nlinarith [norm_nonneg z]

end SICLean.L5.Prop7FinalConjugationAux
