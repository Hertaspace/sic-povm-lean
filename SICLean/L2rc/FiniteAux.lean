import SICLean.L2rc.Generic

set_option autoImplicit false

/-! # Real-root uniqueness used by the rank-r origin-value bridge -/

namespace SICLean.L2rc.FiniteAux

theorem nonneg_quadratic_unique (s a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hqa : a ^ 2 = s * a + 1) (hqb : b ^ 2 = s * b + 1) : a = b := by
  have hsa : s < a := by
    by_contra h
    have hh : a ≤ s := le_of_not_gt h
    have hm := mul_le_mul_of_nonneg_right hh ha
    nlinarith
  have hpos : 0 < a + b - s := by linarith
  have hf : (a - b) * (a + b - s) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hf | hf
  · linarith
  · linarith

end SICLean.L2rc.FiniteAux
