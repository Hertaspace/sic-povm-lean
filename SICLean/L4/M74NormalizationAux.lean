import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

/-! Elementary real-algebra lemmas for the positive normalization. -/

namespace SICLean.L4.M74NormalizationAux

/-- The root greater than one is the positive-discriminant branch. -/
theorem quadratic_root_gt_one {e n : ℝ} (he : 1 < e) (hn : 0 ≤ n)
    (hp : e ^ 2 - (n + 2) * e + 1 = 0) :
    e = (n + 2 + Real.sqrt (n ^ 2 + 4 * n)) / 2 := by
  have he0 : 0 < e := by linarith
  have hd : 0 ≤ n ^ 2 + 4 * n := by positivity
  have hprod : 0 < e * (2 * e - (n + 2)) := by
    nlinarith [sq_nonneg (e - 1)]
  have hs : 0 ≤ 2 * e - (n + 2) := by
    by_contra h
    have hm := mul_nonpos_of_nonneg_of_nonpos he0.le (le_of_not_ge h)
    linarith
  have hr : Real.sqrt (n ^ 2 + 4 * n) = 2 * e - (n + 2) := by
    apply (Real.sqrt_eq_iff_eq_sq hd hs).2
    nlinarith [hp]
  linarith

/-- Both factors use the nonnegative real square root. -/
theorem quadratic_sqrt_normalization {e n : ℝ} (he : 1 < e) (hn : 0 ≤ n)
    (hp : e ^ 2 - (n + 2) * e + 1 = 0) :
    Real.sqrt e ^ 2 - Real.sqrt n * Real.sqrt e - 1 = 0 := by
  have he0 : 0 ≤ e := by linarith
  have hr : Real.sqrt (n * e) = e - 1 := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hn he0) (by linarith)).2
    nlinarith [hp]
  rw [Real.sqrt_mul hn] at hr
  nlinarith [Real.sq_sqrt he0]

end SICLean.L4.M74NormalizationAux
