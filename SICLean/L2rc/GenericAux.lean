import SICLean.L2c.Finite

set_option autoImplicit false

/-! Real radical identities used by the generic Theorem 2 derivation. -/

noncomputable section

namespace SICLean.L2rc.Generic.Aux

theorem real_plus_formula (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt ((N + 2 + Real.sqrt (N ^ 2 + 4 * N)) / 2) =
      (Real.sqrt (N + 4) + Real.sqrt N) / 2 := by
  have ht : Real.sqrt (N + 4) ^ 2 = N + 4 := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have hr : Real.sqrt (N ^ 2 + 4 * N) = Real.sqrt N * Real.sqrt (N + 4) := by
    rw [show N ^ 2 + 4 * N = N * (N + 4) by ring, Real.sqrt_mul hN]
  have hn : 0 ≤ (Real.sqrt (N + 4) + Real.sqrt N) / 2 := by positivity
  apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) hn).mpr
  rw [hr]
  nlinarith

theorem real_minus_formula (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt ((N + 2 - Real.sqrt (N ^ 2 + 4 * N)) / 2) =
      (Real.sqrt (N + 4) - Real.sqrt N) / 2 := by
  have ht : Real.sqrt (N + 4) ^ 2 = N + 4 := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have hts : Real.sqrt N ≤ Real.sqrt (N + 4) := Real.sqrt_le_sqrt (by linarith)
  have hr : Real.sqrt (N ^ 2 + 4 * N) = Real.sqrt N * Real.sqrt (N + 4) := by
    rw [show N ^ 2 + 4 * N = N * (N + 4) by ring, Real.sqrt_mul hN]
  have hn : 0 ≤ (Real.sqrt (N + 4) - Real.sqrt N) / 2 := by linarith
  have hrad : 0 ≤ (N + 2 - Real.sqrt (N ^ 2 + 4 * N)) / 2 := by
    rw [hr]
    nlinarith [sq_nonneg (Real.sqrt (N + 4) - Real.sqrt N)]
  apply (Real.sqrt_eq_iff_mul_self_eq hrad hn).mpr
  rw [hr]
  nlinarith

theorem real_plus_quadratic (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt ((N + 2 + Real.sqrt (N ^ 2 + 4 * N)) / 2) ^ 2 =
      Real.sqrt N * Real.sqrt ((N + 2 + Real.sqrt (N ^ 2 + 4 * N)) / 2) + 1 := by
  rw [real_plus_formula N hN]
  have ht : Real.sqrt (N + 4) ^ 2 = N + 4 := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  nlinarith

theorem real_plus_mul_minus (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt ((N + 2 + Real.sqrt (N ^ 2 + 4 * N)) / 2) *
      Real.sqrt ((N + 2 - Real.sqrt (N ^ 2 + 4 * N)) / 2) = 1 := by
  rw [real_plus_formula N hN, real_minus_formula N hN]
  have ht : Real.sqrt (N + 4) ^ 2 = N + 4 := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  nlinarith

end SICLean.L2rc.Generic.Aux
