import Mathlib.NumberTheory.Real.Irrational
import SICLean.L4.SpecialValueGeometry

set_option autoImplicit false

/-! Elementary facts about the smaller root of X² - (N+2)X + 1. -/

namespace SICLean.L4.G2RepellingGeometryAux

open scoped MatrixGroups

theorem order_pos (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < specialValueOrder M :=
  sub_pos.mpr hM.2

theorem small_root_properties (N : ℝ) (hN : 0 < N) :
    let ε := (N + 2 - Real.sqrt (N ^ 2 + 4 * N)) / 2
    0 < ε ∧ ε < 1 ∧ ε ^ 2 - (N + 2) * ε + 1 = 0 := by
  have hD : 0 ≤ N ^ 2 + 4 * N := by positivity
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg (N ^ 2 + 4 * N)
  have hlo : N < Real.sqrt (N ^ 2 + 4 * N) :=
    (sq_lt_sq₀ hN.le hs0).mp (by nlinarith)
  have hhi : Real.sqrt (N ^ 2 + 4 * N) < N + 2 :=
    (sq_lt_sq₀ hs0 (by linarith)).mp (by nlinarith)
  dsimp
  exact ⟨by linarith, by linarith, by nlinarith⟩

/-- The discriminant lies strictly between the consecutive integer squares (N+1)² and (N+2)². -/
theorem discriminant_not_square (N : ℤ) (hN : 0 < N) :
    ¬ IsSquare (N ^ 2 + 4 * N) := by
  rintro ⟨k, hk⟩
  have habs : |k| ^ 2 = N ^ 2 + 4 * N := by
    rw [sq_abs]
    nlinarith [hk]
  have hlo : N + 1 < |k| :=
    (sq_lt_sq₀ (by omega : 0 ≤ N + 1) (abs_nonneg k)).mp (by nlinarith)
  have hhi : |k| < N + 2 :=
    (sq_lt_sq₀ (abs_nonneg k) (by omega : 0 ≤ N + 2)).mp (by nlinarith)
  omega

theorem small_root_irrational (N : ℤ) (hN : 0 < N) :
    Irrational (((N : ℝ) + 2 - Real.sqrt ((N : ℝ) ^ 2 + 4 * (N : ℝ))) / 2) := by
  have hs : Irrational (Real.sqrt (((N ^ 2 + 4 * N : ℤ) : ℝ))) :=
    (irrational_sqrt_intCast_iff_of_nonneg (by nlinarith)).mpr
      (discriminant_not_square N hN)
  have hs' : Irrational (Real.sqrt ((N : ℝ) ^ 2 + 4 * (N : ℝ))) := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using hs
  convert (hs'.intCast_sub (N + 2)).div_intCast (m := 2) (by norm_num) using 1
  push_cast
  ring

end SICLean.L4.G2RepellingGeometryAux
