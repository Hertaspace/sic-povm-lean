import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

/-! Elementary arithmetic for the quadratic field realizing a positive period. -/

noncomputable section

namespace SICLean.L3.PeriodDataExistenceAux

open Polynomial

/-- The period polynomial over the rationals. -/
def periodPolynomial (N : ℕ) : ℚ[X] :=
  X ^ 2 - C ((N : ℚ) + 2) * X + 1

theorem periodPolynomial_monic (N : ℕ) : (periodPolynomial N).Monic := by
  have h : periodPolynomial N = X ^ 2 - (C ((N : ℚ) + 2) * X - 1) := by
    unfold periodPolynomial
    ring
  rw [h]
  apply monic_X_pow_sub
  compute_degree!

theorem periodPolynomial_natDegree (N : ℕ) : (periodPolynomial N).natDegree = 2 := by
  unfold periodPolynomial
  compute_degree!

/-- An integral root would divide the constant coefficient, hence be ±1. -/
theorem periodPolynomial_irreducible (N : ℕ) (hN : 0 < N) :
    Irreducible (periodPolynomial N) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [periodPolynomial_natDegree]
  intro q hq
  let p : ℤ[X] := X ^ 2 - C ((N : ℤ) + 2) * X + 1
  have hp : p.Monic := by
    have h : p = X ^ 2 - (C ((N : ℤ) + 2) * X - 1) := by
      dsimp [p]
      ring
    rw [h]
    apply monic_X_pow_sub
    compute_degree!
  have hq' : aeval q p = 0 := by
    simpa [p, periodPolynomial, IsRoot, aeval_def, eval₂_natCast] using hq
  obtain ⟨z, hqz, hz⟩ := exists_integer_of_is_root_of_monic hp hq'
  have hz' : z ∣ (1 : ℤ) := by simpa [p] using hz
  rcases Int.isUnit_eq_one_or (isUnit_of_dvd_one hz') with hz1 | hz1
  · subst z
    have hq1 : q = 1 := by simpa using hqz
    subst q
    simp [periodPolynomial, IsRoot] at hq
    have hzero : (N : ℚ) = 0 := by linarith
    exact (Nat.ne_of_gt hN) (by exact_mod_cast hzero)
  · subst z
    have hq1 : q = -1 := by simpa using hqz
    subst q
    simp [periodPolynomial, IsRoot] at hq
    have hnonneg : (0 : ℚ) ≤ N := Nat.cast_nonneg N
    linarith

/-- The larger real root of the period polynomial. -/
def epsilonPlus (N : ℕ) : ℝ :=
  ((N : ℝ) + 2 + Real.sqrt ((N : ℝ) * ((N : ℝ) + 4))) / 2

/-- The conjugate real root of the period polynomial. -/
def epsilonMinus (N : ℕ) : ℝ :=
  ((N : ℝ) + 2 - Real.sqrt ((N : ℝ) * ((N : ℝ) + 4))) / 2

theorem epsilonPlus_isRoot (N : ℕ) :
    (periodPolynomial N).eval₂ (algebraMap ℚ ℝ) (epsilonPlus N) = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ (N : ℝ) * ((N : ℝ) + 4) by positivity)
  simp only [periodPolynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_one, map_add, map_natCast, map_ofNat, eval₂_natCast,
    eval₂_ofNat]
  dsimp [epsilonPlus]
  nlinarith

theorem epsilonMinus_isRoot (N : ℕ) :
    (periodPolynomial N).eval₂ (algebraMap ℚ ℝ) (epsilonMinus N) = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ (N : ℝ) * ((N : ℝ) + 4) by positivity)
  simp only [periodPolynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_one, map_add, map_natCast, map_ofNat, eval₂_natCast,
    eval₂_ofNat]
  dsimp [epsilonMinus]
  nlinarith

theorem epsilonPlus_gt_one (N : ℕ) (hN : 0 < N) : 1 < epsilonPlus N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := Real.sqrt_nonneg ((N : ℝ) * ((N : ℝ) + 4))
  dsimp [epsilonPlus]
  linarith

theorem epsilonMinus_eq_inv (N : ℕ) : epsilonMinus N = (epsilonPlus N)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have hs := Real.sq_sqrt (show 0 ≤ (N : ℝ) * ((N : ℝ) + 4) by positivity)
  dsimp [epsilonMinus, epsilonPlus]
  nlinarith

end SICLean.L3.PeriodDataExistenceAux
