import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! Auxiliary finite algebra for the q-binomial identities. -/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.FiniteQBinomialAux

/-- Extract the first factor, retaining the shift in the base variable. -/
theorem product_prepend {R : Type*} [CommRing R] (t q : R) (n : ℕ) :
    (∏ r ∈ Finset.range (n + 1), (1 - q ^ r * t)) =
      (1 - t) * ∏ r ∈ Finset.range n, (1 - q ^ r * (q * t)) := by
  rw [Finset.prod_range_succ']
  simp only [pow_zero, one_mul, pow_succ, mul_assoc]
  exact mul_comm _ _

/-- The numerator products obey the same denominator-cleared Pascal identity. -/
theorem numerator_pascal {K : Type*} [Field K] (q : K) (hq : q ≠ 0)
    (i j : ℕ) :
    (1 - q ^ (j + 1)) * (∏ r ∈ Finset.range j, (1 - q⁻¹ ^ r * q ^ i)) +
        q ^ (j + 1) * (∏ r ∈ Finset.range (j + 1), (1 - q⁻¹ ^ r * q ^ i)) =
      ∏ r ∈ Finset.range (j + 1), (1 - q⁻¹ ^ r * q ^ (i + 1)) := by
  rw [product_prepend (q ^ (i + 1)) q⁻¹ j,
    Finset.prod_range_succ (fun r => 1 - q⁻¹ ^ r * q ^ i) j]
  have hi : q⁻¹ * q ^ (i + 1) = q ^ i := by
    rw [pow_succ, mul_comm (q ^ i) q, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  rw [hi]
  have hj : q ^ (j + 1) * q⁻¹ ^ j = q := by
    rw [pow_succ, mul_right_comm, ← mul_pow, mul_inv_cancel₀ hq, one_pow, one_mul]
  have hh : q ^ (j + 1) * (q⁻¹ ^ j * q ^ i) = q ^ (i + 1) := by
    rw [← mul_assoc, hj, pow_succ, mul_comm]
  linear_combination -(∏ r ∈ Finset.range j, (1 - q⁻¹ ^ r * q ^ i)) * hh

/-- A finite product expansion from the shifted coefficient recurrence. -/
theorem product_expansion {R : Type*} [CommRing R]
    (q : R) (c : ℕ → ℕ → R)
    (hzero : ∀ n, c n 0 = 1)
    (hoff : ∀ n a, n < a → c n a = 0)
    (hsucc : ∀ n a, c (n + 1) (a + 1) =
      q ^ (a + 1) * c n (a + 1) - q ^ a * c n a)
    (t : R) (n : ℕ) :
    (∏ r ∈ Finset.range n, (1 - q ^ r * t)) =
      ∑ a ∈ Finset.range (n + 1), c n a * t ^ a := by
  induction n generalizing t with
  | zero => simp [hzero]
  | succ n ih =>
      rw [product_prepend, ih]
      have hshift :
          1 + (∑ a ∈ Finset.range (n + 1), c n (a + 1) * (q * t) ^ (a + 1)) =
            ∑ a ∈ Finset.range (n + 1), c n a * (q * t) ^ a := by
        calc
          _ = ∑ a ∈ Finset.range (n + 2), c n a * (q * t) ^ a := by
            rw [Finset.sum_range_succ' (fun a => c n a * (q * t) ^ a) (n + 1)]
            simp [hzero, add_comm]
          _ = _ := by
            rw [Finset.sum_range_succ (fun a => c n a * (q * t) ^ a) (n + 1)]
            simp [hoff n (n + 1) (Nat.lt_succ_self n)]
      rw [Finset.sum_range_succ' (fun a => c (n + 1) a * t ^ a) (n + 1)]
      simp only [pow_zero, mul_one, hzero]
      have hterms :
          (∑ a ∈ Finset.range (n + 1), c (n + 1) (a + 1) * t ^ (a + 1)) =
            (∑ a ∈ Finset.range (n + 1), c n (a + 1) * (q * t) ^ (a + 1)) -
              t * (∑ a ∈ Finset.range (n + 1), c n a * (q * t) ^ a) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hsucc]
        simp only [mul_pow, pow_succ]
        ring
      rw [hterms]
      linear_combination -hshift

end SICLean.L5.FiniteQBinomialAux
