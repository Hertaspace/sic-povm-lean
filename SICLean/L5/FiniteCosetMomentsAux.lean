import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Division-free conversion of binomial moments to monomial moments

The identity `x * choose x r = r * choose x r + (r + 1) * choose x (r + 1)`
keeps every index in the box below the target multi-index. Strong induction
on the total degree therefore works over any commutative semiring.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SICLean.L5.FiniteCosetMomentsAux

lemma nat_mul_choose (x r : ℕ) :
    x * x.choose r = r * x.choose r + (r + 1) * x.choose (r + 1) := by
  by_cases h : r ≤ x
  · have hrec := Nat.choose_succ_right_eq x r
    have hx : x = r + (x - r) := (Nat.add_sub_of_le h).symm
    nlinarith
  · have hx : x < r := Nat.lt_of_not_ge h
    simp [Nat.choose_eq_zero_of_lt hx,
      Nat.choose_eq_zero_of_lt (lt_trans hx (Nat.lt_succ_self r))]

lemma cast_mul_choose {k : Type*} [CommSemiring k] (x r : ℕ) :
    (x : k) * (x.choose r : k) =
      (r : k) * (x.choose r : k) + (r + 1 : k) * (x.choose (r + 1) : k) := by
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    congrArg (fun n : ℕ => (n : k)) (nat_mul_choose x r)

lemma product_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : Type*} [CommMonoid k] (v : ι → ℕ → k) (j : ι → ℕ) (i : ι) (n : ℕ) :
    (∏ a, v a (Function.update j i n a)) =
      v i n * ∏ a ∈ Finset.univ.erase i, v a (j a) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun a => v a (Function.update j i n a))
    (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]

lemma binomial_step {d : ℕ} {k : Type*} [CommSemiring k]
    (x r : Fin d → ℕ) (i : Fin d) :
    (x i : k) * (∏ a, (Nat.choose (x a) (r a) : k)) =
      (r i : k) * (∏ a, (Nat.choose (x a) (r a) : k)) +
      (r i + 1 : k) * (∏ a, (Nat.choose (x a) (Function.update r i (r i + 1) a) : k)) := by
  classical
  rw [product_update (fun a n => (Nat.choose (x a) n : k)) r i (r i + 1)]
  rw [← Finset.mul_prod_erase Finset.univ (fun a => (Nat.choose (x a) (r a) : k))
    (Finset.mem_univ i)]
  rw [← mul_assoc, cast_mul_choose]
  ring

lemma monomial_step {d : ℕ} {k : Type*} [CommSemiring k]
    (x : Fin d → k) (j : Fin d → ℕ) (i : Fin d) (hi : j i ≠ 0) :
    (∏ a, x a ^ j a) =
      x i * (∏ a, x a ^ Function.update j i (j i - 1) a) := by
  classical
  rw [product_update (fun a n => x a ^ n) j i (j i - 1)]
  rw [← Finset.mul_prod_erase Finset.univ (fun a => x a ^ j a)
    (Finset.mem_univ i)]
  rw [← mul_assoc, ← pow_succ']
  congr 2
  exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)).symm

lemma monomial_moment_of_binomial_box
    {α : Type*} [Fintype α] {d : ℕ} {k : Type*} [CommSemiring k]
    (x : α → Fin d → ℕ) (g : α → k) (j : Fin d → ℕ)
    (hbinomial : ∀ r : Fin d → ℕ, r ≤ j →
      ∑ u, g u * (∏ a, (Nat.choose (x u a) (r a) : k)) = 0) :
    ∑ u, g u * (∏ a, (x u a : k) ^ j a) = 0 := by
  classical
  induction hn : (∑ a, j a) using Nat.strong_induction_on generalizing g j with
  | h n ih =>
    by_cases hj0 : ∀ a, j a = 0
    · simpa only [hj0, Nat.choose_zero_right, Nat.cast_one, pow_zero,
        Finset.prod_const_one, mul_one] using hbinomial j le_rfl
    obtain ⟨i, hi⟩ := not_forall.mp hj0
    let j' : Fin d → ℕ := Function.update j i (j i - 1)
    have hj' : j' ≤ j := by
      intro a
      by_cases ha : a = i
      · subst a
        simp [j']
      · simp [j', ha]
    have hlt : (∑ a, j' a) < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun a _ => hj' a) ⟨i, Finset.mem_univ _, ?_⟩
      simp only [j', Function.update_self]
      omega
    have hbinomial' : ∀ r : Fin d → ℕ, r ≤ j' →
        ∑ u, (g u * (x u i : k)) * (∏ a, (Nat.choose (x u a) (r a) : k)) = 0 := by
      intro r hr
      have hrj : r ≤ j := le_trans hr hj'
      have hrsj : Function.update r i (r i + 1) ≤ j := by
        intro a
        by_cases ha : a = i
        · subst a
          simp only [Function.update_self]
          have hri := hr i
          simp only [j', Function.update_self] at hri
          omega
        · simpa [ha] using hrj a
      calc
        _ = ∑ u, ((r i : k) * (g u * (∏ a, (Nat.choose (x u a) (r a) : k))) +
            (r i + 1 : k) * (g u * (∏ a,
              (Nat.choose (x u a) (Function.update r i (r i + 1) a) : k)))) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [mul_assoc, binomial_step]
          ring
        _ = (r i : k) * (∑ u, g u * (∏ a, (Nat.choose (x u a) (r a) : k))) +
            (r i + 1 : k) * (∑ u, g u * (∏ a,
              (Nat.choose (x u a) (Function.update r i (r i + 1) a) : k))) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = 0 := by rw [hbinomial r hrj, hbinomial _ hrsj]; simp
    have hrec := ih (∑ a, j' a) hlt (fun u => g u * (x u i : k)) j' hbinomial' rfl
    calc
      _ = ∑ u, (g u * (x u i : k)) * (∏ a, (x u a : k) ^ j' a) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [monomial_step (fun a => (x u a : k)) j i hi]
        exact (mul_assoc _ _ _).symm
      _ = 0 := hrec

end SICLean.L5.FiniteCosetMomentsAux
