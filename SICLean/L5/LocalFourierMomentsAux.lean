import SICLean.L5.LocalCyclotomicValuation

set_option autoImplicit false

/-!
Finite valuation and reduction helpers for `LocalFourierMoments`.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalFourierMomentsAux

open LocalFourierSetup FiniteCosetMoments FiniteQBinomial

variable {L : Type*} [Field L]

/-- Products of integral elements are integral, including the empty product. -/
theorem value_prod_nonneg {ι : Type*} (v : AddValuation L (WithTop ℝ))
    (S : Finset ι) (f : ι → L) (hf : ∀ i ∈ S, 0 ≤ v (f i)) :
    0 ≤ v (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi, v.map_mul]
      exact add_nonneg (hf i (Finset.mem_insert_self i S))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Finite real valuations of the factors add to the valuation of the product. -/
theorem value_prod_eq_sum {ι : Type*} (v : AddValuation L (WithTop ℝ))
    (S : Finset ι) (f : ι → L) (w : ι → ℝ)
    (hf : ∀ i ∈ S, v (f i) = (w i : WithTop ℝ)) :
    v (∏ i ∈ S, f i) = ((∑ i ∈ S, w i : ℝ) : WithTop ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul,
        hf i (Finset.mem_insert_self i S),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), WithTop.coe_add]

/-- The totalized reduction map commutes with sums on integral inputs. -/
theorem reduce_sum {ι : Type*} (v : AddValuation L (WithTop ℝ))
    (S : Finset ι) (f : ι → L) (hf : ∀ i ∈ S, 0 ≤ v (f i)) :
    reduce v (∑ i ∈ S, f i) = ∑ i ∈ S, reduce v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [reduce_eq_residue v 0 (by simp)]
      change IsLocalRing.residue (integers v) 0 = 0
      exact map_zero _
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        reduce_add v _ _ (hf i (Finset.mem_insert_self i S))
          (v.map_le_sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- The totalized reduction map commutes with products on integral inputs. -/
theorem reduce_prod {ι : Type*} (v : AddValuation L (WithTop ℝ))
    (S : Finset ι) (f : ι → L) (hf : ∀ i ∈ S, 0 ≤ v (f i)) :
    reduce v (∏ i ∈ S, f i) = ∏ i ∈ S, reduce v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      rw [reduce_eq_residue v 1 (by simp)]
      change IsLocalRing.residue (integers v) 1 = 1
      exact map_one _
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        reduce_mul v _ _ (hf i (Finset.mem_insert_self i S))
          (value_prod_nonneg v S f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- Reducing natural frequency coordinates modulo the order preserves the kernel. -/
theorem pow_dot_natCast {q d : ℕ} (z : L) (hz : z ^ q = 1)
    (x : Fin d → ZMod q) (a : Fin d → ℕ) :
    z ^ (∑ i, a i * (x i).val) =
      z ^ (∑ i, (x i).val * (a i : ZMod q).val) := by
  simp only [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.mul_comm (x i).val, pow_mul, pow_mul, ZMod.val_natCast,
    ← pow_eq_pow_mod (a i) hz]

/-- An index above the group exponent makes every binomial weight zero. -/
theorem globalBinomialMoment_eq_zero_of_large_index
    {p s d : ℕ} [Fact p.Prime] {k : Type*} [CommRing k]
    (f : Point p s d → k) (j : Fin d → ℕ) (i : Fin d) (hi : p ^ s ≤ j i) :
    globalBinomialMoment f j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  have hlt : (x i).val < j i := (ZMod.val_lt (x i)).trans_le hi
  have hw : binomialWeight k (fun i => (x i).val) j = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hlt]
  rw [hw, mul_zero]

end SICLean.L5.LocalFourierMomentsAux
