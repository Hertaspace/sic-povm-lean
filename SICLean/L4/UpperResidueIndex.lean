import SICLean.L4.UpperContourGeometry

set_option autoImplicit false

/-!
# The finite index partition, before any infinite sum

Finite partitioning is
completed before absolute convergence is used to pass to infinite sums.
The owner of (K,J) is an explicit integer remainder, not a choice of a
witness. The finite square uses the same integer radius R.
All auxiliary declarations in this file belong to this namespace.
[RW26, p. 29, Appendix A.2].
The index is organized by this finite partition.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperResidueIndex

/-- Explicit owner m = K+a(J+n) mod c, including c=1. -/
def owner (M : SL(2, ℤ)) (n : ℤ) (k : ℕ × ℕ) : ℕ :=
  (((k.1 : ℤ) + M 0 0 * ((k.2 : ℤ) + n)) % M 1 0).toNat

/-- The unfiltered finite square 0 ≤ K,J < cR. -/
def square (M : SL(2, ℤ)) (R : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range ((M 1 0).toNat * R)).product
    (Finset.range ((M 1 0).toNat * R))

def squareSum (M : SL(2, ℤ)) (R : ℕ) (f : ℕ × ℕ → ℂ) : ℂ :=
  ∑ k ∈ square M R, f k

def classTerm (M : SL(2, ℤ)) (m n : ℤ) (f : ℕ × ℕ → ℂ)
    (k : ℕ × ℕ) : ℂ :=
  if k ∈ modularPhiPoleLabels M (m + 1) n then f k else 0

/--
Coprimality. [RW26, p. 29]. Elementary SL₂ arithmetic behind the reindexing.
-/
theorem lower_row_coprime (M : SL(2, ℤ)) :
    Int.gcd (M 1 0) (M 1 1) = 1 := by
  exact Int.isCoprime_iff_gcd_eq_one.mp (M.isCoprime_row 1)

/--
[RW26, p. 29].
-/
theorem owner_lt (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n : ℤ) (k : ℕ × ℕ) :
    owner M n k < (M 1 0).toNat := by
  unfold owner
  have hnonneg := Int.emod_nonneg
    ((k.1 : ℤ) + M 0 0 * ((k.2 : ℤ) + n)) (ne_of_gt hM)
  have hlt := Int.emod_lt_of_pos
    ((k.1 : ℤ) + M 0 0 * ((k.2 : ℤ) + n)) hM
  omega

/--
[RW26, p. 29].
The inverse of d modulo c is a, since ad-bc=1.
-/
theorem owner_congruence (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n : ℤ)
    (k : ℕ × ℕ) :
    Int.ModEq (M 1 0) ((k.2 : ℤ) + M 1 1 * (k.1 : ℤ))
      (M 1 1 * (owner M n k : ℤ) - n) := by
  have hcast : (owner M n k : ℤ) =
      ((k.1 : ℤ) + M 0 0 * ((k.2 : ℤ) + n)) % M 1 0 := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hM))
  rw [hcast, Int.modEq_iff_dvd]
  refine ⟨M 0 1 * ((k.2 : ℤ) + n) - M 1 1 *
    (((k.1 : ℤ) + M 0 0 * ((k.2 : ℤ) + n)) / M 1 0), ?_⟩
  have hdiv := Int.emod_add_mul_ediv
    ((k.1 : ℤ) + M 0 0 * ((k.2 : ℤ) + n)) (M 1 0)
  linear_combination M 1 1 * hdiv + ((k.2 : ℤ) + n) * det_coe_int M

/--
[RW26, p. 29].
Exactly one representative, rather than c copies.
-/
theorem unique_class (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n : ℤ) (k : ℕ × ℕ) :
    ∃! m : Fin (M 1 0).toNat,
      k ∈ modularPhiPoleLabels M ((m.val : ℤ) + 1) n := by
  refine ⟨⟨owner M n k, owner_lt M hM n k⟩, ?_, ?_⟩
  · simpa only [modularPhiPoleLabels, Set.mem_ofPred_eq, add_sub_cancel_right]
      using owner_congruence M hM n k
  · intro m hm
    have hlabel : Int.ModEq (M 1 0) ((k.2 : ℤ) + M 1 1 * (k.1 : ℤ))
        (M 1 1 * (m.val : ℤ) - n) := by
      simpa only [modularPhiPoleLabels, Set.mem_ofPred_eq, add_sub_cancel_right] using hm
    have hmul : Int.ModEq (M 1 0) (M 1 1 * (m.val : ℤ))
        (M 1 1 * (owner M n k : ℤ)) := by
      simpa only [sub_add_cancel] using
        (hlabel.symm.trans (owner_congruence M hM n k)).add_right n
    have hmod : Int.ModEq (M 1 0) (m.val : ℤ) (owner M n k : ℤ) := by
      simpa only [lower_row_coprime, Nat.cast_one, Int.ediv_one] using
        hmul.cancel_left_div_gcd hM
    have hmlt : (m.val : ℤ) < M 1 0 := by
      have := m.isLt
      omega
    have holt : (owner M n k : ℤ) < M 1 0 := by
      have := owner_lt M hM n k
      omega
    rw [Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg _) hmlt,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) holt] at hmod
    exact Fin.ext (Int.natCast_inj.mp hmod)

/-- [RW26, p. 29]. -/
theorem owner_eq_iff (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n : ℤ)
    (k : ℕ × ℕ) (m : ℕ) (hm : m < (M 1 0).toNat) :
    owner M n k = m ↔ k ∈ modularPhiPoleLabels M ((m : ℤ) + 1) n := by
  have howner : k ∈ modularPhiPoleLabels M ((owner M n k : ℤ) + 1) n := by
    simpa only [modularPhiPoleLabels, Set.mem_ofPred_eq, add_sub_cancel_right]
      using owner_congruence M hM n k
  constructor
  · intro heq
    simpa only [heq] using howner
  · intro hlabel
    obtain ⟨j, _, huniq⟩ := unique_class M hM n k
    have ho := huniq (⟨owner M n k, owner_lt M hM n k⟩ : Fin (M 1 0).toNat) howner
    have hm' := huniq (⟨m, hm⟩ : Fin (M 1 0).toNat) hlabel
    exact congrArg Fin.val (ho.trans hm'.symm)

/--
[RW26, p. 29]. Uses actual finite labels, not a new pole set.
-/
theorem mem_boxLabels_iff_owner (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n : ℤ) (m R : ℕ) (hm : m < (M 1 0).toNat) (k : ℕ × ℕ) :
    k ∈ UpperContour.boxLabels M (m : ℤ) n R ↔
      k ∈ square M R ∧ owner M n k = m := by
  change k ∈ (square M R).filter _ ↔ _
  rw [Finset.mem_filter, owner_eq_iff M hM n k m hm]

/--
[RW26, p. 29].
Finite indicator identity with coefficient one.
-/
theorem sum_classTerm (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n : ℤ)
    (f : ℕ × ℕ → ℂ) (k : ℕ × ℕ) :
    (∑ m ∈ Finset.range (M 1 0).toNat, classTerm M (m : ℤ) n f k) = f k := by
  have howner : k ∈ modularPhiPoleLabels M ((owner M n k : ℤ) + 1) n :=
    (owner_eq_iff M hM n k (owner M n k) (owner_lt M hM n k)).mp rfl
  calc
    _ = classTerm M (owner M n k : ℤ) n f k := by
      apply Finset.sum_eq_single (owner M n k)
      · intro m hm hne
        have hnot : k ∉ modularPhiPoleLabels M ((m : ℤ) + 1) n := by
          rw [← owner_eq_iff M hM n k m (Finset.mem_range.mp hm)]
          exact Ne.symm hne
        exact if_neg hnot
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (owner_lt M hM n k)))
    _ = f k := if_pos howner

/--
[RW26, p. 29]. The decisive finite identity, with no extra c.
-/
theorem sum_boxes_eq_square (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n : ℤ)
    (R : ℕ) (f : ℕ × ℕ → ℂ) :
    (∑ m ∈ Finset.range (M 1 0).toNat,
      ∑ k ∈ UpperContour.boxLabels M (m : ℤ) n R, f k) = squareSum M R f := by
  calc
    _ = ∑ m ∈ Finset.range (M 1 0).toNat,
        ∑ k ∈ square M R, classTerm M (m : ℤ) n f k := by
      apply Finset.sum_congr rfl
      intro m hm
      change (∑ k ∈ (square M R).filter _, f k) = _
      rw [Finset.sum_filter]
      rfl
    _ = ∑ k ∈ square M R,
        ∑ m ∈ Finset.range (M 1 0).toNat, classTerm M (m : ℤ) n f k :=
      Finset.sum_comm
    _ = squareSum M R f :=
      Finset.sum_congr rfl (fun k _ => sum_classTerm M hM n f k)

/--
[RW26, p. 29]. This also includes the empty R=0 square.
-/
theorem square_mono (M : SL(2, ℤ)) : Monotone (square M) := by
  intro R S hRS ⟨K, J⟩ hk
  simp only [square, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range] at hk ⊢
  exact ⟨hk.1.trans_le (Nat.mul_le_mul_left _ hRS),
    hk.2.trans_le (Nat.mul_le_mul_left _ hRS)⟩

/--
[RW26, p. 29].
No convergence or analytic claim is built into this square.
-/
theorem square_exhaust (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : ℕ × ℕ) :
    ∀ᶠ R : ℕ in atTop, k ∈ square M R := by
  rcases k with ⟨K, J⟩
  have hc : 0 < (M 1 0).toNat := by omega
  filter_upwards [eventually_ge_atTop (max K J + 1)] with R hR
  have hle : R ≤ (M 1 0).toNat * R := Nat.le_mul_of_pos_left R hc
  simp only [square, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  constructor <;> omega

/--
[RW26, p. 28, p. 29, (55), (56), (58)]. Restricting an absolutely summable family is legitimate.
-/
theorem summable_norm_classTerm (M : SL(2, ℤ)) (m n : ℤ)
    (f : ℕ × ℕ → ℂ) (hf : Summable (fun k => ‖f k‖)) :
    Summable (fun k => ‖classTerm M m n f k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hf
  intro k
  by_cases hk : k ∈ modularPhiPoleLabels M (m + 1) n <;>
    simp [classTerm, hk]

/--
[RW26, p. 28, p. 29, (55), (56), (58)].
First take finite squares, then the limit along integer R.
-/
theorem squareSum_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (f : ℕ × ℕ → ℂ) (hf : Summable (fun k => ‖f k‖)) :
    Tendsto (fun R : ℕ => squareSum M R f) atTop (𝓝 (∑' k, f k)) := by
  have hsq : Tendsto (square M) atTop atTop :=
    (square_mono M).tendsto_atTop_finset fun k =>
      (square_exhaust M hM k).exists
  simpa only [squareSum, Function.comp_def] using
    hf.of_norm.hasSum.comp hsq

/--
[RW26, p. 28, p. 29, (55), (56), (58)].
Both iterated sums are justified by the absolute product-index sum.
-/
theorem tsum_orders (f : ℕ × ℕ → ℂ) (hf : Summable (fun k => ‖f k‖)) :
    (∑' k, f k) = (∑' K, ∑' J, f (K, J)) ∧
      (∑' K, ∑' J, f (K, J)) = (∑' J, ∑' K, f (K, J)) := by
  have h : Summable f := hf.of_norm
  refine ⟨h.tsum_prod, ?_⟩
  exact (Summable.tsum_comm (f := fun K J => f (K, J)) h).symm

#print owner
#print square
#check UpperContour.mem_boxLabels
#check unique_class
#check sum_boxes_eq_square
#check squareSum_tendsto
#check tsum_orders

end SICLean.L4.UpperResidueIndex
