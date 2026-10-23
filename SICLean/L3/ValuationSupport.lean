import SICLean.L3.FiniteSystem

set_option autoImplicit false

noncomputable section

namespace SICLean.L3.ValuationSupport

open scoped BigOperators

/-- Split off zero and the nonzero fixed points of negation, then choose
one representative of each remaining pair. -/
theorem exists_neg_pair_sum {G R : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G] [CommRing R]
    (f : G → R) (hf : ∀ s, f (-s) = f s) :
    ∃ T : Finset G,
      (∀ s ∈ T, s + s ≠ 0) ∧
      (∀ s, s + s ≠ 0 → (s ∈ T ↔ -s ∉ T)) ∧
      (∑ s : G, f s) =
        f 0 + (∑ h : {h : G // h ≠ 0 ∧ h + h = 0}, f h.val) +
          2 * ∑ s ∈ T, f s := by
  classical
  let : LinearOrder G := LinearOrder.lift' (Fintype.equivFin G)
    (Fintype.equivFin G).injective
  let T : Finset G := Finset.univ.filter (fun s : G => s < -s)
  let U : Finset G := Finset.univ.filter (fun s : G => -s < s)
  let A : Finset G := Finset.univ.filter (fun s : G => s + s = 0)
  have hT : ∀ s ∈ T, s + s ≠ 0 := by
    intro s hs he
    have hlt : s < -s := (Finset.mem_filter.mp hs).2
    have heq : s = -s := eq_neg_iff_add_eq_zero.mpr he
    exact (ne_of_lt hlt) heq
  have hpair : ∀ s, s + s ≠ 0 → (s ∈ T ↔ -s ∉ T) := by
    intro s hs
    have hne : s ≠ -s := fun he => hs (eq_neg_iff_add_eq_zero.mp he)
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, neg_neg]
    exact lt_iff_not_ge.trans (not_congr (le_iff_lt_or_eq.trans
      (or_iff_left hne.symm)))
  have hcov :
      Finset.univ.filter (fun s : G => ¬s + s = 0) = T ∪ U := by
    ext s
    simp only [T, U, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [← eq_neg_iff_add_eq_zero]
    exact ne_iff_lt_or_gt
  have hdis : Disjoint T U := by
    refine Finset.disjoint_left.mpr ?_
    intro s hs ht
    exact lt_asymm (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2
  have hsum : (∑ s ∈ U, f s) = ∑ s ∈ T, f s := by
    apply Finset.sum_bijective (fun s : G => -s) neg_involutive.bijective
    · intro s
      simp only [U, T, Finset.mem_filter, Finset.mem_univ, true_and, neg_neg]
    · intro s hs
      exact (hf s).symm
  have hA : (∑ s ∈ A, f s) =
      f 0 + (∑ h : {h : G // h ≠ 0 ∧ h + h = 0}, f h.val) := by
    have hzero : (0 : G) ∈ A := by simp [A]
    have hrest : (∑ s ∈ A.erase 0, f s) =
        ∑ h : {h : G // h ≠ 0 ∧ h + h = 0}, f h.val := by
      exact Finset.sum_subtype (A.erase 0) (by intro s; simp [A]) f
    have ha := Finset.sum_erase_add A f hzero
    rw [hrest] at ha
    simpa only [add_comm] using ha.symm
  refine ⟨T, hT, hpair, ?_⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s : G => s + s = 0) f
  rw [hcov, Finset.sum_union hdis, hsum] at hsplit
  change (∑ s ∈ A, f s) + ((∑ s ∈ T, f s) + ∑ s ∈ T, f s) =
    ∑ s : G, f s at hsplit
  rw [hA, ← two_mul] at hsplit
  exact hsplit.symm

variable {L : Type*} [Field L] (v : AddValuation L (WithTop ℝ))

theorem value_pow_eq_one {x : L} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    v x = 0 := by
  have hxn : x ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hx
    exact zero_ne_one hx
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hxn)
  have hv : n • v x = 0 := by rw [← v.map_pow, hx, v.map_one]
  rw [← hr, ← WithTop.coe_nsmul, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hv
  have hr0 := (nsmul_eq_zero_iff.mp hv).resolve_right hn
  rw [← hr, hr0, WithTop.coe_zero]

theorem natCast_nonneg (n : ℕ) : 0 ≤ v (n : L) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_le_add ih (by simp)

theorem nonneg_of_square {x : L} (h : 0 ≤ v (x ^ 2)) : 0 ≤ v x := by
  by_cases ht : v x = ⊤
  · simp [ht]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
  rw [v.map_pow, ← hr, ← WithTop.coe_nsmul, ← WithTop.coe_zero,
    WithTop.coe_le_coe] at h
  rw [two_nsmul] at h
  rw [← hr, ← WithTop.coe_zero, WithTop.coe_le_coe]
  linarith

/-- Real coordinates are used only after proving that the field element is nonzero. -/
def realValue (x : L) : ℝ := (v x).untop₀

theorem coe_realValue {x : L} (hx : x ≠ 0) :
    (realValue v x : WithTop ℝ) = v x :=
  WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hx)

theorem realValue_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    realValue v (x * y) = realValue v x + realValue v y := by
  exact congrArg WithTop.untop₀ (v.map_mul x y) |>.trans
    (WithTop.untop₀_add (v.ne_top_iff.mpr hx) (v.ne_top_iff.mpr hy))

theorem realValue_pow {x : L} (hx : x ≠ 0) (n : ℕ) :
    realValue v (x ^ n) = n • realValue v x := by
  induction n with
  | zero => simp [realValue]
  | succ n ih => rw [pow_succ, realValue_mul v (pow_ne_zero _ hx) hx, ih, succ_nsmul]

end SICLean.L3.ValuationSupport
