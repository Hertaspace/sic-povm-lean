import SICLean.L2a.Main

set_option autoImplicit false

/-!
# Finite metric groups, with the normalization of [RW26]

Source: [RW26, Def. 1].
The nonvanishing field below is the requirement that the Gaussian takes
values in ℂˣ. The formulas use its underlying ℂ-valued function.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2b

variable {A : Type*} [AddCommGroup A]

local instance : DecidableEq A := Classical.decEq A

/-- Polarization of a Gaussian, not a separately chosen bicharacter. -/
def metricPairing (q : A → ℂ) (x y : A) : ℂ :=
  q (x + y) / (q x * q y)

/-- [RW26, Def. 1]. These hypotheses belong to the general abstract theorem.
For the concrete group below every field is a theorem, never an input on E. -/
structure IsMetricGaussian (q : A → ℂ) : Prop where
  nonzero : ∀ x, q x ≠ 0
  even : ∀ x, q (-x) = q x
  add_left : ∀ x y z,
    metricPairing q (x + y) z = metricPairing q x z * metricPairing q y z
  add_right : ∀ x y z,
    metricPairing q x (y + z) = metricPairing q x y * metricPairing q x z
  nondegenerate : ∀ x, (∀ y, metricPairing q x y = 1) → x = 0

/-- The ℂˣ-valued version of the same Gaussian, with no extra data. -/
def gaussianUnits {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) : ℂˣ :=
  Units.mk0 (q x) (hq.nonzero x)

theorem metric_zero {q : A → ℂ} (hq : IsMetricGaussian q) : q 0 = 1 := by
  have hp := hq.add_right 0 0 0
  simp only [add_zero] at hp
  have hv : metricPairing q 0 0 = (q 0)⁻¹ := by
    simp only [metricPairing, add_zero]
    field_simp
  rw [hv] at hp
  have key : (q 0)⁻¹ * (1 - (q 0)⁻¹) = 0 := by
    have h : (q 0)⁻¹ * (1 - (q 0)⁻¹) = (q 0)⁻¹ - (q 0)⁻¹ * (q 0)⁻¹ := by ring
    rw [h, ← hp, sub_self]
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (inv_ne_zero (hq.nonzero 0))
  · exact inv_eq_one.mp (sub_eq_zero.mp h).symm

theorem metric_pairing_symmetric (q : A → ℂ) (x y : A) :
    metricPairing q x y = metricPairing q y x := by
  simp only [metricPairing]
  rw [add_comm y x, mul_comm (q y) (q x)]

variable [Fintype A]

/-- The positive real square root, embedded in ℂ. -/
def sqrtCard (A : Type*) [Fintype A] : ℂ :=
  (Real.sqrt (Fintype.card A) : ℂ)

/-- The normalized counting integral of [RW26], with total mass √|A|. -/
def normalizedSum (f : A → ℂ) : ℂ :=
  (∑ x : A, f x) / sqrtCard A

/-- The hat in [RW26] is F⁻¹: the character has the minus sign. -/
def fourier (q : A → ℂ) (f : A → ℂ) (y : A) : ℂ :=
  normalizedSum (fun x => f x * metricPairing q x (-y))

theorem sqrtCard_ne_zero : sqrtCard A ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt (Fintype.card A) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  simp only [sqrtCard]
  exact Complex.ofReal_ne_zero.mpr h.ne'

theorem metric_norm {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) :
    ‖q x‖ = 1 := by
  have h1 : q 0 = 1 := metric_zero hq
  have hchar : ∀ y : A, ∃ k : ℕ, 0 < k ∧ (metricPairing q x y) ^ k = 1 := by
    intro y
    have hz : metricPairing q x 0 = 1 := by
      simp only [metricPairing, add_zero, h1, mul_one]
      exact div_self (hq.nonzero x)
    have hpow : ∀ k : ℕ, metricPairing q x (k • y) = (metricPairing q x y) ^ k := by
      intro k
      induction k with
      | zero => simp only [zero_nsmul, pow_zero, hz]
      | succ k ih =>
        rw [succ_nsmul, hq.add_right x (k • y) y, ih, pow_succ]
    refine ⟨addOrderOf y, addOrderOf_pos y, ?_⟩
    rw [← hpow, addOrderOf_nsmul_eq_zero y, hz]
  have hnorm : ∀ y : A, ‖metricPairing q x y‖ = 1 := by
    intro y
    obtain ⟨k, hk, hval⟩ := hchar y
    have h2 : ‖metricPairing q x y‖ ^ k = 1 := by
      rw [← norm_pow, hval, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').mp h2
  have key : metricPairing q x (-x) = 1 / (q x * q x) := by
    simp only [metricPairing, add_neg_cancel, hq.even x, h1, div_one]
  have hn := hnorm (-x)
  rw [key, norm_div, norm_one, one_div, inv_eq_one] at hn
  have h5 : ‖q x‖ ^ 2 = 1 := by
    have h7 : ‖q x‖ ^ 2 = ‖q x * q x‖ := by rw [← norm_pow, pow_two]
    rw [h7, hn]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h5

theorem character_sum {q : A → ℂ} (hq : IsMetricGaussian q) (y : A) :
    (∑ x : A, metricPairing q x y) =
      if y = 0 then (Fintype.card A : ℂ) else 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · have hone : ∀ x : A, metricPairing q x 0 = 1 := by
      intro x
      simp only [metricPairing, add_zero, metric_zero hq, mul_one]
      exact div_self (hq.nonzero x)
    simp only [hone, if_pos rfl]
    rw [Finset.sum_const, Nat.smul_one_eq_cast, Finset.card_univ]
    simp
  · have hex : ∃ x₀ : A, metricPairing q x₀ y ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hy (hq.nondegenerate y (fun z => by
        rw [metric_pairing_symmetric q y z, hc z]))
    obtain ⟨x₀, hx₀⟩ := hex
    have htr : ∑ x : A, metricPairing q (x + x₀) y = ∑ x : A, metricPairing q x y :=
      Fintype.sum_equiv (Equiv.addRight x₀) _ _ (fun _ => rfl)
    have hsplit : ∀ x : A,
        metricPairing q (x + x₀) y = metricPairing q x y * metricPairing q x₀ y :=
      fun x => hq.add_left x x₀ y
    have hcalc : (∑ x : A, metricPairing q x y) * metricPairing q x₀ y
        = ∑ x : A, metricPairing q x y := by
      calc (∑ x : A, metricPairing q x y) * metricPairing q x₀ y
          = ∑ x : A, metricPairing q x y * metricPairing q x₀ y :=
            Finset.sum_mul _ _ _
        _ = ∑ x : A, metricPairing q (x + x₀) y :=
            Finset.sum_congr rfl (fun x _ => (hsplit x).symm)
        _ = ∑ x : A, metricPairing q x y := htr
    rw [if_neg hy]
    have hS : (∑ x : A, metricPairing q x y) * (1 - metricPairing q x₀ y) = 0 := by
      have h : (∑ x : A, metricPairing q x y) * (1 - metricPairing q x₀ y)
          = (∑ x : A, metricPairing q x y) - (∑ x : A, metricPairing q x y) * metricPairing q x₀ y := by
        ring
      rw [h, hcalc, sub_self]
    have hne : (1 - metricPairing q x₀ y) ≠ 0 := sub_ne_zero.mpr hx₀.symm
    exact (mul_eq_zero.mp hS).resolve_right hne

theorem fourier_twice {q : A → ℂ} (hq : IsMetricGaussian q) (f : A → ℂ) (x : A) :
    fourier q (fourier q f) x = f (-x) := by
  have hN : sqrtCard A * sqrtCard A = (Fintype.card A : ℂ) := by
    rw [sqrtCard, ← Complex.ofReal_mul]
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card A))
  have hN0 : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp Fintype.card_pos)
  -- the polarization factor appearing after one round trip
  have key : ∀ y z : A,
      metricPairing q z (-y) * metricPairing q y (-x) = metricPairing q (z + x) (-y) := by
    intro y z
    have hnn : metricPairing q y (-x) = metricPairing q (-y) x := by
      simp only [metricPairing]
      rw [show -y + x = -(y + -x) from by rw [neg_add, neg_neg], hq.even (y + -x), hq.even y,
        hq.even x]
    rw [hnn, ← metric_pairing_symmetric q x (-y), hq.add_left z x (-y)]
  have hpull : ∀ (S : A → ℂ),
      (∑ y : A, (S y / sqrtCard A) * metricPairing q y (-x))
        = (∑ y : A, S y * metricPairing q y (-x)) / sqrtCard A := by
    intro S
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ =>
      div_mul_eq_mul_div (S y) (sqrtCard A) (metricPairing q y (-x))
  have hswap : (∑ w : A, (∑ v : A, f v * metricPairing q v (-w)) * metricPairing q w (-x))
      = (∑ v : A, f v * (∑ w : A, metricPairing q v (-w) * metricPairing q w (-x))) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, mul_assoc]
  have hin : ∀ v : A, (∑ w : A, metricPairing q v (-w) * metricPairing q w (-x))
      = if v + x = 0 then (Fintype.card A : ℂ) else 0 := by
    intro v
    have h1 : (∑ w : A, metricPairing q v (-w) * metricPairing q w (-x))
        = ∑ w : A, metricPairing q (-w) (v + x) :=
      Finset.sum_congr rfl fun w _ => (key w v).trans (metric_pairing_symmetric q (v + x) (-w))
    rw [h1, Fintype.sum_equiv (Equiv.neg A)
      (fun w => metricPairing q (-w) (v + x)) (fun w => metricPairing q w (v + x))
      (fun w => rfl)]
    exact character_sum hq (v + x)
  have hlast : (∑ v : A, f v * (if v + x = 0 then (Fintype.card A : ℂ) else 0))
      = f (-x) * (Fintype.card A : ℂ) := by
    rw [Finset.sum_eq_single_of_mem (-x) (Finset.mem_univ _)
      (fun b _ hb => by
        have hbn : ¬(b + x = 0) := fun h => hb (eq_neg_iff_add_eq_zero.mpr h)
        simp [hbn]),
      if_pos (neg_add_cancel x)]
  simp only [fourier, normalizedSum]
  rw [hpull (fun w => ∑ v : A, f v * metricPairing q v (-w)), div_div, hN, hswap]
  simp only [hin]
  rw [hlast, mul_div_cancel_right₀ _ hN0]

/-- Groups of order at most four are excluded.
This is the assertion in [RW26, footnote 5]. -/
theorem gaussian_not_constant_off_zero {q : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) :
    ¬ ∃ c : ℂ, ∀ x : A, x ≠ 0 → q x = c := by
  rintro ⟨c, hc⟩
  have hex : ∃ x : A, x ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h1 : Fintype.card A ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => by rw [hall a, hall b]⟩
    omega
  obtain ⟨x, hx⟩ := hex
  have hqx : q x = c := hc x hx
  have hc0 : c ≠ 0 := by rw [← hqx]; exact hq.nonzero x
  have hnorm : ‖c‖ = 1 := by
    rw [← hqx]
    exact metric_norm hq x
  have hsum : (∑ y : A, metricPairing q x y) = 0 := by
    rw [show (∑ y : A, metricPairing q x y) = (∑ y : A, metricPairing q y x) from
      Finset.sum_congr rfl fun y _ => metric_pairing_symmetric q x y,
      character_sum hq x, if_neg hx]
  have hb0 : metricPairing q x 0 = 1 := by
    simp only [metricPairing, add_zero, metric_zero hq, mul_one]
    exact div_self (hq.nonzero x)
  have hbx : metricPairing q x (-x) = 1 / (c * c) := by
    simp only [metricPairing, add_neg_cancel, hq.even x, metric_zero hq, hqx, div_one]
  have hrest : ∀ y : A, y ≠ 0 → y ≠ -x → metricPairing q x y = 1 / c := by
    intro y hy0 hyx
    have hxy : x + y ≠ 0 := by
      intro h
      exact hyx (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h))
    rw [metricPairing, hc x hx, hc y hy0, hc (x + y) hxy]
    field_simp
  have h0x : (0 : A) ∉ ({-(x : A)} : Finset A) := by
    simp only [Finset.mem_singleton]
    intro h
    exact hx (neg_eq_zero.mp h.symm)
  have hcardins : (insert (0 : A) {-(x : A)} : Finset A).card = 2 := by
    rw [Finset.card_insert_of_notMem h0x, Finset.card_singleton]
  have hcard2 : (Finset.univ \ (insert (0 : A) {-(x : A)} : Finset A)).card
      = Fintype.card A - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hcardins, Finset.card_univ]
  have hmem : ∀ y ∈ Finset.univ \ (insert (0 : A) {-(x : A)}), metricPairing q x y = 1 / c := by
    intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or,
      not_false_iff] at hy
    exact hrest y hy.2.1 hy.2.2
  have hsumrest : (∑ y ∈ Finset.univ \ (insert (0 : A) {-(x : A)}), metricPairing q x y)
      = ((Fintype.card A - 2 : ℕ) : ℂ) * (1 / c) := by
    rw [Finset.sum_congr rfl (fun y hy => hmem y hy), Finset.sum_const, hcard2]
    push_cast
    ring
  rw [← Finset.sum_sdiff (Finset.subset_univ _), Finset.sum_insert h0x, Finset.sum_singleton,
    hb0, hbx, hsumrest] at hsum
  -- hsum : 1 + 1/(c*c) + ((card A - 2 : ℕ) : ℂ) * (1/c) = 0
  have hN2 : ((Fintype.card A - 2 : ℕ) : ℂ) = (Fintype.card A : ℂ) - 2 := by
    have h2 : 2 ≤ Fintype.card A := by omega
    rw [Nat.cast_sub h2, Nat.cast_ofNat]
  rw [hN2] at hsum
  have hkey : c + c⁻¹ = -((Fintype.card A : ℂ) - 2) := by
    rw [inv_eq_one_div]
    field_simp at hsum ⊢
    linear_combination hsum
  have habs : ‖c + c⁻¹‖ ≤ 2 := by
    have h1 : ‖c + c⁻¹‖ ≤ ‖c‖ + ‖c⁻¹‖ := norm_add_le _ _
    rw [norm_inv, hnorm, inv_one] at h1
    linarith
  have hval : ‖c + c⁻¹‖ = (Fintype.card A : ℝ) - 2 := by
    have h2 : ((Fintype.card A : ℕ) : ℂ) - 2 = (((Fintype.card A : ℝ) - 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hkey, norm_neg, h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by
        have : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast (by omega : 2 ≤ Fintype.card A)
        linarith)]
  rw [hval] at habs
  have h4 : (Fintype.card A : ℝ) ≤ 4 := by linarith
  have h5 : Fintype.card A ≤ 4 := by exact_mod_cast h4
  omega

end SICLean.L2b
