import SICLean.L4.G2SingleFinite
import SICLean.L4.G2DegenerateParametersAux

set_option autoImplicit false

/-!
# Character orthogonality, v=0, and the value at the origin

The degenerate cases are included. [RW26, p. 3, (3)--(7), p. 13] gives the
off-origin target; the value at the origin is included.

The existing quotient is used throughout, including noncyclic groups. No Fourier inversion, (31), or
(36) is reproved. The elementary character lemmas below supply the general-M orthogonality; the
nonzero-v analytic result is exactly ResidueLedger.finite_ratio_sum_nonzero.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2.DegenerateParameters

open SpecialValueBridge StripCounting
open G2DegenerateParametersAux

/-- The actual (3) character, at both zero arguments. [RW26, (3), p. 3]. This does not assume the
group is cyclic. -/
theorem pairing_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : SpecialValueGroup M) :
    specialValuePairing M hM 0 u = 1 ∧ specialValuePairing M hM u 0 = 1 := by
  refine Quotient.inductionOn u fun x => ?_
  change specialValuePairing M hM (specialValueMk M 0) (specialValueMk M x) = 1 ∧
    specialValuePairing M hM (specialValueMk M x) (specialValueMk M 0) = 1
  rw [specialValuePairing_mk, specialValuePairing_mk]
  simp [specialValuePairingLift, specialValueOmega,
    L2r.rowAction, e]

/-- Additivity of the character in the summation variable. [RW26, (3), p. 3]. Pure algebra of the
existing exponential. -/
theorem pairing_add_left (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x y u : SpecialValueGroup M) :
    specialValuePairing M hM (x + y) u =
      specialValuePairing M hM x u * specialValuePairing M hM y u := by
  refine Quotient.inductionOn x fun a => ?_
  refine Quotient.inductionOn y fun b => ?_
  refine Quotient.inductionOn u fun c => ?_
  change specialValuePairing M hM (specialValueMk M (a + b)) (specialValueMk M c) =
    specialValuePairing M hM (specialValueMk M a) (specialValueMk M c) *
      specialValuePairing M hM (specialValueMk M b) (specialValueMk M c)
  simp only [specialValuePairing_mk]
  exact pairingLift_add_left M a b c

/-- Nondegeneracy on the true row quotient, from the lattice criterion. Test integer basis rows; S≡0
mod N alone is not a zero-class test. [RW26, (3), p. 3]. -/
theorem pairing_separates_right (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : SpecialValueGroup M) (hu : u ≠ 0) :
    ∃ x : SpecialValueGroup M, specialValuePairing M hM x u ≠ 1 := by
  revert hu
  refine Quotient.inductionOn u fun a ha => ?_
  by_contra h
  push Not at h
  apply ha
  apply (QuotientAddGroup.eq_zero_iff a).mpr
  apply pairingLift_kernel_mem M hM a
  intro x
  exact (specialValuePairing_mk M hM x a).symm.trans (h (specialValueMk M x))

/-- Character orthogonality for arbitrary allowed M. [RW26, (3), p. 3]. -/
theorem groupSum_pairing (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : SpecialValueGroup M) :
    groupSum M hM (fun x => specialValuePairing M hM x u) =
      if u = 0 then (specialValueOrder M : ℂ) else 0 := by
  let : Fintype (SpecialValueGroup M) := specialGroupFintype M hM
  change (∑ x, specialValuePairing M hM x u) = _
  by_cases hu : u = 0
  · subst u
    simp_rw [(pairing_zero M hM _).2]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hc : Fintype.card (SpecialValueGroup M) = (specialValueOrder M).toNat := by
      rw [← Nat.card_eq_fintype_card, specialValueGroup_card M hM]
    rw [hc]
    exact_mod_cast Int.toNat_of_nonneg (specialValueOrder_pos M hM).le
  · rw [if_neg hu]
    obtain ⟨a, ha⟩ := pairing_separates_right M hM u hu
    have hs : (∑ x, specialValuePairing M hM (a + x) u) =
        ∑ x, specialValuePairing M hM x u := by
      exact Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun _ => rfl)
    simp_rw [pairing_add_left] at hs
    rw [← Finset.mul_sum] at hs
    exact (mul_eq_zero.mp (by linear_combination hs :
      (specialValuePairing M hM a u - 1) *
        (∑ x, specialValuePairing M hM x u) = 0)).resolve_left (sub_ne_zero.mpr ha)

/-- The separately prescribed minus origin is A⁻¹. [RW26, (4), p. 3]. -/
theorem origin_inverse (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    repellingMinus M hM 0 = (repellingPlus M hM 0)⁻¹ := by
  rw [(repellingValues_zero M hM).1, (repellingValues_zero M hM).2, inv_inv]

/-- A−A⁻¹=√N, using the existing positive real roots and L/√ε=√N. [RW26, (4), p. 3]. -/
theorem origin_difference (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    repellingPlus M hM 0 - repellingMinus M hM 0 =
      (Real.sqrt (specialValueOrder M : ℝ) : ℂ) := by
  rw [(repellingValues_zero M hM).1, (repellingValues_zero M hM).2]
  have hr := sqrt_epsilon_ne_zero M hM
  have hs : (Real.sqrt (epsilon M) : ℂ) ^ 2 = (epsilon M : ℂ) := by
    exact_mod_cast Real.sq_sqrt (epsilon_pos M hM).le
  have hn : (length M : ℂ) / (Real.sqrt (epsilon M) : ℂ) =
      (Real.sqrt (specialValueOrder M : ℝ) : ℂ) := by
    exact_mod_cast normalized_length M hM
  rw [← hn, length, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp
  linear_combination -hs

/-- The value at (0,0). [RW26, (7), p. 3]. -/
theorem origin_cubic_correction (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    repellingPlus M hM 0 ^ 3 -
        (repellingPlus M hM 0 + (Real.sqrt (specialValueOrder M : ℝ) : ℂ)) =
      (specialValueOrder M : ℂ) * repellingPlus M hM 0 := by
  have hA : repellingPlus M hM 0 ≠ 0 := by
    rw [(repellingValues_zero M hM).1]
    exact inv_ne_zero (sqrt_epsilon_ne_zero M hM)
  have hd := congrArg (fun z : ℂ => z * repellingPlus M hM 0)
    (origin_difference M hM)
  rw [origin_inverse, sub_mul, inv_mul_cancel₀ hA] at hd
  have hq : repellingPlus M hM 0 ^ 2 - 1 =
      (Real.sqrt (specialValueOrder M : ℝ) : ℂ) * repellingPlus M hM 0 := by
    linear_combination hd
  rw [← sqrt_order_sq M hM]
  linear_combination (repellingPlus M hM 0 +
    (Real.sqrt (specialValueOrder M : ℝ) : ℂ)) * hq

/-- F⁺/F⁻ is 1 off the true zero class and A² at it. [RW26, footnote 2, p. 3, (4)]. -/
theorem diagonal_ratio (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    repellingPlus M hM x / repellingMinus M hM x =
      if x = 0 then repellingPlus M hM 0 ^ 2 else 1 := by
  by_cases hx : x = 0
  · subst x
    rw [if_pos rfl, origin_inverse, div_eq_mul_inv, inv_inv, pow_two]
  · rw [if_neg hx, repelling_agree_off_zero M hM x hx,
      div_self (repellingMinus_ne_zero M hM x)]

/-- All u at v=0, before comparison with the main term. Character orthogonality gives precisely the
extra √N at u=0. [RW26, (7), p. 3]. -/
theorem ratio_sum_zero_shift (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ∀ u : SpecialValueGroup M,
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
        (repellingPlus M hM x / repellingMinus M hM x)) =
      repellingPlus M hM 0 + (if u = 0 then (Real.sqrt (specialValueOrder M : ℝ) : ℂ) else 0) := by
  intro u
  let : Fintype (SpecialValueGroup M) := specialGroupFintype M hM
  have hs : groupSum M hM (fun x => specialValuePairing M hM x u *
        (repellingPlus M hM x / repellingMinus M hM x)) =
      groupSum M hM (fun x => specialValuePairing M hM x u) +
        (repellingPlus M hM 0 ^ 2 - 1) := by
    unfold groupSum
    calc
      _ = ∑ x, (specialValuePairing M hM x u +
          if x = 0 then repellingPlus M hM 0 ^ 2 - 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp only
        rw [diagonal_ratio]
        by_cases hx0 : x = 0
        · subst x
          simp only [ite_true, (pairing_zero M hM u).1, one_mul]
          ring
        · simp [hx0]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hA : repellingPlus M hM 0 ≠ 0 := by
    rw [(repellingValues_zero M hM).1]
    exact inv_ne_zero (sqrt_epsilon_ne_zero M hM)
  have hd := congrArg (fun z : ℂ => z * repellingPlus M hM 0)
    (origin_difference M hM)
  rw [origin_inverse, sub_mul, inv_mul_cancel₀ hA] at hd
  have hq : repellingPlus M hM 0 ^ 2 - 1 =
      (Real.sqrt (specialValueOrder M : ℝ) : ℂ) * repellingPlus M hM 0 := by
    linear_combination hd
  change (Real.sqrt (specialValueOrder M : ℝ) : ℂ)⁻¹ *
    groupSum M hM (fun x => specialValuePairing M hM x u *
      (repellingPlus M hM x / repellingMinus M hM x)) = _
  rw [hs, groupSum_pairing, hq]
  have hN := sqrt_order_ne_zero M hM
  by_cases hu : u = 0
  · rw [if_pos hu, if_pos hu, ← sqrt_order_sq M hM]
    field_simp
    ring
  · rw [if_neg hu, if_neg hu, zero_add, add_zero]
    exact inv_mul_cancel_left₀ hN _

/-- The v=0 main term is A when u≠0. [RW26, (7), p. 3, footnote 2]. -/
theorem ratio_main_zero_shift_nonzero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : SpecialValueGroup M) (hu : u ≠ 0) :
    repellingPlus M hM (u + 0) / (repellingMinus M hM u * repellingMinus M hM 0) =
      repellingPlus M hM 0 := by
  rw [add_zero, repelling_agree_off_zero M hM u hu, div_mul_eq_div_div,
    div_self (repellingMinus_ne_zero M hM u), origin_inverse, one_div, inv_inv]

/-- Literal left side at the origin is A+√N. [RW26, (7), p. 3]. No G1 is needed. -/
theorem ratio_sum_origin (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    normalizedValueSum M hM (fun x => specialValuePairing M hM x 0 *
      (repellingPlus M hM x / repellingMinus M hM (x + 0))) =
      repellingPlus M hM 0 + (Real.sqrt (specialValueOrder M : ℝ) : ℂ) := by
  simpa using ratio_sum_zero_shift M hM 0

/-- The right side at the origin is A³. [RW26, (7), p. 3]. -/
theorem ratio_main_origin (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    repellingPlus M hM (0 + 0) / (repellingMinus M hM 0 * repellingMinus M hM 0) =
      repellingPlus M hM 0 ^ 3 := by
  rw [add_zero, origin_inverse, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Full repelling identity. For v ≠ 0 the proof uses `ResidueLedger.finite_ratio_sum_nonzero`; for
v = 0 it uses the preceding character identities. This is the input of the existing transport iff.
[RW26, (7), p. 3, p. 13]. -/
theorem repelling_pentagon (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ∀ u v : SpecialValueGroup M,
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
        (repellingPlus M hM x / repellingMinus M hM (x + v))) =
      repellingPlus M hM (u + v) / (repellingMinus M hM u * repellingMinus M hM v) -
        (if u = 0 ∧ v = 0 then (specialValueOrder M : ℂ) * repellingPlus M hM 0 else 0) := by
  intro u v
  by_cases hv : v = 0
  · subst v
    by_cases hu : u = 0
    · subst u
      rw [ratio_sum_origin, ratio_main_origin, if_pos ⟨rfl, rfl⟩]
      linear_combination -(origin_cubic_correction M hM)
    · rw [ratio_main_zero_shift_nonzero M hM u hu,
        if_neg (by simp [hu]), sub_zero]
      simpa only [add_zero, if_neg hu] using ratio_sum_zero_shift M hM u
  · rw [if_neg (by simp [hv]), sub_zero]
    have hsummand : (fun x => specialValuePairing M hM x u *
        (repellingPlus M hM x / repellingMinus M hM (x + v))) =
        ResidueLedger.ratioSummand M hM u v := by
      funext x
      exact (mul_div_assoc _ _ _).symm
    rw [hsummand]
    exact ResidueLedger.finite_ratio_sum_nonzero hG1 M hM u v hv

/-- The restriction is made only after the all-parameter identity. [RW26, (7), p. 3, p. 13]. -/
theorem repelling_pentagon_off_origin (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ∀ u v : SpecialValueGroup M, (u, v) ≠ (0, 0) →
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
        (repellingPlus M hM x / repellingMinus M hM (x + v))) =
      repellingPlus M hM (u + v) / (repellingMinus M hM u * repellingMinus M hM v) := by
  intro u v huv
  have hnot : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨rfl, rfl⟩
    exact huv rfl
  simpa only [if_neg hnot, sub_zero] using repelling_pentagon hG1 M hM u v

#check @specialValueLattice_mem_iff
#check @specialValueGroup_card
#check @ResidueLedger.finite_ratio_sum_nonzero
#check @repellingValues_zero
#check @groupSum_pairing
#check @origin_cubic_correction
#check @repelling_pentagon

end SICLean.L4.G2.DegenerateParameters
