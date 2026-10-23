import SICLean.L5.ConjugationSpecialPoint
import SICLean.L4.M74Gaussian

set_option autoImplicit false

/-!
# Conjugation of the attracting special values

Builds on `ConjugationSpecialPoint`. All values are `specialValuePlus` and
`specialValueMinus`, together with the Gaussian and the quotient group, for
every `SpecialValueAdmissible M`.
Sources: [RW26, p. 2, (2)], [RW26, p. 3, (3)--(5)], [RW26, p. 14, Prop. 7],
[RW26, p. 14, Cor. 1, (28)], [RW-rec, p. 3, Def. 1], [RW-rec, p. 4, Prop. 2, (7)].
These are the Gaussian relation, the off-zero reflection relation, and the
fixed value at zero. The nonzero-label hypothesis is kept where it appears.
The value at zero uses the prescribed positive square root.
No Artin or reciprocity theorem is an input, including for the mixed
plus/minus identity at zero.
-/

noncomputable section

open Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L5.ConjugationSpecialValue

open SICLean.L4

/-- Finite-order Gaussian from [RW26, p. 3, (3)], using the root-order theorem. -/
theorem specialValueGaussianLift_conj (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    (starRingEnd ℂ) (specialValueGaussianLift M u) = (specialValueGaussianLift M u)⁻¹ := by
  apply (Complex.inv_eq_conj ?_).symm
  apply Complex.norm_eq_one_of_pow_eq_one (SICLean.L3.M74.gaussianLift_order M hM u)
  have hN := specialValueOrder_pos M hM
  omega

/-- The same relation on the quotient labels. -/
theorem specialValueGaussian_conj (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    (starRingEnd ℂ) (specialValueGaussian M hM x) = (specialValueGaussian M hM x)⁻¹ := by
  refine Quotient.inductionOn x ?_
  intro u
  change (starRingEnd ℂ) (specialValueGaussian M hM (specialValueMk M u)) =
    (specialValueGaussian M hM (specialValueMk M u))⁻¹
  rw [specialValueGaussian_mk]
  exact specialValueGaussianLift_conj M hM u

/-- Piecewise plus lift, including its prescribed lattice branch.
[RW26, p. 14, Cor. 1]. Off the lattice this is the reflection conjugation. -/
theorem specialValuePlusLift_conj (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    (starRingEnd ℂ) (specialValuePlusLift M u) =
      specialValueGaussianLift M u * specialValuePlusLift M u := by
  by_cases hu : u ∈ specialValueLattice M
  · have hG : specialValueGaussianLift M u = 1 := by
      have h := specialValueGaussianLift_periodic M hM 0 u hu
      simpa only [zero_add, specialValueGaussianLift_zero] using h
    simp [specialValuePlusLift, hu, hG]
  · simpa only [specialValuePlusLift, if_neg hu] using
      ConjugationSpecialPoint.specialValueRaw_conj_gaussian M hM u hu

/-- The same relation, with the inverse of the positive root at lattice labels. -/
theorem specialValueMinusLift_conj (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    (starRingEnd ℂ) (specialValueMinusLift M u) =
      specialValueGaussianLift M u * specialValueMinusLift M u := by
  by_cases hu : u ∈ specialValueLattice M
  · have hG : specialValueGaussianLift M u = 1 := by
      have h := specialValueGaussianLift_periodic M hM 0 u hu
      simpa only [zero_add, specialValueGaussianLift_zero] using h
    simp [specialValueMinusLift, hu, hG]
  · simpa only [specialValueMinusLift, if_neg hu] using
      ConjugationSpecialPoint.specialValueRaw_conj_gaussian M hM u hu

/-- [RW26, p. 14, Prop. 7], including x = 0.
The zero branch pairs the plus value with the minus value. -/
theorem specialValuePlus_conj_inv_minus_neg (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : SpecialValueGroup M) :
    (starRingEnd ℂ) (specialValuePlus M hM x) = (specialValueMinus M hM (-x))⁻¹ := by
  refine Quotient.inductionOn x ?_
  intro u
  change (starRingEnd ℂ) (specialValuePlus M hM (specialValueMk M u)) =
    (specialValueMinus M hM (specialValueMk M (-u)))⁻¹
  rw [specialValuePlus_mk, specialValueMinus_mk]
  by_cases hu : u ∈ specialValueLattice M
  · have hnu : -u ∈ specialValueLattice M := neg_mem hu
    simp [specialValuePlusLift, specialValueMinusLift, hu, hnu]
  · have hnu : -u ∉ specialValueLattice M := by
      intro h
      exact hu (by simpa only [neg_neg] using neg_mem h)
    simpa only [specialValuePlusLift, specialValueMinusLift, if_neg hu, if_neg hnu] using
      ConjugationSpecialPoint.specialValueRaw_conj_inv M hM u hu

/-- The same mixed identity with the branches exchanged, including x = 0. -/
theorem specialValueMinus_conj_inv_plus_neg (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : SpecialValueGroup M) :
    (starRingEnd ℂ) (specialValueMinus M hM x) = (specialValuePlus M hM (-x))⁻¹ := by
  refine Quotient.inductionOn x ?_
  intro u
  change (starRingEnd ℂ) (specialValueMinus M hM (specialValueMk M u)) =
    (specialValuePlus M hM (specialValueMk M (-u)))⁻¹
  rw [specialValueMinus_mk, specialValuePlus_mk]
  by_cases hu : u ∈ specialValueLattice M
  · have hnu : -u ∈ specialValueLattice M := neg_mem hu
    simp [specialValueMinusLift, specialValuePlusLift, hu, hnu]
  · have hnu : -u ∉ specialValueLattice M := by
      intro h
      exact hu (by simpa only [neg_neg] using neg_mem h)
    simpa only [specialValueMinusLift, specialValuePlusLift, if_neg hu, if_neg hnu] using
      ConjugationSpecialPoint.specialValueRaw_conj_inv M hM u hu

/-- [RW-rec, p. 4, Prop. 2, (7)]; [RW26, p. 14, Cor. 1, (28)].
Conjugation of the plus value on every quotient label. The Gaussian factor is
`specialValueGaussian`, with its positive sign. -/
theorem specialValuePlus_conj (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    (starRingEnd ℂ) (specialValuePlus M hM x) =
      specialValueGaussian M hM x * specialValuePlus M hM x := by
  refine Quotient.inductionOn x ?_
  intro u
  change (starRingEnd ℂ) (specialValuePlus M hM (specialValueMk M u)) =
    specialValueGaussian M hM (specialValueMk M u) *
      specialValuePlus M hM (specialValueMk M u)
  rw [specialValuePlus_mk, specialValueGaussian_mk]
  exact specialValuePlusLift_conj M hM u

/-- [RW26, p. 14, Cor. 1, (28)], the corresponding minus formula. -/
theorem specialValueMinus_conj (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    (starRingEnd ℂ) (specialValueMinus M hM x) =
      specialValueGaussian M hM x * specialValueMinus M hM x := by
  refine Quotient.inductionOn x ?_
  intro u
  change (starRingEnd ℂ) (specialValueMinus M hM (specialValueMk M u)) =
    specialValueGaussian M hM (specialValueMk M u) *
      specialValueMinus M hM (specialValueMk M u)
  rw [specialValueMinus_mk, specialValueGaussian_mk]
  exact specialValueMinusLift_conj M hM u

/-- [RW-rec, p. 4, (7)]; [RW26, p. 14, Prop. 7], together with plus/minus
agreement off zero ([RW26, p. 3, footnote 2]). The hypothesis x ≠ 0 is essential. -/
theorem specialValuePlus_conj_mul_neg (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) (hx : x ≠ 0) :
    (starRingEnd ℂ) (specialValuePlus M hM x) * specialValuePlus M hM (-x) = 1 := by
  rw [specialValuePlus_conj_inv_minus_neg,
    specialValue_agree_off_zero M hM (-x) (neg_ne_zero.mpr hx)]
  exact inv_mul_cancel₀ (specialValueMinus_ne_zero M hM (-x))

/-- The same relation in reciprocal form. -/
theorem specialValuePlus_conj_inv_neg (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) (hx : x ≠ 0) :
    (starRingEnd ℂ) (specialValuePlus M hM x) = (specialValuePlus M hM (-x))⁻¹ := by
  rw [specialValuePlus_conj_inv_minus_neg,
    specialValue_agree_off_zero M hM (-x) (neg_ne_zero.mpr hx)]

/-- [RW-rec, p. 3, Def. 1]; [RW-rec, p. 4, Prop. 2, (7)]; [RW26, p. 2, (2)].
The value at the origin is the positive square root of ε. -/
theorem specialValuePlus_conj_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (starRingEnd ℂ) (specialValuePlus M hM 0) = specialValuePlus M hM 0 := by
  rw [specialValuePlus_zero]
  exact Complex.conj_ofReal _

/-- The three conjugation formulas for `specialValuePlus`: the Gaussian relation
on every label, the off-zero reflection relation, and the fixed value at zero.
[RW-rec, p. 4, Prop. 2, (7)]; [RW26, p. 14, Prop. 7]; [RW26, p. 14, Cor. 1]. -/
theorem specialValuePlus_conjugation (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (∀ x : SpecialValueGroup M,
      (starRingEnd ℂ) (specialValuePlus M hM x) =
        specialValueGaussian M hM x * specialValuePlus M hM x) ∧
    (∀ x : SpecialValueGroup M, x ≠ 0 →
      (starRingEnd ℂ) (specialValuePlus M hM x) * specialValuePlus M hM (-x) = 1) ∧
    (starRingEnd ℂ) (specialValuePlus M hM 0) = specialValuePlus M hM 0 := by
  exact ⟨specialValuePlus_conj M hM, specialValuePlus_conj_mul_neg M hM,
    specialValuePlus_conj_zero M hM⟩

#print SICLean.L4.specialValuePlus
#check SICLean.L4.specialValuePlus_zero
#check SICLean.L4.specialValue_agree_off_zero
#check SICLean.L4.specialValue_mixed_reflection
#check SICLean.L3.M74.gaussian_order
#check specialValuePlus_conjugation

end SICLean.L5.ConjugationSpecialValue
