import SICLean.L5.RayArithmeticConjugation

set_option autoImplicit false

/-!
Auxiliary arithmetic for the two explicit real sign classes.
-/

noncomputable section
open scoped MatrixGroups NumberField Classical
open NumberField ClassFieldTheory

namespace SICLean.L5.RayArithmeticSignsAux

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM

/-- The positive integral trace parameter is at least one, so the attracting root of its norm-one
quadratic is greater than two. -/
theorem epsilon_gt_two : 2 < ActualField.sigma₁ M hM (ActualField.epsilon M hM) := by
  rw [ActualField.sigma₁_epsilon]
  have he := L4.specialValueEpsilon_gt_one M hM
  have hn : (1 : ℝ) ≤ (L4.specialValueOrder M : ℝ) := by
    exact_mod_cast L4.specialValueOrder_pos M hM
  have hp := L4.specialValueEpsilon_characteristic M hM
  by_contra h
  have he2 := le_of_not_gt h
  have he0 : 0 ≤ L4.specialValueEpsilon M := by linarith
  have hsq := mul_le_mul_of_nonneg_right he2 he0
  have hne := mul_le_mul_of_nonneg_right hn he0
  nlinarith

/-- A rational-integer global congruence is preserved by the literal quadratic conjugation, also
when the input is field-valued. -/
theorem globallyCongruent_conjugation (m : ℕ) (a : K)
    (ha : RayArithmeticModulus.GloballyCongruent M hM m a) :
    RayArithmeticModulus.GloballyCongruent M hM m
      (RayArithmeticPlaces.conjugation M hM a) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨RayArithmeticPlaces.integerConjugation M hM b, ?_⟩
  have h := congrArg (RayArithmeticPlaces.conjugation M hM) hb
  simpa [RayArithmeticPlaces.integerConjugation] using h

/-- Principal ideal multiplication descends to the literal ray quotient. -/
theorem principalClass_mul (m : ℕ) (a b : Kˣ)
    (ha : RayArithmeticModulus.FiniteCongruent M hM m a)
    (hb : RayArithmeticModulus.FiniteCongruent M hM m b) :
    RayArithmeticModulus.principalClass M hM m (a * b)
        (ClassFieldTheory.IsRayCongruent.mul ha hb) =
      RayArithmeticModulus.principalClass M hM m a ha *
        RayArithmeticModulus.principalClass M hM m b hb := by
  unfold RayArithmeticModulus.principalClass
  rw [← map_mul]
  congr 1
  exact Subtype.ext (map_mul (toPrincipalIdeal (𝓞 K) K) a b)

/-- Equal real signs make the quotient of two finite-congruent generators totally positive, hence
ray principal. -/
theorem principalClass_eq_of_same_sign (m : ℕ) (a b : Kˣ)
    (ha : RayArithmeticModulus.FiniteCongruent M hM m a)
    (hb : RayArithmeticModulus.FiniteCongruent M hM m b)
    (h₁ : (0 < ActualField.sigma₁ M hM (a : K) ∧
              0 < ActualField.sigma₁ M hM (b : K)) ∨
          (ActualField.sigma₁ M hM (a : K) < 0 ∧
              ActualField.sigma₁ M hM (b : K) < 0))
    (h₂ : (0 < ActualField.sigma₂ M hM (a : K) ∧
              0 < ActualField.sigma₂ M hM (b : K)) ∨
          (ActualField.sigma₂ M hM (a : K) < 0 ∧
              ActualField.sigma₂ M hM (b : K) < 0)) :
    RayArithmeticModulus.principalClass M hM m a ha =
      RayArithmeticModulus.principalClass M hM m b hb := by
  unfold RayArithmeticModulus.principalClass
  apply QuotientGroup.eq.mpr
  change (toPrincipalIdeal (𝓞 K) K a)⁻¹ * toPrincipalIdeal (𝓞 K) K b ∈
    rayPrincipalIdealSubgroup (RayArithmeticModulus.modulus M hM m)
  refine (mem_rayPrincipalIdealSubgroup_iff (RayArithmeticModulus.modulus M hM m) _).mpr
    ⟨a⁻¹ * b, ?_, ?_⟩
  · apply (RayArithmeticModulus.isRayCongruent_iff M hM m _).mpr
    refine ⟨IsRayCongruent.mul (IsRayCongruent.inv ha) hb, ?_, ?_⟩
    · simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
      rcases h₁ with ⟨ha₁, hb₁⟩ | ⟨ha₁, hb₁⟩
      · exact mul_pos (inv_pos.mpr ha₁) hb₁
      · exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr ha₁) hb₁
    · simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
      rcases h₂ with ⟨ha₂, hb₂⟩ | ⟨ha₂, hb₂⟩
      · exact mul_pos (inv_pos.mpr ha₂) hb₂
      · exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr ha₂) hb₂
  · simp only [map_mul, map_inv]

end SICLean.L5.RayArithmeticSignsAux
