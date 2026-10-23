import SICLean.L4.M74Coefficients

set_option autoImplicit false

/-!
# Elementary algebra for the two M74 zero branches

The branch inequalities use only the strict period inequality in
`PeriodData`. The inverse polynomial uses the positive-root
normalization.
-/

noncomputable section

namespace SICLean.L4.M74EquationsAux

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The square of the attracting positive root is strictly larger than one. -/
theorem period_sqrt_mul_ne_one (P : SICLean.L3.PeriodData K) :
    (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) *
      (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) ≠ (1 : ℂ) := by
  intro h
  have hnonneg : 0 ≤ P.sigma₁ P.epsilon :=
    le_of_lt (lt_trans zero_lt_one P.epsilon_gt_one)
  have hreal : Real.sqrt (P.sigma₁ P.epsilon) *
      Real.sqrt (P.sigma₁ P.epsilon) = 1 := by
    exact_mod_cast h
  rw [Real.mul_self_sqrt hnonneg] at hreal
  exact (ne_of_gt P.epsilon_gt_one) hreal

/-- The plus and minus zero branches are distinct. -/
theorem period_sqrt_ne_inv (P : SICLean.L3.PeriodData K) :
    (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) ≠
      (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)⁻¹ := by
  have hroot : (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (lt_trans zero_lt_one P.epsilon_gt_one)).ne'
  intro h
  apply period_sqrt_mul_ne_one P
  calc
    (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) *
        (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) =
        (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)⁻¹ *
          (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) :=
      congrArg (fun z : ℂ => z * (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)) h
    _ = 1 := inv_mul_cancel₀ hroot

/-- The inverse zero branch satisfies the opposite-sign quadratic. -/
theorem period_sqrt_inv_polynomial (P : SICLean.L3.PeriodData K) :
    (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)⁻¹ ^ 2 +
      (Real.sqrt (P.N : ℝ) : ℂ) *
        (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)⁻¹ - 1 = 0 := by
  have hroot : (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (lt_trans zero_lt_one P.epsilon_gt_one)).ne'
  have hnormalization :
      (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) ^ 2 -
        (Real.sqrt (P.N : ℝ) : ℂ) *
          (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) - 1 = 0 := by
    exact_mod_cast SICLean.L3.M74.period_sqrt_normalization P
  field_simp [hroot]
  linear_combination -hnormalization

end SICLean.L4.M74EquationsAux
