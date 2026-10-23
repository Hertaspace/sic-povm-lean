import SICLean.L4.ModularDivisor

set_option autoImplicit false

/-!
# Auxiliary real algebra

Elementary real arithmetic for a hyperbolic matrix with a chosen real fixed point, plus the small
amount of integer-matrix linear algebra needed for the quotient cardinality. These lemmas are
internal support for `SICLean.L4.DistributionLattice`; none of them is a new mathematical input.
-/

noncomputable section

open Set
open scoped MatrixGroups

namespace SICLean.L4

/-- Determinant of the integer matrix, read in `ℝ`. -/
theorem dl_det (M : SL(2, ℤ)) :
    (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_two] at h
  have h' : ((M 0 0 : ℤ) * (M 1 1 : ℤ) - (M 0 1 : ℤ) * (M 1 0 : ℤ) : ℝ) = 1 := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- The fixed-point quadratic relation in real form. -/
theorem dl_quad (M : SL(2, ℤ)) (τ : ℝ)
    (hper : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ : ℂ) = (τ : ℂ)) :
    (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0 := by
  have hdenC : ((M 1 0 : ℂ) * (τ : ℂ) + (M 1 1 : ℂ)) ≠ 0 := by
    intro h
    have h0 : (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) = 0 := by
      have := congrArg Complex.re h
      simpa using this
    linarith
  have hmul : ((M 0 0 : ℂ) * (τ : ℂ) + (M 0 1 : ℂ)) =
      (τ : ℂ) * ((M 1 0 : ℂ) * (τ : ℂ) + (M 1 1 : ℂ)) := by
    rw [etaMobius, etaDenom] at hfix
    exact (div_eq_iff hdenC).mp hfix
  have hmulR : (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) =
      τ * ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) := by
    apply Complex.ofReal_inj.mp
    push_cast
    exact hmul
  linarith

/-- `ε⁻¹ = a - cτ` for the real fixed point. -/
theorem dl_period_inv (M : SL(2, ℤ)) (τ : ℝ)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ = (M 0 0 : ℝ) - (M 1 0 : ℝ) * τ := by
  have hmul : ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) *
      ((M 0 0 : ℝ) - (M 1 0 : ℝ) * τ) = 1 := by
    have hid : ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) *
        ((M 0 0 : ℝ) - (M 1 0 : ℝ) * τ) - 1 =
        -((M 1 0 : ℝ)) *
          ((M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ)) +
          ((M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) - 1) := by
      ring
    rw [hquad, dl_det M] at hid
    linarith
  exact inv_eq_of_mul_eq_one_right hmul

/-- Trace identity `ε + ε⁻¹ = a + d`. -/
theorem dl_period_sum (M : SL(2, ℤ)) (τ : ℝ)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) + ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ =
      (M 0 0 : ℝ) + (M 1 1 : ℝ) := by
  rw [dl_period_inv M τ hquad]
  ring

/-- The conjugate root lies on the same quadratic. -/
theorem dl_conj_quad (M : SL(2, ℤ)) (τ : ℝ)
    (hc : (M 1 0 : ℝ) ≠ 0)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    (M 1 0 : ℝ) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) ^ 2 +
        ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) -
        (M 0 1 : ℝ) = 0 := by
  have htarget : (M 1 0 : ℝ) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) ^ 2 +
        ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) -
        (M 0 1 : ℝ) =
      (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) := by
    field_simp
    ring
  rw [htarget, hquad]

/-- The conjugate root paired with the inverse automorphy factor. -/
theorem dl_conj_period (M : SL(2, ℤ)) (τ : ℝ)
    (hc : (M 1 0 : ℝ) ≠ 0)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    (M 1 0 : ℝ) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) + (M 1 1 : ℝ) =
      ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ := by
  rw [dl_period_inv M τ hquad]
  field_simp
  ring

/-- The conjugate root is smaller. -/
theorem dl_conj_lt (M : SL(2, ℤ)) (τ : ℝ)
    (hc : 0 < (M 1 0 : ℝ)) (hε : 1 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    ((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ < τ := by
  have hcne : (M 1 0 : ℝ) ≠ 0 := ne_of_gt hc
  have hdiff : (M 1 0 : ℝ) *
      (τ - (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ)) =
      ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) - ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ := by
    rw [dl_period_inv M τ hquad]
    field_simp
    ring
  have hinv : ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hε
  have hpos : 0 < ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) - ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ := by
    linarith
  have hprod : 0 < (M 1 0 : ℝ) *
      (τ - (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ)) := by
    rw [hdiff]
    exact hpos
  nlinarith [hc, hprod]

/-- `ε = a - cτ'` at the conjugate root. -/
theorem dl_period_eq_conj (M : SL(2, ℤ)) (τ : ℝ)
    (hc : (M 1 0 : ℝ) ≠ 0) :
    (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) =
      (M 0 0 : ℝ) - (M 1 0 : ℝ) *
        (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) := by
  field_simp
  ring

/-- Product of the two real roots. -/
theorem dl_tau_mul_conj (M : SL(2, ℤ)) (τ : ℝ)
    (hc : (M 1 0 : ℝ) ≠ 0)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    τ * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) =
      -(M 0 1 : ℝ) / (M 1 0 : ℝ) := by
  field_simp
  nlinarith [hquad]

/-- First coordinate identity for the difference operator on the first basis vector. -/
theorem dl_diff_first_tau (M : SL(2, ℤ)) (τ : ℝ)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    (((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ - 1) * τ =
      ((M 1 1 : ℝ) - 1) * τ - (M 0 1 : ℝ) := by
  rw [dl_period_inv M τ hquad]
  nlinarith [hquad]

/-- Second coordinate identity for the difference operator on the first basis vector. -/
theorem dl_diff_second_tau_conj (M : SL(2, ℤ)) (τ : ℝ)
    (hc : (M 1 0 : ℝ) ≠ 0)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    (((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) - 1) *
        (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) =
      ((M 1 1 : ℝ) - 1) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) - (M 0 1 : ℝ) := by
  have hprod := dl_tau_mul_conj M τ hc hquad
  have hmain : (M 1 0 : ℝ) * τ *
      (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) = -(M 0 1 : ℝ) := by
    calc (M 1 0 : ℝ) * τ * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ)
        = (M 1 0 : ℝ) * (τ * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ)) := by ring
      _ = (M 1 0 : ℝ) * (-(M 0 1 : ℝ) / (M 1 0 : ℝ)) := by rw [hprod]
      _ = -(M 0 1 : ℝ) := by field_simp
  nlinarith [hmain]

/-- Integer coefficient comparison at an irrational real number. -/
theorem dl_int_coeff_zero {τ : ℝ} (hτ : Irrational τ) (A B : ℤ)
    (h : (A : ℝ) * τ + (B : ℝ) = 0) : A = 0 ∧ B = 0 := by
  have hA : A = 0 := by
    by_contra hA
    have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    have hτeq : τ = (-(B : ℝ)) / (A : ℝ) := by
      field_simp
      linarith
    have hrat : (((-(B : ℚ) / (A : ℚ) : ℚ) : ℝ)) = (-(B : ℝ)) / (A : ℝ) := by
      push_cast
      ring
    exact hτ.ne_rat (-(B : ℚ) / (A : ℚ)) (hτeq.trans hrat.symm)
  subst hA
  constructor
  · rfl
  · simpa using h

/-- Integer coefficient equality at an irrational real number. -/
theorem dl_int_coeff_eq {τ : ℝ} (hτ : Irrational τ) (a b c d : ℤ)
    (h : (a : ℝ) * τ + (b : ℝ) = (c : ℝ) * τ + (d : ℝ)) : a = c ∧ b = d := by
  have hz : ((a - c : ℤ) : ℝ) * τ + ((b - d : ℤ) : ℝ) = 0 := by
    push_cast
    linarith
  have hab := dl_int_coeff_zero hτ (a - c) (b - d) hz
  constructor
  · omega
  · omega

/-- Expansion of the inverse difference operator on a linear form. -/
theorem dl_inv_sub_mul_linear (M : SL(2, ℤ)) (τ : ℝ)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0)
    (k l : ℝ) :
    (((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ - 1) * (k * τ + l) =
      (((M 1 1 : ℝ) - 1) * k - (M 1 0 : ℝ) * l) * τ +
        (((M 0 0 : ℝ) - 1) * l - (M 0 1 : ℝ) * k) := by
  rw [dl_period_inv M τ hquad]
  have h : (M 1 0 : ℝ) * τ ^ 2 =
      ((M 0 0 : ℝ) - (M 1 1 : ℝ)) * τ + (M 0 1 : ℝ) := by linarith
  linear_combination (-k) * h

/-- Expansion of the difference operator at the conjugate root. -/
theorem dl_sub_mul_linear_conj (M : SL(2, ℤ)) (τ : ℝ)
    (hc : (M 1 0 : ℝ) ≠ 0)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0)
    (k l : ℝ) :
    (((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) - 1) *
        (k * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) + l) =
      (((M 1 1 : ℝ) - 1) * k - (M 1 0 : ℝ) * l) *
          (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) +
        (((M 0 0 : ℝ) - 1) * l - (M 0 1 : ℝ) * k) := by
  rw [dl_period_eq_conj M τ hc]
  have h := dl_conj_quad M τ hc hquad
  have h' : (M 1 0 : ℝ) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) ^ 2 =
      ((M 0 0 : ℝ) - (M 1 1 : ℝ)) *
          (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) + (M 0 1 : ℝ) := by linarith
  linear_combination (-k) * h'

/-- The attracting eigenvector identity `ε τ = a τ + b`. -/
theorem dl_period_mul_tau (M : SL(2, ℤ)) (τ : ℝ)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) * τ = (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) := by
  have h : (M 1 0 : ℝ) * τ ^ 2 =
      ((M 0 0 : ℝ) - (M 1 1 : ℝ)) * τ + (M 0 1 : ℝ) := by linarith
  linear_combination h

/-- The repelling eigenvector identity `ε⁻¹ τ' = a τ' + b`. -/
theorem dl_period_inv_mul_conj (M : SL(2, ℤ)) (τ : ℝ)
    (hc : (M 1 0 : ℝ) ≠ 0)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ *
        (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) =
      (M 0 0 : ℝ) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) + (M 0 1 : ℝ) := by
  rw [dl_period_inv M τ hquad]
  have hprod := dl_tau_mul_conj M τ hc hquad
  have hmain : (M 1 0 : ℝ) * τ *
      (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) = -(M 0 1 : ℝ) := by
    calc (M 1 0 : ℝ) * τ * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ)
        = (M 1 0 : ℝ) * (τ * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ)) := by ring
      _ = (M 1 0 : ℝ) * (-(M 0 1 : ℝ) / (M 1 0 : ℝ)) := by rw [hprod]
      _ = -(M 0 1 : ℝ) := by field_simp
  nlinarith [hmain]

/-- `dτ - b = ε⁻¹ τ`. -/
theorem dl_d_tau_sub (M : SL(2, ℤ)) (τ : ℝ)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    (M 1 1 : ℝ) * τ - (M 0 1 : ℝ) =
      ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ))⁻¹ * τ := by
  rw [dl_period_inv M τ hquad]
  nlinarith [hquad]

/-- `dτ' - b = ε τ'`. -/
theorem dl_d_conj_sub (M : SL(2, ℤ)) (τ : ℝ)
    (hc : (M 1 0 : ℝ) ≠ 0)
    (hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0) :
    (M 1 1 : ℝ) * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) - (M 0 1 : ℝ) =
      ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) *
        (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ) := by
  rw [dl_period_eq_conj M τ hc]
  nlinarith [dl_conj_quad M τ hc hquad]

end SICLean.L4
