import SICLean.L4.G2RawKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2KernelConvergenceAux

open G2

lemma norm_e_formula (z : ℂ) :
    ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  rw [e, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma norm_combU (M : SL(2, ℤ)) (m : ℤ) (z : ℂ) :
    ‖combU M m z‖ = Real.exp (-2 * Real.pi * z.im) := by
  simp [combU, norm_zpow, norm_e_formula]

lemma norm_combV (M : SL(2, ℤ)) (z : ℂ) :
    ‖combV M z‖ = Real.exp (-2 * Real.pi * z.im / epsilon M) := by
  rw [combV, norm_e_formula]
  congr 1
  simp only [Complex.div_ofReal_im]
  ring

lemma norm_le_of_sub_one {w : ℂ} {C : ℝ} (h : ‖w - 1‖ ≤ C) :
    ‖w‖ ≤ C + 1 := by
  calc
    ‖w‖ = ‖(w - 1) + 1‖ := by simp
    _ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C + 1 := by simpa using add_le_add_right h 1

lemma upper_phi_bounded (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (F : Finset (ℤ × ℤ)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ A R : ℝ, 0 < A ∧ 0 < R ∧
      ∀ i ∈ F, ∀ z : ℂ, |z.re| ≤ B → R ≤ z.im →
        ‖modularPhi M i.1 i.2 z (repellingTau M : ℂ)‖ ≤ A ∧
        ‖(modularPhi M i.1 i.2 z (repellingTau M : ℂ))⁻¹‖ ≤ A := by
  obtain ⟨C, κ, R, hC, hκ, hR, h⟩ := fixed_phi_upper_estimate M hM F B hB
  refine ⟨C + 1, R, by linarith, hR, ?_⟩
  intro i hi z hz hy
  have hs := (h i hi z hz hy).2
  have he : Real.exp (-κ * z.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hsum : ‖modularPhi M i.1 i.2 z (repellingTau M : ℂ) - 1‖ +
      ‖(modularPhi M i.1 i.2 z (repellingTau M : ℂ))⁻¹ - 1‖ ≤ C :=
    hs.trans (by simpa using mul_le_mul_of_nonneg_left he hC.le)
  constructor
  · apply norm_le_of_sub_one
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans hsum
  · apply norm_le_of_sub_one
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans hsum

lemma lower_phi_bounded (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (F : Finset (ℤ × ℤ)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ A R : ℝ, 0 < A ∧ 0 < R ∧
      ∀ i ∈ F, ∀ z : ℂ, |z.re| ≤ B → z.im ≤ -R →
        ‖modularPhi M i.1 i.2 z (repellingTau M : ℂ) /
          modularReflectionFactor M i.1 i.2 z (repellingTau M : ℂ)‖ ≤ A ∧
        ‖modularReflectionFactor M i.1 i.2 z (repellingTau M : ℂ) *
          (modularPhi M i.1 i.2 z (repellingTau M : ℂ))⁻¹‖ ≤ A := by
  obtain ⟨C, κ, R, hC, hκ, hR, h⟩ := fixed_phi_lower_estimate M hM F B hB
  refine ⟨C + 1, R, by linarith, hR, ?_⟩
  intro i hi z hz hy
  have hs := (h i hi z hz hy).2
  have he : Real.exp (κ * z.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hκ.le (by linarith))
  have hsum :
      ‖modularPhi M i.1 i.2 z (repellingTau M : ℂ) /
        modularReflectionFactor M i.1 i.2 z (repellingTau M : ℂ) - 1‖ +
      ‖modularReflectionFactor M i.1 i.2 z (repellingTau M : ℂ) *
        (modularPhi M i.1 i.2 z (repellingTau M : ℂ))⁻¹ - 1‖ ≤ C :=
    hs.trans (by simpa using mul_le_mul_of_nonneg_left he hC.le)
  constructor
  · apply norm_le_of_sub_one
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans hsum
  · apply norm_le_of_sub_one
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans hsum

lemma exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) : Real.exp (-t) ≤ 1 / 2 := by
  rw [Real.exp_neg]
  have htwo : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  simpa only [one_div] using
    (inv_le_inv₀ (Real.exp_pos t) (by norm_num : (0 : ℝ) < 2)).mpr htwo

lemma inverse_comb_of_dominance (U V : ℂ) (a : ℝ)
    (ha : 0 < a) (hU : ‖U‖ = a) (hV : ‖V‖ ≤ a / 2) :
    ‖(V - U)⁻¹‖ ≤ 2 / a := by
  have hsub := norm_sub_norm_le U V
  rw [norm_sub_rev, hU] at hsub
  have hd : a / 2 ≤ ‖V - U‖ := by linarith
  rw [norm_inv]
  calc
    ‖V - U‖⁻¹ ≤ (a / 2)⁻¹ :=
      (inv_le_inv₀ (by linarith) (by positivity)).mpr hd
    _ = 2 / a := by ring

lemma reflection_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (r n : ℤ) (z τ : ℂ) : modularReflectionFactor M r n z τ ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (zpow_ne_zero _ (etaMultiplier_ne_zero M hM.1))
      (zpow_ne_zero _ (by norm_num))
  · exact e_ne_zero _

lemma quotient_reflection_bound (P Q S T : ℂ) (A : ℝ)
    (hS : S ≠ 0) (hT : T ≠ 0)
    (hP : ‖P / S‖ ≤ A) (hQ : ‖T * Q⁻¹‖ ≤ A) :
    ‖P / Q‖ ≤ (A * A) * ‖S / T‖ := by
  have heq : P / Q = ((P / S) * (T * Q⁻¹)) * (S / T) := by
    field_simp
  rw [heq, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hP hQ (norm_nonneg _) (by
    exact (norm_nonneg _).trans hP)) (norm_nonneg _)

lemma comb_gap_pos (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < 2 * Real.pi * (1 / epsilon M - 1) := by
  have hi : 1 < 1 / epsilon M :=
    (lt_div_iff₀ (epsilon_pos M hM)).mpr (by simpa using epsilon_lt_one M hM)
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sub_pos.mpr hi)

lemma upper_comb_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m : ℤ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ z.im →
      ‖(combV M z - combU M m z)⁻¹‖ ≤
        2 * Real.exp (2 * Real.pi * z.im) := by
  let a := 2 * Real.pi * (1 / epsilon M - 1)
  have ha : 0 < a := comb_gap_pos M hM
  refine ⟨1 / a, by positivity, ?_⟩
  intro z hz
  have ht : 1 ≤ a * z.im := by
    have := (div_le_iff₀ ha).mp hz
    nlinarith
  have hV : ‖combV M z‖ ≤ Real.exp (-2 * Real.pi * z.im) / 2 := by
    rw [norm_combV]
    calc
      Real.exp (-2 * Real.pi * z.im / epsilon M) =
          Real.exp (-2 * Real.pi * z.im) * Real.exp (-(a * z.im)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [a]
        ring
      _ ≤ Real.exp (-2 * Real.pi * z.im) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (exp_neg_le_half ht) (Real.exp_pos _).le
      _ = _ := by ring
  calc
    ‖(combV M z - combU M m z)⁻¹‖ ≤
        2 / Real.exp (-2 * Real.pi * z.im) :=
      inverse_comb_of_dominance _ _ _ (Real.exp_pos _) (norm_combU M m z) hV
    _ = 2 * Real.exp (2 * Real.pi * z.im) := by
      rw [show -2 * Real.pi * z.im = -(2 * Real.pi * z.im) by ring,
        Real.exp_neg, div_inv_eq_mul]

lemma lower_comb_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m : ℤ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, z.im ≤ -R →
      ‖(combV M z - combU M m z)⁻¹‖ ≤
        2 * Real.exp (2 * Real.pi * z.im / epsilon M) := by
  let a := 2 * Real.pi * (1 / epsilon M - 1)
  have ha : 0 < a := comb_gap_pos M hM
  refine ⟨1 / a, by positivity, ?_⟩
  intro z hz
  have ht : 1 ≤ -(a * z.im) := by
    have hh : 1 / a ≤ -z.im := by linarith
    have := (div_le_iff₀ ha).mp hh
    nlinarith
  have hU : ‖combU M m z‖ ≤ Real.exp (-2 * Real.pi * z.im / epsilon M) / 2 := by
    rw [norm_combU]
    calc
      Real.exp (-2 * Real.pi * z.im) =
          Real.exp (-2 * Real.pi * z.im / epsilon M) * Real.exp (a * z.im) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [a]
        ring
      _ ≤ Real.exp (-2 * Real.pi * z.im / epsilon M) * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa only [neg_neg] using exp_neg_le_half ht
      _ = _ := by ring
  have hinv := inverse_comb_of_dominance (combV M z) (combU M m z) _
    (Real.exp_pos _) (norm_combV M z) hU
  calc
    ‖(combV M z - combU M m z)⁻¹‖ ≤
        2 / Real.exp (-2 * Real.pi * z.im / epsilon M) := by
      simpa only [norm_inv, norm_sub_rev] using hinv
    _ = 2 * Real.exp (2 * Real.pi * z.im / epsilon M) := by
      rw [show -2 * Real.pi * z.im / epsilon M =
        -(2 * Real.pi * z.im / epsilon M) by ring, Real.exp_neg, div_inv_eq_mul]

theorem upper_tail_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ z : ℂ, |z.re| ≤ B → R ≤ z.im →
        ‖rawF M u v m z‖ ≤ C * Real.exp (-2 * Real.pi * rawUpperRate M u * z.im) ∧
        ‖ratioKernel M u v m z‖ ≤
          C * Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) := by
  let F : Finset (ℤ × ℤ) := {(m, 0), (m + 1, 0), (m + v.1, 0), (m + v.1, 1)}
  obtain ⟨A, R, hA, hR, hphi⟩ := upper_phi_bounded M hM F
    (B + |argument M v|) (add_nonneg hB (abs_nonneg _))
  obtain ⟨S, hS, hcomb⟩ := upper_comb_bound M hM m
  refine ⟨2 * (A * A), max R S, by positivity, lt_max_of_lt_left hR, ?_⟩
  intro z hz hy
  have hyR : R ≤ z.im := (le_max_left R S).trans hy
  have hyS : S ≤ z.im := (le_max_right R S).trans hy
  have hzB : |z.re| ≤ B + |argument M v| :=
    hz.trans (le_add_of_nonneg_right (abs_nonneg _))
  have hzshift : |(z + (argument M v : ℂ)).re| ≤ B + |argument M v| := by
    change |z.re + argument M v| ≤ B + |argument M v|
    exact (abs_add_le _ _).trans (add_le_add hz (le_refl _))
  have hyshift : R ≤ (z + (argument M v : ℂ)).im := by simpa using hyR
  have hp := (hphi (m, 0) (by simp [F]) z hzB hyR).1
  have hp' := (hphi (m + 1, 0) (by simp [F]) z hzB hyR).1
  have hq := (hphi (m + v.1, 0) (by simp [F])
    (z + (argument M v : ℂ)) hzshift hyshift).2
  have hq' := (hphi (m + v.1, 1) (by simp [F])
    (z + (argument M v : ℂ)) hzshift hyshift).2
  have hpq : ‖modularPhi M m 0 z (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 0 (z + (argument M v : ℂ)) (repellingTau M : ℂ)‖ ≤ A * A := by
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul hp hq (norm_nonneg _) hA.le
  have hpq' : ‖modularPhi M (m + 1) 0 z (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 1 (z + (argument M v : ℂ)) (repellingTau M : ℂ)‖ ≤ A * A := by
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul hp' hq' (norm_nonneg _) hA.le
  constructor
  · calc
      ‖rawF M u v m z‖ = ‖kernelK M u m z‖ *
          ‖(combV M z - combU M m z)⁻¹‖ *
          ‖modularPhi M m 0 z (repellingTau M : ℂ) /
            modularPhi M (m + v.1) 0 (z + (argument M v : ℂ)) (repellingTau M : ℂ)‖ := by
        rw [rawF, norm_mul, norm_div, div_eq_mul_inv, norm_inv]
      _ ≤ Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
          (2 * Real.exp (2 * Real.pi * z.im)) * (A * A) := by
        rw [kernelK_norm M hM]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hcomb z hyS) (Real.exp_pos _).le)
          hpq (norm_nonneg _) (by positivity)
      _ = (2 * (A * A)) *
          Real.exp (-2 * Real.pi * rawUpperRate M u * z.im) := by
        calc
          _ = (2 * (A * A)) * (Real.exp
              (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
              Real.exp (2 * Real.pi * z.im)) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 2
            dsimp [rawUpperRate]
            field_simp [ne_of_gt (epsilon_pos M hM)]
            ring
  · calc
      ‖ratioKernel M u v m z‖ ≤
          Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
            (A * A) := by
        rw [ratioKernel, norm_mul, kernelK_norm M hM]
        exact mul_le_mul_of_nonneg_left hpq' (Real.exp_pos _).le
      _ ≤ (2 * (A * A)) *
          Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) := by
        nlinarith [mul_nonneg (mul_nonneg hA.le hA.le)
          (Real.exp_pos (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im)).le]

theorem lower_tail_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ z : ℂ, |z.re| ≤ B → z.im ≤ -R →
        ‖rawF M u v m z‖ ≤ C * Real.exp (-2 * Real.pi * rawLowerRate M u v * z.im) ∧
        ‖ratioKernel M u v m z‖ ≤
          C * Real.exp (-2 * Real.pi * finalLowerRate M u v * z.im) := by
  let F : Finset (ℤ × ℤ) := {(m, 0), (m + 1, 0), (m + v.1, 0), (m + v.1, 1)}
  obtain ⟨A, R, hA, hR, hphi⟩ := lower_phi_bounded M hM F
    (B + |argument M v|) (add_nonneg hB (abs_nonneg _))
  obtain ⟨S, hS, hcomb⟩ := lower_comb_bound M hM m
  refine ⟨2 * (A * A), max R S, by positivity, lt_max_of_lt_left hR, ?_⟩
  intro z hz hy
  have hyR : z.im ≤ -R := by linarith [le_max_left R S]
  have hyS : z.im ≤ -S := by linarith [le_max_right R S]
  have hzB : |z.re| ≤ B + |argument M v| :=
    hz.trans (le_add_of_nonneg_right (abs_nonneg _))
  have hzshift : |(z + (argument M v : ℂ)).re| ≤ B + |argument M v| := by
    change |z.re + argument M v| ≤ B + |argument M v|
    exact (abs_add_le _ _).trans (add_le_add hz (le_refl _))
  have hyshift : (z + (argument M v : ℂ)).im ≤ -R := by simpa using hyR
  have hp := (hphi (m, 0) (by simp [F]) z hzB hyR).1
  have hp' := (hphi (m + 1, 0) (by simp [F]) z hzB hyR).1
  have hq := (hphi (m + v.1, 0) (by simp [F])
    (z + (argument M v : ℂ)) hzshift hyshift).2
  have hq' := (hphi (m + v.1, 1) (by simp [F])
    (z + (argument M v : ℂ)) hzshift hyshift).2
  have hpq : ‖modularPhi M m 0 z (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 0 (z + (argument M v : ℂ)) (repellingTau M : ℂ)‖ ≤
      (A * A) * Real.exp (-2 * Real.pi * (inverseOffset M v / epsilon M) * z.im) := by
    calc
      _ ≤ (A * A) * ‖modularReflectionFactor M m 0 z (repellingTau M : ℂ) /
          modularReflectionFactor M (m + v.1) 0 (z + (argument M v : ℂ))
            (repellingTau M : ℂ)‖ :=
        quotient_reflection_bound _ _ _ _ _
          (reflection_ne_zero M hM _ _ _ _) (reflection_ne_zero M hM _ _ _ _) hp hq
      _ = _ := by rw [raw_reflection_ratio_norm M hM]
  have hpq' : ‖modularPhi M (m + 1) 0 z (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 1 (z + (argument M v : ℂ)) (repellingTau M : ℂ)‖ ≤
      (A * A) * Real.exp (-2 * Real.pi *
        ((inverseOffset M v - 1 - epsilon M) / epsilon M) * z.im) := by
    calc
      _ ≤ (A * A) * ‖modularReflectionFactor M (m + 1) 0 z (repellingTau M : ℂ) /
          modularReflectionFactor M (m + v.1) 1 (z + (argument M v : ℂ))
            (repellingTau M : ℂ)‖ :=
        quotient_reflection_bound _ _ _ _ _
          (reflection_ne_zero M hM _ _ _ _) (reflection_ne_zero M hM _ _ _ _) hp' hq'
      _ = _ := by rw [final_reflection_ratio_norm M hM]
  constructor
  · calc
      ‖rawF M u v m z‖ = ‖kernelK M u m z‖ *
          ‖(combV M z - combU M m z)⁻¹‖ *
          ‖modularPhi M m 0 z (repellingTau M : ℂ) /
            modularPhi M (m + v.1) 0 (z + (argument M v : ℂ)) (repellingTau M : ℂ)‖ := by
        rw [rawF, norm_mul, norm_div, div_eq_mul_inv, norm_inv]
      _ ≤ Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
          (2 * Real.exp (2 * Real.pi * z.im / epsilon M)) *
          ((A * A) * Real.exp (-2 * Real.pi * (inverseOffset M v / epsilon M) * z.im)) := by
        rw [kernelK_norm M hM]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hcomb z hyS) (Real.exp_pos _).le)
          hpq (norm_nonneg _) (by positivity)
      _ = (2 * (A * A)) * Real.exp (-2 * Real.pi * rawLowerRate M u v * z.im) := by
        calc
          _ = (2 * (A * A)) * (Real.exp
              (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
              Real.exp (2 * Real.pi * z.im / epsilon M) *
              Real.exp (-2 * Real.pi * (inverseOffset M v / epsilon M) * z.im)) := by ring
          _ = _ := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 2
            dsimp [rawLowerRate]
            ring
  · calc
      ‖ratioKernel M u v m z‖ ≤
          Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
          ((A * A) * Real.exp (-2 * Real.pi *
            ((inverseOffset M v - 1 - epsilon M) / epsilon M) * z.im)) := by
        rw [ratioKernel, norm_mul, kernelK_norm M hM]
        exact mul_le_mul_of_nonneg_left hpq' (Real.exp_pos _).le
      _ = (A * A) * Real.exp (-2 * Real.pi * finalLowerRate M u v * z.im) := by
        calc
          _ = (A * A) * (Real.exp
              (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
              Real.exp (-2 * Real.pi *
                ((inverseOffset M v - 1 - epsilon M) / epsilon M) * z.im)) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 2
            dsimp [finalLowerRate]
            ring
      _ ≤ (2 * (A * A)) * Real.exp (-2 * Real.pi * finalLowerRate M u v * z.im) := by
        nlinarith [mul_nonneg (mul_nonneg hA.le hA.le)
          (Real.exp_pos (-2 * Real.pi * finalLowerRate M u v * z.im)).le]

/-- A continuous line pullback with two exponential tails is integrable. -/
lemma integrable_of_exponential_decay (f : ℝ → ℂ) (hf : Continuous f)
    (C κ R : ℝ) (hκ : 0 < κ) (hR : 0 < R)
    (hbound : ∀ t : ℝ, R ≤ |t| → ‖f t‖ ≤ C * Real.exp (-κ * |t|)) :
    Integrable f := by
  have hleft : IntegrableOn f (Iic (-R)) := by
    apply ((integrableOn_exp_mul_Iic hκ (-R)).const_mul C).mono'
      hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    change t ≤ -R at ht
    have ht₀ : t ≤ 0 := by linarith [ht]
    have h := hbound t (by rw [abs_of_nonpos ht₀]; linarith [ht])
    simpa only [abs_of_nonpos ht₀, mul_neg, neg_mul, neg_neg] using h
  have hright : IntegrableOn f (Ioi R) := by
    apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hκ) R).const_mul C).mono'
      hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change R < t at ht
    have ht₀ : 0 ≤ t := by linarith [ht]
    simpa only [abs_of_nonneg ht₀] using
      hbound t (by rw [abs_of_nonneg ht₀]; exact ht.le)
  have hmid : IntegrableOn f (Icc (-R) R) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have h := (hleft.union hmid).union hright
  have hcover : Iic (-R) ∪ Icc (-R) R ∪ Ioi R = (univ : Set ℝ) := by
    apply eq_univ_of_forall
    intro t
    by_cases ht : t ≤ -R
    · exact Or.inl (Or.inl ht)
    · by_cases ht' : t ≤ R
      · exact Or.inl (Or.inr ⟨(lt_of_not_ge ht).le, ht'⟩)
      · exact Or.inr (lt_of_not_ge ht')
  simpa only [hcover, integrableOn_univ] using h

/-! Actual fixed-parameter regularity, including inverse zeros at Φ poles. -/

lemma repelling_etaDenom (M : SL(2, ℤ)) :
    etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
  simp [etaDenom, epsilon, g1T]

lemma phi_analytic_no_poles (M : SL(2, ℤ)) (hc : 0 < M 1 0) (r n : ℤ)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hp : modularPhiPoleMultiplicity M r n z τ = 0) :
    AnalyticAt ℂ (fun w : ℂ => modularPhi M r n w τ) z := by
  have hj := modularPhi_joint_analytic_no_poles M hc r n (z, τ) ⟨hτ, hp⟩
  simpa only [Function.comp_def] using
    hj.comp (f := fun w : ℂ => (w, τ)) (x := z) (by fun_prop)

lemma phi_inv_analytic_no_zeros (M : SL(2, ℤ)) (hc : 0 < M 1 0) (r n : ℤ)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hz : modularPhiZeroMultiplicity M r n z τ = 0) :
    AnalyticAt ℂ (fun w : ℂ => (modularPhi M r n w τ)⁻¹) z := by
  by_cases hp : modularPhiPoleMultiplicity M r n z τ = 0
  · exact (phi_analytic_no_poles M hc r n z τ hτ hp).inv
      ((modularPhi_ne_zero_iff M hc r n z τ hτ hp).mpr hz)
  · have ho : meromorphicOrderAt
        (fun w : ℂ => (modularPhi M r n w τ)⁻¹) z =
        ((modularPhiPoleMultiplicity M r n z τ : ℤ) : WithTop ℤ) := by
      change meromorphicOrderAt (fun w : ℂ => modularPhi M r n w τ)⁻¹ z = _
      rw [meromorphicOrderAt_inv, modularPhi_order M hc r n z τ hτ]
      simp [modularPhiDivisorOrder, hz]
    apply AnalyticAt.of_meromorphicOrderAt_pos
    · rw [ho]
      exact_mod_cast Nat.pos_of_ne_zero hp
    · simp [modularPhi_pole_value M hc r n z τ hτ hp]

/-- Return to the common chain's coordinate before testing its explicit guard. -/
def commonCoordinate (M : SL(2, ℤ)) (m j : ℤ) (z : ℂ) : ℂ :=
  (M 1 0 : ℂ) * z + (epsilon M : ℂ) * (m : ℂ) +
    (j : ℂ) * (length M : ℂ)

lemma right_mem_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (K J j : ℕ) (hj : j ≤ (M 1 0).toNat)
    (hK : j = (M 1 0).toNat → 1 ≤ K) :
    rightPoint M K J + (j : ℝ) * length M ∈ guardSet M v := by
  change _ ∈ (commonRight M ∪ commonLeft M v) ∪ _
  refine Or.inl (Or.inl ?_)
  change _ ∈ (⋃ i : Fin (M 1 0).toNat,
    translateSet (rightCoordinates M) ((i : ℝ) * length M)) ∪ _
  by_cases hjlt : j < (M 1 0).toNat
  · refine Or.inl (Set.mem_iUnion.mpr ⟨⟨j, hjlt⟩, ?_⟩)
    exact ⟨rightPoint M K J, ⟨K, J, rfl⟩, rfl⟩
  · have hjeq : j = (M 1 0).toNat := by omega
    have hjcast : (j : ℝ) = (M 1 0 : ℝ) := by
      rw [hjeq]
      exact_mod_cast Int.toNat_of_nonneg hM.1.le
    refine Or.inr ⟨rightPoint M K J, ⟨K, J, hK hjeq, rfl⟩, ?_⟩
    rw [hjcast]

lemma left_mem_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (K J j : ℕ) (hj : j ≤ (M 1 0).toNat)
    (hJ : j = (M 1 0).toNat → 1 ≤ J) :
    leftPoint M v K J + (j : ℝ) * length M ∈ guardSet M v := by
  change _ ∈ (commonRight M ∪ commonLeft M v) ∪ _
  refine Or.inl (Or.inr ?_)
  change _ ∈ (⋃ i : Fin (M 1 0).toNat,
    translateSet (leftCoordinates M v) ((i : ℝ) * length M)) ∪ _
  by_cases hjlt : j < (M 1 0).toNat
  · refine Or.inl (Set.mem_iUnion.mpr ⟨⟨j, hjlt⟩, ?_⟩)
    exact ⟨leftPoint M v K J, ⟨K, J, rfl⟩, rfl⟩
  · have hjeq : j = (M 1 0).toNat := by omega
    have hjcast : (j : ℝ) = (M 1 0 : ℝ) := by
      rw [hjeq]
      exact_mod_cast Int.toNat_of_nonneg hM.1.le
    refine Or.inr ⟨leftPoint M v K J, ⟨K, J, hJ hjeq, rfl⟩, ?_⟩
    rw [hjcast]

/-- The guard's finite component range covers every integer m. -/
lemma comb_mem_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m k : ℤ) (j : Fin ((M 1 0).toNat + 1)) :
    combCoordinate M m k + (j : ℝ) * length M ∈ guardSet M v := by
  have hrem₀ : 0 ≤ m % M 1 0 := Int.emod_nonneg m hM.1.ne'
  have hrem : m % M 1 0 < M 1 0 := Int.emod_lt_of_pos m hM.1
  let m₀ : Fin (M 1 0).toNat := ⟨(m % M 1 0).toNat, by omega⟩
  let k₀ : ℤ := k + (1 - M 1 1) * (m / M 1 0)
  have hm₀ : (m₀ : ℤ) = m % M 1 0 := Int.toNat_of_nonneg hrem₀
  have hdiv : m % M 1 0 + M 1 0 * (m / M 1 0) = m :=
    Int.emod_add_mul_ediv m (M 1 0)
  have hind : (1 - M 1 1) * m + M 1 0 * k =
      (1 - M 1 1) * (m₀ : ℤ) + M 1 0 * k₀ := by
    rw [hm₀]
    dsimp [k₀]
    linear_combination -(1 - M 1 1) * hdiv
  have hcoord : combCoordinate M m k = combCoordinate M (m₀ : ℤ) k₀ := by
    unfold combCoordinate
    rw [hind]
  change _ ∈ (commonRight M ∪ commonLeft M v) ∪ _
  exact Or.inr ⟨m₀, k₀, j, by rw [hcoord]⟩

lemma comb_zero_coordinate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m : ℤ) (z : ℂ) (hz : combV M z - combU M m z = 0) :
    ∃ k : ℤ, (M 1 0 : ℂ) * z + (epsilon M : ℂ) * (m : ℂ) =
      (combCoordinate M m k : ℂ) := by
  have heps : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
  have hL : (1 : ℂ) - (epsilon M : ℂ) ≠ 0 := by
    exact_mod_cast (sub_pos.mpr (epsilon_lt_one M hM)).ne'
  have he : e (z / (epsilon M : ℂ)) =
      e ((m : ℂ) * (repellingTau M : ℂ) + z) := by
    simpa only [combV, combU, e_int_mul, e_add'] using sub_eq_zero.mp hz
  have hone : e (z / (epsilon M : ℂ) -
      ((m : ℂ) * (repellingTau M : ℂ) + z)) = 1 := by
    rw [sub_eq_add_neg, e_add', e_neg', he]
    exact mul_inv_cancel₀ (e_ne_zero _)
  obtain ⟨k, hk⟩ := e_eq_one_iff_int hone
  have hmul : z = ((m : ℂ) * (repellingTau M : ℂ) + z + (k : ℂ)) *
      (epsilon M : ℂ) := by
    apply (div_eq_iff heps).mp
    linear_combination hk
  have hT : (M 1 0 : ℂ) * (repellingTau M : ℂ) + (M 1 1 : ℂ) =
      (epsilon M : ℂ) := repelling_etaDenom M
  refine ⟨k, ?_⟩
  simp only [combCoordinate, scale, length]
  push_cast
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hL).mpr
  linear_combination (M 1 0 : ℂ) * hmul +
    (epsilon M : ℂ) * (m : ℂ) * hT

lemma raw_regular_of_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : ℤ) (j : Fin ((M 1 0).toNat + 1)) (z : ℂ)
    (hsafe : ∀ x ∈ guardSet M v, commonCoordinate M m (j : ℤ) z ≠ (x : ℂ)) :
    modularPhiPoleMultiplicity M m 0 z (repellingTau M : ℂ) = 0 ∧
      modularPhiZeroMultiplicity M (m + v.1) 0
        (z + (argument M v : ℂ)) (repellingTau M : ℂ) = 0 ∧
      combV M z - combU M m z ≠ 0 := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
  have hj : j.val ≤ (M 1 0).toNat := by omega
  have hp : modularPhiPoleIndices M m 0 z (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, hz⟩
    apply hsafe (rightPoint M (K + 1) J + (j.val : ℝ) * length M)
      (right_mem_guard M hM v (K + 1) J j.val hj (by omega))
    dsimp [modularPhiPolePoint] at hz
    rw [repelling_etaDenom] at hz
    have hmul := (eq_div_iff hc).mp hz
    dsimp [commonCoordinate, rightPoint]
    push_cast at hmul ⊢
    linear_combination hmul
  have hz : modularPhiZeroIndices M (m + v.1) 0
      (z + (argument M v : ℂ)) (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, hz⟩
    apply hsafe (leftPoint M v K (J + 1) + (j.val : ℝ) * length M)
      (left_mem_guard M hM v K (J + 1) j.val hj (by omega))
    dsimp [modularPhiZeroPoint] at hz
    rw [repelling_etaDenom] at hz
    have hmul := (eq_div_iff hc).mp hz
    have harg := congrArg (fun t : ℝ => (t : ℂ)) (argument_common_coordinate M hM v)
    change _ = (inverseOffset M v : ℂ) at harg
    dsimp [commonCoordinate, leftPoint]
    push_cast at hmul harg ⊢
    linear_combination hmul - harg
  refine ⟨by simp [modularPhiPoleMultiplicity, hp],
    by simp [modularPhiZeroMultiplicity, hz], ?_⟩
  intro hzero
  obtain ⟨k, hk⟩ := comb_zero_coordinate M hM m z hzero
  apply hsafe (combCoordinate M m k + (j : ℝ) * length M)
    (comb_mem_guard M hM v m k j)
  dsimp [commonCoordinate]
  rw [hk]
  push_cast
  rfl

lemma ratio_regular_of_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : ℤ) (j : Fin (M 1 0).toNat) (z : ℂ)
    (hsafe : ∀ x ∈ guardSet M v, commonCoordinate M m (j : ℤ) z ≠ (x : ℂ)) :
    modularPhiPoleMultiplicity M (m + 1) 0 z (repellingTau M : ℂ) = 0 ∧
      modularPhiZeroMultiplicity M (m + v.1) 1
        (z + (argument M v : ℂ)) (repellingTau M : ℂ) = 0 := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
  have hp : modularPhiPoleIndices M (m + 1) 0 z (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, hz⟩
    apply hsafe (rightPoint M K J + (j.val : ℝ) * length M)
      (right_mem_guard M hM v K J j.val j.isLt.le (by omega))
    dsimp [modularPhiPolePoint] at hz
    rw [repelling_etaDenom] at hz
    have hmul := (eq_div_iff hc).mp hz
    dsimp [commonCoordinate, rightPoint]
    push_cast at hmul ⊢
    linear_combination hmul
  have hz : modularPhiZeroIndices M (m + v.1) 1
      (z + (argument M v : ℂ)) (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, hz⟩
    apply hsafe (leftPoint M v K J + (j.val : ℝ) * length M)
      (left_mem_guard M hM v K J j.val j.isLt.le (by omega))
    dsimp [modularPhiZeroPoint] at hz
    rw [repelling_etaDenom] at hz
    have hmul := (eq_div_iff hc).mp hz
    have harg := congrArg (fun t : ℝ => (t : ℂ)) (argument_common_coordinate M hM v)
    change _ = (inverseOffset M v : ℂ) at harg
    dsimp [commonCoordinate, leftPoint]
    push_cast at hmul harg ⊢
    linear_combination hmul - harg
  exact ⟨by simp [modularPhiPoleMultiplicity, hp],
    by simp [modularPhiZeroMultiplicity, hz]⟩

lemma rawF_analytic_of_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (j : Fin ((M 1 0).toNat + 1)) (z : ℂ)
    (hsafe : ∀ x ∈ guardSet M v, commonCoordinate M m (j : ℤ) z ≠ (x : ℂ)) :
    AnalyticAt ℂ (rawF M u v m) z := by
  obtain ⟨hp, hz, hcomb⟩ := raw_regular_of_guard M hM v m j z hsafe
  have hτ : (repellingTau M : ℂ) ∈ modularPhiDomain M :=
    real_mem_modularPhiDomain M _ (epsilon_pos M hM)
  have hP := phi_analytic_no_poles M hM.1 m 0 z _ hτ hp
  have hQ := phi_inv_analytic_no_zeros M hM.1 (m + v.1) 0
    (z + (argument M v : ℂ)) _ hτ hz
  have hQs : AnalyticAt ℂ (fun w : ℂ =>
      (modularPhi M (m + v.1) 0 (w + (argument M v : ℂ))
        (repellingTau M : ℂ))⁻¹) z :=
    hQ.comp (f := fun w : ℂ => w + (argument M v : ℂ)) (by fun_prop)
  have hK : AnalyticAt ℂ (kernelK M u m) z := by
    unfold kernelK e
    fun_prop
  have hC : AnalyticAt ℂ (fun w : ℂ => combV M w - combU M m w) z := by
    unfold combV combU e
    fun_prop
  change AnalyticAt ℂ (fun w : ℂ => rawF M u v m w) z
  simpa only [rawF, div_eq_mul_inv] using
    (hK.fun_div hC hcomb).fun_mul (hP.fun_mul hQs)

lemma ratio_analytic_of_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (j : Fin (M 1 0).toNat) (z : ℂ)
    (hsafe : ∀ x ∈ guardSet M v, commonCoordinate M m (j : ℤ) z ≠ (x : ℂ)) :
    AnalyticAt ℂ (ratioKernel M u v m) z := by
  obtain ⟨hp, hz⟩ := ratio_regular_of_guard M hM v m j z hsafe
  have hτ : (repellingTau M : ℂ) ∈ modularPhiDomain M :=
    real_mem_modularPhiDomain M _ (epsilon_pos M hM)
  have hP := phi_analytic_no_poles M hM.1 (m + 1) 0 z _ hτ hp
  have hQ := phi_inv_analytic_no_zeros M hM.1 (m + v.1) 1
    (z + (argument M v : ℂ)) _ hτ hz
  have hQs : AnalyticAt ℂ (fun w : ℂ =>
      (modularPhi M (m + v.1) 1 (w + (argument M v : ℂ))
        (repellingTau M : ℂ))⁻¹) z :=
    hQ.comp (f := fun w : ℂ => w + (argument M v : ℂ)) (by fun_prop)
  have hK : AnalyticAt ℂ (kernelK M u m) z := by
    unfold kernelK e
    fun_prop
  change AnalyticAt ℂ (fun w : ℂ => ratioKernel M u v m w) z
  simpa only [ratioKernel, div_eq_mul_inv] using hK.fun_mul (hP.fun_mul hQs)

lemma common_vertical_avoids_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (t : ℝ) : ∀ x ∈ guardSet M v, g1VerticalPoint D.crossing t ≠ (x : ℂ) := by
  intro x hx he
  have hline := (commonChain_boundary_avoids M hM v δ D hD).1
  have hxr : D.crossing = x := by
    simpa [g1VerticalPoint] using congrArg Complex.re he
  apply hline
  simpa only [hxr] using hx

lemma common_circle_avoids_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (r : ℝ) (hr : r ∈ D.centers) (θ : ℝ) :
    ∀ x ∈ guardSet M v, circleMap (r : ℂ) (D.radius r) θ ≠ (x : ℂ) := by
  have hpos : 0 < D.radius r := by
    obtain ⟨_, _, _, _, _, _, hrad⟩ := hD
    exact (hrad r hr).1
  intro x hx he
  apply (commonChain_boundary_avoids M hM v δ D hD).2 r hr x hx
  have hn : ‖circleMap (r : ℂ) (D.radius r) θ - (r : ℂ)‖ = D.radius r := by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hpos]
  rw [he] at hn
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hn

lemma component_vertical_avoids_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m j : ℤ) (t : ℝ) : ∀ x ∈ guardSet M v,
      commonCoordinate M m j
        (g1VerticalPoint (componentChain M D m j).crossing t) ≠ (x : ℂ) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
  have hp := componentChain_verticalPoint M hM D m j t
  have hmul := (eq_div_iff hc).mp hp
  have hcoord : commonCoordinate M m j
      (g1VerticalPoint (componentChain M D m j).crossing t) =
      g1VerticalPoint D.crossing ((M 1 0 : ℝ) * t) := by
    unfold commonCoordinate
    linear_combination hmul
  rw [hcoord]
  exact common_vertical_avoids_guard M hM v δ D hD _

lemma component_circle_avoids_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m j : ℤ) (r : ℝ) (hr : r ∈ (componentChain M D m j).centers) (θ : ℝ) :
    ∀ x ∈ guardSet M v, commonCoordinate M m j
      (circleMap (r : ℂ) ((componentChain M D m j).radius r) θ) ≠ (x : ℂ) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
  have hcR : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hM.1.ne'
  change r ∈ D.centers.image
    (fun s => (s - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ)) at hr
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
  have hcancel : (M 1 0 : ℝ) *
      ((s - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ)) +
      epsilon M * (m : ℝ) + (j : ℝ) * length M = s := by
    field_simp
    ring
  have hrad : (componentChain M D m j).radius
      ((s - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ)) =
      D.radius s / (M 1 0 : ℝ) := by
    change D.radius ((M 1 0 : ℝ) *
      ((s - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ)) +
      epsilon M * (m : ℝ) + (j : ℝ) * length M) / (M 1 0 : ℝ) = _
    rw [hcancel]
  rw [hrad]
  have hp := componentChain_circlePoint M hM D m j s θ
  have hmul := (eq_div_iff hc).mp hp
  have hcoord : commonCoordinate M m j
      (circleMap (((s - epsilon M * (m : ℝ) - (j : ℝ) * length M) /
        (M 1 0 : ℝ) : ℝ) : ℂ) (D.radius s / (M 1 0 : ℝ)) θ) =
      circleMap (s : ℂ) (D.radius s) θ := by
    unfold commonCoordinate
    linear_combination hmul
  rw [hcoord]
  exact common_circle_avoids_guard M hM v δ D hD s hs θ

lemma rawF_vertical_continuous (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : ℤ) (j : Fin ((M 1 0).toNat + 1)) :
    Continuous (fun t : ℝ => rawF M u v m
      (g1VerticalPoint (componentChain M D m (j : ℤ)).crossing t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hA := rawF_analytic_of_guard M hM u v m j _
    (component_vertical_avoids_guard M hM v δ D hD m (j : ℤ) t)
  exact hA.continuousAt.comp (f := fun t : ℝ =>
    g1VerticalPoint (componentChain M D m (j : ℤ)).crossing t)
    (by unfold g1VerticalPoint; fun_prop)

lemma rawF_circle_continuous (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : ℤ) (j : Fin ((M 1 0).toNat + 1))
    (r : ℝ) (hr : r ∈ (componentChain M D m (j : ℤ)).centers) :
    Continuous (fun θ : ℝ => rawF M u v m
      (circleMap (r : ℂ) ((componentChain M D m (j : ℤ)).radius r) θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hA := rawF_analytic_of_guard M hM u v m j _
    (component_circle_avoids_guard M hM v δ D hD m (j : ℤ) r hr θ)
  exact hA.continuousAt.comp (continuous_circleMap _ _).continuousAt

lemma ratio_vertical_continuous (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : ℤ) (j : Fin (M 1 0).toNat) :
    Continuous (fun t : ℝ => ratioKernel M u v m
      (g1VerticalPoint (componentChain M D m (j : ℤ)).crossing t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hA := ratio_analytic_of_guard M hM u v m j _
    (component_vertical_avoids_guard M hM v δ D hD m (j : ℤ) t)
  exact hA.continuousAt.comp (f := fun t : ℝ =>
    g1VerticalPoint (componentChain M D m (j : ℤ)).crossing t)
    (by unfold g1VerticalPoint; fun_prop)

lemma ratio_circle_continuous (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : ℤ) (j : Fin (M 1 0).toNat)
    (r : ℝ) (hr : r ∈ (componentChain M D m (j : ℤ)).centers) :
    Continuous (fun θ : ℝ => ratioKernel M u v m
      (circleMap (r : ℂ) ((componentChain M D m (j : ℤ)).radius r) θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hA := ratio_analytic_of_guard M hM u v m j _
    (component_circle_avoids_guard M hM v δ D hD m (j : ℤ) r hr θ)
  exact hA.continuousAt.comp (continuous_circleMap _ _).continuousAt

end SICLean.L4.G2KernelConvergenceAux
