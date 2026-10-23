import SICLean.L4.G2ContourChain
import SICLean.L4.ModularSectorUpper

set_option autoImplicit false

/-!
Fixed real-parameter consequences of the modular sector estimates. The only geometric step is that a
sufficiently high part of a bounded vertical strip lies in the fixed sector with angle π/6.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2RawKernelAux

open ModularSector

theorem upperSector_of_im_dominates (R : ℝ) (z : ℂ)
    (him : 0 < z.im) (hre : |z.re| ≤ z.im) (hR : R ≤ z.im) :
    z ∈ upperSector (Real.pi / 6) R := by
  have hz : z ≠ 0 := fun h => him.ne' (by simp [h])
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnle : ‖z‖ ≤ 2 * z.im := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * z.im := by rw [abs_of_pos him]; linarith
  have hratio : (1 : ℝ) / 2 ≤ z.im / ‖z‖ := by
    apply (le_div_iff₀ hn).mpr
    linarith
  have hasin : Real.pi / 6 ≤ Real.arcsin (z.im / ‖z‖) := by
    apply (Real.le_arcsin_iff_sin_le' (by constructor <;> linarith [Real.pi_pos])).mpr
    simpa only [Real.sin_pi_div_six] using hratio
  have hasin' := Real.arcsin_le_pi_div_two (z.im / ‖z‖)
  refine ⟨hR.trans (Complex.im_le_norm z), ?_, ?_⟩
  · by_cases hr : 0 ≤ z.re
    · rw [Complex.arg_of_re_nonneg hr]
      exact hasin
    · rw [Complex.arg_of_re_neg_of_im_nonneg (lt_of_not_ge hr) him.le,
        Complex.neg_im, neg_div, Real.arcsin_neg]
      linarith [Real.pi_pos]
  · by_cases hr : 0 ≤ z.re
    · rw [Complex.arg_of_re_nonneg hr]
      linarith [Real.pi_pos]
    · rw [Complex.arg_of_re_neg_of_im_nonneg (lt_of_not_ge hr) him.le,
        Complex.neg_im, neg_div, Real.arcsin_neg]
      linarith

theorem fixed_real_phi_upper_estimate (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (hT : 0 < realDenom M τ₀)
    (F : Finset (ℤ × ℤ)) (B : ℝ) (_hB : 0 ≤ B) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ i ∈ F, ∀ z : ℂ, |z.re| ≤ B → R ≤ z.im →
        (z, (τ₀ : ℂ)) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ‖modularPhi M i.1 i.2 z (τ₀ : ℂ) - 1‖ +
          ‖(modularPhi M i.1 i.2 z (τ₀ : ℂ))⁻¹ - 1‖ ≤
            C * Real.exp (-κ * z.im) := by
  have hα : 0 < Real.pi / 6 := by positivity
  have hα' : Real.pi / 6 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨ρ, C, k, R₁, hρ, hC, hk, hR₁, hρeq, _, hdec⟩ :=
    upper_half_upper_decay M hM F τ₀ (Real.pi / 6) hT hα hα'
  obtain ⟨R₂, hR₂, hdiv⟩ :=
    tail_divisor_free M hM F τ₀ (Real.pi / 6) hT hα hα'
  have hτ : (τ₀ : ℂ) ∈ upperParameterDisk τ₀ ρ := by
    simp [upperParameterDisk, parameterDisk, hρ.le]
  have hτ' : (τ₀ : ℂ) ∈ parameterDisk τ₀ (parameterRadius M τ₀ (Real.pi / 6)) := by
    rw [← hρeq]
    exact hτ.1
  let R := max 1 (max B (max R₁ R₂))
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBR : B ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR₁R : R₁ ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hR₂R : R₂ ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨C, k, R, hC, hk, hR, ?_⟩
  intro i hi z hzre hzim
  have him : 0 < z.im := hR.trans_le hzim
  have hre : |z.re| ≤ z.im := hzre.trans (hBR.trans hzim)
  have hz₁ := upperSector_of_im_dominates R₁ z him hre (hR₁R.trans hzim)
  have hz₂ := upperSector_of_im_dominates R₂ z him hre (hR₂R.trans hzim)
  refine ⟨(hdiv _ hτ' i hi z (Or.inl hz₂)).2.2, ?_⟩
  calc
    ‖modularPhi M i.1 i.2 z (τ₀ : ℂ) - 1‖ +
        ‖(modularPhi M i.1 i.2 z (τ₀ : ℂ))⁻¹ - 1‖
      ≤ C * Real.exp (-k * ‖z‖) := hdec _ hτ i hi z hz₁
    _ ≤ C * Real.exp (-k * z.im) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      nlinarith [Complex.im_le_norm z]

theorem fixed_real_phi_lower_estimate (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (hT : 0 < realDenom M τ₀)
    (F : Finset (ℤ × ℤ)) (B : ℝ) (_hB : 0 ≤ B) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ i ∈ F, ∀ z : ℂ, |z.re| ≤ B → z.im ≤ -R →
        (z, (τ₀ : ℂ)) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ‖modularPhi M i.1 i.2 z (τ₀ : ℂ) /
          modularReflectionFactor M i.1 i.2 z (τ₀ : ℂ) - 1‖ +
        ‖modularReflectionFactor M i.1 i.2 z (τ₀ : ℂ) *
          (modularPhi M i.1 i.2 z (τ₀ : ℂ))⁻¹ - 1‖ ≤
            C * Real.exp (κ * z.im) := by
  have hα : 0 < Real.pi / 6 := by positivity
  have hα' : Real.pi / 6 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨ρ, C, k, R₁, hρ, hC, hk, hR₁, hρeq, _, hdec⟩ :=
    upper_half_lower_decay M hM F τ₀ (Real.pi / 6) hT hα hα'
  obtain ⟨R₂, hR₂, hdiv⟩ :=
    tail_divisor_free M hM F τ₀ (Real.pi / 6) hT hα hα'
  have hτ : (τ₀ : ℂ) ∈ upperParameterDisk τ₀ ρ := by
    simp [upperParameterDisk, parameterDisk, hρ.le]
  have hτ' : (τ₀ : ℂ) ∈ parameterDisk τ₀ (parameterRadius M τ₀ (Real.pi / 6)) := by
    rw [← hρeq]
    exact hτ.1
  let R := max 1 (max B (max R₁ R₂))
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBR : B ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR₁R : R₁ ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hR₂R : R₂ ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨C, k, R, hC, hk, hR, ?_⟩
  intro i hi z hzre hzim
  have him : 0 < (-z).im := by simp only [Complex.neg_im]; linarith
  have hre : |(-z).re| ≤ (-z).im := by
    simp only [Complex.neg_re, abs_neg, Complex.neg_im]
    linarith [hzre, hBR]
  have hz₁ := upperSector_of_im_dominates R₁ (-z) him hre (by
    simp only [Complex.neg_im]; linarith)
  have hz₂ := upperSector_of_im_dominates R₂ (-z) him hre (by
    simp only [Complex.neg_im]; linarith)
  refine ⟨(hdiv _ hτ' i hi z (Or.inr hz₂)).2.2, ?_⟩
  calc
    ‖modularPhi M i.1 i.2 z (τ₀ : ℂ) /
        modularReflectionFactor M i.1 i.2 z (τ₀ : ℂ) - 1‖ +
      ‖modularReflectionFactor M i.1 i.2 z (τ₀ : ℂ) *
        (modularPhi M i.1 i.2 z (τ₀ : ℂ))⁻¹ - 1‖
      ≤ C * Real.exp (-k * ‖z‖) := hdec _ hτ i hi z hz₁
    _ ≤ C * Real.exp (k * z.im) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      have hnorm := Complex.im_le_norm (-z)
      simp only [Complex.neg_im, norm_neg] at hnorm
      nlinarith

theorem fixed_phi_upper_estimate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (F : Finset (ℤ × ℤ)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ i ∈ F, ∀ z : ℂ, |z.re| ≤ B → R ≤ z.im →
        (z, (G2.repellingTau M : ℂ)) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ‖modularPhi M i.1 i.2 z (G2.repellingTau M : ℂ) - 1‖ +
          ‖(modularPhi M i.1 i.2 z (G2.repellingTau M : ℂ))⁻¹ - 1‖ ≤
            C * Real.exp (-κ * z.im) := by
  apply fixed_real_phi_upper_estimate M hM.1 (G2.repellingTau M) _ F B hB
  simpa only [realDenom, G2.epsilon, g1T] using G2.epsilon_pos M hM

theorem fixed_phi_lower_estimate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (F : Finset (ℤ × ℤ)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ i ∈ F, ∀ z : ℂ, |z.re| ≤ B → z.im ≤ -R →
        (z, (G2.repellingTau M : ℂ)) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ‖modularPhi M i.1 i.2 z (G2.repellingTau M : ℂ) /
          modularReflectionFactor M i.1 i.2 z (G2.repellingTau M : ℂ) - 1‖ +
        ‖modularReflectionFactor M i.1 i.2 z (G2.repellingTau M : ℂ) *
          (modularPhi M i.1 i.2 z (G2.repellingTau M : ℂ))⁻¹ - 1‖ ≤
            C * Real.exp (κ * z.im) := by
  apply fixed_real_phi_lower_estimate M hM.1 (G2.repellingTau M) _ F B hB
  simpa only [realDenom, G2.epsilon, g1T] using G2.epsilon_pos M hM

open G2

lemma rawKernel_norm_e (z : ℂ) : ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  rw [e, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma rawKernel_reflection_norm (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (r n s k : ℤ) (z w : ℂ) :
    ‖modularReflectionFactor M r n z (repellingTau M : ℂ) /
      modularReflectionFactor M s k w (repellingTau M : ℂ)‖ =
      Real.exp (-2 * Real.pi *
        (modularReflectionPolynomial M r n z (repellingTau M : ℂ) -
         modularReflectionPolynomial M s k w (repellingTau M : ℂ)).im) := by
  have hm : ‖etaMultiplier M‖ ≠ 0 := norm_ne_zero_iff.mpr (etaMultiplier_ne_zero M hM.1)
  simp only [modularReflectionFactor, norm_div, norm_mul, norm_zpow, norm_neg,
    norm_one, one_zpow, mul_one, rawKernel_norm_e]
  rw [mul_div_mul_left _ _ (zpow_ne_zero _ hm), ← Real.exp_sub, Complex.sub_im]
  congr 1
  ring

lemma rawKernel_polynomial_im (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (r n : ℤ) (z : ℂ) :
    (modularReflectionPolynomial M r n z (repellingTau M : ℂ)).im =
      -(1 / 2 : ℝ) * ((M 1 0 : ℝ) * (2 * z.re * z.im) / epsilon M +
        (2 * (r : ℝ) - 1 - (2 * (n : ℝ) - 1) / epsilon M) * z.im) := by
  have hT : etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
    simp [etaDenom, epsilon, g1T]
  rw [modularReflectionPolynomial, hT, repellingTau_fixedPoint M hM]
  simp [modularBernoulliTwo, pow_two, Complex.mul_im, Complex.mul_re]
  ring

/-! Isolated exponential denominators, actual off-axis units, exact shifts, and the two rational
identities used by the kernel germs. -/


lemma e_affine_eventually_ne_one (a b z : ℂ) (ha : a ≠ 0) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, e (a * w + b) ≠ 1 := by
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => e (a * w + b)) Set.univ := by
    intro w _
    unfold e
    fun_prop
  rcases (hf z (Set.mem_univ z)).eventually_eq_or_eventually_ne analyticAt_const with hz | hz
  · have hall : Set.EqOn (fun w : ℂ => e (a * w + b)) (fun _ => 1) Set.univ :=
      hf.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
        isPreconnected_univ (Set.mem_univ z) hz
    have hi := hall (x := a⁻¹ * (Complex.I - b)) (Set.mem_univ _)
    have hx : a * (a⁻¹ * (Complex.I - b)) + b = Complex.I := by field_simp; ring
    dsimp only at hi
    rw [hx] at hi
    obtain ⟨k, hk⟩ := e_eq_one_iff_int hi
    have := congrArg Complex.im hk
    norm_num at this
  · exact hz

lemma e_affine_difference_eventually_ne_zero (a b c d z : ℂ) (hac : a ≠ c) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, e (a * w + b) - e (c * w + d) ≠ 0 := by
  filter_upwards [e_affine_eventually_ne_one (a - c) (b - d) z (sub_ne_zero.mpr hac)]
    with w hw
  intro hzero
  apply hw
  have heq : e (a * w + b) = e ((a - c) * w + (b - d)) * e (c * w + d) := by
    rw [← e_add']
    congr 1
    ring
  have hmul : e ((a - c) * w + (b - d)) * e (c * w + d) = 1 * e (c * w + d) := by
    rw [← heq, sub_eq_zero.mp hzero, one_mul]
  exact mul_right_cancel₀ (e_ne_zero _) hmul

lemma e_sub_ne_zero_of_im_ne (a b : ℂ) (him : a.im ≠ b.im) : e a - e b ≠ 0 := by
  intro hz
  have heq : e a = e b := sub_eq_zero.mp hz
  have hone : e (a - b) = 1 := by
    rw [sub_eq_add_neg, e_add', e_neg', heq, mul_inv_cancel₀ (e_ne_zero b)]
  obtain ⟨k, hk⟩ := e_eq_one_iff_int hone
  have hk' := congrArg Complex.im hk
  simp only [Complex.sub_im, Complex.intCast_im] at hk'
  exact him (sub_eq_zero.mp hk')

lemma phi_nonreal_unit (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℝ) (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousAt (fun w => modularPhi M m n w (τ : ℂ)) z ∧
      modularPhi M m n z (τ : ℂ) ≠ 0 := by
  have hunit := modularPhi_real_off_lattice M hM m n τ hT z (by
    rintro ⟨k, l, h⟩
    apply hz
    rw [h]
    simp)
  refine ⟨?_, (modularPhi_ne_zero_iff M hM m n z (τ : ℂ) hunit.1 hunit.2.1).mpr hunit.2.2⟩
  have hc := (modularPhi_joint_analytic_no_poles M hM m n (z, (τ : ℂ))
    ⟨hunit.1, hunit.2.1⟩).continuousAt
  exact hc.comp (f := fun w : ℂ => (w, (τ : ℂ)))
    (continuousAt_id.prodMk continuousAt_const)

lemma modularPhi_period (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m n : ℤ) (z : ℂ) :
    modularPhi M (m + M 1 0) n (z - (G2.epsilon M : ℂ)) (G2.repellingTau M : ℂ) =
      modularPhi M m n z (G2.repellingTau M : ℂ) := by
  have heps : (G2.epsilon M : ℂ) = (M 1 0 : ℂ) * (G2.repellingTau M : ℂ) + (M 1 1 : ℂ) := by
    simp [G2.epsilon, g1T]
  have h := modularPhi_shift_integer M hM.1 (m + M 1 0) n
    (-(M 1 0)) (-(M 1 1)) z (G2.repellingTau M : ℂ)
  rw [heps]
  convert h using 1 <;> push_cast <;> congr 1 <;> ring

lemma phi_eventually_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, modularPhi M m n w τ ≠ 0 := by
  filter_upwards [modularPhi_reflection_germ M hM m n z τ hτ] with w hw
  have hR : modularReflectionFactor M m n w τ ≠ 0 := by
    unfold modularReflectionFactor
    exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (etaMultiplier_ne_zero M hM))
      (zpow_ne_zero _ (by norm_num))) (e_ne_zero _)
  exact left_ne_zero_of_mul (hw ▸ hR)

lemma modularPhi_translate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m n : ℤ) (z : ℂ) :
    modularPhi M (m + 1 - M 0 0) n (z + ((M 0 0 : ℂ) * (G2.repellingTau M : ℂ) + (M 0 1 : ℂ))) (G2.repellingTau M : ℂ) =
      modularPhi M (m + 1) (n + 1) z (G2.repellingTau M : ℂ) := by
  have h := modularPhi_shift_integer M hM.1 (m + 1 - M 0 0) n
    (M 0 0) (M 0 1) z (G2.repellingTau M : ℂ)
  have hn : n + M 1 1 * M 0 0 - M 1 0 * M 0 1 = n + 1 := by
    linear_combination det_coe_int M
  have hm : m + 1 - M 0 0 + M 0 0 = m + 1 := by ring
  simpa only [hm, hn, add_assoc] using h

lemma ratio_difference (K U V t A B q : ℂ) (hq : q ≠ 0)
    (hcomb : V - U ≠ 0) (hU : 1 - U ≠ 0)
    (_htU : 1 - t * U ≠ 0) (htV : 1 - t * V ≠ 0) (hB : B ≠ 0) :
    K / (V - U) * (A / B) - (q * K) / (q * (V - U)) *
      (((1 - V) * (A / (1 - U))) / ((1 - t * V) * (B / (1 - t * U)))) =
      (1 - t) * (K * ((A / (1 - U)) / ((1 - t * V) * B))) := by
  have htV' : 1 - V * t ≠ 0 := by simpa only [mul_comm] using htV
  field_simp [htV']
  ring

lemma single_difference (K U V A q : ℂ) (hq : q ≠ 0)
    (hcomb : V - U ≠ 0) (hU : 1 - U ≠ 0) :
    K / (V - U) * A - (q * K) / (q * (V - U)) * ((1 - V) * (A / (1 - U))) =
      K * (A / (1 - U)) := by
  field_simp
  ring

end SICLean.L4.G2RawKernelAux
