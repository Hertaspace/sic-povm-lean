import SICLean.L4.G2ResidueLedger

set_option autoImplicit false

/-! Auxiliary analytic estimates for the single bent contour. -/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2SingleBentAux

open G2 G2KernelConvergenceAux

def bentPoint (M : SL(2, ℤ)) (δ β : ℝ) (m j : ℤ) (R : ℝ) : ℂ :=
  (-(δ : ℂ) - (M 1 0 : ℂ) * Complex.I + (R : ℂ) * ((β : ℂ) - Complex.I) -
    (epsilon M : ℂ) * (m : ℂ) - (j : ℂ) * (length M : ℂ)) / (M 1 0 : ℂ)

lemma bentPoint_re (M : SL(2, ℤ)) (δ β : ℝ) (m j : ℤ) (R : ℝ) :
    (bentPoint M δ β m j R).re =
      (-δ + R * β - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ) := by
  simp [bentPoint, ← Complex.ofReal_intCast, Complex.div_ofReal_re]

lemma bentPoint_im (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ β : ℝ) (m j : ℤ) (R : ℝ) :
    (bentPoint M δ β m j R).im = -1 - R / (M 1 0 : ℝ) := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hM.1.ne'
  simp [bentPoint, ← Complex.ofReal_intCast, Complex.div_ofReal_im]
  field_simp
  ring

lemma rawG_analytic_of_regular (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ)
    (hp : modularPhiPoleMultiplicity M m 0 z (repellingTau M : ℂ) = 0)
    (hc : combV M z - combU M m z ≠ 0) :
    AnalyticAt ℂ (rawG M u m) z := by
  have hP := phi_analytic_no_poles M hM.1 m 0 z _
    (real_mem_modularPhiDomain M _ (epsilon_pos M hM)) hp
  have hK : AnalyticAt ℂ (kernelK M u m) z := by
    unfold kernelK e
    fun_prop
  have hC : AnalyticAt ℂ (fun w : ℂ => combV M w - combU M m w) z := by
    unfold combV combU e
    fun_prop
  simpa only [rawG] using! (hK.fun_div hC hc).fun_mul hP

lemma phi_analytic_nonreal (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m n : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => modularPhi M m n w (repellingTau M : ℂ)) z := by
  obtain ⟨hτ, hp, _⟩ := modularPhi_real_off_lattice M hM.1 m n
    (repellingTau M) (epsilon_pos M hM) z (by
      rintro ⟨k, l, rfl⟩
      exact hz (by simp))
  exact phi_analytic_no_poles M hM.1 m n z _ hτ hp

lemma comb_ne_zero_nonreal (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m : ℤ) (z : ℂ) (hz : z.im ≠ 0) : combV M z - combU M m z ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := comb_zero_coordinate M hM m z hzero
  have hi := congrArg Complex.im hk
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, add_zero, zero_add] at hi
  exact (mul_ne_zero (by exact_mod_cast hM.1.ne') hz) hi

lemma rawG_analytic_nonreal (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℂ (rawG M u m) z := by
  have hP := phi_analytic_nonreal M hM m 0 z hz
  have hK : AnalyticAt ℂ (kernelK M u m) z := by
    unfold kernelK e
    fun_prop
  have hC : AnalyticAt ℂ (fun w : ℂ => combV M w - combU M m w) z := by
    unfold combV combU e
    fun_prop
  simpa only [rawG] using!
    (hK.fun_div hC (comb_ne_zero_nonreal M hM m z hz)).fun_mul hP

lemma rawG_analytic_left (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ)
    (hleft : (M 1 0 : ℝ) * z.re + epsilon M * (m : ℝ) < 0)
    (hcomb : combV M z - combU M m z ≠ 0) :
    AnalyticAt ℂ (rawG M u m) z := by
  apply rawG_analytic_of_regular M hM u m z _ hcomb
  have hp : modularPhiPoleIndices M m 0 z (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, hz⟩
    have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
    rw [modularPhiPolePoint, repelling_etaDenom] at hz
    have he := congrArg Complex.re ((eq_div_iff hc).mp hz)
    simp only [Complex.mul_re, Complex.add_re, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
      Complex.intCast_im, Complex.natCast_re, Complex.natCast_im,
      Complex.zero_re, Complex.one_re, Int.cast_zero, zero_mul, mul_zero, sub_zero] at he
    nlinarith [mul_nonneg (epsilon_pos M hM).le (Nat.cast_nonneg K),
      Nat.cast_nonneg (α := ℝ) J, epsilon_pos M hM]
  simp [modularPhiPoleMultiplicity, hp]

lemma rawG_analytic_crossing (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (δ : ℝ) (hδ : 0 < δ ∧ δ < scale M)
    (m j : ℤ) (hj : 0 ≤ j) (x : ℝ)
    (hx : (M 1 0 : ℝ) * x + epsilon M * (m : ℝ) = -δ - (j : ℝ) * length M) :
    AnalyticAt ℂ (rawG M u m) (x : ℂ) := by
  apply rawG_analytic_left M hM u m (x : ℂ)
  · rw [Complex.ofReal_re, hx]
    have hj' : 0 ≤ (j : ℝ) := by exact_mod_cast hj
    have := mul_nonneg hj' (length_pos M hM).le
    linarith [hδ.1]
  · intro hz
    obtain ⟨k, hk⟩ := comb_zero_coordinate M hM m (x : ℂ) hz
    have hr := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero] at hr
    apply G2ContourChainAux.neg_gap_not_scaled (scale M) δ (scale_identities M hM).1
      hδ.1 hδ.2
    refine ⟨(1 - M 1 1) * m + M 1 0 * k + j * specialValueOrder M, ?_⟩
    rw [← G2ContourChainAux.shifted_comb_scaled M hM]
    change -δ = combCoordinate M m k + (j : ℝ) * length M
    linarith [hx, hr]

lemma rawG_difference_nonreal (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    rawG M u m z - rawG M u (m + 1 - M 0 0) (z + (translate M : ℂ)) =
      singleKernel M u m z := by
  have h₁ := (rawG_analytic_nonreal M hM u m z hz).continuousAt
  have hz' : (z + (translate M : ℂ)).im ≠ 0 := by simpa using hz
  have h₂ := (rawG_analytic_nonreal M hM u (m + 1 - M 0 0)
    (z + (translate M : ℂ)) hz').continuousAt.comp (f := fun w : ℂ => w + (translate M : ℂ))
      (continuousAt_id.add continuousAt_const)
  have h₃ : ContinuousAt (singleKernel M u m) z := by
    have hK : AnalyticAt ℂ (kernelK M u m) z := by
      unfold kernelK e
      fun_prop
    exact (hK.fun_mul (phi_analytic_nonreal M hM (m + 1) 0 z hz)).continuousAt
  exact tendsto_nhds_unique ((h₁.sub h₂).mono_left nhdsWithin_le_nhds)
    ((h₃.mono_left nhdsWithin_le_nhds).congr'
      (rawG_difference_germ M hM u m z).symm)

lemma rawG_upper_tail_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ z : ℂ, |z.re| ≤ B → T ≤ z.im →
        ‖rawG M u m z‖ ≤ C * Real.exp (-2 * Real.pi * rawUpperRate M u * z.im) := by
  obtain ⟨A, R, hA, hR, hphi⟩ := upper_phi_bounded M hM {(m, 0)} B hB
  obtain ⟨S, hS, hcomb⟩ := upper_comb_bound M hM m
  refine ⟨2 * A, max R S, by positivity, lt_max_of_lt_left hR, ?_⟩
  intro z hz ht
  have hp := (hphi (m, 0) (by simp) z hz ((le_max_left R S).trans ht)).1
  have hc := hcomb z ((le_max_right R S).trans ht)
  calc
    ‖rawG M u m z‖ = ‖kernelK M u m z‖ *
        ‖(combV M z - combU M m z)⁻¹‖ *
        ‖modularPhi M m 0 z (repellingTau M : ℂ)‖ := by
      simp only [rawG, div_eq_mul_inv, norm_mul]
    _ ≤ Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
        (2 * Real.exp (2 * Real.pi * z.im)) * A := by
      rw [kernelK_norm M hM]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) hp
        (norm_nonneg _) (by positivity)
    _ = (2 * A) * Real.exp (-2 * Real.pi * rawUpperRate M u * z.im) := by
      rw [show Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
          (2 * Real.exp (2 * Real.pi * z.im)) * A =
          (2 * A) * (Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
          Real.exp (2 * Real.pi * z.im)) by ring, ← Real.exp_add]
      congr 2
      dsimp [rawUpperRate]
      field_simp [ne_of_gt (epsilon_pos M hM)]
      ring

lemma reflection_factor_norm (M : SL(2, ℤ)) (r n : ℤ) (z : ℂ) :
    ‖modularReflectionFactor M r n z (repellingTau M : ℂ)‖ =
      ‖(etaMultiplier M) ^ (-2 : ℤ)‖ *
        Real.exp (-2 * Real.pi *
          (modularReflectionPolynomial M r n z (repellingTau M : ℂ)).im) := by
  have hs : ‖(-1 : ℂ) ^ (r + n)‖ = 1 := by
    simp only [norm_zpow, norm_neg, norm_one, one_zpow]
  simp only [modularReflectionFactor, norm_mul, hs, mul_one,
    G2RawKernelAux.rawKernel_norm_e]

lemma lower_sector_phi_bounded (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (Fm : Finset ℤ) :
    ∃ A Q : ℝ, 0 < A ∧ 0 < Q ∧
      ∀ m ∈ Fm, ∀ z : ℂ,
        -z ∈ ModularSector.upperSector (Real.pi / 6) Q →
        ‖modularPhi M m 0 z (repellingTau M : ℂ) /
          modularReflectionFactor M m 0 z (repellingTau M : ℂ)‖ ≤ A := by
  let F : Finset (ℤ × ℤ) := Fm.image (fun m => (m, 0))
  have hT : 0 < ModularSector.realDenom M (repellingTau M) := by
    simpa only [ModularSector.realDenom, G2.epsilon, g1T] using epsilon_pos M hM
  obtain ⟨ρ, C, k, Q, hρ, hC, hk, hQ, _, _, hdec⟩ :=
    ModularSector.upper_half_lower_decay M hM.1 F (repellingTau M)
      (Real.pi / 6) hT (by positivity) (by linarith [Real.pi_pos])
  have hτ : (repellingTau M : ℂ) ∈
      ModularSector.upperParameterDisk (repellingTau M) ρ := by
    simp [ModularSector.upperParameterDisk, ModularSector.parameterDisk, hρ.le]
  refine ⟨C + 1, Q, by linarith, hQ, ?_⟩
  intro m hm z hz
  have hi : (m, 0) ∈ F := Finset.mem_image.mpr ⟨m, hm, rfl⟩
  have hs := hdec _ hτ (m, 0) hi z hz
  have he : Real.exp (-k * ‖z‖) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg _))
  have hsum : ModularSector.lowerError M (m, 0) z (repellingTau M : ℂ) ≤ C :=
    hs.trans (by simpa using mul_le_mul_of_nonneg_left he hC.le)
  apply norm_le_of_sub_one
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans hsum

lemma lower_comb_uniform (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ∃ S : ℝ, 0 < S ∧ ∀ (m : ℤ) (z : ℂ), z.im ≤ -S →
      ‖(combV M z - combU M m z)⁻¹‖ ≤
        2 * Real.exp (2 * Real.pi * z.im / epsilon M) := by
  let a := 2 * Real.pi * (1 / epsilon M - 1)
  have ha : 0 < a := comb_gap_pos M hM
  refine ⟨1 / a, by positivity, ?_⟩
  intro m z hz
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

lemma rawG_lower_cone_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (Fm : Finset ℤ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ m ∈ Fm, ∀ z : ℂ, |z.re| ≤ -z.im → z.im ≤ -T →
        ‖rawG M u m z‖ ≤ C * Real.exp
          (Real.pi / epsilon M *
            (2 * (M 1 0 : ℝ) * z.re + (2 * (m : ℝ) - 1) * epsilon M +
              3 - 2 * upperCoefficient M u) * z.im) := by
  obtain ⟨A, Q, hA, hQ, hphi⟩ := lower_sector_phi_bounded M hM Fm
  obtain ⟨S, hS, hcomb⟩ := lower_comb_uniform M hM
  let E : ℝ := ‖(etaMultiplier M) ^ (-2 : ℤ)‖
  have hE : 0 < E := norm_pos_iff.mpr
    (zpow_ne_zero _ (etaMultiplier_ne_zero M hM.1))
  refine ⟨2 * A * E, max Q S, by positivity, lt_max_of_lt_left hQ, ?_⟩
  intro m hm z hre hy
  have him : 0 < (-z).im := by
    simp only [Complex.neg_im]
    linarith [le_max_left Q S]
  have hz : -z ∈ ModularSector.upperSector (Real.pi / 6) Q :=
    G2RawKernelAux.upperSector_of_im_dominates Q (-z) him
      (by simpa only [Complex.neg_re, abs_neg, Complex.neg_im] using hre)
      (by simp only [Complex.neg_im]; linarith [le_max_left Q S])
  have hp : ‖modularPhi M m 0 z (repellingTau M : ℂ)‖ ≤
      A * ‖modularReflectionFactor M m 0 z (repellingTau M : ℂ)‖ :=
    (div_le_iff₀ (norm_pos_iff.mpr (reflection_ne_zero M hM _ _ _ _))).mp
      (by simpa only [norm_div] using hphi m hm z hz)
  rw [reflection_factor_norm] at hp
  have hc := hcomb m z (show z.im ≤ -S by linarith [le_max_right Q S])
  calc
    ‖rawG M u m z‖ = ‖kernelK M u m z‖ *
        ‖(combV M z - combU M m z)⁻¹‖ *
        ‖modularPhi M m 0 z (repellingTau M : ℂ)‖ := by
      simp only [rawG, div_eq_mul_inv, norm_mul]
    _ ≤ Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
        (2 * Real.exp (2 * Real.pi * z.im / epsilon M)) *
        (A * (E * Real.exp (-2 * Real.pi *
          (modularReflectionPolynomial M m 0 z (repellingTau M : ℂ)).im))) := by
      rw [kernelK_norm M hM]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) hp
        (norm_nonneg _) (by positivity)
    _ = (2 * A * E) *
        (Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) *
          Real.exp (2 * Real.pi * z.im / epsilon M) *
          Real.exp (-2 * Real.pi *
            (modularReflectionPolynomial M m 0 z (repellingTau M : ℂ)).im)) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      rw [G2RawKernelAux.rawKernel_polynomial_im M hM]
      simp only [Int.cast_zero, mul_zero, zero_sub]
      field_simp [ne_of_gt (epsilon_pos M hM)]
      ring

lemma rawG_affine_lower_gaussian (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (Fm : Finset ℤ) (B β : ℝ) (hB : 0 ≤ B)
    (hβ : 0 < β ∧ β < 1) :
    ∃ C C₁ R₀ : ℝ, 0 < C ∧ 0 < C₁ ∧ 0 < R₀ ∧
      ∀ m ∈ Fm, ∀ x : ℝ, |x| ≤ B → ∀ R : ℝ, R₀ ≤ R →
        ∀ z : ℂ, z.re = x + β * R / (M 1 0 : ℝ) →
          z.im = -1 - R / (M 1 0 : ℝ) →
        ‖rawG M u m z‖ ≤ C * Real.exp
          (-(2 * Real.pi * β / ((M 1 0 : ℝ) * epsilon M)) * R ^ 2 + C₁ * R) := by
  obtain ⟨C₀, T, hC₀, hT, hcone⟩ := rawG_lower_cone_bound M hM u Fm
  let c : ℝ := (M 1 0 : ℝ)
  let ε : ℝ := epsilon M
  let U : ℝ := upperCoefficient M u
  have hc : 0 < c := by dsimp [c]; exact_mod_cast hM.1
  have he : 0 < ε := epsilon_pos M hM
  have hb : 0 < β := hβ.1
  have hgap : 0 < 1 - β := sub_pos.mpr hβ.2
  let K : ℝ := ∑ m ∈ Fm, |(m : ℝ)|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun m _ => abs_nonneg (m : ℝ))
  let P : ℝ := 2 * c * B + (2 * K + 1) * ε + 3 + 2 * |U|
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let C₁ : ℝ := Real.pi * P / (c * ε) + 1
  let D : ℝ := Real.pi * P / ε
  let R₀ : ℝ := max 1 (max (c * B / (1 - β)) (c * T))
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hR₀ : 0 < R₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C₀ * Real.exp D, C₁, R₀, by positivity, hC₁, hR₀, ?_⟩
  intro m hm x hx R hR z hzre hzim
  change z.re = x + β * R / c at hzre
  change z.im = -1 - R / c at hzim
  have hRnonneg : 0 ≤ R := (hR₀.trans_le hR).le
  have hRgap : c * B / (1 - β) ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRT : c * T ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hTdiv : T ≤ R / c := (le_div_iff₀ hc).mpr (by nlinarith [hRT])
  have hBgap : B ≤ (1 - β) * R / c := by
    apply (le_div_iff₀ hc).mpr
    have h := (div_le_iff₀ hgap).mp hRgap
    nlinarith
  have hBlinear : B + β * R / c ≤ R / c := by
    calc
      B + β * R / c ≤ (1 - β) * R / c + β * R / c := by linarith
      _ = R / c := by ring
  have hcone_re : |z.re| ≤ -z.im := by
    rw [hzre]
    calc
      |x + β * R / c| ≤ |x| + |β * R / c| := abs_add_le _ _
      _ ≤ B + β * R / c := by
        rw [abs_of_nonneg (div_nonneg (mul_nonneg hβ.1.le hRnonneg) hc.le)]
        linarith
      _ ≤ -z.im := by rw [hzim]; linarith
  have hcone_im : z.im ≤ -T := by rw [hzim]; linarith
  have hg := hcone m hm z hcone_re hcone_im
  change ‖rawG M u m z‖ ≤ C₀ * Real.exp
    (Real.pi / ε * (2 * c * z.re + (2 * (m : ℝ) - 1) * ε + 3 - 2 * U) * z.im) at hg
  have hmK : |(m : ℝ)| ≤ K :=
    Finset.single_le_sum (fun n (_ : n ∈ Fm) => abs_nonneg (n : ℝ)) hm
  let q : ℝ := 2 * c * x + (2 * (m : ℝ) - 1) * ε + 3 - 2 * U
  have hq : -P ≤ q := by
    have hxm := mul_le_mul_of_nonneg_left (abs_le.mp hx).1
      (show 0 ≤ 2 * c by positivity)
    have hml : -(2 * K + 1) ≤ 2 * (m : ℝ) - 1 := by
      linarith [(abs_le.mp hmK).1]
    have hmm := mul_le_mul_of_nonneg_right hml he.le
    dsimp [P, q]
    nlinarith [le_abs_self U]
  have hqmul : Real.pi / ε * (q * z.im) ≤
      Real.pi / ε * ((-P) * z.im) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonpos_right hq (hcone_im.trans (neg_nonpos.mpr hT.le)))
      (div_nonneg Real.pi_pos.le he.le)
  have hupper : Real.pi / ε * ((-P) * z.im) =
      D + (C₁ - 1) * R := by
    rw [hzim]
    dsimp [D, C₁]
    field_simp
    ring
  rw [hupper] at hqmul
  have hneg : 0 ≤ (2 * Real.pi * β / ε) * R := by positivity
  have hexpand :
      Real.pi / ε *
        (2 * c * z.re + (2 * (m : ℝ) - 1) * ε + 3 - 2 * U) * z.im =
      -(2 * Real.pi * β / (c * ε)) * R ^ 2 -
        (2 * Real.pi * β / ε) * R + Real.pi / ε * (q * z.im) := by
    rw [hzre, hzim]
    dsimp [q]
    field_simp [ne_of_gt hc, ne_of_gt he]
    ring
  have hscalar :
      Real.pi / ε *
        (2 * c * z.re + (2 * (m : ℝ) - 1) * ε + 3 - 2 * U) * z.im ≤
      -(2 * Real.pi * β / (c * ε)) * R ^ 2 + C₁ * R + D := by
    rw [hexpand]
    nlinarith
  calc
    ‖rawG M u m z‖ ≤ C₀ * Real.exp
        (Real.pi / ε *
          (2 * c * z.re + (2 * (m : ℝ) - 1) * ε + 3 - 2 * U) * z.im) := hg
    _ ≤ C₀ * Real.exp
        (-(2 * Real.pi * β / (c * ε)) * R ^ 2 + C₁ * R + D) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscalar) hC₀.le
    _ = _ := by
      dsimp only [c, ε]
      rw [Real.exp_add]
      ring

end SICLean.L4.G2SingleBentAux
