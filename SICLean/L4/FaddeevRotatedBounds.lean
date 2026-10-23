import SICLean.L4.FaddeevRotatedKernel
import SICLean.L4.FaddeevRotatedBoundsAux

set_option autoImplicit false

/-!
Compact middle intervals and uniform exponential tails produce an actual common L¹ majorant, not
just pointwise integrability.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4.Sector

def expMajorant (C lam t : ℝ) : ℝ := C * Real.exp (-2 * lam * |t|)

theorem rotated_real_parts_lower (b : ℂ) (θ v t lam M : ℝ)
    (hv : 0 ≤ v) (hlam : 0 ≤ lam)
    (hA : lam ≤ rotatedRe b θ) (hB : lam ≤ rotatedInvRe b θ)
    (hM : |(b * rotation θ).im| ≤ M ∧ |(b⁻¹ * rotation θ).im| ≤ M) :
    lam * |t| - v * M ≤ |(b * rotatedPoint θ v t).re| ∧
      lam * |t| - v * M ≤ |(b⁻¹ * rotatedPoint θ v t).re| := by
  exact rotated_re_abs_lower b θ v t lam M hv hlam hA hB hM

theorem exists_uniform_im_bound {K : Set ℂ} {β κ : ℝ} (hK : Family K β κ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ K, ∀ θ : ℝ,
      |(b * rotation θ).im| ≤ M ∧ |(b⁻¹ * rotation θ).im| ≤ M := by
  obtain ⟨m, hmpos, hm⟩ :=
    hK.compact.exists_forall_le' continuous_norm.continuousOn
      (fun b hb => norm_pos_iff.mpr (admissibleB_ne_zero b (hK.admissible b hb)))
  obtain ⟨C, hCpos, hC⟩ := hK.compact.isBounded.exists_pos_norm_le
  refine ⟨max C (1 / m), le_trans hCpos.le (le_max_left _ _), ?_⟩
  intro b hb θ
  have hbC : ‖b‖ ≤ C := hC b hb
  have hbm : m ≤ ‖b‖ := hm b hb
  have hbinv : ‖b⁻¹‖ = (‖b‖)⁻¹ := norm_inv b
  have hinvle : (‖b‖)⁻¹ ≤ 1 / m := by
    calc
      (‖b‖)⁻¹ ≤ m⁻¹ := (inv_le_inv₀ (lt_of_lt_of_le hmpos hbm) hmpos).mpr hbm
      _ = 1 / m := inv_eq_one_div m
  constructor
  · calc
      |(b * rotation θ).im| ≤ ‖b * rotation θ‖ := Complex.abs_im_le_norm _
      _ = ‖b‖ * ‖rotation θ‖ := norm_mul _ _
      _ = ‖b‖ := by rw [norm_rotation]; ring
      _ ≤ C := hbC
      _ ≤ max C (1 / m) := le_max_left _ _
  · calc
      |(b⁻¹ * rotation θ).im| ≤ ‖b⁻¹ * rotation θ‖ := Complex.abs_im_le_norm _
      _ = ‖b⁻¹‖ * ‖rotation θ‖ := norm_mul _ _
      _ = ‖b⁻¹‖ := by rw [norm_rotation]; ring
      _ = (‖b‖)⁻¹ := hbinv
      _ ≤ 1 / m := hinvle
      _ ≤ max C (1 / m) := le_max_right _ _

theorem exists_tail_threshold (lam v M : ℝ) (hlam : 0 < lam) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : ℝ, R ≤ |t| → 1 + v * M ≤ lam * |t| := by
  refine ⟨max 1 ((1 + v * M) / lam), le_max_left _ _, ?_⟩
  intro t ht
  have hR : (1 + v * M) / lam ≤ |t| := (le_max_right _ _).trans ht
  have hbase : lam * ((1 + v * M) / lam) = 1 + v * M := by
    field_simp [hlam.ne']
  calc
    1 + v * M = lam * ((1 + v * M) / lam) := hbase.symm
    _ ≤ lam * |t| := mul_le_mul_of_nonneg_left hR hlam.le

theorem amplitude_tail_bound (b : ℂ) (θ v t lam M : ℝ)
    (hv : 0 < v) (hlam : 0 < lam)
    (hA : lam ≤ rotatedRe b θ) (hB : lam ≤ rotatedInvRe b θ)
    (hM : |(b * rotation θ).im| ≤ M ∧ |(b⁻¹ * rotation θ).im| ≤ M)
    (ht : 1 + v * M ≤ lam * |t|) :
    ‖amplitude b θ v t‖ ≤
      (4 / v) * Real.exp (2 * v * M) * Real.exp (-2 * lam * |t|) := by
  exact amplitude_tail_bound_aux b θ v t lam M hv hlam hA hB hM ht

theorem exists_middle_denominator_lower {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) (R : ℝ) (hR : 0 ≤ R) :
    ∃ m : ℝ, 0 < m ∧ ∀ b ∈ K, ∀ θ ∈ Icc (-(opening β κ)) (opening β κ),
      ∀ t ∈ Icc (-R) R, m ≤ ‖rotatedDenominator b θ v t‖ := by
  let Θ : ℝ := opening β κ
  let S : Set ((ℂ × ℝ) × ℝ) := (K ×ˢ Icc (-Θ) Θ) ×ˢ Icc (-R) R
  have hS : IsCompact S := (hK.compact.prod isCompact_Icc).prod isCompact_Icc
  have hcont : ContinuousOn
      (fun p : (ℂ × ℝ) × ℝ => ‖rotatedDenominator p.1.1 p.1.2 v p.2‖) S := by
    intro p hp
    have hb0 : p.1.1 ≠ 0 :=
      admissibleB_ne_zero _ (hK.admissible _ hp.1.1)
    unfold rotatedDenominator rotatedPoint linePoint rotation
    fun_prop
  have hpos : ∀ p ∈ S, 0 < ‖rotatedDenominator p.1.1 p.1.2 v p.2‖ := by
    intro p hp
    have hbK : p.1.1 ∈ K := hp.1.1
    have hθ : p.1.2 ∈ Icc (-Θ) Θ := hp.1.2
    have hb0 : p.1.1 ≠ 0 := admissibleB_ne_zero _ (hK.admissible _ hbK)
    exact norm_pos_iff.mpr (rotatedDenominator_ne_zero hlam hv hbK hb0 hθ p.2)
  obtain ⟨m, hmpos, hm⟩ := hS.exists_forall_le' hcont hpos
  refine ⟨m, hmpos, ?_⟩
  intro b hb θ hθ t ht
  exact hm ((b, θ), t) ⟨⟨hb, hθ⟩, ht⟩

theorem exists_uniform_amplitude_exp_bound {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ θ ∈ Icc (-(opening β κ)) (opening β κ),
      ∀ t : ℝ, ‖amplitude b θ v t‖ ≤ expMajorant C lam t := by
  have hlam0 : 0 < lam := hlam.1
  have hv0 : 0 < v := hv.1
  obtain ⟨M, hM0, hM⟩ := exists_uniform_im_bound hK
  obtain ⟨R, hR1, hR⟩ := exists_tail_threshold lam v M hlam0
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  obtain ⟨m, hm0, hm⟩ := exists_middle_denominator_lower hK hlam hv R hR0
  let A : ℝ := (4 / v) * Real.exp (2 * v * M)
  let D : ℝ := (1 / m) * Real.exp (2 * lam * R)
  have hApos : 0 < A :=
    mul_pos (div_pos (by norm_num) hv0) (Real.exp_pos _)
  have hDpos : 0 < D :=
    mul_pos (div_pos (by norm_num) hm0) (Real.exp_pos _)
  refine ⟨max A D, lt_of_lt_of_le hApos (le_max_left _ _), ?_⟩
  intro b hb θ hθ t
  by_cases ht : 1 + v * M ≤ lam * |t|
  · have htail := amplitude_tail_bound_aux b θ v t lam M hv0 hlam0
      (hlam.2 b hb θ hθ).1 (hlam.2 b hb θ hθ).2 (hM b hb θ) ht
    calc
      ‖amplitude b θ v t‖ ≤ A * Real.exp (-2 * lam * |t|) := by
        simpa [A, mul_assoc] using htail
      _ ≤ max A D * Real.exp (-2 * lam * |t|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have htlt : |t| < R := by
      by_contra h
      exact ht (hR t (le_of_not_gt h))
    have htIcc : t ∈ Icc (-R) R := by
      rw [mem_Icc]
      exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have hmden : m ≤ ‖rotatedDenominator b θ v t‖ := hm b hb θ hθ t htIcc
    have hdenpos : 0 < ‖rotatedDenominator b θ v t‖ := lt_of_lt_of_le hm0 hmden
    have hmid : ‖amplitude b θ v t‖ ≤ 1 / m := by
      rw [amplitude, norm_inv]
      calc
        (‖rotatedDenominator b θ v t‖)⁻¹ ≤ m⁻¹ :=
          (inv_le_inv₀ hdenpos hm0).mpr hmden
        _ = 1 / m := inv_eq_one_div m
    have hexpge : Real.exp (-2 * lam * R) ≤ Real.exp (-2 * lam * |t|) := by
      apply Real.exp_le_exp.mpr
      have hle : lam * |t| ≤ lam * R := mul_le_mul_of_nonneg_left (le_of_lt htlt) hlam0.le
      nlinarith
    have hD1 : D * Real.exp (-2 * lam * R) = 1 / m := by
      dsimp [D]
      rw [mul_assoc, ← Real.exp_add]
      have hzero : 2 * lam * R + -2 * lam * R = 0 := by ring
      rw [hzero, Real.exp_zero, mul_one]
    calc
      ‖amplitude b θ v t‖ ≤ 1 / m := hmid
      _ = D * Real.exp (-2 * lam * R) := hD1.symm
      _ ≤ D * Real.exp (-2 * lam * |t|) :=
        mul_le_mul_of_nonneg_left hexpge hDpos.le
      _ ≤ max A D * Real.exp (-2 * lam * |t|) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

theorem expMajorant_nonneg (C lam t : ℝ) (hC : 0 ≤ C) :
    0 ≤ expMajorant C lam t := by
  unfold expMajorant
  positivity

theorem integrable_expMajorant (C lam : ℝ) (hlam : 0 < lam) :
    Integrable (expMajorant C lam) := by
  unfold expMajorant
  exact (integrable_exp_neg_two_mul_abs lam hlam).const_mul C

theorem exists_uniform_amplitude_majorant {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) :
    ∃ B : ℝ → ℝ, Integrable B ∧ (∀ t : ℝ, 0 ≤ B t) ∧
      ∀ b ∈ K, ∀ θ ∈ Icc (-(opening β κ)) (opening β κ),
        ∀ t : ℝ, ‖amplitude b θ v t‖ ≤ B t := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_amplitude_exp_bound hK hlam hv
  exact ⟨expMajorant C lam, integrable_expMajorant C lam hlam.1,
    fun t => expMajorant_nonneg C lam t hCpos.le,
    fun b hb θ hθ t => hC b hb θ hθ t⟩

theorem integrable_amplitude {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) :
    Integrable (amplitude b θ v) := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_amplitude_exp_bound hK hlam hv
  have hmaj : Integrable (expMajorant C lam) := integrable_expMajorant C lam hlam.1
  have hmeas : AEStronglyMeasurable (amplitude b θ v) volume := by
    have hb0 : b ≠ 0 := admissibleB_ne_zero b (hK.admissible b hb)
    have hne : ∀ t : ℝ, rotatedDenominator b θ v t ≠ 0 :=
      fun t => rotatedDenominator_ne_zero hlam hv hb hb0 hθ t
    have hdencont : Continuous (fun t : ℝ => rotatedDenominator b θ v t) := by
      unfold rotatedDenominator rotatedPoint linePoint rotation
      fun_prop
    change AEStronglyMeasurable (fun t : ℝ => (rotatedDenominator b θ v t)⁻¹) volume
    exact (hdencont.inv₀ hne).aestronglyMeasurable
  exact Integrable.mono' hmaj hmeas (Eventually.of_forall (fun t => hC b hb θ hθ t))

theorem exists_uniform_l1_bound {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ b ∈ K,
      ∀ θ ∈ Icc (-(opening β κ)) (opening β κ),
        (∫ t : ℝ, ‖amplitude b θ v t‖) ≤ C₀ := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_amplitude_exp_bound hK hlam hv
  refine ⟨C / lam + 1, ?_, ?_⟩
  · have h1 : 0 < C / lam := div_pos hCpos hlam.1
    linarith
  intro b hb θ hθ
  have hInt : Integrable (amplitude b θ v) := integrable_amplitude hK hlam hv hb hθ
  have hmaj : Integrable (expMajorant C lam) := integrable_expMajorant C lam hlam.1
  have hle : (∫ t : ℝ, ‖amplitude b θ v t‖) ≤ ∫ t : ℝ, expMajorant C lam t :=
    integral_mono hInt.norm hmaj (fun t => hC b hb θ hθ t)
  calc
    (∫ t : ℝ, ‖amplitude b θ v t‖) ≤ ∫ t : ℝ, expMajorant C lam t := hle
    _ = C * (∫ t : ℝ, Real.exp (-2 * lam * |t|)) := by
      unfold expMajorant
      rw [integral_const_mul]
    _ = C * (1 / lam) := by rw [integral_exp_neg_two_mul_abs lam hlam.1]
    _ ≤ C / lam + 1 := by
      have : C * (1 / lam) = C / lam := by ring
      rw [this]
      linarith

theorem uniform_amplitude_tails {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ b ∈ K,
      ∀ θ ∈ Icc (-(opening β κ)) (opening β κ),
        (∫ t : ℝ in {t | R ≤ |t|}, ‖amplitude b θ v t‖) < ε := by
  have hlam0 : 0 < lam := hlam.1
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_amplitude_exp_bound hK hlam hv
  intro ε hε
  have hδ : 0 < ε * lam / C := div_pos (mul_pos hε hlam0) hCpos
  have hpos2 : 0 < 2 * lam := by linarith
  have hcomp : Tendsto (fun R : ℝ => Real.exp (-(2 * lam * R))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop hpos2)
  have htend : Tendsto (fun R : ℝ => Real.exp (-2 * lam * R)) atTop (𝓝 0) := by
    have hfun : (fun R : ℝ => Real.exp (-(2 * lam * R))) =
        (fun R : ℝ => Real.exp (-2 * lam * R)) := by
      funext R
      congr 1
      ring
    exact hfun ▸ hcomp
  have hev : ∀ᶠ R in atTop, Real.exp (-2 * lam * R) < ε * lam / C :=
    htend.eventually (eventually_lt_nhds hδ)
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp hev
  refine ⟨max R0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro b hb θ hθ
  have hRle : R0 ≤ max R0 1 := le_max_left _ _
  have hexpR : Real.exp (-2 * lam * (max R0 1)) < ε * lam / C := hR0 _ hRle
  have hRnonneg : 0 ≤ max R0 1 := le_trans zero_lt_one.le (le_max_right _ _)
  have hmono : (∫ t : ℝ in {t | max R0 1 ≤ |t|}, ‖amplitude b θ v t‖) ≤
      ∫ t : ℝ in {t | max R0 1 ≤ |t|}, expMajorant C lam t := by
    apply setIntegral_mono
    · exact (integrable_amplitude hK hlam hv hb hθ).norm.integrableOn
    · exact (integrable_expMajorant C lam hlam0).integrableOn
    · intro t
      exact hC b hb θ hθ t
  have htailEq : (∫ t : ℝ in {t | max R0 1 ≤ |t|}, expMajorant C lam t) =
      C * ((1 / lam) * Real.exp (-2 * lam * (max R0 1))) := by
    unfold expMajorant
    rw [integral_const_mul,
      integral_exp_neg_two_mul_abs_tail lam (max R0 1) hlam0 hRnonneg]
  calc
    (∫ t : ℝ in {t | max R0 1 ≤ |t|}, ‖amplitude b θ v t‖)
        ≤ ∫ t : ℝ in {t | max R0 1 ≤ |t|}, expMajorant C lam t := hmono
    _ = C * ((1 / lam) * Real.exp (-2 * lam * (max R0 1))) := htailEq
    _ < ε := by
      have hClam : 0 < C / lam := div_pos hCpos hlam0
      calc
        C * ((1 / lam) * Real.exp (-2 * lam * (max R0 1))) =
            (C / lam) * Real.exp (-2 * lam * (max R0 1)) := by ring
        _ < (C / lam) * (ε * lam / C) :=
          mul_lt_mul_of_pos_left hexpR hClam
        _ = ε := by
          field_simp [hCpos.ne', hlam0.ne']

end SICLean.L4.Sector
