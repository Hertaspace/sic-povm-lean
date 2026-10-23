import SICLean.L4.G1BilateralSeparation

set_option autoImplicit false

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1BilateralRatioTailsAux

lemma disk_mono {τ₀ r s : ℝ} (h : r ≤ s) :
    ModularSector.parameterDisk τ₀ r ⊆ ModularSector.parameterDisk τ₀ s :=
  Metric.closedBall_subset_closedBall h

lemma disk_self (τ₀ r : ℝ) (hr : 0 ≤ r) :
    (τ₀ : ℂ) ∈ ModularSector.parameterDisk τ₀ r := Metric.mem_closedBall_self hr

lemma disk_nhds (τ₀ r : ℝ) (hr : 0 < r) :
    ModularSector.parameterDisk τ₀ r ∈ 𝓝 (τ₀ : ℂ) := Metric.closedBall_mem_nhds _ hr

lemma finite_compact_bound {ι E : Type*} [DecidableEq ι] [TopologicalSpace E]
    (F : Finset ι) (K : Set E) (hK : IsCompact K) (f : ι → E → ℂ)
    (hf : ∀ i ∈ F, ContinuousOn (f i) K) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ∈ F, ∀ x ∈ K, ‖f i x‖ ≤ C := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨C, hC, hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hf i (Finset.mem_insert_self _ _))
    refine ⟨max C B, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (hB x hx).trans (le_max_right _ _)
    · exact (hbound j hj x hx).trans (le_max_left _ _)

lemma norm_e (z : ℂ) : ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  rw [e, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma e_add (z w : ℂ) : e (z + w) = e z * e w :=
  EtaMultiplierAux.exp_phase_add z w

lemma e_sub (z w : ℂ) : e (z - w) = e z / e w :=
  EtaMultiplierAux.exp_phase_sub z w

lemma norm_e_vertical (A B : ℂ) (x t : ℝ) :
    ‖e (A * g1VerticalPoint x t + B)‖ =
      ‖e (A * (x : ℂ) + B)‖ * Real.exp (-(2 * Real.pi * A.re) * t) := by
  rw [norm_e, norm_e, ← Real.exp_add]
  congr 1
  simp [g1VerticalPoint, Complex.mul_im, Complex.mul_re]
  <;> ring

lemma analyticAt_phase (M : SL(2, ℤ)) (w : ℂ) (n h ell m : ℤ)
    {z τ : ℂ} (hτ : τ ∈ modularPhiDomain M) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => g1Exponent M q.1 w q.2 n h ell m) (τ, z) := by
  have hT : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hτ
  have ht : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1) (τ, z) := analyticAt_fst
  have hz : AnalyticAt ℂ (fun q : ℂ × ℂ => q.2) (τ, z) := analyticAt_snd
  have hd : AnalyticAt ℂ (fun q : ℂ × ℂ => etaDenom M q.1) (τ, z) :=
    (analyticAt_const.mul ht).add analyticAt_const
  have hm : AnalyticAt ℂ (fun q : ℂ × ℂ => etaMobius M q.1) (τ, z) :=
    ((analyticAt_const.mul ht).add analyticAt_const).div hd hT
  exact ((((((analyticAt_const.mul hz).sub analyticAt_const).add
    (hd.mul analyticAt_const)).mul analyticAt_const).div hd hT).add
      (analyticAt_const.mul (hz.add (analyticAt_const.mul ht)))).add
        (analyticAt_const.mul ((hz.div hd hT).add (analyticAt_const.mul hm)))

lemma analyticAt_slope (M : SL(2, ℤ)) (w y : ℂ) (h ell p : ℤ)
    {τ : ℂ} (hτ : τ ∈ modularPhiDomain M) (lower : Bool) :
    AnalyticAt ℂ (fun t : ℂ =>
      (if lower then G1RatioTail.complexL M t w y h ell p
       else G1RatioTail.complexS M t w h ell) / etaDenom M t) τ := by
  have hT : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hτ
  have hd : AnalyticAt ℂ (fun t : ℂ => etaDenom M t) τ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hs : AnalyticAt ℂ (fun t : ℂ => G1RatioTail.complexS M t w h ell) τ :=
    analyticAt_const.add (analyticAt_const.mul hd)
  cases lower
  · exact hs.div hd hT
  · exact ((hs.add analyticAt_const).add (analyticAt_const.mul hd)).div hd hT

lemma norm_reflection_ratio (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r s n : ℤ) (z u τ : ℂ) :
    ‖modularReflectionFactor M r n z τ / modularReflectionFactor M s n u τ‖ =
      ‖e (modularReflectionPolynomial M r n z τ -
        modularReflectionPolynomial M s n u τ)‖ := by
  have hμ : etaMultiplier M ≠ 0 := etaMultiplier_ne_zero M hM
  rw [e_sub]
  simp only [modularReflectionFactor, norm_div, norm_mul, norm_zpow,
    norm_neg, norm_one, one_zpow, mul_one]
  exact mul_div_mul_left _ _ (zpow_ne_zero _ (norm_ne_zero_iff.mpr hμ))

/-- The affine reflected phase uses exactly the existing reflection polynomial. -/
lemma lower_phase_affine (M : SL(2, ℤ)) (τ w y z : ℂ) (n h ell p m : ℤ)
    (hT : etaDenom M τ ≠ 0) :
    modularReflectionPolynomial M (m + 1) n z τ -
      modularReflectionPolynomial M (m + p) n (z + y) τ +
        g1Exponent M τ w z n h ell m =
    G1RatioTail.complexL M τ w y h ell p / etaDenom M τ * z +
      (modularReflectionPolynomial M (m + 1) n 0 τ -
        modularReflectionPolynomial M (m + p) n y τ +
          g1Exponent M τ w 0 n h ell m) := by
  rw [G1RatioTail.reflection_difference_affine M τ y z n p m hT,
    G1RatioTail.exponent_affine M τ w z n h ell m hT]
  unfold G1RatioTail.complexL
  field_simp
  <;> ring

lemma kernel_eq (M : SL(2, ℤ)) (τ w y z : ℂ) (n h ell p m : ℤ) :
    G1RatioTail.complexKernel M τ w y n h ell p m z =
      (modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ) *
        e (g1Exponent M τ w z n h ell m) := by
  rfl

lemma norm_lower_kernel (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y z : ℂ) (n h ell p m : ℤ) (hτ : τ ∈ modularPhiDomain M) :
    let q := modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ
    let a := modularReflectionFactor M (m + 1) n z τ /
      modularReflectionFactor M (m + p) n (z + y) τ
    ‖G1RatioTail.complexKernel M τ w y n h ell p m z‖ =
      ‖q / a‖ * ‖e (modularReflectionPolynomial M (m + 1) n z τ -
        modularReflectionPolynomial M (m + p) n (z + y) τ +
          g1Exponent M τ w z n h ell m)‖ := by
  dsimp only
  have ha : modularReflectionFactor M (m + 1) n z τ /
      modularReflectionFactor M (m + p) n (z + y) τ ≠ 0 :=
    div_ne_zero (ModularSector.reflectionFactor_joint_unit M hM _ _ _ _ hτ).2
      (ModularSector.reflectionFactor_joint_unit M hM _ _ _ _ hτ).2
  rw [e_add, norm_mul, ← norm_reflection_ratio M hM,
    ← mul_assoc, ← norm_mul, div_mul_cancel₀ _ ha, kernel_eq, norm_mul]

lemma kernel_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (w y : ℂ) (n h ell p m : ℤ) {z τ : ℂ}
    (hreg : (z, τ) ∈ ModularCluster.regularDomain M
      (G1Pinch.ratioData w y n h ell p m)) :
    AnalyticAt ℂ (fun q : ℂ × ℂ =>
      G1RatioTail.complexKernel M q.2 w y n h ell p m q.1) (z, τ) :=
  ModularCluster.kernel_joint_analytic M hM _ _ hreg

lemma vertical_continuous (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n h ell p m : ℤ) (x : ℝ)
    (hsafe : ∀ t : ℝ, (g1VerticalPoint x t, τ) ∈ ModularCluster.regularDomain M
      (G1Pinch.ratioData w y n h ell p m)) :
    Continuous (g1VerticalPullback (G1RatioTail.complexKernel M τ w y n h ell p m) x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (kernel_analytic M hM w y n h ell p m (hsafe t)).continuousAt
  have hm : ContinuousAt (fun t : ℝ => (g1VerticalPoint x t, τ)) t := by
    unfold g1VerticalPoint
    fun_prop
  exact (hc.comp (f := fun t : ℝ => (g1VerticalPoint x t, τ)) hm).mul continuousAt_const

lemma norm_vertical (f : ℂ → ℂ) (x t : ℝ) :
    ‖g1VerticalPullback f x t‖ = ‖f (g1VerticalPoint x t)‖ := by
  simp [g1VerticalPullback, norm_mul]

def phaseConstant (M : SL(2, ℤ)) (τ w y : ℂ) (n h ell p m : ℤ)
    (lower : Bool) : ℂ :=
  (if lower then modularReflectionPolynomial M (m + 1) n 0 τ -
    modularReflectionPolynomial M (m + p) n y τ else 0) +
      g1Exponent M τ w 0 n h ell m

lemma phaseConstant_continuous (M : SL(2, ℤ)) (w y : ℂ) (n h ell p m : ℤ)
    (lower : Bool) {τ : ℂ} (hτ : τ ∈ modularPhiDomain M) :
    ContinuousAt (fun t => phaseConstant M t w y n h ell p m lower) τ := by
  have hT : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hτ
  have hd : ContinuousAt (etaDenom M) τ := by unfold etaDenom; fun_prop
  have hm : ContinuousAt (etaMobius M) τ := by
    unfold etaMobius
    exact ((continuous_const.mul continuous_id).add continuous_const).continuousAt.div hd hT
  have hP (r : ℤ) (z : ℂ) : ContinuousAt
      (fun t : ℂ => modularReflectionPolynomial M r n z t) τ := by
    unfold modularReflectionPolynomial
    fun_prop
  have hE : ContinuousAt (fun t : ℂ => g1Exponent M t w 0 n h ell m) τ :=
    ((analyticAt_phase M w n h ell m hτ).comp
      (f := fun t : ℂ => (t, 0)) (analyticAt_id.prod analyticAt_const)).continuousAt
  cases lower
  · simpa [phaseConstant] using hE
  · exact ((hP (m + 1) 0).sub (hP (m + p) y)).add hE

lemma affine_phase_bound (M : SL(2, ℤ)) (w y : ℂ) (n h ell p : ℤ)
    (F : Finset ℤ) (τ₀ ρ a b : ℝ) (lower : Bool)
    (hdisk : ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M) :
    ∃ B : ℝ, 0 < B ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
      ∀ x ∈ Icc a b, ∀ t : ℝ,
        ‖e (((if lower then G1RatioTail.complexL M τ w y h ell p
          else G1RatioTail.complexS M τ w h ell) / etaDenom M τ) *
            g1VerticalPoint x t + phaseConstant M τ w y n h ell p m lower)‖ ≤
          B * Real.exp (-(2 * Real.pi *
            ((if lower then G1RatioTail.complexL M τ w y h ell p
              else G1RatioTail.complexS M τ w h ell) / etaDenom M τ).re) * t) := by
  let A : ℂ → ℂ := fun τ =>
    (if lower then G1RatioTail.complexL M τ w y h ell p
      else G1RatioTail.complexS M τ w h ell) / etaDenom M τ
  let K := ModularSector.parameterDisk τ₀ ρ ×ˢ Icc a b
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  let f : ℤ → (ℂ × ℝ) → ℂ := fun m q =>
    e (A q.1 * (q.2 : ℂ) + phaseConstant M q.1 w y n h ell p m lower)
  have hf : ∀ m ∈ F, ContinuousOn (f m) K := by
    intro m hm
    have hA : ContinuousOn A (ModularSector.parameterDisk τ₀ ρ) := by
      intro τ hτ
      exact (analyticAt_slope M w y h ell p (hdisk hτ) lower).continuousAt.continuousWithinAt
    have hB : ContinuousOn (fun τ => phaseConstant M τ w y n h ell p m lower)
        (ModularSector.parameterDisk τ₀ ρ) := by
      intro τ hτ
      exact (phaseConstant_continuous M w y n h ell p m lower (hdisk hτ)).continuousWithinAt
    have hA' : ContinuousOn (fun q : ℂ × ℝ => A q.1) K :=
      hA.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hB' : ContinuousOn (fun q : ℂ × ℝ =>
        phaseConstant M q.1 w y n h ell p m lower) K :=
      hB.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hx : Continuous (fun q : ℂ × ℝ => (q.2 : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_snd
    have he : Continuous e := by unfold e; fun_prop
    exact he.comp_continuousOn ((hA'.mul hx.continuousOn).add hB')
  obtain ⟨B, hB, hbound⟩ := finite_compact_bound F K hK f hf
  refine ⟨B, hB, ?_⟩
  intro τ hτ m hm x hx t
  rw [norm_e_vertical]
  exact mul_le_mul_of_nonneg_right (hbound m hm (τ, x) ⟨hτ, hx⟩) (Real.exp_pos _).le

lemma lower_window_margin (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hL : g1L M τ₀ w y h ell p < 0) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).re ∧
          κ ≤ -(2 * Real.pi *
            (G1RatioTail.complexL M τ (w : ℂ) (y : ℂ) h ell p / etaDenom M τ).re) := by
  have hS : 0 < g1S M τ₀ (-w - y) (-h) (1 - p - ell) := by
    have he : g1S M τ₀ (-w - y) (-h) (1 - p - ell) =
        -g1L M τ₀ w y h ell p := by
      unfold g1L g1S
      push_cast
      ring
    rw [he]
    linarith
  obtain ⟨ρ, κ, hρ, hκ, hm⟩ :=
    G1BilateralGeometry.single_window_margin M hM τ₀ (-w - y) (-h) (1 - p - ell) hT hS
  refine ⟨ρ, κ, hρ, hκ, ?_⟩
  intro τ hτ
  obtain ⟨hd, hden, hk⟩ := hm τ hτ
  refine ⟨hd, hden, ?_⟩
  have he : G1RatioTail.complexS M τ ((-w - y : ℝ) : ℂ) (-h) (1 - p - ell) =
      -G1RatioTail.complexL M τ (w : ℂ) (y : ℂ) h ell p := by
    unfold G1RatioTail.complexL G1RatioTail.complexS
    push_cast
    ring
  simpa only [he, neg_div, Complex.neg_re, mul_neg] using hk

/-- Both tail estimates are the same affine exponential estimate after reflection. -/
lemma uniform_tail_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (lower : Bool)
    (hwindow : ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        τ ∈ modularPhiDomain M ∧
          κ ≤ if lower then -(2 * Real.pi *
            (G1RatioTail.complexL M τ (w : ℂ) (y : ℂ) h ell p / etaDenom M τ).re)
          else 2 * Real.pi *
            (G1RatioTail.complexS M τ (w : ℂ) h ell / etaDenom M τ).re) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
        ∀ x ∈ Icc a b, ∀ t : ℝ, R ≤ |t| →
          (if lower then t ≤ 0 else 0 ≤ t) →
          ‖G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m
            (g1VerticalPoint x t)‖ ≤ C * Real.exp (-κ * |t|) := by
  obtain ⟨ρw, κ, hρw, hκ, hw⟩ := hwindow
  let A := max |a| |b|
  obtain ⟨α, Rs, hα, hα', hRs, hsector⟩ := G1BilateralGeometry.upper_strip_sector (-A) A
  obtain ⟨ρs, Cs, k, Rt, hρs, hCs, hk, hRt, hdec⟩ :=
    G1BilateralGeometry.finite_shift_ratio_estimates M hM F n p τ₀ α (y : ℂ) hT hα hα'
  let ρ := min ρw ρs
  have hdisk : ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M :=
    fun τ hτ => (hw τ (disk_mono (min_le_left _ _) hτ)).1
  obtain ⟨B, hB, hphase⟩ := affine_phase_bound M (w : ℂ) (y : ℂ) n h ell p F
    τ₀ ρ a b lower hdisk
  refine ⟨ρ, (Cs + 1) * B, κ, max Rs (2 * Rt), lt_min hρw hρs,
    by positivity, hκ, lt_of_lt_of_le hRs (le_max_left _ _), ?_⟩
  intro τ hτ m hm x hx t ht hsign
  have hxA : x ∈ Icc (-A) A := by
    have ha : |a| ≤ A := le_max_left _ _
    have hb : |b| ≤ A := le_max_right _ _
    constructor <;> linarith [neg_abs_le a, le_abs_self b, hx.1, hx.2]
  have hxA' : -x ∈ Icc (-A) A := ⟨by linarith [hxA.2], by linarith [hxA.1]⟩
  have hmag : 2 * Rt ≤ |t| := (le_max_right Rs (2 * Rt)).trans ht
  have hmagS : Rs ≤ |t| := (le_max_left Rs (2 * Rt)).trans ht
  have hz : (if lower then -g1VerticalPoint x t else g1VerticalPoint x t) ∈
      ModularSector.upperSector α Rt := by
    cases lower
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      rw [abs_of_nonneg hsign] at hmag hmagS
      exact ModularSector.upperSector_antitone le_rfl (by linarith)
        (hsector x hxA t hmagS)
    · simp only [↓reduceIte] at hsign ⊢
      rw [abs_of_nonpos hsign] at hmag hmagS
      have he : -g1VerticalPoint x t = g1VerticalPoint (-x) (-t) := by
        simp [g1VerticalPoint]; ring
      rw [he]
      exact ModularSector.upperSector_antitone le_rfl (by linarith)
        (hsector (-x) hxA' (-t) hmagS)
  let z := g1VerticalPoint x t
  let Q := modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + (y : ℂ)) τ
  let U := modularReflectionFactor M (m + 1) n z τ /
    modularReflectionFactor M (m + p) n (z + (y : ℂ)) τ
  have hq : ‖(if lower then Q / U else Q)‖ ≤ Cs + 1 := by
    have he := hdec τ (disk_mono (min_le_right _ _) hτ) m hm
    have hexp : Cs * Real.exp (-k * ‖z‖) ≤ Cs := by
      calc _ ≤ Cs * 1 := mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg z])) hCs.le
           _ = Cs := mul_one _
    have hnorm (q : ℂ) (hq : ‖q - 1‖ + ‖q⁻¹ - 1‖ ≤ Cs * Real.exp (-k * ‖z‖)) :
        ‖q‖ ≤ Cs + 1 := by
      have hn := norm_le_norm_sub_add q 1
      have heq : ‖q - 1‖ ≤ Cs := (le_trans (le_add_of_nonneg_right (norm_nonneg _)) hq).trans hexp
      simp only [norm_one] at hn
      linarith
    cases lower
    · exact hnorm Q (he.1 z hz)
    · have hb := he.2 z hz
      have hn := norm_le_norm_sub_add (Q / U) 1
      have heq : ‖Q / U - 1‖ ≤ Cs :=
        (le_trans (le_add_of_nonneg_right (norm_nonneg _)) hb).trans hexp
      change ‖Q / U‖ ≤ Cs + 1
      simp only [norm_one] at hn
      linarith
  let S := (if lower then G1RatioTail.complexL M τ (w : ℂ) (y : ℂ) h ell p
    else G1RatioTail.complexS M τ (w : ℂ) h ell) / etaDenom M τ
  have hker : ‖G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m z‖ =
      ‖(if lower then Q / U else Q)‖ *
        ‖e (S * z + phaseConstant M τ (w : ℂ) (y : ℂ) n h ell p m lower)‖ := by
    have hT' : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M (hdisk hτ)
    cases lower
    · rw [kernel_eq, norm_mul, G1RatioTail.exponent_affine M τ (w : ℂ) z n h ell m hT']
      simp only [S, Q, phaseConstant, Bool.false_eq_true, ↓reduceIte, zero_add]
    · rw [norm_lower_kernel M hM τ (w : ℂ) (y : ℂ) z n h ell p m (hdisk hτ),
        lower_phase_affine M τ (w : ℂ) (y : ℂ) z n h ell p m hT']
      rfl
  have hexponent : -(2 * Real.pi * S.re) * t ≤ -κ * |t| := by
    have hmargin := (hw τ (disk_mono (min_le_left _ _) hτ)).2
    cases lower
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign hmargin
      rw [abs_of_nonneg hsign]
      dsimp only [S]
      simpa only [Bool.false_eq_true, ↓reduceIte, neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right hmargin hsign)
    · simp only [↓reduceIte] at hsign hmargin
      rw [abs_of_nonpos hsign]
      dsimp only [S]
      simp only [↓reduceIte]
      nlinarith [mul_le_mul_of_nonpos_right hmargin hsign]
  rw [hker]
  calc
    _ ≤ (Cs + 1) * (B * Real.exp (-(2 * Real.pi * S.re) * t)) :=
      mul_le_mul hq (hphase τ hτ m hm x hx t) (norm_nonneg _)
        (by positivity)
    _ ≤ (Cs + 1) * B * Real.exp (-κ * |t|) := by
      calc _ = ((Cs + 1) * B) * Real.exp (-(2 * Real.pi * S.re) * t) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
             (mul_nonneg (by linarith) hB.le)

lemma decay_mono {C C' k k' t : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C')
    (hk : k' ≤ k) (ht : 0 ≤ t) :
    C * Real.exp (-k * t) ≤ C' * Real.exp (-k' * t) := by
  exact mul_le_mul hCC (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
    (hC.trans hCC)

lemma kernel_measurable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n h ell p m : ℤ) (hτ : τ ∈ modularPhiDomain M) :
    Measurable (G1RatioTail.complexKernel M τ w y n h ell p m) := by
  have hm : Meromorphic (G1RatioTail.complexKernel M τ w y n h ell p m) :=
    fun z => ModularCluster.kernel_meromorphic M hM _ τ hτ z (Set.mem_univ z)
  exact hm.measurable


lemma vertical_joint_continuousAt (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (w y : ℂ) (n h ell p m : ℤ) (x t : ℝ) {τ : ℂ}
    (hreg : (g1VerticalPoint x t, τ) ∈ ModularCluster.regularDomain M
      (G1Pinch.ratioData w y n h ell p m)) :
    ContinuousAt (fun q : ℂ × ℝ => g1VerticalPullback
      (G1RatioTail.complexKernel M q.1 w y n h ell p m) x q.2) (τ, t) := by
  have hm : ContinuousAt (fun q : ℂ × ℝ => (g1VerticalPoint x q.2, q.1)) (τ, t) := by
    unfold g1VerticalPoint
    fun_prop
  exact ((kernel_analytic M hM w y n h ell p m hreg).continuousAt.comp
    (f := fun q : ℂ × ℝ => (g1VerticalPoint x q.2, q.1)) hm).mul continuousAt_const

lemma circle_joint_continuousAt (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (w y : ℂ) (n h ell p m : ℤ) (r ρ θ : ℝ) {τ : ℂ}
    (hreg : (circleMap (r : ℂ) ρ θ, τ) ∈ ModularCluster.regularDomain M
      (G1Pinch.ratioData w y n h ell p m)) :
    ContinuousAt (fun q : ℂ × ℝ => g1CirclePullback
      (G1RatioTail.complexKernel M q.1 w y n h ell p m) r ρ q.2) (τ, θ) := by
  have hm : ContinuousAt (fun q : ℂ × ℝ => (circleMap (r : ℂ) ρ q.2, q.1)) (τ, θ) :=
    (((continuous_circleMap (r : ℂ) ρ).comp continuous_snd).prodMk continuous_fst).continuousAt
  exact ((kernel_analytic M hM w y n h ell p m hreg).continuousAt.comp
    (f := fun q : ℂ × ℝ => (circleMap (r : ℂ) ρ q.2, q.1)) hm).mul
      (continuous_const.mul (((continuous_circleMap (r : ℂ) ρ).comp continuous_snd).sub
        continuous_const)).continuousAt

lemma abs_majorant_integrable (C κ R : ℝ) (hκ : 0 < κ) :
    Integrable (fun t : ℝ => if |t| ≤ R then C else C * Real.exp (-κ * |t|)) := by
  have h₁ : Integrable ((Icc (-R) R).indicator (fun _ : ℝ => C)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (s := Icc (-R) R) (C := C) (μ := volume)
        (by simp only [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have h₂ : Integrable (((Icc (-R) R)ᶜ).indicator
      (fun t : ℝ => C * Real.exp (-κ * |t|))) :=
    (G1RatioTail.exponential_majorant_integrable C κ hκ).indicator measurableSet_Icc.compl
  have heq : (fun t : ℝ => if |t| ≤ R then C else C * Real.exp (-κ * |t|)) =
      fun t : ℝ => (Icc (-R) R).indicator (fun _ : ℝ => C) t +
        ((Icc (-R) R)ᶜ).indicator (fun t : ℝ => C * Real.exp (-κ * |t|)) t := by
    funext t
    by_cases ht : |t| ≤ R
    · have ht' : t ∈ Icc (-R) R := abs_le.mp ht
      simp [ht, ht']
    · have ht' : t ∉ Icc (-R) R := fun h => ht (abs_le.mpr h)
      simp [ht, ht']
  rw [heq]
  exact h₁.add h₂

/-- A holomorphic dominated family has an analytic integral on a closed subdisk. -/
lemma integral_analytic_of_domination
    {μ : Measure ℝ} {F : ℂ → ℝ → ℂ} {c : ℂ} {R : ℝ} {B : ℝ → ℝ}
    (hR : 0 < R)
    (hm : ∀ q ∈ Metric.closedBall c R, AEStronglyMeasurable (F q) μ)
    (hdm : ∀ q ∈ Metric.closedBall c R,
      AEStronglyMeasurable (fun t => fderiv ℂ (fun v => F v t) q) μ)
    (hh : ∀ t, AnalyticOnNhd ℂ (fun q => F q t) (Metric.closedBall c R))
    (hB : ∀ᵐ t ∂μ, ∀ q ∈ Metric.closedBall c R, ‖F q t‖ ≤ B t)
    (hBi : Integrable B μ) :
    AnalyticOnNhd ℂ (fun q => ∫ t, F q t ∂μ)
      (Metric.closedBall c (R / 2)) := by
  have hd : DifferentiableOn ℂ (fun q => ∫ t, F q t ∂μ) (Metric.ball c R) := by
    intro q hq
    let r := (R - dist q c) / 4
    have hr : 0 < r := by
      dsimp [r]
      exact div_pos (sub_pos.mpr hq) (by norm_num)
    have hsub : Metric.ball q (2*r) ⊆ Metric.closedBall c R := by
      intro v hv
      simp only [Metric.mem_ball] at hq hv
      simp only [Metric.mem_closedBall]
      have htri := dist_triangle v q c
      dsimp [r] at hv
      linarith
    have hqc : q ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hq
    have hint : Integrable (F q) μ :=
      hBi.mono' (hm q hqc) (hB.mono fun t ht => ht q hqc)
    have hmeas : ∀ᶠ v in 𝓝 q, AEStronglyMeasurable (F v) μ := by
      filter_upwards [Metric.ball_mem_nhds q (show 0 < 2*r by positivity)] with v hv
      exact hm v (hsub hv)
    have hbound : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball q r,
        ‖fderiv ℂ (fun u => F u t) v‖ ≤ (2 * B t) / r := by
      filter_upwards [hB] with t ht v hv
      exact joint_norm_fderiv_le_of_ball_bound hr hv
        ((hh t).differentiableOn.mono hsub)
        (fun u hu => ht u (hsub hu))
    have hdiff : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball q r,
        HasFDerivAt (fun u => F u t) (fderiv ℂ (fun u => F u t) v) v := by
      exact Eventually.of_forall fun t v hv =>
        (hh t v (hsub (Metric.ball_subset_ball (by linarith) hv))).differentiableAt.hasFDerivAt
    exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds q hr) hmeas hint (hdm q hqc) hbound
      ((hBi.const_mul 2).div_const r) hdiff).differentiableAt.differentiableWithinAt
  exact (hd.analyticOnNhd Metric.isOpen_ball).mono
    (Metric.closedBall_subset_ball (by linarith))

lemma continuous_parameter_fderiv
    {K : ℂ × ℂ → ℂ} {z j : ℝ → ℂ} {τ : ℂ}
    (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ t, AnalyticAt ℂ K (z t, τ)) :
    Continuous (fun t => fderiv ℂ (fun q => K (z t, q) * j t) τ) := by
  have hdiff (t : ℝ) :
      DifferentiableAt ℂ (fun q => K (z t, q)) τ :=
    ((hK t).comp (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hcont :
      Continuous (fun t => fderiv ℂ (fun q => K (z t, q)) τ) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc : ContDiffAt ℂ 1 K (z t, τ) := (hK t).contDiffAt
    have hc' :
        ContinuousAt (fun v : ℂ => fderiv ℂ (fun q => K (v, q)) τ) (z t) :=
      (hc.fderiv
        (contDiffAt_const : ContDiffAt ℂ 0 (fun _ : ℂ => τ) (z t))
        (by norm_num)).continuousAt
    exact hc'.comp hz.continuousAt
  simpa only [fderiv_mul_const (hdiff _) _] using hj.fun_smul hcont

lemma pullback_integral_analytic {μ : Measure ℝ} {K : ℂ × ℂ → ℂ}
    {z j : ℝ → ℂ} {c : ℂ} {R : ℝ} {B : ℝ → ℝ}
    (hR : 0 < R) (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ τ ∈ Metric.closedBall c R, ∀ t : ℝ, AnalyticAt ℂ K (z t, τ))
    (hB : ∀ᵐ t ∂μ, ∀ τ ∈ Metric.closedBall c R, ‖K (z t, τ) * j t‖ ≤ B t)
    (hBi : Integrable B μ) :
    AnalyticOnNhd ℂ (fun τ => ∫ t, K (z t, τ) * j t ∂μ)
      (Metric.closedBall c (R / 2)) := by
  apply integral_analytic_of_domination hR
  · intro τ hτ
    apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (((hK τ hτ t).continuousAt.comp (f := fun t : ℝ => (z t, τ))
      (hz.continuousAt.prodMk continuousAt_const)).mul hj.continuousAt)
  · intro τ hτ
    exact (continuous_parameter_fderiv (K := K) (z := z) (j := j) hz hj
      (hK τ hτ)).aestronglyMeasurable
  · intro t τ hτ
    exact ((hK τ hτ t).comp (f := fun τ : ℂ => (z t, τ))
      (analyticAt_const.prod analyticAt_id)).mul analyticAt_const
  · exact hB
  · exact hBi

end SICLean.L4.G1BilateralRatioTailsAux
