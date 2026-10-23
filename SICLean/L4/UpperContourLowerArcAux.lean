import SICLean.L4.UpperContourBounds
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContourLowerArcAux

open UpperContour

theorem continuous_rotation : Continuous UpperWindow.rotation := by
  unfold UpperWindow.rotation
  fun_prop

theorem norm_rotation (θ : ℝ) : ‖UpperWindow.rotation θ‖ = 1 := by
  simp [UpperWindow.rotation, Complex.norm_exp]

theorem hasDerivAt_rotation (θ : ℝ) :
    HasDerivAt UpperWindow.rotation (I * UpperWindow.rotation θ) θ := by
  simpa [UpperWindow.rotation, mul_comm] using!
    (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul I |>.cexp

theorem hasDerivAt_arcPoint (v : ℂ) (r θ : ℝ) :
    HasDerivAt (UpperContour.arcPoint v r) (I * (r : ℂ) * UpperWindow.rotation θ) θ := by
  simpa only [UpperContour.arcPoint, mul_assoc, mul_left_comm I (r : ℂ)] using!
    ((hasDerivAt_rotation θ).const_mul (r : ℂ)).const_add v

/-- The finite polar contour identity.  Holomorphy is required at each point
of the closed parameter rectangle; no globally chosen primitive is needed. -/
theorem finite_rotation_of_differentiable
    (f : ℂ → ℂ) (v : ℂ) (r a b : ℝ) (hr : 0 ≤ r) (hab : a ≤ b)
    (hf : ∀ θ ∈ Icc a b, ∀ t ∈ Icc 0 r,
      DifferentiableAt ℂ f (UpperContour.arcPoint v t θ)) :
    rayFinite f v (UpperWindow.rotation a) r + arcIntegral f v r a b -
      rayFinite f v (UpperWindow.rotation b) r = 0 := by
  let L₁ : ℝ × ℝ →L[ℝ] ℂ :=
    Complex.ofRealCLM ∘L ContinuousLinearMap.fst ℝ ℝ ℝ
  let L₂ : ℝ × ℝ →L[ℝ] ℂ :=
    Complex.ofRealCLM ∘L ContinuousLinearMap.snd ℝ ℝ ℝ
  let ρ : ℝ × ℝ → ℂ := fun p => UpperWindow.rotation p.1
  let H : ℝ × ℝ → ℂ := fun p => UpperContour.arcPoint v p.2 p.1
  let dρ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => (I * ρ p) • L₁
  let dH : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    ρ p • L₂ + (I * (H p - v)) • L₁
  have hρ (p : ℝ × ℝ) : HasFDerivAt ρ (dρ p) p := by
    simpa [ρ, UpperWindow.rotation, dρ, L₁, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using
      ((L₁.hasFDerivAt (x := p)).const_mul I).cexp
  have hH (p : ℝ × ℝ) : HasFDerivAt H (dH p) p := by
    have hz : HasFDerivAt (fun p : ℝ × ℝ => (p.2 : ℂ)) L₂ p :=
      L₂.hasFDerivAt
    apply ((hz.mul (hρ p)).const_add v).congr_fderiv
    apply ContinuousLinearMap.ext
    intro q
    simp [dH, dρ, L₁, L₂, H, ρ, UpperContour.arcPoint, smul_eq_mul]
    ring
  let df : ℝ × ℝ → ℂ := fun p => deriv f (H p)
  let A : ℝ × ℝ → ℂ := fun p => f (H p) * ρ p
  let G : ℝ × ℝ → ℂ := fun p => -(f (H p) * (I * (H p - v)))
  let dA : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    f (H p) • dρ p + ρ p • (df p • dH p)
  let dG : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    -(f (H p) • (I • dH p) + (I * (H p - v)) • (df p • dH p))
  have hfd (p : ℝ × ℝ) (hp : p ∈ Icc (a, 0) (b, r)) :
      DifferentiableAt ℂ f (H p) :=
    hf p.1 ⟨hp.1.1, hp.2.1⟩ p.2 ⟨hp.1.2, hp.2.2⟩
  have hfc : ContinuousOn (fun p => f (H p)) (Icc (a, 0) (b, r)) := by
    intro p hp
    exact ((hfd p hp).continuousAt.comp (hH p).continuousAt).continuousWithinAt
  have hAc : ContinuousOn A (Icc (a, 0) (b, r)) :=
    hfc.mul (fun p _ => (hρ p).continuousAt.continuousWithinAt)
  have hHc : ContinuousOn H (Icc (a, 0) (b, r)) :=
    fun p _ => (hH p).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (Icc (a, 0) (b, r)) :=
    (hfc.mul (continuousOn_const.mul (hHc.sub continuousOn_const))).neg
  have hderiv (p : ℝ × ℝ) (hp : p ∈ Icc (a, 0) (b, r)) :
      HasFDerivAt (fun p => f (H p)) (df p • dH p) p :=
    (hfd p hp).hasDerivAt.comp_hasFDerivAt p (hH p)
  have hAd (p : ℝ × ℝ) (hp : p ∈ Ioo a b ×ˢ Ioo 0 r) :
      HasFDerivAt A (dA p) p := by
    exact (hderiv p ⟨⟨hp.1.1.le, hp.2.1.le⟩,
      ⟨hp.1.2.le, hp.2.2.le⟩⟩).mul (hρ p)
  have hGd (p : ℝ × ℝ) (hp : p ∈ Ioo a b ×ˢ Ioo 0 r) :
      HasFDerivAt G (dG p) p := by
    exact ((hderiv p ⟨⟨hp.1.1.le, hp.2.1.le⟩,
      ⟨hp.1.2.le, hp.2.2.le⟩⟩).mul
      (((hH p).sub_const v).const_mul I)).neg
  have hzero (p : ℝ × ℝ) : dA p (1, 0) + dG p (0, 1) = 0 := by
    simp [dA, dG, dρ, dH, L₁, L₂, H, ρ, UpperContour.arcPoint, smul_eq_mul]
    ring
  have hi : IntegrableOn (fun p => dA p (1, 0) + dG p (0, 1))
      (Icc (a, 0) (b, r)) := by
    simp_rw [hzero]
    exact integrableOn_zero
  have hgreen := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    A G dA dG (a, 0) (b, r) ⟨hab, hr⟩ hAc hGc hAd hGd hi
  simp only [hzero, integral_zero, A, G, H, ρ, UpperContour.arcPoint,
    ofReal_zero, zero_mul, add_zero, add_sub_cancel_left, mul_zero, neg_zero,
    intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_neg] at hgreen
  have hc : (∫ θ : ℝ in a..b, f (v + (r : ℂ) * UpperWindow.rotation θ) *
      (I * ((r : ℂ) * UpperWindow.rotation θ))) = arcIntegral f v r a b := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp [arcIntegral, arcPullback, UpperContour.arcPoint]
    ring
  rw [hc] at hgreen
  change 0 = (-arcIntegral f v r a b + rayFinite f v (UpperWindow.rotation b) r) -
    rayFinite f v (UpperWindow.rotation a) r at hgreen
  linear_combination hgreen

theorem norm_arcPullback (f : ℂ → ℂ) (v : ℂ) (r θ : ℝ) (hr : 0 ≤ r) :
    ‖arcPullback f v r θ‖ = r * ‖f (UpperContour.arcPoint v r θ)‖ := by
  simp [arcPullback, norm_mul, norm_rotation, abs_of_nonneg hr, mul_comm]

theorem norm_arcIntegral_le (f : ℂ → ℂ) (v : ℂ) (r a b B : ℝ)
    (hr : 0 ≤ r) (hab : a ≤ b)
    (hbound : ∀ θ ∈ Icc a b, ‖f (UpperContour.arcPoint v r θ)‖ ≤ B) :
    ‖arcIntegral f v r a b‖ ≤ (b - a) * r * B := by
  calc
    ‖arcIntegral f v r a b‖ ≤ (r * B) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro θ hθ
      rw [norm_arcPullback f v r θ hr]
      apply mul_le_mul_of_nonneg_left _ hr
      exact hbound θ (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hθ)
    _ = (b - a) * r * B := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

theorem arcPullback_intervalIntegrable (f : ℂ → ℂ) (v : ℂ) (r a b : ℝ)
    (hab : a ≤ b)
    (hf : ∀ θ ∈ Icc a b, ContinuousAt f (UpperContour.arcPoint v r θ)) :
    IntervalIntegrable (arcPullback f v r) volume a b := by
  have hfc : ContinuousOn (fun θ => f (UpperContour.arcPoint v r θ)) (Icc a b) := by
    intro θ hθ
    exact ((hf θ hθ).comp (hasDerivAt_arcPoint v r θ).continuousAt).continuousWithinAt
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hfc.mul (continuous_const.mul continuous_rotation).continuousOn

theorem kernel_analyticAt_of_nonvanishing (kind : Kind) (M : SL(2, ℤ))
    (hM : 0 < M 1 0) (m n h ℓ p : ℤ) (x : UpperWindow.Parameters) (z : ℂ)
    (hnum : (z, x.1) ∈ modularPhiNonvanishingDomain M (m + 1) n)
    (hden : (z + x.2.2, x.1) ∈ modularPhiNonvanishingDomain M (m + p) n) :
    AnalyticAt ℂ (UpperContour.kernel kind M m n h ℓ p x) z := by
  have ht : AnalyticAt ℂ (fun w : ℂ => (w, x.1)) z :=
    analyticAt_id.prod analyticAt_const
  have hty : AnalyticAt ℂ (fun w : ℂ => (w + x.2.2, x.1)) z :=
    (analyticAt_id.add analyticAt_const).prod analyticAt_const
  have hA : AnalyticAt ℂ (fun w => modularPhi M (m + 1) n w x.1) z := by
    exact (modularPhi_joint_analytic_no_poles M hM (m + 1) n (z, x.1)
      ⟨hnum.1, hnum.2.1⟩).comp (f := fun w : ℂ => (w, x.1)) (x := z) ht
  have hB : AnalyticAt ℂ (fun w => modularPhi M (m + p) n (w + x.2.2) x.1) z := by
    exact (modularPhi_joint_analytic_no_poles M hM (m + p) n (z + x.2.2, x.1)
      ⟨hden.1, hden.2.1⟩).comp (f := fun w : ℂ => (w + x.2.2, x.1)) (x := z) hty
  have hBne : modularPhi M (m + p) n (z + x.2.2) x.1 ≠ 0 :=
    (modularPhi_ne_zero_iff M hM (m + p) n (z + x.2.2) x.1 hden.1
      hden.2.1).mpr hden.2.2
  have he : AnalyticAt ℂ (fun w => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 w)) z := by
    unfold e UpperWindow.phase
    fun_prop
  cases kind with
  | single => simpa only [UpperContour.kernel, UpperWindow.singleKernel] using! hA.mul he
  | ratio => simpa only [UpperContour.kernel, UpperWindow.ratioKernel] using! (hA.div hB hBne).mul he

theorem lower_sector_analyticAt (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    AnalyticAt ℂ (UpperContour.kernel kind M m n h ℓ p x)
      (UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ) := by
  obtain ⟨hnum, hden⟩ := UpperWindow.sector_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx
    r θ hr (Or.inr hθ)
  exact kernel_analyticAt_of_nonvanishing kind M hc.1 m n h ℓ p x _ hnum hden

theorem lower_sector_differentiableAt (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    DifferentiableAt ℂ (UpperContour.kernel kind M m n h ℓ p x)
      (UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ) :=
  (lower_sector_analyticAt kind M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ).differentiableAt

theorem norm_rotated_rayPullback (f : ℂ → ℂ) (v : ℂ) (r θ : ℝ) :
    ‖rayPullback f v (UpperWindow.rotation θ) r‖ =
      ‖f (UpperContour.arcPoint v r θ)‖ := by
  simp only [rayPullback, UpperContour.arcPoint, norm_mul, norm_rotation, mul_one]

theorem lower_rayPullback_continuousOn (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (θ : ℝ)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    ContinuousOn (rayPullback (UpperContour.kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (UpperWindow.rotation θ)) (Ici 0) := by
  intro r hr
  have hpoint := (lower_sector_analyticAt kind M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ).continuousAt
  have hpath : Continuous (fun t : ℝ => UpperWindow.base M m n δ x.1 +
      (t : ℂ) * UpperWindow.rotation θ) := by fun_prop
  have hp : ContinuousAt (UpperContour.kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1 + (r : ℂ) * UpperWindow.rotation θ) := hpoint
  exact ((hp.comp (x := r) hpath.continuousAt).mul continuousAt_const).continuousWithinAt

theorem norm_e (z : ℂ) : ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  unfold e
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem rotation_sq (θ : ℝ) :
    (UpperWindow.rotation θ) ^ 2 = UpperWindow.rotation (2 * θ) := by
  unfold UpperWindow.rotation
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem rotation_div_im (T : ℂ) (θ : ℝ) (hT : T ≠ 0) :
    (UpperWindow.rotation θ / T).im = Real.sin (θ - T.arg) / ‖T‖ := by
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT
  simp only [UpperWindow.rotation, mul_comm I, Complex.div_im,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re,
    Real.sin_sub, Complex.cos_arg hT, Complex.sin_arg,
    Complex.normSq_eq_norm_sq]
  field_simp

theorem negative_quadratic_exponent (T : ℂ) (c r θ : ℝ) (hT : T ≠ 0) :
    -2 * Real.pi * (-(c : ℂ) / (2 * T) *
      ((r : ℂ) * UpperWindow.rotation θ) ^ 2).im =
      (Real.pi * c / ‖T‖) * r ^ 2 * Real.sin (2 * θ - T.arg) := by
  have hq : -(c : ℂ) / (2 * T) * ((r : ℂ) * UpperWindow.rotation θ) ^ 2 =
      ((-c * r ^ 2 / 2 : ℝ) : ℂ) * ((UpperWindow.rotation θ) ^ 2 / T) := by
    push_cast
    ring
  simp only [hq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, rotation_sq, rotation_div_im T (2 * θ) hT]
  ring

theorem single_exp_signed_bound (P L T : ℂ) (c r θ : ℝ)
    (hT : T ≠ 0) (hr : 0 ≤ r) :
    ‖e (P + L * ((r : ℂ) * UpperWindow.rotation θ) -
      (c : ℂ) / (2 * T) * ((r : ℂ) * UpperWindow.rotation θ) ^ 2)‖ ≤
      ‖e P‖ * Real.exp ((Real.pi * c / ‖T‖) * r ^ 2 *
        Real.sin (2 * θ - T.arg) + 2 * Real.pi * ‖L‖ * r) := by
  have hrot : ‖UpperWindow.rotation θ‖ = 1 := by
    simp [UpperWindow.rotation, Complex.norm_exp]
  have hlin : -(L * ((r : ℂ) * UpperWindow.rotation θ)).im ≤ ‖L‖ * r := by
    calc
      -(L * ((r : ℂ) * UpperWindow.rotation θ)).im ≤
          |(L * ((r : ℂ) * UpperWindow.rotation θ)).im| := neg_le_abs _
      _ ≤ ‖L * ((r : ℂ) * UpperWindow.rotation θ)‖ := Complex.abs_im_le_norm _
      _ = ‖L‖ * r := by simp [norm_mul, hrot, abs_of_nonneg hr]
  have hquad := negative_quadratic_exponent T c r θ hT
  rw [norm_e, norm_e, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlin' := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 2 * Real.pi by positivity)
  simp only [Complex.sub_im, Complex.add_im] at *
  simp only [neg_div, neg_mul, Complex.neg_im] at hquad
  nlinarith

theorem affine_exp_bound (P L : ℂ) (r θ lam : ℝ) (hr : 0 ≤ r)
    (hlam : lam ≤ (L * UpperWindow.rotation θ).im) :
    ‖e (P + L * ((r : ℂ) * UpperWindow.rotation θ))‖ ≤
      ‖e P‖ * Real.exp (-2 * Real.pi * lam * r) := by
  rw [norm_e, norm_e, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlam hr
  have heq : (L * ((r : ℂ) * UpperWindow.rotation θ)).im =
      r * (L * UpperWindow.rotation θ).im := by
    rw [show L * ((r : ℂ) * UpperWindow.rotation θ) =
      (r : ℂ) * (L * UpperWindow.rotation θ) by ring]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Complex.add_im, heq]
  nlinarith [Real.pi_pos]


theorem radius_mul_exp_tendsto_zero (k : ℝ) (hk : 0 < k) :
    Tendsto (fun r : ℝ => r * Real.exp (-k * r)) atTop (𝓝 0) := by
  simpa only [Real.rpow_one] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 k hk

/-- A global exponential majorant obtained by completing the square. -/
theorem gaussian_le_exponential (a b r : ℝ) (ha : 0 < a) :
    Real.exp (-a * r ^ 2 + b * r) ≤
      Real.exp ((b + 1) ^ 2 / (4 * a)) * Real.exp (-r) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq : -a * r ^ 2 + (b + 1) * r ≤ (b + 1) ^ 2 / (4 * a) := by
    apply (le_div_iff₀ (show 0 < 4 * a by positivity)).mpr
    nlinarith [sq_nonneg (2 * a * r - (b + 1))]
  linarith

theorem radius_mul_gaussian_tendsto_zero (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun r : ℝ => r * Real.exp (-a * r ^ 2 + b * r)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun r : ℝ =>
    Real.exp ((b + 1) ^ 2 / (4 * a)) * (r * Real.exp (-r)))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact mul_nonneg hr (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simpa only [mul_assoc, mul_left_comm r] using
      mul_le_mul_of_nonneg_left (gaussian_le_exponential a b r ha) hr
  · simpa only [neg_mul, one_mul, mul_zero] using
      (radius_mul_exp_tendsto_zero 1 zero_lt_one).const_mul
        (Real.exp ((b + 1) ^ 2 / (4 * a)))

theorem integrableOn_of_exponential_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (C k : ℝ) (hk : 0 < k)
    (hf : ContinuousOn f (Ioi 0))
    (hbound : ∀ r ∈ Ioi (0 : ℝ), ‖f r‖ ≤ C * Real.exp (-k * r)) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  apply ((integrableOn_exp_mul_Ioi (a := -k) (by linarith) 0).const_mul C).mono'
    (hf.aestronglyMeasurable measurableSet_Ioi)
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hbound)

theorem tendsto_zero_of_radius_exponential_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (C k : ℝ) (hk : 0 < k)
    (hbound : ∀ r : ℝ, 0 ≤ r → ‖f r‖ ≤ C * r * Real.exp (-k * r)) :
    Tendsto f atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun r : ℝ => C * r * Real.exp (-k * r))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact hbound r hr
  · simpa only [mul_assoc, mul_zero] using (radius_mul_exp_tendsto_zero k hk).const_mul C

theorem tendsto_zero_of_radius_gaussian_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (C a b : ℝ) (ha : 0 < a)
    (hbound : ∀ r : ℝ, 0 ≤ r → ‖f r‖ ≤ C * r * Real.exp (-a * r ^ 2 + b * r)) :
    Tendsto f atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun r : ℝ => C * r * Real.exp (-a * r ^ 2 + b * r))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact hbound r hr
  · simpa only [mul_assoc, mul_zero] using
      (radius_mul_gaussian_tendsto_zero a b ha).const_mul C

lemma compact_qPochhammer_bounds (a η b : ℝ) (ha : a < 1) (hη : 0 < η) (hb : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u q : ℂ, ‖u‖ ≤ a → η ≤ ‖q‖ → ‖q‖ ≤ b →
      ‖qPochhammer u q‖ ≤ C ∧ ‖(qPochhammer u q)⁻¹‖ ≤ C := by
  let S : Set (ℂ × ℂ) := Metric.closedBall (0 : ℂ) a ×ˢ
    (Metric.closedBall (0 : ℂ) b ∩ {q : ℂ | η ≤ ‖q‖})
  have hS : IsCompact S := (isCompact_closedBall (0 : ℂ) a).prod
    ((isCompact_closedBall (0 : ℂ) b).inter_right
      (isClosed_le continuous_const continuous_norm))
  have hmem (p : ℂ × ℂ) (hp : p ∈ S) :
      ‖p.1‖ ≤ a ∧ η ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ b := by
    simpa only [S, Set.mem_prod, Metric.mem_closedBall, dist_zero_right,
      Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc, and_left_comm, and_comm] using hp
  have hcont : ContinuousOn (fun p : ℂ × ℂ => qPochhammer p.1 p.2) S := by
    intro p hp
    exact (analyticOnNhd_qPochhammer_joint p
      ⟨hη.trans_le (hmem p hp).2.1, (hmem p hp).2.2.trans_lt hb⟩).continuousAt.continuousWithinAt
  have hne (p : ℂ × ℂ) (hp : p ∈ S) : qPochhammer p.1 p.2 ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one _ _ ((hmem p hp).1.trans_lt ha)
      (hη.trans_le (hmem p hp).2.1) ((hmem p hp).2.2.trans_lt hb)
  obtain ⟨D, hD⟩ := hS.bddAbove_image hcont.norm
  obtain ⟨E, hE⟩ := hS.bddAbove_image (hcont.inv₀ hne).norm
  refine ⟨max 1 (max D E), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u q hu hqη hqb
  have hp : (u, q) ∈ S := by
    simpa only [S, Set.mem_prod, Metric.mem_closedBall, dist_zero_right,
      Set.mem_inter_iff, Set.mem_setOf_eq] using And.intro hu (And.intro hqb hqη)
  exact ⟨(hD (Set.mem_image_of_mem _ hp)).trans
      ((le_max_left D E).trans (le_max_right _ _)),
    (hE (Set.mem_image_of_mem _ hp)).trans
      ((le_max_right D E).trans (le_max_right _ _))⟩


lemma compact_modularPhi_bounds_of_arguments (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (a η b : ℝ) (ha : a < 1) (hη : 0 < η) (hb : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℤ) (z τ : ℂ), 0 < τ.im →
      η ≤ ‖e τ‖ → ‖e τ‖ ≤ b →
      η ≤ ‖e (etaMobius M τ)‖ → ‖e (etaMobius M τ)‖ ≤ b →
      ‖(e τ) ^ m * e z‖ ≤ a →
      ‖(e (etaMobius M τ)) ^ n * e (z / etaDenom M τ)‖ ≤ a →
      ‖modularPhi M m n z τ‖ ≤ C ∧ ‖(modularPhi M m n z τ)⁻¹‖ ≤ C := by
  obtain ⟨D, hD, hDb⟩ := compact_qPochhammer_bounds a η b ha hη hb
  refine ⟨D * D, mul_pos hD hD, ?_⟩
  intro m n z τ hτ hqη hqb hQη hQb hu hv
  have hnum := hDb ((e τ) ^ m * e z) (e τ) hu hqη hqb
  have hden := hDb ((e (etaMobius M τ)) ^ n * e (z / etaDenom M τ))
    (e (etaMobius M τ)) hv hQη hQb
  have hdenne : modularPhiQDenominator M n z τ ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one _ _ (hv.trans_lt ha)
      (hη.trans_le hQη) (hQb.trans_lt hb)
  rw [modularPhi_eq_qProduct M hM m n z τ hτ hdenne,
    modularPhiQProduct, modularPhiQNumerator, modularPhiQDenominator]
  constructor
  · rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul hnum.1 hden.2 (norm_nonneg _) hD.le
  · rw [inv_div, div_eq_mul_inv, norm_mul]
    exact mul_le_mul hden.1 hnum.2 (norm_nonneg _) hD.le

lemma reflected_q_argument (q z : ℂ) (hq : q ≠ 0) (k : ℤ) :
    q ^ (1 - k) * e (-z) = q / (q ^ k * e z) := by
  rw [zpow_sub₀ hq, zpow_one, e_neg']
  ring

lemma reflected_a_argument (m : ℤ) (z τ : ℂ) :
    (e τ) ^ (-m) * e (-z) = e τ / UpperWindow.aArg m τ z := by
  convert reflected_q_argument (e τ) z (e_ne_zero τ) (m + 1) using 1 <;>
    congr 2 <;> omega

lemma reflected_b_argument (m p : ℤ) (y z τ : ℂ) :
    (e τ) ^ (1 - m - p) * e (-z - y) = e τ / UpperWindow.bArg m p τ y z := by
  convert reflected_q_argument (e τ) (z + y) (e_ne_zero τ) (m + p) using 1 <;>
    congr 2 <;> ring

lemma reflected_d_argument (M : SL(2, ℤ)) (n : ℤ) (z τ : ℂ) :
    (e (etaMobius M τ)) ^ (1 - n) * e (-z / etaDenom M τ) =
      e (etaMobius M τ) / UpperWindow.dArg M n τ z := by
  simpa only [UpperWindow.dArg, neg_div] using
    reflected_q_argument (e (etaMobius M τ)) (z / etaDenom M τ)
      (e_ne_zero _) n

lemma reflected_c_argument (M : SL(2, ℤ)) (n : ℤ) (y z τ : ℂ) :
    (e (etaMobius M τ)) ^ (1 - n) * e ((-z - y) / etaDenom M τ) =
      e (etaMobius M τ) / UpperWindow.cArg M n τ y z := by
  rw [show (-z - y) / etaDenom M τ = -((z + y) / etaDenom M τ) by ring]
  exact reflected_q_argument (e (etaMobius M τ)) ((z + y) / etaDenom M τ)
    (e_ne_zero _) n


lemma norm_e_le_one_of_im_nonneg (z : ℂ) (hz : 0 ≤ z.im) : ‖e z‖ ≤ 1 := by
  rw [e, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [Complex.mul_re, Complex.mul_im]
  nlinarith [Real.pi_pos]

lemma reflected_a_add (m : ℤ) (z u τ : ℂ) :
    e τ / UpperWindow.aArg m τ (z + u) =
      (e τ / UpperWindow.aArg m τ z) * e (-u) := by
  simp only [UpperWindow.aArg, e_add', e_neg', div_eq_mul_inv, mul_inv_rev]
  ring

lemma reflected_b_add (m p : ℤ) (y z u τ : ℂ) :
    e τ / UpperWindow.bArg m p τ y (z + u) =
      (e τ / UpperWindow.bArg m p τ y z) * e (-u) := by
  unfold UpperWindow.bArg
  rw [show z + u + y = (z + y) + u by ring]
  simp only [e_add', e_neg', div_eq_mul_inv, mul_inv_rev]
  ring

lemma reflected_d_add (M : SL(2, ℤ)) (n : ℤ) (z u τ : ℂ) :
    e (etaMobius M τ) / UpperWindow.dArg M n τ (z + u) =
      (e (etaMobius M τ) / UpperWindow.dArg M n τ z) * e (-u / etaDenom M τ) := by
  unfold UpperWindow.dArg
  rw [add_div, e_add', neg_div, e_neg']
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma reflected_c_add (M : SL(2, ℤ)) (n : ℤ) (y z u τ : ℂ) :
    e (etaMobius M τ) / UpperWindow.cArg M n τ y (z + u) =
      (e (etaMobius M τ) / UpperWindow.cArg M n τ y z) * e (-u / etaDenom M τ) := by
  unfold UpperWindow.cArg
  rw [show z + u + y = (z + y) + u by ring, add_div, e_add', neg_div, e_neg']
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


lemma compact_lower_reflected_arguments_all_int (M : SL(2, ℤ)) (h ℓ p n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (K : Set UpperWindow.Parameters) (hK : IsCompact K)
    (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∀ x ∈ K, ∀ m : ℤ,
      ∀ r : ℝ, 0 ≤ r → ∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
      ‖e x.1 / UpperWindow.aArg m x.1 z‖ ≤ a ∧
        ‖e (etaMobius M x.1) / UpperWindow.dArg M n x.1 z‖ ≤ a ∧
        ‖e x.1 / UpperWindow.bArg m p x.1 x.2.2 z‖ ≤ a ∧
        ‖e (etaMobius M x.1) / UpperWindow.cArg M n x.1 x.2.2 z‖ ≤ a := by
  obtain ⟨a, ha0, ha1, hav⟩ := UpperWindow.compact_vertex_margin M h ℓ p n
    ψ σ ρ δ hc K hK hKU
  refine ⟨a, ha0, ha1, ?_⟩
  intro x hx m r hr θ hθ
  have hxU := hKU hx
  have hm0 : (0 : ℕ) ∈ Finset.range (M 1 0).toNat := by
    have hcpos := hc.1
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨_, _, _, _, hVA, hVD, hVB, hVC⟩ := hav x hx 0 hm0
  obtain ⟨hAm, hDm, hBm, hCm⟩ := UpperWindow.reflected_vertex_moduli M h ℓ p m n
    ψ σ ρ δ hc x hxU
  obtain ⟨hA0, hD0, hB0, hC0⟩ := UpperWindow.reflected_vertex_moduli M h ℓ p 0 n
    ψ σ ρ δ hc x hxU
  have hAm' : ‖e x.1 / UpperWindow.aArg m x.1 (UpperWindow.base M m n δ x.1)‖ ≤ a := by
    rw [hAm, ← hA0]; exact hVA
  have hDm' : ‖e (etaMobius M x.1) /
      UpperWindow.dArg M n x.1 (UpperWindow.base M m n δ x.1)‖ ≤ a := by
    rw [hDm, ← hD0]; exact hVD
  have hBm' : ‖e x.1 /
      UpperWindow.bArg m p x.1 x.2.2 (UpperWindow.base M m n δ x.1)‖ ≤ a := by
    rw [hBm, ← hB0]; exact hVB
  have hCm' : ‖e (etaMobius M x.1) /
      UpperWindow.cArg M n x.1 x.2.2 (UpperWindow.base M m n δ x.1)‖ ≤ a := by
    rw [hCm, ← hC0]; exact hVC
  have hdir := UpperWindow.lower_direction_im_nonneg (etaDenom M x.1) ψ θ
    hxU.1.2.1 hxU.1.2.2 hc.2.2.1 hθ
  let u := (r : ℂ) * UpperWindow.rotation θ
  have hu : 0 ≤ (-u).im := by
    rw [show -u = (r : ℂ) * (-UpperWindow.rotation θ) by dsimp [u]; ring]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_nonneg hr hdir.1
  have huT : 0 ≤ (-u / etaDenom M x.1).im := by
    rw [show -u / etaDenom M x.1 =
      (r : ℂ) * (-UpperWindow.rotation θ / etaDenom M x.1) by dsimp [u]; ring]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_nonneg hr hdir.2.le
  have he := norm_e_le_one_of_im_nonneg (-u) hu
  have heT := norm_e_le_one_of_im_nonneg (-u / etaDenom M x.1) huT
  have hmul (v t : ℂ) (hv : ‖v‖ ≤ a) (ht : ‖t‖ ≤ 1) : ‖v * t‖ ≤ a := by
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul hv ht (norm_nonneg _) ha0.le
  dsimp only [UpperContour.arcPoint]
  rw [reflected_a_add, reflected_d_add, reflected_b_add, reflected_c_add]
  exact ⟨hmul _ _ hAm' he, hmul _ _ hDm' heT,
    hmul _ _ hBm' he, hmul _ _ hCm' heT⟩


lemma compact_lower_reflected_phi_bounds_all_int (M : SL(2, ℤ)) (h ℓ p n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (K : Set UpperWindow.Parameters) (hK : IsCompact K)
    (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ m : ℤ,
      ∀ r : ℝ, 0 ≤ r → ∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
      ‖modularPhi M (-m) (1 - n) (-z) x.1‖ ≤ C ∧
        ‖(modularPhi M (-m) (1 - n) (-z) x.1)⁻¹‖ ≤ C ∧
        ‖modularPhi M (1 - m - p) (1 - n) (-z - x.2.2) x.1‖ ≤ C ∧
        ‖(modularPhi M (1 - m - p) (1 - n) (-z - x.2.2) x.1)⁻¹‖ ≤ C := by
  obtain ⟨a, ha0, ha1, hargs⟩ := compact_lower_reflected_arguments_all_int M h ℓ p n
    ψ σ ρ δ hc K hK hKU
  obtain ⟨η, R, b, hη, _, _, hb1, hparameters⟩ :=
    UpperWindow.compact_parameter_bounds M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨C, hC, hphi⟩ := compact_modularPhi_bounds_of_arguments M hc.1 a η b ha1 hη hb1
  refine ⟨C, hC, ?_⟩
  intro x hx m r hr θ hθ
  obtain ⟨hτ, _, _, _, _, _, hqη, hqb, hQη, hQb, _, _⟩ := hparameters x hx
  obtain ⟨hA, hD, hB, hE⟩ := hargs x hx m r hr θ hθ
  let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
  have hsingle := hphi (-m) (1 - n) (-z) x.1 (hη.trans_le hτ)
    hqη hqb hQη hQb (by rw [reflected_a_argument]; exact hA)
    (by rw [reflected_d_argument]; exact hD)
  have hratio := hphi (1 - m - p) (1 - n) (-z - x.2.2) x.1 (hη.trans_le hτ)
    hqη hqb hQη hQb (by rw [reflected_b_argument]; exact hB)
    (by rw [reflected_c_argument]; exact hE)
  exact ⟨hsingle.1, hsingle.2, hratio.1, hratio.2⟩

lemma continuous_modularPhi_of_qDenominator_ne_zero
    (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im)
    (hd : modularPhiQDenominator M n z τ ≠ 0) :
    ContinuousAt (fun w => modularPhi M m n w τ) z := by
  have hηim : 0 < (etaMobius M τ).im := by
    rw [← coe_smul_eq_etaMobius M (⟨τ, hτ⟩ : UpperHalfPlane)]
    exact (M • (⟨τ, hτ⟩ : UpperHalfPlane)).im_pos
  have hn : AnalyticAt ℂ (fun w => modularPhiQNumerator m w τ) z := by
    have hpair : AnalyticAt ℂ (fun w : ℂ => ((e τ) ^ m * e w, e τ)) z := by
      unfold e
      fun_prop
    simpa only [modularPhiQNumerator, Function.comp_def] using
      (analyticOnNhd_qPochhammer_joint ((e τ) ^ m * e z, e τ)
        ⟨norm_pos_iff.mpr (e_ne_zero _), norm_e_lt_one ⟨τ, hτ⟩⟩).comp (x := z) hpair
  have hdana : AnalyticAt ℂ (fun w => modularPhiQDenominator M n w τ) z := by
    have hpair : AnalyticAt ℂ (fun w : ℂ =>
        ((e (etaMobius M τ)) ^ n * e (w / etaDenom M τ), e (etaMobius M τ))) z := by
      unfold e
      fun_prop
    simpa only [modularPhiQDenominator, Function.comp_def] using
      (analyticOnNhd_qPochhammer_joint
        ((e (etaMobius M τ)) ^ n * e (z / etaDenom M τ), e (etaMobius M τ))
        ⟨norm_pos_iff.mpr (e_ne_zero _), norm_e_lt_one ⟨_, hηim⟩⟩).comp (x := z) hpair
  have hqcont : ContinuousAt (fun w => modularPhiQProduct M m n w τ) z :=
    (hn.div hdana hd).continuousAt
  have heq : (fun w => modularPhi M m n w τ) =ᶠ[𝓝 z]
      (fun w => modularPhiQProduct M m n w τ) := by
    filter_upwards [hdana.continuousAt.eventually_ne hd] with w hw
    exact modularPhi_eq_qProduct M hM m n w τ hτ hw
  exact hqcont.congr heq.symm


lemma modularPhi_reflection_div (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hL : ContinuousAt (fun w => modularPhi M k n w τ) z)
    (hR : ContinuousAt (fun w => modularPhi M (1 - k) (1 - n) (-w) τ) z) :
    modularPhi M k n z τ = modularReflectionFactor M k n z τ /
      modularPhi M (1 - k) (1 - n) (-z) τ := by
  have hcont : ContinuousAt (fun w => modularReflectionFactor M k n w τ) z := by
    unfold modularReflectionFactor modularReflectionPolynomial modularBernoulliTwo e
    fun_prop
  have heq := ModularCocycleAux.eq_of_germ (hL.mul hR) hcont
    (modularPhi_reflection_germ M hM k n z τ hτ)
  change modularPhi M k n z τ * modularPhi M (1 - k) (1 - n) (-z) τ =
    modularReflectionFactor M k n z τ at heq
  have hF : modularReflectionFactor M k n z τ ≠ 0 := by
    unfold modularReflectionFactor
    exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (etaMultiplier_ne_zero M hM))
      (zpow_ne_zero _ (by norm_num))) (e_ne_zero _)
  have hRne : modularPhi M (1 - k) (1 - n) (-z) τ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at heq
    exact hF heq.symm
  exact (eq_div_iff hRne).mpr heq

lemma lower_reflection_values (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
    modularPhi M (m + 1) n z x.1 = modularReflectionFactor M (m + 1) n z x.1 /
        modularPhi M (-m) (1 - n) (-z) x.1 ∧
      modularPhi M (m + p) n (z + x.2.2) x.1 =
        modularReflectionFactor M (m + p) n (z + x.2.2) x.1 /
        modularPhi M (1 - m - p) (1 - n) (-z - x.2.2) x.1 := by
  let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
  obtain ⟨hτdom, _, _, _, _, _, hQ0, hQ1⟩ := UpperWindow.tauRegion_properties M hc.1
    ψ hc.2.2.1 x.1 hx.1
  have hxsub : ({x} : Set UpperWindow.Parameters) ⊆
      UpperWindow.domain M h ℓ p ψ σ ρ δ := by
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using hx
  obtain ⟨a, _, ha1, hargs⟩ := compact_lower_reflected_arguments_all_int M h ℓ p n
    ψ σ ρ δ hc {x} isCompact_singleton hxsub
  obtain ⟨_, hD, _, hC⟩ := hargs x (Set.mem_singleton x) m r hr θ hθ
  have hd1 : modularPhiQDenominator M (1 - n) (-z) x.1 ≠ 0 := by
    apply qPochhammer_ne_zero_of_norm_lt_one _ _ _ hQ0 hQ1
    rw [reflected_d_argument]
    exact hD.trans_lt ha1
  have hd2 : modularPhiQDenominator M (1 - n) (-z - x.2.2) x.1 ≠ 0 := by
    apply qPochhammer_ne_zero_of_norm_lt_one _ _ _ hQ0 hQ1
    rw [reflected_c_argument]
    exact hC.trans_lt ha1
  have hRc1 := continuous_modularPhi_of_qDenominator_ne_zero M hc.1 (-m) (1 - n)
    (-z) x.1 hx.1.1 hd1
  have hRc2 := continuous_modularPhi_of_qDenominator_ne_zero M hc.1 (1 - m - p) (1 - n)
    (-z - x.2.2) x.1 hx.1.1 hd2
  obtain ⟨hU1, hU2⟩ := UpperWindow.sector_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx
    r θ hr (Or.inr hθ)
  have hL1 : ContinuousAt (fun w => modularPhi M (m + 1) n w x.1) z := by
    have hA := modularPhi_joint_analytic_no_poles M hc.1 (m + 1) n (z, x.1)
      ⟨hU1.1, hU1.2.1⟩
    simpa only [Function.comp_def] using hA.continuousAt.comp (x := z)
      (by fun_prop : ContinuousAt (fun w : ℂ => (w, x.1)) z)
  have hL2 : ContinuousAt (fun w => modularPhi M (m + p) n w x.1) (z + x.2.2) := by
    have hA := modularPhi_joint_analytic_no_poles M hc.1 (m + p) n (z + x.2.2, x.1)
      ⟨hU2.1, hU2.2.1⟩
    simpa only [Function.comp_def] using hA.continuousAt.comp (x := z + x.2.2)
      (by fun_prop : ContinuousAt (fun w : ℂ => (w, x.1)) (z + x.2.2))
  have hR1 : ContinuousAt (fun w => modularPhi M (1 - (m + 1)) (1 - n) (-w) x.1) z := by
    simpa only [show 1 - (m + 1) = -m by ring, Function.comp_def] using
      hRc1.comp (by fun_prop : ContinuousAt (fun w : ℂ => -w) z)
  have hRc2' : ContinuousAt (fun w => modularPhi M (1 - (m + p)) (1 - n) w x.1)
      (-(z + x.2.2)) := by
    simpa only [show 1 - (m + p) = 1 - m - p by ring,
      show -(z + x.2.2) = -z - x.2.2 by ring] using hRc2
  have hR2 : ContinuousAt
      (fun w => modularPhi M (1 - (m + p)) (1 - n) (-w) x.1) (z + x.2.2) :=
    hRc2'.comp (by fun_prop : ContinuousAt (fun w : ℂ => -w) (z + x.2.2))
  constructor
  · simpa only [show 1 - (m + 1) = -m by ring] using
      modularPhi_reflection_div M hc.1 (m + 1) n z x.1 hτdom hL1 hR1
  · simpa only [show 1 - (m + p) = 1 - m - p by ring,
      show -(z + x.2.2) = -z - x.2.2 by ring] using
      modularPhi_reflection_div M hc.1 (m + p) n (z + x.2.2) x.1 hτdom hL2 hR2

lemma single_lower_reflection_raw (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
    UpperContour.kernel .single M m n h ℓ p x z =
      (etaMultiplier M) ^ (-2 : ℤ) * (-1 : ℂ) ^ (m + 1 + n) *
        e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z +
          modularReflectionPolynomial M (m + 1) n z x.1) /
        modularPhi M (-m) (1 - n) (-z) x.1 := by
  obtain ⟨hphi, _⟩ := lower_reflection_values M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ
  dsimp only
  change modularPhi M (m + 1) n _ x.1 * e _ = _
  rw [hphi, modularReflectionFactor, e_add']
  ring

lemma reflection_factor_ratio (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m p n : ℤ) (z y τ E : ℂ) :
    modularReflectionFactor M (m + 1) n z τ /
        modularReflectionFactor M (m + p) n (z + y) τ * e E =
      (-1 : ℂ) ^ (1 - p) *
        e (E + modularReflectionPolynomial M (m + 1) n z τ -
          modularReflectionPolynomial M (m + p) n (z + y) τ) := by
  unfold modularReflectionFactor
  rw [show m + 1 + n = (1 - p) + (m + p + n) by ring,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [show E + modularReflectionPolynomial M (m + 1) n z τ -
      modularReflectionPolynomial M (m + p) n (z + y) τ =
      (E + modularReflectionPolynomial M (m + 1) n z τ) +
        (-modularReflectionPolynomial M (m + p) n (z + y) τ) by ring,
    e_add', e_add', e_neg']
  have hμ := etaMultiplier_ne_zero M hM
  have hs : (-1 : ℂ) ^ (m + p + n) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have he := e_ne_zero (modularReflectionPolynomial M (m + p) n (z + y) τ)
  simp only [zpow_neg, zpow_ofNat]
  field_simp [hμ, hs, he]
  <;> ring

lemma ratio_lower_reflection_raw (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
    UpperContour.kernel .ratio M m n h ℓ p x z =
      (-1 : ℂ) ^ (1 - p) *
        e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z +
          modularReflectionPolynomial M (m + 1) n z x.1 -
          modularReflectionPolynomial M (m + p) n (z + x.2.2) x.1) *
        (modularPhi M (1 - m - p) (1 - n) (-z - x.2.2) x.1 /
          modularPhi M (-m) (1 - n) (-z) x.1) := by
  obtain ⟨hphi1, hphi2⟩ := lower_reflection_values M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ
  dsimp only
  change (modularPhi M (m + 1) n _ x.1 / modularPhi M (m + p) n _ x.1) * e _ = _
  rw [hphi1, hphi2]
  rw [← reflection_factor_ratio M hc.1 m p n]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring


theorem fixed_lower_kernel_exp_bound (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      ‖UpperContour.kernel kind M m n h ℓ p x (UpperContour.arcPoint
        (UpperWindow.base M m n δ x.1) r θ)‖ ≤ C * Real.exp (-k * r) := by
  have hK : IsCompact ({x} : Set UpperWindow.Parameters) := isCompact_singleton
  have hxK : x ∈ ({x} : Set UpperWindow.Parameters) := mem_singleton x
  have hKU : ({x} : Set UpperWindow.Parameters) ⊆
      UpperWindow.domain M h ℓ p ψ σ ρ δ := singleton_subset_iff.mpr hx
  obtain ⟨C₀, hC₀, hphi⟩ := compact_lower_reflected_phi_bounds_all_int M h ℓ p n
    ψ σ ρ δ hc {x} hK hKU
  have hT : etaDenom M x.1 ≠ 0 := by
    intro hz
    have hα : 0 < (etaDenom M x.1).arg := hx.1.2.1
    simp [hz] at hα
  let v := UpperWindow.base M m n δ x.1
  cases kind with
  | ratio =>
    obtain ⟨lam, hlam, hslope⟩ := UpperWindow.compact_arc_linear_margin M h ℓ p
      ψ σ ρ δ hc {x} hK hKU
    let P : ℂ → ℂ := fun z =>
      UpperWindow.phase M m n h ℓ x.1 x.2.1 z +
        modularReflectionPolynomial M (m + 1) n z x.1 -
        modularReflectionPolynomial M (m + p) n (z + x.2.2) x.1
    have hexpand (u : ℂ) : P (v + u) = P v +
        UpperWindow.lowerSlope M h ℓ p x.1 x.2.1 x.2.2 * u := by
      dsimp [P, modularReflectionPolynomial, UpperWindow.phase,
        UpperWindow.lowerSlope, UpperWindow.s, UpperWindow.height]
      push_cast
      field_simp
      ring
    let B : ℝ := max 1 ‖e (P v)‖
    have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨B * C₀ ^ 2, 2 * Real.pi * lam, mul_pos hB (sq_pos_of_pos hC₀),
      by positivity, ?_⟩
    intro r hr θ hθ
    have hp := hphi x hxK m r hr θ hθ
    have he : ‖e (P (UpperContour.arcPoint v r θ))‖ ≤
        B * Real.exp (-2 * Real.pi * lam * r) := by
      rw [UpperContour.arcPoint, hexpand]
      exact (affine_exp_bound _ _ r θ lam hr ((hslope x hxK).2 θ hθ)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
    calc
      _ = ‖e (P (UpperContour.arcPoint v r θ))‖ *
          (‖modularPhi M (1 - m - p) (1 - n)
            (-UpperContour.arcPoint v r θ - x.2.2) x.1‖ *
          ‖(modularPhi M (-m) (1 - n) (-UpperContour.arcPoint v r θ) x.1)⁻¹‖) := by
        rw [ratio_lower_reflection_raw M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ]
        simp [P, v, norm_zpow, div_eq_mul_inv]
      _ ≤ (B * Real.exp (-2 * Real.pi * lam * r)) * (C₀ * C₀) :=
        mul_le_mul he (mul_le_mul hp.2.2.1 hp.2.1 (norm_nonneg _) hC₀.le)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg hB.le (Real.exp_pos _).le)
      _ = _ := by ring
  | single =>
    obtain ⟨a, ha, hquad⟩ := UpperWindow.compact_quadratic_margin M h ℓ p
      ψ σ ρ δ hc {x} hK hKU
    let P : ℂ → ℂ := fun z => UpperWindow.phase M m n h ℓ x.1 x.2.1 z +
      modularReflectionPolynomial M (m + 1) n z x.1
    let L : ℂ := UpperWindow.upperSlope M h ℓ x.1 x.2.1 -
      (M 1 0 : ℂ) * v / etaDenom M x.1 - ((m : ℂ) + 1 / 2) +
      (2 * (n : ℂ) - 1) / (2 * etaDenom M x.1)
    have hexpand (u : ℂ) : P (v + u) = P v + L * u -
        (M 1 0 : ℂ) / (2 * etaDenom M x.1) * u ^ 2 := by
      dsimp [P, L, modularReflectionPolynomial, UpperWindow.phase,
        UpperWindow.upperSlope, UpperWindow.s]
      push_cast
      field_simp
      ring
    let B : ℝ := max 1 ‖e (P v)‖
    let U : ℝ := max 1 ‖(etaMultiplier M) ^ (-2 : ℤ)‖
    let b : ℝ := 2 * Real.pi * ‖L‖
    let D : ℝ := U * B * C₀
    have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hU : 0 < U := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hD : 0 < D := mul_pos (mul_pos hU hB) hC₀
    refine ⟨D * Real.exp ((b + 1) ^ 2 / (4 * a)), 1,
      mul_pos hD (Real.exp_pos _), zero_lt_one, ?_⟩
    intro r hr θ hθ
    have hp := hphi x hxK m r hr θ hθ
    have he : ‖e (P (UpperContour.arcPoint v r θ))‖ ≤
        B * Real.exp (-a * r ^ 2 + b * r) := by
      rw [UpperContour.arcPoint, hexpand]
      have he₀ := single_exp_signed_bound (P v) L (etaDenom M x.1)
        (M 1 0 : ℝ) r θ hT hr
      simp only [Complex.ofReal_intCast] at he₀
      refine he₀.trans (mul_le_mul (le_max_right _ _) ?_ (Real.exp_pos _).le hB.le)
      apply Real.exp_le_exp.mpr
      have hq := mul_le_mul_of_nonneg_right ((hquad x hxK).2 θ hθ) (sq_nonneg r)
      dsimp [b]
      nlinarith
    have hsign : ‖(-1 : ℂ) ^ (m + 1 + n)‖ = 1 := by simp
    have hg : ‖UpperContour.kernel .single M m n h ℓ p x (UpperContour.arcPoint v r θ)‖ ≤
        D * Real.exp (-a * r ^ 2 + b * r) := by
      calc
        _ = ‖(etaMultiplier M) ^ (-2 : ℤ)‖ *
            ‖e (P (UpperContour.arcPoint v r θ))‖ *
            ‖(modularPhi M (-m) (1 - n) (-UpperContour.arcPoint v r θ) x.1)⁻¹‖ := by
          rw [single_lower_reflection_raw M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ]
          simp only [P, v, norm_mul, hsign, mul_one, norm_inv, div_eq_mul_inv]
        _ ≤ U * (B * Real.exp (-a * r ^ 2 + b * r)) * C₀ :=
          mul_le_mul (mul_le_mul (le_max_right _ _) he (norm_nonneg _) hU.le)
            hp.2.1 (norm_nonneg _) (mul_nonneg hU.le (mul_nonneg hB.le (Real.exp_pos _).le))
        _ = _ := by dsimp [D]; ring
    refine hg.trans ?_
    simpa only [neg_one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (gaussian_le_exponential a b r ha) hD.le


end SICLean.L4.UpperContourLowerArcAux
