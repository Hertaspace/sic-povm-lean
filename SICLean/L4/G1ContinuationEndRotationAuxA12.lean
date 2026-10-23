import SICLean.L4.G1ContinuationEndRotationAux

set_option autoImplicit false

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.G1ContinuationEndRotationAuxA12

open UpperContour
open G1ContinuationEndRotationAux

/-- A continuous finite part and an exponential tail give absolute convergence. -/
lemma integrableOn_of_eventual_exp_bound (g : ℝ → ℂ) (C k R₀ : ℝ)
    (hk : 0 < k) (hR₀ : 0 ≤ R₀) (hg : ContinuousOn g (Ici 0))
    (hbound : ∀ R ≥ R₀, ‖g R‖ ≤ C * Real.exp (-k * R)) :
    IntegrableOn g (Ioi 0) := by
  have hnear : IntegrableOn g (Icc 0 R₀) :=
    (hg.mono (fun t ht => ht.1)).integrableOn_Icc
  have htail : IntegrableOn g (Ioi R₀) := by
    refine ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) R₀).const_mul C).mono'
      ((hg.mono (fun t ht => hR₀.trans ht.le)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound t ht.le
  refine (integrableOn_union.mpr ⟨hnear, htail⟩).mono_set ?_
  intro t ht
  by_cases h : t ≤ R₀
  · exact Or.inl ⟨ht.le, h⟩
  · exact Or.inr (lt_of_not_ge h)

/-- Splitting an oriented line preserves the minus sign of its incoming ray. -/
lemma integral_line_split (f : ℂ → ℂ) (v d : ℂ)
    (hf : Integrable (rayPullback f v d)) :
    (∫ t : ℝ, rayPullback f v d t) = rayIntegral f v d - rayIntegral f v (-d) := by
  have hleft : (∫ t : ℝ in Iic 0, rayPullback f v d t) =
      -rayIntegral f v (-d) := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    unfold rayIntegral
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [rayPullback, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hf.integrableOn hf.integrableOn, hleft]
  unfold rayIntegral
  ring

lemma integrable_line_of_rays (f : ℂ → ℂ) (v d : ℂ)
    (hp : IntegrableOn (rayPullback f v d) (Ioi 0))
    (hn : IntegrableOn (rayPullback f v (-d)) (Ioi 0)) :
    Integrable (rayPullback f v d) := by
  have hn0 : IntegrableOn (rayPullback f v (-d)) (Ioi (-(0 : ℝ))) := by
    simpa only [neg_zero] using hn
  have hleft : IntegrableOn (rayPullback f v d) (Iic 0) := by
    apply (integrableOn_Iic_iff_integrableOn_Iio (f := _) (b := (0 : ℝ))).mpr
    have hnneg := hn0.comp_neg_Iio.neg
    change IntegrableOn (fun t : ℝ =>
      -(f (v + ((-t : ℝ) : ℂ) * (-d)) * (-d))) (Iio 0) at hnneg
    change IntegrableOn (fun t : ℝ => f (v + (t : ℂ) * d) * d) (Iio 0)
    simpa only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg] using hnneg
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hleft, hp⟩

/-- A finite polar Cauchy identity followed by the two improper limits. -/
lemma ray_rotation (f : ℂ → ℂ) (v : ℂ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ θ ∈ Icc a b, ∀ t : ℝ, 0 ≤ t →
      DifferentiableAt ℂ f (UpperContour.arcPoint v t θ))
    (ha : IntegrableOn (rayPullback f v (UpperWindow.rotation a)) (Ioi 0))
    (hb : IntegrableOn (rayPullback f v (UpperWindow.rotation b)) (Ioi 0))
    (harc : Tendsto (fun R : ℝ => arcIntegral f v R a b) atTop (𝓝 0)) :
    rayIntegral f v (UpperWindow.rotation a) =
      rayIntegral f v (UpperWindow.rotation b) := by
  have hlim := ((UpperContourUpperArcAux.rayFinite_tendsto f v _ ha).add harc).sub
    (UpperContourUpperArcAux.rayFinite_tendsto f v _ hb)
  have hzero : Tendsto (fun R : ℝ => rayFinite f v (UpperWindow.rotation a) R +
      arcIntegral f v R a b - rayFinite f v (UpperWindow.rotation b) R)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (UpperContourLowerArcAux.finite_rotation_of_differentiable f v R a b hR hab
      (fun θ hθ t ht => hf θ hθ t ht.1)).symm
  simpa only [add_zero, sub_eq_zero] using tendsto_nhds_unique hlim hzero

/-- Moving the origin of a vertical line is a real translation of its parameter. -/
lemma vertical_integral_eq (f : ℂ → ℂ) (v : ℂ) :
    (∫ t : ℝ, g1VerticalPullback f v.re t) =
      ∫ t : ℝ, rayPullback f v Complex.I t := by
  have heq (t : ℝ) : rayPullback f v Complex.I t =
      g1VerticalPullback f v.re (t + v.im) := by
    dsimp [rayPullback, g1VerticalPullback, g1VerticalPoint]
    congr 2
    apply Complex.ext <;> simp <;> ring
  simp_rw [heq]
  exact (integral_add_right_eq_self (g1VerticalPullback f v.re) v.im).symm

lemma vertical_integral_eq_lineIntegral (f : ℂ → ℂ) (v : ℂ) (ψ : ℝ)
    (hv : Integrable (rayPullback f v Complex.I))
    (ht : Integrable (linePullback f v ψ))
    (hp : rayIntegral f v Complex.I =
      rayIntegral f v (Complex.I * UpperWindow.rotation ψ))
    (hn : rayIntegral f v (-Complex.I) =
      rayIntegral f v (-(Complex.I * UpperWindow.rotation ψ))) :
    (∫ t : ℝ, g1VerticalPullback f v.re t) = lineIntegral f v ψ := by
  rw [vertical_integral_eq, integral_line_split f v Complex.I hv, hp, hn]
  exact (integral_line_split f v (Complex.I * UpperWindow.rotation ψ) ht).symm

lemma norm_e_affine_ray (A B v d : ℂ) (R : ℝ) :
    ‖e (A * (v + (R : ℂ) * d) + B)‖ =
      ‖e (A * v + B)‖ * Real.exp (-(2 * Real.pi * (A * d).im) * R) := by
  rw [G1BilateralRatioTailsAux.norm_e, G1BilateralRatioTailsAux.norm_e, ← Real.exp_add]
  congr 1
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma upper_vertical_exp_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n h ell p : ℤ)
    (τ w y v : ℂ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ)
    (hs : 0 < (G1RatioTail.complexS M τ w h ell / etaDenom M τ).re) :
    ∃ C κ R₀ : ℝ, 0 < κ ∧ 0 < R₀ ∧ ∀ R ≥ R₀,
      ‖UpperWindow.ratioKernel M m n h ell p τ w y (v + (R : ℂ) * Complex.I)‖ ≤
        C * Real.exp (-κ * R) := by
  let S := G1RatioTail.complexS M τ w h ell / etaDenom M τ
  let B := ‖e (S * v + g1Exponent M τ w 0 n h ell m)‖
  let F : Finset (ℤ × ℤ) := {(m + 1, n), (m + p, n)}
  have hT := (UpperWindow.tauRegion_properties M hM ψ hψ' τ hτ).2.2.2.1
  obtain ⟨D, k, R₀, hD, hk, hR₀, hb⟩ :=
    G1ContinuationEndRotationAux.upper_arc_estimates M hM ψ (‖v‖ + ‖y‖) hψ hψ'
      {τ} isCompact_singleton (by simpa only [singleton_subset_iff] using hτ) F
  refine ⟨D * D * B, 2 * Real.pi * S.re, R₀, by dsimp [S]; positivity, hR₀, ?_⟩
  intro R hR
  have hv : v ∈ Metric.closedBall (0 : ℂ) (‖v‖ + ‖y‖) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hvy : v + y ∈ Metric.closedBall (0 : ℂ) (‖v‖ + ‖y‖) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using norm_add_le v y
  have hrot : UpperWindow.rotation (Real.pi / 2) = Complex.I := by
    unfold UpperWindow.rotation
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_div]
  have hθ : Real.pi / 2 ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ) :=
    ⟨le_rfl, by linarith⟩
  have hn := (hb τ (mem_singleton τ) (m + 1, n) (by simp [F]) v hv R hR
    (Real.pi / 2) hθ).2.2.1
  have hd := (hb τ (mem_singleton τ) (m + p, n) (by simp [F]) (v + y) hvy R hR
    (Real.pi / 2) hθ).2.2.2
  simp only [hrot] at hn hd
  have hd' : ‖(modularPhi M (m + p) n (v + (R : ℂ) * Complex.I + y) τ)⁻¹‖ ≤ D := by
    simpa only [add_right_comm] using hd
  have hp : ‖e (g1Exponent M τ w (v + (R : ℂ) * Complex.I) n h ell m)‖ =
      B * Real.exp (-(2 * Real.pi * S.re) * R) := by
    rw [G1RatioTail.exponent_affine M τ w _ n h ell m hT]
    change ‖e (S * (v + (R : ℂ) * Complex.I) + g1Exponent M τ w 0 n h ell m)‖ = _
    simpa only [B, Complex.mul_I_im] using
      norm_e_affine_ray S (g1Exponent M τ w 0 n h ell m) v Complex.I R
  change ‖(modularPhi M (m + 1) n (v + (R : ℂ) * Complex.I) τ /
    modularPhi M (m + p) n (v + (R : ℂ) * Complex.I + y) τ) *
    e (g1Exponent M τ w (v + (R : ℂ) * Complex.I) n h ell m)‖ ≤ _
  rw [div_eq_mul_inv, norm_mul, norm_mul, hp]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul hn hd' (norm_nonneg _) hD.le)
    (by positivity)).trans_eq (by ring)

/-- The seed's northwest and southeast quadrants exclude precisely the two divisor families relevant
to the ratio. Poles of its denominator are allowed. -/
lemma seed_ratio_analyticAt_quadrant (M : SL(2, ℤ)) (h ell p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (x : UpperWindow.Parameters) (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ)
    (z : ℂ)
    (hz : let v := UpperWindow.base M m n δ x.1
      (z.re ≤ v.re ∧ v.im ≤ z.im) ∨ (v.re ≤ z.re ∧ z.im ≤ v.im)) :
    AnalyticAt ℂ (UpperWindow.ratioKernel M m n h ell p x.1 x.2.1 x.2.2) z := by
  have hτ : x.1 ∈ modularPhiDomain M :=
    (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).1
  have hnp : modularPhiPoleMultiplicity M (m + 1) n z x.1 = 0 := by
    have hempty : modularPhiPoleIndices M (m + 1) n z x.1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨K, J⟩ ⟨_, heq⟩
      have hq := seed_pole_quadrants M h ell p m n ψ σ ρ δ hc x hx K J
      rcases hz with hzu | hzl
      · exact (not_le_of_gt hq.1) (by simpa [heq] using hzu.1)
      · exact (not_le_of_gt hq.2.1) (by simpa [heq] using hzl.2)
    simp [modularPhiPoleMultiplicity, hempty]
  have hnz : modularPhiZeroMultiplicity M (m + p) n (z + x.2.2) x.1 = 0 := by
    have hempty : modularPhiZeroIndices M (m + p) n (z + x.2.2) x.1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨K, J⟩ ⟨_, heq⟩
      have heq' : z = modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2 := by
        rw [← heq]
        ring
      have hq := seed_pole_quadrants M h ell p m n ψ σ ρ δ hc x hx K J
      rcases hz with hzu | hzl
      · exact (not_le_of_gt hq.2.2.2) (by simpa [heq'] using hzu.2)
      · exact (not_le_of_gt hq.2.2.1) (by simpa [heq'] using hzl.1)
    simp [modularPhiZeroMultiplicity, hempty]
  have ha : AnalyticAt ℂ (fun w : ℂ => modularPhi M (m + 1) n w x.1) z := by
    simpa only [Function.comp_def] using
      (modularPhi_joint_analytic_no_poles M hc.1 (m + 1) n (z, x.1) ⟨hτ, hnp⟩).comp
        (x := z) (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (w, x.1)) z)
  have hb : AnalyticAt ℂ
      (fun w : ℂ => (modularPhi M (m + p) n (w + x.2.2) x.1)⁻¹) z := by
    simpa only [Function.comp_def] using
      (UpperContourGeometryAux.reciprocal_analyticAt M hc.1 (m + p) n
        (z + x.2.2, x.1) hτ hnz).comp (x := z)
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (w + x.2.2, x.1)) z)
  have he : AnalyticAt ℂ
      (fun w : ℂ => e (UpperWindow.phase M m n h ell x.1 x.2.1 w)) z := by
    unfold UpperWindow.phase e
    fun_prop
  change AnalyticAt ℂ (fun w : ℂ =>
    (modularPhi M (m + 1) n w x.1 / modularPhi M (m + p) n (w + x.2.2) x.1) *
      e (UpperWindow.phase M m n h ell x.1 x.2.1 w)) z
  simp only [div_eq_mul_inv]
  exact (ha.mul hb).mul he

lemma seed_ratio_upper_sector_analyticAt (M : SL(2, ℤ)) (h ell p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (x : UpperWindow.Parameters) (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ)
    (r θ : ℝ) (hr : 0 ≤ r) (hθ : θ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ)) :
    AnalyticAt ℂ (UpperWindow.ratioKernel M m n h ell p x.1 x.2.1 x.2.2)
      (UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ) := by
  apply seed_ratio_analyticAt_quadrant M h ell p m n ψ σ ρ δ hc x hx
  apply Or.inl
  have hcos : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1
      (by linarith [hθ.2, hc.2.2.1, Real.pi_pos])
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2, hc.2.2.1, Real.pi_pos])
  simp only [UpperContour.arcPoint, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero, rotation_re, rotation_im]
  constructor
  · linarith [mul_nonpos_of_nonneg_of_nonpos hr hcos]
  · linarith [mul_nonneg hr hsin]

lemma seed_ratio_lower_sector_analyticAt (M : SL(2, ℤ)) (h ell p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (x : UpperWindow.Parameters) (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ)
    (r θ : ℝ) (hr : 0 ≤ r) (hθ : θ ∈ Icc (-Real.pi / 2) (-Real.pi / 2 + ψ)) :
    AnalyticAt ℂ (UpperWindow.ratioKernel M m n h ell p x.1 x.2.1 x.2.2)
      (UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ) := by
  apply seed_ratio_analyticAt_quadrant M h ell p m n ψ σ ρ δ hc x hx
  apply Or.inr
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [hθ.1]) (by linarith [hθ.2, hc.2.2.1, Real.pi_pos])
  have hsin : Real.sin θ ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le
    (by linarith [hθ.2, hc.2.2.1, Real.pi_pos]) (by linarith [hθ.1, Real.pi_pos])
  simp only [UpperContour.arcPoint, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero, rotation_re, rotation_im]
  constructor
  · linarith [mul_nonneg hr hcos]
  · linarith [mul_nonpos_of_nonneg_of_nonpos hr hsin]

end SICLean.L4.G1ContinuationEndRotationAuxA12
