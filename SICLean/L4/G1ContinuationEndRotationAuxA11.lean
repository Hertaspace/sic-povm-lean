import SICLean.L4.G1ContinuationEndRotationAux

set_option autoImplicit false

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1ContinuationEndRotationAuxA11

open UpperContour

/-- The finite boundary identity for two parallel rays and their connectors. The two complex
directions may be linearly dependent. -/
theorem finite_parallel_ray_ledger (f : ℂ → ℂ) (a b d : ℂ) (R : ℝ)
    (hR : 0 ≤ R)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 R,
      DifferentiableAt ℂ f (a + (s : ℂ) * (b - a) + (t : ℂ) * d)) :
    rayFinite f a d R + rayFinite f (a + (R : ℂ) * d) (b - a) 1 =
      rayFinite f a (b - a) 1 + rayFinite f b d R := by
  let L : ℝ × ℝ →L[ℝ] ℂ :=
    (b - a) • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
      d • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hL (p : ℝ × ℝ) : L p = (p.1 : ℂ) * (b - a) + (p.2 : ℂ) * d := by
    simp [L, mul_comm]
  let H : ℝ × ℝ → ℂ := fun p => a + L p
  have hH (p : ℝ × ℝ) : H p = a + (p.1 : ℂ) * (b - a) + (p.2 : ℂ) * d := by
    simp [H, hL, add_assoc]
  let F : ℝ × ℝ → ℂ := fun p => f (H p)
  let F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => deriv f (H p) • L
  have hFderiv (p : ℝ × ℝ) (hp : p ∈ Icc (0, 0) (1, R)) :
      HasFDerivAt F (F' p) p := by
    have hd := (hf p.1 ⟨hp.1.1, hp.2.1⟩ p.2 ⟨hp.1.2, hp.2.2⟩)
    rw [← hH p] at hd
    exact hd.hasDerivAt.comp_hasFDerivAt p (L.hasFDerivAt.const_add a)
  have hFc : ContinuousOn F (Icc (0, 0) (1, R)) :=
    fun p hp => (hFderiv p hp).continuousAt.continuousWithinAt
  have hinner (p : ℝ × ℝ) (hp : p ∈ Ioo 0 1 ×ˢ Ioo 0 R) :
      p ∈ Icc (0, 0) (1, R) :=
    ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩
  have hzero (p : ℝ × ℝ) :
      (d • F' p) (1, 0) + (-((b - a) • F' p)) (0, 1) = 0 := by
    simp [F', hL, smul_eq_mul]
    ring
  have hgreen := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fun p => d • F p) (fun p => -((b - a) • F p))
    (fun p => d • F' p) (fun p => -((b - a) • F' p))
    (0, 0) (1, R) ⟨by norm_num, hR⟩
    (hFc.const_smul d) (hFc.const_smul (b - a)).neg
    (fun p hp => (hFderiv p (hinner p hp)).const_smul d)
    (fun p hp => ((hFderiv p (hinner p hp)).const_smul (b - a)).neg)
    (by simp_rw [hzero]; exact integrableOn_zero)
  simp only [hzero, integral_zero, F, hH, smul_eq_mul, ofReal_zero, ofReal_one,
    zero_mul, one_mul, add_zero, intervalIntegral.integral_neg] at hgreen
  have htop : (∫ s : ℝ in 0..1,
      (b - a) * f (a + (s : ℂ) * (b - a) + (R : ℂ) * d)) =
      rayFinite f (a + (R : ℂ) * d) (b - a) 1 := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [rayPullback]
    rw [mul_comm (b - a)]
    congr 2
    ring
  have hbottom : (∫ s : ℝ in 0..1, (b - a) * f (a + (s : ℂ) * (b - a))) =
      rayFinite f a (b - a) 1 := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact mul_comm _ _
  have hright : (∫ t : ℝ in 0..R, d * f (a + (b - a) + (t : ℂ) * d)) =
      rayFinite f b d R := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [rayPullback]
    rw [show a + (b - a) = b by ring, mul_comm]
  have hleft : (∫ t : ℝ in 0..R, d * f (a + (t : ℂ) * d)) =
      rayFinite f a d R := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact mul_comm _ _
  rw [htop, hbottom, hright, hleft] at hgreen
  linear_combination hgreen

/-- A uniform bound for the values of the kernel controls the translated connector, including its
tangent factor. -/
theorem norm_translated_connector_le (f : ℂ → ℂ) (a b d : ℂ) (R B : ℝ)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖f (a + (R : ℂ) * d + (s : ℂ) * (b - a))‖ ≤ B) :
    ‖rayFinite f (a + (R : ℂ) * d) (b - a) 1‖ ≤ B * ‖b - a‖ := by
  calc
    ‖rayFinite f (a + (R : ℂ) * d) (b - a) 1‖ ≤ (B * ‖b - a‖) * |1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      rw [rayPullback, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hf s ⟨hs.1.le, hs.2⟩) (norm_nonneg _)
    _ = B * ‖b - a‖ := by norm_num

theorem connector_tendsto_zero_of_uniform_bound (f : ℂ → ℂ) (a b d : ℂ)
    (B : ℝ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hf : ∀ᶠ R : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖f (a + (R : ℂ) * d + (s : ℂ) * (b - a))‖ ≤ B R) :
    Tendsto (fun R : ℝ => rayFinite f (a + (R : ℂ) * d) (b - a) 1)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun R => B R * ‖b - a‖) ?_
    (by simpa using hB.mul_const ‖b - a‖)
  filter_upwards [hf] with R hR
  exact norm_translated_connector_le f a b d R (B R) hR

/-- Translation of an integrable ray through a holomorphic half strip. The only limiting boundary
term is the explicit translated connector. -/
theorem parallel_ray_integral_eq (f : ℂ → ℂ) (a b d : ℂ)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t →
      DifferentiableAt ℂ f (a + (s : ℂ) * (b - a) + (t : ℂ) * d))
    (ha : IntegrableOn (rayPullback f a d) (Ioi 0))
    (hb : IntegrableOn (rayPullback f b d) (Ioi 0))
    (hconnector : Tendsto
      (fun R : ℝ => rayFinite f (a + (R : ℂ) * d) (b - a) 1) atTop (𝓝 0)) :
    rayIntegral f a d = rayFinite f a (b - a) 1 + rayIntegral f b d := by
  have ha' := UpperContourUpperArcAux.rayFinite_tendsto f a d ha
  have hb' := UpperContourUpperArcAux.rayFinite_tendsto f b d hb
  have heq : (fun R : ℝ => rayFinite f a d R +
      rayFinite f (a + (R : ℂ) * d) (b - a) 1) =ᶠ[atTop]
      (fun R : ℝ => rayFinite f a (b - a) 1 + rayFinite f b d R) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact finite_parallel_ray_ledger f a b d R hR
      (fun s hs t ht => hf s hs t ht.1)
  have hlim := tendsto_nhds_unique ((ha'.add hconnector).congr' heq) (hb'.const_add _)
  simpa only [add_zero] using hlim

/-- Continuity handles the bounded initial interval; an eventual exponential bound handles the
entire remaining ray. -/
theorem integrableOn_Ioi_of_eventual_exp_bound (f : ℝ → ℂ) (C k : ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ))) (hk : 0 < k)
    (hbound : ∃ R₀ : ℝ, ∀ r ≥ R₀, ‖f r‖ ≤ C * Real.exp (-k * r)) :
    IntegrableOn f (Ioi 0) := by
  obtain ⟨R₀, hbound⟩ := hbound
  let R : ℝ := max 0 R₀
  have hR : 0 ≤ R := le_max_left _ _
  have hhead : IntegrableOn f (Icc 0 R) :=
    (hf.mono (fun r hr => hr.1)).integrableOn_Icc
  have hcont : ContinuousOn f (Ioi R) :=
    hf.mono (fun r hr => hR.trans hr.le)
  have hmajor : IntegrableOn (fun r : ℝ => C * Real.exp (-k * r)) (Ioi R) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) R).const_mul C
  have htail : IntegrableOn f (Ioi R) := by
    refine hmajor.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hbound r ((le_max_right 0 R₀).trans hr.le)
  apply (integrableOn_union.mpr ⟨hhead, htail⟩).mono_set
  intro r hr
  by_cases hrR : r ≤ R
  · exact Or.inl ⟨hr.le, hrR⟩
  · exact Or.inr (lt_of_not_ge hrR)

/-- Translation of a real half-line, with no integrability assumption. -/
theorem integral_Ici_add_right (g : ℝ → ℂ) (u v : ℝ) :
    (∫ t : ℝ in Ici u, g (t + v)) = ∫ t : ℝ in Ici (u + v), g t := by
  have A : MeasurableEmbedding (fun t : ℝ => t + v) :=
    (Homeomorph.addRight v).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := (volume : Measure ℝ)) g (Ici (u + v))
  rw [map_add_right_eq_self] at h
  have hpre : (fun t : ℝ => t + v) ⁻¹' Ici (u + v) = Ici u := by
    ext t
    simp only [mem_preimage, mem_Ici, add_le_add_iff_right]
  rw [hpre] at h
  exact h.symm

/-- The fixed bend is the common origin of the outgoing lower and upper rays. -/
theorem bentIntegral_eq_rays (f : ℂ → ℂ) (x ψ : ℝ) :
    g1BentIntegral f x ψ =
      -rayIntegral f ((x : ℂ) - I) (g1LowerDirection ψ) +
        rayIntegral f ((x : ℂ) - I) I := by
  have hlower : (∫ r : ℝ in Ici 0, g1BentLowerPullback f x ψ r) =
      rayIntegral f ((x : ℂ) - I) (g1LowerDirection ψ) := by
    rw [integral_Ici_eq_integral_Ioi]
    rfl
  have hupper : (∫ t : ℝ in Ici (-1), g1VerticalPullback f x t) =
      rayIntegral f ((x : ℂ) - I) I := by
    rw [← show (0 : ℝ) + -1 = -1 by norm_num,
      ← integral_Ici_add_right (g1VerticalPullback f x) 0 (-1),
      integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [g1VerticalPullback, g1VerticalPoint, rayPullback]
    push_cast
    congr 2
    ring
  exact congrArg₂ (fun l u : ℂ => -l + u) hlower hupper

/-- Splitting and reversing the negative half of an integrable tilted line. -/
theorem lineIntegral_eq_rays (f : ℂ → ℂ) (v : ℂ) (ψ : ℝ)
    (hf : Integrable (linePullback f v ψ)) :
    lineIntegral f v ψ = -rayIntegral f v (g1LowerDirection ψ) +
      rayIntegral f v (I * UpperWindow.rotation ψ) := by
  have hdir : g1LowerDirection ψ = -(I * UpperWindow.rotation ψ) := by
    have h := (G1ContinuationEndRotationAux.reflected_lower_direction ψ).trans
      (G1ContinuationEndRotationAux.rotation_quarter ψ)
    exact neg_eq_iff_eq_neg.mp h
  have hneg (t : ℝ) : linePullback f v ψ (-t) =
      -rayPullback f v (g1LowerDirection ψ) t := by
    simp [linePullback, rayPullback, hdir, mul_neg, neg_mul]
  have hleft : (∫ t : ℝ in Iic 0, linePullback f v ψ t) =
      -rayIntegral f v (g1LowerDirection ψ) := by
    calc
      _ = ∫ t : ℝ in Ioi 0, linePullback f v ψ (-t) := by
        simpa using (integral_comp_neg_Ioi 0 (linePullback f v ψ)).symm
      _ = -rayIntegral f v (g1LowerDirection ψ) := by
        simp_rw [hneg]
        rw [integral_neg]
        rfl
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hf.integrableOn hf.integrableOn
  change (∫ t : ℝ, linePullback f v ψ t) = _
  rw [← hsplit, hleft]
  rfl

end SICLean.L4.G1ContinuationEndRotationAuxA11
