import SICLean.L4.FaddeevHolomorphic
import SICLean.L4.ModularClusterIntegralsAux
import SICLean.L4.G1ContinuationCircles
import SICLean.L4.G1BilateralSingleTails
import SICLean.L4.G1BilateralRatioTails

/-!
# Auxiliary proofs for moving G1 integral charts

Compact parameter bounds are assembled directly from the uniform Faddeev sector estimate, with an
explicit angular buffer for bounded affine offsets. The parameter-integral lemmas use Cauchy
derivative bounds and a common integrable majorant. The finite-label bent-graph criterion supplies
open charts and actual contour regularity, including reciprocal zeros.
-/

set_option autoImplicit false

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1ContinuationHolomorphyAux
open G1Continuation

lemma extension_regular (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y z : ℂ) (n h ell p m : ℤ) (D : CircleExtension)
    (hτ : τ ∈ modularPhiDomain M) (hD : SeparatesExtension D M τ y n p m)
    (hz : z.re = D.base.crossing ∨
      (∃ r ∈ D.base.centers, dist z (r : ℂ) = D.base.radius r) ∨
      (∃ a ∈ D.extra.centers, dist z a = D.extra.radius a)) :
    (z, τ) ∈ ModularCluster.regularDomain M (G1Pinch.ratioData w y n h ell p m) := by
  apply (ModularCluster.regularDomain_iff_no_labels M hM _ z τ).mpr
  refine ⟨hτ, ?_⟩
  intro b hb he
  have hb' : b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p m) := by
    simpa only [ModularCluster.labels, G1Pinch.ratioData] using hb
  have he' : z = ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p m) τ b := by
    simpa only [ModularCluster.branchPoint, G1Pinch.ratioData] using he
  have hav := (hD.2.2 b hb').1
  rw [← he'] at hav
  rcases hz with hz | ⟨r, hr, hz⟩ | ⟨a, ha, hz⟩
  · exact hav.1 hz
  · exact hav.2.1 r hr hz
  · exact hav.2.2 a ha hz

lemma extension_vertical_regular (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n h ell p m : ℤ) (D : CircleExtension)
    (hτ : τ ∈ modularPhiDomain M) (hD : SeparatesExtension D M τ y n p m) (t : ℝ) :
    (g1VerticalPoint D.base.crossing t, τ) ∈
      ModularCluster.regularDomain M (G1Pinch.ratioData w y n h ell p m) := by
  apply extension_regular M hM τ w y _ n h ell p m D hτ hD
  exact Or.inl (by simp [g1VerticalPoint])

lemma extension_base_circle_regular (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n h ell p m : ℤ) (D : CircleExtension)
    (hτ : τ ∈ modularPhiDomain M) (hD : SeparatesExtension D M τ y n p m)
    (r : ℝ) (hr : r ∈ D.base.centers) (θ : ℝ) :
    (circleMap (r : ℂ) (D.base.radius r) θ, τ) ∈
      ModularCluster.regularDomain M (G1Pinch.ratioData w y n h ell p m) := by
  apply extension_regular M hM τ w y _ n h ell p m D hτ hD
  exact Or.inr (Or.inl ⟨r, hr, circleMap_mem_sphere _ (hD.1 r hr).le θ⟩)

lemma extension_extra_circle_regular (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n h ell p m : ℤ) (D : CircleExtension)
    (hτ : τ ∈ modularPhiDomain M) (hD : SeparatesExtension D M τ y n p m)
    (a : ℂ) (ha : a ∈ D.extra.centers) (θ : ℝ) :
    (circleMap a (D.extra.radius a) θ, τ) ∈
      ModularCluster.regularDomain M (G1Pinch.ratioData w y n h ell p m) := by
  apply extension_regular M hM τ w y _ n h ell p m D hτ hD
  exact Or.inr (Or.inr ⟨a, ha, circleMap_mem_sphere _ (hD.2.1 a ha).le θ⟩)

theorem analyticAt_exp_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : SL(2, ℤ)) (m n h ell : ℤ) {z τ w : E → ℂ} {x : E}
    (hz : AnalyticAt ℂ z x) (hτ : AnalyticAt ℂ τ x)
    (hw : AnalyticAt ℂ w x) (hdom : τ x ∈ modularPhiDomain M) :
    AnalyticAt ℂ (fun q => e (UpperWindow.phase M m n h ell (τ q) (w q) (z q))) x := by
  have hne : etaDenom M (τ x) ≠ 0 := etaDenom_ne_zero_of_mem M hdom
  have hden : AnalyticAt ℂ (fun q => etaDenom M (τ q)) x := by
    unfold etaDenom
    exact (analyticAt_const.mul hτ).add analyticAt_const
  have hmob : AnalyticAt ℂ (fun q => etaMobius M (τ q)) x := by
    unfold etaMobius
    exact ((analyticAt_const.mul hτ).add analyticAt_const).div hden hne
  have hphase : AnalyticAt ℂ
      (fun q => UpperWindow.phase M m n h ell (τ q) (w q) (z q)) x := by
    dsimp only [UpperWindow.phase]
    exact ((((((analyticAt_const.mul hz).sub analyticAt_const).add
      (hden.mul analyticAt_const)).mul hw).div hden hne).add
      (analyticAt_const.mul (hz.add (analyticAt_const.mul hτ)))).add
        (analyticAt_const.mul ((hz.div hden hne).add (analyticAt_const.mul hmob)))
  unfold e
  fun_prop

lemma finite_path_compact_bound {E ι : Type*} [TopologicalSpace E] [Fintype ι]
    (K : Set E) (hK : IsCompact K) (a b : ℝ) (f : ι → E → ℝ → ℂ)
    (hf : ∀ i, ContinuousOn (fun q : E × ℝ => f i q.1 q.2) (K ×ˢ Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i v, v ∈ K → ∀ t ∈ Icc a b, ‖f i v t‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := G1BilateralRatioTailsAux.finite_compact_bound Finset.univ
    (K ×ˢ Icc a b) (hK.prod isCompact_Icc)
    (fun i q => f i q.1 q.2) (fun i _ => hf i)
  exact ⟨C, hC, fun i v hv t ht => hb i (Finset.mem_univ _) (v, t) ⟨hv, ht⟩⟩

lemma ratio_path_continuous (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n h ell p m : ℤ) (z j : ℝ → ℂ)
    (hz : Continuous z) (hj : Continuous j)
    (hr : ∀ t, (z t, τ) ∈ ModularCluster.regularDomain M
      (G1Pinch.ratioData w y n h ell p m)) :
    Continuous (fun t => G1RatioTail.complexKernel M τ w y n h ell p m (z t) * j t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ((G1BilateralRatioTailsAux.kernel_analytic M hM w y n h ell p m
    (hr t)).continuousAt.comp
    (f := fun t : ℝ => (z t, τ)) (hz.continuousAt.prodMk continuousAt_const)).mul
      hj.continuousAt

lemma extensionTruncated_tendsto (D : CircleExtension) (f : ℂ → ℂ)
    (hi : ExtensionIntegrable D f) :
    Tendsto (extensionTruncated D f) atTop (𝓝 (extensionIntegral D f)) := by
  exact (G1ChainTransfer.truncated_tendsto D.base f hi.1).add_const _

lemma connectors_tendsto_of_tail (f : ℂ → ℂ) (a b C κ R₀ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x ∈ Icc (min a b) (max a b), ∀ t : ℝ, R₀ ≤ |t| →
      ‖f (g1VerticalPoint x t)‖ ≤ C * Real.exp (-κ * |t|)) :
    Tendsto (G1FiniteLedger.connectors f a b) atTop (𝓝 0) := by
  have hbound (t : ℝ) (ht : R₀ ≤ |t|) :
      ‖G1RatioTail.horizontalIntegral f a b t‖ ≤
        |b - a| * C * Real.exp (-κ * |t|) := by
    calc
      _ ≤ (C * Real.exp (-κ * |t|)) * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun x hx => hb x ⟨hx.1.le, hx.2⟩ t ht)
      _ = _ := by ring
  have hlim : Tendsto (fun R : ℝ => |b - a| * C * Real.exp (-κ * R)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hκ))).const_mul (|b - a| * C)
  have hp : Tendsto (fun R : ℝ => G1RatioTail.horizontalIntegral f a b R) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (max R₀ 0)] with R hR
    have hR₀' : R₀ ≤ R := (le_max_left _ _).trans hR
    have hR' : 0 ≤ R := (le_max_right _ _).trans hR
    simpa only [abs_of_nonneg hR'] using hbound R (by simpa [abs_of_nonneg hR'] using hR₀')
  have hn : Tendsto (fun R : ℝ => G1RatioTail.horizontalIntegral f a b (-R)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (max R₀ 0)] with R hR
    have hR₀' : R₀ ≤ R := (le_max_left _ _).trans hR
    have hR' : 0 ≤ R := (le_max_right _ _).trans hR
    simpa only [abs_neg, abs_of_nonneg hR'] using
      hbound (-R) (by simpa [abs_neg, abs_of_nonneg hR'] using hR₀')
  change Tendsto (fun R : ℝ => G1RatioTail.horizontalIntegral f a b (-R) -
    G1RatioTail.horizontalIntegral f a b R) atTop (𝓝 0)
  convert hn.sub hp using 1 <;> simp only [sub_self]



lemma integral_differentiableOn_of_domination
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {μ : Measure ℝ} {F : E → ℝ → ℂ} {U : Set E} {B : ℝ → ℝ}
    (hU : IsOpen U)
    (hm : ∀ q ∈ U, AEStronglyMeasurable (F q) μ)
    (hdm : ∀ q ∈ U,
      AEStronglyMeasurable (fun t => fderiv ℂ (fun v => F v t) q) μ)
    (hh : ∀ᵐ t ∂μ, AnalyticOnNhd ℂ (fun q => F q t) U)
    (hB : ∀ᵐ t ∂μ, ∀ q ∈ U, ‖F q t‖ ≤ B t)
    (hBi : Integrable B μ) :
    DifferentiableOn ℂ (fun q => ∫ t, F q t ∂μ) U := by
  intro q hq
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hq)
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsub' : Metric.ball q (2 * r) ⊆ U := by
    simpa only [r, mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using hsub
  have hint : Integrable (F q) μ :=
    hBi.mono' (hm q hq) (hB.mono fun t ht => ht q hq)
  have hmeas : ∀ᶠ v in 𝓝 q, AEStronglyMeasurable (F v) μ := by
    filter_upwards [hU.mem_nhds hq] with v hv
    exact hm v hv
  have hbound : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball q r,
      ‖fderiv ℂ (fun u => F u t) v‖ ≤ (2 * B t) / r := by
    filter_upwards [hh, hB] with t ht htB v hv
    exact joint_norm_fderiv_le_of_ball_bound hr hv
      (ht.differentiableOn.mono hsub') (fun u hu => htB u (hsub' hu))
  have hdiff : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball q r,
      HasFDerivAt (fun u => F u t) (fderiv ℂ (fun u => F u t) v) v := by
    filter_upwards [hh] with t ht v hv
    exact (ht v (hsub' (Metric.ball_subset_ball (by linarith) hv))).differentiableAt.hasFDerivAt
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds q hr) hmeas hint (hdm q hq) hbound
    ((hBi.const_mul 2).div_const r) hdiff).differentiableAt.differentiableWithinAt

lemma continuousOn_parameter_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : ℂ × E → ℂ} {z j : ℝ → ℂ} {u : E} {S : Set ℝ}
    (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ t ∈ S, AnalyticAt ℂ K (z t, u)) :
    ContinuousOn (fun t => fderiv ℂ (fun q => K (z t, q) * j t) u) S := by
  intro t ht
  have hcont : ContinuousAt
      (fun t => fderiv ℂ (fun q => K (z t, q)) u) t := by
    have hc : ContDiffAt ℂ 1 K (z t, u) := (hK t ht).contDiffAt
    have hc' : ContinuousAt
        (fun v : ℂ => fderiv ℂ (fun q => K (v, q)) u) (z t) :=
      (hc.fderiv
        (contDiffAt_const : ContDiffAt ℂ 0 (fun _ : ℂ => u) (z t))
        (by norm_num)).continuousAt
    exact hc'.comp hz.continuousAt
  have heq : (fun t => fderiv ℂ (fun q => K (z t, q) * j t) u) =ᶠ[𝓝[S] t]
      (fun t => j t • fderiv ℂ (fun q => K (z t, q)) u) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hdiff : DifferentiableAt ℂ (fun q : E => K (z v, q)) u :=
      ((hK v hv).comp (analyticAt_const.prod analyticAt_id)).differentiableAt
    exact fderiv_mul_const hdiff (j v)
  exact (hj.continuousAt.smul hcont).continuousWithinAt.congr_of_eventuallyEq heq
    (heq.eq_of_nhdsWithin ht)

lemma pullback_integral_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {μ : Measure ℝ} {K : ℂ × E → ℂ} {z j : ℝ → ℂ}
    {U : Set E} {B : ℝ → ℝ}
    (hU : IsOpen U) (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ u ∈ U, ∀ t : ℝ, AnalyticAt ℂ K (z t, u))
    (hB : ∀ᵐ t ∂μ, ∀ u ∈ U, ‖K (z t, u) * j t‖ ≤ B t)
    (hBi : Integrable B μ) :
    DifferentiableOn ℂ (fun u => ∫ t, K (z t, u) * j t ∂μ) U := by
  apply integral_differentiableOn_of_domination hU
  · intro u hu
    apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (((hK u hu t).continuousAt.comp (f := fun t : ℝ => (z t, u))
      (hz.continuousAt.prodMk continuousAt_const)).mul hj.continuousAt)
  · intro u hu
    exact (continuousOn_univ.mp (continuousOn_parameter_fderiv hz hj (S := univ)
      (fun t _ => hK u hu t))).aestronglyMeasurable
  · exact Eventually.of_forall fun t u hu =>
      ((hK u hu t).comp (f := fun u : E => (z t, u))
        (analyticAt_const.prod analyticAt_id)).mul analyticAt_const
  · exact hB
  · exact hBi

lemma pullback_setIntegral_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {μ : Measure ℝ} {S : Set ℝ} {K : ℂ × E → ℂ} {z j : ℝ → ℂ}
    {U : Set E} {B : ℝ → ℝ}
    (hS : MeasurableSet S) (hU : IsOpen U) (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ u ∈ U, ∀ t ∈ S, AnalyticAt ℂ K (z t, u))
    (hB : ∀ᵐ t ∂μ.restrict S, ∀ u ∈ U, ‖K (z t, u) * j t‖ ≤ B t)
    (hBi : Integrable B (μ.restrict S)) :
    DifferentiableOn ℂ (fun u => ∫ t in S, K (z t, u) * j t ∂μ) U := by
  apply integral_differentiableOn_of_domination hU
  · intro u hu
    apply ContinuousOn.aestronglyMeasurable (s := S) _ hS
    intro t ht
    exact (((hK u hu t ht).continuousAt.comp (f := fun t : ℝ => (z t, u))
      (hz.continuousAt.prodMk continuousAt_const)).mul hj.continuousAt).continuousWithinAt
  · intro u hu
    exact (continuousOn_parameter_fderiv hz hj (hK u hu)).aestronglyMeasurable hS
  · filter_upwards [ae_restrict_mem hS] with t ht u hu
    exact ((hK u hu t ht).comp (f := fun u : E => (z t, u))
      (analyticAt_const.prod analyticAt_id)).mul analyticAt_const
  · exact hB
  · exact hBi

lemma differentiableOn_analyticOnNhd_three {f : ℂ × (ℂ × ℂ) → ℂ}
    {U : Set (ℂ × (ℂ × ℂ))} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ f U := by
  intro u hu
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hu)
  exact ModularClusterIntegralsAux.analyticAt_of_differentiableOn_closedBall_three
    (hf.mono hrs) hr

lemma pullback_integral_analyticOn_two
    {μ : Measure ℝ} {K : ℂ × (ℂ × ℂ) → ℂ} {z j : ℝ → ℂ}
    {U : Set (ℂ × ℂ)} {B : ℝ → ℝ}
    (hU : IsOpen U) (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ u ∈ U, ∀ t : ℝ, AnalyticAt ℂ K (z t, u))
    (hB : ∀ᵐ t ∂μ, ∀ u ∈ U, ‖K (z t, u) * j t‖ ≤ B t)
    (hBi : Integrable B μ) :
    AnalyticOnNhd ℂ (fun u => ∫ t, K (z t, u) * j t ∂μ) U :=
  JointAnalytic.differentiableOn_analyticOnNhd
    (pullback_integral_differentiableOn hU hz hj hK hB hBi) hU

lemma pullback_integral_analyticOn_three
    {μ : Measure ℝ} {K : ℂ × (ℂ × (ℂ × ℂ)) → ℂ} {z j : ℝ → ℂ}
    {U : Set (ℂ × (ℂ × ℂ))} {B : ℝ → ℝ}
    (hU : IsOpen U) (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ u ∈ U, ∀ t : ℝ, AnalyticAt ℂ K (z t, u))
    (hB : ∀ᵐ t ∂μ, ∀ u ∈ U, ‖K (z t, u) * j t‖ ≤ B t)
    (hBi : Integrable B μ) :
    AnalyticOnNhd ℂ (fun u => ∫ t, K (z t, u) * j t ∂μ) U :=
  differentiableOn_analyticOnNhd_three
    (pullback_integral_differentiableOn hU hz hj hK hB hBi) hU

lemma pullback_setIntegral_analyticOn_two
    {μ : Measure ℝ} {S : Set ℝ} {K : ℂ × (ℂ × ℂ) → ℂ} {z j : ℝ → ℂ}
    {U : Set (ℂ × ℂ)} {B : ℝ → ℝ}
    (hS : MeasurableSet S) (hU : IsOpen U) (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ u ∈ U, ∀ t ∈ S, AnalyticAt ℂ K (z t, u))
    (hB : ∀ᵐ t ∂μ.restrict S, ∀ u ∈ U, ‖K (z t, u) * j t‖ ≤ B t)
    (hBi : Integrable B (μ.restrict S)) :
    AnalyticOnNhd ℂ (fun u => ∫ t in S, K (z t, u) * j t ∂μ) U :=
  JointAnalytic.differentiableOn_analyticOnNhd
    (pullback_setIntegral_differentiableOn hS hU hz hj hK hB hBi) hU

lemma pullback_setIntegral_analyticOn_three
    {μ : Measure ℝ} {S : Set ℝ} {K : ℂ × (ℂ × (ℂ × ℂ)) → ℂ} {z j : ℝ → ℂ}
    {U : Set (ℂ × (ℂ × ℂ))} {B : ℝ → ℝ}
    (hS : MeasurableSet S) (hU : IsOpen U) (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ u ∈ U, ∀ t ∈ S, AnalyticAt ℂ K (z t, u))
    (hB : ∀ᵐ t ∂μ.restrict S, ∀ u ∈ U, ‖K (z t, u) * j t‖ ≤ B t)
    (hBi : Integrable B (μ.restrict S)) :
    AnalyticOnNhd ℂ (fun u => ∫ t in S, K (z t, u) * j t ∂μ) U :=
  differentiableOn_analyticOnNhd_three
    (pullback_setIntegral_differentiableOn hS hU hz hj hK hB hBi) hU




/-- An arbitrary leading direction with a positive angular buffer. -/
theorem affine_sector (β κ ε A : ℝ) (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hε : 0 < ε) (hε' : ε ≤ Real.pi / 2) (hA : 0 ≤ A)
    (u H : ℂ) (hu : u ≠ 0)
    (harg : |(-u).arg| ≤ Sector.opening β κ - ε)
    (hH : ‖H‖ ≤ A)
    (hnorm : max 2 (2 * A / Real.sin ε) ≤ ‖u‖) :
    Sector.InDecaySector β κ (u + H) ∧ ‖u‖ / 2 ≤ ‖u + H‖ := by
  have hp := Real.pi_pos
  have hs : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε (by linarith)
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hAun : 2 * A ≤ ‖u‖ * Real.sin ε :=
    (div_le_iff₀ hs).mp ((le_max_right _ _).trans hnorm)
  have hq : ‖H / u‖ ≤ Real.sin ε / 2 := by
    rw [norm_div, div_le_iff₀ hun]
    nlinarith
  obtain ⟨hqarg, hqnorm⟩ := ModularSector.arg_one_add_small ε hε.le hε' (H / u) hq
  have hq0 : 1 + H / u ≠ 0 := norm_pos_iff.mp (by linarith)
  have hfactor : -(u + H) = (-u) * (1 + H / u) := by field_simp
  have hargx : (-(u + H)).arg = (-u).arg + (1 + H / u).arg := by
    rw [hfactor]
    apply Complex.arg_mul (neg_ne_zero.mpr hu) hq0
    have harg' := abs_le.mp harg
    have hqarg' := abs_le.mp hqarg
    dsimp [Sector.opening] at harg'
    constructor <;> linarith
  have hn : ‖u‖ / 2 ≤ ‖u + H‖ := by
    have ht : ‖u‖ - ‖H‖ ≤ ‖u + H‖ := by
      simpa using norm_sub_norm_le u (-H)
    have hsle := Real.sin_le_one ε
    have hAhalf : A ≤ ‖u‖ / 2 := by nlinarith
    linarith
  refine ⟨⟨?_, ?_⟩, hn⟩
  · have htwo := (le_max_left _ _).trans hnorm
    linarith
  · rw [hargx, abs_le]
    have harg' := abs_le.mp harg
    have hqarg' := abs_le.mp hqarg
    constructor <;> linarith

/-- Scaled rays admit uniform bounded affine offsets. -/
theorem ray_sector (β κ ε A B : ℝ) (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hε : 0 < ε) (hε' : ε ≤ Real.pi / 2) (hA : 0 ≤ A) (hB : 0 < B)
    (d H : ℂ) (hd : d ≠ 0)
    (harg : |(-d).arg| ≤ Sector.opening β κ - ε)
    (hdB : 1 / B ≤ ‖d‖) (hH : ‖H‖ ≤ A)
    (r : ℝ) (hr : B * max 2 (2 * A / Real.sin ε) ≤ r) :
    Sector.InDecaySector β κ ((r : ℂ) * d + H) ∧
      r / (2 * B) ≤ ‖(r : ℂ) * d + H‖ := by
  have hmaxpos : 0 < max 2 (2 * A / Real.sin ε) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hrpos : 0 < r := (mul_pos hB hmaxpos).trans_le hr
  have hunorm : ‖(r : ℂ) * d‖ = r * ‖d‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have huarg : |(-((r : ℂ) * d)).arg| = |(-d).arg| := by
    rw [← mul_neg, Complex.arg_real_mul (-d) hrpos]
  have hnorm : max 2 (2 * A / Real.sin ε) ≤ ‖(r : ℂ) * d‖ := by
    rw [hunorm]
    have hstep : r / B ≤ r * ‖d‖ := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hdB hrpos.le
    have hBr : max 2 (2 * A / Real.sin ε) ≤ r / B := (le_div_iff₀ hB).2 (by simpa [mul_comm] using hr)
    exact hBr.trans hstep
  obtain ⟨hsec, hn⟩ := affine_sector β κ ε A hβ hκ hε hε' hA
    ((r : ℂ) * d) H (mul_ne_zero (Complex.ofReal_ne_zero.mpr hrpos.ne') hd)
    (by rwa [huarg]) hH hnorm
  refine ⟨hsec, ?_⟩
  have hl : r / B ≤ r * ‖d‖ := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hdB hrpos.le
  rw [hunorm] at hn
  calc r / (2 * B) = (r / B) / 2 := by ring
       _ ≤ (r * ‖d‖) / 2 := div_le_div_of_nonneg_right hl (by norm_num)
       _ ≤ _ := hn

lemma factor_direction_arg (β κ ε : ℝ) (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hε : 0 < ε) (d b : ℂ) (hd : d ≠ 0) (hb : b ≠ 0)
    (hbarg : |b.arg| ≤ β)
    (hbudget : |(-Complex.I * d).arg| + 2 * β + κ + ε ≤ Real.pi / 2) :
    |(-(Complex.I * d / b)).arg| ≤ Sector.opening β κ - ε := by
  have hp := Real.pi_pos
  have hda := abs_nonneg (-Complex.I * d).arg
  have hbinv : (b⁻¹).arg = -b.arg := by
    rw [Complex.arg_inv, if_neg]
    exact ne_of_lt (lt_of_le_of_lt (le_abs_self _) (by linarith))
  have heq : -(Complex.I * d / b) = (-Complex.I * d) * b⁻¹ := by ring
  rw [heq]
  have harg' := abs_le.mp hbarg
  have hda' := abs_le.mp (le_refl |(-Complex.I * d).arg|)
  rw [Complex.arg_mul (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hd)
    (inv_ne_zero hb) (by rw [hbinv]; constructor <;> linarith), hbinv]
  change |(-Complex.I * d).arg - b.arg| ≤ _
  have hsub := abs_sub (-Complex.I * d).arg b.arg
  dsimp [Sector.opening]
  linarith

/-- This export covers arbitrary compact sets of complex parameters. Its hypotheses contain only
compactness and an explicit angle budget. -/
theorem compact_modular_ray_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (K : Set ℂ) (hK : IsCompact K)
    (hdom : K ⊆ modularPhiDomain M)
    (β κ : ℝ)
    (hFamily : Sector.Family ((fun τ => Complex.sqrt (etaDenom M τ)) '' K) β κ)
    (d : ℂ) (hd : ‖d‖ = 1) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ Real.pi / 2)
    (hbudget : |(-Complex.I * d).arg| + 2 * β + κ + ε ≤ Real.pi / 2)
    (A : ℝ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ τ ∈ K, ∀ i ∈ F, ∀ v : ℂ, ‖v‖ ≤ A → ∀ r : ℝ, R ≤ r →
        let z := (r : ℂ) * d + v
        (z, τ) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
          ‖modularPhi M i.1 i.2 z τ‖ + ‖(modularPhi M i.1 i.2 z τ)⁻¹‖ ≤ C := by
  let KB : Set ℂ := (fun τ => Complex.sqrt (etaDenom M τ)) '' K
  obtain ⟨B₀, hB₀⟩ := hFamily.compact.exists_bound_of_continuousOn continuousOn_id
  let B := max 1 B₀
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbB : ∀ b ∈ KB, ‖b‖ ≤ B := fun b hb => (hB₀ b hb).trans (le_max_right _ _)
  let L : Set (ℂ × ℂ) := Metric.closedBall 0 A ×ˢ K
  have hL : IsCompact L := (isCompact_closedBall _ _).prod hK
  let H : ((ℤ × ℤ) × ℕ) → (ℂ × ℂ) → ℂ := fun ij q =>
    (modularPhiFactorPoint M ij.1.1 ij.1.2 ij.2 q.1 q.2).2
  have hHcont : ∀ ij ∈ F.product (Finset.range (M 1 0).toNat), ContinuousOn (H ij) L := by
    intro ij hij q hq
    exact ((modularPhiFactorPoint_analytic M ij.1.1 ij.1.2 ij.2) q
      (hdom hq.2)).continuousAt.snd.continuousWithinAt
  obtain ⟨A₁, hA₁, hH⟩ := G1BilateralRatioTailsAux.finite_compact_bound
    (F.product (Finset.range (M 1 0).toNat)) L hL H hHcont
  obtain ⟨lam, hlam⟩ := Sector.exists_uniform_margin hFamily
  obtain ⟨C₀, v₀, hC₀, hv₀, hdec⟩ := Sector.phiExtended_uniform_sector_decay hFamily
  let C := 2 * ModularSector.finiteProductConstant (M 1 0).toNat C₀ + 2
  let R := B * max 2 (2 * A₁ / Real.sin ε)
  have hR : 0 < R := mul_pos hB (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hC : 0 < C := by
    dsimp [C, ModularSector.finiteProductConstant]
    positivity
  refine ⟨C, R, hC, hR, ?_⟩
  intro τ hτ i hi v hv r hr
  let z := (r : ℂ) * d + v
  let b := Complex.sqrt (etaDenom M τ)
  have hb : b ∈ KB := ⟨τ, hτ, rfl⟩
  have hbne : b ≠ 0 := (modularPhi_sqrt_admissible M τ (hdom hτ)).2.2
  have hdne : d ≠ 0 := norm_ne_zero_iff.mp (by rw [hd]; norm_num)
  have hleadne : Complex.I * d / b ≠ 0 := div_ne_zero (mul_ne_zero Complex.I_ne_zero hdne) hbne
  have hleadarg : |(-(Complex.I * d / b)).arg| ≤ Sector.opening β κ - ε :=
    factor_direction_arg β κ ε hFamily.beta_nonneg hFamily.kappa_pos hε d b hdne hbne
      (hFamily.arg_le b hb) hbudget
  have hleadnorm : 1 / B ≤ ‖Complex.I * d / b‖ := by
    rw [norm_div, norm_mul, Complex.norm_I, hd, one_mul]
    exact one_div_le_one_div_of_le (norm_pos_iff.mpr hbne) (hbB b hb)
  have hfactor : ∀ j ∈ Finset.range (M 1 0).toNat,
      Sector.InDecaySector β κ (modularPhiFactorPoint M i.1 i.2 j z τ).2 := by
    intro j hj
    have hvo : (v, τ) ∈ L := ⟨by simpa using hv, hτ⟩
    have hoff := hH (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩) (v, τ) hvo
    have hsec := ray_sector β κ ε A₁ B hFamily.beta_nonneg hFamily.kappa_pos
      hε hε' hA₁.le hB (Complex.I * d / b)
      (modularPhiFactorPoint M i.1 i.2 j v τ).2 hleadne hleadarg hleadnorm hoff r hr
    have heq : (modularPhiFactorPoint M i.1 i.2 j z τ).2 =
        (r : ℂ) * (Complex.I * d / b) + (modularPhiFactorPoint M i.1 i.2 j v τ).2 := by
      rw [ModularSector.factorPoint_split, ModularSector.factorPoint_split]
      dsimp only [z, b]
      ring
    rw [heq]
    exact hsec.1
  have hfree : ∀ j ∈ Finset.range (M 1 0).toNat,
      phiPoleMultiplicity b (modularPhiFactorPoint M i.1 i.2 j z τ).2 = 0 ∧
        phiZeroMultiplicity b (modularPhiFactorPoint M i.1 i.2 j z τ).2 = 0 := by
    intro j hj
    exact ModularSector.phi_divisor_free_decaySector hFamily hlam hb (hfactor j hj)
  have hmult := modularPhi_multiplicity_pullback M hM i.1 i.2 z τ (hdom hτ)
  have hpole : modularPhiPoleMultiplicity M i.1 i.2 z τ = 0 := by
    rw [hmult.1]
    exact Finset.sum_eq_zero fun j hj => (hfree j hj).1
  have hzero : modularPhiZeroMultiplicity M i.1 i.2 z τ = 0 := by
    rw [hmult.2]
    exact Finset.sum_eq_zero fun j hj => (hfree j hj).2
  refine ⟨⟨hdom hτ, hpole, hzero⟩, ?_⟩
  let f : ℕ → ℂ := fun j => phiExtended b (modularPhiFactorPoint M i.1 i.2 j z τ).2
  have herror : ∀ j ∈ Finset.range (M 1 0).toNat, ‖f j - 1‖ + ‖(f j)⁻¹ - 1‖ ≤ C₀ := by
    intro j hj
    have hpoint := hdec b hb _ (hfactor j hj)
    have hexp : Real.exp (-2 * v₀ * ‖(modularPhiFactorPoint M i.1 i.2 j z τ).2‖) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg (modularPhiFactorPoint M i.1 i.2 j z τ).2])
    exact hpoint.trans (by simpa using mul_le_mul_of_nonneg_left hexp hC₀.le)
  have hforward : ∀ j ∈ Finset.range (M 1 0).toNat, ‖f j - 1‖ ≤ C₀ * 1 := by
    intro j hj
    simpa using (le_add_of_nonneg_right (norm_nonneg ((f j)⁻¹ - 1))).trans (herror j hj)
  have hinverse : ∀ j ∈ Finset.range (M 1 0).toNat, ‖(f j)⁻¹ - 1‖ ≤ C₀ * 1 := by
    intro j hj
    simpa using (le_add_of_nonneg_left (norm_nonneg (f j - 1))).trans (herror j hj)
  have hp := ModularSector.finite_product_error _ f C₀ 1 hC₀.le zero_le_one le_rfl hforward
  have hi' := ModularSector.finite_inverse_product_error _ f C₀ 1 hC₀.le zero_le_one le_rfl hinverse
  have hpn := norm_le_norm_sub_add (∏ j ∈ Finset.range (M 1 0).toNat, f j) 1
  have hin := norm_le_norm_sub_add ((∏ j ∈ Finset.range (M 1 0).toNat, f j)⁻¹) 1
  change ‖(∏ j ∈ Finset.range (M 1 0).toNat, f j)‖ +
    ‖(∏ j ∈ Finset.range (M 1 0).toNat, f j)⁻¹‖ ≤ C
  dsimp only [C]
  simp only [norm_one, mul_one] at hp hi' hpn hin
  linarith

/-- Reflection at actual non-pole point values, with no tail geometry assumed. -/
lemma point_reflection_of_no_poles (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (i : ℤ × ℤ) (z τ : ℂ) (hdom : τ ∈ modularPhiDomain M)
    (hp : modularPhiPoleMultiplicity M i.1 i.2 z τ = 0)
    (hr : modularPhiPoleMultiplicity M (1 - i.1) (1 - i.2) (-z) τ = 0) :
    modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ =
      modularReflectionFactor M i.1 i.2 z τ := by
  have hAi := modularPhi_joint_analytic_no_poles M hM i.1 i.2 (z, τ) ⟨hdom, hp⟩
  have hAr := modularPhi_joint_analytic_no_poles M hM (1 - i.1) (1 - i.2) (-z, τ) ⟨hdom, hr⟩
  have hL : ContinuousAt (fun w : ℂ => modularPhi M i.1 i.2 w τ) z := by
    have hpair : ContinuousAt (fun w : ℂ => (w, τ)) z :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp (g := fun p : ℂ × ℂ => modularPhi M i.1 i.2 p.1 p.2)
      (f := fun w : ℂ => (w, τ)) (x := z) hAi.continuousAt hpair
  have hR : ContinuousAt (fun w : ℂ => modularPhi M (1 - i.1) (1 - i.2) (-w) τ) z := by
    have hpair : ContinuousAt (fun w : ℂ => (-w, τ)) z :=
      continuousAt_neg.prodMk continuousAt_const
    exact ContinuousAt.comp (g := fun p : ℂ × ℂ => modularPhi M (1 - i.1) (1 - i.2) p.1 p.2)
      (f := fun w : ℂ => (-w, τ)) (x := z) hAr.continuousAt hpair
  have hnorm := modularPhi_reflection_normalized M hM i.1 i.2 z τ hdom hL hR
  have hμ : etaMultiplier M ≠ 0 := etaMultiplier_ne_zero M hM
  have hkey : (etaMultiplier M * etaMultiplier M) *
      (modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) =
      (-1 : ℂ) ^ (i.1 + i.2) * e (modularReflectionPolynomial M i.1 i.2 z τ) := by
    calc
      (etaMultiplier M * etaMultiplier M) *
          (modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) =
          (etaMultiplier M * modularPhi M i.1 i.2 z τ) *
            (etaMultiplier M * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) := by ring
      _ = _ := hnorm
  have hgoal : modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ =
      (etaMultiplier M * etaMultiplier M)⁻¹ *
        ((-1 : ℂ) ^ (i.1 + i.2) * e (modularReflectionPolynomial M i.1 i.2 z τ)) := by
    rw [← hkey]
    field_simp [hμ]
  have hpow : (etaMultiplier M) ^ (-2 : ℤ) = (etaMultiplier M * etaMultiplier M)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
    ring
  rw [hgoal]
  unfold modularReflectionFactor
  rw [hpow]
  ring

/-- Broad compact-parameter bounds for both normalized lower representatives. -/
theorem compact_modular_reflected_ray_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (K : Set ℂ) (hK : IsCompact K)
    (hdom : K ⊆ modularPhiDomain M)
    (β κ : ℝ)
    (hFamily : Sector.Family ((fun τ => Complex.sqrt (etaDenom M τ)) '' K) β κ)
    (d : ℂ) (hd : ‖d‖ = 1) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ Real.pi / 2)
    (hbudget : |(-Complex.I * d).arg| + 2 * β + κ + ε ≤ Real.pi / 2)
    (A : ℝ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ τ ∈ K, ∀ i ∈ F, ∀ v : ℂ, ‖v‖ ≤ A → ∀ r : ℝ, R ≤ r →
        let z := -((r : ℂ) * d + v)
        (z, τ) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
          ‖modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ‖ +
          ‖modularReflectionFactor M i.1 i.2 z τ * (modularPhi M i.1 i.2 z τ)⁻¹‖ ≤ C := by
  obtain ⟨C, R, hC, hR, hbound⟩ := compact_modular_ray_bound M hM
    (F.image ModularSector.reflectedIndex) K hK hdom β κ hFamily d hd ε hε hε' hbudget A
  refine ⟨C, R, hC, hR, ?_⟩
  intro τ hτ i hi v hv r hr
  let z : ℂ := -((r : ℂ) * d + v)
  have hi' : ModularSector.reflectedIndex i ∈ F.image ModularSector.reflectedIndex :=
    Finset.mem_image_of_mem _ hi
  have hub := hbound τ hτ (ModularSector.reflectedIndex i) hi' v hv r hr
  have hupper : (-z, τ) ∈ modularPhiNonvanishingDomain M (1 - i.1) (1 - i.2) := by
    simpa only [z, neg_neg, ModularSector.reflectedIndex] using hub.1
  have hmult := ModularSector.divisor_multiplicity_reflection M i.1 i.2 z τ
  have hpole : modularPhiPoleMultiplicity M i.1 i.2 z τ = 0 := by
    rw [hmult.1]
    exact hupper.2.2
  have hzero : modularPhiZeroMultiplicity M i.1 i.2 z τ = 0 := by
    rw [hmult.2]
    exact hupper.2.1
  have hlower : (z, τ) ∈ modularPhiNonvanishingDomain M i.1 i.2 := ⟨hdom hτ, hpole, hzero⟩
  refine ⟨hlower, ?_⟩
  have hpne := ModularSector.tail_value_ne_zero M hM i z τ hlower
  have hrne := ModularSector.tail_value_ne_zero M hM (ModularSector.reflectedIndex i) (-z) τ hupper
  have hab := point_reflection_of_no_poles M hM i z τ (hdom hτ) hpole hupper.2.1
  have h₁ : modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ =
      (modularPhi M (1 - i.1) (1 - i.2) (-z) τ)⁻¹ := by
    rw [← hab]
    field_simp
  have h₂ : modularReflectionFactor M i.1 i.2 z τ * (modularPhi M i.1 i.2 z τ)⁻¹ =
      modularPhi M (1 - i.1) (1 - i.2) (-z) τ := by
    rw [← hab]
    field_simp
  change ‖modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ‖ +
    ‖modularReflectionFactor M i.1 i.2 z τ * (modularPhi M i.1 i.2 z τ)⁻¹‖ ≤ C
  rw [h₁, h₂, add_comm]
  simpa only [z, neg_neg, ModularSector.reflectedIndex] using hub.2



open G1Continuation

lemma bent_ineq_iff (z : ℂ) (x t : ℝ) (ht : 0 ≤ t) :
    x + max 0 (-z.im - 1) * t < z.re ↔
      x < z.re ∧ x + (-z.im - 1) * t < z.re := by
  rw [max_mul_of_nonneg _ _ ht, zero_mul, add_max, add_zero, max_lt_iff]

lemma bent_ineq_add (z T : ℂ) (x t : ℝ) (u v : ℕ)
    (ht : 0 ≤ t) (hT : 0 ≤ T.re) (hT' : 0 ≤ T.re + T.im * t)
    (hz : x + max 0 (-z.im - 1) * t < z.re) :
    x + max 0 (-(z + (u : ℂ) * T + (v : ℂ)).im - 1) * t <
      (z + (u : ℂ) * T + (v : ℂ)).re := by
  rw [bent_ineq_iff _ _ _ ht] at hz ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, add_zero]
  have hu : 0 ≤ (u : ℝ) := Nat.cast_nonneg _
  have hv : 0 ≤ (v : ℝ) := Nat.cast_nonneg _
  constructor
  · nlinarith [mul_nonneg hu hT]
  · nlinarith [mul_nonneg hu hT']

lemma pole_factor_point (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (j u v : ℕ) :
    modularPhiPolePoint M m n τ
        (modularPhiPoleFactorLabel M m n j u v).1
        (modularPhiPoleFactorLabel M m n j u v).2 =
      modularPhiPolePoint M m n τ
        (modularPhiPoleFactorLabel M m n j 0 0).1
        (modularPhiPoleFactorLabel M m n j 0 0).2 +
          (u : ℂ) * etaDenom M τ + (v : ℂ) := by
  have hc : ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast divisorC_cast M hM
  have hcne : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [modularPhiPoleFactorLabel, modularPhiPolePoint, Nat.cast_add,
    Nat.cast_mul, Nat.mul_zero, Nat.zero_add, hc]
  field_simp
  ring

lemma bentClear_iff_finite (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (n m : ℤ) (x ψ : ℝ)
    (ht : 0 ≤ Real.tan ψ) (hT : 0 ≤ (etaDenom M τ).re)
    (hT' : 0 ≤ (etaDenom M τ).re + (etaDenom M τ).im * Real.tan ψ) :
    BentClear M τ n m x ψ ↔
      ∀ j : Fin (M 1 0).toNat,
        let k := modularPhiPoleFactorLabel M (m + 1) n (j : ℕ) 0 0
        let z := modularPhiPolePoint M (m + 1) n τ k.1 k.2
        x + max 0 (-z.im - 1) * Real.tan ψ < z.re := by
  constructor
  · intro hc j
    exact hc _ (pole_label_mem M hM (m + 1) n 0 0 j j.isLt)
  · intro hc k hk
    obtain ⟨hj, hK, hJ⟩ := pole_label_decompose M hM (m + 1) n k.1 k.2 hk
    let j : Fin (M 1 0).toNat := ⟨_, hj⟩
    have he : k = modularPhiPoleFactorLabel M (m + 1) n j
        (k.1 / (M 1 0).toNat) (k.2 / (M 1 0).toNat) := by
      apply Prod.ext
      · exact hK
      · exact hJ
    rw [he]
    dsimp only
    rw [pole_factor_point M hM]
    exact bent_ineq_add _ _ x (Real.tan ψ) _ _ ht hT hT' (hc j)

lemma bent_slope_pos (T : ℂ) (ψ : ℝ) (hT : 0 < T.re)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) (ha : |T.arg| < ψ) :
    0 < T.re + T.im * Real.tan ψ := by
  have hhalf : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have htpos : 0 < Real.tan ψ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hψ (hψ'.trans hhalf)
  have htlt : Real.tan ψ < 1 := by
    simpa only [Real.tan_pi_div_four] using
      Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hψ.le hhalf hψ'
  have harg : -(Real.pi / 4) < T.arg := by
    have := (abs_lt.mp ha).1
    linarith
  have htarg : -1 < T.im / T.re := by
    rw [← Complex.tan_arg]
    have hlow : -(Real.pi / 2) < -(Real.pi / 4) := by linarith [Real.pi_pos]
    have hhigh : T.arg < Real.pi / 2 :=
      ((le_abs_self T.arg).trans_lt ha).trans (hψ'.trans hhalf)
    simpa only [Real.tan_neg, Real.tan_pi_div_four] using
      Real.tan_lt_tan_of_lt_of_lt_pi_div_two hlow hhigh harg
  have him : -T.re < T.im := by simpa using (lt_div_iff₀ hT).mp htarg
  have hmul := mul_lt_mul_of_pos_right him htpos
  nlinarith


lemma single_admissible_isOpen (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell m : ℤ) (x ψ : ℝ) :
    IsOpen {u : ℂ × ℂ | u.1 ∈ modularPhiDomain M ∧
      0 < (etaDenom M u.1).re ∧ 0 < ψ ∧ ψ < Real.pi / 4 ∧
      |(etaDenom M u.1).arg| < ψ ∧
      u.2 ∈ singleWindow M u.1 h ell ∧ BentClear M u.1 n m x ψ} := by
  apply isOpen_iff_mem_nhds.mpr
  intro u hu
  rcases hu with ⟨huD, huRe, hψ, hψ', huArg, huW, huClear⟩
  have hden : Continuous (fun v : ℂ × ℂ => etaDenom M v.1) := by
    unfold etaDenom
    fun_prop
  have hTne : etaDenom M u.1 ≠ 0 := etaDenom_ne_zero_of_mem M huD
  have ht : 0 ≤ Real.tan ψ :=
    (Real.tan_pos_of_pos_of_lt_pi_div_two hψ (by linarith [Real.pi_pos])).le
  have huSlope := bent_slope_pos (etaDenom M u.1) ψ huRe hψ hψ' huArg
  have hfinite := (bentClear_iff_finite M hM u.1 n m x ψ ht huRe.le huSlope.le).mp huClear
  have hfin : ∀ᶠ v : ℂ × ℂ in 𝓝 u,
      ∀ j : Fin (M 1 0).toNat,
        let k := modularPhiPoleFactorLabel M (m + 1) n (j : ℕ) 0 0
        let z := modularPhiPolePoint M (m + 1) n v.1 k.1 k.2
        x + max 0 (-z.im - 1) * Real.tan ψ < z.re := by
    rw [Filter.eventually_all]
    intro j
    have hcont : Continuous (fun v : ℂ × ℂ =>
        let k := modularPhiPoleFactorLabel M (m + 1) n (j : ℕ) 0 0
        let z := modularPhiPolePoint M (m + 1) n v.1 k.1 k.2
        x + max 0 (-z.im - 1) * Real.tan ψ - z.re) := by
      unfold modularPhiPolePoint etaDenom
      fun_prop
    have he := hcont.continuousAt.eventually
      (gt_mem_nhds (show
        (let k := modularPhiPoleFactorLabel M (m + 1) n (j : ℕ) 0 0
         let z := modularPhiPolePoint M (m + 1) n u.1 k.1 k.2
         x + max 0 (-z.im - 1) * Real.tan ψ - z.re) < 0 by
           dsimp only
           linarith [hfinite j]))
    filter_upwards [he] with v hv
    dsimp only at hv ⊢
    linarith
  have hdom : ∀ᶠ v : ℂ × ℂ in 𝓝 u, v.1 ∈ modularPhiDomain M :=
    ((modularPhiDomain_isOpen M).preimage continuous_fst).mem_nhds huD
  have hre : ∀ᶠ v : ℂ × ℂ in 𝓝 u, 0 < (etaDenom M v.1).re :=
    (Complex.continuous_re.comp hden).continuousAt.eventually (lt_mem_nhds huRe)
  have hargCont : ContinuousAt (fun v : ℂ × ℂ => |(etaDenom M v.1).arg|) u :=
    ((Complex.continuousAt_arg (Or.inl huRe)).comp
      (f := fun v : ℂ × ℂ => etaDenom M v.1) hden.continuousAt).abs
  have harg : ∀ᶠ v : ℂ × ℂ in 𝓝 u, |(etaDenom M v.1).arg| < ψ :=
    hargCont.eventually (gt_mem_nhds huArg)
  have hnum : Continuous (fun v : ℂ × ℂ => G1RatioTail.complexS M v.1 v.2 h ell) := by
    unfold G1RatioTail.complexS etaDenom
    fun_prop
  have hwCont : ContinuousAt (fun v : ℂ × ℂ =>
      (G1RatioTail.complexS M v.1 v.2 h ell / etaDenom M v.1).re) u :=
    Complex.continuous_re.continuousAt.comp
      (hnum.continuousAt.div hden.continuousAt hTne)
  have hw : ∀ᶠ v : ℂ × ℂ in 𝓝 u, v.2 ∈ singleWindow M v.1 h ell :=
    hwCont.eventually (lt_mem_nhds huW)
  filter_upwards [hdom, hre, harg, hw, hfin] with v hvD hvRe hvArg hvW hvfin
  refine ⟨hvD, hvRe, hψ, hψ', hvArg, hvW, ?_⟩
  exact (bentClear_iff_finite M hM v.1 n m x ψ ht hvRe.le
    (bent_slope_pos (etaDenom M v.1) ψ hvRe hψ hψ' hvArg).le).mpr hvfin


lemma holomorphic_of_bent_graph (M : SL(2, ℤ)) (τ z : ℂ) (n m : ℤ) (x ψ : ℝ)
    (hτ : τ ∈ modularPhiDomain M) (hc : BentClear M τ n m x ψ)
    (hz : z.re ≤ x + max 0 (-z.im - 1) * Real.tan ψ) :
    (z, τ) ∈ modularPhiHolomorphicDomain M (m + 1) n := by
  have hempty : modularPhiPoleIndices M (m + 1) n z τ = ∅ := by
    ext k
    simp only [modularPhiPoleIndices, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hk he
    have hc' := hc k hk
    dsimp only at hc'
    rw [← he] at hc'
    exact (not_lt_of_ge hz) hc'
  exact ⟨hτ, by simp [modularPhiPoleMultiplicity, hempty]⟩

lemma bentClear_path_regular (M : SL(2, ℤ)) (τ : ℂ) (n m : ℤ) (x ψ : ℝ)
    (hτ : τ ∈ modularPhiDomain M) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hc : BentClear M τ n m x ψ) :
    (∀ t : ℝ, -1 ≤ t →
      (g1VerticalPoint x t, τ) ∈ modularPhiHolomorphicDomain M (m + 1) n) ∧
    (∀ r : ℝ, 0 ≤ r →
      (g1BentLowerPoint x ψ r, τ) ∈ modularPhiHolomorphicDomain M (m + 1) n) := by
  constructor
  · intro t ht
    apply holomorphic_of_bent_graph M τ _ n m x ψ hτ hc
    simp [g1VerticalPoint, max_eq_left (show -t - 1 ≤ 0 by linarith)]
  · intro r hr
    apply holomorphic_of_bent_graph M τ _ n m x ψ hτ hc
    have hcpos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hre : (g1BentLowerPoint x ψ r).re = x + r * Real.sin ψ := by
      simp [g1BentLowerPoint, G1BilateralSingleTailsAux.branch_direction_re]
    have him : (g1BentLowerPoint x ψ r).im = -1 - r * Real.cos ψ := by
      simp [g1BentLowerPoint, G1BilateralSingleTailsAux.branch_direction_im]
      ring
    rw [hre, him]
    have hnonneg : 0 ≤ -(-1 - r * Real.cos ψ) - 1 := by
      nlinarith [mul_nonneg hr hcpos.le]
    rw [max_eq_right hnonneg, Real.tan_eq_sin_div_cos]
    have heq : (-(-1 - r * Real.cos ψ) - 1) *
        (Real.sin ψ / Real.cos ψ) = r * Real.sin ψ := by
      field_simp
      <;> ring
    rw [heq]



lemma extensionIntegral_eq_of_finite_ledger (D₀ D₁ : CircleExtension) (f : ℂ → ℂ)
    (hi₀ : ExtensionIntegrable D₀ f) (hi₁ : ExtensionIntegrable D₁ f)
    (hc : Tendsto (G1FiniteLedger.connectors f D₀.base.crossing D₁.base.crossing)
      atTop (𝓝 0))
    (hl : ∀ᶠ R : ℝ in atTop, extensionTruncated D₁ f R - extensionTruncated D₀ f R +
      G1FiniteLedger.connectors f D₀.base.crossing D₁.base.crossing R = 0) :
    extensionIntegral D₀ f = extensionIntegral D₁ f := by
  have hlim := ((extensionTruncated_tendsto D₁ f hi₁).sub
    (extensionTruncated_tendsto D₀ f hi₀)).add hc
  have hzero : Tendsto (fun R : ℝ => extensionTruncated D₁ f R -
      extensionTruncated D₀ f R +
      G1FiniteLedger.connectors f D₀.base.crossing D₁.base.crossing R) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hl.mono fun _ h => h.symm)
  have heq := tendsto_nhds_unique hlim hzero
  exact (sub_eq_zero.mp (by simpa only [add_zero] using heq)).symm



open G1Continuation G1BilateralRatioTailsAux

lemma moving_affine_phase_bound (M : SL(2, ℤ)) (n h ell p : ℤ)
    (F : Finset ℤ) (K : Set Parameters) (hK : IsCompact K)
    (hdom : ∀ v ∈ K, v.1 ∈ modularPhiDomain M) (a b : ℝ) (lower : Bool) :
    ∃ B : ℝ, 0 < B ∧ ∀ v ∈ K, ∀ m ∈ F, ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖e (((if lower then G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p
        else G1RatioTail.complexS M v.1 v.2.1 h ell) / etaDenom M v.1) *
          g1VerticalPoint x t + phaseConstant M v.1 v.2.1 v.2.2 n h ell p m lower)‖ ≤
        B * Real.exp (-(2 * Real.pi *
          ((if lower then G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p
            else G1RatioTail.complexS M v.1 v.2.1 h ell) / etaDenom M v.1).re) * t) := by
  let A : Parameters → ℂ := fun v =>
    (if lower then G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p
      else G1RatioTail.complexS M v.1 v.2.1 h ell) / etaDenom M v.1
  let f : ℤ → (Parameters × ℝ) → ℂ := fun m q =>
    e (A q.1 * (q.2 : ℂ) + phaseConstant M q.1.1 q.1.2.1 q.1.2.2 n h ell p m lower)
  have hf : ∀ m ∈ F, ContinuousOn (f m) (K ×ˢ Icc a b) := by
    intro m hm q hq
    apply ContinuousAt.continuousWithinAt
    have hd : etaDenom M q.1.1 ≠ 0 := etaDenom_ne_zero_of_mem M (hdom q.1 hq.1)
    cases lower <;>
      dsimp [f, A, phaseConstant, G1RatioTail.complexL, G1RatioTail.complexS,
        g1Exponent, modularReflectionPolynomial, modularBernoulliTwo, e, etaMobius] <;>
      fun_prop (disch := exact hd)
  obtain ⟨B, hB, hbound⟩ := finite_compact_bound F (K ×ˢ Icc a b)
    (hK.prod isCompact_Icc) f hf
  refine ⟨B, hB, ?_⟩
  intro v hv m hm x hx t
  rw [norm_e_vertical]
  exact mul_le_mul_of_nonneg_right (hbound m hm (v, x) ⟨hv, hx⟩) (Real.exp_pos _).le

lemma moving_ratio_phase_margin (M : SL(2, ℤ)) (h ell p : ℤ)
    (v : Parameters) (hdom : v.1 ∈ modularPhiDomain M)
    (hS : 0 < (G1RatioTail.complexS M v.1 v.2.1 h ell / etaDenom M v.1).re)
    (hL : (G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p / etaDenom M v.1).re < 0) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧ ∀ u ∈ Metric.closedBall v ρ,
      u.1 ∈ modularPhiDomain M ∧
      κ ≤ 2 * Real.pi * (G1RatioTail.complexS M u.1 u.2.1 h ell / etaDenom M u.1).re ∧
      κ ≤ -(2 * Real.pi * (G1RatioTail.complexL M u.1 u.2.1 u.2.2 h ell p /
        etaDenom M u.1).re) := by
  let s : Parameters → ℝ := fun u =>
    2 * Real.pi * (G1RatioTail.complexS M u.1 u.2.1 h ell / etaDenom M u.1).re
  let l : Parameters → ℝ := fun u =>
    -(2 * Real.pi * (G1RatioTail.complexL M u.1 u.2.1 u.2.2 h ell p / etaDenom M u.1).re)
  have hd : etaDenom M v.1 ≠ 0 := etaDenom_ne_zero_of_mem M hdom
  have hsc : ContinuousAt s v := by
    dsimp [s, G1RatioTail.complexS]
    fun_prop (disch := exact hd)
  have hlc : ContinuousAt l v := by
    dsimp [l, G1RatioTail.complexL, G1RatioTail.complexS]
    fun_prop (disch := exact hd)
  have hs : 0 < s v := by dsimp [s]; positivity
  have hl : 0 < l v := by dsimp [l]; nlinarith [Real.pi_pos]
  have he : ∀ᶠ u in 𝓝 v,
      u.1 ∈ modularPhiDomain M ∧ s v / 2 ≤ s u ∧ l v / 2 ≤ l u := by
    filter_upwards [((modularPhiDomain_isOpen M).preimage continuous_fst).mem_nhds hdom,
      hsc.eventually (Ioi_mem_nhds (half_lt_self hs)),
      hlc.eventually (Ioi_mem_nhds (half_lt_self hl))] with u hu hs' hl'
    exact ⟨hu, hs'.le, hl'.le⟩
  obtain ⟨ρ, hρ, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp he
  refine ⟨ρ, min (s v / 2) (l v / 2), hρ, lt_min (half_pos hs) (half_pos hl), ?_⟩
  intro u hu
  exact ⟨(hb hu).1, (min_le_left _ _).trans (hb hu).2.1,
    (min_le_right _ _).trans (hb hu).2.2⟩

lemma moving_single_phase_margin (M : SL(2, ℤ)) (h ell : ℤ)
    (v : ℂ × ℂ) (hdom : v.1 ∈ modularPhiDomain M)
    (hS : 0 < (G1RatioTail.complexS M v.1 v.2 h ell / etaDenom M v.1).re) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧ ∀ u ∈ Metric.closedBall v ρ,
      u.1 ∈ modularPhiDomain M ∧
      κ ≤ 2 * Real.pi * (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1).re := by
  let s : (ℂ × ℂ) → ℝ := fun u =>
    2 * Real.pi * (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1).re
  have hd : etaDenom M v.1 ≠ 0 := etaDenom_ne_zero_of_mem M hdom
  have hsc : ContinuousAt s v := by
    dsimp [s, G1RatioTail.complexS]
    fun_prop (disch := exact hd)
  have hs : 0 < s v := by dsimp [s]; positivity
  have he : ∀ᶠ u in 𝓝 v, u.1 ∈ modularPhiDomain M ∧ s v / 2 ≤ s u := by
    filter_upwards [((modularPhiDomain_isOpen M).preimage continuous_fst).mem_nhds hdom,
      hsc.eventually (Ioi_mem_nhds (half_lt_self hs))] with u hu hs'
    exact ⟨hu, hs'.le⟩
  obtain ⟨ρ, hρ, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp he
  exact ⟨ρ, s v / 2, hρ, half_pos hs, fun u hu => hb hu⟩

end SICLean.L4.G1ContinuationHolomorphyAux


namespace SICLean.L4.G1ContinuationHolomorphyAux

open G1BilateralGeometry G1BilateralSingleTails G1BilateralSingleTailsAux

lemma moving_gaussian_margin (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (ψ : ℝ) (hdom : τ ∈ modularPhiDomain M)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (harg : |(etaDenom M τ).arg| < ψ) :
    ∃ ρ a : ℝ, 0 < ρ ∧ 0 < a ∧ ∀ t ∈ Metric.closedBall τ ρ,
      t ∈ modularPhiDomain M ∧ a ≤ gaussianCoefficient M t ψ := by
  have hd : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hdom
  have hdc : Continuous (etaDenom M) := by unfold etaDenom; fun_prop
  have harc : ContinuousAt (fun t => (etaDenom M t).arg) τ :=
    (Complex.continuousAt_arg hdom).comp hdc.continuousAt
  have hgc : ContinuousAt (fun t => gaussianCoefficient M t ψ) τ := by
    unfold gaussianCoefficient
    exact (continuousAt_const.div hdc.continuousAt.norm (norm_ne_zero_iff.mpr hd)).mul
      (Real.continuous_sin.continuousAt.comp (continuousAt_const.sub harc))
  have hs : 0 < Real.sin (2 * ψ - (etaDenom M τ).arg) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [(abs_lt.mp harg).2])
      (by linarith [(abs_lt.mp harg).1, Real.pi_pos])
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hg : 0 < gaussianCoefficient M τ ψ := by
    unfold gaussianCoefficient
    exact mul_pos (div_pos (mul_pos Real.pi_pos hc) (norm_pos_iff.mpr hd)) hs
  have he : ∀ᶠ t in 𝓝 τ, t ∈ modularPhiDomain M ∧
      gaussianCoefficient M τ ψ / 2 ≤ gaussianCoefficient M t ψ := by
    filter_upwards [(modularPhiDomain_isOpen M).mem_nhds hdom,
      hgc.eventually (Ioi_mem_nhds (half_lt_self hg))] with t ht hg'
    exact ⟨ht, hg'.le⟩
  obtain ⟨ρ, hρ, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp he
  exact ⟨ρ, gaussianCoefficient M τ ψ / 2, hρ, half_pos hg, fun t ht => hb ht⟩

lemma lowerPhase_real_expansion (M : SL(2, ℤ)) (τ w : ℂ)
    (x ψ r : ℝ) (n h ell m : ℤ) (hd : etaDenom M τ ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I *
      lowerPhase M τ w (g1BentLowerPoint x ψ r) n h ell m).re =
      -gaussianCoefficient M τ ψ * r ^ 2 +
        (2 * (Real.pi : ℂ) * Complex.I * bentLinear M τ w x ψ n h ell m).re * r +
        (2 * (Real.pi : ℂ) * Complex.I *
          lowerPhase M τ w ((x : ℂ) - Complex.I) n h ell m).re := by
  rw [bent_phase_quadratic M τ w x ψ r n h ell m hd]
  have hq := gaussian_coefficient_exact M τ ψ hd
  change (2 * (Real.pi : ℂ) * Complex.I * bentQuadratic M τ ψ).re = _ at hq
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I * bentQuadratic M τ ψ).re * r ^ 2 +
        (2 * (Real.pi : ℂ) * Complex.I * bentLinear M τ w x ψ n h ell m).re * r +
        (2 * (Real.pi : ℂ) * Complex.I *
          lowerPhase M τ w ((x : ℂ) - Complex.I) n h ell m).re := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I *
        (bentQuadratic M τ ψ * (r : ℂ) ^ 2 +
          bentLinear M τ w x ψ n h ell m * (r : ℂ) +
          lowerPhase M τ w ((x : ℂ) - Complex.I) n h ell m) =
        (2 * (Real.pi : ℂ) * Complex.I * bentQuadratic M τ ψ) * ((r ^ 2 : ℝ) : ℂ) +
          (2 * (Real.pi : ℂ) * Complex.I * bentLinear M τ w x ψ n h ell m) * (r : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I *
            lowerPhase M τ w ((x : ℂ) - Complex.I) n h ell m by push_cast; ring]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    _ = _ := by rw [hq]

lemma moving_reflection_gaussian_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hdom : ∀ v ∈ K, v.1 ∈ modularPhiDomain M)
    (x : ℤ → ℝ) (ψ a : ℝ) (n h ell : ℤ)
    (hgauss : ∀ v ∈ K, a ≤ gaussianCoefficient M v.1 ψ) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ v ∈ K, ∀ m ∈ F, ∀ r : ℝ, 0 ≤ r →
      ‖modularReflectionFactor M (m + 1) n (g1BentLowerPoint (x m) ψ r) v.1 *
        e (g1Exponent M v.1 v.2 (g1BentLowerPoint (x m) ψ r) n h ell m)‖ ≤
          C * Real.exp (-a * r ^ 2 + B * r) := by
  obtain ⟨B, hB, hBl⟩ := G1BilateralRatioTailsAux.finite_compact_bound F K hK
    (fun m v => 2 * (Real.pi : ℂ) * Complex.I *
      bentLinear M v.1 v.2 (x m) ψ n h ell m) (by
        intro m hm v hv
        apply ContinuousAt.continuousWithinAt
        have hd := etaDenom_ne_zero_of_mem M (hdom v hv)
        unfold bentLinear G1RatioTail.complexS
        fun_prop (disch := simp_all))
  obtain ⟨D, hD, hDc⟩ := G1BilateralRatioTailsAux.finite_compact_bound F K hK
    (fun m v => 2 * (Real.pi : ℂ) * Complex.I *
      lowerPhase M v.1 v.2 ((x m : ℝ) - Complex.I) n h ell m) (by
        intro m hm v hv
        apply ContinuousAt.continuousWithinAt
        have hd := etaDenom_ne_zero_of_mem M (hdom v hv)
        unfold lowerPhase modularReflectionPolynomial modularBernoulliTwo g1Exponent etaMobius
        fun_prop (disch := exact hd))
  refine ⟨‖(etaMultiplier M) ^ (-2 : ℤ)‖ * Real.exp D, B,
    mul_pos (norm_pos_iff.mpr (zpow_ne_zero _ (etaMultiplier_ne_zero M hM)))
      (Real.exp_pos D), hB, ?_⟩
  intro v hv m hm r hr
  rw [norm_reflection_times_e]
  change _ * Real.exp ((2 * (Real.pi : ℂ) * Complex.I *
    lowerPhase M v.1 v.2 (g1BentLowerPoint (x m) ψ r) n h ell m).re) ≤ _
  rw [lowerPhase_real_expansion M v.1 v.2 (x m) ψ r n h ell m
    (etaDenom_ne_zero_of_mem M (hdom v hv))]
  have hlin := (Complex.re_le_norm _).trans (hBl m hm v hv)
  have hconst := (Complex.re_le_norm _).trans (hDc m hm v hv)
  have hcoef := hgauss v hv
  have hbexp : -gaussianCoefficient M v.1 ψ * r ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I * bentLinear M v.1 v.2 (x m) ψ n h ell m).re * r +
      (2 * (Real.pi : ℂ) * Complex.I *
        lowerPhase M v.1 v.2 ((x m : ℝ) - Complex.I) n h ell m).re ≤
        D + (-a * r ^ 2 + B * r) := by
    nlinarith [mul_le_mul_of_nonneg_right hlin hr,
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg r)]
  calc
    _ ≤ ‖(etaMultiplier M) ^ (-2 : ℤ)‖ * Real.exp (D + (-a * r ^ 2 + B * r)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbexp) (norm_nonneg _)
    _ = _ := by rw [Real.exp_add]; ring

end SICLean.L4.G1ContinuationHolomorphyAux

namespace SICLean.L4.G1ContinuationHolomorphyAux

lemma sqrt_arg_abs (M : SL(2, ℤ)) (τ : ℂ) (hdom : τ ∈ modularPhiDomain M) :
    |(Complex.sqrt (etaDenom M τ)).arg| = |(etaDenom M τ).arg| / 2 := by
  obtain ⟨hb, hsq, hb0⟩ := modularPhi_sqrt_admissible M τ hdom
  have hab := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb))
  have he : (etaDenom M τ).arg = (Complex.sqrt (etaDenom M τ)).arg +
      (Complex.sqrt (etaDenom M τ)).arg := by
    conv_lhs => rw [← hsq, sq]
    exact Complex.arg_mul hb0 hb0 ⟨by linarith [hab.1], by linarith [hab.2]⟩
  rw [he, show (Complex.sqrt (etaDenom M τ)).arg +
    (Complex.sqrt (etaDenom M τ)).arg = 2 * (Complex.sqrt (etaDenom M τ)).arg by ring,
    abs_mul]
  norm_num

lemma compact_sqrt_family (M : SL(2, ℤ)) (K : Set ℂ) (hK : IsCompact K)
    (hdom : K ⊆ modularPhiDomain M) (β κ : ℝ) (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hangle : β + κ < Real.pi / 2)
    (harg : ∀ τ ∈ K, |(etaDenom M τ).arg| ≤ 2 * β) :
    Sector.Family ((fun τ => Complex.sqrt (etaDenom M τ)) '' K) β κ := by
  refine ⟨?_, ?_, ?_, hβ, hκ, hangle⟩
  · apply hK.image_of_continuousOn
    exact Complex.continuousOn_sqrt.comp (by unfold etaDenom; fun_prop) hdom
  · rintro _ ⟨τ, hτ, rfl⟩
    exact (modularPhi_sqrt_admissible M τ (hdom hτ)).1
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [sqrt_arg_abs M τ (hdom hτ)]
    linarith [harg τ hτ]

lemma local_denom_arg_bound (M : SL(2, ℤ)) (τ : ℂ) (ψ : ℝ)
    (hdom : τ ∈ modularPhiDomain M) (harg : |(etaDenom M τ).arg| < ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall τ ρ ⊆ modularPhiDomain M ∧
      ∀ t ∈ Metric.closedBall τ ρ, |(etaDenom M t).arg| ≤ ψ := by
  have hdc : Continuous (etaDenom M) := by unfold etaDenom; fun_prop
  have hc : ContinuousAt (fun t => |(etaDenom M t).arg|) τ :=
    ((Complex.continuousAt_arg hdom).comp hdc.continuousAt).abs
  have he : ∀ᶠ t in 𝓝 τ, t ∈ modularPhiDomain M ∧ |(etaDenom M t).arg| ≤ ψ := by
    filter_upwards [(modularPhiDomain_isOpen M).mem_nhds hdom,
      hc.eventually (Iio_mem_nhds harg)] with t ht ht'
    exact ⟨ht, ht'.le⟩
  obtain ⟨ρ, hρ, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp he
  exact ⟨ρ, hρ, fun t ht => (hb ht).1, fun t ht => (hb ht).2⟩

end SICLean.L4.G1ContinuationHolomorphyAux

namespace SICLean.L4.G1ContinuationHolomorphyAux

lemma compact_modular_vertical_bounds (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (K : Set ℂ) (hK : IsCompact K)
    (hdom : K ⊆ modularPhiDomain M) (ψ : ℝ) (hψ : 0 < ψ)
    (hψ' : ψ < Real.pi / 4) (harg : ∀ τ ∈ K, |(etaDenom M τ).arg| ≤ ψ) (A : ℝ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ τ ∈ K, ∀ i ∈ F,
      ∀ v : ℂ, ‖v‖ ≤ A → ∀ r : ℝ, R ≤ r →
        ((r : ℂ) * Complex.I + v, τ) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        (-((r : ℂ) * Complex.I + v), τ) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ‖modularPhi M i.1 i.2 ((r : ℂ) * Complex.I + v) τ‖ +
          ‖(modularPhi M i.1 i.2 ((r : ℂ) * Complex.I + v) τ)⁻¹‖ ≤ C ∧
        ‖modularPhi M i.1 i.2 (-((r : ℂ) * Complex.I + v)) τ /
          modularReflectionFactor M i.1 i.2 (-((r : ℂ) * Complex.I + v)) τ‖ +
          ‖modularReflectionFactor M i.1 i.2 (-((r : ℂ) * Complex.I + v)) τ *
            (modularPhi M i.1 i.2 (-((r : ℂ) * Complex.I + v)) τ)⁻¹‖ ≤ C := by
  let δ : ℝ := (Real.pi / 2 - 2 * ψ) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ' : δ ≤ Real.pi / 2 := by dsimp [δ]; linarith [Real.pi_pos]
  have hfam := compact_sqrt_family M K hK hdom (ψ / 2) δ (by positivity) hδ
    (by dsimp [δ]; linarith [Real.pi_pos])
    (fun τ hτ => by linarith [harg τ hτ])
  have hbudget : |(-Complex.I * Complex.I).arg| + 2 * (ψ / 2) + δ + δ ≤ Real.pi / 2 := by
    simp only [neg_mul, Complex.I_mul_I, neg_neg, Complex.arg_one, abs_zero]
    dsimp [δ]
    linarith [Real.pi_pos]
  obtain ⟨Cu, Ru, hCu, hRu, hu⟩ := compact_modular_ray_bound M hM F K hK hdom
    (ψ / 2) δ hfam Complex.I Complex.norm_I δ hδ hδ' hbudget A
  obtain ⟨Cl, Rl, hCl, hRl, hl⟩ := compact_modular_reflected_ray_bound M hM F K hK hdom
    (ψ / 2) δ hfam Complex.I Complex.norm_I δ hδ hδ' hbudget A
  refine ⟨max Cu Cl, max Ru Rl, lt_of_lt_of_le hCu (le_max_left _ _),
    lt_of_lt_of_le hRu (le_max_left _ _), ?_⟩
  intro τ hτ i hi v hv r hr
  have hu' := hu τ hτ i hi v hv r ((le_max_left _ _).trans hr)
  have hl' := hl τ hτ i hi v hv r ((le_max_right _ _).trans hr)
  exact ⟨hu'.1, hl'.1, hu'.2.trans (le_max_left _ _), hl'.2.trans (le_max_right _ _)⟩

lemma reflected_lower_direction_centered_arg (ψ : ℝ) (hψ : 0 < ψ)
    (hψ' : ψ < Real.pi / 4) : (-Complex.I * -g1LowerDirection ψ).arg = ψ := by
  have harg := G1BilateralGeometryAux.reflected_lower_direction_arg ψ hψ hψ'
  have hd : -g1LowerDirection ψ ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [norm_neg, G1BilateralSingleTailsAux.norm_lower_direction]; norm_num)
  rw [Complex.arg_mul (neg_ne_zero.mpr Complex.I_ne_zero) hd (by
    rw [Complex.arg_neg_I, harg]
    constructor <;> linarith [Real.pi_pos]), Complex.arg_neg_I, harg]
  ring

lemma compact_modular_bent_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (K : Set ℂ) (hK : IsCompact K)
    (hdom : K ⊆ modularPhiDomain M) (ψ : ℝ) (hψ : 0 < ψ)
    (hψ' : ψ < Real.pi / 4) (harg : ∀ τ ∈ K, |(etaDenom M τ).arg| ≤ ψ) (A : ℝ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ τ ∈ K, ∀ i ∈ F,
      ∀ x : ℝ, |x| ≤ A → ∀ r : ℝ, R ≤ r →
        (g1BentLowerPoint x ψ r, τ) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ‖modularPhi M i.1 i.2 (g1BentLowerPoint x ψ r) τ /
          modularReflectionFactor M i.1 i.2 (g1BentLowerPoint x ψ r) τ‖ +
          ‖modularReflectionFactor M i.1 i.2 (g1BentLowerPoint x ψ r) τ *
            (modularPhi M i.1 i.2 (g1BentLowerPoint x ψ r) τ)⁻¹‖ ≤ C := by
  let δ : ℝ := (Real.pi / 2 - 2 * ψ) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ' : δ ≤ Real.pi / 2 := by dsimp [δ]; linarith [Real.pi_pos]
  have hfam := compact_sqrt_family M K hK hdom (ψ / 2) δ (by positivity) hδ
    (by dsimp [δ]; linarith [Real.pi_pos])
    (fun τ hτ => by linarith [harg τ hτ])
  have hbudget : |(-Complex.I * -g1LowerDirection ψ).arg| +
      2 * (ψ / 2) + δ + δ ≤ Real.pi / 2 := by
    rw [reflected_lower_direction_centered_arg ψ hψ hψ', abs_of_pos hψ]
    dsimp [δ]
    linarith
  obtain ⟨C, R, hC, hR, hb⟩ := compact_modular_reflected_ray_bound M hM F K hK hdom
    (ψ / 2) δ hfam (-g1LowerDirection ψ)
    (G1BilateralGeometryAux.reflected_lower_direction_norm ψ) δ hδ hδ' hbudget (A + 1)
  refine ⟨C, R, hC, hR, ?_⟩
  intro τ hτ i hi x hx r hr
  have hv : ‖-((x : ℂ) - Complex.I)‖ ≤ A + 1 := by
    rw [norm_neg]
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_right hx 1)
  have he : -((r : ℂ) * -g1LowerDirection ψ + -((x : ℂ) - Complex.I)) =
      g1BentLowerPoint x ψ r := by unfold g1BentLowerPoint; ring
  simpa only [he] using hb τ hτ i hi (-((x : ℂ) - Complex.I)) hv r hr

end SICLean.L4.G1ContinuationHolomorphyAux

namespace SICLean.L4.G1ContinuationHolomorphyAux

open G1BilateralRatioTailsAux G1BilateralGeometry

lemma compact_ratio_one_tail_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (F : Finset ℤ) (K : Set G1Continuation.Parameters)
    (hK : IsCompact K) (hdom : ∀ v ∈ K, v.1 ∈ modularPhiDomain M)
    (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (harg : ∀ v ∈ K, |(etaDenom M v.1).arg| ≤ ψ)
    (lower : Bool) (κ : ℝ)
    (hmargin : ∀ v ∈ K, κ ≤ if lower then
      -(2 * Real.pi * (G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p /
        etaDenom M v.1).re) else
      2 * Real.pi * (G1RatioTail.complexS M v.1 v.2.1 h ell / etaDenom M v.1).re)
    (a b : ℝ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ v ∈ K, ∀ m ∈ F,
      ∀ cross ∈ Icc a b, ∀ t : ℝ, R ≤ |t| →
      (if lower then t ≤ 0 else 0 ≤ t) →
      (g1VerticalPoint cross t, v.1) ∈ modularPhiNonvanishingDomain M (m + 1) n ∧
      (g1VerticalPoint cross t + v.2.2, v.1) ∈ modularPhiNonvanishingDomain M (m + p) n ∧
      ‖UpperWindow.ratioKernel M m n h ell p v.1 v.2.1 v.2.2
        (g1VerticalPoint cross t)‖ ≤ C * Real.exp (-κ * |t|) := by
  obtain ⟨Y, hY⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun v : G1Continuation.Parameters => v.2.2) K by fun_prop)
  let A : ℝ := max |a| |b| + max Y 0
  let KT : Set ℂ := Prod.fst '' K
  have hKT : IsCompact KT := hK.image continuous_fst
  have hdKT : KT ⊆ modularPhiDomain M := by rintro _ ⟨v, hv, rfl⟩; exact hdom v hv
  have haKT : ∀ τ ∈ KT, |(etaDenom M τ).arg| ≤ ψ := by
    rintro _ ⟨v, hv, rfl⟩
    exact harg v hv
  obtain ⟨P, R, hP, hR, hPhi⟩ := compact_modular_vertical_bounds M hM
    (indexFamily F n p) KT hKT hdKT ψ hψ hψ' haKT A
  obtain ⟨B, hB, hphase⟩ := moving_affine_phase_bound M n h ell p F K hK hdom a b lower
  refine ⟨(P * P) * B, R, by positivity, hR, ?_⟩
  intro v hv m hm cross hcross t ht hsign
  have hcrossA : |cross| ≤ max |a| |b| := by
    exact abs_le.mpr ⟨((neg_le_neg (le_max_left |a| |b|)).trans
      (neg_abs_le a)).trans hcross.1,
      hcross.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  have hnormx : ‖(cross : ℂ)‖ ≤ A := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      hcrossA.trans (le_add_of_nonneg_right (le_max_right Y 0))
  have hnormy : ‖(cross : ℂ) + v.2.2‖ ≤ A := by
    exact (norm_add_le _ _).trans (by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        add_le_add hcrossA ((hY v hv).trans (le_max_left Y 0)))
  have hpoint (i : ℤ × ℤ) (hi : i ∈ indexFamily F n p) (u : ℂ) (hu : ‖u‖ ≤ A) :
      ((t : ℂ) * Complex.I + u, v.1) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
      ‖(if lower then modularPhi M i.1 i.2 ((t : ℂ) * Complex.I + u) v.1 /
          modularReflectionFactor M i.1 i.2 ((t : ℂ) * Complex.I + u) v.1
        else modularPhi M i.1 i.2 ((t : ℂ) * Complex.I + u) v.1)‖ +
        ‖(if lower then modularReflectionFactor M i.1 i.2 ((t : ℂ) * Complex.I + u) v.1 *
          (modularPhi M i.1 i.2 ((t : ℂ) * Complex.I + u) v.1)⁻¹
        else (modularPhi M i.1 i.2 ((t : ℂ) * Complex.I + u) v.1)⁻¹)‖ ≤ P := by
    cases lower
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      have hb := hPhi v.1 ⟨v, hv, rfl⟩ i hi u hu |t| ht
      rw [abs_of_nonneg hsign] at hb
      exact ⟨hb.1, hb.2.2.1⟩
    · simp only [↓reduceIte] at hsign ⊢
      have hb := hPhi v.1 ⟨v, hv, rfl⟩ i hi (-u) (by simpa using hu) |t| ht
      have he : -((|t| : ℝ) * Complex.I + -u) = (t : ℂ) * Complex.I + u := by
        rw [abs_of_nonpos hsign]
        push_cast
        ring
      simpa only [he] using And.intro hb.2.1 hb.2.2.2
  have hin : (m + 1, n) ∈ indexFamily F n p :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm)
  have hid : (m + p, n) ∈ indexFamily F n p :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)
  have hn := hpoint (m + 1, n) hin (cross : ℂ) hnormx
  have hd := hpoint (m + p, n) hid ((cross : ℂ) + v.2.2) hnormy
  have hne : etaDenom M v.1 ≠ 0 := etaDenom_ne_zero_of_mem M (hdom v hv)
  let z := g1VerticalPoint cross t
  let Q := modularPhi M (m + 1) n z v.1 / modularPhi M (m + p) n (z + v.2.2) v.1
  let U := modularReflectionFactor M (m + 1) n z v.1 /
    modularReflectionFactor M (m + p) n (z + v.2.2) v.1
  have hn' : (z, v.1) ∈ modularPhiNonvanishingDomain M (m + 1) n := by
    simpa only [z, g1VerticalPoint, add_comm] using hn.1
  have hd' : (z + v.2.2, v.1) ∈ modularPhiNonvanishingDomain M (m + p) n := by
    simpa only [z, g1VerticalPoint, add_assoc, add_left_comm, add_comm] using hd.1
  refine ⟨hn', hd', ?_⟩
  have hq : ‖(if lower then Q / U else Q)‖ ≤ P * P := by
    have hnormn := (le_add_of_nonneg_right (norm_nonneg _)).trans hn.2
    have hnormd := (le_add_of_nonneg_left (norm_nonneg _)).trans hd.2
    have heq : (if lower then Q / U else Q) =
        (if lower then modularPhi M (m + 1) n ((t : ℂ) * Complex.I + cross) v.1 /
            modularReflectionFactor M (m + 1) n ((t : ℂ) * Complex.I + cross) v.1
          else modularPhi M (m + 1) n ((t : ℂ) * Complex.I + cross) v.1) *
        (if lower then modularReflectionFactor M (m + p) n
            ((t : ℂ) * Complex.I + ((cross : ℂ) + v.2.2)) v.1 *
              (modularPhi M (m + p) n ((t : ℂ) * Complex.I + ((cross : ℂ) + v.2.2)) v.1)⁻¹
          else (modularPhi M (m + p) n
            ((t : ℂ) * Complex.I + ((cross : ℂ) + v.2.2)) v.1)⁻¹) := by
      cases lower <;> dsimp [Q, U, z, g1VerticalPoint] <;>
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, add_comm, add_left_comm, add_assoc] <;> ring
    rw [heq, norm_mul]
    exact mul_le_mul hnormn hnormd (norm_nonneg _) hP.le
  let S := (if lower then G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p
    else G1RatioTail.complexS M v.1 v.2.1 h ell) / etaDenom M v.1
  have hker : ‖G1RatioTail.complexKernel M v.1 v.2.1 v.2.2 n h ell p m z‖ =
      ‖(if lower then Q / U else Q)‖ *
        ‖e (S * z + phaseConstant M v.1 v.2.1 v.2.2 n h ell p m lower)‖ := by
    cases lower
    · rw [kernel_eq, norm_mul, G1RatioTail.exponent_affine M v.1 v.2.1 z n h ell m hne]
      simp only [S, Q, phaseConstant, Bool.false_eq_true, ↓reduceIte, zero_add]
    · rw [norm_lower_kernel M hM v.1 v.2.1 v.2.2 z n h ell p m (hdom v hv),
        lower_phase_affine M v.1 v.2.1 v.2.2 z n h ell p m hne]
      rfl
  have hexponent : -(2 * Real.pi * S.re) * t ≤ -κ * |t| := by
    have hmarg := hmargin v hv
    cases lower
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign hmarg
      rw [abs_of_nonneg hsign]
      dsimp only [S]
      simpa only [Bool.false_eq_true, ↓reduceIte, neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right hmarg hsign)
    · simp only [↓reduceIte] at hsign hmarg
      rw [abs_of_nonpos hsign]
      dsimp only [S]
      simp only [↓reduceIte]
      nlinarith [mul_le_mul_of_nonpos_right hmarg hsign]
  change ‖G1RatioTail.complexKernel M v.1 v.2.1 v.2.2 n h ell p m z‖ ≤ _
  rw [hker]
  calc
    _ ≤ (P * P) * (B * Real.exp (-(2 * Real.pi * S.re) * t)) :=
      mul_le_mul hq (hphase v hv m hm cross hcross t) (norm_nonneg _) (by positivity)
    _ ≤ (P * P) * (B * Real.exp (-κ * |t|)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexponent) hB.le) (by positivity)
    _ = _ := by ring

lemma compact_ratio_two_tail_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (F : Finset ℤ) (K : Set G1Continuation.Parameters)
    (hK : IsCompact K) (hdom : ∀ v ∈ K, v.1 ∈ modularPhiDomain M)
    (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (harg : ∀ v ∈ K, |(etaDenom M v.1).arg| ≤ ψ) (κ : ℝ) (hκ : 0 < κ)
    (hupper : ∀ v ∈ K, κ ≤ 2 * Real.pi *
      (G1RatioTail.complexS M v.1 v.2.1 h ell / etaDenom M v.1).re)
    (hlower : ∀ v ∈ K, κ ≤ -(2 * Real.pi *
      (G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p / etaDenom M v.1).re))
    (a b : ℝ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ v ∈ K, ∀ m ∈ F,
      ∀ cross ∈ Icc a b, ∀ t : ℝ, R ≤ |t| →
      (g1VerticalPoint cross t, v.1) ∈ modularPhiNonvanishingDomain M (m + 1) n ∧
      (g1VerticalPoint cross t + v.2.2, v.1) ∈ modularPhiNonvanishingDomain M (m + p) n ∧
      ‖UpperWindow.ratioKernel M m n h ell p v.1 v.2.1 v.2.2
        (g1VerticalPoint cross t)‖ ≤ C * Real.exp (-κ * |t|) := by
  obtain ⟨Cu, Ru, hCu, hRu, hu⟩ := compact_ratio_one_tail_bound M hM n h ell p
    F K hK hdom ψ hψ hψ' harg false κ hupper a b
  obtain ⟨Cl, Rl, hCl, hRl, hl⟩ := compact_ratio_one_tail_bound M hM n h ell p
    F K hK hdom ψ hψ hψ' harg true κ hlower a b
  refine ⟨max Cu Cl, max Ru Rl, lt_of_lt_of_le hCu (le_max_left _ _),
    lt_of_lt_of_le hRu (le_max_left _ _), ?_⟩
  intro v hv m hm cross hcross t ht
  by_cases ht0 : 0 ≤ t
  · obtain ⟨hn, hd, hb⟩ := hu v hv m hm cross hcross t ((le_max_left _ _).trans ht) ht0
    exact ⟨hn, hd, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
  · obtain ⟨hn, hd, hb⟩ := hl v hv m hm cross hcross t ((le_max_right _ _).trans ht)
      (le_of_not_ge ht0)
    exact ⟨hn, hd, hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)⟩




open G1BilateralGeometry G1BilateralSingleTails G1BilateralSingleTailsAux

lemma compact_single_two_tail_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (F : Finset ℤ) (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hdom : ∀ v ∈ K, v.1 ∈ modularPhiDomain M)
    (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (harg : ∀ v ∈ K, |(etaDenom M v.1).arg| ≤ ψ) (κ a : ℝ)
    (hupper : ∀ v ∈ K, κ ≤ 2 * Real.pi *
      (G1RatioTail.complexS M v.1 v.2 h ell / etaDenom M v.1).re)
    (hgauss : ∀ v ∈ K, a ≤ gaussianCoefficient M v.1 ψ)
    (cross : ℤ → ℝ) :
    ∃ C B R : ℝ, 0 < C ∧ 0 < B ∧ 0 < R ∧
      ∀ v ∈ K, ∀ m ∈ F,
        (∀ t : ℝ, R ≤ t → ‖g1VerticalPullback
          (UpperWindow.singleKernel M m n h ell v.1 v.2) (cross m) t‖ ≤
            C * Real.exp (-κ * t)) ∧
        (∀ r : ℝ, R ≤ r → ‖g1BentLowerPullback
          (UpperWindow.singleKernel M m n h ell v.1 v.2) (cross m) ψ r‖ ≤
            C * Real.exp (-a * r ^ 2 + B * r)) := by
  obtain ⟨A, hA, hcross⟩ := finite_real_bounds F cross
  let KT : Set ℂ := Prod.fst '' K
  have hKT : IsCompact KT := hK.image continuous_fst
  have hdKT : KT ⊆ modularPhiDomain M := by
    rintro _ ⟨v, hv, rfl⟩
    exact hdom v hv
  have haKT : ∀ τ ∈ KT, |(etaDenom M τ).arg| ≤ ψ := by
    rintro _ ⟨v, hv, rfl⟩
    exact harg v hv
  let FI : Finset (ℤ × ℤ) := F.image (fun m => (m + 1, n))
  have hFI : ∀ m ∈ F, (m + 1, n) ∈ FI := fun m hm => Finset.mem_image_of_mem _ hm
  obtain ⟨Cnu, Ru, hCnu, hRu, hnu⟩ := compact_modular_vertical_bounds M hM
    FI KT hKT hdKT ψ hψ hψ' haKT A
  obtain ⟨Cnl, Rl, hCnl, hRl, hnl⟩ := compact_modular_bent_bound M hM
    FI KT hKT hdKT ψ hψ hψ' haKT A
  obtain ⟨D, hD, hDc⟩ := G1BilateralRatioTailsAux.finite_compact_bound F K hK
    (fun m v => 2 * (Real.pi : ℂ) * Complex.I *
      g1Exponent M v.1 v.2 (cross m : ℂ) n h ell m) (by
        intro m hm v hv
        apply ContinuousAt.continuousWithinAt
        have hd := etaDenom_ne_zero_of_mem M (hdom v hv)
        unfold g1Exponent etaMobius
        fun_prop (disch := exact hd))
  obtain ⟨Cg, B, hCg, hB, hg⟩ := moving_reflection_gaussian_bound M hM
    F K hK hdom cross ψ a n h ell hgauss
  let Cu := Cnu * Real.exp D
  let Cl := Cnl * Cg
  let C := max Cu Cl
  let R := max Ru Rl
  have hCu : 0 < Cu := mul_pos hCnu (Real.exp_pos D)
  have hCl : 0 < Cl := mul_pos hCnl hCg
  have hC : 0 < C := hCu.trans_le (le_max_left _ _)
  have hR : 0 < R := hRu.trans_le (le_max_left _ _)
  refine ⟨C, B, R, hC, hB, hR, ?_⟩
  intro v hv m hm
  have hvT : v.1 ∈ KT := ⟨v, hv, rfl⟩
  have hcm : |cross m| ≤ A := abs_le.mpr (hcross m hm)
  have hden : etaDenom M v.1 ≠ 0 := etaDenom_ne_zero_of_mem M (hdom v hv)
  have hkernel : ∀ z : ℂ, UpperWindow.singleKernel M m n h ell v.1 v.2 z =
      modularPhi M (m + 1) n z v.1 * e (g1Exponent M v.1 v.2 z n h ell m) := fun _ => rfl
  constructor
  · intro t ht
    have htu : Ru ≤ t := (le_max_left _ _).trans ht
    have ht0 : 0 ≤ t := hR.le.trans ht
    let z := g1VerticalPoint (cross m) t
    have hpoint : (t : ℂ) * Complex.I + (cross m : ℂ) = z := by
      dsimp [z, g1VerticalPoint]
      ring
    have hvo : ‖(cross m : ℂ)‖ ≤ A := by simpa using hcm
    have hb := hnu v.1 hvT (m + 1, n) (hFI m hm) (cross m : ℂ) hvo t htu
    have hphi : ‖modularPhi M (m + 1) n z v.1‖ ≤ Cnu := by
      have hb' : ‖modularPhi M (m + 1) n z v.1‖ +
          ‖(modularPhi M (m + 1) n z v.1)⁻¹‖ ≤ Cnu := by
        simpa only [hpoint] using hb.2.2.1
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans hb'
    have hc := (Complex.re_le_norm _).trans (hDc m hm v hv)
    have hphase : -(2 * Real.pi *
        (G1RatioTail.complexS M v.1 v.2 h ell / etaDenom M v.1).re) * t +
        (2 * (Real.pi : ℂ) * Complex.I *
          g1Exponent M v.1 v.2 (cross m : ℂ) n h ell m).re ≤ D + (-κ * t) := by
      nlinarith [mul_le_mul_of_nonneg_right (hupper v hv) ht0]
    calc
      _ = ‖modularPhi M (m + 1) n z v.1‖ *
          ‖e (g1Exponent M v.1 v.2 z n h ell m)‖ := by
        simp only [g1VerticalPullback, hkernel, norm_mul, Complex.norm_I, mul_one, z]
      _ ≤ Cnu * Real.exp (D + (-κ * t)) := by
        rw [norm_vertical_e M v.1 v.2 (cross m) t n h ell m hden]
        exact mul_le_mul hphi (Real.exp_le_exp.mpr hphase) (Real.exp_pos _).le hCnu.le
      _ = Cu * Real.exp (-κ * t) := by rw [Real.exp_add]; ring
      _ ≤ C * Real.exp (-κ * t) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · intro r hr
    have hrl : Rl ≤ r := (le_max_right _ _).trans hr
    have hr0 : 0 ≤ r := hR.le.trans hr
    let z := g1BentLowerPoint (cross m) ψ r
    let Af := modularReflectionFactor M (m + 1) n z v.1
    have hAf : Af ≠ 0 :=
      (ModularSector.reflectionFactor_joint_unit M hM (m + 1) n z v.1 (hdom v hv)).2
    have hb := hnl v.1 hvT (m + 1, n) (hFI m hm) (cross m) hcm r hrl
    have hphi : ‖modularPhi M (m + 1) n z v.1 / Af‖ ≤ Cnl :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans hb.2
    have hker : UpperWindow.singleKernel M m n h ell v.1 v.2 z =
        (modularPhi M (m + 1) n z v.1 / Af) *
          (Af * e (g1Exponent M v.1 v.2 z n h ell m)) := by
      rw [hkernel, ← mul_assoc, div_mul_cancel₀ _ hAf]
    have hgaussbound := hg v hv m hm r hr0
    calc
      _ = ‖UpperWindow.singleKernel M m n h ell v.1 v.2 z‖ := by
        simp only [g1BentLowerPullback, norm_mul, norm_lower_direction, mul_one, z]
      _ = ‖modularPhi M (m + 1) n z v.1 / Af‖ *
          ‖Af * e (g1Exponent M v.1 v.2 z n h ell m)‖ := by rw [hker, norm_mul]
      _ ≤ Cnl * (Cg * Real.exp (-a * r ^ 2 + B * r)) :=
        mul_le_mul hphi hgaussbound (norm_nonneg _) hCnl.le
      _ = Cl * Real.exp (-a * r ^ 2 + B * r) := by ring
      _ ≤ C * Real.exp (-a * r ^ 2 + B * r) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le


end SICLean.L4.G1ContinuationHolomorphyAux
