import SICLean.L4.ModularClusterRegularity
import SICLean.L4.FaddeevContinuationAux
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

/-!
# Auxiliary analytic facts for the fixed cluster circles

The continuous spectral parameters are allowed to vary jointly. All facts
below concern the specified kernel on its explicit regular locus.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology MatrixGroups Interval

namespace SICLean.L4.ModularClusterIntegralsAux

open ModularCluster

set_option maxHeartbeats 800000 in
/-- Analytic pullback of the actual kernel, with all four complex inputs
varying and with the discrete data fixed. -/
theorem analyticAt_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData)
    {z τ w y : E → ℂ} {x : E}
    (hz : AnalyticAt ℂ z x) (hτ : AnalyticAt ℂ τ x)
    (hw : AnalyticAt ℂ w x) (hy : AnalyticAt ℂ y x)
    (hsafe : (z x, τ x) ∈ regularDomain M (withParameters k (w x) (y x))) :
    AnalyticAt ℂ (fun q => ModularCluster.kernel M (withParameters k (w q) (y q)) (z q) (τ q)) x := by
  have hnum : AnalyticAt ℂ (fun q => modularPhi M (k.m + 1) k.n (z q) (τ q)) x :=
    (modularPhi_joint_analytic_no_poles M hM (k.m + 1) k.n (z x, τ x)
      ⟨hsafe.1, hsafe.2.1⟩).comp (f := fun q => (z q, τ q)) (hz.prod hτ)
  have hinv : AnalyticAt ℂ
      (fun q => if k.ratio = true then
        (modularPhi M (k.m + k.p) k.n (z q + y q) (τ q))⁻¹ else 1) x := by
    split_ifs with hratio
    · exact (inversePhi_joint_analytic M hM (k.m + k.p) k.n (z x + y x, τ x)
        ⟨hsafe.1, hsafe.2.2 hratio⟩).comp (f := fun q => (z q + y q, τ q))
          ((hz.add hy).prod hτ)
    · exact analyticAt_const
  have hden : AnalyticAt ℂ (fun q => etaDenom M (τ q)) x := by
    unfold etaDenom
    exact (analyticAt_const.mul hτ).add analyticAt_const
  have hne : etaDenom M (τ x) ≠ 0 := Complex.slitPlane_ne_zero hsafe.1
  have hmob : AnalyticAt ℂ (fun q => etaMobius M (τ q)) x := by
    unfold etaMobius
    exact ((analyticAt_const.mul hτ).add analyticAt_const).div hden hne
  have hphase : AnalyticAt ℂ
      (fun q => phase M (withParameters k (w q) (y q)) (z q) (τ q)) x := by
    dsimp only [phase, withParameters]
    exact ((((((analyticAt_const.mul hz).sub analyticAt_const).add
      (hden.mul analyticAt_const)).mul hw).div hden hne).add
      (analyticAt_const.mul (hz.add (analyticAt_const.mul hτ)))).add
        (analyticAt_const.mul ((hz.div hden hne).add (analyticAt_const.mul hmob)))
  have he : AnalyticAt ℂ
      (fun q => e (phase M (withParameters k (w q) (y q)) (z q) (τ q))) x := by
    unfold e
    fun_prop
  exact (hnum.mul hinv).mul he

/-- A compact path gives a uniform bound for the parameter derivative.
This is the differentiation-under-the-integral step; it applies to a
finite dimensional complex parameter space with any continuous path. -/
theorem differentiableOn_integral_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {F : E × ℂ → ℂ} {p : E} {ρ a b : ℝ} {c : ℝ → ℂ}
    (hc : Continuous c) (hab : a ≤ b)
    (hF : ∀ q ∈ Metric.closedBall p ρ, ∀ t ∈ Icc a b,
      AnalyticAt ℂ F (q, c t)) :
    DifferentiableOn ℂ (fun q => ∫ t in a..b, F (q, c t)) (Metric.ball p ρ) := by
  let D : E → ℝ → E →L[ℂ] ℂ := fun q t =>
    (fderiv ℂ F (q, c t)).comp (ContinuousLinearMap.inl ℂ E ℂ)
  have hmap : Continuous (fun v : E × ℝ => (v.1, c v.2)) :=
    continuous_fst.prodMk (hc.comp continuous_snd)
  have hD : ContinuousOn (fun v : E × ℝ => D v.1 v.2)
      (Metric.closedBall p ρ ×ˢ Icc a b) := by
    intro v hv
    have hd : ContinuousAt (fderiv ℂ F) (v.1, c v.2) :=
      (hF v.1 hv.1 v.2 hv.2).contDiffAt (n := 1) |>.continuousAt_fderiv (by norm_num)
    exact ((hd.comp (f := fun v : E × ℝ => (v.1, c v.2)) (x := v)
      hmap.continuousAt).clm_comp continuousAt_const).continuousWithinAt
  obtain ⟨B, hB⟩ := ((isCompact_closedBall p ρ).prod isCompact_Icc).exists_bound_of_continuousOn hD
  have hsub : ∀ t ∈ Ι a b, t ∈ Icc a b := by
    intro t ht
    rw [uIoc_of_le hab] at ht
    exact Ioc_subset_Icc_self ht
  have hcont (q : E) (hq : q ∈ Metric.closedBall p ρ) :
      ContinuousOn (fun t => F (q, c t)) (Icc a b) := by
    intro t ht
    exact ((hF q hq t ht).continuousAt.comp (f := fun t : ℝ => (q, c t))
      ((show ContinuousAt (fun _ : ℝ => q) t from continuousAt_const).prodMk
        hc.continuousAt)).continuousWithinAt
  have hDcont (q : E) (hq : q ∈ Metric.closedBall p ρ) :
      ContinuousOn (D q) (Icc a b) :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hq, ht⟩)
  intro q hq
  have hqc : q ∈ Metric.closedBall p ρ := Metric.ball_subset_closedBall hq
  have hnb : Metric.ball p ρ ∈ 𝓝 q := Metric.isOpen_ball.mem_nhds hq
  have hderiv := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (μ := volume) (F := fun q t => F (q, c t)) (F' := D)
    (bound := fun _ => B) hnb
    (by
      filter_upwards [hnb] with q' hq'
      exact ((hcont q' (Metric.ball_subset_closedBall hq')).mono hsub).aestronglyMeasurable
        measurableSet_uIoc)
    ((hcont q hqc).intervalIntegrable_of_Icc hab)
    (((hDcont q hqc).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall (fun t ht q' hq' =>
      hB (q', t) ⟨Metric.ball_subset_closedBall hq', hsub t ht⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun t ht q' hq' => by
      have hm : HasFDerivAt (fun u : E => (u, c t))
          (ContinuousLinearMap.inl ℂ E ℂ) q' :=
        (hasFDerivAt_id q').prodMk (hasFDerivAt_const (c t) q')
      exact (hF q' (Metric.ball_subset_closedBall hq') t (hsub t ht)).differentiableAt.hasFDerivAt.comp q' hm))
  exact hderiv.differentiableAt.differentiableWithinAt

/-! The three-variable Cauchy bridge, with the product maximum norm. -/

open SICLean.L4.JointAnalytic
attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

abbrev Torus3 := Theta × Theta × Theta

def angleMeasure3 : Measure Torus3 :=
  (volume : Measure Theta).prod angleMeasure

instance : IsFiniteMeasure angleMeasure3 := by
  unfold angleMeasure3
  infer_instance

def integralCLM3 : C(Torus3, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 angleMeasure3 ℂ)

lemma integralCLM3_apply (F : C(Torus3, ℂ)) :
    integralCLM3 F = ∫ t, F t ∂angleMeasure3 := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 angleMeasure3 ℂ F) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp angleMeasure3 F)

lemma integral_theta_triple (g : ℝ → ℝ → ℝ → ℂ)
    (hg : Continuous (fun t : Torus3 => g t.1 t.2.1 t.2.2)) :
    (∫ t : Torus3, g t.1 t.2.1 t.2.2 ∂angleMeasure3) =
      ∫ a : ℝ in 0..2 * Real.pi,
        ∫ b : ℝ in 0..2 * Real.pi,
          ∫ c : ℝ in 0..2 * Real.pi, g a b c := by
  rw [show angleMeasure3 = (volume : Measure Theta).prod angleMeasure from rfl]
  have hgi : Integrable (fun t : Torus3 => g t.1 t.2.1 t.2.2)
      ((volume : Measure Theta).prod angleMeasure) :=
    continuousMap_integrable _ ⟨_, hg⟩
  rw [integral_prod (fun t : Torus3 => g t.1 t.2.1 t.2.2) hgi]
  have hinner (a : Theta) :
      (∫ t : Theta × Theta, g a t.1 t.2 ∂angleMeasure) =
        ∫ b : ℝ in 0..2 * Real.pi,
          ∫ c : ℝ in 0..2 * Real.pi, g a b c := by
    apply integral_theta_prod
    exact hg.comp (continuous_const.prodMk continuous_id)
  simp_rw [hinner]
  rw [integral_subtype measurableSet_Icc
    (fun a : ℝ => ∫ b : ℝ in 0..2 * Real.pi,
      ∫ c : ℝ in 0..2 * Real.pi, g a b c)]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le]

open Metric in
lemma triple_mem_closedBall {p : ℂ × ℂ × ℂ} {r : ℝ} {a : ℂ} {b : ℂ × ℂ}
    (ha : a ∈ closedBall p.1 r) (hb : b ∈ closedBall p.2 r) :
    (a, b) ∈ closedBall p r := by
  simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using And.intro ha hb

open Metric in
lemma triple_cauchy {f : ℂ × ℂ × ℂ → ℂ} {p q : ℂ × ℂ × ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall p r))
    (hr : 0 < r) (hq : q ∈ ball p r) :
    (∮ a in C(p.1, r), ∮ b in C(p.2.1, r), ∮ c in C(p.2.2, r),
      (a - q.1)⁻¹ * (b - q.2.1)⁻¹ * (c - q.2.2)⁻¹ * f (a, b, c)) =
        (2 * (Real.pi : ℂ) * I) ^ 3 * f q := by
  have hq' : q.1 ∈ ball p.1 r ∧ q.2 ∈ ball p.2 r := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
  have h₂ (a : ℂ) (ha : a ∈ closedBall p.1 r) :
      (∮ b in C(p.2.1, r), ∮ c in C(p.2.2, r),
        (b - q.2.1)⁻¹ * (c - q.2.2)⁻¹ * f (a, b, c)) =
          (2 * (Real.pi : ℂ) * I) ^ 2 * f (a, q.2) := by
    have hs : DifferentiableOn ℂ (fun b : ℂ × ℂ => f (a, b)) (closedBall p.2 r) :=
      hf.comp ((differentiableOn_const a).prodMk differentiableOn_id)
        (fun b hb => triple_mem_closedBall ha hb)
    exact double_cauchy (f := fun b : ℂ × ℂ => f (a, b))
      (p := p.2) (q := q.2) (r := r) hs hr hq'.2
  have h₁ :
      (∮ a in C(p.1, r), (a - q.1)⁻¹ * f (a, q.2)) =
        (2 * (Real.pi : ℂ) * I) * f q := by
    have hs : DifferentiableOn ℂ (fun a : ℂ => f (a, q.2)) (closedBall p.1 r) :=
      hf.comp (differentiableOn_id.prodMk (differentiableOn_const q.2))
        (fun a ha => triple_mem_closedBall ha (ball_subset_closedBall hq'.2))
    simpa only [smul_eq_mul, Prod.mk.eta] using hs.circleIntegral_sub_inv_smul hq'.1
  calc
    _ = ∮ a in C(p.1, r), (a - q.1)⁻¹ *
        ((2 * (Real.pi : ℂ) * I) ^ 2 * f (a, q.2)) := by
      apply circleIntegral.integral_congr hr.le
      intro a ha
      change (∮ b in C(p.2.1, r), ∮ c in C(p.2.2, r),
        (a - q.1)⁻¹ * (b - q.2.1)⁻¹ * (c - q.2.2)⁻¹ * f (a, b, c)) =
          (a - q.1)⁻¹ * ((2 * (Real.pi : ℂ) * I) ^ 2 * f (a, q.2))
      rw [← h₂ a (sphere_subset_closedBall ha), ← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr hr.le
      intro b hb
      dsimp only
      rw [← circleIntegral.integral_const_mul]
      congr 1
      funext c
      ring
    _ = (2 * (Real.pi : ℂ) * I) ^ 2 *
        (∮ a in C(p.1, r), (a - q.1)⁻¹ * f (a, q.2)) := by
      rw [← circleIntegral.integral_const_mul]
      congr 1
      funext a
      ring
    _ = (2 * (Real.pi : ℂ) * I) ^ 3 * f q := by rw [h₁]; ring

lemma kernel_analytic3 {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (G₁ G₂ G₃ F : C(T, ℂ)) (p : ℂ × ℂ × ℂ)
    (h₁ : ∀ t, G₁ t - p.1 ≠ 0) (h₂ : ∀ t, G₂ t - p.2.1 ≠ 0)
    (h₃ : ∀ t, G₃ t - p.2.2 ≠ 0) :
    AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ =>
      Ring.inverse (G₁ - ContinuousMap.const T q.1) *
      Ring.inverse (G₂ - ContinuousMap.const T q.2.1) *
      Ring.inverse (G₃ - ContinuousMap.const T q.2.2) * F) p := by
  have hu₁ : IsUnit (G₁ - ContinuousMap.const T p.1) :=
    (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr h₁
  have a₁ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => G₁ - ContinuousMap.const T q.1) p :=
    analyticAt_const.sub
      (((ContinuousLinearMap.const ℂ T).analyticAt p.1).comp analyticAt_fst)
  have i₁ : AnalyticAt ℂ Ring.inverse (G₁ - ContinuousMap.const T p.1) := by
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hu₁.unit)
  have c₁ : AnalyticAt ℂ
      (fun q : ℂ × ℂ × ℂ => Ring.inverse (G₁ - ContinuousMap.const T q.1)) p :=
    i₁.comp (f := fun q : ℂ × ℂ × ℂ => G₁ - ContinuousMap.const T q.1) a₁
  have c₂₃ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ =>
      Ring.inverse (G₂ - ContinuousMap.const T q.2.1) *
      Ring.inverse (G₃ - ContinuousMap.const T q.2.2) * F) p :=
    (kernel_analytic G₂ G₃ F p.2 h₂ h₃).comp analyticAt_snd
  have hm : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ =>
      Ring.inverse (G₁ - ContinuousMap.const T q.1) *
        (Ring.inverse (G₂ - ContinuousMap.const T q.2.1) *
          Ring.inverse (G₃ - ContinuousMap.const T q.2.2) * F)) p := c₁.mul c₂₃
  apply hm.congr
  filter_upwards [] with q
  simp only [mul_assoc]

open Metric in
theorem analyticAt_of_differentiableOn_closedBall_three {f : ℂ × ℂ × ℂ → ℂ}
    {p : ℂ × ℂ × ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall p r)) (hr : 0 < r) : AnalyticAt ℂ f p := by
  let G₁ : C(Torus3, ℂ) := ⟨fun t => circleMap p.1 r t.1, by fun_prop⟩
  let G₂ : C(Torus3, ℂ) := ⟨fun t => circleMap p.2.1 r t.2.1, by fun_prop⟩
  let G₃ : C(Torus3, ℂ) := ⟨fun t => circleMap p.2.2 r t.2.2, by fun_prop⟩
  have hF : Continuous (fun t : Torus3 => f (G₁ t, G₂ t, G₃ t)) :=
    hf.continuousOn.comp_continuous
      (G₁.continuous.prodMk (G₂.continuous.prodMk G₃.continuous))
      (fun t => triple_mem_closedBall
        (sphere_subset_closedBall (circleMap_mem_sphere p.1 hr.le t.1))
        (pair_mem_closedBall
          (sphere_subset_closedBall (circleMap_mem_sphere p.2.1 hr.le t.2.1))
          (sphere_subset_closedBall (circleMap_mem_sphere p.2.2 hr.le t.2.2))))
  let H : C(Torus3, ℂ) :=
    ⟨fun t => f (G₁ t, G₂ t, G₃ t) * deriv (circleMap p.1 r) t.1 *
      deriv (circleMap p.2.1 r) t.2.1 * deriv (circleMap p.2.2 r) t.2.2,
      by
        apply ((hF.mul ?_).mul ?_).mul ?_ <;>
          simp only [deriv_circleMap] <;> fun_prop⟩
  let K : (ℂ × ℂ × ℂ) → C(Torus3, ℂ) := fun q =>
    Ring.inverse (G₁ - ContinuousMap.const _ q.1) *
    Ring.inverse (G₂ - ContinuousMap.const _ q.2.1) *
    Ring.inverse (G₃ - ContinuousMap.const _ q.2.2) * H
  have h₁ (q : ℂ × ℂ × ℂ) (hq : q ∈ ball p r) :
      IsUnit (G₁ - ContinuousMap.const _ q.1) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro t
    change circleMap p.1 r t.1 - q.1 ≠ 0
    apply sub_ne_zero.mpr
    apply circleMap_ne_mem_ball
    have hq' : dist q.1 p.1 < r ∧ dist q.2 p.2 < r := by
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
    exact hq'.1
  have h₂ (q : ℂ × ℂ × ℂ) (hq : q ∈ ball p r) :
      IsUnit (G₂ - ContinuousMap.const _ q.2.1) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro t
    change circleMap p.2.1 r t.2.1 - q.2.1 ≠ 0
    apply sub_ne_zero.mpr
    apply circleMap_ne_mem_ball
    have hq' : dist q.1 p.1 < r ∧ dist q.2.1 p.2.1 < r ∧ dist q.2.2 p.2.2 < r := by
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
    exact hq'.2.1
  have h₃ (q : ℂ × ℂ × ℂ) (hq : q ∈ ball p r) :
      IsUnit (G₃ - ContinuousMap.const _ q.2.2) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro t
    change circleMap p.2.2 r t.2.2 - q.2.2 ≠ 0
    apply sub_ne_zero.mpr
    apply circleMap_ne_mem_ball
    have hq' : dist q.1 p.1 < r ∧ dist q.2.1 p.2.1 < r ∧ dist q.2.2 p.2.2 < r := by
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
    exact hq'.2.2
  have hK : AnalyticAt ℂ K p := by
    apply kernel_analytic3
    · intro t
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mp (h₁ p (mem_ball_self hr)) t
    · intro t
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mp (h₂ p (mem_ball_self hr)) t
    · intro t
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mp (h₃ p (mem_ball_self hr)) t
  have hL : AnalyticAt ℂ (fun q => integralCLM3 (K q)) p :=
    (integralCLM3.analyticAt (K p)).comp (f := K) hK
  have hA : AnalyticAt ℂ
      (fun q => ((2 * (Real.pi : ℂ) * I) ^ 3)⁻¹ * integralCLM3 (K q)) p :=
    analyticAt_const.mul hL
  apply hA.congr
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with q hq
  let g : ℝ → ℝ → ℝ → ℂ := fun a b c =>
    deriv (circleMap p.1 r) a * (deriv (circleMap p.2.1 r) b *
      (deriv (circleMap p.2.2 r) c *
        ((circleMap p.1 r a - q.1)⁻¹ * (circleMap p.2.1 r b - q.2.1)⁻¹ *
          (circleMap p.2.2 r c - q.2.2)⁻¹ *
            f (circleMap p.1 r a, circleMap p.2.1 r b, circleMap p.2.2 r c))))
  have hKe (t : Torus3) : K q t = g t.1 t.2.1 t.2.2 := by
    dsimp only [K]
    simp only [ContinuousMap.mul_apply]
    rw [ringInverse_apply _ (h₁ q hq), ringInverse_apply _ (h₂ q hq),
      ringInverse_apply _ (h₃ q hq)]
    dsimp [G₁, G₂, G₃, H, g]
    ring
  have hcontg : Continuous (fun t : Torus3 => g t.1 t.2.1 t.2.2) := by
    rw [show (fun t : Torus3 => g t.1 t.2.1 t.2.2) = K q from (funext hKe).symm]
    exact (K q).continuous
  have hrepr : integralCLM3 (K q) =
      ∮ a in C(p.1, r), ∮ b in C(p.2.1, r), ∮ c in C(p.2.2, r),
        (a - q.1)⁻¹ * (b - q.2.1)⁻¹ * (c - q.2.2)⁻¹ * f (a, b, c) := by
    rw [integralCLM3_apply]
    simp_rw [hKe]
    rw [integral_theta_triple g hcontg]
    dsimp only [g]
    unfold circleIntegral
    simp only [smul_eq_mul]
    congr 1
    funext a
    simp_rw [intervalIntegral.integral_const_mul]
  rw [hrepr, triple_cauchy hf hr hq]
  simp

end SICLean.L4.ModularClusterIntegralsAux
