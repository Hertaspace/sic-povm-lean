import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

set_option autoImplicit false

/-!
# A two-variable complex analytic bridge

The domain carries the product (maximum) norm. Two applications of the one-variable Cauchy formula
represent a holomorphic function by a continuous linear integral of an analytic map into a Banach
algebra of continuous functions on the two circles. This supplies the multivariable bridge that the
one-variable `DifferentiableOn.analyticOnNhd` does not provide.
-/

noncomputable section

open Set Complex Filter MeasureTheory
open scoped Topology

namespace SICLean.L4.JointAnalytic

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

abbrev Theta := ↥(Set.Icc (0 : ℝ) (2 * Real.pi))

instance : IsFiniteMeasure (volume : Measure Theta) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    simp
    finiteness

def angleMeasure : Measure (Theta × Theta) :=
  (volume : Measure Theta).prod (volume : Measure Theta)

instance : IsFiniteMeasure angleMeasure := by
  unfold angleMeasure
  infer_instance

def integralCLM : C(Theta × Theta, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 angleMeasure ℂ)

lemma integralCLM_apply (F : C(Theta × Theta, ℂ)) :
    integralCLM F = ∫ t, F t ∂angleMeasure := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 angleMeasure ℂ F) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp angleMeasure F)

lemma continuousMap_integrable {T : Type*} [TopologicalSpace T]
    [MeasurableSpace T] [BorelSpace T] [CompactSpace T]
    (μ : Measure T) [IsFiniteMeasure μ] (F : C(T, ℂ)) :
    Integrable F μ := by
  exact (L1.integrable_coeFn (ContinuousMap.toLp 1 μ ℂ F)).congr
    (ContinuousMap.coeFn_toLp μ F)

lemma integral_theta_prod (g : ℝ → ℝ → ℂ)
    (hg : Continuous (fun t : Theta × Theta => g t.1 t.2)) :
    (∫ t : Theta × Theta, g t.1 t.2 ∂angleMeasure) =
      ∫ a : ℝ in 0..2 * Real.pi,
        ∫ b : ℝ in 0..2 * Real.pi, g a b := by
  rw [show angleMeasure =
    (volume : Measure Theta).prod (volume : Measure Theta) from rfl]
  have hgi : Integrable (fun t : Theta × Theta => g t.1 t.2)
      ((volume : Measure Theta).prod (volume : Measure Theta)) :=
    continuousMap_integrable _ ⟨_, hg⟩
  rw [integral_prod (fun t : Theta × Theta => g t.1 t.2) hgi]
  simp_rw [integral_subtype measurableSet_Icc]
  rw [integral_subtype measurableSet_Icc
    (fun a : ℝ => ∫ b in Icc (0 : ℝ) (2 * Real.pi), g a b)]
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le]

lemma ringInverse_apply {T : Type*} [TopologicalSpace T]
    (a : C(T, ℂ)) (ha : IsUnit a) (t : T) :
    (Ring.inverse a) t = (a t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [ContinuousMap.mul_apply, ContinuousMap.one_apply] using
    congrArg (fun g : C(T, ℂ) => g t) (Ring.inverse_mul_cancel a ha)

open Metric in
lemma pair_mem_closedBall {p : ℂ × ℂ} {r : ℝ} {a b : ℂ}
    (ha : a ∈ closedBall p.1 r) (hb : b ∈ closedBall p.2 r) :
    (a, b) ∈ closedBall p r := by
  simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using And.intro ha hb

open Metric in
lemma double_cauchy {f : ℂ × ℂ → ℂ} {p q : ℂ × ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall p r))
    (hr : 0 < r) (hq : q ∈ ball p r) :
    (∮ a in C(p.1, r), ∮ b in C(p.2, r),
      (a - q.1)⁻¹ * (b - q.2)⁻¹ * f (a, b)) =
        (2 * (Real.pi : ℂ) * I) ^ 2 * f q := by
  have hq' : q.1 ∈ ball p.1 r ∧ q.2 ∈ ball p.2 r := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
  have h₂ (a : ℂ) (ha : a ∈ closedBall p.1 r) :
      (∮ b in C(p.2, r), (b - q.2)⁻¹ * f (a, b)) =
        (2 * (Real.pi : ℂ) * I) * f (a, q.2) := by
    have hs : DifferentiableOn ℂ (fun b : ℂ => f (a, b)) (closedBall p.2 r) :=
      hf.comp ((differentiableOn_const a).prodMk differentiableOn_id)
        (fun b hb => pair_mem_closedBall ha hb)
    simpa only [smul_eq_mul] using hs.circleIntegral_sub_inv_smul hq'.2
  have h₁ :
      (∮ a in C(p.1, r), (a - q.1)⁻¹ * f (a, q.2)) =
        (2 * (Real.pi : ℂ) * I) * f q := by
    have hs : DifferentiableOn ℂ (fun a : ℂ => f (a, q.2)) (closedBall p.1 r) :=
      hf.comp (differentiableOn_id.prodMk (differentiableOn_const q.2))
        (fun a ha => pair_mem_closedBall ha (ball_subset_closedBall hq'.2))
    simpa only [smul_eq_mul, Prod.mk.eta] using hs.circleIntegral_sub_inv_smul hq'.1
  calc
    _ = ∮ a in C(p.1, r), (a - q.1)⁻¹ *
        ((2 * (Real.pi : ℂ) * I) * f (a, q.2)) := by
      apply circleIntegral.integral_congr hr.le
      intro a ha
      change (∮ b in C(p.2, r),
        (a - q.1)⁻¹ * (b - q.2)⁻¹ * f (a, b)) =
          (a - q.1)⁻¹ * ((2 * (Real.pi : ℂ) * I) * f (a, q.2))
      rw [show (fun b : ℂ => (a - q.1)⁻¹ * (b - q.2)⁻¹ * f (a, b)) =
        (fun b => (a - q.1)⁻¹ * ((b - q.2)⁻¹ * f (a, b))) by
          funext b
          ring]
      rw [circleIntegral.integral_const_mul, h₂ a (sphere_subset_closedBall ha)]
    _ = (2 * (Real.pi : ℂ) * I) *
        (∮ a in C(p.1, r), (a - q.1)⁻¹ * f (a, q.2)) := by
      rw [← circleIntegral.integral_const_mul]
      congr 1
      funext a
      ring
    _ = (2 * (Real.pi : ℂ) * I) ^ 2 * f q := by rw [h₁]; ring

lemma kernel_analytic {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (G₁ G₂ F : C(T, ℂ)) (p : ℂ × ℂ)
    (h₁ : ∀ t, G₁ t - p.1 ≠ 0) (h₂ : ∀ t, G₂ t - p.2 ≠ 0) :
    AnalyticAt ℂ (fun q : ℂ × ℂ =>
      Ring.inverse (G₁ - ContinuousMap.const T q.1) *
      Ring.inverse (G₂ - ContinuousMap.const T q.2) * F) p := by
  have hu₁ : IsUnit (G₁ - ContinuousMap.const T p.1) :=
    (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr h₁
  have hu₂ : IsUnit (G₂ - ContinuousMap.const T p.2) :=
    (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr h₂
  have a₁ : AnalyticAt ℂ (fun q : ℂ × ℂ => G₁ - ContinuousMap.const T q.1) p :=
    analyticAt_const.sub
      (((ContinuousLinearMap.const ℂ T).analyticAt p.1).comp analyticAt_fst)
  have a₂ : AnalyticAt ℂ (fun q : ℂ × ℂ => G₂ - ContinuousMap.const T q.2) p :=
    analyticAt_const.sub
      (((ContinuousLinearMap.const ℂ T).analyticAt p.2).comp analyticAt_snd)
  have i₁ : AnalyticAt ℂ Ring.inverse (G₁ - ContinuousMap.const T p.1) := by
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hu₁.unit)
  have i₂ : AnalyticAt ℂ Ring.inverse (G₂ - ContinuousMap.const T p.2) := by
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hu₂.unit)
  have c₁ : AnalyticAt ℂ
      (fun q : ℂ × ℂ => Ring.inverse (G₁ - ContinuousMap.const T q.1)) p :=
    i₁.comp (f := fun q : ℂ × ℂ => G₁ - ContinuousMap.const T q.1) a₁
  have c₂ : AnalyticAt ℂ
      (fun q : ℂ × ℂ => Ring.inverse (G₂ - ContinuousMap.const T q.2)) p :=
    i₂.comp (f := fun q : ℂ × ℂ => G₂ - ContinuousMap.const T q.2) a₂
  exact (c₁.mul c₂).mul analyticAt_const

open Metric in
theorem analyticAt_of_differentiableOn_closedBall {f : ℂ × ℂ → ℂ}
    {p : ℂ × ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall p r)) (hr : 0 < r) : AnalyticAt ℂ f p := by
  let G₁ : C(Theta × Theta, ℂ) := ⟨fun t => circleMap p.1 r t.1, by fun_prop⟩
  let G₂ : C(Theta × Theta, ℂ) := ⟨fun t => circleMap p.2 r t.2, by fun_prop⟩
  have hF : Continuous (fun t : Theta × Theta => f (G₁ t, G₂ t)) :=
    hf.continuousOn.comp_continuous (G₁.continuous.prodMk G₂.continuous)
      (fun t => pair_mem_closedBall
        (sphere_subset_closedBall (circleMap_mem_sphere p.1 hr.le t.1))
        (sphere_subset_closedBall (circleMap_mem_sphere p.2 hr.le t.2)))
  let H : C(Theta × Theta, ℂ) :=
    ⟨fun t => f (G₁ t, G₂ t) *
      deriv (circleMap p.1 r) t.1 * deriv (circleMap p.2 r) t.2,
      by
        apply (hF.mul ?_).mul ?_ <;> simp only [deriv_circleMap] <;> fun_prop⟩
  let K : (ℂ × ℂ) → C(Theta × Theta, ℂ) := fun q =>
    Ring.inverse (G₁ - ContinuousMap.const _ q.1) *
    Ring.inverse (G₂ - ContinuousMap.const _ q.2) * H
  have h₁ (q : ℂ × ℂ) (hq : q ∈ ball p r) :
      IsUnit (G₁ - ContinuousMap.const _ q.1) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro t
    change circleMap p.1 r t.1 - q.1 ≠ 0
    apply sub_ne_zero.mpr
    apply circleMap_ne_mem_ball
    have hq' : dist q.1 p.1 < r ∧ dist q.2 p.2 < r := by
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
    exact hq'.1
  have h₂ (q : ℂ × ℂ) (hq : q ∈ ball p r) :
      IsUnit (G₂ - ContinuousMap.const _ q.2) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro t
    change circleMap p.2 r t.2 - q.2 ≠ 0
    apply sub_ne_zero.mpr
    apply circleMap_ne_mem_ball
    have hq' : dist q.1 p.1 < r ∧ dist q.2 p.2 < r := by
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
    exact hq'.2
  have hK : AnalyticAt ℂ K p := by
    apply kernel_analytic
    · intro t
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mp (h₁ p (mem_ball_self hr)) t
    · intro t
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mp (h₂ p (mem_ball_self hr)) t
  have hL : AnalyticAt ℂ (fun q => integralCLM (K q)) p :=
    (integralCLM.analyticAt (K p)).comp (f := K) hK
  have hA : AnalyticAt ℂ
      (fun q => ((2 * (Real.pi : ℂ) * I) ^ 2)⁻¹ * integralCLM (K q)) p :=
    analyticAt_const.mul hL
  apply hA.congr
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with q hq
  let g : ℝ → ℝ → ℂ := fun a b =>
    deriv (circleMap p.1 r) a * (deriv (circleMap p.2 r) b *
      ((circleMap p.1 r a - q.1)⁻¹ * (circleMap p.2 r b - q.2)⁻¹ *
        f (circleMap p.1 r a, circleMap p.2 r b)))
  have hKe (t : Theta × Theta) : K q t = g t.1 t.2 := by
    dsimp only [K]
    simp only [ContinuousMap.mul_apply]
    rw [ringInverse_apply _ (h₁ q hq), ringInverse_apply _ (h₂ q hq)]
    dsimp [G₁, G₂, H, g]
    ring
  have hcontg : Continuous (fun t : Theta × Theta => g t.1 t.2) := by
    rw [show (fun t : Theta × Theta => g t.1 t.2) = K q from (funext hKe).symm]
    exact (K q).continuous
  have hrepr : integralCLM (K q) =
      ∮ a in C(p.1, r), ∮ b in C(p.2, r),
        (a - q.1)⁻¹ * (b - q.2)⁻¹ * f (a, b) := by
    rw [integralCLM_apply]
    simp_rw [hKe]
    rw [integral_theta_prod g hcontg]
    dsimp only [g]
    unfold circleIntegral
    simp only [smul_eq_mul]
    congr 1
    funext a
    rw [intervalIntegral.integral_const_mul]
  rw [hrepr, double_cauchy hf hr hq]
  simp

open Metric in
theorem differentiableOn_analyticOnNhd {f : ℂ × ℂ → ℂ}
    {s : Set (ℂ × ℂ)} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s := by
  intro p hp
  obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hp)
  exact analyticAt_of_differentiableOn_closedBall (hf.mono hrs) hr

end SICLean.L4.JointAnalytic
