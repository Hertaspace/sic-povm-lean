import SICLean.L4.G1ContinuationHolomorphyAux
import SICLean.L4.G1BilateralSingleTails
import SICLean.L4.G1BilateralRatioTails

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Moving-parameter joint charts, common majorants, and no branching

Moving-parameter estimates and integral charts. The kernels are
UpperWindow's actual modularPhi kernels. Moving w,y is explicit in the analytic maps below: the
fixed-KernelData theorem alone is insufficient. Reciprocal charts allow denominator Φ poles, where
the reciprocal is its analytic zero. No integral, regularity or continuation property is stored in
geometric data.

Joint-chart inputs are modularPhi_joint_analytic_no_poles and inversePhi_joint_analytic, with common
moving-parameter bounds as explicit outputs. [RW26, p. 6, p. 7, p. 29].
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1Continuation

open G1ContinuationHolomorphyAux

def singleRegular (M : SL(2, ℤ)) (n m : ℤ) : Set (ℂ × (ℂ × ℂ)) :=
  {q | (q.1, q.2.1) ∈ modularPhiHolomorphicDomain M (m + 1) n}

def ratioRegular (M : SL(2, ℤ)) (n p m : ℤ) : Set (ℂ × Parameters) :=
  {q | (q.1, q.2.1) ∈ modularPhiHolomorphicDomain M (m + 1) n ∧
    (q.1 + q.2.2.2, q.2.1) ∈ ModularCluster.inversePhiDomain M (m + p) n}

def singleAdmissible (M : SL(2, ℤ)) (n h ell m : ℤ) (x ψ : ℝ) : Set (ℂ × ℂ) :=
  {u | u.1 ∈ modularPhiDomain M ∧ 0 < (etaDenom M u.1).re ∧
    0 < ψ ∧ ψ < Real.pi / 4 ∧ |(etaDenom M u.1).arg| < ψ ∧
    u.2 ∈ singleWindow M u.1 h ell ∧ BentClear M u.1 n m x ψ}

def singleBentValue (M : SL(2, ℤ)) (n h ell m : ℤ) (x ψ : ℝ) (u : ℂ × ℂ) : ℂ :=
  g1BentIntegral (UpperWindow.singleKernel M m n h ell u.1 u.2) x ψ

/-- J01. Literal actual kernels, preserving the nγτ term and total division. [RW26, p. 7]. -/
theorem existing_kernel_bridges (M : SL(2, ℤ)) (τ w y : ℂ) (n h ell p m : ℤ) :
    UpperWindow.singleKernel M m n h ell τ w =
      G1BilateralGeometry.singleKernel M τ w n h ell m ∧
    UpperWindow.ratioKernel M m n h ell p τ w y =
      G1RatioTail.complexKernel M τ w y n h ell p m := by
  constructor
  · funext z
    simp [UpperWindow.singleKernel, G1BilateralGeometry.singleKernel,
      ModularCluster.kernel, G1BilateralGeometry.singleData, UpperWindow.phase,
      ModularCluster.phase]
  · funext z
    simp [UpperWindow.ratioKernel, G1RatioTail.complexKernel, G1Pinch.ratioData,
      ModularCluster.kernel, UpperWindow.phase, ModularCluster.phase, div_eq_mul_inv]

/-- J02. All continuous variables vary jointly, on an ordinary open chart. [RW26, p. 6]. -/
theorem single_kernel_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell m : ℤ) :
    IsOpen (singleRegular M n m) ∧ AnalyticOnNhd ℂ
      (fun q : ℂ × (ℂ × ℂ) => UpperWindow.singleKernel M m n h ell q.2.1 q.2.2 q.1)
      (singleRegular M n m) := by
  constructor
  · exact ((modularPhiDivisor_domains_isOpen M hM (m + 1) n).1).preimage
      (show Continuous (fun q : ℂ × (ℂ × ℂ) => (q.1, q.2.1)) by fun_prop)
  · intro q hq
    have hz : AnalyticAt ℂ (fun v : ℂ × (ℂ × ℂ) => v.1) q := analyticAt_fst
    have hτ : AnalyticAt ℂ (fun v : ℂ × (ℂ × ℂ) => v.2.1) q :=
      analyticAt_fst.comp analyticAt_snd
    have hw : AnalyticAt ℂ (fun v : ℂ × (ℂ × ℂ) => v.2.2) q :=
      analyticAt_snd.comp analyticAt_snd
    have hnum : AnalyticAt ℂ
        (fun v : ℂ × (ℂ × ℂ) => modularPhi M (m + 1) n v.1 v.2.1) q :=
      (modularPhi_joint_analytic_no_poles M hM (m + 1) n (q.1, q.2.1) hq).comp
        (f := fun v : ℂ × (ℂ × ℂ) => (v.1, v.2.1)) (hz.prod hτ)
    exact hnum.mul (G1ContinuationHolomorphyAux.analyticAt_exp_phase M m n h ell
      hz hτ hw hq.1)

/-- J03. Inverse charts, including their zeros, not fixed-τ meromorphy. [RW26, p. 6]. -/
theorem ratio_kernel_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p m : ℤ) :
    IsOpen (ratioRegular M n p m) ∧ AnalyticOnNhd ℂ
      (fun q : ℂ × Parameters =>
        UpperWindow.ratioKernel M m n h ell p q.2.1 q.2.2.1 q.2.2.2 q.1)
      (ratioRegular M n p m) := by
  constructor
  · exact (((modularPhiDivisor_domains_isOpen M hM (m + 1) n).1).preimage
      (show Continuous (fun q : ℂ × Parameters => (q.1, q.2.1)) by fun_prop)).inter
        ((ModularCluster.inversePhiDomain_isOpen M hM (m + p) n).preimage
          (show Continuous (fun q : ℂ × Parameters => (q.1 + q.2.2.2, q.2.1)) by
            fun_prop))
  · intro q hq
    have hz : AnalyticAt ℂ (fun v : ℂ × Parameters => v.1) q := analyticAt_fst
    have hτ : AnalyticAt ℂ (fun v : ℂ × Parameters => v.2.1) q :=
      analyticAt_fst.comp analyticAt_snd
    have hw : AnalyticAt ℂ (fun v : ℂ × Parameters => v.2.2.1) q :=
      analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
    have hy : AnalyticAt ℂ (fun v : ℂ × Parameters => v.2.2.2) q :=
      analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
    have hnum : AnalyticAt ℂ
        (fun v : ℂ × Parameters => modularPhi M (m + 1) n v.1 v.2.1) q :=
      (modularPhi_joint_analytic_no_poles M hM (m + 1) n (q.1, q.2.1) hq.1).comp
        (f := fun v : ℂ × Parameters => (v.1, v.2.1)) (hz.prod hτ)
    have hinv : AnalyticAt ℂ
        (fun v : ℂ × Parameters =>
          (modularPhi M (m + p) n (v.1 + v.2.2.2) v.2.1)⁻¹) q :=
      (ModularCluster.inversePhi_joint_analytic M hM (m + p) n
        (q.1 + q.2.2.2, q.2.1) hq.2).comp
          (f := fun v : ℂ × Parameters => (v.1 + v.2.2.2, v.2.1)) ((hz.add hy).prod hτ)
    simpa only [UpperWindow.ratioKernel, div_eq_mul_inv, Pi.mul_apply] using!
      (hnum.mul hinv).mul (G1ContinuationHolomorphyAux.analyticAt_exp_phase M m n h ell
        hz hτ hw hq.1.1)

/-- J04. C,κ,R are chosen before τ,w,y,t and the finite component. [RW26, p. 7, p. 29]. Extends the
existing fixed-w,y bilateral estimates. -/
theorem ratio_joint_tail_majorant (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ∃ (U : Set Parameters) (C κ R : ℝ),
      IsOpen U ∧ x ∈ U ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ v ∈ U, ∀ m : Fin (M 1 0).toNat, ∀ t : ℝ, R ≤ |t| →
        (g1VerticalPoint (D m).base.crossing t, v) ∈ ratioRegular M n p (m : ℤ) ∧
        ‖g1VerticalPullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p
          v.1 v.2.1 v.2.2) (D m).base.crossing t‖ ≤ C * Real.exp (-κ * |t|) := by
  have hdom : x.1 ∈ modularPhiDomain M :=
    (UpperWindow.tauRegion_properties M hM ψ hψ' x.1 hx.1).1
  have harg : |(etaDenom M x.1).arg| < ψ := by
    rw [abs_of_pos hx.1.2.1]
    exact hx.1.2.2
  obtain ⟨ρs, κ, hρs, hκ, hs⟩ :=
    moving_ratio_phase_margin M h ell p x hdom hx.2.1.1 hx.2.1.2
  obtain ⟨ρa, hρa, hda, haa⟩ := local_denom_arg_bound M x.1 ψ hdom harg
  let ρ := min ρs ρa
  have hρ : 0 < ρ := lt_min hρs hρa
  let K := Metric.closedBall x ρ
  have hsub : K ⊆ Metric.closedBall x ρs :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hτball (v : Parameters) (hv : v ∈ K) : v.1 ∈ Metric.closedBall x.1 ρa := by
    have hd : dist v x ≤ ρa := (Metric.mem_closedBall.mp hv).trans (min_le_right _ _)
    rw [Prod.dist_eq] at hd
    exact (le_max_left _ _).trans hd
  have hdK : ∀ v ∈ K, v.1 ∈ modularPhiDomain M := fun v hv => (hs v (hsub hv)).1
  have haK : ∀ v ∈ K, |(etaDenom M v.1).arg| ≤ ψ := fun v hv => haa _ (hτball v hv)
  let A := ∑ m : Fin (M 1 0).toNat, |(D m).base.crossing|
  have hcross (m : Fin (M 1 0).toNat) : (D m).base.crossing ∈ Icc (-A) A := by
    exact abs_le.mp (Finset.single_le_sum (fun m _ => abs_nonneg (D m).base.crossing)
      (Finset.mem_univ m))
  let F : Finset ℤ := Finset.univ.image (fun m : Fin (M 1 0).toNat => (m : ℤ))
  have hF (m : Fin (M 1 0).toNat) : (m : ℤ) ∈ F :=
    Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
  obtain ⟨C, R, hC, hR, hb⟩ := compact_ratio_two_tail_bound M hM n h ell p F K
    (isCompact_closedBall _ _) hdK ψ hψ hψ' haK κ hκ
    (fun v hv => (hs v (hsub hv)).2.1) (fun v hv => (hs v (hsub hv)).2.2) (-A) A
  refine ⟨Metric.ball x ρ, C, κ, R, Metric.isOpen_ball, Metric.mem_ball_self hρ,
    hC, hκ, hR, ?_⟩
  intro v hv m t ht
  obtain ⟨hn, hd, hb'⟩ := hb v (Metric.ball_subset_closedBall hv) (m : ℤ) (hF m)
    (D m).base.crossing (hcross m) t ht
  refine ⟨⟨⟨hn.1, hn.2.1⟩, hd.1, hd.2.2⟩, ?_⟩
  simpa only [g1VerticalPullback, norm_mul, Complex.norm_I, mul_one] using hb'

/-- J05. One integrable baseline majorant and one finite-circle bound, including all Jacobians, for
moving τ,w,y. [RW26, p. 29]. -/
theorem ratio_joint_full_majorant (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ∃ (U : Set Parameters) (B : ℝ → ℝ) (C : ℝ),
      IsOpen U ∧ x ∈ U ∧ Integrable B ∧ 0 < C ∧
      ∀ v ∈ U, ∀ m : Fin (M 1 0).toNat,
        (∀ t : ℝ, ‖g1VerticalPullback
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p v.1 v.2.1 v.2.2)
          (D m).base.crossing t‖ ≤ B t) ∧
        (∀ r ∈ (D m).base.centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖g1CirclePullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p
            v.1 v.2.1 v.2.2) r ((D m).base.radius r) θ‖ ≤ C) ∧
        (∀ a ∈ (D m).extra.centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖complexCirclePullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p
            v.1 v.2.1 v.2.2) a ((D m).extra.radius a) θ‖ ≤ C) := by
  obtain ⟨Ut, Ct, κ, R, hUt, hxt, hCt, hκ, hR, ht⟩ :=
    ratio_joint_tail_majorant M hM n h ell p ψ hψ hψ' x hx D hD
  obtain ⟨Us, hUs, hxs, hsub, hs⟩ :=
    separating_extension_stable M hM n h ell p ψ hψ hψ' x hx D hD
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hUt.inter hUs).mem_nhds ⟨hxt, hxs⟩)
  let K := Metric.closedBall x ρ
  have hreg (v : Parameters) (hv : v ∈ K) (m : Fin (M 1 0).toNat) (z : ℂ)
      (hz : z.re = (D m).base.crossing ∨
        (∃ r ∈ (D m).base.centers, dist z (r : ℂ) = (D m).base.radius r) ∨
        (∃ a ∈ (D m).extra.centers, dist z a = (D m).extra.radius a)) :
      (z, v) ∈ ratioRegular M n p (m : ℤ) := by
    have hvU := hball hv
    have hd := extension_regular M hM v.1 v.2.1 v.2.2 z n h ell p (m : ℤ)
      (D m) (UpperWindow.tauRegion_properties M hM ψ hψ' v.1
        (hsub hvU.2).1).1 (hs v hvU.2 m) hz
    exact ⟨⟨hd.1, hd.2.1⟩, hd.1, hd.2.2 rfl⟩
  have hcont (m : Fin (M 1 0).toNat) (z j : ℝ → ℂ)
      (hz : Continuous z) (hj : Continuous j) (a b : ℝ)
      (hr : ∀ v ∈ K, ∀ t ∈ Icc a b, (z t, v) ∈ ratioRegular M n p (m : ℤ)) :
      ContinuousOn (fun q : Parameters × ℝ =>
        UpperWindow.ratioKernel M (m : ℤ) n h ell p q.1.1 q.1.2.1 q.1.2.2 (z q.2) *
          j q.2) (K ×ˢ Icc a b) := by
    intro q hq
    have hm : ContinuousAt (fun q : Parameters × ℝ => (z q.2, q.1)) q :=
      ((hz.comp continuous_snd).prodMk continuous_fst).continuousAt
    exact (((ratio_kernel_joint_analytic M hM n h ell p (m : ℤ)).2 _
      (hr q.1 hq.1 q.2 hq.2)).continuousAt.comp
        (f := fun q : Parameters × ℝ => (z q.2, q.1)) hm).mul
        (hj.comp continuous_snd).continuousAt |>.continuousWithinAt
  obtain ⟨Cv, hCv, hv⟩ := finite_path_compact_bound K (isCompact_closedBall _ _)
    (-R) R (fun (m : Fin (M 1 0).toNat) v t => g1VerticalPullback
      (UpperWindow.ratioKernel M (m : ℤ) n h ell p v.1 v.2.1 v.2.2)
        (D m).base.crossing t) (fun m => hcont m _ _
          (by unfold g1VerticalPoint; fun_prop) continuous_const (-R) R
          (fun v hv t _ => hreg v hv m _ (Or.inl (by simp [g1VerticalPoint]))))
  let Ib := Σ m : Fin (M 1 0).toNat, (D m).base.centers
  obtain ⟨Cb, hCb, hb⟩ := finite_path_compact_bound K (isCompact_closedBall _ _)
    0 (2 * Real.pi) (fun (i : Ib) v θ => g1CirclePullback
      (UpperWindow.ratioKernel M (i.1 : ℤ) n h ell p v.1 v.2.1 v.2.2)
        i.2.val ((D i.1).base.radius i.2.val) θ)
    (fun i => hcont i.1 _ _ (continuous_circleMap _ _)
      (continuous_const.mul ((continuous_circleMap _ _).sub continuous_const)) _ _
      (fun v hv θ _ => hreg v hv i.1 _ (Or.inr (Or.inl ⟨i.2.val, i.2.property,
        circleMap_mem_sphere _ ((hs v (hball hv).2 i.1).1 _ i.2.property).le θ⟩))))
  let Ie := Σ m : Fin (M 1 0).toNat, (D m).extra.centers
  obtain ⟨Ce, hCe, he⟩ := finite_path_compact_bound K (isCompact_closedBall _ _)
    0 (2 * Real.pi) (fun (i : Ie) v θ => complexCirclePullback
      (UpperWindow.ratioKernel M (i.1 : ℤ) n h ell p v.1 v.2.1 v.2.2)
        i.2.val ((D i.1).extra.radius i.2.val) θ)
    (fun i => hcont i.1 _ _ (continuous_circleMap _ _)
      (continuous_const.mul ((continuous_circleMap _ _).sub continuous_const)) _ _
      (fun v hv θ _ => hreg v hv i.1 _ (Or.inr (Or.inr ⟨i.2.val, i.2.property,
        circleMap_mem_sphere _ ((hs v (hball hv).2 i.1).2.1 _ i.2.property).le θ⟩))))
  let B : ℝ → ℝ := fun t => if |t| ≤ R then Cv else Ct * Real.exp (-κ * |t|)
  have hBi : Integrable B := by
    have hc : Integrable ((Icc (-R) R).indicator (fun _ : ℝ => Cv)) :=
      (integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const (s := Icc (-R) R) (C := Cv) (μ := volume)
          (by simp only [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have ht' : Integrable (((Icc (-R) R)ᶜ).indicator
        (fun t : ℝ => Ct * Real.exp (-κ * |t|))) :=
      (G1RatioTail.exponential_majorant_integrable Ct κ hκ).indicator
        measurableSet_Icc.compl
    have heq : B = fun t => (Icc (-R) R).indicator (fun _ : ℝ => Cv) t +
        ((Icc (-R) R)ᶜ).indicator (fun t : ℝ => Ct * Real.exp (-κ * |t|)) t := by
      funext t
      by_cases ht : |t| ≤ R
      · simp [B, ht, abs_le.mp ht]
      · have hnot : t ∉ Icc (-R) R := fun h => ht (abs_le.mpr h)
        simp [B, ht, hnot]
    rw [heq]
    exact hc.add ht'
  refine ⟨Metric.ball x ρ, B, max Cb Ce, Metric.isOpen_ball,
    Metric.mem_ball_self hρ, hBi, lt_of_lt_of_le hCb (le_max_left _ _), ?_⟩
  intro v hvU m
  have hvK : v ∈ K := Metric.ball_subset_closedBall hvU
  refine ⟨?_, ?_, ?_⟩
  · intro t
    dsimp only [B]
    split_ifs with ht'
    · exact hv m v hvK t (abs_le.mp ht')
    · exact (ht v (hball hvK).1 m t (le_of_not_ge ht')).2
  · intro r hr θ hθ
    exact (hb ⟨m, ⟨r, hr⟩⟩ v hvK θ hθ).trans (le_max_left _ _)
  · intro a ha θ hθ
    exact (he ⟨m, ⟨a, ha⟩⟩ v hvK θ hθ).trans (le_max_right _ _)

/-- J06. Actual absolute convergence is an output for every separating chain. [RW26, p. 7]. -/
theorem ratio_extension_integrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ∀ m, ExtensionIntegrable (D m)
      (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2) := by
  obtain ⟨U, B, C, hU, hxU, hBi, hC, hb⟩ :=
    ratio_joint_full_majorant M hM n h ell p ψ hψ hψ' x hx D hD
  have hτ := (UpperWindow.tauRegion_properties M hM ψ hψ' x.1 hx.1).1
  intro m
  let f := UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2
  have heq : f = G1RatioTail.complexKernel M x.1 x.2.1 x.2.2 n h ell p (m : ℤ) :=
    (existing_kernel_bridges M x.1 x.2.1 x.2.2 n h ell p (m : ℤ)).2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply hBi.mono' _ (Eventually.of_forall (hb x hxU m).1)
    change AEStronglyMeasurable (g1VerticalPullback f (D m).base.crossing) volume
    rw [heq]
    exact (G1BilateralRatioTailsAux.vertical_continuous M hM x.1 x.2.1 x.2.2
      n h ell p (m : ℤ) (D m).base.crossing
      (extension_vertical_regular M hM x.1 x.2.1 x.2.2 n h ell p (m : ℤ)
        (D m) hτ (hD m))).aestronglyMeasurable
  · intro r hr
    change IntervalIntegrable (g1CirclePullback f r ((D m).base.radius r)) _ _ _
    rw [heq]
    exact (ratio_path_continuous M hM x.1 x.2.1 x.2.2 n h ell p (m : ℤ)
      (circleMap (r : ℂ) ((D m).base.radius r))
      (fun θ => Complex.I * (circleMap (r : ℂ) ((D m).base.radius r) θ - (r : ℂ)))
      (continuous_circleMap _ _)
      (continuous_const.mul ((continuous_circleMap _ _).sub continuous_const))
      (extension_base_circle_regular M hM x.1 x.2.1 x.2.2 n h ell p (m : ℤ)
        (D m) hτ (hD m) r hr)).intervalIntegrable _ _
  · intro a ha
    change IntervalIntegrable (complexCirclePullback f a ((D m).extra.radius a)) _ _ _
    rw [heq]
    exact (ratio_path_continuous M hM x.1 x.2.1 x.2.2 n h ell p (m : ℤ)
      (circleMap a ((D m).extra.radius a))
      (fun θ => Complex.I * (circleMap a ((D m).extra.radius a) θ - a))
      (continuous_circleMap _ _)
      (continuous_const.mul ((continuous_circleMap _ _).sub continuous_const))
      (extension_extra_circle_regular M hM x.1 x.2.1 x.2.2 n h ell p (m : ℤ)
        (D m) hτ (hD m) a ha)).intervalIntegrable _ _

/-- J07. Joint integral holomorphy uses J03 + J05, not a germ in z alone. [RW26, p. 29]. -/
theorem ratio_extension_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ∃ U : Set Parameters, IsOpen U ∧ x ∈ U ∧ U ⊆ ratioTube M n h ell p ψ ∧
      AnalyticOnNhd ℂ (ratioExtensionSum M D n h ell p) U ∧
      ∀ v ∈ U, ∀ m, SeparatesExtension (D m) M v.1 v.2.2 n p (m : ℤ) := by
  obtain ⟨Ub, B, C, hUb, hxb, hBi, hC, hb⟩ :=
    ratio_joint_full_majorant M hM n h ell p ψ hψ hψ' x hx D hD
  obtain ⟨Us, hUs, hxs, hsub, hs⟩ :=
    separating_extension_stable M hM n h ell p ψ hψ hψ' x hx D hD
  let U := Ub ∩ Us
  have hU : IsOpen U := hUb.inter hUs
  let K (m : Fin (M 1 0).toNat) (q : ℂ × Parameters) : ℂ :=
    UpperWindow.ratioKernel M (m : ℤ) n h ell p q.2.1 q.2.2.1 q.2.2.2 q.1
  have hreg (v : Parameters) (hv : v ∈ U) (m : Fin (M 1 0).toNat) (z : ℂ)
      (hz : z.re = (D m).base.crossing ∨
        (∃ r ∈ (D m).base.centers, dist z (r : ℂ) = (D m).base.radius r) ∨
        (∃ a ∈ (D m).extra.centers, dist z a = (D m).extra.radius a)) :
      AnalyticAt ℂ (K m) (z, v) := by
    apply (ratio_kernel_joint_analytic M hM n h ell p (m : ℤ)).2
    have hd := extension_regular M hM v.1 v.2.1 v.2.2 z n h ell p (m : ℤ)
      (D m) (UpperWindow.tauRegion_properties M hM ψ hψ' v.1
        (hsub hv.2).1).1 (hs v hv.2 m) hz
    exact ⟨⟨hd.1, hd.2.1⟩, hd.1, hd.2.2 rfl⟩
  have hv (m : Fin (M 1 0).toNat) : AnalyticOnNhd ℂ
      (fun v => ∫ t : ℝ, g1VerticalPullback
        (UpperWindow.ratioKernel M (m : ℤ) n h ell p v.1 v.2.1 v.2.2)
          (D m).base.crossing t) U := by
    apply pullback_integral_analyticOn_three (K := K m) (B := B) hU
      (by fun_prop) continuous_const
    · intro v hv t
      exact hreg v hv m _ (Or.inl (by simp [g1VerticalPoint]))
    · exact Eventually.of_forall fun t v hv => (hb v hv.1 m).1 t
    · exact hBi
  have hc (m : Fin (M 1 0).toNat) (a : ℂ) (ρ : ℝ)
      (hcircle : ∀ v ∈ U, ∀ θ : ℝ,
        AnalyticAt ℂ (K m) (circleMap a ρ θ, v))
      (hbound : ∀ v ∈ U, ∀ θ ∈ Icc 0 (2 * Real.pi),
        ‖K m (circleMap a ρ θ, v) *
          (Complex.I * (circleMap a ρ θ - a))‖ ≤ C) :
      AnalyticOnNhd ℂ (fun v => ∫ θ : ℝ in 0..(2 * Real.pi),
        K m (circleMap a ρ θ, v) * (Complex.I * (circleMap a ρ θ - a))) U := by
    have hi : Integrable (fun _ : ℝ => C) (volume.restrict (Icc 0 (2 * Real.pi))) :=
      integrableOn_const (s := Icc 0 (2 * Real.pi)) (C := C) (μ := volume)
        (by simp only [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have ha := pullback_setIntegral_analyticOn_three (K := K m)
      (μ := volume) (S := Icc 0 (2 * Real.pi)) (B := fun _ => C)
      measurableSet_Icc hU (continuous_circleMap a ρ)
      (continuous_const.mul ((continuous_circleMap a ρ).sub continuous_const))
      (fun v hv θ _ => hcircle v hv θ)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ v hv
        exact hbound v hv θ hθ) hi
    simpa only [Pi.mul_apply, Pi.sub_apply,
      intervalIntegral.integral_of_le Real.two_pi_pos.le,
      integral_Icc_eq_integral_Ioc] using ha
  have hbases (m : Fin (M 1 0).toNat) (r : ℝ) (hr : r ∈ (D m).base.centers) :
      AnalyticOnNhd ℂ (fun v => ∫ θ : ℝ in 0..(2 * Real.pi),
        g1CirclePullback
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p v.1 v.2.1 v.2.2)
            r ((D m).base.radius r) θ) U := by
    refine hc m (r : ℂ) ((D m).base.radius r) ?_ ?_
    · intro v hv θ
      exact hreg v hv m _ (Or.inr (Or.inl
        ⟨r, hr, circleMap_mem_sphere _ ((hs v hv.2 m).1 r hr).le θ⟩))
    · intro v hv θ hθ
      exact (hb v hv.1 m).2.1 r hr θ hθ
  have hextras (m : Fin (M 1 0).toNat) (a : ℂ) (ha : a ∈ (D m).extra.centers) :
      AnalyticOnNhd ℂ (fun v => ∫ θ : ℝ in 0..(2 * Real.pi),
        complexCirclePullback
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p v.1 v.2.1 v.2.2)
            a ((D m).extra.radius a) θ) U := by
    refine hc m a ((D m).extra.radius a) ?_ ?_
    · intro v hv θ
      exact hreg v hv m _ (Or.inr (Or.inr
        ⟨a, ha, circleMap_mem_sphere _ ((hs v hv.2 m).2.1 a ha).le θ⟩))
    · intro v hv θ hθ
      exact (hb v hv.1 m).2.2 a ha θ hθ
  refine ⟨U, hU, ⟨hxb, hxs⟩, fun v hv => hsub hv.2, ?_,
    fun v hv m => hs v hv.2 m⟩
  unfold ratioExtensionSum
  apply Finset.analyticOnNhd_fun_sum
  intro m _
  unfold extensionIntegral g1ChainIntegral
  exact ((hv m).add (Finset.analyticOnNhd_fun_sum _ (hbases m))).add
    (Finset.analyticOnNhd_fun_sum _ (hextras m))

/-- J08. Gaussian coefficient is independent of w on compact neighborhoods. Both pullback majorants
are explicit common outputs. [RW26, p. 7]. -/
theorem single_joint_majorants (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell m : ℤ) (x ψ : ℝ) (u : ℂ × ℂ)
    (hu : u ∈ singleAdmissible M n h ell m x ψ) :
    ∃ (U : Set (ℂ × ℂ)) (C κ a B R : ℝ), IsOpen U ∧ u ∈ U ∧
      U ⊆ singleAdmissible M n h ell m x ψ ∧
      0 < C ∧ 0 < κ ∧ 0 < a ∧ 0 < B ∧ 0 < R ∧
      ∀ v ∈ U,
        (∀ t ≥ R, ‖g1VerticalPullback
          (UpperWindow.singleKernel M m n h ell v.1 v.2) x t‖ ≤ C * Real.exp (-κ * t)) ∧
        (∀ r ≥ R, ‖g1BentLowerPullback
          (UpperWindow.singleKernel M m n h ell v.1 v.2) x ψ r‖ ≤
            C * Real.exp (-a * r ^ 2 + B * r)) := by
  have hu0 := hu
  rcases hu with ⟨hdom, hre, hψ, hψ', harg, hS, hclear⟩
  obtain ⟨ρs, κ, hρs, hκ, hs⟩ := moving_single_phase_margin M h ell u hdom hS
  obtain ⟨ρa, hρa, hda, haa⟩ := local_denom_arg_bound M u.1 ψ hdom harg
  obtain ⟨ρg, a, hρg, ha, hg⟩ := moving_gaussian_margin M hM u.1 ψ hdom hψ hψ' harg
  let ρ := min ρs (min ρa ρg)
  have hρ : 0 < ρ := lt_min hρs (lt_min hρa hρg)
  let K := Metric.closedBall u ρ
  have hsub : K ⊆ Metric.closedBall u ρs :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hτball (v : ℂ × ℂ) (hv : v ∈ K) : v.1 ∈ Metric.closedBall u.1 ρ := by
    have hd : dist v u ≤ ρ := Metric.mem_closedBall.mp hv
    rw [Prod.dist_eq] at hd
    exact (le_max_left _ _).trans hd
  have hτa (v : ℂ × ℂ) (hv : v ∈ K) : v.1 ∈ Metric.closedBall u.1 ρa :=
    Metric.closedBall_subset_closedBall
      ((min_le_right _ _).trans (min_le_left _ _)) (hτball v hv)
  have hτg (v : ℂ × ℂ) (hv : v ∈ K) : v.1 ∈ Metric.closedBall u.1 ρg :=
    Metric.closedBall_subset_closedBall
      ((min_le_right _ _).trans (min_le_right _ _)) (hτball v hv)
  have hdK : ∀ v ∈ K, v.1 ∈ modularPhiDomain M := fun v hv => (hs v (hsub hv)).1
  have haK : ∀ v ∈ K, |(etaDenom M v.1).arg| ≤ ψ := fun v hv => haa _ (hτa v hv)
  obtain ⟨C, B, R, hC, hB, hR, hb⟩ := compact_single_two_tail_bound M hM n h ell
    {m} K (isCompact_closedBall _ _) hdK ψ hψ hψ' haK κ a
    (fun v hv => (hs v (hsub hv)).2) (fun v hv => (hg _ (hτg v hv)).2) (fun _ => x)
  have hA : IsOpen (singleAdmissible M n h ell m x ψ) :=
    single_admissible_isOpen M hM n h ell m x ψ
  refine ⟨Metric.ball u ρ ∩ singleAdmissible M n h ell m x ψ,
    C, κ, a, B, R, Metric.isOpen_ball.inter hA,
    ⟨Metric.mem_ball_self hρ, hu0⟩, inter_subset_right, hC, hκ, ha, hB, hR, ?_⟩
  intro v hv
  exact hb v (Metric.ball_subset_closedBall hv.1) m (Finset.mem_singleton_self m)

/-- J09. Only the existing bent integral, never a vertical nonreal lower tail. [RW26, p. 7, (22)].
-/
theorem single_bent_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell m : ℤ) (x ψ : ℝ) :
    IsOpen (singleAdmissible M n h ell m x ψ) ∧
      AnalyticOnNhd ℂ (singleBentValue M n h ell m x ψ)
        (singleAdmissible M n h ell m x ψ) ∧
      ∀ u ∈ singleAdmissible M n h ell m x ψ,
        G1BentIntegrable (UpperWindow.singleKernel M m n h ell u.1 u.2) x ψ := by
  have hlocal (u : ℂ × ℂ) (hu : u ∈ singleAdmissible M n h ell m x ψ) :
      AnalyticAt ℂ (singleBentValue M n h ell m x ψ) u ∧
        G1BentIntegrable (UpperWindow.singleKernel M m n h ell u.1 u.2) x ψ := by
    obtain ⟨U, C, κ, a, B, R, hU, huU, hsub, hC, hκ, ha, hB, hR, htail⟩ :=
      single_joint_majorants M hM n h ell m x ψ u hu
    obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds huU)
    let P := Metric.closedBall u ρ
    let V := Metric.ball u ρ
    let K (q : ℂ × (ℂ × ℂ)) : ℂ :=
      UpperWindow.singleKernel M m n h ell q.2.1 q.2.2 q.1
    have hreg (v : ℂ × ℂ) (hv : v ∈ P) :
        (∀ t : ℝ, -1 ≤ t → AnalyticAt ℂ K (g1VerticalPoint x t, v)) ∧
        (∀ r : ℝ, 0 ≤ r → AnalyticAt ℂ K (g1BentLowerPoint x ψ r, v)) := by
      have hvA := hsub (hball hv)
      have hpaths := bentClear_path_regular M v.1 n m x ψ hvA.1
        hvA.2.2.1 hvA.2.2.2.1 hvA.2.2.2.2.2.2
      exact ⟨fun t ht => (single_kernel_joint_analytic M hM n h ell m).2 _
        (hpaths.1 t ht), fun r hr => (single_kernel_joint_analytic M hM n h ell m).2 _
          (hpaths.2 r hr)⟩
    have hcont (z j : ℝ → ℂ) (hz : Continuous z) (hj : Continuous j) (S : Set ℝ)
        (hr : ∀ v ∈ P, ∀ t ∈ S, AnalyticAt ℂ K (z t, v)) :
        ContinuousOn (fun q : (ℂ × ℂ) × ℝ => K (z q.2, q.1) * j q.2) (P ×ˢ S) := by
      intro q hq
      have hm : ContinuousAt (fun q : (ℂ × ℂ) × ℝ => (z q.2, q.1)) q :=
        ((hz.comp continuous_snd).prodMk continuous_fst).continuousAt
      exact (((hr q.1 hq.1 q.2 hq.2).continuousAt.comp
        (f := fun q : (ℂ × ℂ) × ℝ => (z q.2, q.1)) hm).mul
          (hj.comp continuous_snd).continuousAt).continuousWithinAt
    obtain ⟨Cv, hCv, hcv⟩ := finite_path_compact_bound P (isCompact_closedBall _ _)
      (-1) R (fun (_ : PUnit.{1}) v t =>
        g1VerticalPullback (UpperWindow.singleKernel M m n h ell v.1 v.2) x t)
      (fun _ => hcont (g1VerticalPoint x) (fun _ => Complex.I)
        (by unfold g1VerticalPoint; fun_prop) continuous_const (Icc (-1) R)
        (fun v hv t ht => (hreg v hv).1 t ht.1))
    obtain ⟨Cl, hCl, hcl⟩ := finite_path_compact_bound P (isCompact_closedBall _ _)
      0 R (fun (_ : PUnit.{1}) v r =>
        g1BentLowerPullback (UpperWindow.singleKernel M m n h ell v.1 v.2) x ψ r)
      (fun _ => hcont (g1BentLowerPoint x ψ) (fun _ => g1LowerDirection ψ)
        (by unfold g1BentLowerPoint; fun_prop) continuous_const (Icc 0 R)
        (fun v hv r hr => (hreg v hv).2 r hr.1))
    let Cmid := max Cv Cl
    let C' := max C Cmid
    have hCC' : C ≤ C' := le_max_left _ _
    have hCvC' : Cv ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
    have hClC' : Cl ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
    have hmajor := G1BilateralSingleTails.majorants_integrable C' κ a B R
      (hC.le.trans hCC') hκ ha
    have hupper (v : ℂ × ℂ) (hv : v ∈ V) (t : ℝ) (ht : -1 ≤ t) :
        ‖g1VerticalPullback (UpperWindow.singleKernel M m n h ell v.1 v.2) x t‖ ≤
          G1BilateralSingleTails.upperMajorant C' κ R t := by
      unfold G1BilateralSingleTails.upperMajorant
      split_ifs with htR
      · exact (hcv PUnit.unit v (Metric.ball_subset_closedBall hv) t ⟨ht, htR⟩).trans hCvC'
      · exact ((htail v (hball (Metric.ball_subset_closedBall hv))).1 t
          (le_of_not_ge htR)).trans
          (mul_le_mul_of_nonneg_right hCC' (Real.exp_pos _).le)
    have hlower (v : ℂ × ℂ) (hv : v ∈ V) (r : ℝ) (hr : 0 ≤ r) :
        ‖g1BentLowerPullback (UpperWindow.singleKernel M m n h ell v.1 v.2) x ψ r‖ ≤
          G1BilateralSingleTails.lowerMajorant C' a B R r := by
      unfold G1BilateralSingleTails.lowerMajorant
      split_ifs with hrR
      · exact (hcl PUnit.unit v (Metric.ball_subset_closedBall hv) r ⟨hr, hrR⟩).trans hClC'
      · exact ((htail v (hball (Metric.ball_subset_closedBall hv))).2 r
          (le_of_not_ge hrR)).trans
          (mul_le_mul_of_nonneg_right hCC' (Real.exp_pos _).le)
    have haupper : AnalyticOnNhd ℂ (fun v => ∫ t : ℝ in Ici (-1),
        g1VerticalPullback (UpperWindow.singleKernel M m n h ell v.1 v.2) x t) V := by
      refine pullback_setIntegral_analyticOn_two (μ := volume) (S := Ici (-1))
        (K := K) (z := g1VerticalPoint x) (j := fun _ => Complex.I)
        (B := G1BilateralSingleTails.upperMajorant C' κ R)
        measurableSet_Ici Metric.isOpen_ball (by unfold g1VerticalPoint; fun_prop)
        continuous_const ?_ ?_ hmajor.2.2.1
      · intro v hv t ht
        exact (hreg v (Metric.ball_subset_closedBall hv)).1 t ht
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht v hv
        exact hupper v hv t ht
    have halower : AnalyticOnNhd ℂ (fun v => ∫ r : ℝ in Ici 0,
        g1BentLowerPullback (UpperWindow.singleKernel M m n h ell v.1 v.2) x ψ r) V := by
      refine pullback_setIntegral_analyticOn_two (μ := volume) (S := Ici 0)
        (K := K) (z := g1BentLowerPoint x ψ) (j := fun _ => g1LowerDirection ψ)
        (B := G1BilateralSingleTails.lowerMajorant C' a B R)
        measurableSet_Ici Metric.isOpen_ball (by unfold g1BentLowerPoint; fun_prop)
        continuous_const ?_ ?_ hmajor.2.2.2
      · intro v hv r hr
        exact (hreg v (Metric.ball_subset_closedBall hv)).2 r hr
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr v hv
        exact hlower v hv r hr
    have huV : u ∈ V := Metric.mem_ball_self hρ
    have huP : u ∈ P := Metric.mem_closedBall_self hρ.le
    have hcontupper : ContinuousOn
        (g1VerticalPullback (UpperWindow.singleKernel M m n h ell u.1 u.2) x) (Ici (-1)) := by
      intro t ht
      have hz : Continuous (g1VerticalPoint x) := by unfold g1VerticalPoint; fun_prop
      exact ((((hreg u huP).1 t ht).continuousAt.comp
        (f := fun t : ℝ => (g1VerticalPoint x t, u))
        (hz.prodMk continuous_const).continuousAt).mul continuousAt_const).continuousWithinAt
    have hcontlower : ContinuousOn
        (g1BentLowerPullback (UpperWindow.singleKernel M m n h ell u.1 u.2) x ψ) (Ici 0) := by
      intro r hr
      have hz : Continuous (g1BentLowerPoint x ψ) := by unfold g1BentLowerPoint; fun_prop
      exact ((((hreg u huP).2 r hr).continuousAt.comp
        (f := fun r : ℝ => (g1BentLowerPoint x ψ r, u))
        (hz.prodMk continuous_const).continuousAt).mul continuousAt_const).continuousWithinAt
    refine ⟨((halower u huV).neg.add (haupper u huV)), ?_, ?_⟩
    · exact hmajor.2.2.2.mono' (hcontlower.aestronglyMeasurable measurableSet_Ici)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
          exact hlower u huV r hr)
    · exact hmajor.2.2.1.mono' (hcontupper.aestronglyMeasurable measurableSet_Ici)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          exact hupper u huV t ht)
  exact ⟨single_admissible_isOpen M hM n h ell m x ψ,
    fun u hu => (hlocal u hu).1, fun u hu => (hlocal u hu).2⟩

/-- J10. Infinite equality follows from the finite ledger and vanishing connectors. [RW26, p. 13].
-/
theorem complex_same_assignment_integral (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D₀ D₁ : Fin (M 1 0).toNat → CircleExtension)
    (h₀ : ∀ m, SeparatesExtension (D₀ m) M x.1 x.2.2 n p (m : ℤ))
    (h₁ : ∀ m, SeparatesExtension (D₁ m) M x.1 x.2.2 n p (m : ℤ)) :
    (∀ m, extensionIntegral (D₀ m)
      (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2) =
        extensionIntegral (D₁ m)
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)) ∧
      ratioExtensionSum M D₀ n h ell p x = ratioExtensionSum M D₁ n h ell p x := by
  have hτ := UpperWindow.tauRegion_properties M hM ψ hψ' x.1 hx.1
  obtain ⟨ρ, κ, hρ, hκ, hmargin⟩ := moving_ratio_phase_margin M h ell p x
    hτ.1 hx.2.1.1 hx.2.1.2
  have hmarg := hmargin x (Metric.mem_closedBall_self hρ.le)
  have harg : |(etaDenom M x.1).arg| ≤ ψ := by
    rw [abs_of_pos hx.1.2.1]
    exact hx.1.2.2.le
  have hi₀ := ratio_extension_integrable M hM n h ell p ψ hψ hψ' x hx D₀ h₀
  have hi₁ := ratio_extension_integrable M hM n h ell p ψ hψ hψ' x hx D₁ h₁
  have heq (m : Fin (M 1 0).toNat) :
      extensionIntegral (D₀ m)
        (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2) =
      extensionIntegral (D₁ m)
        (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2) := by
    let a := (D₀ m).base.crossing
    let b := (D₁ m).base.crossing
    obtain ⟨C, R, hC, hR, hb⟩ := compact_ratio_two_tail_bound M hM n h ell p
      {(m : ℤ)} {x} isCompact_singleton (by intro v hv; simpa only [mem_singleton_iff.mp hv] using hτ.1)
      ψ hψ hψ' (by intro v hv; simpa only [mem_singleton_iff.mp hv] using harg)
      κ hκ (by intro v hv; simpa only [mem_singleton_iff.mp hv] using hmarg.2.1)
      (by intro v hv; simpa only [mem_singleton_iff.mp hv] using hmarg.2.2)
      (min a b) (max a b)
    have hconn := connectors_tendsto_of_tail
      (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
      a b C κ R hκ (fun cross hcross t ht =>
        (hb x (mem_singleton _) (m : ℤ) (Finset.mem_singleton_self _) cross hcross t ht).2.2)
    apply extensionIntegral_eq_of_finite_ledger (D₀ m) (D₁ m) _ (hi₀ m) (hi₁ m) hconn
    obtain ⟨R₀, hR₀, hledger⟩ := finite_zero_winding_ledger M hM x.1 x.2.1 x.2.2
      hτ.1 hτ.2.2.1 n h ell p (m : ℤ) (D₀ m) (D₁ m) (h₀ m) (h₁ m)
    filter_upwards [eventually_ge_atTop R₀] with R hR
    exact hledger R hR
  refine ⟨heq, ?_⟩
  exact Finset.sum_congr rfl (fun m _ => heq m)

/-- J11. Fixed local integrals agree on ordinary overlapping neighborhoods. [RW26, p. 29]. -/
theorem overlapping_transport_germs (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D₀ D₁ : Fin (M 1 0).toNat → CircleExtension)
    (h₀ : ∀ m, SeparatesExtension (D₀ m) M x.1 x.2.2 n p (m : ℤ))
    (h₁ : ∀ m, SeparatesExtension (D₁ m) M x.1 x.2.2 n p (m : ℤ)) :
    ratioExtensionSum M D₀ n h ell p =ᶠ[𝓝 x] ratioExtensionSum M D₁ n h ell p := by
  obtain ⟨U₀, hU₀, hx₀, hs₀, hD₀⟩ :=
    separating_extension_stable M hM n h ell p ψ hψ hψ' x hx D₀ h₀
  obtain ⟨U₁, hU₁, hx₁, hs₁, hD₁⟩ :=
    separating_extension_stable M hM n h ell p ψ hψ hψ' x hx D₁ h₁
  filter_upwards [hU₀.mem_nhds hx₀, hU₁.mem_nhds hx₁] with v hv₀ hv₁
  exact (complex_same_assignment_integral M hM n h ell p ψ hψ hψ' v
    (hs₀ hv₀) D₀ D₁ (hD₀ v hv₀) (hD₁ v hv₁)).2

/-- J12. Single-valued joint analytic gluing is an output, not a monodromy premise. Combined with
C11/J11 this identifies any finite route and any detours. [RW26, p. 29]. Uniqueness is restricted to
the domain, so values outside it are irrelevant. -/
theorem ratio_global_analytic_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ F : Parameters → ℂ, AnalyticOnNhd ℂ F (ratioTube M n h ell p ψ) ∧
      (∀ x ∈ ratioTube M n h ell p ψ,
        ∀ D : Fin (M 1 0).toNat → CircleExtension,
        (∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) →
          ratioExtensionSum M D n h ell p x = F x) ∧
      ∀ G : Parameters → ℂ,
        (∀ x ∈ ratioTube M n h ell p ψ,
          ∀ D : Fin (M 1 0).toNat → CircleExtension,
          (∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) →
            ratioExtensionSum M D n h ell p x = G x) →
        EqOn F G (ratioTube M n h ell p ψ) := by
  have hex : ∀ x ∈ ratioTube M n h ell p ψ,
      ∃ D : Fin (M 1 0).toNat → CircleExtension,
        ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ) := by
    intro x hx
    exact exists_separating_extensions M hM x.1
      (UpperWindow.tauRegion_properties M hM ψ hψ' x.1 hx.1).2.2.1 n h ell p x.2 hx.2
  choose D hD using fun x : ratioTube M n h ell p ψ => hex x x.property
  let F : Parameters → ℂ := fun x =>
    if hx : x ∈ ratioTube M n h ell p ψ then
      ratioExtensionSum M (D ⟨x, hx⟩) n h ell p x else 0
  have hvalue : ∀ x ∈ ratioTube M n h ell p ψ,
      ∀ E : Fin (M 1 0).toNat → CircleExtension,
      (∀ m, SeparatesExtension (E m) M x.1 x.2.2 n p (m : ℤ)) →
        ratioExtensionSum M E n h ell p x = F x := by
    intro x hx E hE
    dsimp only [F]
    rw [dif_pos hx]
    exact (complex_same_assignment_integral M hM n h ell p ψ hψ hψ' x hx
      E (D ⟨x, hx⟩) hE (hD ⟨x, hx⟩)).2
  refine ⟨F, ?_, hvalue, ?_⟩
  · intro x hx
    obtain ⟨U, hU, hxU, hsub, ha, hs⟩ := ratio_extension_joint_analytic M hM n h ell p
      ψ hψ hψ' x hx (D ⟨x, hx⟩) (hD ⟨x, hx⟩)
    apply (ha x hxU).congr
    filter_upwards [hU.mem_nhds hxU] with v hv
    exact hvalue v (hsub hv) (D ⟨x, hx⟩) (hs v hv)
  · intro G hG x hx
    exact (hvalue x hx (D ⟨x, hx⟩) (hD ⟨x, hx⟩)).symm.trans
      (hG x hx (D ⟨x, hx⟩) (hD ⟨x, hx⟩))

#check @modularPhi_joint_local_quotient
#check @modularPhi_joint_analytic_no_poles
#check @ModularCluster.inversePhi_joint_analytic
#check @ModularCluster.finite_family_uniform_boundary_bound_parameters
#print ratioRegular
#print singleAdmissible
#check @ratio_global_analytic_value

end SICLean.L4.G1Continuation
