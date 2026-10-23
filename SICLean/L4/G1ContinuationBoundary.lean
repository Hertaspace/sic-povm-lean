import SICLean.L4.G1ContinuationStrict
import SICLean.L4.G1ContinuationBoundaryAux

set_option autoImplicit false

/-!
# Fixed given chains near real targets, ready for the real endpoint
Thirteen boundary interfaces. These exports quantify ordinary joint neighborhoods of (τ,w) /
(τ,w,y). They never assume a nonempty good-locus filter along a possibly wholly singular fixed-w,y τ
fiber. The original real-chain and bent-contour definitions are used literally.

[RW26, p. 7, (22), (23), p. 29].

B13 is only lower-half-plane identification on the displayed unit loci. It uses etaPhase, never
lower-half q products. Fixed-real-τ removable values, real limits and G1RealConclusion are treated
separately.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1Continuation

def singleTargetSum (M : SL(2, ℤ)) (τ₀ δ ψ : ℝ) (n h ell : ℤ) (u : ℂ × ℂ) : ℂ :=
  ∑ m ∈ Finset.range (M 1 0).toNat,
    g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
      (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ

def ratioTargetSum (M : SL(2, ℤ)) (D : Fin (M 1 0).toNat → G1VerticalChain)
    (n h ell p : ℤ) (x : Parameters) : ℂ :=
  ∑ m : Fin (M 1 0).toNat,
    g1ChainIntegral (D m) (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)

def upperSingleGood (M : SL(2, ℤ)) (h ell : ℤ) : Set (ℂ × ℂ) :=
  {u | 0 < u.1.im ∧ u ∈ singleGood M h ell}

def upperRatioGood (M : SL(2, ℤ)) (h ell p : ℤ) : Set Parameters :=
  {x | 0 < x.1.im ∧ x ∈ ratioGood M h ell p}

/-- B01. Exact raw RHS and locus types of the G1 interface. [RW26, p. 7, (22), (23)]. -/
theorem real_rhs_and_locus_bridges (M : SL(2, ℤ)) (τ₀ : ℝ) (h ell p : ℤ)
    (w : ℂ) (v : ℂ × ℂ) :
    singleRaw M h ell ((τ₀ : ℂ), w) = g1SingleRawRHS M τ₀ h ell w ∧
    ratioRaw M h ell p ((τ₀ : ℂ), v) = g1RatioRawRHS M τ₀ h ell p v ∧
    (((τ₀ : ℂ), w) ∈ singleGood M h ell ↔ w ∈ g1SingleRHSLocus M τ₀ h ell) ∧
    (((τ₀ : ℂ), v) ∈ ratioGood M h ell p ↔ v ∈ g1RatioRHSLocus M τ₀ h ell p) := by
  exact ⟨rfl, rfl, Iff.rfl, Iff.rfl⟩

/-- B02. Every prescribed δ,ψ in G1RealConclusion admits a full joint tube. [RW26, p. 7]. -/
theorem real_bent_joint_geometry (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      ∀ u ∈ U, ∀ m ∈ Finset.range (M 1 0).toNat,
        u ∈ singleAdmissible M n h ell (m : ℤ)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ := by
  exact G1ContinuationBoundaryAux.real_bent_joint_geometry M hM τ₀ w δ ψ n h ell
    hT hs hδ hψ hψ'

/-- B03. Any original separating family, not just an explicit construction, works for jointly moving
parameters. [RW26, p. 29]. -/
theorem real_ratio_joint_geometry (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
      ∀ x ∈ U, x.1 ∈ modularPhiDomain M ∧ 0 < (etaDenom M x.1).re ∧
        x.2 ∈ ratioFiber M x.1 n h ell p ∧
        ∀ m, G1FixedSeparation.SeparatesAt (D m) M x.1 x.2.2 n p (m : ℤ) := by
  exact G1ContinuationBoundaryAux.real_ratio_joint_geometry M hM τ₀ w y n h ell p
    hT hs hL D hD

/-- B04. Full-disk common pullback majorants, now with w also moving. [RW26, p. 7]. -/
theorem real_single_joint_majorants (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ (U : Set (ℂ × ℂ)) (Bup Bdown : ℝ → ℝ),
      IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      IntegrableOn Bup (Ici (-1)) ∧ IntegrableOn Bdown (Ici 0) ∧
      ∀ u ∈ U, ∀ m ∈ Finset.range (M 1 0).toNat,
        (∀ t ∈ Ici (-1), ‖g1VerticalPullback
          (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) t‖ ≤ Bup t) ∧
        (∀ r ∈ Ici 0, ‖g1BentLowerPullback
          (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ r‖ ≤ Bdown r) := by
  exact G1ContinuationBoundaryAux.real_single_joint_majorants M hM τ₀ w δ ψ n h ell
    hT hs hδ hψ hψ'

/-- B05. A common baseline majorant and finite-circle bound for moving τ,w,y. [RW26, p. 7]. The
finite-circle bound includes the CCW Jacobian. -/
theorem real_ratio_joint_majorants (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ (U : Set Parameters) (B : ℝ → ℝ) (C : ℝ),
      IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧ Integrable B ∧ 0 < C ∧
      ∀ x ∈ U, ∀ m : Fin (M 1 0).toNat,
        (∀ t : ℝ, ‖g1VerticalPullback
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
          (D m).crossing t‖ ≤ B t) ∧
        (∀ r ∈ (D m).centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖g1CirclePullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p
            x.1 x.2.1 x.2.2) r ((D m).radius r) θ‖ ≤ C) := by
  exact G1ContinuationBoundaryAux.real_ratio_joint_majorants M hM τ₀ w y n h ell p
    hT hs hL D hD

/-- B06. Joint ordinary-neighborhood analytic integral at the actual real target. [RW26, p. 29].
Extends G1BilateralSingleTails' existing τ-only export. -/
theorem real_single_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      AnalyticOnNhd ℂ (singleTargetSum M τ₀ δ ψ n h ell) U ∧
      ∀ u ∈ U, ∀ m ∈ Finset.range (M 1 0).toNat,
        G1BentIntegrable (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ := by
  exact G1ContinuationBoundaryAux.real_single_joint_analytic M hM τ₀ w δ ψ n h ell
    hT hs hδ hψ hψ'

set_option maxHeartbeats 1200000 in
/-- B07. Same joint analyticity for every original fixed separating family. [RW26, p. 29]. Extends
G1BilateralRatioTails' existing τ-only export. -/
theorem real_ratio_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
      AnalyticOnNhd ℂ (ratioTargetSum M D n h ell p) U ∧
      ∀ x ∈ U, ∀ m, G1ChainIntegrable (D m)
        (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2) := by
  obtain ⟨Ug, hUg, hcg, hg⟩ :=
    G1Continuation.real_ratio_joint_geometry M hM τ₀ w y n h ell p hT hs hL D hD
  obtain ⟨Ub, B, C, hUb, hcb, hBi, hC, hb⟩ :=
    G1Continuation.real_ratio_joint_majorants M hM τ₀ w y n h ell p hT hs hL D hD
  let c : Parameters := ((τ₀ : ℂ), (w : ℂ), (y : ℂ))
  obtain ⟨ρ, hρ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hUg.inter hUb).mem_nhds (show c ∈ Ug ∩ Ub from ⟨hcg, hcb⟩))
  have hreg (x : Parameters) (hx : x ∈ Metric.closedBall c ρ)
      (m : Fin (M 1 0).toNat) :=
    G1FixedSeparation.separatesAt_regularDomain M hM x.1 x.2.1 x.2.2
      n h ell p (m : ℤ) (D m) (hg x (hsub hx).1).1
      ((hg x (hsub hx).1).2.2.2 m)
  let K (m : Fin (M 1 0).toNat) : ℂ × Parameters → ℂ := fun q =>
    UpperWindow.ratioKernel M (m : ℤ) n h ell p q.2.1 q.2.2.1 q.2.2.2 q.1
  have hk (m : Fin (M 1 0).toNat) (x : Parameters)
      (z : ℂ)
      (hz : (z, x.1) ∈ ModularCluster.regularDomain M
        (G1Pinch.ratioData x.2.1 x.2.2 n h ell p (m : ℤ))) :
      AnalyticAt ℂ (K m) (z, x) := by
    apply (ratio_kernel_joint_analytic M hM n h ell p (m : ℤ)).2
    exact ⟨⟨hz.1, hz.2.1⟩, hz.1, hz.2.2 rfl⟩
  have hv (m : Fin (M 1 0).toNat) :
      Continuous (g1VerticalPoint (D m).crossing) := by
    unfold g1VerticalPoint
    fun_prop
  have hCi : Integrable (fun _ : ℝ => C)
      (volume.restrict (Ioc 0 (2 * Real.pi))) :=
    integrableOn_const (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsingle (m : Fin (M 1 0).toNat) : AnalyticOnNhd ℂ
      (fun x : Parameters => g1ChainIntegral (D m)
        (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2))
      (Metric.closedBall c (ρ / 2)) := by
    have hline := G1ContinuationBoundaryAux.pullback_integral_joint_analytic (K := K m)
      (z := g1VerticalPoint (D m).crossing) (j := fun _ => Complex.I)
      (c := c) (R := ρ) (B := B) hρ (hv m) continuous_const
      (fun x hx t => hk m x _ ((hreg x hx m).1 t))
      (Eventually.of_forall (fun t x hx => (hb x (hsub hx).2 m).1 t)) hBi
    have hcircles : ∀ r ∈ (D m).centers, AnalyticOnNhd ℂ
        (fun x : Parameters => ∫ θ : ℝ in 0..(2 * Real.pi),
          g1CirclePullback
            (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
            r ((D m).radius r) θ) (Metric.closedBall c (ρ / 2)) := by
      intro r hr
      let z : ℝ → ℂ := circleMap (r : ℂ) ((D m).radius r)
      let j : ℝ → ℂ := fun θ => Complex.I * (z θ - (r : ℂ))
      have hj : Continuous j := continuous_const.mul ((continuous_circleMap _ _).sub continuous_const)
      have hcircle := G1ContinuationBoundaryAux.pullback_integral_joint_analytic
        (μ := volume.restrict (Ioc 0 (2 * Real.pi))) (K := K m) (z := z) (j := j)
        (c := c) (R := ρ) (B := fun _ => C) hρ (continuous_circleMap _ _) hj
        (fun x hx θ => hk m x _ ((hreg x hx m).2 r hr θ))
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ x hx
          exact (hb x (hsub hx).2 m).2 r hr θ ⟨hθ.1.le, hθ.2⟩) hCi
      simpa only [intervalIntegral.integral_of_le
        (show (0 : ℝ) ≤ 2 * Real.pi by positivity), K, z, j, g1CirclePullback] using hcircle
    have hcir := Finset.analyticOnNhd_fun_sum (D m).centers hcircles
    intro x hx
    have ha := (hline x hx).add (hcir x hx)
    apply ha.congr
    filter_upwards [] with v
    simp only [g1ChainIntegral, Pi.add_apply, K, g1VerticalPullback]
  let U := Metric.ball c (ρ / 2)
  have hUs : U ⊆ Metric.closedBall c ρ :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  refine ⟨U, Metric.isOpen_ball, Metric.mem_ball_self (half_pos hρ), ?_, ?_⟩
  · exact (show AnalyticOnNhd ℂ (ratioTargetSum M D n h ell p)
        (Metric.closedBall c (ρ / 2)) from by
      exact Finset.analyticOnNhd_fun_sum Finset.univ (fun m _ => hsingle m)).mono
          Metric.ball_subset_closedBall
  · intro x hx m
    have hxc := hUs hx
    constructor
    · exact G1ContinuationBoundaryAux.integrable_pullback_of_domination (K := K m)
        (z := g1VerticalPoint (D m).crossing) (j := fun _ => Complex.I)
        (hv m) continuous_const (fun t => hk m x _ ((hreg x hxc m).1 t))
        (Eventually.of_forall (fun t => (hb x (hsub hxc).2 m).1 t)) hBi
    · intro r hr
      let z : ℝ → ℂ := circleMap (r : ℂ) ((D m).radius r)
      let j : ℝ → ℂ := fun θ => Complex.I * (z θ - (r : ℂ))
      have hj : Continuous j := continuous_const.mul ((continuous_circleMap _ _).sub continuous_const)
      have hi := G1ContinuationBoundaryAux.integrable_pullback_of_domination
        (μ := volume.restrict (Ioc 0 (2 * Real.pi))) (K := K m) (z := z) (j := j)
        (continuous_circleMap _ _) hj
        (fun θ => hk m x _ ((hreg x hxc m).2 r hr θ))
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
          exact (hb x (hsub hxc).2 m).2 r hr θ ⟨hθ.1.le, hθ.2⟩) hCi
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (show (0 : ℝ) ≤ 2 * Real.pi by positivity)).mpr
      exact hi

/-- B08. Direct single entry point: any real δ,ψ, joint comparison locus. [RW26, p. 29]. No
good-locus condition is imposed on the target itself. -/
theorem single_upper_identity_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      ∀ u ∈ U ∩ upperSingleGood M h ell,
        singleTargetSum M τ₀ δ ψ n h ell u =
          UpperResidueParameters.prefactor M u.1 * singleRaw M h ell u := by
  obtain ⟨U, hU, h₀, hgeom⟩ := real_bent_joint_geometry M hM τ₀ w δ ψ n h ell
    hT hs hδ hψ hψ'
  refine ⟨U, hU, h₀, ?_⟩
  rintro u ⟨hu, hup, hgood⟩
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hTim : 0 < (etaDenom M u.1).im := by
    simpa [etaDenom] using mul_pos hc hup
  have harg : 0 < (etaDenom M u.1).arg := by
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hTim.le) ?_
    intro hz
    exact hTim.ne' (Complex.arg_eq_zero_iff.mp hz.symm).2
  have hindex : (0 : ℕ) ∈ Finset.range (M 1 0).toNat := by
    have hpos : 0 < (M 1 0).toNat := by omega
    simpa only [Finset.mem_range] using hpos
  have hadm := hgeom u hu 0 hindex
  have htube : u ∈ singleTube M h ell ψ :=
    ⟨⟨hup, harg, (le_abs_self _).trans_lt hadm.2.2.2.2.1⟩, hadm.2.2.2.2.2.1⟩
  have hx : ∀ m : Fin (M 1 0).toNat,
      BentClear M u.1 n (m : ℤ) (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ := by
    intro m
    exact (hgeom u hu m (Finset.mem_range.mpr m.isLt)).2.2.2.2.2.2
  have hid := (upper_single_all_strict M hM n h ell ψ hψ hψ' u htube hgood
    (fun m => g1BentCrossing M τ₀ δ n (m : ℤ)) hx).2
  change (∑ m ∈ Finset.range (M 1 0).toNat,
    g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
      (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) = _
  rw [Finset.sum_range]
  exact hid

/-- B09. Direct ratio entry point: any given separating chain, joint comparison. [RW26, p. 29]. No
extra nonvanishing of a denominator Φ representative on the chain. -/
theorem ratio_upper_identity_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
      ∀ x ∈ U ∩ upperRatioGood M h ell p,
        ratioTargetSum M D n h ell p x =
          UpperResidueParameters.prefactor M x.1 * ratioRaw M h ell p x := by
  obtain ⟨U, hU, h₀, hgeom⟩ := real_ratio_joint_geometry M hM τ₀ w y n h ell p
    hT hs hL D hD
  have hψ : 0 < Real.pi / 8 := by positivity
  have hψ' : Real.pi / 8 < Real.pi / 4 := by linarith [Real.pi_pos]
  obtain ⟨ρ, hρ, hden⟩ := G1BilateralGeometry.full_disk_denom M hM τ₀ (Real.pi / 16)
    hT (by positivity) (by linarith [Real.pi_pos])
  refine ⟨U ∩ (fun x : Parameters => x.1) ⁻¹' Metric.ball (τ₀ : ℂ) ρ,
    hU.inter (Metric.isOpen_ball.preimage continuous_fst), ⟨h₀, Metric.mem_ball_self hρ⟩, ?_⟩
  rintro x ⟨⟨hxU, hxball⟩, hup, hgood⟩
  obtain ⟨_, _, hfiber, hsep⟩ := hgeom x hxU
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hTim : 0 < (etaDenom M x.1).im := by
    simpa [etaDenom] using mul_pos hc hup
  have harg : 0 < (etaDenom M x.1).arg := by
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hTim.le) ?_
    intro hz
    exact hTim.ne' (Complex.arg_eq_zero_iff.mp hz.symm).2
  have harg' : (etaDenom M x.1).arg < Real.pi / 8 := by
    have hb := (hden x.1 (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hxball).le)).2.2.2
    linarith [le_abs_self (etaDenom M x.1).arg]
  have htube : x ∈ ratioTube M n h ell p (Real.pi / 8) :=
    ⟨⟨hup, harg, harg'⟩, hfiber⟩
  have hext : ∀ m, SeparatesExtension (ofChain (D m)) M x.1 x.2.2 n p (m : ℤ) := by
    intro m
    exact (ofChain_separates (D m) M x.1 x.2.2 n p (m : ℤ)).mpr (hsep m)
  have hid := (upper_ratio_all_strict M hM n h ell p (Real.pi / 8) hψ hψ' x
    htube hgood (fun m => ofChain (D m)) hext).2
  simpa only [ratioExtensionSum, ofChain_integral, ratioTargetSum] using hid

/-- B10. Joint comparison filter is provably nontrivial, unlike a fixed-w τ slice. [RW26, p. 29]. -/
theorem single_upper_joint_germ_neBot (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    NeBot (𝓝[upperSingleGood M h ell] ((τ₀ : ℂ), (w : ℂ))) ∧
      singleTargetSum M τ₀ δ ψ n h ell =ᶠ[
        𝓝[upperSingleGood M h ell] ((τ₀ : ℂ), (w : ℂ))]
        (fun u => UpperResidueParameters.prefactor M u.1 * singleRaw M h ell u) := by
  refine ⟨mem_closure_iff_nhdsWithin_neBot.mp
    (G1ContinuationBoundaryAux.real_mem_closure_upper_joint
      M τ₀ hT (singleGood M h ell)
      (single_good_open_dense_fibers M hM h ell).2 (w : ℂ)), ?_⟩
  obtain ⟨U, hU, hmem, hident⟩ :=
    single_upper_identity_neighborhood M hM τ₀ w δ ψ n h ell
      hT hs hδ hψ hψ'
  filter_upwards [
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds hmem),
    self_mem_nhdsWithin (s := upperSingleGood M h ell)
      (a := ((τ₀ : ℂ), (w : ℂ)))] with u hu hgood
  exact hident u ⟨hu, hgood⟩

/-- B11. Joint ratio filter nontriviality includes a target on any RHS divisor. [RW26, p. 29]. -/
theorem ratio_upper_joint_germ_neBot (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    NeBot (𝓝[upperRatioGood M h ell p] ((τ₀ : ℂ), (w : ℂ), (y : ℂ))) ∧
      ratioTargetSum M D n h ell p =ᶠ[
        𝓝[upperRatioGood M h ell p] ((τ₀ : ℂ), (w : ℂ), (y : ℂ))]
        (fun x => UpperResidueParameters.prefactor M x.1 * ratioRaw M h ell p x) := by
  refine ⟨mem_closure_iff_nhdsWithin_neBot.mp
    (G1ContinuationBoundaryAux.real_mem_closure_upper_joint
      M τ₀ hT (ratioGood M h ell p)
      (ratio_good_open_dense_fibers M hM h ell p).2
      ((w : ℂ), (y : ℂ))), ?_⟩
  obtain ⟨U, hU, hmem, hident⟩ :=
    ratio_upper_identity_neighborhood M hM τ₀ w y n h ell p
      hT hs hL D hD
  filter_upwards [
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds hmem),
    self_mem_nhdsWithin (s := upperRatioGood M h ell p)
      (a := ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))] with x hx hgood
  exact hident x ⟨hx, hgood⟩

/-- B12. Literal sums and kernels of G1RealConclusion, with its Finset/Fin ranges. [RW26, p. 7]. -/
theorem real_target_sum_bridges (M : SL(2, ℤ)) (τ₀ w y δ ψ : ℝ) (n h ell p : ℤ)
    (D : Fin (M 1 0).toNat → G1VerticalChain) :
    singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)) =
      (∑ m ∈ Finset.range (M 1 0).toNat,
        g1BentIntegral (g1SingleKernel M τ₀ w n h ell (m : ℤ))
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) ∧
    ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) =
      ∑ m : Fin (M 1 0).toNat, g1ChainIntegral (D m)
        (g1RatioKernel M τ₀ w y n h ell p (m : ℤ)) := by
  exact ⟨rfl, rfl⟩

/-- B13. Identify lower integrals on the unit loci via joint charts and etaPhase. No q-product is
evaluated below the axis, and no real removable value is claimed. [RW26, p. 7, p. 29]. The full-disk
lower identification is included. -/
theorem lower_half_identification (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (hT : 0 < g1T M τ₀) :
    (∀ (n h ell : ℤ) (w δ ψ : ℝ),
      0 < g1S M τ₀ w h ell → 0 < δ → 0 < ψ → ψ < Real.pi / 4 →
      ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
        ∀ u ∈ U ∩ singleGood M h ell, u.1.im < 0 →
          singleTargetSum M τ₀ δ ψ n h ell u = g1Prefactor M u.1 * singleRaw M h ell u) ∧
    (∀ (n h ell p : ℤ) (w y : ℝ),
      0 < g1S M τ₀ w h ell → g1L M τ₀ w y h ell p < 0 →
      ∀ D : Fin (M 1 0).toNat → G1VerticalChain,
      (∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
        (g1InversePoles M τ₀ y n p (m : ℤ))) →
      ∃ U : Set Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
        ∀ x ∈ U ∩ ratioGood M h ell p, x.1.im < 0 →
          ratioTargetSum M D n h ell p x = g1Prefactor M x.1 * ratioRaw M h ell p x) := by
  have hτ₀ : (τ₀ : ℂ) ∈ etaPhaseDomain M := real_mem_etaPhaseDomain M τ₀ hT
  constructor
  · intro n h ell w δ ψ hs hδ hψ hψ'
    obtain ⟨Ui, hUi, h₀i, hI, _⟩ := real_single_joint_analytic M hM τ₀ w δ ψ
      n h ell hT hs hδ hψ hψ'
    obtain ⟨Ub, hUb, h₀b, hid⟩ := single_upper_identity_neighborhood M hM τ₀ w δ ψ
      n h ell hT hs hδ hψ hψ'
    obtain ⟨Uc, N, Q, hUc, h₀c, hN, hQ, hchart⟩ :=
      G1ContinuationBoundaryAux.single_raw_joint_chart M hM h ell
        ((τ₀ : ℂ), (w : ℂ)) hτ₀
    let U : Set (ℂ × ℂ) := (Ui ∩ Ub) ∩
      (Uc ∩ (fun u : ℂ × ℂ => u.1) ⁻¹' etaPhaseDomain M)
    have hU : IsOpen U := (hUi.inter hUb).inter
      (hUc.inter ((etaPhaseDomain_isOpen M).preimage continuous_fst))
    have h₀ : ((τ₀ : ℂ), (w : ℂ)) ∈ U := ⟨⟨h₀i, h₀b⟩, h₀c, hτ₀⟩
    have hP : AnalyticOnNhd ℂ (fun u : ℂ × ℂ => etaPhase M u.1) U := by
      intro u hu
      exact (etaPhase_analyticOnNhd M u.1 hu.2.2).comp
        (f := fun u : ℂ × ℂ => u.1) (x := u) analyticAt_fst
    have hopen : IsOpen (upperSingleGood M h ell) :=
      (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).inter
        (single_good_open_dense_fibers M hM h ell).1
    obtain ⟨V, hV, h₀V, heq⟩ := G1ContinuationBoundaryAux.quotient_identity_neighborhood
      ((τ₀ : ℂ), (w : ℂ)) (singleGood M h ell) (upperSingleGood M h ell)
      (single_upper_joint_germ_neBot M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').1
      hopen (fun _ hu => hu.2) (singleTargetSum M τ₀ δ ψ n h ell)
      (fun u => etaPhase M u.1) (singleRaw M h ell) N Q U hU h₀
      (hI.mono (fun _ hu => hu.1.1)) hP
      (hN.mono (fun _ hu => hu.2.1)) (hQ.mono (fun _ hu => hu.2.1))
      (fun u hu => hchart u ⟨hu.1.2.1, hu.2⟩)
      (by
        rintro u ⟨hu, hgood⟩
        rw [hid u ⟨hu.1.2, hgood⟩,
          G1ContinuationBoundaryAux.upper_prefactor_eq_etaPhase M hM u.1 hgood.1])
    refine ⟨V, hV, h₀V, ?_⟩
    intro u hu _
    exact heq u hu
  · intro n h ell p w y hs hL D hD
    obtain ⟨Ui, hUi, h₀i, hI, _⟩ := real_ratio_joint_analytic M hM τ₀ w y
      n h ell p hT hs hL D hD
    obtain ⟨Ub, hUb, h₀b, hid⟩ := ratio_upper_identity_neighborhood M hM τ₀ w y
      n h ell p hT hs hL D hD
    obtain ⟨Uc, N, Q, hUc, h₀c, hN, hQ, hchart⟩ :=
      G1ContinuationBoundaryAux.ratio_raw_joint_chart M hM h ell p
        ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) hτ₀
    let U : Set Parameters := (Ui ∩ Ub) ∩
      (Uc ∩ (fun x : Parameters => x.1) ⁻¹' etaPhaseDomain M)
    have hU : IsOpen U := (hUi.inter hUb).inter
      (hUc.inter ((etaPhaseDomain_isOpen M).preimage continuous_fst))
    have h₀ : ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U := ⟨⟨h₀i, h₀b⟩, h₀c, hτ₀⟩
    have hP : AnalyticOnNhd ℂ (fun x : Parameters => etaPhase M x.1) U := by
      intro x hx
      exact (etaPhase_analyticOnNhd M x.1 hx.2.2).comp
        (f := fun x : Parameters => x.1) (x := x) analyticAt_fst
    have hopen : IsOpen (upperRatioGood M h ell p) :=
      (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).inter
        (ratio_good_open_dense_fibers M hM h ell p).1
    obtain ⟨V, hV, h₀V, heq⟩ := G1ContinuationBoundaryAux.quotient_identity_neighborhood
      ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) (ratioGood M h ell p) (upperRatioGood M h ell p)
      (ratio_upper_joint_germ_neBot M hM τ₀ w y n h ell p hT hs hL D hD).1
      hopen (fun _ hx => hx.2) (ratioTargetSum M D n h ell p)
      (fun x => etaPhase M x.1) (ratioRaw M h ell p) N Q U hU h₀
      (hI.mono (fun _ hx => hx.1.1)) hP
      (hN.mono (fun _ hx => hx.2.1)) (hQ.mono (fun _ hx => hx.2.1))
      (fun x hx => hchart x ⟨hx.1.2.1, hx.2⟩)
      (by
        rintro x ⟨hx, hgood⟩
        rw [hid x ⟨hx.1.2, hgood⟩,
          G1ContinuationBoundaryAux.upper_prefactor_eq_etaPhase M hM x.1 hgood.1])
    refine ⟨V, hV, h₀V, ?_⟩
    intro x hx _
    exact heq x hx

#check @G1BilateralSingleTails.summed_bent_integral_limits
#check @G1BilateralRatioTails.summed_chain_integral_limits
#check @qPochhammer_eta_prefactor
#check @etaPhase_analyticOnNhd
#check @etaPhase_tendsto_real
#check @single_upper_identity_neighborhood
#check @ratio_upper_identity_neighborhood
#print singleTargetSum
#print ratioTargetSum
#print lower_half_identification

end SICLean.L4.G1Continuation
