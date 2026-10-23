import SICLean.L4.G1BilateralGeometry
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false

noncomputable section

open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1BilateralSingleTailsAux

open G1BilateralGeometry

/-- A finite family of real crossings lies in one compact interval. -/
theorem finite_real_bounds (F : Finset ℤ) (f : ℤ → ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m ∈ F, f m ∈ Icc (-A) A := by
  refine ⟨∑ m ∈ F, |f m|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro m hm
  have h := Finset.single_le_sum (fun i (_ : i ∈ F) => abs_nonneg (f i)) hm
  exact abs_le.mp h

/-- The outward lower-ray Jacobian has unit modulus. -/
theorem norm_lower_direction (ψ : ℝ) : ‖g1LowerDirection ψ‖ = 1 := by
  simp [g1LowerDirection, Complex.norm_exp, Complex.mul_re]


/-- A quadratic exponential with strictly negative leading coefficient is integrable. -/
theorem integrable_real_quadratic_exp (a B : ℝ) (ha : 0 < a) :
    Integrable (fun r : ℝ => Real.exp (-a * r ^ 2 + B * r)) := by
  have hi := (integrable_exp_neg_mul_sq ha).comp_sub_right (B / (2 * a))
  have hi' := hi.const_mul (Real.exp (B ^ 2 / (4 * a)))
  convert hi' using 1
  ext r
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- Replacing a left finite piece of an integrable ray function by a constant preserves
integrability. -/
theorem integrableOn_if_le (f : ℝ → ℝ) (C R b : ℝ)
    (hf : IntegrableOn f (Ici b)) :
    IntegrableOn (fun r : ℝ => if r ≤ R then C else f r) (Ici b) := by
  have hc : IntegrableOn (fun _ : ℝ => C) (Iic R) (volume.restrict (Ici b)) := by
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iic]
    simpa only [Iic_inter_Ici, IntegrableOn] using
      (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => C) (Icc b R))
  have htail : IntegrableOn f (Iic R)ᶜ (volume.restrict (Ici b)) :=
    (show Integrable f (volume.restrict (Ici b)) from hf).integrableOn
  change Integrable ((Iic R).piecewise (fun _ : ℝ => C) f) (volume.restrict (Ici b))
  exact Integrable.piecewise measurableSet_Iic hc htail

/-- Joint regularity gives continuity of a fixed-parameter path pullback. -/
theorem kernel_pullback_continuousOn (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : ModularCluster.KernelData) (τ v : ℂ) (q : ℝ → ℂ) (s : Set ℝ)
    (hq : ContinuousOn q s)
    (hreg : ∀ t ∈ s, (q t, τ) ∈ ModularCluster.regularDomain M k) :
    ContinuousOn (fun t => ModularCluster.kernel M k (q t) τ * v) s := by
  have hc := (ModularCluster.kernel_joint_analytic M hM k).continuousOn
  exact (hc.comp (hq.prodMk continuousOn_const) hreg).mul continuousOn_const


lemma finite_continuous_bound (F : Finset ℤ) (K : Set ℂ) (hK : IsCompact K)
    (f : ℤ → ℂ → ℂ) (hf : ∀ m ∈ F, ContinuousOn (f m) K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m ∈ F, ∀ τ ∈ K, ‖f m τ‖ ≤ B := by
  have hsum : ContinuousOn (fun τ => ∑ m ∈ F, ‖f m τ‖) K :=
    continuousOn_finsetSum F (fun m hm => (hf m hm).norm)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hsum
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro m hm τ hτ
  calc
    ‖f m τ‖ ≤ ∑ j ∈ F, ‖f j τ‖ := Finset.single_le_sum (f := fun j => ‖f j τ‖) (fun _ _ => norm_nonneg _) hm
    _ ≤ ‖∑ j ∈ F, ‖f j τ‖‖ := le_abs_self _
    _ ≤ B := hB τ hτ
    _ ≤ |B| + 1 := by linarith [le_abs_self B]

lemma continuousOn_phase (M : SL(2, ℤ)) (w z : ℂ) (n h ell m : ℤ)
    (K : Set ℂ) (hK : ∀ τ ∈ K, etaDenom M τ ≠ 0) :
    ContinuousOn (fun τ => g1Exponent M τ w z n h ell m) K := by
  intro τ hτ
  apply ContinuousAt.continuousWithinAt
  have hT := hK τ hτ
  unfold g1Exponent etaMobius etaDenom at *
  fun_prop (disch := assumption)

lemma continuousOn_reflectionPolynomial (M : SL(2, ℤ)) (z : ℂ) (r n : ℤ)
    (K : Set ℂ) (hK : ∀ τ ∈ K, etaDenom M τ ≠ 0) :
    ContinuousOn (fun τ => modularReflectionPolynomial M r n z τ) K := by
  intro τ hτ
  apply ContinuousAt.continuousWithinAt
  have hT := hK τ hτ
  unfold modularReflectionPolynomial etaMobius etaDenom at *
  fun_prop (disch := assumption)

lemma phase_affine (M : SL(2, ℤ)) (τ w z : ℂ) (n h ell m : ℤ)
    (hT : etaDenom M τ ≠ 0) :
    g1Exponent M τ w z n h ell m =
      G1RatioTail.complexS M τ w h ell / etaDenom M τ * z +
        g1Exponent M τ w 0 n h ell m := by
  unfold g1Exponent G1RatioTail.complexS
  field_simp
  ring

lemma norm_reflection_times_e (M : SL(2, ℤ)) (τ w z : ℂ) (n h ell m : ℤ) :
    ‖modularReflectionFactor M (m+1) n z τ * e (g1Exponent M τ w z n h ell m)‖ =
      ‖(etaMultiplier M) ^ (-2 : ℤ)‖ * Real.exp
        ((2 * (Real.pi : ℂ) * Complex.I *
          (modularReflectionPolynomial M (m+1) n z τ + g1Exponent M τ w z n h ell m)).re) := by
  simp only [modularReflectionFactor, norm_mul, norm_zpow, norm_neg, norm_one,
    one_zpow, mul_one, e, Complex.norm_exp]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [mul_add, Complex.add_re]

lemma singleKernel_eq (M : SL(2, ℤ)) (τ w z : ℂ) (n h ell m : ℤ) :
    G1BilateralGeometry.singleKernel M τ w n h ell m z =
      modularPhi M (m+1) n z τ * e (g1Exponent M τ w z n h ell m) := by
  simp [G1BilateralGeometry.singleKernel, ModularCluster.kernel,
    G1BilateralGeometry.singleData, ModularCluster.phase, g1Exponent]

lemma norm_vertical_e (M : SL(2, ℤ)) (τ w : ℂ) (x t : ℝ) (n h ell m : ℤ)
    (hd : etaDenom M τ ≠ 0) :
    ‖e (g1Exponent M τ w (g1VerticalPoint x t) n h ell m)‖ =
      Real.exp (-(2 * Real.pi * (G1RatioTail.complexS M τ w h ell / etaDenom M τ).re) * t +
        (2 * (Real.pi : ℂ) * Complex.I * g1Exponent M τ w (x : ℂ) n h ell m).re) := by
  have hv : g1Exponent M τ w (g1VerticalPoint x t) n h ell m =
      (G1RatioTail.complexS M τ w h ell / etaDenom M τ) * Complex.I * (t : ℂ) +
        g1Exponent M τ w (x : ℂ) n h ell m := by
    rw [phase_affine M τ w (g1VerticalPoint x t) n h ell m hd,
      phase_affine M τ w (x : ℂ) n h ell m hd]
    unfold g1VerticalPoint
    ring
  rw [e, Complex.norm_exp, hv]
  congr 1
  simp [mul_add, Complex.mul_re, Complex.mul_im]
  ring


lemma branch_pole_re (M : SL(2, ℤ)) (τ : ℂ) (n m : ℤ) (K J : ℕ) :
    (modularPhiPolePoint M (m + 1) n τ K J).re =
      ((n : ℝ) - (m : ℝ) * (etaDenom M τ).re +
        (K : ℝ) * (etaDenom M τ).re + (J : ℝ)) / (M 1 0 : ℝ) := by
  simp [modularPhiPolePoint]

lemma branch_pole_im (M : SL(2, ℤ)) (τ : ℂ) (n m : ℤ) (K J : ℕ) :
    (modularPhiPolePoint M (m + 1) n τ K J).im =
      (-(m : ℝ) * (etaDenom M τ).im +
        (K : ℝ) * (etaDenom M τ).im) / (M 1 0 : ℝ) := by
  simp [modularPhiPolePoint]

lemma branch_direction_re (ψ : ℝ) : (g1LowerDirection ψ).re = Real.sin ψ := by
  simp [g1LowerDirection, Complex.exp_re, show -Real.pi / 2 + ψ = ψ - Real.pi / 2 by ring,
    Real.cos_sub_pi_div_two]
lemma branch_direction_im (ψ : ℝ) : (g1LowerDirection ψ).im = -Real.cos ψ := by
  simp [g1LowerDirection, Complex.exp_im, show -Real.pi / 2 + ψ = ψ - Real.pi / 2 by ring,
    Real.sin_sub_pi_div_two]

def branchNormalProjection (ψ : ℝ) (z : ℂ) : ℝ :=
  Real.cos ψ * z.re + Real.sin ψ * z.im

lemma branchNormalProjection_sub (ψ : ℝ) (z v : ℂ) :
    branchNormalProjection ψ (z - v) = branchNormalProjection ψ z - branchNormalProjection ψ v := by
  simp only [branchNormalProjection, Complex.sub_re, Complex.sub_im]
  ring

lemma branchNormalProjection_le (ψ : ℝ) (z : ℂ)
    (hc : 0 ≤ Real.cos ψ) (hs : 0 ≤ Real.sin ψ) :
    branchNormalProjection ψ z ≤ 2 * ‖z‖ := by
  have h₁ := mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hc
  have h₂ := mul_le_mul_of_nonneg_left (Complex.im_le_norm z) hs
  have h₃ := mul_le_mul_of_nonneg_right (Real.cos_le_one ψ) (norm_nonneg z)
  have h₄ := mul_le_mul_of_nonneg_right (Real.sin_le_one ψ) (norm_nonneg z)
  unfold branchNormalProjection
  linarith

lemma branchNormalProjection_bent (x ψ r : ℝ) :
    branchNormalProjection ψ (g1BentLowerPoint x ψ r) = Real.cos ψ * x - Real.sin ψ := by
  simp only [branchNormalProjection, g1BentLowerPoint, Complex.add_re, Complex.sub_re,
    Complex.ofReal_re, Complex.I_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_im, branch_direction_re,
    branch_direction_im, Complex.add_im, Complex.sub_im, Complex.I_im]
  ring

lemma branch_base_re_center (M : SL(2, ℤ)) (τ₀ δ : ℝ) (n m : ℤ) :
    (modularPhiPolePoint M (m + 1) n (τ₀ : ℂ) 0 0).re -
      g1BentCrossing M τ₀ δ n m = δ := by
  rw [branch_pole_re]
  simp [g1BentCrossing, etaDenom, g1T]

lemma branch_base_projection_center (M : SL(2, ℤ)) (τ₀ δ ψ : ℝ) (n m : ℤ) :
    branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n (τ₀ : ℂ) 0 0) -
      (Real.cos ψ * g1BentCrossing M τ₀ δ n m - Real.sin ψ) =
        δ * Real.cos ψ + Real.sin ψ := by
  simp only [branchNormalProjection, branch_pole_re, branch_pole_im]
  simp [etaDenom, g1T, g1BentCrossing]
  ring

lemma branch_re_increment (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (n m : ℤ) (K J : ℕ) (hT : 0 ≤ (etaDenom M τ).re) :
    (modularPhiPolePoint M (m + 1) n τ 0 0).re ≤
      (modularPhiPolePoint M (m + 1) n τ K J).re := by
  rw [branch_pole_re, branch_pole_re]
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  apply (div_le_div_iff_of_pos_right hc).2
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have hinc : 0 ≤ (K : ℝ) * (etaDenom M τ).re + (J : ℝ) := by positivity
  linarith

lemma branch_projection_increment (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (ψ : ℝ) (n m : ℤ) (K J : ℕ)
    (hT : 0 ≤ branchNormalProjection ψ (etaDenom M τ)) (hcψ : 0 ≤ Real.cos ψ) :
    branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n τ 0 0) ≤
      branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n τ K J) := by
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hdiff : branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n τ K J) -
      branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n τ 0 0) =
        ((K : ℝ) * branchNormalProjection ψ (etaDenom M τ) + (J : ℝ) * Real.cos ψ) /
          (M 1 0 : ℝ) := by
    simp only [branchNormalProjection, branch_pole_re, branch_pole_im]
    ring
  have hnonneg : 0 ≤ ((K : ℝ) * branchNormalProjection ψ (etaDenom M τ) +
      (J : ℝ) * Real.cos ψ) / (M 1 0 : ℝ) := by positivity
  linarith

lemma branch_base_neighborhood (M : SL(2, ℤ))
    (F : Finset ℤ) (τ₀ δ ψ : ℝ) (n : ℤ) (hT : 0 < g1T M τ₀)
    (hδ : 0 < δ) (hcψ : 0 < Real.cos ψ) (hsψ : 0 ≤ Real.sin ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
      0 < (etaDenom M τ).re ∧ 0 < branchNormalProjection ψ (etaDenom M τ) ∧
      ∀ m ∈ F,
        δ / 2 < (modularPhiPolePoint M (m + 1) n τ 0 0).re -
          g1BentCrossing M τ₀ δ n m ∧
        δ * Real.cos ψ / 2 <
          branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n τ 0 0) -
            (Real.cos ψ * g1BentCrossing M τ₀ δ n m - Real.sin ψ) := by
  have hreal : ∀ᶠ τ : ℂ in 𝓝 (τ₀ : ℂ), 0 < (etaDenom M τ).re := by
    have hcont : ContinuousAt (fun τ : ℂ => (etaDenom M τ).re) (τ₀ : ℂ) := by
      unfold etaDenom
      fun_prop
    apply hcont.eventually_const_lt
    simpa [etaDenom, g1T] using hT
  have hproj : ∀ᶠ τ : ℂ in 𝓝 (τ₀ : ℂ), 0 < branchNormalProjection ψ (etaDenom M τ) := by
    have hcont : ContinuousAt (fun τ : ℂ => branchNormalProjection ψ (etaDenom M τ))
        (τ₀ : ℂ) := by unfold branchNormalProjection etaDenom; fun_prop
    apply hcont.eventually_const_lt
    simpa [branchNormalProjection, etaDenom, g1T] using mul_pos hcψ hT
  have hbase : ∀ᶠ τ : ℂ in 𝓝 (τ₀ : ℂ), ∀ m ∈ F,
      δ / 2 < (modularPhiPolePoint M (m + 1) n τ 0 0).re -
          g1BentCrossing M τ₀ δ n m ∧
      δ * Real.cos ψ / 2 <
        branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n τ 0 0) -
          (Real.cos ψ * g1BentCrossing M τ₀ δ n m - Real.sin ψ) := by
    apply (Filter.eventually_all_finset F).2
    intro m hm
    have hcont₁ : ContinuousAt (fun τ : ℂ =>
        (modularPhiPolePoint M (m + 1) n τ 0 0).re -
          g1BentCrossing M τ₀ δ n m) (τ₀ : ℂ) := by
      unfold modularPhiPolePoint etaDenom
      fun_prop
    have hcont₂ : ContinuousAt (fun τ : ℂ =>
        branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n τ 0 0) -
          (Real.cos ψ * g1BentCrossing M τ₀ δ n m - Real.sin ψ)) (τ₀ : ℂ) := by
      unfold branchNormalProjection modularPhiPolePoint etaDenom
      fun_prop
    have h₁ := hcont₁.eventually_const_lt (show δ / 2 <
        (modularPhiPolePoint M (m + 1) n (τ₀ : ℂ) 0 0).re -
          g1BentCrossing M τ₀ δ n m by rw [branch_base_re_center]; linarith)
    have h₂ := hcont₂.eventually_const_lt (show δ * Real.cos ψ / 2 <
        branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n (τ₀ : ℂ) 0 0) -
          (Real.cos ψ * g1BentCrossing M τ₀ δ n m - Real.sin ψ) by
      rw [branch_base_projection_center]
      nlinarith [mul_pos hδ hcψ])
    exact h₁.and h₂
  have hgood := hreal.and (hproj.and hbase)
  obtain ⟨ρ, hρ, hρgood⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgood
  exact ⟨ρ, hρ, hρgood⟩

lemma branch_single_regular_of_gap (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w z : ℂ) (n h ell m : ℤ) (ε : ℝ) (hε : 0 < ε)
    (hτ : τ ∈ modularPhiDomain M)
    (hgap : ∀ K J : ℕ, (K, J) ∈ modularPhiPoleLabels M (m + 1) n →
      ε ≤ dist z (modularPhiPolePoint M (m + 1) n τ K J)) :
    (z, τ) ∈ ModularCluster.regularDomain M (singleData w n h ell m) := by
  apply (ModularCluster.regularDomain_iff_no_labels M hM _ z τ).2
  refine ⟨hτ, ?_⟩
  intro b hb hzb
  have hb' : b.1 = true ∧ b.2 ∈ modularPhiPoleLabels M (m + 1) n := by
    by_cases hbtrue : b.1 = true
    · exact ⟨hbtrue, by simpa [ModularCluster.labels, singleData, hbtrue] using hb⟩
    · simp [ModularCluster.labels, singleData, hbtrue] at hb
  have hd := hgap b.2.1 b.2.2 hb'.2
  rw [ModularCluster.branchPoint, if_pos hb'.1] at hzb
  change z = modularPhiPolePoint M (m + 1) n τ b.2.1 b.2.2 at hzb
  rw [hzb, dist_self] at hd
  exact (not_le_of_gt hε) hd

lemma differentiableOn_integral_of_disk_bound
    {F : ℂ × ℂ → ℂ} {c : ℝ → ℂ} {p : ℂ} {ρ : ℝ}
    {s : Set ℝ} {bound : ℝ → ℝ}
    (hρ : 0 < ρ) (hc : Continuous c) (hs : MeasurableSet s)
    (hF : ∀ q ∈ Metric.closedBall p ρ, ∀ t ∈ s, AnalyticAt ℂ F (q, c t))
    (hbound : ∀ q ∈ Metric.closedBall p ρ, ∀ t ∈ s, ‖F (q, c t)‖ ≤ bound t)
    (hint : IntegrableOn bound s) :
    DifferentiableOn ℂ (fun q => ∫ t in s, F (q, c t)) (Metric.ball p (ρ / 2)) := by
  let D : ℂ → ℝ → ℂ := fun q t => (fderiv ℂ F (q, c t)) (1, 0)
  have hsub (q : ℂ) (hq : q ∈ Metric.ball p (ρ / 2)) :
      Metric.closedBall q (ρ / 2) ⊆ Metric.closedBall p ρ := by
    intro v hv
    apply Metric.mem_closedBall.mpr
    have hq' := Metric.mem_ball.mp hq
    have hv' := Metric.mem_closedBall.mp hv
    calc
      dist v p ≤ dist v q + dist q p := dist_triangle v q p
      _ ≤ ρ := by linarith
  have hsmall : Metric.ball p (ρ / 2) ⊆ Metric.closedBall p ρ :=
    (Metric.ball_subset_closedBall).trans (Metric.closedBall_subset_closedBall (by linarith))
  have hcont (q : ℂ) (hq : q ∈ Metric.closedBall p ρ) :
      ContinuousOn (fun t => F (q, c t)) s := by
    intro t ht
    exact ((hF q hq t ht).continuousAt.comp (f := fun t : ℝ => (q, c t))
      (continuousAt_const.prodMk hc.continuousAt)).continuousWithinAt
  have hdcont (q : ℂ) (hq : q ∈ Metric.closedBall p ρ) : ContinuousOn (D q) s := by
    intro t ht
    have hd : ContinuousAt (fderiv ℂ F) (q, c t) :=
      (hF q hq t ht).contDiffAt (n := 1) |>.continuousAt_fderiv (by norm_num)
    exact ((hd.comp (f := fun t : ℝ => (q, c t))
      (continuousAt_const.prodMk hc.continuousAt)).clm_apply continuousAt_const).continuousWithinAt
  have hder (q : ℂ) (hq : q ∈ Metric.closedBall p ρ) (t : ℝ) (ht : t ∈ s) :
      HasDerivAt (fun u => F (u, c t)) (D q t) q := by
    exact (hF q hq t ht).differentiableAt.hasFDerivAt.comp_hasDerivAt q
      ((hasDerivAt_id q).prodMk (hasDerivAt_const q (c t)))
  have hd_bound (q : ℂ) (hq : q ∈ Metric.ball p (ρ / 2)) (t : ℝ) (ht : t ∈ s) :
      ‖D q t‖ ≤ bound t / (ρ / 2) := by
    rw [← (hder q (hsmall hq) t ht).deriv]
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (ne_of_gt (half_pos hρ))]
      intro v hv
      exact ((hF v (hsub q hq hv) t ht).comp (f := fun u : ℂ => (u, c t))
        (analyticAt_id.prod analyticAt_const)).differentiableAt.differentiableWithinAt
    · intro v hv
      exact hbound v (hsub q hq (Metric.sphere_subset_closedBall hv)) t ht
  intro q hq
  have hnb : Metric.ball p (ρ / 2) ∈ 𝓝 q := Metric.isOpen_ball.mem_nhds hq
  have hq' := hsmall hq
  have hiq : IntegrableOn (fun t => F (q, c t)) s :=
    hint.mono' ((hcont q hq').aestronglyMeasurable hs)
      (by filter_upwards [ae_restrict_mem hs] with t ht; exact hbound q hq' t ht)
  have hiD : IntegrableOn (fun t => bound t / (ρ / 2)) s := hint.div_const _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume.restrict s) (F := fun q t => F (q, c t)) (F' := D)
    (bound := fun t => bound t / (ρ / 2)) hnb
    (by filter_upwards [hnb] with v hv; exact (hcont v (hsmall hv)).aestronglyMeasurable hs)
    hiq ((hdcont q hq').aestronglyMeasurable hs)
    (by filter_upwards [ae_restrict_mem hs] with t ht; exact fun v hv => hd_bound v hv t ht)
    hiD
    (by filter_upwards [ae_restrict_mem hs] with t ht; exact fun v hv => hder v (hsmall hv) t ht)
  exact hd.2.differentiableAt.differentiableWithinAt


lemma bent_integral_differentiableOn_of_bound
    (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : ModularCluster.KernelData)
    (p : ℂ) (ρ x ψ : ℝ) (bu bl : ℝ → ℝ) (hρ : 0 < ρ)
    (hu : IntegrableOn bu (Ici (-1))) (hl : IntegrableOn bl (Ici 0))
    (hreg : ∀ τ ∈ Metric.closedBall p ρ,
      (∀ t : ℝ, -1 ≤ t → (g1VerticalPoint x t, τ) ∈ ModularCluster.regularDomain M k) ∧
      (∀ r : ℝ, 0 ≤ r → (g1BentLowerPoint x ψ r, τ) ∈ ModularCluster.regularDomain M k))
    (hb : ∀ τ ∈ Metric.closedBall p ρ,
      (∀ t : ℝ, -1 ≤ t → ‖g1VerticalPullback (fun z => ModularCluster.kernel M k z τ) x t‖ ≤ bu t) ∧
      (∀ r : ℝ, 0 ≤ r → ‖g1BentLowerPullback (fun z => ModularCluster.kernel M k z τ) x ψ r‖ ≤ bl r)) :
    DifferentiableOn ℂ
      (fun τ => g1BentIntegral (fun z => ModularCluster.kernel M k z τ) x ψ)
      (Metric.ball p (ρ / 2)) := by
  have huv : DifferentiableOn ℂ
      (fun τ => ∫ t in Ici (-1), g1VerticalPullback (fun z => ModularCluster.kernel M k z τ) x t)
      (Metric.ball p (ρ / 2)) := by
    apply differentiableOn_integral_of_disk_bound
      (F := fun q : ℂ × ℂ => ModularCluster.kernel M k q.2 q.1 * Complex.I)
      (c := g1VerticalPoint x) hρ (by unfold g1VerticalPoint; fun_prop) measurableSet_Ici
    · intro τ hτ t ht
      exact ((ModularCluster.kernel_joint_analytic M hM k
        (g1VerticalPoint x t, τ) ((hreg τ hτ).1 t ht)).comp (x := (τ, g1VerticalPoint x t)) (f := fun q : ℂ × ℂ => (q.2, q.1))
          (analyticAt_snd.prod analyticAt_fst)).mul analyticAt_const
    · exact fun τ hτ t ht => (hb τ hτ).1 t ht
    · exact hu
  have hll : DifferentiableOn ℂ
      (fun τ => ∫ t in Ici 0, g1BentLowerPullback (fun z => ModularCluster.kernel M k z τ) x ψ t)
      (Metric.ball p (ρ / 2)) := by
    apply differentiableOn_integral_of_disk_bound
      (F := fun q : ℂ × ℂ => ModularCluster.kernel M k q.2 q.1 * g1LowerDirection ψ)
      (c := g1BentLowerPoint x ψ) hρ (by unfold g1BentLowerPoint; fun_prop) measurableSet_Ici
    · intro τ hτ t ht
      exact ((ModularCluster.kernel_joint_analytic M hM k
        (g1BentLowerPoint x ψ t, τ) ((hreg τ hτ).2 t ht)).comp (x := (τ, g1BentLowerPoint x ψ t)) (f := fun q : ℂ × ℂ => (q.2, q.1))
          (analyticAt_snd.prod analyticAt_fst)).mul analyticAt_const
    · exact fun τ hτ t ht => (hb τ hτ).2 t ht
    · exact hl
  exact hll.neg.add huv


end SICLean.L4.G1BilateralSingleTailsAux
