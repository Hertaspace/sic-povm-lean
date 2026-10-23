import SICLean.L4.G1PinchGeometry

set_option autoImplicit false

/-!
Local stability of the fixed G1 geometry. Real affine branches allow a vertical boundary test to be
projected to a real parameter. Uniform local finiteness then reduces all boundary tests to finitely
many labels.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G1FixedSeparationAux

theorem branchPoint_realProjection (M : SL(2, ℤ)) (k : ModularCluster.KernelData)
    (hy : k.y.im = 0) (τ : ℂ) (b : ModularCluster.Label) :
    ModularCluster.branchPoint M k (τ.re : ℂ) b =
      ((ModularCluster.branchPoint M k τ b).re : ℂ) := by
  rcases b with ⟨b, K, J⟩
  cases b <;> apply Complex.ext <;>
    simp [ModularCluster.branchPoint, modularPhiPolePoint, modularPhiZeroPoint,
      etaDenom, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, hy] <;>
    by_cases hc : (M 1 0 : ℝ) = 0 <;> (try simp [hc]) <;> field_simp

theorem branchPoint_ofReal (M : SL(2, ℤ)) (k : ModularCluster.KernelData)
    (hy : k.y.im = 0) (τ : ℝ) (b : ModularCluster.Label) :
    ModularCluster.branchPoint M k (τ : ℂ) b =
      ((ModularCluster.branchPoint M k (τ : ℂ) b).re : ℂ) := by
  simpa only [Complex.ofReal_re] using branchPoint_realProjection M k hy (τ : ℂ) b

theorem projection_dist (τ : ℂ) (τ₀ : ℝ) :
    dist (τ.re : ℂ) (τ₀ : ℂ) ≤ dist τ (τ₀ : ℂ) := by
  simpa [dist_eq_norm, ← Complex.ofReal_sub] using
    Complex.abs_re_le_norm (τ - (τ₀ : ℂ))

theorem lt_iff_of_no_eq {X : Type*} [TopologicalSpace X] (S : Set X)
    (hS : IsPreconnected S) (f : X → ℝ) (hf : ContinuousOn f S)
    (c : ℝ) (hne : ∀ z ∈ S, f z ≠ c) (x y : X) (hx : x ∈ S) (hy : y ∈ S) :
    f x < c ↔ f y < c := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨z, hz, heq⟩ := hS.intermediate_value hx hy hf ⟨h.le, le_of_not_gt hn⟩
    exact hne z hz heq
  · intro h
    by_contra hn
    obtain ⟨z, hz, heq⟩ := hS.intermediate_value hy hx hf ⟨h.le, le_of_not_gt hn⟩
    exact hne z hz heq

/-- Every labeled branch preserves its side of the baseline and its membership in every prescribed
circle on one full closed parameter ball. The assumption consists only of initial boundary
avoidance. -/
theorem exists_stable_geometry (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : ModularCluster.KernelData) (hy : k.y.im = 0)
    (τ₀ : ℝ) (hT : 0 < g1T M τ₀) (D : G1VerticalChain)
    (hboundary : ∀ b ∈ ModularCluster.labels M k,
      (ModularCluster.branchPoint M k (τ₀ : ℂ) b).re ≠ D.crossing ∧
        ∀ r ∈ D.centers,
          dist (ModularCluster.branchPoint M k (τ₀ : ℂ) b) (r : ℂ) ≠ D.radius r) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (τ₀ : ℂ) ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ Metric.closedBall (τ₀ : ℂ) ρ,
        g1T M τ₀ / 2 < (etaDenom M τ).re ∧
          ∀ b ∈ ModularCluster.labels M k,
            (ModularCluster.branchPoint M k τ b).re ≠ D.crossing ∧
            ((ModularCluster.branchPoint M k τ b).re < D.crossing ↔
              (ModularCluster.branchPoint M k (τ₀ : ℂ) b).re < D.crossing) ∧
            ∀ r ∈ D.centers,
              dist (ModularCluster.branchPoint M k τ b) (r : ℂ) ≠ D.radius r ∧
              (dist (ModularCluster.branchPoint M k τ b) (r : ℂ) < D.radius r ↔
                dist (ModularCluster.branchPoint M k (τ₀ : ℂ) b) (r : ℂ) < D.radius r) := by
  let R : ℝ := |D.crossing| + ∑ r ∈ D.centers, (|r| + |D.radius r|) + 1
  have hsum : 0 ≤ ∑ r ∈ D.centers, (|r| + |D.radius r|) :=
    Finset.sum_nonneg fun r _ => add_nonneg (abs_nonneg r) (abs_nonneg _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcrossR : |D.crossing| ≤ R := by dsimp [R]; linarith
  have hcircleR : ∀ r ∈ D.centers, D.radius r + |r| ≤ R := by
    intro r hr
    have hs := Finset.single_le_sum
      (fun s (_ : s ∈ D.centers) => add_nonneg (abs_nonneg s) (abs_nonneg (D.radius s))) hr
    have ha := le_abs_self (D.radius r)
    dsimp [R]
    linarith [abs_nonneg D.crossing]
  obtain ⟨ε, hε, hεD, hfinite⟩ := ModularCluster.exists_uniform_finite_labels M hM k
    (τ₀ : ℂ) (real_mem_modularPhiDomain M τ₀ hT) R hR
  let F : Set ModularCluster.Label := {b | b ∈ ModularCluster.labels M k ∧
    ∃ τ ∈ Metric.closedBall (τ₀ : ℂ) ε, ‖ModularCluster.branchPoint M k τ b‖ ≤ R}
  have hFfinite : F.Finite := hfinite
  have hcont (b : ModularCluster.Label) :
      Continuous (fun τ => ModularCluster.branchPoint M k τ b) :=
    (ModularCluster.branchPoint_analytic M k b).continuous
  have hF : ∀ᶠ τ in 𝓝 (τ₀ : ℂ), ∀ b ∈ F,
      (ModularCluster.branchPoint M k τ b).re ≠ D.crossing ∧
        ∀ r ∈ D.centers, dist (ModularCluster.branchPoint M k τ b) (r : ℂ) ≠ D.radius r := by
    apply hFfinite.eventually_all.mpr
    intro b hb
    have hb₀ := hboundary b hb.1
    refine ((Complex.continuous_re.comp (hcont b)).continuousAt.eventually_ne hb₀.1).and ?_
    apply D.centers.eventually_all.mpr
    intro r hr
    exact ((hcont b).dist continuous_const).continuousAt.eventually_ne (hb₀.2 r hr)
  have hden : Continuous (fun τ : ℂ => (etaDenom M τ).re) := by
    unfold etaDenom
    fun_prop
  have hden₀ : (etaDenom M (τ₀ : ℂ)).re = g1T M τ₀ := by
    simp [etaDenom, g1T, Complex.mul_re]
  have hTev : ∀ᶠ τ in 𝓝 (τ₀ : ℂ), g1T M τ₀ / 2 < (etaDenom M τ).re :=
    (isOpen_Ioi.preimage hden).mem_nhds (by
      change g1T M τ₀ / 2 < (etaDenom M (τ₀ : ℂ)).re
      rw [hden₀]
      linarith)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hF.and hTev)
  let ρ : ℝ := min ε (δ / 2)
  have hρ : 0 < ρ := lt_min hε (by linarith)
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρδ : ρ < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsmall : ∀ τ ∈ Metric.closedBall (τ₀ : ℂ) ρ,
      (∀ b ∈ F, (ModularCluster.branchPoint M k τ b).re ≠ D.crossing ∧
        ∀ r ∈ D.centers, dist (ModularCluster.branchPoint M k τ b) (r : ℂ) ≠ D.radius r) ∧
      g1T M τ₀ / 2 < (etaDenom M τ).re := by
    intro τ hτ
    exact hδsub (lt_of_le_of_lt hτ hρδ)
  have hball : Metric.closedBall (τ₀ : ℂ) ρ ⊆ Metric.closedBall (τ₀ : ℂ) ε :=
    Metric.closedBall_subset_closedBall hρε
  have hnoVertical : ∀ τ ∈ Metric.closedBall (τ₀ : ℂ) ρ,
      ∀ b ∈ ModularCluster.labels M k, (ModularCluster.branchPoint M k τ b).re ≠ D.crossing := by
    intro τ hτ b hb heq
    have hpτ : (τ.re : ℂ) ∈ Metric.closedBall (τ₀ : ℂ) ρ :=
      le_trans (projection_dist τ τ₀) hτ
    have hp : ModularCluster.branchPoint M k (τ.re : ℂ) b = (D.crossing : ℂ) := by
      rw [branchPoint_realProjection M k hy, heq]
    have hbF : b ∈ F := ⟨hb, (τ.re : ℂ), hball hpτ, by
      simpa [hp, Complex.norm_real, Real.norm_eq_abs] using hcrossR⟩
    have hne := ((hsmall _ hpτ).1 b hbF).1
    exact hne (by simp [hp])
  have hnoCircle : ∀ τ ∈ Metric.closedBall (τ₀ : ℂ) ρ,
      ∀ b ∈ ModularCluster.labels M k, ∀ r ∈ D.centers,
        dist (ModularCluster.branchPoint M k τ b) (r : ℂ) ≠ D.radius r := by
    intro τ hτ b hb r hr heq
    have hnorm : ‖ModularCluster.branchPoint M k τ b‖ ≤ R := by
      calc
        ‖ModularCluster.branchPoint M k τ b‖ ≤
            dist (ModularCluster.branchPoint M k τ b) (r : ℂ) + ‖(r : ℂ)‖ := by
          simpa only [dist_zero_right] using
            dist_triangle (ModularCluster.branchPoint M k τ b) (r : ℂ) 0
        _ = D.radius r + |r| := by simp [heq, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ R := hcircleR r hr
    have hbF : b ∈ F := ⟨hb, τ, hball hτ, hnorm⟩
    exact ((hsmall _ hτ).1 b hbF).2 r hr heq
  refine ⟨ρ, hρ, hball.trans hεD, ?_⟩
  intro τ hτ
  refine ⟨(hsmall τ hτ).2, ?_⟩
  intro b hb
  have hbase : (τ₀ : ℂ) ∈ Metric.closedBall (τ₀ : ℂ) ρ :=
    Metric.mem_closedBall_self hρ.le
  have hconn := (convex_closedBall (τ₀ : ℂ) ρ).isPreconnected
  refine ⟨hnoVertical τ hτ b hb, ?_, ?_⟩
  · exact lt_iff_of_no_eq _ hconn _
      (Complex.continuous_re.comp (hcont b)).continuousOn D.crossing
      (fun z hz => hnoVertical z hz b hb) τ (τ₀ : ℂ) hτ hbase
  · intro r hr
    refine ⟨hnoCircle τ hτ b hb r hr, ?_⟩
    exact lt_iff_of_no_eq _ hconn _ ((hcont b).dist continuous_const).continuousOn
      (D.radius r) (fun z hz => hnoCircle z hz b hb r hr) τ (τ₀ : ℂ) hτ hbase

end SICLean.L4.G1FixedSeparationAux
