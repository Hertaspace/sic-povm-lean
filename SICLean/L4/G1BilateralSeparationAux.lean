import SICLean.L4.G1BilateralGeometry
import SICLean.L4.ModularClusterLedger

set_option autoImplicit false

/-!
# Full-disk separator auxiliaries

Real shadows reduce an infinite baseline to labeled local finiteness in a bounded strip. Fixed
circles use bounded complex regions instead. Finite continuous positive separations give common
radii and margins; connected disks then preserve the strict side and inside relations. All branch
labels, including labels merged at a real parameter, are retained.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1BilateralSeparationAux

lemma exists_closedBall_of_eventually {P : ℂ → Prop} {z : ℂ}
    (h : ∀ᶠ τ in 𝓝 z, P τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ Metric.closedBall z ρ, P τ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε / 2, by positivity, ?_⟩
  intro τ hτ
  apply hball
  have := Metric.mem_closedBall.mp hτ
  linarith

lemma finite_positive_disk {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℝ) (z : ℂ)
    (hc : ∀ i ∈ s, ContinuousAt (f i) z) (hp : ∀ i ∈ s, 0 < f i z) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
      ∀ τ ∈ Metric.closedBall z ρ, ∀ i ∈ s, ε ≤ f i τ := by
  obtain ⟨ε, hε, hle⟩ := ModularCluster.exists_pos_le_of_finset s
    (fun i => f i z / 2) (fun i hi => half_pos (hp i hi))
  have he : ∀ᶠ τ in 𝓝 z, ∀ i ∈ s, ε ≤ f i τ := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    have hlt : ε < f i z := lt_of_le_of_lt (hle i hi) (half_lt_self (hp i hi))
    exact ((hc i hi).eventually (isOpen_Ioi.mem_nhds hlt)).mono (fun _ h => h.le)
  obtain ⟨ρ, hρ, h⟩ := exists_closedBall_of_eventually he
  exact ⟨ρ, ε, hρ, hε, h⟩

lemma ratio_branch_shadow (M : SL(2, ℤ)) (y : ℝ) (n p m : ℤ)
    (τ : ℂ) (b : ModularCluster.Label) :
    ModularCluster.branchPoint M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m)
      (τ.re : ℂ) b =
      ((ModularCluster.branchPoint M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m)
        τ b).re : ℂ) := by
  rcases b with ⟨b, K, J⟩
  cases b <;>
    simp [ModularCluster.branchPoint, G1Pinch.ratioData, modularPhiPolePoint,
      modularPhiZeroPoint, etaDenom]

lemma shadow_mem_disk (τ : ℂ) (τ₀ ρ : ℝ)
    (hτ : τ ∈ ModularSector.parameterDisk τ₀ ρ) :
    (τ.re : ℂ) ∈ ModularSector.parameterDisk τ₀ ρ := by
  apply Metric.mem_closedBall.mpr
  have h := Metric.mem_closedBall.mp hτ
  calc
    dist (τ.re : ℂ) (τ₀ : ℂ) = |(τ - (τ₀ : ℂ)).re| := by
      simp [dist_eq_norm, ← Complex.ofReal_sub]
    _ ≤ ‖τ - (τ₀ : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ρ := by simpa only [dist_eq_norm] using h

/-- The complex chain contract indexed without losing merged labels. -/
lemma separatesAt_iff_labels (D : G1VerticalChain) (M : SL(2, ℤ)) (τ : ℂ)
    (y : ℝ) (n p m : ℤ) :
    G1FixedSeparation.SeparatesAt D M τ (y : ℂ) n p m ↔
      (∀ r ∈ D.centers, 0 < D.radius r) ∧
      (∀ b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m),
        (ModularCluster.branchPoint M
          (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b).re ≠ D.crossing ∧
        (∀ r ∈ D.centers, dist (ModularCluster.branchPoint M
          (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b) (r : ℂ) ≠ D.radius r) ∧
        G1FixedSeparation.leftAssignmentAt D (ModularCluster.branchPoint M
          (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b) =
            if b.1 = true then 0 else 1) := by
  simp only [G1FixedSeparation.SeparatesAt]
  constructor
  · rintro ⟨hr, havoid, hP, hZ⟩
    refine ⟨hr, ?_⟩
    rintro ⟨b, K, J⟩ hb
    cases b
    · have hb' : (K, J) ∈ modularPhiZeroLabels M (m + p) n := by
        simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
      have hm : modularPhiZeroPoint M (m + p) n τ K J - (y : ℂ) ∈
          (fun q : ℕ × ℕ => modularPhiZeroPoint M (m + p) n τ q.1 q.2 - (y : ℂ)) ''
            modularPhiZeroLabels M (m + p) n := ⟨(K, J), hb', rfl⟩
      simpa only [ModularCluster.branchPoint, G1Pinch.ratioData,
        Bool.false_eq_true, if_false, if_true] using
        ⟨(havoid _ (Or.inr hm)).1, (havoid _ (Or.inr hm)).2, hZ _ hm⟩
    · have hb' : (K, J) ∈ modularPhiPoleLabels M (m + 1) n := by
        simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
      have hm : modularPhiPolePoint M (m + 1) n τ K J ∈
          (fun q : ℕ × ℕ => modularPhiPolePoint M (m + 1) n τ q.1 q.2) ''
            modularPhiPoleLabels M (m + 1) n := ⟨(K, J), hb', rfl⟩
      simpa only [ModularCluster.branchPoint, G1Pinch.ratioData,
        Bool.false_eq_true, if_false, if_true] using
        ⟨(havoid _ (Or.inl hm)).1, (havoid _ (Or.inl hm)).2, hP _ hm⟩
  · rintro ⟨hr, hb⟩
    have hP : ∀ K J : ℕ, (K, J) ∈ modularPhiPoleLabels M (m + 1) n →
        (modularPhiPolePoint M (m + 1) n τ K J).re ≠ D.crossing ∧
        (∀ r ∈ D.centers,
          dist (modularPhiPolePoint M (m + 1) n τ K J) (r : ℂ) ≠ D.radius r) ∧
        G1FixedSeparation.leftAssignmentAt D
          (modularPhiPolePoint M (m + 1) n τ K J) = 0 := by
      intro K J h
      simpa only [ModularCluster.branchPoint, G1Pinch.ratioData,
        Bool.false_eq_true, if_false, if_true] using
        hb (true, K, J) (by simpa [ModularCluster.labels, G1Pinch.ratioData] using h)
    have hZ : ∀ K J : ℕ, (K, J) ∈ modularPhiZeroLabels M (m + p) n →
        (modularPhiZeroPoint M (m + p) n τ K J - (y : ℂ)).re ≠ D.crossing ∧
        (∀ r ∈ D.centers,
          dist (modularPhiZeroPoint M (m + p) n τ K J - (y : ℂ))
            (r : ℂ) ≠ D.radius r) ∧
        G1FixedSeparation.leftAssignmentAt D
          (modularPhiZeroPoint M (m + p) n τ K J - (y : ℂ)) = 1 := by
      intro K J h
      simpa only [ModularCluster.branchPoint, G1Pinch.ratioData,
        Bool.false_eq_true, if_false, if_true] using
        hb (false, K, J) (by simpa [ModularCluster.labels, G1Pinch.ratioData] using h)
    refine ⟨hr, ?_, ?_, ?_⟩
    · intro z hz
      rcases hz with ⟨⟨K, J⟩, h, rfl⟩ | ⟨⟨K, J⟩, h, rfl⟩
      · exact ⟨(hP K J h).1, (hP K J h).2.1⟩
      · exact ⟨(hZ K J h).1, (hZ K J h).2.1⟩
    · rintro z ⟨⟨K, J⟩, h, rfl⟩
      exact (hP K J h).2.2
    · rintro z ⟨⟨K, J⟩, h, rfl⟩
      exact (hZ K J h).2.2

lemma branch_continuous (M : SL(2, ℤ)) (k : ModularCluster.KernelData)
    (b : ModularCluster.Label) : Continuous (fun τ => ModularCluster.branchPoint M k τ b) := by
  exact continuous_iff_continuousAt.mpr fun τ =>
    (ModularCluster.branchPoint_analytic M k b τ (mem_univ _)).continuousAt

/-- Local finiteness of the real shadows suffices for an infinite baseline. -/
lemma finite_real_strip_labels (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p m : ℤ) (hτ₀ : (τ₀ : ℂ) ∈ modularPhiDomain M)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M ∧
      {b | b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) ∧
        ∃ τ ∈ ModularSector.parameterDisk τ₀ ρ,
          |(ModularCluster.branchPoint M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m)
            τ b).re| ≤ R}.Finite := by
  obtain ⟨ρ, hρ, hdom, hfin⟩ := ModularCluster.exists_uniform_finite_labels
    M hM (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) (τ₀ : ℂ) hτ₀ R hR
  refine ⟨ρ, hρ, hdom, hfin.subset ?_⟩
  rintro b ⟨hb, τ, hτ, hRτ⟩
  refine ⟨hb, (τ.re : ℂ), shadow_mem_disk τ τ₀ ρ hτ, ?_⟩
  rw [ratio_branch_shadow]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hRτ

/-- A finite set contains every label whose continuous separation could be small. -/
lemma uniform_gap_of_finite_nearby {ι : Type*} (A : Set ι) (z : ℂ)
    (f : ι → ℂ → ℝ) (hc : ∀ i ∈ A, Continuous (f i))
    (hp : ∀ i ∈ A, 0 < f i z) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hfin : {i | i ∈ A ∧ ∃ τ ∈ Metric.closedBall z ρ₀, f i τ < 1}.Finite) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧ ρ ≤ ρ₀ ∧
      ∀ τ ∈ Metric.closedBall z ρ, ∀ i ∈ A, ε ≤ f i τ := by
  let s := hfin.toFinset
  have hmem : ∀ i, i ∈ s ↔ i ∈ A ∧
      ∃ τ ∈ Metric.closedBall z ρ₀, f i τ < 1 := fun i => hfin.mem_toFinset
  obtain ⟨ρ₁, ε, hρ₁, hε, hgap⟩ := finite_positive_disk s f z
    (fun i hi => (hc i ((hmem i).mp hi).1).continuousAt)
    (fun i hi => hp i ((hmem i).mp hi).1)
  refine ⟨min ρ₀ ρ₁, min ε 1, lt_min hρ₀ hρ₁, lt_min hε one_pos,
    min_le_left _ _, ?_⟩
  intro τ hτ i hi
  by_cases hsmall : f i τ < 1
  · have hτ₀ : τ ∈ Metric.closedBall z ρ₀ :=
      Metric.closedBall_subset_closedBall (min_le_left _ _) hτ
    have his : i ∈ s := (hmem i).mpr ⟨hi, τ, hτ₀, hsmall⟩
    exact (min_le_left _ _).trans
      (hgap τ (Metric.closedBall_subset_closedBall (min_le_right _ _) hτ) i his)
  · exact (min_le_right _ _).trans (not_lt.mp hsmall)

/-- All labels keep a positive distance from one fixed circle boundary. -/
lemma uniform_circle_gap_single (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : ModularCluster.KernelData) (τ₀ a : ℂ) (r : ℝ)
    (hτ₀ : τ₀ ∈ modularPhiDomain M)
    (havoid : ∀ b ∈ ModularCluster.labels M k,
      dist (ModularCluster.branchPoint M k τ₀ b) a ≠ r) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
      Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ b ∈ ModularCluster.labels M k,
        ε ≤ |dist (ModularCluster.branchPoint M k τ b) a - r| := by
  obtain ⟨ρ₀, hρ₀, hdom, hfin⟩ := ModularCluster.exists_uniform_finite_labels
    M hM k τ₀ hτ₀ (‖a‖ + |r| + 1) (by positivity)
  have hnear : {b | b ∈ ModularCluster.labels M k ∧
      ∃ τ ∈ Metric.closedBall τ₀ ρ₀,
        |dist (ModularCluster.branchPoint M k τ b) a - r| < 1}.Finite := by
    apply hfin.subset
    rintro b ⟨hb, τ, hτ, hgap⟩
    refine ⟨hb, τ, hτ, ?_⟩
    have hdist : dist (ModularCluster.branchPoint M k τ b) a - r < 1 :=
      (le_abs_self _).trans_lt hgap
    have htri : ‖ModularCluster.branchPoint M k τ b‖ ≤
        dist (ModularCluster.branchPoint M k τ b) a + ‖a‖ := by
      simpa only [dist_zero_right] using
        dist_triangle (ModularCluster.branchPoint M k τ b) a 0
    linarith [le_abs_self r]
  obtain ⟨ρ, ε, hρ, hε, hle, hgap⟩ := uniform_gap_of_finite_nearby
    (ModularCluster.labels M k) τ₀
    (fun b τ => |dist (ModularCluster.branchPoint M k τ b) a - r|)
    (fun b _ => (((branch_continuous M k b).dist continuous_const).sub
      continuous_const).abs)
    (fun b hb => abs_pos.mpr (sub_ne_zero.mpr (havoid b hb))) ρ₀ hρ₀ hnear
  exact ⟨ρ, ε, hρ, hε,
    fun τ hτ => hdom (Metric.closedBall_subset_closedBall hle hτ), hgap⟩

/-- A continuous real function cannot skip an intermediate value on a disk. -/
lemma lt_iff_on_disk (z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (f : ℂ → ℝ)
    (hf : Continuous f) (a : ℝ)
    (hne : ∀ τ ∈ Metric.closedBall z ρ, f τ ≠ a)
    (τ : ℂ) (hτ : τ ∈ Metric.closedBall z ρ) : f τ < a ↔ f z < a := by
  have hz : z ∈ Metric.closedBall z ρ := Metric.mem_closedBall_self hρ
  have hs : IsPreconnected (Metric.closedBall z ρ) :=
    (convex_closedBall z ρ).isPreconnected
  constructor
  · intro ht
    by_contra hn
    obtain ⟨v, hv, he⟩ := hs.intermediate_value₂ hτ hz hf.continuousOn
      continuousOn_const ht.le (not_lt.mp hn)
    exact hne v hv he
  · intro ht
    by_contra hn
    obtain ⟨v, hv, he⟩ := hs.intermediate_value₂ hz hτ hf.continuousOn
      continuousOn_const ht.le (not_lt.mp hn)
    exact hne v hv he

end SICLean.L4.G1BilateralSeparationAux
