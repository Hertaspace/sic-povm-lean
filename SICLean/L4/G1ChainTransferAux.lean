import SICLean.L4.G1FixedSeparation
import SICLean.L4.G1FiniteChainLedger

set_option autoImplicit false

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1ChainTransferAux

/-- All candidate branches at real parameters are real, with their full labels retained. -/
lemma branch_mem_candidate (M : SL(2, ℤ)) (τ w y : ℝ) (n h ell p m : ℤ)
    (b : ModularCluster.Label)
    (hb : b ∈ ModularCluster.labels M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)) :
    ∃ x ∈ G1FiniteLedger.candidatePoles M τ y n p m,
      ModularCluster.branchPoint M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)
        (τ : ℂ) b = (x : ℂ) := by
  rcases b with ⟨b, K, J⟩
  cases b
  · have hb' : (K, J) ∈ modularPhiZeroLabels M (m + p) n := by
      simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
    let z := modularPhiZeroPoint M (m + p) n (τ : ℂ) K J - (y : ℂ)
    have hz : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · simp [z, modularPhiZeroPoint, etaDenom, Complex.div_im]
    refine ⟨z.re, Or.inr ⟨K, J, hb', hz⟩, ?_⟩
    simpa [ModularCluster.branchPoint, G1Pinch.ratioData, z] using hz.symm
  · have hb' : (K, J) ∈ modularPhiPoleLabels M (m + 1) n := by
      simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
    let z := modularPhiPolePoint M (m + 1) n (τ : ℂ) K J
    have hz : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · simp [z, modularPhiPolePoint, etaDenom, Complex.div_im]
    refine ⟨z.re, Or.inl ⟨K, J, hb', hz⟩, ?_⟩
    simpa [ModularCluster.branchPoint, G1Pinch.ratioData, z] using hz.symm

/-- Excluding the actual real candidate centers places a point in the joint regular locus. -/
lemma regular_of_avoids (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ) (z : ℂ)
    (hz : ∀ x ∈ G1FiniteLedger.candidatePoles M τ y n p m, z ≠ (x : ℂ)) :
    (z, (τ : ℂ)) ∈ ModularCluster.regularDomain M
      (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m) := by
  rw [ModularCluster.regularDomain_iff_no_labels M hM]
  refine ⟨real_mem_modularPhiDomain M τ hT, ?_⟩
  intro b hb
  obtain ⟨x, hx, heq⟩ := branch_mem_candidate M τ w y n h ell p m b hb
  rw [heq]
  exact hz x hx

/-- A finite chain and its circles fit into a strictly larger horizontal box. -/
lemma exists_bound (D₀ D₁ : G1VerticalChain) :
    ∃ B : ℝ, G1FiniteLedger.boundedBy D₀ B ∧ G1FiniteLedger.boundedBy D₁ B := by
  let F := D₀.centers.image (fun r => |r| + D₀.radius r) ∪
    D₁.centers.image (fun r => |r| + D₁.radius r) ∪
    {|D₀.crossing|, |D₁.crossing|}
  obtain ⟨B, hB⟩ := F.finite_toSet.bddAbove
  refine ⟨B + 1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have := hB (show |D₀.crossing| ∈ F by simp [F])
    linarith
  · intro r hr
    have := hB (show |r| + D₀.radius r ∈ F from
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)))
    linarith
  · have := hB (show |D₁.crossing| ∈ F by simp [F])
    linarith
  · intro r hr
    have := hB (show |r| + D₁.radius r ∈ F from
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)))
    linarith

/-- Continuity handles the compact middle, and an integrable exponential handles both tails. -/
lemma integrable_of_tail_bound (f : ℝ → ℂ) (hf : Continuous f) (C κ R : ℝ)
    (hκ : 0 < κ) (hbound : ∀ t : ℝ, R ≤ |t| → ‖f t‖ ≤ C * Real.exp (-κ * |t|)) :
    Integrable f := by
  have hmid := hf.integrableOn_Icc (μ := volume) (a := -R) (b := R)
  have htail : IntegrableOn f (Icc (-R) R)ᶜ := by
    apply (G1RatioTail.exponential_majorant_integrable C κ hκ).integrableOn.mono'
      hf.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
    apply hbound
    by_contra h
    have habs : |t| < R := lt_of_not_ge h
    exact ht ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  rw [← integrableOn_univ, ← union_compl_self (Icc (-R) R), integrableOn_union]
  exact ⟨hmid, htail⟩

end SICLean.L4.G1ChainTransferAux
