import SICLean.L4.G1BilateralGeometry
import SICLean.L4.ModularClusterLedger
import SICLean.L4.G1BilateralSeparationAux

set_option autoImplicit false

/-!
# Actual branches and full-disk fixed separators

Geometry uses exactly `G1VerticalChain`, `G1Separates`,
`G1FixedSeparation.SeparatesAt`, and the actual labeled branches. A fixed chain (or fixed finite
family) precedes the radius. No claim chooses one radius for all possible separating chains.

For arbitrary contract chains, circle membership is compared with its initial membership, not
equality to the circle center. Only ExplicitChain gets the stronger existing `TracksClusters`
conclusion. All labels of a merged pole stay present. A denominator Φ pole is allowed on a contour:
its reciprocal is an analytic zero, by `regularDomain` interface.

[RW26, p. 6, p. 7, p. 13]. Full disks are included, with the full-ball interfaces as inputs.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1BilateralSeparation

open G1BilateralSeparationAux

/-- S01. Actual affine numerator branch, with no pseudolattice substitution. [RW26, p. 6]. -/
theorem numerator_branch_re (M : SL(2, ℤ)) (τ : ℂ) (n m : ℤ) (K J : ℕ) :
    (modularPhiPolePoint M (m + 1) n τ K J).re =
      ((n : ℝ) + ((K : ℝ) - (m : ℝ)) * (etaDenom M τ).re + (J : ℝ)) /
        (M 1 0 : ℝ) := by
  simp [modularPhiPolePoint]
  ring

/-- S02. Actual inverse-denominator branch includes the translation -y. [RW26, p. 6]. -/
theorem inverse_branch_re (M : SL(2, ℤ)) (τ : ℂ) (y : ℝ)
    (n p m : ℤ) (K J : ℕ) :
    (modularPhiZeroPoint M (m + p) n τ K J - (y : ℂ)).re =
      ((n : ℝ) - 1 - ((m : ℝ) + (p : ℝ) + (K : ℝ)) *
        (etaDenom M τ).re - (J : ℝ)) / (M 1 0 : ℝ) - y := by
  simp [modularPhiZeroPoint]
  ring

/-- S03. All infinitely many actual branches keep a common baseline separation. Project to the real
parameter axis and use labeled local finiteness in a bounded real strip, then keep a common
separation for the finite dangerous set. [RW26, p. 6]. The full-disk statement is included. -/
theorem uniform_baseline_gap (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p m : ℤ) (hT : 0 < g1T M τ₀) (D : G1VerticalChain)
    (hD : G1Separates D (g1NumeratorPoles M τ₀ n m)
      (g1InversePoles M τ₀ y n p m)) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
      ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        ∀ b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m),
          ε ≤ |(ModularCluster.branchPoint M
            (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b).re - D.crossing| := by
  let k := G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m
  have hsep := (separatesAt_iff_labels D M (τ₀ : ℂ) y n p m).mp
    ((G1FixedSeparation.separatesAt_ofReal_iff D M τ₀ y n p m).mpr hD)
  obtain ⟨ρ₀, hρ₀, hdom, hfin⟩ := finite_real_strip_labels M hM τ₀ y n p m
    (real_mem_modularPhiDomain M τ₀ hT) (|D.crossing| + 1) (by positivity)
  have hnear : {b | b ∈ ModularCluster.labels M k ∧
      ∃ τ ∈ ModularSector.parameterDisk τ₀ ρ₀,
        |(ModularCluster.branchPoint M k τ b).re - D.crossing| < 1}.Finite := by
    apply hfin.subset
    rintro b ⟨hb, τ, hτ, hgap⟩
    refine ⟨hb, τ, hτ, ?_⟩
    have htri : |(ModularCluster.branchPoint M k τ b).re| ≤
        |(ModularCluster.branchPoint M k τ b).re - D.crossing| + |D.crossing| := by
      simpa only [sub_add_cancel] using
        abs_add_le ((ModularCluster.branchPoint M k τ b).re - D.crossing) D.crossing
    linarith
  obtain ⟨ρ, ε, hρ, hε, hle, hgap⟩ := uniform_gap_of_finite_nearby
    (ModularCluster.labels M k) (τ₀ : ℂ)
    (fun b τ => |(ModularCluster.branchPoint M k τ b).re - D.crossing|)
    (fun b _ => ((Complex.continuous_re.comp (branch_continuous M k b)).sub continuous_const).abs)
    (fun b hb => abs_pos.mpr (sub_ne_zero.mpr (hsep.2 b hb).1)) ρ₀ hρ₀ hnear
  exact ⟨ρ, ε, hρ, hε,
    fun τ hτ => hdom (Metric.closedBall_subset_closedBall hle hτ), hgap⟩

/-- S04. One positive distance from every actual branch to every fixed circle boundary. [RW26, p.
6]. -/
theorem uniform_circle_gap (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p m : ℤ) (hT : 0 < g1T M τ₀) (D : G1VerticalChain)
    (hD : G1Separates D (g1NumeratorPoles M τ₀ n m)
      (g1InversePoles M τ₀ y n p m)) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
      ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ r ∈ D.centers,
        ∀ b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m),
          ε ≤ |dist (ModularCluster.branchPoint M
            (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b) (r : ℂ) - D.radius r| := by
  let k := G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m
  have hsep := (separatesAt_iff_labels D M (τ₀ : ℂ) y n p m).mp
    ((G1FixedSeparation.separatesAt_ofReal_iff D M τ₀ y n p m).mpr hD)
  have hτ₀ := real_mem_modularPhiDomain M τ₀ hT
  choose ρr εr hr using fun r : {r : ℝ // r ∈ D.centers} =>
    uniform_circle_gap_single M hM k (τ₀ : ℂ) (r.val : ℂ) (D.radius r.val)
      hτ₀ (fun b hb => (hsep.2 b hb).2.1 r.val r.property)
  obtain ⟨ρd, hρd, hdom⟩ := ModularCluster.RegularityAux.closedBall_in_open
    (ModularCluster.isOpen_modularPhiDomain M) hτ₀
  obtain ⟨ρ₁, hρ₁, hleρ⟩ := ModularCluster.exists_pos_le_of_finset Finset.univ
    ρr (fun r _ => (hr r).1)
  obtain ⟨ε, hε, hleε⟩ := ModularCluster.exists_pos_le_of_finset Finset.univ
    εr (fun r _ => (hr r).2.1)
  refine ⟨min ρd ρ₁, ε, lt_min hρd hρ₁, hε,
    fun τ hτ => hdom (Metric.closedBall_subset_closedBall (min_le_left _ _) hτ), ?_⟩
  intro τ hτ r hrD b hb
  let i : {r : ℝ // r ∈ D.centers} := ⟨r, hrD⟩
  have hle : min ρd ρ₁ ≤ ρr i :=
    (min_le_right _ _).trans (hleρ i (Finset.mem_univ _))
  exact (hleε i (Finset.mem_univ _)).trans
    ((hr i).2.2.2 τ (Metric.closedBall_subset_closedBall hle hτ) b hb)

/-- S05. Baseline-side assignments stay exactly equal to the initial ones. [RW26, p. 7, p. 13]. -/
theorem baseline_side_stable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p m : ℤ) (hT : 0 < g1T M τ₀) (D : G1VerticalChain)
    (hD : G1Separates D (g1NumeratorPoles M τ₀ n m)
      (g1InversePoles M τ₀ y n p m)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
      ∀ b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m),
        ((ModularCluster.branchPoint M
          (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b).re < D.crossing ↔
        (ModularCluster.branchPoint M
          (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) (τ₀ : ℂ) b).re < D.crossing) := by
  obtain ⟨ρ, ε, hρ, hε, _, hgap⟩ := uniform_baseline_gap M hM τ₀ y n p m hT D hD
  refine ⟨ρ, hρ, ?_⟩
  intro τ hτ b hb
  apply lt_iff_on_disk (τ₀ : ℂ) ρ hρ.le
    (fun τ => (ModularCluster.branchPoint M
      (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b).re)
    (Complex.continuous_re.comp (branch_continuous M _ b)) D.crossing ?_ τ hτ
  intro v hv he
  have := hgap v hv b hb
  rw [he, sub_self, abs_zero] at this
  exact (not_le_of_gt hε) this

/-- S06. Arbitrary contract circles track their initial inside relation. No equality-to-center is
asserted. [RW26, p. 7, p. 13]. -/
theorem circle_membership_stable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p m : ℤ) (hT : 0 < g1T M τ₀) (D : G1VerticalChain)
    (hD : G1Separates D (g1NumeratorPoles M τ₀ n m)
      (g1InversePoles M τ₀ y n p m)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
      ∀ r ∈ D.centers,
        ∀ b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m),
          (dist (ModularCluster.branchPoint M
            (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b) (r : ℂ) < D.radius r ↔
          dist (ModularCluster.branchPoint M
            (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) (τ₀ : ℂ) b) (r : ℂ) < D.radius r) := by
  obtain ⟨ρ, ε, hρ, hε, _, hgap⟩ := uniform_circle_gap M hM τ₀ y n p m hT D hD
  refine ⟨ρ, hρ, ?_⟩
  intro τ hτ r hr b hb
  apply lt_iff_on_disk (τ₀ : ℂ) ρ hρ.le
    (fun τ => dist (ModularCluster.branchPoint M
      (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b) (r : ℂ))
    ((branch_continuous M _ b).dist continuous_const) (D.radius r) ?_ τ hτ
  intro v hv he
  have := hgap v hv r hr b hb
  rw [he, sub_self, abs_zero] at this
  exact (not_le_of_gt hε) this

/-- S07. Every fixed chain admitted by the G1 contract works on a full disk. [RW26, p. 7, p. 13]. -/
theorem separating_chain_stable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p m : ℤ) (hT : 0 < g1T M τ₀) (D : G1VerticalChain)
    (hD : G1Separates D (g1NumeratorPoles M τ₀ n m)
      (g1InversePoles M τ₀ y n p m)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        G1FixedSeparation.SeparatesAt D M τ (y : ℂ) n p m := by
  obtain ⟨ρ₁, ε₁, hρ₁, hε₁, hdom, hgap₁⟩ :=
    uniform_baseline_gap M hM τ₀ y n p m hT D hD
  obtain ⟨ρ₂, ε₂, hρ₂, hε₂, _, hgap₂⟩ :=
    uniform_circle_gap M hM τ₀ y n p m hT D hD
  obtain ⟨ρ₃, hρ₃, hside⟩ := baseline_side_stable M hM τ₀ y n p m hT D hD
  obtain ⟨ρ₄, hρ₄, hcircle⟩ := circle_membership_stable M hM τ₀ y n p m hT D hD
  let ρ := min (min ρ₁ ρ₂) (min ρ₃ ρ₄)
  have hle₁ : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hle₂ : ρ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hle₃ : ρ ≤ ρ₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₄ : ρ ≤ ρ₄ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ hρ₄),
    fun τ hτ => hdom (Metric.closedBall_subset_closedBall hle₁ hτ), ?_⟩
  intro τ hτ
  have hτ₁ := Metric.closedBall_subset_closedBall hle₁ hτ
  have hτ₂ := Metric.closedBall_subset_closedBall hle₂ hτ
  have hτ₃ := Metric.closedBall_subset_closedBall hle₃ hτ
  have hτ₄ := Metric.closedBall_subset_closedBall hle₄ hτ
  have hsep := (separatesAt_iff_labels D M (τ₀ : ℂ) y n p m).mp
    ((G1FixedSeparation.separatesAt_ofReal_iff D M τ₀ y n p m).mpr hD)
  apply (separatesAt_iff_labels D M τ y n p m).mpr
  refine ⟨hsep.1, ?_⟩
  intro b hb
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have := hgap₁ τ hτ₁ b hb
    rw [he, sub_self, abs_zero] at this
    exact (not_le_of_gt hε₁) this
  · intro r hr he
    have := hgap₂ τ hτ₂ r hr b hb
    rw [he, sub_self, abs_zero] at this
    exact (not_le_of_gt hε₂) this
  · have hwind : G1FixedSeparation.circleWindingAt D
        (ModularCluster.branchPoint M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) τ b) =
        G1FixedSeparation.circleWindingAt D
        (ModularCluster.branchPoint M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) (τ₀ : ℂ) b) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [hcircle τ hτ₄ r hr b hb]
    calc
      _ = G1FixedSeparation.leftAssignmentAt D
          (ModularCluster.branchPoint M (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m)
            (τ₀ : ℂ) b) := by
        simp only [G1FixedSeparation.leftAssignmentAt, hside τ hτ₃ b hb, hwind]
      _ = _ := (hsep.2 b hb).2.2

/-- S08. The stronger existing whole-cluster tracking for ExplicitChain. [RW26, p. 6]. -/
theorem explicit_chain_stable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p m : ℤ) (hT : 0 < g1T M τ₀) (D : G1VerticalChain)
    (hD : G1FixedSeparation.ExplicitChain M τ₀ y n p m D) :
    ∃ ρ : ℝ, 0 < ρ ∧ ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        g1T M τ₀ / 2 < (etaDenom M τ).re ∧
          G1FixedSeparation.SeparatesAt D M τ (y : ℂ) n p m ∧
          G1FixedSeparation.TracksClusters D M τ₀ y τ n p m := by
  have hsep := G1FixedSeparation.explicitChain_separates M hM τ₀ y hT n p m D hD
  obtain ⟨ρ₁, hρ₁, hdom, hsep₁⟩ := separating_chain_stable M hM τ₀ y n p m hT D hsep
  obtain ⟨ρ₂, hρ₂, hcircle⟩ := circle_membership_stable M hM τ₀ y n p m hT D hsep
  have hTcont : Continuous (fun τ : ℂ => (etaDenom M τ).re) := by
    unfold etaDenom
    fun_prop
  have hTcenter : (etaDenom M (τ₀ : ℂ)).re = g1T M τ₀ := by
    simp [etaDenom, g1T]
  obtain ⟨ρ₃, hρ₃, hT₃⟩ := exists_closedBall_of_eventually
    (hTcont.continuousAt.eventually (isOpen_Ioi.mem_nhds
      (show g1T M τ₀ / 2 < (etaDenom M (τ₀ : ℂ)).re by rw [hTcenter]; linarith)))
  let ρ := min ρ₁ (min ρ₂ ρ₃)
  have hle₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hle₂ : ρ ≤ ρ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₃ : ρ ≤ ρ₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, lt_min hρ₁ (lt_min hρ₂ hρ₃),
    fun τ hτ => hdom (Metric.closedBall_subset_closedBall hle₁ hτ), ?_⟩
  intro τ hτ
  refine ⟨hT₃ τ (Metric.closedBall_subset_closedBall hle₃ hτ),
    hsep₁ τ (Metric.closedBall_subset_closedBall hle₁ hτ), ?_⟩
  intro r hr K J hKJ
  have hb : (false, K, J) ∈ ModularCluster.labels M
      (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m) := by
    simpa [ModularCluster.labels, G1Pinch.ratioData] using hKJ
  have hstable := hcircle τ (Metric.closedBall_subset_closedBall hle₂ hτ) r hr
    (false, K, J) hb
  simp only [ModularCluster.branchPoint, G1Pinch.ratioData, Bool.false_eq_true,
    if_false] at hstable
  rw [hstable]
  have hz : modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ) =
      (((modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ)).re) : ℂ) := by
    simpa only [ModularCluster.branchPoint, G1Pinch.ratioData, Bool.false_eq_true,
      if_false, Complex.ofReal_re] using
      ratio_branch_shadow M y n p m (τ₀ : ℂ) (false, K, J)
  constructor
  · intro hin
    by_contra hne
    have hx : (modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ)).re ∈
        g1InversePoles M τ₀ y n p m := by
      exact ⟨K, J, hKJ, hz.symm⟩
    have hxne : (modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ)).re ≠ r := by
      intro he
      exact hne (hz.trans (congrArg (fun x : ℝ => (x : ℂ)) he))
    have hout := (hD.2.2.2.1 r hr).2.2.2 _ hx hxne
    have hdist : dist (modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ))
        (r : ℂ) = |(modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ)).re - r| := by
      conv_lhs => rw [hz]
      simp [dist_eq_norm, ← Complex.ofReal_sub]
    rw [hdist] at hin
    linarith
  · intro he
    rw [he, dist_self]
    exact (hD.2.2.2.1 r hr).1

/-- S09. G1 contract existence plus one full-disk radius for all m. [RW26, p. 6, p. 7]. No integral
window is needed for this geometry. -/
theorem exists_fixed_separating_family (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p : ℤ) (hT : 0 < g1T M τ₀) (hpinch : g1NoPinch M τ₀ y p) :
    ∃ (D : Fin (M 1 0).toNat → G1VerticalChain) (ρ : ℝ),
      0 < ρ ∧ ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M ∧
        ∀ m : Fin (M 1 0).toNat,
          G1FixedSeparation.ExplicitChain M τ₀ y n p (m : ℤ) (D m) ∧
          G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
            (g1InversePoles M τ₀ y n p (m : ℤ)) ∧
          ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
            G1FixedSeparation.SeparatesAt (D m) M τ (y : ℂ) n p (m : ℤ) ∧
            G1FixedSeparation.TracksClusters (D m) M τ₀ y τ n p (m : ℤ) := by
  choose D hD using fun m : Fin (M 1 0).toNat =>
    G1FixedSeparation.exists_explicitChain M hM τ₀ y hT n p (m : ℤ) hpinch
  choose ρm hρm hdomm hstm using fun m : Fin (M 1 0).toNat =>
    explicit_chain_stable M hM τ₀ y n p (m : ℤ) hT (D m) (hD m)
  obtain ⟨ρd, hρd, hdom⟩ := ModularCluster.RegularityAux.closedBall_in_open
    (ModularCluster.isOpen_modularPhiDomain M) (real_mem_modularPhiDomain M τ₀ hT)
  obtain ⟨ρ₁, hρ₁, hle⟩ := ModularCluster.exists_pos_le_of_finset Finset.univ
    ρm (fun m _ => hρm m)
  refine ⟨D, min ρd ρ₁, lt_min hρd hρ₁,
    fun τ hτ => hdom (Metric.closedBall_subset_closedBall (min_le_left _ _) hτ), ?_⟩
  intro m
  refine ⟨hD m, G1FixedSeparation.explicitChain_separates M hM τ₀ y hT n p
    (m : ℤ) (D m) (hD m), ?_⟩
  intro τ hτ
  exact (hstm m τ (Metric.closedBall_subset_closedBall
    ((min_le_right _ _).trans (hle m (Finset.mem_univ _))) hτ)).2

/-- S10. The exact contract's arbitrary fixed family has one regular tube on all baselines and
circles. This excludes only numerator poles and denominator zeros. [RW26, p. 6]. -/
theorem family_regular_tube (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
      ∀ m : Fin (M 1 0).toNat,
        (∀ t : ℝ, (g1VerticalPoint (D m).crossing t, τ) ∈
          ModularCluster.regularDomain M
            (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p (m : ℤ))) ∧
        (∀ r ∈ (D m).centers, ∀ θ : ℝ,
          (circleMap (r : ℂ) ((D m).radius r) θ, τ) ∈
            ModularCluster.regularDomain M
              (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p (m : ℤ))) := by
  let P : Fin (M 1 0).toNat → ℝ → ℝ → Prop := fun m ρ _ =>
    ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
      τ ∈ modularPhiDomain M ∧
      G1FixedSeparation.SeparatesAt (D m) M τ (y : ℂ) n p (m : ℤ)
  have hmono : ∀ i r s B C, s ≤ r → B ≤ C → P i r B → P i s C := by
    intro i r s B C hsr _ hi τ hτ
    exact hi τ (Metric.closedBall_subset_closedBall hsr hτ)
  have hex : ∀ m ∈ (Finset.univ : Finset (Fin (M 1 0).toNat)),
      ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧ P m ρ B := by
    intro m _
    obtain ⟨ρ, hρ, hdom, hsep⟩ :=
      separating_chain_stable M hM τ₀ y n p (m : ℤ) hT (D m) (hD m)
    exact ⟨ρ, 1, hρ, zero_lt_one, fun τ hτ => ⟨hdom hτ, hsep τ hτ⟩⟩
  obtain ⟨ρ, B, hρ, _, hP⟩ :=
    ModularCluster.RegularityAux.finite_uniform_radius_bound Finset.univ P hmono hex
  refine ⟨ρ, hρ, ?_⟩
  intro τ hτ m
  obtain ⟨hdom, hsep⟩ := hP m (Finset.mem_univ _) τ hτ
  exact G1FixedSeparation.separatesAt_regularDomain M hM τ (w : ℂ) (y : ℂ)
    n h ell p (m : ℤ) (D m) hdom hsep

/-- S11. No cross-class collisions anywhere in a small full disk, for all G1 components. Same-class
multiple poles remain allowed. [RW26, p. 6]. -/
theorem noPinch_full_disk (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (n p : ℤ) (hT : 0 < g1T M τ₀) (hpinch : g1NoPinch M τ₀ y p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m : Fin (M 1 0).toNat,
        ModularCluster.crossSeparated M
          (G1Pinch.ratioData 0 (y : ℂ) n 0 0 p (m : ℤ)) τ := by
  obtain ⟨D, ρ, hρ, hdom, hsep⟩ := exists_fixed_separating_family M hM τ₀ y n p hT hpinch
  refine ⟨ρ, hρ, hdom, ?_⟩
  intro τ hτ m b hb b' hb' he
  have hs := (separatesAt_iff_labels (D m) M τ y n p (m : ℤ)).mp
    ((hsep m).2.2 τ hτ).1
  have ha := (hs.2 b hb).2.2
  have ha' := (hs.2 b' hb').2.2
  rw [he] at ha
  have hi := ha.symm.trans ha'
  cases h₁ : b.1 <;> cases h₂ : b'.1 <;> simp_all

/-- S12. A single circle-pullback bound for all components and every fixed circle, including the CCW
Jacobian. [RW26, p. 6]. -/
theorem family_circle_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m : Fin (M 1 0).toNat,
        ∀ r ∈ (D m).centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖g1CirclePullback
            (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
            r ((D m).radius r) θ‖ ≤ C := by
  obtain ⟨ρ, hρ, hreg⟩ := family_regular_tube M hM τ₀ w y n h ell p hT D hD
  let ι := Σ m : Fin (M 1 0).toNat, {r : ℝ // r ∈ (D m).centers}
  let P : ι → ℝ → ℝ → Prop := fun i s B =>
    ∀ τ ∈ ModularSector.parameterDisk τ₀ s, ∀ θ ∈ Icc 0 (2 * Real.pi),
      ‖g1CirclePullback
        (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (i.1 : ℤ))
        i.2.val ((D i.1).radius i.2.val) θ‖ ≤ B
  have hmono : ∀ i r s B C, s ≤ r → B ≤ C → P i r B → P i s C := by
    intro i r s B C hsr hBC hi τ hτ θ hθ
    exact (hi τ (Metric.closedBall_subset_closedBall hsr hτ) θ hθ).trans hBC
  have hex : ∀ i : ι, ∃ s B : ℝ, 0 < s ∧ 0 < B ∧ P i s B := by
    intro i
    let k := G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p (i.1 : ℤ)
    let a : ℂ := (i.2.val : ℂ)
    let r := (D i.1).radius i.2.val
    let f : ℂ × ℝ → ℂ := fun q =>
      ModularCluster.circleKernel M k a r q.1 q.2
    have hmap : Continuous (fun q : ℂ × ℝ => (circleMap a r q.2, q.1)) :=
      ((continuous_circleMap a r).comp continuous_snd).prodMk continuous_fst
    have hmt : MapsTo (fun q : ℂ × ℝ => (circleMap a r q.2, q.1))
        (ModularSector.parameterDisk τ₀ ρ ×ˢ Icc 0 (2 * Real.pi))
        (ModularCluster.regularDomain M k) := by
      intro q hq
      exact (hreg q.1 hq.1 i.1).2 i.2.val i.2.property q.2
    have hc : ContinuousOn f
        (ModularSector.parameterDisk τ₀ ρ ×ˢ Icc 0 (2 * Real.pi)) := by
      exact ((ModularCluster.kernel_joint_analytic M hM k).continuousOn.comp
        hmap.continuousOn hmt).mul
        (continuous_const.mul (((continuous_circleMap a r).comp continuous_snd).sub
          continuous_const)).continuousOn
    obtain ⟨B, hB⟩ := ((isCompact_closedBall (τ₀ : ℂ) ρ).prod
      isCompact_Icc).bddAbove_image hc.norm
    refine ⟨ρ, max B 1, hρ,
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro τ hτ θ hθ
    have hb : ‖f (τ, θ)‖ ≤ B := hB ⟨(τ, θ), ⟨hτ, hθ⟩, rfl⟩
    exact hb.trans (le_max_left _ _)
  obtain ⟨s, B, hs, hB, hall⟩ :=
    ModularCluster.RegularityAux.finite_uniform_radius_bound Finset.univ P hmono
      (fun i _ => hex i)
  refine ⟨s, B, hs, hB, ?_⟩
  intro τ hτ m r hr θ hθ
  exact hall ⟨m, r, hr⟩ (Finset.mem_univ _) τ hτ θ hθ

#check @G1FixedSeparation.separatesAt_ofReal_iff
#check @ModularCluster.regularDomain_iff_no_labels
#check @ModularCluster.kernel_joint_analytic
#check @exists_fixed_separating_family
#check @family_regular_tube
#print G1FixedSeparation.TracksClusters

end SICLean.L4.G1BilateralSeparation
