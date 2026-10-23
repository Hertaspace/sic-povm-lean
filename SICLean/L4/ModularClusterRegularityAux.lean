import SICLean.L4.ModularClusterGeometry

set_option autoImplicit false

/-! Local chart and compact tube lemmas for the fixed-circle kernels. -/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.ModularCluster.RegularityAux

lemma chartNumerator_ne_zero_iff (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (κ : ℕ → ℤ) (q : ℂ × ℂ)
    (hq : q ∈ modularPhiChartDomain M r n κ) :
    modularPhiChartNumerator M r n κ q.1 q.2 ≠ 0 ↔
      modularPhiZeroMultiplicity M r n q.1 q.2 = 0 := by
  rw [(modularPhi_multiplicity_pullback M hM r n q.1 q.2 hq.1).2]
  simp only [modularPhiChartNumerator, Finset.prod_ne_zero_iff, Finset.sum_eq_zero_iff]
  apply forall₂_congr
  intro j hj
  exact continuationNumerator_ne_zero_iff _ _ _
    (modularPhi_sqrt_admissible M q.2 hq.1).1 (hq.2 j hj)

lemma inverse_locus_isOpen (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ) :
    IsOpen {q : ℂ × ℂ | q.2 ∈ modularPhiDomain M ∧
      modularPhiZeroMultiplicity M r n q.1 q.2 = 0} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hτ, hz⟩
  obtain ⟨U, hU, hqU, hchart, hN, hD, hfreq, heq⟩ :=
    modularPhi_joint_local_quotient M hM r n q hτ
  let κ : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M r n j q.1 q.2).1
    (modularPhiFactorPoint M r n j q.1 q.2).2
  have hNz : modularPhiChartNumerator M r n κ q.1 q.2 ≠ 0 :=
    (chartNumerator_ne_zero_iff M hM r n κ q (hchart hqU)).mpr hz
  have hnonzero : ∀ᶠ v in 𝓝 q, modularPhiChartNumerator M r n κ v.1 v.2 ≠ 0 :=
    (hN q hqU).continuousAt.eventually_ne hNz
  filter_upwards [hU.mem_nhds hqU, hnonzero] with v hv hn
  exact ⟨(hchart hv).1, (chartNumerator_ne_zero_iff M hM r n κ v (hchart hv)).mp hn⟩

lemma inverse_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ) :
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ => (modularPhi M r n q.1 q.2)⁻¹)
      {q : ℂ × ℂ | q.2 ∈ modularPhiDomain M ∧
        modularPhiZeroMultiplicity M r n q.1 q.2 = 0} := by
  rintro q ⟨hτ, hz⟩
  obtain ⟨U, hU, hqU, hchart, hN, hD, hfreq, heq⟩ :=
    modularPhi_joint_local_quotient M hM r n q hτ
  let κ : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M r n j q.1 q.2).1
    (modularPhiFactorPoint M r n j q.1 q.2).2
  have hNz : modularPhiChartNumerator M r n κ q.1 q.2 ≠ 0 :=
    (chartNumerator_ne_zero_iff M hM r n κ q (hchart hqU)).mpr hz
  apply ((hD q hqU).div (hN q hqU) hNz).congr
  filter_upwards [hU.mem_nhds hqU] with v hv
  rw [modularPhi_eq_chart M hM r n κ v (hchart hv), modularPhiChart, inv_div]
  rfl

lemma boundaries_isCompact (C : Circles) : IsCompact (boundaries C) := by
  have heq : boundaries C = ⋃ a ∈ C.centers, Metric.sphere a (C.radius a) := by
    ext z
    simp [boundaries]
  rw [heq]
  exact C.centers.isCompact_biUnion fun a _ => isCompact_sphere a (C.radius a)

lemma closedBall_in_open {P : Type*} [PseudoMetricSpace P] {U : Set P}
    (hU : IsOpen U) {p : P} (hp : p ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall p ρ ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro q hq
  exact hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hq) (half_lt_self hε))

lemma compact_slice_tube {P : Type*} [PseudoMetricSpace P]
    {K : Set ℂ} (hK : IsCompact K) {U : Set (ℂ × P)} (hU : IsOpen U)
    {p : P} (hp : ∀ z ∈ K, (z, p) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ K ×ˢ Metric.closedBall p ρ ⊆ U := by
  have hsub : K ×ˢ ({p} : Set P) ⊆ U := by
    rintro ⟨z, v⟩ ⟨hz, hv⟩
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact hp z hz
  obtain ⟨V, W, hV, hW, hKV, hpW, hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hsub
  obtain ⟨ρ, hρ, hρW⟩ := closedBall_in_open hW (hpW (Set.mem_singleton p))
  exact ⟨ρ, hρ, fun q hq => hVW ⟨hKV hq.1, hρW hq.2⟩⟩

lemma compact_slice_bound {P : Type*} [PseudoMetricSpace P] [ProperSpace P]
    {K : Set ℂ} (hK : IsCompact K) {U : Set (ℂ × P)} (hU : IsOpen U)
    {p : P} (hp : ∀ z ∈ K, (z, p) ∈ U) {f : ℂ × P → ℂ}
    (hf : ContinuousOn f U) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧
      ∀ z ∈ K, ∀ v ∈ Metric.closedBall p ρ, (z, v) ∈ U ∧ ‖f (z, v)‖ ≤ B := by
  obtain ⟨ρ, hρ, hsub⟩ := compact_slice_tube hK hU hp
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall p ρ)).bddAbove_image
    (hf.mono hsub).norm
  refine ⟨ρ, max B 1, hρ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz v hv
  exact ⟨hsub ⟨hz, hv⟩,
    (hB (Set.mem_image_of_mem _ ⟨hz, hv⟩)).trans (le_max_left _ _)⟩

lemma finite_uniform_radius_bound {ι : Type*} (S : Finset ι)
    (P : ι → ℝ → ℝ → Prop)
    (hmono : ∀ i r s B D, s ≤ r → B ≤ D → P i r B → P i s D)
    (hex : ∀ i ∈ S, ∃ r B : ℝ, 0 < r ∧ 0 < B ∧ P i r B) :
    ∃ r B : ℝ, 0 < r ∧ 0 < B ∧ ∀ i ∈ S, P i r B := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 1, zero_lt_one, zero_lt_one, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨r, B, hr, hB, hS⟩ := ih (fun j hj => hex j (Finset.mem_insert_of_mem hj))
    obtain ⟨s, D, hs, hD, hiP⟩ := hex i (Finset.mem_insert_self _ _)
    refine ⟨min r s, max B D, lt_min hr hs,
      lt_of_lt_of_le hB (le_max_left _ _), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hmono j s (min r s) D (max B D) (min_le_right _ _) (le_max_right _ _) hiP
    · exact hmono j r (min r s) B (max B D) (min_le_left _ _) (le_max_left _ _) (hS j hj)

theorem poleBudget_eq_multiplicities
    (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    poleBudget M k z τ =
      modularPhiPoleMultiplicity M (k.m + 1) k.n z τ +
        if k.ratio = true then
          modularPhiZeroMultiplicity M (k.m + k.p) k.n (z + k.y) τ else 0 := by
  classical
  let P := modularPhiPoleIndices M (k.m + 1) k.n z τ
  let Z := modularPhiZeroIndices M (k.m + k.p) k.n (z + k.y) τ
  letI : Finite P :=
    (modularPhiDivisor_indices_finite M hM (k.m + 1) k.n z τ hτ).1.to_subtype
  letI : Finite Z :=
    (modularPhiDivisor_indices_finite M hM (k.m + k.p) k.n (z + k.y) τ hτ).2.to_subtype
  by_cases hr : k.ratio = true
  · let f : P ⊕ Z → fiber M k z τ := fun p =>
      match p with
      | Sum.inl p => ⟨(true, p.val), by
          change p.val ∈ modularPhiPoleLabels M (k.m + 1) k.n ∧
            modularPhiPolePoint M (k.m + 1) k.n τ p.val.1 p.val.2 = z
          exact ⟨p.property.1, p.property.2.symm⟩⟩
      | Sum.inr p => ⟨(false, p.val), by
          change (k.ratio = true ∧ p.val ∈ modularPhiZeroLabels M (k.m + k.p) k.n) ∧
            modularPhiZeroPoint M (k.m + k.p) k.n τ p.val.1 p.val.2 - k.y = z
          exact ⟨⟨hr, p.property.1⟩, sub_eq_iff_eq_add.mpr p.property.2.symm⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        cases a <;> cases b <;> simpa [f, Subtype.ext_iff] using hab
      · rintro ⟨⟨b, p⟩, hb⟩
        cases b
        · have hb' : p ∈ modularPhiZeroLabels M (k.m + k.p) k.n ∧
              modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2 - k.y = z := by
            simpa [fiber, labels, branchPoint, hr] using hb
          refine ⟨Sum.inr ⟨p, hb'.1, ?_⟩, rfl⟩
          exact (sub_eq_iff_eq_add.mp hb'.2).symm
        · have hb' : p ∈ modularPhiPoleLabels M (k.m + 1) k.n ∧
              modularPhiPolePoint M (k.m + 1) k.n τ p.1 p.2 = z := by
            simpa [fiber, labels, branchPoint] using hb
          exact ⟨Sum.inl ⟨p, hb'.1, hb'.2.symm⟩, rfl⟩
    calc
      poleBudget M k z τ = Nat.card (P ⊕ Z) := (Nat.card_eq_of_bijective f hf).symm
      _ = Nat.card P + Nat.card Z := Nat.card_sum
      _ = _ := by simp [P, Z, modularPhiPoleMultiplicity, modularPhiZeroMultiplicity, hr]
  · let f : P → fiber M k z τ := fun p => ⟨(true, p.val), by
      change p.val ∈ modularPhiPoleLabels M (k.m + 1) k.n ∧
        modularPhiPolePoint M (k.m + 1) k.n τ p.val.1 p.val.2 = z
      exact ⟨p.property.1, p.property.2.symm⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        simpa [f, Subtype.ext_iff] using hab
      · rintro ⟨⟨b, p⟩, hb⟩
        cases b
        · simp [fiber, labels, branchPoint, hr] at hb
        · have hb' : p ∈ modularPhiPoleLabels M (k.m + 1) k.n ∧
              modularPhiPolePoint M (k.m + 1) k.n τ p.1 p.2 = z := by
            simpa [fiber, labels, branchPoint] using hb
          exact ⟨⟨p, hb'.1, hb'.2.symm⟩, rfl⟩
    calc
      poleBudget M k z τ = Nat.card P := (Nat.card_eq_of_bijective f hf).symm
      _ = _ := by simp [P, modularPhiPoleMultiplicity, hr]

end SICLean.L4.ModularCluster.RegularityAux
