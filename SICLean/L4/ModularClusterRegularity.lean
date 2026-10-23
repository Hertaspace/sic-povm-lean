import SICLean.L4.ModularClusterGeometry
import SICLean.L4.ModularClusterRegularityAux

set_option autoImplicit false

/-!
# The actual kernels on fixed circle tubes

Fixed-circle regularity theorems. Joint-chart and compactness consequences are formalized
here. [RW26, p. 6].

The reciprocal of the specified Φ has value 0 at a Φ pole. This is its
correct analytic zero, unlike applying a product reflection identity at
that pole. Actual joint analyticity of the reciprocal on the no-zero
locus is a theorem below. No raw q quotient or new φ, Φ, μ, or sqrt is used.
For the ratio, cancellations can lower the pole order: poleBudget is
only a bound. Joint statements use open subsets of ℂ², never a punctured
ℂ² neighborhood that still contains polar curves.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.ModularCluster

/--
Literal E_m. [RW26, p. 7, (22), (23)].
-/
def phase (M : SL(2, ℤ)) (k : KernelData) (z τ : ℂ) : ℂ :=
  (((M 1 0 : ℂ) * z - (k.n : ℂ) + etaDenom M τ * (k.m : ℂ)) * k.w) /
      etaDenom M τ +
    (k.ell : ℂ) * (z + (k.m : ℂ) * τ) +
    (k.h : ℂ) * (z / etaDenom M τ + (k.n : ℂ) * etaMobius M τ)

/-- The two actual G1 kernels, with the common exponential included. -/
def kernel (M : SL(2, ℤ)) (k : KernelData) (z τ : ℂ) : ℂ :=
  modularPhi M (k.m + 1) k.n z τ *
    (if k.ratio = true then (modularPhi M (k.m + k.p) k.n (z + k.y) τ)⁻¹ else 1) *
    e (phase M k z τ)

/-- No zero of Φ. Its poles are included, and the reciprocal there is 0. -/
def inversePhiDomain (M : SL(2, ℤ)) (r n : ℤ) : Set (ℂ × ℂ) :=
  {q | q.2 ∈ modularPhiDomain M ∧ modularPhiZeroMultiplicity M r n q.1 q.2 = 0}

/-- Explicit candidate-pole exclusion, without any analytic hypothesis. -/
def regularDomain (M : SL(2, ℤ)) (k : KernelData) : Set (ℂ × ℂ) :=
  {q | q.2 ∈ modularPhiDomain M ∧
    modularPhiPoleMultiplicity M (k.m + 1) k.n q.1 q.2 = 0 ∧
    (k.ratio = true → modularPhiZeroMultiplicity M (k.m + k.p) k.n (q.1 + k.y) q.2 = 0)}

/-- Exact germ order, allowing cancellation in a ratio. -/
def kernelOrder (M : SL(2, ℤ)) (k : KernelData) (z τ : ℂ) : ℤ :=
  modularPhiDivisorOrder M (k.m + 1) k.n z τ -
    (if k.ratio = true then modularPhiDivisorOrder M (k.m + k.p) k.n (z + k.y) τ else 0)

/--
Openness is a local-finiteness consequence, not part of the definition; [RW26, p. 6].
-/
theorem inversePhiDomain_isOpen (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ) :
    IsOpen (inversePhiDomain M r n) := by
  exact RegularityAux.inverse_locus_isOpen M hM r n

/--
Actual pointwise reciprocal, including its analytic zero at Φ poles.
The proof uses the actual chart Φ=N/D, with N nonzero on the no-zero locus, so that
its inverse is D/N even at D=0; [RW26, p. 6] divisor sets.
-/
theorem inversePhi_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ) :
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ => (modularPhi M r n q.1 q.2)⁻¹)
      (inversePhiDomain M r n) := by
  exact RegularityAux.inverse_joint_analytic M hM r n

/--
Explicit domain is open. [RW26, p. 6].
-/
theorem regularDomain_isOpen (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData) :
    IsOpen (regularDomain M k) := by
  by_cases hr : k.ratio = true
  · have hshift : Continuous (fun q : ℂ × ℂ => (q.1 + k.y, q.2)) := by fun_prop
    convert ((modularPhiDivisor_domains_isOpen M hM (k.m + 1) k.n).1).inter
      ((inversePhiDomain_isOpen M hM (k.m + k.p) k.n).preimage hshift) using 1
    ext q
    simp [regularDomain, modularPhiHolomorphicDomain, inversePhiDomain, hr, and_assoc,
      and_left_comm]
  · convert (modularPhiDivisor_domains_isOpen M hM (k.m + 1) k.n).1 using 1
    ext q
    simp [regularDomain, modularPhiHolomorphicDomain, hr]

/--
The specified kernel is jointly analytic away from its possible poles;
denominator Φ poles are allowed; [RW26, p. 6] joint charts are inputs, not a circle-limit theorem.
-/
theorem kernel_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData) :
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ => kernel M k q.1 q.2) (regularDomain M k) := by
  intro q hq
  have hnum := modularPhi_joint_analytic_no_poles M hM (k.m + 1) k.n q ⟨hq.1, hq.2.1⟩
  have hT : etaDenom M q.2 ≠ 0 := etaDenom_ne_zero_of_mem M hq.1
  have hphase : AnalyticAt ℂ (fun v : ℂ × ℂ => e (phase M k v.1 v.2)) q := by
    have hz : AnalyticAt ℂ (fun v : ℂ × ℂ => v.1) q := analyticAt_fst
    have ht : AnalyticAt ℂ (fun v : ℂ × ℂ => v.2) q := analyticAt_snd
    unfold e phase etaMobius etaDenom
    fun_prop (disch := exact hT)
  unfold kernel
  by_cases hr : k.ratio = true
  · simp only [if_pos hr]
    have hshift : AnalyticAt ℂ (fun v : ℂ × ℂ => (v.1 + k.y, v.2)) q :=
      (analyticAt_fst.add analyticAt_const).prod analyticAt_snd
    exact (hnum.mul ((inversePhi_joint_analytic M hM (k.m + k.p) k.n
      (q.1 + k.y, q.2) ⟨hq.1, hq.2.2 hr⟩).comp (x := q) hshift)).mul hphase
  · simp only [if_neg hr, mul_one]
    exact hnum.mul hphase

/--
Fixed-τ meromorphy, with arbitrary center values still permitted at
candidate poles; [RW26, p. 6] charts.
-/
theorem kernel_meromorphic (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData)
    (τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    MeromorphicOn (fun z => kernel M k z τ) Set.univ := by
  intro z _
  have hnum := modularPhi_meromorphic M hM (k.m + 1) k.n τ hτ z (Set.mem_univ z)
  have hden : MeromorphicAt (fun v => modularPhi M (k.m + k.p) k.n (v + k.y) τ) z :=
    (modularPhi_meromorphic M hM (k.m + k.p) k.n τ hτ
      (z + k.y) (Set.mem_univ _)).comp_analyticAt (x := z)
        (g := fun v => v + k.y) (by fun_prop)
  have hphase : AnalyticAt ℂ (fun v => e (phase M k v τ)) z := by
    unfold e phase
    fun_prop
  unfold kernel
  by_cases hr : k.ratio = true
  · simp only [if_pos hr]
    exact (hnum.mul hden.inv).mul hphase.meromorphicAt
  · simp only [if_neg hr, mul_one]
    exact hnum.mul hphase.meromorphicAt

/--
Exact fixed-τ germ order, with no assertion about center continuity. [RW26, p. 6].
-/
theorem kernel_order (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    meromorphicOrderAt (fun w => kernel M k w τ) z = (kernelOrder M k z τ : WithTop ℤ) := by
  have hnum := modularPhi_meromorphic M hM (k.m + 1) k.n τ hτ z (Set.mem_univ z)
  have hden : MeromorphicAt (fun v => modularPhi M (k.m + k.p) k.n (v + k.y) τ) z :=
    (modularPhi_meromorphic M hM (k.m + k.p) k.n τ hτ
      (z + k.y) (Set.mem_univ _)).comp_analyticAt (x := z)
        (g := fun v => v + k.y) (by fun_prop)
  have hphase : AnalyticAt ℂ (fun v => e (phase M k v τ)) z := by
    unfold e phase
    fun_prop
  have hphaseOrder : meromorphicOrderAt (fun v => e (phase M k v τ)) z = 0 := by
    rw [hphase.meromorphicOrderAt_eq, hphase.analyticOrderAt_eq_zero.mpr (e_ne_zero _)]
    rfl
  unfold kernel kernelOrder
  by_cases hr : k.ratio = true
  · simp only [if_pos hr]
    have hm := meromorphicOrderAt_mul (hnum.mul hden.inv) hphase.meromorphicAt
    have hn := meromorphicOrderAt_mul hnum hden.inv
    change meromorphicOrderAt (fun v => modularPhi M (k.m + 1) k.n v τ *
      (modularPhi M (k.m + k.p) k.n (v + k.y) τ)⁻¹ * e (phase M k v τ)) z =
        meromorphicOrderAt (fun v => modularPhi M (k.m + 1) k.n v τ *
          (modularPhi M (k.m + k.p) k.n (v + k.y) τ)⁻¹) z +
            meromorphicOrderAt (fun v => e (phase M k v τ)) z at hm
    change meromorphicOrderAt (fun v => modularPhi M (k.m + 1) k.n v τ *
      (modularPhi M (k.m + k.p) k.n (v + k.y) τ)⁻¹) z =
        meromorphicOrderAt (fun v => modularPhi M (k.m + 1) k.n v τ) z +
          meromorphicOrderAt (fun v => (modularPhi M (k.m + k.p) k.n (v + k.y) τ)⁻¹) z at hn
    rw [hm, hphaseOrder, add_zero, hn]
    have hd : meromorphicOrderAt (fun v => modularPhi M (k.m + k.p) k.n (v + k.y) τ) z =
        (modularPhiDivisorOrder M (k.m + k.p) k.n (z + k.y) τ : WithTop ℤ) :=
      (meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := fun v =>
        modularPhi M (k.m + k.p) k.n v τ) (x := z) (c := k.y)).trans
          (modularPhi_order M hM (k.m + k.p) k.n (z + k.y) τ hτ)
    rw [fun_meromorphicOrderAt_inv, hd, modularPhi_order M hM (k.m + 1) k.n z τ hτ]
    simp [sub_eq_add_neg]
  · simp only [if_neg hr, mul_one, sub_zero]
    rw [fun_meromorphicOrderAt_mul hnum hphase.meromorphicAt,
      hphaseOrder, add_zero, modularPhi_order M hM (k.m + 1) k.n z τ hτ]

/--
Budget is a bound, including when two Φ poles or two Φ zeros cancel
in the ratio; [RW26, p. 6].
-/
theorem kernelOrder_lower_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    -(poleBudget M k z τ : ℤ) ≤ kernelOrder M k z τ := by
  rw [RegularityAux.poleBudget_eq_multiplicities M hM k z τ hτ]
  unfold kernelOrder modularPhiDivisorOrder
  split_ifs <;> push_cast <;> omega

/--
Bridge from the geometric circle selection to actual regularity; [RW26, p. 6].
-/
theorem regularDomain_iff_no_labels (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (z τ : ℂ) :
    (z, τ) ∈ regularDomain M k ↔
      τ ∈ modularPhiDomain M ∧ ∀ b ∈ labels M k, z ≠ branchPoint M k τ b := by
  by_cases hτ : τ ∈ modularPhiDomain M
  · have hzero : poleBudget M k z τ = 0 ↔
        ∀ b ∈ labels M k, z ≠ branchPoint M k τ b := by
      constructor
      · intro h b hb heq
        have hpos : 0 < poleBudget M k z τ :=
          (Set.natCard_pos (fiber_finite M hM k z τ hτ)).mpr ⟨b, hb, heq.symm⟩
        omega
      · intro h
        have hempty : fiber M k z τ = ∅ := by
          ext b
          simp only [fiber, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          intro hb hp
          exact h b hb hp.symm
        simp [poleBudget, hempty]
    rw [← hzero, RegularityAux.poleBudget_eq_multiplicities M hM k z τ hτ]
    simp only [regularDomain, mem_ofPred_eq, hτ, true_and, Nat.add_eq_zero_iff]
    by_cases hr : k.ratio = true <;> simp [hr]
  · simp [regularDomain, hτ]

/--
A common full closed tube over finitely many fixed circle boundaries.
The center hypothesis is explicit divisor exclusion; [RW26, p. 6] divisor sets.
-/
theorem exists_regular_boundary_tube (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M) (C : Circles)
    (hsafe : ∀ z ∈ boundaries C, (z, τ₀) ∈ regularDomain M k) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ z ∈ boundaries C, (z, τ) ∈ regularDomain M k := by
  obtain ⟨r, hr, htube⟩ := RegularityAux.compact_slice_tube
    (RegularityAux.boundaries_isCompact C) (regularDomain_isOpen M hM k) hsafe
  obtain ⟨s, hs, hdomain⟩ :=
    RegularityAux.closedBall_in_open (modularPhiDomain_isOpen M) hτ₀
  refine ⟨min r s, lt_min hr hs,
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hdomain, ?_⟩
  intro τ hτ z hz
  exact htube ⟨hz, Metric.closedBall_subset_closedBall (min_le_left _ _) hτ⟩

/--
Joint continuity on the compact circle tube, not merely fixed-τ
meromorphy; [RW26, p. 6] sets.
-/
theorem continuousOn_boundary_tube (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (ρ : ℝ) (C : Circles)
    (hsafe : ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ z ∈ boundaries C,
      (z, τ) ∈ regularDomain M k) :
    ContinuousOn (fun q : ℂ × ℂ => kernel M k q.1 q.2)
      (boundaries C ×ˢ Metric.closedBall τ₀ ρ) := by
  exact (kernel_joint_analytic M hM k).continuousOn.mono
    (fun q hq => hsafe q.2 hq.2 q.1 hq.1)

/--
One bound precedes every circle, parameter, and point. It does not bound
any individual residue. [RW26, p. 6]. The bound holds on a full ball.
-/
theorem exists_uniform_boundary_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M) (C : Circles)
    (hsafe : ∀ z ∈ boundaries C, (z, τ₀) ∈ regularDomain M k) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧ Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ z ∈ boundaries C,
        (z, τ) ∈ regularDomain M k ∧ ‖kernel M k z τ‖ ≤ B := by
  obtain ⟨r, B, hr, hB, hbound⟩ := RegularityAux.compact_slice_bound
    (RegularityAux.boundaries_isCompact C) (regularDomain_isOpen M hM k) hsafe
    (f := fun q : ℂ × ℂ => kernel M k q.1 q.2) (kernel_joint_analytic M hM k).continuousOn
  obtain ⟨s, hs, hdomain⟩ :=
    RegularityAux.closedBall_in_open (modularPhiDomain_isOpen M) hτ₀
  refine ⟨min r s, B, lt_min hr hs, hB,
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hdomain, ?_⟩
  intro τ hτ z hz
  exact hbound z hz τ (Metric.closedBall_subset_closedBall (min_le_left _ _) hτ)

/--
Common constants across a finite index family, retaining its own
circles for each kernel. [RW26, p. 6]. The bounds hold on full balls.
-/
theorem finite_family_uniform_boundary_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (S : Finset KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M)
    (C : KernelData → Circles)
    (hsafe : ∀ k ∈ S, ∀ z ∈ boundaries (C k), (z, τ₀) ∈ regularDomain M k) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧ Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ k ∈ S, ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ z ∈ boundaries (C k),
        (z, τ) ∈ regularDomain M k ∧ ‖kernel M k z τ‖ ≤ B := by
  classical
  revert hsafe
  induction S using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨ρ, hρ, hdomain⟩ :=
      RegularityAux.closedBall_in_open (modularPhiDomain_isOpen M) hτ₀
    exact ⟨ρ, 1, hρ, zero_lt_one, hdomain, by simp⟩
  | @insert k S hk ih =>
    intro hsafe
    obtain ⟨r, B, hr, hB, hdomain, hS⟩ :=
      ih (fun j hj => hsafe j (Finset.mem_insert_of_mem hj))
    obtain ⟨s, D, hs, hD, hdomain', hkbound⟩ :=
      exists_uniform_boundary_bound M hM k τ₀ hτ₀ (C k) (hsafe k (Finset.mem_insert_self _ _))
    refine ⟨min r s, max B D, lt_min hr hs,
      lt_of_lt_of_le hB (le_max_left _ _),
      (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hdomain, ?_⟩
    intro j hj τ hτ z hz
    rcases Finset.mem_insert.mp hj with rfl | hj
    · obtain ⟨hreg, hnorm⟩ := hkbound τ
        (Metric.closedBall_subset_closedBall (min_le_right _ _) hτ) z hz
      exact ⟨hreg, hnorm.trans (le_max_right _ _)⟩
    · obtain ⟨hreg, hnorm⟩ := hS j hj τ
        (Metric.closedBall_subset_closedBall (min_le_left _ _) hτ) z hz
      exact ⟨hreg, hnorm.trans (le_max_left _ _)⟩

/--
Joint (τ,w,y) control for the local boundedness and removability step.
There is one polydisk radius and bound, chosen before the continuous
parameters and the finite index family. The fixed-(w, y) boundary bound
uses the actual joint charts. [RW26, p. 6].
-/
theorem finite_family_uniform_boundary_bound_parameters (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (S : Finset KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M)
    (C : KernelData → Circles)
    (hsafe : ∀ k ∈ S, ∀ z ∈ boundaries (C k), (z, τ₀) ∈ regularDomain M k) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧ Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ k ∈ S, ∀ τ ∈ Metric.closedBall τ₀ ρ,
        ∀ w ∈ Metric.closedBall k.w ρ, ∀ y ∈ Metric.closedBall k.y ρ,
          ∀ z ∈ boundaries (C k),
            (z, τ) ∈ regularDomain M (withParameters k w y) ∧
              ‖kernel M (withParameters k w y) z τ‖ ≤ B := by
  let P : KernelData → ℝ → ℝ → Prop := fun k r B =>
    ∀ τ ∈ Metric.closedBall τ₀ r, ∀ w ∈ Metric.closedBall k.w r,
      ∀ y ∈ Metric.closedBall k.y r, ∀ z ∈ boundaries (C k),
        (z, τ) ∈ regularDomain M (withParameters k w y) ∧
          ‖kernel M (withParameters k w y) z τ‖ ≤ B
  have hmono : ∀ k r s B D, s ≤ r → B ≤ D → P k r B → P k s D := by
    intro k r s B D hsr hBD h τ hτ w hw y hy z hz
    obtain ⟨hreg, hnorm⟩ := h τ (Metric.closedBall_subset_closedBall hsr hτ)
      w (Metric.closedBall_subset_closedBall hsr hw) y (Metric.closedBall_subset_closedBall hsr hy) z hz
    exact ⟨hreg, hnorm.trans hBD⟩
  have hsingle : ∀ k ∈ S, ∃ r B : ℝ, 0 < r ∧ 0 < B ∧ P k r B := by
    intro k hk
    let V : Set (ℂ × (ℂ × ℂ × ℂ)) := {q |
      (q.1, q.2.1) ∈ modularPhiHolomorphicDomain M (k.m + 1) k.n ∧
      (k.ratio = true → (q.1 + q.2.2.2, q.2.1) ∈ inversePhiDomain M (k.m + k.p) k.n)}
    have hV : IsOpen V := by
      have hn : IsOpen {q : ℂ × (ℂ × ℂ × ℂ) |
          (q.1, q.2.1) ∈ modularPhiHolomorphicDomain M (k.m + 1) k.n} :=
        ((modularPhiDivisor_domains_isOpen M hM (k.m + 1) k.n).1).preimage (by fun_prop)
      by_cases hr : k.ratio = true
      · convert hn.inter ((inversePhiDomain_isOpen M hM (k.m + k.p) k.n).preimage
          (show Continuous (fun q : ℂ × (ℂ × ℂ × ℂ) => (q.1 + q.2.2.2, q.2.1)) by fun_prop)) using 1
        ext q
        simp [V, hr]
      · simpa [V, hr] using hn
    have hbase : ∀ z ∈ boundaries (C k), (z, (τ₀, k.w, k.y)) ∈ V := by
      intro z hz
      have hreg := hsafe k hk z hz
      exact ⟨⟨hreg.1, hreg.2.1⟩, fun hr => ⟨hreg.1, hreg.2.2 hr⟩⟩
    have hf : ContinuousOn
        (fun q : ℂ × (ℂ × ℂ × ℂ) =>
          kernel M (withParameters k q.2.2.1 q.2.2.2) q.1 q.2.1) V := by
      intro q hq
      have hn : ContinuousAt
          (fun v : ℂ × (ℂ × ℂ × ℂ) => modularPhi M (k.m + 1) k.n v.1 v.2.1) q :=
        ((modularPhi_joint_analytic_no_poles M hM (k.m + 1) k.n
          (q.1, q.2.1) hq.1).continuousAt).comp
            (x := q) (f := fun v : ℂ × (ℂ × ℂ × ℂ) => (v.1, v.2.1)) (by fun_prop)
      have hT : etaDenom M q.2.1 ≠ 0 := etaDenom_ne_zero_of_mem M hq.1.1
      have he : ContinuousAt
          (fun v : ℂ × (ℂ × ℂ × ℂ) =>
            e (phase M (withParameters k v.2.2.1 v.2.2.2) v.1 v.2.1)) q := by
        change ContinuousAt (fun v : ℂ × (ℂ × ℂ × ℂ) =>
          e ((((M 1 0 : ℂ) * v.1 - (k.n : ℂ) + etaDenom M v.2.1 * (k.m : ℂ)) * v.2.2.1) /
              etaDenom M v.2.1 + (k.ell : ℂ) * (v.1 + (k.m : ℂ) * v.2.1) +
              (k.h : ℂ) * (v.1 / etaDenom M v.2.1 + (k.n : ℂ) * etaMobius M v.2.1))) q
        unfold e etaMobius etaDenom
        fun_prop (disch := exact hT)
      apply ContinuousAt.continuousWithinAt
      change ContinuousAt (fun v : ℂ × (ℂ × ℂ × ℂ) =>
        modularPhi M (k.m + 1) k.n v.1 v.2.1 *
          (if k.ratio = true then
            (modularPhi M (k.m + k.p) k.n (v.1 + v.2.2.2) v.2.1)⁻¹ else 1) *
          e (phase M (withParameters k v.2.2.1 v.2.2.2) v.1 v.2.1)) q
      by_cases hr : k.ratio = true
      · simp only [if_pos hr]
        have hd : ContinuousAt
            (fun v : ℂ × (ℂ × ℂ × ℂ) =>
              (modularPhi M (k.m + k.p) k.n (v.1 + v.2.2.2) v.2.1)⁻¹) q :=
          ((inversePhi_joint_analytic M hM (k.m + k.p) k.n
            (q.1 + q.2.2.2, q.2.1) (hq.2 hr)).continuousAt).comp
              (x := q) (f := fun v : ℂ × (ℂ × ℂ × ℂ) => (v.1 + v.2.2.2, v.2.1)) (by fun_prop)
        exact (hn.mul hd).mul he
      · simp only [if_neg hr, mul_one]
        exact hn.mul he
    obtain ⟨r, B, hr, hB, hbound⟩ := RegularityAux.compact_slice_bound
      (RegularityAux.boundaries_isCompact (C k)) hV hbase hf
    refine ⟨r, B, hr, hB, ?_⟩
    intro τ hτ w hw y hy z hz
    have hp : (τ, w, y) ∈ Metric.closedBall (τ₀, k.w, k.y) r := by
      rw [Metric.mem_closedBall, Prod.dist_eq, Prod.dist_eq]
      exact max_le (Metric.mem_closedBall.mp hτ)
        (max_le (Metric.mem_closedBall.mp hw) (Metric.mem_closedBall.mp hy))
    obtain ⟨hreg, hnorm⟩ := hbound z hz (τ, w, y) hp
    exact ⟨⟨hreg.1.1, hreg.1.2, fun hr => (hreg.2 hr).2⟩, hnorm⟩
  obtain ⟨r, B, hr, hB, hbound⟩ := RegularityAux.finite_uniform_radius_bound S P hmono hsingle
  obtain ⟨s, hs, hdomain⟩ :=
    RegularityAux.closedBall_in_open (modularPhiDomain_isOpen M) hτ₀
  refine ⟨min r s, B, lt_min hr hs, hB,
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hdomain, ?_⟩
  intro k hk
  exact hmono k r (min r s) B B (min_le_left _ _) le_rfl (hbound k hk)

#check modularPhi_joint_analytic_no_poles
#check modularPhi_pole_value
#check modularPhi_eq_chart
#check continuationNumerator_ne_zero_iff
#check modularPhi_joint_local_quotient
#check AnalyticOnNhd.continuousOn
#check meromorphicOrderAt
#print phase
#print kernel
#print regularDomain
#print kernelOrder

end SICLean.L4.ModularCluster
