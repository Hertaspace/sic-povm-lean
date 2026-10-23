import SICLean.L4.G1ContinuationGeometry
import SICLean.L4.G1ContinuationCirclesAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Finite complex-circle corrections and their geometric transport

Finite circle corrections. `CircleExtension` contains the given
G1VerticalChain and the existing ModularCluster.Circles data, with no analytic or integral field.
Complex centers are necessary during transport: real-centered circles cannot distinguish conjugate
numerator/inverse poles. The terminal interface is still exactly `G1Separates` / `g1ChainIntegral`.
No new no-pinch predicate is used. Labels, including coincident labels, remain.

[RW26, p. 7, p. 13, p. 29]. The complex-center bookkeeping is an explicit implementation
elaboration.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1Continuation

structure CircleExtension where
  base : G1VerticalChain
  extra : ModularCluster.Circles

def ofChain (D : G1VerticalChain) : CircleExtension :=
  ⟨D, ⟨∅, fun _ => 0⟩⟩

def complexCirclePullback (f : ℂ → ℂ) (a : ℂ) (r θ : ℝ) : ℂ :=
  f (circleMap a r θ) * (Complex.I * (circleMap a r θ - a))

def extensionIntegral (D : CircleExtension) (f : ℂ → ℂ) : ℂ :=
  g1ChainIntegral D.base f + ∑ a ∈ D.extra.centers,
    ∫ θ : ℝ in 0..(2 * Real.pi), complexCirclePullback f a (D.extra.radius a) θ

def ExtensionIntegrable (D : CircleExtension) (f : ℂ → ℂ) : Prop :=
  G1ChainIntegrable D.base f ∧ ∀ a ∈ D.extra.centers,
    IntervalIntegrable (complexCirclePullback f a (D.extra.radius a)) volume 0 (2 * Real.pi)

def extensionAssignment (D : CircleExtension) (z : ℂ) : ℤ :=
  G1FixedSeparation.leftAssignmentAt D.base z +
    ∑ a ∈ D.extra.centers, if dist z a < D.extra.radius a then 1 else 0

def extensionAvoids (D : CircleExtension) (z : ℂ) : Prop :=
  z.re ≠ D.base.crossing ∧
    (∀ r ∈ D.base.centers, dist z (r : ℂ) ≠ D.base.radius r) ∧
    ∀ a ∈ D.extra.centers, dist z a ≠ D.extra.radius a

def SeparatesExtension (D : CircleExtension) (M : SL(2, ℤ)) (τ y : ℂ)
    (n p m : ℤ) : Prop :=
  (∀ r ∈ D.base.centers, 0 < D.base.radius r) ∧
  (∀ a ∈ D.extra.centers, 0 < D.extra.radius a) ∧
  ∀ b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p m),
    let z := ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p m) τ b
    extensionAvoids D z ∧ extensionAssignment D z = if b.1 then 0 else 1

def extensionTruncated (D : CircleExtension) (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  G1FiniteLedger.truncatedIntegral D.base f R + ∑ a ∈ D.extra.centers,
    ∫ θ : ℝ in 0..(2 * Real.pi), complexCirclePullback f a (D.extra.radius a) θ

def ratioExtensionSum (M : SL(2, ℤ)) (D : Fin (M 1 0).toNat → CircleExtension)
    (n h ell p : ℤ) (x : Parameters) : ℂ :=
  ∑ m : Fin (M 1 0).toNat,
    extensionIntegral (D m) (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)

def candidateLocations (M : SL(2, ℤ)) (τ y : ℂ) (n p m : ℤ) : Set ℂ :=
  {z | ∃ b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p m),
    ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p m) τ b = z}

/-- Literal right-of-bent-graph condition for every actual numerator branch. At real τ all pole
imaginary parts vanish. No regularity/integral is a field. -/
def BentClear (M : SL(2, ℤ)) (τ : ℂ) (n m : ℤ) (x ψ : ℝ) : Prop :=
  ∀ k ∈ modularPhiPoleLabels M (m + 1) n,
    let z := modularPhiPolePoint M (m + 1) n τ k.1 k.2
    x + max 0 (-z.im - 1) * Real.tan ψ < z.re

/-- C01. Literal embedding of the existing integral. [RW26, p. 7, p. 13]. -/
theorem ofChain_integral (D : G1VerticalChain) (f : ℂ → ℂ) :
    extensionIntegral (ofChain D) f = g1ChainIntegral D f := by
  simp [extensionIntegral, ofChain]

/-- C02. No convergence is assumed by the data constructor. [RW26, p. 29]. -/
theorem ofChain_integrable (D : G1VerticalChain) (f : ℂ → ℂ) :
    ExtensionIntegrable (ofChain D) f ↔ G1ChainIntegrable D f := by
  simp [ExtensionIntegrable, ofChain]

/-- C03. Exact reuse of complex assignment, then its real contract. [RW26, p. 7, p. 13]. -/
theorem ofChain_separates (D : G1VerticalChain) (M : SL(2, ℤ)) (τ y : ℂ)
    (n p m : ℤ) :
    SeparatesExtension (ofChain D) M τ y n p m ↔
      G1FixedSeparation.SeparatesAt D M τ y n p m := by
  rw [G1ContinuationCirclesAux.separatesAt_iff_labels]
  simp [SeparatesExtension, ofChain, extensionAvoids, extensionAssignment, and_assoc]

/-- C04. Only finitely many inverse labels are right of a chosen baseline. [RW26, p. 6]. -/
theorem inverse_right_finite_complex (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℂ) (hT : 0 < (etaDenom M τ).re) (n p m : ℤ) (x : ℝ) :
    {k | k ∈ modularPhiZeroLabels M (m + p) n ∧
      x ≤ (modularPhiZeroPoint M (m + p) n τ k.1 k.2 - y).re}.Finite := by
  have hc : (0 : ℝ) < M 1 0 := by exact_mod_cast hM
  let B : ℝ := (n : ℝ) - 1 - ((m : ℝ) + (p : ℝ)) * (etaDenom M τ).re -
    (x + y.re) * (M 1 0 : ℝ)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (B / (etaDenom M τ).re) B)
  apply ((Set.finite_le_nat N).prod (Set.finite_le_nat N)).subset
  intro k hk
  have hmul : (x + y.re) * (M 1 0 : ℝ) ≤
      (n : ℝ) - 1 - ((m : ℝ) + (p : ℝ) + (k.1 : ℝ)) *
        (etaDenom M τ).re - (k.2 : ℝ) := by
    apply (le_div_iff₀ hc).mp
    have := hk.2
    rw [G1ContinuationCirclesAux.inverse_re] at this
    linarith
  have hb : (k.1 : ℝ) * (etaDenom M τ).re + (k.2 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hK : (k.1 : ℝ) ≤ B / (etaDenom M τ).re := by
    apply (le_div_iff₀ hT).mpr
    linarith [(Nat.cast_nonneg k.2 : (0 : ℝ) ≤ k.2)]
  have hJ : (k.2 : ℝ) ≤ B := by
    nlinarith [mul_nonneg ((Nat.cast_nonneg k.1 : (0 : ℝ) ≤ k.1)) hT.le]
  constructor
  · have : (k.1 : ℝ) < N := hK.trans_lt ((le_max_left _ _).trans_lt hN)
    exact_mod_cast this.le
  · have : (k.2 : ℝ) < N := hJ.trans_lt ((le_max_right _ _).trans_lt hN)
    exact_mod_cast this.le

/-- C05. Geometric existence over the whole complex fiber, not assumed transport. [RW26, p. 29]. All
added circles are CCW. -/
theorem exists_separating_extensions (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hT : 0 < (etaDenom M τ).re) (n h ell p : ℤ)
    (v : ℂ × ℂ) (hv : v ∈ ratioFiber M τ n h ell p) :
    ∃ D : Fin (M 1 0).toNat → CircleExtension,
      ∀ m, SeparatesExtension (D m) M τ v.2 n p (m : ℤ) := by
  classical
  have hright (m : ℤ) (x : ℝ) :
      {b | b ∈ modularPhiZeroLabels M (m + p) n ∧
        x ≤ (modularPhiZeroPoint M (m + p) n τ b.1 b.2 - v.2).re}.Finite :=
    inverse_right_finite_complex M hM τ v.2 hT n p m x
  have hex (m : Fin (M 1 0).toNat) :
      ∃ D : CircleExtension, SeparatesExtension D M τ v.2 n p (m : ℤ) := by
    let k := G1Pinch.ratioData 0 v.2 n 0 0 p (m : ℤ)
    let q : ℕ × ℕ → ℂ := fun b =>
      modularPhiZeroPoint M ((m : ℤ) + p) n τ b.1 b.2 - v.2
    let u : ℝ := ((n : ℝ) - (m : ℝ) * (etaDenom M τ).re) / (M 1 0 : ℝ)
    have hc : (0 : ℝ) < M 1 0 := by exact_mod_cast hM
    have hpRe (K J : ℕ) :
        (modularPhiPolePoint M ((m : ℤ) + 1) n τ K J).re =
          ((n : ℝ) - (m : ℝ) * (etaDenom M τ).re +
            (K : ℝ) * (etaDenom M τ).re + (J : ℝ)) / (M 1 0 : ℝ) := by
      simp [modularPhiPolePoint]
    have hpLower (K J : ℕ) :
        u ≤ (modularPhiPolePoint M ((m : ℤ) + 1) n τ K J).re := by
      rw [hpRe]
      apply (div_le_div_iff_of_pos_right hc).mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg K) hT.le,
        (Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
    have hfin := hright (m : ℤ) (u - 1)
    obtain ⟨x, hx, hnot⟩ :=
      (Set.Ioo_infinite (show u - 1 < u by linarith)).exists_notMem_finite
        (hfin.image (fun b => (q b).re))
    have havoid (b : ℕ × ℕ)
        (hb : b ∈ modularPhiZeroLabels M ((m : ℤ) + p) n) : (q b).re ≠ x := by
      intro heq
      apply hnot
      exact ⟨b, ⟨hb, by change u - 1 ≤ (q b).re; linarith [hx.1]⟩, heq⟩
    let S : Set ℂ := q '' {b | b ∈ modularPhiZeroLabels M ((m : ℤ) + p) n ∧
      x ≤ (q b).re}
    have hS : S.Finite :=
      (hright (m : ℤ) x).image q
    let A : Finset ℂ := hS.toFinset
    have hA (a : ℂ) : a ∈ A ↔ a ∈ S := hS.mem_toFinset
    have hAinv (b : ℕ × ℕ)
        (hb : b ∈ modularPhiZeroLabels M ((m : ℤ) + p) n) :
        q b ∈ A ↔ x ≤ (q b).re := by
      constructor
      · intro hz
        obtain ⟨b', ⟨_, hb'⟩, heq⟩ := (hA _).mp hz
        simpa only [heq] using hb'
      · intro hz
        exact (hA _).mpr ⟨b, ⟨hb, hz⟩, rfl⟩
    let R : ℝ := ∑ a ∈ A, ‖a‖
    have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hdom : τ ∈ modularPhiDomain M := Complex.mem_slitPlane_iff.mpr (Or.inl hT)
    obtain ⟨ρ, C, hρ, -, hcenters, hpos, -, hiso, -⟩ :=
      ModularCluster.exists_fixed_circles M hM k τ hdom R hR
    have hself : τ ∈ Metric.closedBall τ ρ := Metric.mem_closedBall_self hρ.le
    have hAC (a : ℂ) (ha : a ∈ A) : a ∈ C.centers := by
      have hn : ‖a‖ ≤ R := by
        dsimp [R]
        exact Finset.single_le_sum (fun a _ => norm_nonneg a) ha
      obtain ⟨b, ⟨hb, _⟩, heq⟩ := (hA _).mp ha
      change a ∈ (C.centers : Set ℂ)
      rw [hcenters]
      refine ⟨hn, (false, b), ?_, ?_⟩
      · simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hb
      · simpa [k, ModularCluster.branchPoint, G1Pinch.ratioData, q] using heq
    let rad : ℂ → ℝ := fun a => C.radius a / 2
    have hrad (a : ℂ) (ha : a ∈ A) : 0 < rad a ∧ rad a < C.radius a := by
      have hp := (hpos a (hAC a ha)).1
      dsimp [rad]
      constructor <;> linarith
    have hout (b : ModularCluster.Label) (hb : b ∈ ModularCluster.labels M k)
        (a : ℂ) (ha : a ∈ A) (hne : ModularCluster.branchPoint M k τ b ≠ a) :
        rad a < dist (ModularCluster.branchPoint M k τ b) a :=
      (hrad a ha).2.trans ((hiso a (hAC a ha) b hb τ hself).2 hne)
    have hboundary (b : ModularCluster.Label) (hb : b ∈ ModularCluster.labels M k)
        (a : ℂ) (ha : a ∈ A) :
        dist (ModularCluster.branchPoint M k τ b) a ≠ rad a := by
      by_cases heq : ModularCluster.branchPoint M k τ b = a
      · simpa [heq] using (hrad a ha).1.ne
      · exact (hout b hb a ha heq).ne'
    have hsum (b : ModularCluster.Label) (hb : b ∈ ModularCluster.labels M k) :
        (∑ a ∈ A, if dist (ModularCluster.branchPoint M k τ b) a < rad a
          then (1 : ℤ) else 0) =
          if ModularCluster.branchPoint M k τ b ∈ A then 1 else 0 := by
      by_cases hz : ModularCluster.branchPoint M k τ b ∈ A
      · rw [if_pos hz, Finset.sum_eq_single (ModularCluster.branchPoint M k τ b)]
        · simp [(hrad _ hz).1]
        · intro a ha hne
          exact if_neg (not_lt.mpr (hout b hb a ha hne.symm).le)
        · exact fun hn => (hn hz).elim
      · rw [if_neg hz]
        apply Finset.sum_eq_zero
        intro a ha
        have hne : ModularCluster.branchPoint M k τ b ≠ a := by
          intro heq
          exact hz (heq ▸ ha)
        exact if_neg (not_lt.mpr (hout b hb a ha hne).le)
    have hsep : ModularCluster.crossSeparated M k τ := hv.2 m
    have hpNotA (K J : ℕ)
        (hb : (K, J) ∈ modularPhiPoleLabels M ((m : ℤ) + 1) n) :
        modularPhiPolePoint M ((m : ℤ) + 1) n τ K J ∉ A := by
      intro ha
      obtain ⟨b, ⟨hb', _⟩, heq⟩ := (hA _).mp ha
      have htrue : (true, K, J) ∈ ModularCluster.labels M k := by
        simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hb
      have hfalse : (false, b) ∈ ModularCluster.labels M k := by
        simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hb'
      have heq' : ModularCluster.branchPoint M k τ (true, K, J) =
          ModularCluster.branchPoint M k τ (false, b) := by
        simpa [k, ModularCluster.branchPoint, G1Pinch.ratioData, q] using heq.symm
      have hc' := hsep _ htrue _ hfalse heq'
      simp at hc'
    let D : CircleExtension := ⟨G1ChainTransfer.plainChain x, ⟨A, rad⟩⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · simp [D, G1ChainTransfer.plainChain]
    · exact fun a ha => (hrad a ha).1
    · rintro ⟨b, K, J⟩ hb
      have hb' : (b, K, J) ∈ ModularCluster.labels M k := hb
      refine ⟨?_, ?_⟩
      · refine ⟨?_, by simp [D, G1ChainTransfer.plainChain],
          fun a ha => hboundary _ hb' a ha⟩
        cases b
        · exact havoid (K, J) (by simpa [ModularCluster.labels, G1Pinch.ratioData] using hb)
        · exact (hx.2.trans_le (hpLower K J)).ne'
      · simp only [extensionAssignment, D, G1ChainTransfer.plainChain,
          G1FixedSeparation.leftAssignmentAt, G1FixedSeparation.circleWindingAt,
          Finset.sum_empty, add_zero]
        change (if (ModularCluster.branchPoint M k τ (b, K, J)).re < x
            then (1 : ℤ) else 0) +
          (∑ a ∈ A, if dist (ModularCluster.branchPoint M k τ (b, K, J)) a < rad a
            then (1 : ℤ) else 0) = if b then 0 else 1
        rw [hsum _ hb']
        cases b
        · have hl : (K, J) ∈ modularPhiZeroLabels M ((m : ℤ) + p) n := by
            simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
          change (if (q (K, J)).re < x then (1 : ℤ) else 0) +
            (if q (K, J) ∈ A then 1 else 0) = 1
          simp only [hAinv (K, J) hl]
          by_cases hx' : (q (K, J)).re < x
          · simp [hx', not_le.mpr hx']
          · simp [hx', le_of_not_gt hx']
        · have hl : (K, J) ∈ modularPhiPoleLabels M ((m : ℤ) + 1) n := by
            simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
          have hn := hpNotA K J hl
          have hr := hx.2.trans_le (hpLower K J)
          simp [k, ModularCluster.branchPoint, G1Pinch.ratioData,
            not_lt.mpr hr.le, hn]
  choose D hD using hex
  exact ⟨D, hD⟩

/-- C06. A fixed chain works on an ordinary joint neighborhood of (τ,w,y). [RW26, p. 29]. -/
theorem separating_extension_stable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ∃ U : Set Parameters, IsOpen U ∧ x ∈ U ∧ U ⊆ ratioTube M n h ell p ψ ∧
      ∀ v ∈ U, ∀ m, SeparatesExtension (D m) M v.1 v.2.2 n p (m : ℤ) := by
  have hT : 0 < (etaDenom M x.1).re :=
    (UpperWindow.tauRegion_properties M hM ψ hψ' x.1 hx.1).2.2.1
  have hm (m : Fin (M 1 0).toNat) :
      ∀ᶠ q : ℂ × ℂ in 𝓝 (x.1, x.2.2), SeparatesExtension (D m) M q.1 q.2 n p (m : ℤ) := by
    have he := G1ContinuationCirclesAux.separation_eventually M hM n p (m : ℤ)
      (x.1, x.2.2) hT (D m).base (D m).extra (hD m).2.2
    filter_upwards [he] with q hq
    exact ⟨(hD m).1, (hD m).2.1, hq⟩
  have hmap : Continuous (fun v : Parameters => (v.1, v.2.2)) := by fun_prop
  have he : ∀ᶠ v in 𝓝 x, ∀ m, SeparatesExtension (D m) M v.1 v.2.2 n p (m : ℤ) :=
    (hmap.tendsto x).eventually (Filter.eventually_all.mpr hm)
  have hTube := (ratio_fiber_and_tube_open M hM x.1 hT n h ell p ψ hψ hψ').2
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp (he.and (hTube.mem_nhds hx))
  exact ⟨U, hUopen, hxU, fun v hv => (hUsub hv).2, fun v hv => (hUsub hv).1⟩

/-- C07. Assignment equality is a conclusion about all actual branch labels. [RW26, p. 7, p. 13]. -/
theorem separating_extensions_same_assignment (M : SL(2, ℤ)) (τ y : ℂ)
    (n p m : ℤ) (D₀ D₁ : CircleExtension)
    (h₀ : SeparatesExtension D₀ M τ y n p m)
    (h₁ : SeparatesExtension D₁ M τ y n p m) :
    ∀ z ∈ candidateLocations M τ y n p m,
      extensionAssignment D₀ z = extensionAssignment D₁ z := by
  rintro z ⟨b, hb, rfl⟩
  exact (h₀.2.2 b hb).2.trans (h₁.2.2 b hb).2.symm

/-- C08. Finite ledger before taking any infinite-tail limit. Sign follows: right vertical minus
left vertical plus bottom-minus-top connectors. [RW26, p. 13]. -/
theorem finite_zero_winding_ledger (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (hτ : τ ∈ modularPhiDomain M) (hT : 0 < (etaDenom M τ).re)
    (n h ell p m : ℤ) (D₀ D₁ : CircleExtension)
    (h₀ : SeparatesExtension D₀ M τ y n p m)
    (h₁ : SeparatesExtension D₁ M τ y n p m) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R ≥ R₀,
      let f := UpperWindow.ratioKernel M m n h ell p τ w y
      extensionTruncated D₁ f R - extensionTruncated D₀ f R +
        G1FiniteLedger.connectors f D₀.base.crossing D₁.base.crossing R = 0 := by
  let circleIndices (D : CircleExtension) : Finset (ℝ ⊕ ℂ) :=
    D.base.centers.disjSum D.extra.centers

  let circleCenter : (ℝ ⊕ ℂ) → ℂ := Sum.elim (fun r : ℝ => (r : ℂ)) id

  let circleRadius (D : CircleExtension) : (ℝ ⊕ ℂ) → ℝ :=
    Sum.elim D.base.radius D.extra.radius

  have circle_assignment (D : CircleExtension) (z : ℂ) :
      G1ContinuationCirclesAux.assignment (circleIndices D) circleCenter (circleRadius D)
        D.base.crossing z = extensionAssignment D z := by
    simp only [G1ContinuationCirclesAux.assignment, G1ContinuationCirclesAux.circleCount,
      circleIndices, circleCenter, circleRadius, Finset.sum_disjSum,
      extensionAssignment, G1FixedSeparation.leftAssignmentAt,
      G1FixedSeparation.circleWindingAt, Sum.elim_inl, Sum.elim_inr, id_eq,
      add_assoc] <;> rfl

  have circle_truncated (D : CircleExtension) (f : ℂ → ℂ) (R : ℝ) :
      G1ContinuationCirclesAux.truncated (circleIndices D) circleCenter (circleRadius D)
        D.base.crossing f R = extensionTruncated D f R := by
    simp [G1ContinuationCirclesAux.truncated, circleIndices, circleCenter, circleRadius,
      Finset.sum_disjSum, extensionTruncated, G1FiniteLedger.truncatedIntegral,
      FinitePrincipalParts.circleCCW, complexCirclePullback, add_assoc]

  have hInv := fun x => G1Continuation.inverse_right_finite_complex M hM τ y hT n p m x
  let s₀ := circleIndices D₀
  let s₁ := circleIndices D₁
  let c := circleCenter
  let r₀ := circleRadius D₀
  let r₁ := circleRadius D₁
  let x₀ := D₀.base.crossing
  let x₁ := D₁.base.crossing
  let k := G1Pinch.ratioData w y n h ell p m
  let f : ℂ → ℂ := fun z => ModularCluster.kernel M k z τ
  have hf : f = UpperWindow.ratioKernel M m n h ell p τ w y := by
    ext z
    simp only [f, ModularCluster.kernel, k, G1Pinch.ratioData, ite_true,
      UpperWindow.ratioKernel, ModularCluster.phase, UpperWindow.phase, div_eq_mul_inv]
  have hpos (D : CircleExtension) (hD : SeparatesExtension D M τ y n p m) :
      ∀ i ∈ circleIndices D, 0 < circleRadius D i := by
    intro i hi
    cases i with
    | inl a => exact hD.1 a (by simpa [circleIndices] using hi)
    | inr a => exact hD.2.1 a (by simpa [circleIndices] using hi)
  have hlabel (D : CircleExtension) (hD : SeparatesExtension D M τ y n p m)
      (b : ModularCluster.Label)
      (hb : b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p m)) :
      let z := ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p m) τ b
      z.re ≠ D.base.crossing ∧
        (∀ i ∈ circleIndices D, dist z (circleCenter i) ≠ circleRadius D i) ∧
        G1ContinuationCirclesAux.assignment (circleIndices D) circleCenter (circleRadius D)
          D.base.crossing z = if b.1 then 0 else 1 := by
    have hh := hD.2.2 b hb
    refine ⟨hh.1.1, ?_, ?_⟩
    · intro i hi
      cases i with
      | inl a => exact hh.1.2.1 a (by simpa [circleIndices] using hi)
      | inr a => exact hh.1.2.2 a (by simpa [circleIndices] using hi)
    · simpa only [circle_assignment] using hh.2
  let b₀ : ℝ := ∑ i ∈ s₀, (‖c i‖ + |r₀ i|)
  let b₁ : ℝ := ∑ i ∈ s₁, (‖c i‖ + |r₁ i|)
  have hb₀ : 0 ≤ b₀ := Finset.sum_nonneg (fun i _ => add_nonneg (norm_nonneg _) (abs_nonneg _))
  have hb₁ : 0 ≤ b₁ := Finset.sum_nonneg (fun i _ => add_nonneg (norm_nonneg _) (abs_nonneg _))
  let B := |x₀| + |x₁| + b₀ + b₁ + 1
  have hx₀ : -B ≤ x₀ := by dsimp [B]; linarith [neg_le_abs x₀, abs_nonneg x₁]
  have hx₁ : -B ≤ x₁ := by dsimp [B]; linarith [neg_le_abs x₁, abs_nonneg x₀]
  let S : ℝ → Set ℂ := fun R =>
    (FinitePrincipalParts.closedRectangle (g1VerticalPoint (min x₀ x₁) (-R))
      (g1VerticalPoint (max x₀ x₁) R) ∪
      {z | ∃ i ∈ s₀, z ∈ Metric.closedBall (c i) (r₀ i)}) ∪
      {z | ∃ i ∈ s₁, z ∈ Metric.closedBall (c i) (r₁ i)}
  have hball_lower (s : Finset (ℝ ⊕ ℂ)) (r : (ℝ ⊕ ℂ) → ℝ) (b : ℝ)
      (hb : b = ∑ i ∈ s, (‖c i‖ + |r i|)) (hbB : b ≤ B)
      (i : ℝ ⊕ ℂ) (hi : i ∈ s) (z : ℂ) (hz : z ∈ Metric.closedBall (c i) (r i)) :
      -B ≤ z.re := by
    have hle : ‖c i‖ + |r i| ≤ b := by
      rw [hb]
      exact Finset.single_le_sum (fun j _ => add_nonneg (norm_nonneg _) (abs_nonneg _)) hi
    have hn : ‖z - c i‖ ≤ r i := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    have hzNorm : ‖z‖ ≤ ‖c i‖ + r i := by
      calc
        ‖z‖ = ‖(z - c i) + c i‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c i‖ + ‖c i‖ := norm_add_le _ _
        _ ≤ ‖c i‖ + r i := by linarith
    linarith [Complex.abs_re_le_norm z, neg_le_abs z.re, le_abs_self (r i)]
  have hSlower (R : ℝ) (z : ℂ) (hz : z ∈ S R) : -B ≤ z.re := by
    rcases hz with (hz | ⟨i, hi, hz⟩) | ⟨i, hi, hz⟩
    · have hh : min x₀ x₁ ≤ z.re := by
        simpa [FinitePrincipalParts.closedRectangle, g1VerticalPoint] using hz.1
      exact (le_min hx₀ hx₁).trans hh
    · apply hball_lower s₀ r₀ b₀ rfl ?_ i hi z hz
      dsimp [B]
      linarith [abs_nonneg x₀, abs_nonneg x₁]
    · apply hball_lower s₁ r₁ b₁ rfl ?_ i hi z hz
      dsimp [B]
      linarith [abs_nonneg x₀, abs_nonneg x₁]
  let Q := (hInv (-B)).toFinset
  let P := Q.image (fun q : ℕ × ℕ => modularPhiZeroPoint M (m + p) n τ q.1 q.2 - y)
  have hQ (q : ℕ × ℕ) : q ∈ Q ↔ q ∈ modularPhiZeroLabels M (m + p) n ∧
      -B ≤ (modularPhiZeroPoint M (m + p) n τ q.1 q.2 - y).re := by
    exact Set.Finite.mem_toFinset _
  have hPcand (z : ℂ) (hz : z ∈ P) : z ∈ candidateLocations M τ y n p m := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨(false, q), ?_, ?_⟩
    · simpa [ModularCluster.labels, G1Pinch.ratioData] using (hQ q).mp hq |>.1
    · rfl
  have hcapture (R : ℝ) (z : ℂ) (hz : z ∈ S R)
      (hc : z ∈ candidateLocations M τ y n p m) : z ∈ P := by
    rcases hc with ⟨⟨flag, K, J⟩, hb, rfl⟩
    cases flag with
    | false =>
      refine Finset.mem_image.mpr ⟨(K, J), (hQ (K, J)).mpr ⟨?_, ?_⟩, rfl⟩
      · simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
      · exact hSlower R _ hz
    | true =>
      have hn₀ := hlabel D₀ h₀ (true, K, J) hb
      have hn₁ := hlabel D₁ h₁ (true, K, J) hb
      have hzero₀ := G1ContinuationCirclesAux.assignment_zero_constraints s₀ c r₀ x₀ _
        hn₀.1 hn₀.2.1 (by simpa using hn₀.2.2)
      have hzero₁ := G1ContinuationCirclesAux.assignment_zero_constraints s₁ c r₁ x₁ _
        hn₁.1 hn₁.2.1 (by simpa using hn₁.2.2)
      exfalso
      rcases hz with (hz | ⟨i, hi, hz⟩) | ⟨i, hi, hz⟩
      · have hzre : (ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p m) τ
            (true, K, J)).re ≤ max x₀ x₁ := by
          simpa [FinitePrincipalParts.closedRectangle, g1VerticalPoint] using hz.2.1
        exact (not_lt_of_ge hzre) (max_lt hzero₀.1 hzero₁.1)
      · exact (not_lt_of_ge (Metric.mem_closedBall.mp hz)) (hzero₀.2 i hi)
      · exact (not_lt_of_ge (Metric.mem_closedBall.mp hz)) (hzero₁.2 i hi)
  have hlocal : ∀ z : ℂ, ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z ∧
      f =ᶠ[𝓝[≠] z] (fun u => FinitePrincipalParts.principalPart z
        (ModularCluster.poleBudget M k z τ) A u + g u) := by
    intro z
    exact ModularCluster.LedgerAux.principalPart_germ f z (ModularCluster.poleBudget M k z τ)
      (ModularCluster.kernelOrder M k z τ)
      (ModularCluster.kernel_meromorphic M hM k τ hτ z (Set.mem_univ z))
      (ModularCluster.kernel_order M hM k z τ hτ)
      (ModularCluster.kernelOrder_lower_bound M hM k z τ hτ)
  choose A g hAg using hlocal
  refine ⟨(∑ z ∈ P, |z.im|) + 1, by positivity, ?_⟩
  intro R hR
  have hRpos : 0 < R := by
    have hh : 0 ≤ ∑ z ∈ P, |z.im| := Finset.sum_nonneg (fun z _ => abs_nonneg _)
    linarith
  have hheight (z : ℂ) (hz : z ∈ P) : |z.im| < R := by
    have hh : |z.im| ≤ ∑ z ∈ P, |z.im| :=
      Finset.single_le_sum (f := fun z : ℂ => |z.im|) (fun z _ => abs_nonneg _) hz
    linarith
  have hfa : AnalyticOnNhd ℂ f (S R \ id '' (P : Set ℂ)) := by
    intro z hz
    apply ModularCluster.kernel_analyticAt_of_no_labels M hM k τ z hτ
    intro b hb he
    apply hz.2
    refine ⟨z, hcapture R z hz.1 ?_, rfl⟩
    refine ⟨b, ?_, ?_⟩
    · simpa [ModularCluster.labels, k, G1Pinch.ratioData] using hb
    · exact he.symm
  obtain ⟨H, hH, hfH⟩ := G1FiniteChainLedgerAux.finite_regularized_remainder P id
    Function.injective_id f (S R) (fun z => ModularCluster.poleBudget M k z τ) A g hfa
    (fun z _ => (hAg z).1) (fun z _ => (hAg z).2)
  have hboundary (D : CircleExtension) (hD : SeparatesExtension D M τ y n p m)
      (z : ℂ) (hz : z ∈ P) :
      z.re ≠ D.base.crossing ∧ ∀ i ∈ circleIndices D,
        dist z (circleCenter i) ≠ circleRadius D i := by
    obtain ⟨b, hb, rfl⟩ := hPcand z hz
    exact ⟨(hlabel D hD b hb).1, (hlabel D hD b hb).2.1⟩
  have hass (z : ℂ) (hz : z ∈ P) :
      G1ContinuationCirclesAux.assignment s₀ c r₀ x₀ z =
        G1ContinuationCirclesAux.assignment s₁ c r₁ x₁ z := by
    obtain ⟨b, hb, rfl⟩ := hPcand z hz
    exact (hlabel D₀ h₀ b hb).2.2.trans (hlabel D₁ h₁ b hb).2.2.symm
  have heq := G1ContinuationCirclesAux.finite_zero_of_principal_parts s₀ s₁ c c r₀ r₁ x₀ x₁
    f H P (fun z => ModularCluster.poleBudget M k z τ) A (S R) R hRpos (hpos D₀ h₀)
    (hpos D₁ h₁) (by intro i hi z hz; exact Or.inl (Or.inr ⟨i, hi, hz⟩))
    (by intro i hi z hz; exact Or.inr ⟨i, hi, hz⟩)
    (hboundary D₀ h₀) (hboundary D₁ h₁) hheight (by intro z hz; exact Or.inl (Or.inl hz))
    hH (by intro z hz hn; exact hfH z hz (by simpa using hn)) hass
  change G1ContinuationCirclesAux.truncated (circleIndices D₁) circleCenter (circleRadius D₁)
      D₁.base.crossing f R - G1ContinuationCirclesAux.truncated (circleIndices D₀)
      circleCenter (circleRadius D₀) D₀.base.crossing f R +
      G1FiniteLedger.connectors f D₀.base.crossing D₁.base.crossing R = 0 at heq
  rw [circle_truncated, circle_truncated, hf] at heq
  exact heq

/-- C09. Whole-cluster principal part, no simple-pole or distinct-label premise. [RW26, p. 29]. Only
a genuine punctured principal-part equality licenses the residue. -/
theorem complex_circle_residue (f g : ℂ → ℂ) (a : ℂ) (r : ℝ) (N : ℕ)
    (A : ℕ → ℂ) (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (Metric.closedBall a r))
    (hf : ∀ z ∈ Metric.closedBall a r, z ≠ a →
      f z = FinitePrincipalParts.principalPart a N A z + g z) :
    (∫ θ : ℝ in 0..(2 * Real.pi), complexCirclePullback f a r θ) =
      2 * (Real.pi : ℂ) * Complex.I * FinitePrincipalParts.residueCoefficient N A := by
  simpa only [complexCirclePullback, FinitePrincipalParts.circleCCW] using
    (FinitePrincipalParts.circleCCW_of_local_principalPart f g a r N A hr hg hf)

/-- C10. The positive circle is exactly the finite correction for a right shift. [RW26, p. 13]. -/
theorem baseline_crossing_circle_correction (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y a : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hT : 0 < (etaDenom M τ).re) (n h ell p m : ℤ) (x₀ x₁ r : ℝ)
    (hx₀ : x₀ < a.re) (hx₁ : a.re < x₁) (hr : 0 < r)
    (hr' : r < min (a.re - x₀) (x₁ - a.re))
    (honly : candidateLocations M τ y n p m ∩ {z | x₀ ≤ z.re ∧ z.re ≤ x₁} = {a}) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R ≥ R₀,
      let f := UpperWindow.ratioKernel M m n h ell p τ w y
      G1FiniteLedger.verticalSegment f x₁ R - G1FiniteLedger.verticalSegment f x₀ R +
        G1FiniteLedger.connectors f x₀ x₁ R =
          ∫ θ : ℝ in 0..(2 * Real.pi), complexCirclePullback f a r θ := by
  let k := G1Pinch.ratioData w y n h ell p m
  let f : ℂ → ℂ := fun z => ModularCluster.kernel M k z τ
  have hf : f = UpperWindow.ratioKernel M m n h ell p τ w y := by
    ext z
    simp only [f, ModularCluster.kernel, k, G1Pinch.ratioData, ite_true,
      UpperWindow.ratioKernel, ModularCluster.phase, UpperWindow.phase, div_eq_mul_inv]
  have hcandidate (b : ModularCluster.Label) (hb : b ∈ ModularCluster.labels M k) :
      ModularCluster.branchPoint M k τ b ∈ candidateLocations M τ y n p m := by
    refine ⟨b, ?_, ?_⟩
    · simpa only [k, G1Pinch.ratioData, ModularCluster.labels] using hb
    · rfl
  have hpoint (z : ℂ) (hz : z ∈ candidateLocations M τ y n p m)
      (hx : x₀ ≤ z.re ∧ z.re ≤ x₁) : z = a := by
    have : z ∈ candidateLocations M τ y n p m ∩ {z | x₀ ≤ z.re ∧ z.re ≤ x₁} := ⟨hz, hx⟩
    rwa [honly, Set.mem_singleton_iff] at this
  have hrl : r < a.re - x₀ := hr'.trans_le (min_le_left _ _)
  have hrr : r < x₁ - a.re := hr'.trans_le (min_le_right _ _)
  have hcoords (z : ℂ) (hz : z ∈ Metric.closedBall a r) :
      |z.re - a.re| ≤ r ∧ |z.im - a.im| ≤ r := by
    have hn : ‖z - a‖ ≤ r := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    exact ⟨by simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - a)).trans hn,
      by simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - a)).trans hn⟩
  have hiso : ∀ b ∈ ModularCluster.labels M k,
      dist (ModularCluster.branchPoint M k τ b) a ≤ r → ModularCluster.branchPoint M k τ b = a := by
    intro b hb hd
    have hre := (hcoords _ hd).1
    have hlow := (abs_le.mp hre).1
    have hupp := (abs_le.mp hre).2
    exact hpoint _ (hcandidate b hb) ⟨by linarith, by linarith⟩
  obtain ⟨A, g, hg, hfg⟩ := ModularCluster.exists_local_principalPart M hM k τ a hτ r hr hiso
  refine ⟨|a.im| + r + 1, by positivity, ?_⟩
  intro R hR
  have hRpos : 0 < R := by have := abs_nonneg a.im; linarith
  let lo := g1VerticalPoint x₀ (-R)
  let hi := g1VerticalPoint x₁ R
  have hre : lo.re < hi.re := by simpa [lo, hi, g1VerticalPoint] using hx₀.trans hx₁
  have him : lo.im < hi.im := by simp [lo, hi, g1VerticalPoint]; linarith
  have hinside : Metric.closedBall a r ⊆ FinitePrincipalParts.openRectangle lo hi := by
    intro z hz
    obtain ⟨hzre, hzim⟩ := hcoords z hz
    obtain ⟨hzrel, hzrer⟩ := abs_le.mp hzre
    obtain ⟨hziml, hzimr⟩ := abs_le.mp hzim
    have hal := neg_le_abs a.im
    have har := le_abs_self a.im
    simp only [FinitePrincipalParts.openRectangle, lo, hi, g1VerticalPoint,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add, Set.mem_setOf_eq]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hfa : AnalyticOnNhd ℂ f (FinitePrincipalParts.closedRectangle lo hi \
      (fun _ : Unit => a) '' (({()} : Finset Unit) : Set Unit)) := by
    intro z hz
    apply ModularCluster.kernel_analyticAt_of_no_labels M hM k τ z hτ
    intro b hb he
    apply hz.2
    refine ⟨(), by simp, ?_⟩
    have hzre : x₀ ≤ z.re ∧ z.re ≤ x₁ := by
      have hh := hz.1
      simp only [FinitePrincipalParts.closedRectangle, lo, hi, g1VerticalPoint,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, Set.mem_setOf_eq] at hh
      exact ⟨hh.1, hh.2.1⟩
    exact (hpoint z (he ▸ hcandidate b hb) hzre).symm
  have heq := FinitePrincipalParts.rectangle_finite_principal_parts ({()} : Finset Unit)
    f lo hi (fun _ => a) (fun _ => r) (fun _ => ModularCluster.poleBudget M k a τ)
    (fun _ => A) (fun _ => g) hre him (by intro i hi; exact hr)
    (by intro i hi; exact hinside)
    (by intro i hi j hj hij; exact (hij (Subsingleton.elim _ _)).elim)
    hfa (by intro i hi; exact hg) (by intro i hi; exact hfg)
  have hres : FinitePrincipalParts.rectangleCCW lo hi f =
      FinitePrincipalParts.circleCCW a r f := by simpa using heq.1
  rw [hf] at hres
  simpa only [lo, hi, G1FiniteLedger.rectangle_orientation,
    FinitePrincipalParts.circleCCW, complexCirclePullback] using hres

/-- C11. Output: a finite route with fixed geometric chains on each piece. It requires neither an
avoidance path nor a transport cover as input. [RW26, p. 29]. -/
theorem finite_route_separator_cover (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (τ : ℂ) (hτ : τ ∈ UpperWindow.tauRegion M ψ)
    (v₀ v₁ : ℂ × ℂ) (hv₀ : v₀ ∈ ratioFiber M τ n h ell p)
    (hv₁ : v₁ ∈ ratioFiber M τ n h ell p) :
    ∃ (P : Polygon) (U : Fin P.length → Set Parameters)
      (D : Fin P.length → Fin (M 1 0).toNat → CircleExtension),
      PolygonIn P (ratioFiber M τ n h ell p) v₀ v₁ ∧
      (∀ i, IsOpen (U i) ∧ U i ⊆ ratioTube M n h ell p ψ) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, (τ, polygonPoint P i t) ∈ U i) ∧
      (∀ i, ∀ x ∈ U i, ∀ m, SeparatesExtension (D i m) M x.1 x.2.2 n p (m : ℤ)) := by
  have hT : 0 < (etaDenom M τ).re :=
    (UpperWindow.tauRegion_properties M hM ψ hψ' τ hτ).2.2.1
  have hlocal (v : ratioFiber M τ n h ell p) :
      ∃ (U : Set Parameters) (D : Fin (M 1 0).toNat → CircleExtension),
        IsOpen U ∧ (τ, (v : ℂ × ℂ)) ∈ U ∧ U ⊆ ratioTube M n h ell p ψ ∧
          ∀ x ∈ U, ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ) := by
    obtain ⟨D, hD⟩ := exists_separating_extensions M hM τ hT n h ell p v v.property
    obtain ⟨U, hU, hvU, hsub, hsep⟩ :=
      separating_extension_stable M hM n h ell p ψ hψ hψ' (τ, (v : ℂ × ℂ))
        ⟨hτ, v.property⟩ D hD
    exact ⟨U, D, hU, hvU, hsub, hsep⟩
  choose U D hU hvU hsub hsep using hlocal
  let V (v : ratioFiber M τ n h ell p) : Set (ℂ × ℂ) :=
    (fun z : ℂ × ℂ => (τ, z)) ⁻¹' U v
  have hV (v : ratioFiber M τ n h ell p) : IsOpen (V v) :=
    (hU v).preimage (continuous_const.prodMk continuous_id)
  have hVS (v : ratioFiber M τ n h ell p) : V v ⊆ ratioFiber M τ n h ell p := by
    intro z hz
    exact (hsub v hz).2
  have hcover : ratioFiber M τ n h ell p ⊆ ⋃ v, V v := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hvU ⟨z, hz⟩⟩
  obtain ⟨P, hP⟩ := polygonal_route_exists M hM τ hT n h ell p v₀ v₁ hv₀ hv₁
  obtain ⟨Q, k, hQ, hpiece⟩ := G1ContinuationCirclesAux.polygon_subordinate_open_cover
    (ratioFiber M τ n h ell p) v₀ v₁
      (G1ContinuationCirclesAux.polygon_joinedIn P _ v₀ v₁ hP)
      V hV hVS hcover
  refine ⟨Q, (fun i => U (k i)), (fun i => D (k i)), hQ, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hU (k i), hsub (k i)⟩
  · intro i t ht
    exact hpiece i t ht
  · intro i x hx m
    exact hsep (k i) x hx m

/-- C12. Existing real terminal chains stay fixed for moving τ,w,y, on both sides. Pure geometry; no
lower identity is asserted. [RW26, p. 29]. -/
theorem real_chain_fixed_joint_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (w : ℂ) (n p : ℤ) (hT : 0 < g1T M τ₀)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set Parameters, IsOpen U ∧ ((τ₀ : ℂ), w, (y : ℂ)) ∈ U ∧
      ∀ x ∈ U, x.1 ∈ modularPhiDomain M ∧ 0 < (etaDenom M x.1).re ∧
        ∀ m, SeparatesExtension (ofChain (D m)) M x.1 x.2.2 n p (m : ℤ) := by
  let x₀ : Parameters := ((τ₀ : ℂ), w, (y : ℂ))
  have hT₀ : 0 < (etaDenom M (τ₀ : ℂ)).re := by simpa [etaDenom, g1T] using hT
  have hm (m : Fin (M 1 0).toNat) :
      ∀ᶠ q : ℂ × ℂ in 𝓝 ((τ₀ : ℂ), (y : ℂ)),
        SeparatesExtension (ofChain (D m)) M q.1 q.2 n p (m : ℤ) := by
    have hs := (ofChain_separates (D m) M (τ₀ : ℂ) (y : ℂ) n p (m : ℤ)).mpr
      ((G1FixedSeparation.separatesAt_ofReal_iff (D m) M τ₀ y n p (m : ℤ)).mpr (hD m))
    have he := G1ContinuationCirclesAux.separation_eventually M hM n p (m : ℤ)
      ((τ₀ : ℂ), (y : ℂ)) hT₀ (ofChain (D m)).base (ofChain (D m)).extra hs.2.2
    filter_upwards [he] with q hq
    exact ⟨hs.1, hs.2.1, hq⟩
  have hmap : Continuous (fun x : Parameters => (x.1, x.2.2)) := by fun_prop
  have he : ∀ᶠ x in 𝓝 x₀, ∀ m,
      SeparatesExtension (ofChain (D m)) M x.1 x.2.2 n p (m : ℤ) :=
    (hmap.tendsto x₀).eventually (Filter.eventually_all.mpr hm)
  have hdom : ∀ᶠ x in 𝓝 x₀, x.1 ∈ modularPhiDomain M :=
    ((ModularCluster.isOpen_modularPhiDomain M).preimage continuous_fst).mem_nhds
      (real_mem_modularPhiDomain M τ₀ hT)
  have hcont : Continuous (fun x : Parameters => (etaDenom M x.1).re) := by
    unfold etaDenom
    fun_prop
  have hpos : ∀ᶠ x in 𝓝 x₀, 0 < (etaDenom M x.1).re :=
    hcont.continuousAt.eventually (isOpen_Ioi.mem_nhds hT₀)
  obtain ⟨U, hsub, hU, hxU⟩ := mem_nhds_iff.mp (hdom.and (hpos.and he))
  exact ⟨U, hU, hxU, fun x hx => hsub hx⟩

#check @G1FixedSeparation.SeparatesAt
#check @G1FiniteLedger.finite_zero_assignment
#check @ModularCluster.Circles
#print CircleExtension
#print SeparatesExtension
#print extensionIntegral

end SICLean.L4.G1Continuation
