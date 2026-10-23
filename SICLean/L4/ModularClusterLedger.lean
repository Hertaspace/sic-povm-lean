import SICLean.L4.ModularClusterIntegrals
import SICLean.L4.ModularClusterLedgerAux

set_option autoImplicit false

/-!
# Merged principal parts and the finite circle ledger

The divisor sets are those of [RW26, p. 6].
The principal-part and circle interfaces are included below.

A Laurent expansion about a fixed cluster center is asserted only at the
parameter where all those labels coincide. Nearby split poles have their
own centers. The split ledger and its limit do not require any individual
simple residue to remain bounded. A ratio can have cancellation: its
principal part is padded to poleBudget, and its top coefficient may be zero.
Every local comparison is in a fixed-τ punctured ℂ germ or explicitly on a
closed disk minus its centers, never at a pole's arbitrary raw point value.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.ModularCluster

def circleLedger (M : SL(2, ℤ)) (k : KernelData) (C : Circles) (τ : ℂ) : ℂ :=
  ∑ a ∈ C.centers, circleContribution M k a (C.radius a) τ

/-- Integer coefficients encode CCW corrections, deletion, or reversal. -/
def weightedCircleLedger (M : SL(2, ℤ)) (k : KernelData) (C : Circles)
    (ν : ℂ → ℤ) (τ : ℂ) : ℂ :=
  ∑ a ∈ C.centers, (ν a : ℂ) * circleContribution M k a (C.radius a) τ

/--
Extraction: a finite germ order and isolation
produce a genuine principal part plus an analytic remainder on the whole
closed disk. This does not identify the raw center value; [RW26, p. 6].
-/
theorem exists_local_principalPart (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M) (r : ℝ) (hr : 0 < r)
    (hiso : ∀ b ∈ labels M k, dist (branchPoint M k τ b) a ≤ r →
      branchPoint M k τ b = a) :
    ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), AnalyticOnNhd ℂ g (Metric.closedBall a r) ∧
      ∀ z ∈ Metric.closedBall a r, z ≠ a →
        kernel M k z τ = FinitePrincipalParts.principalPart a (poleBudget M k a τ) A z + g z := by
  obtain ⟨A, g, _, hg, hfg⟩ := LedgerAux.principalPart_extraction
    (fun z => kernel M k z τ) a (poleBudget M k a τ) (kernelOrder M k a τ)
    (kernel_meromorphic M hM k τ hτ a (mem_univ a))
    (kernel_order M hM k a τ hτ) (kernelOrder_lower_bound M hM k a τ hτ)
    (Metric.closedBall a r) (kernel_analytic_on_isolated_disk M hM k τ a hτ r hiso)
  exact ⟨A, g, hg, hfg⟩

/--
At a pole of the single function the budget is the exact pole order, because
the exponential is a unit and excludes Φ pole-zero cancellation; [RW26, p. 6].
-/
theorem single_kernel_order (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (hsingle : k.ratio = false)
    (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M) (hp : 0 < poleBudget M k a τ) :
    meromorphicOrderAt (fun z => kernel M k z τ) a =
      (-(poleBudget M k a τ : ℤ) : WithTop ℤ) := by
  rw [kernel_order M hM k a τ hτ]
  have hb := poleBudget_single M k hsingle a τ
  have hz := zeroMultiplicity_eq_zero_of_pole M hM (k.m + 1) k.n a τ hτ
    (by simpa [hb] using hp)
  simp [kernelOrder, hsingle, modularPhiDivisorOrder, hz, hb]

/--
A merged single pole really has the full high order. No irrationality
assumption; in particular the rational multiple examples are included.
This leading-coefficient clause is deliberately not asserted for ratios; [RW26, p. 6].
-/
theorem merged_single_principalPart (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (hsingle : k.ratio = false) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hp : 0 < poleBudget M k a (τ₀ : ℂ))
    (hiso : ∀ b ∈ labels M k, dist (branchPoint M k (τ₀ : ℂ) b) a ≤ r →
      branchPoint M k (τ₀ : ℂ) b = a) :
    ∃ (A : ℕ → ℂ) (g : ℂ → ℂ),
      A (poleBudget M k a (τ₀ : ℂ) - 1) ≠ 0 ∧
      AnalyticOnNhd ℂ g (Metric.closedBall a r) ∧
      (∀ z ∈ Metric.closedBall a r, z ≠ a →
        kernel M k z (τ₀ : ℂ) =
          FinitePrincipalParts.principalPart a (poleBudget M k a (τ₀ : ℂ)) A z + g z) ∧
      circleContribution M k a r (τ₀ : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I *
          FinitePrincipalParts.residueCoefficient (poleBudget M k a (τ₀ : ℂ)) A := by
  have hτ₀ := real_mem_modularPhiDomain M τ₀ hT
  obtain ⟨A, g, hA, hg, hfg⟩ := LedgerAux.principalPart_extraction
    (fun z => kernel M k z (τ₀ : ℂ)) a (poleBudget M k a (τ₀ : ℂ))
    (-(poleBudget M k a (τ₀ : ℂ) : ℤ))
    (kernel_meromorphic M hM k (τ₀ : ℂ) hτ₀ a (mem_univ a))
    (single_kernel_order M hM k hsingle (τ₀ : ℂ) a hτ₀ hp) le_rfl
    (Metric.closedBall a r)
    (kernel_analytic_on_isolated_disk M hM k (τ₀ : ℂ) a hτ₀ r hiso)
  exact ⟨A, g, hA rfl hp, hg, hfg,
    FinitePrincipalParts.circleCCW_of_local_principalPart
      (fun z => kernel M k z (τ₀ : ℂ)) g a r (poleBudget M k a (τ₀ : ℂ)) A hr hg hfg⟩

/--
Whole-cluster formula at an isolated center, including padded principal
parts and order zero. [RW26, p. 6]. The proof uses `circleCCW_of_local_principalPart`.
-/
theorem circleContribution_principalPart (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M) (r : ℝ) (hr : 0 < r)
    (hiso : ∀ b ∈ labels M k, dist (branchPoint M k τ b) a ≤ r →
      branchPoint M k τ b = a) :
    ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), AnalyticOnNhd ℂ g (Metric.closedBall a r) ∧
      (∀ z ∈ Metric.closedBall a r, z ≠ a →
        kernel M k z τ = FinitePrincipalParts.principalPart a (poleBudget M k a τ) A z + g z) ∧
      circleContribution M k a r τ = 2 * (Real.pi : ℂ) * Complex.I *
        FinitePrincipalParts.residueCoefficient (poleBudget M k a τ) A := by
  obtain ⟨A, g, hg, hfg⟩ := exists_local_principalPart M hM k τ a hτ r hr hiso
  exact ⟨A, g, hg, hfg,
    FinitePrincipalParts.circleCCW_of_local_principalPart
      (fun z => kernel M k z τ) g a r (poleBudget M k a τ) A hr hg hfg⟩

/--
A local circle may be resized while enclosing precisely the same merged
center. This supplies a concrete circle-change interface; [RW26, p. 6].
-/
theorem circleContribution_radius_independent (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (r r' : ℝ) (hr : 0 < r) (hr' : 0 < r')
    (hiso : ∀ b ∈ labels M k, dist (branchPoint M k τ b) a ≤ max r r' →
      branchPoint M k τ b = a) :
    circleContribution M k a r τ = circleContribution M k a r' τ := by
  obtain ⟨A, g, hg, hfg⟩ := exists_local_principalPart M hM k τ a hτ
    (max r r') (lt_of_lt_of_le hr (le_max_left _ _)) hiso
  have hcircle (s : ℝ) (hs : 0 < s) (hle : s ≤ max r r') :
      circleContribution M k a s τ = 2 * (Real.pi : ℂ) * Complex.I *
        FinitePrincipalParts.residueCoefficient (poleBudget M k a τ) A :=
    FinitePrincipalParts.circleCCW_of_local_principalPart
      (fun z => kernel M k z τ) g a s (poleBudget M k a τ) A hs
      (hg.mono (Metric.closedBall_subset_closedBall hle))
      (fun z hz => hfg z (Metric.closedBall_subset_closedBall hle hz))
  exact (hcircle r hr (le_max_left _ _)).trans (hcircle r' hr' (le_max_right _ _)).symm

/--
The finite outer-circle ledger, complementing the rectangular ledger.
The finite global principal-part decomposition is an explicit analytic
input, not an assumed integral equality. [RW26, p. 6].
-/
theorem outer_circle_finite_principal_parts (f g : ℂ → ℂ) (a : ℂ) (r : ℝ)
    (P : Finset ℂ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (hr : 0 < r)
    (hinside : ∀ z ∈ P, dist z a < r)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall a r))
    (hfg : ∀ z ∈ Metric.closedBall a r, z ∉ P →
      f z = FinitePrincipalParts.finitePrincipalPart P id N A z + g z) :
    FinitePrincipalParts.circleCCW a r f = 2 * (Real.pi : ℂ) * Complex.I *
      ∑ z ∈ P, FinitePrincipalParts.residueCoefficient (N z) (A z) := by
  exact LedgerAux.outer_circle_finite_principal_parts f g a r P N A hr hinside hg hfg

/--
Before merging, all moving centers inside one fixed circle contribute
their total residue. Local expansions are at the moving centers; no false
fixed-center expansion is asserted for split poles; [RW26, p. 6].
-/
theorem circleContribution_split_ledger (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M) (r : ℝ) (hr : 0 < r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ) ∈ regularDomain M k) :
    ∃ (P : Finset ℂ) (A : ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ),
      (P : Set ℂ) = movingCenters M k τ a r ∧
      (∀ z ∈ P, AnalyticAt ℂ (g z) z ∧
        (fun w => kernel M k w τ) =ᶠ[𝓝[≠] z]
          (fun w => FinitePrincipalParts.principalPart z (poleBudget M k z τ) (A z) w + g z w)) ∧
      circleContribution M k a r τ = 2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ P, FinitePrincipalParts.residueCoefficient (poleBudget M k z τ) (A z) := by
  have hex : ∀ z : ℂ, ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z ∧
      (fun w => kernel M k w τ) =ᶠ[𝓝[≠] z]
        (fun w => FinitePrincipalParts.principalPart z (poleBudget M k z τ) A w + g w) :=
    fun z => LedgerAux.principalPart_germ (fun w => kernel M k w τ) z
      (poleBudget M k z τ) (kernelOrder M k z τ)
      (kernel_meromorphic M hM k τ hτ z (mem_univ z))
      (kernel_order M hM k z τ hτ) (kernelOrder_lower_bound M hM k z τ hτ)
  choose A g hA using hex
  let P := (movingCenters_finite M hM k τ a hτ r hr).toFinset
  have hP : (P : Set ℂ) = movingCenters M k τ a r := Set.Finite.coe_toFinset _
  refine ⟨P, A, g, hP, fun z _ => hA z, ?_⟩
  exact LedgerAux.circle_finite_prescribed_germs (fun z => kernel M k z τ) a r P
    (fun z => poleBudget M k z τ) A g hr
    (fun z hz => (show z ∈ movingCenters M k τ a r from hP ▸ hz).1)
    (kernel_analyticOn_closedBall_off_centers M hM k τ a hτ r P hP hsafe)
    (fun z _ => hA z)

/--
The full finite sum at the merged parameter, without replacing
multiple poles by simple ones; [RW26, p. 6].
-/
theorem finite_circle_ledger_at_center (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M) (C : Circles)
    (hr : ∀ a ∈ C.centers, 0 < C.radius a)
    (hdisj : ∀ a ∈ C.centers, ∀ a' ∈ C.centers, a ≠ a' →
      Disjoint (Metric.closedBall a (C.radius a)) (Metric.closedBall a' (C.radius a')))
    (hiso : ∀ a ∈ C.centers, ∀ b ∈ labels M k,
      dist (branchPoint M k τ₀ b) a ≤ C.radius a → branchPoint M k τ₀ b = a) :
    ∃ (A : ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ),
      (∀ a ∈ C.centers, AnalyticOnNhd ℂ (g a) (Metric.closedBall a (C.radius a)) ∧
        ∀ z ∈ Metric.closedBall a (C.radius a), z ≠ a →
          kernel M k z τ₀ =
            FinitePrincipalParts.principalPart a (poleBudget M k a τ₀) (A a) z + g a z) ∧
      circleLedger M k C τ₀ = 2 * (Real.pi : ℂ) * Complex.I *
        ∑ a ∈ C.centers, FinitePrincipalParts.residueCoefficient (poleBudget M k a τ₀) (A a) := by
  have hex : ∀ a : ℂ, ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), a ∈ C.centers →
      AnalyticOnNhd ℂ g (Metric.closedBall a (C.radius a)) ∧
      (∀ z ∈ Metric.closedBall a (C.radius a), z ≠ a →
        kernel M k z τ₀ =
          FinitePrincipalParts.principalPart a (poleBudget M k a τ₀) A z + g z) ∧
      circleContribution M k a (C.radius a) τ₀ = 2 * (Real.pi : ℂ) * Complex.I *
        FinitePrincipalParts.residueCoefficient (poleBudget M k a τ₀) A := by
    intro a
    by_cases ha : a ∈ C.centers
    · obtain ⟨A, g, hg, hfg, hc⟩ := circleContribution_principalPart M hM k τ₀ a hτ₀
        (C.radius a) (hr a ha) (hiso a ha)
      exact ⟨A, g, fun _ => ⟨hg, hfg, hc⟩⟩
    · exact ⟨0, 0, fun h => (ha h).elim⟩
  choose A g h using hex
  refine ⟨A, g, fun a ha => ⟨(h a ha).1, (h a ha).2.1⟩, ?_⟩
  unfold circleLedger
  simp_rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a ha => (h a ha).2.2)

/--
Finite sum continuity; [RW26, p. 6]. No estimate for a sum over infinitely many clusters.
-/
theorem continuousAt_circleLedger (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (C : Circles)
    (hr : ∀ a ∈ C.centers, 0 < C.radius a)
    (hsafe : ∀ z ∈ boundaries C, (z, τ₀) ∈ regularDomain M k) :
    ContinuousAt (circleLedger M k C) τ₀ := by
  apply tendsto_finsetSum
  intro a ha
  exact continuousAt_circleContribution M hM k τ₀ a (C.radius a) (hr a ha)
    (fun z hz => hsafe z ⟨a, ha, hz⟩)

/--
Direct finite-chain limit; [RW26, p. 6].
-/
theorem circleLedger_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (C : Circles)
    (hr : ∀ a ∈ C.centers, 0 < C.radius a)
    (hsafe : ∀ z ∈ boundaries C, (z, τ₀) ∈ regularDomain M k) :
    Tendsto (circleLedger M k C) (𝓝 τ₀) (𝓝 (circleLedger M k C τ₀)) := by
  exact continuousAt_circleLedger M hM k τ₀ C hr hsafe

/--
Signed/integer circle corrections transfer with the parameter. The
coefficient is fixed, as required for finite chain ledger; [RW26, p. 6].
-/
theorem weightedCircleLedger_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (C : Circles) (ν : ℂ → ℤ)
    (hr : ∀ a ∈ C.centers, 0 < C.radius a)
    (hsafe : ∀ z ∈ boundaries C, (z, τ₀) ∈ regularDomain M k) :
    Tendsto (weightedCircleLedger M k C ν) (𝓝 τ₀)
      (𝓝 (weightedCircleLedger M k C ν τ₀)) := by
  apply tendsto_finsetSum
  intro a ha
  exact continuousAt_const.mul (continuousAt_circleContribution M hM k τ₀ a
    (C.radius a) (hr a ha) (fun z hz => hsafe z ⟨a, ha, hz⟩))

/--
Real boundary outlet: identify both limits with the high-order merged
principal parts. Rational τ₀, same-class multiplicities and cancellation
are included. [RW26, p. 6]. The lower side is included. No simple-residue bounds appear as
hypotheses.
-/
theorem real_boundary_merged_ledger (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) (C : Circles)
    (hr : ∀ a ∈ C.centers, 0 < C.radius a)
    (hdisj : ∀ a ∈ C.centers, ∀ a' ∈ C.centers, a ≠ a' →
      Disjoint (Metric.closedBall a (C.radius a)) (Metric.closedBall a' (C.radius a')))
    (hiso : ∀ a ∈ C.centers, ∀ b ∈ labels M k,
      dist (branchPoint M k (τ₀ : ℂ) b) a ≤ C.radius a → branchPoint M k (τ₀ : ℂ) b = a) :
    ∃ (A : ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ),
      (∀ a ∈ C.centers, AnalyticOnNhd ℂ (g a) (Metric.closedBall a (C.radius a)) ∧
        ∀ z ∈ Metric.closedBall a (C.radius a), z ≠ a →
          kernel M k z (τ₀ : ℂ) =
            FinitePrincipalParts.principalPart a (poleBudget M k a (τ₀ : ℂ)) (A a) z + g a z) ∧
      circleLedger M k C (τ₀ : ℂ) = 2 * (Real.pi : ℂ) * Complex.I *
        ∑ a ∈ C.centers,
          FinitePrincipalParts.residueCoefficient (poleBudget M k a (τ₀ : ℂ)) (A a) ∧
      Tendsto (circleLedger M k C) (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
        (𝓝 (2 * (Real.pi : ℂ) * Complex.I * ∑ a ∈ C.centers,
          FinitePrincipalParts.residueCoefficient (poleBudget M k a (τ₀ : ℂ)) (A a))) ∧
      Tendsto (circleLedger M k C) (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ))
        (𝓝 (2 * (Real.pi : ℂ) * Complex.I * ∑ a ∈ C.centers,
          FinitePrincipalParts.residueCoefficient (poleBudget M k a (τ₀ : ℂ)) (A a))) := by
  have hτ₀ := real_mem_modularPhiDomain M τ₀ hT
  obtain ⟨A, g, hloc, hledger⟩ :=
    finite_circle_ledger_at_center M hM k (τ₀ : ℂ) hτ₀ C hr hdisj hiso
  have hsafe : ∀ z ∈ boundaries C, (z, (τ₀ : ℂ)) ∈ regularDomain M k := by
    rintro z ⟨a, ha, hz⟩
    exact sphere_regular_of_isolated M hM k (τ₀ : ℂ) a hτ₀ (C.radius a)
      (hr a ha) (hiso a ha) z hz
  have hlim := circleLedger_tendsto M hM k (τ₀ : ℂ) C hr hsafe
  rw [hledger] at hlim
  exact ⟨A, g, hloc, hledger, hlim.mono_left nhdsWithin_le_nhds,
    hlim.mono_left nhdsWithin_le_nhds⟩

/--
Any actual local Laurent coefficients at the moving centers have a
convergent sum. There is no individual coefficient bound. The centers and
germ expansions are explicit inputs; their existence is supplied by
`circleContribution_split_ledger` and `exists_local_principalPart`; [RW26, p. 6].
-/
theorem split_residue_sum_tendsto_merged (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ a : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M) (r : ℝ) (hr : 0 < r)
    (hiso : ∀ b ∈ labels M k, dist (branchPoint M k τ₀ b) a ≤ r →
      branchPoint M k τ₀ b = a)
    (P : ℂ → Finset ℂ) (A : ℂ → ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ → ℂ)
    (hP : ∀ᶠ τ in 𝓝 τ₀, (P τ : Set ℂ) = movingCenters M k τ a r)
    (hA : ∀ᶠ τ in 𝓝 τ₀, ∀ z ∈ P τ, AnalyticAt ℂ (g τ z) z ∧
      (fun w => kernel M k w τ) =ᶠ[𝓝[≠] z]
        (fun w => FinitePrincipalParts.principalPart z (poleBudget M k z τ) (A τ z) w + g τ z w))
    (A₀ : ℕ → ℂ) (g₀ : ℂ → ℂ)
    (hg₀ : AnalyticOnNhd ℂ g₀ (Metric.closedBall a r))
    (hA₀ : ∀ z ∈ Metric.closedBall a r, z ≠ a →
      kernel M k z τ₀ = FinitePrincipalParts.principalPart a (poleBudget M k a τ₀) A₀ z + g₀ z) :
    Tendsto (fun τ => ∑ z ∈ P τ,
      FinitePrincipalParts.residueCoefficient (poleBudget M k z τ) (A τ z)) (𝓝 τ₀)
      (𝓝 (FinitePrincipalParts.residueCoefficient (poleBudget M k a τ₀) A₀)) := by
  have hsafe := sphere_regular_of_isolated M hM k τ₀ a hτ₀ r hr hiso
  have hev := eventually_regular_sphere M hM k τ₀ a hτ₀ r hsafe
  have hledger : ∀ᶠ τ in 𝓝 τ₀,
      circleContribution M k a r τ = 2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ P τ, FinitePrincipalParts.residueCoefficient (poleBudget M k z τ) (A τ z) := by
    filter_upwards [hev, hP, hA] with τ hτ hPτ hAτ
    exact LedgerAux.circle_finite_prescribed_germs (fun z => kernel M k z τ) a r
      (P τ) (fun z => poleBudget M k z τ) (A τ) (g τ) hr
      (fun z hz => (show z ∈ movingCenters M k τ a r from hPτ ▸ hz).1)
      (kernel_analyticOn_closedBall_off_centers M hM k τ a hτ.1 r (P τ) hPτ hτ.2) hAτ
  have hcenter : circleContribution M k a r τ₀ = 2 * (Real.pi : ℂ) * Complex.I *
      FinitePrincipalParts.residueCoefficient (poleBudget M k a τ₀) A₀ :=
    FinitePrincipalParts.circleCCW_of_local_principalPart (fun z => kernel M k z τ₀)
      g₀ a r (poleBudget M k a τ₀) A₀ hr hg₀ hA₀
  have hc : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hlim := (circleContribution_tendsto M hM k τ₀ a r hr hsafe).div_const
    (2 * (Real.pi : ℂ) * Complex.I)
  rw [hcenter, mul_div_cancel_left₀ _ hc] at hlim
  apply hlim.congr'
  filter_upwards [hledger] with τ hτ
  rw [hτ, mul_div_cancel_left₀ _ hc]

/--
Clockwise reversal has the negative sign. This records the orientation of the finite circle
contribution.
[RW26, p. 6].
-/
theorem circle_correction_orientation (M : SL(2, ℤ)) (k : KernelData)
    (τ a : ℂ) (r : ℝ) :
    FinitePrincipalParts.circleCW a r (fun z => kernel M k z τ) =
      -circleContribution M k a r τ := by
  exact FinitePrincipalParts.circleCW_eq_neg a r (fun z => kernel M k z τ)

#check FinitePrincipalParts.principalPart
#check FinitePrincipalParts.residueCoefficient
#check FinitePrincipalParts.circleCCW_of_local_principalPart
#check FinitePrincipalParts.finite_circle_ledger
#check MeromorphicAt
#check meromorphicOrderAt
#print circleLedger
#print weightedCircleLedger
#print split_residue_sum_tendsto_merged

end SICLean.L4.ModularCluster
