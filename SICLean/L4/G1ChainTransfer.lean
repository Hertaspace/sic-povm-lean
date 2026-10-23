import SICLean.L4.G1FixedSeparation
import SICLean.L4.G1FiniteChainLedger
import SICLean.L4.G1ChainTransferAux

set_option autoImplicit false

/-!
# Absolute integrability and independence of the G1 chain

[RW26, p. 7, p. 13] describe the deformations. The comparisons are
formalized here.

All main statements use the existing `G1VerticalChain`, `G1Separates`, `g1ChainIntegral`,
`G1ChainIntegrable`, `g1RatioKernel`, `g1S`, `g1L`, and `g1NoPinch` directly. Integrability is an
output for every geometric chain, never an extra input to a transfer theorem. There is no disjoint
circle, simple-pole, special-baseline or irrational-parameter assumption. The only generic
truncation lemma takes an integrability fact, which `chain_integrable` supplies for all these actual
kernels.

`contract_chain_clauses` provides precisely geometric existence and the common value on all
separating families. It deliberately does not assert the G1 RHS identity, its removability, or
`G1RealConclusion`. No G2 file is imported or used.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1ChainTransfer

/-- A bare upward line, as an existing G1VerticalChain with no circles. Used only to state the sign
of crossing a pole. -/
def plainChain (x : ℝ) : G1VerticalChain :=
  { crossing := x, centers := ∅, radius := fun _ => 0 }

/-- Both boundary-safe clauses and equality of the existing assignment follow from G1Separates
alone. [RW26, p. 7, p. 13]. -/
theorem separates_boundary_assignment (D₀ D₁ : G1VerticalChain) (P Z : Set ℝ)
    (hD₀ : G1Separates D₀ P Z) (hD₁ : G1Separates D₁ P Z) :
    G1FiniteLedger.boundaryAvoids D₀ (P ∪ Z) ∧
      G1FiniteLedger.boundaryAvoids D₁ (P ∪ Z) ∧
        G1FiniteLedger.sameAssignment D₀ D₁ (P ∪ Z) := by
  refine ⟨⟨hD₀.1, hD₀.2.1⟩, ⟨hD₁.1, hD₁.2.1⟩, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · rw [hD₀.2.2.1 x hx, hD₁.2.2.1 x hx]
  · rw [hD₀.2.2.2 x hx, hD₁.2.2.2 x hx]

/-- Joint regularity locus at every real-chain boundary point. Phi poles of the denominator are
allowed; the specified inverse there is its analytic zero. No continuity claim is made at candidate
poles. [RW26, p. 6, p. 7, p. 13]. -/
theorem boundary_regularDomain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ) (D : G1VerticalChain)
    (hD : G1FiniteLedger.boundaryAvoids D (G1FiniteLedger.candidatePoles M τ y n p m)) :
    (∀ t : ℝ, (g1VerticalPoint D.crossing t, (τ : ℂ)) ∈
      ModularCluster.regularDomain M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)) ∧
      ∀ r ∈ D.centers, ∀ θ : ℝ, (circleMap (r : ℂ) (D.radius r) θ, (τ : ℂ)) ∈
        ModularCluster.regularDomain M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m) := by
  constructor
  · intro t
    apply G1ChainTransferAux.regular_of_avoids M hM τ w y n h ell p m hT
    intro x hx heq
    have hx' : D.crossing = x := by
      simpa [g1VerticalPoint] using congrArg Complex.re heq
    exact (hD.2 x hx).1 hx'.symm
  · intro r hr θ
    apply G1ChainTransferAux.regular_of_avoids M hM τ w y n h ell p m hT
    intro x hx heq
    have hd := circleMap_mem_sphere (r : ℂ) (hD.1 r hr).le θ
    rw [heq] at hd
    exact (hD.2 x hx).2 r hr (by
      simpa only [Metric.mem_sphere, dist_eq_norm, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hd)

/-- Continuity of the actual pullbacks on the whole boundary, including regular denominator-pole
points. [RW26, p. 7, p. 13]. -/
theorem boundary_continuous (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ) (D : G1VerticalChain)
    (hD : G1FiniteLedger.boundaryAvoids D (G1FiniteLedger.candidatePoles M τ y n p m)) :
    Continuous (g1VerticalPullback (g1RatioKernel M τ w y n h ell p m) D.crossing) ∧
      ∀ r ∈ D.centers,
        Continuous (g1CirclePullback (g1RatioKernel M τ w y n h ell p m) r (D.radius r)) := by
  obtain ⟨hv, hc⟩ := boundary_regularDomain M hM τ w y n h ell p m hT D hD
  have hk (q : ℝ → ℂ) (hq : Continuous q)
      (hsafe : ∀ t, (q t, (τ : ℂ)) ∈ ModularCluster.regularDomain M
        (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)) :
      Continuous (fun t => g1RatioKernel M τ w y n h ell p m (q t)) := by
    simp_rw [G1Pinch.g1RatioKernel_eq_kernel]
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((ModularCluster.kernel_joint_analytic M hM
      (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)) _ (hsafe t)).continuousAt.comp
      (f := fun u : ℝ => (q u, (τ : ℂ)))
      (hq.prodMk continuous_const).continuousAt
  constructor
  · exact (hk _ (by unfold g1VerticalPoint; fun_prop) hv).mul continuous_const
  · intro r hr
    exact (hk _ (continuous_circleMap _ _) (hc r hr)).mul
      (continuous_const.mul ((continuous_circleMap _ _).sub continuous_const))

/-- All finite circles are integrable; no strict window is needed for a compact boundary. [RW26, p.
7, p. 13]. -/
theorem circles_intervalIntegrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ) (D : G1VerticalChain)
    (hD : G1FiniteLedger.boundaryAvoids D (G1FiniteLedger.candidatePoles M τ y n p m)) :
    ∀ r ∈ D.centers,
      IntervalIntegrable (g1CirclePullback (g1RatioKernel M τ w y n h ell p m) r (D.radius r))
        volume 0 (2 * Real.pi) := by
  intro r hr
  exact (boundary_continuous M hM τ w y n h ell p m hT D hD).2 r hr
    |>.intervalIntegrable _ _

/-- Strict windows plus a regular compact middle give absolute vertical integrability. No G1
identity or no-pinch premise is used here. [RW26, p. 7, p. 13]. -/
theorem vertical_integrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0)
    (D : G1VerticalChain)
    (hD : G1FiniteLedger.boundaryAvoids D (G1FiniteLedger.candidatePoles M τ y n p m)) :
    Integrable (g1VerticalPullback (g1RatioKernel M τ w y n h ell p m) D.crossing) := by
  obtain ⟨ρ, C, κ, R, hρ, _hC, hκ, _hR, hbound⟩ :=
    G1RatioTail.uniform_two_tail_bound M hM τ w y D.crossing D.crossing n h ell p
      {m} hT hs hL le_rfl
  apply G1ChainTransferAux.integrable_of_tail_bound _
    (boundary_continuous M hM τ w y n h ell p m hT D hD).1 C κ R hκ
  intro t ht
  have hτ : (τ : ℂ) ∈ ModularSector.upperParameterDisk τ ρ := by
    simp [ModularSector.upperParameterDisk, ModularSector.parameterDisk, hρ.le]
  have hb := hbound (τ : ℂ) hτ m (Finset.mem_singleton_self m) D.crossing
    ⟨le_rfl, le_rfl⟩ t ht
  simpa only [G1RatioTail.complexKernel_real, g1VerticalPullback, norm_mul,
    Complex.norm_I, mul_one] using hb

/-- Direct contract integrability, as a conclusion for every boundary-safe chain. Disjoint small
circles are needed only for one construction, not for this statement. [RW26, p. 7, p. 13]. -/
theorem chain_integrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0)
    (D : G1VerticalChain)
    (hD : G1FiniteLedger.boundaryAvoids D (G1FiniteLedger.candidatePoles M τ y n p m)) :
    G1ChainIntegrable D (g1RatioKernel M τ w y n h ell p m) := by
  exact ⟨vertical_integrable M hM τ w y n h ell p m hT hs hL D hD,
    circles_intervalIntegrable M hM τ w y n h ell p m hT D hD⟩

/-- The only analytic premise here is the integrability already output above. The limit is to the
contract's integral, not a new definition of that integral. [RW26, p. 7, p. 13]. -/
theorem truncated_tendsto (D : G1VerticalChain) (f : ℂ → ℂ)
    (hInt : G1ChainIntegrable D f) :
    Tendsto (G1FiniteLedger.truncatedIntegral D f) atTop (𝓝 (g1ChainIntegral D f)) := by
  have hv := intervalIntegral_tendsto_integral hInt.1
    tendsto_neg_atTop_atBot tendsto_id
  unfold G1FiniteLedger.truncatedIntegral G1FiniteLedger.verticalSegment g1ChainIntegral
  exact hv.add_const _

/-- Arbitrary baseline order and arbitrary finite circles. Same assignment on the full candidate
divisor is sufficient, including canceled poles. Finite-zero-assignment + two vanishing edges prove
this; convergence is not an input. [RW26, p. 7, p. 13]. -/
theorem same_assignment_integral (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0)
    (D₀ D₁ : G1VerticalChain)
    (hD₀ : G1FiniteLedger.boundaryAvoids D₀ (G1FiniteLedger.candidatePoles M τ y n p m))
    (hD₁ : G1FiniteLedger.boundaryAvoids D₁ (G1FiniteLedger.candidatePoles M τ y n p m))
    (hassign : G1FiniteLedger.sameAssignment D₀ D₁ (G1FiniteLedger.candidatePoles M τ y n p m)) :
    G1ChainIntegrable D₀ (g1RatioKernel M τ w y n h ell p m) ∧
      G1ChainIntegrable D₁ (g1RatioKernel M τ w y n h ell p m) ∧
      g1ChainIntegral D₀ (g1RatioKernel M τ w y n h ell p m) =
        g1ChainIntegral D₁ (g1RatioKernel M τ w y n h ell p m) := by
  have hi₀ := chain_integrable M hM τ w y n h ell p m hT hs hL D₀ hD₀
  have hi₁ := chain_integrable M hM τ w y n h ell p m hT hs hL D₁ hD₁
  refine ⟨hi₀, hi₁, ?_⟩
  obtain ⟨B, hB₀, hB₁⟩ := G1ChainTransferAux.exists_bound D₀ D₁
  obtain ⟨htop, hbot⟩ :=
    G1RatioTail.horizontal_limits M hM τ w y D₀.crossing D₁.crossing n h ell p m hT hs hL
  have hlim := ((truncated_tendsto D₁ _ hi₁).sub (truncated_tendsto D₀ _ hi₀)).add
    (hbot.sub htop)
  have hzero : Tendsto (fun R =>
      G1FiniteLedger.truncatedIntegral D₁ (g1RatioKernel M τ w y n h ell p m) R -
      G1FiniteLedger.truncatedIntegral D₀ (g1RatioKernel M τ w y n h ell p m) R +
      G1FiniteLedger.connectors (g1RatioKernel M τ w y n h ell p m)
        D₀.crossing D₁.crossing R) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop B] with R hR
    exact (G1FiniteLedger.finite_zero_assignment M hM τ w y B R n h ell p m hT
      D₀ D₁ hD₀ hD₁ hassign hB₀ hB₁ hR).symm
  have heq := tendsto_nhds_unique hlim hzero
  exact (sub_eq_zero.mp (by simpa only [sub_self, add_zero] using heq)).symm

/-- The per-component G1 interface form: every two G1Separates chains give the same existing
integral. [RW26, p. 7, p. 13]. -/
theorem separating_integral_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0)
    (D₀ D₁ : G1VerticalChain)
    (hD₀ : G1Separates D₀ (g1NumeratorPoles M τ n m) (g1InversePoles M τ y n p m))
    (hD₁ : G1Separates D₁ (g1NumeratorPoles M τ n m) (g1InversePoles M τ y n p m)) :
    g1ChainIntegral D₀ (g1RatioKernel M τ w y n h ell p m) =
      g1ChainIntegral D₁ (g1RatioKernel M τ w y n h ell p m) := by
  obtain ⟨hb₀, hb₁, ha⟩ := separates_boundary_assignment D₀ D₁ _ _ hD₀ hD₁
  exact (same_assignment_integral M hM τ w y n h ell p m hT hs hL
    D₀ D₁ hb₀ hb₁ ha).2.2

/-- The exact Fin-c sum and integrability types used in G1RealConclusion. The reference family
requires only the same geometric predicate. [RW26, p. 7, p. 13]. -/
theorem family_integral_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0)
    (D₀ D₁ : Fin (M 1 0).toNat → G1VerticalChain)
    (hD₀ : ∀ m, G1Separates (D₀ m) (g1NumeratorPoles M τ n (m : ℤ))
      (g1InversePoles M τ y n p (m : ℤ)))
    (hD₁ : ∀ m, G1Separates (D₁ m) (g1NumeratorPoles M τ n (m : ℤ))
      (g1InversePoles M τ y n p (m : ℤ))) :
    (∀ m, G1ChainIntegrable (D₁ m) (g1RatioKernel M τ w y n h ell p (m : ℤ))) ∧
      (∑ m : Fin (M 1 0).toNat, g1ChainIntegral (D₀ m) (g1RatioKernel M τ w y n h ell p (m : ℤ))) =
        ∑ m : Fin (M 1 0).toNat, g1ChainIntegral (D₁ m) (g1RatioKernel M τ w y n h ell p (m : ℤ)) := by
  refine ⟨fun m => chain_integrable M hM τ w y n h ell p (m : ℤ) hT hs hL
    (D₁ m) ⟨(hD₁ m).1, (hD₁ m).2.1⟩, ?_⟩
  apply Finset.sum_congr rfl
  intro m _
  exact separating_integral_eq M hM τ w y n h ell p (m : ℤ) hT hs hL
    (D₀ m) (D₁ m) (hD₀ m) (hD₁ m)

/-- Unconditional geometric existence + all-chain common value, ready for the last G1 module to
identify that value. This is not the real integral identity or RHS removability. [RW26, p. 7, p.
13]. -/
theorem contract_chain_clauses (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0)
    (hpinch : g1NoPinch M τ y p) :
    ∃ D₀ : Fin (M 1 0).toNat → G1VerticalChain,
      (∀ m, G1Separates (D₀ m) (g1NumeratorPoles M τ n (m : ℤ))
        (g1InversePoles M τ y n p (m : ℤ))) ∧
      ∀ D : Fin (M 1 0).toNat → G1VerticalChain,
        (∀ m, G1Separates (D m) (g1NumeratorPoles M τ n (m : ℤ))
          (g1InversePoles M τ y n p (m : ℤ))) →
        (∀ m, G1ChainIntegrable (D m) (g1RatioKernel M τ w y n h ell p (m : ℤ))) ∧
        (∑ m : Fin (M 1 0).toNat, g1ChainIntegral (D m) (g1RatioKernel M τ w y n h ell p (m : ℤ))) =
          ∑ m : Fin (M 1 0).toNat, g1ChainIntegral (D₀ m) (g1RatioKernel M τ w y n h ell p (m : ℤ)) := by
  obtain ⟨D₀, hD₀⟩ :=
    (G1FixedSeparation.noPinch_iff_exists_separatingFamily M hM τ y hT n p).mp hpinch
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  obtain ⟨hInt, hEq⟩ := family_integral_eq M hM τ w y n h ell p hT hs hL D₀ D hD₀ hD
  exact ⟨hInt, hEq.symm⟩

/-- Right shift across one whole pole adds +2πi times its residue, even if it is a multiple pole.
The residue is given by a genuine punctured principal part, not defined as its circle integral. This
determines the counterclockwise sign used by all chains. [RW26,
p. 7, p. 13]. -/
theorem upward_shift_residue (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y x₀ x₁ a : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0)
    (ha₀ : x₀ < a) (ha₁ : a < x₁)
    (hcross₀ : x₀ ∉ G1FiniteLedger.candidatePoles M τ y n p m)
    (hcross₁ : x₁ ∉ G1FiniteLedger.candidatePoles M τ y n p m)
    (honly : G1FiniteLedger.candidatePoles M τ y n p m ∩ Ioo x₀ x₁ = {a}) :
    ∃ (ρ : ℝ) (A : ℕ → ℂ) (g : ℂ → ℂ),
      0 < ρ ∧ ρ < min (a - x₀) (x₁ - a) ∧
      AnalyticOnNhd ℂ g (Metric.closedBall (a : ℂ) ρ) ∧
      (∀ z ∈ Metric.closedBall (a : ℂ) ρ, z ≠ (a : ℂ) →
        g1RatioKernel M τ w y n h ell p m z =
          FinitePrincipalParts.principalPart (a : ℂ)
            (G1FiniteLedger.orderBudget M τ w y n h ell p m a) A z + g z) ∧
      g1ChainIntegral (plainChain x₁) (g1RatioKernel M τ w y n h ell p m) =
        g1ChainIntegral (plainChain x₀) (g1RatioKernel M τ w y n h ell p m) +
          2 * (Real.pi : ℂ) * Complex.I * FinitePrincipalParts.residueCoefficient
            (G1FiniteLedger.orderBudget M τ w y n h ell p m a) A := by
  let ρ := min (a - x₀) (x₁ - a) / 2
  have hmin : 0 < min (a - x₀) (x₁ - a) :=
    lt_min (sub_pos.mpr ha₀) (sub_pos.mpr ha₁)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρmin : ρ < min (a - x₀) (x₁ - a) := by
    dsimp [ρ]
    linarith
  have hρ₀ : ρ < a - x₀ := lt_of_lt_of_le hρmin (min_le_left _ _)
  have hρ₁ : ρ < x₁ - a := lt_of_lt_of_le hρmin (min_le_right _ _)
  have hiso : ∀ x ∈ G1FiniteLedger.candidatePoles M τ y n p m,
      |x - a| ≤ ρ → x = a := by
    intro x hx hdist
    have hxint : x ∈ Ioo x₀ x₁ := by
      rcases abs_le.mp hdist with ⟨hl, hu⟩
      constructor <;> linarith
    have hxmem : x ∈ ({a} : Set ℝ) := by
      rw [← honly]
      exact ⟨hx, hxint⟩
    simpa using hxmem
  have hfar : ∀ x ∈ G1FiniteLedger.candidatePoles M τ y n p m,
      x ≠ a → ρ < |x - a| := by
    intro x hx hxa
    by_contra hh
    exact hxa (hiso x hx (le_of_not_gt hh))
  let D : G1VerticalChain :=
    { crossing := x₀, centers := {a}, radius := fun _ => ρ }
  have hD : G1FiniteLedger.boundaryAvoids D
      (G1FiniteLedger.candidatePoles M τ y n p m) := by
    refine ⟨?_, ?_⟩
    · intro r hr
      exact hρ
    · intro x hx
      refine ⟨?_, ?_⟩
      · intro heq
        change x = x₀ at heq
        exact hcross₀ (heq ▸ hx)
      · intro r hr
        have hra : r = a := by simpa [D] using hr
        subst r
        change |x - a| ≠ ρ
        intro heq
        have hxa : x = a := hiso x hx heq.le
        subst x
        simp at heq
        linarith
  have hplain : G1FiniteLedger.boundaryAvoids (plainChain x₁)
      (G1FiniteLedger.candidatePoles M τ y n p m) := by
    refine ⟨by simp [plainChain], ?_⟩
    intro x hx
    refine ⟨?_, by simp [plainChain]⟩
    intro heq
    change x = x₁ at heq
    exact hcross₁ (heq ▸ hx)
  have hassign : G1FiniteLedger.sameAssignment D (plainChain x₁)
      (G1FiniteLedger.candidatePoles M τ y n p m) := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      simp only [g1LeftAssignment, g1CircleWinding, D, plainChain,
        Finset.sum_singleton, Finset.sum_empty]
      simp [ha₁, not_lt_of_ge ha₀.le, hρ]
    · have hnoinside : ¬ |x - a| < ρ := not_lt_of_ge (hfar x hx hxa).le
      have hbefore : (x < x₁) ↔ x < x₀ := by
        constructor
        · intro hx₁
          by_contra hh
          have hne : x ≠ x₀ := by
            intro heq
            exact hcross₀ (heq ▸ hx)
          have hx₀ : x₀ < x := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hne)
          have hxmem : x ∈ ({a} : Set ℝ) := by
            rw [← honly]
            exact ⟨hx, ⟨hx₀, hx₁⟩⟩
          exact hxa (by simpa using hxmem)
        · intro hx₀
          linarith
      simp only [g1LeftAssignment, g1CircleWinding, D, plainChain,
        Finset.sum_singleton, Finset.sum_empty]
      simp [hnoinside, hbefore]
  obtain ⟨A, g, hg, hfg, hres⟩ := G1FiniteLedger.circle_isolated_residue
    M hM τ w y a ρ n h ell p m hT hρ hiso
  refine ⟨ρ, A, g, hρ, hρmin, hg, hfg, ?_⟩
  have heq := (same_assignment_integral M hM τ w y n h ell p m hT hs hL
    D (plainChain x₁) hD hplain hassign).2.2
  calc
    g1ChainIntegral (plainChain x₁) (g1RatioKernel M τ w y n h ell p m) =
        g1ChainIntegral D (g1RatioKernel M τ w y n h ell p m) := heq.symm
    _ = g1ChainIntegral (plainChain x₀) (g1RatioKernel M τ w y n h ell p m) +
        FinitePrincipalParts.circleCCW (a : ℂ) ρ (g1RatioKernel M τ w y n h ell p m) := by
      simp [g1ChainIntegral, D, plainChain, G1FiniteLedger.circle_eq_circleCCW]
    _ = _ := by rw [hres]

#check @G1RealConclusion
#check @G1FixedSeparation.noPinch_iff_exists_separatingFamily
#check @G1FixedSeparation.exists_fixedSeparatingFamily
#check @G1FiniteLedger.finite_zero_assignment
#check @G1RatioTail.horizontal_limits
#check @same_assignment_integral
#print contract_chain_clauses
#print upward_shift_residue

end SICLean.L4.G1ChainTransfer
