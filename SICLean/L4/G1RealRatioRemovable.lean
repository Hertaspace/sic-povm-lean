import SICLean.L4.G1RealRatioBoundary
import SICLean.L4.G1RealLoci
import SICLean.L4.G1RealRatioRemovableAux

set_option autoImplicit false

/-!
# Ratio fixed-real-τ removable RHS

The normalized value is the actual fixed-contour integral divided by the existing eta prefactor.
Neither analyticity nor any identity is stored in a definition. The good locus removes the entire
displayed Φ divisor. Its fixed-τ neighborhood filter, including NeBot, is part of the output.

[RW26, p. 7, (22), (23), p. 29]. No G2 identity or finite-Fourier conclusion is imported.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1RealRatioRemovable

/-- Actual finite-chain sum divided by the existing eta prefactor. -/
def normalizedValue (M : SL(2, ℤ))
    (D : Fin (M 1 0).toNat → G1VerticalChain) (n h ell p : ℤ)
    (x : G1Continuation.Parameters) : ℂ :=
  G1Continuation.ratioTargetSum M D n h ell p x / g1Prefactor M x.1

/-- Fixed-real-τ spectral pair; no value of a displayed quotient is assigned here. -/
def spectralValue (M : SL(2, ℤ)) (τ₀ : ℝ)
    (D : Fin (M 1 0).toNat → G1VerticalChain) (n h ell p : ℤ)
    (v : ℂ × ℂ) : ℂ :=
  normalizedValue M D n h ell p ((τ₀ : ℂ), v)

/-- RR01. Normalize every original separating-chain integral in an ordinary joint chart. [RW26, p.
7, (23), p. 29]. -/
theorem normalized_value_analytic_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set G1Continuation.Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
      AnalyticOnNhd ℂ (normalizedValue M D n h ell p) U := by
  obtain ⟨U, hU, hxU, hsum, _⟩ :=
    G1RealRatioBoundary.joint_analytic_neighborhood M hM τ₀ w y n h ell p hT hs hL D hD
  obtain ⟨ρ, hρ, _, hphase, hphase_ne⟩ :=
    G1RealEtaPhase.real_prefactor_neighborhood M hM τ₀ hT
  refine ⟨U ∩ Prod.fst ⁻¹' Metric.ball (τ₀ : ℂ) ρ,
    hU.inter (Metric.isOpen_ball.preimage continuous_fst),
    ⟨hxU, Metric.mem_ball_self hρ⟩, ?_⟩
  intro x hx
  exact (hsum x hx.1).div ((hphase x.1 hx.2).comp analyticAt_fst)
    (hphase_ne x.1 hx.2)

/-- RR02. Extend off-real comparison to the common unit locus of all three factors. Only comparison
points, never the center, are assumed to be good. The proof uses modularPhi_joint_unit_neighborhood
for
ordinary joint continuity of all three affine Φ factors. Fixed-τ continuity alone cannot identify
the real comparison slice from the off-real germ. [RW26, p. 7, (23), p. 29]. -/
theorem normalized_value_eq_raw_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set G1Continuation.Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
      ∀ x ∈ U ∩ G1Continuation.ratioGood M h ell p,
        normalizedValue M D n h ell p x = G1Continuation.ratioRaw M h ell p x := by
  obtain ⟨A, hA, hxA, han⟩ :=
    normalized_value_analytic_neighborhood M hM τ₀ w y n h ell p hT hs hL D hD
  obtain ⟨ρ, hρ, _, _, hphase_ne⟩ :=
    G1RealEtaPhase.real_prefactor_neighborhood M hM τ₀ hT
  obtain ⟨B, hB, hxB, heq⟩ := mem_nhdsWithin.mp
    (G1RealRatioBoundary.bilateral_rhs_joint_germ M hM τ₀ w y n h ell p hT hs hL D hD)
  let U : Set G1Continuation.Parameters :=
    (A ∩ B) ∩ Prod.fst ⁻¹' Metric.ball (τ₀ : ℂ) ρ
  have hU : IsOpen U := (hA.inter hB).inter (Metric.isOpen_ball.preimage continuous_fst)
  have hoff : ∀ x ∈ U ∩ G1Continuation.ratioGood M h ell p, x.1.im ≠ 0 →
      normalizedValue M D n h ell p x = G1Continuation.ratioRaw M h ell p x := by
    intro x hx him
    change G1Continuation.ratioTargetSum M D n h ell p x / g1Prefactor M x.1 = _
    rw [heq ⟨hx.1.1.2, hx.2, him⟩]
    exact mul_div_cancel_left₀ _ (hphase_ne x.1 hx.1.2)
  refine ⟨U, hU, ⟨⟨hxA, hxB⟩, Metric.mem_ball_self hρ⟩, ?_⟩
  intro x hx
  by_cases him : x.1.im = 0
  · exact G1RealRatioRemovableAux.eq_of_off_real _ _ _
      (hU.inter (G1Continuation.ratio_good_open_dense_fibers M hM h ell p).1) x hx him
      (han x hx.1.1.1).continuousAt
      (G1RealRatioRemovableAux.ratioRaw_continuousAt M hM h ell p x hx.2) hoff
  · exact hoff x hx him

/-- RR03. With τ fixed, the full analytic divisor in ℂ² is excluded, not one point. [RW26, p. 7,
(23), p. 29]. -/
theorem fixed_tau_good_identity (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ ((w : ℂ), (y : ℂ)) ∈ V ∧
      ∀ v ∈ V ∩ g1RatioRHSLocus M τ₀ h ell p,
        g1RatioRawRHS M τ₀ h ell p v = spectralValue M τ₀ D n h ell p v := by
  obtain ⟨U, hU, hxU, heq⟩ :=
    normalized_value_eq_raw_neighborhood M hM τ₀ w y n h ell p hT hs hL D hD
  refine ⟨(fun v : ℂ × ℂ => ((τ₀ : ℂ), v)) ⁻¹' U,
    hU.preimage (continuous_const.prodMk continuous_id), hxU, ?_⟩
  intro v hv
  exact (heq ((τ₀ : ℂ), v) ⟨hv.1, hv.2⟩).symm

/-- RR04. An ordinary analytic extension on the full spectral pair neighborhood. [RW26, p. 7, (23),
p. 29]. -/
theorem spectral_value_analytic_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ ((w : ℂ), (y : ℂ)) ∈ V ∧
      AnalyticOnNhd ℂ (spectralValue M τ₀ D n h ell p) V := by
  obtain ⟨U, hU, hxU, han⟩ :=
    normalized_value_analytic_neighborhood M hM τ₀ w y n h ell p hT hs hL D hD
  refine ⟨(fun v : ℂ × ℂ => ((τ₀ : ℂ), v)) ⁻¹' U,
    hU.preimage (continuous_const.prodMk continuous_id), hxU, ?_⟩
  intro v hv
  exact (han ((τ₀ : ℂ), v) hv).comp (analyticAt_const.prod analyticAt_id)

/-- RR05. The finite center value follows from ordinary spectral continuity. [RW26, p. 7, (23), p.
29]. -/
theorem spectral_value_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    Tendsto (spectralValue M τ₀ D n h ell p) (𝓝 ((w : ℂ), (y : ℂ)))
      (𝓝 (spectralValue M τ₀ D n h ell p ((w : ℂ), (y : ℂ)))) := by
  obtain ⟨V, _, hxV, han⟩ :=
    spectral_value_analytic_neighborhood M hM τ₀ w y n h ell p hT hs hL D hD
  exact (han _ hxV).continuousAt.tendsto

/-- RR06. Finite raw RHS limit on the contract's full fixed-τ good locus. This is stronger than a
limit along a single chosen spectral path. [RW26, p. 7, (23), p. 29]. -/
theorem raw_tendsto_spectral_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    Tendsto (g1RatioRawRHS M τ₀ h ell p)
      (𝓝[g1RatioRHSLocus M τ₀ h ell p] ((w : ℂ), (y : ℂ)))
      (𝓝 (spectralValue M τ₀ D n h ell p ((w : ℂ), (y : ℂ)))) := by
  obtain ⟨V, hV, hxV, heq⟩ :=
    fixed_tau_good_identity M hM τ₀ w y n h ell p hT hs hL D hD
  apply (spectral_value_tendsto M hM τ₀ w y n h ell p hT hs hL D hD).mono_left
    nhdsWithin_le_nhds |>.congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV),
    self_mem_nhdsWithin] with v hv hgood
  exact (heq v ⟨hv, hgood⟩).symm

/-- RR07. The contract's limUnder is this finite value; NeBot is supplied by fixed-τ density. [RW26,
p. 7, (23), p. 29]. -/
theorem rhs_eq_spectral_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    g1RatioRHS M τ₀ w y h ell p = spectralValue M τ₀ D n h ell p ((w : ℂ), (y : ℂ)) := by
  have := G1RealLoci.ratio_rhs_locus_nhdsWithin_neBot M hM τ₀ h ell p hT
    ((w : ℂ), (y : ℂ))
  exact (raw_tendsto_spectral_value M hM τ₀ w y n h ell p hT hs hL D hD).limUnder_eq

/-- RR08. The original ratio removable-value contract, including NeBot and the named limit. [RW26,
p. 7, (23), p. 29]. -/
theorem ratio_removable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    G1RatioRemovable M τ₀ w y h ell p := by
  refine ⟨G1RealLoci.ratio_rhs_locus_nhdsWithin_neBot M hM τ₀ h ell p hT _, ?_⟩
  rw [rhs_eq_spectral_value M hM τ₀ w y n h ell p hT hs hL D hD]
  exact raw_tendsto_spectral_value M hM τ₀ w y n h ell p hT hs hL D hD

/-- RR09. Every given separating representative evaluates to the exact contract RHS. [RW26, p. 7,
(23), p. 29]. -/
theorem separating_sum_evaluation (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    (∑ m : Fin (M 1 0).toNat,
      g1ChainIntegral (D m) (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))) =
        g1Prefactor M (τ₀ : ℂ) * g1RatioRHS M τ₀ w y h ell p := by
  rw [rhs_eq_spectral_value M hM τ₀ w y n h ell p hT hs hL D hD]
  have hphase := G1RealEtaPhase.prefactor_ne_zero M hM (τ₀ : ℂ)
    (G1RealEtaPhase.real_positive_domain_and_nonzero M τ₀ hT).1
  change G1Continuation.ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) =
    g1Prefactor M (τ₀ : ℂ) *
      (G1Continuation.ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) /
        g1Prefactor M (τ₀ : ℂ))
  exact (mul_div_cancel₀ _ hphase).symm

/-- RR10. Existence and all representatives, via contract_chain_clauses. A genuine no-pinch
assumption is used here to obtain the original chains. [RW26, p. 7, (23), p. 29]. -/
theorem ratio_contract_clause (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (hpinch : g1NoPinch M τ₀ y p) :
    G1RatioRemovable M τ₀ w y h ell p ∧
      (∃ D : Fin (M 1 0).toNat → G1VerticalChain,
        ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
          (g1InversePoles M τ₀ y n p (m : ℤ))) ∧
      (∀ D : Fin (M 1 0).toNat → G1VerticalChain,
        (∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
          (g1InversePoles M τ₀ y n p (m : ℤ))) →
        (∀ m, G1ChainIntegrable (D m) (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))) ∧
        (∑ m : Fin (M 1 0).toNat,
          g1ChainIntegral (D m) (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))) =
            g1Prefactor M (τ₀ : ℂ) * g1RatioRHS M τ₀ w y h ell p) := by
  obtain ⟨D₀, hD₀, hall⟩ :=
    G1ChainTransfer.contract_chain_clauses M hM τ₀ w y n h ell p hT hs hL hpinch
  refine ⟨ratio_removable M hM τ₀ w y n h ell p hT hs hL D₀ hD₀,
    ⟨D₀, hD₀⟩, ?_⟩
  intro D hD
  exact ⟨(hall D hD).1,
    separating_sum_evaluation M hM τ₀ w y n h ell p hT hs hL D hD⟩

#check @G1RealLoci.ratio_rhs_locus_nhdsWithin_neBot
#check @G1Continuation.ratio_upper_identity_neighborhood
#check @G1Continuation.lower_half_identification
#check @modularPhi_joint_unit_neighborhood
#check @G1ChainTransfer.contract_chain_clauses
#check @raw_tendsto_spectral_value
#check @ratio_contract_clause
#print normalizedValue
#print spectralValue
#print G1RatioRemovable

end SICLean.L4.G1RealRatioRemovable
