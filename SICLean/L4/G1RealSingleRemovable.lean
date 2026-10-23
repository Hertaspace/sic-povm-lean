import SICLean.L4.G1RealSingleBoundary
import SICLean.L4.G1RealLoci
import SICLean.L4.G1RealSingleRemovableAux

set_option autoImplicit false

/-!
# Single-function fixed-real-τ removable RHS

The normalized value is the actual fixed-contour integral divided by the existing eta prefactor.
Neither analyticity nor any identity is stored in a definition. The good locus removes the entire
displayed Φ divisor. Its fixed-τ neighborhood filter, including NeBot, is part of the output.

[RW26, p. 7, (22), (23), p. 29]. No G2 identity or finite-Fourier conclusion is imported.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1RealSingleRemovable

/-- Concrete normalization of the integral; no regularity is assumed. -/
def normalizedValue (M : SL(2, ℤ)) (τ₀ δ ψ : ℝ) (n h ell : ℤ)
    (u : ℂ × ℂ) : ℂ :=
  G1Continuation.singleTargetSum M τ₀ δ ψ n h ell u / g1Prefactor M u.1

/-- Fixed-τ spectral function, evaluated at the original real target later. -/
def spectralValue (M : SL(2, ℤ)) (τ₀ δ ψ : ℝ) (n h ell : ℤ) (z : ℂ) : ℂ :=
  normalizedValue M τ₀ δ ψ n h ell ((τ₀ : ℂ), z)

/-- SR01. Normalize the joint analytic integral by the nonzero principal-branch prefactor. [RW26, p.
7, (22), p. 29]. -/
theorem normalized_value_analytic_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      AnalyticOnNhd ℂ (normalizedValue M τ₀ δ ψ n h ell) U := by
  obtain ⟨U, hU, huU, hA, _⟩ :=
    G1RealSingleBoundary.joint_analytic_neighborhood M hM τ₀ w δ ψ n h ell
      hT hs hδ hψ hψ'
  obtain ⟨ρ, hρ, _, hP, hne⟩ :=
    G1RealEtaPhase.real_prefactor_neighborhood M hM τ₀ hT
  refine ⟨U ∩ Prod.fst ⁻¹' Metric.ball (τ₀ : ℂ) ρ,
    hU.inter (Metric.isOpen_ball.preimage continuous_fst),
    ⟨huU, Metric.mem_ball_self hρ⟩, ?_⟩
  intro u hu
  exact (hA u hu.1).div ((hP u.1 hu.2).comp analyticAt_fst) (hne u.1 hu.2)

/-- SR02. Extend the upper/lower off-real comparison to all joint good points. The target need not
be good. Only comparison points are divisor-free. The proof uses modularPhi_joint_unit_neighborhood
for
ordinary joint continuity of the raw expression at each comparison point; fixed-τ continuity alone
does not justify passing from off-real parameters to the real slice. [RW26, p. 7, (22), p. 29]. -/
theorem normalized_value_eq_raw_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      ∀ u ∈ U ∩ G1Continuation.singleGood M h ell,
        normalizedValue M τ₀ δ ψ n h ell u = G1Continuation.singleRaw M h ell u := by
  obtain ⟨U, hU, huU, hA⟩ :=
    normalized_value_analytic_neighborhood M hM τ₀ w δ ψ n h ell
      hT hs hδ hψ hψ'
  obtain ⟨ρ, hρ, _, _hP, hne⟩ :=
    G1RealEtaPhase.real_prefactor_neighborhood M hM τ₀ hT
  have hE := G1RealSingleBoundary.bilateral_rhs_joint_germ M hM τ₀ w δ ψ n h ell
    hT hs hδ hψ hψ'
  obtain ⟨V, hVsub, hV, huV⟩ :=
    mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hE)
  have hB : IsOpen (Prod.fst ⁻¹' Metric.ball (τ₀ : ℂ) ρ : Set (ℂ × ℂ)) :=
    Metric.isOpen_ball.preimage continuous_fst
  have hG := (G1Continuation.single_good_open_dense_fibers M hM h ell).1
  refine ⟨U ∩ V ∩ Prod.fst ⁻¹' Metric.ball (τ₀ : ℂ) ρ,
    (hU.inter hV).inter hB, ⟨⟨huU, huV⟩, Metric.mem_ball_self hρ⟩, ?_⟩
  intro u hu
  apply G1RealSingleRemovableAux.eq_of_offReal_germ
    (hA u hu.1.1.1).continuousAt
    (G1RealSingleRemovableAux.single_raw_continuousAt M hM h ell u hu.2)
  filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hu.1.1.2),
    nhdsWithin_le_nhds (hG.mem_nhds hu.2),
    nhdsWithin_le_nhds (hB.mem_nhds hu.1.2),
    self_mem_nhdsWithin] with v hvV hvG hvB hvim
  change G1Continuation.singleTargetSum M τ₀ δ ψ n h ell v / g1Prefactor M v.1 = _
  rw [hVsub hvV ⟨hvG, hvim⟩]
  exact mul_div_cancel_left₀ _ (hne v.1 hvB)

/-- SR03. Restrict SR02 to the fixed real τ spectral fiber, keeping the full locus. [RW26, p. 7,
(22), p. 29]. -/
theorem fixed_tau_good_identity (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ V : Set ℂ, IsOpen V ∧ (w : ℂ) ∈ V ∧
      ∀ z ∈ V ∩ g1SingleRHSLocus M τ₀ h ell,
        g1SingleRawRHS M τ₀ h ell z = spectralValue M τ₀ δ ψ n h ell z := by
  obtain ⟨U, hU, huU, hEq⟩ :=
    normalized_value_eq_raw_neighborhood M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  refine ⟨(fun z : ℂ => ((τ₀ : ℂ), z)) ⁻¹' U,
    hU.preimage (continuous_const.prodMk continuous_id), huU, ?_⟩
  intro z hz
  exact (hEq ((τ₀ : ℂ), z) ⟨hz.1, hz.2⟩).symm

/-- SR04. The actual normalized integral is an ordinary analytic spectral extension. [RW26, p. 7,
(22), p. 29]. -/
theorem spectral_value_analytic_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ V : Set ℂ, IsOpen V ∧ (w : ℂ) ∈ V ∧
      AnalyticOnNhd ℂ (spectralValue M τ₀ δ ψ n h ell) V := by
  obtain ⟨U, hU, huU, hA⟩ :=
    normalized_value_analytic_neighborhood M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  refine ⟨(fun z : ℂ => ((τ₀ : ℂ), z)) ⁻¹' U,
    hU.preimage (continuous_const.prodMk continuous_id), huU, ?_⟩
  intro z hz
  exact (hA ((τ₀ : ℂ), z) hz).comp (analyticAt_const.prod analyticAt_id)

/-- SR05. Continuity of the extension at the center, before restricting to good points. [RW26, p. 7,
(22), p. 29]. -/
theorem spectral_value_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    Tendsto (spectralValue M τ₀ δ ψ n h ell) (𝓝 (w : ℂ))
      (𝓝 (spectralValue M τ₀ δ ψ n h ell (w : ℂ))) := by
  obtain ⟨V, _hV, hwV, hA⟩ :=
    spectral_value_analytic_neighborhood M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  exact (hA (w : ℂ) hwV).continuousAt

/-- SR06. Finite raw RHS limit along the interface's fixed-τ good-locus filter. No value of total
inversion at the divisor center is used. [RW26, p. 7, (22), p. 29]. -/
theorem raw_tendsto_spectral_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    Tendsto (g1SingleRawRHS M τ₀ h ell)
      (𝓝[g1SingleRHSLocus M τ₀ h ell] (w : ℂ))
      (𝓝 (spectralValue M τ₀ δ ψ n h ell (w : ℂ))) := by
  obtain ⟨V, hV, hwV, hEq⟩ :=
    fixed_tau_good_identity M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  have heq : g1SingleRawRHS M τ₀ h ell =ᶠ[
      𝓝[g1SingleRHSLocus M τ₀ h ell] (w : ℂ)] spectralValue M τ₀ δ ψ n h ell := by
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hwV),
      self_mem_nhdsWithin] with z hzV hzG
    exact hEq z ⟨hzV, hzG⟩
  exact ((spectral_value_tendsto M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').mono_left
    nhdsWithin_le_nhds).congr' heq.symm

/-- SR07. Identify the specified limUnder using SR06 and the nontrivial locus filter. [RW26, p. 7,
(22), p. 29]. -/
theorem rhs_eq_spectral_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    g1SingleRHS M τ₀ w h ell = spectralValue M τ₀ δ ψ n h ell (w : ℂ) := by
  have := G1RealLoci.single_rhs_locus_nhdsWithin_neBot M hM τ₀ h ell hT (w : ℂ)
  exact (raw_tendsto_spectral_value M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').limUnder_eq

/-- SR08. The original removable-value contract, including NeBot and its named limit. [RW26, p. 7,
(22), p. 29]. -/
theorem single_removable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    G1SingleRemovable M τ₀ w h ell := by
  refine ⟨G1RealLoci.single_rhs_locus_nhdsWithin_neBot M hM τ₀ h ell hT (w : ℂ), ?_⟩
  rw [rhs_eq_spectral_value M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ']
  exact raw_tendsto_spectral_value M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'

/-- SR09. Every prescribed bent contour gives the literal contract sum and limUnder RHS. [RW26, p.
7, (22), p. 29]. -/
theorem bent_sum_evaluation (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    (∑ m ∈ Finset.range (M 1 0).toNat,
      g1BentIntegral (g1SingleKernel M τ₀ w n h ell (m : ℤ))
        (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) =
      g1Prefactor M (τ₀ : ℂ) * g1SingleRHS M τ₀ w h ell := by
  change G1Continuation.singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)) = _
  rw [rhs_eq_spectral_value M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ']
  obtain ⟨ρ, hρ, _, _, hne⟩ :=
    G1RealEtaPhase.real_prefactor_neighborhood M hM τ₀ hT
  have hP := hne (τ₀ : ℂ) (Metric.mem_ball_self hρ)
  dsimp only [spectralValue, normalizedValue]
  field_simp [hP]

/-- SR10. Complete single-function clause used by `g1RealConclusion`. Quantification over
n,h,ell,δ,ψ is exactly that of G1RealConclusion. [RW26, p. 7, (22), p. 29]. -/
theorem single_contract_clause (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    G1SingleRemovable M τ₀ w h ell ∧
      (∀ m ∈ Finset.range (M 1 0).toNat,
        G1BentIntegrable (g1SingleKernel M τ₀ w n h ell (m : ℤ))
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) ∧
      (∑ m ∈ Finset.range (M 1 0).toNat,
        g1BentIntegral (g1SingleKernel M τ₀ w n h ell (m : ℤ))
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) =
        g1Prefactor M (τ₀ : ℂ) * g1SingleRHS M τ₀ w h ell := by
  exact ⟨single_removable M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ',
    G1RealSingleBoundary.real_integrable M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ',
    bent_sum_evaluation M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'⟩

#check @G1RealLoci.single_rhs_locus_nhdsWithin_neBot
#check @G1Continuation.single_upper_identity_neighborhood
#check @G1Continuation.lower_half_identification
#check @modularPhi_joint_unit_neighborhood
#check @G1RealEtaPhase.real_prefactor_neighborhood
#check @raw_tendsto_spectral_value
#check @single_contract_clause
#print normalizedValue
#print spectralValue
#print G1SingleRemovable

end SICLean.L4.G1RealSingleRemovable
