import SICLean.L4.G1ContinuationBoundary
import SICLean.L4.G1RealEtaPhase
import SICLean.L4.G1RealRatioBoundaryAux

set_option autoImplicit false

/-!
# Ratio ordinary real-boundary limits from both sides

Ordinary and one-sided limit statements. The common value is always the existing
G1Continuation target sum. No normalized-value definition, fixed-real-τ good-locus identity,
G1SingleRemovable/G1RatioRemovable assumption, or G2 input is introduced.

The τ-only limit exports specialize the proved bilateral tail limits. The joint ordinary limits use
B04--B07. Upper/lower RHS comparison uses B08/B09 and B13 with the exact η phase. The final
bilateral locus deletes the entire displayed Φ divisor and also excludes Im τ = 0; its NeBot claim
is joint in all complex variables, never on a fixed-spectral τ slice. Fixed-real-τ removable values
are proved in `G1RealSingleRemovable` and `G1RealRatioRemovable`.

[RW26, p. 7, p. 29]. Two-sided limits in τ are formalized here.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1RealRatioBoundary

open G1Continuation

/-- RB01. Real absolute integrability for every component of any prescribed given separating family.
Specialize the bilateral integrable tube and real-kernel bridge. [RW26, p. 7, (23)]. -/
theorem real_integrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∀ m : Fin (M 1 0).toNat,
      G1ChainIntegrable (D m) (g1RatioKernel M τ₀ w y n h ell p (m : ℤ)) := by
  obtain ⟨ρ, hρ, hInt⟩ :=
    G1BilateralRatioTails.family_chain_integrable M hM τ₀ w y n h ell p hT hs hL D hD
  have hc : (τ₀ : ℂ) ∈ ModularSector.parameterDisk τ₀ ρ :=
    Metric.mem_closedBall_self hρ.le
  intro m
  simpa only [G1RatioTail.complexKernel_real] using hInt _ hc m

/-- RB02. Fixed real w,y: ordinary full-τ-neighborhood limit of the exact Fin sum. It reuses
`summed_chain_integral_limits`, J01 and B12. [RW26, p. 7, (23)]. -/
theorem tau_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    Tendsto (fun τ : ℂ => ratioTargetSum M D n h ell p (τ, (w : ℂ), (y : ℂ)))
      (𝓝 (τ₀ : ℂ)) (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))) := by
  exact (G1BilateralRatioTails.summed_chain_integral_limits
    M hM τ₀ w y n h ell p hT hs hL D hD).1

/-- RB03. Fixed real w,y: upper-half integral limit for every given separating family. It restricts
the existing summed ordinary limit. [RW26, p. 7, (23)]. -/
theorem tau_upper_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    Tendsto (fun τ : ℂ => ratioTargetSum M D n h ell p (τ, (w : ℂ), (y : ℂ)))
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))) := by
  exact (tau_tendsto M hM τ₀ w y n h ell p hT hs hL D hD).mono_left
    nhdsWithin_le_nhds

/-- RB04. Fixed real w,y: lower-half integral limit to the same actual real sum. It restricts the
existing summed ordinary limit. [RW26, p. 7, (23)]. -/
theorem tau_lower_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    Tendsto (fun τ : ℂ => ratioTargetSum M D n h ell p (τ, (w : ℂ), (y : ℂ)))
      (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ))
      (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))) := by
  exact (tau_tendsto M hM τ₀ w y n h ell p hT hs hL D hD).mono_left
    nhdsWithin_le_nhds

/-- RB05. Moving complex τ,w,y: full ordinary open analytic and integrable chart for the same
original chains. It follows from B05/B07, including circles. [RW26, p. 7, p. 29]. -/
theorem joint_analytic_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
      AnalyticOnNhd ℂ (ratioTargetSum M D n h ell p) U ∧
      ∀ x ∈ U, ∀ m : Fin (M 1 0).toNat,
        G1ChainIntegrable (D m)
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2) := by
  exact real_ratio_joint_analytic M hM τ₀ w y n h ell p hT hs hL D hD

/-- RB06. Moving complex τ,w,y: ordinary-neighborhood continuity of the chain sum. It follows from
the analyticity in B07. [RW26, p. 7, p. 29]. -/
theorem joint_continuous_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
      ContinuousOn (ratioTargetSum M D n h ell p) U := by
  obtain ⟨U, hU, hc, ha, _⟩ :=
    joint_analytic_neighborhood M hM τ₀ w y n h ell p hT hs hL D hD
  exact ⟨U, hU, hc, ha.continuousOn⟩

/-- RB07. Joint ordinary integral limit with both spectral variables moving. It follows from
B07, including targets on apparent RHS divisors. [RW26, p. 7, p. 29]. -/
theorem joint_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    Tendsto (ratioTargetSum M D n h ell p) (𝓝 ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))
      (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))) := by
  obtain ⟨U, hU, hc, ha, _⟩ :=
    joint_analytic_neighborhood M hM τ₀ w y n h ell p hT hs hL D hD
  exact (ha _ hc).continuousAt.tendsto

/-- RB08. Upper joint integral limit for simultaneously moving complex τ,w,y. It restricts
the joint ordinary limit. [RW26, p. 7, p. 29]. -/
theorem joint_upper_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    Tendsto (ratioTargetSum M D n h ell p)
      (𝓝[{x : Parameters | 0 < x.1.im}] ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))
      (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))) := by
  exact (joint_tendsto M hM τ₀ w y n h ell p hT hs hL D hD).mono_left
    nhdsWithin_le_nhds

/-- RB09. Lower joint integral limit for simultaneously moving complex τ,w,y. It restricts
the joint ordinary limit. [RW26, p. 7, p. 29]. -/
theorem joint_lower_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    Tendsto (ratioTargetSum M D n h ell p)
      (𝓝[{x : Parameters | x.1.im < 0}] ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))
      (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))) := by
  exact (joint_tendsto M hM τ₀ w y n h ell p hT hs hL D hD).mono_left
    nhdsWithin_le_nhds

/-- RB10. Upper good-locus ordinary joint germ with the exact η-free prefactor. It combines B09/B11
and the upper η-prefactor bridge. [RW26, p. 7, (23), p. 29]. -/
theorem upper_rhs_joint_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ratioTargetSum M D n h ell p =ᶠ[
      𝓝[upperRatioGood M h ell p] ((τ₀ : ℂ), (w : ℂ), (y : ℂ))]
      (fun x : Parameters => g1Prefactor M x.1 * ratioRaw M h ell p x) := by
  have heq := (ratio_upper_joint_germ_neBot M hM τ₀ w y n h ell p hT hs hL D hD).2
  filter_upwards [heq, self_mem_nhdsWithin] with x hx hgood
  simpa only [G1RealEtaPhase.upper_prefactor_eq_g1Prefactor M hM x.1 hgood.1] using hx

/-- RB11. Lower good-locus ordinary joint germ for the same given separating family. It restricts
B13; uses the η-free prefactor, not lower q products. [RW26, p. 7, p. 29]. -/
theorem lower_rhs_joint_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ratioTargetSum M D n h ell p =ᶠ[
      𝓝[{x : Parameters | x ∈ ratioGood M h ell p ∧ x.1.im < 0}] ((τ₀ : ℂ), (w : ℂ), (y : ℂ))]
      (fun x : Parameters => g1Prefactor M x.1 * ratioRaw M h ell p x) := by
  obtain ⟨U, hU, hc, heq⟩ :=
    (lower_half_identification M hM τ₀ hT).2 n h ell p w y hs hL D hD
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hc),
    self_mem_nhdsWithin] with x hx hgood
  exact heq x ⟨hx, hgood.1⟩ hgood.2

/-- RB12. Bilateral off-real good-locus germ deletes all three displayed Φ divisors. The proof
intersects B09/B13 neighborhoods before the sign split. The target need not be good; fixed-real-τ
spectral comparison is downstream. [RW26, p. 7, p. 29]. -/
theorem bilateral_rhs_joint_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ratioTargetSum M D n h ell p =ᶠ[
      𝓝[{x : Parameters | x ∈ ratioGood M h ell p ∧ x.1.im ≠ 0}] ((τ₀ : ℂ), (w : ℂ), (y : ℂ))]
      (fun x : Parameters => g1Prefactor M x.1 * ratioRaw M h ell p x) := by
  have hu := upper_rhs_joint_germ M hM τ₀ w y n h ell p hT hs hL D hD
  have hl := lower_rhs_joint_germ M hM τ₀ w y n h ell p hT hs hL D hD
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hu hl ⊢
  filter_upwards [hu, hl] with x hxu hxl hx
  rcases lt_or_gt_of_ne hx.2 with hneg | hpos
  · exact hxl ⟨hx.1, hneg⟩
  · exact hxu ⟨hpos, hx.1⟩

/-- RB13. Both joint one-sided RHS filters are nontrivial and have the same finite integral limit.
The proof uses moving complex w,y and the full three-factor good locus. No nontrivial fixed-w,y
τ-filter is asserted. [RW26, p. 7, p. 29]. -/
theorem rhs_one_sided_joint_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    (NeBot (𝓝[upperRatioGood M h ell p] ((τ₀ : ℂ), (w : ℂ), (y : ℂ))) ∧
      Tendsto (fun x : Parameters => g1Prefactor M x.1 * ratioRaw M h ell p x)
        (𝓝[upperRatioGood M h ell p] ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))
        (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ))))) ∧
    (NeBot (𝓝[{x : Parameters | x ∈ ratioGood M h ell p ∧ x.1.im < 0}] ((τ₀ : ℂ), (w : ℂ), (y : ℂ))) ∧
      Tendsto (fun x : Parameters => g1Prefactor M x.1 * ratioRaw M h ell p x)
        (𝓝[{x : Parameters | x ∈ ratioGood M h ell p ∧ x.1.im < 0}] ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))
        (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ))))) := by
  have ht := joint_tendsto M hM τ₀ w y n h ell p hT hs hL D hD
  refine ⟨⟨(ratio_upper_joint_germ_neBot
    M hM τ₀ w y n h ell p hT hs hL D hD).1, ?_⟩,
    ⟨G1RealRatioBoundaryAux.ratio_lower_joint_neBot M hM τ₀ w y h ell p hT, ?_⟩⟩
  · exact (ht.mono_left nhdsWithin_le_nhds).congr'
      (upper_rhs_joint_germ M hM τ₀ w y n h ell p hT hs hL D hD)
  · exact (ht.mono_left nhdsWithin_le_nhds).congr'
      (lower_rhs_joint_germ M hM τ₀ w y n h ell p hT hs hL D hD)

/-- RB14. Bilateral off-real RHS limit with explicit joint-filter nontriviality. It combines
B07, the upper η bridge and B13. The value is the actual target sum of the original chain, with no
fixed-real-τ
removable value presupposed. [RW26, p. 7, p. 29]. -/
theorem rhs_bilateral_joint_limit (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    NeBot (𝓝[{x : Parameters | x ∈ ratioGood M h ell p ∧ x.1.im ≠ 0}] ((τ₀ : ℂ), (w : ℂ), (y : ℂ))) ∧
      Tendsto (fun x : Parameters => g1Prefactor M x.1 * ratioRaw M h ell p x)
        (𝓝[{x : Parameters | x ∈ ratioGood M h ell p ∧ x.1.im ≠ 0}] ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))
        (𝓝 (ratioTargetSum M D n h ell p ((τ₀ : ℂ), (w : ℂ), (y : ℂ)))) := by
  have hn := (ratio_upper_joint_germ_neBot
    M hM τ₀ w y n h ell p hT hs hL D hD).1
  refine ⟨hn.mono (nhdsWithin_mono _ ?_), ?_⟩
  · intro x hx
    exact ⟨hx.2, ne_of_gt hx.1⟩
  · exact ((joint_tendsto M hM τ₀ w y n h ell p hT hs hL D hD).mono_left
      nhdsWithin_le_nhds).congr'
        (bilateral_rhs_joint_germ M hM τ₀ w y n h ell p hT hs hL D hD)

#check @G1BilateralRatioTails.summed_chain_integral_limits
#check @G1Continuation.real_ratio_joint_analytic
#check @G1Continuation.lower_half_identification
#check @SICLean.L4.G1RealEtaPhase.upper_prefactor_eq_g1Prefactor
#print joint_analytic_neighborhood
#print bilateral_rhs_joint_germ
#print rhs_bilateral_joint_limit

end SICLean.L4.G1RealRatioBoundary
