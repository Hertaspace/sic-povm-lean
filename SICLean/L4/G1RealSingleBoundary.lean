import SICLean.L4.G1ContinuationBoundary
import SICLean.L4.G1RealEtaPhase
import SICLean.L4.G1RealSingleBoundaryAux

set_option autoImplicit false

/-!
# Single-function ordinary real-boundary limits from both sides

Boundary-limit and comparison theorems. The common value is always the existing
G1Continuation target sum. No normalized-value definition, fixed-real-τ good-locus identity,
G1SingleRemovable/G1RatioRemovable assumption, or G2 input is introduced.

The τ-only limit exports specialize the proved bilateral tail limits. The joint ordinary limits use
B04--B07. Upper/lower RHS comparison uses B08/B09 and B13 with the exact η phase. The final
bilateral locus deletes the entire displayed Φ divisor and also excludes Im τ = 0; its NeBot claim
is joint in all complex variables, never on a fixed-spectral τ slice. Fixed-real-τ removable values
are proved in `G1RealSingleRemovable`.

[RW26, p. 7, p. 29]. Two-sided limits in τ are formalized here.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1RealSingleBoundary

open G1Continuation

/-- SB01. Real absolute integrability for every contract component, with the actual bent lower tail.
Specialize bilateral integrability using the real-kernel bridge. [RW26, p. 7, (22)]. -/
theorem real_integrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∀ m ∈ Finset.range (M 1 0).toNat,
      G1BentIntegrable (g1SingleKernel M τ₀ w n h ell (m : ℤ))
        (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ := by
  obtain ⟨ρ, hρ, hint⟩ := G1BilateralSingleTails.bent_integrable_full_disk M hM
    ((Finset.range (M 1 0).toNat).image Int.ofNat)
    τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  intro m hm
  simpa only [G1BilateralGeometry.singleKernel_real] using
    hint (τ₀ : ℂ) (Metric.mem_closedBall_self hρ.le) (m : ℤ)
      (Finset.mem_image_of_mem _ hm)

/-- SB02. Fixed real w: ordinary full-τ-neighborhood limit of the exact target sum. It reuses
`summed_bent_integral_limits`, J01 and B12. [RW26, p. 7, (22)]. -/
theorem tau_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    Tendsto (fun τ : ℂ => singleTargetSum M τ₀ δ ψ n h ell (τ, (w : ℂ)))
      (𝓝 (τ₀ : ℂ)) (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)))) := by
  simpa only [singleTargetSum, G1RealSingleBoundaryAux.single_kernel_eq,
    G1BilateralGeometry.singleKernel_real] using
    (G1BilateralSingleTails.summed_bent_integral_limits M hM τ₀ w δ ψ n h ell
      hT hs hδ hψ hψ').1

/-- SB03. Fixed real w: upper-half integral limit, with no RHS-locus condition. It restricts the
existing summed ordinary limit. [RW26, p. 7, (22)]. -/
theorem tau_upper_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    Tendsto (fun τ : ℂ => singleTargetSum M τ₀ δ ψ n h ell (τ, (w : ℂ)))
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)))) := by
  exact (tau_tendsto M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').mono_left
    nhdsWithin_le_nhds

/-- SB04. Fixed real w: lower-half integral limit to the same actual real integral. It restricts the
existing summed ordinary limit. [RW26, p. 7, (22)]. -/
theorem tau_lower_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    Tendsto (fun τ : ℂ => singleTargetSum M τ₀ δ ψ n h ell (τ, (w : ℂ)))
      (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ))
      (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)))) := by
  exact (tau_tendsto M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').mono_left
    nhdsWithin_le_nhds

/-- SB05. Moving complex τ,w: a full ordinary open analytic and integrable chart. It follows from
B04/B06; no regularity is assumed of the RHS at the target. [RW26, p. 7, p. 29]. -/
theorem joint_analytic_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      AnalyticOnNhd ℂ (singleTargetSum M τ₀ δ ψ n h ell) U ∧
      ∀ u ∈ U, ∀ m ∈ Finset.range (M 1 0).toNat,
        G1BentIntegrable (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ := by
  exact real_single_joint_analytic M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'

/-- SB06. Moving complex τ,w: ordinary-neighborhood continuity of the target sum. It follows from
the analyticity in B06. [RW26, p. 7, p. 29]. -/
theorem joint_continuous_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      ContinuousOn (singleTargetSum M τ₀ δ ψ n h ell) U := by
  obtain ⟨U, hU, hmem, ha, _⟩ :=
    joint_analytic_neighborhood M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  exact ⟨U, hU, hmem, ha.continuousOn⟩

/-- SB07. Joint ordinary limit allows the spectral variable to move through its target. It follows
from B06, without a good-locus hypothesis. [RW26, p. 7, p. 29]. -/
theorem joint_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    Tendsto (singleTargetSum M τ₀ δ ψ n h ell) (𝓝 ((τ₀ : ℂ), (w : ℂ)))
      (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)))) := by
  obtain ⟨U, _, hmem, ha, _⟩ :=
    joint_analytic_neighborhood M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  exact (ha _ hmem).continuousAt.tendsto

/-- SB08. Upper joint integral limit for simultaneously moving complex τ,w. It restricts
the joint ordinary limit. [RW26, p. 7, p. 29]. -/
theorem joint_upper_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    Tendsto (singleTargetSum M τ₀ δ ψ n h ell)
      (𝓝[{u : ℂ × ℂ | 0 < u.1.im}] ((τ₀ : ℂ), (w : ℂ)))
      (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)))) := by
  exact (joint_tendsto M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').mono_left
    nhdsWithin_le_nhds

/-- SB09. Lower joint integral limit for simultaneously moving complex τ,w. It restricts
the joint ordinary limit. [RW26, p. 7, p. 29]. -/
theorem joint_lower_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    Tendsto (singleTargetSum M τ₀ δ ψ n h ell)
      (𝓝[{u : ℂ × ℂ | u.1.im < 0}] ((τ₀ : ℂ), (w : ℂ)))
      (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)))) := by
  exact (joint_tendsto M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').mono_left
    nhdsWithin_le_nhds

/-- SB10. Upper good-locus ordinary joint germ with the exact η-free prefactor. It combines B08/B10
and the upper η-prefactor bridge. [RW26, p. 7, (22), p. 29]. -/
theorem upper_rhs_joint_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    singleTargetSum M τ₀ δ ψ n h ell =ᶠ[
      𝓝[upperSingleGood M h ell] ((τ₀ : ℂ), (w : ℂ))]
      (fun u : ℂ × ℂ => g1Prefactor M u.1 * singleRaw M h ell u) := by
  obtain ⟨U, hU, hmem, hid⟩ :=
    single_upper_identity_neighborhood M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hmem),
    self_mem_nhdsWithin] with u hu hgood
  rw [hid u ⟨hu, hgood⟩,
    G1RealEtaPhase.upper_prefactor_eq_g1Prefactor M hM u.1 hgood.1]

/-- SB11. Lower good-locus ordinary joint germ with the same η-free prefactor. It restricts B13; no
q product is evaluated below the axis. [RW26, p. 7, p. 29]. -/
theorem lower_rhs_joint_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    singleTargetSum M τ₀ δ ψ n h ell =ᶠ[
      𝓝[{u : ℂ × ℂ | u ∈ singleGood M h ell ∧ u.1.im < 0}] ((τ₀ : ℂ), (w : ℂ))]
      (fun u : ℂ × ℂ => g1Prefactor M u.1 * singleRaw M h ell u) := by
  obtain ⟨U, hU, hmem, hid⟩ :=
    (lower_half_identification M hM τ₀ hT).1 n h ell w δ ψ hs hδ hψ hψ'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hmem),
    self_mem_nhdsWithin] with u hu hgood
  exact hid u ⟨hu, hgood.1⟩ hgood.2

/-- SB12. Bilateral off-real good-locus germ, deleting the complete Φ divisor. The proof intersects
the ordinary B08/B13 neighborhoods before splitting on the sign of Im τ. Fixed-real-τ
comparison remains downstream. [RW26, p. 7, p. 29]. -/
theorem bilateral_rhs_joint_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    singleTargetSum M τ₀ δ ψ n h ell =ᶠ[
      𝓝[{u : ℂ × ℂ | u ∈ singleGood M h ell ∧ u.1.im ≠ 0}] ((τ₀ : ℂ), (w : ℂ))]
      (fun u : ℂ × ℂ => g1Prefactor M u.1 * singleRaw M h ell u) := by
  have hup := upper_rhs_joint_germ M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  have hdown := lower_rhs_joint_germ M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hup hdown ⊢
  filter_upwards [hup, hdown] with u hu hd hgood
  rcases lt_or_gt_of_ne hgood.2 with hneg | hpos
  · exact hd ⟨hgood.1, hneg⟩
  · exact hu ⟨hpos, hgood.1⟩

/-- SB13. Each joint one-sided RHS filter is nontrivial and has the same finite integral limit. Core
check: lower-side nontriviality uses moving spectral parameters and the entire good locus; it is
never a fixed-w τ-slice claim. [RW26, p. 7, p. 29]. -/
theorem rhs_one_sided_joint_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    (NeBot (𝓝[upperSingleGood M h ell] ((τ₀ : ℂ), (w : ℂ))) ∧
      Tendsto (fun u : ℂ × ℂ => g1Prefactor M u.1 * singleRaw M h ell u)
        (𝓝[upperSingleGood M h ell] ((τ₀ : ℂ), (w : ℂ)))
        (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ))))) ∧
    (NeBot (𝓝[{u : ℂ × ℂ | u ∈ singleGood M h ell ∧ u.1.im < 0}] ((τ₀ : ℂ), (w : ℂ))) ∧
      Tendsto (fun u : ℂ × ℂ => g1Prefactor M u.1 * singleRaw M h ell u)
        (𝓝[{u : ℂ × ℂ | u ∈ singleGood M h ell ∧ u.1.im < 0}] ((τ₀ : ℂ), (w : ℂ)))
        (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ))))) := by
  constructor
  · refine ⟨(single_upper_joint_germ_neBot M hM τ₀ w δ ψ n h ell
      hT hs hδ hψ hψ').1, ?_⟩
    exact ((joint_tendsto M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').mono_left
      nhdsWithin_le_nhds).congr'
        (upper_rhs_joint_germ M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ')
  · refine ⟨G1RealSingleBoundaryAux.lower_good_nhdsWithin_neBot M hM τ₀ w h ell hT, ?_⟩
    exact ((joint_lower_tendsto M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').mono_left
      (nhdsWithin_mono _ (fun _ hu => hu.2))).congr'
        (lower_rhs_joint_germ M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ')

/-- SB14. Bilateral off-real RHS limit with explicit nontriviality. This is a joint limit to the
actual target sum, not a fixed-real-τ removable value. It combines the joint ordinary limit and
both good-locus germs. [RW26, p. 7, p. 29]. -/
theorem rhs_bilateral_joint_limit (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    NeBot (𝓝[{u : ℂ × ℂ | u ∈ singleGood M h ell ∧ u.1.im ≠ 0}] ((τ₀ : ℂ), (w : ℂ))) ∧
      Tendsto (fun u : ℂ × ℂ => g1Prefactor M u.1 * singleRaw M h ell u)
        (𝓝[{u : ℂ × ℂ | u ∈ singleGood M h ell ∧ u.1.im ≠ 0}] ((τ₀ : ℂ), (w : ℂ)))
        (𝓝 (singleTargetSum M τ₀ δ ψ n h ell ((τ₀ : ℂ), (w : ℂ)))) := by
  refine ⟨?_, ?_⟩
  · exact ((single_upper_joint_germ_neBot M hM τ₀ w δ ψ n h ell
      hT hs hδ hψ hψ').1).mono
        (nhdsWithin_mono _ (fun _ hu => ⟨hu.2, ne_of_gt hu.1⟩))
  · exact ((joint_tendsto M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ').mono_left
      nhdsWithin_le_nhds).congr'
        (bilateral_rhs_joint_germ M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ')

#check @G1BilateralSingleTails.summed_bent_integral_limits
#check @G1Continuation.real_single_joint_analytic
#check @G1Continuation.lower_half_identification
#check @SICLean.L4.G1RealEtaPhase.upper_prefactor_eq_g1Prefactor
#print joint_analytic_neighborhood
#print bilateral_rhs_joint_germ
#print rhs_bilateral_joint_limit

end SICLean.L4.G1RealSingleBoundary
