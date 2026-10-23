import SICLean.L4.G1ContinuationHolomorphy
import SICLean.L4.G1ContinuationEndRotation
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1ContinuationStrictAux

open G1Continuation

/-- The actual three-factor quotient, with no choice of divisor values. -/
def ratioExpression (M : SL(2, ℤ)) (h ell p : ℤ) (x : Parameters) : ℂ :=
  modularPhi M (p + ell) (-h) (x.2.1 + x.2.2) x.1 /
    (modularPhi M p 0 x.2.2 x.1 * modularPhi M ell (1 - h) x.2.1 x.1)

theorem ratio_seed_mem_tube (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) :
    x ∈ ratioTube M n h ell p ψ := by
  exact ⟨hx.1,
    (initial_fibers_inside_target M n h ell p ψ σ ρ δ hc x.1 hx.1).2.2.2 x.2 hx⟩

/-- Both contour rotations give a comparison on an ordinary joint neighborhood. The fixed
representative remains separating throughout that neighborhood. -/
theorem ratio_rotated_seed_germ (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) :
    ∃ D : Fin (M 1 0).toNat → CircleExtension,
      (∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) ∧
      ratioExtensionSum M D n h ell p =ᶠ[𝓝 x]
        (fun v => UpperResidueParameters.prefactor M v.1 * ratioExpression M h ell p v) := by
  obtain ⟨D, hD, _⟩ := ratio_seed_end_rotation M n h ell p ψ σ ρ δ hc x hx
  obtain ⟨U, hU, hxU, hsub, _, hsep⟩ :=
    ratio_extension_joint_analytic M hc.1 n h ell p ψ hc.2.1 hc.2.2.1 x
      (ratio_seed_mem_tube M n h ell p ψ σ ρ δ hc x hx) D hD
  refine ⟨D, hD, ?_⟩
  filter_upwards [hU.mem_nhds hxU,
    (UpperWindow.domain_isOpen M h ell p ψ σ ρ δ hc).mem_nhds hx] with v hv hvseed
  obtain ⟨E, hE, hval⟩ := ratio_seed_end_rotation M n h ell p ψ σ ρ δ hc v hvseed
  exact ((complex_same_assignment_integral M hc.1 n h ell p ψ hc.2.1 hc.2.2.1 v
    (hsub hv) D E (hsep v hv) hE).2.trans hval).trans
      (UpperIntegralIdentities.upper_ratio M n h ell p ψ σ ρ δ hc v hvseed).2

/-- A polygon inside the deleted window is an ordinary path in that window. -/
theorem polygon_joinedIn (P : Polygon) (Ω : Set (ℂ × ℂ)) (v₀ v₁ : ℂ × ℂ)
    (hv₀ : v₀ ∈ Ω) (hP : PolygonIn P Ω v₀ v₁) : JoinedIn Ω v₀ v₁ := by
  have hstep : ∀ i : Fin P.length,
      JoinedIn Ω (P.vertex i.castSucc) (P.vertex i.succ) := by
    intro i
    apply JoinedIn.ofLine (f := polygonPoint P i)
    · unfold polygonPoint
      fun_prop
    · simp [polygonPoint]
    · simp [polygonPoint]
    · rintro _ ⟨t, ht, rfl⟩
      exact hP.2.2.2 i t ht
  have hroute : ∀ i : Fin (P.length + 1),
      JoinedIn Ω (P.vertex 0) (P.vertex i) := by
    refine Fin.induction ?_ ?_
    · exact JoinedIn.refl (hP.2.1.symm ▸ hv₀)
    · intro i hi
      exact hi.trans (hstep i)
  simpa only [hP.2.1, hP.2.2.1] using hroute (Fin.last P.length)

theorem ratio_fiber_isPreconnected (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hT : 0 < (etaDenom M τ).re) (n h ell p : ℤ)
    (hne : (ratioFiber M τ n h ell p).Nonempty) :
    IsPreconnected (ratioFiber M τ n h ell p) := by
  apply IsConnected.isPreconnected
  apply IsPathConnected.isConnected
  apply isPathConnected_iff.mpr
  refine ⟨hne, ?_⟩
  intro v₀ hv₀ v₁ hv₁
  obtain ⟨P, hP⟩ := polygonal_route_exists M hM τ hT n h ell p v₀ v₁ hv₀ hv₁
  exact polygon_joinedIn P _ v₀ v₁ hv₀ hP

end SICLean.L4.G1ContinuationStrictAux

namespace SICLean.L4.G1ContinuationStrictAux

theorem unitFiber_dense (M : SL(2, ℤ)) (m n : ℤ) (τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M) :
    Dense {z : ℂ | (z, τ) ∈ modularPhiNonvanishingDomain M m n} := by
  let P : Set ℂ :=
    Set.range (fun k : ℕ × ℕ => modularPhiPolePoint M m n τ k.1 k.2)
  let Z : Set ℂ :=
    Set.range (fun k : ℕ × ℕ => modularPhiZeroPoint M m n τ k.1 k.2)
  have hcount : (P ∪ Z).Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  apply (hcount.dense_compl ℂ).mono
  intro z hz
  refine ⟨hτ, ?_, ?_⟩
  · have he : modularPhiPoleIndices M m n z τ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨K, J⟩ ⟨_, hpoint⟩
      exact hz (Or.inl ⟨(K, J), hpoint.symm⟩)
    simp [modularPhiPoleMultiplicity, he]
  · have he : modularPhiZeroIndices M m n z τ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨K, J⟩ ⟨_, hpoint⟩
      exact hz (Or.inr ⟨(K, J), hpoint.symm⟩)
    simp [modularPhiZeroMultiplicity, he]


end SICLean.L4.G1ContinuationStrictAux

namespace SICLean.L4.G1ContinuationStrictAux

open G1Continuation

theorem single_window_inverse_domain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ell : ℤ) (τ w : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hT : 0 < (etaDenom M τ).re) (hw : w ∈ singleWindow M τ h ell) :
    (w, τ) ∈ ModularCluster.inversePhiDomain M ell (1 - h) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hTne : etaDenom M τ ≠ 0 := by
    intro he; simp [he] at hT
  have hempty : modularPhiZeroIndices M ell (1 - h) w τ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, hwzero⟩
    have he : G1RatioTail.complexS M τ w h ell / etaDenom M τ =
        -(K : ℂ) - (J : ℂ) * (etaDenom M τ)⁻¹ := by
      rw [hwzero]
      unfold G1RatioTail.complexS modularPhiZeroPoint
      push_cast
      field_simp
      ring
    have hinv : 0 ≤ ((etaDenom M τ)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hT.le (Complex.normSq_nonneg _)
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hw' := hw
    change 0 < (G1RatioTail.complexS M τ w h ell / etaDenom M τ).re at hw'
    rw [he] at hw'
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re,
      Complex.mul_re, Complex.natCast_im, zero_mul, sub_zero] at hw'
    nlinarith [mul_nonneg hJ hinv]
  exact ⟨hτ, by simp [modularPhiZeroMultiplicity, hempty]⟩

theorem single_raw_slice_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ell : ℤ) (τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hT : 0 < (etaDenom M τ).re) :
    AnalyticOnNhd ℂ (fun w : ℂ => (modularPhi M ell (1 - h) w τ)⁻¹)
      (singleWindow M τ h ell) := by
  intro w hw
  exact (ModularCluster.inversePhi_joint_analytic M hM ell (1-h) (w, τ)
    (single_window_inverse_domain M hM h ell τ w hτ hT hw)).comp
      (f := fun z : ℂ => (z, τ)) (x := w) (analyticAt_id.prod analyticAt_const)

end SICLean.L4.G1ContinuationStrictAux



namespace SICLean.L4.G1ContinuationStrictAux

open G1Continuation

def singleSum (M : SL(2, ℤ)) (x : Fin (M 1 0).toNat → ℝ)
    (n h ell : ℤ) (ψ : ℝ) (u : ℂ × ℂ) : ℂ :=
  ∑ m : Fin (M 1 0).toNat, singleBentValue M n h ell (m : ℤ) (x m) ψ u

theorem canonical_choices (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    UpperWindow.Choices M ψ (1 / 4) (1 / 4) (1 / (8 * (M 1 0 : ℝ))) := by
  have hcR : (0 : ℝ) < M 1 0 := by exact_mod_cast hM
  refine ⟨hM, hψ, hψ', by norm_num, by norm_num, by norm_num, by positivity, ?_⟩
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * (M 1 0 : ℝ)) hcR]
  nlinarith

theorem single_continuation_unique_of_crossing (M : SL(2, ℤ)) (n h ell : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ)
    (hcrossing : ∀ u ∈ singleTube M h ell ψ,
      ∀ x₀ x₁ : Fin (M 1 0).toNat → ℝ,
      (∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x₀ m) ψ) →
      (∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x₁ m) ψ) →
      singleSum M x₀ n h ell ψ u = singleSum M x₁ n h ell ψ u) (τ : ℂ)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F (singleWindow M τ h ell))
    (hseed : ∀ w, (τ, w) ∈ UpperIntegralIdentities.singleDomain M h ell ψ σ ρ δ →
      F w = UpperResidueParameters.prefactor M τ * (modularPhi M ell (1 - h) w τ)⁻¹) :
    ∀ w ∈ singleWindow M τ h ell, ∀ x : Fin (M 1 0).toNat → ℝ,
      (∀ m : Fin (M 1 0).toNat, BentClear M τ n (m : ℤ) (x m) ψ) →
        F w = singleSum M x n h ell ψ (τ, w) := by
  intro w hw x hx
  have hτprop := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 τ hτ
  have hG : AnalyticOnNhd ℂ (fun z : ℂ => singleSum M x n h ell ψ (τ, z))
      (singleWindow M τ h ell) := by
    intro z hz
    unfold singleSum
    apply Finset.analyticAt_fun_sum
    intro m hm
    have hreg : (τ, z) ∈ singleAdmissible M n h ell (m : ℤ) (x m) ψ := by
      refine ⟨hτprop.1, hτprop.2.2.1, hc.2.1, hc.2.2.1, ?_, hz, hx m⟩
      rw [abs_of_pos hτ.2.1]
      exact hτ.2.2
    exact ((single_bent_joint_analytic M hc.1 n h ell (m : ℤ) (x m) ψ).2.1 _ hreg).comp
      (f := fun z : ℂ => (τ, z)) (x := z) (analyticAt_const.prod analyticAt_id)
  obtain ⟨U, hU, ⟨z₀, hz₀⟩, hUseed⟩ :=
    (UpperIntegralIdentities.initial_fibers M h ell 0 ψ σ ρ δ hc τ hτ).1
  have hEqSeed : ∀ z ∈ U, F z = singleSum M x n h ell ψ (τ, z) := by
    intro z hz
    have hzseed := hUseed z hz
    have hztube : (τ, z) ∈ singleTube M h ell ψ :=
      ⟨hτ, (initial_fibers_inside_target M n h ell 0 ψ σ ρ δ hc τ hτ).2.1 z hzseed⟩
    obtain ⟨x₀, hx₀, hval⟩ := single_seed_end_rotation M n h ell ψ σ ρ δ hc (τ, z) hzseed
    have hcross := hcrossing (τ, z) hztube x x₀ hx hx₀
    exact (hseed z hzseed).trans
      (((UpperIntegralIdentities.upper_single M n h ell ψ σ ρ δ hc (τ, z) hzseed).2).symm.trans
        (hval.symm.trans hcross.symm))
  apply hF.eqOn_of_preconnected_of_eventuallyEq hG
    (single_window_open_convex M τ h ell).2.isPreconnected
    ((initial_fibers_inside_target M n h ell 0 ψ σ ρ δ hc τ hτ).2.1 z₀ (hUseed z₀ hz₀))
    (Filter.mem_of_superset (hU.mem_nhds hz₀) fun z hz => hEqSeed z hz) hw


end SICLean.L4.G1ContinuationStrictAux

namespace SICLean.L4.G1ContinuationStrictAux

open G1Continuation

/-- The negative lower-slope condition excludes every pole of the sum factor. -/
theorem ratio_sum_holomorphic_domain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ell p : ℤ) (τ w y : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hT : 0 < (etaDenom M τ).re)
    (hL : (G1RatioTail.complexL M τ w y h ell p / etaDenom M τ).re < 0) :
    (w + y, τ) ∈ modularPhiHolomorphicDomain M (p + ell) (-h) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hTne : etaDenom M τ ≠ 0 := by
    intro he; simp [he] at hT
  have hempty : modularPhiPoleIndices M (p + ell) (-h) (w + y) τ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, hpoint⟩
    have he : G1RatioTail.complexL M τ w y h ell p / etaDenom M τ =
        (K : ℂ) + (J : ℂ) * (etaDenom M τ)⁻¹ := by
      have hrep : G1RatioTail.complexL M τ w y h ell p =
          (M 1 0 : ℂ) * (w + y) + (h : ℂ) +
            (((p + ell : ℤ) : ℂ) - 1) * etaDenom M τ := by
        unfold G1RatioTail.complexL G1RatioTail.complexS
        push_cast
        ring
      rw [hrep, hpoint]
      unfold modularPhiPolePoint
      push_cast
      field_simp
      ring
    have hinv : 0 ≤ ((etaDenom M τ)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hT.le (Complex.normSq_nonneg _)
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    rw [he] at hL
    simp only [Complex.add_re, Complex.natCast_re,
      Complex.mul_re, Complex.natCast_im, zero_mul, sub_zero] at hL
    nlinarith [mul_nonneg hJ hinv]
  exact ⟨hτ, by simp [modularPhiPoleMultiplicity, hempty]⟩

/-- The deleted hyperplanes are exactly the zero family of the y factor. -/
theorem ratio_y_inverse_domain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (v : ℂ × ℂ) (hv : v ∈ ratioFiber M τ n h ell p) :
    (v.2, τ) ∈ ModularCluster.inversePhiDomain M p 0 := by
  have hdel := (crossSeparated_iff_deleted_hyperplanes M hM τ v.1 v.2 n h ell p).mp hv.2
  have hempty : modularPhiZeroIndices M p 0 v.2 τ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨hlabel, hpoint⟩
    have hlabel' : (K, J) ∈ pinchLabels M p := by
      simpa only [modularPhiZeroLabels, pinchLabels, mem_ofPred_eq,
        zero_sub] using hlabel
    have hpoint' : modularPhiZeroPoint M p 0 τ K J = pinchValue M τ p (K, J) := by
      unfold modularPhiZeroPoint pinchValue
      push_cast
      ring
    exact hdel (K, J) hlabel' (hpoint.trans hpoint')
  exact ⟨hτ, by simp [modularPhiZeroMultiplicity, hempty]⟩

/-- Literal actual Φ and literal reciprocals are jointly analytic on the tube. The numerator has no
poles and the denominator factors have no zeros there. -/
theorem ratio_raw_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ' : ψ < Real.pi / 4) :
    AnalyticOnNhd ℂ (ratioExpression M h ell p) (ratioTube M n h ell p ψ) := by
  intro x hx
  have hprop := UpperWindow.tauRegion_properties M hM ψ hψ' x.1 hx.1
  have hsum := modularPhi_joint_analytic_no_poles M hM (p + ell) (-h)
    (x.2.1 + x.2.2, x.1)
      (ratio_sum_holomorphic_domain M hM h ell p x.1 x.2.1 x.2.2 hprop.1
        hprop.2.2.1 hx.2.1.2)
  have hy := ModularCluster.inversePhi_joint_analytic M hM p 0 (x.2.2, x.1)
    (ratio_y_inverse_domain M hM n h ell p x.1 hprop.1 x.2 hx.2)
  have hw := ModularCluster.inversePhi_joint_analytic M hM ell (1 - h) (x.2.1, x.1)
    (single_window_inverse_domain M hM h ell x.1 x.2.1 hprop.1 hprop.2.2.1 hx.2.1.1)
  have hprojw : AnalyticAt ℂ (fun q : Parameters => q.2.1) x :=
    analyticAt_fst.comp (f := fun q : Parameters => q.2) (x := x) analyticAt_snd
  have hprojy : AnalyticAt ℂ (fun q : Parameters => q.2.2) x :=
    analyticAt_snd.comp (f := fun q : Parameters => q.2) (x := x) analyticAt_snd
  have hsum' := hsum.comp (f := fun q : Parameters => (q.2.1 + q.2.2, q.1))
    (x := x) ((hprojw.add hprojy).prod analyticAt_fst)
  have hy' := hy.comp (f := fun q : Parameters => (q.2.2, q.1))
    (x := x) (hprojy.prod analyticAt_fst)
  have hw' := hw.comp (f := fun q : Parameters => (q.2.1, q.1))
    (x := x) (hprojw.prod analyticAt_fst)
  have hform : ratioExpression M h ell p = fun q : Parameters =>
      modularPhi M (p + ell) (-h) (q.2.1 + q.2.2) q.1 *
        (modularPhi M p 0 q.2.2 q.1)⁻¹ * (modularPhi M ell (1 - h) q.2.1 q.1)⁻¹ := by
    funext q
    simp only [ratioExpression, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hform]
  exact (hsum'.mul hy').mul hw'

theorem ratio_raw_slice_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ' : ψ < Real.pi / 4)
    (τ : ℂ) (hτ : τ ∈ UpperWindow.tauRegion M ψ) :
    AnalyticOnNhd ℂ (fun v : ℂ × ℂ => ratioExpression M h ell p (τ, v))
      (ratioFiber M τ n h ell p) := by
  intro v hv
  exact (ratio_raw_joint_analytic M hM n h ell p ψ hψ' (τ, v) ⟨hτ, hv⟩).comp
    (f := fun z : ℂ × ℂ => (τ, z)) (x := v) (analyticAt_const.prod analyticAt_id)

/-- The nonempty seed determines an analytic function on the full no-pinch fiber. -/
theorem ratio_analytic_identification (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (τ : ℂ)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (F : (ℂ × ℂ) → ℂ)
    (hF : AnalyticOnNhd ℂ F (ratioFiber M τ n h ell p))
    (hseed : ∀ v, (τ, v) ∈ UpperWindow.domain M h ell p ψ σ ρ δ →
      F v = UpperResidueParameters.prefactor M τ * ratioExpression M h ell p (τ, v)) :
    ∀ v ∈ ratioFiber M τ n h ell p,
      F v = UpperResidueParameters.prefactor M τ * ratioExpression M h ell p (τ, v) := by
  obtain ⟨V, hV, hVne, hVseed⟩ :=
    (UpperIntegralIdentities.initial_fibers M h ell p ψ σ ρ δ hc τ hτ).2
  obtain ⟨v₀, hv₀⟩ := hVne
  have hv₀target : v₀ ∈ ratioFiber M τ n h ell p :=
    (initial_fibers_inside_target M n h ell p ψ σ ρ δ hc τ hτ).2.2.2 v₀
      (hVseed v₀ hv₀)
  have hG : AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ => UpperResidueParameters.prefactor M τ *
        ratioExpression M h ell p (τ, v)) (ratioFiber M τ n h ell p) :=
    analyticOnNhd_const.mul (ratio_raw_slice_analytic M hc.1 n h ell p ψ hc.2.2.1 τ hτ)
  have heq : F =ᶠ[𝓝 v₀] (fun v => UpperResidueParameters.prefactor M τ *
      ratioExpression M h ell p (τ, v)) := by
    filter_upwards [hV.mem_nhds hv₀] with v hv
    exact hseed v (hVseed v hv)
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG
    (ratio_fiber_isPreconnected M hc.1 τ
      (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 τ hτ).2.2.1
      n h ell p ⟨v₀, hv₀target⟩) hv₀target heq

/-- Every separating representative has the actual analytic ratio value. -/
theorem upper_ratio_all_strict_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ratioExtensionSum M D n h ell p x =
      UpperResidueParameters.prefactor M x.1 * ratioExpression M h ell p x := by
  obtain ⟨F, hF, hval, _⟩ := ratio_global_analytic_value M hM n h ell p ψ hψ hψ'
  have hFslice : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => F (x.1, v))
      (ratioFiber M x.1 n h ell p) := by
    intro v hv
    exact (hF (x.1, v) ⟨hx.1, hv⟩).comp
      (f := fun z : ℂ × ℂ => (x.1, z)) (x := v) (analyticAt_const.prod analyticAt_id)
  have hc := canonical_choices M hM ψ hψ hψ'
  have hseed : ∀ v, (x.1, v) ∈ UpperWindow.domain M h ell p ψ (1 / 4) (1 / 4)
      (1 / (8 * (M 1 0 : ℝ))) →
      F (x.1, v) = UpperResidueParameters.prefactor M x.1 *
        ratioExpression M h ell p (x.1, v) := by
    intro v hv
    obtain ⟨E, hE, hEval⟩ := ratio_seed_end_rotation M n h ell p ψ _ _ _ hc (x.1, v) hv
    exact (hval (x.1, v) (ratio_seed_mem_tube M n h ell p ψ _ _ _ hc (x.1, v) hv)
      E hE).symm.trans (hEval.trans
        (UpperIntegralIdentities.upper_ratio M n h ell p ψ _ _ _ hc (x.1, v) hv).2)
  exact (hval x hx D hD).trans
    (ratio_analytic_identification M n h ell p ψ _ _ _ hc x.1 hx.1
      (fun v => F (x.1, v)) hFslice hseed x.2 hx.2)

theorem ratio_continuation_unique (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (τ : ℂ)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (F : (ℂ × ℂ) → ℂ)
    (hF : AnalyticOnNhd ℂ F (ratioFiber M τ n h ell p))
    (hseed : ∀ v, (τ, v) ∈ UpperWindow.domain M h ell p ψ σ ρ δ →
      F v = UpperResidueParameters.prefactor M τ * ratioExpression M h ell p (τ, v)) :
    ∀ v ∈ ratioFiber M τ n h ell p,
      ∀ D : Fin (M 1 0).toNat → CircleExtension,
      (∀ m, SeparatesExtension (D m) M τ v.2 n p (m : ℤ)) →
        F v = ratioExtensionSum M D n h ell p (τ, v) := by
  intro v hv D hD
  exact (ratio_analytic_identification M n h ell p ψ σ ρ δ hc τ hτ F hF hseed v hv).trans
    (upper_ratio_all_strict_value M hc.1 n h ell p ψ hc.2.1 hc.2.2.1 (τ, v)
      ⟨hτ, hv⟩ D hD).symm

end SICLean.L4.G1ContinuationStrictAux

namespace SICLean.L4.G1ContinuationStrictAux

open G1Continuation

lemma affine_ribbon (f : ℂ → ℂ) (a d : ℂ) (x₀ x₁ r₀ r₁ : ℝ)
    (hx : x₀ ≤ x₁) (hr : r₀ ≤ r₁)
    (hf : ∀ p ∈ Icc (x₀, r₀) (x₁, r₁),
      DifferentiableAt ℂ f ((p.1 : ℂ) + a + (p.2 : ℂ) * d)) :
    (∫ r : ℝ in r₀..r₁, f ((x₁ : ℂ) + a + (r : ℂ) * d) * d) -
      (∫ r : ℝ in r₀..r₁, f ((x₀ : ℂ) + a + (r : ℂ) * d) * d) =
    (∫ x : ℝ in x₀..x₁, f ((x : ℂ) + a + (r₁ : ℂ) * d)) -
      (∫ x : ℝ in x₀..x₁, f ((x : ℂ) + a + (r₀ : ℂ) * d)) := by
  let L : ℝ × ℝ →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      d • Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let H : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + a + (p.2 : ℂ) * d
  have hH (p : ℝ × ℝ) : HasFDerivAt H L p := by
    simpa [H, L, add_comm, add_left_comm, add_assoc, mul_comm] using
      L.hasFDerivAt.add_const a
  let F : ℝ × ℝ → ℂ := fun p => f (H p)
  let DF : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => deriv f (H p) • L
  have hdf (p : ℝ × ℝ) (hp : p ∈ Icc (x₀, r₀) (x₁, r₁)) :
      HasFDerivAt F (DF p) p :=
    (hf p hp).hasDerivAt.comp_hasFDerivAt p (hH p)
  have hfc : ContinuousOn F (Icc (x₀, r₀) (x₁, r₁)) :=
    fun p hp => (hdf p hp).continuousAt.continuousWithinAt
  have hinner (p : ℝ × ℝ) (hp : p ∈ Ioo x₀ x₁ ×ˢ Ioo r₀ r₁) :
      p ∈ Icc (x₀, r₀) (x₁, r₁) :=
    ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩
  have hzero (p : ℝ × ℝ) : (d • DF p) (1, 0) + (-DF p) (0, 1) = 0 := by
    simp [DF, L, smul_eq_mul]
    ring
  have hg := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fun p => d • F p) (fun p => -F p) (fun p => d • DF p) (fun p => -DF p)
    (x₀, r₀) (x₁, r₁) ⟨hx, hr⟩ (hfc.const_smul d) hfc.neg
    (fun p hp => (hdf p (hinner p hp)).const_smul d)
    (fun p hp => (hdf p (hinner p hp)).neg)
    (by simp only [hzero]; exact integrableOn_zero)
  simp only [hzero, integral_zero, F, H, smul_eq_mul,
    intervalIntegral.integral_neg, mul_comm d] at hg
  linear_combination -hg

lemma q_small_bounds (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ →
      (1 / 2 : ℝ) < ‖qPochhammer u q‖ ∧ ‖qPochhammer u q‖ < 2 := by
  have hc : ContinuousAt (fun u : ℂ => ‖qPochhammer u q‖) 0 :=
    ((differentiable_qPochhammer_x q hq0 hq1).continuous.continuousAt).norm
  have hn : ∀ᶠ u : ℂ in 𝓝 0,
      (1 / 2 : ℝ) < ‖qPochhammer u q‖ ∧ ‖qPochhammer u q‖ < 2 :=
    hc.preimage_mem_nhds (Ioo_mem_nhds (by norm_num [qPochhammer_zero])
      (by norm_num [qPochhammer_zero]))
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨δ, hδ, fun u hu => hsub (by simpa [Metric.mem_ball, dist_zero_right] using hu)⟩

lemma exp_small (C k ε : ℝ) (hk : 0 < k) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, C * Real.exp (-k * R) < ε := by
  have ht : Tendsto (fun R : ℝ => C * Real.exp (-k * R)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hk tendsto_id)).const_mul C
  exact ht.eventually (eventually_lt_nhds hε)

lemma e_upper_bound (A B : ℂ) (x₀ x₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc x₀ x₁, ∀ R : ℝ,
      ‖B * e (A * g1VerticalPoint x R)‖ ≤
        C * Real.exp (-(2 * Real.pi * A.re) * R) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc x₀ x₁)).exists_bound_of_continuousOn
    (f := fun x : ℝ => B * e (A * (x : ℂ))) (by unfold e; fun_prop)
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx R
  have he := G1BilateralRatioTailsAux.norm_e_vertical A 0 x R
  simp only [add_zero] at he
  rw [norm_mul, he, ← mul_assoc]
  have hc := hC x hx
  rw [norm_mul] at hc
  exact mul_le_mul_of_nonneg_right (hc.trans (le_max_left _ _)) (Real.exp_pos _).le



lemma upper_phi_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (ψ : ℝ) (hψ' : ψ < Real.pi / 4)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (m n : ℤ) (x₀ x₁ : ℝ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R ≥ R₀, ∀ x ∈ Icc x₀ x₁,
      ‖modularPhi M m n (g1VerticalPoint x R) τ‖ ≤ 4 := by
  have hp := UpperWindow.tauRegion_properties M hM ψ hψ' τ hτ
  obtain ⟨δ₁, hδ₁, hq₁⟩ := q_small_bounds (e τ) hp.2.2.2.2.1 hp.2.2.2.2.2.1
  obtain ⟨δ₂, hδ₂, hq₂⟩ := q_small_bounds (e (etaMobius M τ))
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2
  obtain ⟨C₁, hC₁, he₁⟩ := e_upper_bound 1 ((e τ)^m) x₀ x₁
  obtain ⟨C₂, hC₂, he₂⟩ := e_upper_bound (1 / etaDenom M τ)
    ((e (etaMobius M τ))^n) x₀ x₁
  have hk₂ : 0 < 2 * Real.pi * (1 / etaDenom M τ).re := by
    simp only [one_div, Complex.inv_re]
    exact mul_pos (by positivity) (div_pos hp.2.2.1 (Complex.normSq_pos.mpr hp.2.2.2.1))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
    ((exp_small C₁ (2 * Real.pi) δ₁ (by positivity) hδ₁).and
      (exp_small C₂ (2 * Real.pi * (1 / etaDenom M τ).re) δ₂ hk₂ hδ₂))
  refine ⟨max R₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR x hx
  have hR' := hR₀ R ((le_max_left _ _).trans hR)
  have hu₁ : ‖(e τ)^m * e (g1VerticalPoint x R)‖ < δ₁ := by
    exact lt_of_le_of_lt (by simpa using he₁ x hx R) hR'.1
  have hu₂ : ‖(e (etaMobius M τ))^n * e (g1VerticalPoint x R / etaDenom M τ)‖ < δ₂ := by
    exact lt_of_le_of_lt (by simpa [div_eq_mul_inv, mul_comm] using he₂ x hx R) hR'.2
  have hn := hq₁ _ hu₁
  have hd := hq₂ _ hu₂
  have hden : modularPhiQDenominator M n (g1VerticalPoint x R) τ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hd.1)
  rw [modularPhi_eq_qProduct M hM m n _ τ hτ.1 hden]
  simp only [modularPhiQProduct, modularPhiQNumerator, modularPhiQDenominator, norm_div]
  apply (div_le_iff₀ (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hd.1)).mpr
  nlinarith [hn.2]

lemma upper_single_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w : ℂ) (ψ : ℝ) (hψ' : ψ < Real.pi / 4)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (n h ell m : ℤ)
    (hs : w ∈ singleWindow M τ h ell) (x₀ x₁ : ℝ) :
    ∃ C κ R₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R₀ ∧
      ∀ R ≥ R₀, ∀ x ∈ Icc x₀ x₁,
        ‖UpperWindow.singleKernel M m n h ell τ w (g1VerticalPoint x R)‖ ≤
          C * Real.exp (-κ * R) := by
  have hp := UpperWindow.tauRegion_properties M hM ψ hψ' τ hτ
  obtain ⟨R₀, hR₀, hphi⟩ := upper_phi_bound M hM τ ψ hψ' hτ (m+1) n x₀ x₁
  let A := G1RatioTail.complexS M τ w h ell / etaDenom M τ
  obtain ⟨C, hC, he⟩ := e_upper_bound A (e (g1Exponent M τ w 0 n h ell m)) x₀ x₁
  have hκ : 0 < 2 * Real.pi * A.re := mul_pos (by positivity) hs
  refine ⟨4*C, 2 * Real.pi * A.re, R₀, by positivity, hκ, hR₀, ?_⟩
  intro R hR x hx
  have hphase : e (UpperWindow.phase M m n h ell τ w (g1VerticalPoint x R)) =
      e (g1Exponent M τ w 0 n h ell m) * e (A * g1VerticalPoint x R) := by
    change e (g1Exponent M τ w (g1VerticalPoint x R) n h ell m) = _
    rw [G1RatioTail.exponent_affine M τ w _ n h ell m hp.2.2.2.1]
    simp only [e, mul_add, Complex.exp_add]
    exact mul_comm _ _
  rw [UpperWindow.singleKernel, norm_mul, hphase]
  have hb := mul_le_mul (hphi R hR x hx) (he x hx R) (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 4)
  simpa only [mul_assoc] using hb



lemma poleMultiplicity_zero_of_avoids (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ)
    (havoid : ∀ k ∈ modularPhiPoleLabels M m n,
      z ≠ modularPhiPolePoint M m n τ k.1 k.2) :
    modularPhiPoleMultiplicity M m n z τ = 0 := by
  have he : modularPhiPoleIndices M m n z τ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro k ⟨hk, hz⟩
    exact havoid k hk hz
  simp [modularPhiPoleMultiplicity, he]

lemma single_kernel_differentiable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w z : ℂ) (n h ell m : ℤ) (hτ : τ ∈ modularPhiDomain M)
    (havoid : ∀ k ∈ modularPhiPoleLabels M (m + 1) n,
      z ≠ modularPhiPolePoint M (m + 1) n τ k.1 k.2) :
    DifferentiableAt ℂ (UpperWindow.singleKernel M m n h ell τ w) z := by
  have hreg : (z, (τ, w)) ∈ singleRegular M n m :=
    ⟨hτ, poleMultiplicity_zero_of_avoids M _ _ z τ havoid⟩
  have ha := (single_kernel_joint_analytic M hM n h ell m).2 _ hreg
  exact (ha.comp (x := z) (f := fun z : ℂ => (z, (τ, w)))
    (by fun_prop)).differentiableAt

lemma cos_pos (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) : 0 < Real.cos ψ := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

lemma tan_nonneg (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) : 0 ≤ Real.tan ψ := by
  rw [Real.tan_eq_sin_div_cos]
  exact (div_pos (Real.sin_pos_of_pos_of_lt_pi hψ (by linarith [Real.pi_pos]))
    (cos_pos ψ hψ hψ')).le

lemma clear_upper_avoids (M : SL(2, ℤ)) (τ : ℂ) (n m : ℤ) (X ψ : ℝ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) (hc : BentClear M τ n m X ψ)
    (x r : ℝ) (hx : x ≤ X) :
    ∀ k ∈ modularPhiPoleLabels M (m + 1) n,
      g1VerticalPoint x r ≠ modularPhiPolePoint M (m + 1) n τ k.1 k.2 := by
  intro k hk heq
  have hclear := hc k hk
  have hn : 0 ≤ max 0 (-(modularPhiPolePoint M (m + 1) n τ k.1 k.2).im - 1) *
      Real.tan ψ := mul_nonneg (le_max_left _ _) (tan_nonneg ψ hψ hψ')
  have hre : (modularPhiPolePoint M (m + 1) n τ k.1 k.2).re = x := by
    simpa [g1VerticalPoint] using (congrArg Complex.re heq).symm
  dsimp only at hclear
  rw [hre] at hclear
  linarith

lemma clear_lower_avoids (M : SL(2, ℤ)) (τ : ℂ) (n m : ℤ) (X ψ : ℝ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) (hc : BentClear M τ n m X ψ)
    (x r : ℝ) (hx : x ≤ X) (hr : 0 ≤ r) :
    ∀ k ∈ modularPhiPoleLabels M (m + 1) n,
      g1BentLowerPoint x ψ r ≠ modularPhiPolePoint M (m + 1) n τ k.1 k.2 := by
  intro k hk heq
  have hclear := hc k hk
  have hre : (modularPhiPolePoint M (m + 1) n τ k.1 k.2).re = x + r * Real.sin ψ := by
    simpa [g1BentLowerPoint, G1BilateralSingleTailsAux.branch_direction_re] using
      (congrArg Complex.re heq).symm
  have him : (modularPhiPolePoint M (m + 1) n τ k.1 k.2).im = -1 - r * Real.cos ψ := by
    have hi := (congrArg Complex.im heq).symm
    simpa [g1BentLowerPoint, G1BilateralSingleTailsAux.branch_direction_im, sub_eq_add_neg] using hi
  have hcos := cos_pos ψ hψ hψ'
  have he : max 0 (-(modularPhiPolePoint M (m + 1) n τ k.1 k.2).im - 1) = r * Real.cos ψ := by
    rw [him, show -(-1 - r * Real.cos ψ) - 1 = r * Real.cos ψ by ring]
    exact max_eq_right (mul_nonneg hr hcos.le)
  have htan : (r * Real.cos ψ) * Real.tan ψ = r * Real.sin ψ := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  dsimp only at hclear
  rw [he, htan, hre] at hclear
  linarith

lemma lower_single_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w : ℂ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (n h ell : ℤ)
    (m : Fin (M 1 0).toNat) (x₀ x₁ : ℝ) :
    ∃ C κ R₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R₀ ∧
      ∀ R ≥ R₀, ∀ x ∈ Icc x₀ x₁,
        ‖UpperWindow.singleKernel M (m : ℤ) n h ell τ w (g1BentLowerPoint x ψ R)‖ ≤
          C * Real.exp (-κ * R) := by
  let A : ℝ := max |x₀| |x₁| + 1
  obtain ⟨C, a, B, R₀, hC, ha, hB, hR₀, hb⟩ :=
    single_lower_gaussian_translations M hM n h ell ψ A hψ hψ'
      {(τ, w)} isCompact_singleton (by
        intro u hu
        have hu' : u = (τ, w) := hu
        subst u
        exact hτ)
  refine ⟨C, 1, max R₀ ((B + 1) / a), hC, zero_lt_one,
    lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro R hR x hx
  have hRg : R₀ ≤ R := (le_max_left _ _).trans hR
  have hR0 : 0 ≤ R := hR₀.le.trans hRg
  have hxabs : |x| ≤ max |x₀| |x₁| := by
    apply abs_le.mpr
    constructor
    · have h0 := neg_abs_le x₀
      linarith [le_max_left |x₀| |x₁|, hx.1]
    · exact hx.2.trans ((le_abs_self x₁).trans (le_max_right _ _))
  have hz : (x : ℂ) - Complex.I ∈ Metric.closedBall 0 A := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖(x : ℂ) - Complex.I‖ ≤ ‖(x : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ ≤ A := by simpa [A] using add_le_add_right hxabs 1
  have hbound := (hb (τ, w) (by simp)).2 m ((x : ℂ) - Complex.I) hz R hRg
  have hlin : B + 1 ≤ a * R := by
    simpa only [mul_comm] using (div_le_iff₀ ha).mp ((le_max_right _ _).trans hR)
  have hexp : -a * R^2 + B * R ≤ -R := by nlinarith [mul_le_mul_of_nonneg_right hlin hR0]
  exact hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by simpa using hexp)) hC.le)



lemma horizontal_tendsto (G : ℝ → ℝ → ℂ) (x₀ x₁ C κ R₀ : ℝ)
    (hx : x₀ ≤ x₁) (hκ : 0 < κ)
    (hbound : ∀ R ≥ R₀, ∀ x ∈ Icc x₀ x₁, ‖G R x‖ ≤ C * Real.exp (-κ * R)) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in x₀..x₁, G R x) atTop (𝓝 0) := by
  have ht : Tendsto (fun R : ℝ => C * Real.exp (-κ * R) * |x₁-x₀|) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hκ tendsto_id)).const_mul C).mul_const |x₁-x₀|
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop R₀] with R hR
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hxx
  rw [uIoc_of_le hx] at hxx
  exact hbound R hR x ⟨hxx.1.le, hxx.2⟩

def bentTruncated (f : ℂ → ℂ) (x ψ R : ℝ) : ℂ :=
  -(∫ r : ℝ in 0..R, g1BentLowerPullback f x ψ r) +
    ∫ r : ℝ in -1..R, g1VerticalPullback f x r

lemma bent_truncated_tendsto (f : ℂ → ℂ) (x ψ : ℝ) (hi : G1BentIntegrable f x ψ) :
    Tendsto (bentTruncated f x ψ) atTop (𝓝 (g1BentIntegral f x ψ)) := by
  have hd := intervalIntegral_tendsto_integral_Ioi 0
    (hi.1.mono_set Ioi_subset_Ici_self) tendsto_id
  have hu := intervalIntegral_tendsto_integral_Ioi (-1)
    (hi.2.mono_set Ioi_subset_Ici_self) tendsto_id
  change Tendsto (fun R : ℝ => bentTruncated f x ψ R) atTop (𝓝 (g1BentIntegral f x ψ))
  simpa only [bentTruncated, g1BentIntegral, integral_Ici_eq_integral_Ioi, id_eq] using hd.neg.add hu

lemma bent_finite_ribbon (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w : ℂ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hτ : τ ∈ modularPhiDomain M) (n h ell m : ℤ) (x₀ x₁ R : ℝ)
    (hx : x₀ ≤ x₁) (hR : 0 ≤ R) (hc : BentClear M τ n m x₁ ψ) :
    let f := UpperWindow.singleKernel M m n h ell τ w
    bentTruncated f x₁ ψ R - bentTruncated f x₀ ψ R =
      (∫ x : ℝ in x₀..x₁, f (g1VerticalPoint x R)) -
        (∫ x : ℝ in x₀..x₁, f (g1BentLowerPoint x ψ R)) := by
  let f := UpperWindow.singleKernel M m n h ell τ w
  have hup := affine_ribbon f 0 Complex.I x₀ x₁ (-1) R hx (by linarith) (by
    intro p hp
    simpa only [g1VerticalPoint, add_zero] using
      single_kernel_differentiable M hM τ w (g1VerticalPoint p.1 p.2) n h ell m hτ
        (clear_upper_avoids M τ n m x₁ ψ hψ hψ' hc p.1 p.2 hp.2.1))
  have hlo := affine_ribbon f (-Complex.I) (g1LowerDirection ψ) x₀ x₁ 0 R hx hR (by
    intro p hp
    simpa only [g1BentLowerPoint, sub_eq_add_neg] using
      single_kernel_differentiable M hM τ w (g1BentLowerPoint p.1 ψ p.2) n h ell m hτ
        (clear_lower_avoids M τ n m x₁ ψ hψ hψ' hc p.1 p.2 hp.2.1 hp.1.2))
  have hu : (∫ r : ℝ in -1..R, g1VerticalPullback f x₁ r) -
      (∫ r : ℝ in -1..R, g1VerticalPullback f x₀ r) =
      (∫ x : ℝ in x₀..x₁, f (g1VerticalPoint x R)) -
        (∫ x : ℝ in x₀..x₁, f ((x : ℂ) - Complex.I)) := by
    simpa only [g1VerticalPullback, g1VerticalPoint, add_zero,
      Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, sub_eq_add_neg] using hup
  have hl : (∫ r : ℝ in 0..R, g1BentLowerPullback f x₁ ψ r) -
      (∫ r : ℝ in 0..R, g1BentLowerPullback f x₀ ψ r) =
      (∫ x : ℝ in x₀..x₁, f (g1BentLowerPoint x ψ R)) -
        (∫ x : ℝ in x₀..x₁, f ((x : ℂ) - Complex.I)) := by
    simpa only [g1BentLowerPullback, g1BentLowerPoint, sub_eq_add_neg,
      Complex.ofReal_zero, zero_mul, add_zero] using hlo
  dsimp only
  change bentTruncated f x₁ ψ R - bentTruncated f x₀ ψ R = _
  unfold bentTruncated
  linear_combination hu - hl

lemma bent_component_eq_of_le (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w : ℂ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (n h ell : ℤ)
    (m : Fin (M 1 0).toNat) (hs : w ∈ singleWindow M τ h ell)
    (x₀ x₁ : ℝ) (hx : x₀ ≤ x₁)
    (hc₀ : BentClear M τ n (m : ℤ) x₀ ψ)
    (hc₁ : BentClear M τ n (m : ℤ) x₁ ψ) :
    g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell τ w) x₀ ψ =
      g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell τ w) x₁ ψ := by
  let f := UpperWindow.singleKernel M (m : ℤ) n h ell τ w
  have hp := UpperWindow.tauRegion_properties M hM ψ hψ' τ hτ
  have had₀ : (τ, w) ∈ singleAdmissible M n h ell (m : ℤ) x₀ ψ :=
    ⟨hp.1, hp.2.2.1, hψ, hψ', by rw [abs_of_pos hτ.2.1]; exact hτ.2.2, hs, hc₀⟩
  have had₁ : (τ, w) ∈ singleAdmissible M n h ell (m : ℤ) x₁ ψ :=
    ⟨hp.1, hp.2.2.1, hψ, hψ', by rw [abs_of_pos hτ.2.1]; exact hτ.2.2, hs, hc₁⟩
  have hi₀ := (single_bent_joint_analytic M hM n h ell (m : ℤ) x₀ ψ).2.2 _ had₀
  have hi₁ := (single_bent_joint_analytic M hM n h ell (m : ℤ) x₁ ψ).2.2 _ had₁
  have ht := (bent_truncated_tendsto f x₁ ψ hi₁).sub (bent_truncated_tendsto f x₀ ψ hi₀)
  obtain ⟨Cu, κu, Ru, _, hκu, _, hbu⟩ :=
    upper_single_bound M hM τ w ψ hψ' hτ n h ell (m : ℤ) hs x₀ x₁
  obtain ⟨Cl, κl, Rl, _, hκl, _, hbl⟩ :=
    lower_single_bound M hM τ w ψ hψ hψ' hτ n h ell m x₀ x₁
  have htu := horizontal_tendsto (fun R x => f (g1VerticalPoint x R))
    x₀ x₁ Cu κu Ru hx hκu hbu
  have htl := horizontal_tendsto (fun R x => f (g1BentLowerPoint x ψ R))
    x₀ x₁ Cl κl Rl hx hκl hbl
  have he : (fun R => bentTruncated f x₁ ψ R - bentTruncated f x₀ ψ R) =ᶠ[atTop]
      (fun R => (∫ x : ℝ in x₀..x₁, f (g1VerticalPoint x R)) -
        (∫ x : ℝ in x₀..x₁, f (g1BentLowerPoint x ψ R))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact bent_finite_ribbon M hM τ w ψ hψ hψ' hp.1 n h ell (m : ℤ) x₀ x₁ R hx hR hc₁
  have hz := tendsto_nhds_unique ht ((htu.sub htl).congr' he.symm)
  exact (sub_eq_zero.mp (by simpa only [sub_zero] using hz)).symm

lemma single_component_crossing_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w : ℂ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (n h ell : ℤ)
    (m : Fin (M 1 0).toNat) (hs : w ∈ singleWindow M τ h ell)
    (x₀ x₁ : ℝ)
    (hc₀ : BentClear M τ n (m : ℤ) x₀ ψ)
    (hc₁ : BentClear M τ n (m : ℤ) x₁ ψ) :
    g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell τ w) x₀ ψ =
      g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell τ w) x₁ ψ := by
  rcases le_total x₀ x₁ with hx | hx
  · exact bent_component_eq_of_le M hM τ w ψ hψ hψ' hτ n h ell m hs x₀ x₁ hx hc₀ hc₁
  · exact (bent_component_eq_of_le M hM τ w ψ hψ hψ' hτ n h ell m hs x₁ x₀ hx hc₁ hc₀).symm



theorem single_bent_crossing_invariance (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hu : u ∈ singleTube M h ell ψ)
    (x₀ x₁ : Fin (M 1 0).toNat → ℝ)
    (h₀ : ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x₀ m) ψ)
    (h₁ : ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x₁ m) ψ) :
    (∑ m : Fin (M 1 0).toNat, singleBentValue M n h ell (m : ℤ) (x₀ m) ψ u) =
      ∑ m : Fin (M 1 0).toNat, singleBentValue M n h ell (m : ℤ) (x₁ m) ψ u := by
  apply Finset.sum_congr rfl
  intro m hm
  exact single_component_crossing_eq M hM u.1 u.2 ψ hψ hψ' hu.1 n h ell m hu.2
    (x₀ m) (x₁ m) (h₀ m) (h₁ m)


end SICLean.L4.G1ContinuationStrictAux
