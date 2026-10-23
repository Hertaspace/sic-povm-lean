import SICLean.L4.G1ContinuationStrict
import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit false

/-!
Real-center joint neighborhoods for the fixed G1 chains.

The single-function estimates combine the joint tail constants of J08 with the J02 joint kernel
chart on a compact parameter ball times a compact path segment. Finite sums of nonnegative majorants
control every component on one neighborhood. The ratio geometry retains the given chain assignments
by C12 and the common strict margins of A03.

The ordinary neighborhoods here include both signs of Im τ.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1ContinuationBoundaryAux

open G1Continuation G1BilateralGeometryAux

lemma real_mem_closure_upper_joint {E : Type*} [TopologicalSpace E]
    (M : SL(2, ℤ)) (τ₀ : ℝ) (hT : 0 < g1T M τ₀)
    (S : Set (ℂ × E))
    (hS : ∀ τ ∈ modularPhiDomain M, Dense {v : E | (τ, v) ∈ S}) (v₀ : E) :
    ((τ₀ : ℂ), v₀) ∈ closure {u : ℂ × E | 0 < u.1.im ∧ u ∈ S} := by
  have hupper : (τ₀ : ℂ) ∈ closure {τ : ℂ | 0 < τ.im} := by
    rw [Complex.closure_setOfPred_lt_im]
    simp
  apply mem_closure_iff_nhds.mpr
  intro U hU
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨τ, ⟨hτA, hτD⟩, hτupper⟩ :=
    (mem_closure_iff_nhds.mp hupper) _
      (inter_mem hA (G1BilateralGeometryAux.domain_eventually M τ₀ hT))
  obtain ⟨v, hvB, hvS⟩ :=
    (mem_closure_iff_nhds.mp (hS τ hτD.1 v₀)) B hB
  exact ⟨(τ, v), hAB ⟨hτA, hvB⟩, hτupper, hvS⟩

private theorem real_bent_clear (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ δ ψ : ℝ) (n m : ℤ) (hT : 0 < g1T M τ₀) (hδ : 0 < δ) :
    BentClear M (τ₀ : ℂ) n m (g1BentCrossing M τ₀ δ n m) ψ := by
  intro k hk
  have hi : (modularPhiPolePoint M (m + 1) n (τ₀ : ℂ) k.1 k.2).im = 0 := by
    simp [modularPhiPolePoint, etaDenom]
  have hr := G1BilateralSingleTailsAux.branch_re_increment M hM (τ₀ : ℂ)
    n m k.1 k.2 (by simpa [denom_real] using hT.le)
  have hb := G1BilateralSingleTailsAux.branch_base_re_center M τ₀ δ n m
  simp only [hi, neg_zero, zero_sub, max_eq_left (by norm_num : (-1 : ℝ) ≤ 0),
    zero_mul, add_zero]
  linarith

private theorem real_single_admissible (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell m : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ((τ₀ : ℂ), (w : ℂ)) ∈ singleAdmissible M n h ell m
      (g1BentCrossing M τ₀ δ n m) ψ := by
  refine ⟨Or.inl (by simpa [denom_real] using hT),
    by simpa [denom_real] using hT, hψ, hψ', ?_, ?_,
    real_bent_clear M hM τ₀ δ ψ n m hT hδ⟩
  · rw [denom_real, Complex.arg_ofReal_of_nonneg hT.le, abs_zero]
    exact hψ
  · change 0 < (G1RatioTail.complexS M (τ₀ : ℂ) (w : ℂ) h ell /
      etaDenom M (τ₀ : ℂ)).re
    rw [complexS_real, denom_real, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_pos hs hT

/-- The prescribed real bent chains all lie in the open geometric domain. -/
theorem real_bent_joint_geometry (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      ∀ u ∈ U, ∀ m ∈ Finset.range (M 1 0).toNat,
        u ∈ singleAdmissible M n h ell (m : ℤ)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ := by
  let U := ⋂ m : Fin (M 1 0).toNat,
    singleAdmissible M n h ell (m : ℤ)
      (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ
  refine ⟨U, isOpen_iInter_of_finite (fun m =>
    (single_bent_joint_analytic M hM n h ell (m : ℤ)
      (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ).1), ?_, ?_⟩
  · exact mem_iInter.mpr fun m =>
      real_single_admissible M hM τ₀ w δ ψ n h ell (m : ℤ) hT hs hδ hψ hψ'
  · intro u hu m hm
    exact mem_iInter.mp hu ⟨m, Finset.mem_range.mp hm⟩

private theorem extension_crossSeparated (M : SL(2, ℤ)) (D : CircleExtension)
    (τ w y : ℂ) (n h ell p m : ℤ)
    (hD : SeparatesExtension D M τ y n p m) :
    ModularCluster.crossSeparated M (G1Pinch.ratioData w y n h ell p m) τ := by
  intro b hb b' hb' heq
  have hb0 : b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p m) := by
    simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
  have hb0' : b' ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p m) := by
    simpa [ModularCluster.labels, G1Pinch.ratioData] using hb'
  have heq0 : ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p m) τ b =
      ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p m) τ b' := by
    simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using heq
  have ha := (hD.2.2 b hb0).2
  have ha' := (hD.2.2 b' hb0').2
  rw [heq0] at ha
  cases hbb : b.1 <;> cases hbb' : b'.1 <;> simp_all

/-- The old real chains keep their branch assignments on a full joint tube. -/
theorem real_ratio_joint_geometry (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ U : Set Parameters, IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧
      ∀ x ∈ U, x.1 ∈ modularPhiDomain M ∧ 0 < (etaDenom M x.1).re ∧
        x.2 ∈ ratioFiber M x.1 n h ell p ∧
        ∀ m, G1FixedSeparation.SeparatesAt (D m) M x.1 x.2.2 n p (m : ℤ) := by
  obtain ⟨Us, hUs, hcs, hsep⟩ :=
    real_chain_fixed_joint_neighborhood M hM τ₀ y (w : ℂ) n p hT D hD
  obtain ⟨Ua, κ, hUa, hca, hκ, hmargin⟩ :=
    real_ratio_angular_neighborhood M hM τ₀ w y (Real.pi / 8) h ell p hT hs hL
      (by positivity) (by linarith [Real.pi_pos])
  refine ⟨Us ∩ Ua, hUs.inter hUa, ⟨hcs, hca⟩, ?_⟩
  intro x hx
  obtain ⟨hdom, hden, hsep⟩ := hsep x hx.1
  have hb := hmargin x hx.2 0 ⟨le_rfl, by positivity⟩
  simp only [G1Continuation.rotation, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one] at hb
  refine ⟨hdom, hden, ⟨⟨lt_of_lt_of_le hκ hb.1, by linarith [hb.2]⟩, ?_⟩, ?_⟩
  · intro m
    exact extension_crossSeparated M (ofChain (D m)) x.1 x.2.1 x.2.2
      n h ell p (m : ℤ) (hsep m)
  · intro m
    exact (ofChain_separates (D m) M x.1 x.2.2 n p (m : ℤ)).mp (hsep m)

private theorem single_regular_of_clear (M : SL(2, ℤ)) (τ w z : ℂ)
    (n h ell m : ℤ) (x ψ : ℝ)
    (hu : (τ, w) ∈ singleAdmissible M n h ell m x ψ)
    (hgraph : z.re ≤ x + max 0 (-z.im - 1) * Real.tan ψ) :
    (z, (τ, w)) ∈ singleRegular M n m := by
  refine ⟨hu.1, ?_⟩
  have hind : modularPhiPoleIndices M (m + 1) n z τ = ∅ := by
    ext k
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hk, hz⟩
    have hclear := hu.2.2.2.2.2.2 k hk
    change x + max 0 (-(modularPhiPolePoint M (m + 1) n τ k.1 k.2).im - 1) *
      Real.tan ψ < (modularPhiPolePoint M (m + 1) n τ k.1 k.2).re at hclear
    rw [← hz] at hclear
    exact (not_lt_of_ge hgraph) hclear
  simp [modularPhiPoleMultiplicity, hind]

private theorem bent_point_on_graph (x ψ r : ℝ) (hψ : 0 < ψ)
    (hψ' : ψ < Real.pi / 4) (hr : 0 ≤ r) :
    (g1BentLowerPoint x ψ r).re =
      x + max 0 (-(g1BentLowerPoint x ψ r).im - 1) * Real.tan ψ := by
  have hc : 0 < Real.cos ψ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  simp only [g1BentLowerPoint, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.I_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
    G1BilateralGeometryAux.lower_direction_re, Complex.add_im, Complex.sub_im,
    Complex.I_im, Complex.mul_im, G1BilateralGeometryAux.lower_direction_im, add_zero]
  have he : -(0 - 1 + r * -Real.cos ψ) - 1 = r * Real.cos ψ := by ring
  rw [he, max_eq_right (mul_nonneg hr hc.le), Real.tan_eq_sin_div_cos]
  field_simp

private theorem single_pullback_continuousOn (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell m : ℤ) (K : Set ((ℂ × ℂ) × ℝ)) (z j : ℝ → ℂ)
    (hz : Continuous z) (hj : Continuous j)
    (hreg : ∀ q ∈ K, (z q.2, q.1) ∈ singleRegular M n m) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℝ =>
      UpperWindow.singleKernel M m n h ell q.1.1 q.1.2 (z q.2) * j q.2) K := by
  intro q hq
  have hc := ((single_kernel_joint_analytic M hM n h ell m).2 _ (hreg q hq)).continuousAt
  have hmap : ContinuousAt (fun q : (ℂ × ℂ) × ℝ => (z q.2, q.1)) q :=
    ((hz.comp continuous_snd).prodMk continuous_fst).continuousAt
  exact ((hc.comp (f := fun q : (ℂ × ℂ) × ℝ => (z q.2, q.1)) hmap).mul
    (hj.comp continuous_snd).continuousAt).continuousWithinAt

private theorem single_full_majorants (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell m : ℤ) (x ψ : ℝ) (u : ℂ × ℂ)
    (hu : u ∈ singleAdmissible M n h ell m x ψ) :
    ∃ (U : Set (ℂ × ℂ)) (Bup Bdown : ℝ → ℝ), IsOpen U ∧ u ∈ U ∧
      IntegrableOn Bup (Ici (-1)) ∧ IntegrableOn Bdown (Ici 0) ∧
      (∀ t, 0 ≤ Bup t) ∧ (∀ r, 0 ≤ Bdown r) ∧
      ∀ v ∈ U,
        (∀ t ∈ Ici (-1), ‖g1VerticalPullback
          (UpperWindow.singleKernel M m n h ell v.1 v.2) x t‖ ≤ Bup t) ∧
        (∀ r ∈ Ici 0, ‖g1BentLowerPullback
          (UpperWindow.singleKernel M m n h ell v.1 v.2) x ψ r‖ ≤ Bdown r) := by
  obtain ⟨U, C, κ, a, B, R, hU, huU, hUa, hC, hκ, ha, hB, hR, ht⟩ :=
    single_joint_majorants M hM n h ell m x ψ u hu
  obtain ⟨ρ, hρ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds huU)
  let Kup : Set ((ℂ × ℂ) × ℝ) := Metric.closedBall u ρ ×ˢ Icc (-1) R
  let Kdown : Set ((ℂ × ℂ) × ℝ) := Metric.closedBall u ρ ×ˢ Icc 0 R
  have hregup : ∀ q ∈ Kup, (g1VerticalPoint x q.2, q.1) ∈ singleRegular M n m := by
    intro q hq
    apply single_regular_of_clear M q.1.1 q.1.2 (g1VerticalPoint x q.2)
      n h ell m x ψ (hUa (hsub hq.1))
    simp only [g1VerticalPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, mul_one,
      sub_zero, add_zero, Complex.add_im, Complex.mul_im]
    rw [max_eq_left (by linarith [hq.2.1])]
    simp
  have hregdown : ∀ q ∈ Kdown, (g1BentLowerPoint x ψ q.2, q.1) ∈ singleRegular M n m := by
    intro q hq
    exact single_regular_of_clear M q.1.1 q.1.2 (g1BentLowerPoint x ψ q.2)
      n h ell m x ψ (hUa (hsub hq.1))
      (bent_point_on_graph x ψ q.2 hu.2.2.1 hu.2.2.2.1 hq.2.1).le
  have hcup : ContinuousOn (fun q : (ℂ × ℂ) × ℝ => g1VerticalPullback
      (UpperWindow.singleKernel M m n h ell q.1.1 q.1.2) x q.2) Kup := by
    exact single_pullback_continuousOn M hM n h ell m Kup
      (g1VerticalPoint x) (fun _ => Complex.I)
      (by unfold g1VerticalPoint; fun_prop) continuous_const hregup
  have hcdown : ContinuousOn (fun q : (ℂ × ℂ) × ℝ => g1BentLowerPullback
      (UpperWindow.singleKernel M m n h ell q.1.1 q.1.2) x ψ q.2) Kdown := by
    exact single_pullback_continuousOn M hM n h ell m Kdown
      (g1BentLowerPoint x ψ) (fun _ => g1LowerDirection ψ)
      (by unfold g1BentLowerPoint; fun_prop) continuous_const hregdown
  obtain ⟨Cu, hCu⟩ := ((isCompact_closedBall u ρ).prod isCompact_Icc).exists_bound_of_continuousOn hcup
  obtain ⟨Cd, hCd⟩ := ((isCompact_closedBall u ρ).prod isCompact_Icc).exists_bound_of_continuousOn hcdown
  let D := max C (max Cu Cd)
  have hD : 0 < D := hC.trans_le (le_max_left _ _)
  obtain ⟨hup, hdown, hiup, hidown⟩ :=
    G1BilateralSingleTails.majorants_integrable D κ a B R hD.le hκ ha
  refine ⟨Metric.ball u ρ, G1BilateralSingleTails.upperMajorant D κ R,
    G1BilateralSingleTails.lowerMajorant D a B R, Metric.isOpen_ball,
    Metric.mem_ball_self hρ, hiup, hidown, hup, hdown, ?_⟩
  intro v hv
  have hvclosed := Metric.ball_subset_closedBall hv
  have hvU := hsub hvclosed
  constructor
  · intro t htmem
    dsimp only [G1BilateralSingleTails.upperMajorant]
    split_ifs with htR
    · exact (hCu (v, t) ⟨hvclosed, htmem, htR⟩).trans
        ((le_max_left Cu Cd).trans (le_max_right C _))
    · exact ((ht v hvU).1 t (le_of_not_ge htR)).trans
        (mul_le_mul_of_nonneg_right (le_max_left C _) (Real.exp_pos _).le)
  · intro r hrmem
    dsimp only [G1BilateralSingleTails.lowerMajorant]
    split_ifs with hrR
    · exact (hCd (v, r) ⟨hvclosed, hrmem, hrR⟩).trans
        ((le_max_right Cu Cd).trans (le_max_right C _))
    · exact ((ht v hvU).2 r (le_of_not_ge hrR)).trans
        (mul_le_mul_of_nonneg_right (le_max_left C _) (Real.exp_pos _).le)

/-- The finite family shares one neighborhood and two integrable majorants. -/
theorem real_single_joint_majorants (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ (U : Set (ℂ × ℂ)) (Bup Bdown : ℝ → ℝ),
      IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      IntegrableOn Bup (Ici (-1)) ∧ IntegrableOn Bdown (Ici 0) ∧
      ∀ u ∈ U, ∀ m ∈ Finset.range (M 1 0).toNat,
        (∀ t ∈ Ici (-1), ‖g1VerticalPullback
          (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) t‖ ≤ Bup t) ∧
        (∀ r ∈ Ici 0, ‖g1BentLowerPullback
          (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ r‖ ≤ Bdown r) := by
  have hex (m : Fin (M 1 0).toNat) :=
    single_full_majorants M hM n h ell (m : ℤ)
      (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ ((τ₀ : ℂ), (w : ℂ))
      (real_single_admissible M hM τ₀ w δ ψ n h ell (m : ℤ) hT hs hδ hψ hψ')
  choose U Bu Bd hU hc hiu hid hnu hnd hb using hex
  refine ⟨⋂ m, U m, fun t => ∑ m, Bu m t, fun r => ∑ m, Bd m r,
    isOpen_iInter_of_finite hU, mem_iInter.mpr hc, ?_, ?_, ?_⟩
  · exact integrable_finsetSum Finset.univ (fun m _ => hiu m)
  · exact integrable_finsetSum Finset.univ (fun m _ => hid m)
  · intro u hu m hm
    let i : Fin (M 1 0).toNat := ⟨m, Finset.mem_range.mp hm⟩
    have hbi := hb i u (mem_iInter.mp hu i)
    constructor
    · intro t ht
      exact (hbi.1 t ht).trans
        (Finset.single_le_sum (fun j _ => hnu j t) (Finset.mem_univ i))
    · intro r hr
      exact (hbi.2 r hr).trans
        (Finset.single_le_sum (fun j _ => hnd j r) (Finset.mem_univ i))

/-- Finite sums of the prescribed single integrals are jointly analytic. -/
theorem real_single_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      AnalyticOnNhd ℂ (fun u : ℂ × ℂ =>
        ∑ m ∈ Finset.range (M 1 0).toNat,
          g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
            (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) U ∧
      ∀ u ∈ U, ∀ m ∈ Finset.range (M 1 0).toNat,
        G1BentIntegrable (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ := by
  obtain ⟨U, hU, hc, hgeom⟩ :=
    real_bent_joint_geometry M hM τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  refine ⟨U, hU, hc, ?_, ?_⟩
  · have hsummand (m : ℕ) (hm : m ∈ Finset.range (M 1 0).toNat) :
        AnalyticOnNhd ℂ (fun u : ℂ × ℂ =>
          g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
            (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) U :=
      (single_bent_joint_analytic M hM n h ell (m : ℤ)
        (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ).2.1.mono (fun u hu => hgeom u hu m hm)
    simpa only [Finset.sum_apply] using
      Finset.analyticOnNhd_fun_sum (Finset.range (M 1 0).toNat) hsummand
  · intro u hu m hm
    exact (single_bent_joint_analytic M hM n h ell (m : ℤ)
      (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ).2.2 u (hgeom u hu m hm)

lemma ratio_regular_of_separates (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (x : Parameters) (n h ell p m : ℤ) (D : G1VerticalChain)
    (hτ : x.1 ∈ modularPhiDomain M)
    (hD : G1FixedSeparation.SeparatesAt D M x.1 x.2.2 n p m) :
    (∀ t : ℝ, (g1VerticalPoint D.crossing t, x) ∈ ratioRegular M n p m) ∧
      ∀ r ∈ D.centers, ∀ θ : ℝ,
        (circleMap (r : ℂ) (D.radius r) θ, x) ∈ ratioRegular M n p m := by
  have hr := G1FixedSeparation.separatesAt_regularDomain M hM x.1 x.2.1 x.2.2
    n h ell p m D hτ hD
  have hb (z : ℂ) (hz : (z, x.1) ∈ ModularCluster.regularDomain M
      (G1Pinch.ratioData x.2.1 x.2.2 n h ell p m)) :
      (z, x) ∈ ratioRegular M n p m := by
    rcases hz with ⟨hdom, hnum, hinv⟩
    exact ⟨⟨hdom, hnum⟩, hdom, hinv rfl⟩
  exact ⟨fun t => hb _ (hr.1 t), fun r hmem θ => hb _ (hr.2 r hmem θ)⟩

lemma ratio_vertical_joint_continuousAt (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p m : ℤ) (c t : ℝ) {x : Parameters}
    (hreg : (g1VerticalPoint c t, x) ∈ ratioRegular M n p m) :
    ContinuousAt (fun q : Parameters × ℝ => g1VerticalPullback
      (UpperWindow.ratioKernel M m n h ell p q.1.1 q.1.2.1 q.1.2.2) c q.2) (x, t) := by
  have hm : ContinuousAt (fun q : Parameters × ℝ => (g1VerticalPoint c q.2, q.1))
      (x, t) := by
    unfold g1VerticalPoint
    fun_prop
  exact (((ratio_kernel_joint_analytic M hM n h ell p m).2 _ hreg).continuousAt.comp
    (f := fun q : Parameters × ℝ => (g1VerticalPoint c q.2, q.1)) hm).mul
      continuousAt_const

lemma ratio_circle_joint_continuousAt (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p m : ℤ) (r ρ θ : ℝ) {x : Parameters}
    (hreg : (circleMap (r : ℂ) ρ θ, x) ∈ ratioRegular M n p m) :
    ContinuousAt (fun q : Parameters × ℝ => g1CirclePullback
      (UpperWindow.ratioKernel M m n h ell p q.1.1 q.1.2.1 q.1.2.2) r ρ q.2)
      (x, θ) := by
  have hm : ContinuousAt (fun q : Parameters × ℝ => (circleMap (r : ℂ) ρ q.2, q.1))
      (x, θ) :=
    (((continuous_circleMap (r : ℂ) ρ).comp continuous_snd).prodMk continuous_fst).continuousAt
  exact (((ratio_kernel_joint_analytic M hM n h ell p m).2 _ hreg).continuousAt.comp
    (f := fun q : Parameters × ℝ => (circleMap (r : ℂ) ρ q.2, q.1)) hm).mul
      (continuous_const.mul (((continuous_circleMap (r : ℂ) ρ).comp continuous_snd).sub
        continuous_const)).continuousAt

/-- Compact moving parameters and the finite family of circles share fixed bounds. -/
lemma ratio_compact_middle_circle_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (K : Set Parameters) (hK : IsCompact K)
    (hdom : ∀ x ∈ K, x.1 ∈ modularPhiDomain M)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ x ∈ K, ∀ m,
      G1FixedSeparation.SeparatesAt (D m) M x.1 x.2.2 n p (m : ℤ)) (R : ℝ) :
    ∃ Cmid Ccircle : ℝ, 0 < Cmid ∧ 0 < Ccircle ∧
      ∀ x ∈ K, ∀ m : Fin (M 1 0).toNat,
        (∀ t ∈ Icc (-R) R, ‖g1VerticalPullback
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
          (D m).crossing t‖ ≤ Cmid) ∧
        (∀ r ∈ (D m).centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖g1CirclePullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p
            x.1 x.2.1 x.2.2) r ((D m).radius r) θ‖ ≤ Ccircle) := by
  let fv : Fin (M 1 0).toNat → Parameters × ℝ → ℂ := fun m q =>
    g1VerticalPullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p
      q.1.1 q.1.2.1 q.1.2.2) (D m).crossing q.2
  have hcv : ∀ m ∈ Finset.univ, ContinuousOn (fv m) (K ×ˢ Icc (-R) R) := by
    intro m _ q hq
    exact (ratio_vertical_joint_continuousAt M hM n h ell p (m : ℤ)
      (D m).crossing q.2 ((ratio_regular_of_separates M hM q.1 n h ell p (m : ℤ)
        (D m) (hdom q.1 hq.1) (hD q.1 hq.1 m)).1 q.2)).continuousWithinAt
  obtain ⟨Cmid, hCmid, hmid⟩ := G1BilateralRatioTailsAux.finite_compact_bound
    Finset.univ (K ×ˢ Icc (-R) R) (hK.prod isCompact_Icc) fv hcv
  let ι := Σ m : Fin (M 1 0).toNat, {r : ℝ // r ∈ (D m).centers}
  let fc : ι → Parameters × ℝ → ℂ := fun i q =>
    g1CirclePullback (UpperWindow.ratioKernel M (i.1 : ℤ) n h ell p
      q.1.1 q.1.2.1 q.1.2.2) i.2.val ((D i.1).radius i.2.val) q.2
  have hcc : ∀ i ∈ Finset.univ, ContinuousOn (fc i) (K ×ˢ Icc 0 (2 * Real.pi)) := by
    intro i _ q hq
    exact (ratio_circle_joint_continuousAt M hM n h ell p (i.1 : ℤ) i.2.val
      ((D i.1).radius i.2.val) q.2
      ((ratio_regular_of_separates M hM q.1 n h ell p (i.1 : ℤ) (D i.1)
        (hdom q.1 hq.1) (hD q.1 hq.1 i.1)).2 i.2.val i.2.property q.2)).continuousWithinAt
  obtain ⟨Ccircle, hCcircle, hcircle⟩ := G1BilateralRatioTailsAux.finite_compact_bound
    Finset.univ (K ×ˢ Icc 0 (2 * Real.pi)) (hK.prod isCompact_Icc) fc hcc
  refine ⟨Cmid, Ccircle, hCmid, hCcircle, ?_⟩
  intro x hx m
  constructor
  · intro t ht
    exact hmid m (Finset.mem_univ m) (x, t) ⟨hx, ht⟩
  · intro r hr θ hθ
    exact hcircle ⟨m, r, hr⟩ (Finset.mem_univ _) (x, θ) ⟨hx, hθ⟩

lemma quotient_identity_neighborhood {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (z₀ : E) (good upper : Set E)
    (hne : NeBot (𝓝[upper] z₀)) (hupperOpen : IsOpen upper) (hsub : upper ⊆ good)
    (I P raw N Q : E → ℂ) (U : Set E) (hU : IsOpen U) (h₀ : z₀ ∈ U)
    (hI : AnalyticOnNhd ℂ I U) (hP : AnalyticOnNhd ℂ P U)
    (hN : AnalyticOnNhd ℂ N U) (hQ : AnalyticOnNhd ℂ Q U)
    (hchart : ∀ z ∈ U ∩ good, Q z ≠ 0 ∧ raw z = N z / Q z)
    (hident : ∀ z ∈ U ∩ upper, I z = P z * raw z) :
    ∃ V : Set E, IsOpen V ∧ z₀ ∈ V ∧
      ∀ z ∈ V ∩ good, I z = P z * raw z := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z₀ h₀
  let _ := hne
  obtain ⟨z, hzb, hzu⟩ := (Filter.Eventually.and
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hr))
    (self_mem_nhdsWithin (s := upper) (a := z₀))).exists
  have hgerm : (fun z => I z * Q z) =ᶠ[𝓝 z] (fun z => P z * N z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzb, hupperOpen.mem_nhds hzu] with v hvb hvu
    obtain ⟨hq, hv⟩ := hchart v ⟨hball hvb, hsub hvu⟩
    rw [hident v ⟨hball hvb, hvu⟩, hv]
    field_simp
  have heq := ((hI.mul hQ).mono hball).eqOn_of_preconnected_of_eventuallyEq
    ((hP.mul hN).mono hball) (convex_ball z₀ r).isPreconnected hzb hgerm
  refine ⟨Metric.ball z₀ r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
  rintro v ⟨hvb, hvg⟩
  obtain ⟨hq, hv⟩ := hchart v ⟨hball hvb, hvg⟩
  rw [hv, ← mul_div_assoc, eq_div_iff hq]
  exact heq hvb

lemma single_raw_joint_chart (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ell : ℤ) (u : ℂ × ℂ) (hu : u.1 ∈ modularPhiDomain M) :
    ∃ (U : Set (ℂ × ℂ)) (N Q : (ℂ × ℂ) → ℂ),
      IsOpen U ∧ u ∈ U ∧ AnalyticOnNhd ℂ N U ∧ AnalyticOnNhd ℂ Q U ∧
      ∀ v ∈ U ∩ singleGood M h ell, Q v ≠ 0 ∧ singleRaw M h ell v = N v / Q v := by
  let κ : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M ell (1 - h) j u.2 u.1).1
    (modularPhiFactorPoint M ell (1 - h) j u.2 u.1).2
  obtain ⟨V, hV, huV, hdom, hA, hD, _, _⟩ :=
    modularPhi_joint_local_quotient M hM ell (1 - h) (u.2, u.1) hu
  let N : (ℂ × ℂ) → ℂ := fun v => modularPhiChartDenominator M ell (1 - h) κ v.2 v.1
  let Q : (ℂ × ℂ) → ℂ := fun v => modularPhiChartNumerator M ell (1 - h) κ v.2 v.1
  refine ⟨Prod.swap ⁻¹' V, N, Q, hV.preimage continuous_swap, huV, ?_, ?_, ?_⟩
  · intro v hv
    exact (hD (v.2, v.1) hv).comp (f := Prod.swap) (x := v) (analyticAt_snd.prod analyticAt_fst)
  · intro v hv
    exact (hA (v.2, v.1) hv).comp (f := Prod.swap) (x := v) (analyticAt_snd.prod analyticAt_fst)
  · rintro v ⟨hv, hgood⟩
    have heq : modularPhi M ell (1 - h) v.2 v.1 = Q v / N v :=
      modularPhi_eq_chart M hM ell (1 - h) κ (v.2, v.1) (hdom hv)
    have hne := (modularPhi_ne_zero_iff M hM ell (1 - h) v.2 v.1
      hgood.1 hgood.2.1).mpr hgood.2.2
    rw [heq] at hne
    refine ⟨(div_ne_zero_iff.mp hne).1, ?_⟩
    simp only [singleRaw, heq, inv_div]

lemma ratio_raw_joint_chart (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ell p : ℤ) (x : Parameters) (hx : x.1 ∈ modularPhiDomain M) :
    ∃ (U : Set Parameters) (N Q : Parameters → ℂ),
      IsOpen U ∧ x ∈ U ∧ AnalyticOnNhd ℂ N U ∧ AnalyticOnNhd ℂ Q U ∧
      ∀ v ∈ U ∩ ratioGood M h ell p, Q v ≠ 0 ∧ ratioRaw M h ell p v = N v / Q v := by
  let ka : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M (p + ell) (-h) j (x.2.1 + x.2.2) x.1).1
    (modularPhiFactorPoint M (p + ell) (-h) j (x.2.1 + x.2.2) x.1).2
  let kb : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M p 0 j x.2.2 x.1).1
    (modularPhiFactorPoint M p 0 j x.2.2 x.1).2
  let kc : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M ell (1 - h) j x.2.1 x.1).1
    (modularPhiFactorPoint M ell (1 - h) j x.2.1 x.1).2
  obtain ⟨Va, hVa, hxa, hda, hAa, hDa, _, _⟩ :=
    modularPhi_joint_local_quotient M hM (p + ell) (-h) (x.2.1 + x.2.2, x.1) hx
  obtain ⟨Vb, hVb, hxb, hdb, hAb, hDb, _, _⟩ :=
    modularPhi_joint_local_quotient M hM p 0 (x.2.2, x.1) hx
  obtain ⟨Vc, hVc, hxc, hdc, hAc, hDc, _, _⟩ :=
    modularPhi_joint_local_quotient M hM ell (1 - h) (x.2.1, x.1) hx
  let fa : Parameters → ℂ × ℂ := fun v => (v.2.1 + v.2.2, v.1)
  let fb : Parameters → ℂ × ℂ := fun v => (v.2.2, v.1)
  let fc : Parameters → ℂ × ℂ := fun v => (v.2.1, v.1)
  let U := fa ⁻¹' Va ∩ (fb ⁻¹' Vb ∩ fc ⁻¹' Vc)
  let Aa : Parameters → ℂ := fun v => modularPhiChartNumerator M (p + ell) (-h) ka (fa v).1 (fa v).2
  let Da : Parameters → ℂ := fun v => modularPhiChartDenominator M (p + ell) (-h) ka (fa v).1 (fa v).2
  let Ab : Parameters → ℂ := fun v => modularPhiChartNumerator M p 0 kb (fb v).1 (fb v).2
  let Db : Parameters → ℂ := fun v => modularPhiChartDenominator M p 0 kb (fb v).1 (fb v).2
  let Ac : Parameters → ℂ := fun v => modularPhiChartNumerator M ell (1 - h) kc (fc v).1 (fc v).2
  let Dc : Parameters → ℂ := fun v => modularPhiChartDenominator M ell (1 - h) kc (fc v).1 (fc v).2
  have hw : ∀ v, AnalyticAt ℂ (fun v : Parameters => v.2.1) v := fun v =>
    analyticAt_fst.comp (f := fun v : Parameters => v.2) (x := v) analyticAt_snd
  have hy : ∀ v, AnalyticAt ℂ (fun v : Parameters => v.2.2) v := fun v =>
    analyticAt_snd.comp (f := fun v : Parameters => v.2) (x := v) analyticAt_snd
  have hfa : ∀ v, AnalyticAt ℂ fa v := fun v => ((hw v).add (hy v)).prod analyticAt_fst
  have hfb : ∀ v, AnalyticAt ℂ fb v := fun v => (hy v).prod analyticAt_fst
  have hfc : ∀ v, AnalyticAt ℂ fc v := fun v => (hw v).prod analyticAt_fst
  have hAa' : AnalyticOnNhd ℂ Aa U := fun v hv => (hAa _ hv.1).comp (f := fa) (x := v) (hfa v)
  have hDa' : AnalyticOnNhd ℂ Da U := fun v hv => (hDa _ hv.1).comp (f := fa) (x := v) (hfa v)
  have hAb' : AnalyticOnNhd ℂ Ab U := fun v hv => (hAb _ hv.2.1).comp (f := fb) (x := v) (hfb v)
  have hDb' : AnalyticOnNhd ℂ Db U := fun v hv => (hDb _ hv.2.1).comp (f := fb) (x := v) (hfb v)
  have hAc' : AnalyticOnNhd ℂ Ac U := fun v hv => (hAc _ hv.2.2).comp (f := fc) (x := v) (hfc v)
  have hDc' : AnalyticOnNhd ℂ Dc U := fun v hv => (hDc _ hv.2.2).comp (f := fc) (x := v) (hfc v)
  refine ⟨U, fun v => Aa v * Db v * Dc v, fun v => Da v * Ab v * Ac v,
    (hVa.preimage (by dsimp [fa]; fun_prop)).inter
      ((hVb.preimage (by dsimp [fb]; fun_prop)).inter
        (hVc.preimage (by dsimp [fc]; fun_prop))),
    ⟨hxa, hxb, hxc⟩, (hAa'.mul hDb').mul hDc', (hDa'.mul hAb').mul hAc', ?_⟩
  rintro v ⟨hv, hgood⟩
  have hea : modularPhi M (p + ell) (-h) (v.2.1 + v.2.2) v.1 = Aa v / Da v :=
    modularPhi_eq_chart M hM (p + ell) (-h) ka (fa v) (hda hv.1)
  have heb : modularPhi M p 0 v.2.2 v.1 = Ab v / Db v :=
    modularPhi_eq_chart M hM p 0 kb (fb v) (hdb hv.2.1)
  have hec : modularPhi M ell (1 - h) v.2.1 v.1 = Ac v / Dc v :=
    modularPhi_eq_chart M hM ell (1 - h) kc (fc v) (hdc hv.2.2)
  have hna := (modularPhi_ne_zero_iff M hM (p + ell) (-h) (v.2.1 + v.2.2) v.1
    hgood.1.1 hgood.1.2.1).mpr hgood.1.2.2
  have hnb := (modularPhi_ne_zero_iff M hM p 0 v.2.2 v.1
    hgood.2.1.1 hgood.2.1.2.1).mpr hgood.2.1.2.2
  have hnc := (modularPhi_ne_zero_iff M hM ell (1 - h) v.2.1 v.1
    hgood.2.2.1 hgood.2.2.2.1).mpr hgood.2.2.2.2
  rw [hea] at hna
  rw [heb] at hnb
  rw [hec] at hnc
  refine ⟨mul_ne_zero (mul_ne_zero (div_ne_zero_iff.mp hna).2
    (div_ne_zero_iff.mp hnb).1) (div_ne_zero_iff.mp hnc).1, ?_⟩
  simp only [ratioRaw, hea, heb, hec]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma upper_prefactor_eq_etaPhase (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) : UpperResidueParameters.prefactor M τ = etaPhase M τ := by
  have hη := ModularCocycleUpperAux.etaMobius_im_pos M hτ
  have hd : qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) ≠ 0 :=
    qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _))
      (norm_e_lt_one ⟨etaMobius M τ, hη⟩)
  simpa only [UpperResidueParameters.prefactor, mul_div_assoc] using
    qPochhammer_eta_prefactor M hM (⟨τ, hτ⟩ : UpperHalfPlane) hd

open G1BilateralRatioTailsAux

lemma ratio_phase_continuous (M : SL(2, ℤ)) (n h ell p m : ℤ) (lower : Bool)
    {x : Parameters} (hx : x.1 ∈ modularPhiDomain M) :
    ContinuousAt (fun v : Parameters =>
      phaseConstant M v.1 v.2.1 v.2.2 n h ell p m lower) x := by
  have hT : etaDenom M x.1 ≠ 0 := etaDenom_ne_zero_of_mem M hx
  have hd : ContinuousAt (fun v : Parameters => etaDenom M v.1) x := by
    unfold etaDenom
    fun_prop
  have hm : ContinuousAt (fun v : Parameters => etaMobius M v.1) x := by
    unfold etaMobius
    exact ((continuous_const.mul continuous_fst).add continuous_const).continuousAt.div hd hT
  have hP (r : ℤ) : ContinuousAt (fun v : Parameters =>
      modularReflectionPolynomial M r n v.2.2 v.1) x := by
    unfold modularReflectionPolynomial
    fun_prop
  have hP0 (r : ℤ) : ContinuousAt (fun v : Parameters =>
      modularReflectionPolynomial M r n 0 v.1) x := by
    unfold modularReflectionPolynomial
    fun_prop
  have hE : ContinuousAt (fun v : Parameters => g1Exponent M v.1 v.2.1 0 n h ell m) x := by
    unfold g1Exponent
    fun_prop
  cases lower
  · simpa [phaseConstant] using hE
  · exact ((hP0 (m + 1)).sub (hP (m + p))).add hE

lemma ratio_slope_continuous (M : SL(2, ℤ)) (h ell p : ℤ) (lower : Bool)
    {x : Parameters} (hx : x.1 ∈ modularPhiDomain M) :
    ContinuousAt (fun v : Parameters =>
      (if lower then G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p
       else G1RatioTail.complexS M v.1 v.2.1 h ell) / etaDenom M v.1) x := by
  have hT : etaDenom M x.1 ≠ 0 := etaDenom_ne_zero_of_mem M hx
  have hd : ContinuousAt (fun v : Parameters => etaDenom M v.1) x := by
    unfold etaDenom
    fun_prop
  have hs : ContinuousAt (fun v : Parameters => G1RatioTail.complexS M v.1 v.2.1 h ell) x := by
    unfold G1RatioTail.complexS
    exact ((continuousAt_const.mul (continuous_fst.comp continuous_snd).continuousAt).add
      continuousAt_const).add (continuousAt_const.mul hd)
  cases lower
  · exact hs.div hd hT
  · exact ((hs.add (continuousAt_const.mul
      (continuous_snd.comp continuous_snd).continuousAt)).add
        (continuousAt_const.mul hd)).div hd hT

lemma ratio_compact_affine_phase_bound (M : SL(2, ℤ)) (n h ell p : ℤ)
    (F : Finset ℤ) (K : Set Parameters) (hK : IsCompact K)
    (hdom : ∀ x ∈ K, x.1 ∈ modularPhiDomain M) (a b : ℝ) (lower : Bool) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, ∀ m ∈ F, ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖e (((if lower then G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p
        else G1RatioTail.complexS M x.1 x.2.1 h ell) / etaDenom M x.1) *
          g1VerticalPoint c t + phaseConstant M x.1 x.2.1 x.2.2 n h ell p m lower)‖ ≤
        B * Real.exp (-(2 * Real.pi *
          ((if lower then G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p
            else G1RatioTail.complexS M x.1 x.2.1 h ell) / etaDenom M x.1).re) * t) := by
  let A : Parameters → ℂ := fun x =>
    (if lower then G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p
      else G1RatioTail.complexS M x.1 x.2.1 h ell) / etaDenom M x.1
  let f : ℤ → (Parameters × ℝ) → ℂ := fun m q =>
    e (A q.1 * (q.2 : ℂ) + phaseConstant M q.1.1 q.1.2.1 q.1.2.2 n h ell p m lower)
  have hf : ∀ m ∈ F, ContinuousOn (f m) (K ×ˢ Icc a b) := by
    intro m hm
    have hA : ContinuousOn A K := fun x hx =>
      (ratio_slope_continuous M h ell p lower (hdom x hx)).continuousWithinAt
    have hB : ContinuousOn (fun x : Parameters =>
        phaseConstant M x.1 x.2.1 x.2.2 n h ell p m lower) K := fun x hx =>
      (ratio_phase_continuous M n h ell p m lower (hdom x hx)).continuousWithinAt
    have hA' : ContinuousOn (fun q : Parameters × ℝ => A q.1) (K ×ˢ Icc a b) :=
      hA.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hB' : ContinuousOn (fun q : Parameters × ℝ =>
        phaseConstant M q.1.1 q.1.2.1 q.1.2.2 n h ell p m lower) (K ×ˢ Icc a b) :=
      hB.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hx : Continuous (fun q : Parameters × ℝ => (q.2 : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_snd
    have he : Continuous e := by unfold e; fun_prop
    exact he.comp_continuousOn ((hA'.mul hx.continuousOn).add hB')
  obtain ⟨B, hB, hb⟩ := finite_compact_bound F (K ×ˢ Icc a b)
    (hK.prod isCompact_Icc) f hf
  refine ⟨B, hB, ?_⟩
  intro x hx m hm c hc t
  rw [norm_e_vertical]
  exact mul_le_mul_of_nonneg_right (hb m hm (x, c) ⟨hx, hc⟩) (Real.exp_pos _).le

lemma ratio_compact_window_margin (M : SL(2, ℤ)) (h ell p : ℤ)
    (K : Set Parameters) (hK : IsCompact K)
    (hdom : ∀ x ∈ K, x.1 ∈ modularPhiDomain M)
    (hwin : ∀ x ∈ K, x.2 ∈ strictRatioWindow M x.1 h ell p) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ K,
      κ ≤ 2 * Real.pi * (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1).re ∧
      κ ≤ -(2 * Real.pi *
        (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1).re) := by
  let f : Parameters → ℝ := fun x => min
    (2 * Real.pi * (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1).re)
    (-(2 * Real.pi *
      (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1).re))
  have hf : ContinuousOn f K := by
    intro x hx
    have hS : ContinuousAt (fun v : Parameters =>
        (G1RatioTail.complexS M v.1 v.2.1 h ell / etaDenom M v.1).re) x :=
      Complex.continuous_re.continuousAt.comp
        (ratio_slope_continuous M h ell p false (hdom x hx))
    have hL : ContinuousAt (fun v : Parameters =>
        (G1RatioTail.complexL M v.1 v.2.1 v.2.2 h ell p / etaDenom M v.1).re) x :=
      Complex.continuous_re.continuousAt.comp
        (ratio_slope_continuous M h ell p true (hdom x hx))
    have hc : ContinuousAt f x :=
      (continuousAt_const.mul hS).min (continuousAt_const.mul hL).neg
    exact hc.continuousWithinAt
  have hp : ∀ x ∈ K, 0 < f x := by
    intro x hx
    obtain ⟨hS, hL⟩ := hwin x hx
    exact lt_min (mul_pos (by positivity) hS) (by nlinarith [Real.pi_pos])
  obtain ⟨κ, hκ, hb⟩ := hK.exists_forall_le' hf hp
  refine ⟨κ, hκ, fun x hx => ⟨?_, ?_⟩⟩
  · exact (hb x hx).trans (min_le_left _ _)
  · exact (hb x hx).trans (min_le_right _ _)

lemma ratio_bounded_shift_estimates (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (n p : ℤ) (τ₀ α A : ℝ) (hT : 0 < g1T M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) (hA : 0 ≤ A) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F, ∀ y : ℂ, ‖y‖ ≤ A →
        (∀ z ∈ ModularSector.upperSector α R,
          let q := modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ
          ‖q - 1‖ + ‖q⁻¹ - 1‖ ≤ C * Real.exp (-k * ‖z‖)) ∧
        (∀ z : ℂ, -z ∈ ModularSector.upperSector α R →
          let q := modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ
          let a := modularReflectionFactor M (m + 1) n z τ /
            modularReflectionFactor M (m + p) n (z + y) τ
          ‖q / a - 1‖ + ‖a * q⁻¹ - 1‖ ≤ C * Real.exp (-k * ‖z‖)) := by
  obtain ⟨ρ, C, k, R, hρ, hC, hk, hR, _, _, hest⟩ :=
    ModularSector.bounded_shift_ratio_decay M hM (G1BilateralGeometry.indexFamily F n p)
      τ₀ α A hT hα hα' hA
  refine ⟨ρ, C, k, R, hρ, hC, hk, hR, ?_⟩
  intro τ hτ m hm y hy
  have hi : (m + 1, n) ∈ G1BilateralGeometry.indexFamily F n p :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have hj : (m + p, n) ∈ G1BilateralGeometry.indexFamily F n p :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  exact hest τ hτ (m + 1, n) hi (m + p, n) hj y hy

lemma ratio_compact_tail_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (F : Finset ℤ) (K : Set Parameters) (hK : IsCompact K)
    (hdom : ∀ x ∈ K, x.1 ∈ modularPhiDomain M)
    (A α Rs Cs k Rt κ : ℝ) (hCs : 0 < Cs) (hk : 0 < k)
    (hsector : ∀ c ∈ Icc (-A) A, ∀ t : ℝ, Rs ≤ t →
      g1VerticalPoint c t ∈ ModularSector.upperSector α (t / 2))
    (hdec : ∀ x ∈ K, ∀ m ∈ F,
      (∀ z ∈ ModularSector.upperSector α Rt,
        ‖modularPhi M (m + 1) n z x.1 / modularPhi M (m + p) n (z + x.2.2) x.1 - 1‖ +
          ‖(modularPhi M (m + 1) n z x.1 /
            modularPhi M (m + p) n (z + x.2.2) x.1)⁻¹ - 1‖ ≤ Cs * Real.exp (-k * ‖z‖)) ∧
      (∀ z : ℂ, -z ∈ ModularSector.upperSector α Rt →
        let q := modularPhi M (m + 1) n z x.1 / modularPhi M (m + p) n (z + x.2.2) x.1
        let a := modularReflectionFactor M (m + 1) n z x.1 /
          modularReflectionFactor M (m + p) n (z + x.2.2) x.1
        ‖q / a - 1‖ + ‖a * q⁻¹ - 1‖ ≤ Cs * Real.exp (-k * ‖z‖)))
    (lower : Bool)
    (hmargin : ∀ x ∈ K, κ ≤ if lower then -(2 * Real.pi *
        (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1).re)
      else 2 * Real.pi * (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1).re) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ m ∈ F, ∀ c ∈ Icc (-A) A,
      ∀ t : ℝ, max Rs (2 * Rt) ≤ |t| → (if lower then t ≤ 0 else 0 ≤ t) →
        ‖G1RatioTail.complexKernel M x.1 x.2.1 x.2.2 n h ell p m
          (g1VerticalPoint c t)‖ ≤ C * Real.exp (-κ * |t|) := by
  obtain ⟨B, hB, hphase⟩ :=
    ratio_compact_affine_phase_bound M n h ell p F K hK hdom (-A) A lower
  refine ⟨(Cs + 1) * B, by positivity, ?_⟩
  intro x hx m hm c hc t ht hsign
  have hc' : -c ∈ Icc (-A) A := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hmag : 2 * Rt ≤ |t| := (le_max_right Rs (2 * Rt)).trans ht
  have hmagS : Rs ≤ |t| := (le_max_left Rs (2 * Rt)).trans ht
  have hz : (if lower then -g1VerticalPoint c t else g1VerticalPoint c t) ∈
      ModularSector.upperSector α Rt := by
    cases lower
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      rw [abs_of_nonneg hsign] at hmag hmagS
      exact ModularSector.upperSector_antitone le_rfl (by linarith)
        (hsector c hc t hmagS)
    · simp only [↓reduceIte] at hsign ⊢
      rw [abs_of_nonpos hsign] at hmag hmagS
      have he : -g1VerticalPoint c t = g1VerticalPoint (-c) (-t) := by
        simp [g1VerticalPoint]
        ring
      rw [he]
      exact ModularSector.upperSector_antitone le_rfl (by linarith)
        (hsector (-c) hc' (-t) hmagS)
  let z := g1VerticalPoint c t
  let Q := modularPhi M (m + 1) n z x.1 / modularPhi M (m + p) n (z + x.2.2) x.1
  let V := modularReflectionFactor M (m + 1) n z x.1 /
    modularReflectionFactor M (m + p) n (z + x.2.2) x.1
  have hq : ‖(if lower then Q / V else Q)‖ ≤ Cs + 1 := by
    have he := hdec x hx m hm
    have hexp : Cs * Real.exp (-k * ‖z‖) ≤ Cs := by
      calc _ ≤ Cs * 1 := mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg z])) hCs.le
           _ = Cs := mul_one _
    cases lower
    · have heq : ‖Q - 1‖ ≤ Cs :=
        (le_trans (le_add_of_nonneg_right (norm_nonneg _)) (he.1 z hz)).trans hexp
      have hn := norm_le_norm_sub_add Q 1
      simp only [norm_one] at hn
      change ‖Q‖ ≤ Cs + 1
      linarith
    · have hb := he.2 z hz
      have hn := norm_le_norm_sub_add (Q / V) 1
      have heq : ‖Q / V - 1‖ ≤ Cs :=
        (le_trans (le_add_of_nonneg_right (norm_nonneg _)) hb).trans hexp
      change ‖Q / V‖ ≤ Cs + 1
      simp only [norm_one] at hn
      linarith
  let S := (if lower then G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p
    else G1RatioTail.complexS M x.1 x.2.1 h ell) / etaDenom M x.1
  have hker : ‖G1RatioTail.complexKernel M x.1 x.2.1 x.2.2 n h ell p m z‖ =
      ‖(if lower then Q / V else Q)‖ *
        ‖e (S * z + phaseConstant M x.1 x.2.1 x.2.2 n h ell p m lower)‖ := by
    have hT' : etaDenom M x.1 ≠ 0 := etaDenom_ne_zero_of_mem M (hdom x hx)
    cases lower
    · rw [kernel_eq, norm_mul, G1RatioTail.exponent_affine M x.1 x.2.1 z n h ell m hT']
      simp only [S, Q, phaseConstant, Bool.false_eq_true, ↓reduceIte, zero_add]
    · rw [norm_lower_kernel M hM x.1 x.2.1 x.2.2 z n h ell p m (hdom x hx),
        lower_phase_affine M x.1 x.2.1 x.2.2 z n h ell p m hT']
      rfl
  have hexponent : -(2 * Real.pi * S.re) * t ≤ -κ * |t| := by
    have hmar := hmargin x hx
    cases lower
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign hmar
      rw [abs_of_nonneg hsign]
      dsimp only [S]
      simpa only [Bool.false_eq_true, ↓reduceIte, neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right hmar hsign)
    · simp only [↓reduceIte] at hsign hmar
      rw [abs_of_nonpos hsign]
      dsimp only [S]
      simp only [↓reduceIte]
      nlinarith [mul_le_mul_of_nonpos_right hmar hsign]
  rw [hker]
  calc
    _ ≤ (Cs + 1) * (B * Real.exp (-(2 * Real.pi * S.re) * t)) :=
      mul_le_mul hq (hphase x hx m hm c hc t) (norm_nonneg _) (by positivity)
    _ ≤ (Cs + 1) * B * Real.exp (-κ * |t|) := by
      calc _ = ((Cs + 1) * B) * Real.exp (-(2 * Real.pi * S.re) * t) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
             (mul_nonneg (by linarith) hB.le)

lemma real_ratio_joint_majorants_of_geometry (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (D : Fin (M 1 0).toNat → G1VerticalChain) (x₀ : Parameters)
    (hcenter : x₀.1 = (τ₀ : ℂ))
    (V : Set Parameters) (hV : IsOpen V) (hx₀ : x₀ ∈ V)
    (hgeom : ∀ x ∈ V, x.1 ∈ modularPhiDomain M ∧ 0 < (etaDenom M x.1).re ∧
      x.2 ∈ ratioFiber M x.1 n h ell p ∧
      ∀ m, G1FixedSeparation.SeparatesAt (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ∃ (U : Set Parameters) (B : ℝ → ℝ) (C : ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ Integrable B ∧ 0 < C ∧
      ∀ x ∈ U, ∀ m : Fin (M 1 0).toNat,
        (∀ t : ℝ, ‖g1VerticalPullback
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
          (D m).crossing t‖ ≤ B t) ∧
        (∀ r ∈ (D m).centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖g1CirclePullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p
            x.1 x.2.1 x.2.2) r ((D m).radius r) θ‖ ≤ C) := by
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hx₀)
  let K₀ := Metric.closedBall x₀ (ε / 2)
  have hK₀ : IsCompact K₀ := isCompact_closedBall _ _
  have hK₀V : K₀ ⊆ V :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεV
  obtain ⟨Ay, hAy⟩ := hK₀.exists_bound_of_continuousOn
    ((continuous_snd.comp continuous_snd : Continuous (fun x : Parameters => x.2.2)).continuousOn)
  let A := ∑ m : Fin (M 1 0).toNat, |(D m).crossing|
  have hcross (m : Fin (M 1 0).toNat) : (D m).crossing ∈ Icc (-A) A := by
    have hm : |(D m).crossing| ≤ A := Finset.single_le_sum
      (fun m _ => abs_nonneg (D m).crossing) (Finset.mem_univ m)
    exact abs_le.mp hm
  let F : Finset ℤ := Finset.univ.image (fun m : Fin (M 1 0).toNat => (m : ℤ))
  have hF (m : Fin (M 1 0).toNat) : (m : ℤ) ∈ F :=
    Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
  obtain ⟨α, Rs, hα, hα', hRs, hsector⟩ := G1BilateralGeometry.upper_strip_sector (-A) A
  obtain ⟨ρs, Cs, k, Rt, hρs, hCs, hk, hRt, hdec⟩ :=
    ratio_bounded_shift_estimates M hM F n p τ₀ α (max Ay 0) hT hα hα' (le_max_right _ _)
  let K : Set Parameters := K₀ ∩ (fun x : Parameters => x.1) ⁻¹'
    ModularSector.parameterDisk τ₀ ρs
  have hK : IsCompact K := hK₀.inter_right
    (Metric.isClosed_closedBall.preimage continuous_fst)
  have hKnhds : K ∈ 𝓝 x₀ := by
    apply inter_mem
    · exact Metric.closedBall_mem_nhds _ (half_pos hε)
    · apply continuous_fst.continuousAt.preimage_mem_nhds
      rw [hcenter]
      exact disk_nhds τ₀ ρs hρs
  have hKV : K ⊆ V := fun x hx => hK₀V hx.1
  have hdom : ∀ x ∈ K, x.1 ∈ modularPhiDomain M := fun x hx => (hgeom x (hKV hx)).1
  have hseparate : ∀ x ∈ K, ∀ m,
      G1FixedSeparation.SeparatesAt (D m) M x.1 x.2.2 n p (m : ℤ) :=
    fun x hx => (hgeom x (hKV hx)).2.2.2
  obtain ⟨κ, hκ, hmargin⟩ := ratio_compact_window_margin M h ell p K hK hdom
    (fun x hx => (hgeom x (hKV hx)).2.2.1.1)
  have hdecK := fun x (hx : x ∈ K) m (hm : m ∈ F) =>
    hdec x.1 hx.2 m hm x.2.2 ((hAy x hx.1).trans (le_max_left _ _))
  obtain ⟨Cup, hCup, hup⟩ := ratio_compact_tail_bound M hM n h ell p F K hK hdom
    A α Rs Cs k Rt κ hCs hk hsector hdecK false (fun x hx => (hmargin x hx).1)
  obtain ⟨Cdown, hCdown, hdown⟩ := ratio_compact_tail_bound M hM n h ell p F K hK hdom
    A α Rs Cs k Rt κ hCs hk hsector hdecK true (fun x hx => (hmargin x hx).2)
  let R := max Rs (2 * Rt)
  obtain ⟨Cmid, Ccircle, hCmid, hCcircle, hcompact⟩ :=
    ratio_compact_middle_circle_bound M hM n h ell p K hK hdom D hseparate R
  let Ct := max Cup Cdown
  let C := max Ct Cmid
  refine ⟨interior K, G1BilateralRatioTails.verticalMajorant C κ R, Ccircle,
    isOpen_interior, mem_interior_iff_mem_nhds.mpr hKnhds,
    interior_subset.trans hKV, abs_majorant_integrable C κ R hκ, hCcircle, ?_⟩
  intro x hx m
  have hxK : x ∈ K := interior_subset hx
  refine ⟨?_, (hcompact x hxK m).2⟩
  intro t
  by_cases hmid : |t| ≤ R
  · rw [G1BilateralRatioTails.verticalMajorant, if_pos hmid]
    exact ((hcompact x hxK m).1 t (abs_le.mp hmid)).trans (le_max_right _ _)
  · rw [G1BilateralRatioTails.verticalMajorant, if_neg hmid,
      (existing_kernel_bridges M x.1 x.2.1 x.2.2 n h ell p (m : ℤ)).2,
      norm_vertical]
    have hb : ‖G1RatioTail.complexKernel M x.1 x.2.1 x.2.2 n h ell p (m : ℤ)
        (g1VerticalPoint (D m).crossing t)‖ ≤ Ct * Real.exp (-κ * |t|) := by
      rcases le_total 0 t with ht | ht
      · exact (hup x hxK (m : ℤ) (hF m) (D m).crossing (hcross m) t
          (le_of_not_ge hmid) ht).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      · exact (hdown x hxK (m : ℤ) (hF m) (D m).crossing (hcross m) t
          (le_of_not_ge hmid) ht).trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

theorem real_ratio_joint_majorants (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ (U : Set Parameters) (B : ℝ → ℝ) (C : ℝ),
      IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧ Integrable B ∧ 0 < C ∧
      ∀ x ∈ U, ∀ m : Fin (M 1 0).toNat,
        (∀ t : ℝ, ‖g1VerticalPullback
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
          (D m).crossing t‖ ≤ B t) ∧
        (∀ r ∈ (D m).centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖g1CirclePullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p
            x.1 x.2.1 x.2.2) r ((D m).radius r) θ‖ ≤ C) := by
  obtain ⟨V, hV, hx, hgeom⟩ := real_ratio_joint_geometry M hM τ₀ w y n h ell p hT hs hL D hD
  obtain ⟨U, B, C, hU, hxU, _, hB, hC, hbound⟩ :=
    real_ratio_joint_majorants_of_geometry M hM τ₀ n h ell p hT D
      ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) rfl V hV hx hgeom
  exact ⟨U, B, C, hU, hxU, hB, hC, hbound⟩

lemma differentiableOn_analyticOnNhd_three {f : (ℂ × ℂ × ℂ) → ℂ}
    {s : Set (ℂ × ℂ × ℂ)} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s := by
  intro p hp
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hp)
  exact ModularClusterIntegralsAux.analyticAt_of_differentiableOn_closedBall_three
    (hf.mono hrs) hr

lemma integral_joint_analytic_of_domination
    {μ : Measure ℝ} {F : (ℂ × ℂ × ℂ) → ℝ → ℂ}
    {c : ℂ × ℂ × ℂ} {R : ℝ} {B : ℝ → ℝ}
    (hR : 0 < R)
    (hm : ∀ q ∈ Metric.closedBall c R, AEStronglyMeasurable (F q) μ)
    (hdm : ∀ q ∈ Metric.closedBall c R,
      AEStronglyMeasurable (fun t => fderiv ℂ (fun v => F v t) q) μ)
    (hh : ∀ t, AnalyticOnNhd ℂ (fun q => F q t) (Metric.closedBall c R))
    (hB : ∀ᵐ t ∂μ, ∀ q ∈ Metric.closedBall c R, ‖F q t‖ ≤ B t)
    (hBi : Integrable B μ) :
    AnalyticOnNhd ℂ (fun q => ∫ t, F q t ∂μ)
      (Metric.closedBall c (R / 2)) := by
  have hd : DifferentiableOn ℂ (fun q => ∫ t, F q t ∂μ) (Metric.ball c R) := by
    intro q hq
    let r := (R - dist q c) / 4
    have hr : 0 < r := by
      dsimp [r]
      exact div_pos (sub_pos.mpr hq) (by norm_num)
    have hsub : Metric.ball q (2*r) ⊆ Metric.closedBall c R := by
      intro v hv
      simp only [Metric.mem_ball] at hq hv
      simp only [Metric.mem_closedBall]
      have htri := dist_triangle v q c
      dsimp [r] at hv
      linarith
    have hqc : q ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hq
    have hint : Integrable (F q) μ :=
      hBi.mono' (hm q hqc) (hB.mono fun t ht => ht q hqc)
    have hmeas : ∀ᶠ v in 𝓝 q, AEStronglyMeasurable (F v) μ := by
      filter_upwards [Metric.ball_mem_nhds q (show 0 < 2*r by positivity)] with v hv
      exact hm v (hsub hv)
    have hbound : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball q r,
        ‖fderiv ℂ (fun u => F u t) v‖ ≤ (2 * B t) / r := by
      filter_upwards [hB] with t ht v hv
      exact joint_norm_fderiv_le_of_ball_bound hr hv
        ((hh t).differentiableOn.mono hsub)
        (fun u hu => ht u (hsub hu))
    have hdiff : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball q r,
        HasFDerivAt (fun u => F u t) (fderiv ℂ (fun u => F u t) v) v := by
      exact Eventually.of_forall fun t v hv =>
        (hh t v (hsub (Metric.ball_subset_ball (by linarith) hv))).differentiableAt.hasFDerivAt
    exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds q hr) hmeas hint (hdm q hqc) hbound
      ((hBi.const_mul 2).div_const r) hdiff).differentiableAt.differentiableWithinAt
  exact (differentiableOn_analyticOnNhd_three hd Metric.isOpen_ball).mono
    (Metric.closedBall_subset_ball (by linarith))

lemma continuous_parameter_fderiv_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : ℂ × E → ℂ} {z j : ℝ → ℂ} {q : E}
    (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ t, AnalyticAt ℂ K (z t, q)) :
    Continuous (fun t => fderiv ℂ (fun v => K (z t, v) * j t) q) := by
  have hdiff (t : ℝ) :
      DifferentiableAt ℂ (fun v => K (z t, v)) q :=
    ((hK t).comp (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hcont :
      Continuous (fun t => fderiv ℂ (fun v => K (z t, v)) q) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc : ContDiffAt ℂ 1 K (z t, q) := (hK t).contDiffAt
    have hc' :
        ContinuousAt (fun u : ℂ => fderiv ℂ (fun v => K (u, v)) q) (z t) :=
      (hc.fderiv
        (contDiffAt_const : ContDiffAt ℂ 0 (fun _ : ℂ => q) (z t))
        (by norm_num)).continuousAt
    exact hc'.comp hz.continuousAt
  simpa only [fderiv_mul_const (hdiff _) _] using hj.fun_smul hcont

lemma pullback_integral_joint_analytic {μ : Measure ℝ}
    {K : ℂ × (ℂ × ℂ × ℂ) → ℂ} {z j : ℝ → ℂ}
    {c : ℂ × ℂ × ℂ} {R : ℝ} {B : ℝ → ℝ}
    (hR : 0 < R) (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ q ∈ Metric.closedBall c R, ∀ t : ℝ, AnalyticAt ℂ K (z t, q))
    (hB : ∀ᵐ t ∂μ, ∀ q ∈ Metric.closedBall c R, ‖K (z t, q) * j t‖ ≤ B t)
    (hBi : Integrable B μ) :
    AnalyticOnNhd ℂ (fun q => ∫ t, K (z t, q) * j t ∂μ)
      (Metric.closedBall c (R / 2)) := by
  apply integral_joint_analytic_of_domination hR
  · intro q hq
    apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (((hK q hq t).continuousAt.comp (f := fun t : ℝ => (z t, q))
      (hz.continuousAt.prodMk continuousAt_const)).mul hj.continuousAt)
  · intro q hq
    exact (continuous_parameter_fderiv_joint (K := K) (z := z) (j := j) hz hj
      (hK q hq)).aestronglyMeasurable
  · intro t q hq
    exact ((hK q hq t).comp (f := fun q : ℂ × ℂ × ℂ => (z t, q))
      (analyticAt_const.prod analyticAt_id)).mul analyticAt_const
  · exact hB
  · exact hBi


lemma integrable_pullback_of_domination
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {μ : Measure ℝ} {K : ℂ × E → ℂ} {z j : ℝ → ℂ} {q : E} {B : ℝ → ℝ}
    (hz : Continuous z) (hj : Continuous j)
    (hK : ∀ t, AnalyticAt ℂ K (z t, q))
    (hB : ∀ᵐ t ∂μ, ‖K (z t, q) * j t‖ ≤ B t) (hBi : Integrable B μ) :
    Integrable (fun t => K (z t, q) * j t) μ := by
  apply hBi.mono' ?_ hB
  apply Continuous.aestronglyMeasurable
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (((hK t).continuousAt.comp (f := fun t : ℝ => (z t, q))
    (hz.continuousAt.prodMk continuousAt_const)).mul hj.continuousAt)

end SICLean.L4.G1ContinuationBoundaryAux
