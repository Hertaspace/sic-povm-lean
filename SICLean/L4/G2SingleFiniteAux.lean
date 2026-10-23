import SICLean.L4.G2SingleBent
import SICLean.L4.G1FiniteChainLedgerAux
import SICLean.L4.UpperContourClosure

set_option autoImplicit false

/-!
Helpers for the single-function finiteization.

The integral algebra preserves the literal bent-chain parameterization.
The residue account splits each truncated bent strip at height -1 into
an upper rectangle and a lower parallelogram. Local simple principal parts
give the rectangle's residue sum. The lower piece is analytic, so its two
horizontal sides account for the bend. Adjacent connectors telescope,
and absolute integrability supplies the final truncation limit.
-/

noncomputable section

open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2SingleFiniteAux

open G2 G2.SingleBent G2.CombResidues G2.StripCounting
open FinitePrincipalParts G1FiniteChainLedgerAux

theorem lower_pullback_translate (f : ℂ → ℂ) (q x ψ : ℝ) :
    g1BentLowerPullback f (x + q) ψ =
      g1BentLowerPullback (fun z => f (z + (q : ℂ))) x ψ := by
  funext r
  have hp : g1BentLowerPoint (x + q) ψ r = g1BentLowerPoint x ψ r + (q : ℂ) := by
    simp only [g1BentLowerPoint, Complex.ofReal_add]
    ring
  simp only [g1BentLowerPullback, hp]

theorem bent_integral_translate (f : ℂ → ℂ) (q x ψ : ℝ) :
    g1BentIntegral f (x + q) ψ =
      g1BentIntegral (fun z => f (z + (q : ℂ))) x ψ := by
  simp only [g1BentIntegral, lower_pullback_translate,
    G2ExactTelescopingAux.vertical_pullback_translate_fun]

theorem bent_integrable_translate_iff (f : ℂ → ℂ) (q x ψ : ℝ) :
    G1BentIntegrable f (x + q) ψ ↔
      G1BentIntegrable (fun z => f (z + (q : ℂ))) x ψ := by
  simp only [G1BentIntegrable, lower_pullback_translate,
    G2ExactTelescopingAux.vertical_pullback_translate_fun]

theorem bent_integral_sub (f g : ℂ → ℂ) (x ψ : ℝ)
    (hf : G1BentIntegrable f x ψ) (hg : G1BentIntegrable g x ψ) :
    g1BentIntegral (fun z => f z - g z) x ψ =
      g1BentIntegral f x ψ - g1BentIntegral g x ψ := by
  have hl : g1BentLowerPullback (fun z => f z - g z) x ψ =
      (fun r => g1BentLowerPullback f x ψ r - g1BentLowerPullback g x ψ r) := by
    funext r
    exact sub_mul _ _ _
  have hv : g1VerticalPullback (fun z => f z - g z) x =
      (fun t => g1VerticalPullback f x t - g1VerticalPullback g x t) := by
    funext t
    exact sub_mul _ _ _
  unfold g1BentIntegral
  rw [hl, hv, MeasureTheory.integral_sub hf.1 hg.1, MeasureTheory.integral_sub hf.2 hg.2]
  ring

theorem bent_integral_congr_ae (f g : ℂ → ℂ) (x ψ : ℝ)
    (hl : g1BentLowerPullback f x ψ =ᵐ[volume.restrict (Ici 0)]
      g1BentLowerPullback g x ψ)
    (hv : g1VerticalPullback f x =ᵐ[volume.restrict (Ici (-1))]
      g1VerticalPullback g x) :
    g1BentIntegral f x ψ = g1BentIntegral g x ψ := by
  simp only [g1BentIntegral, MeasureTheory.integral_congr_ae hl,
    MeasureTheory.integral_congr_ae hv]

theorem crossing_integer_period (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (m j k : ℤ) :
    G2.SingleBent.crossing M δ (m + M 1 0 * k) j =
      G2.SingleBent.crossing M δ m j + (-(k : ℝ) * G2.epsilon M) := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  simp only [G2.SingleBent.crossing]
  push_cast
  field_simp
  <;> ring

lemma simple_pole_expansion (N D : ℂ → ℂ) (p d : ℂ)
    (hN : AnalyticAt ℂ N p) (hD : AnalyticAt ℂ D p)
    (hD0 : D p = 0) (hd : HasDerivAt D d p) (hd0 : d ≠ 0) :
    ∃ (R : ℝ) (g : ℂ → ℂ), 0 < R ∧
      AnalyticOnNhd ℂ g (Metric.closedBall p R) ∧
      ∀ z ∈ Metric.closedBall p R, z ≠ p →
        N z / D z = (N p / d) / (z - p) + g z := by
  let A : ℂ → ℂ := fun z => N z / dslope D p z
  have hA : AnalyticAt ℂ A p := hN.div (analyticAt_dslope_local hD) (by
    simpa only [dslope_same, hd.deriv] using hd0)
  have hAp : A p = N p / d := by simp only [A, dslope_same, hd.deriv]
  have hg := analyticAt_dslope_local hA
  obtain ⟨r, hr, hgr⟩ := hg.exists_ball_analyticOnNhd
  refine ⟨r / 2, dslope A p, by positivity, hgr.mono ?_, ?_⟩
  · exact Metric.closedBall_subset_ball (by linarith)
  · intro z hz hzp
    have hDz : (z - p) * dslope D p z = D z := by
      simpa only [smul_eq_mul, hD0, sub_zero] using sub_smul_dslope D p z
    have hAz : (z - p) * dslope A p z = A z - A p := by
      simpa only [smul_eq_mul] using sub_smul_dslope A p z
    calc
      N z / D z = A z / (z - p) := by
        rw [← hDz]
        dsimp [A]
        simp only [div_div]
        congr 1
        ring
      _ = (N p / d) / (z - p) + dslope A p z := by
        rw [← hAp]
        have hAz2 : A z = A p + (z - p) * dslope A p z := by
          linear_combination -hAz
        conv_lhs => rw [hAz2]
        field_simp [sub_ne_zero.mpr hzp]
        <;> ring


/-- Finite simple poles strictly inside a rectangle, with local analytic remainders. -/
theorem rectangle_simple_poles {ι : Type*} (P : Finset ι) (p : ι → ℂ)
    (hp : Function.Injective p) (f : ℂ → ℂ) (lo hi : ℂ) (a : ι → ℂ)
    (hre : lo.re < hi.re) (him : lo.im < hi.im)
    (hinside : ∀ i ∈ P, p i ∈ openRectangle lo hi)
    (hf : AnalyticOnNhd ℂ f (closedRectangle lo hi \ p '' (P : Set ι)))
    (hlocal : ∀ i, ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧
      AnalyticOnNhd ℂ g (Metric.closedBall (p i) r) ∧
      ∀ z ∈ Metric.closedBall (p i) r, z ≠ p i → f z = a i / (z - p i) + g z) :
    rectangleCCW lo hi f = 2 * (Real.pi : ℂ) * I * ∑ i ∈ P, a i := by
  choose r g hr hg hfg using hlocal
  have hfg' (i : ι) (hiP : i ∈ P) : f =ᶠ[𝓝[≠] (p i)]
      (fun z => principalPart (p i) 1 (fun _ => a i) z + g i z) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (hr i)),
      self_mem_nhdsWithin] with z hz hzp
    simpa [principalPart] using hfg i z hz hzp
  obtain ⟨H, hH, hFH⟩ := finite_regularized_remainder P p hp f (closedRectangle lo hi)
    (fun _ => 1) (fun i _ => a i) g hf
    (fun i _ => hg i (p i) (Metric.mem_closedBall_self (hr i).le)) hfg'
  have hoff (z : ℂ) (hz : z ∈ rectangleBoundary lo hi) : z ∉ p '' (P : Set ι) := by
    rintro ⟨i, hiP, rfl⟩
    exact hz.2 (hinside i hiP)
  have hterm (i : ι) (hiP : i ∈ P) :
      ContinuousOn (principalPart (p i) 1 (fun _ => a i)) (rectangleBoundary lo hi) := by
    intro z hz
    exact (principalPart_analyticAt (p i) 1 (fun _ => a i)
      (fun he => hoff z hz ⟨i, hiP, he.symm⟩)).continuousAt.continuousWithinAt
  have hPP : ContinuousOn (finitePrincipalPart P p (fun _ => 1) (fun i _ => a i))
      (rectangleBoundary lo hi) := by
    exact continuousOn_finset_sum P hterm
  have hHC : ContinuousOn H (rectangleBoundary lo hi) :=
    hH.continuousOn.mono (fun _ h => h.1)
  calc
    rectangleCCW lo hi f = rectangleCCW lo hi
        (fun z => finitePrincipalPart P p (fun _ => 1) (fun i _ => a i) z + H z) := by
      apply rectangleCCW_congr lo hi hre.le him.le
      intro z hz
      exact hFH z hz.1 (hoff z hz)
    _ = rectangleCCW lo hi (finitePrincipalPart P p (fun _ => 1) (fun i _ => a i)) +
        rectangleCCW lo hi H := rectangleCCW_add lo hi hre.le him.le hPP hHC
    _ = _ := by
      rw [rectangleCCW_eq_zero lo hi hre.le him.le hH.differentiableOn, add_zero]
      unfold finitePrincipalPart
      rw [rectangleCCW_fun_sum P lo hi hre.le him.le _ hterm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hiP
      simpa [residueCoefficient] using
        rectangleCCW_principalPart lo hi (p i) 1 (fun _ => a i) (hinside i hiP)

/-- The single raw kernel is regular whenever its two denominator guards hold. -/
theorem rawG_analytic_of_poleMultiplicity_eq_zero (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) (m : ℤ) (z : ℂ)
    (hp : modularPhiPoleMultiplicity M m 0 z (repellingTau M : ℂ) = 0)
    (hc : combV M z - combU M m z ≠ 0) : AnalyticAt ℂ (rawG M u m) z := by
  have hphi := G2KernelConvergenceAux.phi_analytic_no_poles M hM.1 m 0 z
    (repellingTau M : ℂ) (real_mem_modularPhiDomain M _ (epsilon_pos M hM)) hp
  have hK : AnalyticAt ℂ (kernelK M u m) z := by
    unfold kernelK e
    fun_prop
  have hC : AnalyticAt ℂ (fun w => combV M w - combU M m w) z := by
    unfold combV combU e
    fun_prop
  exact (hK.div hC hc).mul hphi

/-- Neither the real comb nor the real-parameter Φ divisor meets the nonreal plane. -/
theorem rawG_analytic_nonreal (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℂ (rawG M u m) z := by
  have hP : modularPhiPoleIndices M m 0 z (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, h⟩
    apply hz
    rw [h]
    simp [modularPhiPolePoint, etaDenom]
  apply rawG_analytic_of_poleMultiplicity_eq_zero M hM u m z
  · simp [modularPhiPoleMultiplicity, hP]
  · intro hc
    obtain ⟨k, hk, _⟩ := (comb_zeros M hM m z).mp hc
    apply hz
    rw [hk]
    simp [root]


/-- The labelled roots of one fixed component in the full strip. -/
def componentKs (M : SL(2, ℤ)) (m : ℤ) : Finset ℤ :=
  ((stripFinset M).filter (fun x => x.1 = m)).image Prod.snd

theorem mem_componentKs (M : SL(2, ℤ)) (m k : ℤ) :
    k ∈ componentKs M m ↔ (m, k) ∈ stripFinset M := by
  constructor
  · intro hk
    obtain ⟨⟨r, s⟩, hx, hs⟩ := Finset.mem_image.mp hk
    obtain ⟨hx, hr⟩ := Finset.mem_filter.mp hx
    dsimp at hr hs
    subst r
    subst s
    exact hx
  · intro hk
    exact Finset.mem_image.mpr ⟨(m, k), Finset.mem_filter.mpr ⟨hk, rfl⟩, rfl⟩

theorem root_re_coordinate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m k : ℤ) :
    (M 1 0 : ℝ) * (root M m k).re + epsilon M * (m : ℝ) = combCoordinate M m k := by
  simpa only [add_re, mul_re, ofReal_re, ofReal_im, intCast_re, intCast_im,
    mul_zero, sub_zero, zero_mul] using congrArg Complex.re (root_coordinate M hM m k)

theorem crossing_mul (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (m j : ℤ) :
    (M 1 0 : ℝ) * crossing M δ m j =
      -δ - epsilon M * (m : ℝ) - (j : ℝ) * length M := by
  simp only [crossing, mul_div_cancel₀ _ (show (M 1 0 : ℝ) ≠ 0 by exact_mod_cast hM.1.ne')]

theorem root_ne_crossing (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < scale M) (m k j : ℤ) :
    (root M m k).re ≠ crossing M δ m j := by
  intro he
  have hr := root_re_coordinate M hM m k
  rw [he, crossing_mul M hM] at hr
  have hc : combCoordinate M m k + (j : ℝ) * length M = -δ := by linarith
  apply G2ContourChainAux.neg_gap_not_scaled (scale M) δ (scale_identities M hM).1 hδ.1 hδ.2
  refine ⟨(1 - M 1 1) * m + M 1 0 * k + j * specialValueOrder M, ?_⟩
  rw [← G2ContourChainAux.shifted_comb_scaled M hM m k j]
  exact hc.symm

theorem root_inside_strip (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < scale M) (m : Fin (M 1 0).toNat) (k : ℤ) :
    k ∈ componentKs M (m : ℤ) ↔
      crossing M δ (m : ℤ) (M 1 0) < (root M (m : ℤ) k).re ∧
        (root M (m : ℤ) k).re < crossing M δ (m : ℤ) 0 := by
  rw [mem_componentKs, mem_stripFinset_iff M hM δ hδ.1 hδ.2]
  have hc : (0 : ℝ) < M 1 0 := by exact_mod_cast hM.1
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg _
  have hmlt : (m : ℤ) < M 1 0 := by
    have hm := m.isLt
    have hc := Int.toNat_of_nonneg hM.1.le
    omega
  have hr := root_re_coordinate M hM (m : ℤ) k
  have hx0 := crossing_mul M hM δ (m : ℤ) (M 1 0)
  have hx1 := crossing_mul M hM δ (m : ℤ) 0
  simp only [Int.cast_zero, zero_mul, sub_zero] at hx1
  constructor
  · rintro ⟨_, _, hlo, hhi⟩
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨hm0, hmlt, ?_, ?_⟩ <;> nlinarith

theorem rawG_phi_poleMultiplicity_eq_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (hδ : 0 < δ) (m : ℤ) (z : ℂ)
    (hz : z.re ≤ crossing M δ m 0) :
    modularPhiPoleMultiplicity M m 0 z (repellingTau M : ℂ) = 0 := by
  have hp : modularPhiPoleIndices M m 0 z (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨_, he⟩
    have hc : (0 : ℝ) < M 1 0 := by exact_mod_cast hM.1
    have hcC : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
    dsimp [modularPhiPolePoint] at he
    rw [G2KernelConvergenceAux.repelling_etaDenom] at he
    have hmul := congrArg Complex.re ((eq_div_iff hcC).mp he)
    simp only [mul_re, ofReal_re, ofReal_im, intCast_re, intCast_im, natCast_re, natCast_im,
      Int.cast_zero,
      zero_re, one_re, sub_re, neg_re, mul_zero, sub_zero, zero_mul, zero_sub, add_re,
      sub_im, zero_im, one_im] at hmul
    have hx := crossing_mul M hM δ m 0
    simp only [Int.cast_zero, zero_mul, sub_zero] at hx
    have hzz := mul_le_mul_of_nonneg_left hz hc.le
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith [mul_nonneg hK (epsilon_pos M hM).le, epsilon_pos M hM]
  simp [modularPhiPoleMultiplicity, hp]

/-- Actual regularity in the upper rectangle after removing exactly the labelled comb roots. -/
theorem rawG_upper_rectangle_analytic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (δ : ℝ) (hδ : 0 < δ ∧ δ < scale M)
    (m : Fin (M 1 0).toNat) (T : ℝ) :
    AnalyticOnNhd ℂ (rawG M u (m : ℤ))
      (closedRectangle (g1VerticalPoint (crossing M δ (m : ℤ) (M 1 0)) (-1))
        (g1VerticalPoint (crossing M δ (m : ℤ) 0) T) \
          (root M (m : ℤ)) '' (componentKs M (m : ℤ) : Set ℤ)) := by
  intro z hz
  apply rawG_analytic_of_poleMultiplicity_eq_zero M hM u (m : ℤ) z
  · apply rawG_phi_poleMultiplicity_eq_zero M hM δ hδ.1
    simpa only [g1VerticalPoint, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] using hz.1.2.1
  · intro hc
    obtain ⟨k, hk, _⟩ := (comb_zeros M hM (m : ℤ) z).mp hc
    have hr : root M (m : ℤ) k ∈ closedRectangle
        (g1VerticalPoint (crossing M δ (m : ℤ) (M 1 0)) (-1))
        (g1VerticalPoint (crossing M δ (m : ℤ) 0) T) := hk ▸ hz.1
    have hr' : crossing M δ (m : ℤ) (M 1 0) ≤ (root M (m : ℤ) k).re ∧
        (root M (m : ℤ) k).re ≤ crossing M δ (m : ℤ) 0 := by
      simpa [closedRectangle, g1VerticalPoint] using And.intro hr.1 hr.2.1
    have hK := (root_inside_strip M hM δ hδ m k).mpr
      ⟨lt_of_le_of_ne hr'.1 (root_ne_crossing M hM δ hδ (m : ℤ) k (M 1 0)).symm,
        lt_of_le_of_ne hr'.2 (root_ne_crossing M hM δ hδ (m : ℤ) k 0)⟩
    exact hz.2 ⟨k, hK, hk.symm⟩

lemma integral_scale_complex (f : ℝ → ℂ) (a b c : ℝ) :
    (∫ t : ℝ in a..b, (c : ℂ) * f (c * t)) = ∫ t : ℝ in c * a..c * b, f t := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [real_smul] using intervalIntegral.smul_integral_comp_mul_left (a := a) (b := b) f c

lemma integral_reverse_scale_complex (f : ℝ → ℂ) (a b c e : ℝ) :
    (∫ t : ℝ in a..b, (c : ℂ) * f (e - c * t)) = ∫ t : ℝ in e - c * b..e - c * a, f t := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [real_smul] using intervalIntegral.smul_integral_comp_sub_mul (a := a) (b := b) f c e

lemma lower_parallelogram (f : ℂ → ℂ) (a b R : ℝ) (d : ℂ)
    (hab : a < b) (hR : 0 < R) (hd : d.im < 0)
    (hf : ∀ z : ℂ, z.im ≤ -1 → AnalyticAt ℂ f z) :
    (∫ r : ℝ in 0..R, f ((b : ℂ) - I + (r : ℂ) * d) * d) -
      (∫ r : ℝ in 0..R, f ((a : ℂ) - I + (r : ℂ) * d) * d) =
      (∫ t : ℝ in 0..(b - a), f ((a : ℂ) - I + (R : ℂ) * d + (t : ℂ))) -
        (∫ t : ℝ in 0..(b - a), f ((a : ℂ) - I + (t : ℂ))) := by
  let w : ℝ := b - a
  have hw : 0 < w := sub_pos.mpr hab
  have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  let v : ℂ := ((a : ℂ) - I + (R : ℂ) * d) / (w : ℂ)
  let T : ℂ := -(R : ℂ) * d / (w : ℂ)
  let F : ℂ → ℂ := fun z => (w : ℂ) * f ((w : ℂ) * z)
  have hT : 0 < T.im := by
    dsimp [T]
    simp only [div_ofReal_im, mul_im, neg_im, ofReal_im, ofReal_re, neg_re, zero_mul, zero_add, neg_zero, add_zero]
    exact div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hR) hd) hw
  have hF : AnalyticOnNhd ℂ F (UpperContour.closedBox v T 1) := by
    intro z hz
    rw [UpperContour.closedBox_eq_image v T hT.ne' 1] at hz
    rcases hz with ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    have hid : (w : ℂ) * (v + (s : ℂ) * T + (t : ℂ)) =
        (a : ℂ) - I + (R : ℂ) * (1 - (s : ℂ)) * d + (t : ℂ) * (w : ℂ) := by
      dsimp [v, T]
      field_simp
      <;> ring
    have him : ((w : ℂ) * (v + (s : ℂ) * T + (t : ℂ))).im ≤ -1 := by
      rw [hid]
      simp only [add_im, sub_im, sub_re, ofReal_im, I_im, mul_im, ofReal_re,
        Complex.one_re, Complex.one_im, mul_re, mul_zero, zero_mul, sub_zero,
        zero_sub, mul_one, add_zero, zero_add]
      have hnonneg : 0 ≤ R * (1 - s) := mul_nonneg hR.le (sub_nonneg.mpr hs.2)
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hnonneg hd.le]
    exact analyticAt_const.mul ((hf _ him).comp (f := fun z : ℂ => (w : ℂ) * z)
      (analyticAt_const.mul analyticAt_id))
  have hbound : UpperContour.clockwiseBoundary F v T 1 = 0 := by
    have h := UpperContour.parallelogram_finite_principal_parts F v T hT 1 (by norm_num)
      (∅ : Finset ℂ) (fun _ => 1) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (by simp) (by simp) (by simp) (by simpa using hF) (by simp) (by simp)
    simpa using h
  have hv : (w : ℂ) * v = (a : ℂ) - I + (R : ℂ) * d := by
    dsimp [v]
    field_simp
  have hvT : (w : ℂ) * (v + T) = (a : ℂ) - I := by
    dsimp [v, T]
    field_simp
    <;> ring
  have hfirst : UpperContour.firstSide F v 1 =
      -(∫ t : ℝ in 0..w, f ((a : ℂ) - I + (R : ℂ) * d + (t : ℂ))) := by
    dsimp [UpperContour.firstSide]
    simp only [Nat.cast_one]
    rw [intervalIntegral.integral_symm]
    congr 1
    calc
      (∫ t : ℝ in 0..(1 : ℝ), F (v + (t : ℂ))) =
        ∫ t : ℝ in 0..1, (w : ℂ) *
          f ((a : ℂ) - I + (R : ℂ) * d + ((w * t : ℝ) : ℂ)) := by
            apply intervalIntegral.integral_congr
            intro t ht
            dsimp [F]
            congr 2
            push_cast
            linear_combination hv
      _ = _ := by
        simpa only [mul_zero, mul_one] using
          integral_scale_complex (fun t : ℝ => f ((a : ℂ) - I + (R : ℂ) * d + (t : ℂ))) 0 1 w
  have hthird : UpperContour.thirdSide F v T 1 =
      ∫ t : ℝ in 0..w, f ((a : ℂ) - I + (t : ℂ)) := by
    dsimp [UpperContour.thirdSide]
    simp only [Nat.cast_one, one_mul]
    calc
      (∫ t : ℝ in 0..(1 : ℝ), F (v + T + (t : ℂ))) =
        ∫ t : ℝ in 0..1, (w : ℂ) * f ((a : ℂ) - I + ((w * t : ℝ) : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          dsimp [F]
          congr 2
          push_cast
          linear_combination hvT
      _ = _ := by
        simpa only [mul_zero, mul_one] using
          integral_scale_complex (fun t : ℝ => f ((a : ℂ) - I + (t : ℂ))) 0 1 w
  have hsecond : UpperContour.secondSide F v T 1 =
      -(∫ r : ℝ in 0..R, f ((a : ℂ) - I + (r : ℂ) * d) * d) := by
    dsimp [UpperContour.secondSide]
    simp only [Nat.cast_one]
    calc
      (∫ t : ℝ in 0..(1 : ℝ), F (v + (t : ℂ) * T) * T) =
        -(∫ t : ℝ in 0..1, (R : ℂ) *
          (f ((a : ℂ) - I + ((R - R * t : ℝ) : ℂ) * d) * d)) := by
          rw [← intervalIntegral.integral_neg]
          apply intervalIntegral.integral_congr
          intro t ht
          have hp : (w : ℂ) * (v + (t : ℂ) * T) =
              (a : ℂ) - I + ((R - R * t : ℝ) : ℂ) * d := by
            dsimp [v, T]
            push_cast
            field_simp
            <;> ring
          dsimp [F]
          rw [hp]
          dsimp [T]
          field_simp
          <;> ring
      _ = _ := by
        congr 1
        simpa only [mul_zero, mul_one, sub_self, sub_zero] using
          integral_reverse_scale_complex (fun r : ℝ => f ((a : ℂ) - I + (r : ℂ) * d) * d) 0 1 R R
  have hfourth : UpperContour.fourthSide F v T 1 =
      ∫ r : ℝ in 0..R, f ((b : ℂ) - I + (r : ℂ) * d) * d := by
    dsimp [UpperContour.fourthSide]
    simp only [Nat.cast_one]
    rw [intervalIntegral.integral_symm]
    calc
      -(∫ t : ℝ in 0..(1 : ℝ), F (v + 1 + (t : ℂ) * T) * T) =
        ∫ t : ℝ in 0..1, (R : ℂ) *
          (f ((b : ℂ) - I + ((R - R * t : ℝ) : ℂ) * d) * d) := by
          rw [← intervalIntegral.integral_neg]
          apply intervalIntegral.integral_congr
          intro t ht
          have hp : (w : ℂ) * (v + 1 + (t : ℂ) * T) =
              (b : ℂ) - I + ((R - R * t : ℝ) : ℂ) * d := by
            dsimp [v, T]
            push_cast
            field_simp
            dsimp [w]
            push_cast
            <;> ring
          dsimp [F]
          rw [hp]
          dsimp [T]
          field_simp
          <;> ring
      _ = _ := by
        simpa only [mul_zero, mul_one, sub_self, sub_zero] using
          integral_reverse_scale_complex (fun r : ℝ => f ((b : ℂ) - I + (r : ℂ) * d) * d) 0 1 R R
  unfold UpperContour.clockwiseBoundary at hbound
  rw [hfirst, hsecond, hthird, hfourth] at hbound
  change _ = _ - _
  dsimp [w] at hbound
  linear_combination hbound

lemma horizontal_shift (f : ℂ → ℂ) (a b y : ℝ) :
    (∫ t : ℝ in 0..(b - a), f ((a : ℂ) + (t : ℂ) + (y : ℂ) * I)) =
      horizontalIntegral f a b y := by
  have h := intervalIntegral.integral_comp_add_left
    (a := 0) (b := b - a) (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) a
  have he : a + (b - a) = b := by ring
  simpa only [he, add_zero, Complex.ofReal_add,
    horizontalIntegral, horizontalPullback] using h

lemma rectangle_bent_orientation (f : ℂ → ℂ) (a b T : ℝ) :
    FinitePrincipalParts.rectangleCCW (g1VerticalPoint a (-1)) (g1VerticalPoint b T) f =
      (∫ t : ℝ in -1..T, g1VerticalPullback f b t) -
        (∫ t : ℝ in -1..T, g1VerticalPullback f a t) +
        horizontalIntegral f a b (-1) - horizontalIntegral f a b T := by
  simp only [FinitePrincipalParts.rectangleCCW, g1VerticalPoint, add_re, ofReal_re,
    mul_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_self, add_zero,
    add_im, mul_im, mul_one, zero_add, g1VerticalPullback,
    intervalIntegral.integral_mul_const, horizontalIntegral, horizontalPullback]
  ring

lemma finite_bent_boundary (f : ℂ → ℂ) (a b R T : ℝ) (d : ℂ)
    (hab : a < b) (hR : 0 < R) (hd : d.im < 0)
    (hf : ∀ z : ℂ, z.im ≤ -1 → AnalyticAt ℂ f z) :
    (-(∫ r : ℝ in 0..R, f ((b : ℂ) - I + (r : ℂ) * d) * d) +
      ∫ t : ℝ in -1..T, g1VerticalPullback f b t) -
      (-(∫ r : ℝ in 0..R, f ((a : ℂ) - I + (r : ℂ) * d) * d) +
        ∫ t : ℝ in -1..T, g1VerticalPullback f a t) =
      FinitePrincipalParts.rectangleCCW (g1VerticalPoint a (-1)) (g1VerticalPoint b T) f +
        horizontalIntegral f a b T -
        (∫ t : ℝ in 0..(b - a), f ((a : ℂ) - I + (R : ℂ) * d + (t : ℂ))) := by
  have h := lower_parallelogram f a b R d hab hR hd hf
  have htop : (∫ t : ℝ in 0..(b - a), f ((a : ℂ) - I + (t : ℂ))) =
      horizontalIntegral f a b (-1) := by
    convert horizontal_shift f a b (-1) using 1
    apply intervalIntegral.integral_congr
    intro t ht
    congr 1
    push_cast
    ring
  rw [htop] at h
  rw [rectangle_bent_orientation]
  linear_combination -h

lemma lowerPoint_eq_affine (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ β : ℝ) (m j : ℤ) (R : ℝ) :
    lowerPoint M δ β m j R =
      (crossing M δ m j : ℂ) - I + (R : ℂ) * lowerJacobian M β := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
  dsimp [lowerPoint, crossing, lowerJacobian]
  push_cast
  field_simp
  <;> ring

lemma full_crossing_width (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (m : ℤ) :
    crossing M δ m 0 - crossing M δ m (M 1 0) = length M := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hM.1.ne'
  dsimp [crossing]
  push_cast
  field_simp
  <;> ring

lemma lowerJacobian_im_neg (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (β : ℝ) :
    (lowerJacobian M β).im < 0 := by
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  simpa [lowerJacobian, div_ofReal_im] using div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) hc

lemma common_finite_bent_boundary (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : ℂ → ℂ) (δ β : ℝ) (m : ℤ) (T : ℝ) (hT : 0 < T)
    (hf : ∀ z : ℂ, z.im ≤ -1 → AnalyticAt ℂ f z) :
    (-(∫ r : ℝ in 0..T, f (lowerPoint M δ β m 0 r) * lowerJacobian M β) +
      ∫ t : ℝ in -1..T, g1VerticalPullback f (crossing M δ m 0) t) -
      (-(∫ r : ℝ in 0..T, f (lowerPoint M δ β m (M 1 0) r) * lowerJacobian M β) +
        ∫ t : ℝ in -1..T, g1VerticalPullback f (crossing M δ m (M 1 0)) t) =
      FinitePrincipalParts.rectangleCCW (g1VerticalPoint (crossing M δ m (M 1 0)) (-1))
        (g1VerticalPoint (crossing M δ m 0) T) f +
        horizontalIntegral f (crossing M δ m (M 1 0)) (crossing M δ m 0) T -
        (∫ t : ℝ in 0..length M, f (lowerPoint M δ β m (M 1 0) T + (t : ℂ))) := by
  have hab : crossing M δ m (M 1 0) < crossing M δ m 0 := by
    have hw := full_crossing_width M hM δ m
    linarith [length_pos M hM]
  simpa only [← lowerPoint_eq_affine M hM δ β m,
    full_crossing_width M hM δ m] using
      finite_bent_boundary f (crossing M δ m (M 1 0)) (crossing M δ m 0) T T
        (lowerJacobian M β) hab hT (lowerJacobian_im_neg M hM β) hf


theorem interval_integral_Ici_tendsto (f : ℝ → ℂ) (a : ℝ)
    (hf : IntegrableOn f (Ici a)) (b : ℝ → ℝ) (hb : Tendsto b atTop atTop) :
    Tendsto (fun T : ℝ => ∫ r : ℝ in a..b T, f r) atTop
      (𝓝 (∫ r : ℝ in Ici a, f r)) := by
  simpa only [integral_Ici_eq_integral_Ioi] using
    intervalIntegral_tendsto_integral_Ioi a (hf.mono_set Ioi_subset_Ici_self) hb

theorem bent_truncated_scaled_tendsto (f : ℂ → ℂ) (x ψ a : ℝ)
    (ha : 0 < a) (hInt : G1BentIntegrable f x ψ) :
    Tendsto (fun T : ℝ =>
      -(∫ r : ℝ in 0..T * a, g1BentLowerPullback f x ψ r) +
        ∫ t : ℝ in -1..T, g1VerticalPullback f x t)
      atTop (𝓝 (g1BentIntegral f x ψ)) := by
  have hl := interval_integral_Ici_tendsto (g1BentLowerPullback f x ψ) 0 hInt.1
    (fun T : ℝ => T * a) (tendsto_id.atTop_mul_const ha)
  have hv := interval_integral_Ici_tendsto (g1VerticalPullback f x) (-1) hInt.2
    (fun T : ℝ => T) tendsto_id
  simpa only [g1BentIntegral] using hl.neg.add hv

theorem lowerJacobian_eq_scale_mul_direction (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    lowerJacobian M β = (lowerScale M β : ℂ) * g1LowerDirection (angle β) := by
  rw [(angle_direction β hβ).2.2]
  have hsqrt : (Real.sqrt (1 + β ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 1 + β ^ 2)).ne'
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
  simp only [lowerJacobian, lowerScale, Complex.ofReal_div]
  push_cast
  field_simp

theorem lower_truncated_eq_g1 (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : ℂ → ℂ) (δ β : ℝ) (hβ : 0 < β ∧ β < 1) (m j : ℤ) (T : ℝ) :
    (∫ r : ℝ in 0..T, f (lowerPoint M δ β m j r) * lowerJacobian M β) =
      ∫ r : ℝ in 0..T * lowerScale M β,
        g1BentLowerPullback f (crossing M δ m j) (angle β) r := by
  have heq : (fun r : ℝ => f (lowerPoint M δ β m j r) * lowerJacobian M β) =
      (fun r : ℝ => lowerScale M β •
        g1BentLowerPullback f (crossing M δ m j) (angle β) (r * lowerScale M β)) := by
    funext r
    rw [lowerPoint_eq_g1 M hM δ β hβ m j r,
      lowerJacobian_eq_scale_mul_direction M hM β hβ]
    simp only [g1BentLowerPullback, Complex.real_smul]
    ring
  rw [heq, intervalIntegral.integral_smul]
  simpa only [zero_mul] using
    intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := T)
      (g1BentLowerPullback f (crossing M δ m j) (angle β)) (lowerScale M β)

theorem common_truncated_bent_tendsto (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : ℂ → ℂ) (δ β : ℝ) (hβ : 0 < β ∧ β < 1) (m j : ℤ)
    (hInt : G1BentIntegrable f (crossing M δ m j) (angle β)) :
    Tendsto (fun T : ℝ =>
      -(∫ r : ℝ in 0..T, f (lowerPoint M δ β m j r) * lowerJacobian M β) +
        ∫ t : ℝ in -1..T, g1VerticalPullback f (crossing M δ m j) t)
      atTop (𝓝 (SingleBent.integral M δ β m j f)) := by
  simpa only [lower_truncated_eq_g1 M hM f δ β hβ m j, SingleBent.integral] using
    bent_truncated_scaled_tendsto f (crossing M δ m j) (angle β) (lowerScale M β)
      (lowerPoint_hasDerivAt M hM δ β m j 0).2 hInt

theorem rawG_truncated_bent_tendsto (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1)
    (m : ℤ) (j : Fin ((M 1 0).toNat + 1)) :
    Tendsto (fun T : ℝ =>
      -(∫ r : ℝ in 0..T,
          rawG M u m (lowerPoint M δ β m (j : ℤ) r) * lowerJacobian M β) +
        ∫ t : ℝ in -1..T,
          g1VerticalPullback (rawG M u m) (crossing M δ m (j : ℤ)) t)
      atTop (𝓝 (SingleBent.integral M δ β m (j : ℤ) (rawG M u m))) := by
  exact common_truncated_bent_tendsto M hM (rawG M u m) δ β hβ m (j : ℤ)
    (rawG_bent_integrable M hM u hu δ β hδ hβ m j)

theorem sum_adjacent_interval_integrals (f : ℝ → ℂ) (a : ℕ → ℝ) (n : ℕ)
    (hInt : ∀ k < n, IntervalIntegrable f volume (a k) (a (k + 1))) :
    (∑ j : Fin n, ∫ t : ℝ in a (j : ℕ)..a ((j : ℕ) + 1), f t) =
      ∫ t : ℝ in a 0..a n, f t := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ∫ t : ℝ in a k..a (k + 1), f t)]
  exact intervalIntegral.sum_integral_adjacent_intervals hInt

theorem sum_reverse_adjacent_interval_integrals (f : ℝ → ℂ) (a : ℕ → ℝ) (n : ℕ)
    (hInt : ∀ k < n, IntervalIntegrable f volume (a k) (a (k + 1))) :
    (∑ j : Fin n, ∫ t : ℝ in a ((j : ℕ) + 1)..a (j : ℕ), f t) =
      ∫ t : ℝ in a n..a 0, f t := by
  calc
    _ = ∑ j : Fin n, -(∫ t : ℝ in a (j : ℕ)..a ((j : ℕ) + 1), f t) := by
      apply Finset.sum_congr rfl
      intro j _
      exact intervalIntegral.integral_symm (f := f) (μ := volume)
        (a := a (j : ℕ)) (b := a ((j : ℕ) + 1))
    _ = -(∫ t : ℝ in a 0..a n, f t) := by
      rw [Finset.sum_neg_distrib, sum_adjacent_interval_integrals f a n hInt]
    _ = _ := (intervalIntegral.integral_symm (a := a 0) (b := a n) (f := f)).symm



/-- The upper rectangle contains precisely the finite roots of this component. -/
theorem rawG_upper_rectangle (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (δ : ℝ) (hδ : 0 < δ ∧ δ < scale M)
    (m : Fin (M 1 0).toNat) (T : ℝ) (hT : 0 < T) (a : ℤ → ℂ)
    (hlocal : ∀ k, ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧
      AnalyticOnNhd ℂ g (Metric.closedBall (root M (m : ℤ) k) r) ∧
      ∀ z ∈ Metric.closedBall (root M (m : ℤ) k) r, z ≠ root M (m : ℤ) k →
        rawG M u (m : ℤ) z = a k / (z - root M (m : ℤ) k) + g z) :
    rectangleCCW (g1VerticalPoint (crossing M δ (m : ℤ) (M 1 0)) (-1))
      (g1VerticalPoint (crossing M δ (m : ℤ) 0) T) (rawG M u (m : ℤ)) =
        2 * (Real.pi : ℂ) * I * ∑ k ∈ componentKs M (m : ℤ), a k := by
  have hp : Function.Injective (root M (m : ℤ)) := by
    intro k l hkl
    have hs : (scale M : ℂ) ≠ 0 := by exact_mod_cast (scale_identities M hM).1.ne'
    apply Int.cast_injective (α := ℂ)
    apply add_left_cancel (a := (m : ℂ) * (repellingTau M : ℂ))
    exact mul_left_cancel₀ hs hkl
  have hre : crossing M δ (m : ℤ) (M 1 0) < crossing M δ (m : ℤ) 0 := by
    have hw := full_crossing_width M hM δ (m : ℤ)
    linarith [length_pos M hM]
  apply rectangle_simple_poles (componentKs M (m : ℤ)) (root M (m : ℤ)) hp _ _ _ a
  · simpa [g1VerticalPoint] using hre
  · simp only [g1VerticalPoint, add_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero]
    linarith
  · intro k hk
    have hin := (root_inside_strip M hM δ hδ m k).mp hk
    simpa [openRectangle, g1VerticalPoint, root] using
      And.intro hin.1 (And.intro hin.2 (And.intro (by norm_num : (-1 : ℝ) < 0) hT))
  · exact rawG_upper_rectangle_analytic M hM u δ hδ m T
  · exact hlocal


/-- Summing the separate component root sets preserves all pair labels. -/
theorem component_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : ℤ × ℤ → ℂ) :
    (∑ m : Fin (M 1 0).toNat, ∑ k ∈ componentKs M (m : ℤ), f (m, k)) =
      ∑ x ∈ stripFinset M, f x := by
  have hrange (x : ℤ × ℤ) (hx : x ∈ stripFinset M) :
      0 ≤ x.1 ∧ x.1.toNat < (M 1 0).toNat := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨Int.natCast_nonneg _, by simpa [canonicalRepresentative] using i.1.isLt⟩
  have hone (m : ℤ) : (∑ k ∈ componentKs M m, f (m, k)) =
      ∑ x ∈ (stripFinset M).filter (fun x => x.1 = m), f x := by
    unfold componentKs
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro x hx
      have hx1 := (Finset.mem_filter.mp hx).2
      rw [← hx1]
    · intro x hx y hy he
      apply Prod.ext
      · exact ((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm
      · exact he
  simp_rw [hone]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ =>
    ∑ x ∈ (stripFinset M).filter (fun x => x.1 = (m : ℤ)), f x)]
  have hfilter (m : ℕ) : (stripFinset M).filter (fun x => x.1 = (m : ℤ)) =
      (stripFinset M).filter (fun x => x.1.toNat = m) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hm⟩
      exact ⟨hx, by rw [hm, Int.toNat_natCast]⟩
    · rintro ⟨hx, hm⟩
      exact ⟨hx, by rw [← hm]; exact (Int.toNat_of_nonneg (hrange x hx).1).symm⟩
  simp_rw [hfilter]
  apply Finset.sum_fiberwise_of_maps_to
  intro x hx
  exact Finset.mem_range.mpr (hrange x hx).2

lemma segment_shift (f : ℂ → ℂ) (z : ℂ) (a b : ℝ) :
    (∫ t : ℝ in 0..(b - a), f (z + (a : ℂ) + (t : ℂ))) =
      ∫ t : ℝ in a..b, f (z + (t : ℂ)) := by
  have h := intervalIntegral.integral_comp_add_left
    (a := 0) (b := b - a) (fun x : ℝ => f (z + (x : ℂ))) a
  have he : a + (b - a) = b := by ring
  simpa only [he, add_zero, Complex.ofReal_add, add_assoc] using h

lemma rawG_horizontal_continuous (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    Continuous (fun t : ℝ => rawG M u m (z + (t : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have him : (z + (t : ℂ)).im ≠ 0 := by simpa using hz
  exact (rawG_analytic_nonreal M hM u m _ him).continuousAt.comp
    (f := fun t : ℝ => z + (t : ℂ)) (by fun_prop)

lemma upperConnector_full_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (δ : ℝ) (m : ℤ) (T : ℝ) (hT : 0 < T) :
    (∑ j : Fin (M 1 0).toNat, upperConnector M u δ m (j : ℤ) T) =
      horizontalIntegral (rawG M u m) (crossing M δ m (M 1 0)) (crossing M δ m 0) T := by
  have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.1.le
  have hcont : Continuous (horizontalPullback (rawG M u m) T) := by
    have h := rawG_horizontal_continuous M hM u m ((T : ℂ) * I) (by simpa using hT.ne')
    change Continuous (fun t : ℝ => rawG M u m ((t : ℂ) + (T : ℂ) * I))
    simpa only [add_comm] using h
  simpa only [upperConnector, horizontalIntegral, Nat.cast_add, Nat.cast_one, hc, Nat.cast_zero] using
    sum_reverse_adjacent_interval_integrals (horizontalPullback (rawG M u m) T)
      (fun n : ℕ => crossing M δ m (n : ℤ)) (M 1 0).toNat
      (fun k hk => hcont.intervalIntegrable _ _)

lemma crossing_step (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (m j : ℤ) :
    crossing M δ m j - crossing M δ m (j + 1) = shiftLength M := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hM.1.ne'
  dsimp [crossing, shiftLength]
  push_cast
  field_simp
  ring

lemma lowerPoint_horizontal (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ β : ℝ) (m j : ℤ) (T : ℝ) :
    lowerPoint M δ β m j T =
      (lowerPoint M δ β m 0 T - (crossing M δ m 0 : ℂ)) + (crossing M δ m j : ℂ) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
  dsimp [lowerPoint, crossing]
  push_cast
  field_simp
  ring

lemma lowerPoint_im (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ β : ℝ) (m j : ℤ) (T : ℝ) :
    (lowerPoint M δ β m j T).im = -1 - T / (M 1 0 : ℝ) := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hM.1.ne'
  unfold lowerPoint
  simp only [Complex.div_im, add_im, sub_im, sub_re, neg_im,
    ofReal_im, ofReal_re, Complex.intCast_re, Complex.intCast_im, mul_im, mul_re,
    I_im, I_re, zero_mul, mul_zero, add_zero, zero_sub, mul_one, sub_zero,
    neg_zero, Complex.normSq_apply]
  field_simp
  ring

lemma lowerConnector_full_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (δ β : ℝ) (m : ℤ) (T : ℝ) (hT : 0 ≤ T) :
    (∑ j : Fin (M 1 0).toNat, lowerConnector M u δ β m (j : ℤ) T) =
      ∫ t : ℝ in 0..length M, rawG M u m (lowerPoint M δ β m (M 1 0) T + (t : ℂ)) := by
  have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.1.le
  have hcR : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  let z := lowerPoint M δ β m 0 T - (crossing M δ m 0 : ℂ)
  let a : ℕ → ℝ := fun n => crossing M δ m (n : ℤ)
  let F : ℝ → ℂ := fun t => rawG M u m (z + (t : ℂ))
  have hz : z.im ≠ 0 := by
    change (lowerPoint M δ β m 0 T - (crossing M δ m 0 : ℂ)).im ≠ 0
    rw [sub_im, ofReal_im, sub_zero, lowerPoint_im M hM]
    have hn := div_nonneg hT hcR.le
    linarith
  have hcont : Continuous F := rawG_horizontal_continuous M hM u m z hz
  have hterm (j : Fin (M 1 0).toNat) :
      lowerConnector M u δ β m (j : ℤ) T =
        ∫ t : ℝ in a (j.val + 1)..a j.val, F t := by
    dsimp [lowerConnector]
    rw [← crossing_step M hM δ m (j : ℤ), lowerPoint_horizontal M hM δ β m ((j : ℤ) + 1) T]
    exact segment_shift (rawG M u m) z (crossing M δ m ((j : ℤ) + 1)) (crossing M δ m (j : ℤ))
  calc
    _ = ∑ j : Fin (M 1 0).toNat, ∫ t : ℝ in a (j.val + 1)..a j.val, F t :=
      Finset.sum_congr rfl (fun j _ => hterm j)
    _ = ∫ t : ℝ in a (M 1 0).toNat..a 0, F t :=
      sum_reverse_adjacent_interval_integrals F a (M 1 0).toNat (fun k hk => hcont.intervalIntegrable _ _)
    _ = _ := by
      dsimp [a]
      simp only [hc]
      rw [← segment_shift (rawG M u m) z (crossing M δ m (M 1 0)) (crossing M δ m 0),
        full_crossing_width M hM δ m, ← lowerPoint_horizontal M hM δ β m (M 1 0) T]

lemma full_closing_segments_tendsto_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1)
    (m : Fin (M 1 0).toNat) :
    Tendsto (horizontalIntegral (rawG M u (m : ℤ))
      (crossing M δ (m : ℤ) (M 1 0)) (crossing M δ (m : ℤ) 0)) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => ∫ t : ℝ in 0..length M,
        rawG M u (m : ℤ) (lowerPoint M δ β (m : ℤ) (M 1 0) T + (t : ℂ)))
        atTop (𝓝 0) := by
  have hupper := tendsto_finsetSum (Finset.univ : Finset (Fin (M 1 0).toNat))
    (fun j _ => (closing_segments_tendsto_zero M hM u hu δ β hδ hβ m j).1)
  have hlower := tendsto_finsetSum (Finset.univ : Finset (Fin (M 1 0).toNat))
    (fun j _ => (closing_segments_tendsto_zero M hM u hu δ β hδ hβ m j).2)
  constructor
  · apply (show Tendsto (fun T : ℝ => ∑ j : Fin (M 1 0).toNat,
      upperConnector M u δ (m : ℤ) (j : ℤ) T) atTop (𝓝 0) by simpa using hupper).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact upperConnector_full_sum M hM u δ (m : ℤ) T hT
  · apply (show Tendsto (fun T : ℝ => ∑ j : Fin (M 1 0).toNat,
      lowerConnector M u δ β (m : ℤ) (j : ℤ) T) atTop (𝓝 0) by simpa using hlower).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact lowerConnector_full_sum M hM u δ β (m : ℤ) T hT


end SICLean.L4.G2SingleFiniteAux
