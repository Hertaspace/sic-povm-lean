import SICLean.L4.UpperContourGeometry
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

/-! Auxiliary finite principal-part proof for the actual tilted boundary. -/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContourClosureAux

open UpperContour

private theorem coords_affine_literal (v T : ℂ) (hT : T.im ≠ 0) (a b : ℝ) :
    UpperWindow.coords T (v + (a : ℂ) * T + (b : ℂ) - v) = (a, b) := by
  have he : v + (a : ℂ) * T + (b : ℂ) - v = (a : ℂ) * T + (b : ℂ) := by ring
  rw [he]
  apply Prod.ext <;> simp [UpperWindow.coords, Complex.mul_re, Complex.mul_im, hT]

private theorem affine_mem_boundary (v T : ℂ) (hT : T.im ≠ 0)
    (R a b : ℝ) (ha : a ∈ Icc 0 R) (hb : b ∈ Icc 0 R)
    (he : a = 0 ∨ a = R ∨ b = 0 ∨ b = R) :
    v + (a : ℂ) * T + (b : ℂ) ∈ boxBoundary v T R := by
  simp only [boxBoundary, Set.mem_sdiff, closedBox, openBox, Set.mem_ofPred_eq,
    coords_affine_literal v T hT a b]
  refine ⟨⟨ha.1, ha.2, hb.1, hb.2⟩, ?_⟩
  rcases he with rfl | rfl | rfl | rfl <;> simp

private theorem horizontal_mem_boundary (v T : ℂ) (hT : T.im ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) (t a : ℝ) (ht : t ∈ [[0, R]])
    (ha : a = 0 ∨ a = R) :
    v + (a : ℂ) * T + (t : ℂ) ∈ boxBoundary v T R := by
  have ht' : t ∈ Icc 0 R := by simpa [uIcc_of_le hR] using ht
  rcases ha with ha | ha <;> subst a
  · exact affine_mem_boundary v T hT R 0 t ⟨le_rfl, hR⟩ ht' (Or.inl rfl)
  · exact affine_mem_boundary v T hT R R t ⟨hR, le_rfl⟩ ht' (Or.inr (Or.inl rfl))

private theorem vertical_mem_boundary (v T : ℂ) (hT : T.im ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) (t b : ℝ) (ht : t ∈ [[0, R]])
    (hb : b = 0 ∨ b = R) :
    v + (b : ℂ) + (t : ℂ) * T ∈ boxBoundary v T R := by
  have ht' : t ∈ Icc 0 R := by simpa [uIcc_of_le hR] using ht
  have hm : v + (b : ℂ) + (t : ℂ) * T = v + (t : ℂ) * T + (b : ℂ) := by ring
  rw [hm]
  rcases hb with hb | hb <;> subst b
  · exact affine_mem_boundary v T hT R t 0 ht' ⟨le_rfl, hR⟩ (Or.inr (Or.inr (Or.inl rfl)))
  · exact affine_mem_boundary v T hT R t R ht' ⟨hR, le_rfl⟩ (Or.inr (Or.inr (Or.inr rfl)))

private theorem horizontal_intervalIntegrable (v T : ℂ) (hT : T.im ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (boxBoundary v T R)) (a : ℝ) (ha : a = 0 ∨ a = R) :
    IntervalIntegrable (fun t : ℝ => f (v + (a : ℂ) * T + (t : ℂ))) volume 0 R :=
  (hf.comp (by fun_prop) (fun t ht => horizontal_mem_boundary v T hT R hR t a ht ha)).intervalIntegrable

private theorem vertical_intervalIntegrable (v T : ℂ) (hT : T.im ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (boxBoundary v T R)) (b : ℝ) (hb : b = 0 ∨ b = R) :
    IntervalIntegrable (fun t : ℝ => f (v + (b : ℂ) + (t : ℂ) * T) * T) volume 0 R :=
  ((hf.comp (by fun_prop) (fun t ht => vertical_mem_boundary v T hT R hR t b ht hb)).mul_const T).intervalIntegrable

private theorem clockwiseBoundary_eq (f : ℂ → ℂ) (v T : ℂ) (R : ℕ) :
    clockwiseBoundary f v T R =
      -(∫ t : ℝ in 0..(R : ℝ), f (v + (t : ℂ))) +
      (∫ t : ℝ in 0..(R : ℝ), f (v + (t : ℂ) * T) * T) +
      (∫ t : ℝ in 0..(R : ℝ), f (v + (R : ℂ) * T + (t : ℂ))) -
      (∫ t : ℝ in 0..(R : ℝ), f (v + (R : ℂ) + (t : ℂ) * T) * T) := by
  simp only [clockwiseBoundary, firstSide, secondSide, thirdSide, fourthSide,
    intervalIntegral.integral_symm 0 (R : ℝ), sub_eq_add_neg]

private theorem clockwiseBoundary_congr (v T : ℂ) (hT : T.im ≠ 0) (R : ℕ)
    {f g : ℂ → ℂ} (he : EqOn f g (boxBoundary v T (R : ℝ))) :
    clockwiseBoundary f v T R = clockwiseBoundary g v T R := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have hh (a : ℝ) (ha : a = 0 ∨ a = (R : ℝ)) :
      (∫ t : ℝ in 0..(R : ℝ), f (v + (a : ℂ) * T + (t : ℂ))) =
        ∫ t : ℝ in 0..(R : ℝ), g (v + (a : ℂ) * T + (t : ℂ)) :=
    intervalIntegral.integral_congr (fun t ht => he (horizontal_mem_boundary v T hT _ hR t a ht ha))
  have hv (b : ℝ) (hb : b = 0 ∨ b = (R : ℝ)) :
      (∫ t : ℝ in 0..(R : ℝ), f (v + (b : ℂ) + (t : ℂ) * T) * T) =
        ∫ t : ℝ in 0..(R : ℝ), g (v + (b : ℂ) + (t : ℂ) * T) * T :=
    intervalIntegral.integral_congr (fun t ht => congrArg (fun z => z * T)
      (he (vertical_mem_boundary v T hT _ hR t b ht hb)))
  have hh0 := hh 0 (Or.inl rfl)
  have hv0 := hv 0 (Or.inl rfl)
  have hhR := hh R (Or.inr rfl)
  have hvR := hv R (Or.inr rfl)
  simp only [ofReal_zero, zero_mul, add_zero, ofReal_natCast] at hh0 hv0 hhR hvR
  rw [clockwiseBoundary_eq, clockwiseBoundary_eq, hh0, hv0, hhR, hvR]

private theorem clockwiseBoundary_sub (v T : ℂ) (hT : T.im ≠ 0) (R : ℕ)
    {f g : ℂ → ℂ} (hf : ContinuousOn f (boxBoundary v T (R : ℝ)))
    (hg : ContinuousOn g (boxBoundary v T (R : ℝ))) :
    clockwiseBoundary (fun w => f w - g w) v T R =
      clockwiseBoundary f v T R - clockwiseBoundary g v T R := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have hf0 := horizontal_intervalIntegrable v T hT (R : ℝ) hR hf 0 (Or.inl rfl)
  have hg0 := horizontal_intervalIntegrable v T hT (R : ℝ) hR hg 0 (Or.inl rfl)
  have hf1 := vertical_intervalIntegrable v T hT (R : ℝ) hR hf 0 (Or.inl rfl)
  have hg1 := vertical_intervalIntegrable v T hT (R : ℝ) hR hg 0 (Or.inl rfl)
  have hf2 := horizontal_intervalIntegrable v T hT (R : ℝ) hR hf R (Or.inr rfl)
  have hg2 := horizontal_intervalIntegrable v T hT (R : ℝ) hR hg R (Or.inr rfl)
  have hf3 := vertical_intervalIntegrable v T hT (R : ℝ) hR hf R (Or.inr rfl)
  have hg3 := vertical_intervalIntegrable v T hT (R : ℝ) hR hg R (Or.inr rfl)
  simp only [ofReal_zero, zero_mul, add_zero, ofReal_natCast] at hf0 hg0 hf1 hg1 hf2 hg2 hf3 hg3
  simp only [clockwiseBoundary_eq, sub_mul]
  rw [intervalIntegral.integral_sub hf0 hg0, intervalIntegral.integral_sub hf1 hg1,
    intervalIntegral.integral_sub hf2 hg2, intervalIntegral.integral_sub hf3 hg3]
  ring

private theorem clockwiseBoundary_fun_sum {ι : Type*} (s : Finset ι)
    (v T : ℂ) (hT : T.im ≠ 0) (R : ℕ) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (boxBoundary v T (R : ℝ))) :
    clockwiseBoundary (fun w => ∑ i ∈ s, f i w) v T R =
      ∑ i ∈ s, clockwiseBoundary (f i) v T R := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have h0 (i : ι) (hi : i ∈ s) := horizontal_intervalIntegrable v T hT (R : ℝ) hR (hf i hi) 0 (Or.inl rfl)
  have h1 (i : ι) (hi : i ∈ s) := vertical_intervalIntegrable v T hT (R : ℝ) hR (hf i hi) 0 (Or.inl rfl)
  have h2 (i : ι) (hi : i ∈ s) := horizontal_intervalIntegrable v T hT (R : ℝ) hR (hf i hi) R (Or.inr rfl)
  have h3 (i : ι) (hi : i ∈ s) := vertical_intervalIntegrable v T hT (R : ℝ) hR (hf i hi) R (Or.inr rfl)
  simp only [ofReal_zero, zero_mul, add_zero, ofReal_natCast] at h0 h1 h2 h3
  simp only [clockwiseBoundary_eq, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum h0, intervalIntegral.integral_finsetSum h1,
    intervalIntegral.integral_finsetSum h2, intervalIntegral.integral_finsetSum h3]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]

private theorem clockwiseBoundary_const_mul (v T : ℂ) (R : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    clockwiseBoundary (fun w => c * f w) v T R = c * clockwiseBoundary f v T R := by
  simp only [clockwiseBoundary_eq, mul_assoc, intervalIntegral.integral_const_mul]
  ring

private theorem principalPart_analyticAt (p : ℂ) (N : ℕ) (A : ℕ → ℂ) {w : ℂ}
    (hw : w ≠ p) : AnalyticAt ℂ (FinitePrincipalParts.principalPart p N A) w := by
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

private theorem principalPart_continuousOn (p : ℂ) (N : ℕ) (A : ℕ → ℂ)
    {s : Set ℂ} (hs : ∀ w ∈ s, w ≠ p) :
    ContinuousOn (FinitePrincipalParts.principalPart p N A) s := by
  apply continuousOn_finsetSum
  intro j hj
  exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
    (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (hs w hw)))

private theorem clockwiseBoundary_primitive (v T : ℂ) (hT : T.im ≠ 0) (R : ℕ)
    (F f : ℂ → ℂ) (hd : ∀ w ∈ boxBoundary v T (R : ℝ), HasDerivAt F (f w) w)
    (hc : ContinuousOn f (boxBoundary v T (R : ℝ))) : clockwiseBoundary f v T R = 0 := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have hh (a : ℝ) (ha : a = 0 ∨ a = (R : ℝ)) :
      (∫ t : ℝ in 0..(R : ℝ), f (v + (a : ℂ) * T + (t : ℂ))) =
        F (v + (a : ℂ) * T + (R : ℂ)) - F (v + (a : ℂ) * T) := by
    have hd' (t : ℝ) (ht : t ∈ [[0, (R : ℝ)]]) :
        HasDerivAt (fun t : ℝ => F (v + (a : ℂ) * T + (t : ℂ)))
          (f (v + (a : ℂ) * T + (t : ℂ))) t := by
      have hu : HasDerivAt (fun t : ℝ => v + (a : ℂ) * T + (t : ℂ)) 1 t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_add (v + (a : ℂ) * T)
      simpa [Function.comp_def, smul_eq_mul] using
        (hd _ (horizontal_mem_boundary v T hT _ hR t a ht ha)).scomp t hu
    simpa only [ofReal_zero, add_zero, ofReal_natCast] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd'
        (horizontal_intervalIntegrable v T hT _ hR hc a ha)
  have hv (b : ℝ) (hb : b = 0 ∨ b = (R : ℝ)) :
      (∫ t : ℝ in 0..(R : ℝ), f (v + (b : ℂ) + (t : ℂ) * T) * T) =
        F (v + (b : ℂ) + (R : ℂ) * T) - F (v + (b : ℂ)) := by
    have hd' (t : ℝ) (ht : t ∈ [[0, (R : ℝ)]]) :
        HasDerivAt (fun t : ℝ => F (v + (b : ℂ) + (t : ℂ) * T))
          (f (v + (b : ℂ) + (t : ℂ) * T) * T) t := by
      have hu : HasDerivAt (fun t : ℝ => v + (b : ℂ) + (t : ℂ) * T) T t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const T).const_add (v + (b : ℂ))
      simpa [Function.comp_def, smul_eq_mul, mul_comm] using
        (hd _ (vertical_mem_boundary v T hT _ hR t b ht hb)).scomp t hu
    simpa only [ofReal_zero, zero_mul, add_zero, ofReal_natCast] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd'
        (vertical_intervalIntegrable v T hT _ hR hc b hb)
  have hh0 := hh 0 (Or.inl rfl)
  have hv0 := hv 0 (Or.inl rfl)
  have hhR := hh R (Or.inr rfl)
  have hvR := hv R (Or.inr rfl)
  simp only [ofReal_zero, zero_mul, add_zero, ofReal_natCast] at hh0 hv0 hhR hvR
  rw [clockwiseBoundary_eq, hh0, hv0, hhR, hvR]
  have he : v + (R : ℂ) * T + (R : ℂ) = v + (R : ℂ) + (R : ℂ) * T := by ring
  rw [he]
  ring

private theorem inversePower_primitive (p : ℂ) (n : ℕ) {w : ℂ} (hw : w ≠ p) :
    HasDerivAt (fun z : ℂ => ((z - p) ^ (n + 1))⁻¹ / (-(n + 1 : ℂ)))
      (1 / (w - p) ^ (n + 1 + 1)) w := by
  have hn := sub_ne_zero.mpr hw
  have hk : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  convert! ((((hasDerivAt_id w).sub_const p).pow (n + 1)).inv
    (pow_ne_zero _ hn)).div_const (-(n + 1 : ℂ)) using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.pow_apply, id_eq, mul_one, pow_succ]
  field_simp [hn, pow_ne_zero n hn, hk]

private theorem boundary_ne_center (v T p : ℂ) (R : ℝ) (hp : p ∈ openBox v T R)
    {w : ℂ} (hw : w ∈ boxBoundary v T R) : w ≠ p := by
  intro he
  exact hw.2 (he ▸ hp)

private theorem clockwiseBoundary_higher_inverse_power (v T p : ℂ) (R n : ℕ)
    (hT : T.im ≠ 0) (hp : p ∈ openBox v T (R : ℝ)) :
    clockwiseBoundary (fun w => 1 / (w - p) ^ (n + 1 + 1)) v T R = 0 := by
  apply clockwiseBoundary_primitive v T hT R
    (fun z : ℂ => ((z - p) ^ (n + 1))⁻¹ / (-(n + 1 : ℂ)))
  · intro w hw
    exact inversePower_primitive p n (boundary_ne_center v T p _ hp hw)
  · exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
      (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (boundary_ne_center v T p _ hp hw)))

lemma tilted_boundary_zero_of_differentiableAt (f : ℂ → ℂ) (v T : ℂ) (R : ℕ)
    (hT : T.im ≠ 0)
    (hf : ∀ z ∈ closedBox v T (R : ℝ), DifferentiableAt ℂ f z) :
    clockwiseBoundary f v T R = 0 := by
  let L : ℝ × ℝ →L[ℝ] ℂ :=
    T • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
      Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL (p : ℝ × ℝ) : L p = (p.1 : ℂ) * T + (p.2 : ℂ) := by
    simp [L, mul_comm]
  let A : ℝ × ℝ → ℂ := fun p => v + L p
  have hA (p : ℝ × ℝ) : A p = v + (p.1 : ℂ) * T + (p.2 : ℂ) := by
    simp [A, hL, add_assoc]
  have hAmem (p : ℝ × ℝ) (hp : p ∈ Icc 0 (R : ℝ) ×ˢ Icc 0 (R : ℝ)) :
      A p ∈ closedBox v T (R : ℝ) := by
    have hc : UpperWindow.coords T ((p.1 : ℂ) * T + (p.2 : ℂ)) = p := by
      apply Prod.ext <;> simp [UpperWindow.coords, Complex.mul_re, Complex.mul_im, hT]
    have he : A p - v = (p.1 : ℂ) * T + (p.2 : ℂ) := by rw [hA]; ring
    change 0 ≤ (UpperWindow.coords T (A p - v)).1 ∧
      (UpperWindow.coords T (A p - v)).1 ≤ R ∧
      0 ≤ (UpperWindow.coords T (A p - v)).2 ∧
      (UpperWindow.coords T (A p - v)).2 ≤ R
    rw [he, hc]
    exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  let F : ℝ × ℝ → ℂ := f ∘ A
  let F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    (deriv f (A p)) • L
  have hFderiv (p : ℝ × ℝ) (hp : p ∈ Icc 0 (R : ℝ) ×ˢ Icc 0 (R : ℝ)) :
      HasFDerivAt F (F' p) p := by
    have hd := ((hf (A p) (hAmem p hp)).hasDerivAt.complexToReal_fderiv).comp p
      (L.hasFDerivAt.const_add v)
    simpa [F, A, F', ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp] using hd
  have hFcont : ContinuousOn F (Icc 0 (R : ℝ) ×ˢ Icc 0 (R : ℝ)) := by
    intro p hp
    exact (hFderiv p hp).continuousAt.continuousWithinAt
  have hnonneg : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hinner (p : ℝ × ℝ)
      (hp : p ∈ Ioo (min 0 (R : ℝ)) (max 0 (R : ℝ)) ×ˢ
        Ioo (min 0 (R : ℝ)) (max 0 (R : ℝ))) :
      p ∈ Icc 0 (R : ℝ) ×ˢ Icc 0 (R : ℝ) := by
    simpa only [min_eq_left hnonneg, max_eq_right hnonneg] using
      (show p ∈ Icc (min 0 (R : ℝ)) (max 0 (R : ℝ)) ×ˢ
        Icc (min 0 (R : ℝ)) (max 0 (R : ℝ)) from
        ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩)
  have hdiv (p : ℝ × ℝ) : F' p (1, 0) + (-(T • F' p)) (0, 1) = 0 := by
    simp [F', hL, mul_comm]
  have hzero := integral2_divergence_prod_of_hasFDerivAt F (fun p => -(T • F p))
    F' (fun p => -(T • F' p)) 0 0 (R : ℝ) (R : ℝ)
    (by simpa only [uIcc_of_le hnonneg] using hFcont)
    (by simpa only [uIcc_of_le hnonneg] using (show ContinuousOn (fun p => -(T • F p)) _ from (hFcont.const_smul T).neg))
    (fun p hp => hFderiv p (hinner p hp))
    (fun p hp => ((hFderiv p (hinner p hp)).const_smul T).neg)
    (by simp only [hdiv]; exact integrableOn_zero)
  simp only [hdiv, intervalIntegral.integral_zero] at hzero
  unfold clockwiseBoundary firstSide secondSide thirdSide fourthSide
  simp only [F, Function.comp_apply, hA, ofReal_zero, zero_mul, add_zero,
    smul_eq_mul, intervalIntegral.integral_neg] at hzero
  simp only [intervalIntegral.integral_symm 0 (R : ℝ)]
  have hpoint (t : ℝ) : v + (R : ℂ) + (t : ℂ) * T =
      v + (t : ℂ) * T + (R : ℂ) := by ring
  simp only [Complex.ofReal_natCast, mul_comm T] at hzero
  simp_rw [hpoint]
  linear_combination -hzero

lemma clockwiseBoundary_eq_zero_of_analyticOnNhd (f : ℂ → ℂ) (v T : ℂ) (R : ℕ)
    (hT : T.im ≠ 0) (hf : AnalyticOnNhd ℂ f (closedBox v T (R : ℝ))) :
    clockwiseBoundary f v T R = 0 :=
  tilted_boundary_zero_of_differentiableAt f v T R hT
    (fun z hz => (hf z hz).differentiableAt)

private theorem exists_regularized_remainder (f : ℂ → ℂ) (v T : ℂ) (R : ℕ)
    (P : Finset ℂ) (r : ℂ → ℝ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ)
    (g : ℂ → ℂ → ℂ) (hr : ∀ a ∈ P, 0 < r a)
    (hinside : ∀ a ∈ P, Metric.closedBall a (r a) ⊆ openBox v T (R : ℝ))
    (hdisj : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      Disjoint (Metric.closedBall a (r a)) (Metric.closedBall b (r b)))
    (hf : AnalyticOnNhd ℂ f (closedBox v T (R : ℝ) \ (P : Set ℂ)))
    (hg : ∀ a ∈ P, AnalyticOnNhd ℂ (g a) (Metric.closedBall a (r a)))
    (hfg : ∀ a ∈ P, ∀ z ∈ Metric.closedBall a (r a), z ≠ a →
      f z = FinitePrincipalParts.principalPart a (N a) (A a) z + g a z) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (closedBox v T (R : ℝ)) ∧
      EqOn H (fun w => f w - FinitePrincipalParts.finitePrincipalPart P id N A w)
        (boxBoundary v T (R : ℝ)) := by
  classical
  let q : ℂ → ℂ := fun w => f w - FinitePrincipalParts.finitePrincipalPart P id N A w
  let H : ℂ → ℂ := fun w => if w ∈ P then limUnder (𝓝[≠] w) q else q w
  have htclosed : IsClosed (P : Set ℂ) := P.finite_toSet.isClosed
  have hc (a : ℂ) (ha : a ∈ P) : a ∈ Metric.closedBall a (r a) :=
    Metric.mem_closedBall_self (hr a ha).le
  have hnoother (a : ℂ) (ha : a ∈ P) (w : ℂ)
      (hw : w ∈ Metric.closedBall a (r a)) (b : ℂ) (hb : b ∈ P)
      (he : w = b) : b = a := by
    by_contra hba
    exact Set.disjoint_left.mp (hdisj a ha b hb (Ne.symm hba)) hw (he ▸ hc b hb)
  have hHoff (w : ℂ) (hw : w ∉ P) : H w = q w := by simp [H, hw]
  have hqana (w : ℂ) (hw : w ∈ closedBox v T (R : ℝ) \ (P : Set ℂ)) :
      AnalyticAt ℂ q w := by
    apply (hf w hw).sub
    apply Finset.analyticAt_fun_sum
    intro a ha
    apply principalPart_analyticAt
    intro he
    exact hw.2 (he ▸ ha)
  have hHcenter (a : ℂ) (ha : a ∈ P) : AnalyticAt ℂ H a := by
    let L : ℂ → ℂ := fun w => g a w -
      ∑ b ∈ P.erase a, FinitePrincipalParts.principalPart b (N b) (A b) w
    have hLana : AnalyticAt ℂ L a := by
      apply (hg a ha a (hc a ha)).sub
      apply Finset.analyticAt_fun_sum
      intro b hb
      exact principalPart_analyticAt b (N b) (A b) (Ne.symm (Finset.mem_erase.mp hb).1)
    have hqLpoint (w : ℂ) (hw : w ∈ Metric.closedBall a (r a)) (hne : w ≠ a) :
        q w = L w := by
      dsimp only [q, L, FinitePrincipalParts.finitePrincipalPart, id_eq]
      rw [hfg a ha w hw hne, ← Finset.sum_erase_add P
        (fun b => FinitePrincipalParts.principalPart b (N b) (A b) w) ha]
      ring
    have hqL : q =ᶠ[𝓝[≠] a] L := by
      apply eventually_nhdsWithin_iff.mpr
      filter_upwards [Metric.closedBall_mem_nhds a (hr a ha)] with w hw hne
      exact hqLpoint w hw hne
    have hlim : Tendsto q (𝓝[≠] a) (𝓝 (L a)) :=
      (hLana.continuousAt.tendsto.mono_left inf_le_left).congr' hqL.symm
    have hvalue : H a = L a := by
      dsimp only [H]
      rw [if_pos ha]
      exact hlim.limUnder_eq
    apply hLana.congr
    filter_upwards [Metric.closedBall_mem_nhds a (hr a ha)] with w hw
    by_cases he : w = a
    · simpa only [he] using hvalue.symm
    · have hwt : w ∉ P := by
        intro hwP
        have hwa := hnoother a ha w hw w hwP rfl
        exact he hwa
      rw [hHoff w hwt, hqLpoint w hw he]
  refine ⟨H, ?_, ?_⟩
  · intro w hw
    by_cases hwt : w ∈ P
    · exact hHcenter w hwt
    · apply (hqana w ⟨hw, hwt⟩).congr
      filter_upwards [htclosed.isOpen_compl.mem_nhds hwt] with z hz
      exact (hHoff z hz).symm
  · intro w hw
    apply hHoff
    intro hwP
    exact hw.2 (hinside w hwP (hc w hwP))

private theorem tiltedInv_log_neg_upper (w : ℂ) (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w - (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw,
    Complex.ofReal_sub]
  ring

private theorem tiltedInv_log_neg_lower (w : ℂ) (hw : w.im < 0) :
    Complex.log (-w) = Complex.log w + (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw,
    Complex.ofReal_add]
  ring

private theorem tiltedInv_integral_log (w d : ℂ) (r s : ℝ)
    (hslit : ∀ t ∈ Set.uIcc r s, w + (t : ℂ) * d ∈ Complex.slitPlane) :
    (∫ t : ℝ in r..s, (w + (t : ℂ) * d)⁻¹ * d) =
      Complex.log (w + (s : ℂ) * d) - Complex.log (w + (r : ℂ) * d) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have hd : HasDerivAt (fun x : ℝ => w + (x : ℂ) * d) d t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const d).const_add w
    simpa [div_eq_mul_inv, mul_comm] using hd.clog_real (hslit t ht)
  · apply ContinuousOn.intervalIntegrable
    exact ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn.inv₀
      (fun t ht => Complex.slitPlane_ne_zero (hslit t ht))).mul continuousOn_const

private theorem tiltedInv_integral_neg_log (w d : ℂ) (r s : ℝ)
    (hslit : ∀ t ∈ Set.uIcc r s, -(w + (t : ℂ) * d) ∈ Complex.slitPlane) :
    (∫ t : ℝ in r..s, (w + (t : ℂ) * d)⁻¹ * d) =
      Complex.log (-(w + (s : ℂ) * d)) -
        Complex.log (-(w + (r : ℂ) * d)) := by
  have heq (t : ℝ) : -w + (t : ℂ) * -d = -(w + (t : ℂ) * d) := by ring
  have h := tiltedInv_integral_log (-w) (-d) r s (by
    intro t ht
    rw [heq]
    exact hslit t ht)
  simpa only [heq, inv_neg, neg_mul_neg] using h

theorem clockwiseBoundary_inv (v T a : ℂ) (R : ℕ)
    (hT : 0 < T.im) (ha : a ∈ UpperContour.openBox v T (R : ℝ)) :
    UpperContour.clockwiseBoundary (fun z => 1 / (z - a)) v T R =
      -2 * (Real.pi : ℂ) * Complex.I := by
  let b : ℝ := (a.im - v.im) / T.im
  let c : ℝ := (a.re - v.re) - b * T.re
  change 0 < b ∧ b < (R : ℝ) ∧ 0 < c ∧ c < (R : ℝ) at ha
  rcases ha with ⟨hb0, hbR, hc0, hcR⟩
  have him : a.im - v.im = b * T.im := by
    dsimp [b]
    field_simp
  have hre : a.re - v.re = b * T.re + c := by dsimp [c]; ring
  have hbot : ∀ t : ℝ, v - a + (t : ℂ) * 1 ∈ Complex.slitPlane := by
    intro t
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [add_im, sub_im, mul_one, ofReal_im, add_zero]
    nlinarith [mul_pos hb0 hT]
  have htop : ∀ t : ℝ, v + (R : ℂ) * T - a + (t : ℂ) * 1 ∈
      Complex.slitPlane := by
    intro t
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [add_im, sub_im, mul_im, natCast_re, natCast_im, mul_one,
      zero_mul, add_zero, ofReal_im]
    nlinarith [mul_pos (sub_pos.mpr hbR) hT]
  have hright : ∀ t : ℝ, v + (R : ℂ) - a + (t : ℂ) * T ∈
      Complex.slitPlane := by
    intro t
    apply Complex.mem_slitPlane_iff.mpr
    by_cases hz : (v + (R : ℂ) - a + (t : ℂ) * T).im = 0
    · left
      simp only [add_im, sub_im, mul_im, natCast_im, ofReal_re,
        ofReal_im, zero_mul, add_zero] at hz
      have htb : t = b := by nlinarith
      simp only [add_re, sub_re, mul_re, natCast_re, ofReal_re, ofReal_im,
        zero_mul, sub_zero]
      rw [htb]
      linarith
    · exact Or.inr hz
  have hleft : ∀ t : ℝ, -(v - a + (t : ℂ) * T) ∈ Complex.slitPlane := by
    intro t
    apply Complex.mem_slitPlane_iff.mpr
    by_cases hz : (-(v - a + (t : ℂ) * T)).im = 0
    · left
      simp only [neg_im, add_im, sub_im, mul_im, ofReal_re,
        ofReal_im, zero_mul, add_zero, neg_eq_zero] at hz
      have htb : t = b := by nlinarith
      simp only [neg_re, add_re, sub_re, mul_re, ofReal_re, ofReal_im,
        zero_mul, sub_zero]
      rw [htb]
      linarith
    · exact Or.inr hz
  have h1 : UpperContour.firstSide (fun z => 1 / (z - a)) v R =
      Complex.log (v - a) - Complex.log (v + (R : ℂ) - a) := by
    unfold UpperContour.firstSide
    have h := tiltedInv_integral_log (v - a) 1 (R : ℝ) 0 (fun t _ => hbot t)
    simp only [ofReal_natCast, mul_one] at h
    simpa only [one_div, ofReal_zero, add_zero, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm, mul_comm] using h
  have h2 : UpperContour.secondSide (fun z => 1 / (z - a)) v T R =
      Complex.log (-(v + (R : ℂ) * T - a)) - Complex.log (-(v - a)) := by
    unfold UpperContour.secondSide
    have h := tiltedInv_integral_neg_log (v - a) T 0 (R : ℝ) (fun t _ => hleft t)
    simp only [ofReal_natCast, ofReal_zero, zero_mul, add_zero] at h
    simpa only [one_div, ofReal_zero, add_zero, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm, mul_comm] using h
  have h3 : UpperContour.thirdSide (fun z => 1 / (z - a)) v T R =
      Complex.log (v + (R : ℂ) * T + (R : ℂ) - a) -
        Complex.log (v + (R : ℂ) * T - a) := by
    unfold UpperContour.thirdSide
    have h := tiltedInv_integral_log (v + (R : ℂ) * T - a) 1 0 (R : ℝ)
      (fun t _ => htop t)
    simp only [ofReal_natCast, ofReal_zero, add_zero, mul_one] at h
    simpa only [one_div, ofReal_zero, add_zero, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm, mul_comm] using h
  have h4 : UpperContour.fourthSide (fun z => 1 / (z - a)) v T R =
      Complex.log (v + (R : ℂ) - a) -
        Complex.log (v + (R : ℂ) * T + (R : ℂ) - a) := by
    unfold UpperContour.fourthSide
    have h := tiltedInv_integral_log (v + (R : ℂ) - a) T (R : ℝ) 0
      (fun t _ => hright t)
    simp only [ofReal_natCast, ofReal_zero, zero_mul, add_zero] at h
    simpa only [one_div, ofReal_zero, add_zero, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm, mul_comm] using h
  have hv : (v - a).im < 0 := by simp only [sub_im]; nlinarith [mul_pos hb0 hT]
  have hvT : 0 < (v + (R : ℂ) * T - a).im := by
    simp only [add_im, sub_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero]
    nlinarith [mul_pos (sub_pos.mpr hbR) hT]
  unfold UpperContour.clockwiseBoundary
  rw [h1, h2, h3, h4, tiltedInv_log_neg_upper _ hvT, tiltedInv_log_neg_lower _ hv]
  ring

private theorem clockwiseBoundary_principalPart_of_inv (v T p : ℂ) (R : ℕ)
    (N : ℕ) (A : ℕ → ℂ) (hT : T.im ≠ 0)
    (hp : p ∈ openBox v T (R : ℝ))
    (hinv : clockwiseBoundary (fun w => 1 / (w - p)) v T R =
      -2 * (Real.pi : ℂ) * I) :
    clockwiseBoundary (FinitePrincipalParts.principalPart p N A) v T R =
      -2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient N A := by
  have hkernel (j : ℕ) :
      clockwiseBoundary (fun w => 1 / (w - p) ^ (j + 1)) v T R =
        if j = 0 then -2 * (Real.pi : ℂ) * I else 0 := by
    cases j with
    | zero => simpa only [zero_add, pow_one, ↓reduceIte] using hinv
    | succ n => exact clockwiseBoundary_higher_inverse_power v T p R n hT hp
  unfold FinitePrincipalParts.principalPart
  rw [clockwiseBoundary_fun_sum (Finset.range N) v T hT R]
  · have hb (j : ℕ) :
        clockwiseBoundary (fun w => A j / (w - p) ^ (j + 1)) v T R =
          A j * (if j = 0 then -2 * (Real.pi : ℂ) * I else 0) := by
      have heq : (fun w : ℂ => A j / (w - p) ^ (j + 1)) =
          (fun w : ℂ => A j * (1 / (w - p) ^ (j + 1))) := by
        ext w
        simp [div_eq_mul_inv]
      rw [heq, clockwiseBoundary_const_mul, hkernel]
    simp_rw [hb]
    cases N with
    | zero => simp [FinitePrincipalParts.residueCoefficient]
    | succ n =>
      rw [Finset.sum_eq_single 0]
      · simp [FinitePrincipalParts.residueCoefficient, mul_comm]
      · intro b hb hb0
        simp [hb0]
      · simp
  · intro j hj
    exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
      (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (boundary_ne_center v T p _ hp hw)))

/-- The clockwise boundary of the actual tilted parallelogram records the
finite principal-part coefficients with the factor `-2πi`. -/
theorem parallelogram_finite_principal_parts (f : ℂ → ℂ) (v T : ℂ)
    (hT : 0 < T.im) (R : ℕ) (hR : 1 ≤ R) (P : Finset ℂ)
    (r : ℂ → ℝ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ)
    (hr : ∀ a ∈ P, 0 < r a)
    (hinside : ∀ a ∈ P, Metric.closedBall a (r a) ⊆ openBox v T (R : ℝ))
    (hdisj : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      Disjoint (Metric.closedBall a (r a)) (Metric.closedBall b (r b)))
    (hf : AnalyticOnNhd ℂ f (closedBox v T (R : ℝ) \ (P : Set ℂ)))
    (hg : ∀ a ∈ P, AnalyticOnNhd ℂ (g a) (Metric.closedBall a (r a)))
    (hfg : ∀ a ∈ P, ∀ z ∈ Metric.closedBall a (r a), z ≠ a →
      f z = FinitePrincipalParts.principalPart a (N a) (A a) z + g a z) :
    clockwiseBoundary f v T R = -2 * (Real.pi : ℂ) * Complex.I *
      ∑ a ∈ P, FinitePrincipalParts.residueCoefficient (N a) (A a) := by
  classical
  have hp (a : ℂ) (ha : a ∈ P) : a ∈ openBox v T (R : ℝ) :=
    hinside a ha (Metric.mem_closedBall_self (hr a ha).le)
  have hboundary : boxBoundary v T (R : ℝ) ⊆
      closedBox v T (R : ℝ) \ (P : Set ℂ) := by
    intro w hw
    refine ⟨hw.1, ?_⟩
    intro hwP
    exact hw.2 (hp w hwP)
  have hPcont : ContinuousOn (FinitePrincipalParts.finitePrincipalPart P id N A)
      (boxBoundary v T (R : ℝ)) := by
    apply continuousOn_finsetSum
    intro a ha
    exact principalPart_continuousOn a (N a) (A a)
      (fun w hw => boundary_ne_center v T a _ (hp a ha) hw)
  obtain ⟨H, hHana, hHe⟩ := exists_regularized_remainder f v T R P r N A g
    hr hinside hdisj hf hg hfg
  have hHzero : clockwiseBoundary H v T R = 0 :=
    clockwiseBoundary_eq_zero_of_analyticOnNhd H v T R hT.ne' hHana
  have hfP : clockwiseBoundary f v T R =
      clockwiseBoundary (FinitePrincipalParts.finitePrincipalPart P id N A) v T R := by
    have he := clockwiseBoundary_congr v T hT.ne' R hHe
    rw [clockwiseBoundary_sub v T hT.ne' R (hf.continuousOn.mono hboundary) hPcont] at he
    linear_combination -he + hHzero
  rw [hfP]
  change clockwiseBoundary (fun w => ∑ a ∈ P,
    FinitePrincipalParts.principalPart a (N a) (A a) w) v T R = _
  rw [clockwiseBoundary_fun_sum P v T hT.ne' R]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact clockwiseBoundary_principalPart_of_inv v T a R (N a) (A a) hT.ne'
      (hp a ha) (clockwiseBoundary_inv v T a R hT (hp a ha))
  · intro a ha
    exact principalPart_continuousOn a (N a) (A a)
      (fun w hw => boundary_ne_center v T a _ (hp a ha) hw)

lemma simple_principalPart_germ_of_order (f : ℂ → ℂ) (a : ℂ)
    (hf : MeromorphicAt f a) (ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f a) :
    ∃ (A : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g a ∧
      f =ᶠ[𝓝[≠] a] (fun z => A / (z - a) + g z) := by
  have hmul : MeromorphicAt (fun z => (z - a) * f z) a :=
    (show AnalyticAt ℂ (fun z : ℂ => z - a) a by fun_prop).meromorphicAt.mul hf
  have homul : 0 ≤ meromorphicOrderAt (fun z => (z - a) * f z) a := by
    rw [fun_meromorphicOrderAt_mul
      (show AnalyticAt ℂ (fun z : ℂ => z - a) a by fun_prop).meromorphicAt hf,
      meromorphicOrderAt_id_sub_const]
    have h := add_le_add_left ho (1 : WithTop ℤ)
    simpa [add_comm] using h
  obtain ⟨G, hG, hfg⟩ := hmul.meromorphicOrderAt_nonneg_iff.mp homul
  refine ⟨G a, dslope G a, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hG
    exact ⟨q.fslope, hq.has_fpower_series_dslope_fslope⟩
  · filter_upwards [hfg, self_mem_nhdsWithin] with z hz hza
    have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
    rw [dslope_of_ne _ hza]
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    field_simp
    linear_combination hz

lemma kernel_order_ge_neg_one (kind : UpperContour.Kind) (M : SL(2, ℤ))
    (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (x : UpperWindow.Parameters) (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ)
    (k : ℕ × ℕ) (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (UpperContour.kernel kind M m n h ℓ p x)
      (modularPhiPolePoint M (m + 1) n x.1 k.1 k.2) := by
  let a := modularPhiPolePoint M (m + 1) n x.1 k.1 k.2
  have hM : 0 < M 1 0 := hc.1
  have hτ : x.1 ∈ modularPhiDomain M :=
    (UpperWindow.tauRegion_properties M hM ψ hc.2.2.1 x.1 hx.1).1
  have hi : x.1.im ≠ 0 := hx.1.1.ne'
  have hpnum : modularPhiPoleMultiplicity M (m + 1) n a x.1 = 1 :=
    (modularPhiDivisor_simple_of_im_ne_zero M hM (m + 1) n x.1 hτ hi).1 k hk
  have hznumset : modularPhiZeroIndices M (m + 1) n a x.1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact Set.disjoint_left.mp (modularPhiDivisor_disjoint M hM (m + 1) n x.1 hτ)
      ⟨k, hk, rfl⟩ ⟨q, hq.1, hq.2.symm⟩
  have hznum : modularPhiZeroMultiplicity M (m + 1) n a x.1 = 0 := by
    simp [modularPhiZeroMultiplicity, hznumset]
  have honum : meromorphicOrderAt (fun z => modularPhi M (m + 1) n z x.1) a = -1 := by
    rw [modularPhi_order M hM (m + 1) n a x.1 hτ]
    simp [modularPhiDivisorOrder, hznum, hpnum]
  have hE : AnalyticAt ℂ (fun z => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)) a := by
    unfold e UpperWindow.phase
    fun_prop
  have hoE : meromorphicOrderAt (fun z => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)) a = 0 := by
    simp [hE.meromorphicOrderAt_eq, hE.analyticOrderAt_eq_zero.mpr (e_ne_zero _)]
  have hmnum : MeromorphicAt (fun z => modularPhi M (m + 1) n z x.1) a :=
    modularPhi_meromorphic M hM (m + 1) n x.1 hτ a (Set.mem_univ _)
  cases kind with
  | single =>
    change (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (fun z => modularPhi M (m + 1) n z x.1 * e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)) a
    rw [fun_meromorphicOrderAt_mul hmnum hE.meromorphicAt, honum, hoE, add_zero]
  | ratio =>
    have hzdenSet : modularPhiZeroIndices M (m + p) n (a + x.2.2) x.1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact Set.disjoint_left.mp (UpperWindow.no_pinch M h ℓ p m n ψ σ ρ δ hc x hx)
        ⟨k, hk, rfl⟩ ⟨q, hq.1, by dsimp only; rw [← hq.2]; ring⟩
    have hzden : modularPhiZeroMultiplicity M (m + p) n (a + x.2.2) x.1 = 0 := by
      simp [modularPhiZeroMultiplicity, hzdenSet]
    have hmden : MeromorphicAt (fun z => modularPhi M (m + p) n (z + x.2.2) x.1) a := by
      exact (modularPhi_meromorphic M hM (m + p) n x.1 hτ
        (a + x.2.2) (Set.mem_univ _)).comp_analyticAt
          (g := fun z : ℂ => z + x.2.2) (x := a) (by fun_prop)
    have hoden : meromorphicOrderAt (fun z => modularPhi M (m + p) n (z + x.2.2) x.1) a =
        (((0 : ℤ) - (modularPhiPoleMultiplicity M (m + p) n (a + x.2.2) x.1 : ℤ)) : WithTop ℤ) := by
      have hshift := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt
        (f := fun z => modularPhi M (m + p) n z x.1) (c := x.2.2) (x := a)
      simp only [Function.comp_def] at hshift
      rw [hshift, modularPhi_order M hM (m + p) n (a + x.2.2) x.1 hτ]
      simp [modularPhiDivisorOrder, hzden]
    change (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (fun z => (modularPhi M (m + 1) n z x.1 / modularPhi M (m + p) n (z + x.2.2) x.1) *
        e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)) a
    rw [fun_meromorphicOrderAt_mul
      (f := fun z => modularPhi M (m + 1) n z x.1 / modularPhi M (m + p) n (z + x.2.2) x.1)
      (g := fun z => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z))
      (hmnum.div hmden) hE.meromorphicAt,
      fun_meromorphicOrderAt_div hmnum hmden, honum, hoden, hoE, add_zero]
    have hInt : (-1 : ℤ) ≤ -1 - (0 -
        (modularPhiPoleMultiplicity M (m + p) n (a + x.2.2) x.1 : ℤ)) := by omega
    exact WithTop.coe_le_coe.mpr hInt

end SICLean.L4.UpperContourClosureAux
