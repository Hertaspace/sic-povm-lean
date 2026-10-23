import SICLean.L4.UpperWindowParameters
import SICLean.L4.ModularDivisor

set_option autoImplicit false

/-! Elementary coordinate, divisor and exponential helpers. -/

noncomputable section
open Complex Set
open scoped Topology MatrixGroups

namespace SICLean.L4.UpperWindow

lemma denom_im_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℂ)
    (hτ : τ.im ≠ 0) : (etaDenom M τ).im ≠ 0 := by
  simpa [etaDenom] using mul_ne_zero (show (M 1 0 : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hM) hτ

lemma coords_eq_iff (T z : ℂ) (hT : T.im ≠ 0) (a b : ℝ) :
    coords T z = (a, b) ↔ z = (a : ℂ) * T + (b : ℂ) := by
  constructor
  · intro h
    simpa [h] using (coords_reconstruct T z hT).symm
  · rintro rfl
    exact coords_real_combination T hT a b

lemma nonvanishingDomain_of_avoids (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M)
    (hp : ∀ K J : ℕ, z ≠ modularPhiPolePoint M m n τ K J)
    (hz : ∀ K J : ℕ, z ≠ modularPhiZeroPoint M m n τ K J) :
    (z, τ) ∈ modularPhiNonvanishingDomain M m n := by
  refine ⟨hτ, ?_, ?_⟩
  · have he : modularPhiPoleIndices M m n z τ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hp k.1 k.2 hk.2
    simp [modularPhiPoleMultiplicity, he]
  · have he : modularPhiZeroIndices M m n z τ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hz k.1 k.2 hk.2
    simp [modularPhiZeroMultiplicity, he]

lemma fractional_grid_ne (c : ℤ) (hc : 0 < c) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (K j : ℕ) :
    (K + α) / (c : ℝ) ≠ (j : ℝ) := by
  intro he
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hh := (div_eq_iff (ne_of_gt hcR)).mp he
  have h0 : (0 : ℝ) < (c : ℝ) * j - K := by linarith
  have h1 : (c : ℝ) * j - K < 1 := by linarith
  have hz0 : (0 : ℤ) < c * (j : ℤ) - (K : ℤ) := by exact_mod_cast h0
  have hz1 : c * (j : ℤ) - (K : ℤ) < (1 : ℤ) := by exact_mod_cast h1
  omega

lemma norm_e_exp (z : ℂ) : ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  simp [e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

lemma norm_e_of_im_eq (z τ : ℂ) (a : ℝ) (h : z.im = τ.im * a) :
    ‖e z‖ = Real.rpow ‖e τ‖ a := by
  rw [Real.rpow_eq_pow, norm_e_exp, norm_e_exp, ← Real.exp_mul, h]
  congr 1 <;> ring

lemma im_div_combination (T : ℂ) (a b : ℝ) :
    (((a : ℂ) * T + (b : ℂ)) / T).im = -(b * T.im) / Complex.normSq T := by
  simp only [Complex.div_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, add_zero, zero_add]
  ring

lemma quadrant_ne_cone (T v z : ℂ) (hT : 0 < T.im)
    (hv : (0 ≤ v.im ∧ 0 ≤ (v / T).im) ∨ (v.im ≤ 0 ∧ (v / T).im ≤ 0))
    (hz : (0 < (coords T z).1 ∧ 0 < (coords T z).2) ∨
      ((coords T z).1 < 0 ∧ (coords T z).2 < 0)) : v ≠ z := by
  intro he
  subst v
  have hr := coords_reconstruct T z (ne_of_gt hT)
  have hi : z.im = (coords T z).1 * T.im := by
    conv_lhs => rw [← hr]
    simp
  have hd : (z / T).im = -((coords T z).2 * T.im) / Complex.normSq T := by
    conv_lhs => rw [← hr]
    exact im_div_combination T _ _
  have hns : 0 < Complex.normSq T := Complex.normSq_pos.mpr (by
    intro hzero
    simpa [hzero] using hT)
  rcases hv with hv | hv <;> rcases hz with hz | hz
  · have hh : (z / T).im < 0 := by rw [hd]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hz.2 hT)) hns
    linarith [hv.2]
  · have hh : z.im < 0 := by rw [hi]; exact mul_neg_of_neg_of_pos hz.1 hT
    linarith [hv.1]
  · have hh : 0 < z.im := by rw [hi]; exact mul_pos hz.1 hT
    linarith [hv.1]
  · have hh : 0 < (z / T).im := by rw [hd]; exact div_pos (neg_pos.mpr (mul_neg_of_neg_of_pos hz.2 hT)) hns
    linarith [hv.2]

lemma side_tilted_zero (ψ t : ℝ) : side ψ ((t : ℂ) * (Complex.I * rotation ψ)) = 0 := by
  have hh : rotation (-ψ) * rotation ψ = 1 := by
    simp only [rotation, ← Complex.exp_add, Complex.ofReal_neg]
    ring_nf
    exact Complex.exp_zero
  unfold side
  rw [show rotation (-ψ) * ((t : ℂ) * (Complex.I * rotation ψ)) =
    (t : ℂ) * Complex.I * (rotation (-ψ) * rotation ψ) by ring, hh]
  simp

lemma mobius_denominator_relation (M : SL(2, ℤ)) (τ : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    (M 1 0 : ℂ) * etaMobius M τ = (M 0 0 : ℂ) - 1 / etaDenom M τ := by
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by
    exact_mod_cast det_coe_int M
  unfold etaMobius
  field_simp
  unfold etaDenom
  linear_combination -hdet

lemma norm_q_argument (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r : ℤ) (τ z : ℂ)
    (hτ : τ.im ≠ 0) :
    ‖(e τ) ^ r * e z‖ = Real.rpow ‖e τ‖
      ((r : ℝ) + (M 1 0 : ℝ) * (coords (etaDenom M τ) z).1) := by
  rw [e_int_mul, ← e_add']
  apply norm_e_of_im_eq
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  simp [coords, etaDenom]
  field_simp
  <;> ring

lemma norm_Q_argument (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r : ℤ) (τ z : ℂ)
    (hτ : τ.im ≠ 0) :
    ‖(e (etaMobius M τ)) ^ r * e (z / etaDenom M τ)‖ =
      Real.rpow ‖e (etaMobius M τ)‖
        ((r : ℝ) - (M 1 0 : ℝ) * (coords (etaDenom M τ) z).2) := by
  have hTi := denom_im_ne_zero M hM τ hτ
  have hT : etaDenom M τ ≠ 0 := by intro hh; simpa [hh] using hTi
  have hm := congrArg Complex.im (mobius_denominator_relation M τ hT)
  simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero, Complex.sub_im, Complex.div_im, Complex.one_im,
    Complex.one_re, zero_mul, zero_div, zero_sub] at hm
  have hr := coords_reconstruct (etaDenom M τ) z hTi
  have hd := im_div_combination (etaDenom M τ)
    (coords (etaDenom M τ) z).1 (coords (etaDenom M τ) z).2
  rw [hr] at hd
  rw [e_int_mul, ← e_add']
  apply norm_e_of_im_eq
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, hd]
  simp only [neg_neg, one_mul] at hm
  linear_combination (coords (etaDenom M τ) z).2 * hm

lemma affine_divisor_signs (c δ H : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hχ : c * δ < 1) (hH0 : c * δ < H) (hH1 : H < 1) (K : ℕ) :
    0 < δ + K / c ∧ δ - (H + K) / c < 0 ∧
      δ - (1 + K) / c < 0 ∧ 0 < δ + (1 + K - H) / c := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  refine ⟨add_pos_of_pos_of_nonneg hδ (div_nonneg hK hc.le), ?_, ?_, ?_⟩
  · have hh : δ < (H + K) / c := (lt_div_iff₀ hc).mpr (by nlinarith)
    linarith
  · have hh : δ < (1 + K) / c := (lt_div_iff₀ hc).mpr (by nlinarith)
    linarith
  · exact add_pos hδ (div_pos (by linarith) hc)

lemma tilted_ne_cone (T : ℂ) (ψ t : ℝ) (z : ℂ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (hTi : T.im ≠ 0)
    (hz : (0 < (coords T z).1 ∧ 0 < (coords T z).2) ∨
      ((coords T z).1 < 0 ∧ (coords T z).2 < 0)) :
    (t : ℂ) * (Complex.I * rotation ψ) ≠ z := by
  intro he
  have hr := coords_reconstruct T z hTi
  have hs := side_tilted_zero ψ t
  rw [he, ← hr] at hs
  rcases hz with hz | hz
  · have hh := side_positive_combination T ψ _ _ hT hTψ hψ hz.1 hz.2
    linarith
  · have hh := side_negative_combination T ψ _ _ hT hTψ hψ hz.1 hz.2
    linarith

lemma window_height_bounds (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    let H := coords (etaDenom M x.1) (height M p x.1 x.2.2)
    0 < (M 1 0 : ℝ) ∧ 0 < δ ∧ (M 1 0 : ℝ) * δ < 1 ∧
      (M 1 0 : ℝ) * δ < H.1 ∧ (M 1 0 : ℝ) * δ < H.2 ∧ H.1 < 1 ∧ H.2 < 1 := by
  have hm := radius_margins M ψ σ ρ δ hc
  have hi := coordinate_inequalities M h ℓ p ψ σ ρ δ hc x hx
  refine ⟨by exact_mod_cast hc.1, hc.2.2.2.2.2.2.1, hm.2.2.2.2.2,
    hi.2.2.1, hi.2.2.2.1, ?_, ?_⟩
  · linarith [hi.1, hi.2.2.2.2.1]
  · linarith [hi.2.1, hi.2.2.2.2.2]

lemma window_affine_signs (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ)
    (K J : ℕ) :
    let H := coords (etaDenom M x.1) (height M p x.1 x.2.2)
    (0 < δ + K / (M 1 0 : ℝ) ∧ δ - (H.1 + K) / (M 1 0 : ℝ) < 0 ∧
      δ - (1 + K) / (M 1 0 : ℝ) < 0 ∧ 0 < δ + (1 + K - H.1) / (M 1 0 : ℝ)) ∧
    (0 < δ + J / (M 1 0 : ℝ) ∧ δ - (H.2 + J) / (M 1 0 : ℝ) < 0 ∧
      δ - (1 + J) / (M 1 0 : ℝ) < 0 ∧ 0 < δ + (1 + J - H.2) / (M 1 0 : ℝ)) := by
  have hh := window_height_bounds M h ℓ p ψ σ ρ δ hc x hx
  exact ⟨affine_divisor_signs _ _ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.2.1 K,
    affine_divisor_signs _ _ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.2 J⟩

lemma coords_height (M : SL(2, ℤ)) (hM : 0 < M 1 0) (p : ℤ) (τ y : ℂ)
    (hτ : τ.im ≠ 0) :
    coords (etaDenom M τ) (height M p τ y) =
      ((p : ℝ) + (M 1 0 : ℝ) * (coords (etaDenom M τ) y).1,
        1 + (M 1 0 : ℝ) * (coords (etaDenom M τ) y).2) := by
  apply (coords_eq_iff _ _ (denom_im_ne_zero M hM τ hτ) _ _).mpr
  have hy := coords_reconstruct (etaDenom M τ) y (denom_im_ne_zero M hM τ hτ)
  unfold height
  push_cast
  linear_combination -(M 1 0 : ℂ) * hy

lemma reflected_norm (q a : ℂ) (hq : q ≠ 0) (r : ℝ)
    (ha : ‖a‖ = Real.rpow ‖q‖ r) :
    ‖q / a‖ = Real.rpow ‖q‖ (1 - r) := by
  simp only [Real.rpow_eq_pow] at ha ⊢
  rw [norm_div, ha, Real.rpow_sub (norm_pos_iff.mpr hq), Real.rpow_one]

lemma delta_grid_ne (c : ℤ) (hc : 0 < c) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : (c : ℝ) * δ < 1) (K j : ℕ) :
    δ + K / (c : ℝ) ≠ (j : ℝ) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  convert fractional_grid_ne c hc ((c : ℝ) * δ) (mul_pos hcR hδ0) hδ1 K j using 1
  field_simp
  <;> ring

lemma height_grid_ne (c : ℤ) (hc : 0 < c) (δ H : ℝ)
    (hδ0 : 0 < δ) (hH0 : (c : ℝ) * δ < H) (hH1 : H < 1) (K j : ℕ) :
    δ + (1 + K - H) / (c : ℝ) ≠ (j : ℝ) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hα0 : 0 < 1 + (c : ℝ) * δ - H := by nlinarith
  have hα1 : 1 + (c : ℝ) * δ - H < 1 := by linarith
  convert fractional_grid_ne c hc (1 + (c : ℝ) * δ - H) hα0 hα1 K j using 1
  field_simp
  <;> ring

end SICLean.L4.UpperWindow
