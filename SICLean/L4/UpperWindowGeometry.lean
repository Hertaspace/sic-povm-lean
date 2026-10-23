import SICLean.L4.QProduct
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

/-!
# Real coordinates and the two rotation sectors

`coords` is an explicit real coordinate map,
total even at Im T=0; reconstruction is asserted only when Im T≠0.
[RW26, p. 28, p. 29, Appendix A.2]. Coordinates, sides, and angles are formalized here.
-/

noncomputable section
open Complex Set
open scoped Topology

namespace SICLean.L4.UpperWindow

/-- Coordinates in the ordered real basis (T,1), not (1,T). -/
def coords (T z : ℂ) : ℝ × ℝ :=
  (z.im / T.im, z.re - (z.im / T.im) * T.re)

def rotation (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

/-- Positive on the right of the upward direction i exp(iψ). -/
def side (ψ : ℝ) (z : ℂ) : ℝ := (rotation (-ψ) * z).re

/--
Coordinate inversion; the basis (T,1).
[RW26, p. 28, Appendix A.2].
-/
theorem coords_reconstruct (T z : ℂ) (hT : T.im ≠ 0) :
    (coords T z).1 * T + ((coords T z).2 : ℂ) = z := by
  apply Complex.ext
  · simp only [coords, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one]
    field_simp
    ring
  · simp only [coords, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, zero_add]
    field_simp
    ring

/--
Coordinates of real affine combinations.
[RW26, p. 28, Appendix A.2].
-/
theorem coords_real_combination (T : ℂ) (hT : T.im ≠ 0) (a b : ℝ) :
    coords T ((a : ℂ) * T + (b : ℂ)) = (a, b) := by
  apply Prod.ext
  · simp only [coords, Prod.fst, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, add_zero]
    field_simp
    ring
  · simp only [coords, Prod.snd, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
    ring

/--
Additive coordinate bookkeeping.
[RW26, p. 28, Appendix A.2].
-/
theorem coords_add (T z u : ℂ) : coords T (z + u) = coords T z + coords T u := by
  apply Prod.ext
  · simp only [coords, Prod.fst_add, Complex.add_re, Complex.add_im, add_div]
  · simp only [coords, Prod.snd_add, Complex.add_re, Complex.add_im, add_div]
    ring

/--
Relative-coordinate bookkeeping.
[RW26, p. 28, Appendix A.2].
-/
theorem coords_sub (T z u : ℂ) : coords T (z - u) = coords T z - coords T u := by
  apply Prod.ext
  · simp only [coords, Prod.fst_sub, Complex.sub_re, Complex.sub_im, sub_div]
  · simp only [coords, Prod.snd_sub, Complex.sub_re, Complex.sub_im, sub_div]
    ring

/--
Joint continuity away from Im T=0.
[RW26, p. 28, Appendix A.2].
-/
theorem coords_continuousOn :
    ContinuousOn (fun p : ℂ × ℂ => coords p.1 p.2) {p | p.1.im ≠ 0} := by
  have hIm : Continuous (fun p : ℂ × ℂ => p.1.im) :=
    Complex.continuous_im.comp continuous_fst
  have hRe : Continuous (fun p : ℂ × ℂ => p.1.re) :=
    Complex.continuous_re.comp continuous_fst
  have hzim : Continuous (fun p : ℂ × ℂ => p.2.im) :=
    Complex.continuous_im.comp continuous_snd
  have hzre : Continuous (fun p : ℂ × ℂ => p.2.re) :=
    Complex.continuous_re.comp continuous_snd
  have hdiv : ContinuousOn (fun p : ℂ × ℂ => p.2.im / p.1.im) {p | p.1.im ≠ 0} :=
    hzim.continuousOn.div hIm.continuousOn (fun p hp => hp)
  change ContinuousOn (fun p : ℂ × ℂ =>
    (p.2.im / p.1.im, p.2.re - (p.2.im / p.1.im) * p.1.re)) {p | p.1.im ≠ 0}
  exact ContinuousOn.prodMk hdiv (hzre.continuousOn.sub (hdiv.mul hRe.continuousOn))

/--
Unit direction for the line and arcs.
[RW26, p. 28, Appendix A.2].
-/
theorem rotation_norm_ne_zero (θ : ℝ) : ‖rotation θ‖ = 1 ∧ rotation θ ≠ 0 := by
  have h : rotation θ = Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [rotation, mul_comm]
  constructor
  · rw [h, Complex.norm_exp_ofReal_mul_I]
  · rw [h]
    exact Complex.exp_ne_zero _

private lemma rotation_eq_cos_add_sin (θ : ℝ) :
    rotation θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  unfold rotation
  rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring]
  exact Complex.exp_ofReal_mul_I θ

private lemma rotation_re (θ : ℝ) : (rotation θ).re = Real.cos θ := by
  rw [rotation_eq_cos_add_sin]
  simp [Complex.cos_ofReal_re]

private lemma rotation_im (θ : ℝ) : (rotation θ).im = Real.sin θ := by
  rw [rotation_eq_cos_add_sin]
  simp [Complex.sin_ofReal_re]

private lemma rotation_add (θ α : ℝ) :
    rotation (θ + α) = rotation θ * rotation α := by
  unfold rotation
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma rotation_sub (θ α : ℝ) :
    rotation θ / rotation α = rotation (θ - α) := by
  unfold rotation
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

private lemma side_eq (ψ : ℝ) (z : ℂ) :
    side ψ z = Real.cos ψ * z.re + Real.sin ψ * z.im := by
  unfold side
  rw [rotation_eq_cos_add_sin]
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

private lemma side_mul_eq (ψ : ℝ) (T : ℂ) :
    side ψ T = ‖T‖ * Real.cos (T.arg - ψ) := by
  rw [side_eq, ← Complex.norm_mul_cos_arg T, ← Complex.norm_mul_sin_arg T, Real.cos_sub]
  ring

private lemma side_affine (ψ a b : ℝ) (T : ℂ) :
    side ψ ((a : ℂ) * T + (b : ℂ)) = a * side ψ T + b * Real.cos ψ := by
  rw [side_eq, side_eq]
  simp [Complex.mul_re, Complex.mul_im]
  ring

private lemma cos_arg_sub_psi_pos (T : ℂ) (ψ : ℝ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4) :
    0 < Real.cos (T.arg - ψ) := by
  have hpi := Real.pi_pos
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

private lemma cos_psi_pos (ψ : ℝ) (hψ0 : 0 < ψ) (hψ : ψ < Real.pi / 4) :
    0 < Real.cos ψ := by
  have hpi := Real.pi_pos
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

private lemma arg_ne_zero_of_pos {T : ℂ} (hT : 0 < T.arg) : T ≠ 0 := by
  intro h
  rw [h, Complex.arg_zero] at hT
  exact lt_irrefl 0 hT

private lemma rotation_div (T : ℂ) (hT : T ≠ 0) (θ : ℝ) :
    rotation θ / T = ((‖T‖ : ℝ)⁻¹ : ℂ) * rotation (θ - T.arg) := by
  have hrep : T = (‖T‖ : ℂ) * rotation T.arg := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I T]
    congr 1
    simp [rotation, mul_comm]
  calc
    rotation θ / T = rotation θ / ((‖T‖ : ℂ) * rotation T.arg) := by
          conv_lhs => rw [hrep]
    _ = rotation (θ - T.arg) / (‖T‖ : ℂ) := by
          rw [mul_comm (‖T‖ : ℂ) (rotation T.arg), div_mul_eq_div_div, rotation_sub]
    _ = ((‖T‖ : ℝ)⁻¹ : ℂ) * rotation (θ - T.arg) := by
          rw [div_eq_inv_mul]

private lemma rotation_div_im (T : ℂ) (hT : T ≠ 0) (θ : ℝ) :
    (rotation θ / T).im = ((‖T‖ : ℝ)⁻¹) * Real.sin (θ - T.arg) := by
  rw [rotation_div T hT θ]
  simp [Complex.mul_im, rotation_im]

private lemma affine_rotation_im (T : ℂ) (a b θ : ℝ) :
    (((a : ℂ) + (b : ℂ) / T) * rotation θ).im
      = a * Real.sin θ + b * (rotation θ / T).im := by
  rw [add_mul,
    show (b : ℂ) / T * rotation θ = (b : ℂ) * (rotation θ / T) by ring]
  simp [Complex.mul_im, rotation_im]

/--
Strict positive cone is to the right of the oriented line; [RW26, p. 28, Appendix A.2].
-/
theorem side_positive_combination (T : ℂ) (ψ a b : ℝ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (ha : 0 < a) (hb : 0 < b) :
    0 < side ψ ((a : ℂ) * T + (b : ℂ)) := by
  have hψ0 : 0 < ψ := lt_trans hT hTψ
  have hTne : T ≠ 0 := arg_ne_zero_of_pos hT
  have hr : 0 < ‖T‖ := norm_pos_iff.mpr hTne
  rw [side_affine, side_mul_eq]
  have h1 : 0 < a * (‖T‖ * Real.cos (T.arg - ψ)) :=
    mul_pos ha (mul_pos hr (cos_arg_sub_psi_pos T ψ hT hTψ hψ))
  have h2 : 0 < b * Real.cos ψ := mul_pos hb (cos_psi_pos ψ hψ0 hψ)
  linarith

/--
Strict negative cone is to the left.
No unwrapped angle π<arg<π+arg T is asserted for Complex.arg.
[RW26, p. 28, Appendix A.2].
-/
theorem side_negative_combination (T : ℂ) (ψ a b : ℝ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (ha : a < 0) (hb : b < 0) :
    side ψ ((a : ℂ) * T + (b : ℂ)) < 0 := by
  have hψ0 : 0 < ψ := lt_trans hT hTψ
  have hTne : T ≠ 0 := arg_ne_zero_of_pos hT
  have hr : 0 < ‖T‖ := norm_pos_iff.mpr hTne
  rw [side_affine, side_mul_eq]
  have h1 : a * (‖T‖ * Real.cos (T.arg - ψ)) < 0 :=
    mul_neg_of_neg_of_pos ha (mul_pos hr (cos_arg_sub_psi_pos T ψ hT hTψ hψ))
  have h2 : b * Real.cos ψ < 0 := mul_neg_of_neg_of_pos hb (cos_psi_pos ψ hψ0 hψ)
  linarith

/--
Upper-sector product arguments cannot increase.
[RW26, p. 28, Appendix A.2].
-/
theorem upper_direction_im_nonneg (T : ℂ) (ψ θ : ℝ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (hθ : θ ∈ Icc T.arg (Real.pi / 2 + ψ)) :
    0 ≤ (rotation θ).im ∧ 0 ≤ (rotation θ / T).im := by
  have hpi := Real.pi_pos
  have hTne : T ≠ 0 := arg_ne_zero_of_pos hT
  constructor
  · rw [rotation_im]
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1, hT]
    · linarith [hθ.2, hψ]
  · rw [rotation_div_im T hTne θ]
    apply mul_nonneg
    · exact inv_nonneg.mpr (norm_nonneg T)
    · apply Real.sin_nonneg_of_nonneg_of_le_pi
      · linarith [hθ.1]
      · linarith [hθ.2, hT, hψ]

/--
Reflected lower-sector arguments cannot increase.
The first inequality is non-strict at θ=0.
[RW26, p. 28, Appendix A.2].
-/
theorem lower_direction_im_nonneg (T : ℂ) (ψ θ : ℝ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    0 ≤ (-rotation θ).im ∧ 0 < (-rotation θ / T).im := by
  have hpi := Real.pi_pos
  have hTne : T ≠ 0 := arg_ne_zero_of_pos hT
  have hlo : -Real.pi / 2 < θ := by linarith [hθ.1, hTψ]
  have hhi : θ ≤ 0 := hθ.2
  constructor
  · rw [Complex.neg_im, rotation_im]
    have hsin : Real.sin θ ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hhi (by linarith)
    linarith
  · rw [show -rotation θ / T = -(rotation θ / T) by ring]
    rw [Complex.neg_im, rotation_div_im T hTne θ]
    have hsin : Real.sin (θ - T.arg) < 0 := by
      apply Real.sin_neg_of_neg_of_neg_pi_lt
      · linarith
      · linarith
    have hpos : 0 < ((‖T‖ : ℝ)⁻¹) := inv_pos.mpr (norm_pos_iff.mpr hTne)
    nlinarith

/--
Positive coordinates of s give upper linear decay, including endpoints; the arbitrary-coordinate
version elaborates the center.
[RW26, p. 28, Appendix A.2].
-/
theorem upper_linear_pos (T : ℂ) (ψ a b θ : ℝ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (ha : 0 < a) (hb : 0 < b)
    (hθ : θ ∈ Icc T.arg (Real.pi / 2 + ψ)) :
    0 < (((a : ℂ) + (b : ℂ) / T) * rotation θ).im := by
  have hpi := Real.pi_pos
  have hTne : T ≠ 0 := arg_ne_zero_of_pos hT
  rw [affine_rotation_im]
  have hsin : 0 < Real.sin θ := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1, hT]
    · linarith [hθ.2, hψ]
  have hq : 0 ≤ (rotation θ / T).im :=
    (upper_direction_im_nonneg T ψ θ hT hTψ hψ hθ).2
  have h1 : 0 < a * Real.sin θ := mul_pos ha hsin
  have h2 : 0 ≤ b * (rotation θ / T).im := mul_nonneg hb.le hq
  linarith

/--
Negative coordinates of s+H-(T+1) give lower ratio decay; arbitrary-coordinate elaboration.
[RW26, p. 28, Appendix A.2].
-/
theorem lower_linear_pos (T : ℂ) (ψ a b θ : ℝ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (ha : a < 0) (hb : b < 0)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    0 < (((a : ℂ) + (b : ℂ) / T) * rotation θ).im := by
  have hpi := Real.pi_pos
  have hTne : T ≠ 0 := arg_ne_zero_of_pos hT
  rw [affine_rotation_im]
  have hsin : Real.sin θ ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ.2 (by linarith [hθ.1, hTψ])
  have hq : 0 < (-rotation θ / T).im :=
    (lower_direction_im_nonneg T ψ θ hT hTψ hψ hθ).2
  have hq' : (rotation θ / T).im < 0 := by
    rw [show -rotation θ / T = -(rotation θ / T) by ring, Complex.neg_im] at hq
    linarith
  have h1 : 0 ≤ a * Real.sin θ := mul_nonneg_of_nonpos_of_nonpos ha.le hsin
  have h2 : 0 < b * (rotation θ / T).im := mul_pos_of_neg_of_neg hb hq'
  linarith

/--
The negative sine bound in the single-function arc. This does not assert
any bound uniform as arg T tends to 0.
[RW26, p. 28, Appendix A.2].
-/
theorem lower_quadratic_margin (T : ℂ) (ψ θ : ℝ)
    (hT : 0 < T.arg) (hTψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    0 < Real.sin T.arg ∧ Real.sin T.arg ≤ -Real.sin (2 * θ - T.arg) := by
  have hpi := Real.pi_pos
  have hsinT : 0 < Real.sin T.arg := by
    apply Real.sin_pos_of_pos_of_lt_pi hT
    linarith [hψ]
  refine ⟨hsinT, ?_⟩
  have hsinθ : Real.sin θ ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ.2 (by linarith [hθ.1, hTψ])
  have hcos : 0 < Real.cos (T.arg - θ) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hθ.1, hθ.2, hT, hψ]
  have hsum : Real.sin T.arg + Real.sin (2 * θ - T.arg)
      = 2 * Real.sin θ * Real.cos (T.arg - θ) := by
    rw [Real.sin_add_sin]
    ring_nf
  have hle : Real.sin T.arg + Real.sin (2 * θ - T.arg) ≤ 0 := by
    rw [hsum]
    have h2sin : 2 * Real.sin θ ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg h2sin hcos.le
  linarith

-- Elaboration checks.
#print coords
#check coords_reconstruct
#check side_positive_combination
#check lower_quadratic_margin

end SICLean.L4.UpperWindow
