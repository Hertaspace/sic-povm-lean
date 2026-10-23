import SICLean.L4.FaddeevContour
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false

/-!
The inverse kernel on an arbitrary rectangle containing its pole. The logarithm is used on the
lower, right, and upper edges; on the left edge `log (-(w-p))` avoids the branch cut. The two corner
jumps give `2πi`. This is a finite calculation, independent of any residue theorem.
-/

noncomputable section
open Complex Set MeasureTheory
open scoped Interval

namespace SICLean.L4.FinitePrincipalPartsRectangleKernel

private lemma horizontal_inv (p : ℂ) (a b y : ℝ) (hy : y ≠ p.im) :
    (∫ x : ℝ in a..b, ((x : ℂ) + (y : ℂ) * I - p)⁻¹) =
      log ((b : ℂ) + (y : ℂ) * I - p) -
        log ((a : ℂ) + (y : ℂ) * I - p) := by
  have hs (x : ℝ) : (x : ℂ) + (y : ℂ) * I - p ∈ slitPlane := by
    right
    simpa using sub_ne_zero.mpr hy
  have hc : Continuous (fun x : ℝ => ((x : ℂ) + (y : ℂ) * I - p)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun x => slitPlane_ne_zero (hs x))
  have h := Contour.integral_of_primitive_along
    (F := fun w : ℂ => log (w - p)) (f := fun w => (w - p)⁻¹)
    (γ := fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (γ' := fun _ => 1)
    (a := a) (b := b)
    (fun x _ => by
      have hd : HasDerivAt (fun w : ℂ => w - p) 1
          ((x : ℂ) + (y : ℂ) * I) := (hasDerivAt_id _).sub_const p
      convert! (Complex.hasDerivAt_log (hs x)).comp ((x : ℂ) + (y : ℂ) * I) hd using 1
      simp)
    (fun x _ => by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * I))
    (by simpa using hc.intervalIntegrable a b)
  simpa using h

private lemma vertical_inv_right (p : ℂ) (a b x : ℝ) (hx : p.re < x) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + (y : ℂ) * I - p)⁻¹) =
      log ((x : ℂ) + (b : ℂ) * I - p) -
        log ((x : ℂ) + (a : ℂ) * I - p) := by
  have hs (y : ℝ) : (x : ℂ) + (y : ℂ) * I - p ∈ slitPlane := by
    left
    simpa using sub_pos.mpr hx
  have hc : Continuous (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I - p)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun y => slitPlane_ne_zero (hs y))
  have h := Contour.integral_of_primitive_along
    (F := fun w : ℂ => log (w - p)) (f := fun w => (w - p)⁻¹)
    (γ := fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (γ' := fun _ => I)
    (a := a) (b := b)
    (fun y _ => by
      have hd : HasDerivAt (fun w : ℂ => w - p) 1
          ((x : ℂ) + (y : ℂ) * I) := (hasDerivAt_id _).sub_const p
      convert! (Complex.hasDerivAt_log (hs y)).comp ((x : ℂ) + (y : ℂ) * I) hd using 1
      simp)
    (fun y _ => by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ))
    (hc.mul_const I |>.intervalIntegrable a b)
  simpa [intervalIntegral.integral_mul_const, mul_comm] using h

private lemma vertical_inv_left (p : ℂ) (a b x : ℝ) (hx : x < p.re) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + (y : ℂ) * I - p)⁻¹) =
      log (-((x : ℂ) + (b : ℂ) * I - p)) -
        log (-((x : ℂ) + (a : ℂ) * I - p)) := by
  have hs (y : ℝ) : -((x : ℂ) + (y : ℂ) * I - p) ∈ slitPlane := by
    left
    simp only [neg_re, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, zero_mul, sub_self, add_zero]
    linarith
  have hn (y : ℝ) : (x : ℂ) + (y : ℂ) * I - p ≠ 0 := by
    simpa only [neg_ne_zero] using slitPlane_ne_zero (hs y)
  have hc : Continuous (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I - p)⁻¹) :=
    Continuous.inv₀ (by fun_prop) hn
  have h := Contour.integral_of_primitive_along
    (F := fun w : ℂ => log (-(w - p))) (f := fun w => (w - p)⁻¹)
    (γ := fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (γ' := fun _ => I)
    (a := a) (b := b)
    (fun y _ => by
      have hd : HasDerivAt (fun w : ℂ => -(w - p)) (-1)
          ((x : ℂ) + (y : ℂ) * I) := ((hasDerivAt_id _).sub_const p).neg
      convert! (Complex.hasDerivAt_log (hs y)).comp ((x : ℂ) + (y : ℂ) * I) hd using 1
      simp only [mul_neg_one, inv_neg, neg_neg])
    (fun y _ => by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ))
    (hc.mul_const I |>.intervalIntegrable a b)
  simpa [intervalIntegral.integral_mul_const, mul_comm] using h

private lemma log_sub_log_neg_upper (z : ℂ) (hz : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simp only [sub_im, log_im, arg_neg_eq_arg_sub_pi_of_im_pos hz,
      mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    ring

private lemma log_sub_log_neg_lower (z : ℂ) (hz : z.im < 0) :
    log z - log (-z) = -(Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simp only [sub_im, log_im, arg_neg_eq_arg_add_pi_of_im_neg hz,
      mul_im, neg_re, ofReal_re, I_im, mul_one, neg_im, ofReal_im, neg_zero,
      I_re, mul_zero, add_zero]
    ring

theorem integral_boundary_rect_inv (lo hi p : ℂ)
    (hp : lo.re < p.re ∧ p.re < hi.re ∧ lo.im < p.im ∧ p.im < hi.im) :
    (∫ x : ℝ in lo.re..hi.re,
      ((x : ℂ) + (lo.im : ℂ) * I - p)⁻¹) +
      I * (∫ y : ℝ in lo.im..hi.im,
        ((hi.re : ℂ) + (y : ℂ) * I - p)⁻¹) -
      (∫ x : ℝ in lo.re..hi.re,
        ((x : ℂ) + (hi.im : ℂ) * I - p)⁻¹) -
      I * (∫ y : ℝ in lo.im..hi.im,
        ((lo.re : ℂ) + (y : ℂ) * I - p)⁻¹) =
      2 * (Real.pi : ℂ) * I := by
  rw [horizontal_inv p lo.re hi.re lo.im hp.2.2.1.ne,
    horizontal_inv p lo.re hi.re hi.im hp.2.2.2.ne',
    vertical_inv_right p lo.im hi.im hi.re hp.2.1,
    vertical_inv_left p lo.im hi.im lo.re hp.1]
  have hu := log_sub_log_neg_upper
    ((lo.re : ℂ) + (hi.im : ℂ) * I - p) (by simpa using sub_pos.mpr hp.2.2.2)
  have hl := log_sub_log_neg_lower
    ((lo.re : ℂ) + (lo.im : ℂ) * I - p) (by simpa using sub_neg.mpr hp.2.2.1)
  linear_combination hu - hl

end SICLean.L4.FinitePrincipalPartsRectangleKernel
