import SICLean.L4.FaddeevContinuation
import SICLean.L4.QProduct
import SICLean.L4.EtaMultiplier
import SICLean.L4.FaddeevProductIdentityAux

set_option autoImplicit false

/-!
# Integral to product comparison

The proof first works on the unit-circle arc in the first quadrant. There the two elementary
difference equations combine into a negative real shift, so finite iteration and the integral's left
limit identify the products. Analytic continuation in the argument and then the parameter removes
the unit-circle restriction. No second definition of Faddeev's function is used.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace SICLean.L4.FaddeevProductBridge

def numeratorArgument (b z : ℂ) : ℂ :=
  -Complex.exp ((Real.pi : ℂ) * Complex.I * b ^ 2) *
    Complex.exp (2 * (Real.pi : ℂ) * b * z)

def denominatorArgument (b z : ℂ) : ℂ :=
  -Complex.exp (-(Real.pi : ℂ) * Complex.I * (b⁻¹) ^ 2) *
    Complex.exp (2 * (Real.pi : ℂ) * b⁻¹ * z)

def realStep (b : ℂ) : ℂ := Complex.I * b - Complex.I * b⁻¹

lemma realStep_eq (b : ℂ) (hb : b⁻¹ = star b) :
    realStep b = (-2 * b.im : ℝ) := by
  apply Complex.ext <;> simp [realStep, hb, Complex.mul_re, Complex.mul_im]
  ring

lemma bases_norm (b : ℂ) (hb : 0 < b.re) (hi : 0 < b.im) :
    0 < ‖e (b ^ 2)‖ ∧ ‖e (b ^ 2)‖ < 1 ∧
      0 < ‖e (-(b⁻¹) ^ 2)‖ ∧ ‖e (-(b⁻¹) ^ 2)‖ < 1 := by
  have hb0 : b ≠ 0 := admissibleB_ne_zero b hb
  have hr : 0 < (b⁻¹).re := admissibleB_inv b hb
  have him : (b⁻¹).im < 0 := by
    rw [Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hi) (Complex.normSq_pos.mpr hb0)
  refine ⟨norm_pos_iff.mpr (e_ne_zero _), ?_, norm_pos_iff.mpr (e_ne_zero _), ?_⟩
  · rw [e, Complex.norm_exp, Real.exp_lt_one_iff]
    have hp := mul_pos (mul_pos Real.pi_pos hb) hi
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul,
      sub_zero, add_zero, mul_one]
    nlinarith
  · rw [e, Complex.norm_exp, Real.exp_lt_one_iff]
    have hp := mul_neg_of_pos_of_neg (mul_pos Real.pi_pos hr) him
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul,
      sub_zero, add_zero, mul_one]
    nlinarith

lemma numeratorArgument_add_step (b z : ℂ) (hb : b ≠ 0) :
    numeratorArgument b (z + realStep b) = numeratorArgument b z * e (b ^ 2) := by
  have he : 2 * (Real.pi : ℂ) * b * (z + realStep b) =
      2 * (Real.pi : ℂ) * b * z +
        2 * (Real.pi : ℂ) * Complex.I * b ^ 2 - 2 * (Real.pi : ℂ) * Complex.I := by
    unfold realStep
    field_simp
    ring
  rw [numeratorArgument, he, Complex.exp_sub, Complex.exp_add,
    Complex.exp_two_pi_mul_I, div_one]
  simp only [numeratorArgument, e]
  ring

lemma denominatorArgument_add_step (b z : ℂ) (hb : b ≠ 0) :
    denominatorArgument b (z + realStep b) =
      denominatorArgument b z * e (-(b⁻¹) ^ 2) := by
  have he : 2 * (Real.pi : ℂ) * b⁻¹ * (z + realStep b) =
      2 * (Real.pi : ℂ) * b⁻¹ * z +
        2 * (Real.pi : ℂ) * Complex.I * (-(b⁻¹) ^ 2) + 2 * (Real.pi : ℂ) * Complex.I := by
    unfold realStep
    field_simp
    ring
  rw [denominatorArgument, he, Complex.exp_add, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]
  simp only [denominatorArgument, e]
  ring

lemma numerator_factor (b z : ℂ) :
    continuationFactor b (z + Complex.I * b / 2) = 1 - numeratorArgument b z := by
  unfold continuationFactor numeratorArgument
  rw [show 2 * (Real.pi : ℂ) * b * (z + Complex.I * b / 2) =
    (Real.pi : ℂ) * Complex.I * b ^ 2 + 2 * (Real.pi : ℂ) * b * z by ring,
    Complex.exp_add]
  ring

lemma denominator_factor (b z : ℂ) (hb : b ≠ 0) :
    continuationFactor b⁻¹ (z + Complex.I * b - Complex.I * b⁻¹ / 2) =
      1 - denominatorArgument b z := by
  unfold continuationFactor denominatorArgument
  rw [show 2 * (Real.pi : ℂ) * b⁻¹ * (z + Complex.I * b - Complex.I * b⁻¹ / 2) =
    (-(Real.pi : ℂ) * Complex.I * (b⁻¹) ^ 2 + 2 * (Real.pi : ℂ) * b⁻¹ * z) +
      2 * (Real.pi : ℂ) * Complex.I by field_simp; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, Complex.exp_add]
  ring

lemma phi_realStep (b z : ℂ) (hb : AdmissibleB b) (hu : b⁻¹ = star b)
    (hzlo : -b.re < z.im) (hzhi : z.im < 0) :
    phi b z * (1 - denominatorArgument b z) =
      (1 - numeratorArgument b z) * phi b (z + realStep b) := by
  have hz : InStrip b z := by
    simp only [InStrip, stripWidth, hu, Complex.star_def, Complex.conj_re]
    rw [abs_lt]
    constructor <;> linarith
  have hzb : InStrip b (z + Complex.I * b) := by
    simp only [InStrip, stripWidth, hu, Complex.star_def, Complex.conj_re, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    rw [abs_lt]
    constructor <;> linarith
  have hzh : InStrip b (z + realStep b) := by
    rw [realStep_eq b hu]
    simpa only [InStrip, Complex.add_im, Complex.ofReal_im, add_zero] using hz
  have h1 := phi_difference_b b (z + Complex.I * b / 2) hb
    (by convert hz using 1; ring) (by convert hzb using 1; ring)
  have h2 := phi_difference_inv_b b
    (z + Complex.I * b - Complex.I * b⁻¹ / 2) hb
    (by convert hzh using 1; simp only [realStep]; ring)
    (by convert hzb using 1; ring)
  change phi b (z + Complex.I * b / 2 - Complex.I * b / 2) =
    continuationFactor b (z + Complex.I * b / 2) *
      phi b (z + Complex.I * b / 2 + Complex.I * b / 2) at h1
  change phi b (z + Complex.I * b - Complex.I * b⁻¹ / 2 - Complex.I * b⁻¹ / 2) =
    continuationFactor b⁻¹ (z + Complex.I * b - Complex.I * b⁻¹ / 2) *
      phi b (z + Complex.I * b - Complex.I * b⁻¹ / 2 + Complex.I * b⁻¹ / 2) at h2
  rw [numerator_factor] at h1
  rw [denominator_factor b z (admissibleB_ne_zero b hb)] at h2
  have h1' : phi b z = (1 - numeratorArgument b z) * phi b (z + Complex.I * b) := by
    rw [show z + Complex.I * b / 2 - Complex.I * b / 2 = z by ring,
      show z + Complex.I * b / 2 + Complex.I * b / 2 = z + Complex.I * b by ring] at h1
    exact h1
  have h2' : phi b (z + realStep b) =
      (1 - denominatorArgument b z) * phi b (z + Complex.I * b) := by
    rw [show z + Complex.I * b - Complex.I * b⁻¹ / 2 - Complex.I * b⁻¹ / 2 =
      z + realStep b by unfold realStep; ring,
      show z + Complex.I * b - Complex.I * b⁻¹ / 2 + Complex.I * b⁻¹ / 2 =
        z + Complex.I * b by ring] at h2
    exact h2
  rw [h1', h2']
  ring

lemma numeratorArgument_add_nat_step (b z : ℂ) (n : ℕ) (hb : b ≠ 0) :
    numeratorArgument b (z + (n : ℂ) * realStep b) =
      numeratorArgument b z * e (b ^ 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show z + ((n + 1 : ℕ) : ℂ) * realStep b =
        (z + (n : ℂ) * realStep b) + realStep b by push_cast; ring,
        numeratorArgument_add_step b _ hb, ih, pow_succ]
      ring

lemma denominatorArgument_add_nat_step (b z : ℂ) (n : ℕ) (hb : b ≠ 0) :
    denominatorArgument b (z + (n : ℂ) * realStep b) =
      denominatorArgument b z * e (-(b⁻¹) ^ 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show z + ((n + 1 : ℕ) : ℂ) * realStep b =
        (z + (n : ℂ) * realStep b) + realStep b by push_cast; ring,
        denominatorArgument_add_step b _ hb, ih, pow_succ]
      ring

lemma phi_finite_realStep (b z : ℂ) (n : ℕ) (hb : AdmissibleB b)
    (hu : b⁻¹ = star b) (hzlo : -b.re < z.im) (hzhi : z.im < 0) :
    phi b z * qPochhammerNat (denominatorArgument b z) (e (-(b⁻¹) ^ 2)) n =
      qPochhammerNat (numeratorArgument b z) (e (b ^ 2)) n *
        phi b (z + (n : ℂ) * realStep b) := by
  induction n with
  | zero => simp [qPochhammerNat_zero]
  | succ n ih =>
      have hzim : (z + (n : ℂ) * realStep b).im = z.im := by
        rw [realStep_eq b hu]
        simp
      have hs := phi_realStep b (z + (n : ℂ) * realStep b) hb hu
        (by simpa only [hzim] using hzlo) (by simpa only [hzim] using hzhi)
      rw [numeratorArgument_add_nat_step b z n (admissibleB_ne_zero b hb),
        denominatorArgument_add_nat_step b z n (admissibleB_ne_zero b hb)] at hs
      rw [qPochhammerNat_succ, qPochhammerNat_succ,
        show z + ((n + 1 : ℕ) : ℂ) * realStep b =
          (z + (n : ℂ) * realStep b) + realStep b by push_cast; ring]
      calc
        _ = (phi b z * qPochhammerNat (denominatorArgument b z) (e (-(b⁻¹) ^ 2)) n) *
            (1 - denominatorArgument b z * e (-(b⁻¹) ^ 2) ^ n) := by ring
        _ = qPochhammerNat (numeratorArgument b z) (e (b ^ 2)) n *
            (phi b (z + (n : ℂ) * realStep b) *
              (1 - denominatorArgument b z * e (-(b⁻¹) ^ 2) ^ n)) := by rw [ih]; ring
        _ = _ := by rw [hs]; ring

lemma phi_unit_lower_cross_mul (b z : ℂ) (hb : AdmissibleB b)
    (hi : 0 < b.im) (hu : b⁻¹ = star b) (hzlo : -b.re < z.im) (hzhi : z.im < 0) :
    phi b z * qPochhammer (denominatorArgument b z) (e (-(b⁻¹) ^ 2)) =
      qPochhammer (numeratorArgument b z) (e (b ^ 2)) := by
  obtain ⟨hq0, hq1, hQ0, hQ1⟩ := bases_norm b hb hi
  have hleft := (tendsto_qPochhammerNat (denominatorArgument b z)
    (e (-(b⁻¹) ^ 2)) hQ0 hQ1).const_mul (phi b z)
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * (-2 * b.im)) atTop atBot := by
    exact Tendsto.atTop_mul_const_of_neg (by linarith : -2 * b.im < 0)
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hp : Tendsto (fun n : ℕ => phi b (z + (n : ℂ) * realStep b)) atTop (𝓝 1) := by
    convert (tendsto_phi_real_atBot b z hb).comp ht using 1
    ext n
    congr 2
    rw [realStep_eq b hu]
    push_cast
    ring
  have hright := (tendsto_qPochhammerNat (numeratorArgument b z)
    (e (b ^ 2)) hq0 hq1).mul hp
  simp only [mul_one] at hright
  exact tendsto_nhds_unique hleft
    (hright.congr (fun n => (phi_finite_realStep b z n hb hu hzlo hzhi).symm))

lemma analyticAt_numerator (b z : ℂ) (hb : AdmissibleB b) (hi : 0 < b.im) :
    AnalyticAt ℂ (fun w => qPochhammer (numeratorArgument b w) (e (b ^ 2))) z := by
  obtain ⟨hq0, hq1, _, _⟩ := bases_norm b hb hi
  exact ((differentiable_qPochhammer_x (e (b ^ 2)) hq0 hq1).analyticAt
    (z := numeratorArgument b z)).comp (by unfold numeratorArgument; fun_prop)

lemma analyticAt_denominator (b z : ℂ) (hb : AdmissibleB b) (hi : 0 < b.im) :
    AnalyticAt ℂ (fun w => qPochhammer (denominatorArgument b w) (e (-(b⁻¹) ^ 2))) z := by
  obtain ⟨_, _, hQ0, hQ1⟩ := bases_norm b hb hi
  exact ((differentiable_qPochhammer_x (e (-(b⁻¹) ^ 2)) hQ0 hQ1).analyticAt
    (z := denominatorArgument b z)).comp (by unfold denominatorArgument; fun_prop)

lemma analyticAt_numerator_parameter (b z : ℂ) (hb : AdmissibleB b) (hi : 0 < b.im) :
    AnalyticAt ℂ (fun c => qPochhammer (numeratorArgument c z) (e (c ^ 2))) b := by
  obtain ⟨hq0, hq1, _, _⟩ := bases_norm b hb hi
  have hm : AnalyticAt ℂ (fun c : ℂ => (numeratorArgument c z, e (c ^ 2))) b := by
    unfold numeratorArgument e
    fun_prop
  exact (analyticOnNhd_qPochhammer_joint (numeratorArgument b z, e (b ^ 2))
    ⟨hq0, hq1⟩).comp (f := fun c : ℂ => (numeratorArgument c z, e (c ^ 2))) hm

lemma analyticAt_denominator_parameter (b z : ℂ) (hb : AdmissibleB b) (hi : 0 < b.im) :
    AnalyticAt ℂ (fun c => qPochhammer (denominatorArgument c z) (e (-(c⁻¹) ^ 2))) b := by
  obtain ⟨_, _, hQ0, hQ1⟩ := bases_norm b hb hi
  have hb0 : b ≠ 0 := admissibleB_ne_zero b hb
  have hm : AnalyticAt ℂ (fun c : ℂ => (denominatorArgument c z, e (-(c⁻¹) ^ 2))) b := by
    unfold denominatorArgument e
    fun_prop
  exact (analyticOnNhd_qPochhammer_joint (denominatorArgument b z, e (-(b⁻¹) ^ 2))
    ⟨hQ0, hQ1⟩).comp
      (f := fun c : ℂ => (denominatorArgument c z, e (-(c⁻¹) ^ 2))) hm

lemma stripWidth_pos (b : ℂ) (hb : AdmissibleB b) : 0 < stripWidth b := by
  have hi := admissibleB_inv b hb
  unfold stripWidth
  exact half_pos (add_pos hb hi)

lemma phi_unit_cross_mul (b z : ℂ) (hb : AdmissibleB b)
    (hi : 0 < b.im) (hu : b⁻¹ = star b) (hz : InStrip b z) :
    phi b z * qPochhammer (denominatorArgument b z) (e (-(b⁻¹) ^ 2)) =
      qPochhammer (numeratorArgument b z) (e (b ^ 2)) := by
  let f : ℂ → ℂ := fun w => phi b w *
    qPochhammer (denominatorArgument b w) (e (-(b⁻¹) ^ 2)) -
      qPochhammer (numeratorArgument b w) (e (b ^ 2))
  have ha : AnalyticOnNhd ℂ f {w : ℂ | |w.im| < stripWidth b} := by
    intro w hw
    exact ((analyticAt_phi_of_inStrip b w hb hw).mul
      (analyticAt_denominator b w hb hi)).sub (analyticAt_numerator b w hb hi)
  have hw : stripWidth b = b.re := by simp [stripWidth, hu]
  have hzero := ProductIdentity.eqOn_zero_strip_of_lower (stripWidth b)
    (stripWidth_pos b hb) f ha (fun w hw' => by
      dsimp [f]
      exact sub_eq_zero.mpr (phi_unit_lower_cross_mul b w hb hi hu
        (by simpa only [hw] using hw'.1) hw'.2)) hz
  exact sub_eq_zero.mp hzero

lemma analyticAt_phi_parameter_real (b : ℂ) (x : ℝ) (hb : AdmissibleB b) :
    AnalyticAt ℂ (fun c => phi c (x : ℂ)) b := by
  have hp : (b, (x : ℂ)) ∈ parameterDomain := by
    exact ⟨hb, by simpa only [InStrip, Complex.ofReal_im, abs_zero] using stripWidth_pos b hb⟩
  have hphi := JointAnalytic.differentiableOn_analyticOnNhd
    differentiableOn_phi_joint isOpen_parameterDomain (b, (x : ℂ)) hp
  exact hphi.comp (f := fun c : ℂ => (c, (x : ℂ)))
    (analyticAt_id.prod analyticAt_const)

/-- The literal integral/q-product cross multiplication on the real axis, with no quotient and no
nonzero-product hypothesis. -/
theorem phi_real_cross_mul (b : ℂ) (x : ℝ) (hb : AdmissibleB b) (hi : 0 < b.im) :
    phi b (x : ℂ) * qPochhammer (denominatorArgument b x) (e (-(b⁻¹) ^ 2)) =
      qPochhammer (numeratorArgument b x) (e (b ^ 2)) := by
  let f : ℂ → ℂ := fun c => phi c (x : ℂ) *
    qPochhammer (denominatorArgument c x) (e (-(c⁻¹) ^ 2)) -
      qPochhammer (numeratorArgument c x) (e (c ^ 2))
  have ha : AnalyticOnNhd ℂ f {c : ℂ | 0 < c.re ∧ 0 < c.im} := by
    intro c hc
    exact ((analyticAt_phi_parameter_real c x hc.1).mul
      (analyticAt_denominator_parameter c x hc.1 hc.2)).sub
        (analyticAt_numerator_parameter c x hc.1 hc.2)
  have hz := ProductIdentity.eqOn_zero_upperQuadrant_of_unit f ha
    (fun c hc hu => by
      dsimp [f]
      apply sub_eq_zero.mpr
      apply phi_unit_cross_mul c x hc.1 hc.2 hu
      simpa only [InStrip, Complex.ofReal_im, abs_zero] using stripWidth_pos c hc.1) ⟨hb, hi⟩
  exact sub_eq_zero.mp hz

/-- Integral to infinite-product identification throughout the defining strip, before division. In
particular common product zeros are allowed. -/
theorem phi_strip_cross_mul (b z : ℂ) (hb : AdmissibleB b) (hi : 0 < b.im)
    (hz : InStrip b z) :
    phi b z * qPochhammer (denominatorArgument b z) (e (-(b⁻¹) ^ 2)) =
      qPochhammer (numeratorArgument b z) (e (b ^ 2)) := by
  let f : ℂ → ℂ := fun w => phi b w *
    qPochhammer (denominatorArgument b w) (e (-(b⁻¹) ^ 2)) -
      qPochhammer (numeratorArgument b w) (e (b ^ 2))
  have ha : AnalyticOnNhd ℂ f {w : ℂ | |w.im| < stripWidth b} := by
    intro w hw
    exact ((analyticAt_phi_of_inStrip b w hb hw).mul
      (analyticAt_denominator b w hb hi)).sub (analyticAt_numerator b w hb hi)
  have hzero := ProductIdentity.eqOn_zero_strip_of_real (stripWidth b)
    (stripWidth_pos b hb) f ha (fun x => sub_eq_zero.mpr (phi_real_cross_mul b x hb hi)) hz
  exact sub_eq_zero.mp hzero

end SICLean.L4.FaddeevProductBridge
