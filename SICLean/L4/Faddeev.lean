import SICLean.L4.FaddeevBounds
import SICLean.L4.FaddeevContour
import SICLean.L4.FaddeevHolomorphic
import SICLean.L4.FaddeevInversionAux
import SICLean.L4.FaddeevDifferenceAux
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

/-!
# Faddeev's quantum dilogarithm

[RW26, §2.1, pp. 4--5]

`ℝ + i0` means an oriented path from left to right passing above zero. We define its logarithmic
integral on a horizontal line below every nonzero upper pole. `logPhi_eq_detour` identifies this
definition with the real axis with an upper semicircle traversed clockwise, and `tendsto_detourLog`
gives the literal shrinking-detour interpretation. It is not a principal value.

The parameter is complex with positive real part. Only values in the open convergence strip have
mathematical meaning here. In particular, Lean's total Bochner integral outside that strip is not a
meromorphic continuation. The difference equations below explicitly require both shifted arguments
to remain in the strip. Global continuation is treated separately.

The contour comparison uses finite rectangles and small semicircular
corrections. Joint holomorphy locally determines the height and uses a common integrable bound.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace SICLean.L4

/-- The parameter domain used in [RW26, §2.1] and the G1 estimates. -/
def AdmissibleB (b : ℂ) : Prop := 0 < b.re

/-- Half the real part of `b + b⁻¹`, positive when `AdmissibleB b`. -/
def stripWidth (b : ℂ) : ℝ := (b.re + (b⁻¹).re) / 2

/-- The open strip of absolute convergence of the defining integral. -/
def InStrip (b z : ℂ) : Prop := |z.im| < stripWidth b

/-- The first nonzero upper poles have heights at least this number. -/
def poleHeight (b : ℂ) : ℝ := Real.pi * min b.re (b⁻¹).re

/-- A horizontal line above zero and below every nonzero upper pole. -/
def AdmissibleHeight (b : ℂ) (h : ℝ) : Prop := 0 < h ∧ h < poleHeight b

/-- A concrete choice of height. Height-independence is a theorem below. -/
def canonicalHeight (b : ℂ) : ℝ := poleHeight b / 2

/-- The [RW26] logarithmic kernel including the factor `1/w` in `dw/w`. -/
def kernel (b z w : ℂ) : ℂ :=
  Complex.exp (-2 * Complex.I * z * w) /
    (4 * Complex.sinh (b * w) * Complex.sinh (b⁻¹ * w) * w)

/-- Parameterization of a horizontal line, oriented from left to right. -/
def linePoint (h x : ℝ) : ℂ := (x : ℂ) + Complex.I * (h : ℂ)

def logPhiAtHeight (b z : ℂ) (h : ℝ) : ℂ :=
  ∫ x : ℝ, kernel b z (linePoint h x)

def logPhi (b z : ℂ) : ℂ := logPhiAtHeight b z (canonicalHeight b)

/-- Faddeev's function on the convergence strip, in [RW26] normalization. -/
def phi (b z : ℂ) : ℂ := Complex.exp (logPhi b z)

/-- A circle point used for the upper detour, `θ: π → 0`. -/
def arcPoint (r θ : ℝ) : ℂ := (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))

def arcKernel (b z : ℂ) (r θ : ℝ) : ℂ :=
  kernel b z (arcPoint r θ) * (Complex.I * arcPoint r θ)

/-- Real tails plus a clockwise upper semicircle. The orientation is essential. -/
def detourLog (b z : ℂ) (r : ℝ) : ℂ :=
  (∫ x : ℝ in Iic (-r), kernel b z (x : ℂ)) +
    (∫ θ : ℝ in Real.pi..0, arcKernel b z r θ) +
    (∫ x : ℝ in Ici r, kernel b z (x : ℂ))

/-- Open domain for joint holomorphy in the parameter and the argument. -/
def parameterDomain : Set (ℂ × ℂ) :=
  {p | AdmissibleB p.1 ∧ InStrip p.1 p.2}

/-- Derivative of the horizontal-line kernel with respect to `z`. -/
def zDerivativeKernel (b z : ℂ) (h x : ℝ) : ℂ :=
  (-2 * Complex.I * linePoint h x) * kernel b z (linePoint h x)

lemma admissibleB_ne_zero (b : ℂ) (hb : AdmissibleB b) : b ≠ 0 := by
  intro h
  simpa [AdmissibleB, h] using hb

lemma admissibleB_inv (b : ℂ) (hb : AdmissibleB b) : AdmissibleB b⁻¹ := by
  change 0 < (b⁻¹).re
  rw [Complex.inv_re]
  exact div_pos hb (Complex.normSq_pos.mpr (admissibleB_ne_zero b hb))

/-- The imaginary part of a sinh zero on this line would be a strictly positive integer multiple of
the first pole height, which is too large. -/
lemma sinh_line_ne_zero (c : ℂ) (h x : ℝ) (hc : c ≠ 0)
    (hci : 0 < (c⁻¹).re) (hh : 0 < h)
    (hhp : h < Real.pi * (c⁻¹).re) :
    Complex.sinh (c * linePoint h x) ≠ 0 := by
  intro hs
  have hs' : Complex.sin ((c * linePoint h x) * Complex.I) = 0 := by
    rw [Complex.sin_mul_I, hs, zero_mul]
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp hs'
  have hz : c * linePoint h x = -(n : ℂ) * (Real.pi : ℂ) * Complex.I := by
    calc
      c * linePoint h x =
          ((c * linePoint h x) * Complex.I) * (-Complex.I) := by
        simp [mul_assoc]
      _ = (n : ℂ) * (Real.pi : ℂ) * (-Complex.I) :=
        congrArg (fun z : ℂ => z * (-Complex.I)) hn
      _ = -(n : ℂ) * (Real.pi : ℂ) * Complex.I := by ring
  have hw : linePoint h x =
      c⁻¹ * (-(n : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    calc
      linePoint h x = c⁻¹ * (c * linePoint h x) := by simp [hc]
      _ = c⁻¹ * (-(n : ℂ) * (Real.pi : ℂ) * Complex.I) := by rw [hz]
  have him := congrArg Complex.im hw
  simp [linePoint, Complex.mul_im, Complex.mul_re] at him
  have him' : h = -(n : ℝ) * (Real.pi * (c⁻¹).re) := by
    rw [Complex.inv_re]
    nlinarith [him]
  have hp : 0 < Real.pi * (c⁻¹).re := mul_pos Real.pi_pos hci
  have hnp : 0 < -(n : ℝ) := by
    apply (mul_pos_iff_of_pos_right hp).mp
    rwa [← him']
  have hnl : -(n : ℝ) < 1 := by
    apply (mul_lt_mul_iff_left₀ hp).mp
    simpa only [← him', one_mul] using hhp
  have hneg : (n : ℝ) < 0 := by linarith
  have hlow : (-1 : ℝ) < (n : ℝ) := by linarith
  have hneg' : n < 0 := by exact_mod_cast hneg
  have hlow' : (-1 : ℤ) < n := by exact_mod_cast hlow
  omega

theorem isOpen_parameterDomain : IsOpen parameterDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hb : AdmissibleB p.1 := hp.1
  have hz : InStrip p.1 p.2 := hp.2
  have hre : ContinuousAt (fun q : ℂ × ℂ => q.1.re) p :=
    (Complex.continuous_re.comp continuous_fst).continuousAt
  have hrei : ContinuousAt (fun q : ℂ × ℂ => (q.1⁻¹).re) p :=
    Complex.continuous_re.continuousAt.comp
      (continuous_fst.continuousAt.inv₀ (admissibleB_ne_zero p.1 hb))
  have hw : ContinuousAt (fun q : ℂ × ℂ => stripWidth q.1) p :=
    (hre.add hrei).div_const 2
  have hi : ContinuousAt (fun q : ℂ × ℂ => |q.2.im|) p :=
    (Complex.continuous_im.comp continuous_snd).continuousAt.abs
  change ∀ᶠ q in 𝓝 p, AdmissibleB q.1 ∧ InStrip q.1 q.2
  filter_upwards [continuousAt_const.eventually_lt hre hb,
    hi.eventually_lt hw hz] with q hq₁ hq₂
  exact ⟨hq₁, hq₂⟩

theorem canonicalHeight_admissible (b : ℂ) (hb : AdmissibleB b) :
    AdmissibleHeight b (canonicalHeight b) := by
  have hbi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hp : 0 < poleHeight b :=
    mul_pos Real.pi_pos (lt_min hb hbi)
  change 0 < poleHeight b / 2 ∧ poleHeight b / 2 < poleHeight b
  constructor <;> linarith

/-- No zero of either sinh and no `w = 0` occurs on an admissible line. -/
theorem line_denominator_ne_zero (b : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hh : AdmissibleHeight b h) (x : ℝ) :
    4 * Complex.sinh (b * linePoint h x) *
      Complex.sinh (b⁻¹ * linePoint h x) * linePoint h x ≠ 0 := by
  have hb₀ := admissibleB_ne_zero b hb
  have hbi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hh₁ : h < Real.pi * b.re :=
    lt_of_lt_of_le hh.2
      (mul_le_mul_of_nonneg_left (min_le_left _ _) Real.pi_pos.le)
  have hh₂ : h < Real.pi * (b⁻¹).re :=
    lt_of_lt_of_le hh.2
      (mul_le_mul_of_nonneg_left (min_le_right _ _) Real.pi_pos.le)
  have hs₁ := sinh_line_ne_zero b h x hb₀ hbi hh.1 hh₂
  have hs₂ : Complex.sinh (b⁻¹ * linePoint h x) ≠ 0 := by
    apply sinh_line_ne_zero b⁻¹ h x (inv_ne_zero hb₀)
    · simpa only [inv_inv] using (show 0 < b.re from hb)
    · exact hh.1
    · simpa only [inv_inv] using hh₁
  have hw : linePoint h x ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp [linePoint] at hi
    exact (ne_of_gt hh.1) hi
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs₁) hs₂) hw

lemma sinh_upperStrip_ne_zero (c w : ℂ) (hc : c ≠ 0)
    (hci : 0 < (c⁻¹).re) (hw : w ≠ 0) (him₀ : 0 ≤ w.im)
    (himp : w.im < Real.pi * (c⁻¹).re) :
    Complex.sinh (c * w) ≠ 0 := by
  intro hs
  have hs' : Complex.sin ((c * w) * Complex.I) = 0 := by
    rw [Complex.sin_mul_I, hs, zero_mul]
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp hs'
  have hz : c * w = -(n : ℂ) * (Real.pi : ℂ) * Complex.I := by
    calc
      c * w = ((c * w) * Complex.I) * (-Complex.I) := by simp [mul_assoc]
      _ = (n : ℂ) * (Real.pi : ℂ) * (-Complex.I) :=
        congrArg (fun z : ℂ => z * (-Complex.I)) hn
      _ = -(n : ℂ) * (Real.pi : ℂ) * Complex.I := by ring
  have hw' : w = c⁻¹ * (-(n : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    calc
      w = c⁻¹ * (c * w) := by simp [hc]
      _ = c⁻¹ * (-(n : ℂ) * (Real.pi : ℂ) * Complex.I) := by rw [hz]
  have him := congrArg Complex.im hw'
  simp [Complex.mul_im, Complex.mul_re] at him
  have him' : w.im = -(n : ℝ) * (Real.pi * (c⁻¹).re) := by
    rw [Complex.inv_re]
    nlinarith [him]
  have hp : 0 < Real.pi * (c⁻¹).re := mul_pos Real.pi_pos hci
  have hnp : 0 ≤ -(n : ℝ) := by
    apply (mul_nonneg_iff_of_pos_right hp).mp
    rwa [← him']
  have hnl : -(n : ℝ) < 1 := by
    apply (mul_lt_mul_iff_left₀ hp).mp
    simpa only [← him', one_mul] using himp
  have hnonpos : (n : ℝ) ≤ 0 := by linarith
  have hlow : (-1 : ℝ) < (n : ℝ) := by linarith
  have hnonpos' : n ≤ 0 := by exact_mod_cast hnonpos
  have hlow' : (-1 : ℤ) < n := by exact_mod_cast hlow
  have hn₀ : n = 0 := by omega
  apply hw
  simpa [hn₀] using hw'

lemma upperStrip_denominator_ne_zero (b w : ℂ) (hb : AdmissibleB b)
    (hw : w ≠ 0) (him₀ : 0 ≤ w.im) (himp : w.im < poleHeight b) :
    4 * Complex.sinh (b * w) * Complex.sinh (b⁻¹ * w) * w ≠ 0 := by
  have hb₀ := admissibleB_ne_zero b hb
  have hbi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hh₁ : w.im < Real.pi * b.re :=
    lt_of_lt_of_le himp
      (mul_le_mul_of_nonneg_left (min_le_left _ _) Real.pi_pos.le)
  have hh₂ : w.im < Real.pi * (b⁻¹).re :=
    lt_of_lt_of_le himp
      (mul_le_mul_of_nonneg_left (min_le_right _ _) Real.pi_pos.le)
  have hs₁ := sinh_upperStrip_ne_zero b w hb₀ hbi hw him₀ hh₂
  have hs₂ : Complex.sinh (b⁻¹ * w) ≠ 0 := by
    apply sinh_upperStrip_ne_zero b⁻¹ w (inv_ne_zero hb₀)
    · simpa only [inv_inv] using (show 0 < b.re from hb)
    · exact hw
    · exact him₀
    · simpa only [inv_inv] using hh₁
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs₁) hs₂) hw

lemma real_denominator_ne_zero (b : ℂ) (hb : AdmissibleB b)
    (x : ℝ) (hx : x ≠ 0) :
    4 * Complex.sinh (b * (x : ℂ)) *
      Complex.sinh (b⁻¹ * (x : ℂ)) * (x : ℂ) ≠ 0 := by
  apply upperStrip_denominator_ne_zero b (x : ℂ) hb
  · exact_mod_cast hx
  · simp
  · change 0 < poleHeight b
    exact mul_pos Real.pi_pos (lt_min hb (admissibleB_inv b hb))

lemma continuousAt_kernel_of_denominator_ne_zero (b z w : ℂ)
    (hw : 4 * Complex.sinh (b * w) * Complex.sinh (b⁻¹ * w) * w ≠ 0) :
    ContinuousAt (kernel b z) w := by
  unfold kernel
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact hw

lemma continuousAt_realKernel (b z : ℂ) (hb : AdmissibleB b)
    (x : ℝ) (hx : x ≠ 0) :
    ContinuousAt (fun t : ℝ => kernel b z (t : ℂ)) x := by
  exact (continuousAt_kernel_of_denominator_ne_zero b z (x : ℂ)
    (real_denominator_ne_zero b hb x hx)).comp
      Complex.continuous_ofReal.continuousAt

lemma continuousOn_realKernel_Ici (b z : ℂ) (hb : AdmissibleB b)
    (r : ℝ) (hr : 0 < r) :
    ContinuousOn (fun t : ℝ => kernel b z (t : ℂ)) (Ici r) := by
  intro x hx
  exact (continuousAt_realKernel b z hb x
    (ne_of_gt (lt_of_lt_of_le hr hx))).continuousWithinAt

lemma continuousOn_realKernel_Iic (b z : ℂ) (hb : AdmissibleB b)
    (r : ℝ) (hr : 0 < r) :
    ContinuousOn (fun t : ℝ => kernel b z (t : ℂ)) (Iic (-r)) := by
  intro x hx
  have hx₀ : x < 0 := by
    change x ≤ -r at hx
    linarith
  exact (continuousAt_realKernel b z hb x (ne_of_lt hx₀)).continuousWithinAt

lemma continuous_arcPoint (r : ℝ) : Continuous (arcPoint r) := by
  unfold arcPoint
  fun_prop

lemma norm_arcPoint (r θ : ℝ) : ‖arcPoint r θ‖ = |r| := by
  simp [arcPoint, Complex.norm_exp_I_mul_ofReal]

lemma im_arcPoint (r θ : ℝ) : (arcPoint r θ).im = r * Real.sin θ := by
  simp only [arcPoint, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  rw [mul_comm Complex.I (θ : ℂ), Complex.exp_ofReal_mul_I_im]

lemma arcPoint_ne_zero (r θ : ℝ) (hr : 0 < r) : arcPoint r θ ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt hr)
  · exact Complex.exp_ne_zero _

lemma im_arcPoint_nonneg (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc 0 Real.pi) :
    0 ≤ (arcPoint r θ).im := by
  rw [im_arcPoint]
  exact mul_nonneg hr (Real.sin_nonneg_of_mem_Icc hθ)

lemma im_arcPoint_le (r θ : ℝ) (hr : 0 ≤ r) :
    (arcPoint r θ).im ≤ r := by
  calc
    (arcPoint r θ).im ≤ |(arcPoint r θ).im| := le_abs_self _
    _ ≤ ‖arcPoint r θ‖ := Complex.abs_im_le_norm _
    _ = r := by rw [norm_arcPoint, abs_of_nonneg hr]

lemma continuousOn_arcKernel (b z : ℂ) (r : ℝ)
    (hb : AdmissibleB b) (hr : AdmissibleHeight b r) :
    ContinuousOn (arcKernel b z r) (Icc 0 Real.pi) := by
  intro θ hθ
  have hd := upperStrip_denominator_ne_zero b (arcPoint r θ) hb
    (arcPoint_ne_zero r θ hr.1) (im_arcPoint_nonneg r θ hr.1.le hθ)
    (lt_of_le_of_lt (im_arcPoint_le r θ hr.1.le) hr.2)
  have hk : ContinuousAt (fun t : ℝ => kernel b z (arcPoint r t)) θ :=
    (continuousAt_kernel_of_denominator_ne_zero b z (arcPoint r θ) hd).comp
      (continuous_arcPoint r).continuousAt
  exact (hk.mul
    (continuous_const.mul (continuous_arcPoint r)).continuousAt).continuousWithinAt

lemma intervalIntegrable_arcKernel (b z : ℂ) (r : ℝ)
    (hb : AdmissibleB b) (hr : AdmissibleHeight b r) :
    IntervalIntegrable (arcKernel b z r) volume Real.pi 0 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [Set.uIcc_of_ge Real.pi_pos.le] using continuousOn_arcKernel b z r hb hr

/-- Absolute convergence, not a conditionally convergent contour prescription. -/
theorem integrable_lineKernel (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z) (hh : AdmissibleHeight b h) :
    Integrable (fun x : ℝ => kernel b z (linePoint h x)) := by
  have hz' : 2 * |z.im| < b.re + (b⁻¹).re := by
    change |z.im| < (b.re + (b⁻¹).re) / 2 at hz
    linarith
  simpa only [kernel, linePoint] using
    integrable_exp_div_sinh_product_line_mul b b⁻¹ z h hb (admissibleB_inv b hb) hz'
      (line_denominator_ne_zero b h hb hh)

private lemma integrable_zDerivativeKernel_aux (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z) (hh : AdmissibleHeight b h) :
    Integrable (zDerivativeKernel b z h) := by
  have hz' : 2 * |z.im| < b.re + (b⁻¹).re := by
    change |z.im| < (b.re + (b⁻¹).re) / 2 at hz
    linarith
  change Integrable (fun x : ℝ => zDerivativeKernel b z h x)
  simpa only [zDerivativeKernel, kernel, linePoint] using
    integrable_derivative_exp_div_sinh_product_line_mul b b⁻¹ z h hb
      (admissibleB_inv b hb) hz' (line_denominator_ne_zero b h hb hh)

lemma exp_line_norm_bound (u : ℂ) (h x r : ℝ) (hr : 0 ≤ r) (hu : ‖u‖ ≤ r) :
    ‖Complex.exp (-2 * Complex.I * u * linePoint h x)‖ ≤
      Real.exp (2 * r * |h|) *
        (Real.exp (2 * r * x) + Real.exp (-(2 * r * x))) := by
  have hre : |u.re| ≤ r := (Complex.abs_re_le_norm u).trans hu
  have him : |u.im| ≤ r := (Complex.abs_im_le_norm u).trans hu
  have hre' : u.re * h ≤ r * |h| := by
    calc
      u.re * h ≤ |u.re * h| := le_abs_self _
      _ = |u.re| * |h| := abs_mul _ _
      _ ≤ r * |h| := mul_le_mul_of_nonneg_right hre (abs_nonneg _)
  have him' : u.im * x ≤ r * |x| := by
    calc
      u.im * x ≤ |u.im * x| := le_abs_self _
      _ = |u.im| * |x| := abs_mul _ _
      _ ≤ r * |x| := mul_le_mul_of_nonneg_right him (abs_nonneg _)
  have hform : (-2 * Complex.I * u * linePoint h x).re =
      2 * u.re * h + 2 * u.im * x := by
    simp [linePoint, Complex.mul_re, Complex.mul_im]
    <;> ring
  rw [Complex.norm_exp, hform]
  calc
    Real.exp (2 * u.re * h + 2 * u.im * x) ≤
        Real.exp (2 * r * |h| + |2 * r * x|) := by
      apply Real.exp_le_exp.mpr
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * r)]
      nlinarith
    _ = Real.exp (2 * r * |h|) * Real.exp |2 * r * x| := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_abs_le _) (Real.exp_pos _).le

lemma kernel_add_argument (b z u w : ℂ) :
    kernel b (z + u) w = Complex.exp (-2 * Complex.I * u * w) * kernel b z w := by
  unfold kernel
  rw [show -2 * Complex.I * (z + u) * w =
      -2 * Complex.I * u * w + -2 * Complex.I * z * w by ring,
    Complex.exp_add]
  ring

lemma zDerivativeKernel_add_argument (b z u : ℂ) (h x : ℝ) :
    zDerivativeKernel b (z + u) h x =
      Complex.exp (-2 * Complex.I * u * linePoint h x) * zDerivativeKernel b z h x := by
  unfold zDerivativeKernel
  rw [kernel_add_argument]
  ring

lemma hasDerivAt_kernel_argument (b z w : ℂ) :
    HasDerivAt (fun ζ : ℂ => kernel b ζ w)
      ((-2 * Complex.I * w) * kernel b z w) z := by
  have h := (((hasDerivAt_id z).const_mul (-2 * Complex.I)).mul_const w).cexp
  convert! h.div_const (4 * Complex.sinh (b * w) * Complex.sinh (b⁻¹ * w) * w) using 1 <;>
    (try simp only [id_eq, mul_one, kernel]) <;> ring

lemma zDerivativeKernel_local_bound (b z ζ : ℂ) (h x r : ℝ)
    (hr : 0 ≤ r) (hζ : ‖ζ - z‖ ≤ r) :
    ‖zDerivativeKernel b ζ h x‖ ≤ Real.exp (2 * r * |h|) *
      (‖zDerivativeKernel b (z + Complex.I * (r : ℂ)) h x‖ +
       ‖zDerivativeKernel b (z - Complex.I * (r : ℂ)) h x‖) := by
  have heq : ζ = z + (ζ - z) := by ring
  rw [heq, zDerivativeKernel_add_argument, norm_mul]
  have hb := mul_le_mul_of_nonneg_right (exp_line_norm_bound (ζ - z) h x r hr hζ)
    (norm_nonneg (zDerivativeKernel b z h x))
  convert hb using 1 <;> try rfl
  simp only [zDerivativeKernel_add_argument, sub_eq_add_neg, norm_mul, Complex.norm_exp]
  have hp : (-2 * Complex.I * (Complex.I * (r : ℂ)) * linePoint h x).re = 2 * r * x := by
    simp [linePoint, Complex.mul_re, Complex.mul_im]
    <;> ring
  have hm : (-2 * Complex.I * -(Complex.I * (r : ℂ)) * linePoint h x).re = -(2 * r * x) := by
    simp [linePoint, Complex.mul_re, Complex.mul_im]
    <;> ring
  rw [hp, hm]
  ring


lemma isOpen_inStrip (b : ℂ) : IsOpen {z | InStrip b z} := by
  exact isOpen_lt Complex.continuous_im.abs continuous_const

lemma inStrip_add_I_of_le (b z : ℂ) (r : ℝ) (hr : |z.im| + |r| < stripWidth b) :
    InStrip b (z + Complex.I * (r : ℂ)) := by
  change |(z + Complex.I * (r : ℂ)).im| < stripWidth b
  simpa using (abs_add_le z.im r).trans_lt hr

lemma hasDerivAt_logPhiAtHeight_aux (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z) (hh : AdmissibleHeight b h) :
    HasDerivAt (fun ζ => logPhiAtHeight b ζ h)
      (∫ x : ℝ, zDerivativeKernel b z h x) z := by
  let r : ℝ := (stripWidth b - |z.im|) / 2
  have hr : 0 < r := by dsimp [r]; exact half_pos (sub_pos.mpr hz)
  have hgap : |z.im| + |r| < stripWidth b := by
    rw [abs_of_pos hr]
    dsimp [r]
    change |z.im| < stripWidth b at hz
    linarith
  have hp : InStrip b (z + Complex.I * (r : ℂ)) := inStrip_add_I_of_le b z r hgap
  have hm : InStrip b (z - Complex.I * (r : ℂ)) := by
    simpa [sub_eq_add_neg] using inStrip_add_I_of_le b z (-r) (by simpa using hgap)
  let B : ℝ → ℝ := fun x => Real.exp (2 * r * |h|) *
    (‖zDerivativeKernel b (z + Complex.I * (r : ℂ)) h x‖ +
     ‖zDerivativeKernel b (z - Complex.I * (r : ℂ)) h x‖)
  have hB : Integrable B :=
    ((integrable_zDerivativeKernel_aux b (z + Complex.I * (r : ℂ)) h hb hp hh).norm.add
      (integrable_zDerivativeKernel_aux b (z - Complex.I * (r : ℂ)) h hb hm hh).norm).const_mul _
  have hmeas : ∀ᶠ ζ in 𝓝 z, AEStronglyMeasurable
      (fun x : ℝ => kernel b ζ (linePoint h x)) := by
    filter_upwards [(isOpen_inStrip b).mem_nhds hz] with ζ hζ
    exact (integrable_lineKernel b ζ h hb hζ hh).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (zDerivativeKernel b z h) :=
    (integrable_zDerivativeKernel_aux b z h hb hz hh).aestronglyMeasurable
  have hD : ∀ᵐ x : ℝ, ∀ ζ ∈ Metric.ball z r,
      HasDerivAt (fun ζ => kernel b ζ (linePoint h x))
        (zDerivativeKernel b ζ h x) ζ := by
    exact Eventually.of_forall (fun x ζ _ => hasDerivAt_kernel_argument b ζ (linePoint h x))
  have hbound : ∀ᵐ x : ℝ, ∀ ζ ∈ Metric.ball z r,
      ‖zDerivativeKernel b ζ h x‖ ≤ B x := by
    refine Eventually.of_forall (fun x ζ hζ => ?_)
    exact zDerivativeKernel_local_bound b z ζ h x r hr.le
      (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hζ))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z hr) hmeas (integrable_lineKernel b z h hb hz hh)
    hDmeas hbound hB hD).2


lemma kernel_uniform_tail_bound (b z : ℂ) (H : ℝ) (hb : AdmissibleB b) :
    ∃ C R : ℝ, ∀ h x : ℝ, |h| ≤ H → R ≤ |x| →
      ‖kernel b z (linePoint h x)‖ ≤
        C * Real.exp (-(b.re + (b⁻¹).re - 2 * |z.im|) * |x|) := by
  have hc : 0 < (b⁻¹).re := admissibleB_inv b hb
  refine ⟨4 * Real.exp ((2 * |z.re| + |b.im| + |(b⁻¹).im|) * H),
    max 1 (max ((1 + |b.im| * H) / b.re)
      ((1 + |(b⁻¹).im| * H) / (b⁻¹).re)), ?_⟩
  intro h x hh hx
  have hx1 : 1 ≤ |x| := (le_max_left _ _).trans hx
  have hxp : 1 + |b.im| * H ≤ b.re * |x| := by
    have ht := (le_max_left ((1 + |b.im| * H) / b.re)
      ((1 + |(b⁻¹).im| * H) / (b⁻¹).re)).trans ((le_max_right _ _).trans hx)
    simpa only [mul_comm] using (div_le_iff₀ hb).mp ht
  have hxq : 1 + |(b⁻¹).im| * H ≤ (b⁻¹).re * |x| := by
    have ht := (le_max_right ((1 + |b.im| * H) / b.re)
      ((1 + |(b⁻¹).im| * H) / (b⁻¹).re)).trans ((le_max_right _ _).trans hx)
    simpa only [mul_comm] using (div_le_iff₀ hc).mp ht
  have hw : 1 ≤ ‖linePoint h x‖ := by
    calc
      1 ≤ |x| := hx1
      _ = |(linePoint h x).re| := by simp [linePoint]
      _ ≤ _ := Complex.abs_re_le_norm _
  calc
    ‖kernel b z (linePoint h x)‖ =
        ‖Complex.exp (-2 * I * z * linePoint h x) /
          (4 * Complex.sinh (b * linePoint h x) *
            Complex.sinh (b⁻¹ * linePoint h x))‖ / ‖linePoint h x‖ := by
      rw [kernel, div_mul_eq_div_div, norm_div]
    _ ≤ ‖Complex.exp (-2 * I * z * linePoint h x) /
          (4 * Complex.sinh (b * linePoint h x) *
            Complex.sinh (b⁻¹ * linePoint h x))‖ := div_le_self (norm_nonneg _) hw
    _ ≤ _ := norm_exp_div_sinh_product_line_le_uniform b b⁻¹ z h x H
      |z.re| |z.im| hb.le hc.le hh le_rfl le_rfl hxp hxq

lemma kernel_vertical_sides_tendsto_zero (b z : ℂ) (h₁ h₂ : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z) :
    Tendsto (fun x : ℝ => ∫ y : ℝ in h₁..h₂, kernel b z (linePoint y x)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => ∫ y : ℝ in h₁..h₂, kernel b z (linePoint y x)) atTop (𝓝 0) := by
  let H := max |h₁| |h₂|
  obtain ⟨C, R, hbound⟩ := kernel_uniform_tail_bound b z H hb
  let δ := b.re + (b⁻¹).re - 2 * |z.im|
  have hδ : 0 < δ := by
    change |z.im| < (b.re + (b⁻¹).re) / 2 at hz
    dsimp [δ]
    linarith
  have hH (y : ℝ) (hy : y ∈ [[h₁,h₂]]) : |y| ≤ H := by
    have h₁ : |h₁| ≤ H := le_max_left _ _
    have h₂ : |h₂| ≤ H := le_max_right _ _
    apply abs_le.mpr
    exact ⟨(le_min (abs_le.mp h₁).1 (abs_le.mp h₂).1).trans hy.1,
      hy.2.trans (max_le (abs_le.mp h₁).2 (abs_le.mp h₂).2)⟩
  have aux {l : Filter ℝ} (habs : Tendsto (fun x : ℝ => |x|) l atTop) :
      Tendsto (fun x : ℝ => ∫ y : ℝ in h₁..h₂, kernel b z (linePoint y x)) l (𝓝 0) := by
    apply Contour.tendsto_intervalIntegral_zero_of_uniform_bound
      (M := fun x : ℝ => C * Real.exp (-δ * |x|))
    · filter_upwards [habs.eventually (eventually_ge_atTop R)] with x hx
      exact fun y hy => hbound y x (hH y hy) hx
    · simpa [neg_mul] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp (habs.const_mul_atTop hδ)).const_mul C
  exact ⟨aux tendsto_abs_atBot_atTop, aux tendsto_abs_atTop_atTop⟩

lemma differentiableOn_kernel_upperStrip (b z : ℂ) (h₁ h₂ : ℝ)
    (hb : AdmissibleB b) (hh₁ : AdmissibleHeight b h₁) (hh₂ : AdmissibleHeight b h₂) :
    DifferentiableOn ℂ (kernel b z) {w : ℂ | w.im ∈ [[h₁,h₂]]} := by
  intro w hw
  have hhw : AdmissibleHeight b w.im := by
    exact ⟨(lt_min hh₁.1 hh₂.1).trans_le hw.1,
      hw.2.trans_lt (max_lt hh₁.2 hh₂.2)⟩
  have heq : linePoint w.im w.re = w := by apply Complex.ext <;> simp [linePoint]
  have hd := line_denominator_ne_zero b w.im hb hhw w.re
  rw [heq] at hd
  apply DifferentiableAt.differentiableWithinAt
  unfold kernel
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact hd

theorem logPhiAtHeight_eq (b z : ℂ) (h₁ h₂ : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z)
    (hh₁ : AdmissibleHeight b h₁) (hh₂ : AdmissibleHeight b h₂) :
    logPhiAtHeight b z h₁ = logPhiAtHeight b z h₂ := by
  obtain ⟨hl,hr⟩ := kernel_vertical_sides_tendsto_zero b z h₁ h₂ hb hz
  have heq := Contour.horizontal_integral_eq_of_vanishing_sides (kernel b z) h₁ h₂
    (differentiableOn_kernel_upperStrip b z h₁ h₂ hb hh₁ hh₂)
    (by simpa [linePoint, mul_comm] using integrable_lineKernel b z h₁ hb hz hh₁)
    (by simpa [linePoint, mul_comm] using integrable_lineKernel b z h₂ hb hz hh₂)
    (by simpa [linePoint, mul_comm] using hl)
    (by simpa [linePoint, mul_comm] using hr)
  simpa [logPhiAtHeight, linePoint, mul_comm] using heq

theorem integrable_detour (b z : ℂ) (r : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z) (hr : AdmissibleHeight b r) :
    IntegrableOn (fun x : ℝ => kernel b z (x : ℂ)) (Iic (-r)) ∧
    IntervalIntegrable (arcKernel b z r) volume Real.pi 0 ∧
    IntegrableOn (fun x : ℝ => kernel b z (x : ℂ)) (Ici r) := by
  let δ : ℝ := b.re + (b⁻¹).re - 2 * |z.im|
  have hδ : 0 < δ := by
    change |z.im| < (b.re + (b⁻¹).re) / 2 at hz
    dsimp [δ]
    linarith
  obtain ⟨C, R, hbound⟩ := kernel_uniform_tail_bound b z 0 hb
  have hbot : (fun x : ℝ => kernel b z (x : ℂ)) =O[atBot]
      (fun x : ℝ => Real.exp (δ * x)) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_le_atBot (min (-R) 0)] with x hx
    have hx0 : x ≤ 0 := hx.trans (min_le_right _ _)
    have hxR : R ≤ |x| := by
      rw [abs_of_nonpos hx0]
      linarith [hx.trans (min_le_left (-R) 0)]
    simpa only [linePoint, Complex.ofReal_zero, mul_zero, add_zero,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonpos hx0,
      mul_neg, neg_mul, neg_neg] using hbound 0 x (by simp) hxR
  have htop : (fun x : ℝ => kernel b z (x : ℂ)) =O[atTop]
      (fun x : ℝ => Real.exp (-δ * x)) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (max R 0)] with x hx
    have hx0 : 0 ≤ x := (le_max_right _ _).trans hx
    have hxR : R ≤ |x| := by
      rw [abs_of_nonneg hx0]
      exact (le_max_left _ _).trans hx
    simpa only [linePoint, Complex.ofReal_zero, mul_zero, add_zero,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hx0]
      using hbound 0 x (by simp) hxR
  have hmi := ((continuousOn_realKernel_Iic b z hb r hr.1).locallyIntegrableOn
    measurableSet_Iic).integrableOn_of_isBigO_atBot hbot
      (integrableOn_Iic_iff_integrableAtFilter_atBot.mp
        (integrableOn_exp_mul_Iic hδ 0)).1
  have hpi := ((continuousOn_realKernel_Ici b z hb r hr.1).locallyIntegrableOn
    measurableSet_Ici).integrableOn_of_isBigO_atTop htop
      (integrableOn_Ici_iff_integrableAtFilter_atTop.mp
        (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
          (integrableOn_exp_mul_Ioi (neg_neg_iff_pos.mpr hδ) 0))).1
  exact ⟨hmi, intervalIntegrable_arcKernel b z r hb hr, hpi⟩

lemma differentiableAt_kernel_of_denominator_ne_zero (b z w : ℂ)
    (hw : 4 * Complex.sinh (b * w) * Complex.sinh (b⁻¹ * w) * w ≠ 0) :
    DifferentiableAt ℂ (kernel b z) w := by
  unfold kernel
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact hw

lemma differentiableOn_kernel_openUpperStrip (b z : ℂ) (hb : AdmissibleB b) :
    DifferentiableOn ℂ (kernel b z) {w : ℂ | 0 < w.im ∧ w.im < poleHeight b} := by
  intro w hw
  have hw0 : w ≠ 0 := by intro he; simpa [he] using hw.1
  exact (differentiableAt_kernel_of_denominator_ne_zero b z w
    (upperStrip_denominator_ne_zero b w hb hw0 hw.1.le hw.2)).differentiableWithinAt

lemma continuousOn_kernel_puncturedUpperStrip (b z : ℂ) (hb : AdmissibleB b) :
    ContinuousOn (kernel b z) {w : ℂ | 0 ≤ w.im ∧ w.im < poleHeight b ∧ w ≠ 0} := by
  intro w hw
  exact (continuousAt_kernel_of_denominator_ne_zero b z w
    (upperStrip_denominator_ne_zero b w hb hw.2.2 hw.1 hw.2.1)).continuousWithinAt

/-- This is the precise bridge from the definition to RW26's `ℝ + i0`. -/
theorem logPhi_eq_detour (b z : ℂ) (r : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z) (hr : AdmissibleHeight b r) :
    logPhi b z = detourLog b z r := by
  let h := (r + poleHeight b) / 2
  have hh : AdmissibleHeight b h := by
    change 0 < (r + poleHeight b) / 2 ∧ (r + poleHeight b) / 2 < poleHeight b
    constructor <;> linarith [hr.1, hr.2]
  have hrh : r ≤ h := by dsimp [h]; linarith [hr.2]
  obtain ⟨hminus, _, hplus⟩ := integrable_detour b z r hb hz hr
  obtain ⟨hleft,hright⟩ := kernel_vertical_sides_tendsto_zero b z 0 h hb hz
  have heq := Contour.horizontal_eq_detour hr.1 hrh hh.2
    (differentiableOn_kernel_openUpperStrip b z hb)
    (continuousOn_kernel_puncturedUpperStrip b z hb)
    (by simpa [linePoint, mul_comm] using integrable_lineKernel b z h hb hz hh)
    hminus hplus
    (by simpa [linePoint, mul_comm] using hleft)
    (by simpa [linePoint, mul_comm] using hright)
  have hpoint (θ : ℝ) : circleMap 0 r θ = arcPoint r θ := by
    simp [circleMap, arcPoint, mul_comm]
  calc
    logPhi b z = logPhiAtHeight b z h := logPhiAtHeight_eq b z (canonicalHeight b) h
      hb hz (canonicalHeight_admissible b hb) hh
    _ = detourLog b z r := by
      simpa [logPhiAtHeight, detourLog, arcKernel, linePoint, hpoint, mul_comm] using heq

theorem tendsto_detourLog (b z : ℂ) (hb : AdmissibleB b) (hz : InStrip b z) :
    Tendsto (detourLog b z) (nhdsWithin 0 (Ioi 0)) (𝓝 (logPhi b z)) := by
  have hp : 0 < poleHeight b := by
    have hc := (canonicalHeight_admissible b hb).1
    change 0 < poleHeight b / 2 at hc
    linarith
  have hsmall : ∀ᶠ r in nhdsWithin 0 (Ioi 0), AdmissibleHeight b r := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hp)] with r hr hrH
    exact ⟨hr, hrH⟩
  exact tendsto_const_nhds.congr' (hsmall.mono fun r hr => (logPhi_eq_detour b z r hb hz hr))

theorem differentiableOn_logPhi (b : ℂ) (hb : AdmissibleB b) :
    DifferentiableOn ℂ (logPhi b) {z | InStrip b z} := by
  intro z hz
  exact (hasDerivAt_logPhiAtHeight_aux b z (canonicalHeight b) hb hz
    (canonicalHeight_admissible b hb)).differentiableAt.differentiableWithinAt

theorem differentiableOn_phi (b : ℂ) (hb : AdmissibleB b) :
    DifferentiableOn ℂ (phi b) {z | InStrip b z} := by
  exact Complex.differentiable_exp.comp_differentiableOn (differentiableOn_logPhi b hb)

open Metric in
theorem exists_local_integrable_kernel_majorant
    (p₀ : ℂ × ℂ) (hp₀ : p₀ ∈ parameterDomain)
    (h : ℝ) (hh : AdmissibleHeight p₀.1 h) :
    ∃ r > 0, ∃ B : ℝ → ℝ, Integrable B ∧
      ∀ p ∈ Metric.ball p₀ (2 * r),
        (AdmissibleB p.1 ∧ InStrip p.1 p.2 ∧ AdmissibleHeight p.1 h) ∧
          ∀ x : ℝ, ‖kernel p.1 p.2 (linePoint h x)‖ ≤ B x := by
  have hb₀ : AdmissibleB p₀.1 := hp₀.1
  have hc₀ : 0 < (p₀.1⁻¹).re := admissibleB_inv p₀.1 hb₀
  change 0 < p₀.1.re at hb₀
  let a := p₀.1.re / 2
  let c := (p₀.1⁻¹).re / 2
  let δ := (p₀.1.re + (p₀.1⁻¹).re - 2 * |p₀.2.im|) / 2
  let P := |p₀.1.im| + 1
  let Q := |(p₀.1⁻¹).im| + 1
  let M := |p₀.2.re| + 1
  have ha : 0 < a := by dsimp [a]; exact half_pos hb₀
  have hc : 0 < c := by dsimp [c]; exact half_pos hc₀
  have hδ : 0 < δ := by
    have hz₀ : |p₀.2.im| < (p₀.1.re + (p₀.1⁻¹).re) / 2 := hp₀.2
    dsimp [δ]
    linarith
  have hre : ContinuousAt (fun p : ℂ × ℂ => p.1.re) p₀ :=
    (Complex.continuous_re.comp continuous_fst).continuousAt
  have hinv : ContinuousAt (fun p : ℂ × ℂ => p.1⁻¹) p₀ :=
    continuous_fst.continuousAt.inv₀ (admissibleB_ne_zero p₀.1 hb₀)
  have hrei : ContinuousAt (fun p : ℂ × ℂ => (p.1⁻¹).re) p₀ :=
    Complex.continuous_re.continuousAt.comp hinv
  have him : ContinuousAt (fun p : ℂ × ℂ => |p.1.im|) p₀ :=
    (Complex.continuous_im.comp continuous_fst).continuousAt.abs
  have himi : ContinuousAt (fun p : ℂ × ℂ => |(p.1⁻¹).im|) p₀ :=
    (Complex.continuous_im.continuousAt.comp hinv).abs
  have hzre : ContinuousAt (fun p : ℂ × ℂ => |p.2.re|) p₀ :=
    (Complex.continuous_re.comp continuous_snd).continuousAt.abs
  have hzim : ContinuousAt (fun p : ℂ × ℂ => |p.2.im|) p₀ :=
    (Complex.continuous_im.comp continuous_snd).continuousAt.abs
  have hdecay : ContinuousAt (fun p : ℂ × ℂ =>
      p.1.re + (p.1⁻¹).re - 2 * |p.2.im|) p₀ :=
    (hre.add hrei).sub (continuousAt_const.mul hzim)
  have hheight : ContinuousAt (fun p : ℂ × ℂ => poleHeight p.1) p₀ := by
    exact continuousAt_const.mul (hre.inf hrei)
  let S : Set (ℂ × ℂ) := {p |
    a < p.1.re ∧ c < (p.1⁻¹).re ∧
      δ < p.1.re + (p.1⁻¹).re - 2 * |p.2.im| ∧
      |p.1.im| < P ∧ |(p.1⁻¹).im| < Q ∧ |p.2.re| < M ∧
        h < poleHeight p.1}
  have hS : S ∈ 𝓝 p₀ := by
    have hpa : a < p₀.1.re := by dsimp [a]; linarith [hb₀]
    have hpc : c < (p₀.1⁻¹).re := by dsimp [c]; linarith
    have hpd : δ < p₀.1.re + (p₀.1⁻¹).re - 2 * |p₀.2.im| := by
      dsimp [δ] at hδ ⊢
      linarith
    have hpP : |p₀.1.im| < P := by dsimp [P]; linarith
    have hpQ : |(p₀.1⁻¹).im| < Q := by dsimp [Q]; linarith
    have hpM : |p₀.2.re| < M := by dsimp [M]; linarith
    filter_upwards [continuousAt_const.eventually_lt hre hpa,
      continuousAt_const.eventually_lt hrei hpc,
      continuousAt_const.eventually_lt hdecay hpd,
      him.eventually_lt continuousAt_const hpP,
      himi.eventually_lt continuousAt_const hpQ,
      hzre.eventually_lt continuousAt_const hpM,
      continuousAt_const.eventually_lt hheight hh.2] with
        p hpa hpc hpd hpP hpQ hpM hph
    exact ⟨hpa, hpc, hpd, hpP, hpQ, hpM, hph⟩
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp hS
  let K := Metric.closedBall p₀ (ε / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKS : K ⊆ S :=
    (Metric.closedBall_subset_ball (show ε / 2 < ε by linarith)).trans hεS
  have hdom : ∀ p ∈ K,
      AdmissibleB p.1 ∧ InStrip p.1 p.2 ∧ AdmissibleHeight p.1 h := by
    intro p hp
    rcases hKS hp with ⟨hpa, hpc, hpd, hpP, hpQ, hpM, hph⟩
    refine ⟨ha.trans hpa, ?_, hh.1, hph⟩
    change |p.2.im| < (p.1.re + (p.1⁻¹).re) / 2
    linarith
  let R := max 1 (max ((1 + P * |h|) / a) ((1 + Q * |h|) / c))
  let C := 4 * Real.exp ((2 * M + P + Q) * |h|)
  have htail : ∀ p ∈ K, ∀ x : ℝ, R ≤ |x| →
      ‖kernel p.1 p.2 (linePoint h x)‖ ≤ C * Real.exp (-δ * |x|) := by
    intro p hp x hx
    rcases hKS hp with ⟨hpa, hpc, hpd, hpP, hpQ, hpM, hph⟩
    have hx1 : 1 ≤ |x| := (le_max_left _ _).trans hx
    have hxp : 1 + P * |h| ≤ a * |x| := by
      have hhx := (le_max_left ((1 + P * |h|) / a)
        ((1 + Q * |h|) / c)).trans ((le_max_right _ _).trans hx)
      simpa only [mul_comm] using (div_le_iff₀ ha).mp hhx
    have hxq : 1 + Q * |h| ≤ c * |x| := by
      have hhx := (le_max_right ((1 + P * |h|) / a)
        ((1 + Q * |h|) / c)).trans ((le_max_right _ _).trans hx)
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hhx
    simpa only [kernel, linePoint] using
      norm_exp_div_sinh_product_line_mul_le_uniform_parameters
        p.1 p.1⁻¹ p.2 h x a c P Q M δ ha hc hpa.le hpc.le
          hpP.le hpQ.le hpM.le hpd.le hx1 hxp hxq
  have hcont : ContinuousOn (fun px : (ℂ × ℂ) × ℝ =>
      kernel px.1.1 px.1.2 (linePoint h px.2)) (K ×ˢ Icc (-R) R) := by
    intro px hpx
    have hb : AdmissibleB px.1.1 := (hdom px.1 hpx.1).1
    have hheight : AdmissibleHeight px.1.1 h := (hdom px.1 hpx.1).2.2
    have hinvpx : ContinuousAt (fun qx : (ℂ × ℂ) × ℝ => qx.1.1⁻¹) px :=
      (continuous_fst.comp continuous_fst).continuousAt.inv₀
        (admissibleB_ne_zero px.1.1 hb)
    apply ContinuousAt.continuousWithinAt
    unfold kernel linePoint
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact line_denominator_ne_zero px.1.1 h hb hheight px.2
  obtain ⟨B, hB, hBbound⟩ :=
    exists_integrable_majorant_of_compact_exp_tail hK
      (fun p x => kernel p.1 p.2 (linePoint h x)) hδ hcont htail
  refine ⟨ε / 4, by linarith, B, hB, ?_⟩
  intro p hp
  have hpK : p ∈ K := by
    change dist p p₀ ≤ ε / 2
    have hpdist : dist p p₀ < 2 * (ε / 4) := hp
    linarith
  exact ⟨hdom p hpK, hBbound p hpK⟩

theorem local_lineKernel_majorant :
    ∀ p ∈ parameterDomain, ∀ h : ℝ, AdmissibleHeight p.1 h →
      ∃ s ∈ 𝓝 p, ∃ B : ℝ → ℝ, Integrable B ∧
        ∀ q ∈ s, ∀ x : ℝ, ‖kernel q.1 q.2 (linePoint h x)‖ ≤ B x := by
  intro p hp h hh
  obtain ⟨r, hr, B, hB, hbound⟩ := exists_local_integrable_kernel_majorant p hp h hh
  refine ⟨Metric.ball p (2 * r), Metric.ball_mem_nhds p (by positivity), B, hB, ?_⟩
  intro q hq x
  exact (hbound q hq).2 x

lemma joint_differentiableAt_kernel (p : ℂ × ℂ) (w : ℂ)
    (hb : p.1 ≠ 0)
    (hd : 4 * Complex.sinh (p.1 * w) * Complex.sinh (p.1⁻¹ * w) * w ≠ 0) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ => kernel q.1 q.2 w) p := by
  unfold kernel
  fun_prop (disch := assumption)

lemma joint_admissibleHeight_eventually (p : ℂ × ℂ) (h : ℝ)
    (hb : AdmissibleB p.1) (hh : AdmissibleHeight p.1 h) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 p, AdmissibleB q.1 ∧ AdmissibleHeight q.1 h := by
  have hr : ContinuousAt (fun q : ℂ × ℂ => q.1.re) p := by fun_prop
  have hri : ContinuousAt (fun q : ℂ × ℂ => (q.1⁻¹).re) p :=
    Complex.continuous_re.continuousAt.comp
      (continuous_fst.continuousAt.inv₀ (admissibleB_ne_zero p.1 hb))
  have hp : ContinuousAt (fun q : ℂ × ℂ => poleHeight q.1) p :=
    continuousAt_const.mul (hr.min hri)
  filter_upwards [continuousAt_const.eventually_lt hr hb,
    continuousAt_const.eventually_lt hp hh.2] with q hq₁ hq₂
  exact ⟨hq₁, hh.1, hq₂⟩

lemma joint_continuous_lineKernel (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hh : AdmissibleHeight b h) :
    Continuous (fun x : ℝ => kernel b z (linePoint h x)) := by
  unfold kernel
  apply Continuous.div
  · unfold linePoint; fun_prop
  · unfold linePoint; fun_prop
  · exact line_denominator_ne_zero b h hb hh

lemma joint_contDiffAt_kernel_uncurry (p : ℂ × ℂ) (w : ℂ)
    (hb : p.1 ≠ 0)
    (hd : 4 * Complex.sinh (p.1 * w) * Complex.sinh (p.1⁻¹ * w) * w ≠ 0) :
    ContDiffAt ℂ 1 (fun q : ℂ × (ℂ × ℂ) => kernel q.2.1 q.2.2 q.1) (w,p) := by
  unfold kernel
  fun_prop (disch := assumption)

lemma joint_continuousAt_fderiv_kernel_parameter (p : ℂ × ℂ) (w : ℂ)
    (hb : p.1 ≠ 0)
    (hd : 4 * Complex.sinh (p.1 * w) * Complex.sinh (p.1⁻¹ * w) * w ≠ 0) :
    ContinuousAt (fun w => fderiv ℂ (fun q : ℂ × ℂ => kernel q.1 q.2 w) p) w := by
  exact ((joint_contDiffAt_kernel_uncurry p w hb hd).fderiv
    (contDiffAt_const : ContDiffAt ℂ 0 (fun _ : ℂ => p) w) (by norm_num)).continuousAt

lemma joint_continuous_fderiv_lineKernel (p : ℂ × ℂ) (h : ℝ)
    (hb : AdmissibleB p.1) (hh : AdmissibleHeight p.1 h) :
    Continuous (fun x : ℝ => fderiv ℂ
      (fun q : ℂ × ℂ => kernel q.1 q.2 (linePoint h x)) p) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (joint_continuousAt_fderiv_kernel_parameter p (linePoint h x)
    (admissibleB_ne_zero p.1 hb) (line_denominator_ne_zero p.1 h hb hh x)).comp
    (by unfold linePoint; fun_prop)

open Metric in
theorem joint_hasFDerivAt_logPhiAtHeight_of_bound (p : ℂ × ℂ) (h r : ℝ) (B : ℝ → ℝ)
    (hr : 0 < r)
    (hgood : ∀ q ∈ ball p (2*r),
      AdmissibleB q.1 ∧ InStrip q.1 q.2 ∧ AdmissibleHeight q.1 h)
    (hB : ∀ q ∈ ball p (2*r), ∀ x : ℝ, ‖kernel q.1 q.2 (linePoint h x)‖ ≤ B x)
    (hBi : Integrable B) :
    HasFDerivAt (fun q : ℂ × ℂ => logPhiAtHeight q.1 q.2 h)
      (∫ x : ℝ, fderiv ℂ (fun q : ℂ × ℂ => kernel q.1 q.2 (linePoint h x)) p) p := by
  have hp : p ∈ ball p (2*r) := mem_ball_self (by positivity)
  have hpG := hgood p hp
  apply joint_hasFDerivAt_integral_of_locally_dominated_holomorphic hr
  · filter_upwards [isOpen_ball.mem_nhds hp] with q hq
    exact (joint_continuous_lineKernel q.1 q.2 h (hgood q hq).1
      (hgood q hq).2.2).aestronglyMeasurable
  · exact integrable_lineKernel p.1 p.2 h hpG.1 hpG.2.1 hpG.2.2
  · exact (joint_continuous_fderiv_lineKernel p h hpG.1 hpG.2.2).aestronglyMeasurable
  · intro x q hq
    exact (joint_differentiableAt_kernel q (linePoint h x)
      (admissibleB_ne_zero q.1 (hgood q hq).1)
      (line_denominator_ne_zero q.1 h (hgood q hq).1 (hgood q hq).2.2 x)
      ).differentiableWithinAt
  · exact fun x q hq => hB q hq x
  · exact hBi

open Metric in
theorem joint_differentiableOn_logPhi_of_local_majorant
    (hmajorant : ∀ p ∈ parameterDomain, ∀ h : ℝ, AdmissibleHeight p.1 h →
      ∃ s ∈ 𝓝 p, ∃ B : ℝ → ℝ, Integrable B ∧
        ∀ q ∈ s, ∀ x : ℝ, ‖kernel q.1 q.2 (linePoint h x)‖ ≤ B x) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => logPhi p.1 p.2) parameterDomain := by
  intro p hp
  let h := canonicalHeight p.1
  have hh : AdmissibleHeight p.1 h := canonicalHeight_admissible p.1 hp.1
  obtain ⟨s, hs, B, hBi, hB⟩ := hmajorant p hp h hh
  have hgood : ∀ᶠ q : ℂ × ℂ in 𝓝 p,
      AdmissibleB q.1 ∧ InStrip q.1 q.2 ∧ AdmissibleHeight q.1 h := by
    filter_upwards [isOpen_parameterDomain.mem_nhds hp,
      joint_admissibleHeight_eventually p h hp.1 hh] with q hq hhq
    exact ⟨hq.1, hq.2, hhq.2⟩
  have hU : s ∩ {q : ℂ × ℂ |
      AdmissibleB q.1 ∧ InStrip q.1 q.2 ∧ AdmissibleHeight q.1 h} ∈ 𝓝 p :=
    Filter.inter_mem hs hgood
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp hU
  have hr : 0 < R/2 := by positivity
  have heqR : 2 * (R/2) = R := by ring
  have hgood' : ∀ q ∈ ball p (2*(R/2)),
      AdmissibleB q.1 ∧ InStrip q.1 q.2 ∧ AdmissibleHeight q.1 h := by
    intro q hq
    exact (hRU (by simpa [heqR] using hq)).2
  have hB' : ∀ q ∈ ball p (2*(R/2)), ∀ x : ℝ,
      ‖kernel q.1 q.2 (linePoint h x)‖ ≤ B x := by
    intro q hq
    exact hB q (hRU (by simpa [heqR] using hq)).1
  have hd : DifferentiableAt ℂ (fun q : ℂ × ℂ => logPhiAtHeight q.1 q.2 h) p :=
    (joint_hasFDerivAt_logPhiAtHeight_of_bound p h (R/2) B hr hgood' hB' hBi).differentiableAt
  have heq : (fun q : ℂ × ℂ => logPhi q.1 q.2) =ᶠ[𝓝 p]
      (fun q => logPhiAtHeight q.1 q.2 h) := by
    filter_upwards [hgood] with q hq
    exact logPhiAtHeight_eq q.1 q.2 (canonicalHeight q.1) h hq.1 hq.2.1
      (canonicalHeight_admissible q.1 hq.1) hq.2.2
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Locally determine a contour height before differentiating; the `min` in the canonical height is
not a holomorphic function of the parameter. -/
theorem differentiableOn_logPhi_joint :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => logPhi p.1 p.2) parameterDomain := by
  exact joint_differentiableOn_logPhi_of_local_majorant local_lineKernel_majorant

theorem differentiableOn_phi_joint :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => phi p.1 p.2) parameterDomain := by
  exact Complex.differentiable_exp.comp_differentiableOn differentiableOn_logPhi_joint

theorem integrable_zDerivativeKernel (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z) (hh : AdmissibleHeight b h) :
    Integrable (zDerivativeKernel b z h) := by
  exact integrable_zDerivativeKernel_aux b z h hb hz hh

theorem hasDerivAt_logPhi (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hz : InStrip b z) (hh : AdmissibleHeight b h) :
    HasDerivAt (logPhi b) (∫ x : ℝ, zDerivativeKernel b z h x) z := by
  have heq : logPhi b =ᶠ[𝓝 z] (fun ζ => logPhiAtHeight b ζ h) := by
    filter_upwards [(isOpen_inStrip b).mem_nhds hz] with ζ hζ
    exact logPhiAtHeight_eq b ζ (canonicalHeight b) h hb hζ
      (canonicalHeight_admissible b hb) hh
  exact (hasDerivAt_logPhiAtHeight_aux b z h hb hz hh).congr_of_eventuallyEq heq

theorem phi_ne_zero (b z : ℂ) (hb : AdmissibleB b) (hz : InStrip b z) :
    phi b z ≠ 0 := by
  exact Complex.exp_ne_zero _

theorem phi_self_dual (b z : ℂ) (hb : AdmissibleB b) (hz : InStrip b z) :
    phi b z = phi b⁻¹ z := by
  have hc : canonicalHeight b = canonicalHeight b⁻¹ := by
    simp [canonicalHeight, poleHeight, min_comm]
  unfold phi logPhi
  rw [hc]
  congr 1
  unfold logPhiAtHeight
  congr 1
  funext x
  simp only [kernel, inv_inv]
  congr 1
  ring

lemma inStrip_b_shifts_iff (b z : ℂ) (hb : AdmissibleB b) :
    (InStrip b (z - Complex.I * b / 2) ∧ InStrip b (z + Complex.I * b / 2)) ↔
      |z.im| < (b⁻¹).re / 2 := by
  have hm : (z - Complex.I * b / 2).im = z.im - b.re / 2 := by
    simp [Complex.div_ofNat_im]
  have hp : (z + Complex.I * b / 2).im = z.im + b.re / 2 := by
    simp [Complex.div_ofNat_im]
  simp only [InStrip, stripWidth, hm, hp, abs_lt]
  change 0 < b.re at hb
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> constructor <;> linarith

lemma kernel_b_difference (b z w : ℂ) (hs : Complex.sinh (b * w) ≠ 0) :
    kernel b (z - Complex.I * b / 2) w - kernel b (z + Complex.I * b / 2) w =
      -Complex.exp (-2 * Complex.I * z * w) / (2 * Complex.sinh (b⁻¹ * w) * w) := by
  have hm : -2 * Complex.I * (z - Complex.I * b / 2) * w =
      -2 * Complex.I * z * w + -(b * w) := by
    ring_nf
    simp [Complex.I_sq]
    <;> ring
  have hp : -2 * Complex.I * (z + Complex.I * b / 2) * w =
      -2 * Complex.I * z * w + b * w := by
    ring_nf
    simp [Complex.I_sq]
    <;> ring
  simp only [kernel, hm, hp, Complex.exp_add]
  rw [← sub_div, ← mul_sub, ← neg_sub, ← Complex.two_sinh]
  calc
    _ = (2 * Complex.sinh (b * w) * (-Complex.exp (-2 * Complex.I * z * w))) /
        (2 * Complex.sinh (b * w) * (2 * Complex.sinh (b⁻¹ * w) * w)) := by
          congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ (mul_ne_zero (by norm_num) hs)

lemma zDerivativeKernel_b_difference (b z : ℂ) (h x : ℝ)
    (hs : Complex.sinh (b * linePoint h x) ≠ 0) (hw : linePoint h x ≠ 0) :
    zDerivativeKernel b (z - Complex.I * b / 2) h x -
      zDerivativeKernel b (z + Complex.I * b / 2) h x =
        Complex.I * (Complex.exp (-2 * Complex.I * z * linePoint h x) /
          Complex.sinh (b⁻¹ * linePoint h x)) := by
  simp only [zDerivativeKernel, ← mul_sub, kernel_b_difference b z (linePoint h x) hs]
  field_simp
  <;> ring

lemma singleSinh_line_integrable (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hh : AdmissibleHeight b h)
    (hminus : InStrip b (z - Complex.I * b / 2))
    (hplus : InStrip b (z + Complex.I * b / 2)) :
    Integrable (fun x : ℝ => Complex.exp (-2 * Complex.I * z * linePoint h x) /
      Complex.sinh (b⁻¹ * linePoint h x)) := by
  have hd := (integrable_zDerivativeKernel b _ h hb hminus hh).sub
    (integrable_zDerivativeKernel b _ h hb hplus hh)
  have heq (x : ℝ) :
      Complex.exp (-2 * Complex.I * z * linePoint h x) /
          Complex.sinh (b⁻¹ * linePoint h x) =
        (-Complex.I) * (zDerivativeKernel b (z - Complex.I * b / 2) h x -
          zDerivativeKernel b (z + Complex.I * b / 2) h x) := by
    have hn := line_denominator_ne_zero b h hb hh x
    have hs : Complex.sinh (b * linePoint h x) ≠ 0 := fun hs => hn (by simp [hs])
    have hw : linePoint h x ≠ 0 := fun hw => hn (by simp [hw])
    rw [zDerivativeKernel_b_difference b z h x hs hw]
    ring_nf
    simp [Complex.I_sq]
  exact (hd.const_mul (-Complex.I)).congr
    (Filter.Eventually.of_forall (fun x => (heq x).symm))

lemma logPhi_b_difference_eq_integral (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hh : AdmissibleHeight b h)
    (hminus : InStrip b (z - Complex.I * b / 2))
    (hplus : InStrip b (z + Complex.I * b / 2)) :
    logPhi b (z - Complex.I * b / 2) - logPhi b (z + Complex.I * b / 2) =
      ∫ x : ℝ, -Complex.exp (-2 * Complex.I * z * linePoint h x) /
        (2 * Complex.sinh (b⁻¹ * linePoint h x) * linePoint h x) := by
  have hm := logPhiAtHeight_eq b _ (canonicalHeight b) h hb hminus
    (canonicalHeight_admissible b hb) hh
  have hp := logPhiAtHeight_eq b _ (canonicalHeight b) h hb hplus
    (canonicalHeight_admissible b hb) hh
  change logPhiAtHeight b _ (canonicalHeight b) - logPhiAtHeight b _ (canonicalHeight b) = _
  rw [hm, hp]
  unfold logPhiAtHeight
  rw [← integral_sub (integrable_lineKernel b _ h hb hminus hh)
    (integrable_lineKernel b _ h hb hplus hh)]
  apply integral_congr_ae
  filter_upwards [] with x
  apply kernel_b_difference
  have hn := line_denominator_ne_zero b h hb hh x
  exact fun hs => hn (by simp [hs])

lemma hasDerivAt_logPhi_b_difference (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hh : AdmissibleHeight b h)
    (hminus : InStrip b (z - Complex.I * b / 2))
    (hplus : InStrip b (z + Complex.I * b / 2)) :
    HasDerivAt (fun ζ : ℂ => logPhi b (ζ - Complex.I * b / 2) -
      logPhi b (ζ + Complex.I * b / 2))
      (Complex.I * ∫ x : ℝ, Complex.exp (-2 * Complex.I * z * linePoint h x) /
        Complex.sinh (b⁻¹ * linePoint h x)) z := by
  have hm := (hasDerivAt_logPhi b _ h hb hminus hh).comp z
    ((hasDerivAt_id z).sub_const (Complex.I * b / 2))
  have hp := (hasDerivAt_logPhi b _ h hb hplus hh).comp z
    ((hasDerivAt_id z).add_const (Complex.I * b / 2))
  have heq :
      (∫ x : ℝ, zDerivativeKernel b (z - Complex.I * b / 2) h x) -
        (∫ x : ℝ, zDerivativeKernel b (z + Complex.I * b / 2) h x) =
      Complex.I * ∫ x : ℝ, Complex.exp (-2 * Complex.I * z * linePoint h x) /
        Complex.sinh (b⁻¹ * linePoint h x) := by
    rw [← integral_sub (integrable_zDerivativeKernel b _ h hb hminus hh)
      (integrable_zDerivativeKernel b _ h hb hplus hh), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    apply zDerivativeKernel_b_difference
    · have hn := line_denominator_ne_zero b h hb hh x
      exact fun hs => hn (by simp [hs])
    · have hn := line_denominator_ne_zero b h hb hh x
      exact fun hw => hn (by simp [hw])
  convert! hm.sub hp using 1 <;> simp [Function.comp_def, heq]

lemma norm_kernel_real_translate (b z : ℂ) (h x t : ℝ) :
    ‖kernel b (z + (t : ℂ)) (linePoint h x)‖ =
      Real.exp (2 * h * t) * ‖kernel b z (linePoint h x)‖ := by
  rw [kernel_add_argument, norm_mul, Complex.norm_exp]
  congr 2
  simp [linePoint, Complex.mul_re, Complex.mul_im]
  <;> ring

lemma norm_logPhi_real_translate_le (b z : ℂ) (t : ℝ) :
    ‖logPhi b (z + (t : ℂ))‖ ≤ Real.exp (2 * canonicalHeight b * t) *
      ∫ x : ℝ, ‖kernel b z (linePoint (canonicalHeight b) x)‖ := by
  unfold logPhi logPhiAtHeight
  calc
    _ ≤ ∫ x : ℝ, ‖kernel b (z + (t : ℂ)) (linePoint (canonicalHeight b) x)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun x => norm_kernel_real_translate b z (canonicalHeight b) x t)

lemma tendsto_logPhi_real_atBot (b z : ℂ) (hb : AdmissibleB b) :
    Tendsto (fun t : ℝ => logPhi b (z + (t : ℂ))) atBot (𝓝 0) := by
  have hh : 0 < canonicalHeight b := (canonicalHeight_admissible b hb).1
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun t => norm_logPhi_real_translate_le b z t))
  simpa using (Real.tendsto_exp_atBot.comp
    ((tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot).const_mul_atBot
      (mul_pos (by norm_num : (0 : ℝ) < 2) hh))).mul_const
      (∫ x : ℝ, ‖kernel b z (linePoint (canonicalHeight b) x)‖)

lemma tendsto_phi_real_atBot (b z : ℂ) (hb : AdmissibleB b) :
    Tendsto (fun t : ℝ => phi b (z + (t : ℂ))) atBot (𝓝 1) := by
  simpa only [phi, Function.comp_def, Complex.exp_zero] using
    Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_logPhi_real_atBot b z hb)

lemma difference_factor_ne_zero (b z : ℂ) (hb : AdmissibleB b)
    (hz : |z.im| < (b⁻¹).re / 2) :
    1 + Complex.exp (2 * (Real.pi : ℂ) * b * z) ≠ 0 := by
  intro hzero
  have he : Complex.exp (2 * (Real.pi : ℂ) * b * z) =
      Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [Complex.exp_pi_mul_I]
    linear_combination hzero
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hb0 := admissibleB_ne_zero b hb
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hzn : z = (((n : ℂ) + 1 / 2) * Complex.I) * b⁻¹ := by
    have hc : 2 * (Real.pi : ℂ) * b ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hπ) hb0
    apply (mul_left_cancel₀ hc)
    calc
      2 * (Real.pi : ℂ) * b * z =
          (Real.pi : ℂ) * Complex.I + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
      _ = 2 * (Real.pi : ℂ) * b * ((((n : ℂ) + 1 / 2) * Complex.I) * b⁻¹) := by
        field_simp
        <;> ring
  have hzIm : z.im = ((n : ℝ) + 1 / 2) * (b⁻¹).re := by
    rw [hzn]
    simp [Complex.mul_im, Complex.mul_re]
  have hbi : 0 < (b⁻¹).re := admissibleB_inv b hb
  rw [hzIm] at hz
  have hbounds := abs_lt.mp hz
  have hnneg : (n : ℝ) < 0 := by nlinarith
  have hnlow : (-1 : ℝ) < (n : ℝ) := by nlinarith
  have hnneg' : n < 0 := by exact_mod_cast hnneg
  have hnlow' : (-1 : ℤ) < n := by exact_mod_cast hnlow
  omega

lemma tendsto_difference_exp_real_atBot (b z : ℂ) (hb : AdmissibleB b) :
    Tendsto (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * b * (z + (t : ℂ)))) atBot (𝓝 0) := by
  have hc : 0 < 2 * Real.pi * b.re := mul_pos (mul_pos (by norm_num) Real.pi_pos) hb
  have heq (t : ℝ) :
      ‖Complex.exp (2 * (Real.pi : ℂ) * b * (z + (t : ℂ)))‖ =
        Real.exp ((2 * (Real.pi : ℂ) * b * z).re) * Real.exp ((2 * Real.pi * b.re) * t) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    <;> ring
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun t => (heq t).le))
  simpa using (Real.tendsto_exp_atBot.comp
    ((tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot).const_mul_atBot hc)).const_mul
      (Real.exp ((2 * (Real.pi : ℂ) * b * z).re))

lemma norm_exp_div_singleSinh_line_le (p z : ℂ) (h x : ℝ)
    (hp : 0 ≤ p.re) (hpx : 1 + |p.im * h| ≤ p.re * |x|) :
    ‖Complex.exp (-2 * Complex.I * z * linePoint h x) /
      Complex.sinh (p * linePoint h x)‖ ≤
      (4 * Real.exp (2 * z.re * h + |p.im * h|)) *
        Real.exp (-(p.re - 2 * |z.im|) * |x|) := by
  have he : ‖Complex.exp (-2 * Complex.I * z * linePoint h x)‖ ≤
      Real.exp (2 * |z.im| * |x| + 2 * z.re * h) := by
    simpa only [linePoint] using norm_exp_line_le z h x
  have hp' : ‖Complex.sinh (p * linePoint h x)‖⁻¹ ≤
      4 * Real.exp (-(p.re * |x| - |p.im * h|)) := by
    simpa only [linePoint] using norm_sinh_line_inv_le p h x hp hpx
  rw [norm_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (2 * |z.im| * |x| + 2 * z.re * h) *
        (4 * Real.exp (-(p.re * |x| - |p.im * h|))) := by gcongr
    _ = 4 * (Real.exp (2 * |z.im| * |x| + 2 * z.re * h) *
        Real.exp (-(p.re * |x| - |p.im * h|))) := by ring
    _ = 4 * Real.exp ((2 * |z.im| * |x| + 2 * z.re * h) +
        (-(p.re * |x| - |p.im * h|))) := by
      congr 1
      exact (Real.exp_add _ _).symm
    _ = 4 * Real.exp ((2 * z.re * h + |p.im * h|) +
        (-(p.re - 2 * |z.im|) * |x|)) := by congr 2; ring
    _ = _ := by rw [Real.exp_add]; ring

lemma norm_exp_div_singleSinh_line_le_uniform (p z : ℂ) (h x H : ℝ)
    (hp : 0 ≤ p.re) (hH : |h| ≤ H) (hpx : 1 + |p.im| * H ≤ p.re * |x|) :
    ‖Complex.exp (-2 * Complex.I * z * linePoint h x) /
      Complex.sinh (p * linePoint h x)‖ ≤
      (4 * Real.exp ((2 * |z.re| + |p.im|) * H)) *
        Real.exp (-(p.re - 2 * |z.im|) * |x|) := by
  have hph : |p.im * h| ≤ |p.im| * H := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hH (abs_nonneg _)
  have hzh : z.re * h ≤ |z.re| * H := by
    calc
      z.re * h ≤ |z.re * h| := le_abs_self _
      _ = |z.re| * |h| := abs_mul _ _
      _ ≤ |z.re| * H := mul_le_mul_of_nonneg_left hH (abs_nonneg _)
  calc
    _ ≤ (4 * Real.exp (2 * z.re * h + |p.im * h|)) *
        Real.exp (-(p.re - 2 * |z.im|) * |x|) :=
      norm_exp_div_singleSinh_line_le p z h x hp (by linarith)
    _ ≤ _ := by
      gcongr
      nlinarith

lemma singleSinh_verticalIntegral_tendsto_zero (c z : ℂ) (s a b : ℝ)
    (hc : 0 < c.re) (hz : 2 * |z.im| < c.re) :
    Tendsto (fun x : ℝ => ∫ y : ℝ in a..b,
      Complex.exp (-2 * Complex.I * z * linePoint (s + y) x) /
        Complex.sinh (c * linePoint (s + y) x)) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => ∫ y : ℝ in a..b,
      Complex.exp (-2 * Complex.I * z * linePoint (s + y) x) /
        Complex.sinh (c * linePoint (s + y) x)) atBot (𝓝 0) := by
  let H : ℝ := |s| + max |a| |b|
  let C : ℝ := 4 * Real.exp ((2 * |z.re| + |c.im|) * H)
  let δ : ℝ := c.re - 2 * |z.im|
  have hδ : 0 < δ := sub_pos.mpr hz
  have hH (y : ℝ) (hy : y ∈ Set.uIcc a b) : |s + y| ≤ H := by
    apply (abs_add_le s y).trans
    have hy' : |y| ≤ max |a| |b| := by
      rcases Set.mem_uIcc.mp hy with hy | hy
      · exact abs_le_max_abs_abs hy.1 hy.2
      · simpa only [max_comm] using abs_le_max_abs_abs hy.1 hy.2
    exact add_le_add le_rfl hy'
  have hlim {l : Filter ℝ} (habs : Tendsto (fun x : ℝ => |x|) l atTop) :
      Tendsto (fun x : ℝ => ∫ y : ℝ in a..b,
        Complex.exp (-2 * Complex.I * z * linePoint (s + y) x) /
          Complex.sinh (c * linePoint (s + y) x)) l (𝓝 0) := by
    apply Contour.tendsto_intervalIntegral_zero_of_uniform_bound
      (M := fun x => C * Real.exp (-δ * |x|))
    · filter_upwards [habs.eventually (eventually_ge_atTop
        ((1 + |c.im| * H) / c.re))] with x hx
      intro y hy
      apply norm_exp_div_singleSinh_line_le_uniform c z (s + y) x H hc.le (hH y hy)
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hx
    · simpa using (Real.tendsto_exp_atBot.comp
        (habs.const_mul_atTop_of_neg (neg_neg_of_pos hδ))).const_mul C
  exact ⟨hlim tendsto_abs_atTop_atTop, hlim tendsto_abs_atBot_atTop⟩

/-- The single pole at `iπb` contributes `-2π i b exp(2πbz)`. The finite rectangular correction is
proved in `FaddeevContour`. -/
lemma integral_singleSinh_line (b z : ℂ) (h : ℝ)
    (hb : AdmissibleB b) (hh : AdmissibleHeight b h)
    (hz : |z.im| < (b⁻¹).re / 2) :
    (∫ x : ℝ, Complex.exp (-2 * Complex.I * z * linePoint h x) /
      Complex.sinh (b⁻¹ * linePoint h x)) =
      -2 * (Real.pi : ℂ) * Complex.I * b * Complex.exp (2 * (Real.pi : ℂ) * b * z) /
        (1 + Complex.exp (2 * (Real.pi : ℂ) * b * z)) := by
  let f : ℂ → ℂ := fun w => Complex.exp (-2 * Complex.I * z * w) / Complex.sinh (b⁻¹ * w)
  let p : ℂ := Complex.I * (Real.pi : ℂ) * b
  let A : ℝ := Real.pi * b.re - h
  let E : ℂ := Complex.exp (2 * (Real.pi : ℂ) * b * z)
  have hb0 := admissibleB_ne_zero b hb
  have hbi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hzh : 2 * |z.im| < (b⁻¹).re := by linarith
  have hhπ : h < Real.pi * b.re := hh.2.trans_le
    (mul_le_mul_of_nonneg_left (min_le_left _ _) Real.pi_pos.le)
  have hA : 0 < A := sub_pos.mpr hhπ
  have hpim : p.im = Real.pi * b.re := by
    dsimp [p]; simp [Complex.mul_im, Complex.mul_re]
  have hshift := (inStrip_b_shifts_iff b z hb).mpr hz
  have hbase : Integrable (fun x : ℝ => f (linePoint h x)) :=
    singleSinh_line_integrable b z h hb hh hshift.1 hshift.2
  have hbottom (x : ℝ) :
      f (p + ((x : ℂ) + ((-A : ℝ) : ℂ) * Complex.I)) = f (linePoint h (x + p.re)) := by
    congr 1
    apply Complex.ext <;> simp [p, A, linePoint, Complex.mul_re, Complex.mul_im] <;> ring
  have htop (x : ℝ) : f (p + ((x : ℂ) + (h : ℂ) * Complex.I)) = -E * f (linePoint h x) := by
    have hpoint : p + ((x : ℂ) + (h : ℂ) * Complex.I) = linePoint h x + p := by
      dsimp [linePoint]; ring
    rw [hpoint]
    exact singleSinhKernel_period b z (linePoint h x) hb0
  have hbottomint : Integrable (fun x : ℝ =>
      f (p + ((x : ℂ) + ((-A : ℝ) : ℂ) * Complex.I))) :=
    (hbase.comp_add_right p.re).congr (Filter.Eventually.of_forall fun x => (hbottom x).symm)
  have htopint : Integrable (fun x : ℝ => f (p + ((x : ℂ) + (h : ℂ) * Complex.I))) :=
    (hbase.const_mul (-E)).congr (Filter.Eventually.of_forall fun x => (htop x).symm)
  have hbottomval :
      (∫ x : ℝ, f (p + ((x : ℂ) + ((-A : ℝ) : ℂ) * Complex.I))) =
        ∫ x : ℝ, f (linePoint h x) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hbottom)]
    exact integral_add_right_eq_self (fun x : ℝ => f (linePoint h x)) p.re
  have htopval :
      (∫ x : ℝ, f (p + ((x : ℂ) + (h : ℂ) * Complex.I))) =
        -E * ∫ x : ℝ, f (linePoint h x) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall htop), integral_const_mul]
  obtain ⟨g, hg, hfg⟩ := singleSinhKernel_principal_part b z hb
  have hrect : ∀ᶠ R : ℝ in atTop,
      (∫ x : ℝ in -R..R, f (p + ((x : ℂ) + ((-A : ℝ) : ℂ) * Complex.I))) -
      (∫ x : ℝ in -R..R, f (p + ((x : ℂ) + (h : ℂ) * Complex.I))) +
      Complex.I * (∫ y : ℝ in -A..h, f (p + ((R : ℂ) + (y : ℂ) * Complex.I))) -
      Complex.I * (∫ y : ℝ in -A..h, f (p + (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))) =
        2 * (Real.pi : ℂ) * Complex.I * (-b * E) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact Contour.integral_boundary_rect_simple_pole_of_strip
      (f := f) (g := g) (R := R) (A := A) (B := h)
      (lo := 0) (hi := 2 * Real.pi * b.re) p (-b * E)
      hR hA hh.1 (by rw [hpim]; dsimp [A]; linarith [hh.1])
      (by rw [hpim]; linarith) hg hfg
  have hpointSide (x y : ℝ) :
      p + ((x : ℂ) + (y : ℂ) * Complex.I) = linePoint (p.im + y) (p.re + x) := by
    apply Complex.ext <;> simp [linePoint] <;> ring
  have hsides := singleSinh_verticalIntegral_tendsto_zero b⁻¹ z p.im (-A) h hbi hzh
  have hrightCoord : Tendsto (fun R : ℝ => p.re + R) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_id
  have hleftCoord : Tendsto (fun R : ℝ => p.re + -R) atTop atBot :=
    tendsto_const_nhds.add_atBot tendsto_neg_atTop_atBot
  have hright : Tendsto (fun R : ℝ => ∫ y : ℝ in -A..h,
      f (p + ((R : ℂ) + (y : ℂ) * Complex.I))) atTop (𝓝 0) := by
    simpa only [f, hpointSide, Function.comp_def] using hsides.1.comp hrightCoord
  have hleft : Tendsto (fun R : ℝ => ∫ y : ℝ in -A..h,
      f (p + (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))) atTop (𝓝 0) := by
    simpa only [f, hpointSide, Function.comp_def] using hsides.2.comp hleftCoord
  have hbottomlim := intervalIntegral_tendsto_integral hbottomint tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have htoplim := intervalIntegral_tendsto_integral htopint tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hlim := ((hbottomlim.sub htoplim).add (hright.const_mul Complex.I)).sub
    (hleft.const_mul Complex.I)
  have heq := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (hrect.mono fun _ hR => hR.symm))
  simp only [mul_zero, add_zero, sub_zero, hbottomval, htopval] at heq
  apply (eq_div_iff (difference_factor_ne_zero b z hb hz)).mpr
  change (∫ x : ℝ, f (linePoint h x)) * (1 + E) = -2 * (Real.pi : ℂ) * Complex.I * b * E
  linear_combination heq

lemma phi_difference_b_of_singleSinh_integral (b : ℂ) (hb : AdmissibleB b)
    (hJ : ∀ ζ : ℂ, |ζ.im| < (b⁻¹).re / 2 →
      (∫ x : ℝ, Complex.exp (-2 * Complex.I * ζ * linePoint (canonicalHeight b) x) /
        Complex.sinh (b⁻¹ * linePoint (canonicalHeight b) x)) =
        -2 * (Real.pi : ℂ) * Complex.I * b * Complex.exp (2 * (Real.pi : ℂ) * b * ζ) /
          (1 + Complex.exp (2 * (Real.pi : ℂ) * b * ζ))) (z : ℂ)
    (hminus : InStrip b (z - Complex.I * b / 2))
    (hplus : InStrip b (z + Complex.I * b / 2)) :
    phi b (z - Complex.I * b / 2) = (1 + Complex.exp (2 * (Real.pi : ℂ) * b * z)) *
      phi b (z + Complex.I * b / 2) := by
  let F : ℂ → ℂ := fun ζ => Complex.exp (logPhi b (ζ - Complex.I * b / 2) -
      logPhi b (ζ + Complex.I * b / 2)) / (1 + Complex.exp (2 * (Real.pi : ℂ) * b * ζ))
  have hz : |z.im| < (b⁻¹).re / 2 := (inStrip_b_shifts_iff b z hb).mp ⟨hminus, hplus⟩
  have hF (ζ : ℂ) (hζ : |ζ.im| < (b⁻¹).re / 2) : HasDerivAt F 0 ζ := by
    have hζs := (inStrip_b_shifts_iff b ζ hb).mpr hζ
    have hfactor := difference_factor_ne_zero b ζ hb hζ
    have hD := hasDerivAt_logPhi_b_difference b ζ (canonicalHeight b) hb
      (canonicalHeight_admissible b hb) hζs.1 hζs.2
    rw [hJ ζ hζ] at hD
    have hE := (((hasDerivAt_id ζ).const_mul (2 * (Real.pi : ℂ) * b)).cexp).const_add 1
    have hquot := hD.cexp.div hE hfactor
    simp only [id_eq, mul_one] at hquot
    convert! hquot using 1
    generalize hce : Complex.exp (2 * (Real.pi : ℂ) * b * ζ) = E at hfactor ⊢
    generalize hpe : Complex.exp (logPhi b (ζ - Complex.I * b / 2) -
      logPhi b (ζ + Complex.I * b / 2)) = P
    field_simp [hfactor]
    ring_nf
    simp [Complex.I_sq]
  have hreal (t : ℝ) : HasDerivAt (fun t : ℝ => F (z + (t : ℂ))) 0 t := by
    have hzt : |(z + (t : ℂ)).im| < (b⁻¹).re / 2 := by simpa using hz
    have hc := (hF (z + (t : ℂ)) hzt).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_add z)
    convert! hc.comp_ofReal using 1 <;> simp [add_comm]
  have hconst (t : ℝ) : F (z + (t : ℂ)) = F z := by
    simpa using is_const_of_deriv_eq_zero (fun t => (hreal t).differentiableAt)
      (fun t => (hreal t).deriv) t 0
  have hLm : Tendsto (fun t : ℝ => logPhi b (z + (t : ℂ) - Complex.I * b / 2)) atBot (𝓝 0) := by
    convert! tendsto_logPhi_real_atBot b (z - Complex.I * b / 2) hb using 1
    ext t
    congr 1
    ring
  have hLp : Tendsto (fun t : ℝ => logPhi b (z + (t : ℂ) + Complex.I * b / 2)) atBot (𝓝 0) := by
    convert! tendsto_logPhi_real_atBot b (z + Complex.I * b / 2) hb using 1
    ext t
    congr 1
    ring
  have hFlim : Tendsto (fun t : ℝ => F (z + (t : ℂ))) atBot (𝓝 1) := by
    convert! (hLm.sub hLp).cexp.div
        (tendsto_const_nhds.add (tendsto_difference_exp_real_atBot b z hb))
        (by norm_num : (1 : ℂ) + 0 ≠ 0) using 1 <;> simp [F]
  have hFone : F z = 1 := by
    exact (tendsto_nhds_unique hFlim (tendsto_const_nhds.congr (fun t => (hconst t).symm))).symm
  have hratio := (div_eq_one_iff_eq (difference_factor_ne_zero b z hb hz)).mp hFone
  change Complex.exp (logPhi b (z - Complex.I * b / 2) - logPhi b (z + Complex.I * b / 2)) = _ at hratio
  rw [Complex.exp_sub] at hratio
  exact (div_eq_iff (Complex.exp_ne_zero _)).mp hratio

/-- Standard b-difference equation, restricted to the overlap of strips. FKV (hep-th/0006156), (17);
Andersen--Kashaev (1109.6295), App. A (48). Consistent with the unnumbered difference identities
following [RW26, (9)], after the stated change of variables. -/
theorem phi_difference_b (b z : ℂ) (hb : AdmissibleB b)
    (hminus : InStrip b (z - Complex.I * b / 2))
    (hplus : InStrip b (z + Complex.I * b / 2)) :
    phi b (z - Complex.I * b / 2) =
      (1 + Complex.exp (2 * (Real.pi : ℂ) * b * z)) *
        phi b (z + Complex.I * b / 2) := by
  exact phi_difference_b_of_singleSinh_integral b hb
    (fun ζ hζ => integral_singleSinh_line b ζ (canonicalHeight b) hb
      (canonicalHeight_admissible b hb) hζ) z hminus hplus

/-- The dual difference equation has `b⁻¹` in both the shift and exponential. -/
theorem phi_difference_inv_b (b z : ℂ) (hb : AdmissibleB b)
    (hminus : InStrip b (z - Complex.I * b⁻¹ / 2))
    (hplus : InStrip b (z + Complex.I * b⁻¹ / 2)) :
    phi b (z - Complex.I * b⁻¹ / 2) =
      (1 + Complex.exp (2 * (Real.pi : ℂ) * b⁻¹ * z)) *
        phi b (z + Complex.I * b⁻¹ / 2) := by
  have hbi := admissibleB_inv b hb
  have hm : InStrip b⁻¹ (z - Complex.I * b⁻¹ / 2) := by
    simpa only [InStrip, stripWidth, inv_inv, add_comm] using hminus
  have hp : InStrip b⁻¹ (z + Complex.I * b⁻¹ / 2) := by
    simpa only [InStrip, stripWidth, inv_inv, add_comm] using hplus
  have h := phi_difference_b b⁻¹ z hbi hm hp
  rw [← phi_self_dual b _ hb hminus, ← phi_self_dual b _ hb hplus] at h
  exact h

lemma kernel_neg_argument_add (b z w : ℂ) :
    kernel b z w + kernel b (-z) w = inversionRegular b z w / w ^ 3 := by
  unfold kernel inversionRegular inversionDenom
  rw [← add_div]
  have hnum : Complex.exp (-2 * Complex.I * z * w) +
      Complex.exp (-2 * Complex.I * -z * w) =
        2 * Complex.cosh ((-2 * Complex.I * z) * w) := by
    rw [show -2 * Complex.I * -z * w = -((-2 * Complex.I * z) * w) by ring,
      Complex.cosh]
    ring
  rw [hnum, ← sinhSlope_mul b w, ← sinhSlope_mul b⁻¹ w]
  rw [div_div]
  have hden : 4 * (w * sinhSlope b w) * (w * sinhSlope b⁻¹ w) * w =
      2 * (2 * sinhSlope b w * sinhSlope b⁻¹ w * w ^ 3) := by ring
  rw [hden]
  exact mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0)

lemma kernel_inversion_principalPart (b z w : ℂ) (hb : b ≠ 0) (hw : w ≠ 0) :
    kernel b z w + kernel b (-z) w =
      1 / (2 * w ^ 3) - (z ^ 2 + (b ^ 2 + (b⁻¹) ^ 2) / 12) / w +
        inversionRemainder b z w := by
  rw [kernel_neg_argument_add, inversionRegular_taylor b z w hb]
  field_simp

lemma arc_invCube_integrand (r θ : ℝ) (hr : r ≠ 0) :
    1 / (2 * arcPoint r θ ^ 3) * (Complex.I * arcPoint r θ) =
      Complex.I / (2 * (r : ℂ) ^ 2) *
        Complex.exp ((-2 * Complex.I) * (θ : ℂ)) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hexp : Complex.exp ((-2 * Complex.I) * (θ : ℂ)) =
      (Complex.exp (Complex.I * (θ : ℂ)) ^ 2)⁻¹ := by
    rw [show (-2 * Complex.I) * (θ : ℂ) =
      -(2 * (Complex.I * (θ : ℂ))) by ring, Complex.exp_neg]
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul]
  rw [hexp]
  unfold arcPoint
  field_simp

lemma integral_arc_invCube (r : ℝ) (hr : r ≠ 0) :
    (∫ θ : ℝ in Real.pi..0,
      1 / (2 * arcPoint r θ ^ 3) * (Complex.I * arcPoint r θ)) = 0 := by
  simp_rw [arc_invCube_integrand r _ hr]
  rw [intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (by simp : (-2 * Complex.I : ℂ) ≠ 0)]
  have hexp : Complex.exp ((-2 * Complex.I) * (Real.pi : ℂ)) = 1 := by
    rw [show (-2 * Complex.I) * (Real.pi : ℂ) =
      ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by norm_num; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-1)
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, hexp, sub_self, zero_div, mul_zero]

lemma integral_arc_inv (r : ℝ) (hr : 0 < r) :
    (∫ θ : ℝ in Real.pi..0,
      (arcPoint r θ)⁻¹ * (Complex.I * arcPoint r θ)) = -Complex.I * (Real.pi : ℂ) := by
  have heq (θ : ℝ) :
      (arcPoint r θ)⁻¹ * (Complex.I * arcPoint r θ) = Complex.I := by
    field_simp [arcPoint_ne_zero r θ hr]
  simp_rw [heq]
  simp [mul_comm]

lemma tendsto_small_arc_of_continuousAt {f : ℂ → ℂ} (hf : ContinuousAt f 0) :
    Tendsto (fun r : ℝ => ∫ θ : ℝ in Real.pi..0,
      f (arcPoint r θ) * (Complex.I * arcPoint r θ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have hB : ∀ᶠ w in 𝓝 (0 : ℂ), ‖f w‖ < ‖f 0‖ + 1 :=
    hf.norm.eventually_lt continuousAt_const (by linarith)
  obtain ⟨δ, hδ, hBδ⟩ := Metric.eventually_nhds_iff.mp hB
  apply Contour.tendsto_intervalIntegral_zero_of_uniform_bound
    (M := fun r : ℝ => (‖f 0‖ + 1) * r)
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r hr hrδ
    intro θ _
    have hr₀ : 0 < r := hr
    have hrδ₀ : r < δ := hrδ
    have hdist : dist (arcPoint r θ) 0 < δ := by
      simpa only [dist_zero_right, norm_arcPoint, abs_of_pos hr₀] using hrδ₀
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_arcPoint, abs_of_pos hr₀]
    exact mul_le_mul_of_nonneg_right (hBδ hdist).le hr₀.le
  · have ht : Tendsto (fun r : ℝ => r) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := nhdsWithin_le_nhds
    simpa using ht.const_mul (‖f 0‖ + 1)

lemma tendsto_inversionRemainder_arc (b z : ℂ) (hb : b ≠ 0) :
    Tendsto (fun r : ℝ => ∫ θ : ℝ in Real.pi..0,
      inversionRemainder b z (arcPoint r θ) * (Complex.I * arcPoint r θ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
  tendsto_small_arc_of_continuousAt (analyticAt_inversionRemainder b z hb).continuousAt

lemma arcKernel_add_principalPart (b z : ℂ) (r θ : ℝ)
    (hb : b ≠ 0) (hr : 0 < r) :
    arcKernel b z r θ + arcKernel b (-z) r θ =
      1 / (2 * arcPoint r θ ^ 3) * (Complex.I * arcPoint r θ) -
        (z ^ 2 + (b ^ 2 + (b⁻¹) ^ 2) / 12) *
          ((arcPoint r θ)⁻¹ * (Complex.I * arcPoint r θ)) +
      inversionRemainder b z (arcPoint r θ) * (Complex.I * arcPoint r θ) := by
  unfold arcKernel
  rw [← add_mul, kernel_inversion_principalPart b z (arcPoint r θ) hb
    (arcPoint_ne_zero r θ hr)]
  ring

lemma integral_arcKernel_add (b z : ℂ) (r : ℝ)
    (hb : AdmissibleB b) (hr : AdmissibleHeight b r) :
    (∫ θ : ℝ in Real.pi..0, arcKernel b z r θ) +
      (∫ θ : ℝ in Real.pi..0, arcKernel b (-z) r θ) =
        Complex.I * (Real.pi : ℂ) * (z ^ 2 + (b ^ 2 + (b⁻¹) ^ 2) / 12) +
        (∫ θ : ℝ in Real.pi..0,
          inversionRemainder b z (arcPoint r θ) * (Complex.I * arcPoint r θ)) := by
  let T : ℝ → ℂ := fun θ => 1 / (2 * arcPoint r θ ^ 3) * (Complex.I * arcPoint r θ)
  let Q : ℝ → ℂ := fun θ => (arcPoint r θ)⁻¹ * (Complex.I * arcPoint r θ)
  let R : ℝ → ℂ := fun θ => inversionRemainder b z (arcPoint r θ) * (Complex.I * arcPoint r θ)
  let C : ℂ := z ^ 2 + (b ^ 2 + (b⁻¹) ^ 2) / 12
  have hT : IntervalIntegrable T volume Real.pi 0 := by
    have heq : T = fun θ : ℝ => Complex.I / (2 * (r : ℂ) ^ 2) *
        Complex.exp ((-2 * Complex.I) * (θ : ℂ)) :=
      funext (fun θ => arc_invCube_integrand r θ (ne_of_gt hr.1))
    rw [heq]
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hQ : IntervalIntegrable Q volume Real.pi 0 := by
    have heq : Q = fun _ => Complex.I := by
      funext θ
      dsimp [Q]
      field_simp [arcPoint_ne_zero r θ hr.1]
    rw [heq]
    exact intervalIntegrable_const
  have hK := (intervalIntegrable_arcKernel b z r hb hr).add
    (intervalIntegrable_arcKernel b (-z) r hb hr)
  have hR : IntervalIntegrable R volume Real.pi 0 := by
    apply IntervalIntegrable.congr (g := R) _ ((hK.sub hT).add (hQ.const_mul C))
    intro θ _
    dsimp only [T, Q, R, C]
    rw [arcKernel_add_principalPart b z r θ (admissibleB_ne_zero b hb) hr.1]
    ring
  rw [← intervalIntegral.integral_add (intervalIntegrable_arcKernel b z r hb hr)
    (intervalIntegrable_arcKernel b (-z) r hb hr)]
  have heq : (fun θ => arcKernel b z r θ + arcKernel b (-z) r θ) =
      fun θ => (T θ - C * Q θ) + R θ := by
    funext θ
    exact arcKernel_add_principalPart b z r θ (admissibleB_ne_zero b hb) hr.1
  rw [heq, intervalIntegral.integral_add (hT.sub (hQ.const_mul C)) hR,
    intervalIntegral.integral_sub hT (hQ.const_mul C), intervalIntegral.integral_const_mul]
  change (∫ θ : ℝ in Real.pi..0, T θ) - C * (∫ θ : ℝ in Real.pi..0, Q θ) + _ = _
  rw [show (∫ θ : ℝ in Real.pi..0, T θ) = 0 from integral_arc_invCube r (ne_of_gt hr.1),
    show (∫ θ : ℝ in Real.pi..0, Q θ) = -Complex.I * (Real.pi : ℂ) from
      integral_arc_inv r hr.1]
  dsimp only [C, R]
  ring

lemma tendsto_arcKernel_add (b z : ℂ) (hb : AdmissibleB b) :
    Tendsto (fun r : ℝ =>
      (∫ θ : ℝ in Real.pi..0, arcKernel b z r θ) +
        (∫ θ : ℝ in Real.pi..0, arcKernel b (-z) r θ))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (Complex.I * (Real.pi : ℂ) * (z ^ 2 + (b ^ 2 + (b⁻¹) ^ 2) / 12))) := by
  have hp : 0 < poleHeight b := mul_pos Real.pi_pos (lt_min hb (admissibleB_inv b hb))
  have hsmall : ∀ᶠ r in nhdsWithin 0 (Ioi 0), AdmissibleHeight b r := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hp)] with r hr hrp
    exact ⟨hr, hrp⟩
  have ht := (tendsto_inversionRemainder_arc b z (admissibleB_ne_zero b hb)).const_add
      (Complex.I * (Real.pi : ℂ) * (z ^ 2 + (b ^ 2 + (b⁻¹) ^ 2) / 12))
  simp only [add_zero] at ht
  exact ht.congr' (hsmall.mono fun r hr => (integral_arcKernel_add b z r hb hr).symm)

lemma kernel_reflection (b z w : ℂ) : kernel b z (-w) = -kernel b (-z) w := by
  unfold kernel
  have hnum : -2 * Complex.I * z * -w = -2 * Complex.I * -z * w := by ring
  rw [hnum]
  simp only [mul_neg, Complex.sinh_neg, neg_mul, neg_neg, div_neg]

lemma kernel_left_tail_reflection (b z : ℂ) (r : ℝ) :
    (∫ x : ℝ in Iic (-r), kernel b z (x : ℂ)) =
      -(∫ x : ℝ in Ici r, kernel b (-z) (x : ℂ)) := by
  have h := integral_comp_neg_Iic (-r) (fun x : ℝ => kernel b z (-((x : ℂ))))
  simp only [Complex.ofReal_neg, neg_neg, kernel_reflection, integral_neg] at h
  simpa only [← integral_Ici_eq_integral_Ioi] using h

lemma detourLog_add_neg (b z : ℂ) (r : ℝ) :
    detourLog b z r + detourLog b (-z) r =
      (∫ θ : ℝ in Real.pi..0, arcKernel b z r θ) +
        (∫ θ : ℝ in Real.pi..0, arcKernel b (-z) r θ) := by
  unfold detourLog
  rw [kernel_left_tail_reflection b z r, kernel_left_tail_reflection b (-z) r, neg_neg]
  ring

lemma logPhi_add_neg (b z : ℂ) (hb : AdmissibleB b) (hz : InStrip b z) :
    logPhi b z + logPhi b (-z) =
      Complex.I * (Real.pi : ℂ) * z ^ 2 +
        Complex.I * (Real.pi : ℂ) * (b ^ 2 + (b⁻¹) ^ 2) / 12 := by
  have hzn : InStrip b (-z) := by simpa [InStrip] using hz
  have ht := (tendsto_detourLog b z hb hz).add (tendsto_detourLog b (-z) hb hzn)
  have ha := tendsto_arcKernel_add b z hb
  have heq := tendsto_nhds_unique ht
    (ha.congr' (Eventually.of_forall fun r => (detourLog_add_neg b z r).symm))
  convert heq using 1 <;> ring

/-- In this normalization the constant is `(b² + b⁻²)/12`, not `/24`. The latter is the constant in
the chosen integral logarithm `logPhi b 0`. This does not refer to the principal branch of
`Complex.log`. FKV (16), Andersen--Kashaev App. A (43), (47). -/
theorem phi_inversion (b z : ℂ) (hb : AdmissibleB b) (hz : InStrip b z) :
    phi b z * phi b (-z) =
      Complex.exp (Complex.I * (Real.pi : ℂ) * z ^ 2 +
        Complex.I * (Real.pi : ℂ) * (b ^ 2 + (b⁻¹) ^ 2) / 12) := by
  unfold phi
  rw [← Complex.exp_add, logPhi_add_neg b z hb hz]

end SICLean.L4
