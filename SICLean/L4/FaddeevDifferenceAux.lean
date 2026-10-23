import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The single-sinh kernel in the difference equation

The only pole between heights zero and `2π Re b` is `iπb`. Divided differences give its principal
part and a holomorphic remainder; the contour computation can therefore use a rectangle with a
small-circle correction rather than a general residue theorem.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4

lemma singleSinhKernel_period (b z w : ℂ) (hb : b ≠ 0) :
    Complex.exp (-2 * Complex.I * z * (w + Complex.I * (Real.pi : ℂ) * b)) /
        Complex.sinh (b⁻¹ * (w + Complex.I * (Real.pi : ℂ) * b)) =
      -Complex.exp (2 * (Real.pi : ℂ) * b * z) *
        (Complex.exp (-2 * Complex.I * z * w) / Complex.sinh (b⁻¹ * w)) := by
  have hs : b⁻¹ * (w + Complex.I * (Real.pi : ℂ) * b) =
      b⁻¹ * w + (Real.pi : ℂ) * Complex.I := by
    field_simp
    <;> ring
  have he : -2 * Complex.I * z * (w + Complex.I * (Real.pi : ℂ) * b) =
      2 * (Real.pi : ℂ) * b * z + -2 * Complex.I * z * w := by
    ring_nf
    simp [Complex.I_sq]
    <;> ring
  rw [hs, he, Complex.sinh_add, Complex.sinh_mul_I,
    Complex.cosh_mul_I, Complex.sin_pi, Complex.cos_pi]
  simp only [zero_mul, mul_zero, add_zero, mul_neg_one, Complex.exp_add, div_neg]
  ring

lemma singleSinh_denominator_at_pole (b : ℂ) (hb : b ≠ 0) :
    Complex.sinh (b⁻¹ * (Complex.I * (Real.pi : ℂ) * b)) = 0 := by
  have hs : b⁻¹ * (Complex.I * (Real.pi : ℂ) * b) =
      (Real.pi : ℂ) * Complex.I := by field_simp
  simp [hs, Complex.sinh_mul_I]

lemma hasDerivAt_singleSinh_denominator_at_pole (b : ℂ) (hb : b ≠ 0) :
    HasDerivAt (fun w : ℂ => Complex.sinh (b⁻¹ * w))
      (-b⁻¹) (Complex.I * (Real.pi : ℂ) * b) := by
  have hs : b⁻¹ * (Complex.I * (Real.pi : ℂ) * b) =
      (Real.pi : ℂ) * Complex.I := by field_simp
  convert! ((hasDerivAt_id (Complex.I * (Real.pi : ℂ) * b)).const_mul b⁻¹).csinh using 1
  simp [hs, Complex.cosh_mul_I]

lemma singleSinh_numerator_at_pole (b z : ℂ) :
    Complex.exp (-2 * Complex.I * z * (Complex.I * (Real.pi : ℂ) * b)) =
      Complex.exp (2 * (Real.pi : ℂ) * b * z) := by
  congr 1
  ring_nf
  simp [Complex.I_sq]
  <;> ring

lemma singleSinhKernel_residue_limit (b z : ℂ) (hb : b ≠ 0) :
    Tendsto (fun w : ℂ =>
      (w - Complex.I * (Real.pi : ℂ) * b) *
        (Complex.exp (-2 * Complex.I * z * w) / Complex.sinh (b⁻¹ * w)))
      (𝓝[≠] (Complex.I * (Real.pi : ℂ) * b))
      (𝓝 (-b * Complex.exp (2 * (Real.pi : ℂ) * b * z))) := by
  have hd := (hasDerivAt_singleSinh_denominator_at_pole b hb).tendsto_slope
  have hn : Tendsto (fun w : ℂ => Complex.exp (-2 * Complex.I * z * w))
      (𝓝[≠] (Complex.I * (Real.pi : ℂ) * b))
      (𝓝 (Complex.exp (2 * (Real.pi : ℂ) * b * z))) := by
    rw [← singleSinh_numerator_at_pole b z]
    exact (by fun_prop : Continuous (fun w : ℂ =>
      Complex.exp (-2 * Complex.I * z * w))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hn.mul (hd.inv₀ (neg_ne_zero.mpr (inv_ne_zero hb)))
  convert! ht using 1
  · funext w
    rw [slope_def_field, singleSinh_denominator_at_pole b hb, sub_zero]
    by_cases hw : w = Complex.I * (Real.pi : ℂ) * b
    · simp [hw]
    · field_simp
  · simp
    <;> ring

lemma singleSinh_no_other_pole (b w : ℂ) (hb : 0 < b.re)
    (hw₀ : 0 < w.im) (hw₂ : w.im < 2 * Real.pi * b.re)
    (hwp : w ≠ Complex.I * (Real.pi : ℂ) * b) :
    Complex.sinh (b⁻¹ * w) ≠ 0 := by
  intro hs
  have hb0 : b ≠ 0 := by intro hz; simpa [hz] using hb
  have hs' : Complex.sin ((b⁻¹ * w) * Complex.I) = 0 := by
    rw [Complex.sin_mul_I, hs, zero_mul]
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp hs'
  have hz : b⁻¹ * w = -(n : ℂ) * (Real.pi : ℂ) * Complex.I := by
    calc
      b⁻¹ * w = ((b⁻¹ * w) * Complex.I) * (-Complex.I) := by simp [mul_assoc]
      _ = (n : ℂ) * (Real.pi : ℂ) * (-Complex.I) :=
        congrArg (fun z : ℂ => z * (-Complex.I)) hn
      _ = -(n : ℂ) * (Real.pi : ℂ) * Complex.I := by ring
  have hw : w = b * (-(n : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    calc
      w = b * (b⁻¹ * w) := by simp [hb0]
      _ = b * (-(n : ℂ) * (Real.pi : ℂ) * Complex.I) := by rw [hz]
  have him := congrArg Complex.im hw
  simp [Complex.mul_im, Complex.mul_re] at him
  have hp : 0 < Real.pi * b.re := mul_pos Real.pi_pos hb
  have hnp : (n : ℝ) < 0 := by nlinarith
  have hnl : (-2 : ℝ) < (n : ℝ) := by nlinarith
  have hnp' : n < 0 := by exact_mod_cast hnp
  have hnl' : (-2 : ℤ) < n := by exact_mod_cast hnl
  have hn1 : n = -1 := by omega
  apply hwp
  simpa [hn1, mul_comm, mul_left_comm, mul_assoc] using hw

lemma singleSinhKernel_principal_part (b z : ℂ) (hb : 0 < b.re) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g {w : ℂ | 0 < w.im ∧ w.im < 2 * Real.pi * b.re} ∧
      ∀ w : ℂ, 0 < w.im → w.im < 2 * Real.pi * b.re →
        w ≠ Complex.I * (Real.pi : ℂ) * b →
        Complex.exp (-2 * Complex.I * z * w) / Complex.sinh (b⁻¹ * w) =
          (-b * Complex.exp (2 * (Real.pi : ℂ) * b * z)) /
            (w - Complex.I * (Real.pi : ℂ) * b) + g w := by
  let p : ℂ := Complex.I * (Real.pi : ℂ) * b
  let U : Set ℂ := {w | 0 < w.im ∧ w.im < 2 * Real.pi * b.re}
  let d : ℂ → ℂ := fun w => Complex.sinh (b⁻¹ * w)
  let q : ℂ → ℂ := dslope d p
  let A : ℂ → ℂ := fun w => Complex.exp (-2 * Complex.I * z * w) / q w
  have hb0 : b ≠ 0 := by intro hzero; simpa [hzero] using hb
  have hd : Differentiable ℂ d := by dsimp [d]; fun_prop
  have hq : Differentiable ℂ q := by
    apply differentiableOn_univ.mp
    exact (Complex.differentiableOn_dslope (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 p)).2
      hd.differentiableOn
  have hqp : q p = -b⁻¹ := by
    dsimp [q]
    rw [dslope_same]
    exact (hasDerivAt_singleSinh_denominator_at_pole b hb0).deriv
  have hd0 : d p = 0 := singleSinh_denominator_at_pole b hb0
  have hfactor (w : ℂ) : (w - p) * q w = d w := by
    simpa only [q, smul_eq_mul, hd0, sub_zero] using sub_smul_dslope d p w
  have hqne : ∀ w ∈ U, q w ≠ 0 := by
    intro w hw
    by_cases hwp : w = p
    · simpa [hwp, hqp] using (neg_ne_zero.mpr (inv_ne_zero hb0))
    · intro hzero
      have hdne : d w ≠ 0 := singleSinh_no_other_pole b w hb hw.1 hw.2 hwp
      apply hdne
      rw [← hfactor w, hzero, mul_zero]
  have hA : DifferentiableOn ℂ A U := by
    apply DifferentiableOn.div
    · fun_prop
    · exact hq.differentiableOn
    · exact hqne
  have hpIm : p.im = Real.pi * b.re := by
    dsimp [p]
    simp [Complex.mul_im, Complex.mul_re]
  have hpU : p ∈ U := by
    change 0 < p.im ∧ p.im < 2 * Real.pi * b.re
    rw [hpIm]
    constructor <;> nlinarith [mul_pos Real.pi_pos hb]
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hAp : A p = -b * Complex.exp (2 * (Real.pi : ℂ) * b * z) := by
    dsimp [A]
    rw [hqp, singleSinh_numerator_at_pole]
    simp [div_eq_mul_inv]
    <;> ring
  refine ⟨dslope A p, (Complex.differentiableOn_dslope (hU.mem_nhds hpU)).2 hA, ?_⟩
  intro w hw0 hw2 hwp
  change w ≠ p at hwp
  change Complex.exp (-2 * Complex.I * z * w) / Complex.sinh (b⁻¹ * w) =
    (-b * Complex.exp (2 * (Real.pi : ℂ) * b * z)) / (w - p) + dslope A p w
  rw [dslope_of_ne A hwp, slope_def_field, hAp]
  have hqw := hqne w ⟨hw0, hw2⟩
  have hwp0 : w - p ≠ 0 := sub_ne_zero.mpr hwp
  have hdw : Complex.sinh (b⁻¹ * w) = (w - p) * q w := (hfactor w).symm
  rw [hdw]
  dsimp only [A]
  field_simp [hqw, hwp0]
  <;> ring

end SICLean.L4
