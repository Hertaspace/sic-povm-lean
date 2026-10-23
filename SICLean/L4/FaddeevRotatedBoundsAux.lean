import SICLean.L4.FaddeevRotatedKernel
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

/-!
Auxiliary estimates for `FaddeevRotatedBounds`.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4.Sector

lemma re_mul_rotatedPoint (b : ℂ) (θ v t : ℝ) :
    (b * rotatedPoint θ v t).re = rotatedRe b θ * t - (b * rotation θ).im * v := by
  rw [rotatedPoint, ← mul_assoc]
  simp [rotatedRe, linePoint, Complex.mul_re, Complex.mul_im]

lemma re_mul_rotatedPoint_inv (b : ℂ) (θ v t : ℝ) :
    (b⁻¹ * rotatedPoint θ v t).re =
      rotatedInvRe b θ * t - (b⁻¹ * rotation θ).im * v := by
  rw [rotatedPoint, ← mul_assoc]
  simp [rotatedInvRe, linePoint, Complex.mul_re, Complex.mul_im]

lemma sinh_norm_lower_of_nonneg (z : ℂ) (hz : 1 ≤ z.re) :
    Real.exp z.re / 4 ≤ ‖Complex.sinh z‖ := by
  have hlow : Real.exp z.re / 2 - Real.exp (-z.re) / 2 ≤ ‖Complex.sinh z‖ := by
    have h2 : (2 : ℂ) * Complex.sinh z = Complex.exp z - Complex.exp (-z) :=
      Complex.two_sinh z
    have hsub : ‖Complex.exp z‖ - ‖Complex.exp (-z)‖ ≤
        ‖Complex.exp z - Complex.exp (-z)‖ := norm_sub_norm_le _ _
    rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at hsub
    have h2n : ‖(2 : ℂ) * Complex.sinh z‖ = 2 * ‖Complex.sinh z‖ := by
      rw [norm_mul]
      norm_num
    rw [← h2, h2n] at hsub
    linarith
  have hgt : 2 < Real.exp z.re :=
    lt_of_lt_of_le Real.exp_one_gt_two (Real.exp_le_exp.mpr hz)
  have hprod : Real.exp z.re * Real.exp (-z.re) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hneg : 2 * Real.exp (-z.re) ≤ Real.exp z.re := by
    nlinarith [Real.exp_pos z.re, Real.exp_pos (-z.re)]
  linarith

lemma exp_abs_re_div_four_le_norm_sinh (z : ℂ) (hz : 1 ≤ |z.re|) :
    Real.exp |z.re| / 4 ≤ ‖Complex.sinh z‖ := by
  rcases le_or_gt 0 z.re with h | h
  · have hzr : |z.re| = z.re := abs_of_nonneg h
    simpa [hzr] using sinh_norm_lower_of_nonneg z (by simpa [abs_of_nonneg h] using hz)
  · have hzr : |z.re| = -z.re := abs_of_neg h
    have h' : Real.exp (-z.re) / 4 ≤ ‖Complex.sinh (-z)‖ := by
      have h2 : Real.exp ((-z : ℂ).re) / 4 ≤ ‖Complex.sinh (-z)‖ :=
        sinh_norm_lower_of_nonneg (-z) (by simp only [Complex.neg_re]; linarith)
      simpa using h2
    rw [Complex.sinh_neg, norm_neg] at h'
    simpa [hzr] using h'

lemma inv_norm_sinh_le (z : ℂ) (hz : 1 ≤ |z.re|) :
    (‖Complex.sinh z‖)⁻¹ ≤ 4 * Real.exp (-|z.re|) := by
  have hpos : 0 < Real.exp |z.re| / 4 := div_pos (Real.exp_pos _) (by norm_num)
  have hle := exp_abs_re_div_four_le_norm_sinh z hz
  have hs : 0 < ‖Complex.sinh z‖ := lt_of_lt_of_le hpos hle
  calc
    (‖Complex.sinh z‖)⁻¹ ≤ (Real.exp |z.re| / 4)⁻¹ :=
      (inv_le_inv₀ hs hpos).mpr hle
    _ = 4 * Real.exp (-|z.re|) := by
      rw [inv_div, Real.exp_neg]
      ring

lemma norm_amplitude_eq (b : ℂ) (θ v t : ℝ) :
    ‖amplitude b θ v t‖ =
      (4 * ‖Complex.sinh (b * rotatedPoint θ v t)‖ *
        ‖Complex.sinh (b⁻¹ * rotatedPoint θ v t)‖ * ‖linePoint v t‖)⁻¹ := by
  rw [amplitude, rotatedDenominator, norm_inv]
  congr 1
  rw [norm_mul, norm_mul, norm_mul]
  norm_num

lemma rotated_re_abs_lower (b : ℂ) (θ v t lam M : ℝ)
    (hv : 0 ≤ v) (hlam : 0 ≤ lam)
    (hA : lam ≤ rotatedRe b θ) (hB : lam ≤ rotatedInvRe b θ)
    (hM : |(b * rotation θ).im| ≤ M ∧ |(b⁻¹ * rotation θ).im| ≤ M) :
    lam * |t| - v * M ≤ |(b * rotatedPoint θ v t).re| ∧
      lam * |t| - v * M ≤ |(b⁻¹ * rotatedPoint θ v t).re| := by
  constructor
  · rw [re_mul_rotatedPoint]
    have ht : lam * |t| ≤ |rotatedRe b θ * t| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (le_trans hA (le_abs_self _)) (abs_nonneg t)
    have hvt : |(b * rotation θ).im * v| ≤ M * v := by
      rw [abs_mul, abs_of_nonneg hv]
      exact mul_le_mul_of_nonneg_right hM.1 hv
    calc
      lam * |t| - v * M ≤ |rotatedRe b θ * t| - |(b * rotation θ).im * v| := by
        linarith
      _ ≤ |rotatedRe b θ * t - (b * rotation θ).im * v| :=
        abs_sub_abs_le_abs_sub _ _
  · rw [re_mul_rotatedPoint_inv]
    have ht : lam * |t| ≤ |rotatedInvRe b θ * t| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (le_trans hB (le_abs_self _)) (abs_nonneg t)
    have hvt : |(b⁻¹ * rotation θ).im * v| ≤ M * v := by
      rw [abs_mul, abs_of_nonneg hv]
      exact mul_le_mul_of_nonneg_right hM.2 hv
    calc
      lam * |t| - v * M ≤ |rotatedInvRe b θ * t| - |(b⁻¹ * rotation θ).im * v| := by
        linarith
      _ ≤ |rotatedInvRe b θ * t - (b⁻¹ * rotation θ).im * v| :=
        abs_sub_abs_le_abs_sub _ _

lemma inv_sq_exp_target (lam v M t : ℝ) (hv : 0 < v) :
    (v / 4 * Real.exp (lam * |t| - v * M) ^ 2)⁻¹ =
      (4 / v) * Real.exp (2 * v * M) * Real.exp (-2 * lam * |t|) := by
  set a := lam * |t| - v * M with ha
  have hs : Real.exp a ^ 2 = Real.exp (2 * a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have key : -(2 * a) = 2 * v * M + -2 * lam * |t| := by
    rw [ha]
    ring
  calc
    (v / 4 * Real.exp a ^ 2)⁻¹ = (v / 4 * Real.exp (2 * a))⁻¹ := by rw [hs]
    _ = (4 / v) * (Real.exp (2 * a))⁻¹ := by
      field_simp [hv.ne']
    _ = (4 / v) * Real.exp (-(2 * a)) := by rw [Real.exp_neg]
    _ = (4 / v) * Real.exp (2 * v * M + -2 * lam * |t|) := by rw [key]
    _ = (4 / v) * Real.exp (2 * v * M) * Real.exp (-2 * lam * |t|) := by
      rw [Real.exp_add]
      ring

lemma amplitude_tail_bound_aux (b : ℂ) (θ v t lam M : ℝ)
    (hv : 0 < v) (hlam : 0 < lam)
    (hA : lam ≤ rotatedRe b θ) (hB : lam ≤ rotatedInvRe b θ)
    (hM : |(b * rotation θ).im| ≤ M ∧ |(b⁻¹ * rotation θ).im| ≤ M)
    (ht : 1 + v * M ≤ lam * |t|) :
    ‖amplitude b θ v t‖ ≤
      (4 / v) * Real.exp (2 * v * M) * Real.exp (-2 * lam * |t|) := by
  have hRe := rotated_re_abs_lower b θ v t lam M hv.le hlam.le hA hB hM
  have h1 : 1 ≤ |(b * rotatedPoint θ v t).re| := by linarith
  have h2 : 1 ≤ |(b⁻¹ * rotatedPoint θ v t).re| := by linarith
  have hs1 := exp_abs_re_div_four_le_norm_sinh _ h1
  have hs2 := exp_abs_re_div_four_le_norm_sinh _ h2
  have hw : v ≤ ‖linePoint v t‖ := by
    calc
      v = |(linePoint v t).im| := by simp [linePoint, abs_of_pos hv]
      _ ≤ ‖linePoint v t‖ := Complex.abs_im_le_norm _
  set E := Real.exp (lam * |t| - v * M) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E ≤ Real.exp |(b * rotatedPoint θ v t).re| :=
    Real.exp_le_exp.mpr hRe.1
  have hE2 : E ≤ Real.exp |(b⁻¹ * rotatedPoint θ v t).re| :=
    Real.exp_le_exp.mpr hRe.2
  have hE12 : E * E ≤ Real.exp |(b * rotatedPoint θ v t).re| *
      Real.exp |(b⁻¹ * rotatedPoint θ v t).re| :=
    mul_le_mul hE1 hE2 hEpos.le (Real.exp_pos _).le
  have hL : v / 4 * E ^ 2 ≤
      4 * (Real.exp |(b * rotatedPoint θ v t).re| / 4) *
        (Real.exp |(b⁻¹ * rotatedPoint θ v t).re| / 4) * v := by
    nlinarith [mul_nonneg hv.le hEpos.le]
  have hD : 4 * (Real.exp |(b * rotatedPoint θ v t).re| / 4) *
      (Real.exp |(b⁻¹ * rotatedPoint θ v t).re| / 4) * v ≤
      4 * ‖Complex.sinh (b * rotatedPoint θ v t)‖ *
        ‖Complex.sinh (b⁻¹ * rotatedPoint θ v t)‖ * ‖linePoint v t‖ := by
    gcongr
  have hLpos : 0 < v / 4 * E ^ 2 := by positivity
  have hDpos : 0 < 4 * ‖Complex.sinh (b * rotatedPoint θ v t)‖ *
      ‖Complex.sinh (b⁻¹ * rotatedPoint θ v t)‖ * ‖linePoint v t‖ :=
    lt_of_lt_of_le hLpos (le_trans hL hD)
  rw [norm_amplitude_eq]
  calc
    (4 * ‖Complex.sinh (b * rotatedPoint θ v t)‖ *
        ‖Complex.sinh (b⁻¹ * rotatedPoint θ v t)‖ * ‖linePoint v t‖)⁻¹
        ≤ (4 * (Real.exp |(b * rotatedPoint θ v t).re| / 4) *
          (Real.exp |(b⁻¹ * rotatedPoint θ v t).re| / 4) * v)⁻¹ :=
      (inv_le_inv₀ hDpos (lt_of_lt_of_le hLpos hL)).mpr hD
    _ ≤ (v / 4 * E ^ 2)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le hLpos hL) hLpos).mpr hL
    _ = (4 / v) * Real.exp (2 * v * M) * Real.exp (-2 * lam * |t|) :=
      inv_sq_exp_target lam v M t hv


lemma integrable_exp_neg_two_mul_abs (lam : ℝ) (hlam : 0 < lam) :
    Integrable (fun t : ℝ => Real.exp (-2 * lam * |t|)) := by
  have hpos : IntegrableOn (fun t : ℝ => Real.exp (-2 * lam * |t|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -2 * lam) (by linarith) 0).congr_fun ?_
      measurableSet_Ioi
    intro t ht
    simp only [Pi.mul_apply]
    rw [abs_of_nonneg (le_of_lt ht)]
  have hneg : IntegrableOn (fun t : ℝ => Real.exp (-2 * lam * |t|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := 2 * lam) (by linarith) 0).congr_fun ?_
      measurableSet_Iic
    intro t ht
    simp only
    rw [abs_of_nonpos ht]
    ring_nf
  simpa [Iic_union_Ioi] using hneg.union hpos

lemma integral_exp_neg_two_mul_abs (lam : ℝ) (hlam : 0 < lam) :
    (∫ t : ℝ, Real.exp (-2 * lam * |t|)) = 1 / lam := by
  rw [integral_comp_abs (f := fun x : ℝ => Real.exp (-2 * lam * x))]
  rw [integral_exp_mul_Ioi (a := -2 * lam) (by linarith) 0]
  rw [mul_zero, Real.exp_zero]
  field_simp [hlam.ne']

lemma integral_exp_neg_two_mul_abs_tail (lam R : ℝ) (hlam : 0 < lam) (hR : 0 ≤ R) :
    (∫ t : ℝ in {t : ℝ | R ≤ |t|}, Real.exp (-2 * lam * |t|)) =
      (1 / lam) * Real.exp (-2 * lam * R) := by
  rcases lt_or_eq_of_le hR with hRpos | rfl
  · have hset : {t : ℝ | R ≤ |t|} = Iic (-R) ∪ Ici R := by
      ext t
      change (R ≤ |t|) ↔ (t ∈ Iic (-R) ∪ Ici R)
      rw [le_abs]
      simp only [mem_union, mem_Iic, mem_Ici]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (by linarith)
      · rintro (h | h)
        · right; linarith
        · left; linarith
    have hdisj : Disjoint (Iic (-R)) (Ici R) := by
      rw [disjoint_left]
      intro t ht1 ht2
      simp only [mem_Iic] at ht1
      simp only [mem_Ici] at ht2
      linarith
    rw [hset]
    rw [setIntegral_union hdisj measurableSet_Ici
      ((integrable_exp_neg_two_mul_abs lam hlam).integrableOn)
      ((integrable_exp_neg_two_mul_abs lam hlam).integrableOn)]
    have h1 : (∫ t : ℝ in Iic (-R), Real.exp (-2 * lam * |t|)) =
        Real.exp (-2 * lam * R) / (2 * lam) := by
      have hcongr : (∫ t : ℝ in Iic (-R), Real.exp (-2 * lam * |t|)) =
          ∫ t : ℝ in Iic (-R), Real.exp ((2 * lam) * t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        simp only [mem_Iic] at ht
        change Real.exp (-2 * lam * |t|) = Real.exp (2 * lam * t)
        rw [abs_of_nonpos (by linarith)]
        ring_nf
      rw [hcongr, integral_exp_mul_Iic (a := 2 * lam) (by linarith) (-R)]
      have hexp : (2 * lam) * -R = -2 * lam * R := by ring
      rw [hexp]
    have h2 : (∫ t : ℝ in Ici R, Real.exp (-2 * lam * |t|)) =
        Real.exp (-2 * lam * R) / (2 * lam) := by
      rw [integral_Ici_eq_integral_Ioi]
      have hcongr : (∫ t : ℝ in Ioi R, Real.exp (-2 * lam * |t|)) =
          ∫ t : ℝ in Ioi R, Real.exp ((-2 * lam) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only [mem_Ioi] at ht
        change Real.exp (-2 * lam * |t|) = Real.exp (-2 * lam * t)
        rw [abs_of_nonneg (by linarith)]
      rw [hcongr, integral_exp_mul_Ioi (a := -2 * lam) (by linarith) R]
      field_simp [hlam.ne']
    rw [h1, h2]
    field_simp [hlam.ne']
    ring
  · have hset0 : {t : ℝ | 0 ≤ |t|} = univ := by
      ext t
      simp
    rw [hset0, setIntegral_univ, integral_exp_neg_two_mul_abs lam hlam]
    rw [mul_zero, Real.exp_zero, mul_one]

end SICLean.L4.Sector
