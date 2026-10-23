import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Exponential bounds for the Faddeev integrand

The two sinh factors are estimated separately using reverse triangle inequality. The parameter `q`
is independent of `p` in these lemmas; the Faddeev application specializes it to `p⁻¹`. No contour
or special-function identity is assumed here.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4

theorem integrable_of_continuous_exp_abs_bound
    {f : ℝ → ℂ} (hf : Continuous f) {δ : ℝ} (hδ : 0 < δ)
    {C R : ℝ} (hbound : ∀ x : ℝ, R ≤ |x| →
      ‖f x‖ ≤ C * Real.exp (-δ * |x|)) :
    Integrable f := by
  refine hf.locallyIntegrable.integrable_of_isBigO_atBot_atTop
    (g := fun x : ℝ => Real.exp (δ * x))
    (g' := fun x : ℝ => Real.exp (-δ * x)) ?_ ?_ ?_ ?_
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_le_atBot (min (-R) 0)] with x hx
    have hx0 : x ≤ 0 := hx.trans (min_le_right _ _)
    have hxR : R ≤ |x| := by
      rw [abs_of_nonpos hx0]
      linarith [hx.trans (min_le_left (-R) 0)]
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonpos hx0, mul_neg, neg_mul, neg_neg] using hbound x hxR
  · exact (integrableOn_Iic_iff_integrableAtFilter_atBot.mp
      (integrableOn_exp_mul_Iic hδ 0)).1
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (max R 0)] with x hx
    have hx0 : 0 ≤ x := (le_max_right R 0).trans hx
    have hxR : R ≤ |x| := by
      rw [abs_of_nonneg hx0]
      exact (le_max_left R 0).trans hx
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg hx0] using hbound x hxR
  · exact (integrableOn_Ici_iff_integrableAtFilter_atTop.mp
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
        (integrableOn_exp_mul_Ioi (neg_neg_iff_pos.mpr hδ) 0))).1

theorem exp_re_sub_exp_neg_re_le_two_norm_sinh (u : ℂ) :
    Real.exp u.re - Real.exp (-u.re) ≤ 2 * ‖Complex.sinh u‖ := by
  have hh := norm_sub_norm_le (Complex.exp u) (Complex.exp (-u))
  simpa only [Complex.norm_exp, Complex.neg_re, ← Complex.two_sinh,
    norm_mul, Complex.norm_ofNat, Nat.abs_ofNat] using hh

theorem exp_abs_re_le_four_norm_sinh (u : ℂ) (hu : 1 ≤ |u.re|) :
    Real.exp |u.re| ≤ 4 * ‖Complex.sinh u‖ := by
  have base (v : ℂ) (hv : 1 ≤ v.re) :
      Real.exp v.re ≤ 4 * ‖Complex.sinh v‖ := by
    have hneg : Real.exp (-v.re) ≤ 1 := by
      simpa using (Real.exp_le_exp.mpr (show -v.re ≤ 0 by linarith))
    have hpos : 2 ≤ Real.exp v.re := by
      linarith [Real.add_one_le_exp v.re]
    linarith [exp_re_sub_exp_neg_re_le_two_norm_sinh v]
  by_cases h : 0 ≤ u.re
  · rw [abs_of_nonneg h] at hu ⊢
    exact base u hu
  · rw [abs_of_neg (lt_of_not_ge h)] at hu ⊢
    simpa only [Complex.neg_re, Complex.sinh_neg, norm_neg] using base (-u) hu

theorem abs_re_mul_line_lower (p : ℂ) (h x : ℝ) (hp : 0 ≤ p.re) :
    p.re * |x| - |p.im * h| ≤
      |(p * ((x : ℂ) + Complex.I * (h : ℂ))).re| := by
  have hr : (p * ((x : ℂ) + Complex.I * (h : ℂ))).re =
      p.re * x - p.im * h := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hr]
  calc
    p.re * |x| - |p.im * h| = |p.re * x| - |p.im * h| := by
      simp only [abs_mul, abs_of_nonneg hp]
    _ ≤ |p.re * x - p.im * h| := abs_sub_abs_le_abs_sub _ _

theorem norm_sinh_line_inv_le (p : ℂ) (h x : ℝ)
    (hp : 0 ≤ p.re) (hx : 1 + |p.im * h| ≤ p.re * |x|) :
    ‖Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ)))‖⁻¹ ≤
      4 * Real.exp (-(p.re * |x| - |p.im * h|)) := by
  let u := p * ((x : ℂ) + Complex.I * (h : ℂ))
  have hre : p.re * |x| - |p.im * h| ≤ |u.re| :=
    abs_re_mul_line_lower p h x hp
  have hu : 1 ≤ |u.re| := by linarith
  have he : Real.exp (p.re * |x| - |p.im * h|) ≤
      4 * ‖Complex.sinh u‖ :=
    (Real.exp_le_exp.mpr hre).trans (exp_abs_re_le_four_norm_sinh u hu)
  have hl : Real.exp (p.re * |x| - |p.im * h|) / 4 ≤
      ‖Complex.sinh u‖ := by linarith
  have hepos : 0 < Real.exp (p.re * |x| - |p.im * h|) / 4 := by positivity
  have hupos : 0 < ‖Complex.sinh u‖ := hepos.trans_le hl
  calc
    ‖Complex.sinh u‖⁻¹ ≤
        (Real.exp (p.re * |x| - |p.im * h|) / 4)⁻¹ :=
      (inv_le_inv₀ hupos hepos).mpr hl
    _ = 4 * Real.exp (-(p.re * |x| - |p.im * h|)) := by
      rw [Real.exp_neg]
      simp only [inv_div]
      ring

theorem norm_exp_line_le (z : ℂ) (h x : ℝ) :
    ‖Complex.exp (-2 * Complex.I * z *
      ((x : ℂ) + Complex.I * (h : ℂ)))‖ ≤
      Real.exp (2 * |z.im| * |x| + 2 * z.re * h) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hx := le_abs_self (z.im * x)
  rw [abs_mul] at hx
  simp [Complex.mul_re, Complex.mul_im]
  nlinarith

theorem norm_exp_div_sinh_product_line_le (p q z : ℂ) (h x : ℝ)
    (hp : 0 ≤ p.re) (hq : 0 ≤ q.re)
    (hpx : 1 + |p.im * h| ≤ p.re * |x|)
    (hqx : 1 + |q.im * h| ≤ q.re * |x|) :
    ‖Complex.exp (-2 * Complex.I * z *
      ((x : ℂ) + Complex.I * (h : ℂ))) /
      (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))))‖ ≤
      (4 * Real.exp (2 * z.re * h + |p.im * h| + |q.im * h|)) *
        Real.exp (-(p.re + q.re - 2 * |z.im|) * |x|) := by
  let w : ℂ := (x : ℂ) + Complex.I * (h : ℂ)
  have he := norm_exp_line_le z h x
  have hp' := norm_sinh_line_inv_le p h x hp hpx
  have hq' := norm_sinh_line_inv_le q h x hq hqx
  change ‖Complex.exp (-2 * Complex.I * z * w) /
    (4 * Complex.sinh (p * w) * Complex.sinh (q * w))‖ ≤ _
  rw [norm_div, norm_mul, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    ‖Complex.exp (-2 * Complex.I * z * w)‖ /
        (4 * ‖Complex.sinh (p * w)‖ * ‖Complex.sinh (q * w)‖) =
      (1 / 4) * ‖Complex.exp (-2 * Complex.I * z * w)‖ *
        ‖Complex.sinh (p * w)‖⁻¹ * ‖Complex.sinh (q * w)‖⁻¹ := by
          simp only [div_eq_mul_inv, mul_inv]
          ring
    _ ≤ (1 / 4) * Real.exp (2 * |z.im| * |x| + 2 * z.re * h) *
        (4 * Real.exp (-(p.re * |x| - |p.im * h|))) *
        (4 * Real.exp (-(q.re * |x| - |q.im * h|))) := by gcongr
    _ = 4 * (Real.exp (2 * |z.im| * |x| + 2 * z.re * h) *
        Real.exp (-(p.re * |x| - |p.im * h|)) *
        Real.exp (-(q.re * |x| - |q.im * h|))) := by ring
    _ = 4 * Real.exp ((2 * |z.im| * |x| + 2 * z.re * h) +
        (-(p.re * |x| - |p.im * h|)) +
        (-(q.re * |x| - |q.im * h|))) := by simp only [Real.exp_add]
    _ = 4 * Real.exp ((2 * z.re * h + |p.im * h| + |q.im * h|) +
        (-(p.re + q.re - 2 * |z.im|) * |x|)) := by congr 2; ring
    _ = _ := by rw [Real.exp_add]; ring

theorem integrable_exp_div_sinh_product_line
    (p q z : ℂ) (h : ℝ)
    (hp : 0 < p.re) (hq : 0 < q.re)
    (hz : 2 * |z.im| < p.re + q.re)
    (hd : ∀ x : ℝ,
      4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))) ≠ 0) :
    Integrable (fun x : ℝ =>
      Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
        (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
          Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))))) := by
  apply integrable_of_continuous_exp_abs_bound
    (δ := p.re + q.re - 2 * |z.im|)
    (C := 4 * Real.exp (2 * z.re * h + |p.im * h| + |q.im * h|))
    (R := max ((1 + |p.im * h|) / p.re) ((1 + |q.im * h|) / q.re))
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · exact hd
  · linarith
  · intro x hx
    apply norm_exp_div_sinh_product_line_le p q z h x hp.le hq.le
    · have hh := (le_max_left ((1 + |p.im * h|) / p.re)
        ((1 + |q.im * h|) / q.re)).trans hx
      simpa only [mul_comm] using (div_le_iff₀ hp).mp hh
    · have hh := (le_max_right ((1 + |p.im * h|) / p.re)
        ((1 + |q.im * h|) / q.re)).trans hx
      simpa only [mul_comm] using (div_le_iff₀ hq).mp hh

theorem integrable_exp_div_sinh_product_line_mul
    (p q z : ℂ) (h : ℝ)
    (hp : 0 < p.re) (hq : 0 < q.re)
    (hz : 2 * |z.im| < p.re + q.re)
    (hd : ∀ x : ℝ,
      4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))) *
          ((x : ℂ) + Complex.I * (h : ℂ)) ≠ 0) :
    Integrable (fun x : ℝ =>
      Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
        (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
          Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))) *
            ((x : ℂ) + Complex.I * (h : ℂ)))) := by
  apply integrable_of_continuous_exp_abs_bound
    (δ := p.re + q.re - 2 * |z.im|)
    (C := 4 * Real.exp (2 * z.re * h + |p.im * h| + |q.im * h|))
    (R := max 1 (max ((1 + |p.im * h|) / p.re) ((1 + |q.im * h|) / q.re)))
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · exact hd
  · linarith
  · intro x hx
    have hx1 : 1 ≤ |x| := (le_max_left _ _).trans hx
    have hxp : 1 + |p.im * h| ≤ p.re * |x| := by
      have hh := (le_max_left ((1 + |p.im * h|) / p.re)
        ((1 + |q.im * h|) / q.re)).trans ((le_max_right _ _).trans hx)
      simpa only [mul_comm] using (div_le_iff₀ hp).mp hh
    have hxq : 1 + |q.im * h| ≤ q.re * |x| := by
      have hh := (le_max_right ((1 + |p.im * h|) / p.re)
        ((1 + |q.im * h|) / q.re)).trans ((le_max_right _ _).trans hx)
      simpa only [mul_comm] using (div_le_iff₀ hq).mp hh
    have hw : 1 ≤ ‖((x : ℂ) + Complex.I * (h : ℂ))‖ := by
      calc
        1 ≤ |x| := hx1
        _ = |(((x : ℂ) + Complex.I * (h : ℂ))).re| := by simp
        _ ≤ _ := Complex.abs_re_le_norm _
    calc
      _ = ‖Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
        (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
          Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))))‖ /
            ‖((x : ℂ) + Complex.I * (h : ℂ))‖ := by
        rw [div_mul_eq_div_div, norm_div]
      _ ≤ ‖Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
        (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
          Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))))‖ :=
        div_le_self (norm_nonneg _) hw
      _ ≤ _ := norm_exp_div_sinh_product_line_le p q z h x hp.le hq.le hxp hxq

theorem integrable_derivative_exp_div_sinh_product_line_mul
    (p q z : ℂ) (h : ℝ)
    (hp : 0 < p.re) (hq : 0 < q.re)
    (hz : 2 * |z.im| < p.re + q.re)
    (hd : ∀ x : ℝ,
      4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))) *
          ((x : ℂ) + Complex.I * (h : ℂ)) ≠ 0) :
    Integrable (fun x : ℝ =>
      (-2 * Complex.I * ((x : ℂ) + Complex.I * (h : ℂ))) *
      (Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
        (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
          Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))) *
            ((x : ℂ) + Complex.I * (h : ℂ))))) := by
  have hd' : ∀ x : ℝ,
      4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))) ≠ 0 :=
    fun x => (mul_ne_zero_iff.mp (hd x)).1
  have hw : ∀ x : ℝ, ((x : ℂ) + Complex.I * (h : ℂ)) ≠ 0 :=
    fun x => (mul_ne_zero_iff.mp (hd x)).2
  apply ((integrable_exp_div_sinh_product_line p q z h hp hq hz hd').const_mul
    (-2 * Complex.I)).congr
  filter_upwards [] with x
  field_simp [hd' x, hw x]

/-- Uniformity in bounded heights and in a closed argument substrip. -/
theorem norm_exp_div_sinh_product_line_le_uniform
    (p q z : ℂ) (h x H M s : ℝ)
    (hp : 0 ≤ p.re) (hq : 0 ≤ q.re)
    (hH : |h| ≤ H) (hM : |z.re| ≤ M) (hs : |z.im| ≤ s)
    (hpx : 1 + |p.im| * H ≤ p.re * |x|)
    (hqx : 1 + |q.im| * H ≤ q.re * |x|) :
    ‖Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
      (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))))‖ ≤
      (4 * Real.exp ((2 * M + |p.im| + |q.im|) * H)) *
        Real.exp (-(p.re + q.re - 2 * s) * |x|) := by
  have hM0 : 0 ≤ M := (abs_nonneg z.re).trans hM
  have hph : |p.im * h| ≤ |p.im| * H := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hH (abs_nonneg _)
  have hqh : |q.im * h| ≤ |q.im| * H := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hH (abs_nonneg _)
  have hzh : z.re * h ≤ M * H := by
    calc
      z.re * h ≤ |z.re * h| := le_abs_self _
      _ = |z.re| * |h| := abs_mul _ _
      _ ≤ M * H := mul_le_mul hM hH (abs_nonneg _) hM0
  calc
    _ ≤ (4 * Real.exp (2 * z.re * h + |p.im * h| + |q.im * h|)) *
        Real.exp (-(p.re + q.re - 2 * |z.im|) * |x|) :=
      norm_exp_div_sinh_product_line_le p q z h x hp hq
        (by linarith) (by linarith)
    _ ≤ _ := by
      gcongr
      nlinarith

theorem integrable_real_exp_neg_abs {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : ℝ => Real.exp (-δ * |x|)) := by
  have hc : Integrable (fun x : ℝ => (Real.exp (-δ * |x|) : ℂ)) :=
    integrable_of_continuous_exp_abs_bound (by fun_prop) hδ
      (C := 1) (R := 0) (by
        intro x hx
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), one_mul]
        exact le_rfl)
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using hc.norm

/-- A compact middle interval and a common exponential tail give one integrable bound for the whole
compact parameter family. -/
theorem exists_integrable_majorant_of_compact_exp_tail
    {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K) (F : α → ℝ → ℂ)
    {δ C R : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn (fun px : α × ℝ => F px.1 px.2)
      (K ×ˢ Icc (-R) R))
    (htail : ∀ p ∈ K, ∀ x : ℝ, R ≤ |x| →
      ‖F p x‖ ≤ C * Real.exp (-δ * |x|)) :
    ∃ B : ℝ → ℝ, Integrable B ∧
      ∀ p ∈ K, ∀ x : ℝ, ‖F p x‖ ≤ B x := by
  obtain ⟨M₀, hM₀⟩ :=
    (hK.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  let M := max M₀ 0
  let A := M * Real.exp (δ * R) + max C 0
  refine ⟨fun x => A * Real.exp (-δ * |x|),
    (integrable_real_exp_neg_abs hδ).const_mul A, ?_⟩
  intro p hp x
  have hM : 0 ≤ M := le_max_right _ _
  have hA₁ : C ≤ A := by
    dsimp [A]
    exact (le_max_left C 0).trans
      (le_add_of_nonneg_left (mul_nonneg hM (Real.exp_nonneg _)))
  have hA₂ : M * Real.exp (δ * R) ≤ A :=
    le_add_of_nonneg_right (le_max_right C 0)
  by_cases hx : R ≤ |x|
  · exact (htail p hp x hx).trans
      (mul_le_mul_of_nonneg_right hA₁ (Real.exp_nonneg _))
  · have hxR : |x| ≤ R := le_of_lt (lt_of_not_ge hx)
    have hxc : x ∈ Icc (-R) R := by
      constructor
      · linarith [neg_abs_le x]
      · exact (le_abs_self x).trans hxR
    have hexp : 1 ≤ Real.exp (δ * R) * Real.exp (-δ * |x|) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc
      ‖F p x‖ ≤ M₀ := hM₀ (p, x) ⟨hp, hxc⟩
      _ ≤ M := le_max_left _ _
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * (Real.exp (δ * R) * Real.exp (-δ * |x|)) :=
        mul_le_mul_of_nonneg_left hexp hM
      _ = (M * Real.exp (δ * R)) * Real.exp (-δ * |x|) := by ring
      _ ≤ A * Real.exp (-δ * |x|) :=
        mul_le_mul_of_nonneg_right hA₂ (Real.exp_nonneg _)

theorem norm_exp_div_sinh_product_line_mul_le_uniform_parameters
    (p q z : ℂ) (h x a c P Q M δ : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hp : a ≤ p.re) (hq : c ≤ q.re)
    (hP : |p.im| ≤ P) (hQ : |q.im| ≤ Q) (hM : |z.re| ≤ M)
    (hδ : δ ≤ p.re + q.re - 2 * |z.im|)
    (hx : 1 ≤ |x|)
    (hpx : 1 + P * |h| ≤ a * |x|)
    (hqx : 1 + Q * |h| ≤ c * |x|) :
    ‖Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
      (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))) *
          ((x : ℂ) + Complex.I * (h : ℂ)))‖ ≤
      (4 * Real.exp ((2 * M + P + Q) * |h|)) *
        Real.exp (-δ * |x|) := by
  have hp0 : 0 ≤ p.re := ha.le.trans hp
  have hq0 : 0 ≤ q.re := hc.le.trans hq
  have hph : |p.im * h| ≤ P * |h| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hP (abs_nonneg _)
  have hqh : |q.im * h| ≤ Q * |h| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hQ (abs_nonneg _)
  have hzh : z.re * h ≤ M * |h| := by
    calc
      z.re * h ≤ |z.re * h| := le_abs_self _
      _ = |z.re| * |h| := abs_mul _ _
      _ ≤ M * |h| := mul_le_mul_of_nonneg_right hM (abs_nonneg _)
  have hpx' : 1 + |p.im * h| ≤ p.re * |x| := by nlinarith [abs_nonneg x]
  have hqx' : 1 + |q.im * h| ≤ q.re * |x| := by nlinarith [abs_nonneg x]
  have hw : 1 ≤ ‖((x : ℂ) + Complex.I * (h : ℂ))‖ := by
    calc
      1 ≤ |x| := hx
      _ = |(((x : ℂ) + Complex.I * (h : ℂ))).re| := by simp
      _ ≤ _ := Complex.abs_re_le_norm _
  calc
    _ = ‖Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
      (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))))‖ /
          ‖((x : ℂ) + Complex.I * (h : ℂ))‖ := by
      rw [div_mul_eq_div_div, norm_div]
    _ ≤ ‖Complex.exp (-2 * Complex.I * z * ((x : ℂ) + Complex.I * (h : ℂ))) /
      (4 * Complex.sinh (p * ((x : ℂ) + Complex.I * (h : ℂ))) *
        Complex.sinh (q * ((x : ℂ) + Complex.I * (h : ℂ))))‖ :=
      div_le_self (norm_nonneg _) hw
    _ ≤ (4 * Real.exp (2 * z.re * h + |p.im * h| + |q.im * h|)) *
        Real.exp (-(p.re + q.re - 2 * |z.im|) * |x|) :=
      norm_exp_div_sinh_product_line_le p q z h x hp0 hq0 hpx' hqx'
    _ ≤ _ := by
      gcongr
      nlinarith

end SICLean.L4
