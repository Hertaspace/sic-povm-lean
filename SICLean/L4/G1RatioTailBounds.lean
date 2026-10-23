import SICLean.L4.G1PinchGeometry
import SICLean.L4.ModularSectorBilateral
import SICLean.L4.G1RatioTailBoundsAux

set_option autoImplicit false

/-!
# Strict ratio windows and vertical-strip tails

Strict windows and their tail estimates. [RW26, p. 7, p. 13]:
Uniform bounds and the finite account are formalized here.

The complex kernel is exactly the existing kernel with concrete G1 data; its real restriction is
`g1RatioKernel`, not a new real integrand. The window variables specialize to `g1S` and `g1L`. All
square roots, Phi/phi factors and eta multipliers are inherited unchanged. No G1 integral identity,
removable RHS, G2 assertion, or no-pinch premise is needed for the tails. Constants precede all
varying parameters/indices.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1RatioTail

open G1RatioTailBoundsAux

def complexS (M : SL(2, ℤ)) (τ w : ℂ) (h ell : ℤ) : ℂ :=
  (M 1 0 : ℂ) * w + (h : ℂ) + (ell : ℂ) * etaDenom M τ

def complexL (M : SL(2, ℤ)) (τ w y : ℂ) (h ell p : ℤ) : ℂ :=
  complexS M τ w h ell + (M 1 0 : ℂ) * y + ((p : ℂ) - 1) * etaDenom M τ

def complexKernel (M : SL(2, ℤ)) (τ w y : ℂ)
    (n h ell p m : ℤ) (z : ℂ) : ℂ :=
  ModularCluster.kernel M (G1Pinch.ratioData w y n h ell p m) z τ

/-- A finite horizontal connector, directed from a to b, with dz=dx. [RW26, p. 13]. -/
def horizontalIntegral (f : ℂ → ℂ) (a b t : ℝ) : ℂ :=
  ∫ x : ℝ in a..b, f (g1VerticalPoint x t)

/-- Literal real specialization, including specified values at denominator Phi poles. [RW26, p. 7,
(23)]. -/
theorem complexKernel_real (M : SL(2, ℤ)) (τ w y : ℝ)
    (n h ell p m : ℤ) :
    complexKernel M (τ : ℂ) (w : ℂ) (y : ℂ) n h ell p m =
      g1RatioKernel M τ w y n h ell p m := by
  rfl

/-- Both actual real-window casts, not an independently chosen window. [RW26, p. 7]. -/
theorem real_window_casts (M : SL(2, ℤ)) (τ w y : ℝ) (h ell p : ℤ) :
    complexS M (τ : ℂ) (w : ℂ) h ell = (g1S M τ w h ell : ℂ) ∧
      complexL M (τ : ℂ) (w : ℂ) (y : ℂ) h ell p =
        (g1L M τ w y h ell p : ℂ) := by
  simp [complexS, complexL, g1S, g1L, g1T, etaDenom, Complex.ofReal_intCast]

/-- Exact z coefficient in the existing E_m. [RW26, p. 7, (22), (23)]. -/
theorem exponent_affine (M : SL(2, ℤ)) (τ w z : ℂ) (n h ell m : ℤ)
    (hT : etaDenom M τ ≠ 0) :
    g1Exponent M τ w z n h ell m =
      complexS M τ w h ell / etaDenom M τ * z +
        g1Exponent M τ w 0 n h ell m := by
  unfold g1Exponent complexS
  field_simp
  <;> ring

/-- The quadratic terms cancel. The constant uses the actual existing reflection polynomial,
including its non-fixed-point term. [RW26, p. 6, Prop. 1, p. 7]. -/
theorem reflection_difference_affine (M : SL(2, ℤ)) (τ y z : ℂ)
    (n p m : ℤ) (hT : etaDenom M τ ≠ 0) :
    modularReflectionPolynomial M (m + 1) n z τ -
        modularReflectionPolynomial M (m + p) n (z + y) τ =
      ((M 1 0 : ℂ) * y / etaDenom M τ + (p : ℂ) - 1) * z +
        (modularReflectionPolynomial M (m + 1) n 0 τ -
          modularReflectionPolynomial M (m + p) n y τ) := by
  simp only [modularReflectionPolynomial, Int.cast_add, Int.cast_one]
  ring

/-- A common strict margin on a closed upper half-disk. No integrability is a field or premise.
[RW26, p. 7, p. 13]. -/
theorem strict_upper_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ τ ∈ ModularSector.upperParameterDisk τ₀ ρ,
        τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).re ∧
          κ ≤ 2 * Real.pi * (complexS M τ (w : ℂ) h ell / etaDenom M τ).re ∧
          κ ≤ -(2 * Real.pi *
            (complexL M τ (w : ℂ) (y : ℂ) h ell p / etaDenom M τ).re) := by
  have hcast : etaDenom M (τ₀ : ℂ) = (g1T M τ₀ : ℂ) := by
    simp [etaDenom, g1T, Complex.ofReal_intCast]
  have hne : etaDenom M (τ₀ : ℂ) ≠ 0 := by
    rw [hcast]
    exact_mod_cast hT.ne'
  have hS : ContinuousAt (fun τ : ℂ =>
      2 * Real.pi * (complexS M τ (w : ℂ) h ell / etaDenom M τ).re) (τ₀ : ℂ) := by
    unfold complexS etaDenom at *
    fun_prop (disch := assumption)
  have hL' : ContinuousAt (fun τ : ℂ =>
      -(2 * Real.pi * (complexL M τ (w : ℂ) (y : ℂ) h ell p /
        etaDenom M τ).re)) (τ₀ : ℂ) := by
    unfold complexL complexS etaDenom at *
    fun_prop (disch := assumption)
  obtain ⟨ρ₁, κ₁, hρ₁, hκ₁, h₁⟩ := positive_real_disk M hM τ₀ hT _ hS (by
    rw [(real_window_casts M τ₀ w y h ell p).1, hcast]
    simp only [← Complex.ofReal_div, Complex.ofReal_re]
    exact mul_pos (by positivity) (div_pos hs hT))
  obtain ⟨ρ₂, κ₂, hρ₂, hκ₂, h₂⟩ := positive_real_disk M hM τ₀ hT _ hL' (by
    rw [(real_window_casts M τ₀ w y h ell p).2, hcast]
    simp only [← Complex.ofReal_div, Complex.ofReal_re]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (by positivity) (div_neg_of_neg_of_pos hL hT)))
  refine ⟨min ρ₁ ρ₂, min κ₁ κ₂, lt_min hρ₁ hρ₂, lt_min hκ₁ hκ₂, ?_⟩
  intro τ hτ
  have H₁ := h₁ τ (parameterDisk_mono (min_le_left _ _) hτ.1)
  have H₂ := h₂ τ (parameterDisk_mono (min_le_right _ _) hτ.1)
  exact ⟨H₁.1, H₁.2.1, (min_le_left _ _).trans H₁.2.2,
    (min_le_right _ _).trans H₂.2.2⟩

/-- Upper exponential decay for every bounded-width vertical strip, simultaneously in finite m and
nearby upper parameters. [RW26, p. 7, Lemma 1, p. 13]. -/
theorem uniform_upper_strip (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (hs : 0 < g1S M τ₀ w h ell) (hab : a ≤ b) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.upperParameterDisk τ₀ ρ, ∀ m ∈ F,
        ∀ x ∈ Icc a b, ∀ t : ℝ, R ≤ t →
          ‖complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m (g1VerticalPoint x t)‖ ≤
            C * Real.exp (-κ * t) := by
  classical
  let A : ℂ → ℂ := fun τ => complexS M τ (w : ℂ) h ell / etaDenom M τ
  have hcast : etaDenom M (τ₀ : ℂ) = (g1T M τ₀ : ℂ) := by
    simp [etaDenom, g1T, Complex.ofReal_intCast]
  have hne : etaDenom M (τ₀ : ℂ) ≠ 0 := by
    rw [hcast]
    exact_mod_cast hT.ne'
  have hA : ∀ τ : ℂ, etaDenom M τ ≠ 0 → ContinuousAt A τ := by
    intro τ hτ
    unfold A complexS etaDenom at *
    fun_prop (disch := assumption)
  obtain ⟨ρ₁, κ, hρ₁, hκ, hmargin⟩ := positive_real_disk M hM τ₀ hT
    (fun τ => 2 * Real.pi * (A τ).re) (by fun_prop (disch := exact hA _ hne)) (by
      dsimp [A]
      rw [(real_window_casts M τ₀ w y h ell p).1, hcast]
      simp only [← Complex.ofReal_div, Complex.ofReal_re]
      exact mul_pos (by positivity) (div_pos hs hT))
  let G : Finset (ℤ × ℤ) :=
    F.image (fun m => (m + 1, n)) ∪ F.image (fun m => (m + p, n))
  have hα : 0 < Real.pi / 8 := by positivity
  have hα' : Real.pi / 8 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨ρ₂, D, k, R₀, hρ₂, hD, hk, hR₀, _, _, hratio⟩ :=
    ModularSector.bounded_shift_ratio_decay M hM G τ₀ (Real.pi / 8) |y|
      hT hα hα' (abs_nonneg y)
  let ρ := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hdom : ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, etaDenom M τ ≠ 0 := by
    intro τ hτ
    exact ne_zero_of_re_pos (hmargin τ (parameterDisk_mono (min_le_left _ _) hτ)).2.1
  obtain ⟨C, hC, hbound⟩ := affine_exp_compact_bound
    (ModularSector.parameterDisk τ₀ ρ) (isCompact_closedBall _ _) F a b A
    (fun m τ => g1Exponent M τ (w : ℂ) 0 n h ell m)
    (fun τ hτ => (hA τ (hdom τ hτ)).continuousWithinAt)
    (fun m _ τ hτ => (exponent_parameter_continuousAt M τ (w : ℂ) 0
      n h ell m (hdom τ hτ)).continuousWithinAt)
  obtain ⟨R, hR, hstrip⟩ := vertical_strip_sectors a b R₀ hR₀.le
  refine ⟨ρ, (D + 1) * C, κ, R, hρ, by positivity, hκ, hR, ?_⟩
  intro τ hτ m hm x hx t ht
  have hdisk := hτ.1
  have hτ₂ := parameterDisk_mono (min_le_right ρ₁ ρ₂) hdisk
  have hτ₁ := parameterDisk_mono (min_le_left ρ₁ ρ₂) hdisk
  have hi : (m + 1, n) ∈ G := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have hj : (m + p, n) ∈ G := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have H := (hratio τ hτ₂ (m + 1, n) hi (m + p, n) hj (y : ℂ)
    (by simp) ).1 _ ((hstrip x hx t).1 ht)
  have hq : ‖modularPhi M (m + 1) n (g1VerticalPoint x t) τ /
      modularPhi M (m + p) n (g1VerticalPoint x t + (y : ℂ)) τ‖ ≤ D + 1 := by
    apply quotient_norm_le
    have h_exp : Real.exp (-k * ‖g1VerticalPoint x t‖) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (norm_nonneg _)
    exact ((le_add_of_nonneg_right (norm_nonneg _)).trans H).trans
      (by nlinarith)
  have he : ‖e (A τ * g1VerticalPoint x t + g1Exponent M τ (w : ℂ) 0 n h ell m)‖ ≤
      C * Real.exp (-κ * t) := by
    rw [affine_exp_norm]
    apply mul_le_mul (hbound τ hdisk m hm x hx)
      (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC.le
    have Hκ := (hmargin τ hτ₁).2.2
    have ht₀ : 0 ≤ t := le_trans hR.le ht
    nlinarith [mul_le_mul_of_nonneg_right Hκ ht₀]
  rw [complexKernel, kernel_ratio_eq, exponent_affine M τ (w : ℂ)
    (g1VerticalPoint x t) n h ell m (hdom τ hdisk), norm_mul]
  change _ * ‖e (A τ * g1VerticalPoint x t + _)‖ ≤ _
  calc
    _ ≤ (D + 1) * (C * Real.exp (-κ * t)) :=
      mul_le_mul hq he (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Lower exponential decay: t is negative and the exponent is +κt. [RW26, p. 7, p. 13]. Only L<0 is
needed on this tail. -/
theorem uniform_lower_strip (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (hL : g1L M τ₀ w y h ell p < 0) (hab : a ≤ b) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.upperParameterDisk τ₀ ρ, ∀ m ∈ F,
        ∀ x ∈ Icc a b, ∀ t : ℝ, t ≤ -R →
          ‖complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m (g1VerticalPoint x t)‖ ≤
            C * Real.exp (κ * t) := by
  classical
  let A : ℂ → ℂ := fun τ => complexL M τ (w : ℂ) (y : ℂ) h ell p / etaDenom M τ
  let B : ℤ → ℂ → ℂ := fun m τ =>
    modularReflectionPolynomial M (m + 1) n 0 τ -
      modularReflectionPolynomial M (m + p) n (y : ℂ) τ +
        g1Exponent M τ (w : ℂ) 0 n h ell m
  have hcast : etaDenom M (τ₀ : ℂ) = (g1T M τ₀ : ℂ) := by
    simp [etaDenom, g1T, Complex.ofReal_intCast]
  have hne : etaDenom M (τ₀ : ℂ) ≠ 0 := by
    rw [hcast]
    exact_mod_cast hT.ne'
  have hA : ∀ τ : ℂ, etaDenom M τ ≠ 0 → ContinuousAt A τ := by
    intro τ hτ
    unfold A complexL complexS etaDenom at *
    fun_prop (disch := assumption)
  obtain ⟨ρ₁, κ, hρ₁, hκ, hmargin⟩ := positive_real_disk M hM τ₀ hT
    (fun τ => -(2 * Real.pi * (A τ).re)) (by fun_prop (disch := exact hA _ hne)) (by
      dsimp [A]
      rw [(real_window_casts M τ₀ w y h ell p).2, hcast]
      simp only [← Complex.ofReal_div, Complex.ofReal_re]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg (by positivity) (div_neg_of_neg_of_pos hL hT)))
  let G : Finset (ℤ × ℤ) :=
    F.image (fun m => (m + 1, n)) ∪ F.image (fun m => (m + p, n))
  have hα : 0 < Real.pi / 8 := by positivity
  have hα' : Real.pi / 8 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨ρ₂, D, k, R₀, hρ₂, hD, hk, hR₀, _, _, hratio⟩ :=
    ModularSector.bounded_shift_ratio_decay M hM G τ₀ (Real.pi / 8) |y|
      hT hα hα' (abs_nonneg y)
  let ρ := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hdom : ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, etaDenom M τ ≠ 0 := by
    intro τ hτ
    exact ne_zero_of_re_pos (hmargin τ (parameterDisk_mono (min_le_left _ _) hτ)).2.1
  have hB : ∀ m τ, etaDenom M τ ≠ 0 → ContinuousAt (B m) τ := by
    intro m τ hτ
    exact ((polynomial_parameter_continuousAt M τ 0 (m + 1) n hτ).sub
      (polynomial_parameter_continuousAt M τ (y : ℂ) (m + p) n hτ)).add
        (exponent_parameter_continuousAt M τ (w : ℂ) 0 n h ell m hτ)
  obtain ⟨C, hC, hbound⟩ := affine_exp_compact_bound
    (ModularSector.parameterDisk τ₀ ρ) (isCompact_closedBall _ _) F a b A B
    (fun τ hτ => (hA τ (hdom τ hτ)).continuousWithinAt)
    (fun m _ τ hτ => (hB m τ (hdom τ hτ)).continuousWithinAt)
  obtain ⟨R, hR, hstrip⟩ := vertical_strip_sectors a b R₀ hR₀.le
  refine ⟨ρ, (D + 1) * C, κ, R, hρ, by positivity, hκ, hR, ?_⟩
  intro τ hτ m hm x hx t ht
  have hdisk := hτ.1
  have hτ₂ := parameterDisk_mono (min_le_right ρ₁ ρ₂) hdisk
  have hτ₁ := parameterDisk_mono (min_le_left ρ₁ ρ₂) hdisk
  have hi : (m + 1, n) ∈ G := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have hj : (m + p, n) ∈ G := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  let z := g1VerticalPoint x t
  let q := modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + (y : ℂ)) τ
  let a' := modularReflectionFactor M (m + 1) n z τ /
    modularReflectionFactor M (m + p) n (z + (y : ℂ)) τ
  have ha' : a' ≠ 0 := div_ne_zero (reflectionFactor_ne_zero M hM _ _ _ _)
    (reflectionFactor_ne_zero M hM _ _ _ _)
  have H := (hratio τ hτ₂ (m + 1, n) hi (m + p, n) hj (y : ℂ)
    (by simp)).2 z ((hstrip x hx t).2 ht)
  have hq : ‖q / a'‖ ≤ D + 1 := by
    apply quotient_norm_le
    have h_exp : Real.exp (-k * ‖z‖) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (norm_nonneg _)
    exact ((le_add_of_nonneg_right (norm_nonneg _)).trans H).trans (by nlinarith)
  have hAff : modularReflectionPolynomial M (m + 1) n z τ -
      modularReflectionPolynomial M (m + p) n (z + (y : ℂ)) τ +
        g1Exponent M τ (w : ℂ) z n h ell m = A τ * z + B m τ := by
    rw [reflection_difference_affine M τ (y : ℂ) z n p m (hdom τ hdisk),
      exponent_affine M τ (w : ℂ) z n h ell m (hdom τ hdisk)]
    dsimp [A, B, complexL]
    field_simp [hdom τ hdisk]
    <;> ring
  have he : ‖e (A τ * z + B m τ)‖ ≤ C * Real.exp (κ * t) := by
    rw [affine_exp_norm]
    apply mul_le_mul (hbound τ hdisk m hm x hx)
      (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC.le
    have Hκ := (hmargin τ hτ₁).2.2
    have ht₀ : t ≤ 0 := le_trans ht (by linarith)
    nlinarith [mul_le_mul_of_nonpos_right Hκ ht₀]
  have hkernel : complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m z =
      (q / a') * (a' * e (g1Exponent M τ (w : ℂ) z n h ell m)) := by
    rw [complexKernel, kernel_ratio_eq]
    change q * _ = _
    field_simp
  calc
    _ = ‖q / a'‖ * ‖e (A τ * z + B m τ)‖ := by
      rw [hkernel, norm_mul, reflection_exponential_norm M hM, hAff]
    _ ≤ (D + 1) * (C * Real.exp (κ * t)) :=
      mul_le_mul hq he (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- One common positive rate for both tails, all strip points and all m. [RW26, p. 7, p. 13]. No
assertion about the compact middle, which can contain candidate poles. -/
theorem uniform_two_tail_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (hs : 0 < g1S M τ₀ w h ell)
    (hL : g1L M τ₀ w y h ell p < 0) (hab : a ≤ b) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.upperParameterDisk τ₀ ρ, ∀ m ∈ F,
        ∀ x ∈ Icc a b, ∀ t : ℝ, R ≤ |t| →
          ‖complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m (g1VerticalPoint x t)‖ ≤
            C * Real.exp (-κ * |t|) := by
  obtain ⟨ρ₁, C₁, κ₁, R₁, hρ₁, hC₁, hκ₁, hR₁, hu⟩ :=
    uniform_upper_strip M hM τ₀ w y a b n h ell p F hT hs hab
  obtain ⟨ρ₂, C₂, κ₂, R₂, hρ₂, hC₂, hκ₂, hR₂, hl⟩ :=
    uniform_lower_strip M hM τ₀ w y a b n h ell p F hT hL hab
  refine ⟨min ρ₁ ρ₂, C₁ + C₂, min κ₁ κ₂, max R₁ R₂,
    lt_min hρ₁ hρ₂, by positivity, lt_min hκ₁ hκ₂,
    lt_of_lt_of_le hR₁ (le_max_left _ _), ?_⟩
  intro τ hτ m hm x hx t ht
  rcases le_total 0 t with ht₀ | ht₀
  · rw [abs_of_nonneg ht₀] at ht ⊢
    apply (hu τ (upperParameterDisk_mono (min_le_left _ _) hτ) m hm x hx t
      ((le_max_left _ _).trans ht)).trans
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_)
      (Real.exp_pos _).le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left κ₁ κ₂) ht₀]
  · rw [abs_of_nonpos ht₀] at ht ⊢
    apply (hl τ (upperParameterDisk_mono (min_le_right _ _) hτ) m hm x hx t
      (by linarith [le_max_right R₁ R₂])).trans
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_)
      (Real.exp_pos _).le (by positivity)
    nlinarith [mul_le_mul_of_nonpos_right (min_le_right κ₁ κ₂) ht₀]

/-- Finite horizontal segments are absolutely integrable at both tail heights. [RW26, p. 13]. -/
theorem horizontal_intervalIntegrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y a b : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ |t| →
      IntervalIntegrable (fun x : ℝ =>
        g1RatioKernel M τ w y n h ell p m (g1VerticalPoint x t)) volume a b := by
  have hα : 0 < Real.pi / 8 := by positivity
  have hα' : Real.pi / 8 < Real.pi / 2 := by linarith [Real.pi_pos]
  let F : Finset (ℤ × ℤ) := {(m + 1, n), (m + p, n)}
  obtain ⟨R₀, hR₀, han⟩ := ModularSector.bilateral_tail_joint_analytic M hM F τ
    (Real.pi / 8) hT hα hα'
  have hρ := ModularSector.parameterRadius_pos M hM τ (Real.pi / 8) hT hα hα'
  have hτ : (τ : ℂ) ∈ ModularSector.parameterDisk τ
      (ModularSector.parameterRadius M τ (Real.pi / 8)) :=
    Metric.mem_closedBall_self hρ.le
  obtain ⟨R, hR, hstrip⟩ := G1RatioTailBoundsAux.vertical_strip_sectors
    (min a b - |y|) (max a b + |y|) R₀ hR₀.le
  refine ⟨R, hR, ?_⟩
  intro t ht
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx' : min a b ≤ x ∧ x ≤ max a b := hx
  have hx₀ : x ∈ Icc (min a b - |y|) (max a b + |y|) := by
    constructor <;> linarith [abs_nonneg y]
  have hxy : x + y ∈ Icc (min a b - |y|) (max a b + |y|) := by
    constructor <;> linarith [neg_abs_le y, le_abs_self y]
  have hsec : ∀ u ∈ Icc (min a b - |y|) (max a b + |y|),
      g1VerticalPoint u t ∈ ModularSector.upperSector (Real.pi / 8) R₀ ∨
        -g1VerticalPoint u t ∈ ModularSector.upperSector (Real.pi / 8) R₀ := by
    intro u hu
    by_cases ht₀ : 0 ≤ t
    · exact Or.inl ((hstrip u hu t).1 (by simpa [abs_of_nonneg ht₀] using ht))
    · exact Or.inr ((hstrip u hu t).2 (by
        have := ht
        rw [abs_of_nonpos (le_of_not_ge ht₀)] at this
        linarith))
  have hn := (han (τ : ℂ) hτ (m + 1, n) (by simp [F])
    (g1VerticalPoint x t) (hsec x hx₀)).1.continuousAt
  have hd := (han (τ : ℂ) hτ (m + p, n) (by simp [F])
    (g1VerticalPoint (x + y) t) (hsec (x + y) hxy)).2.1.continuousAt
  have hpoint : g1VerticalPoint (x + y) t = g1VerticalPoint x t + (y : ℂ) := by
    simp [g1VerticalPoint, add_assoc, add_comm]
  rw [hpoint] at hd
  have hv : Continuous (fun x : ℝ => g1VerticalPoint x t) := by
    unfold g1VerticalPoint
    fun_prop
  have hnum : ContinuousAt (fun x : ℝ =>
      modularPhi M (m + 1) n (g1VerticalPoint x t) (τ : ℂ)) x :=
    hn.comp (f := fun u : ℝ => (g1VerticalPoint u t, (τ : ℂ)))
      (hv.continuousAt.prodMk continuousAt_const)
  have hden : ContinuousAt (fun x : ℝ =>
      (modularPhi M (m + p) n (g1VerticalPoint x t + (y : ℂ)) (τ : ℂ))⁻¹) x :=
    hd.comp (f := fun u : ℝ => (g1VerticalPoint u t + (y : ℂ), (τ : ℂ)))
      ((hv.continuousAt.add continuousAt_const).prodMk continuousAt_const)
  have hexp : ContinuousAt (fun x : ℝ =>
      e (g1Exponent M (τ : ℂ) (w : ℂ) (g1VerticalPoint x t) n h ell m)) x := by
    unfold e g1Exponent g1VerticalPoint
    fun_prop
  have hk : ContinuousAt (fun x : ℝ =>
      g1RatioKernel M τ w y n h ell p m (g1VerticalPoint x t)) x := by
    unfold g1RatioKernel
    simpa only [div_eq_mul_inv, Pi.mul_def] using (hnum.mul hden).mul hexp
  exact hk.continuousWithinAt

/-- The segment length is retained. Uniformly over nearby upper τ this bounds the integral, not just
its kernel. [RW26, p. 13]. -/
theorem uniform_horizontal_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (hs : 0 < g1S M τ₀ w h ell)
    (hL : g1L M τ₀ w y h ell p < 0) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.upperParameterDisk τ₀ ρ, ∀ m ∈ F,
        ∀ t : ℝ, R ≤ |t| →
          ‖horizontalIntegral (complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m) a b t‖ ≤
            |b - a| * C * Real.exp (-κ * |t|) := by
  obtain ⟨ρ, C, κ, R, hρ, hC, hκ, hR, hbound⟩ := uniform_two_tail_bound
    M hM τ₀ w y (min a b) (max a b) n h ell p F hT hs hL min_le_max
  refine ⟨ρ, C, κ, R, hρ, hC, hκ, hR, ?_⟩
  intro τ hτ m hm t ht
  calc
    _ ≤ (C * Real.exp (-κ * |t|)) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx =>
        hbound τ hτ m hm x ⟨hx.1.le, hx.2⟩ t ht)
    _ = _ := by ring

/-- Both closing edges tend to zero. [RW26, p. 7, p. 13]. -/
theorem horizontal_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y a b : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hs : 0 < g1S M τ w h ell) (hL : g1L M τ w y h ell p < 0) :
    Tendsto (fun R : ℝ => horizontalIntegral (g1RatioKernel M τ w y n h ell p m) a b R)
      atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ => horizontalIntegral (g1RatioKernel M τ w y n h ell p m) a b (-R))
      atTop (𝓝 0) := by
  obtain ⟨ρ, C, κ, R₀, hρ, hC, hκ, hR₀, hb⟩ :=
    uniform_horizontal_bound M hM τ w y a b n h ell p {m} hT hs hL
  have hτ := G1RatioTailBoundsAux.real_mem_upperParameterDisk τ ρ hρ.le
  have hb' := hb (τ : ℂ) hτ m (by simp)
  rw [complexKernel_real] at hb'
  have hlim : Tendsto (fun R : ℝ => |b - a| * C * Real.exp (-κ * R)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hκ))).const_mul (|b - a| * C)
  constructor
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (max R₀ 0)] with R hR
    have hR₀' : R₀ ≤ R := (le_max_left _ _).trans hR
    have hR' : 0 ≤ R := (le_max_right _ _).trans hR
    simpa only [abs_of_nonneg hR'] using hb' R (by simpa [abs_of_nonneg hR'] using hR₀')
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (max R₀ 0)] with R hR
    have hR₀' : R₀ ≤ R := (le_max_left _ _).trans hR
    have hR' : 0 ≤ R := (le_max_right _ _).trans hR
    simpa only [abs_neg, abs_of_nonneg hR'] using
      hb' (-R) (by simpa [abs_neg, abs_of_nonneg hR'] using hR₀')

/-- The strict exponential majorant is actually integrable. This is the tail input, never a
condition stored in a chain. [RW26, p. 7, p. 13]. -/
theorem exponential_majorant_integrable (C κ : ℝ) (hκ : 0 < κ) :
    Integrable (fun t : ℝ => C * Real.exp (-κ * |t|)) := by
  exact (integrable_real_exp_neg_abs hκ).const_mul C

#check @g1RatioKernel
#check @ModularSector.bounded_shift_ratio_decay
#check @G1Pinch.ratioData
#print complexKernel
#print complexS
#print complexL
#check @uniform_two_tail_bound
#check @horizontal_limits

end SICLean.L4.G1RatioTail
