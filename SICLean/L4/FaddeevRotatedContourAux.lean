import SICLean.L4.FaddeevRotatedIntegral
import SICLean.L4.FaddeevContinuation

set_option autoImplicit false

/-!
Auxiliary angular geometry and uniform connector estimates for the rotated Faddeev contour.
Constants in the estimates are independent of the parameter, the angle, the small argument, and the
truncation length.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace SICLean.L4.Sector

lemma scaled_angle_mem {Θ θ s : ℝ} (hΘ : 0 ≤ Θ)
    (hθ : θ ∈ Icc (-Θ) Θ) (hs : s ∈ Icc 0 1) :
    s * θ ∈ Icc (-Θ) Θ := by
  constructor <;> nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hθ.1),
    mul_nonneg hs.1 (sub_nonneg.mpr hθ.2),
    mul_nonneg (sub_nonneg.mpr hs.2) hΘ]

lemma continuous_rotation : Continuous rotation := by
  unfold rotation
  fun_prop

lemma norm_linePoint_le (v t : ℝ) (hv : 0 ≤ v) :
    ‖linePoint v t‖ ≤ |t| + v := by
  simpa [linePoint, norm_mul, abs_of_nonneg hv] using
    norm_add_le (t : ℂ) (Complex.I * (v : ℂ))

lemma small_mem_rotatedStrip {K : Set ℂ} {Θ lam : ℝ}
    (hlam : UniformMargin K Θ lam) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) (hx : ‖x‖ < lam / 4) :
    x ∈ rotatedStrip b θ := by
  have hr := hlam.2 b hb θ hθ
  have hn : ‖x * rotation θ‖ = ‖x‖ := by simp [norm_rotation]
  have hi := Complex.abs_im_le_norm (x * rotation θ)
  change |(x * rotation θ).im| < (rotatedRe b θ + rotatedInvRe b θ) / 2
  rw [hn] at hi
  linarith [hlam.1]

lemma affine_mul_exp_neg_le {lam v r : ℝ} (hlam : 0 < lam)
    (hv : 0 ≤ v) (hr : 0 ≤ r) :
    (r + v) * Real.exp (-(lam / 2 * r)) ≤ 2 / lam + v := by
  have he : Real.exp (-(lam / 2 * r)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (half_pos hlam).le hr))
  have hmul := Real.mul_exp_neg_le_exp_neg_one (lam / 2 * r)
  have h1 : Real.exp (-1 : ℝ) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hrbound : r * Real.exp (-(lam / 2 * r)) ≤ 2 / lam := by
    apply (le_div_iff₀ hlam).mpr
    nlinarith
  calc
    (r + v) * Real.exp (-(lam / 2 * r)) =
        r * Real.exp (-(lam / 2 * r)) + v * Real.exp (-(lam / 2 * r)) := by ring
    _ ≤ 2 / lam + v := add_le_add hrbound (mul_le_of_le_one_right hv he)

lemma connector_kernel_bound {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ b ∈ K, ∀ α ∈ Icc (-(opening β κ)) (opening β κ),
      ∀ t : ℝ, ‖amplitude b α v t‖ ≤ expMajorant C lam t)
    {b x : ℂ} (hb : b ∈ K) {α θ : ℝ}
    (hα : α ∈ Icc (-(opening β κ)) (opening β κ))
    (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : ‖x‖ ≤ lam / 4) (t : ℝ) :
    ‖kernel b x (rotatedPoint α v t) *
      (Complex.I * (θ : ℂ) * rotatedPoint α v t)‖ ≤
      (C * (opening β κ + 1) * (2 / lam + v) * Real.exp (lam / 2 * v)) *
        Real.exp (-lam * |t|) := by
  have hxrot : ‖x * rotation α‖ ≤ lam / 4 := by
    simpa [norm_mul, norm_rotation] using hx
  have hxim : |(x * rotation α).im| ≤ lam / 4 :=
    (Complex.abs_im_le_norm _).trans hxrot
  have hxre : (x * rotation α).re ≤ lam / 4 :=
    (Complex.re_le_norm _).trans hxrot
  have he : ‖Complex.exp (-2 * Complex.I * x * rotatedPoint α v t)‖ ≤
      Real.exp (lam / 2 * (|t| + v)) := by
    refine (norm_rotated_exponential_le x α v t).trans (Real.exp_le_exp.mpr ?_)
    nlinarith [mul_le_mul_of_nonneg_right hxim (abs_nonneg t),
      mul_le_mul_of_nonneg_right hxre hv.1.le]
  have hθabs : |θ| ≤ opening β κ + 1 := by
    have h := abs_le.mpr hθ
    linarith
  have hpoint := norm_linePoint_le v t hv.1.le
  have hpoly := affine_mul_exp_neg_le hlam.1 hv.1.le (abs_nonneg t)
  calc
    ‖kernel b x (rotatedPoint α v t) *
        (Complex.I * (θ : ℂ) * rotatedPoint α v t)‖ =
        ‖Complex.exp (-2 * Complex.I * x * rotatedPoint α v t)‖ *
          ‖amplitude b α v t‖ * (|θ| * ‖linePoint v t‖) := by
      have hid : kernel b x (rotatedPoint α v t) *
          (Complex.I * (θ : ℂ) * rotatedPoint α v t) =
          rotatedKernel b x α v t * (Complex.I * (θ : ℂ) * linePoint v t) := by
        unfold rotatedKernel rotatedPoint
        ring
      rw [hid, rotatedKernel_eq]
      simp
    _ ≤ Real.exp (lam / 2 * (|t| + v)) *
        (C * Real.exp (-2 * lam * |t|)) *
          ((opening β κ + 1) * (|t| + v)) := by
      apply mul_le_mul
      · exact mul_le_mul he (hbound b hb α hα t) (norm_nonneg _) (Real.exp_pos _).le
      · exact mul_le_mul hθabs hpoint (norm_nonneg _) (by linarith [opening_pos hK])
      · positivity
      · positivity
    _ = C * (opening β κ + 1) * Real.exp (lam / 2 * v) *
          ((|t| + v) * Real.exp (-(lam / 2 * |t|))) *
          Real.exp (-lam * |t|) := by
      have heq : Real.exp (lam / 2 * (|t| + v)) * Real.exp (-2 * lam * |t|) =
          Real.exp (lam / 2 * v) * Real.exp (-(lam / 2 * |t|)) *
            Real.exp (-lam * |t|) := by
        simp only [← Real.exp_add]
        congr 1
        ring
      calc
        _ = C * (opening β κ + 1) * (|t| + v) *
            (Real.exp (lam / 2 * (|t| + v)) * Real.exp (-2 * lam * |t|)) := by ring
        _ = _ := by rw [heq]; ring
    _ ≤ (C * (opening β κ + 1) * (2 / lam + v) * Real.exp (lam / 2 * v)) *
          Real.exp (-lam * |t|) := by
      have hc : 0 ≤ C * (opening β κ + 1) * Real.exp (lam / 2 * v) := by
        exact mul_nonneg (mul_nonneg hC.le (by linarith [opening_pos hK]))
          (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left hpoly hc,
        mul_nonneg (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hpoly hc))
          (Real.exp_pos (-lam * |t|)).le]

/-- Green's formula for the explicit rotation homotopy. The two mixed derivatives cancel, including
the derivative of the rotation Jacobian. -/
theorem finite_rotation_of_differentiable
    (f : ℂ → ℂ) (θ v R : ℝ) (hR : 0 < R)
    (hf : ∀ p ∈ Icc ((0 : ℝ), -R) ((1 : ℝ), R),
      DifferentiableAt ℂ f (rotatedPoint (p.1 * θ) v p.2)) :
    (∫ t : ℝ in -R..R, f (rotatedPoint θ v t) * rotation θ) =
      (∫ t : ℝ in -R..R, f (rotatedPoint 0 v t) * rotation 0) +
        (∫ s : ℝ in 0..1, f (rotatedPoint (s * θ) v R) *
          (I * (θ : ℂ) * rotatedPoint (s * θ) v R)) -
        (∫ s : ℝ in 0..1, f (rotatedPoint (s * θ) v (-R)) *
          (I * (θ : ℂ) * rotatedPoint (s * θ) v (-R))) := by
  let L₁ : ℝ × ℝ →L[ℝ] ℂ :=
    Complex.ofRealCLM ∘L ContinuousLinearMap.fst ℝ ℝ ℝ
  let L₂ : ℝ × ℝ →L[ℝ] ℂ :=
    Complex.ofRealCLM ∘L ContinuousLinearMap.snd ℝ ℝ ℝ
  let c : ℂ := I * (θ : ℂ)
  let ρ : ℝ × ℝ → ℂ := fun p => rotation (p.1 * θ)
  let H : ℝ × ℝ → ℂ := fun p => rotatedPoint (p.1 * θ) v p.2
  let dρ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => (c * ρ p) • L₁
  let dH : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    ρ p • L₂ + (c * H p) • L₁
  have hρ (p : ℝ × ℝ) : HasFDerivAt ρ (dρ p) p := by
    simpa [ρ, rotation, c, dρ, L₁, smul_smul, Complex.ofReal_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      ((L₁.hasFDerivAt (x := p)).const_mul c).cexp
  have hH (p : ℝ × ℝ) : HasFDerivAt H (dH p) p := by
    have hz : HasFDerivAt (fun p : ℝ × ℝ => linePoint v p.2) L₂ p := by
      simpa [L₂, linePoint] using L₂.hasFDerivAt.add_const (I * (v : ℂ))
    apply ((hρ p).mul hz).congr_fderiv
    apply ContinuousLinearMap.ext
    intro q
    simp [dH, dρ, L₁, L₂, H, ρ, rotatedPoint, smul_eq_mul]
    ring
  let df : ℝ × ℝ → ℂ := fun p => deriv f (H p)
  let A : ℝ × ℝ → ℂ := fun p => f (H p) * ρ p
  let G : ℝ × ℝ → ℂ := fun p => -(f (H p) * (c * H p))
  let dA : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    f (H p) • dρ p + ρ p • (df p • dH p)
  let dG : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    -(f (H p) • (c • dH p) + (c * H p) • (df p • dH p))
  have hfc : ContinuousOn (fun p => f (H p)) (Icc ((0 : ℝ), -R) ((1 : ℝ), R)) := by
    intro p hp
    have hfp : ContinuousAt f (H p) := (hf p hp).continuousAt
    exact (hfp.comp (hH p).continuousAt).continuousWithinAt
  have hAc : ContinuousOn A (Icc ((0 : ℝ), -R) ((1 : ℝ), R)) :=
    hfc.mul (fun p _ => (hρ p).continuousAt.continuousWithinAt)
  have hGc : ContinuousOn G (Icc ((0 : ℝ), -R) ((1 : ℝ), R)) :=
    (hfc.mul (continuousOn_const.mul (fun p _ => (hH p).continuousAt.continuousWithinAt))).neg
  have hderiv (p : ℝ × ℝ) (hp : p ∈ Icc ((0 : ℝ), -R) ((1 : ℝ), R)) :
      HasFDerivAt (fun p => f (H p)) (df p • dH p) p :=
    (hf p hp).hasDerivAt.comp_hasFDerivAt p (hH p)
  have hAd (p : ℝ × ℝ) (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-R) R) :
      HasFDerivAt A (dA p) p := by
    exact (hderiv p ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩).mul (hρ p)
  have hGd (p : ℝ × ℝ) (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-R) R) :
      HasFDerivAt G (dG p) p := by
    exact ((hderiv p ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩).mul
      ((hH p).const_mul c)).neg
  have hzero (p : ℝ × ℝ) : dA p (1, 0) + dG p (0, 1) = 0 := by
    simp [dA, dG, dρ, dH, L₁, L₂, smul_eq_mul]
    ring
  have hi : IntegrableOn (fun p => dA p (1, 0) + dG p (0, 1))
      (Icc ((0 : ℝ), -R) ((1 : ℝ), R)) := by
    simp_rw [hzero]
    exact integrableOn_zero
  have hgreen := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    A G dA dG ((0 : ℝ), -R) ((1 : ℝ), R) ⟨by norm_num, by linarith⟩
    hAc hGc hAd hGd hi
  simp only [hzero, integral_zero, A, G, H, ρ, c,
    zero_mul, one_mul, intervalIntegral.integral_neg] at hgreen
  linear_combination -hgreen

end SICLean.L4.Sector
