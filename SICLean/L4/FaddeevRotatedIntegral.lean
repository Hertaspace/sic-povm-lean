import SICLean.L4.FaddeevRotatedIntegralAux

set_option autoImplicit false

/-!
# Rotated integrals

A positive separation is kept on local parameter families. The total integral below is only
interpreted under the stated strip conditions. No equality with the continuation is assumed in this
module.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4.Sector

def rotatedStrip (b : ℂ) (θ : ℝ) : Set ℂ :=
  {x | |(x * rotation θ).im| < (rotatedRe b θ + rotatedInvRe b θ) / 2}

def stripGap (b x : ℂ) (θ : ℝ) : ℝ :=
  rotatedRe b θ + rotatedInvRe b θ - 2 * |(x * rotation θ).im|

def rotatedLog (b x : ℂ) (θ v : ℝ) : ℂ :=
  ∫ t : ℝ, rotatedKernel b x θ v t

def rotatedDerivativeKernel (b x : ℂ) (θ v t : ℝ) : ℂ :=
  (-2 * Complex.I * rotatedPoint θ v t) * rotatedKernel b x θ v t

theorem zero_mem_rotatedStrip {K : Set ℂ} {Θ lam : ℝ}
    (hlam : UniformMargin K Θ lam) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) : 0 ∈ rotatedStrip b θ := by
  have h := hlam.2 b hb θ hθ
  change |((0 : ℂ) * rotation θ).im| < _
  simp only [zero_mul, zero_im, abs_zero]
  linarith [hlam.1]

theorem isOpen_rotatedStrip (b : ℂ) (θ : ℝ) : IsOpen (rotatedStrip b θ) := by
  exact isOpen_lt (Complex.continuous_im.comp
    (continuous_id.mul continuous_const)).abs continuous_const

theorem convex_rotatedStrip (b : ℂ) (θ : ℝ) :
    Convex ℝ (rotatedStrip b θ) := by
  let f : ℂ →ₗ[ℝ] ℝ := Complex.imCLM.toLinearMap.comp
    (LinearMap.mul ℝ ℂ (rotation θ))
  have h := (convex_Ioo (-(rotatedRe b θ + rotatedInvRe b θ) / 2)
    ((rotatedRe b θ + rotatedInvRe b θ) / 2)).linear_preimage f
  have hs : rotatedStrip b θ = f ⁻¹' Ioo (-(rotatedRe b θ + rotatedInvRe b θ) / 2)
      ((rotatedRe b θ + rotatedInvRe b θ) / 2) := by
    ext x
    change |(x * rotation θ).im| < _ ↔
      -(rotatedRe b θ + rotatedInvRe b θ) / 2 < (rotation θ * x).im ∧
        (rotation θ * x).im < (rotatedRe b θ + rotatedInvRe b θ) / 2
    rw [mul_comm (rotation θ), abs_lt]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  rw [hs]
  exact h

theorem isPreconnected_rotatedStrip (b : ℂ) (θ : ℝ) :
    IsPreconnected (rotatedStrip b θ) := by
  exact (convex_rotatedStrip b θ).isPreconnected

theorem continuous_rotatedKernel {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b : ℂ} (hb : b ∈ K) (x : ℂ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) :
    Continuous (rotatedKernel b x θ v) := by
  have hd (t : ℝ) := rotatedDenominator_ne_zero hlam hv hb
    (admissibleB_ne_zero b (hK.admissible b hb)) hθ t
  change Continuous (fun t => rotatedKernel b x θ v t)
  simp_rw [rotatedKernel_eq, amplitude]
  apply Continuous.mul
  · unfold rotatedPoint linePoint
    fun_prop
  · apply Continuous.inv₀
    · unfold rotatedDenominator rotatedPoint linePoint
      fun_prop
    · exact hd

theorem integrable_rotatedKernel {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : x ∈ rotatedStrip b θ) : Integrable (rotatedKernel b x θ v) := by
  change Integrable (fun t => rotatedKernel b x θ v t)
  simp_rw [rotatedKernel_eq_twoSinhKernel]
  apply integrable_twoSinhKernel
  · exact hlam.1.trans_le (hlam.2 b hb θ hθ).1
  · exact hlam.1.trans_le (hlam.2 b hb θ hθ).2
  · change |(x * rotation θ).im| < _ at hx
    change 2 * |(x * rotation θ).im| < rotatedRe b θ + rotatedInvRe b θ
    linarith
  · intro t
    simpa only [rotatedDenominator, rotatedPoint, mul_assoc] using
      rotatedDenominator_ne_zero hlam hv hb
        (admissibleB_ne_zero b (hK.admissible b hb)) hθ t

theorem norm_rotated_exponential_le (x : ℂ) (θ v t : ℝ) :
    ‖Complex.exp (-2 * Complex.I * x * rotatedPoint θ v t)‖ ≤
      Real.exp (2 * |(x * rotation θ).im| * |t| + 2 * (x * rotation θ).re * v) := by
  simpa only [rotatedPoint, linePoint, mul_assoc] using
    norm_exp_line_le (x * rotation θ) v t

/-- This is a common pointwise L¹ bound on each strictly smaller strip. -/
theorem exists_uniform_rotatedKernel_majorant {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    ∃ B : ℝ → ℝ, Integrable B ∧ (∀ t : ℝ, 0 ≤ B t) ∧
      ∀ b ∈ K, ∀ θ ∈ Icc (-(opening β κ)) (opening β κ),
        ∀ x : ℂ, |(x * rotation θ).re| ≤ M → δ ≤ stripGap b x θ →
          ∀ t : ℝ, ‖rotatedKernel b x θ v t‖ ≤ B t := by
  obtain ⟨N, hN, hNb⟩ := exists_uniform_parameter_norm_bound hK
  obtain ⟨P, hP, hPb⟩ := exists_uniform_im_bound hK
  obtain ⟨R, hR, hRt⟩ := exists_tail_threshold lam v P hlam.1
  obtain ⟨B₀, hB₀, hB₀pos, hB₀bound⟩ := exists_uniform_amplitude_majorant hK hlam hv
  let D := Real.exp (2 * N * R + 2 * M * v)
  let A := 4 * Real.exp ((2 * M + P + P) * |v|)
  have hD : 0 ≤ D := Real.exp_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨fun t => D * B₀ t + A * Real.exp (-δ * |t|),
    (hB₀.const_mul D).add ((integrable_real_exp_neg_abs hδ).const_mul A),
    fun t => add_nonneg (mul_nonneg hD (hB₀pos t)) (by positivity), ?_⟩
  intro b hb θ hθ x hxM hxδ t
  by_cases ht : R ≤ |t|
  · have htail : ‖rotatedKernel b x θ v t‖ ≤ A * Real.exp (-δ * |t|) := by
      rw [rotatedKernel_eq_twoSinhKernel]
      exact norm_exp_div_sinh_product_line_mul_le_uniform_parameters
        (b * rotation θ) (b⁻¹ * rotation θ) (x * rotation θ) v t
        lam lam P P M δ hlam.1 hlam.1
        (hlam.2 b hb θ hθ).1 (hlam.2 b hb θ hθ).2
        (hPb b hb θ).1 (hPb b hb θ).2 hxM hxδ (hR.trans ht)
        (by simpa [abs_of_pos hv.1, mul_comm P v] using hRt t ht)
        (by simpa [abs_of_pos hv.1, mul_comm P v] using hRt t ht)
    exact htail.trans (le_add_of_nonneg_left (mul_nonneg hD (hB₀pos t)))
  · have htR : |t| ≤ R := (lt_of_not_ge ht).le
    have hre : rotatedRe b θ ≤ N := by
      exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
        (by simpa [norm_mul, norm_rotation] using (hNb b hb).1))
    have hinvre : rotatedInvRe b θ ≤ N := by
      exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
        (by simpa [norm_mul, norm_rotation] using (hNb b hb).2))
    have hxim : |(x * rotation θ).im| ≤ N := by
      dsimp [stripGap] at hxδ
      linarith
    have hxe : (x * rotation θ).re ≤ M := (le_abs_self _).trans hxM
    have he : ‖Complex.exp (-2 * Complex.I * x * rotatedPoint θ v t)‖ ≤ D := by
      apply (norm_rotated_exponential_le x θ v t).trans
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul hxim htR (abs_nonneg t) hN
      have hv' := mul_le_mul_of_nonneg_right hxe hv.1.le
      linarith
    calc
      ‖rotatedKernel b x θ v t‖ =
          ‖Complex.exp (-2 * Complex.I * x * rotatedPoint θ v t)‖ *
            ‖amplitude b θ v t‖ := by rw [rotatedKernel_eq, norm_mul]
      _ ≤ D * B₀ t := mul_le_mul he (hB₀bound b hb θ hθ t) (norm_nonneg _) hD
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

theorem integrable_rotatedDerivativeKernel {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : x ∈ rotatedStrip b θ) :
    Integrable (rotatedDerivativeKernel b x θ v) := by
  have hi := integrable_twoSinhDerivative (b * rotation θ) (b⁻¹ * rotation θ)
    (x * rotation θ) v
    (hlam.1.trans_le (hlam.2 b hb θ hθ).1)
    (hlam.1.trans_le (hlam.2 b hb θ hθ).2)
    (show 2 * |(x * rotation θ).im| < (b * rotation θ).re + (b⁻¹ * rotation θ).re by
      change |(x * rotation θ).im| < _ at hx
      change 2 * |(x * rotation θ).im| < rotatedRe b θ + rotatedInvRe b θ
      linarith)
    (fun t => by
      simpa only [rotatedDenominator, rotatedPoint, mul_assoc] using
        rotatedDenominator_ne_zero hlam hv hb
          (admissibleB_ne_zero b (hK.admissible b hb)) hθ t)
  convert hi.const_mul (rotation θ) using 1
  ext t
  simp only [rotatedDerivativeKernel, twoSinhDerivative, rotatedKernel_eq_twoSinhKernel,
    rotatedPoint]
  ring

theorem differentiableOn_rotatedLog {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) :
    DifferentiableOn ℂ (fun x => rotatedLog b x θ v) (rotatedStrip b θ) := by
  intro x hx
  have hx' : 2 * |(x * rotation θ).im| < rotatedRe b θ + rotatedInvRe b θ := by
    change |(x * rotation θ).im| < _ at hx
    linarith
  exact (hasDerivAt_rotatedIntegral_aux hK hlam hv hb hθ hx').differentiableAt.differentiableWithinAt

theorem hasDerivAt_rotatedLog {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : x ∈ rotatedStrip b θ) :
    HasDerivAt (fun z => rotatedLog b z θ v)
      (∫ t : ℝ, rotatedDerivativeKernel b x θ v t) x := by
  apply hasDerivAt_rotatedIntegral_aux hK hlam hv hb hθ
  change |(x * rotation θ).im| < _ at hx
  linarith

theorem rotatedLog_zero_angle (b x : ℂ) (v : ℝ) :
    rotatedLog b x 0 v = logPhiAtHeight b x v := by
  simp [rotatedLog, logPhiAtHeight, rotatedKernel, rotatedPoint, rotation]

end SICLean.L4.Sector
