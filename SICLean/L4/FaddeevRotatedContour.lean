import SICLean.L4.FaddeevRotatedIntegral
import SICLean.L4.FaddeevContinuation
import SICLean.L4.FaddeevRotatedContourAux

set_option autoImplicit false

/-!
Core contour and identity. The two exact endpoint connectors rotate exp(isθ)(±R+iv), s:0→1. Only a
small x-ball is used for the unbounded contour homotopy. The final strip identity is about the
existing phiExtended and its actual point values.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace SICLean.L4.Sector

def connectorPoint (θ v t s : ℝ) : ℂ := rotatedPoint (s * θ) v t

def connectorKernel (b x : ℂ) (θ v t s : ℝ) : ℂ :=
  kernel b x (connectorPoint θ v t s) *
    (Complex.I * (θ : ℂ) * connectorPoint θ v t s)

def connectorIntegral (b x : ℂ) (θ v t : ℝ) : ℂ :=
  ∫ s : ℝ in 0..1, connectorKernel b x θ v t s

theorem continuousOn_connectorKernel {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b : ℂ} (hb : b ∈ K) (x : ℂ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) (t : ℝ) :
    ContinuousOn (connectorKernel b x θ v t) (Icc 0 1) := by
  have hp : Continuous (connectorPoint θ v t) := by
    unfold connectorPoint rotatedPoint
    exact (continuous_rotation.comp (by fun_prop)).mul_const _
  intro s hs
  have hα := scaled_angle_mem (opening_pos hK).le hθ hs
  have hn := rotated_sinh_ne_zero hlam hv hb
    (admissibleB_ne_zero b (hK.admissible b hb)) hα t
  have hd : 4 * Complex.sinh (b * connectorPoint θ v t s) *
      Complex.sinh (b⁻¹ * connectorPoint θ v t s) * connectorPoint θ v t s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn.1) hn.2)
      (rotatedPoint_ne_zero _ _ _ hv.1)
  exact (((continuousAt_kernel_of_denominator_ne_zero b x _ hd).comp
    hp.continuousAt).mul (by fun_prop)).continuousWithinAt

theorem intervalIntegrable_connectorKernel {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b : ℂ} (hb : b ∈ K) (x : ℂ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) (t : ℝ) :
    IntervalIntegrable (connectorKernel b x θ v t) volume 0 1 := by
  exact (continuousOn_connectorKernel hK hlam hv hb x hθ t).intervalIntegrable_of_Icc
    (by norm_num)

theorem homotopy_avoids_poles {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (t s : ℝ) (hs : s ∈ Icc 0 1) :
    connectorPoint θ v t s ≠ 0 ∧
      Complex.sinh (b * connectorPoint θ v t s) ≠ 0 ∧
      Complex.sinh (b⁻¹ * connectorPoint θ v t s) ≠ 0 := by
  exact ⟨rotatedPoint_ne_zero _ _ _ hv.1,
    rotated_sinh_ne_zero hlam hv hb (admissibleB_ne_zero b (hK.admissible b hb))
      (scaled_angle_mem (opening_pos hK).le hθ hs) t⟩

/-- Endpoint +R: the arc length is already included in connectorKernel. -/
theorem exists_positive_connector_bound {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) :
    ∃ C R₀ : ℝ, 0 < C ∧ 0 < R₀ ∧ ∀ b ∈ K,
      ∀ θ ∈ Icc (-(opening β κ)) (opening β κ),
        ∀ x : ℂ, ‖x‖ ≤ lam / 4 → ∀ R : ℝ, R₀ ≤ R →
          ‖connectorIntegral b x θ v R‖ ≤ C * Real.exp (-lam * R) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_amplitude_exp_bound hK hlam hv
  let C := A * (opening β κ + 1) * (2 / lam + v) * Real.exp (lam / 2 * v)
  have hC : 0 < C := by
    have ho : 0 < opening β κ + 1 := by linarith [opening_pos hK]
    dsimp [C]
    positivity [hlam.1, hv.1]
  refine ⟨C, 1, hC, zero_lt_one, ?_⟩
  intro b hb θ hθ x hx R hR
  have hr : 0 ≤ R := by linarith
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (C := C * Real.exp (-lam * R))
    (f := connectorKernel b x θ v R) (fun s hs => by
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc hs
      simpa only [connectorKernel, connectorPoint, abs_of_nonneg hr] using
        connector_kernel_bound hK hlam hv hA hbound hb
          (scaled_angle_mem (opening_pos hK).le hθ hs') hθ hx R)
  simpa only [connectorIntegral, sub_zero, abs_one, mul_one] using he

/-- Endpoint -R is a separate bound, together with the other tail. -/
theorem exists_negative_connector_bound {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) :
    ∃ C R₀ : ℝ, 0 < C ∧ 0 < R₀ ∧ ∀ b ∈ K,
      ∀ θ ∈ Icc (-(opening β κ)) (opening β κ),
        ∀ x : ℂ, ‖x‖ ≤ lam / 4 → ∀ R : ℝ, R₀ ≤ R →
          ‖connectorIntegral b x θ v (-R)‖ ≤ C * Real.exp (-lam * R) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_amplitude_exp_bound hK hlam hv
  let C := A * (opening β κ + 1) * (2 / lam + v) * Real.exp (lam / 2 * v)
  have hC : 0 < C := by
    have ho : 0 < opening β κ + 1 := by linarith [opening_pos hK]
    dsimp [C]
    positivity [hlam.1, hv.1]
  refine ⟨C, 1, hC, zero_lt_one, ?_⟩
  intro b hb θ hθ x hx R hR
  have hr : 0 ≤ R := by linarith
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (C := C * Real.exp (-lam * R))
    (f := connectorKernel b x θ v (-R)) (fun s hs => by
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc hs
      simpa only [connectorKernel, connectorPoint, abs_neg, abs_of_nonneg hr] using
        connector_kernel_bound hK hlam hv hA hbound hb
          (scaled_angle_mem (opening_pos hK).le hθ hs') hθ hx (-R))
  simpa only [connectorIntegral, sub_zero, abs_one, mul_one] using he

theorem positive_connector_tendsto_zero {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) (hx : ‖x‖ < lam / 4) :
    Tendsto (fun R : ℝ => connectorIntegral b x θ v R) atTop (𝓝 0) := by
  obtain ⟨C, R₀, _, _, hbound⟩ := exists_positive_connector_bound hK hlam hv
  apply squeeze_zero_norm' (a := fun R : ℝ => C * Real.exp (-lam * R))
  · exact (eventually_ge_atTop R₀).mono (fun R hR => hbound b hb θ hθ x hx.le R hR)
  · simpa only [neg_mul, mul_zero, Function.comp_def, id_eq] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hlam.1)).const_mul C

theorem negative_connector_tendsto_zero {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) (hx : ‖x‖ < lam / 4) :
    Tendsto (fun R : ℝ => connectorIntegral b x θ v (-R)) atTop (𝓝 0) := by
  obtain ⟨C, R₀, _, _, hbound⟩ := exists_negative_connector_bound hK hlam hv
  apply squeeze_zero_norm' (a := fun R : ℝ => C * Real.exp (-lam * R))
  · exact (eventually_ge_atTop R₀).mono (fun R hR => hbound b hb θ hθ x hx.le R hR)
  · simpa only [neg_mul, mul_zero, Function.comp_def, id_eq] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hlam.1)).const_mul C

/-- Exact finite boundary identity, with oriented connector signs. -/
theorem finite_rotation_identity {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b : ℂ} (hb : b ∈ K) (x : ℂ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (R : ℝ) (hR : 0 < R) :
    (∫ t : ℝ in -R..R, rotatedKernel b x θ v t) =
      (∫ t : ℝ in -R..R, rotatedKernel b x 0 v t) +
        connectorIntegral b x θ v R - connectorIntegral b x θ v (-R) := by
  simpa only [rotatedKernel, connectorIntegral, connectorKernel, connectorPoint] using
    finite_rotation_of_differentiable (kernel b x) θ v R hR (by
      intro p hp
      have hs : p.1 ∈ Icc (0 : ℝ) 1 := ⟨hp.1.1, hp.2.1⟩
      have hn := homotopy_avoids_poles hK hlam hv hb hθ p.2 p.1 hs
      exact differentiableAt_kernel_of_denominator_ne_zero b x _
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn.2.1) hn.2.2) hn.1))

theorem rotatedLog_eq_logPhi_small {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) (hx : ‖x‖ < lam / 4) :
    rotatedLog b x θ v = logPhi b x := by
  have hzero : (0 : ℝ) ∈ Icc (-(opening β κ)) (opening β κ) :=
    ⟨by linarith [opening_pos hK], (opening_pos hK).le⟩
  have hxθ := small_mem_rotatedStrip hlam hb hθ hx
  have hxzero := small_mem_rotatedStrip hlam hb hzero hx
  have hxstrip : InStrip b x := by
    simpa only [rotatedStrip, rotatedRe, rotatedInvRe, rotation, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one, InStrip, stripWidth, mem_ofPred_eq] using hxzero
  have hlimθ := intervalIntegral_tendsto_integral
    (integrable_rotatedKernel hK hlam hv hb hθ hxθ)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hlimzero := intervalIntegral_tendsto_integral
    (integrable_rotatedKernel hK hlam hv hb hzero hxzero)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hlim := (hlimzero.add (positive_connector_tendsto_zero hK hlam hv hb hθ hx)).sub
    (negative_connector_tendsto_zero hK hlam hv hb hθ hx)
  have heq : (fun R : ℝ => ∫ t : ℝ in -R..R, rotatedKernel b x θ v t) =ᶠ[atTop]
      (fun R : ℝ => (∫ t : ℝ in -R..R, rotatedKernel b x 0 v t) +
        connectorIntegral b x θ v R - connectorIntegral b x θ v (-R)) := by
    exact (eventually_gt_atTop (0 : ℝ)).mono
      (fun R hR => finite_rotation_identity hK hlam hv hb x hθ R hR)
  have hlog : rotatedLog b x θ v = rotatedLog b x 0 v := by
    simpa only [add_zero, sub_zero, rotatedLog] using
      tendsto_nhds_unique hlimθ (hlim.congr' heq.symm)
  rw [hlog, rotatedLog_zero_angle]
  exact logPhiAtHeight_eq b x v (canonicalHeight b) (hK.admissible b hb) hxstrip
    (safe_height_admissible (opening_pos hK).le hlam hv hb)
    (canonicalHeight_admissible b (hK.admissible b hb))

theorem exp_rotatedLog_eq_phi_small {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ)) (hx : ‖x‖ < lam / 4) :
    Complex.exp (rotatedLog b x θ v) = phi b x := by
  rw [rotatedLog_eq_logPhi_small hK hlam hv hb hθ hx]
  rfl

/-- The rotated strip avoids both divisors of φ. This also checks center values. -/
theorem phi_divisor_free_rotatedStrip {K : Set ℂ} {β κ lam : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : x ∈ rotatedStrip b θ) :
    phiPoleMultiplicity b x = 0 ∧ phiZeroMultiplicity b x = 0 := by
  have hadm : AdmissibleB b := hK.admissible b hb
  have hr := hlam.2 b hb θ hθ
  have hbr : 0 ≤ rotatedRe b θ := le_trans hlam.1.le hr.1
  have hbir : 0 ≤ rotatedInvRe b θ := le_trans hlam.1.le hr.2
  have him (m n : ℕ) : (phiPolePoint b m n * rotation θ).im =
      (rotatedRe b θ + rotatedInvRe b θ) / 2 +
        (m : ℝ) * rotatedRe b θ + (n : ℝ) * rotatedInvRe b θ := by
    simp [phiPolePoint, rotatedRe, rotatedInvRe, Complex.mul_re, Complex.mul_im]
    ring
  have hge (m n : ℕ) : (rotatedRe b θ + rotatedInvRe b θ) / 2 ≤
      (phiPolePoint b m n * rotation θ).im := by
    rw [him]
    have hm := mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hbr
    have hn := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hbir
    linarith
  change |(x * rotation θ).im| < (rotatedRe b θ + rotatedInvRe b θ) / 2 at hx
  constructor
  · apply (phiPoleMultiplicity_eq_zero_iff b x hadm).mpr
    intro m n heq
    rw [heq] at hx
    exact (not_lt_of_ge ((hge m n).trans (le_abs_self _))) hx
  · apply (phiZeroMultiplicity_eq_zero_iff b x hadm).mpr
    intro m n heq
    rw [heq] at hx
    simp only [phiZeroPoint, neg_mul, Complex.neg_im, abs_neg] at hx
    exact (not_lt_of_ge ((hge m n).trans (le_abs_self _))) hx

/-- Identity theorem on the connected rotated strip, after the small-ball comparison. No convergence
of the original unrotated integral is asserted. -/
theorem exp_rotatedLog_eq_phiExtended {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : x ∈ rotatedStrip b θ) :
    Complex.exp (rotatedLog b x θ v) = phiExtended b x := by
  have hadm : AdmissibleB b := hK.admissible b hb
  have hf : AnalyticOnNhd ℂ (fun z => Complex.exp (rotatedLog b z θ v))
      (rotatedStrip b θ) :=
    ((differentiableOn_rotatedLog hK hlam hv hb hθ).analyticOnNhd
      (isOpen_rotatedStrip b θ)).cexp
  have hg : AnalyticOnNhd ℂ (phiExtended b) (rotatedStrip b θ) := by
    intro z hz
    exact phiExtended_analyticAt b z hadm
      (phi_divisor_free_rotatedStrip hK hlam hb hθ hz).1
  have hzero : InStrip b 0 := by
    have hb' : 0 < b.re := hadm
    have hi : 0 < (b⁻¹).re := admissibleB_inv b hadm
    simp only [InStrip, Complex.zero_im, abs_zero]
    unfold stripWidth
    positivity
  have hrad : 0 < lam / 4 := div_pos hlam.1 (by norm_num)
  have heq : (fun z => Complex.exp (rotatedLog b z θ v)) =ᶠ[𝓝 (0 : ℂ)]
      phiExtended b := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hrad,
      (isOpen_inStrip b).mem_nhds hzero] with z hz hzs
    have hzn : ‖z‖ < lam / 4 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact (exp_rotatedLog_eq_phi_small hK hlam hv hb hθ hzn).trans
      (phiExtended_eq_phi b z hadm hzs).symm
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (isPreconnected_rotatedStrip b θ) (zero_mem_rotatedStrip hlam hb hθ) heq hx

end SICLean.L4.Sector
