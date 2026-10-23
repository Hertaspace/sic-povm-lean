import SICLean.L4.FaddeevRotatedContour

set_option autoImplicit false

/-!
Constants are outside b and x quantifiers. The function and its inverse refer to the same existing
phiExtended.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4.Sector

def InDecaySector (β κ : ℝ) (x : ℂ) : Prop :=
  1 ≤ ‖x‖ ∧ |(-x).arg| ≤ opening β κ

theorem exists_aligning_angle (x : ℂ) (Θ : ℝ) (hx : x ≠ 0)
    (hΘ : 0 ≤ Θ) (harg : |(-x).arg| ≤ Θ) :
    ∃ θ ∈ Icc (-Θ) Θ, x * rotation θ = -(‖x‖ : ℂ) := by
  let b : ℝ := (-x).arg
  have hb_le : |b| ≤ Θ := harg
  have hb1 : -Θ ≤ b := (abs_le.mp hb_le).1
  have hb2 : b ≤ Θ := (abs_le.mp hb_le).2
  refine ⟨-b, ⟨by linarith, by linarith⟩, ?_⟩
  have hxnorm : ((‖x‖ : ℝ) : ℂ) * Complex.exp ((b : ℂ) * Complex.I) = -x := by
    simpa [b] using Complex.norm_mul_exp_arg_mul_I (-x)
  have hmul : ((‖x‖ : ℝ) : ℂ) = (-x) * Complex.exp (-(b : ℂ) * Complex.I) := by
    calc
      ((‖x‖ : ℝ) : ℂ)
          = (((‖x‖ : ℝ) : ℂ) * Complex.exp ((b : ℂ) * Complex.I)) *
              Complex.exp (-(b : ℂ) * Complex.I) := by
            rw [mul_assoc, ← Complex.exp_add]
            simp
      _ = (-x) * Complex.exp (-(b : ℂ) * Complex.I) := by rw [hxnorm]
  have hfinal : x * Complex.exp (-(b : ℂ) * Complex.I) = -(‖x‖ : ℂ) := by
    have hneg := congrArg Neg.neg hmul
    rw [neg_mul, neg_neg] at hneg
    exact hneg.symm
  have hrot : Complex.exp (-(b : ℂ) * Complex.I) = rotation (-b) := by
    rw [rotation]
    congr 1
    push_cast
    ring
  rw [hrot] at hfinal
  exact hfinal

theorem aligned_mem_rotatedStrip {K : Set ℂ} {Θ lam : ℝ}
    (hlam : UniformMargin K Θ lam) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ)
    (hx : x * rotation θ = -(‖x‖ : ℂ)) : x ∈ rotatedStrip b θ := by
  have hsum_pos : 0 < (rotatedRe b θ + rotatedInvRe b θ) / 2 := by
    have hb' := hlam.2 b hb θ hθ
    have hlampos := hlam.1
    linarith [hb'.1, hb'.2]
  have him : (x * rotation θ).im = 0 := by
    rw [hx]
    simp
  simp only [rotatedStrip, Set.mem_ofPred_eq]
  rw [him, abs_zero]
  exact hsum_pos

theorem norm_exponential_aligned (x : ℂ) (θ v t : ℝ)
    (hx : x * rotation θ = -(‖x‖ : ℂ)) :
    ‖Complex.exp (-2 * Complex.I * x * rotatedPoint θ v t)‖ =
      Real.exp (-2 * v * ‖x‖) := by
  rw [Complex.norm_exp]
  congr 1
  have hw : x * rotatedPoint θ v t = -(‖x‖ : ℂ) * linePoint v t := by
    rw [rotatedPoint, ← mul_assoc, hx]
  have hz : -2 * Complex.I * x * rotatedPoint θ v t =
      (-2 * Complex.I) * (x * rotatedPoint θ v t) := by ring
  have hIre : (-2 * Complex.I : ℂ).re = 0 := by simp
  have hIim : (-2 * Complex.I : ℂ).im = -2 := by simp
  have him : (x * rotatedPoint θ v t).im = -(‖x‖ * v) := by
    rw [hw]
    simp [linePoint, Complex.mul_im, Complex.mul_re]
  rw [hz, Complex.mul_re, hIre, hIim, him]
  ring

theorem norm_rotatedKernel_aligned (b x : ℂ) (θ v t : ℝ)
    (hx : x * rotation θ = -(‖x‖ : ℂ)) :
    ‖rotatedKernel b x θ v t‖ =
      Real.exp (-2 * v * ‖x‖) * ‖amplitude b θ v t‖ := by
  rw [rotatedKernel_eq, norm_mul, norm_exponential_aligned x θ v t hx]

theorem norm_rotatedLog_aligned_le_integral {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : x * rotation θ = -(‖x‖ : ℂ)) :
    ‖rotatedLog b x θ v‖ ≤
      (∫ t : ℝ, ‖amplitude b θ v t‖) * Real.exp (-2 * v * ‖x‖) := by
  have h1 : ‖rotatedLog b x θ v‖ ≤ ∫ t : ℝ, ‖rotatedKernel b x θ v t‖ := by
    simpa [rotatedLog] using
      (norm_integral_le_integral_norm (fun t : ℝ => rotatedKernel b x θ v t))
  have h2 : (∫ t : ℝ, ‖rotatedKernel b x θ v t‖) =
      Real.exp (-2 * v * ‖x‖) * ∫ t : ℝ, ‖amplitude b θ v t‖ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun t => norm_rotatedKernel_aligned b x θ v t hx))
  calc
    ‖rotatedLog b x θ v‖ ≤ ∫ t : ℝ, ‖rotatedKernel b x θ v t‖ := h1
    _ = Real.exp (-2 * v * ‖x‖) * ∫ t : ℝ, ‖amplitude b θ v t‖ := h2
    _ = (∫ t : ℝ, ‖amplitude b θ v t‖) * Real.exp (-2 * v * ‖x‖) := by ring

theorem norm_rotatedLog_aligned_le {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : x * rotation θ = -(‖x‖ : ℂ)) (C₀ : ℝ)
    (hC₀ : (∫ t : ℝ, ‖amplitude b θ v t‖) ≤ C₀) :
    ‖rotatedLog b x θ v‖ ≤ C₀ * Real.exp (-2 * v * ‖x‖) := by
  calc
    ‖rotatedLog b x θ v‖ ≤
        (∫ t : ℝ, ‖amplitude b θ v t‖) * Real.exp (-2 * v * ‖x‖) :=
      norm_rotatedLog_aligned_le_integral hK hlam hv hb hθ hx
    _ ≤ C₀ * Real.exp (-2 * v * ‖x‖) := by
      exact mul_le_mul_of_nonneg_right hC₀ (Real.exp_nonneg _)

theorem norm_exp_sub_one_le_scaled (L : ℂ) (C₀ v r : ℝ)
    (hC₀ : 0 ≤ C₀) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (hL : ‖L‖ ≤ C₀ * Real.exp (-2 * v * r)) :
    ‖Complex.exp L - 1‖ ≤ C₀ * Real.exp C₀ * Real.exp (-2 * v * r) := by
  have hexp_le_one : Real.exp (-2 * v * r) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hLC : ‖L‖ ≤ C₀ := by
    have h := mul_le_mul_of_nonneg_left hexp_le_one hC₀
    linarith
  have hbasic := Complex.norm_exp_sub_sum_le_norm_mul_exp L 1
  have hbasic' : ‖Complex.exp L - 1‖ ≤ ‖L‖ * Real.exp ‖L‖ := by
    simpa using hbasic
  calc
    ‖Complex.exp L - 1‖ ≤ ‖L‖ * Real.exp ‖L‖ := hbasic'
    _ ≤ (C₀ * Real.exp (-2 * v * r)) * Real.exp C₀ := by
      gcongr
    _ = C₀ * Real.exp C₀ * Real.exp (-2 * v * r) := by ring

theorem norm_inv_exp_sub_one_le_scaled (L : ℂ) (C₀ v r : ℝ)
    (hC₀ : 0 ≤ C₀) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (hL : ‖L‖ ≤ C₀ * Real.exp (-2 * v * r)) :
    ‖(Complex.exp L)⁻¹ - 1‖ ≤ C₀ * Real.exp C₀ * Real.exp (-2 * v * r) := by
  have hneg : ‖-L‖ ≤ C₀ * Real.exp (-2 * v * r) := by simpa using hL
  have h := norm_exp_sub_one_le_scaled (-L) C₀ v r hC₀ hv hr hneg
  rwa [Complex.exp_neg] at h

theorem phiExtended_regular_in_sector {K : Set ℂ} {β κ : ℝ}
    (hK : Family K β κ) {b x : ℂ} (hb : b ∈ K) (hx : InDecaySector β κ x) :
    AnalyticAt ℂ (phiExtended b) x ∧ phiExtended b x ≠ 0 := by
  obtain ⟨hr, harg⟩ := hx
  have hxne : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hr
    linarith
  obtain ⟨lam, hlam⟩ := exists_uniform_margin hK
  have hΘ : 0 ≤ opening β κ := le_of_lt (opening_pos hK)
  obtain ⟨θ, hθ, halign⟩ := exists_aligning_angle x (opening β κ) hxne hΘ harg
  have hstrip : x ∈ rotatedStrip b θ := aligned_mem_rotatedStrip hlam hb hθ halign
  obtain ⟨hpole, hzero⟩ := phi_divisor_free_rotatedStrip hK hlam hb hθ hstrip
  have hbAdm : AdmissibleB b := hK.admissible b hb
  exact ⟨phiExtended_analyticAt b x hbAdm hpole,
    (phiExtended_ne_zero_iff b x hbAdm hpole).mpr hzero⟩

theorem phiExtended_sector_decay_with_margin {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ x : ℂ, InDecaySector β κ x →
      ‖phiExtended b x - 1‖ + ‖(phiExtended b x)⁻¹ - 1‖ ≤
        C * Real.exp (-2 * v * ‖x‖) := by
  obtain ⟨C₀, hC₀, hL1⟩ := exists_uniform_l1_bound hK hlam hv
  refine ⟨2 * (C₀ * Real.exp C₀), ?_, ?_⟩
  · have := Real.exp_pos C₀
    positivity
  intro b hb x hx
  obtain ⟨hr, harg⟩ := hx
  have hxne : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hr
    linarith
  have hΘ : 0 ≤ opening β κ := le_of_lt (opening_pos hK)
  obtain ⟨θ, hθ, halign⟩ := exists_aligning_angle x (opening β κ) hxne hΘ harg
  have hstrip : x ∈ rotatedStrip b θ := aligned_mem_rotatedStrip hlam hb hθ halign
  have hexp : Complex.exp (rotatedLog b x θ v) = phiExtended b x :=
    exp_rotatedLog_eq_phiExtended hK hlam hv hb hθ hstrip
  have hbound : ‖rotatedLog b x θ v‖ ≤ C₀ * Real.exp (-2 * v * ‖x‖) :=
    norm_rotatedLog_aligned_le hK hlam hv hb hθ halign C₀ (hL1 b hb θ hθ)
  have hone := norm_exp_sub_one_le_scaled (rotatedLog b x θ v) C₀ v ‖x‖
    hC₀.le hv.1.le (norm_nonneg x) hbound
  have hinv := norm_inv_exp_sub_one_le_scaled (rotatedLog b x θ v) C₀ v ‖x‖
    hC₀.le hv.1.le (norm_nonneg x) hbound
  rw [hexp] at hone hinv
  calc
    ‖phiExtended b x - 1‖ + ‖(phiExtended b x)⁻¹ - 1‖
        ≤ C₀ * Real.exp C₀ * Real.exp (-2 * v * ‖x‖) +
            C₀ * Real.exp C₀ * Real.exp (-2 * v * ‖x‖) := add_le_add hone hinv
    _ = (2 * (C₀ * Real.exp C₀)) * Real.exp (-2 * v * ‖x‖) := by ring

theorem phiExtended_uniform_sector_decay {K : Set ℂ} {β κ : ℝ}
    (hK : Family K β κ) :
    ∃ C v : ℝ, 0 < C ∧ 0 < v ∧ ∀ b ∈ K,
      ∀ x : ℂ, InDecaySector β κ x →
        ‖phiExtended b x - 1‖ + ‖(phiExtended b x)⁻¹ - 1‖ ≤
          C * Real.exp (-2 * v * ‖x‖) := by
  obtain ⟨lam, hlam⟩ := exists_uniform_margin hK
  obtain ⟨v, hv⟩ := exists_safe_height hlam.1
  obtain ⟨C, hC, hdec⟩ := phiExtended_sector_decay_with_margin hK hlam hv
  exact ⟨C, v, hC, hv.1, hdec⟩

theorem phiExtended_uniform_sector_limit {K : Set ℂ} {β κ : ℝ}
    (hK : Family K β κ) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ b ∈ K,
      ∀ x : ℂ, InDecaySector β κ x → R ≤ ‖x‖ →
        ‖phiExtended b x - 1‖ + ‖(phiExtended b x)⁻¹ - 1‖ < ε := by
  obtain ⟨C, v, hC, hv, hdec⟩ := phiExtended_uniform_sector_decay hK
  intro ε hε
  have hlin : Tendsto (fun R : ℝ => -2 * v * R) atTop atBot := by
    have h := (tendsto_id (α := ℝ)).atTop_mul_const_of_neg
      (show -2 * v < 0 by linarith)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hexp : Tendsto (fun R : ℝ => Real.exp (-2 * v * R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hprod : Tendsto (fun R : ℝ => C * Real.exp (-2 * v * R)) atTop (𝓝 0) := by
    simpa using hexp.const_mul C
  have hev : ∀ᶠ R : ℝ in atTop, C * Real.exp (-2 * v * R) < ε :=
    hprod.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) < ε from hε))
  obtain ⟨R, hRε, hR1⟩ := (hev.and (eventually_ge_atTop (1 : ℝ))).exists
  refine ⟨R, hR1, ?_⟩
  intro b hb x hx hRx
  have hstep : C * Real.exp (-2 * v * ‖x‖) ≤ C * Real.exp (-2 * v * R) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    nlinarith
  exact lt_of_le_of_lt (le_trans (hdec b hb x hx) hstep) hRε

end SICLean.L4.Sector
