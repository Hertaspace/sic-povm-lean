import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The regular numerator at the inversion pole

Divided differences remove the sinh zeros before taking derivatives. Three further divided
differences give an exact Taylor identity with a remainder analytic at zero. Its quadratic
coefficient determines the `/12` normalization.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4

lemma analyticAt_dslope_local {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

lemma factorial_mul_iterate_dslope {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (n : ℕ) :
    (n.factorial : ℂ) * (Function.swap dslope a)^[n] f a = iteratedDeriv n f a := by
  rcases hf with ⟨p, r, hp⟩
  have hcoeff := (hp.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at hfac
  change (FormalMultilinearSeries.fslope^[n] p).coeff 0 = _ at hcoeff
  rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add] at hcoeff
  rw [← hcoeff]
  simpa only [FormalMultilinearSeries.coeff, nsmul_eq_mul, Pi.one_def] using hfac

def sinhSlope (c w : ℂ) : ℂ := dslope (fun v : ℂ => Complex.sinh (c * v)) 0 w

lemma analytic_sinhSlope (c : ℂ) : AnalyticOnNhd ℂ (sinhSlope c) univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  exact (Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).mpr (by fun_prop)

lemma sinhSlope_zero (c : ℂ) : sinhSlope c 0 = c := by
  rw [sinhSlope, dslope_same]
  have h : HasDerivAt (fun v : ℂ => Complex.sinh (c * v)) c 0 := by
    convert! ((Complex.hasDerivAt_sinh (c * 0)).comp 0
      ((hasDerivAt_id (0 : ℂ)).const_mul c)) using 1 <;> simp
  exact h.deriv

lemma sinhSlope_mul (c w : ℂ) : w * sinhSlope c w = Complex.sinh (c * w) := by
  simpa [sinhSlope, smul_eq_mul] using
    sub_smul_dslope (fun v : ℂ => Complex.sinh (c * v)) 0 w

lemma sinhSlope_deriv_zero (c : ℂ) : deriv (sinhSlope c) 0 = 0 := by
  have hf : AnalyticAt ℂ (fun v : ℂ => Complex.sinh (c * v)) 0 := by fun_prop
  have h := factorial_mul_iterate_dslope hf 2
  have hd : iteratedDeriv 2 (fun v : ℂ => Complex.sinh (c * v)) 0 = 0 := by
    rw [iteratedDeriv_comp_const_mul Complex.contDiff_sinh c]
    norm_num [iteratedDeriv_succ', Complex.deriv_sinh, Complex.deriv_cosh]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    Function.swap, dslope_same] at h
  change (2 : ℂ) * deriv (sinhSlope c) 0 = _ at h
  rw [hd] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

lemma sinhSlope_deriv2_zero (c : ℂ) : iteratedDeriv 2 (sinhSlope c) 0 = c ^ 3 / 3 := by
  have hf : AnalyticAt ℂ (fun v : ℂ => Complex.sinh (c * v)) 0 := by fun_prop
  have h := factorial_mul_iterate_dslope hf 3
  have hs := factorial_mul_iterate_dslope (analytic_sinhSlope c 0 (mem_univ _)) 2
  have hd : iteratedDeriv 3 (fun v : ℂ => Complex.sinh (c * v)) 0 = c ^ 3 := by
    rw [iteratedDeriv_comp_const_mul Complex.contDiff_sinh c]
    norm_num [iteratedDeriv_succ', Complex.deriv_sinh, Complex.deriv_cosh]
  change (6 : ℂ) * dslope (dslope (sinhSlope c) 0) 0 0 = _ at h
  change (2 : ℂ) * dslope (dslope (sinhSlope c) 0) 0 0 = _ at hs
  rw [hd] at h
  rw [← hs]
  linear_combination h / 3

lemma deriv2_mul_zero {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    iteratedDeriv 2 (fun w => f w * g w) 0 =
      f 0 * iteratedDeriv 2 g 0 + 2 * deriv f 0 * deriv g 0 +
        iteratedDeriv 2 f 0 * g 0 := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  norm_num [Finset.sum_range_succ]

def inversionDenom (b w : ℂ) : ℂ := 2 * sinhSlope b w * sinhSlope b⁻¹ w

lemma analytic_inversionDenom (b : ℂ) : AnalyticOnNhd ℂ (inversionDenom b) univ := by
  intro w hw
  exact (analyticAt_const.mul (analytic_sinhSlope b w hw)).mul (analytic_sinhSlope b⁻¹ w hw)

lemma inversionDenom_zero (b : ℂ) (hb : b ≠ 0) : inversionDenom b 0 = 2 := by
  simp [inversionDenom, sinhSlope_zero, hb]

lemma inversionDenom_deriv_zero (b : ℂ) : deriv (inversionDenom b) 0 = 0 := by
  change deriv (fun w => 2 * sinhSlope b w * sinhSlope b⁻¹ w) 0 = 0
  have h₁ := (analytic_sinhSlope b 0 (mem_univ _)).differentiableAt.hasDerivAt
  have h₂ := (analytic_sinhSlope b⁻¹ 0 (mem_univ _)).differentiableAt.hasDerivAt
  simpa only [inversionDenom, Pi.mul_def, sinhSlope_deriv_zero,
    mul_zero, zero_mul, add_zero] using ((h₁.const_mul 2).mul h₂).deriv

lemma inversionDenom_deriv2_zero (b : ℂ) (hb : b ≠ 0) :
    iteratedDeriv 2 (inversionDenom b) 0 = 2 * (b ^ 2 + (b⁻¹) ^ 2) / 3 := by
  rw [show inversionDenom b = fun w => 2 * (sinhSlope b w * sinhSlope b⁻¹ w) by
    funext w; simp only [inversionDenom]; ring]
  rw [iteratedDeriv_const_mul_field,
    deriv2_mul_zero (analytic_sinhSlope b 0 (mem_univ _))
      (analytic_sinhSlope b⁻¹ 0 (mem_univ _))]
  rw [sinhSlope_zero, sinhSlope_zero, sinhSlope_deriv_zero, sinhSlope_deriv_zero,
    sinhSlope_deriv2_zero, sinhSlope_deriv2_zero]
  field_simp
  <;> ring

def inversionRegular (b z w : ℂ) : ℂ :=
  Complex.cosh ((-2 * Complex.I * z) * w) / inversionDenom b w

lemma analyticAt_inversionRegular (b z : ℂ) (hb : b ≠ 0) :
    AnalyticAt ℂ (inversionRegular b z) 0 := by
  exact (by fun_prop : AnalyticAt ℂ
    (fun w : ℂ => Complex.cosh ((-2 * Complex.I * z) * w)) 0).div
    (analytic_inversionDenom b 0 (mem_univ _))
    (by rw [inversionDenom_zero b hb]; norm_num)

lemma inversionRegular_zero (b z : ℂ) (hb : b ≠ 0) :
    inversionRegular b z 0 = 1 / 2 := by
  simp [inversionRegular, inversionDenom_zero b hb]

lemma inversionRegular_derivatives (b z : ℂ) (hb : b ≠ 0) :
    deriv (inversionRegular b z) 0 = 0 ∧
      iteratedDeriv 2 (inversionRegular b z) 0 =
        -2 * z ^ 2 - (b ^ 2 + (b⁻¹) ^ 2) / 6 := by
  let N : ℂ → ℂ := fun w => Complex.cosh ((-2 * Complex.I * z) * w)
  have hN : AnalyticAt ℂ N 0 := by dsimp [N]; fun_prop
  have hD := analytic_inversionDenom b 0 (mem_univ _)
  have hR := analyticAt_inversionRegular b z hb
  have heq : (fun w => inversionRegular b z w * inversionDenom b w) =ᶠ[𝓝 0] N := by
    filter_upwards [hD.continuousAt.eventually_ne (by
      rw [inversionDenom_zero b hb]; norm_num : inversionDenom b 0 ≠ 0)] with w hw
    exact div_mul_cancel₀ _ hw
  have hN₁ : deriv N 0 = 0 := by
    have h : HasDerivAt N
        (Complex.sinh ((-2 * Complex.I * z) * 0) * (-2 * Complex.I * z)) 0 := by
      simpa [N, Function.comp_def] using
        (Complex.hasDerivAt_cosh ((-2 * Complex.I * z) * 0)).comp 0
          ((hasDerivAt_id (0 : ℂ)).const_mul (-2 * Complex.I * z))
    simpa using h.deriv
  have hN₂ : iteratedDeriv 2 N 0 = -4 * z ^ 2 := by
    dsimp [N]
    rw [iteratedDeriv_comp_const_mul Complex.contDiff_cosh]
    norm_num [iteratedDeriv_succ', Complex.deriv_sinh, Complex.deriv_cosh,
      mul_pow, Complex.I_sq]
  have h₁ := heq.deriv_eq
  rw [deriv_fun_mul hR.differentiableAt hD.differentiableAt,
    inversionDenom_zero b hb, inversionDenom_deriv_zero, hN₁] at h₁
  have hR₁ : deriv (inversionRegular b z) 0 = 0 := by simpa using h₁
  refine ⟨hR₁, ?_⟩
  have h₂ := heq.iteratedDeriv_eq 2
  rw [deriv2_mul_zero hR hD, inversionRegular_zero b z hb, hR₁,
    inversionDenom_zero b hb, inversionDenom_deriv_zero,
    inversionDenom_deriv2_zero b hb, hN₂] at h₂
  linear_combination h₂ / 2

def inversionRemainder (b z : ℂ) : ℂ → ℂ :=
  dslope (dslope (dslope (inversionRegular b z) 0) 0) 0

lemma analyticAt_inversionRemainder (b z : ℂ) (hb : b ≠ 0) :
    AnalyticAt ℂ (inversionRemainder b z) 0 :=
  analyticAt_dslope_local (analyticAt_dslope_local
    (analyticAt_dslope_local (analyticAt_inversionRegular b z hb)))

lemma inversionRegular_taylor (b z w : ℂ) (hb : b ≠ 0) :
    inversionRegular b z w =
      1 / 2 - (z ^ 2 + (b ^ 2 + (b⁻¹) ^ 2) / 12) * w ^ 2 +
        w ^ 3 * inversionRemainder b z w := by
  let f := inversionRegular b z
  have h₀ := sub_smul_dslope f 0 w
  have h₁ := sub_smul_dslope (dslope f 0) 0 w
  have h₂ := sub_smul_dslope (dslope (dslope f 0) 0) 0 w
  have hc := factorial_mul_iterate_dslope (analyticAt_inversionRegular b z hb) 2
  change (2 : ℂ) * dslope (dslope f 0) 0 0 = _ at hc
  have hd := inversionRegular_derivatives b z hb
  simp only [sub_zero, smul_eq_mul, dslope_same] at h₀ h₁ h₂ hc
  change w * inversionRemainder b z w =
    dslope (dslope f 0) 0 w - deriv (dslope f 0) 0 at h₂
  dsimp only [f] at h₀ h₁ h₂ hc
  rw [inversionRegular_zero b z hb] at h₀
  rw [hd.1] at h₁
  rw [hd.2] at hc
  linear_combination -h₀ - w * h₁ - w ^ 2 * h₂ + w ^ 2 * hc / 2

end SICLean.L4
