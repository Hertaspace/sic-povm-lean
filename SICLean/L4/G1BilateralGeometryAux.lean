import SICLean.L4.G1RatioTailBounds

set_option autoImplicit false

/-!
Elementary full-disk continuity margins and bounded translations of unit rays. The window casts use
the existing definitions directly. The ray estimates specialize the existing bilateral sector
geometry, with no new hypotheses.
-/

noncomputable section
open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G1BilateralGeometryAux

lemma denom_real (M : SL(2, ℤ)) (τ₀ : ℝ) :
    etaDenom M (τ₀ : ℂ) = (g1T M τ₀ : ℂ) := by
  simp [etaDenom, g1T]

lemma denom_continuous (M : SL(2, ℤ)) : Continuous (etaDenom M) := by
  unfold etaDenom
  fun_prop

lemma denom_real_ne_zero (M : SL(2, ℤ)) (τ₀ : ℝ) (hT : 0 < g1T M τ₀) :
    etaDenom M (τ₀ : ℂ) ≠ 0 := by
  rw [denom_real]
  exact_mod_cast ne_of_gt hT

lemma disk_of_eventually (τ₀ : ℝ) (P : ℂ → Prop)
    (hP : ∀ᶠ τ in 𝓝 (τ₀ : ℂ), P τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, P τ := by
  obtain ⟨ρ, hρ, h⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hP
  exact ⟨ρ, hρ, h⟩

lemma positive_margin_eventually {f : ℂ → ℝ} {τ : ℂ}
    (hf : ContinuousAt f τ) (hpos : 0 < f τ) :
    ∀ᶠ z in 𝓝 τ, f τ / 2 ≤ f z := by
  filter_upwards [hf.eventually (Ioi_mem_nhds (half_lt_self hpos))] with z hz
  exact hz.le

lemma domain_eventually (M : SL(2, ℤ)) (τ₀ : ℝ) (hT : 0 < g1T M τ₀) :
    ∀ᶠ τ in 𝓝 (τ₀ : ℂ), τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).re := by
  have hcont : ContinuousAt (fun τ : ℂ => (etaDenom M τ).re) (τ₀ : ℂ) :=
    Complex.continuous_re.continuousAt.comp (denom_continuous M).continuousAt
  have hpos : 0 < (etaDenom M (τ₀ : ℂ)).re := by simpa [denom_real] using hT
  filter_upwards [hcont.eventually (Ioi_mem_nhds hpos)] with τ hτ
  exact ⟨Or.inl hτ, hτ⟩

lemma complexS_real (M : SL(2, ℤ)) (τ₀ w : ℝ) (h ell : ℤ) :
    G1RatioTail.complexS M (τ₀ : ℂ) (w : ℂ) h ell = (g1S M τ₀ w h ell : ℂ) := by
  simp [G1RatioTail.complexS, g1S, denom_real]

lemma complexL_real (M : SL(2, ℤ)) (τ₀ w y : ℝ) (h ell p : ℤ) :
    G1RatioTail.complexL M (τ₀ : ℂ) (w : ℂ) (y : ℂ) h ell p =
      (g1L M τ₀ w y h ell p : ℂ) := by
  simp [G1RatioTail.complexL, g1L, complexS_real, denom_real]

lemma upper_window_continuousAt (M : SL(2, ℤ)) (τ₀ w : ℝ) (h ell : ℤ)
    (hT : 0 < g1T M τ₀) :
    ContinuousAt (fun τ : ℂ => 2 * Real.pi *
      (G1RatioTail.complexS M τ (w : ℂ) h ell / etaDenom M τ).re) (τ₀ : ℂ) := by
  have hn := denom_real_ne_zero M τ₀ hT
  unfold G1RatioTail.complexS etaDenom
  fun_prop (disch := exact hn)

lemma lower_window_continuousAt (M : SL(2, ℤ)) (τ₀ w y : ℝ) (h ell p : ℤ)
    (hT : 0 < g1T M τ₀) :
    ContinuousAt (fun τ : ℂ => -(2 * Real.pi *
      (G1RatioTail.complexL M τ (w : ℂ) (y : ℂ) h ell p / etaDenom M τ).re))
      (τ₀ : ℂ) := by
  have hn := denom_real_ne_zero M τ₀ hT
  unfold G1RatioTail.complexL G1RatioTail.complexS etaDenom
  fun_prop (disch := exact hn)

lemma upper_window_pos (M : SL(2, ℤ)) (τ₀ w : ℝ) (h ell : ℤ)
    (hT : 0 < g1T M τ₀) (hs : 0 < g1S M τ₀ w h ell) :
    0 < 2 * Real.pi *
      (G1RatioTail.complexS M (τ₀ : ℂ) (w : ℂ) h ell / etaDenom M (τ₀ : ℂ)).re := by
  rw [complexS_real, denom_real, ← Complex.ofReal_div, Complex.ofReal_re]
  positivity

lemma lower_window_pos (M : SL(2, ℤ)) (τ₀ w y : ℝ) (h ell p : ℤ)
    (hT : 0 < g1T M τ₀) (hL : g1L M τ₀ w y h ell p < 0) :
    0 < -(2 * Real.pi *
      (G1RatioTail.complexL M (τ₀ : ℂ) (w : ℂ) (y : ℂ) h ell p /
        etaDenom M (τ₀ : ℂ)).re) := by
  rw [complexL_real, denom_real, ← Complex.ofReal_div, Complex.ofReal_re]
  exact neg_pos.mpr (mul_neg_of_pos_of_neg (by positivity) (div_neg_of_neg_of_pos hL hT))

lemma interval_abs_bound (a b x : ℝ) (hx : x ∈ Icc a b) :
    |x| ≤ |a| + |b| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b, hx.1, hx.2]

lemma shifted_ray_sector (A : ℝ) (hA : 0 ≤ A) (d : ℂ) (hd : ‖d‖ = 1)
    (harg : Real.pi / 4 ≤ d.arg ∧ d.arg ≤ Real.pi - Real.pi / 4) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : ℂ, ‖u‖ ≤ A → ∀ r : ℝ, R ≤ r →
      (r : ℂ) * d + u ∈ ModularSector.upperSector (Real.pi / 8) (r / 2) := by
  obtain ⟨R, hR, hshift⟩ := ModularSector.bounded_translation_sector
    (Real.pi / 4) A 0 (by positivity) (by linarith [Real.pi_pos]) hA le_rfl
  refine ⟨R, hR, ?_⟩
  intro u hu r hr
  have hrpos : 0 < r := hR.trans_le hr
  have hnorm : ‖(r : ℂ) * d‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, hd, mul_one]
  have hz : (r : ℂ) * d ∈ ModularSector.upperSector (Real.pi / 4) R := by
    exact ⟨by simpa only [hnorm] using hr, by simpa [Complex.arg_real_mul d hrpos] using harg⟩
  obtain ⟨hsector, hn⟩ := hshift u hu ((r : ℂ) * d) hz
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hnorm] using hn
  · convert hsector.2.1 using 1
    ring
  · convert hsector.2.2 using 1
    ring

lemma lower_direction_re (ψ : ℝ) : (g1LowerDirection ψ).re = Real.sin ψ := by
  have hangle : -Real.pi / 2 + ψ = ψ - Real.pi / 2 := by ring
  rw [g1LowerDirection, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re, hangle,
    Real.cos_sub_pi_div_two]

lemma lower_direction_im (ψ : ℝ) : (g1LowerDirection ψ).im = -Real.cos ψ := by
  have hangle : -Real.pi / 2 + ψ = ψ - Real.pi / 2 := by ring
  rw [g1LowerDirection, mul_comm Complex.I, Complex.exp_ofReal_mul_I_im, hangle,
    Real.sin_sub_pi_div_two]

lemma reflected_lower_direction (ψ : ℝ) :
    -g1LowerDirection ψ = Complex.exp (((Real.pi / 2 + ψ : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext
  · rw [Complex.neg_re, lower_direction_re, Complex.exp_ofReal_mul_I_re]
    simp [Real.cos_add]
  · rw [Complex.neg_im, lower_direction_im, Complex.exp_ofReal_mul_I_im]
    simp [Real.sin_add]

lemma reflected_lower_direction_arg (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    (-g1LowerDirection ψ).arg = Real.pi / 2 + ψ := by
  rw [reflected_lower_direction, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor <;> linarith [Real.pi_pos]

lemma reflected_lower_direction_norm (ψ : ℝ) : ‖-g1LowerDirection ψ‖ = 1 := by
  rw [reflected_lower_direction, Complex.norm_exp_ofReal_mul_I]

lemma lower_direction_sq_re (ψ : ℝ) :
    (g1LowerDirection ψ ^ 2).re = -Real.cos (2 * ψ) := by
  simp only [pow_two, Complex.mul_re, lower_direction_re, lower_direction_im]
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq ψ]

lemma lower_direction_sq_im (ψ : ℝ) :
    (g1LowerDirection ψ ^ 2).im = -Real.sin (2 * ψ) := by
  simp only [pow_two, Complex.mul_im, lower_direction_re, lower_direction_im]
  rw [Real.sin_two_mul]
  ring

end SICLean.L4.G1BilateralGeometryAux
