import SICLean.L4.UpperResidueParameters

set_option autoImplicit false

/-!
Elementary geometry and the analytic center lift for the initial integral
identities. These lemmas use only the explicit upper-plane parameter box.
-/

noncomputable section
open Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L4.UpperIntegralIdentitiesAux

/-- The prescribed wedge contains the preimage of exp(iψ/2) under cτ+d. -/
lemma tauRegion_nonempty (M : SL(2, ℤ)) (ψ : ℝ) (hM : 0 < M 1 0)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    (UpperWindow.tauRegion M ψ).Nonempty := by
  let T : ℂ := (Real.cos (ψ / 2) : ℂ) + (Real.sin (ψ / 2) : ℂ) * Complex.I
  let τ : ℂ := (T - (M 1 1 : ℂ)) / (M 1 0 : ℂ)
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hcR : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hT : etaDenom M τ = T := by
    dsimp [etaDenom, τ]
    field_simp [hc]
    ring
  have hθ : ψ / 2 ∈ Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have ha : T.arg = ψ / 2 := by
    simpa only [T, ← Complex.ofReal_cos, ← Complex.ofReal_sin] using
      (Complex.arg_cos_add_sin_mul_I hθ)
  have hi : 0 < T.im := by
    dsimp only [T]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < ψ / 2)
      (by linarith [Real.pi_pos] : ψ / 2 < Real.pi)
  refine ⟨τ, ?_, ?_, ?_⟩
  · have hc_cast : (M 1 0 : ℂ) = ((M 1 0 : ℝ) : ℂ) := by simp
    dsimp [τ]
    rw [hc_cast, Complex.div_ofReal_im]
    simpa only [Complex.sub_im, Complex.intCast_im, sub_zero] using div_pos hi hcR
  · rw [hT, ha]
    linarith
  · rw [hT, ha]
    linarith

/-- The two height coordinates of the literal center are exactly (ρ,ρ). -/
lemma center_height_coords (M : SL(2, ℤ)) (p : ℤ) (ρ : ℝ) (τ : ℂ)
    (hM : 0 < M 1 0) (hτ : 0 < τ.im) :
    UpperWindow.coords (etaDenom M τ)
      (UpperWindow.height M p τ (UpperWindow.centerY M p ρ τ)) = (ρ, ρ) := by
  rw [(UpperWindow.center_equations M hM 0 0 p 0 ρ τ).2]
  simpa only [mul_add, mul_one] using
    UpperWindow.coords_real_combination (etaDenom M τ)
      (im_etaDenom_pos_of_im_pos M hM hτ).ne' ρ ρ

/-- Adding the center y imposes precisely the two remaining box conditions. -/
lemma center_lift_mem_iff (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (u : ℂ × ℂ) :
    (u.1, u.2, UpperWindow.centerY M p ρ u.1) ∈
        UpperWindow.domain M h ℓ p ψ σ ρ δ ↔
      u.1 ∈ UpperWindow.tauRegion M ψ ∧
        |(UpperWindow.coords (etaDenom M u.1) (UpperWindow.s M h ℓ u.1 u.2)).1 - σ| <
          UpperWindow.radius M σ ρ δ ∧
        |(UpperWindow.coords (etaDenom M u.1) (UpperWindow.s M h ℓ u.1 u.2)).2 - σ| <
          UpperWindow.radius M σ ρ δ := by
  constructor
  · intro hx
    exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
  · rintro ⟨hτ, hs₁, hs₂⟩
    have hH := center_height_coords M p ρ u.1 hc.1 hτ.1
    have hr := (UpperWindow.radius_margins M ψ σ ρ δ hc).1
    refine ⟨hτ, hs₁, hs₂, ?_, ?_⟩ <;>
      simpa only [hH, sub_self, abs_zero] using hr

/-- The center lift is an affine, hence analytic, map of the joint variables. -/
lemma center_lift_analytic (M : SL(2, ℤ)) (p : ℤ) (ρ : ℝ) (u : ℂ × ℂ) :
    AnalyticAt ℂ (fun v : ℂ × ℂ => (v.1, v.2, UpperWindow.centerY M p ρ v.1)) u := by
  have hT : AnalyticAt ℂ (fun v : ℂ × ℂ => etaDenom M v.1) u := by
    unfold etaDenom
    exact (analyticAt_const.mul analyticAt_fst).add analyticAt_const
  have hy : AnalyticAt ℂ (fun v : ℂ × ℂ => UpperWindow.centerY M p ρ v.1) u := by
    unfold UpperWindow.centerY
    exact (((analyticAt_const.mul (hT.add analyticAt_const)).sub analyticAt_const).sub
      (analyticAt_const.mul hT)).div_const
  exact analyticAt_fst.prod (analyticAt_snd.prod hy)

end SICLean.L4.UpperIntegralIdentitiesAux
