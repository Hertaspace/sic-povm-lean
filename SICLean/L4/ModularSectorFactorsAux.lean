import SICLean.L4.ModularSectorGeometry

set_option autoImplicit false

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.ModularSector

/-- A relative perturbation in a small disk changes the principal argument
by at most the prescribed angle. -/
lemma arg_one_add_small (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ Real.pi / 2)
    (q : ℂ) (hq : ‖q‖ ≤ Real.sin θ / 2) :
    |(1 + q).arg| ≤ θ ∧ (1 / 2 : ℝ) ≤ ‖1 + q‖ := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ (by linarith)
  have hq' : ‖q‖ ≤ 1 / 2 := le_trans hq (by linarith [Real.sin_le_one θ])
  have hre : 0 ≤ (1 + q).re := by
    have := Complex.abs_re_le_norm q
    simp only [Complex.add_re, Complex.one_re]
    linarith [neg_le_of_abs_le this]
  have hn : (1 / 2 : ℝ) ≤ ‖1 + q‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-q)
    simpa using (show (1 : ℝ) - ‖q‖ ≤ ‖1 + q‖ by simpa using h) |>.trans'
      (by linarith)
  have him : |(1 + q).im| ≤ ‖1 + q‖ * Real.sin θ := by
    simp only [Complex.add_im, Complex.one_im, zero_add]
    have := Complex.abs_im_le_norm q
    nlinarith
  have hr : |(1 + q).im / ‖1 + q‖| ≤ Real.sin θ := by
    rw [abs_div, abs_of_pos (show 0 < ‖1 + q‖ by linarith), div_le_iff₀ (by linarith)]
    simpa [mul_comm] using him
  have hratio : (1 + q).im / ‖1 + q‖ ∈ Icc (-1 : ℝ) 1 := by
    have := abs_le.mp (hr.trans (Real.sin_le_one θ))
    exact this
  refine ⟨?_, hn⟩
  rw [Complex.arg_of_re_nonneg hre, abs_le]
  constructor
  · apply (Real.le_arcsin_iff_sin_le ⟨by linarith, by linarith⟩ hratio).2
    simpa only [Real.sin_neg] using (abs_le.mp hr).1
  · exact (Real.arcsin_le_iff_le_sin hratio ⟨by linarith, hθ'⟩).2 (abs_le.mp hr).2

/-- The sector points lie in an aligned rotated strip, so both existing
divisor counts vanish. -/
lemma phi_divisor_free_decaySector {K : Set ℂ} {β κ lam : ℝ}
    (hK : Sector.Family K β κ)
    (hlam : Sector.UniformMargin K (Sector.opening β κ) lam)
    {b x : ℂ} (hb : b ∈ K) (hx : Sector.InDecaySector β κ x) :
    phiPoleMultiplicity b x = 0 ∧ phiZeroMultiplicity b x = 0 := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hx.1)
  obtain ⟨θ, hθ, halign⟩ := Sector.exists_aligning_angle x (Sector.opening β κ)
    hx0 (Sector.opening_pos hK).le hx.2
  exact Sector.phi_divisor_free_rotatedStrip hK hlam hb hθ
    (Sector.aligned_mem_rotatedStrip hlam hb hθ halign)

end SICLean.L4.ModularSector
