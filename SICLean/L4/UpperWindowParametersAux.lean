import SICLean.L4.UpperWindowGeometry
import SICLean.L4.ModularPhi

set_option autoImplicit false

noncomputable section

open Complex
open scoped Topology MatrixGroups UpperHalfPlane

namespace SICLean.L4.UpperWindow

private theorem norm_e_exp_aux (z : ℂ) :
    ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  rw [e, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

private theorem e_zpow_mul_aux (τ w : ℂ) (n : ℤ) :
    (e τ) ^ n * e w = e ((n : ℂ) * τ + w) := by
  simp only [e]
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  ring

private theorem norm_e_zpow_mul_aux (τ w : ℂ) (n : ℤ) :
    ‖(e τ) ^ n * e w‖ =
      Real.exp (-2 * Real.pi * ((n : ℝ) * τ.im + w.im)) := by
  rw [e_zpow_mul_aux, norm_e_exp_aux]
  congr 1
  simp [Complex.mul_im]

private theorem rpow_norm_e_exp_aux (z : ℂ) (a : ℝ) :
    Real.rpow ‖e z‖ a = Real.exp (-2 * Real.pi * z.im * a) := by
  rw [Real.rpow_eq_pow, norm_e_exp_aux,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]

private theorem etaMobius_im_aux (M : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    (etaMobius M τ).im = τ.im / Complex.normSq (etaDenom M τ) := by
  let z : ℍ := ⟨τ, hτ⟩
  have hi := ModularGroup.im_smul_eq_div_normSq M z
  change (((M • z : ℍ) : ℂ)).im = τ.im / _ at hi
  rw [coe_smul_eq_etaMobius] at hi
  simpa [UpperHalfPlane.denom, etaDenom, z] using hi

/-- The three modulus identities in expanded form, independent of the window definitions. -/
theorem ABC_norms_aux (M : SL(2, ℤ)) (hM : 0 < M 1 0) (h ℓ p : ℤ)
    (τ w y : ℂ) (hτ : 0 < τ.im) :
    ‖(e τ) ^ ℓ * e w‖ = Real.rpow ‖e τ‖
        (coords (etaDenom M τ)
          ((M 1 0 : ℂ) * w + (h : ℂ) + (ℓ : ℂ) * etaDenom M τ)).1 ∧
      ‖(e (etaMobius M τ)) ^ (-h) * e (w / etaDenom M τ)‖ =
        Real.rpow ‖e (etaMobius M τ)‖
          (-(coords (etaDenom M τ)
            ((M 1 0 : ℂ) * w + (h : ℂ) + (ℓ : ℂ) * etaDenom M τ)).2) ∧
      ‖e (y / etaDenom M τ) *
          ((e (etaMobius M τ)) ^ (-h) * e (w / etaDenom M τ))‖ =
        Real.rpow ‖e (etaMobius M τ)‖
          (1 - (coords (etaDenom M τ)
              ((M 1 0 : ℂ) * w + (h : ℂ) + (ℓ : ℂ) * etaDenom M τ)).2 -
            (coords (etaDenom M τ)
              (1 + (p : ℂ) * etaDenom M τ + (M 1 0 : ℂ) * y)).2) := by
  let T := etaDenom M τ
  let S := coords T ((M 1 0 : ℂ) * w + (h : ℂ) + (ℓ : ℂ) * T)
  let H := coords T (1 + (p : ℂ) * T + (M 1 0 : ℂ) * y)
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have ht : τ.im ≠ 0 := ne_of_gt hτ
  have hTi : T.im = (M 1 0 : ℝ) * τ.im := by simp [T, etaDenom]
  have hTin : T.im ≠ 0 := by rw [hTi]; exact mul_ne_zero hc ht
  have hT : T ≠ 0 := by
    intro he
    exact hTin (by simp [he])
  have hn : Complex.normSq T ≠ 0 := (Complex.normSq_pos.mpr hT).ne'
  have hm : (etaMobius M τ).im = τ.im / Complex.normSq T :=
    etaMobius_im_aux M τ hτ
  have hS₁ : τ.im * S.1 = (ℓ : ℝ) * τ.im + w.im := by
    dsimp [S, coords]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero]
    rw [hTi]
    field_simp
    ring
  have hS₂ : (etaMobius M τ).im * (-S.2) =
      -(h : ℝ) * (etaMobius M τ).im + (w / T).im := by
    rw [hm, Complex.div_im]
    dsimp [S, coords]
    simp only [Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, add_zero, sub_zero]
    rw [hTi]
    field_simp
    ring
  have hH₂ : (etaMobius M τ).im * (1 - H.2) = (y / T).im := by
    rw [hm, Complex.div_im]
    dsimp [H, coords]
    simp only [Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, add_zero, zero_add, sub_zero]
    rw [hTi]
    field_simp
    ring
  have hSH : (etaMobius M τ).im * (1 - S.2 - H.2) =
      -(h : ℝ) * (etaMobius M τ).im + (w / T).im + (y / T).im := by
    calc
      _ = (etaMobius M τ).im * (-S.2) + (etaMobius M τ).im * (1 - H.2) := by ring
      _ = _ := by rw [hS₂, hH₂]
  change ‖(e τ) ^ ℓ * e w‖ = Real.rpow ‖e τ‖ S.1 ∧
    ‖(e (etaMobius M τ)) ^ (-h) * e (w / T)‖ =
      Real.rpow ‖e (etaMobius M τ)‖ (-S.2) ∧
    ‖e (y / T) * ((e (etaMobius M τ)) ^ (-h) * e (w / T))‖ =
      Real.rpow ‖e (etaMobius M τ)‖ (1 - S.2 - H.2)
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_e_zpow_mul_aux, rpow_norm_e_exp_aux]
    congr 1
    linear_combination 2 * Real.pi * hS₁
  · rw [norm_e_zpow_mul_aux, rpow_norm_e_exp_aux]
    congr 1
    simp only [Int.cast_neg]
    linear_combination 2 * Real.pi * hS₂
  · rw [norm_mul, norm_e_exp_aux, norm_e_zpow_mul_aux, ← Real.exp_add,
      rpow_norm_e_exp_aux]
    congr 1
    simp only [Int.cast_neg]
    linear_combination 2 * Real.pi * hSH

end SICLean.L4.UpperWindow
