import SICLean.L5.FiniteProductPentagon

set_option autoImplicit false

/-!
Elementary consequences of the fixed negative-kernel Fourier identities.
The scaled delta transform is obtained by involution, so no extra square-root
normalization lemma or choice of a finite enumeration is needed.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L5.FiniteTranslationRatioAux

open L4 FiniteFourier

variable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)

theorem fourier_sub (f g : SpecialValueGroup M → ℂ) (y : SpecialValueGroup M) :
    fourier M hM (fun u => f u - g u) y =
      fourier M hM f y - fourier M hM g y := by
  have hneg : fourier M hM (fun u => -g u) y = -fourier M hM g y := by
    simpa only [neg_one_mul] using fourier_mul_const M hM (-1) g y
  simpa only [sub_eq_add_neg, hneg] using
    fourier_add M hM f (fun u => -g u) y

theorem fourier_neg_argument (f : SpecialValueGroup M → ℂ)
    (y : SpecialValueGroup M) :
    fourier M hM (fun u => f (-u)) y = fourier M hM f (-y) := by
  have hf : (fun u => f (-u)) = fourier M hM (fourier M hM f) := by
    funext u
    exact (fourier_involution M hM f u).symm
  rw [hf, fourier_involution]

theorem fourier_scaled_delta (y : SpecialValueGroup M) :
    fourier M hM (fun u => sqrtOrder M * delta M u) y = 1 := by
  have hf : (fun u => sqrtOrder M * delta M u) =
      fourier M hM (fun _ => 1) := by
    funext u
    exact (fourier_one M hM u).symm
  rw [hf, fourier_involution]

theorem fourier_scaled_delta_translate (h y : SpecialValueGroup M) :
    fourier M hM (fun u => sqrtOrder M * delta M (u + h)) y =
      specialValuePairing M hM h y := by
  rw [fourier_translate M hM (fun u => sqrtOrder M * delta M u),
    fourier_scaled_delta, mul_one]

end SICLean.L5.FiniteTranslationRatioAux
