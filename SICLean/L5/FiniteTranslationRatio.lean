import SICLean.L5.FiniteProductPentagon
import SICLean.L5.FiniteTranslationRatioAux

set_option autoImplicit false

/-!
# Translation ratios and both Fourier identities

[RW-rec, §4] and [RW-rec, §7]. See also [RW26, (4)--(7), p. 3] and [RW26, (36), p. 18].
`R_h` is the quotient `E(t + h) / E(t)`.
The intermediate product identity uses `h ≠ 0`. The two final Fourier identities
are stated for every `h`, including zero.
No integrality, valuation, or reduction assertion is made in this module.
-/

noncomputable section

open Classical
open scoped BigOperators MatrixGroups

namespace SICLean.L5.FiniteTranslationRatio

open L4 FiniteFourier FiniteProductPentagon

/-- Translation quotient from [RW-rec, §4], with `E` the plus branch. -/
def ratio (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (h t : SpecialValueGroup M) : ℂ :=
  specialValuePlus M hM (t + h) / specialValuePlus M hM t

variable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)

/-- Nonvanishing, for reciprocal and valuation arguments. [RW-rec, §4]; [RW26, (5), p. 3]. -/
theorem ratio_ne_zero (h t : SpecialValueGroup M) : ratio M hM h t ≠ 0 := by
  exact div_ne_zero (specialValuePlus_ne_zero M hM (t + h))
    (specialValuePlus_ne_zero M hM t)

/-- The zero-shift case. [RW-rec, §4]. -/
theorem ratio_zero_shift (t : SpecialValueGroup M) : ratio M hM 0 t = 1 := by
  simp only [ratio, add_zero, div_self (specialValuePlus_ne_zero M hM t)]

/-- At `t = 0` the value is `E(h) / E(0)`, with `E(0)` the positive square root.
[RW-rec, §4]; [RW26, (4), p. 3]. -/
theorem ratio_at_zero (h : SpecialValueGroup M) :
    ratio M hM h 0 = specialValuePlus M hM h / specialValuePlus M hM 0 := by
  simp only [ratio, zero_add]

/-- The other exceptional point is `t = -h`.
[RW-rec, §4]; [RW26, (4), p. 3]. -/
theorem ratio_at_neg_shift (h : SpecialValueGroup M) :
    ratio M hM h (-h) = specialValuePlus M hM 0 / specialValuePlus M hM (-h) := by
  simp only [ratio, neg_add_cancel]

/-- Reciprocal means the pointwise inverse of the quotient.
[RW-rec, §4, §7]. -/
theorem ratio_inverse (h t : SpecialValueGroup M) :
    (ratio M hM h t)⁻¹ = specialValuePlus M hM t / specialValuePlus M hM (t + h) := by
  exact inv_div _ _

/-- A reciprocal is a translated negative-shift quotient.
[RW-rec, §4]. -/
theorem reciprocal_as_translate (h t : SpecialValueGroup M) :
    ratio M hM (-h) (t + h) = (ratio M hM h t)⁻¹ := by
  simp only [ratio, add_neg_cancel_right, inv_div]

/-- Multiplicative translation cocycle, used in cyclic products. [RW-rec, Thm. 4]. -/
theorem ratio_cocycle (h k t : SpecialValueGroup M) :
    ratio M hM (h + k) t = ratio M hM h (t + k) * ratio M hM k t := by
  have hi : t + (h + k) = t + k + h := by abel
  simp only [ratio, hi]
  field_simp [specialValuePlus_ne_zero M hM (t + k), specialValuePlus_ne_zero M hM t]

/-- Finite cyclic product in the form used by [RW-rec, Thm. 4].
This is a valuation-free telescoping identity. -/
theorem ratio_cyclic_product (h t : SpecialValueGroup M) (n : ℕ)
    (hn : n • h = 0) :
    (∏ j : Fin n, ratio M hM h (t + j.val • h)) = 1 := by
  have htel : ∀ m : ℕ,
      (∏ j : Fin m, ratio M hM h (t + j.val • h)) = ratio M hM (m • h) t := by
    intro m
    induction m with
    | zero => simp [ratio_zero_shift]
    | succ m ih =>
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih, succ_nsmul', ratio_cocycle]
        ring
  rw [htel, hn, ratio_zero_shift]

/-- Reflection form of the quotient, including the term at `t = 0`.
[RW-rec, (4)]; [RW26, (4)--(5), p. 3]. -/
theorem ratio_reflection (h t : SpecialValueGroup M) :
    ratio M hM h t =
      specialValueGaussian M hM t * specialValuePlus M hM (t + h) *
        specialValuePlus M hM (-t) -
      sqrtOrder M * specialValuePlus M hM h * delta M t := by
  rw [ratio, div_eq_mul_inv, actual_inverse]
  by_cases ht : t = 0
  · subst t
    simp only [zero_add, neg_zero, delta]
    ring
  · simp only [delta, if_neg ht]
    ring

/-- Product-form intermediate identity. The hypothesis `h ≠ 0` is used here.
[RW-rec, §4]; [RW26, (36), p. 18]. -/
theorem ratio_fourier_product (h t : SpecialValueGroup M) (hh : h ≠ 0) :
    fourier M hM (ratio M hM h) t + specialValuePlus M hM h =
      specialValueGaussian M hM (h + t) * specialValuePlus M hM (-h - t) *
        specialValuePlus M hM h * specialValuePlus M hM t := by
  let f : SpecialValueGroup M → ℂ := fun u =>
    specialValuePlus M hM u * specialValueGaussian M hM u *
      specialValuePlus M hM (h - u)
  have hr : ratio M hM h = fun u =>
      f (-u) - specialValuePlus M hM h * (sqrtOrder M * delta M u) := by
    funext u
    rw [ratio_reflection]
    dsimp only [f]
    rw [L3.M74.gaussian_neg, sub_neg_eq_add]
    rw [add_comm h u]
    ring
  have hp := actual_product_fourier M hM h t
  simp only [delta, if_neg hh, mul_zero, zero_mul, sub_zero] at hp
  rw [hr, FiniteTranslationRatioAux.fourier_sub,
    FiniteTranslationRatioAux.fourier_neg_argument, fourier_mul_const,
    FiniteTranslationRatioAux.fourier_scaled_delta]
  change fourier M hM f (-t) - specialValuePlus M hM h * 1 +
    specialValuePlus M hM h = _
  rw [show fourier M hM f (-t) = _ from hp]
  ring

/-- [RW-rec, (15)], for every admissible matrix and every `h, t`.
The delta is at `t = -h`, with coefficient `sqrt(N) q(h)⁻¹`.
[RW26, (4)--(7), p. 3]; [RW26, (36), p. 18]. -/
theorem ratio_fourier (h t : SpecialValueGroup M) :
    fourier M hM (ratio M hM h) t =
      specialValuePlus M hM h * ((ratio M hM h t)⁻¹ - 1) +
      sqrtOrder M * (specialValueGaussian M hM h)⁻¹ * delta M (t + h) := by
  by_cases hh : h = 0
  · subst h
    have hzero : ratio M hM 0 = fun _ => 1 := funext (ratio_zero_shift M hM)
    rw [hzero, FiniteFourier.fourier_one]
    simp [L3.M74.gaussian_zero]
  · have hc :
        sqrtOrder M * specialValuePlus M hM h * specialValuePlus M hM t *
            delta M (t + h) =
          sqrtOrder M * (specialValueGaussian M hM h)⁻¹ * delta M (t + h) := by
      by_cases ht : t + h = 0
      · have ht' : t = -h := (eq_neg_iff_add_eq_zero).mpr ht
        subst t
        have hr := actual_reflection M hM h
        simp only [delta, if_neg hh, mul_zero, add_zero] at hr
        simp only [neg_add_cancel, delta]
        rw [← hr]
        ring
      · simp only [delta, if_neg ht, mul_zero]
    have hp := ratio_fourier_product M hM h t hh
    rw [ratio_inverse, div_eq_mul_inv, actual_inverse]
    rw [show h + t = t + h by abel,
      show -h - t = -(t + h) by abel] at hp
    linear_combination hp + hc

/-- The second identity of [RW-rec, §4], with `E(h)` outside the Fourier transform.
The finite inputs are those of (15): [RW26, (4)--(7), p. 3] and [RW26, (36), p. 18].
This scales the transform of the pointwise reciprocal. -/
theorem ratio_inverse_fourier_scaled (h t : SpecialValueGroup M) :
    specialValuePlus M hM h * fourier M hM (fun u => (ratio M hM h u)⁻¹) t =
      ratio M hM h (-t) + sqrtOrder M * specialValuePlus M hM h * delta M t -
      (specialValueGaussian M hM h)⁻¹ * specialValuePairing M hM h t := by
  have hf : fourier M hM (ratio M hM h) = fun u =>
      specialValuePlus M hM h * ((ratio M hM h u)⁻¹ - 1) +
        (specialValueGaussian M hM h)⁻¹ * (sqrtOrder M * delta M (u + h)) := by
    funext u
    rw [ratio_fourier]
    ring
  have ht := congrArg (fun f => fourier M hM f t) hf
  rw [fourier_involution, FiniteFourier.fourier_add,
    fourier_mul_const, fourier_mul_const,
    FiniteTranslationRatioAux.fourier_scaled_delta_translate,
    FiniteTranslationRatioAux.fourier_sub, FiniteFourier.fourier_one] at ht
  linear_combination -ht

/-- The shape used in [RW-rec, §7]: Fourier of the pointwise inverse of `R_h`.
[RW26, (36), p. 18]. -/
theorem ratio_inverse_fourier (h t : SpecialValueGroup M) :
    fourier M hM (fun u => (ratio M hM h u)⁻¹) t =
      ratio M hM h (-t) / specialValuePlus M hM h + sqrtOrder M * delta M t -
      ((specialValueGaussian M hM h)⁻¹ * specialValuePairing M hM h t) /
        specialValuePlus M hM h := by
  apply mul_left_cancel₀ (specialValuePlus_ne_zero M hM h)
  rw [ratio_inverse_fourier_scaled]
  field_simp [specialValuePlus_ne_zero M hM h]

#print ratio
#check @ratio_fourier
#check @ratio_inverse_fourier_scaled
#check @ratio_inverse_fourier

end SICLean.L5.FiniteTranslationRatio
