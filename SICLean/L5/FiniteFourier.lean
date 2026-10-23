import SICLean.Final.Unconditional
import SICLean.L4.M75Gaussian
import SICLean.L5.FiniteFourierAux

set_option autoImplicit false

/-!
# Finite identities for the negative Fourier kernel and the point values

Finite Fourier identities for the special values. See [RW-rec] and [RW26, p. 15].

All values are the quotient point values. In particular `E(0)` is the positive
real square root of epsilon, whereas the minus branch at `0` is its inverse.
No assertion about a punctured germ is evaluated at its center here.
`specialValueRaw` uses `modularPhi`, `phiExtended`, and `etaMultiplier`,
including their principal slit-plane square root.
No G1 hypothesis, and no algebraicity, conjugation, or valuation premise, is used.
-/

noncomputable section

open Classical
open scoped BigOperators MatrixGroups

namespace SICLean.L5.FiniteFourier

open L4

/-- The positive real normalization, cast into `ℂ`. [RW-rec]; [RW26, p. 15]. -/
def sqrtOrder (M : SL(2, ℤ)) : ℂ :=
  (Real.sqrt (specialValueOrder M : ℝ) : ℂ)

/-- Zero indicator, with values in `ℂ`. [RW-rec]. -/
def delta (M : SL(2, ℤ)) (x : SpecialValueGroup M) : ℂ :=
  if x = 0 then 1 else 0

/-- Fourier transform: the kernel is `B(t, -y)`, not `B(t, y)`.
[RW-rec]; [RW26, p. 15].
The finite sum is `normalizedValueSum`. -/
def fourier (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : SpecialValueGroup M → ℂ) (y : SpecialValueGroup M) : ℂ :=
  G2.SpecialValueBridge.normalizedValueSum M hM
    (fun t => f t * specialValuePairing M hM t (-y))

variable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)

/-- Unfolded finite-sum form. [RW-rec]; [RW26, p. 15]. -/
theorem fourier_eq_sum (f : SpecialValueGroup M → ℂ) (y : SpecialValueGroup M) :
    fourier M hM f y =
      letI : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
      letI : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
      (sqrtOrder M)⁻¹ * ∑ t, f t * specialValuePairing M hM t (-y) := by
  rfl

/-- Additivity of the transform. [RW-rec, §4]; [RW26, p. 15]. -/
theorem fourier_add (f g : SpecialValueGroup M → ℂ) (y : SpecialValueGroup M) :
    fourier M hM (fun t => f t + g t) y = fourier M hM f y + fourier M hM g y := by
  simp only [fourier, G2.SpecialValueBridge.normalizedValueSum, add_mul,
    Finset.sum_add_distrib, mul_add]

/-- Homogeneity of the transform. [RW-rec, §4]. -/
theorem fourier_mul_const (a : ℂ) (f : SpecialValueGroup M → ℂ)
    (y : SpecialValueGroup M) :
    fourier M hM (fun t => a * f t) y = a * fourier M hM f y := by
  simp only [fourier, G2.SpecialValueBridge.normalizedValueSum, mul_assoc,
    ← Finset.mul_sum]
  ring

/-- A delta has constant transform. [RW-rec, §4]; [RW26, p. 15]. -/
theorem fourier_delta (y : SpecialValueGroup M) :
    fourier M hM (delta M) y = (sqrtOrder M)⁻¹ := by
  simp [fourier, G2.SpecialValueBridge.normalizedValueSum, delta, sqrtOrder,
    L3.M75.Gaussian.pairing_zero_left]

/-- Character orthogonality for the negative kernel. [RW-rec, Lemma 1]; [RW26, p. 15]. -/
theorem fourier_one (y : SpecialValueGroup M) :
    fourier M hM (fun _ => 1) y = sqrtOrder M * delta M y := by
  let := G2.StripCounting.specialGroupFintype M hM
  change (sqrtOrder M)⁻¹ * (∑ t, 1 * specialValuePairing M hM t (-y)) = _
  simp only [one_mul, FiniteFourierAux.sum_pairing]
  by_cases hy : y = 0
  · subst y
    rw [neg_zero, if_pos rfl, delta, if_pos rfl, mul_one]
    change _ = (Real.sqrt (specialValueOrder M : ℝ) : ℂ)
    rw [← G2DegenerateParametersAux.sqrt_order_sq M hM]
    change (sqrtOrder M)⁻¹ * sqrtOrder M ^ 2 = sqrtOrder M
    field_simp [sqrtOrder, G2DegenerateParametersAux.sqrt_order_ne_zero M hM]
  · simp [hy, delta]

/-- Translation multiplies by a positive character outside the transform.
[RW-rec, §4]; [RW26, p. 15]. -/
theorem fourier_translate (f : SpecialValueGroup M → ℂ)
    (h y : SpecialValueGroup M) :
    fourier M hM (fun t => f (t + h)) y =
      specialValuePairing M hM h y * fourier M hM f y := by
  let := G2.StripCounting.specialGroupFintype M hM
  change (sqrtOrder M)⁻¹ * (∑ t, f (t + h) * specialValuePairing M hM t (-y)) =
    specialValuePairing M hM h y *
      ((sqrtOrder M)⁻¹ * ∑ t, f t * specialValuePairing M hM t (-y))
  have hs : (∑ t, f (t + h) * specialValuePairing M hM t (-y)) =
      ∑ t, specialValuePairing M hM h y *
        (f (t + h) * specialValuePairing M hM (t + h) (-y)) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [L3.M75.Gaussian.pairing_add_left, FiniteFourierAux.pairing_neg_right M hM h y]
    field_simp [L3.M75.Gaussian.pairing_ne_zero M hM h y]
  have hshift : (∑ t, f (t + h) * specialValuePairing M hM (t + h) (-y)) =
      ∑ t, f t * specialValuePairing M hM t (-y) :=
    Fintype.sum_equiv (Equiv.addRight h) _ _ (fun _ => rfl)
  rw [hs, ← Finset.mul_sum, hshift]
  ring

/-- The square of the negative-kernel transform is reflection.
[RW-rec, §4]; [RW26, p. 15] gives `F² f(x) = f(-x)`. -/
theorem fourier_involution (f : SpecialValueGroup M → ℂ)
    (y : SpecialValueGroup M) :
    fourier M hM (fourier M hM f) y = f (-y) := by
  let := G2.StripCounting.specialGroupFintype M hM
  change (sqrtOrder M)⁻¹ *
    (∑ x, ((sqrtOrder M)⁻¹ * ∑ t, f t * specialValuePairing M hM t (-x)) *
      specialValuePairing M hM x (-y)) = f (-y)
  calc
    _ = (sqrtOrder M)⁻¹ * ((sqrtOrder M)⁻¹ *
        ∑ x, ∑ t, f t *
          (specialValuePairing M hM t (-x) * specialValuePairing M hM x (-y))) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = (sqrtOrder M)⁻¹ * ((sqrtOrder M)⁻¹ *
        ∑ t, f t * ∑ x,
          specialValuePairing M hM t (-x) * specialValuePairing M hM x (-y)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = (sqrtOrder M)⁻¹ * ((sqrtOrder M)⁻¹ *
        (f (-y) * (specialValueOrder M : ℂ))) := by
      simp [FiniteFourierAux.sum_kernel_product, mul_ite]
    _ = f (-y) := by
      rw [← G2DegenerateParametersAux.sqrt_order_sq M hM]
      change (sqrtOrder M)⁻¹ * ((sqrtOrder M)⁻¹ * (f (-y) * sqrtOrder M ^ 2)) = _
      field_simp [sqrtOrder, G2DegenerateParametersAux.sqrt_order_ne_zero M hM]

/-- Mixed reflection gives the inverse of the minus branch, including zero.
[RW26, (5), p. 3]; [RW-rec, (4)] is the form with two factors of `E`. -/
theorem inverse_minus (x : SpecialValueGroup M) :
    (specialValueMinus M hM x)⁻¹ =
      specialValueGaussian M hM x * specialValuePlus M hM (-x) := by
  apply inv_eq_of_mul_eq_one_right
  have hr := specialValue_mixed_reflection M hM (-x)
  rw [neg_neg, L3.M74.gaussian_neg] at hr
  calc
    specialValueMinus M hM x *
        (specialValueGaussian M hM x * specialValuePlus M hM (-x)) =
      specialValueGaussian M hM x *
        (specialValuePlus M hM (-x) * specialValueMinus M hM x) := by ring
    _ = 1 := by rw [hr, mul_inv_cancel₀ (L3.M75.Gaussian.gaussian_ne_zero M hM x)]

/-- The two branches differ at the zero class.
[RW-rec, Def. 1, (4)]; [RW26, (4), p. 3, footnote 2]. -/
theorem plus_minus_correction (x : SpecialValueGroup M) :
    specialValuePlus M hM x = specialValueMinus M hM x + sqrtOrder M * delta M x := by
  by_cases hx : x = 0
  · subst x
    simpa [sqrtOrder, delta, add_comm] using
      (sub_eq_iff_eq_add.mp (FiniteFourierAux.origin_difference M hM))
  · simp only [delta, if_neg hx, mul_zero, add_zero]
    exact specialValue_agree_off_zero M hM x hx

/-- Reflection for `E` equal to the plus branch, including the zero-class term.
[RW-rec, (4)]; [RW26, (4)--(5), p. 3, footnote 2]. -/
theorem actual_reflection (x : SpecialValueGroup M) :
    specialValuePlus M hM x * specialValuePlus M hM (-x) =
      (specialValueGaussian M hM x)⁻¹ +
        sqrtOrder M * specialValuePlus M hM 0 * delta M x := by
  rw [plus_minus_correction M hM (-x), mul_add, specialValue_mixed_reflection]
  by_cases hx : x = 0
  · subst x
    simp only [neg_zero, delta]
    ring
  · simp [delta, hx]

/-- [RW-rec, (5)] for every admissible matrix, with `etaMultiplier`.
[RW26, (6), pp. 3, 13]. -/
theorem actual_fourier (y : SpecialValueGroup M) :
    fourier M hM (specialValuePlus M hM) y =
      etaMultiplier M * specialValueGaussian M hM y * specialValuePlus M hM y := by
  have hf := G2.AttractingIdentities.attracting_fourier g1RealConclusion M hM (-y)
  have hsum : fourier M hM (specialValuePlus M hM) y =
      G2.SpecialValueBridge.normalizedValueSum M hM
        (fun x => specialValuePairing M hM x (-y) * specialValuePlus M hM x) := by
    unfold fourier
    congr 1
    funext x
    exact mul_comm _ _
  rw [hsum, hf, div_eq_mul_inv, inverse_minus, L3.M74.gaussian_neg, neg_neg]
  ring

/-- Pointwise reciprocal used in [RW-rec, §7], before any reduction.
[RW26, (4)--(5), p. 3]. -/
theorem actual_inverse (x : SpecialValueGroup M) :
    (specialValuePlus M hM x)⁻¹ =
      specialValueGaussian M hM x * specialValuePlus M hM (-x) - sqrtOrder M * delta M x := by
  by_cases hx : x = 0
  · subst x
    rw [L3.M74.gaussian_zero, one_mul, neg_zero, delta, if_pos rfl, mul_one]
    have hd := FiniteFourierAux.origin_difference M hM
    simp only [specialValuePlus_zero, specialValueMinus_zero] at hd ⊢
    change _ = _ - (Real.sqrt (specialValueOrder M : ℝ) : ℂ)
    linear_combination -hd
  · rw [specialValue_agree_off_zero M hM x hx, inverse_minus]
    simp [delta, hx]

/-- Fourier of the pointwise inverse, in the shape used in [RW-rec, §7].
[RW26, (6), p. 3].
The final term is the constant function `1`, not a delta. -/
theorem actual_inverse_fourier (y : SpecialValueGroup M) :
    fourier M hM (fun t => (specialValuePlus M hM t)⁻¹) y =
      (etaMultiplier M)⁻¹ * specialValuePlus M hM y - 1 := by
  have hg : (fun t => specialValueGaussian M hM t * specialValuePlus M hM (-t)) =
      (fun t => (etaMultiplier M)⁻¹ * fourier M hM (specialValuePlus M hM) (-t)) := by
    funext t
    rw [actual_fourier, L3.M74.gaussian_neg]
    field_simp [etaMultiplier_ne_zero M hM.1]
  have hi : (fun t => (specialValuePlus M hM t)⁻¹) =
      (fun t => (specialValueGaussian M hM t * specialValuePlus M hM (-t)) +
        (-sqrtOrder M) * delta M t) := by
    funext t
    rw [actual_inverse]
    ring
  have hreflect (f : SpecialValueGroup M → ℂ) :
      fourier M hM (fun t => f (-t)) y = fourier M hM f (-y) := by
    let := G2.StripCounting.specialGroupFintype M hM
    change (sqrtOrder M)⁻¹ * (∑ t, f (-t) * specialValuePairing M hM t (-y)) =
      (sqrtOrder M)⁻¹ * ∑ t, f t * specialValuePairing M hM t (-(-y))
    congr 1
    apply Fintype.sum_equiv (Equiv.neg _) _ _
    intro t
    simp only [Equiv.neg_apply, neg_neg, FiniteFourierAux.pairing_neg_left,
      FiniteFourierAux.pairing_neg_right]
  rw [hi, fourier_add, hg, fourier_mul_const, hreflect, fourier_involution,
    neg_neg, fourier_mul_const, fourier_delta]
  have hS : sqrtOrder M ≠ 0 := G2DegenerateParametersAux.sqrt_order_ne_zero M hM
  field_simp
  ring

end SICLean.L5.FiniteFourier
