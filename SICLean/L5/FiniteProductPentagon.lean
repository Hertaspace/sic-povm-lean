import SICLean.L5.FiniteFourier
import SICLean.L5.FiniteProductPentagonAux

set_option autoImplicit false

/-!
# Ratio and product pentagon identities

[RW-rec, Prop. 1, (6)] and [RW26, (36), p. 18], with [RW26, (7), p. 3].
The identities use the same point values as `FiniteFourier`, including the origin.
-/

noncomputable section

open Classical
open scoped BigOperators MatrixGroups

namespace SICLean.L5.FiniteProductPentagon

open L4 FiniteFourier

/-- The positive-kernel ratio sum, with the minus branch in the denominator. -/
def ratioSum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : SpecialValueGroup M) : ℂ :=
  G2.SpecialValueBridge.normalizedValueSum M hM (fun t =>
    specialValuePairing M hM t u *
      (specialValuePlus M hM t / specialValueMinus M hM (t + v)))

/-- Left-hand side of [RW-rec, Prop. 1, (6)]: the pairing uses a positive `y`. -/
def productSum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x y : SpecialValueGroup M) : ℂ :=
  G2.SpecialValueBridge.normalizedValueSum M hM (fun t =>
    specialValuePlus M hM t * specialValueGaussian M hM t *
      specialValuePlus M hM (x - t) * specialValuePairing M hM t y)

variable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)

/-- The ratio identity for the point values.
[RW-rec, Prop. 1, (6)]; [RW26, (7), p. 3]. -/
theorem actual_ratio (u v : SpecialValueGroup M) :
    ratioSum M hM u v =
      specialValuePlus M hM (u + v) /
        (specialValueMinus M hM u * specialValueMinus M hM v) -
      (specialValueOrder M : ℂ) * specialValuePlus M hM 0 * delta M u * delta M v := by
  have h := G2.AttractingIdentities.attracting_pentagon g1RealConclusion M hM u v
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;>
    simpa [ratioSum, delta, hu, hv] using h

/-- Substitution `u = x + y`, `v = -x`.
[RW-rec, Prop. 1, (6)]; [RW26, (7), p. 3]; [RW26, (36), p. 18]. -/
theorem ratio_at_product_indices (x y : SpecialValueGroup M) :
    ratioSum M hM (x + y) (-x) =
      specialValuePlus M hM y /
        (specialValueMinus M hM (x + y) * specialValueMinus M hM (-x)) -
      (specialValueOrder M : ℂ) * specialValuePlus M hM 0 *
        delta M (x + y) * delta M (-x) := by
  have hidx : x + y + -x = y := by abel
  simpa only [hidx] using actual_ratio M hM (x + y) (-x)

/-- Summand identity, including `t - x = 0`, using the inverse of the minus branch.
[RW-rec, Prop. 1, (6)]; [RW26, (36), p. 18]; [RW26, (3), p. 3]. -/
theorem summand_conversion (x y t : SpecialValueGroup M) :
    specialValuePairing M hM t (x + y) *
        (specialValuePlus M hM t / specialValueMinus M hM (t - x)) =
      specialValueGaussian M hM x *
        (specialValuePlus M hM t * specialValueGaussian M hM t *
          specialValuePlus M hM (x - t) * specialValuePairing M hM t y) := by
  rw [div_eq_mul_inv, L3.M75.Doubling.minus_inv,
    L3.M75.Gaussian.pairing_add_right, L3.M75.Gaussian.gaussian_sub, neg_sub]
  have hB := L3.M75.Gaussian.pairing_ne_zero M hM t x
  field_simp [hB]

/-- The main ratio term acquires the same `q(x)` factor, including at zero.
[RW-rec, Prop. 1, (6)]; [RW26, (36), p. 18]. -/
theorem main_term_conversion (x y : SpecialValueGroup M) :
    specialValuePlus M hM y /
        (specialValueMinus M hM (x + y) * specialValueMinus M hM (-x)) =
      specialValueGaussian M hM x *
        (specialValueGaussian M hM (x + y) * specialValuePlus M hM (-x - y) *
          specialValuePlus M hM x * specialValuePlus M hM y) := by
  have hidx : -(x + y) = -x - y := by abel
  rw [div_eq_mul_inv, mul_inv, L3.M75.Doubling.minus_inv,
    L3.M75.Doubling.minus_inv, L3.M74.gaussian_neg, neg_neg, hidx]
  ring

/-- The simultaneous zero condition is preserved by the substitution.
[RW-rec, Prop. 1, (6)]; [RW26, (36), p. 18]. -/
theorem delta_conversion (x y : SpecialValueGroup M) :
    delta M (x + y) * delta M (-x) = delta M x * delta M y := by
  by_cases hx : x = 0
  · subst x
    simp [delta]
  · simp [delta, hx, neg_ne_zero.mpr hx]

/-- Finite-sum conversion between the ratio sum and the product sum.
[RW-rec, Prop. 1, (6)]; [RW26, (36), p. 18]. -/
theorem sum_conversion (x y : SpecialValueGroup M) :
    ratioSum M hM (x + y) (-x) = specialValueGaussian M hM x * productSum M hM x y := by
  unfold ratioSum productSum G2.SpecialValueBridge.normalizedValueSum
  simp_rw [← sub_eq_add_neg, summand_conversion]
  rw [← Finset.mul_sum]
  ring

/-- The ratio identities and the product identities are equivalent,
including the origin and the minus branch.
[RW-rec, Prop. 1, (6)]; [RW26, (7), p. 3]; [RW26, (36), p. 18]. -/
theorem ratio_iff_product :
    (∀ u v : SpecialValueGroup M,
      ratioSum M hM u v =
        specialValuePlus M hM (u + v) /
          (specialValueMinus M hM u * specialValueMinus M hM v) -
        (specialValueOrder M : ℂ) * specialValuePlus M hM 0 * delta M u * delta M v) ↔
    (∀ x y : SpecialValueGroup M,
      productSum M hM x y =
        specialValueGaussian M hM (x + y) * specialValuePlus M hM (-x - y) *
          specialValuePlus M hM x * specialValuePlus M hM y -
        (specialValueOrder M : ℂ) * specialValuePlus M hM 0 * delta M x * delta M y) := by
  have hcorrection (x y : SpecialValueGroup M) :
      (specialValueOrder M : ℂ) * specialValuePlus M hM 0 *
          delta M (x + y) * delta M (-x) =
        specialValueGaussian M hM x *
          ((specialValueOrder M : ℂ) * specialValuePlus M hM 0 * delta M x * delta M y) := by
    calc
      _ = (specialValueOrder M : ℂ) * specialValuePlus M hM 0 *
          (delta M (x + y) * delta M (-x)) := by ring
      _ = (specialValueOrder M : ℂ) * specialValuePlus M hM 0 *
          (delta M x * delta M y) := by rw [delta_conversion]
      _ = (specialValueOrder M : ℂ) * specialValuePlus M hM 0 *
          ((specialValueGaussian M hM x * delta M x) * delta M y) := by
        rw [FiniteProductPentagonAux.gaussian_mul_delta]
      _ = _ := by ring
  constructor
  · intro hratio x y
    have h := hratio (x + y) (-x)
    have hidx : x + y + -x = y := by abel
    rw [sum_conversion, hidx, main_term_conversion, hcorrection, ← mul_sub] at h
    exact mul_left_cancel₀ (L3.M75.Gaussian.gaussian_ne_zero M hM x) h
  · intro hproduct u v
    have h (x y : SpecialValueGroup M) :
        ratioSum M hM (x + y) (-x) =
          specialValuePlus M hM (x + y + -x) /
            (specialValueMinus M hM (x + y) * specialValueMinus M hM (-x)) -
          (specialValueOrder M : ℂ) * specialValuePlus M hM 0 *
            delta M (x + y) * delta M (-x) := by
      have hidx : x + y + -x = y := by abel
      rw [hidx, sum_conversion, main_term_conversion, hcorrection, ← mul_sub,
        hproduct]
    have hidx : -v + (u + v) = u := by abel
    simpa only [hidx, neg_neg] using h (-v) (u + v)

/-- [RW-rec, Prop. 1, (6)], for the values of every admissible matrix.
[RW26, (36), p. 18]. -/
theorem actual_product (x y : SpecialValueGroup M) :
    productSum M hM x y =
      specialValueGaussian M hM (x + y) * specialValuePlus M hM (-x - y) *
        specialValuePlus M hM x * specialValuePlus M hM y -
      (specialValueOrder M : ℂ) * specialValuePlus M hM 0 * delta M x * delta M y := by
  exact (ratio_iff_product M hM).mp (actual_ratio M hM) x y

/-- Negative-kernel Fourier form of (6): the argument is `-y`.
[RW-rec, Prop. 1, (6)]; [RW26, p. 15]; [RW26, (36), p. 18]. -/
theorem actual_product_fourier (x y : SpecialValueGroup M) :
    fourier M hM (fun t => specialValuePlus M hM t * specialValueGaussian M hM t *
      specialValuePlus M hM (x - t)) (-y) =
      specialValueGaussian M hM (x + y) * specialValuePlus M hM (-x - y) *
        specialValuePlus M hM x * specialValuePlus M hM y -
      (specialValueOrder M : ℂ) * specialValuePlus M hM 0 * delta M x * delta M y := by
  simpa only [FiniteFourier.fourier, neg_neg, productSum] using actual_product M hM x y

/-- The origin is included in the identity.
[RW-rec, Prop. 1, (6)]; [RW26, (36), p. 18]. -/
theorem product_origin :
    productSum M hM 0 0 = specialValuePlus M hM 0 ^ 3 -
      (specialValueOrder M : ℂ) * specialValuePlus M hM 0 := by
  simpa [delta, L3.M74.gaussian_zero, pow_succ] using actual_product M hM 0 0

/-- When `x` and `y` are not both zero, the origin term is absent.
[RW-rec, Prop. 1, (6)]; [RW26, (36), p. 18]. -/
theorem product_off_origin (x y : SpecialValueGroup M) (hxy : x ≠ 0 ∨ y ≠ 0) :
    productSum M hM x y =
      specialValueGaussian M hM (x + y) * specialValuePlus M hM (-x - y) *
        specialValuePlus M hM x * specialValuePlus M hM y := by
  rcases hxy with hx | hy
  · simpa [delta, hx] using actual_product M hM x y
  · simpa [delta, hy] using actual_product M hM x y

/-- Without the origin term, the two sides differ at `(0, 0)`.
[RW-rec, Prop. 1, (6)]; [RW26, (36), p. 18]. -/
theorem uncorrected_origin_fails :
    productSum M hM 0 0 ≠ specialValuePlus M hM 0 ^ 3 := by
  rw [product_origin]
  have hN : (specialValueOrder M : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (specialValueOrder_pos M hM)
  exact fun h => (mul_ne_zero hN (specialValuePlus_ne_zero M hM 0))
    ((sub_eq_self.mp h))

#print productSum
#check @ratio_iff_product
#check @actual_product
#check @actual_product_fourier

end SICLean.L5.FiniteProductPentagon
