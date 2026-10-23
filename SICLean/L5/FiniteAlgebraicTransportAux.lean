import SICLean.L5.FiniteFourier

set_option autoImplicit false

/-!
# Algebraicity of the concrete finite coefficients

The Gaussian satisfies the finite-order relation [RW26, (3), p. 3].
Its polarization gives algebraicity of the positive-sign pairing.
The eta multiplier satisfies its twenty-fourth-power relation, and the
prescribed positive square root satisfies the integer equation `X^2 - N = 0`.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L5.FiniteAlgebraicTransportAux

open L4

/-- The finite order of the Gaussian gives its algebraicity over `ℚ`. -/
theorem gaussian_isAlgebraic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    IsAlgebraic ℚ (specialValueGaussian M hM x) := by
  have hN : 0 < (specialValueOrder M).toNat := by
    have := specialValueOrder_pos M hM
    omega
  apply IsAlgebraic.of_pow (n := 2 * (specialValueOrder M).toNat)
    (mul_pos (by norm_num) hN)
  rw [L3.M74.gaussian_order M hM x]
  exact isAlgebraic_one

/-- Polarization of the same Gaussian gives the literal pairing coefficient. -/
theorem pairing_isAlgebraic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x y : SpecialValueGroup M) :
    IsAlgebraic ℚ (specialValuePairing M hM x y) := by
  have hden : specialValueGaussian M hM x * specialValueGaussian M hM y ≠ 0 :=
    mul_ne_zero (L3.M75.Gaussian.gaussian_ne_zero M hM x)
      (L3.M75.Gaussian.gaussian_ne_zero M hM y)
  have hpair : specialValuePairing M hM x y =
      specialValueGaussian M hM (x + y) /
        (specialValueGaussian M hM x * specialValueGaussian M hM y) := by
    apply (eq_div_iff hden).2
    rw [L3.M75.Gaussian.gaussian_add M hM x y]
    ring
  rw [hpair, div_eq_mul_inv]
  exact (gaussian_isAlgebraic M hM (x + y)).mul
    ((gaussian_isAlgebraic M hM x).mul (gaussian_isAlgebraic M hM y)).inv

/-- The eta multiplier is algebraic for every admissible matrix. -/
theorem multiplier_isAlgebraic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    IsAlgebraic ℚ (etaMultiplier M) :=
  etaMultiplier_isAlgebraic M hM.1

/-- The prescribed positive real square root has algebraic square. -/
theorem sqrtOrder_isAlgebraic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    IsAlgebraic ℚ (FiniteFourier.sqrtOrder M) := by
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  have hN : 0 ≤ (specialValueOrder M : ℝ) := by
    exact_mod_cast (specialValueOrder_pos M hM).le
  have hsq : FiniteFourier.sqrtOrder M ^ 2 = (specialValueOrder M : ℂ) := by
    simp only [FiniteFourier.sqrtOrder, ← Complex.ofReal_pow, Real.sq_sqrt hN,
      Complex.ofReal_intCast]
  rw [hsq]
  exact isAlgebraic_intCast (specialValueOrder M)

/-- All four coefficients admit preimages in the fixed algebraic closure. -/
theorem coefficients_isAlgebraic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x y : SpecialValueGroup M) :
    IsAlgebraic ℚ (specialValueGaussian M hM x) ∧
      IsAlgebraic ℚ (specialValuePairing M hM x y) ∧
      IsAlgebraic ℚ (etaMultiplier M) ∧
      IsAlgebraic ℚ (FiniteFourier.sqrtOrder M) :=
  ⟨gaussian_isAlgebraic M hM x, pairing_isAlgebraic M hM x y,
    multiplier_isAlgebraic M hM, sqrtOrder_isAlgebraic M hM⟩

end SICLean.L5.FiniteAlgebraicTransportAux
