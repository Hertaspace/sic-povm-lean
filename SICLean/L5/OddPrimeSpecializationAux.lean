import SICLean.L5.GoodReductionLocal
import SICLean.L5.PrimeValuation

set_option autoImplicit false

/-!
# Finite-prime dictionary for odd-prime specialization

The normalized additive valuation and the multiplicative adic valuation define the same
local integrality and units. The residue characteristic also equals the norm of the
contracted integer ideal.
-/

noncomputable section

namespace SICLean.L5.OddPrimeSpecializationAux

/-- The additive normalization preserves the local valuation ring. -/
theorem integralAt_iff_goodReduction (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    (Q : FinitePlace.Prime F) (a : F) :
    FinitePlace.IntegralAt Q a ↔ GoodReductionLocal.localIntegral F Q a := by
  classical
  rw [FinitePlace.integralAt_iff_ord_nonneg]
  by_cases ha : a = 0
  · subst a
    simp [FinitePlace.ord_zero, GoodReductionLocal.localIntegral]
  have hav : Q.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  simp only [FinitePlace.ord, ite_eq_right ha, ← WithTop.coe_zero, WithTop.coe_le_coe,
    neg_nonneg, GoodReductionLocal.localIntegral]
  rw [← WithZero.log_one, WithZero.log_le_log hav one_ne_zero]

/-- Zero additive order is exactly multiplicative valuation one. -/
theorem unitAt_iff_multiplicative_one (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    (Q : FinitePlace.Prime F) (a : F) :
    FinitePlace.UnitAt Q a ↔ Q.valuation F a = 1 := by
  classical
  rw [FinitePlace.unitAt_iff_ord_zero]
  by_cases ha : a = 0
  · subst a
    simp [FinitePlace.ord_zero]
  have hav : Q.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  simp only [FinitePlace.ord, ite_eq_right ha, ← WithTop.coe_zero, WithTop.coe_eq_coe,
    neg_eq_zero]
  constructor
  · intro h
    calc
      Q.valuation F a = WithZero.exp (WithZero.log (Q.valuation F a)) :=
        (WithZero.exp_log hav).symm
      _ = 1 := by rw [h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

/-- Both APIs take the characteristic of the same contracted integer ideal. -/
theorem residueChar_eq_primeBelow (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    (Q : FinitePlace.Prime F) :
    FinitePlace.residueChar Q = GoodReductionLocal.primeBelow F Q := by
  exact Ideal.ringChar_quot Q.asIdeal

end SICLean.L5.OddPrimeSpecializationAux
