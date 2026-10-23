import SICLean.L5.LocalFourierSetup
import SICLean.L5.PrimeValuation

set_option autoImplicit false

/-!
# Local arithmetic for the finite split-Frobenius statements

The additive/multiplicative comparison uses the explicit normalized order in
`FinitePlace`, including the value at zero. The power rule is only asserted for integral
elements of the actual valuation ring.
-/

noncomputable section

namespace SICLean.L5.SplitFrobeniusFiniteAux

variable {L : Type*} [Field L] [NumberField L]

theorem congruent_iff_multiplicative_lt (P : FinitePlace.Prime L) (x y : L) :
    FinitePlace.Congruent P x y ↔ P.valuation L (x - y) < 1 := by
  classical
  have he : 0 < (FinitePlace.absoluteRamification P : ℝ) := by
    exact_mod_cast FinitePlace.absoluteRamification_pos P
  change 0 < FinitePlace.valuationFun P (x - y) ↔ _
  by_cases hxy : x - y = 0
  · simp [hxy, FinitePlace.valuationFun, FinitePlace.ord_zero]
  · simp only [FinitePlace.valuationFun, FinitePlace.ord, ite_eq_right hxy,
      WithTop.map_coe, ← WithTop.coe_zero, WithTop.coe_lt_coe,
      div_pos_iff_of_pos_right he, Int.cast_pos, neg_pos]
    rw [← WithZero.log_one,
      WithZero.log_lt_log ((Valuation.ne_zero_iff _).mpr hxy) one_ne_zero]

theorem reduce_pow {A : Type*} [Field A] (v : AddValuation A (WithTop ℝ))
    (a : A) (ha : 0 ≤ v a) (n : ℕ) :
    LocalFourierSetup.reduce v (a ^ n) = LocalFourierSetup.reduce v a ^ n := by
  have hn : 0 ≤ v (a ^ n) := (LocalFourierSetup.integers v).pow_mem ha n
  unfold LocalFourierSetup.reduce
  rw [dite_eq_left hn, dite_eq_left ha]
  exact map_pow (IsLocalRing.residue (LocalFourierSetup.integers v))
    (⟨a, ha⟩ : LocalFourierSetup.integers v) n

end SICLean.L5.SplitFrobeniusFiniteAux
