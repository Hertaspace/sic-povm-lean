import SICLean.L4.M74Equations
import SICLean.L4.M75GaussianAux

set_option autoImplicit false

/-!
# The concrete Gaussian identities used in doubling

The proofs use the concrete integer-row formulas.
All symbols are the existing literal [RW26] row formulas, descended to the
actual quotient. No property of an unknown function E is an input here.
Additivity, polarization and the fourth power
are elementary consequences of that definition, not additional premises.
[RW26, p. 3, (3)].
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L3.M75.Gaussian

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)

/-- Nonvanishing needed for cancellation; [RW26, p. 3, (3)]. -/
theorem gaussian_ne_zero (x : L4.SpecialValueGroup M) :
    L4.specialValueGaussian M hM x ≠ 0 := by
  refine Quotient.inductionOn x ?_
  intro u
  change L4.specialValueGaussian M hM (L4.specialValueMk M u) ≠ 0
  rw [L4.specialValueGaussian_mk]
  exact L4.specialValueGaussianLift_ne_zero M u

/-- Literal character nonvanishing; [RW26, p. 3, (3)]. -/
theorem pairing_ne_zero (x y : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM x y ≠ 0 := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  change L4.specialValuePairing M hM (L4.specialValueMk M u) (L4.specialValueMk M v) ≠ 0
  rw [L4.specialValuePairing_mk]
  exact L4.e_ne_zero _

/-- Character at zero; [RW26, p. 3, (3)]. -/
theorem pairing_zero_right (x : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM x 0 = 1 := by
  refine Quotient.inductionOn x ?_
  intro u
  change L4.specialValuePairing M hM (L4.specialValueMk M u) (L4.specialValueMk M 0) = 1
  rw [L4.specialValuePairing_mk]
  simp [L4.specialValuePairingLift, L4.specialValueOmega, L4.e]

/-- Character at zero; [RW26, p. 3, (3)]. -/
theorem pairing_zero_left (x : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM 0 x = 1 := by
  refine Quotient.inductionOn x ?_
  intro u
  change L4.specialValuePairing M hM (L4.specialValueMk M 0) (L4.specialValueMk M u) = 1
  rw [L4.specialValuePairing_mk]
  simp [L4.specialValuePairingLift, L4.specialValueOmega, L2r.rowAction, L4.e]

/-- Bicharacter in its first variable; [RW26, p. 3, (3)]. -/
theorem pairing_add_left (x y z : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM (x + y) z =
      L4.specialValuePairing M hM x z * L4.specialValuePairing M hM y z := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  refine Quotient.inductionOn z ?_
  intro w
  change L4.specialValuePairing M hM (L4.specialValueMk M (u + v))
      (L4.specialValueMk M w) =
    L4.specialValuePairing M hM (L4.specialValueMk M u) (L4.specialValueMk M w) *
      L4.specialValuePairing M hM (L4.specialValueMk M v) (L4.specialValueMk M w)
  simp only [L4.specialValuePairing_mk]
  exact L4.M75GaussianAux.pairingLift_add_left M u v w

/-- Bicharacter in its second variable; [RW26, p. 3, (3)]. -/
theorem pairing_add_right (x y z : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM x (y + z) =
      L4.specialValuePairing M hM x y * L4.specialValuePairing M hM x z := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  refine Quotient.inductionOn z ?_
  intro w
  change L4.specialValuePairing M hM (L4.specialValueMk M u)
      (L4.specialValueMk M (v + w)) =
    L4.specialValuePairing M hM (L4.specialValueMk M u) (L4.specialValueMk M v) *
      L4.specialValuePairing M hM (L4.specialValueMk M u) (L4.specialValueMk M w)
  simp only [L4.specialValuePairing_mk]
  exact L4.M75GaussianAux.pairingLift_add_right M u v w

/--
Symmetry includes the row convention's positive sign; [RW26, p. 3, (3)].
-/
theorem pairing_symmetric (x y : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM x y = L4.specialValuePairing M hM y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  change L4.specialValuePairing M hM (L4.specialValueMk M u) (L4.specialValueMk M v) =
    L4.specialValuePairing M hM (L4.specialValueMk M v) (L4.specialValueMk M u)
  simp only [L4.specialValuePairing_mk]
  exact L4.M75GaussianAux.pairingLift_symmetric M hM u v

/--
Polarization of the actual Gaussian, not a definition of a new pairing; [RW26, p. 3, (3)].
-/
theorem gaussian_add (x y : L4.SpecialValueGroup M) :
    L4.specialValueGaussian M hM (x + y) =
      L4.specialValueGaussian M hM x * L4.specialValueGaussian M hM y *
        L4.specialValuePairing M hM x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  change L4.specialValueGaussian M hM (L4.specialValueMk M (u + v)) =
    L4.specialValueGaussian M hM (L4.specialValueMk M u) *
      L4.specialValueGaussian M hM (L4.specialValueMk M v) *
        L4.specialValuePairing M hM (L4.specialValueMk M u) (L4.specialValueMk M v)
  simp only [L4.specialValueGaussian_mk, L4.specialValuePairing_mk]
  exact L4.M75GaussianAux.gaussianLift_add M hM u v

/--
Subtraction form needed for s-u, with evenness from M74.gaussian_neg; [RW26, p. 3, (3)].
-/
theorem gaussian_sub (x y : L4.SpecialValueGroup M) :
    L4.specialValueGaussian M hM (x - y) =
      L4.specialValueGaussian M hM x * L4.specialValueGaussian M hM y *
        (L4.specialValuePairing M hM x y)⁻¹ := by
  have hp : L4.specialValuePairing M hM x (-y) =
      (L4.specialValuePairing M hM x y)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← pairing_add_right M hM, add_neg_cancel, pairing_zero_right]
  rw [sub_eq_add_neg, gaussian_add, M74.gaussian_neg, hp]

/--
Diagonal character equals the square of the Gaussian; [RW26, p. 3, (3)].
-/
theorem pairing_self (x : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM x x = L4.specialValueGaussian M hM x ^ 2 := by
  refine Quotient.inductionOn x ?_
  intro u
  change L4.specialValuePairing M hM (L4.specialValueMk M u) (L4.specialValueMk M u) =
    L4.specialValueGaussian M hM (L4.specialValueMk M u) ^ 2
  rw [L4.specialValuePairing_mk, L4.specialValueGaussian_mk]
  exact L4.M75GaussianAux.pairingLift_self M hM u

/--
Doubling equals the fourth power, also when x+x=0; [RW26, p. 3, (3)].
-/
theorem gaussian_double (x : L4.SpecialValueGroup M) :
    L4.specialValueGaussian M hM (x + x) = L4.specialValueGaussian M hM x ^ 4 := by
  rw [gaussian_add, pairing_self]
  ring

/--
The exact phase after t=u+s; no parity or nonzero assumptions; [RW26, p. 3, (3)].
-/
theorem doubling_phase (u s : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM (u + s) u * L4.specialValueGaussian M hM (s - u) =
      L4.specialValueGaussian M hM u ^ 3 * L4.specialValueGaussian M hM s := by
  rw [pairing_add_left, pairing_self, gaussian_sub]
  have hB := pairing_ne_zero M hM s u
  field_simp [hB]

#print L4.specialValueGaussianLift
#print L4.specialValuePairingLift
#check @M74.gaussian_neg
#check @gaussian_double
#check @doubling_phase

end SICLean.L3.M75.Gaussian
