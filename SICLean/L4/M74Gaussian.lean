import SICLean.L4.M74Normalization

set_option autoImplicit false

/-!
# The actual Gaussian for every representative

The Gaussian is the pullback of the existing literal [RW26, (3)] definition,
through the specified additive equivalence. Neither E nor reflection is
used to define it. The 2N exponent is common to the entire finite family.

[RW26, p. 3, (3)].
The negative and power identities are elementary consequences of (3).
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L3.M74

universe u

variable {K : Type u} [Field K] [NumberField K] {P : PeriodData K}

/--
Literal row formula is even, including its integer parity factor; [RW26, p. 3, (3)].
-/
theorem gaussianLift_neg (M : SL(2, ℤ)) (v : ℤ × ℤ) :
    L4.specialValueGaussianLift M (-v) = L4.specialValueGaussianLift M v := by
  have hparity :
      (-1 : ℂ) ^ ((-v).1 + (-v).2 + (-v).1 * (-v).2) =
        (-1 : ℂ) ^ (v.1 + v.2 + v.1 * v.2) := by
    change (-1 : ℂ) ^ (-v.1 + -v.2 + -v.1 * -v.2) = _
    rw [show -v.1 + -v.2 + -v.1 * -v.2 =
        (v.1 + v.2 + v.1 * v.2) + 2 * (-v.1 - v.2) by ring,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
    norm_num
  have homega :
      L4.specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (-v)) (-v) =
        L4.specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) v) v := by
    simp only [L4.specialValueOmega, L2r.rowAction, Prod.fst_neg, Prod.snd_neg]
    ring
  unfold L4.specialValueGaussianLift
  rw [hparity, homega]

/--
Root order follows from the integer numerator in [RW26, (3)].
 [RW26, p. 3, (3)].
-/
theorem gaussianLift_order (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (v : ℤ × ℤ) :
    L4.specialValueGaussianLift M v ^ (2 * (L4.specialValueOrder M).toNat) = 1 := by
  have hpos : 0 < L4.specialValueOrder M := sub_pos.mpr hM.2
  have hN : (L4.specialValueOrder M : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hcast : ((L4.specialValueOrder M).toNat : ℂ) = (L4.specialValueOrder M : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hpos.le
  have hparity :
      ((-1 : ℂ) ^ (v.1 + v.2 + v.1 * v.2)) ^
        (2 * (L4.specialValueOrder M).toNat) = 1 := by
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> simp [pow_mul]
  unfold L4.specialValueGaussianLift
  rw [mul_pow, hparity, one_mul, L4.e_nat_mul]
  rw [Nat.cast_mul, Nat.cast_ofNat, hcast,
    mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hN)]
  exact L4.e_intCast _

/--
Quotient origin is the literal Gaussian value 1; [RW26, p. 3, (3)].
-/
theorem gaussian_zero (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    L4.specialValueGaussian M hM 0 = 1 := by
  simpa only [map_zero] using
    (L4.specialValueGaussian_mk M hM 0).trans (L4.specialValueGaussianLift_zero M)

/--
Evenness survives descent, with no complex conjugation; [RW26, p. 3, (3)].
-/
theorem gaussian_neg (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : L4.SpecialValueGroup M) :
    L4.specialValueGaussian M hM (-x) = L4.specialValueGaussian M hM x := by
  refine Quotient.inductionOn x ?_
  intro v
  change L4.specialValueGaussian M hM (L4.specialValueMk M (-v)) =
    L4.specialValueGaussian M hM (L4.specialValueMk M v)
  rw [L4.specialValueGaussian_mk, L4.specialValueGaussian_mk, gaussianLift_neg]

/--
Descent of the exact finite order, not a modulus-one assertion.
 [RW26, p. 3, (3)].
-/
theorem gaussian_order (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : L4.SpecialValueGroup M) :
    L4.specialValueGaussian M hM x ^ (2 * (L4.specialValueOrder M).toNat) = 1 := by
  refine Quotient.inductionOn x ?_
  intro v
  change L4.specialValueGaussian M hM (L4.specialValueMk M v) ^ _ = 1
  rw [L4.specialValueGaussian_mk]
  exact gaussianLift_order M hM v

/--
Explicit transport of the existing [RW26] Gaussian. No analytic values
or Gaussian laws are inputs or fields of this definition.
-/
def basisGaussian (B : L4.DistributionBasis) (hB : B.Valid)
    (x : L4.DistributionGroup B) : ℂ :=
  L4.specialValueGaussian B.matrix (basis_admissible B hB)
    ((basisRowEquiv B hB).symm x)

/--
Actual representative formula fixes the label and the phase; [RW26, p. 3, (3)].
-/
theorem basisGaussian_mk (B : L4.DistributionBasis) (hB : B.Valid) (v : ℤ × ℤ) :
    basisGaussian B hB
        (L4.distributionMk B (L4.distributionRowPoint B v)
          (L4.distributionRowPoint_mem B hB v)) =
      L4.specialValueGaussianLift B.matrix v := by
  unfold basisGaussian
  rw [← basisRowEquiv_mk B hB v, AddEquiv.symm_apply_apply, L4.specialValueGaussian_mk]

/--
Actual pseudolattice quotient origin; [RW26, p. 3, (3)].
-/
theorem basisGaussian_zero (B : L4.DistributionBasis) (hB : B.Valid) :
    basisGaussian B hB 0 = 1 := by
  simp only [basisGaussian, map_zero, gaussian_zero]

/--
Actual pseudolattice negative label; [RW26, p. 3, (3)].
-/
theorem basisGaussian_neg (B : L4.DistributionBasis) (hB : B.Valid)
    (x : L4.DistributionGroup B) :
    basisGaussian B hB (-x) = basisGaussian B hB x := by
  simp only [basisGaussian, map_neg, gaussian_neg]

/--
Actual pseudolattice Gaussian finite order;
[RW26, p. 3, (3)].
-/
theorem basisGaussian_order (B : L4.DistributionBasis) (hB : B.Valid)
    (x : L4.DistributionGroup B) :
    basisGaussian B hB x ^ (2 * (L4.specialValueOrder B.matrix).toNat) = 1 := by
  exact gaussian_order B.matrix (basis_admissible B hB) ((basisRowEquiv B hB).symm x)

/-- The only Gaussian used in the finite-family coefficient field. -/
def familyGaussian (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (x : PseudolatticeFamilyGroup F i) : ℂ :=
  basisGaussian (pseudolatticeFamilyBasis F i) (familyBasis_valid F i) x

/--
Uniform field input, including every representative; [RW26, p. 3, (3)].
-/
theorem familyGaussian_zero (F : FinitePseudolatticeFamily P) :
    ∀ i, familyGaussian F i 0 = 1 := by
  intro i
  exact basisGaussian_zero (pseudolatticeFamilyBasis F i) (familyBasis_valid F i)

/--
Uniform negative symmetry; no assumption that the group is cyclic; [RW26, p. 3, (3)].
-/
theorem familyGaussian_neg (F : FinitePseudolatticeFamily P) :
    ∀ i (x : PseudolatticeFamilyGroup F i),
      familyGaussian F i (-x) = familyGaussian F i x := by
  intro i x
  exact basisGaussian_neg (pseudolatticeFamilyBasis F i) (familyBasis_valid F i) x

/--
The exponent uses PeriodData.N for all matrices; [RW26, p. 3, (3)].
-/
theorem familyGaussian_order (F : FinitePseudolatticeFamily P) :
    ∀ i (x : PseudolatticeFamilyGroup F i), familyGaussian F i x ^ (2 * P.N) = 1 := by
  intro i x
  have h := basisGaussian_order (pseudolatticeFamilyBasis F i) (familyBasis_valid F i) x
  rw [familyBasis_order_toNat F i] at h
  exact h

#print L4.specialValueGaussianLift
#print basisGaussian
#print familyGaussian
#check @familyGaussian_order

end SICLean.L3.M74
