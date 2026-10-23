import SICLean.L3.PseudolatticeFamily
import SICLean.L4.SpecialValueReflection
import SICLean.L4.M74NormalizationAux

set_option autoImplicit false

/-!
# The common order and the attracting positive root

These are bridges between the statements.
The numerical period is fixed by PeriodData, rather than chosen anew
for each representative. The condition period > 1 selects the attracting
fixed point. All square roots below are the existing positive real roots;
the actual modularPhi, phiExtended and etaMultiplier are unchanged. [RW26, p. 2, p. 3, (2),
(3)--(4)].

Names are in the `L3.M74` namespace.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L3.M74

universe u

variable {K : Type u} [Field K] [NumberField K] {P : PeriodData K}

/--
Entry-positivity part of the actual basis conditions; [RW26, p. 2, (2)].
-/
theorem basis_admissible (B : L4.DistributionBasis) (hB : B.Valid) :
    L4.SpecialValueAdmissible B.matrix := by
  exact ⟨hB.1, hB.2.1⟩

/--
The period > 1 condition excludes the repelling fixed point; [RW26, p. 2, p. 3, (2), (4)].
-/
theorem basis_tau (B : L4.DistributionBasis) (hB : B.Valid) :
    B.tau = L4.specialValueTau B.matrix := by
  have hM := basis_admissible B hB
  have hx : 1 < L4.distributionPeriod B := hB.2.2.2.1
  have hx0 : L4.distributionPeriod B ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one hx)
  have htrace := (L4.distributionBasis_spectral B hB).2.2.2
  have hy := L4.specialValueEpsilon_gt_one B.matrix hM
  have hpoly := L4.specialValueEpsilon_characteristic B.matrix hM
  have horder : (L4.specialValueOrder B.matrix : ℝ) + 2 =
      (B.matrix 0 0 : ℝ) + (B.matrix 1 1 : ℝ) := by
    simp only [L4.specialValueOrder, Int.cast_sub, Int.cast_add, Int.cast_ofNat]
    ring
  rw [horder, ← htrace] at hpoly
  have hprod :
      (L4.specialValueEpsilon B.matrix - L4.distributionPeriod B) *
        (L4.specialValueEpsilon B.matrix -
          (L4.distributionPeriod B)⁻¹) = 0 := by
    nlinarith [mul_inv_cancel₀ hx0]
  have hperiod :
      L4.distributionPeriod B = L4.specialValueEpsilon B.matrix := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · have hinv := inv_lt_one_of_one_lt₀ hx
      linarith
  have hc : 0 < (B.matrix 1 0 : ℝ) := by
    exact_mod_cast hB.1
  dsimp only [L4.distributionPeriod, L4.specialValueEpsilon] at hperiod
  nlinarith

/--
The same automorphy factor, after choosing the attracting root; [RW26, p. 2, (2)].
-/
theorem basis_epsilon (B : L4.DistributionBasis) (hB : B.Valid) :
    L4.distributionPeriod B = L4.specialValueEpsilon B.matrix := by
  unfold L4.distributionPeriod L4.specialValueEpsilon
  rw [basis_tau B hB]

/--
Concrete choice from the row-point correspondence.
Its only input is the actual valid basis, with no value identity assumed.
-/
def basisRowEquiv (B : L4.DistributionBasis) (hB : B.Valid) :
    L4.SpecialValueGroup B.matrix ≃+ L4.DistributionGroup B :=
  Classical.choose (L4.distributionRowGroup_equiv B hB)

/--
Fixes this choice on every row, including zero and lattice rows; [RW26, p. 3, p. 12, (3), Lemma 2].
-/
theorem basisRowEquiv_mk (B : L4.DistributionBasis) (hB : B.Valid)
    (v : ℤ × ℤ) :
    basisRowEquiv B hB (L4.specialValueMk B.matrix v) =
      L4.distributionMk B (L4.distributionRowPoint B v)
        (L4.distributionRowPoint_mem B hB v) := by
  exact Classical.choose_spec (L4.distributionRowGroup_equiv B hB) v

/--
Geometric validity for every representative. [RW26, p. 2, (2)].
-/
theorem familyBasis_valid (F : FinitePseudolatticeFamily P) (i : Fin F.size) :
    (pseudolatticeFamilyBasis F i).Valid := by
  exact (pseudolatticeFamilyBasis_spec F i).1

/--
All representatives use one specified period, not just equal traces; [RW26, p. 23, Theorem 11].
-/
theorem familyBasis_period (F : FinitePseudolatticeFamily P) (i : Fin F.size) :
    L4.distributionPeriod (pseudolatticeFamilyBasis F i) = P.sigma₁ P.epsilon := by
  exact (pseudolatticeFamilyBasis_spec F i).2.1

/--
N=tr(gamma)-2 is the fixed arithmetic N for every family member; [RW26, p. 2, p. 3, (2), (3)].
-/
theorem familyBasis_order (F : FinitePseudolatticeFamily P) (i : Fin F.size) :
    L4.specialValueOrder (pseudolatticeFamilyBasis F i).matrix = (P.N : ℤ) := by
  have hp := congrArg P.sigma₁ P.epsilon_polynomial
  simp only [map_sub, map_pow, map_mul, map_add, map_natCast, map_ofNat,
    map_one, map_zero] at hp
  have he0 : P.sigma₁ P.epsilon ≠ 0 := ne_of_gt (lt_trans zero_lt_one P.epsilon_gt_one)
  have hs := (L4.distributionBasis_spectral _ (familyBasis_valid F i)).2.2.2
  rw [familyBasis_period F i] at hs
  have hm : (((pseudolatticeFamilyBasis F i).matrix 0 0 : ℝ) +
      ((pseudolatticeFamilyBasis F i).matrix 1 1 : ℝ) - ((P.N : ℝ) + 2)) *
        P.sigma₁ P.epsilon = 0 := by
    rw [← hs]
    field_simp
    nlinarith [hp]
  have ht := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right he0)
  have hti : (pseudolatticeFamilyBasis F i).matrix 0 0 +
      (pseudolatticeFamilyBasis F i).matrix 1 1 = (P.N : ℤ) + 2 := by
    exact_mod_cast ht
  unfold L4.specialValueOrder
  omega

/--
Natural exponent/cardinality version; no truncation of a negative order; [RW26, p. 3, (3)].
-/
theorem familyBasis_order_toNat (F : FinitePseudolatticeFamily P) (i : Fin F.size) :
    (L4.specialValueOrder (pseudolatticeFamilyBasis F i).matrix).toNat = P.N := by
  rw [familyBasis_order F i]
  exact Int.toNat_natCast P.N

/--
Transport the given arithmetic polynomial through the first embedding.
 [RW26, p. 2, (2)].
-/
theorem period_polynomial (P : PeriodData K) :
    (P.sigma₁ P.epsilon) ^ 2 - ((P.N : ℝ) + 2) * P.sigma₁ P.epsilon + 1 = 0 := by
  have hp := congrArg P.sigma₁ P.epsilon_polynomial
  simpa only [map_sub, map_pow, map_mul, map_add, map_natCast, map_ofNat,
    map_one, map_zero] using hp

/--
The >1 root of that polynomial, with both radicals positive.
 [RW26, p. 3, (4)].
-/
theorem period_root (P : PeriodData K) :
    P.sigma₁ P.epsilon =
      ((P.N : ℝ) + 2 + Real.sqrt ((P.N : ℝ) ^ 2 + 4 * (P.N : ℝ))) / 2 := by
  exact L4.M74NormalizationAux.quadratic_root_gt_one P.epsilon_gt_one
    (Nat.cast_nonneg P.N) (period_polynomial P)

/--
Exact positive-root normalization needed by the coefficient sqrtN.
 [RW26, p. 3, (4)].
-/
theorem period_sqrt_normalization (P : PeriodData K) :
    Real.sqrt (P.sigma₁ P.epsilon) ^ 2 -
      Real.sqrt (P.N : ℝ) * Real.sqrt (P.sigma₁ P.epsilon) - 1 = 0 := by
  exact L4.M74NormalizationAux.quadratic_sqrt_normalization P.epsilon_gt_one
    (Nat.cast_nonneg P.N) (period_polynomial P)

/--
Keeps the plus and minus zero branches ordered and distinct.
 [RW26, p. 3, (4), footnote 2].
-/
theorem period_sqrt_gap (P : PeriodData K) :
    Real.sqrt (P.sigma₁ P.epsilon) - (Real.sqrt (P.sigma₁ P.epsilon))⁻¹ =
      Real.sqrt (P.N : ℝ) := by
  have hw : Real.sqrt (P.sigma₁ P.epsilon) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (lt_trans zero_lt_one P.epsilon_gt_one))
  calc
    Real.sqrt (P.sigma₁ P.epsilon) - (Real.sqrt (P.sigma₁ P.epsilon))⁻¹ =
        (Real.sqrt (P.sigma₁ P.epsilon) ^ 2 - 1) /
          Real.sqrt (P.sigma₁ P.epsilon) := by
      field_simp
    _ = Real.sqrt (P.N : ℝ) := by
      apply (div_eq_iff hw).2
      linarith [period_sqrt_normalization P]

#check @L4.distributionRowGroup_equiv
#check @pseudolatticeFamilyBasis_spec
#check @familyBasis_order
#print basisRowEquiv
#check @period_sqrt_normalization

end SICLean.L3.M74
