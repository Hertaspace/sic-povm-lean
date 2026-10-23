import SICLean.L4.M78Point

set_option autoImplicit false

/-!
# All actual values at the fixed period

These theorems remove the hAlg hypothesis
of the already proved M72 transports using Point.familyPoint_isAlgebraic.
They do not redefine the values or repeat the equal-value bridge statements.
The final all_specialValues_isAlgebraic_of_pentagon spells out the entire
finite list of attracting (7) premises, and quantifies over every
admissible matrix with this fixed N. No Fourier or Q3 hypothesis is used.
[RW26, p. 3, p. 2, p. 12, p. 20, (2), (4)--(7), (37), Theorem 1, Lemma 2, footnote 2].
-/

noncomputable section

open scoped Classical MatrixGroups
open SICLean.L4.G2.SpecialValueBridge

namespace SICLean.L3.M78.Transport

universe u

variable {K : Type u} [Field K] [NumberField K] {P : PeriodData K}

/--
Every actual arithmetic lattice, via existing M72.values_isAlgebraic_of_family; [RW26, p. 20, (37)].
-/
theorem values_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (I : StablePseudolattice P)
    (g : PseudolatticeGroup P I) :
    IsAlgebraic ℚ (M72.value P I g) ∧ IsAlgebraic ℚ (M72.minusValue P I g) := by
  exact M72.values_isAlgebraic_of_family F (Point.familyPoint_isAlgebraic F h7) I g

/--
Any allowed presentation of an arithmetic lattice, including zero.
Proof: `M72.presentationFamilyEquiv_value`, not a newly assumed invariance law; [RW26, p. 20, (37)].
-/
theorem presentationValue_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (g : L4.DistributionGroup B) :
    IsAlgebraic ℚ (L4.distributionValue B g) := by
  rw [← M72.presentationFamilyEquiv_value F I B hB g]
  exact Point.familyPoint_isAlgebraic F h7 _

/--
The same result for an actual period-point representative in K.
The period-point membership is geometric, not an algebraicity assumption; [RW26, p. 20, (37)].
-/
theorem basisValue_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    IsAlgebraic ℚ (M72.basisValue P B x) := by
  rw [← M72.value_mk P I B hB x hx]
  exact (values_isAlgebraic F h7 I (pseudolatticeMk P I x hx)).1

/--
The minus point in any allowed presentation, with inverse zero branch.
 [RW26, p. 3, footnote 2].
-/
theorem presentationMinus_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (g : L4.DistributionGroup B) :
    IsAlgebraic ℚ (M72.distributionMinus B g) := by
  unfold M72.distributionMinus
  split_ifs
  · have hz := presentationValue_isAlgebraic F h7 I B hB 0
    rw [L4.distributionValue_zero B hB.1] at hz
    exact hz.inv
  · exact presentationValue_isAlgebraic F h7 I B hB g

/--
Arbitrary positive real scales are removed by row labels, without
assuming they are K-embeddings or claiming their set of presentations finite.
 [RW26, p. 20].
-/
theorem arbitraryBasisValues_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (B : L4.DistributionBasis) (hB : B.Valid)
    (hN : L4.specialValueOrder B.matrix = (P.N : ℤ)) (g : L4.DistributionGroup B) :
    IsAlgebraic ℚ (L4.distributionValue B g) ∧
      IsAlgebraic ℚ (M72.distributionMinus B g) := by
  have hv := M72.specialValues_isAlgebraic_of_family F
    (Point.familyPoint_isAlgebraic F h7) B.matrix (M72.basis_parameters B hB).1 hN
    ((M72.rowEquiv B hB).symm g)
  rw [← M72.distributionPlus_eq_specialPlus B hB,
    ← M72.distributionMinus_eq_specialMinus B hB] at hv
  simpa only [AddEquiv.apply_symm_apply] using hv

/--
The quotient values of every admissible matrix at this N.
Proof: `M72.specialValues_isAlgebraic_of_family` at the actual point; [RW26, p. 3, Theorem
1].
-/
theorem specialValues_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ))
    (g : L4.SpecialValueGroup M) :
    IsAlgebraic ℚ (L4.specialValuePlus M hM g) ∧
      IsAlgebraic ℚ (L4.specialValueMinus M hM g) := by
  exact M72.specialValues_isAlgebraic_of_family F (Point.familyPoint_isAlgebraic F h7)
    M hM hN g

/--
Both actual values for every integer row, including lattice rows; [RW26, p. 2, p. 3, (2), footnote
2].
-/
theorem specialValueLifts_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ))
    (v : ℤ × ℤ) :
    IsAlgebraic ℚ (L4.specialValuePlusLift M v) ∧
      IsAlgebraic ℚ (L4.specialValueMinusLift M v) := by
  simpa only [L4.specialValuePlus_mk, L4.specialValueMinus_mk] using
    specialValues_isAlgebraic F h7 M hM hN (L4.specialValueMk M v)

/--
The actual mu*Phi point value is used only off the lattice.
No evaluation of a punctured-germ identity at its center is performed; [RW26, p. 2, (2)].
-/
theorem specialValueRaw_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ))
    (v : ℤ × ℤ) (hv : v ∉ L4.specialValueLattice M) :
    IsAlgebraic ℚ (L4.specialValueRaw M v) := by
  simpa only [L4.specialValuePlusLift, if_neg hv] using
    (specialValueLifts_isAlgebraic F h7 M hM hN v).1

/--
Final fixed-period statement: if every finite representative matrix satisfies
the explicitly written attracting (7), all actual F± of this N
are algebraic. No hAlg, Fourier (6), Prop. 8 or free Q3 argument is present. [RW26, p. 3, (7),
Theorem 1].
-/
theorem all_specialValues_isAlgebraic_of_pentagon (F : FinitePseudolatticeFamily P)
    (h7 : ∀ i : Fin F.size,
      let M := (pseudolatticeFamilyBasis F i).matrix
      let hM := M74.basis_admissible (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i)
      ∀ a b : L4.SpecialValueGroup M,
        normalizedValueSum M hM (fun x => L4.specialValuePairing M hM x a *
          (L4.specialValuePlus M hM x / L4.specialValueMinus M hM (x + b))) =
        L4.specialValuePlus M hM (a + b) /
          (L4.specialValueMinus M hM a * L4.specialValueMinus M hM b) -
            (if a = 0 ∧ b = 0 then
              (L4.specialValueOrder M : ℂ) * L4.specialValuePlus M hM 0 else 0)) :
    ∀ (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
      (_hN : L4.specialValueOrder M = (P.N : ℤ)) (g : L4.SpecialValueGroup M),
      IsAlgebraic ℚ (L4.specialValuePlus M hM g) ∧
        IsAlgebraic ℚ (L4.specialValueMinus M hM g) := by
  exact specialValues_isAlgebraic F h7

/--
No finite-family existence hypothesis: selects it from P.
The remaining input is precisely the full (7) for that selected finite list; [RW26, p. 3, Theorem
1].
-/
theorem chosenFamily_specialValues_isAlgebraic (P : PeriodData K)
    (h7 : M75.Family.FamilyPentagon (chosenPseudolatticeFamily P))
    (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (hN : L4.specialValueOrder M = (P.N : ℤ)) (g : L4.SpecialValueGroup M) :
    IsAlgebraic ℚ (L4.specialValuePlus M hM g) ∧
      IsAlgebraic ℚ (L4.specialValueMinus M hM g) := by
  exact specialValues_isAlgebraic (chosenPseudolatticeFamily P) h7 M hM hN g

#check @M72.values_isAlgebraic_of_family
#check @M72.specialValues_isAlgebraic_of_family
#print L4.specialValueRaw
#check @all_specialValues_isAlgebraic_of_pentagon
#check @chosenFamily_specialValues_isAlgebraic

end SICLean.L3.M78.Transport
