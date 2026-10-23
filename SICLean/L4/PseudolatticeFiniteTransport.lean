import SICLean.L4.PseudolatticeMatrixValues
import SICLean.L3.PseudolatticeFamily

set_option autoImplicit false

/-!
# Normalize every actual value to the finite family

Covers and presentations are selected; the selected scale is a
single totally positive element of K. The maps are additive equivalences
for equal homothety classes.
They are separate from the noninjective order-two projections.
No algebraicity of the analytic family is an input to any construction.

[RW26, p. 2, p. 3, p. 20, p. 23, (2), (3)--(4), Theorem 11, footnote 2].
-/

noncomputable section

open scoped Classical MatrixGroups

namespace SICLean.L3.M72

universe u
variable {K : Type u} [Field K] [NumberField K]
variable {P : PeriodData K}

def familyIndex (F : FinitePseudolatticeFamily P) (I : StablePseudolattice P) : Fin F.size :=
  Classical.choose (F.covers I)

def familyFactor (F : FinitePseudolatticeFamily P) (I : StablePseudolattice P) : K :=
  Classical.choose (Classical.choose_spec (F.covers I))

/--
Selected cover. [RW26, p. 20].
-/
theorem familyCover_spec (F : FinitePseudolatticeFamily P) (I : StablePseudolattice P) :
    TotallyPositive P (familyFactor F I) ∧
      I.val = pseudolatticeScale (familyFactor F I) (F.representative (familyIndex F I)).val := by
  exact Classical.choose_spec (Classical.choose_spec (F.covers I))

/--
Callable period-point membership for lambda^-1*x. [RW26, p. 3].
-/
theorem familyInverse_mem (F : FinitePseudolatticeFamily P) (I : StablePseudolattice P)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeEmbedding P ((familyFactor F I)⁻¹ * x) ∈
      L4.distributionPeriodPoints (pseudolatticeFamilyBasis F (familyIndex F I)) := by
  exact pseudolatticePresentation_point_mem P (F.representative (familyIndex F I))
    (pseudolatticeFamilyBasis F (familyIndex F I))
    (pseudolatticeFamilyBasis_spec F (familyIndex F I)) _
    (inversePoint_mem P (F.representative (familyIndex F I)) I (familyFactor F I)
      (totallyPositive_ne_zero P _ (familyCover_spec F I).1) (familyCover_spec F I).2 x hx)

def familyEquiv (F : FinitePseudolatticeFamily P) (I : StablePseudolattice P) :
    PseudolatticeGroup P I ≃+ PseudolatticeFamilyGroup F (familyIndex F I) :=
  distributionTransport P I (F.representative (familyIndex F I))
    (pseudolatticeFamilyBasis F (familyIndex F I))
    (pseudolatticeFamilyBasis_spec F (familyIndex F I))
    (familyFactor F I) (familyCover_spec F I).1 (familyCover_spec F I).2

def familyMinusPoint (F : FinitePseudolatticeFamily P)
    (z : Coordinate (Fin F.size) (PseudolatticeFamilyGroup F)) : ℂ :=
  if z.2 = 0 then (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)⁻¹
  else pseudolatticeFamilyPoint F z

/--
The normalization is explicitly lambda^-1 on every lift.
[RW26, p. 20].
-/
theorem familyEquiv_mk (F : FinitePseudolatticeFamily P) (I : StablePseudolattice P)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    familyEquiv F I (pseudolatticeMk P I x hx) =
      L4.distributionMk (pseudolatticeFamilyBasis F (familyIndex F I))
        (pseudolatticeEmbedding P ((familyFactor F I)⁻¹ * x))
        (familyInverse_mem F I x hx) := by
  exact distributionTransport_mk P I (F.representative (familyIndex F I))
    (pseudolatticeFamilyBasis F (familyIndex F I))
    (pseudolatticeFamilyBasis_spec F (familyIndex F I))
    (familyFactor F I) (familyCover_spec F I).1 (familyCover_spec F I).2 x hx

/--
Direct interface. [RW26, p. 2, (2)] (actual-value definition).
-/
theorem familyEquiv_value (F : FinitePseudolatticeFamily P) (I : StablePseudolattice P)
    (g : PseudolatticeGroup P I) :
    pseudolatticeFamilyPoint F ⟨familyIndex F I, familyEquiv F I g⟩ = value P I g := by
  exact distributionTransport_value P I (F.representative (familyIndex F I))
    (pseudolatticeFamilyBasis F (familyIndex F I))
    (pseudolatticeFamilyBasis_spec F (familyIndex F I))
    (familyFactor F I) (familyCover_spec F I).1 (familyCover_spec F I).2 g

/--
Both branches remain distinguished at zero; [RW26, p. 3, footnote 2].
-/
theorem familyEquiv_minus (F : FinitePseudolatticeFamily P) (I : StablePseudolattice P)
    (g : PseudolatticeGroup P I) :
    familyMinusPoint F ⟨familyIndex F I, familyEquiv F I g⟩ = minusValue P I g := by
  have hz : familyEquiv F I g = 0 ↔ g = 0 := by
    constructor
    · intro h
      exact (familyEquiv F I).injective (h.trans (map_zero (familyEquiv F I)).symm)
    · rintro rfl
      exact map_zero _
  simp only [familyMinusPoint, minusValue, hz]
  split_ifs
  · rfl
  · exact familyEquiv_value F I g

/--
The exact multiplier identifies the kappa coefficients.
[RW26, p. 3].
-/
theorem familyEquiv_multiplier (F : FinitePseudolatticeFamily P)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) :
    L4.etaMultiplier B.matrix =
      L4.etaMultiplier (pseudolatticeFamilyBasis F (familyIndex F I)).matrix := by
  exact multiplier_scale P (F.representative (familyIndex F I)) I
    (pseudolatticeFamilyBasis F (familyIndex F I)) B
    (pseudolatticeFamilyBasis_spec F (familyIndex F I)) hB
    (familyFactor F I) (familyCover_spec F I).1 (familyCover_spec F I).2

def presentationFamilyEquiv (F : FinitePseudolatticeFamily P)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) :
    L4.DistributionGroup B ≃+ PseudolatticeFamilyGroup F (familyIndex F I) :=
  (pseudolatticeGroupEquiv P I B hB).symm.trans (familyEquiv F I)

/--
Arbitrary allowed B and arbitrary lift x; [RW26, p. 2, p. 12, (2), Lemma 2].
-/
theorem presentationFamilyEquiv_mk (F : FinitePseudolatticeFamily P)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints P I) :
    presentationFamilyEquiv F I B hB
        (L4.distributionMk B (pseudolatticeEmbedding P x)
          (pseudolatticePresentation_point_mem P I B hB x hx)) =
      familyEquiv F I (pseudolatticeMk P I x hx) := by
  change familyEquiv F I ((pseudolatticeGroupEquiv P I B hB).symm _) = _
  rw [← pseudolatticeGroupEquiv_mk P I B hB x hx]
  simp only [AddEquiv.symm_apply_apply]

/--
Value equality with the same finite-family point used by Q4.
[RW26, p. 23, Theorem 11].
-/
theorem presentationFamilyEquiv_value (F : FinitePseudolatticeFamily P)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) (g : L4.DistributionGroup B) :
    pseudolatticeFamilyPoint F ⟨familyIndex F I, presentationFamilyEquiv F I B hB g⟩ =
      L4.distributionValue B g := by
  change pseudolatticeFamilyPoint F
    ⟨familyIndex F I, familyEquiv F I ((pseudolatticeGroupEquiv P I B hB).symm g)⟩ = _
  rw [familyEquiv_value, value_eq_distribution P I B hB]
  simp only [AddEquiv.apply_symm_apply]

def matrixFamilyEquiv (F : FinitePseudolatticeFamily P) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ)) :
    L4.SpecialValueGroup M ≃+
      PseudolatticeFamilyGroup F (familyIndex F (matrixStableLattice P M hM hN)) :=
  (matrixToK P M hM hN).trans (familyEquiv F (matrixStableLattice P M hM hN))

/--
Entire explicit matrix-to-finite-family formula; [RW26, p. 2, (2)].
-/
theorem matrixFamilyEquiv_mk (F : FinitePseudolatticeFamily P) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ))
    (u : ℤ × ℤ) :
    let I := matrixStableLattice P M hM hN
    let x := (familyFactor F I)⁻¹ *
      (((u.1 : K) * matrixTauK P M + (u.2 : K)) / (P.epsilon⁻¹ - 1))
    ∃ hx : pseudolatticeEmbedding P x ∈
        L4.distributionPeriodPoints (pseudolatticeFamilyBasis F (familyIndex F I)),
      matrixFamilyEquiv F M hM hN (L4.specialValueMk M u) =
        L4.distributionMk (pseudolatticeFamilyBasis F (familyIndex F I))
          (pseudolatticeEmbedding P x) hx := by
  obtain ⟨hx, hmk⟩ := matrixToK_mk P M hM hN u
  refine ⟨familyInverse_mem F (matrixStableLattice P M hM hN) _ hx, ?_⟩
  change familyEquiv F (matrixStableLattice P M hM hN)
    (matrixToK P M hM hN (L4.specialValueMk M u)) = _
  rw [hmk]
  exact familyEquiv_mk F (matrixStableLattice P M hM hN) _ hx

/--
Both actual matrix branches reduce to the finite point, for all g.
[RW26, p. 2, p. 3, (2), (4), footnote 2].
-/
theorem matrixFamilyEquiv_values (F : FinitePseudolatticeFamily P) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ))
    (g : L4.SpecialValueGroup M) :
    let i := familyIndex F (matrixStableLattice P M hM hN)
    pseudolatticeFamilyPoint F ⟨i, matrixFamilyEquiv F M hM hN g⟩ =
        L4.specialValuePlus M hM g ∧
      familyMinusPoint F ⟨i, matrixFamilyEquiv F M hM hN g⟩ =
        L4.specialValueMinus M hM g := by
  change pseudolatticeFamilyPoint F
      ⟨familyIndex F (matrixStableLattice P M hM hN),
        familyEquiv F (matrixStableLattice P M hM hN) (matrixToK P M hM hN g)⟩ = _ ∧
    familyMinusPoint F
      ⟨familyIndex F (matrixStableLattice P M hM hN),
        familyEquiv F (matrixStableLattice P M hM hN) (matrixToK P M hM hN g)⟩ = _
  rw [familyEquiv_value, familyEquiv_minus]
  exact matrixToK_values P M hM hN g

def arbitraryBasisFamilyEquiv (F : FinitePseudolatticeFamily P)
    (B : L4.DistributionBasis) (hB : B.Valid)
    (hN : L4.specialValueOrder B.matrix = (P.N : ℤ)) :
    L4.DistributionGroup B ≃+ PseudolatticeFamilyGroup F
      (familyIndex F (matrixStableLattice P B.matrix (basis_parameters B hB).1 hN)) :=
  (rowEquiv B hB).symm.trans (matrixFamilyEquiv F B.matrix (basis_parameters B hB).1 hN)

/--
Arbitrary real scalings reduce by their row labels, without treating
the scales as one element of K. [RW26, p. 2, p. 20, (2)].
-/
theorem arbitraryBasisFamilyEquiv_value (F : FinitePseudolatticeFamily P)
    (B : L4.DistributionBasis) (hB : B.Valid)
    (hN : L4.specialValueOrder B.matrix = (P.N : ℤ)) (g : L4.DistributionGroup B) :
    pseudolatticeFamilyPoint F
        ⟨familyIndex F (matrixStableLattice P B.matrix (basis_parameters B hB).1 hN),
          arbitraryBasisFamilyEquiv F B hB hN g⟩ = L4.distributionValue B g := by
  change pseudolatticeFamilyPoint F
    ⟨familyIndex F (matrixStableLattice P B.matrix (basis_parameters B hB).1 hN),
      familyEquiv F (matrixStableLattice P B.matrix (basis_parameters B hB).1 hN)
        (matrixToK P B.matrix (basis_parameters B hB).1 hN ((rowEquiv B hB).symm g))⟩ = _
  rw [familyEquiv_value]
  exact arbitraryBasis_to_matrixModel P B hB hN g

/--
Usable existential form after the finite point is handled.
[RW26, p. 23, Theorem 11].
-/
theorem every_value_is_familyCoordinate (F : FinitePseudolatticeFamily P)
    (I : StablePseudolattice P) (g : PseudolatticeGroup P I) :
    ∃ (i : Fin F.size) (x : PseudolatticeFamilyGroup F i),
      value P I g = pseudolatticeFamilyPoint F ⟨i, x⟩ := by
  exact ⟨familyIndex F I, familyEquiv F I g, (familyEquiv_value F I g).symm⟩

#print familyEquiv
#print matrixFamilyEquiv
#print arbitraryBasisFamilyEquiv
#check familyEquiv_mk
#check matrixFamilyEquiv_values

end SICLean.L3.M72
