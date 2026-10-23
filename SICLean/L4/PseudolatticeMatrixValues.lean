import SICLean.L4.PseudolatticeHomothety
import SICLean.L4.PseudolatticeMatrixValuesAux

set_option autoImplicit false

/-!
# Row labels, actual SpecialValue, and a K-model

The row equivalence is the one given by the existence statement, together
with its all-integer-lifts formula. The standard
K-lattice has the concrete generators ((epsilon-d)/c,1). Its fullness,
stability, presentation and value comparisons are separate conclusions.
An arbitrary real-scaled Valid basis is compared through its row group;
we do not claim that its two scales themselves come from K. [RW26, p. 2, p. 3, p. 12, p. 20, (2),
(3)--(4), Lemma 2, footnote 2, (37)].
All values use existing modularPhi, phiExtended and etaMultiplier.
-/

noncomputable section

open scoped Classical MatrixGroups

namespace SICLean.L3.M72

universe u
variable {K : Type u} [Field K] [NumberField K]

def rowEquiv (B : L4.DistributionBasis) (hB : B.Valid) :
    L4.SpecialValueGroup B.matrix ≃+ L4.DistributionGroup B :=
  Classical.choose (L4.distributionRowGroup_equiv B hB)

def distributionMinus (B : L4.DistributionBasis) (g : L4.DistributionGroup B) : ℂ :=
  if g = 0 then (Real.sqrt (L4.distributionPeriod B) : ℂ)⁻¹
  else L4.distributionValue B g

/--
All-lifts formula fixes the chosen row equivalence; [RW26, p. 2, p. 3, (2), (3)].
-/
theorem rowEquiv_mk (B : L4.DistributionBasis) (hB : B.Valid) (u : ℤ × ℤ) :
    rowEquiv B hB (L4.specialValueMk B.matrix u) =
      L4.distributionMk B (L4.distributionRowPoint B u)
        (L4.distributionRowPoint_mem B hB u) := by
  exact Classical.choose_spec (L4.distributionRowGroup_equiv B hB) u

/--
The attracting root and the actual automorphy factor coincide; [RW26, p. 2, p. 3, (2), (4)].
-/
theorem basis_parameters (B : L4.DistributionBasis) (hB : B.Valid) :
    L4.SpecialValueAdmissible B.matrix ∧
      B.tau = L4.specialValueTau B.matrix ∧
      L4.distributionPeriod B = L4.specialValueEpsilon B.matrix := by
  have hM : L4.SpecialValueAdmissible B.matrix := ⟨hB.1, hB.2.1⟩
  have he := hB.2.2.2.1
  have hf := L4.specialValueEpsilon_gt_one B.matrix hM
  have ht := (L4.distributionBasis_spectral B hB).2.2.2
  have hp := L4.specialValueEpsilon_characteristic B.matrix hM
  have horder : (L4.specialValueOrder B.matrix : ℝ) + 2 =
      (B.matrix 0 0 : ℝ) + (B.matrix 1 1 : ℝ) := by
    simp [L4.specialValueOrder]
  rw [horder] at hp
  have he0 : L4.distributionPeriod B ≠ 0 := ne_of_gt (lt_trans zero_lt_one he)
  have hchar : L4.distributionPeriod B ^ 2 -
      ((B.matrix 0 0 : ℝ) + (B.matrix 1 1 : ℝ)) *
        L4.distributionPeriod B + 1 = 0 := by
    calc
      _ = L4.distributionPeriod B *
          (L4.distributionPeriod B + (L4.distributionPeriod B)⁻¹ -
            ((B.matrix 0 0 : ℝ) + (B.matrix 1 1 : ℝ))) := by
              field_simp
              ring
      _ = 0 := by rw [ht]; ring
  have hfactor : (L4.distributionPeriod B - L4.specialValueEpsilon B.matrix) *
      (L4.distributionPeriod B + L4.specialValueEpsilon B.matrix -
        ((B.matrix 0 0 : ℝ) + (B.matrix 1 1 : ℝ))) = 0 := by
    nlinarith [hchar, hp]
  have hperiod : L4.distributionPeriod B = L4.specialValueEpsilon B.matrix := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact sub_eq_zero.mp h
    · have hprod := one_lt_mul he.le hf
      nlinarith [hchar, hp]
  refine ⟨hM, ?_, hperiod⟩
  have hc : (B.matrix 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hB.1
  apply mul_left_cancel₀ hc
  exact add_right_cancel (show (B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ) =
      (B.matrix 1 0 : ℝ) * L4.specialValueTau B.matrix + (B.matrix 1 1 : ℝ) from hperiod)

/--
Actual plus values on all classes, including the specified origin; [RW26, p. 2, p. 3, (2), (4)].
-/
theorem distributionPlus_eq_specialPlus (B : L4.DistributionBasis) (hB : B.Valid)
    (g : L4.SpecialValueGroup B.matrix) :
    L4.distributionValue B (rowEquiv B hB g) =
      L4.specialValuePlus B.matrix (basis_parameters B hB).1 g := by
  refine Quotient.inductionOn g ?_
  intro u
  change L4.distributionValue B (rowEquiv B hB (L4.specialValueMk B.matrix u)) = _
  rw [rowEquiv_mk, L4.distributionValue_mk B hB]
  change L4.distributionBasisValue B (L4.distributionRowPoint B u) =
    L4.specialValuePlusLift B.matrix u
  by_cases hu : u ∈ L4.specialValueLattice B.matrix
  · rw [L4.distributionBasisValue_on_lattice B _
      ((L4.distributionRowPoint_lattice_iff B hB u).2 hu)]
    simp only [L4.specialValuePlusLift, if_pos hu, (basis_parameters B hB).2.2]
  · rw [L4.distributionRowPoint_value B hB u hu]
    simp only [L4.specialValuePlusLift, if_neg hu, L4.specialValueRaw,
      L4.specialValueArgument, (basis_parameters B hB).2.1]

/--
Minus has the same nonzero values and the inverse origin only; [RW26, p. 3, footnote 2].
-/
theorem distributionMinus_eq_specialMinus (B : L4.DistributionBasis) (hB : B.Valid)
    (g : L4.SpecialValueGroup B.matrix) :
    distributionMinus B (rowEquiv B hB g) =
      L4.specialValueMinus B.matrix (basis_parameters B hB).1 g := by
  by_cases hg : g = 0
  · subst g
    simp only [map_zero, distributionMinus, ite_true, L4.specialValueMinus_zero,
      (basis_parameters B hB).2.2]
  · have hr : rowEquiv B hB g ≠ 0 := by
      intro h
      exact hg ((rowEquiv B hB).injective (h.trans (map_zero _).symm))
    rw [distributionMinus, if_neg hr]
    exact (distributionPlus_eq_specialPlus B hB g).trans
      (L4.specialValue_agree_off_zero B.matrix (basis_parameters B hB).1 g hg)

def rowToK (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B) :
    L4.SpecialValueGroup B.matrix ≃+ PseudolatticeGroup P I :=
  (rowEquiv B hB.1).trans (pseudolatticeGroupEquiv P I B hB).symm

/--
Explicit dictionary on every integer row, in both embeddings; [RW26, p. 2, (2)].
-/
theorem rowToK_mk (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B) (u : ℤ × ℤ) :
    pseudolatticeGroupEquiv P I B hB (rowToK P I B hB (L4.specialValueMk B.matrix u)) =
      L4.distributionMk B (L4.distributionRowPoint B u)
        (L4.distributionRowPoint_mem B hB.1 u) := by
  simpa only [rowToK, AddEquiv.trans_apply, AddEquiv.apply_symm_apply] using
    rowEquiv_mk B hB.1 u

/--
K, real-pair and matrix presentations give the same plus value; [RW26, p. 2, p. 3, (2), (4)].
-/
theorem value_rowToK (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (g : L4.SpecialValueGroup B.matrix) :
    value P I (rowToK P I B hB g) =
      L4.specialValuePlus B.matrix (basis_parameters B hB.1).1 g := by
  rw [value_eq_distribution P I B hB]
  simpa only [rowToK, AddEquiv.trans_apply, AddEquiv.apply_symm_apply] using
    distributionPlus_eq_specialPlus B hB.1 g

/--
Exact minus comparison, including zero; [RW26, p. 3, footnote 2].
-/
theorem minusValue_rowToK (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (g : L4.SpecialValueGroup B.matrix) :
    minusValue P I (rowToK P I B hB g) =
      L4.specialValueMinus B.matrix (basis_parameters B hB.1).1 g := by
  by_cases hg : g = 0
  · subst g
    simp only [map_zero, minusValue, ite_true, L4.specialValueMinus_zero,
      ← (basis_parameters B hB.1).2.2, hB.2.1]
  · have hr : rowToK P I B hB g ≠ 0 := by
      intro h
      exact hg ((rowToK P I B hB).injective (h.trans (map_zero _).symm))
    rw [minusValue, if_neg hr]
    exact (value_rowToK P I B hB g).trans
      (L4.specialValue_agree_off_zero B.matrix (basis_parameters B hB.1).1 g hg)

def matrixBasis (M : SL(2, ℤ)) : L4.DistributionBasis :=
  ⟨M, L4.specialValueTau M, 1, 1⟩

def matrixTauK (P : PeriodData K) (M : SL(2, ℤ)) : K :=
  (P.epsilon - (M 1 1 : K)) / (M 1 0 : K)

def matrixLattice (P : PeriodData K) (M : SL(2, ℤ)) : Submodule ℤ K :=
  Submodule.span ℤ ({matrixTauK P M, 1} : Set K)

/--
Canonical scales are both 1; [RW26, p. 2, p. 20, (2), (37)].
-/
theorem matrixBasis_valid (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    (matrixBasis M).Valid := by
  exact ⟨hM.1, hM.2, L4.specialValueTau_fixedPoint M hM,
    L4.specialValueEpsilon_gt_one M hM, zero_lt_one, zero_lt_one⟩

/--
Fixed P and equal trace determine the same epsilon and both roots; [RW26, p. 2, p. 3, (2), (4)].
-/
theorem matrixTauK_embedding (P : PeriodData K) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ)) :
    pseudolatticeEmbedding P (matrixTauK P M) = L4.distributionBetaOne (matrixBasis M) ∧
      L4.specialValueEpsilon M = P.sigma₁ P.epsilon := by
  exact L4.PseudolatticeMatrixValuesAux.tauK_embedding P M hM hN

/--
Arithmetic rank two. [RW26, p. 20].
-/
theorem matrixLattice_isLattice (P : PeriodData K) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ)) :
    Submodule.IsLattice ℚ (matrixLattice P M) := by
  exact L4.PseudolatticeMatrixValuesAux.lattice_isLattice P M hM hN

/--
Multiplication has matrix M; its inverse gives equality of lattices. [RW26, p. 20].
-/
theorem matrixLattice_periodStable (P : PeriodData K) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ)) :
    PeriodStable P (matrixLattice P M) := by
  exact L4.PseudolatticeMatrixValuesAux.lattice_periodStable P M hM hN

def matrixStableLattice (P : PeriodData K) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ)) :
    StablePseudolattice P :=
  ⟨matrixLattice P M, matrixLattice_isLattice P M hM hN,
    matrixLattice_periodStable P M hM hN⟩

/--
An actual K-presentation for every admissible matrix of this trace; [RW26, p. 20, (37)].
-/
theorem matrixPresentation (P : PeriodData K) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ)) :
    PseudolatticePresentation P (matrixStableLattice P M hM hN) (matrixBasis M) := by
  refine ⟨matrixBasis_valid M hM, (matrixTauK_embedding P M hM hN).2, ?_⟩
  have h₁ := (matrixTauK_embedding P M hM hN).1
  have h₂ : pseudolatticeEmbedding P (1 : K) =
      L4.distributionBetaTwo (matrixBasis M) := by
    ext <;> simp [pseudolatticeEmbedding, L4.distributionBetaTwo, matrixBasis]
  change L4.distributionLattice (matrixBasis M) =
    (Submodule.span ℤ ({matrixTauK P M, 1} : Set K)).toAddSubgroup.map
      (pseudolatticeEmbedding P)
  rw [Submodule.span_int_eq_addSubgroupClosure, AddMonoidHom.map_closure,
    Set.image_pair, h₁, h₂]
  simp only [L4.distributionLattice, AddSubgroup.zmultiples_eq_closure,
    ← AddSubgroup.closure_union, Set.singleton_union]

def matrixToK (P : PeriodData K) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ)) :
    L4.SpecialValueGroup M ≃+ PseudolatticeGroup P (matrixStableLattice P M hM hN) :=
  rowToK P (matrixStableLattice P M hM hN) (matrixBasis M) (matrixPresentation P M hM hN)

/--
Explicit x_u=(u1*tau_K+u2)/(epsilon^-1-1), not epsilon-1; [RW26, p. 2, (2)].
-/
theorem matrixToK_mk (P : PeriodData K) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ))
    (u : ℤ × ℤ) :
    ∃ hx : ((u.1 : K) * matrixTauK P M + (u.2 : K)) / (P.epsilon⁻¹ - 1) ∈
        pseudolatticePeriodPoints P (matrixStableLattice P M hM hN),
      matrixToK P M hM hN (L4.specialValueMk M u) =
        pseudolatticeMk P (matrixStableLattice P M hM hN)
          (((u.1 : K) * matrixTauK P M + (u.2 : K)) / (P.epsilon⁻¹ - 1)) hx := by
  have hden : P.epsilon⁻¹ - 1 ≠ 0 := by
    intro h
    have he : P.epsilon = 1 := by
      simpa only [inv_inv, inv_one] using
        congrArg (fun x : K => x⁻¹) (sub_eq_zero.mp h)
    have := P.epsilon_gt_one
    simp only [he, map_one, lt_self_iff_false] at this
  let x : K := ((u.1 : K) * matrixTauK P M + (u.2 : K)) / (P.epsilon⁻¹ - 1)
  have hx : x ∈ pseudolatticePeriodPoints P (matrixStableLattice P M hM hN) := by
    change (P.epsilon⁻¹ - 1) * x ∈ matrixLattice P M
    have hmul : (P.epsilon⁻¹ - 1) * x =
        (u.1 : K) * matrixTauK P M + (u.2 : K) := by
      exact mul_div_cancel₀ _ hden
    rw [hmul]
    exact Submodule.mem_span_pair.mpr ⟨u.1, u.2, by simp [zsmul_eq_mul]⟩
  refine ⟨hx, ?_⟩
  apply (pseudolatticeGroupEquiv P (matrixStableLattice P M hM hN)
    (matrixBasis M) (matrixPresentation P M hM hN)).injective
  change pseudolatticeGroupEquiv P (matrixStableLattice P M hM hN)
      (matrixBasis M) (matrixPresentation P M hM hN)
      (rowToK P (matrixStableLattice P M hM hN) (matrixBasis M)
        (matrixPresentation P M hM hN)
        (L4.specialValueMk (matrixBasis M).matrix u)) = _
  rw [rowToK_mk, pseudolatticeGroupEquiv_mk]
  have hemb : pseudolatticeEmbedding P x = L4.distributionRowPoint (matrixBasis M) u := by
    have hτ := (matrixTauK_embedding P M hM hN).1
    have hε := (matrixTauK_embedding P M hM hN).2
    have hτ₁ := congrArg Prod.fst hτ
    have hτ₂ := congrArg Prod.snd hτ
    change P.sigma₁ (matrixTauK P M) = (L4.distributionBetaOne (matrixBasis M)).1 at hτ₁
    change P.sigma₂ (matrixTauK P M) = (L4.distributionBetaOne (matrixBasis M)).2 at hτ₂
    ext <;> simp [x, pseudolatticeEmbedding, L4.distributionRowPoint,
      L4.distributionBetaTwo, matrixBasis, map_div₀, map_add, map_mul, map_sub,
      map_inv₀, hτ₁, hτ₂, P.epsilon_conj, ← hε, L4.distributionPeriod,
      L4.specialValueEpsilon]
  exact congrArg (fun y : L4.distributionPeriodPoints (matrixBasis M) =>
    (QuotientAddGroup.mk y : L4.DistributionGroup (matrixBasis M))) (Subtype.ext hemb.symm)

/--
All actual centers of both branches; [RW26, p. 2, p. 3, (2), (4), footnote 2].
-/
theorem matrixToK_values (P : PeriodData K) (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (hN : L4.specialValueOrder M = (P.N : ℤ))
    (g : L4.SpecialValueGroup M) :
    value P (matrixStableLattice P M hM hN) (matrixToK P M hM hN g) =
        L4.specialValuePlus M hM g ∧
      minusValue P (matrixStableLattice P M hM hN) (matrixToK P M hM hN g) =
        L4.specialValueMinus M hM g := by
  exact ⟨value_rowToK P (matrixStableLattice P M hM hN) (matrixBasis M)
      (matrixPresentation P M hM hN) g,
    minusValue_rowToK P (matrixStableLattice P M hM hN) (matrixBasis M)
      (matrixPresentation P M hM hN) g⟩

/--
Arbitrary real scales can be removed through row labels without
claiming an arithmetic realization of those scales. [RW26, p. 2, p. 20, (2)].
-/
theorem arbitraryBasis_to_matrixModel (P : PeriodData K) (B : L4.DistributionBasis)
    (hB : B.Valid) (hN : L4.specialValueOrder B.matrix = (P.N : ℤ))
    (g : L4.DistributionGroup B) :
    value P (matrixStableLattice P B.matrix (basis_parameters B hB).1 hN)
        (matrixToK P B.matrix (basis_parameters B hB).1 hN ((rowEquiv B hB).symm g)) =
      L4.distributionValue B g := by
  rw [(matrixToK_values P B.matrix (basis_parameters B hB).1 hN
    ((rowEquiv B hB).symm g)).1]
  simpa only [AddEquiv.apply_symm_apply] using
    (distributionPlus_eq_specialPlus B hB ((rowEquiv B hB).symm g)).symm

#print rowEquiv
#print matrixTauK
#print matrixLattice
#print matrixToK
#check @L4.distributionRowPoint_specialArgument
#check @L4.specialValuePlus_mk
#check matrixToK_mk
#check arbitraryBasis_to_matrixModel

end SICLean.L3.M72
