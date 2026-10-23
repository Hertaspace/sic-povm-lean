import SICLean.L4.PseudolatticeFiniteTransport
import SICLean.L4.PseudolatticeSignedTransport
import SICLean.L4.SpecialValueL2c
import SICLean.L4.SpecialValueL2rc
import SICLean.L4.PseudolatticeDownstreamAux

set_option autoImplicit false

/-!
# Q4 projection compatibility and downstream transports

Arithmetic inclusion gives a
specified quotient homomorphism. For an order-two extension its kernel
is {0,h}; we never replace it by an equivalence or assume surjectivity.
The family target and factor are exactly choices, so Q4 has exactly
the labels of FiniteSystem. The last four theorems are conditional
transport statements: algebraicity of the entire analytic family remains
an explicit hypothesis. [RW26, p. 14, p. 20, p. 23, (37)--(38), Prop. 9, Theorem 11]. The L2rc
specialization also
uses the rank-r coordinate interface.
-/

noncomputable section

open scoped Classical MatrixGroups

namespace SICLean.L3.M72

universe u
variable {K : Type u} [Field K] [NumberField K]
variable {P : PeriodData K}

/--
Arithmetic inclusion gives period-point inclusion; [RW26, p. 14, Prop. 9].
-/
theorem periodPoints_mono (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) :
    pseudolatticePeriodPoints P I ≤ pseudolatticePeriodPoints P J := by
  intro x hx
  exact hIJ hx

def quotientProject (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) : PseudolatticeGroup P I →+ PseudolatticeGroup P J where
  toFun := Quotient.lift (fun x : pseudolatticePeriodPoints P I =>
    pseudolatticeMk P J x.val (periodPoints_mono P I J hIJ x.property)) (by
      intro x y hxy
      apply (mk_eq_iff P J _ _ _ _).2
      exact hIJ ((mk_eq_iff P I _ _ x.property y.property).1 (Quotient.sound hxy)))
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y => rfl

/--
Natural quotient map is x mod J on every lift; [RW26, p. 14, Prop. 9].
-/
theorem quotientProject_mk (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    quotientProject P I J hIJ (pseudolatticeMk P I x hx) =
      pseudolatticeMk P J x (periodPoints_mono P I J hIJ hx) := by
  rfl

/--
Arithmetic inclusion and real-pair projection commute; [RW26, p. 14, Prop. 9].
-/
theorem quotientProject_distribution (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (B C : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) (hC : PseudolatticePresentation P J C)
    (hP : L4.distributionPeriodPoints B ≤ L4.distributionPeriodPoints C)
    (g : PseudolatticeGroup P I) :
    pseudolatticeGroupEquiv P J C hC (quotientProject P I J hIJ g) =
      L4.distributionProject B C hP (pseudolatticeGroupEquiv P I B hB g) := by
  have hL : L4.distributionLattice B ≤ L4.distributionLattice C := by
    rw [hB.2.2, hC.2.2]
    exact AddSubgroup.map_mono hIJ
  induction g using Quotient.inductionOn with
  | h x =>
    change pseudolatticeGroupEquiv P J C hC
        (quotientProject P I J hIJ (pseudolatticeMk P I x.val x.property)) =
      L4.distributionProject B C hP
        (pseudolatticeGroupEquiv P I B hB (pseudolatticeMk P I x.val x.property))
    rw [quotientProject_mk, pseudolatticeGroupEquiv_mk, pseudolatticeGroupEquiv_mk,
      L4.distributionProject_mk B C hB.1 hC.1 hP hL]

/--
Exactly {0,h}, without surjectivity; [RW26, p. 14, Prop. 9].
-/
theorem quotientProject_orderTwo_kernel (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) (hh : h ≠ 0 ∧ h + h = 0)
    (x : PseudolatticeGroup P I) :
    quotientProject P I (stablePseudolatticeOverlattice P I h hh)
        (pseudolatticeOverlattice_bounds P I h hh).1 x = 0 ↔ x = 0 ∨ x = h := by
  let J := stablePseudolatticeOverlattice P I h hh
  let B := chosenBasis P I
  let C := chosenBasis P J
  have hB := chosenBasis_spec P I
  have hC := chosenBasis_spec P J
  let e := pseudolatticeGroupEquiv P I B hB
  have hh' : e h ≠ 0 ∧ e h + e h = 0 := by
    constructor
    · simpa using hh.1
    · rw [← map_add, hh.2, map_zero]
  have hJ : L4.distributionLattice C = L4.distributionOverlattice B (e h) :=
    hC.2.2.trans (pseudolatticePresentation_overlattice P I B hB h)
  have hP : L4.distributionPeriodPoints B ≤ L4.distributionPeriodPoints C := by
    apply L4.distributionPeriodPoints_mono B C (hC.2.1.trans hB.2.1.symm)
    rw [hJ]
    exact (L4.distributionOverlattice_bounds B hB.1 (e h) hh').1
  have hk := L4.distributionProject_kernel B C hB.1 hC.1 (e h) hh' hP hJ (e x)
  rw [← quotientProject_distribution P I J
    (pseudolatticeOverlattice_bounds P I h hh).1 B C hB hC hP x] at hk
  have hzJ (y : PseudolatticeGroup P J) :
      pseudolatticeGroupEquiv P J C hC y = 0 ↔ y = 0 := by
    rw [← map_zero (pseudolatticeGroupEquiv P J C hC)]
    exact (pseudolatticeGroupEquiv P J C hC).injective.eq_iff
  simpa only [hzJ, ← map_zero e, e.injective.eq_iff] using hk

def familyOrderTwoK (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    PseudolatticeGroup P (F.representative i) :=
  (pseudolatticeGroupEquiv P (F.representative i) (pseudolatticeFamilyBasis F i)
    (pseudolatticeFamilyBasis_spec F i)).symm h.val

/--
Order-two labels are transported by the existing group equivalence; [RW26, p. 3] quotient.
-/
theorem familyOrderTwoK_spec (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    familyOrderTwoK F i h ≠ 0 ∧ familyOrderTwoK F i h + familyOrderTwoK F i h = 0 := by
  let e := pseudolatticeGroupEquiv P (F.representative i) (pseudolatticeFamilyBasis F i)
    (pseudolatticeFamilyBasis_spec F i)
  change e.symm h.val ≠ 0 ∧ e.symm h.val + e.symm h.val = 0
  constructor
  · simpa using h.property.1
  · rw [← map_add, h.property.2, map_zero]

def familyExtension (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) : StablePseudolattice P :=
  stablePseudolatticeOverlattice P (F.representative i) (familyOrderTwoK F i h)
    (familyOrderTwoK_spec F i h)

/--
K-lattice identity for exactly target and scale, rather than a
new unrelated cover choice; [RW26, p. 14, Prop. 9].
-/
theorem familyTarget_arithmetic (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    (familyExtension F i h).val = pseudolatticeScale (pseudolatticeFamilyFactor F i h)
      (F.representative (pseudolatticeFamilyTarget F i h)).val := by
  apply L4.PseudolatticeDownstreamAux.embeddingImage_injective P
  calc
    pseudolatticeEmbeddingImage P (familyExtension F i h).val =
        L4.distributionOverlattice (pseudolatticeFamilyBasis F i) h.val := by
      change pseudolatticeEmbeddingImage P
        (pseudolatticeOverlattice P (F.representative i) (familyOrderTwoK F i h)) = _
      rw [pseudolatticePresentation_overlattice P (F.representative i)
        (pseudolatticeFamilyBasis F i) (pseudolatticeFamilyBasis_spec F i)]
      simp [familyOrderTwoK]
    _ = L4.distributionLattice
        (L4.distributionScale (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h))
          (pseudolatticeScales P (pseudolatticeFamilyFactor F i h))) :=
      (pseudolatticeFamilyTarget_lattice F i h).symm
    _ = pseudolatticeEmbeddingImage P
        (pseudolatticeScale (pseudolatticeFamilyFactor F i h)
          (F.representative (pseudolatticeFamilyTarget F i h)).val) := by
      rw [pseudolatticeEmbeddingImage_scale]
      rw [(L4.distributionScale_valid _ (pseudolatticeFamilyBasis_spec F _).1
        (pseudolatticeScales P (pseudolatticeFamilyFactor F i h))
        (pseudolatticeFamilyFactor_positive F i h)).2.2]
      rw [(pseudolatticeFamilyBasis_spec F _).2.2]

def familyKProject (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    PseudolatticeGroup P (F.representative i) →+
      PseudolatticeFamilyGroup F (pseudolatticeFamilyTarget F i h) :=
  (distributionTransport P (familyExtension F i h)
    (F.representative (pseudolatticeFamilyTarget F i h))
    (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h))
    (pseudolatticeFamilyBasis_spec F (pseudolatticeFamilyTarget F i h))
    (pseudolatticeFamilyFactor F i h) (pseudolatticeFamilyFactor_positive F i h)
    (familyTarget_arithmetic F i h)).toAddMonoidHom.comp
      (quotientProject P (F.representative i) (familyExtension F i h)
        (pseudolatticeOverlattice_bounds P (F.representative i) (familyOrderTwoK F i h)
          (familyOrderTwoK_spec F i h)).1)

/--
Directly callable: the original finite-system projection,
with no new labels; [RW26, p. 14, Prop. 9].
-/
theorem familyKProject_eq (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i)
    (g : PseudolatticeGroup P (F.representative i)) :
    familyKProject F i h g = pseudolatticeFamilyProject F i h
      (pseudolatticeGroupEquiv P (F.representative i) (pseudolatticeFamilyBasis F i)
        (pseudolatticeFamilyBasis_spec F i) g) := by
  induction g using Quotient.inductionOn with
  | h x =>
    change familyKProject F i h (pseudolatticeMk P (F.representative i) x.val x.property) =
      pseudolatticeFamilyProject F i h
        (pseudolatticeGroupEquiv P (F.representative i) (pseudolatticeFamilyBasis F i)
          (pseudolatticeFamilyBasis_spec F i)
          (pseudolatticeMk P (F.representative i) x.val x.property))
    simp only [familyKProject, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    erw [quotientProject_mk, distributionTransport_mk, pseudolatticeGroupEquiv_mk,
      pseudolatticeFamilyProject_mk]
    simp only [pseudolatticeFamilyScale,
      ← L4.PseudolatticeDownstreamAux.embedding_inverse_scale]

/--
The Q4 target label is lambda_(i,h)^-1*x on every representative; [RW26, p. 14, Prop. 9].
-/
theorem familyKProject_mk (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P (F.representative i)) :
    ∃ hx' : pseudolatticeEmbedding P ((pseudolatticeFamilyFactor F i h)⁻¹ * x) ∈
        L4.distributionPeriodPoints
          (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h)),
      familyKProject F i h (pseudolatticeMk P (F.representative i) x hx) =
        L4.distributionMk (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h))
          (pseudolatticeEmbedding P ((pseudolatticeFamilyFactor F i h)⁻¹ * x)) hx' := by
  have hxB := pseudolatticePresentation_point_mem P (F.representative i)
    (pseudolatticeFamilyBasis F i) (pseudolatticeFamilyBasis_spec F i) x hx
  have hx' := pseudolatticeFamilyTarget_periodPoints F i h hxB
  change L4.distributionHomothety
    ((pseudolatticeFamilyScale F i h).1⁻¹, (pseudolatticeFamilyScale F i h).2⁻¹)
      (pseudolatticeEmbedding P x) ∈ L4.distributionPeriodPoints
        (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h)) at hx'
  simp only [pseudolatticeFamilyScale,
    ← L4.PseudolatticeDownstreamAux.embedding_inverse_scale] at hx'
  refine ⟨hx', ?_⟩
  rw [familyKProject_eq, pseudolatticeGroupEquiv_mk, pseudolatticeFamilyProject_mk]
  simp only [pseudolatticeFamilyScale,
    ← L4.PseudolatticeDownstreamAux.embedding_inverse_scale]

/--
Q4 transported to arithmetic lifts, including g = 0 and h.
[RW26, p. 14, Prop. 9].
-/
theorem familyK_q4 (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i)
    (g : PseudolatticeGroup P (F.representative i)) :
    value P (F.representative i) g *
        value P (F.representative i) (g + familyOrderTwoK F i h) =
      L4.distributionFamilyKappa (pseudolatticeFamilyBasis F) (pseudolatticeFamilyTarget F) i h *
        pseudolatticeFamilyPoint F
          ⟨pseudolatticeFamilyTarget F i h, familyKProject F i h g⟩ := by
  rw [familyKProject_eq,
    value_eq_distribution P (F.representative i) (pseudolatticeFamilyBasis F i)
      (pseudolatticeFamilyBasis_spec F i) g,
    value_eq_distribution P (F.representative i) (pseudolatticeFamilyBasis F i)
      (pseudolatticeFamilyBasis_spec F i) (g + familyOrderTwoK F i h), map_add]
  simp only [familyOrderTwoK, AddEquiv.apply_symm_apply]
  exact pseudolatticeFamily_q4 F i h
    (pseudolatticeGroupEquiv P (F.representative i) (pseudolatticeFamilyBasis F i)
      (pseudolatticeFamilyBasis_spec F i) g)

def l2cFamilyEquiv (F : FinitePseudolatticeFamily P) (M : ℕ) [Fact (4 ≤ M)]
    (hN : L4.specialValueOrder (L4.rwL2cPeriod M) = (P.N : ℤ)) :
    L2c.RWGroup M ≃+ PseudolatticeFamilyGroup F
      (familyIndex F (matrixStableLattice P (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 hN)) :=
  (L4.rwL2cEquiv M).trans
    (matrixFamilyEquiv F (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 hN)

/--
Same L2c quotient and actual functions, with no new Smith labels; [RW26, p. 20, p. 3, (37)--(38),
footnote 2].
-/
theorem l2cFamilyEquiv_values (F : FinitePseudolatticeFamily P) (M : ℕ) [Fact (4 ≤ M)]
    (hN : L4.specialValueOrder (L4.rwL2cPeriod M) = (P.N : ℤ)) (g : L2c.RWGroup M) :
    let i := familyIndex F
      (matrixStableLattice P (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 hN)
    pseudolatticeFamilyPoint F ⟨i, l2cFamilyEquiv F M hN g⟩ = L4.rwL2cPlus M g ∧
      familyMinusPoint F ⟨i, l2cFamilyEquiv F M hN g⟩ = L4.rwL2cMinus M g := by
  exact matrixFamilyEquiv_values F (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 hN
    (L4.rwL2cEquiv M g)

def l2rcFamilyEquiv (F : FinitePseudolatticeFamily P) (d r : ℕ) [Fact (L2r.Admissible d r)]
    (hN : L4.specialValueOrder (L4.rwL2rcPeriod d r) = (P.N : ℤ)) :
    L2rc.RWGroup d r ≃+ PseudolatticeFamilyGroup F
      (familyIndex F (matrixStableLattice P (L4.rwL2rcPeriod d r)
        (L4.rwL2rc_admissible d r).2 hN)) :=
  (L4.rwL2rcEquiv d r).trans
    (matrixFamilyEquiv F (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 hN)

/--
Same rank-r row quotient, actual gamma and actual plus/minus values. [RW26, p. 2, p. 3, (2),
footnote 2].
-/
theorem l2rcFamilyEquiv_values (F : FinitePseudolatticeFamily P) (d r : ℕ)
    [Fact (L2r.Admissible d r)]
    (hN : L4.specialValueOrder (L4.rwL2rcPeriod d r) = (P.N : ℤ)) (g : L2rc.RWGroup d r) :
    let i := familyIndex F
      (matrixStableLattice P (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 hN)
    pseudolatticeFamilyPoint F ⟨i, l2rcFamilyEquiv F d r hN g⟩ = L4.rwL2rcPlus d r g ∧
      familyMinusPoint F ⟨i, l2rcFamilyEquiv F d r hN g⟩ = L4.rwL2rcMinus d r g := by
  exact matrixFamilyEquiv_values F (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 hN
    (L4.rwL2rcEquiv d r g)

/--
Conditional transport from algebraicity of each finite family point.
[RW26, p. 2, Theorem 1].
-/
theorem values_isAlgebraic_of_family (F : FinitePseudolatticeFamily P)
    (hAlg : ∀ z : Coordinate (Fin F.size) (PseudolatticeFamilyGroup F),
      IsAlgebraic ℚ (pseudolatticeFamilyPoint F z))
    (I : StablePseudolattice P) (g : PseudolatticeGroup P I) :
    IsAlgebraic ℚ (value P I g) ∧ IsAlgebraic ℚ (minusValue P I g) := by
  have hv : IsAlgebraic ℚ (value P I g) := by
    rw [← familyEquiv_value F I g]
    exact hAlg _
  refine ⟨hv, ?_⟩
  unfold minusValue
  split_ifs with hg
  · have hz := hAlg ⟨familyIndex F I, familyEquiv F I 0⟩
    rw [familyEquiv_value F I 0, value_zero P I] at hz
    exact hz.inv
  · exact hv

/--
Conditional matrix consequence, including the inverse zero branch; [RW26, p. 2, p. 3, Theorem 1,
footnote 2].
-/
theorem specialValues_isAlgebraic_of_family (F : FinitePseudolatticeFamily P)
    (hAlg : ∀ z : Coordinate (Fin F.size) (PseudolatticeFamilyGroup F),
      IsAlgebraic ℚ (pseudolatticeFamilyPoint F z))
    (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (hN : L4.specialValueOrder M = (P.N : ℤ)) (g : L4.SpecialValueGroup M) :
    IsAlgebraic ℚ (L4.specialValuePlus M hM g) ∧
      IsAlgebraic ℚ (L4.specialValueMinus M hM g) := by
  have hv := values_isAlgebraic_of_family F hAlg (matrixStableLattice P M hM hN)
    (matrixToK P M hM hN g)
  rw [(matrixToK_values P M hM hN g).1, (matrixToK_values P M hM hN g).2] at hv
  exact hv

/--
L2c conditional algebraicity with every upstream analytic obligation
left visible in hAlg; [RW26, p. 20, p. 2, (37), Theorem 1].
-/
theorem l2c_isAlgebraic_of_family (F : FinitePseudolatticeFamily P)
    (hAlg : ∀ z : Coordinate (Fin F.size) (PseudolatticeFamilyGroup F),
      IsAlgebraic ℚ (pseudolatticeFamilyPoint F z)) (M : ℕ) [Fact (4 ≤ M)]
    (hN : L4.specialValueOrder (L4.rwL2cPeriod M) = (P.N : ℤ)) (g : L2c.RWGroup M) :
    IsAlgebraic ℚ (L4.rwL2cPlus M g) ∧ IsAlgebraic ℚ (L4.rwL2cMinus M g) := by
  exact specialValues_isAlgebraic_of_family F hAlg (L4.rwL2cPeriod M)
    (L4.rwL2c_admissible M).2 hN (L4.rwL2cEquiv M g)

/--
Rank-r conditional transport; does not assert Fourier (6) or (7). [RW26, p. 2, Theorem 1].
-/
theorem l2rc_isAlgebraic_of_family (F : FinitePseudolatticeFamily P)
    (hAlg : ∀ z : Coordinate (Fin F.size) (PseudolatticeFamilyGroup F),
      IsAlgebraic ℚ (pseudolatticeFamilyPoint F z)) (d r : ℕ) [Fact (L2r.Admissible d r)]
    (hN : L4.specialValueOrder (L4.rwL2rcPeriod d r) = (P.N : ℤ)) (g : L2rc.RWGroup d r) :
    IsAlgebraic ℚ (L4.rwL2rcPlus d r g) ∧ IsAlgebraic ℚ (L4.rwL2rcMinus d r g) := by
  exact specialValues_isAlgebraic_of_family F hAlg (L4.rwL2rcPeriod d r)
    (L4.rwL2rc_admissible d r).2 hN (L4.rwL2rcEquiv d r g)

#print quotientProject
#print familyKProject
#print l2cFamilyEquiv
#print l2rcFamilyEquiv
#check @L4.distributionFamily_isSolution_of_remaining_equations
#check @FiniteSystem.solution_isAlgebraic
#check familyKProject_eq
#check familyK_q4
#check specialValues_isAlgebraic_of_family

end SICLean.L3.M72
