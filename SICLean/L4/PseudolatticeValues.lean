import SICLean.L3.PseudolatticePresentation
import SICLean.L4.SpecialValueDescent

set_option autoImplicit false

/-!
# Actual values on the arithmetic quotient

The namespace is `L3.M72`.
The choices below select an admissible presentation and a quotient lift,
never a value satisfying an independence or algebraicity property.
[RW26, p. 2, p. 3, p. 12, (2), (4), Lemma 2, footnote 2].
These are arithmetic specializations, not new
analytic continuation claims. Point values use the existing modularPhi
and etaMultiplier, including the separately prescribed origin.
-/

noncomputable section

open scoped Classical

namespace SICLean.L3.M72

universe u
variable {K : Type u} [Field K] [NumberField K]

def chosenBasis (P : PeriodData K) (I : StablePseudolattice P) : L4.DistributionBasis :=
  Classical.choose (exists_pseudolatticePresentation P I)

def basisValue (P : PeriodData K) (B : L4.DistributionBasis) (x : K) : ℂ :=
  L4.distributionBasisValue B (pseudolatticeEmbedding P x)

def value (P : PeriodData K) (I : StablePseudolattice P)
    (g : PseudolatticeGroup P I) : ℂ :=
  basisValue P (chosenBasis P I) (pseudolatticeRepresentative P I g)

/-- The inverse occurs only in the prescribed minus origin. -/
def minusValue (P : PeriodData K) (I : StablePseudolattice P)
    (g : PseudolatticeGroup P I) : ℂ :=
  if g = 0 then (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)⁻¹ else value P I g

/--
The chosen basis satisfies the pseudolattice presentation.
[RW26, p. 2, (2)].
-/
theorem chosenBasis_spec (P : PeriodData K) (I : StablePseudolattice P) :
    PseudolatticePresentation P I (chosenBasis P I) := by
  exact Classical.choose_spec (exists_pseudolatticePresentation P I)

/--
Arithmetic quotient criterion; [RW26, p. 3, p. 12, (3), Lemma 2].
-/
theorem mk_eq_iff (P : PeriodData K) (I : StablePseudolattice P)
    (x y : K) (hx : x ∈ pseudolatticePeriodPoints P I)
    (hy : y ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeMk P I x hx = pseudolatticeMk P I y hy ↔ x - y ∈ I.val := by
  exact QuotientAddGroup.eq_iff_sub_mem

/--
Arbitrary lifts, (i); [RW26, p. 12, Lemma 2].
-/
theorem representative_mk (P : PeriodData K) (I : StablePseudolattice P)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeRepresentative P I (pseudolatticeMk P I x hx) - x ∈ I.val := by
  apply (mk_eq_iff P I _ x (Quotient.out (pseudolatticeMk P I x hx)).property hx).mp
  exact Quotient.out_eq _

/--
Prescribed plus center; [RW26, p. 3, (4), footnote 2].
-/
theorem basisValue_on_lattice (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (x : K) (hx : x ∈ I.val) :
    basisValue P B x = (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) := by
  unfold basisValue
  rw [L4.distributionBasisValue_on_lattice B _ ?_, hB.2.1]
  rw [hB.2.2]
  exact AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩

/--
Literal nonzero-class mu*Phi; [RW26, p. 2, (2)]. No punctured-germ evaluation at zero is used.
-/
theorem basisValue_off_lattice (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) (hxI : x ∉ I.val) :
    basisValue P B x = L4.etaMultiplier B.matrix *
      L4.modularPhi B.matrix
        (L4.distributionIntegerCoordinates B
          (L4.distributionPeriodDifference B (pseudolatticeEmbedding P x)) 0) 0
        ((P.sigma₁ x / B.scale : ℝ) : ℂ) (B.tau : ℂ) := by
  apply L4.distributionBasisValue_off_lattice B (pseudolatticeEmbedding P x)
  rw [hB.2.2]
  rintro ⟨y, hy, hyx⟩
  exact hxI (pseudolatticeEmbedding_injective P hyx ▸ hy)

/--
Every lattice translate, (i); [RW26, p. 12, Lemma 2].
-/
theorem basisValue_periodic (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (x t : K) (hx : x ∈ pseudolatticePeriodPoints P I) (ht : t ∈ I.val) :
    basisValue P B (x + t) = basisValue P B x := by
  unfold basisValue
  rw [map_add]
  apply L4.distributionBasisValue_periodic B hB.1
  · exact pseudolatticePresentation_point_mem P I B hB x hx
  · rw [hB.2.2]
    exact AddSubgroup.mem_map.mpr ⟨t, ht, rfl⟩

/--
Same arithmetic lattice and period, (ii); [RW26, p. 3, p. 6, (17)].
-/
theorem presentation_multiplier (P : PeriodData K) (I : StablePseudolattice P)
    (B C : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (hC : PseudolatticePresentation P I C) :
    L4.etaMultiplier C.matrix = L4.etaMultiplier B.matrix := by
  exact L4.distributionBasis_same_lattice_multiplier B C hB.1 hC.1
    (hC.2.1.trans hB.2.1.symm) (hC.2.2.trans hB.2.2.symm)

/--
Any two allowed bases, (ii); [RW26, p. 6, (17)] center regularity.
-/
theorem presentation_value (P : PeriodData K) (I : StablePseudolattice P)
    (B C : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (hC : PseudolatticePresentation P I C)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    basisValue P C x = basisValue P B x := by
  exact L4.distributionBasis_same_lattice_value B C hB.1 hC.1
    (hC.2.1.trans hB.2.1.symm) (hC.2.2.trans hB.2.2.symm)
    (pseudolatticeEmbedding P x) (pseudolatticePresentation_point_mem P I B hB x hx)

/--
Any representative and any presentation,
(i)--(ii); [RW26, p. 2, (2)].
-/
theorem value_mk (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    value P I (pseudolatticeMk P I x hx) = basisValue P B x := by
  unfold value
  rw [presentation_value P I B (chosenBasis P I) hB (chosenBasis_spec P I)
    (pseudolatticeRepresentative P I (pseudolatticeMk P I x hx))
    (Quotient.out (pseudolatticeMk P I x hx)).property]
  have h := basisValue_periodic P I B hB x
    (pseudolatticeRepresentative P I (pseudolatticeMk P I x hx) - x) hx
    (representative_mk P I x hx)
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

/--
Callable quotient equality; [RW26, p. 2, (2)].
-/
theorem value_eq_distribution (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (g : PseudolatticeGroup P I) :
    value P I g = L4.distributionValue B (pseudolatticeGroupEquiv P I B hB g) := by
  refine Quotient.inductionOn g ?_
  intro x
  change value P I (pseudolatticeMk P I x.val x.property) =
    L4.distributionValue B
      (pseudolatticeGroupEquiv P I B hB (pseudolatticeMk P I x.val x.property))
  rw [value_mk P I B hB, pseudolatticeGroupEquiv_mk,
    L4.distributionValue_mk B hB.1]
  rfl

/--
Actual plus origin; [RW26, p. 3, (4), footnote 2].
-/
theorem value_zero (P : PeriodData K) (I : StablePseudolattice P) :
    value P I 0 = (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) := by
  rw [value_eq_distribution P I (chosenBasis P I) (chosenBasis_spec P I), map_zero,
    L4.distributionValue_zero _ (chosenBasis_spec P I).1,
    (chosenBasis_spec P I).2.1]

/--
Nonvanishing at every actual center; divisor of [RW26, p. 6].
-/
theorem value_ne_zero (P : PeriodData K) (I : StablePseudolattice P)
    (g : PseudolatticeGroup P I) : value P I g ≠ 0 := by
  rw [value_eq_distribution P I (chosenBasis P I) (chosenBasis_spec P I)]
  exact L4.distributionValue_ne_zero _ (chosenBasis_spec P I).1 _

#check @pseudolatticeGroupEquiv
#check @L4.distributionBasis_same_lattice_value
#print basisValue
#print value
#print minusValue
#check value_mk
#check value_eq_distribution

end SICLean.L3.M72
