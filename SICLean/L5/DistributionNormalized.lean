import SICLean.L5.DistributionGeneralValues
import SICLean.L5.DistributionSubgroupLattice
import SICLean.L4.DistributionValues
import SICLean.L5.DistributionNormalizedAux

set_option autoImplicit false

/-!
# Proposition 3(ii), (11)--(12), and the order-two case

[RW-rec, p. 4, Prop. 3(ii), (11)--(12)], with the specialization in
[RW-rec, Appendix A, p. 20]. The coefficient orientation is that of (11).
[RW26, p. 3, (4)] and [RW26, p. 3, footnote 2] give the value at zero;
[RW26, p. 14, Prop. 9] is the two-point product.

(12) divides the identity at x by the identity at x = 0. The eta factors
cancel at this step. Every statement includes x = 0 and x in H. The
projection of G_I need not be all of G_J.
-/

noncomputable section

open scoped Classical BigOperators
open SICLean.L3

namespace SICLean.L5.DistributionNormalized

open DistributionOrbitGeometry DistributionSubgroups

universe u
variable {K : Type u} [Field K] [NumberField K]

def normalizedValue (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) : ℂ :=
  M72.value P I x / (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)

/-- [RW-rec, p. 20, (10)], the length-one orbit specialization.
The zero factor appears once when x belongs to H. -/
theorem subgroup_orbitProduct (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    DistributionGeneral.orbitProduct P I (subgroupLattice P I H)
      (le_overlattice P I H) (project P I H x) =
      ∏ a : H, M72.value P I (x + a.val) := by
  let _ := orbitFintype P I (subgroupLattice P I H) (le_overlattice P I H)
    (project P I H x)
  unfold DistributionGeneral.orbitProduct
  calc
    _ = ∏ a : H, DistributionGeneral.orbitValue P I (subgroupLattice P I H)
        (le_overlattice P I H) (project P I H x)
        (DistributionNormalizedAux.cosetOrbitEquiv P I H x a) :=
      ((DistributionNormalizedAux.cosetOrbitEquiv P I H x).prod_comp _).symm
    _ = _ := Finset.prod_congr rfl fun a _ =>
      DistributionNormalizedAux.orbitValue_coset P I H x a

/-- [RW-rec, p. 4, Prop. 3(ii), (11)]; [RW-rec, Appendix A, p. 20].
The numerator is μ_I raised to |H|, with `etaMultiplier`. -/
theorem distribution_subgroup (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    (PeriodPower.multiplier P I ^ Nat.card H / PeriodPower.multiplier P (subgroupLattice P I H)) *
      M72.value P (subgroupLattice P I H) (project P I H x) =
      ∏ a : H, M72.value P I (x + a.val) := by
  simpa only [DistributionGeneral.distributionFactor, overlattice_index,
    subgroup_orbitProduct] using
    DistributionGeneral.distribution_general P I (subgroupLattice P I H)
      (le_overlattice P I H) (project P I H x)

/-- [RW-rec, p. 4, (12)]; [RW26, p. 3, (4)].
The denominator is the full product at x = 0, including E_I(0) equal to
the positive square root of ε. -/
theorem distribution_subgroup_zero (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) :
    ∏ a : H, M72.value P I a.val =
      (PeriodPower.multiplier P I ^ Nat.card H / PeriodPower.multiplier P (subgroupLattice P I H)) *
        (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) := by
  simpa only [map_zero, zero_add, M72.value_zero] using
    (distribution_subgroup P I H 0).symm

/-- [RW-rec, p. 3, Def. 1]; [RW-rec, Appendix A, p. 19]; [RW26, p. 6].
The product at the subgroup is nonzero, so normalization by it is defined. -/
theorem subgroup_product_ne_zero (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) :
    (∏ a : H, M72.value P I a.val) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun a _ => M72.value_ne_zero P I a.val

/-- [RW-rec, p. 4, (12)]; [RW-rec, p. 3, Def. 1]; [RW26, p. 3, (4)];
[RW26, p. 3, footnote 2]. -/
theorem normalizedValue_zero (P : PeriodData K) (I : StablePseudolattice P) :
    normalizedValue P I 0 = 1 := by
  unfold normalizedValue
  rw [← M72.value_zero P I]
  exact div_self (M72.value_ne_zero P I 0)

/-- [RW-rec, p. 4, (12)]. The eta factors and the zero-orbit phase are those
of (11), before this ratio. -/
theorem distribution_normalized (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    normalizedValue P (subgroupLattice P I H) (project P I H x) =
      ∏ a : H, M72.value P I (x + a.val) / M72.value P I a.val := by
  have hc : PeriodPower.multiplier P I ^ Nat.card H /
      PeriodPower.multiplier P (subgroupLattice P I H) ≠ 0 := by
    simpa only [DistributionGeneral.distributionFactor, overlattice_index] using
      DistributionGeneral.distributionFactor_ne_zero P I (subgroupLattice P I H)
  rw [normalizedValue, Finset.prod_div_distrib,
    ← distribution_subgroup P I H x, distribution_subgroup_zero P I H,
    mul_div_mul_left _ _ hc]

/-- [RW-rec, p. 4, (12)], in cross-multiplied form. -/
theorem distribution_normalized_cross_mul (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    M72.value P (subgroupLattice P I H) (project P I H x) *
        (∏ a : H, M72.value P I a.val) =
      (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) *
        (∏ a : H, M72.value P I (x + a.val)) := by
  rw [distribution_subgroup_zero, ← distribution_subgroup]
  ring

/-- [RW-rec, p. 4, (12)]; [RW26, p. 2, (2)].
The identity for an arbitrary admissible presentation of the target lattice. -/
theorem distribution_normalized_presentation (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (BJ : L4.DistributionBasis)
    (hBJ : PseudolatticePresentation P (subgroupLattice P I H) BJ)
    (z : K) (hz : z ∈ pseudolatticePeriodPoints P I) :
    M72.basisValue P BJ z / (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) =
      ∏ a : H,
        M72.value P I (pseudolatticeMk P I z hz + a.val) / M72.value P I a.val := by
  simpa only [normalizedValue, DistributionNormalizedAux.project_mk,
    M72.value_mk P (subgroupLattice P I H) BJ hBJ] using
    distribution_normalized P I H (pseudolatticeMk P I z hz)

/-- [RW-rec, p. 4, Prop. 3]; [RW26, p. 12, Lem. 2].
Identity on K in both coordinate systems. -/
theorem presentation_project (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (BI BJ : L4.DistributionBasis)
    (hBI : PseudolatticePresentation P I BI)
    (hBJ : PseudolatticePresentation P (subgroupLattice P I H) BJ)
    (hP : L4.distributionPeriodPoints BI ≤ L4.distributionPeriodPoints BJ)
    (x : PseudolatticeGroup P I) :
    pseudolatticeGroupEquiv P (subgroupLattice P I H) BJ hBJ (project P I H x) =
      L4.distributionProject BI BJ hP (pseudolatticeGroupEquiv P I BI hBI x) := by
  have hI : L4.distributionLattice BI ≤ L4.distributionLattice BJ := by
    rw [hBI.2.2, hBJ.2.2]
    exact AddSubgroup.map_mono (le_overlattice P I H)
  refine Quotient.inductionOn x ?_
  intro z
  change pseudolatticeGroupEquiv P (subgroupLattice P I H) BJ hBJ
      (project P I H (pseudolatticeMk P I z.val z.property)) =
    L4.distributionProject BI BJ hP
      (pseudolatticeGroupEquiv P I BI hBI (pseudolatticeMk P I z.val z.property))
  rw [DistributionNormalizedAux.project_mk, pseudolatticeGroupEquiv_mk,
    pseudolatticeGroupEquiv_mk, L4.distributionProject_mk BI BJ hBI.1 hBJ.1 hP hI]

/-- The two-point case of [RW-rec, p. 4, (11)].
[RW26, p. 14, Prop. 9] is the corresponding product identity. -/
theorem orderTwo_distribution (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) (hh : h ≠ 0 ∧ h + h = 0)
    (x : PseudolatticeGroup P I) :
    M72.value P I x * M72.value P I (x + h) =
      (PeriodPower.multiplier P I ^ 2 /
        PeriodPower.multiplier P (subgroupLattice P I (AddSubgroup.zmultiples h))) *
      M72.value P (subgroupLattice P I (AddSubgroup.zmultiples h))
        (project P I (AddSubgroup.zmultiples h) x) := by
  have he := distribution_subgroup P I (AddSubgroup.zmultiples h) x
  rw [orderTwo_subgroup_card P I h hh,
    DistributionNormalizedAux.prod_orderTwo P I h hh
      (fun y => M72.value P I (x + y))] at he
  simpa only [add_zero] using he.symm

/-- [RW-rec, p. 4, (11)] at x = 0: the value at the order-two generator
is the ratio of multipliers. -/
theorem orderTwo_value (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) (hh : h ≠ 0 ∧ h + h = 0) :
    M72.value P I h = PeriodPower.multiplier P I ^ 2 /
      PeriodPower.multiplier P (subgroupLattice P I (AddSubgroup.zmultiples h)) := by
  have he := orderTwo_distribution P I h hh 0
  rw [zero_add, map_zero, M72.value_zero, M72.value_zero, mul_comm
    (PeriodPower.multiplier P I ^ 2 /
      PeriodPower.multiplier P (subgroupLattice P I (AddSubgroup.zmultiples h)))] at he
  have hroot : (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) ≠ 0 := by
    rw [← M72.value_zero P I]
    exact M72.value_ne_zero P I 0
  exact mul_left_cancel₀ hroot he

/-- Specialization of `distribution_subgroup` to `L4.distributionValue`,
with the same kappa orientation. [RW-rec, p. 4, (11)]; [RW26, p. 14, Prop. 9]. -/
theorem orderTwo_existing_interface (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) (hh : h ≠ 0 ∧ h + h = 0)
    (BI BJ : L4.DistributionBasis) (hBI : PseudolatticePresentation P I BI)
    (hBJ : PseudolatticePresentation P (subgroupLattice P I (AddSubgroup.zmultiples h)) BJ)
    (hP : L4.distributionPeriodPoints BI ≤ L4.distributionPeriodPoints BJ)
    (x : PseudolatticeGroup P I) :
    L4.distributionValue BI (pseudolatticeGroupEquiv P I BI hBI x) *
        L4.distributionValue BI (pseudolatticeGroupEquiv P I BI hBI (x + h)) =
      L4.distributionKappa BI BJ *
        L4.distributionValue BJ
          (L4.distributionProject BI BJ hP (pseudolatticeGroupEquiv P I BI hBI x)) := by
  have he := orderTwo_distribution P I h hh x
  rw [M72.value_eq_distribution P I BI hBI,
    M72.value_eq_distribution P I BI hBI,
    M72.value_eq_distribution P (subgroupLattice P I (AddSubgroup.zmultiples h)) BJ hBJ,
    presentation_project P I (AddSubgroup.zmultiples h) BI BJ hBI hBJ hP,
    PeriodPower.multiplier_presentation P I BI hBI,
    PeriodPower.multiplier_presentation P (subgroupLattice P I (AddSubgroup.zmultiples h))
      BJ hBJ] at he
  exact he

#print normalizedValue
#check distribution_subgroup
#check distribution_normalized
#check @L4.distributionValue_distribution
#check orderTwo_existing_interface

end SICLean.L5.DistributionNormalized
