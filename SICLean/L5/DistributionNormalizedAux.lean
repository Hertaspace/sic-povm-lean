import SICLean.L5.DistributionGeneralValues
import SICLean.L5.DistributionSubgroupLattice

set_option autoImplicit false

/-!
Helpers for the length-one specialization of [RW-rec, Prop. 3(ii)].
The quotient equivalence preserves the fibre labels. Values are compared
through the period-power theorem, including the origin.
-/

noncomputable section

open scoped Classical BigOperators
open SICLean.L3

namespace SICLean.L5.DistributionNormalizedAux

open DistributionOrbitGeometry DistributionSubgroups

universe u
variable {K : Type u} [Field K] [NumberField K]

theorem project_mk (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (z : K)
    (hz : z ∈ pseudolatticePeriodPoints P I) :
    project P I H (pseudolatticeMk P I z hz) =
      pseudolatticeMk P (subgroupLattice P I H) z
        (periodPoints_mono P I (subgroupLattice P I H) (le_overlattice P I H) hz) := by
  exact periodProject_mk P I (subgroupLattice P I H) (le_overlattice P I H) z hz

theorem subgroup_orbit_rel_iff (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I)
    (y z : Fibre P I (subgroupLattice P I H) (le_overlattice P I H) (project P I H x)) :
    (orbitSetoid P I (subgroupLattice P I H) (le_overlattice P I H)
      (project P I H x)).r y z ↔ y = z := by
  change (∃ n : ℤ, (fibrePerm P I (subgroupLattice P I H)
    (le_overlattice P I H) (project P I H x) ^ n) y = z) ↔ y = z
  rw [fibrePerm_eq_id]
  change (∃ n : ℤ, ((1 : Equiv.Perm (Fibre P I (subgroupLattice P I H)
    (le_overlattice P I H) (project P I H x))) ^ n) y = z) ↔ y = z
  simp

def fibreOrbitEquiv (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    Fibre P I (subgroupLattice P I H) (le_overlattice P I H) (project P I H x) ≃
      Orbit P I (subgroupLattice P I H) (le_overlattice P I H) (project P I H x) where
  toFun := Quotient.mk _
  invFun := orbitRepresentative P I (subgroupLattice P I H)
    (le_overlattice P I H) (project P I H x)
  left_inv := fun y => (subgroup_orbit_rel_iff P I H x _ _).mp
    (Quotient.exact (Quotient.out_eq (Quotient.mk _ y)))
  right_inv := Quotient.out_eq

def cosetOrbitEquiv (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    H ≃ Orbit P I (subgroupLattice P I H) (le_overlattice P I H) (project P I H x) :=
  (cosetFibreEquiv P I H x).trans (fibreOrbitEquiv P I H x)

theorem orbitRepresentative_coset (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) (a : H) :
    orbitRepresentative P I (subgroupLattice P I H) (le_overlattice P I H)
      (project P I H x) (cosetOrbitEquiv P I H x a) = cosetFibreEquiv P I H x a :=
  (fibreOrbitEquiv P I H x).left_inv _

theorem orbitValue_coset (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) (a : H) :
    DistributionGeneral.orbitValue P I (subgroupLattice P I H) (le_overlattice P I H)
      (project P I H x) (cosetOrbitEquiv P I H x a) = M72.value P I (x + a.val) := by
  let o := cosetOrbitEquiv P I H x a
  let r := orbitLength P I (subgroupLattice P I H) (le_overlattice P I H)
    (project P I H x) o
  let hr := orbitLength_pos P I (subgroupLattice P I H) (le_overlattice P I H)
    (project P I H x) o
  let z := pseudolatticeRepresentative P I (x + a.val)
  have hz : z ∈ pseudolatticePeriodPoints P I := (Quotient.out (x + a.val)).property
  have hmk : pseudolatticeMk P I z hz = x + a.val := Quotient.out_eq _
  have ho : ∃ n : ℤ, ((ambientUnit P I).toEquiv ^ n) (ambientMk I.val z) =
      (orbitRepresentative P I (subgroupLattice P I H) (le_overlattice P I H)
        (project P I H x) o).val := by
    refine ⟨0, ?_⟩
    simp only [zpow_zero, Equiv.Perm.one_apply]
    rw [orbitRepresentative_coset, cosetFibreEquiv_apply,
      ← toAmbient_mk P I z hz, hmk]
  have hv := DistributionGeneral.orbitValue_representative P I (subgroupLattice P I H)
    (le_overlattice P I H) (project P I H x) o z
    (PeriodPower.periodPoints_le_pow P I r hr hz) ho
  calc
    DistributionGeneral.orbitValue P I (subgroupLattice P I H) (le_overlattice P I H)
        (project P I H x) o =
        M72.value (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr)
          (PeriodPower.periodPowerInclusion P I r hr (x + a.val)) := by
      rw [← hmk, PeriodPower.periodPowerInclusion_mk]
      exact hv.symm
    _ = M72.value P I (x + a.val) ^ r := PeriodPower.value_pow P I r hr _
    _ = M72.value P I (x + a.val) := by
      rw [show r = 1 from orbitLength_one P I H x o, pow_one]

theorem prod_orderTwo (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) (hh : h ≠ 0 ∧ h + h = 0)
    (f : PseudolatticeGroup P I → ℂ) :
    (∏ a : AddSubgroup.zmultiples h, f a.val) = f 0 * f h := by
  let t : AddSubgroup.zmultiples h := ⟨h, AddSubgroup.mem_zmultiples h⟩
  have hne : (0 : AddSubgroup.zmultiples h) ≠ t := by
    intro he
    exact hh.1 (congrArg Subtype.val he).symm
  have hpair : ({0, t} : Finset (AddSubgroup.zmultiples h)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Finset.card_pair hne,
      ← Nat.card_eq_fintype_card, orderTwo_subgroup_card P I h hh]
  rw [← hpair, Finset.prod_pair hne]
  rfl

end SICLean.L5.DistributionNormalizedAux
