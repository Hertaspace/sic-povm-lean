import SICLean.L5.PeriodPowerData
import SICLean.L5.DistributionOrbitGeometryAux
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Cycle.Basic

set_option autoImplicit false

/-!
# The finite fibre in K/I and its ε-orbits

[RW-rec, p. 4] and [RW-rec, Appendix A, pp. 18--20]. Periods are as in
[RW26, p. 12, Lem. 2] and [RW26, p. 14, Prop. 8].

The fibre is taken in K/I. A point of the fibre is fixed by some positive power of ε.
Each quotient map below sends a field representative to that same representative.
-/

noncomputable section

open scoped Classical BigOperators
open SICLean.L3

namespace SICLean.L5.DistributionOrbitGeometry

universe u
variable {K : Type u} [Field K] [NumberField K]

abbrev AmbientGroup (I : Submodule ℤ K) := K ⧸ I.toAddSubgroup

def ambientMk (I : Submodule ℤ K) : K →+ AmbientGroup I :=
  QuotientAddGroup.mk' I.toAddSubgroup

def ambientProject (I J : Submodule ℤ K) (hIJ : I ≤ J) :
    AmbientGroup I →+ AmbientGroup J :=
  QuotientAddGroup.map I.toAddSubgroup J.toAddSubgroup
    (AddMonoidHom.id K) (by exact hIJ)

def inclusionIndex (I J : Submodule ℤ K) : ℕ :=
  I.toAddSubgroup.relIndex J.toAddSubgroup

def toAmbient (P : PeriodData K) (I : StablePseudolattice P) :
    PseudolatticeGroup P I →+ AmbientGroup I.val :=
  QuotientAddGroup.map _ _ (pseudolatticePeriodPoints P I).subtype (by
    intro z hz
    exact hz)

/-- Multiplication by the field unit, with its inverse. -/
def ambientUnit (P : PeriodData K) (I : StablePseudolattice P) :
    AmbientGroup I.val ≃+ AmbientGroup I.val where
  toFun := QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft P.epsilon) (by
    intro z hz
    change P.epsilon * z ∈ I.val
    rw [← I.property.2]
    exact (pseudolatticeScale_mem_iff _ _ _).2 ⟨z, hz, rfl⟩)
  invFun := QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft P.epsilon⁻¹) (by
    intro z hz
    change P.epsilon⁻¹ * z ∈ I.val
    have hinv : pseudolatticeScale P.epsilon⁻¹ I.val = I.val := by
      calc
        pseudolatticeScale P.epsilon⁻¹ I.val =
            pseudolatticeScale P.epsilon⁻¹ (pseudolatticeScale P.epsilon I.val) :=
          congrArg (pseudolatticeScale P.epsilon⁻¹) I.property.2.symm
        _ = I.val := (pseudolatticeScale_inv P.epsilon P.epsilon_ne_zero I.val).1
    rw [← hinv]
    exact (pseudolatticeScale_mem_iff _ _ _).2 ⟨z, hz, rfl⟩)
  left_inv := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z => simp [QuotientAddGroup.map_mk, P.epsilon_ne_zero]
  right_inv := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z => simp [QuotientAddGroup.map_mk, P.epsilon_ne_zero]
  map_add' := (QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft P.epsilon) _).map_add

/-- [RW-rec, p. 4]; [RW26, p. 12, Lem. 2].
The K/I label of a period representative. -/
theorem toAmbient_mk (P : PeriodData K) (I : StablePseudolattice P)
    (z : K) (hz : z ∈ pseudolatticePeriodPoints P I) :
    toAmbient P I (pseudolatticeMk P I z hz) = ambientMk I.val z := by rfl

/-- The period group embeds in K/I. [RW-rec, p. 4]; [RW26, p. 12, Lem. 2]. -/
theorem toAmbient_injective (P : PeriodData K) (I : StablePseudolattice P) :
    Function.Injective (toAmbient P I) := by
  intro y z h
  induction y using QuotientAddGroup.induction_on with
  | H y =>
    induction z using QuotientAddGroup.induction_on with
    | H z =>
      change (QuotientAddGroup.mk y.val : AmbientGroup I.val) =
        QuotientAddGroup.mk z.val at h
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change y.val - z.val ∈ I.val
      exact QuotientAddGroup.eq_iff_sub_mem.mp h

/-- [RW-rec, p. 3, Def. 1]; [RW26, p. 12, Lem. 2]. -/
theorem mem_range_toAmbient_iff (P : PeriodData K) (I : StablePseudolattice P)
    (y : AmbientGroup I.val) :
    y ∈ Set.range (toAmbient P I) ↔ ambientUnit P I y = y := by
  induction y using QuotientAddGroup.induction_on with
  | H z =>
    constructor
    · rintro ⟨g, hg⟩
      induction g using QuotientAddGroup.induction_on with
      | H g =>
        have hgz : g.val - z ∈ I.val := QuotientAddGroup.eq_iff_sub_mem.mp hg
        have hmem : z ∈ pseudolatticePeriodPoints P I := by
          have hgmem := g.property
          have hdiff := pseudolattice_le_periodPoints P I hgz
          simpa using (pseudolatticePeriodPoints P I).sub_mem hgmem hdiff
        have hforward := (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I _).mp hmem
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        simpa [sub_mul, one_mul] using hforward
    · intro h
      have hz : (P.epsilon - 1) * z ∈ I.val := by
        simpa [ambientUnit, sub_mul, one_mul] using
          (QuotientAddGroup.eq_iff_sub_mem.mp h)
      have hmem : z ∈ pseudolatticePeriodPoints P I :=
        (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I _).mpr hz
      exact ⟨pseudolatticeMk P I z hmem, rfl⟩

/-- [RW-rec, p. 4]; [RW26, p. 12, Lem. 2]. Inclusion of period points. -/
theorem periodPoints_mono (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) :
    pseudolatticePeriodPoints P I ≤ pseudolatticePeriodPoints P J := by
  intro z hz
  exact hIJ hz

def periodProject (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) : PseudolatticeGroup P I →+ PseudolatticeGroup P J :=
  QuotientAddGroup.map _ _
    (AddSubgroup.inclusion (periodPoints_mono P I J hIJ)) (by
      intro z hz
      exact hIJ hz)

/-- [RW-rec, p. 4]: the projection is induced by the identity on K.
Its restriction to period groups need not be surjective. -/
theorem periodProject_mk (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (z : K) (hz : z ∈ pseudolatticePeriodPoints P I) :
    periodProject P I J hIJ (pseudolatticeMk P I z hz) =
      pseudolatticeMk P J z (periodPoints_mono P I J hIJ hz) := by rfl

/-- The fibre of K/I → K/J over the embedded period point. -/
abbrev Fibre (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :=
  {y : AmbientGroup I.val // ambientProject I.val J.val hIJ y = toAmbient P J x}

/-- The ε-permutation of the fibre. -/
def fibrePerm (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    Equiv.Perm (Fibre P I J hIJ x) where
  toFun := fun y => ⟨ambientUnit P I y.val, by
    have hcomm : ∀ a, ambientProject I.val J.val hIJ (ambientUnit P I a) =
        ambientUnit P J (ambientProject I.val J.val hIJ a) := by
      intro a
      induction a using QuotientAddGroup.induction_on with
      | H a => rfl
    rw [hcomm, y.property]
    exact (mem_range_toAmbient_iff P J _).mp ⟨x, rfl⟩⟩
  invFun := fun y => ⟨(ambientUnit P I).symm y.val, by
    have hcomm : ∀ a, ambientProject I.val J.val hIJ ((ambientUnit P I).symm a) =
        (ambientUnit P J).symm (ambientProject I.val J.val hIJ a) := by
      intro a
      induction a using QuotientAddGroup.induction_on with
      | H a => rfl
    rw [hcomm, y.property]
    apply (ambientUnit P J).injective
    rw [AddEquiv.apply_symm_apply]
    exact ((mem_range_toAmbient_iff P J _).mp ⟨x, rfl⟩).symm⟩
  left_inv := by intro y; apply Subtype.ext; exact (ambientUnit P I).symm_apply_apply y.val
  right_inv := by intro y; apply Subtype.ext; exact (ambientUnit P I).apply_symm_apply y.val

def orbitSetoid (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    Setoid (Fibre P I J hIJ x) where
  r y z := ∃ n : ℤ, (fibrePerm P I J hIJ x ^ n) y = z
  iseqv := Equiv.Perm.SameCycle.equivalence (fibrePerm P I J hIJ x)

abbrev Orbit (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :=
  Quotient (orbitSetoid P I J hIJ x)

def orbitRepresentative (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) : Fibre P I J hIJ x := Quotient.out o

def orbitLength (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) : ℕ :=
  Function.minimalPeriod (fibrePerm P I J hIJ x) (orbitRepresentative P I J hIJ x o)

def orbitLift (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) : K :=
  Quotient.out (orbitRepresentative P I J hIJ x o).val

/-- [RW-rec, p. 4]; [RW-rec, Appendix A, p. 20].
The lattice index is positive. -/
theorem inclusionIndex_pos (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) : 0 < inclusionIndex I.val J.val := by
  exact DistributionOrbitGeometryAux.lattice_relIndex_pos I.val J.val
    I.property.1 J.property.1 hIJ

/-- [RW-rec, p. 4]; [RW-rec, Appendix A, pp. 18--20].
The fibre is finite of cardinality equal to the inclusion index. -/
theorem fibre_finite_card (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    Finite (Fibre P I J hIJ x) ∧
      Nat.card (Fibre P I J hIJ x) = inclusionIndex I.val J.val := by
  exact DistributionOrbitGeometryAux.lattice_fibre_finite_card I.val J.val
    I.property.1 J.property.1 hIJ (toAmbient P J x)

instance fibreFintype (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    Fintype (Fibre P I J hIJ x) := @Fintype.ofFinite _ (fibre_finite_card P I J hIJ x).1

instance orbitFintype (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    Fintype (Orbit P I J hIJ x) := Fintype.ofFinite _

/-- [RW-rec, p. 4]: the least positive return time. -/
theorem orbitLength_pos (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) : 0 < orbitLength P I J hIJ x o := by
  exact Function.minimalPeriod_pos_of_mem_periodicPts
    ((fibrePerm P I J hIJ x).injective.mem_periodicPts _)

/-- [RW-rec, p. 4]; [RW-rec, Appendix A, p. 19].
The orbit length returns the representative to itself. -/
theorem orbitLength_returns (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) :
    (fibrePerm P I J hIJ x ^ orbitLength P I J hIJ x o)
      (orbitRepresentative P I J hIJ x o) = orbitRepresentative P I J hIJ x o := by
  exact Function.iterate_minimalPeriod

/-- [RW-rec, p. 4]: a return exponent is a multiple of the orbit length. -/
theorem orbitLength_dvd_iff (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) (s : ℕ) :
    orbitLength P I J hIJ x o ∣ s ↔
      (fibrePerm P I J hIJ x ^ s) (orbitRepresentative P I J hIJ x o) =
        orbitRepresentative P I J hIJ x o := by
  exact Function.isPeriodicPt_iff_minimalPeriod_dvd.symm

/-- [RW-rec, Appendix A, p. 20]: the sum of the orbit lengths equals the inclusion
index, which is the exponent of μ_I. -/
theorem sum_orbitLength (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    ∑ o : Orbit P I J hIJ x, orbitLength P I J hIJ x o =
      inclusionIndex I.val J.val := by
  let q : Fibre P I J hIJ x → Orbit P I J hIJ x := Quotient.mk _
  have hc : ∀ o : Orbit P I J hIJ x,
      Fintype.card {y // q y = o} = orbitLength P I J hIJ x o := by
    intro o
    let f := fibrePerm P I J hIJ x
    let a := orbitRepresentative P I J hIJ x o
    let g : Fin (orbitLength P I J hIJ x o) → {y // q y = o} := fun n =>
      ⟨(f ^ n.val) a, by
        calc
          q ((f ^ n.val) a) = q a := Quotient.sound
            ((Equiv.Perm.SameCycle.refl f a).pow_left)
          _ = o := Quotient.out_eq o⟩
    have hg : Function.Bijective g := by
      constructor
      · intro m n hmn
        apply Fin.ext
        exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod m.isLt n.isLt).mp
          (congrArg Subtype.val hmn)
      · intro y
        have hy : f.SameCycle a y.val :=
          Quotient.exact ((Quotient.out_eq o).trans y.property.symm)
        obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
        refine ⟨⟨n % orbitLength P I J hIJ x o,
          Nat.mod_lt _ (orbitLength_pos P I J hIJ x o)⟩, ?_⟩
        apply Subtype.ext
        exact Function.iterate_mod_minimalPeriod_eq.trans hn
    simpa using (Fintype.card_congr (Equiv.ofBijective g hg)).symm
  calc
    (∑ o : Orbit P I J hIJ x, orbitLength P I J hIJ x o) =
        ∑ o : Orbit P I J hIJ x, Fintype.card {y // q y = o} := by
      apply Finset.sum_congr rfl
      intro o _
      exact (hc o).symm
    _ = Fintype.card (Fibre P I J hIJ x) := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv q)
    _ = inclusionIndex I.val J.val := by
      rw [← Nat.card_eq_fintype_card]
      exact (fibre_finite_card P I J hIJ x).2

/-- [RW-rec, Appendix A, p. 19]: the orbit lift lies in the period group of
the original lattice I, in the same field. -/
theorem orbitLift_mem (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) :
    orbitLift P I J hIJ x o ∈ pseudolatticePeriodPoints
      (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
      (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o)) := by
  have hsemi : Function.Semiconj (Subtype.val : Fibre P I J hIJ x → AmbientGroup I.val)
      (fibrePerm P I J hIJ x) (ambientUnit P I) := fun _ => rfl
  have hret : ((ambientUnit P I).toEquiv ^ orbitLength P I J hIJ x o)
      (orbitRepresentative P I J hIJ x o).val = (orbitRepresentative P I J hIJ x o).val :=
    (hsemi.iterate_right _ _).symm.trans
      (congrArg Subtype.val (orbitLength_returns P I J hIJ x o))
  apply (DistributionOrbitGeometryAux.quotient_return_iff_pow_mem P I
    (ambientUnit P I).toEquiv (fun _ => rfl) _ (orbitLength_pos P I J hIJ x o) _).mp
  change ((ambientUnit P I).toEquiv ^ orbitLength P I J hIJ x o)
      (QuotientAddGroup.mk (Quotient.out (orbitRepresentative P I J hIJ x o).val)) =
    QuotientAddGroup.mk (Quotient.out (orbitRepresentative P I J hIJ x o).val)
  simpa only [QuotientAddGroup.mk, Quotient.out_eq] using hret

/-- [RW-rec, Appendix A, pp. 19--20]; [RW26, p. 14, Prop. 8].
The same membership for any field representative of any point of the orbit. -/
theorem orbit_member_mem (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) (z : K)
    (ho : ∃ a : ℤ, ((ambientUnit P I).toEquiv ^ a) (ambientMk I.val z) =
      (orbitRepresentative P I J hIJ x o).val) :
    z ∈ pseudolatticePeriodPoints
      (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
      (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o)) := by
  obtain ⟨a, ha⟩ := ho
  have hsemi : Function.Semiconj (Subtype.val : Fibre P I J hIJ x → AmbientGroup I.val)
      (fibrePerm P I J hIJ x) (ambientUnit P I) := fun _ => rfl
  have hret : ((ambientUnit P I).toEquiv ^ orbitLength P I J hIJ x o)
      (orbitRepresentative P I J hIJ x o).val = (orbitRepresentative P I J hIJ x o).val :=
    (hsemi.iterate_right _ _).symm.trans
      (congrArg Subtype.val (orbitLength_returns P I J hIJ x o))
  apply (DistributionOrbitGeometryAux.quotient_return_iff_pow_mem P I
    (ambientUnit P I).toEquiv (fun _ => rfl) _ (orbitLength_pos P I J hIJ x o) _).mp
  apply (((ambientUnit P I).toEquiv ^ a) : Equiv.Perm _).injective
  have hcomm := Equiv.Perm.zpow_apply_comm (ambientUnit P I).toEquiv a
    (orbitLength P I J hIJ x o : ℤ) (x := ambientMk I.val z)
  simp only [zpow_natCast] at hcomm
  change ((ambientUnit P I).toEquiv ^ a)
      (((ambientUnit P I).toEquiv ^ orbitLength P I J hIJ x o) (ambientMk I.val z)) =
    ((ambientUnit P I).toEquiv ^ a) (ambientMk I.val z)
  rw [hcomm, ha, hret]

/-- [RW-rec, Appendix A, p. 19]: the singleton zero orbit occurs over x = 0,
and every representative of that orbit is zero. -/
theorem zero_orbit (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    (∃ o : Orbit P I J hIJ x,
      (orbitRepresentative P I J hIJ x o).val = 0) ↔ x = 0 := by
  constructor
  · rintro ⟨o, ho⟩
    apply toAmbient_injective P J
    rw [map_zero, ← (orbitRepresentative P I J hIJ x o).property, ho, map_zero]
  · rintro rfl
    let y : Fibre P I J hIJ 0 := ⟨0, by simp⟩
    let o : Orbit P I J hIJ 0 := Quotient.mk _ y
    have hsame : (fibrePerm P I J hIJ 0).SameCycle
        (orbitRepresentative P I J hIJ 0 o) y := Quotient.exact (Quotient.out_eq o)
    have hfix : Function.IsFixedPt (fibrePerm P I J hIJ 0) y := by
      apply Subtype.ext
      change ambientUnit P I 0 = 0
      exact map_zero _
    exact ⟨o, congrArg Subtype.val (hsame.eq_of_right hfix)⟩

/-- [RW-rec, Appendix A, p. 19]: the zero orbit has length one.
No index shift is applied to it. -/
theorem zero_orbit_length (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) (ho : (orbitRepresentative P I J hIJ x o).val = 0) :
    orbitLength P I J hIJ x o = 1 := by
  apply Function.minimalPeriod_eq_one_iff_isFixedPt.mpr
  apply Subtype.ext
  change ambientUnit P I (orbitRepresentative P I J hIJ x o).val =
    (orbitRepresentative P I J hIJ x o).val
  rw [ho, map_zero]

#check @QuotientAddGroup.map
#check @Function.minimalPeriod
#print Fibre
#print orbitSetoid
#print orbitLength
#print orbitLift

end SICLean.L5.DistributionOrbitGeometry
