import SICLean.L5.DistributionOrbitGeometry

set_option autoImplicit false

noncomputable section

open SICLean.L3
open SICLean.L5.DistributionOrbitGeometry

namespace SICLean.L5.DistributionSubgroupLatticeAux

universe u
variable {K : Type u} [Field K] [NumberField K]

theorem mk_zero (P : PeriodData K) (I : StablePseudolattice P) :
    pseudolatticeMk P I 0 (pseudolatticePeriodPoints P I).zero_mem = 0 := rfl

theorem mk_add (P : PeriodData K) (I : StablePseudolattice P)
    (x y : K) (hx : x ∈ pseudolatticePeriodPoints P I)
    (hy : y ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeMk P I (x + y) ((pseudolatticePeriodPoints P I).add_mem hx hy) =
      pseudolatticeMk P I x hx + pseudolatticeMk P I y hy := rfl

theorem mk_zsmul (P : PeriodData K) (I : StablePseudolattice P)
    (n : ℤ) (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeMk P I (n • x) ((pseudolatticePeriodPoints P I).zsmul_mem hx n) =
      n • pseudolatticeMk P I x hx := by
  exact map_zsmul (QuotientAddGroup.mk'
    (I.val.toAddSubgroup.addSubgroupOf (pseudolatticePeriodPoints P I)))
    n (⟨x, hx⟩ : pseudolatticePeriodPoints P I)

theorem mk_sub (P : PeriodData K) (I : StablePseudolattice P)
    (x y : K) (hx : x ∈ pseudolatticePeriodPoints P I)
    (hy : y ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeMk P I (x - y) ((pseudolatticePeriodPoints P I).sub_mem hx hy) =
      pseudolatticeMk P I x hx - pseudolatticeMk P I y hy := rfl

theorem mk_eq_iff (P : PeriodData K) (I : StablePseudolattice P)
    (x y : K) (hx : x ∈ pseudolatticePeriodPoints P I)
    (hy : y ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeMk P I x hx = pseudolatticeMk P I y hy ↔ x - y ∈ I.val :=
  QuotientAddGroup.eq_iff_sub_mem

theorem mk_eq_zero_iff (P : PeriodData K) (I : StablePseudolattice P)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeMk P I x hx = 0 ↔ x ∈ I.val :=
  QuotientAddGroup.eq_zero_iff _

theorem mk_representative (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) :
    pseudolatticeMk P I (pseudolatticeRepresentative P I x) (Quotient.out x).property = x :=
  Quotient.out_eq x

theorem ambientProject_mk (I J : Submodule ℤ K) (hIJ : I ≤ J) (z : K) :
    ambientProject I J hIJ (ambientMk I z) = ambientMk J z := rfl

theorem ambientProject_toAmbient (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I) :
    ambientProject I.val J.val hIJ (toAmbient P I x) =
      toAmbient P J (periodProject P I J hIJ x) := by
  refine Quotient.inductionOn x ?_
  intro z
  rfl

theorem toAmbient_representative (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) :
    toAmbient P I x = ambientMk I.val (pseudolatticeRepresentative P I x) := by
  calc
    _ = toAmbient P I (pseudolatticeMk P I _ (Quotient.out x).property) :=
      congrArg _ (mk_representative P I x).symm
    _ = _ := toAmbient_mk P I _ (Quotient.out x).property

theorem fibre_difference_mem (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I)
    (y : Fibre P I J hIJ (periodProject P I J hIJ x)) :
    Quotient.out y.val - pseudolatticeRepresentative P I x ∈ J.val := by
  have hout : ambientMk I.val (Quotient.out y.val) = y.val := Quotient.out_eq y.val
  have heq : ambientMk J.val (Quotient.out y.val) =
      ambientMk J.val (pseudolatticeRepresentative P I x) := by
    calc
      _ = ambientProject I.val J.val hIJ (ambientMk I.val (Quotient.out y.val)) := rfl
      _ = ambientProject I.val J.val hIJ y.val := congrArg _ hout
      _ = toAmbient P J (periodProject P I J hIJ x) := y.property
      _ = ambientProject I.val J.val hIJ (toAmbient P I x) :=
        (ambientProject_toAmbient P I J hIJ x).symm
      _ = _ := by rw [toAmbient_representative, ambientProject_mk]
  exact QuotientAddGroup.eq_iff_sub_mem.mp heq

/-- Computing the relative index of a literal inverse image in the period points. -/
theorem preimage_index (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (J : Submodule ℤ K)
    (hJ : ∀ z, z ∈ J ↔
      ∃ hz : z ∈ pseudolatticePeriodPoints P I, pseudolatticeMk P I z hz ∈ H) :
    inclusionIndex I.val J = Nat.card H := by
  let T := pseudolatticePeriodPoints P I
  let q : T →+ PseudolatticeGroup P I :=
    QuotientAddGroup.mk' (I.val.toAddSubgroup.addSubgroupOf T)
  let L : AddSubgroup T := J.toAddSubgroup.comap T.subtype
  have hmap : L.map T.subtype = J.toAddSubgroup := by
    apply AddSubgroup.map_comap_eq_self
    intro z hz
    exact ⟨⟨z, ((hJ z).mp hz).choose⟩, rfl⟩
  have hker : q.ker = I.val.toAddSubgroup.comap T.subtype := by
    ext z
    exact QuotientAddGroup.eq_zero_iff z
  have himage : L.map q = H := by
    ext a
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzP, hzH⟩ := (hJ z.val).mp hz
      exact hzH
    · intro ha
      refine ⟨Quotient.out a, ?_, Quotient.out_eq a⟩
      apply (hJ _).mpr
      refine ⟨(Quotient.out a).property, ?_⟩
      change pseudolatticeMk P I (pseudolatticeRepresentative P I a) _ ∈ H
      rwa [mk_representative]
  have hrel := I.val.toAddSubgroup.relIndex_comap T.subtype L
  rw [hmap] at hrel
  change I.val.toAddSubgroup.relIndex J.toAddSubgroup = Nat.card H
  rw [← hrel, ← hker, AddSubgroup.relIndex_ker, himage]

end SICLean.L5.DistributionSubgroupLatticeAux
