import SICLean.L5.DistributionOrbitGeometry
import SICLean.L5.DistributionSubgroupLatticeAux

set_option autoImplicit false

/-!
# The overlattice attached to an arbitrary period subgroup

[RW-rec, Prop. 3(ii), p. 4; Appendix A, p. 20].
See also [RW26, Prop. 9, p. 14].
The subgroup lies in the period group. Its inverse image in `K`
defines `J`; the lattice, stability, index, and fibre properties are the conclusions.
-/

noncomputable section

open scoped Classical BigOperators
open SICLean.L3

namespace SICLean.L5.DistributionSubgroups

open DistributionOrbitGeometry
open DistributionSubgroupLatticeAux

universe u
variable {K : Type u} [Field K] [NumberField K]

instance periodGroupFintype (P : PeriodData K) (I : StablePseudolattice P) :
    Fintype (PseudolatticeGroup P I) :=
  @Fintype.ofFinite _ (pseudolatticeGroup_finite_card P I).1

/-- The literal inverse image of H under z |-> z+I on the period points. -/
def overlattice (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) : Submodule ℤ K where
  carrier := {z | ∃ hz : z ∈ pseudolatticePeriodPoints P I, pseudolatticeMk P I z hz ∈ H}
  zero_mem' := ⟨(pseudolatticePeriodPoints P I).zero_mem, H.zero_mem⟩
  add_mem' := by
    rintro x y ⟨hx, hxH⟩ ⟨hy, hyH⟩
    refine ⟨(pseudolatticePeriodPoints P I).add_mem hx hy, ?_⟩
    rw [mk_add P I x y hx hy]
    exact H.add_mem hxH hyH
  smul_mem' := by
    rintro n x ⟨hx, hxH⟩
    refine ⟨(pseudolatticePeriodPoints P I).zsmul_mem hx n, ?_⟩
    rw [mk_zsmul P I n x hx]
    exact H.zsmul_mem hxH n

/-- [RW-rec, pp. 4, 20]: definition of `J`. -/
theorem mem_overlattice_iff (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (z : K) :
    z ∈ overlattice P I H ↔
      ∃ hz : z ∈ pseudolatticePeriodPoints P I, pseudolatticeMk P I z hz ∈ H := Iff.rfl

/-- [RW-rec, pp. 4, 20]. -/
theorem le_overlattice (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) : I.val ≤ overlattice P I H := by
  intro z hz
  refine ⟨pseudolattice_le_periodPoints P I hz, ?_⟩
  rw [(mk_eq_zero_iff P I z _).mpr hz]
  exact H.zero_mem

/-- [RW-rec, pp. 4, 20]: the upper inclusion uses period points,
which `PeriodPower.conventionEquiv` identifies with `(epsilon - 1)⁻¹ I / I`. -/
theorem overlattice_le_periodPoints (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) :
    (overlattice P I H).toAddSubgroup ≤ pseudolatticePeriodPoints P I := by
  rintro z ⟨hz, _⟩
  exact hz

/-- [RW-rec, Prop. 3(ii), p. 4]. No freeness premise on `J` is assumed. -/
theorem overlattice_isLattice (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) :
    Submodule.IsLattice ℚ (overlattice P I H) := by
  let S : Set K := Set.range (fun a : H => pseudolatticeRepresentative P I a.val)
  have hrep (a : H) : pseudolatticeRepresentative P I a.val ∈ overlattice P I H := by
    refine ⟨(Quotient.out a.val).property, ?_⟩
    rw [mk_representative]
    exact a.property
  have heq : overlattice P I H = I.val ⊔ Submodule.span ℤ S := by
    apply le_antisymm
    · rintro z ⟨hz, hzH⟩
      let a : H := ⟨pseudolatticeMk P I z hz, hzH⟩
      have ha := mk_representative P I a.val
      have hdiff : z - pseudolatticeRepresentative P I a.val ∈ I.val :=
        (mk_eq_iff P I _ _ hz (Quotient.out a.val).property).mp ha.symm
      have hr : pseudolatticeRepresentative P I a.val ∈ Submodule.span ℤ S :=
        Submodule.subset_span ⟨a, rfl⟩
      have hm := (I.val ⊔ Submodule.span ℤ S).add_mem
        ((show I.val ≤ I.val ⊔ Submodule.span ℤ S from le_sup_left) hdiff)
        ((show Submodule.span ℤ S ≤ I.val ⊔ Submodule.span ℤ S from le_sup_right) hr)
      simpa only [sub_add_cancel] using hm
    · refine sup_le (le_overlattice P I H) (Submodule.span_le.mpr ?_)
      rintro z ⟨a, rfl⟩
      exact hrep a
  let := I.property.1
  apply Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ (le_overlattice P I H)
  rw [heq]
  exact I.property.1.fg.sup (Submodule.fg_span (Set.finite_range _))

/-- [RW-rec, p. 20]: epsilon fixes `J/I` and preserves `I`, hence `epsilon J = J`. -/
theorem overlattice_periodStable (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) :
    PeriodStable P (overlattice P I H) := by
  let J := overlattice P I H
  have hIJ : I.val ≤ J := le_overlattice P I H
  have hmulI (z : K) (hz : z ∈ I.val) : P.epsilon * z ∈ I.val := by
    rw [← I.property.2]
    exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨z, hz, rfl⟩
  have hdiff (z : K) (hz : z ∈ J) : P.epsilon⁻¹ * z - z ∈ I.val := by
    have hp := overlattice_le_periodPoints P I H hz
    change (P.epsilon⁻¹ - 1) * z ∈ I.val at hp
    simpa only [sub_mul, one_mul] using hp
  have hinv (z : K) (hz : z ∈ J) : P.epsilon⁻¹ * z ∈ J := by
    simpa only [sub_add_cancel] using J.add_mem (hIJ (hdiff z hz)) hz
  have hmul (z : K) (hz : z ∈ J) : P.epsilon * z ∈ J := by
    have hm := hmulI _ (hdiff z hz)
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ P.epsilon_ne_zero, one_mul] at hm
    simpa only [sub_sub_cancel] using J.sub_mem hz (hIJ hm)
  change pseudolatticeScale P.epsilon J = J
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hz
    exact hmul w hw
  · intro z hz
    refine (pseudolatticeScale_mem_iff _ _ _).mpr ⟨P.epsilon⁻¹ * z, hinv z hz, ?_⟩
    rw [← mul_assoc, mul_inv_cancel₀ P.epsilon_ne_zero, one_mul]

def subgroupLattice (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) : StablePseudolattice P :=
  ⟨overlattice P I H, overlattice_isLattice P I H, overlattice_periodStable P I H⟩

def project (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) :
    PseudolatticeGroup P I →+ PseudolatticeGroup P (subgroupLattice P I H) :=
  periodProject P I (subgroupLattice P I H) (le_overlattice P I H)

/-- [RW-rec, p. 4; Appendix A, p. 20]. -/
theorem overlattice_index (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) :
    inclusionIndex I.val (subgroupLattice P I H).val = Nat.card H := by
  exact preimage_index P I H (overlattice P I H) (mem_overlattice_iff P I H)

/-- [RW-rec, pp. 4, 20]. No surjectivity on `G_J` is claimed. -/
theorem project_kernel (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    project P I H x = 0 ↔ x ∈ H := by
  refine Quotient.inductionOn x ?_
  intro z
  change periodProject P I (subgroupLattice P I H) (le_overlattice P I H)
    (pseudolatticeMk P I z.val z.property) = 0 ↔ pseudolatticeMk P I z.val z.property ∈ H
  apply (mk_eq_zero_iff P (subgroupLattice P I H) z.val
    (periodPoints_mono P I _ (le_overlattice P I H) z.property)).trans
  exact ⟨fun hz => (mem_overlattice_iff P I H z.val).mp hz |>.choose_spec,
    fun hz => ⟨z.property, hz⟩⟩

/-- The actual fibre over pi(x) is x+H in K/I. The inverse subtracts
one field representative of x, then takes its I-class. -/
def cosetFibreEquiv (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    H ≃ Fibre P I (subgroupLattice P I H) (le_overlattice P I H) (project P I H x) where
  toFun := fun a => ⟨toAmbient P I (x + a.val), by
    calc
      _ = toAmbient P (subgroupLattice P I H) (project P I H (x + a.val)) :=
        ambientProject_toAmbient P I _ (le_overlattice P I H) _
      _ = _ := by rw [map_add, (project_kernel P I H a.val).mpr a.property, add_zero]⟩
  invFun := fun y =>
    ⟨pseudolatticeMk P I
      (Quotient.out y.val - pseudolatticeRepresentative P I x) (by
        exact overlattice_le_periodPoints P I H
          (fibre_difference_mem P I (subgroupLattice P I H) (le_overlattice P I H) x y)), by
        exact (mem_overlattice_iff P I H _).mp
          (fibre_difference_mem P I (subgroupLattice P I H) (le_overlattice P I H) x y)
          |>.choose_spec⟩
  left_inv := by
    intro a
    apply Subtype.ext
    apply toAmbient_injective P I
    change toAmbient P I (pseudolatticeMk P I
      (Quotient.out (toAmbient P I (x + a.val)) - pseudolatticeRepresentative P I x) _) =
      toAmbient P I a.val
    rw [toAmbient_mk, map_sub]
    have hout : ambientMk I.val (Quotient.out (toAmbient P I (x + a.val))) =
        toAmbient P I (x + a.val) := Quotient.out_eq _
    rw [hout, ← toAmbient_representative, map_add, add_sub_cancel_left]
  right_inv := by
    intro y
    apply Subtype.ext
    change toAmbient P I (x + pseudolatticeMk P I
      (Quotient.out y.val - pseudolatticeRepresentative P I x) _) = y.val
    rw [map_add, toAmbient_mk, map_sub, ← toAmbient_representative]
    have hout : ambientMk I.val (Quotient.out y.val) = y.val := Quotient.out_eq _
    rw [hout]
    abel

/-- [RW-rec, Appendix A, p. 20]: the equivalence has the expected labels. -/
theorem cosetFibreEquiv_apply (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) (a : H) :
    (cosetFibreEquiv P I H x a).val = toAmbient P I (x + a.val) := rfl

/-- [RW-rec, Appendix A, p. 20]: every point of this fibre is fixed.
For an arbitrary point of `G_J` outside the image of `pi`, this need not hold. -/
theorem fibrePerm_eq_id (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    fibrePerm P I (subgroupLattice P I H) (le_overlattice P I H) (project P I H x) =
      Equiv.refl _ := by
  apply Equiv.ext
  intro y
  obtain ⟨a, rfl⟩ := (cosetFibreEquiv P I H x).surjective y
  apply Subtype.ext
  change ambientUnit P I (toAmbient P I (x + a.val)) = toAmbient P I (x + a.val)
  exact (mem_range_toAmbient_iff P I _).mp ⟨x + a.val, rfl⟩

/-- [RW-rec, Appendix A, p. 20]: the length-one specialization used to derive (11) from (10). -/
theorem orbitLength_one (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I)
    (o : Orbit P I (subgroupLattice P I H) (le_overlattice P I H) (project P I H x)) :
    orbitLength P I (subgroupLattice P I H) (le_overlattice P I H)
      (project P I H x) o = 1 := by
  unfold orbitLength
  rw [fibrePerm_eq_id]
  exact Function.minimalPeriod_id

/-- [RW-rec, p. 4].
The cyclic subgroup construction recovers the lattice `I + ℤ·h`. -/
theorem overlattice_zmultiples (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) :
    overlattice P I (AddSubgroup.zmultiples h) = pseudolatticeOverlattice P I h := by
  let r := pseudolatticeRepresentative P I h
  have hr : r ∈ pseudolatticePeriodPoints P I := (Quotient.out h).property
  apply le_antisymm
  · rintro z ⟨hz, hzH⟩
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hzH
    have heq : pseudolatticeMk P I z hz =
        pseudolatticeMk P I (n • r) ((pseudolatticePeriodPoints P I).zsmul_mem hr n) := by
      rw [mk_zsmul P I n r hr, mk_representative]
      exact hn.symm
    have hdiff := (mk_eq_iff P I z (n • r) hz _).mp heq
    apply Submodule.mem_sup.mpr
    exact ⟨z - n • r, hdiff, n • r,
      Submodule.smul_mem _ n (Submodule.mem_span_singleton_self r), sub_add_cancel _ _⟩
  · apply sup_le (le_overlattice P I (AddSubgroup.zmultiples h))
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    refine ⟨hr, ?_⟩
    rw [mk_representative]
    exact AddSubgroup.mem_zmultiples h

/-- [RW-rec, (11)] for `|H| = 2`, and [RW26, Prop. 9, p. 14]. -/
theorem orderTwo_subgroup_card (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) (hh : h ≠ 0 ∧ h + h = 0) :
    Nat.card (AddSubgroup.zmultiples h) = 2 := by
  rw [Nat.card_zmultiples]
  exact addOrderOf_eq_prime (by simpa only [two_nsmul] using hh.2) hh.1

#print overlattice
#print subgroupLattice
#print project
#print cosetFibreEquiv
#check @pseudolatticeGroup_finite_card

end SICLean.L5.DistributionSubgroups
