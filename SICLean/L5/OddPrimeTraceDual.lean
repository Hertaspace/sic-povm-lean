import SICLean.L5.DistributionSubgroupLattice
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.Group.AddChar
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import SICLean.L5.OddPrimeTraceDualAux

set_option autoImplicit false

/-!
# Trace-dual characters of an arbitrary stable integer lattice

All maps retain their specified underlying functions. Auxiliary lattice, quotient and
finite-character arguments are in `OddPrimeTraceDualAux`. [RW-rec, Lemmas 2--3, p. 8].
The trace dual is Mathlib's `Submodule.traceDual ℤ ℚ`, for a full integer lattice,
without a maximal-order ideal assumption. The period group uses `epsilon⁻¹ - 1`.
Stability identifies its relation lattice with `(epsilon - 1)M`; neither this
identification nor the projection changes the field representative of a period point.
[RW26, Prop. 9, p. 3, p. 14, (3)]. Character cardinality comes from Mathlib's finite
abelian duality. No Fourier-averaging assertion is used here.
-/

noncomputable section

open scoped Classical
open SICLean.L3

namespace SICLean.L5.OddPrimeTraceDual

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- [RW-rec, p. 8]: the trace dual of a full integer lattice. -/
def traceDual (I : Submodule ℤ K) : Submodule ℤ K :=
  Submodule.traceDual ℤ ℚ I

/-- [RW-rec, p. 8]: integrality of all trace pairings, for an arbitrary lattice. -/
theorem mem_traceDual (I : Submodule ℤ K) (a : K) :
    a ∈ traceDual I ↔
      ∀ x ∈ I, Algebra.trace ℚ K (a * x) ∈ (algebraMap ℤ ℚ).range := by
  exact Submodule.mem_traceDual

/-- [RW-rec, p. 8]: the trace dual is again a full integer lattice. -/
theorem traceDual_isLattice (I : Submodule ℤ K) (hI : Submodule.IsLattice ℚ I) :
    Submodule.IsLattice ℚ (traceDual I) := by
  exact OddPrimeTraceDualAux.traceDual_isLattice I hI

/-- [RW-rec, p. 8]: full integer lattices equal their trace bidual. -/
theorem traceDual_traceDual (I : Submodule ℤ K) (hI : Submodule.IsLattice ℚ I) :
    traceDual (traceDual I) = I := by
  exact OddPrimeTraceDualAux.traceDual_traceDual I hI

/-- [RW-rec, p. 8]: dualization reverses inclusion. -/
theorem traceDual_antitone (I J : Submodule ℤ K) (hIJ : I ≤ J) :
    traceDual J ≤ traceDual I := by
  intro a ha
  exact (mem_traceDual I a).mpr (fun x hx => (mem_traceDual J a).mp ha x (hIJ hx))

/-- [RW-rec, p. 8]: period stability passes to the trace dual. -/
theorem traceDual_periodStable (P : PeriodData K) (I : StablePseudolattice P) :
    PeriodStable P (traceDual I.val) := by
  have hscale : pseudolatticeScale P.epsilon⁻¹ (traceDual I.val) = traceDual I.val := by
    change pseudolatticeScale P.epsilon⁻¹ (Submodule.traceDual ℤ ℚ I.val) =
      Submodule.traceDual ℤ ℚ I.val
    rw [← OddPrimeTraceDualAux.traceDual_scale I.val P.epsilon P.epsilon_ne_zero,
      I.property.2]
  calc
    pseudolatticeScale P.epsilon (traceDual I.val) =
        pseudolatticeScale P.epsilon
          (pseudolatticeScale P.epsilon⁻¹ (traceDual I.val)) :=
      congrArg (pseudolatticeScale P.epsilon) hscale.symm
    _ = traceDual I.val := (pseudolatticeScale_inv P.epsilon P.epsilon_ne_zero _).2

/-- [RW-rec, p. 8]: the actual stable trace-dual lattice. -/
def dualLattice (P : PeriodData K) (I : StablePseudolattice P) :
    StablePseudolattice P :=
  ⟨traceDual I.val, traceDual_isLattice I.val I.property.1, traceDual_periodStable P I⟩

/-- [RW-rec, p. 8]: the reversed dual inclusion has the same index. -/
theorem traceDual_index (I J : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (hJ : Submodule.IsLattice ℚ J) (hIJ : I ≤ J) :
    DistributionOrbitGeometry.inclusionIndex (traceDual J) (traceDual I) =
      DistributionOrbitGeometry.inclusionIndex I J := by
  exact OddPrimeTraceDualAux.traceDual_index I J hI hJ hIJ

/-- [RW-rec, p. 8] with the convention from [RW-rec, p. 3]. -/
theorem periodRelation_eq_inverse (P : PeriodData K) (I : StablePseudolattice P) :
    pseudolatticeScale (P.epsilon - 1) (traceDual I.val) =
      pseudolatticeScale (P.epsilon⁻¹ - 1) (traceDual I.val) := by
  exact OddPrimeTraceDualAux.scale_period_relation P _ (traceDual_periodStable P I)

/-- [RW-rec, p. 8]: the specified complex trace exponential. -/
def traceExponential (a x : K) : ℂ :=
  L4.e ((Algebra.trace ℚ K (a * x) : ℚ) : ℂ)

/-- [RW-rec, p. 8]: the underlying function evaluates at a field representative. The proof fields
must establish independence of `Quotient.out`. -/
def traceCharacter (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) : AddChar (PseudolatticeGroup P I) ℂ where
  toFun := fun x => traceExponential a.val (pseudolatticeRepresentative P I x)
  map_zero_eq_one' := by
    have h := OddPrimeTraceDualAux.phase_representative P I a 0
      (pseudolatticePeriodPoints P I).zero_mem
    rw [DistributionSubgroupLatticeAux.mk_zero] at h
    exact h.trans (OddPrimeTraceDualAux.phase_zero_right a.val)
  map_add_eq_mul' := by
    intro x y
    have h := OddPrimeTraceDualAux.phase_representative P I a
      (pseudolatticeRepresentative P I x + pseudolatticeRepresentative P I y)
      ((pseudolatticePeriodPoints P I).add_mem
        (Quotient.out x).property (Quotient.out y).property)
    have hmk : pseudolatticeMk P I
        (pseudolatticeRepresentative P I x + pseudolatticeRepresentative P I y)
        ((pseudolatticePeriodPoints P I).add_mem
          (Quotient.out x).property (Quotient.out y).property) = x + y :=
      congrArg₂ (fun z w : PseudolatticeGroup P I => z + w)
        (Quotient.out_eq x) (Quotient.out_eq y)
    rw [hmk] at h
    exact h.trans (OddPrimeTraceDualAux.phase_add_right _ _ _)

/-- [RW-rec, p. 8]: the character formula is valid for every representative, including zero, in the
actual inverse-period convention. -/
theorem traceCharacter_mk (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    traceCharacter P I a (pseudolatticeMk P I x hx) = traceExponential a.val x := by
  exact OddPrimeTraceDualAux.phase_representative P I a x hx

/-- [RW-rec, p. 8]: addition of trace labels is multiplication of character values. `AddChar`
already has its additive group structure; no new character type is used. -/
def traceCharacterHom (P : PeriodData K) (I : StablePseudolattice P) :
    traceDual I.val →+ AddChar (PseudolatticeGroup P I) ℂ where
  toFun := traceCharacter P I
  map_zero' := by
    ext x
    exact OddPrimeTraceDualAux.phase_zero_left _
  map_add' := by
    intro a b
    ext x
    exact OddPrimeTraceDualAux.phase_add_left _ _ _

/-- [RW-rec, p. 8]: the literal subgroup `(epsilon - 1)M` inside `M`. -/
def periodRelations (P : PeriodData K) (I : StablePseudolattice P) :
    AddSubgroup (traceDual I.val) :=
  (pseudolatticeScale (P.epsilon - 1) (traceDual I.val)).toAddSubgroup.comap
    (traceDual I.val).toAddSubgroup.subtype

/-- [RW-rec, p. 8]: exactly the displayed relation subgroup is the character kernel. -/
theorem traceCharacterHom_ker (P : PeriodData K) (I : StablePseudolattice P) :
    (traceCharacterHom P I).ker = periodRelations P I := by
  ext a
  change traceCharacter P I a = 0 ↔
    a.val ∈ pseudolatticeScale (P.epsilon - 1) (Submodule.traceDual ℤ ℚ I.val)
  rw [← OddPrimeTraceDualAux.trace_integral_on_periodPoints_iff P I a.val]
  constructor
  · intro h x hx
    apply (OddPrimeTraceDualAux.phase_eq_one_iff _ _).mp
    change traceExponential a.val x = 1
    rw [← traceCharacter_mk P I a x hx, h]
    rfl
  · intro h
    ext x
    exact (OddPrimeTraceDualAux.phase_eq_one_iff _ _).mpr
      (h _ (Quotient.out x).property)

/-- [RW-rec, p. 8]: the concrete trace-label quotient `M/(epsilon - 1)M`. -/
abbrev DualPeriodGroup (P : PeriodData K) (I : StablePseudolattice P) :=
  traceDual I.val ⧸ periodRelations P I

/-- [RW-rec, p. 8]: descend the specified trace homomorphism to its relation quotient. -/
def traceQuotientCharacterHom (P : PeriodData K) (I : StablePseudolattice P) :
    DualPeriodGroup P I →+ AddChar (PseudolatticeGroup P I) ℂ :=
  QuotientAddGroup.lift (periodRelations P I) (traceCharacterHom P I)
    (traceCharacterHom_ker P I ▸ le_rfl)

/-- [RW-rec, p. 8]: the trace pairing is perfect on the actual finite quotient. -/
theorem traceQuotientCharacterHom_bijective (P : PeriodData K)
    (I : StablePseudolattice P) : Function.Bijective (traceQuotientCharacterHom P I) := by
  obtain ⟨hfinite, hcard⟩ := OddPrimeTraceDualAux.periodCokernel_finite_card P (dualLattice P I)
  have : Finite (DualPeriodGroup P I) := hfinite
  have : Finite (PseudolatticeGroup P I) := (pseudolatticeGroup_finite_card P I).1
  apply OddPrimeTraceDualAux.characterHom_bijective_of_injective_of_card
  · apply (QuotientAddGroup.injective_lift_iff (periodRelations P I)
      (traceCharacterHom P I) _).mpr
    exact (traceCharacterHom_ker P I).symm
  · exact hcard.trans (pseudolatticeGroup_finite_card P I).2.symm

/-- [RW-rec, p. 8]: the additive equivalence has the preceding quotient map as its function. -/
def traceCharacterEquiv (P : PeriodData K) (I : StablePseudolattice P) :
    DualPeriodGroup P I ≃+ AddChar (PseudolatticeGroup P I) ℂ :=
  AddEquiv.ofBijective (traceQuotientCharacterHom P I)
    (traceQuotientCharacterHom_bijective P I)

/-- [RW-rec, p. 8]: the dictionary sends the class of `a` to its specified trace character. -/
theorem traceCharacterEquiv_mk (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) :
    traceCharacterEquiv P I (QuotientAddGroup.mk a) = traceCharacter P I a := by
  rfl

/-- [RW-rec, p. 8]: a nonzero label exists even for the trivial character. In that case a nonzero
element of `(epsilon - 1)M` is required. -/
theorem exists_nonzero_characterRepresentative (P : PeriodData K)
    (I : StablePseudolattice P) (theta : AddChar (PseudolatticeGroup P I) ℂ) :
    ∃ a : traceDual I.val, a.val ≠ 0 ∧ traceCharacter P I a = theta := by
  have hsurj : Function.Surjective (traceCharacterHom P I) := by
    intro theta'
    obtain ⟨q, hq⟩ := (traceQuotientCharacterHom_bijective P I).2 theta'
    refine ⟨Quotient.out q, ?_⟩
    change traceQuotientCharacterHom P I
      (QuotientAddGroup.mk (Quotient.out q)) = theta'
    simpa only [Quotient.out_eq] using hq
  have hker : ∃ a : traceDual I.val, a ≠ 0 ∧ traceCharacterHom P I a = 0 := by
    obtain ⟨a, ha, hrel⟩ := OddPrimeTraceDualAux.exists_nonzero_period_relation P
      (traceDual I.val) (traceDual_isLattice I.val I.property.1)
      (traceDual_periodStable P I)
    refine ⟨a, ?_, ?_⟩
    · intro h
      exact ha (congrArg Subtype.val h)
    · change a ∈ (traceCharacterHom P I).ker
      rw [traceCharacterHom_ker]
      exact hrel
  obtain ⟨a, ha, htheta⟩ := OddPrimeTraceDualAux.exists_nonzero_preimage
    (traceCharacterHom P I) hsurj hker theta
  exact ⟨a, fun h => ha (Subtype.ext h), htheta⟩

/-- [RW-rec, p. 8]: a common trace label is compatible with the existing natural map. -/
theorem traceCharacter_project (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (a : traceDual J.val) :
    (traceCharacter P J a).compAddMonoidHom
        (DistributionOrbitGeometry.periodProject P I J hIJ) =
      traceCharacter P I ⟨a.val, traceDual_antitone I.val J.val hIJ a.property⟩ := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    change traceCharacter P J a
      (pseudolatticeMk P J x.val
        (DistributionOrbitGeometry.periodPoints_mono P I J hIJ x.property)) =
      traceCharacter P I ⟨a.val, traceDual_antitone I.val J.val hIJ a.property⟩
        (pseudolatticeMk P I x.val x.property)
    rw [traceCharacter_mk, traceCharacter_mk]

/-- [RW-rec, Lemma 2, p. 8]: the source character is trivial on the kernel. -/
theorem traceCharacter_trivial_on_projectionKernel (P : PeriodData K)
    (I J : StablePseudolattice P) (hIJ : I.val ≤ J.val) (a : traceDual J.val)
    (x : PseudolatticeGroup P I)
    (hx : DistributionOrbitGeometry.periodProject P I J hIJ x = 0) :
    traceCharacter P I ⟨a.val, traceDual_antitone I.val J.val hIJ a.property⟩ x = 1 := by
  have h := congrArg (fun f : AddChar (PseudolatticeGroup P I) ℂ => f x)
    (traceCharacter_project P I J hIJ a)
  change traceCharacter P J a
    (DistributionOrbitGeometry.periodProject P I J hIJ x) = _ at h
  rw [hx, AddChar.map_zero_eq_one] at h
  exact h.symm

/-- [RW-rec, p. 8]: perfect duality converts generation of the primary dual into faithfulness,
expressed without choosing a primary projection of the label. -/
theorem primary_faithful_iff_dual_quotient_primeTo (P : PeriodData K)
    (I : StablePseudolattice P) (p : ℕ) (hp : p.Prime) (a : traceDual I.val) :
    Function.Injective
        (fun x : AddCommGroup.primaryComponent (PseudolatticeGroup P I) p =>
          traceCharacter P I a x.val) ↔
      ¬ p ∣ Nat.card (DualPeriodGroup P I ⧸
        AddSubgroup.zmultiples (QuotientAddGroup.mk a : DualPeriodGroup P I)) := by
  have : Finite (PseudolatticeGroup P I) := (pseudolatticeGroup_finite_card P I).1
  have : Finite (DualPeriodGroup P I) :=
    (OddPrimeTraceDualAux.periodCokernel_finite_card P (dualLattice P I)).1
  exact OddPrimeTraceDualAux.primary_faithful_iff_dual_quotient_primeTo
    (traceCharacterEquiv P I) (QuotientAddGroup.mk a) p hp

#check @Submodule.traceDual
#check @AddCommGroup.primaryComponent
#check @traceCharacterEquiv
#check @primary_faithful_iff_dual_quotient_primeTo
#print traceExponential
#print periodRelations

end SICLean.L5.OddPrimeTraceDual
