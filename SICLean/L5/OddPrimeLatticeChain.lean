import SICLean.L5.OddPrimeTraceDual
import SICLean.L5.OddPrimeLatticeChainAux
import SICLean.L3.PseudolatticeIdeal
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-!
# The trace-dual lattice chain

[RW-rec, Lemma 3] The chain is defined by the actual submodules `M_i = a Z[epsilon] +
(epsilon - 1)^i I^vee`, `I_i = M_i^vee`. Neither the chain conclusions nor final
faithfulness are structure inputs. All adjacent maps reuse
`DistributionOrbitGeometry.periodProject`. [RW-rec, Lemma 2, Lemma 3, p. 8]. The
arithmetic chain works for every prime dividing N; oddness is not needed for this part
of the subsequent odd-prime valuation argument. The last faithfulness statement uses the
perfect trace-dual dictionary, not an assumption that a faithful character has already
been chosen.
-/

noncomputable section

open scoped Classical
open SICLean.L3

namespace SICLean.L5.OddPrimeLatticeChain

open OddPrimeTraceDual

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- [RW-rec, p. 8]: the actual principal `Z[epsilon]`-submodule `a Z[epsilon]`. -/
def principalOrder (P : PeriodData K) (a : K) : Submodule ℤ K :=
  pseudolatticeScale a (epsilonOrder P).toSubmodule

/-- [RW-rec, p. 8]: no chain property is included in the definition of `M_i`. -/
def chainModule (P : PeriodData K) (I : StablePseudolattice P) (a : K)
    (i : ℕ) : Submodule ℤ K :=
  principalOrder P a ⊔ pseudolatticeScale ((P.epsilon - 1) ^ i) (traceDual I.val)

/-- [RW-rec, p. 8]: dualize the specified `M_i`, using nonzero `a` only to prove that this concrete
submodule is a full stable lattice. -/
def chainLattice (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) : StablePseudolattice P :=
  ⟨traceDual (chainModule P I a.val i),
    traceDual_isLattice _ (OddPrimeLatticeChainAux.module_properties P I a ha i).1,
    traceDual_periodStable P
      ⟨chainModule P I a.val i,
        (OddPrimeLatticeChainAux.module_properties P I a ha i).1,
        (OddPrimeLatticeChainAux.module_properties P I a ha i).2.1⟩⟩

/-- [RW-rec, p. 8]: the same nonzero field element labels every stage. Its membership in the bidual
is a proof obligation. -/
def chainLabel (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) :
    traceDual (chainLattice P I a ha i).val :=
  ⟨a.val, by
    change a.val ∈ traceDual (traceDual (chainModule P I a.val i))
    rw [traceDual_traceDual (chainModule P I a.val i)
      (OddPrimeLatticeChainAux.module_properties P I a ha i).1]
    exact (OddPrimeLatticeChainAux.module_properties P I a ha i).2.2⟩

/-- [RW-rec, p. 8]: each character is the specified trace character of `a`. -/
def chainCharacter (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) :
    AddChar (PseudolatticeGroup P (chainLattice P I a ha i)) ℂ :=
  traceCharacter P (chainLattice P I a ha i) (chainLabel P I a ha i)

/-- [RW-rec, p. 8]: equality transport only, preserving group labels. This is not another inclusion
projection. -/
def periodGroupTransport (P : PeriodData K) {I J : StablePseudolattice P}
    (h : I = J) : PseudolatticeGroup P I ≃+ PseudolatticeGroup P J :=
  Eq.ndrec (motive := fun J => PseudolatticeGroup P I ≃+ PseudolatticeGroup P J)
    (AddEquiv.refl _) h

/-- [RW-rec, p. 8]: the initial dual-side module is precisely `I^vee`. -/
theorem chainModule_zero (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) : chainModule P I a.val 0 = traceDual I.val := by
  unfold chainModule principalOrder
  rw [pow_zero, pseudolatticeScale_one, sup_eq_right]
  exact OddPrimeLatticeChainAux.principal_le P (dualLattice P I) a

/-- [RW-rec, p. 8]: both adjacent module inclusions are conclusions. -/
theorem chainModule_step (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (i : ℕ) :
    chainModule P I a.val (i + 1) ≤ chainModule P I a.val i ∧
      pseudolatticeScale (P.epsilon - 1) (chainModule P I a.val i) ≤
        chainModule P I a.val (i + 1) := by
  have hdelta := OddPrimeLatticeChainAux.delta_scale_le P _ (traceDual_periodStable P I)
  have hprincipal := pseudolatticeScale_periodStable P _
    (epsilonOrder_isStablePseudolattice P).2 a.val
  constructor
  · unfold chainModule
    refine sup_le le_sup_left ?_
    rw [pow_succ, pseudolatticeScale_mul]
    exact (OddPrimeLatticeChainAux.scale_mono _ hdelta).trans le_sup_right
  · unfold chainModule
    rw [OddPrimeLatticeChainAux.scale_sup]
    refine sup_le ?_ ?_
    · exact (OddPrimeLatticeChainAux.delta_scale_le P _ hprincipal).trans le_sup_left
    · rw [← pseudolatticeScale_mul, ← pow_succ']
      exact le_sup_right

/-- [RW-rec, p. 8]: every concrete module is full, stable, and contains `a`. No maximal-order
stability or invertibility is assumed. -/
theorem chainModule_isLattice_stable (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) :
    Submodule.IsLattice ℚ (chainModule P I a.val i) ∧
      PeriodStable P (chainModule P I a.val i) ∧ a.val ∈ chainModule P I a.val i := by
  exact OddPrimeLatticeChainAux.module_properties P I a ha i

/-- [RW-rec, p. 8]: biduality gives equality to the original lattice, not a homothety. -/
theorem chainLattice_zero (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) : chainLattice P I a ha 0 = I := by
  apply Subtype.ext
  change traceDual (chainModule P I a.val 0) = I.val
  rw [chainModule_zero, traceDual_traceDual _ I.property.1]

/-- [RW-rec, Lemma 2, p. 8]: these are precisely its two lattice hypotheses. -/
theorem chainLattice_step (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) :
    (chainLattice P I a ha i).val ≤ (chainLattice P I a ha (i + 1)).val ∧
      pseudolatticeScale (P.epsilon - 1) (chainLattice P I a ha (i + 1)).val ≤
        (chainLattice P I a ha i).val := by
  constructor
  · exact traceDual_antitone _ _ (chainModule_step P I a i).1
  · exact OddPrimeLatticeChainAux.dual_scaled_le _ _ _ (chainModule_step P I a i).2

/-- [RW-rec, p. 8]: the initial character is exactly the prescribed trace label, after transport by
the proved initial lattice equality. -/
theorem chainCharacter_start (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) :
    (chainCharacter P I a ha 0).compAddMonoidHom
        (periodGroupTransport P (chainLattice_zero P I a ha)).symm.toAddMonoidHom =
      traceCharacter P I a := by
  exact OddPrimeLatticeChainAux.traceCharacter_transport P
    (chainLattice_zero P I a ha) (chainLabel P I a ha 0) a rfl

/-- [RW-rec, p. 8]: compatibility uses the existing representative-preserving map. -/
theorem chainCharacter_compatible (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) :
    (chainCharacter P I a ha (i + 1)).compAddMonoidHom
        (DistributionOrbitGeometry.periodProject P
          (chainLattice P I a ha i) (chainLattice P I a ha (i + 1))
          (chainLattice_step P I a ha i).1) =
      chainCharacter P I a ha i := by
  exact traceCharacter_project P _ _ (chainLattice_step P I a ha i).1
    (chainLabel P I a ha (i + 1))

/-- [RW-rec, Lemma 2, p. 8]: triviality is on the projection kernel, not injectivity of that
generally non-surjective map. -/
theorem chainCharacter_trivial_on_kernel (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ)
    (x : PseudolatticeGroup P (chainLattice P I a ha i))
    (hx : DistributionOrbitGeometry.periodProject P
      (chainLattice P I a ha i) (chainLattice P I a ha (i + 1))
      (chainLattice_step P I a ha i).1 x = 0) :
    chainCharacter P I a ha i x = 1 := by
  exact traceCharacter_trivial_on_projectionKernel P _ _ (chainLattice_step P I a ha i).1
    (chainLabel P I a ha (i + 1)) x hx

/-- [RW-rec, p. 8]: the actual additive quotient `M/a Z[epsilon]`. -/
abbrev PrincipalResidue (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) :=
  traceDual I.val ⧸ (principalOrder P a.val).toAddSubgroup.addSubgroupOf
    (traceDual I.val).toAddSubgroup

/-- [RW-rec, p. 8]: finiteness follows from the nonzero actual representative. -/
theorem principalResidue_finite (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) : Finite (PrincipalResidue P I a) := by
  exact DistributionOrbitGeometryAux.lattice_quotient_finite _ _
    (pseudolatticeScale_isLattice _ (epsilonOrder_isStablePseudolattice P).1 a.val ha)
    (traceDual_isLattice _ I.property.1)
    (OddPrimeLatticeChainAux.principal_le P (dualLattice P I) a)

/-- [RW-rec, p. 8]: equality of the two images in `K/a Z[epsilon]` is the precise quotient meaning
of `M_(2j)/a Z[epsilon] = N^j M/a Z[epsilon]`. -/
theorem chainModule_even_quotient (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (j : ℕ) :
    (chainModule P I a.val (2 * j)).toAddSubgroup.map
        (QuotientAddGroup.mk' (principalOrder P a.val).toAddSubgroup) =
      (pseudolatticeScale ((P.N : K) ^ j) (traceDual I.val)).toAddSubgroup.map
        (QuotientAddGroup.mk' (principalOrder P a.val).toAddSubgroup) := by
  unfold chainModule
  rw [OddPrimeLatticeChainAux.even_scale P _ (traceDual_periodStable P I)]
  rw [Submodule.sup_toAddSubgroup]
  rw [AddSubgroup.map_sup]
  have hz : (principalOrder P a.val).toAddSubgroup.map
      (QuotientAddGroup.mk' (principalOrder P a.val).toAddSubgroup) = ⊥ := by
    rw [AddSubgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientAddGroup.ker_mk' _).symm
  rw [hz, bot_sup_eq]

/-- [RW-rec, p. 8]: a power of N kills the finite quotient's primary component; the resulting
even-stage index is prime to p, uniformly for all later powers. -/
theorem chainModule_eventual_primeTo (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (p : ℕ) (hp : p.Prime) (hpN : p ∣ P.N) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      (∀ x : AddCommGroup.primaryComponent (PrincipalResidue P I a) p,
        P.N ^ j • (x.val : PrincipalResidue P I a) = 0) ∧
      ¬ p ∣ DistributionOrbitGeometry.inclusionIndex (principalOrder P a.val)
        (chainModule P I a.val (2 * j)) := by
  letI : Finite (PrincipalResidue P I a) := principalResidue_finite P I a ha
  obtain ⟨j₀, hj₀⟩ := OddPrimeLatticeChainAux.finite_eventual_primeTo_nsmul_range
    (PrincipalResidue P I a) hp hpN
  refine ⟨j₀, fun j hj => ⟨(hj₀ j hj).1, ?_⟩⟩
  have hcard : DistributionOrbitGeometry.inclusionIndex (principalOrder P a.val)
      (chainModule P I a.val (2 * j)) =
        Nat.card (nsmulAddMonoidHom (α := PrincipalResidue P I a) (P.N ^ j)).range := by
    calc
      _ = Nat.card ((chainModule P I a.val (2 * j)).toAddSubgroup.map
          (QuotientAddGroup.mk' (principalOrder P a.val).toAddSubgroup)) :=
        OddPrimeLatticeChainAux.relIndex_eq_card_map _ _
      _ = Nat.card ((pseudolatticeScale ((P.N : K) ^ j) (traceDual I.val)).toAddSubgroup.map
          (QuotientAddGroup.mk' (principalOrder P a.val).toAddSubgroup)) := by
        rw [chainModule_even_quotient]
      _ = _ := by
        simpa only [Nat.cast_pow] using
          (OddPrimeLatticeChainAux.relative_nsmul_range_card
            (principalOrder P a.val) (traceDual I.val) (P.N ^ j)).symm
  rw [hcard]
  exact (hj₀ j hj).2

/-- [RW-rec, p. 8]: the concrete order quotient `a Z[epsilon]/(epsilon - 1)a Z[epsilon]`. -/
abbrev OrderPeriodGroup (P : PeriodData K) (a : K) :=
  principalOrder P a ⧸
    (pseudolatticeScale (P.epsilon - 1) (principalOrder P a)).toAddSubgroup.addSubgroupOf
      (principalOrder P a).toAddSubgroup

/-- [RW-rec, p. 8]: the distinguished class is the class of the field element `a`. -/
def orderGenerator (P : PeriodData K) (a : K) : OrderPeriodGroup P a :=
  QuotientAddGroup.mk (⟨a, OddPrimeLatticeChainAux.mem_principal P a⟩ : principalOrder P a)

/-- [RW-rec, p. 8]: an actual additive equivalence sends `[a]` to `1 mod N`. -/
theorem orderPeriodGroup_equiv_zmod (P : PeriodData K) (a : K) (ha : a ≠ 0) :
    ∃ e : OrderPeriodGroup P a ≃+ ZMod P.N, e (orderGenerator P a) = 1 := by
  exact OddPrimeLatticeChainAux.orderPeriodGroup_equiv_zmod_proof P a ha

/-- [RW-rec, p. 8]: inclusion of principal-order trace labels into the bidual of `I_i`. -/
def principalLabelInclusion (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) :
    principalOrder P a.val →+ traceDual (chainLattice P I a ha i).val where
  toFun := fun b => ⟨b.val, by
    change b.val ∈ traceDual (traceDual (chainModule P I a.val i))
    rw [traceDual_traceDual _ (chainModule_isLattice_stable P I a ha i).1]
    exact (show principalOrder P a.val ≤ chainModule P I a.val i from le_sup_left) b.property⟩
  map_zero' := by rfl
  map_add' := by intros; rfl

/-- [RW-rec, p. 8]: the displayed inclusion descends to the two relation quotients. -/
def orderToChainDual (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) :
    OrderPeriodGroup P a.val →+ DualPeriodGroup P (chainLattice P I a ha i) :=
  QuotientAddGroup.map _ _ (principalLabelInclusion P I a ha i) (by
    intro x hx
    change x.val ∈ pseudolatticeScale (P.epsilon - 1) (principalOrder P a.val) at hx
    change x.val ∈ pseudolatticeScale (P.epsilon - 1)
      (traceDual (traceDual (chainModule P I a.val i)))
    rw [traceDual_traceDual _ (chainModule_isLattice_stable P I a ha i).1]
    exact OddPrimeLatticeChainAux.scale_mono _ le_sup_left hx)

/-- [RW-rec, p. 8]: restriction of the specified inclusion to Mathlib primary components. -/
def primaryComparison (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i p : ℕ) :
    AddCommGroup.primaryComponent (OrderPeriodGroup P a.val) p →+
      AddCommGroup.primaryComponent (DualPeriodGroup P (chainLattice P I a ha i)) p where
  toFun := fun x => ⟨orderToChainDual P I a ha i x.val, by
    obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.mp x.property
    exact AddCommGroup.mem_primaryComponent.mpr
      ⟨n, by rw [← map_nsmul, hn, map_zero]⟩⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' := by intros; apply Subtype.ext; exact map_add _ _ _

/-- [RW-rec, p. 8]: a prime-to-p index makes the canonical primary comparison bijective. -/
theorem primaryComparison_bijective (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i p : ℕ) (hp : p.Prime)
    (hq : ¬ p ∣ DistributionOrbitGeometry.inclusionIndex
      (principalOrder P a.val) (chainModule P I a.val i)) :
    Function.Bijective (primaryComparison P I a ha i p) := by
  have hdual : traceDual (chainLattice P I a ha i).val = chainModule P I a.val i :=
    traceDual_traceDual _ (chainModule_isLattice_stable P I a ha i).1
  have hle : principalOrder P a.val ≤ traceDual (chainLattice P I a ha i).val := by
    rw [hdual]
    exact le_sup_left
  have hq' : ¬p ∣ DistributionOrbitGeometry.inclusionIndex (principalOrder P a.val)
      (traceDual (chainLattice P I a ha i).val) := by
    rwa [hdual]
  change Function.Bijective (OddPrimeLatticeChainAux.primaryMap (orderToChainDual P I a ha i) p)
  exact OddPrimeLatticeChainAux.latticePeriod_primary_bijective _ _ hle _
    (orderToChainDual P I a ha i) (fun _ => rfl) hp hq'

/-- [RW-rec, p. 8]: generation of the primary trace dual is stated before its perfect-pairing
consequence, namely faithfulness on the nontrivial cyclic primary group. -/
theorem chain_final_primary (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (p : ℕ) (hp : p.Prime) (hpN : p ∣ P.N) :
    ∃ j : ℕ,
      (¬ p ∣ Nat.card (DualPeriodGroup P (chainLattice P I a ha (2 * j)) ⧸
        AddSubgroup.zmultiples
          (QuotientAddGroup.mk (chainLabel P I a ha (2 * j)) :
            DualPeriodGroup P (chainLattice P I a ha (2 * j))))) ∧
      IsAddCyclic (AddCommGroup.primaryComponent
        (PseudolatticeGroup P (chainLattice P I a ha (2 * j))) p) ∧
      Nontrivial (AddCommGroup.primaryComponent
        (PseudolatticeGroup P (chainLattice P I a ha (2 * j))) p) ∧
      Function.Injective
        (fun x : AddCommGroup.primaryComponent
          (PseudolatticeGroup P (chainLattice P I a ha (2 * j))) p =>
            chainCharacter P I a ha (2 * j) x.val) := by
  obtain ⟨j, hj⟩ := chainModule_eventual_primeTo P I a ha p hp hpN
  let J := chainLattice P I a ha (2 * j)
  letI : Finite (PseudolatticeGroup P J) := (pseudolatticeGroup_finite_card P J).1
  letI : Finite (DualPeriodGroup P J) :=
    Finite.of_injective (traceCharacterEquiv P J) (traceCharacterEquiv P J).injective
  have hgen : AddSubgroup.zmultiples (orderGenerator P a.val) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn⟩ := OddPrimeLatticeChainAux.generatorHom_surjective P a.val x
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, hn⟩
  have hquot : ¬p ∣ Nat.card (DualPeriodGroup P J ⧸
      AddSubgroup.zmultiples (QuotientAddGroup.mk (chainLabel P I a ha (2 * j)) :
        DualPeriodGroup P J)) :=
    OddPrimeLatticeChainAux.not_dvd_card_quotient_zmultiples_of_primaryMap_surjective
      (orderToChainDual P I a ha (2 * j)) hp (orderGenerator P a.val) hgen
      (primaryComparison_bijective P I a ha (2 * j) p hp (hj j le_rfl).2).2
  have hfaithful : Function.Injective
      (fun x : AddCommGroup.primaryComponent (PseudolatticeGroup P J) p =>
        chainCharacter P I a ha (2 * j) x.val) :=
    (primary_faithful_iff_dual_quotient_primeTo P J p hp
      (chainLabel P I a ha (2 * j))).mpr hquot
  refine ⟨j, hquot, ?_, ?_, hfaithful⟩
  · exact OddPrimeLatticeChainAux.isAddCyclic_of_faithful_complex_character
      ((chainCharacter P I a ha (2 * j)).compAddMonoidHom
        (AddCommGroup.primaryComponent (PseudolatticeGroup P J) p).subtype) hfaithful
  · apply OddPrimeLatticeChainAux.primaryComponent_nontrivial_of_prime_dvd_card p hp
    rwa [(pseudolatticeGroup_finite_card P J).2]

/-- The kernel condition of [RW-rec, Lemma 3, Lemma 2, p. 8], made explicit. The start is equal to I
and theta after equality transport; every adjacent map is the existing natural projection. The
terminal primary component is nontrivial, cyclic, and the final character is injective on it. -/
theorem lemma3 (P : PeriodData K) (I : StablePseudolattice P)
    (theta : AddChar (PseudolatticeGroup P I) ℂ)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ P.N) :
    ∃ r : ℕ, ∃ lattices : Fin (r + 1) → StablePseudolattice P,
      ∃ characters : ∀ i : Fin (r + 1), AddChar (PseudolatticeGroup P (lattices i)) ℂ,
      ∃ hzero : lattices 0 = I,
        (characters 0).compAddMonoidHom
            (periodGroupTransport P hzero).symm.toAddMonoidHom = theta ∧
        (∀ i : Fin r,
          ∃ hstep : (lattices i.castSucc).val ≤ (lattices i.succ).val,
            pseudolatticeScale (P.epsilon - 1) (lattices i.succ).val ≤
              (lattices i.castSucc).val ∧
            (characters i.succ).compAddMonoidHom
                (DistributionOrbitGeometry.periodProject P
                  (lattices i.castSucc) (lattices i.succ) hstep) = characters i.castSucc ∧
            ∀ x : PseudolatticeGroup P (lattices i.castSucc),
              DistributionOrbitGeometry.periodProject P
                  (lattices i.castSucc) (lattices i.succ) hstep x = 0 →
                characters i.castSucc x = 1) ∧
        IsAddCyclic (AddCommGroup.primaryComponent
          (PseudolatticeGroup P (lattices (Fin.last r))) p) ∧
        Nontrivial (AddCommGroup.primaryComponent
          (PseudolatticeGroup P (lattices (Fin.last r))) p) ∧
        Function.Injective
          (fun x : AddCommGroup.primaryComponent
            (PseudolatticeGroup P (lattices (Fin.last r))) p =>
              characters (Fin.last r) x.val) := by
  obtain ⟨a, ha, htheta⟩ := exists_nonzero_characterRepresentative P I theta
  obtain ⟨j, _, hcyclic, hnontrivial, hfaithful⟩ := chain_final_primary P I a ha p hp hpN
  refine ⟨2 * j, fun i => chainLattice P I a ha i.val,
    fun i => chainCharacter P I a ha i.val, chainLattice_zero P I a ha, ?_, ?_,
    hcyclic, hnontrivial, hfaithful⟩
  · exact (chainCharacter_start P I a ha).trans htheta
  · intro i
    exact ⟨(chainLattice_step P I a ha i.val).1,
      (chainLattice_step P I a ha i.val).2,
      chainCharacter_compatible P I a ha i.val,
      chainCharacter_trivial_on_kernel P I a ha i.val⟩

#check @DistributionOrbitGeometry.periodProject
#check @orderPeriodGroup_equiv_zmod
#check @lemma3
#print chainModule
#print chainCharacter

end SICLean.L5.OddPrimeLatticeChain
