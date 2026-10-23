import Mathlib

/-! Mathlib API and typeclass checks.
No theorem, axiom, or proof is declared in this file. -/

set_option autoImplicit false
set_option pp.universes false
set_option pp.proofs false

open scoped nonZeroDivisors NumberField

#check NumberField.RingOfIntegers.instFintypeClassGroup
#check ClassGroup.fintypeOfAdmissibleOfFinite
#print ClassGroup
#check ClassGroup.mk
#check ClassGroup.induction
#check ClassGroup.mk_eq_mk
#check ClassGroup.equiv
#check ClassGroup.mk0_surjective
#check ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring
#check FractionalIdeal.mk0
#check FractionalIdeal.isFractional_of_fg
#check FractionalIdeal.fg_of_isNoetherianRing
#check FractionalIdeal.equivNumOfIsLocalization
#check FractionalIdeal.semifield
#check FractionalIdeal.spanSingleton_mul_spanSingleton
#check FractionalIdeal.eq_spanSingleton_mul
#check conductor
#check mem_conductor_iff
#check conductor_subset_adjoin
#check RingOfIntegers.exponent
#check RingOfIntegers.exponent_eq_sInf
#check Submodule.IsLattice
#print Submodule.IsLattice
#check Submodule.IsLattice.finite
#check Submodule.IsLattice.free
#check Submodule.IsLattice.rank'
#check Submodule.IsLattice.smul
#check Submodule.IsLattice.of_le_of_isLattice_of_fg
#check Submodule.span_span_of_tower
#check Submodule.FG.span
#check Submodule.fg_span
#check Submodule.FG.restrictScalars
#check Submodule.finiteQuotientOfFreeOfRankEq
#check Submodule.finiteQuotient_iff
#check Submodule.quotientEquivPiZMod
#check Submodule.comapMkQRelIso
#check Submodule.comapMkQOrderEmbedding
#check Submodule.subtype
#check Submodule.comap
#check AddSubgroup.toIntSubmodule
#check Submodule.toAddSubgroup
#check Submodule.smul_mem_pointwise_smul
#check Submodule.mem_smul_pointwise_iff_exists
#check Finite.of_injective
#check Finite.of_surjective
#check Fintype.ofFinite
#check NumberField.RingOfIntegers.rank
#check NumberField.fractionalIdealBasis
#check NumberField.basisOfFractionalIdeal
#check NumberField.fractionalIdeal_rank
#check Module.Free.chooseBasis
#check Module.finrank_eq_card_chooseBasisIndex
#check Module.finrank_eq_rank
#check Module.finrank_eq_of_rank_eq
#check Module.finrank_eq_card_basis
#check LinearMap.mulLeft
#check LinearMap.mul'
#check Submodule.restrictScalars
#check Units.mk0
#check Submodule.map_span
#check Submodule.span_le
#check Submodule.span_le_restrictScalars
#check Submodule.span_singleton_mul
#check FractionalIdeal.coe_mul
#check FractionalIdeal.coe_mk
#check QuotientGroup.mk'_eq_mk'
#check ClassGroup.equiv_mk
#check AddSubgroup.nsmul_index_mem

section InstanceChecks

variable (K : Type*) [Field K] [NumberField K]

#synth IsDedekindDomain (𝓞 K)
#synth IsFractionRing (𝓞 K) K
#synth Module.Free ℤ (𝓞 K)
#synth Module.Finite ℤ (𝓞 K)
#synth Finite (ClassGroup (𝓞 K))
#synth Semifield (FractionalIdeal (𝓞 K)⁰ K)

variable (a : FractionalIdeal (𝓞 K)⁰ K)

#synth Module.Finite ℤ a
#synth Module.Free ℤ a

variable (I : Submodule ℤ K) (hI : I.FG)

#check (Submodule.span (𝓞 K) (I : Set K))
#check (hI.span : (Submodule.span (𝓞 K) (I : Set K)).FG)
#check (⟨Submodule.span (𝓞 K) (I : Set K),
  FractionalIdeal.isFractional_of_fg hI.span⟩ : FractionalIdeal (𝓞 K)⁰ K)
#check ((a : Submodule (𝓞 K) K).restrictScalars ℤ)
#check (LinearMap.mulLeft ℤ (1 : K) : K →ₗ[ℤ] K)
#check (Units.mk0 a : a ≠ 0 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)

variable (Q : Type*) [AddCommGroup Q] [Module ℤ Q] [Finite Q]

#synth Finite (Submodule ℤ Q)
#synth Finite (AddSubgroup Q)

end InstanceChecks
