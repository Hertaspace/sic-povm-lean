import SICLean.L5.OddPrimeUnits
import SICLean.L5.GoodReductionLocal
import SICLean.L5.OddPrimeSpecializationAux

set_option autoImplicit false

/-!
# Arbitrary finite primes and the existing downstream interfaces

[RW-rec, Thm. 5, p. 9]. [RW26, p. 2, p. 3, (2), (4)] give the actual-value dictionary.
The local-prime bridge itself comes from Mathlib adic valuations. An arbitrary embedding
of the finite model is allowed. The extension existence theorem is proved here. There is no
hypothesis of
unramifiedness, goodPrime, or global containment of all power periods in one finite
field.
-/

noncomputable section
open scoped Classical MatrixGroups

namespace SICLean.L5.OddPrimeSpecialization

open L3 OddPrimeValues

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- [RW-rec, Thm. 5, p. 9] for every fixed-embed algebraic preimage. [RW26, p. 2, (2)]; the
independent algebraicity statement is OddPrimeValues.value_isAlgebraic. -/
theorem odd_prime_any_preimage (P : PeriodData K) (I : StablePseudolattice P)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (x : PseudolatticeGroup P I) (a : Galois.Qbar)
    (ha : Galois.embed a = M72.value P I x) : v a = 0 := by
  rw [lift_of_embed P I x a ha]
  exact OddPrimeUnits.odd_prime_valuation_zero P I p hodd v hp x

/-- Existence of an actual finite model prevents an empty-preimage reading of the finite-prime
theorem. [RW-rec, Prop. 1, p. 3]; [RW26, Thm. 1, p. 3]. Only this fixed period/lattice's finite set
is placed in the field. -/
theorem exists_value_field (P : PeriodData K) (I : StablePseudolattice P) :
    ∃ F : IntermediateField ℚ Galois.Qbar,
      FiniteDimensional ℚ F ∧ ∀ x, lift P I x ∈ F := by
  let : Finite (PseudolatticeGroup P I) := (pseudolatticeGroup_finite_card P I).1
  let : Fintype (PseudolatticeGroup P I) := Fintype.ofFinite _
  let S : Finset Galois.Qbar := Finset.univ.image (lift P I)
  refine ⟨IntermediateField.adjoin ℚ (S : Set Galois.Qbar),
    IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a), ?_⟩
  intro x
  exact IntermediateField.subset_adjoin ℚ (S : Set Galois.Qbar)
    (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

/-- [RW-rec, Thm. 5, p. 9] at an arbitrary prime of an arbitrary finite model. No assumed extension
to Qbar remains. [RW26] inputs as in OddPrimeUnits. -/
theorem unitAt_of_embed (P : PeriodData K) (I : StablePseudolattice P)
    {L : Type*} [Field L] [NumberField L] (ι : L →ₐ[ℚ] Galois.Qbar)
    (Q : FinitePlace.Prime L) (hodd : FinitePlace.residueChar Q ≠ 2)
    (x : PseudolatticeGroup P I) (a : L)
    (ha : Galois.embed (ι a) = M72.value P I x) : FinitePlace.UnitAt Q a := by
  let : Fact (FinitePlace.residueChar Q).Prime := ⟨FinitePlace.residueChar_prime Q⟩
  obtain ⟨v, hp, hv⟩ := exists_valuation_extension Q ι
  change FinitePlace.valuation Q a = 0
  rw [← hv a]
  exact odd_prime_any_preimage P I (FinitePlace.residueChar Q) hodd v hp x (ι a) ha

/-- Every positive auxiliary period and every label in its larger group, not only labels from the
base group. [RW-rec, p. 4, p. 9, (8)]; [RW26, Prop. 8, p. 14]. -/
theorem power_unitAt_of_embed (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r)
    {L : Type*} [Field L] [NumberField L] (ι : L →ₐ[ℚ] Galois.Qbar)
    (Q : FinitePlace.Prime L) (hodd : FinitePlace.residueChar Q ≠ 2)
    (x : PseudolatticeGroup (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr))
    (a : L) (ha : Galois.embed (ι a) =
      M72.value (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr) x) :
    FinitePlace.UnitAt Q a := by
  exact unitAt_of_embed (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr)
    ι Q hodd x a ha

/-- The already defined U=E/e used in Frobenius/descent. [RW-rec, p. 4, p. 9, (12)]; [RW26, p. 3,
(4)] fixes e. No new normalization is introduced. -/
theorem normalized_unitAt_of_embed (P : PeriodData K) (I : StablePseudolattice P)
    {L : Type*} [Field L] [NumberField L] (ι : L →ₐ[ℚ] Galois.Qbar)
    (Q : FinitePlace.Prime L) (hodd : FinitePlace.residueChar Q ≠ 2)
    (x : PseudolatticeGroup P I) (a : L)
    (ha : Galois.embed (ι a) = DistributionNormalized.normalizedValue P I x) :
    FinitePlace.UnitAt Q a := by
  let : Fact (FinitePlace.residueChar Q).Prime := ⟨FinitePlace.residueChar_prime Q⟩
  obtain ⟨v, hp, hv⟩ := exists_valuation_extension Q ι
  have ha' : ι a = lift P I x / lift P I 0 := by
    apply Galois.embed.injective
    change Galois.embed (ι a) = Galois.embed (lift P I x / lift P I 0)
    rw [ha, map_div₀, embed_lift, embed_lift, M72.value_zero]
    rfl
  change FinitePlace.valuation Q a = 0
  rw [← hv a, ha', v.map_div,
    OddPrimeUnits.odd_prime_valuation_zero P I (FinitePlace.residueChar Q) hodd v hp x,
    zero_value_valuation P I v]
  simp

/-- Existing matrix point-value interface, including its origin. [RW-rec, Def. 1, Thm. 5]; [RW26, p.
2, (2)]. -/
theorem matrix_unitAt_of_embed (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    {L : Type*} [Field L] [NumberField L] (ι : L →ₐ[ℚ] Galois.Qbar)
    (Q : FinitePlace.Prime L) (hodd : FinitePlace.residueChar Q ≠ 2)
    (x : L4.SpecialValueGroup M) (a : L)
    (ha : Galois.embed (ι a) = L4.specialValuePlus M hM x) : FinitePlace.UnitAt Q a := by
  apply unitAt_of_embed (ActualField.periodData M hM) (ActualLattice.stableLattice M hM)
    ι Q hodd (ActualLattice.labelEquiv M hM x) a
  exact ha.trans (ActualValues.value_label M hM x).symm

/-- Exact matrix UnitValued output for LocalActualFourier. [RW-rec, Thm. 5] with finite-input
dictionary [RW26, p. 2, (2)]. No separate matrix lift is defined. -/
theorem matrix_unitValued (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1) :
    LocalFourierSetup.UnitValued v (FiniteAlgebraicTransport.value M hM) := by
  intro x
  rw [← lift_matrix M hM x]
  exact OddPrimeUnits.odd_prime_valuation_zero (ActualField.periodData M hM)
    (ActualLattice.stableLattice M hM) p hodd v hp (ActualLattice.labelEquiv M hM x)

/-- Dictionary between the two existing local APIs. -/
theorem integralAt_iff_goodReduction (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    (Q : FinitePlace.Prime F) (a : F) :
    FinitePlace.IntegralAt Q a ↔ GoodReductionLocal.localIntegral F Q a := by
  exact OddPrimeSpecializationAux.integralAt_iff_goodReduction F Q a

/-- Same local dictionary and provenance as the preceding statement. Unit, rather than merely
integral, is multiplicative valuation exactly 1. -/
theorem unitAt_iff_multiplicative_one (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    (Q : FinitePlace.Prime F) (a : F) :
    FinitePlace.UnitAt Q a ↔ Q.valuation F a = 1 := by
  exact OddPrimeSpecializationAux.unitAt_iff_multiplicative_one F Q a

/-- The two existing definitions specify the same rational prime. [RW-rec, p. 4]; Mathlib
integer-ideal quotient characteristic and norm. -/
theorem residueChar_eq_primeBelow (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    (Q : FinitePlace.Prime F) : FinitePlace.residueChar Q = GoodReductionLocal.primeBelow F Q := by
  exact OddPrimeSpecializationAux.residueChar_eq_primeBelow F Q

/-- Direct use without a goodPrime predicate. Both a and its inverse are locally integral at every
odd prime, including ramified primes. -/
theorem actual_value_localIntegral (P : PeriodData K) (I : StablePseudolattice P)
    (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    (Q : GoodReductionLocal.Prime F) (hodd : GoodReductionLocal.primeBelow F Q ≠ 2)
    (x : PseudolatticeGroup P I) (a : F)
    (ha : Galois.embed (a : Galois.Qbar) = M72.value P I x) :
    GoodReductionLocal.localIntegral F Q a ∧ GoodReductionLocal.localIntegral F Q a⁻¹ := by
  have hunit := unitAt_of_embed P I F.val Q
    (by simpa only [residueChar_eq_primeBelow F Q] using hodd) x a ha
  obtain ⟨_, hi, hinv⟩ := (FinitePlace.unitAt_iff_integral_inv Q a).mp hunit
  exact ⟨(integralAt_iff_goodReduction F Q a).mp hi,
    (integralAt_iff_goodReduction F Q a⁻¹).mp hinv⟩

/-- Same output for the existing normalized value U, including zero. [RW-rec, Thm. 5, p. 4, (12)]
used at Thm8; [RW26, p. 3, (4)]. -/
theorem normalized_value_localIntegral (P : PeriodData K) (I : StablePseudolattice P)
    (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    (Q : GoodReductionLocal.Prime F) (hodd : GoodReductionLocal.primeBelow F Q ≠ 2)
    (x : PseudolatticeGroup P I) (a : F)
    (ha : Galois.embed (a : Galois.Qbar) = DistributionNormalized.normalizedValue P I x) :
    GoodReductionLocal.localIntegral F Q a ∧ GoodReductionLocal.localIntegral F Q a⁻¹ := by
  have hunit := normalized_unitAt_of_embed P I F.val Q
    (by simpa only [residueChar_eq_primeBelow F Q] using hodd) x a ha
  obtain ⟨_, hi, hinv⟩ := (FinitePlace.unitAt_iff_integral_inv Q a).mp hunit
  exact ⟨(integralAt_iff_goodReduction F Q a).mp hi,
    (integralAt_iff_goodReduction F Q a⁻¹).mp hinv⟩

#check @FinitePlace.UnitAt
#check @GoodReductionLocal.localIntegral
#check @OddPrimeValues.exists_valuation_extension
#check @unitAt_of_embed
#check @power_unitAt_of_embed
#check @matrix_unitValued
#check @actual_value_localIntegral

end SICLean.L5.OddPrimeSpecialization
