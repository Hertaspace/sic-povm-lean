import SICLean.L5.PrimeTower
import SICLean.Galois.AlgebraicClosure

set_option autoImplicit false

/-!
# One finite subfield and one compatible prime for a finite algebraic family

Built with Mathlib `FieldTheory/IntermediateField/Adjoin/{Defs,Basic}.lean`, adjoin and
`finiteDimensional_adjoin`, `finiteDimensional_sup`;
`NumberTheory/NumberField/Basic.lean`, `NumberField.of_module_finite`, together with a
maximal ideal lying over the prescribed prime. [RW-rec, Prop. 4, p. 14] with the finite-model
formulation of [RW-rec, p.
4]. The field is the ordinary explicit adjoin in the fixed Qbar. This is not a normal
closure, and it is never the field of all values at all positive-power periods. For a
finite enlargement, a prescribed lower prime is retained; new subfield primes should be
its contractions, not unrelated choices made separately for each label.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open NumberField

/-- A concrete common field for finitely many algebraic numbers. -/
def generatedField (s : Finset Galois.Qbar) : IntermediateField ℚ Galois.Qbar :=
  IntermediateField.adjoin ℚ (s : Set Galois.Qbar)

/-- This explicit adjoin is finite dimensional over ℚ. -/
theorem generatedField_finiteDimensional (s : Finset Galois.Qbar) :
    FiniteDimensional ℚ (generatedField s) := by
  exact IntermediateField.finiteDimensional_adjoin fun a _ =>
    Algebra.IsIntegral.isIntegral a

attribute [instance] generatedField_finiteDimensional

instance generatedField_numberField (s : Finset Galois.Qbar) : NumberField (generatedField s) :=
  NumberField.of_module_finite ℚ (generatedField s)

/-- All supplied numbers lie in the same field. -/
theorem generator_mem (s : Finset Galois.Qbar) (a : Galois.Qbar) (ha : a ∈ s) :
    a ∈ generatedField s := by
  exact IntermediateField.subset_adjoin ℚ (s : Set Galois.Qbar) ha

/-- Increasing the finite algebraic list increases its adjoin. -/
theorem generatedField_mono {s t : Finset Galois.Qbar} (h : s ⊆ t) :
    generatedField s ≤ generatedField t := by
  exact IntermediateField.adjoin.mono ℚ (s : Set Galois.Qbar) (t : Set Galois.Qbar) h

/-- Finite auxiliary lists combine by an actual field compositum. -/
theorem generatedField_union (s t : Finset Galois.Qbar) :
    generatedField (s ∪ t) = generatedField s ⊔ generatedField t := by
  classical
  simp only [generatedField, Finset.coe_union, IntermediateField.adjoin_union]

/-- A generator as an actual element of the finite field, not an unrelated model element. -/
def fieldElement (s : Finset Galois.Qbar) (a : Galois.Qbar) (ha : a ∈ s) : generatedField s :=
  ⟨a, generator_mem s a ha⟩

/-- Coercion returns the original algebraic number. -/
theorem fieldElement_coe (s : Finset Galois.Qbar) (a : Galois.Qbar) (ha : a ∈ s) :
    (fieldElement s a ha : Galois.Qbar) = a := by
  rfl

/-- The embedding is the fixed embedding, not an extra choice per value. -/
theorem fieldElement_embed (s : Finset Galois.Qbar) (a : Galois.Qbar) (ha : a ∈ s) :
    Galois.embed (fieldElement s a ha : Galois.Qbar) = Galois.embed a := by
  rfl

/-- Keep a given number field while adjoining an additional finite list. -/
def enlargedField (K : IntermediateField ℚ Galois.Qbar) (s : Finset Galois.Qbar) :
    IntermediateField ℚ Galois.Qbar := K ⊔ generatedField s

/-- The prescribed base field survives the enlargement. -/
theorem base_le_enlargedField (K : IntermediateField ℚ Galois.Qbar) (s : Finset Galois.Qbar) :
    K ≤ enlargedField K s := by
  exact le_sup_left

/-- Every additional generator lies in the enlarged field. -/
theorem generator_mem_enlargedField (K : IntermediateField ℚ Galois.Qbar)
    (s : Finset Galois.Qbar) (a : Galois.Qbar) (ha : a ∈ s) :
    a ∈ enlargedField K s := by
  exact (le_sup_right : generatedField s ≤ K ⊔ generatedField s) (generator_mem s a ha)

/-- Enlarging a number field by finitely many algebraic numbers stays finite
(`IntermediateField.finiteDimensional_sup`). -/
theorem enlargedField_finiteDimensional (K : IntermediateField ℚ Galois.Qbar) [NumberField K]
    (s : Finset Galois.Qbar) : FiniteDimensional ℚ (enlargedField K s) := by
  exact IntermediateField.finiteDimensional_sup K (generatedField s)

attribute [instance] enlargedField_finiteDimensional

instance enlargedField_numberField (K : IntermediateField ℚ Galois.Qbar) [NumberField K]
    (s : Finset Galois.Qbar) : NumberField (enlargedField K s) :=
  NumberField.of_module_finite ℚ (enlargedField K s)

/-- The concrete inclusion used for primes and reductions under enlargement. -/
def baseToEnlarged (K : IntermediateField ℚ Galois.Qbar) (s : Finset Galois.Qbar) :
    K →ₐ[ℚ] enlargedField K s := IntermediateField.inclusion (base_le_enlargedField K s)

/-- The inclusion is compatible with the fixed ambient Qbar. -/
theorem baseToEnlarged_coe (K : IntermediateField ℚ Galois.Qbar) (s : Finset Galois.Qbar)
    (x : K) : (baseToEnlarged K s x : Galois.Qbar) = (x : Galois.Qbar) := by
  rfl

/-- Every rational prime has a place on any number field, without a supplied valuation. -/
theorem exists_prime_at (L : Type*) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime) :
    ∃ P : Prime L, residueChar P = p := by
  have : Fact p.Prime := ⟨hp⟩
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hI : I ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Int.natCast_ne_zero.mpr hp.ne_zero)
  obtain ⟨Q, hQ, hQI⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral I (S := 𝓞 L)
  have : Q.IsMaximal := hQ
  have : Q.LiesOver I := hQI
  refine ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot hI Q⟩, ?_⟩
  change ringChar (𝓞 L ⧸ Q) = p
  rw [Ideal.ringChar_quot, ← Ideal.over_def Q I]
  simp [I]

/-- One choice for the whole field/family at a fixed p, independent of labels. -/
def chosenPrime (L : Type*) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime) : Prime L :=
  Classical.choose (exists_prime_at L p hp)

/-- The choice has the requested residue characteristic. -/
theorem chosenPrime_char (L : Type*) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime) :
    residueChar (chosenPrime L p hp) = p := by
  exact Classical.choose_spec (exists_prime_at L p hp)

/-- A fixed lower place extends to the concrete enlarged model. -/
theorem enlargedField_exists_prime_above (K : IntermediateField ℚ Galois.Qbar) [NumberField K]
    (s : Finset Galois.Qbar) (P : Prime K) :
    letI : Algebra K (enlargedField K s) := (baseToEnlarged K s).toAlgebra
    ∃ Q : Prime (enlargedField K s), Q.asIdeal.LiesOver P.asIdeal := by
  let : Algebra K (enlargedField K s) := (baseToEnlarged K s).toAlgebra
  exact exists_prime_above P

/-- Extend one chosen place once, rather than reselecting a place for each label. -/
def enlargedPrime (K : IntermediateField ℚ Galois.Qbar) [NumberField K]
    (s : Finset Galois.Qbar) (P : Prime K) : Prime (enlargedField K s) :=
  letI : Algebra K (enlargedField K s) := (baseToEnlarged K s).toAlgebra
  Classical.choose (enlargedField_exists_prime_above K s P)

/-- The chosen prime really lies above the original one. -/
theorem enlargedPrime_above (K : IntermediateField ℚ Galois.Qbar) [NumberField K]
    (s : Finset Galois.Qbar) (P : Prime K) :
    letI : Algebra K (enlargedField K s) := (baseToEnlarged K s).toAlgebra
    (enlargedPrime K s P).asIdeal.LiesOver P.asIdeal := by
  let : Algebra K (enlargedField K s) := (baseToEnlarged K s).toAlgebra
  exact Classical.choose_spec (enlargedField_exists_prime_above K s P)

/-- Its characteristic remains fixed as more algebraic coefficients are added. -/
theorem enlargedPrime_char (K : IntermediateField ℚ Galois.Qbar) [NumberField K]
    (s : Finset Galois.Qbar) (P : Prime K) :
    residueChar (enlargedPrime K s P) = residueChar P := by
  let : Algebra K (enlargedField K s) := (baseToEnlarged K s).toAlgebra
  have := enlargedPrime_above K s P
  exact residueChar_above P (enlargedPrime K s P)

end SICLean.L5.FinitePlace

#check @IntermediateField.finiteDimensional_adjoin
#check @NumberField.of_module_finite
#check @Ideal.exists_maximal_ideal_liesOver_of_isIntegral
#check @SICLean.L5.FinitePlace.enlargedPrime_above
#print SICLean.L5.FinitePlace.generatedField
#print SICLean.L5.FinitePlace.enlargedPrime
