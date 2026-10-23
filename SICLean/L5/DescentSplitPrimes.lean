import SICLean.L5.DescentField
import SICLean.L5.DescentChebotarev

set_option autoImplicit false

/-!
# Exact Frobenius fixing K gives the two split primes of K

[RW-rec, p. 14, Prop. 4] and [RW-rec, pp. 12--13, Thm. 8].
[RW26, p. 20, (37)] identifies K and I.

The prime of K is the contraction of the Chebotarev prime of F. Its partner
is the quadratic conjugate. Rational primes are obtained over ℚ in
`DescentChebotarev`. The argument does not infer the result from infinitude
of primes of K.
-/

noncomputable section
open scoped NumberField MatrixGroups Pointwise

namespace SICLean.L5.DescentSplitPrimes

open GoodReductionLocal FrobeniusPrimes FrobeniusSplitting
open IsDedekindDomain UniqueFactorizationMonoid

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM
local notation "F" => DescentField.field M hM

/-- Contraction along the inclusion K ≤ F. [RW-rec, Prop. 4]. -/
def contractedPrime (m : ℕ) (P : Prime (F m)) : FinitePlace.Prime K :=
  FrobeniusRestriction.contractPrime (F m) K (DescentField.base_le M hM m) P

/-- Transitivity of contraction down to ℤ. [RW-rec, Prop. 4]. -/
theorem contractedPrime_liesOver (m p : ℕ) (P : Prime (F m))
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) :
    (contractedPrime M hM m P).asIdeal.LiesOver (rationalIdeal p) := by
  let : Algebra K (F m) := (IntermediateField.inclusion (DescentField.base_le M hM m)).toAlgebra
  have : IsScalarTower ℚ K (F m) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (DescentField.base_le M hM m))
  have := hP
  exact Ideal.LiesOver.tower_bot P.asIdeal (P.asIdeal.under (𝓞 K)) (rationalIdeal p)

/-- Contraction preserves the rational residue characteristic. [RW-rec, Prop. 4]. -/
theorem primeBelow_contractedPrime (m : ℕ) (P : Prime (F m)) :
    primeBelow K (contractedPrime M hM m P) = primeBelow (F m) P := by
  exact FrobeniusRestriction.primeBelow_contractPrime (F m) K
    (DescentField.base_le M hM m) P

/-- Nonramification descends in the tower. [RW-rec, Prop. 4]. -/
theorem contractedPrime_unramified (m : ℕ) (P : Prime (F m))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal) :
    Algebra.IsUnramifiedAt ℤ (contractedPrime M hM m P).asIdeal := by
  let : Algebra K (F m) := (IntermediateField.inclusion (DescentField.base_le M hM m)).toAlgebra
  have : IsScalarTower ℚ K (F m) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (DescentField.base_le M hM m))
  apply (unramifiedAt_iff_ramificationIdx K (contractedPrime M hM m P)).mpr
  apply Nat.dvd_one.mp
  have he := (unramifiedAt_iff_ramificationIdx (F m) P).mp hunram
  exact he ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) (P.asIdeal.under (𝓞 K)) P.asIdeal

/-- Restriction of the chosen arithmetic Frobenius. [RW-rec, Prop. 4]. -/
theorem arithFrob_contractedPrime (m : ℕ) (P : Prime (F m))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal) :
    arithFrob K (contractedPrime M hM m P) =
      DescentField.restrictK M hM m (arithFrob (F m) P) := by
  exact (FrobeniusRestriction.arithFrob_restrict (F m) K
    (DescentField.base_le M hM m) P (contractedPrime_unramified M hM m P hunram)).symm

/-- [RW-rec, p. 14, Prop. 4]: if the restriction is the identity, the prime of K
is unramified of degree one, hence p splits completely in the quadratic extension K/ℚ. -/
theorem splitsCompletely_of_exact_frobenius (m p : ℕ) (hp : p.Prime)
    (g : F m ≃ₐ[ℚ] F m) (hg : DescentField.restrictK M hM m g = 1)
    (P : Prime (F m)) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal) (hFrob : arithFrob (F m) P = g) :
    splitsCompletely K p := by
  let r := contractedPrime M hM m P
  have hr := contractedPrime_liesOver M hM m p P hP
  have hu := contractedPrime_unramified M hM m P hunram
  have he := (unramifiedAt_iff_ramificationIdx K r).mp hu
  have hf : r.asIdeal.inertiaDeg ℤ = 1 := by
    apply (arithFrob_eq_one_iff_inertiaDeg K r hu).mp
    rw [arithFrob_contractedPrime M hM m P hunram, hFrob, hg]
  have : Fact p.Prime := ⟨hp⟩
  have : (rationalIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have := hr
  refine ⟨hp, fun Q hQ => ?_⟩
  have := hQ
  constructor
  · exact (Ideal.ramificationIdx_eq_of_isGaloisGroup (rationalIdeal p)
      Q.asIdeal r.asIdeal (K ≃ₐ[ℚ] K)).trans he
  · exact (Ideal.inertiaDeg_eq_of_isGaloisGroup (rationalIdeal p)
      Q.asIdeal r.asIdeal (K ≃ₐ[ℚ] K)).trans hf

/-- A split prime of the quadratic field is distinct from its conjugate. -/
theorem conjugate_ne_of_splitsCompletely (p : ℕ) (hp : p.Prime)
    (hsplit : splitsCompletely K p) (r : FinitePlace.Prime K)
    (hr : r.asIdeal.LiesOver (rationalIdeal p)) :
    r ≠ RayArithmeticConjugation.primeConjugation M hM r := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  have : (rationalIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have := hr
  let G := K ≃ₐ[ℚ] K
  have hcard := Ideal.card_stabilizer_eq (G := G) (rationalIdeal p) r.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (rationalIdeal p) r.asIdeal G,
    Ideal.inertiaDegIn_eq_inertiaDeg (rationalIdeal p) r.asIdeal G,
    (hsplit.2 r hr).1, (hsplit.2 r hr).2, one_mul] at hcard
  have hbot := Subgroup.eq_bot_of_card_eq (MulAction.stabilizer G r.asIdeal) hcard
  have hmem : RayArithmeticPlaces.conjugation M hM ∈ MulAction.stabilizer G r.asIdeal := by
    change RayArithmeticConjugation.idealConjugation M hM r.asIdeal = r.asIdeal
    rw [← RayArithmeticConjugation.primeConjugation_asIdeal]
    exact congrArg (fun s : FinitePlace.Prime K => s.asIdeal) h.symm
  rw [hbot] at hmem
  exact RayArithmeticPlaces.conjugation_ne_one M hM (Subgroup.mem_bot.mp hmem)

/-- Quadratic factorization with e = f = 1. [RW-rec, Thm. 8]. -/
theorem isSplitPair_of_splitsCompletely (p : ℕ) (hp : p.Prime)
    (hsplit : splitsCompletely K p) (r : FinitePlace.Prime K)
    (hr : r.asIdeal.LiesOver (rationalIdeal p)) :
    SplitPrimeLattice.IsSplitPair p r (RayArithmeticConjugation.primeConjugation M hM r) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : (rationalIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have := hr
  let q := RayArithmeticConjugation.primeConjugation M hM r
  have hq : q.asIdeal.LiesOver (rationalIdeal p) := by
    dsimp [q]
    rw [RayArithmeticConjugation.primeConjugation_asIdeal]
    exact Ideal.LiesOver.of_eq_map_equiv (rationalIdeal p)
      (RayArithmeticPlaces.integerConjugation M hM).toIntAlgEquiv rfl
  have hne : r ≠ q := conjugate_ne_of_splitsCompletely M hM p hp hsplit r hr
  have hneI : r.asIdeal ≠ q.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  refine ⟨hne, ?_⟩
  have hp0 : rationalIdeal p ≠ ⊥ := by
    simpa [rationalIdeal, Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hJ0 : (rationalIdeal p).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp0
  have hcount : (Ideal.primesOver (rationalIdeal p) (𝓞 K)).ncard = 2 := by
    rw [← (ActualField.baseField_isRealQuadratic M hM).degree_two]
    exact (splitsCompletely_iff_ncard K p hp).mp hsplit
  have hpair : ({r.asIdeal, q.asIdeal} : Set (Ideal (𝓞 K))) =
      Ideal.primesOver (rationalIdeal p) (𝓞 K) := by
    apply Set.eq_of_subset_of_ncard_le
    · intro I hI
      rcases hI with rfl | hI
      · exact ⟨r.isPrime, hr⟩
      · rw [Set.mem_singleton_iff] at hI
        subst I
        exact ⟨q.isPrime, hq⟩
    · rw [hcount, Set.ncard_pair hneI]
    · exact Set.toFinite _
  have hfac : normalizedFactors ((rationalIdeal p).map (algebraMap ℤ (𝓞 K))) =
      {r.asIdeal, q.asIdeal} := by
    apply Multiset.ext.mpr
    intro I
    by_cases hir : I = r.asIdeal
    · subst I
      rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        (rationalIdeal p) r.asIdeal hJ0, (hsplit.2 r hr).1]
      simp [hneI]
    · by_cases hiq : I = q.asIdeal
      · subst I
        have := hq
        rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
          (rationalIdeal p) q.asIdeal hJ0, (hsplit.2 q hq).1]
        simp [hneI]
      · have hnot : I ∉ normalizedFactors
            ((rationalIdeal p).map (algebraMap ℤ (𝓞 K))) := by
          rw [← Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 K) hp0, ← hpair]
          simp [hir, hiq]
        rw [Multiset.count_eq_zero_of_notMem hnot]
        simp [hir, hiq]
  have hprod := Ideal.prod_normalizedFactors_eq_self hJ0
  rw [hfac] at hprod
  simpa [rationalIdeal, Ideal.map_span] using hprod

/-- The Chebotarev witness P contracts to a split pair. [RW-rec, Prop. 4]. -/
theorem contracted_isSplitPair (m p : ℕ) (hp : p.Prime)
    (g : F m ≃ₐ[ℚ] F m) (hg : DescentField.restrictK M hM m g = 1)
    (P : Prime (F m)) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal) (hFrob : arithFrob (F m) P = g) :
    SplitPrimeLattice.IsSplitPair p (contractedPrime M hM m P)
      (RayArithmeticConjugation.primeConjugation M hM (contractedPrime M hM m P)) := by
  exact isSplitPair_of_splitsCompletely M hM p hp
    (splitsCompletely_of_exact_frobenius M hM m p hp g hg P hP hunram hFrob)
    (contractedPrime M hM m P) (contractedPrime_liesOver M hM m p P hP)

/-- [RW-rec, §8]: conjugation fixes p and preserves the lies-over relation. -/
theorem conjugate_liesOver (p : ℕ) (r : FinitePlace.Prime K)
    (hr : r.asIdeal.LiesOver (rationalIdeal p)) :
    (RayArithmeticConjugation.primeConjugation M hM r).asIdeal.LiesOver
      (rationalIdeal p) := by
  have := hr
  rw [RayArithmeticConjugation.primeConjugation_asIdeal,
    RayArithmeticConjugation.idealConjugation]
  exact Ideal.LiesOver.of_eq_map_equiv (rationalIdeal p)
    (RayArithmeticPlaces.integerConjugation M hM).toIntAlgEquiv rfl

/-- [RW-rec, p. 14]: p ∤ cm gives coprimality of either prime of K with the
finite modulus. Maximal-order stability of I is not assumed. -/
theorem prime_coprime_level (m p : ℕ) (hp : p.Prime)
    (hgood : ¬ p ∣ RayArithmeticModulus.level M hM m)
    (r : FinitePlace.Prime K) (hr : r.asIdeal.LiesOver (rationalIdeal p)) :
    RayArithmeticModulus.CoprimeIdeal M hM m r.asIdeal := by
  have := hr
  have hn : (RayArithmeticModulus.level M hM m : 𝓞 K) ∉ r.asIdeal := by
    intro hn
    have hn' : (RayArithmeticModulus.level M hM m : ℤ) ∈ rationalIdeal p :=
      (Ideal.mem_of_liesOver r.asIdeal (rationalIdeal p) _).mpr (by simpa using hn)
    have hdvd := Ideal.mem_span_singleton.mp hn'
    exact hgood (by exact_mod_cast hdvd)
  apply Ideal.isCoprime_iff_codisjoint.mpr
  apply r.isMaximal.out.not_le_iff_codisjoint.mp
  exact fun hle => hn (hle (Ideal.mem_span_singleton_self _))

/-- The same good-prime condition in the class-field modulus. [RW-rec, §8]. -/
theorem prime_not_mem_modulus_support (m p : ℕ) (hp : p.Prime)
    (hgood : ¬ p ∣ RayArithmeticModulus.level M hM m)
    (r : FinitePlace.Prime K) (hr : r.asIdeal.LiesOver (rationalIdeal p)) :
    r ∉ (ClassFieldModulus.modulus M hM (RayArithmeticModulus.level M hM m)).finitePart.support := by
  have hn : 0 < RayArithmeticModulus.level M hM m := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hgood (hz ▸ dvd_zero p)
  intro hs
  have hmem := (ClassFieldModulus.support_iff M hM _ hn r).mp hs
  have hle : RayArithmeticModulus.finiteIdeal M hM m ≤ r.asIdeal := by
    simpa only [RayArithmeticModulus.finiteIdeal, Ideal.span_singleton_le_iff_mem] using hmem
  have hcp := (prime_coprime_level M hM m p hp hgood r hr).sup_eq
  apply r.isPrime.ne_top
  exact top_unique (hcp ▸ sup_le le_rfl hle)

/-- After removing any finite set, infinitely many rational primes split and
have arithmetic Frobenius equal to the chosen g. [RW-rec, Prop. 4]. -/
theorem infinite_exact_frobenius_split (m : ℕ) (g : F m ≃ₐ[ℚ] F m)
    (hg : DescentField.restrictK M hM m g = 1) (B : Finset ℕ) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ∉ B ∧ splitsCompletely K p ∧
      ∃ P : Prime (F m), P.asIdeal.LiesOver (rationalIdeal p) ∧
        Algebra.IsUnramifiedAt ℤ P.asIdeal ∧ arithFrob (F m) P = g} := by
  apply (DescentChebotarev.infinite_rationalPrimes_exact_avoid (F m) g B).mono
  rintro p ⟨⟨hp, P, hP, hunram, hFrob⟩, hB⟩
  exact ⟨hp, hB,
    splitsCompletely_of_exact_frobenius M hM m p hp g hg P hP hunram hFrob,
    P, hP, hunram, hFrob⟩

end SICLean.L5.DescentSplitPrimes
