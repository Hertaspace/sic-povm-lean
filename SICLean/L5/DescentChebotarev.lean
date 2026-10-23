import SICLean.L5.FrobeniusRestriction
import SICLean.L5.DescentChebotarevAux
import CebotarevDensity.Main

set_option autoImplicit false

/-!
# Chebotarev over ℚ, with an exact arithmetic Frobenius

The rational primes used for [RW-rec, p. 14, Prop. 4] come from
`Chebotarev.infinite_setOf_frobenius_class`, transported from 𝓞 ℚ to ℤ.
Conjugation of Frobenius is `FrobeniusRestriction.arithFrob_conjugate`.
Algebraicity of the values is [RW26, p. 3, Thm. 1].

The base field of Chebotarev here is ℚ, not the quadratic field K. The
argument uses 𝓞 ℚ and a conjugacy class, transports 𝓞 ℚ to ℤ, removes the
zero ideal, and conjugates the prime so that the Frobenius equals the
prescribed element g. The value of `frobeniusClass` on the zero ideal is
not used as evidence of nonramification, or of the ideal being nonzero.
-/

noncomputable section
open scoped NumberField Pointwise

namespace SICLean.L5.DescentChebotarev

open GoodReductionLocal FrobeniusPrimes

/-- The rational prime ideal in 𝓞 ℚ. [RW-rec, Prop. 4]. -/
def rationalPrimeIdeal (p : ℕ) : Ideal (𝓞 ℚ) := Ideal.span {(p : 𝓞 ℚ)}

/-- `Rat.ringOfIntegersEquiv`: the two integral bases are isomorphic. -/
theorem rationalPrimeIdeal_eq_comap (p : ℕ) :
    rationalPrimeIdeal p = Ideal.comap Rat.ringOfIntegersEquiv (rationalIdeal p) := by
  rw [rationalPrimeIdeal, rationalIdeal, ← Ideal.map_symm Rat.ringOfIntegersEquiv,
    Ideal.map_span, Set.image_singleton]
  congr 2
  simp

/-- Absolute norm of the rational prime ideal. [RW-rec, Prop. 4]. -/
theorem rationalPrimeIdeal_absNorm (p : ℕ) : (rationalPrimeIdeal p).absNorm = p := by
  rw [rationalPrimeIdeal, Ideal.absNorm_span_natCast,
    NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]

/-- A rational prime gives a prime ideal, after transport through 𝓞 ℚ ≃ ℤ. -/
theorem rationalPrimeIdeal_isPrime (p : ℕ) (hp : p.Prime) :
    (rationalPrimeIdeal p).IsPrime := by
  haveI : (rationalIdeal p).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  rw [rationalPrimeIdeal_eq_comap]
  exact Ideal.comap_isPrime Rat.ringOfIntegersEquiv (rationalIdeal p)

/-- A rational prime gives a nonzero ideal. -/
theorem rationalPrimeIdeal_ne_bot (p : ℕ) (hp : p.Prime) :
    rationalPrimeIdeal p ≠ ⊥ := by
  intro h
  have hnorm := rationalPrimeIdeal_absNorm p
  rw [h, Ideal.absNorm_bot] at hnorm
  exact hp.ne_zero hnorm.symm

/-- Inverse dictionary for nonzero prime ideals of 𝓞 ℚ. -/
theorem nonzero_prime_eq_rationalPrimeIdeal (r : Ideal (𝓞 ℚ))
    (hr : r.IsPrime) (hne : r ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ r = rationalPrimeIdeal p := by
  let e := Rat.ringOfIntegersEquiv
  letI := hr
  have hJp : (Ideal.map e r).IsPrime := Ideal.map_isPrime_of_equiv e
  have hcomap : Ideal.comap e (Ideal.map e r) = r :=
    Ideal.comap_map_of_bijective e e.bijective
  have hJne : Ideal.map e r ≠ ⊥ := by
    intro h
    apply hne
    rw [← hcomap, h, Ideal.comap_bot_of_injective e e.injective]
  rcases Ideal.isPrime_int_iff.mp hJp with h | ⟨p, hp, hpJ⟩
  · exact (hJne h).elim
  · refine ⟨p, hp, ?_⟩
    rw [← hcomap, hpJ, rationalPrimeIdeal_eq_comap]
    rfl

variable (F : IntermediateField ℚ Galois.Qbar) [NumberField F] [IsGalois ℚ F]

/-- Naturality of `IsArithFrobAt` through 𝓞 ℚ ≃ ℤ, with equal base residue
cardinalities. The Frobenius remains the arithmetic one. -/
theorem isArithFrobAt_integerBase_iff (P : Prime F) (g : F ≃ₐ[ℚ] F) :
    IsArithFrobAt (𝓞 ℚ) g P.asIdeal ↔ IsArithFrobAt ℤ g P.asIdeal := by
  unfold IsArithFrobAt AlgHom.IsArithFrobAt
  simp only [MulSemiringAction.toAlgHom_apply,
    DescentChebotarevAux.quotient_card_integerBase]

/-- Contraction through the same integral-base isomorphism. -/
theorem liesOver_rationalPrimeIdeal_iff (P : Prime F) (p : ℕ) :
    P.asIdeal.LiesOver (rationalPrimeIdeal p) ↔ P.asIdeal.LiesOver (rationalIdeal p) := by
  constructor
  · intro h
    constructor
    apply (Ideal.comap_injective_of_surjective Rat.ringOfIntegersEquiv
      Rat.ringOfIntegersEquiv.surjective)
    rw [← rationalPrimeIdeal_eq_comap,
      ← DescentChebotarevAux.under_integerBase]
    exact h.over
  · intro h
    constructor
    rw [rationalPrimeIdeal_eq_comap, DescentChebotarevAux.under_integerBase, h.over]

/-- For separable finite residue fields, the maximal-prime condition matches
`Algebra.IsUnramifiedIn`. -/
theorem unramifiedIn_integerBase_iff (p : ℕ) (hp : p.Prime) :
    Chebotarev.UnramifiedIn ℚ F (rationalPrimeIdeal p) ↔
      Algebra.IsUnramifiedIn (𝓞 F) (rationalIdeal p) := by
  have hp0 : rationalIdeal p ≠ ⊥ := by
    intro h
    apply hp.ne_zero
    exact_mod_cast (Ideal.span_singleton_eq_bot.mp h : (p : ℤ) = 0)
  constructor
  · intro h Q hQ hQp
    letI := hQ
    letI := hQp
    have hQ0 := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
    let P : Prime F := ⟨Q, hQ, hQ0⟩
    exact (DescentChebotarevAux.isUnramifiedAt_integerBase_iff F Q).mp
      (h Q (hQ.isMaximal hQ0) ((liesOver_rationalPrimeIdeal_iff F P p).mpr hQp))
  · intro h Q hQ hQp
    letI := hQ.isPrime
    letI := hQp
    have hQ0 := Ideal.ne_bot_of_liesOver_of_ne_bot (rationalPrimeIdeal_ne_bot p hp) Q
    let P : Prime F := ⟨Q, hQ.isPrime, hQ0⟩
    exact (DescentChebotarevAux.isUnramifiedAt_integerBase_iff F Q).mpr
      (h Q hQ.isPrime ((liesOver_rationalPrimeIdeal_iff F P p).mp hQp))

/-- At a nonzero unramified rational prime, the Frobenius class is the class
of the chosen arithmetic Frobenius. -/
theorem frobeniusClass_eq_mk_arithFrob (p : ℕ) (hp : p.Prime)
    (hunram : Chebotarev.UnramifiedIn ℚ F (rationalPrimeIdeal p))
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p)) :
    Chebotarev.frobeniusClass ℚ F (rationalPrimeIdeal p) =
      ConjClasses.mk (arithFrob F P) := by
  letI := rationalPrimeIdeal_isPrime p hp
  letI : NeZero (rationalPrimeIdeal p) := ⟨rationalPrimeIdeal_ne_bot p hp⟩
  exact Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt ℚ F
    (rationalPrimeIdeal p) hunram (arithFrob F P) P.asIdeal
    ((isArithFrobAt_integerBase_iff F P _).mpr (arithFrob_spec F P))
    ((liesOver_rationalPrimeIdeal_iff F P p).mpr hP)

/-- [RW-rec, p. 14, Prop. 4]: conjugating a prime over the same rational prime
sends its arithmetic Frobenius to the prescribed representative g. -/
theorem exists_exact_frobenius_of_class (g : F ≃ₐ[ℚ] F) (p : ℕ) (hp : p.Prime)
    (hunram : Chebotarev.UnramifiedIn ℚ F (rationalPrimeIdeal p))
    (hclass : Chebotarev.frobeniusClass ℚ F (rationalPrimeIdeal p) = ConjClasses.mk g) :
    ∃ P : Prime F, P.asIdeal.LiesOver (rationalIdeal p) ∧
      Algebra.IsUnramifiedAt ℤ P.asIdeal ∧ arithFrob F P = g := by
  letI := rationalPrimeIdeal_isPrime p hp
  obtain ⟨Q, hQ, hQp, hQ0⟩ := Chebotarev.exists_prime_liesOver ℚ F
    (rationalPrimeIdeal p) (rationalPrimeIdeal_ne_bot p hp)
  let P : Prime F := ⟨Q, hQ, hQ0⟩
  have hP : P.asIdeal.LiesOver (rationalIdeal p) :=
    (liesOver_rationalPrimeIdeal_iff F P p).mp hQp
  have hPunram : Algebra.IsUnramifiedAt ℤ P.asIdeal :=
    ((unramifiedIn_integerBase_iff F p hp).mp hunram) P.asIdeal P.isPrime hP
  have hc : IsConj (arithFrob F P) g := ConjClasses.mk_eq_mk_iff_isConj.mp
    ((frobeniusClass_eq_mk_arithFrob F p hp hunram P hP).symm.trans hclass)
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hc
  refine ⟨FrobeniusRestriction.conjugatePrime F τ P, ?_,
    FrobeniusRestriction.unramified_conjugate F P τ hPunram, ?_⟩
  · letI := hP
    change (τ • P.asIdeal).LiesOver (rationalIdeal p)
    infer_instance
  · rw [FrobeniusRestriction.arithFrob_conjugate F P hPunram τ, hτ]

/-- A Frobenius element equal to g at some prime above a rational prime.
The defining predicate does not assert that its solution set is nonempty
or infinite. [RW-rec, Prop. 4]. -/
def HasExactFrobenius (g : F ≃ₐ[ℚ] F) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ P : Prime F, P.asIdeal.LiesOver (rationalIdeal p) ∧
    Algebra.IsUnramifiedAt ℤ P.asIdeal ∧ arithFrob F P = g

/-- Remove the zero ideal before using the nonzero-prime dictionary.
No conclusion is drawn from the class of the zero ideal. -/
theorem infinite_nonzero_primeIdeals (g : F ≃ₐ[ℚ] F) :
    Set.Infinite {r : Ideal (𝓞 ℚ) | r.IsPrime ∧ r ≠ ⊥ ∧
      Chebotarev.UnramifiedIn ℚ F r ∧
      Chebotarev.frobeniusClass ℚ F r = ConjClasses.mk g} := by
  have h := (Chebotarev.infinite_setOf_frobenius_class
    (K := ℚ) (L := F) (ConjClasses.mk g)).sdiff (Set.finite_singleton ⊥)
  refine h.mono ?_
  rintro r ⟨⟨hr, hunram, hclass⟩, hne⟩
  exact ⟨hr, by simpa only [Set.mem_singleton_iff] using hne, hunram, hclass⟩

/-- Infinitely many rational primes whose arithmetic Frobenius equals g.
There is no density comparison of splitting sets, and no hypothesis t ≠ 1.
[RW-rec, Prop. 4]. -/
theorem infinite_rationalPrimes_exact (g : F ≃ₐ[ℚ] F) :
    Set.Infinite {p : ℕ | HasExactFrobenius F g p} := by
  have h := infinite_nonzero_primeIdeals F g
  apply Set.Infinite.of_image rationalPrimeIdeal
  refine h.mono ?_
  rintro r ⟨hr, hne, hunram, hclass⟩
  obtain ⟨p, hp, rfl⟩ := nonzero_prime_eq_rationalPrimeIdeal r hr hne
  exact ⟨p, ⟨hp, exists_exact_frobenius_of_class F g p hp hunram hclass⟩, rfl⟩

/-- Removing an arbitrary finite exceptional set preserves infinitude. -/
theorem infinite_rationalPrimes_exact_avoid (g : F ≃ₐ[ℚ] F) (B : Finset ℕ) :
    Set.Infinite {p : ℕ | HasExactFrobenius F g p ∧ p ∉ B} := by
  exact (infinite_rationalPrimes_exact F g).sdiff B.finite_toSet

/-- A witness outside a prescribed finite set of rational primes. -/
theorem exists_exact_frobenius_avoid (g : F ≃ₐ[ℚ] F) (B : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ B ∧ ∃ P : Prime F,
      P.asIdeal.LiesOver (rationalIdeal p) ∧
      Algebra.IsUnramifiedAt ℤ P.asIdeal ∧ arithFrob F P = g := by
  obtain ⟨p, ⟨hp, hP⟩, hpB⟩ := (infinite_rationalPrimes_exact_avoid F g B).nonempty
  exact ⟨p, hp, hpB, hP⟩

end SICLean.L5.DescentChebotarev
