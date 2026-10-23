import SICLean.L5.FrobeniusRestriction

set_option autoImplicit false

/-!
# Complete splitting, Frobenius, and prime-ideal counts

[RW-rec, Prop. 4, p. 14]. Algebraicity of the values is [RW26, Thm. 1, p. 3].
Mathlib: `RamificationInertia/Galois.lean`, `RingTheory/RamificationInertia`,
`FieldTheory/Finite/Basic.lean`.

Complete splitting means the local invariants satisfy `e = f = 1`.
The Frobenius criterion and the counting criterion are separate statements.
In particular, `f = 1` is not by itself the splitting criterion at a ramified prime.
No density is defined.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

namespace SICLean.L5.FrobeniusSplitting

open GoodReductionLocal FrobeniusPrimes FrobeniusRestriction

variable (F : IntermediateField ℚ Galois.Qbar) [NumberField F] [IsGalois ℚ F]

/-- Literal complete splitting of a rational prime: all local e and f are 1.
Native invariants are `Ideal.ramificationIdx` and `Ideal.inertiaDeg`. -/
def splitsCompletely (p : ℕ) : Prop :=
  p.Prime ∧ ∀ P : Prime F, P.asIdeal.LiesOver (rationalIdeal p) →
    P.asIdeal.ramificationIdx ℤ = 1 ∧ P.asIdeal.inertiaDeg ℤ = 1

/-- The actual splitting-prime set, with no measure or density attached. -/
def splittingPrimes : Set ℕ := {p | splitsCompletely F p}

/-- `Mathlib.RingTheory.Ideal.GoingUp`; the prime is nonzero. -/
theorem exists_primeOver (p : ℕ) (hp : p.Prime) :
    ∃ P : Prime F, P.asIdeal.LiesOver (rationalIdeal p) := by
  have : Fact p.Prime := ⟨hp⟩
  have : (rationalIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨Q, hQ, hQp⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (rationalIdeal p) (𝓞 F)))
  have := hQp
  have hp0 : rationalIdeal p ≠ ⊥ := by
    simpa [rationalIdeal, Ideal.span_singleton_eq_bot] using hp.ne_zero
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q⟩, hQp⟩

/-- Finite number of primes in a finite number-field extension.
Mathlib DedekindDomain factorization or the finite Galois prime orbit. -/
theorem primesOver_finite (p : ℕ) (hp : p.Prime) :
    (Ideal.primesOver (rationalIdeal p) (𝓞 F)).Finite := by
  exact Algebra.QuasiFinite.finite_primesOver (rationalIdeal p)

/-- `Mathlib.NumberTheory.RamificationInertia.Galois`, with e,f specialized
at any prime above p; finite Galoisness makes them independent of that choice. -/
theorem fundamental_count (P : Prime F) (p : ℕ) (hp : p.Prime)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) :
    (Ideal.primesOver (rationalIdeal p) (𝓞 F)).ncard *
      (P.asIdeal.ramificationIdx ℤ * P.asIdeal.inertiaDeg ℤ) =
        Module.finrank ℚ F := by
  have : Fact p.Prime := ⟨hp⟩
  have : (rationalIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have := hP
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (rationalIdeal p) (𝓞 F) (F ≃ₐ[ℚ] F)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx
      (rationalIdeal p) P.asIdeal (F ≃ₐ[ℚ] F),
    Ideal.inertiaDegIn_eq_inertiaDeg (rationalIdeal p) P.asIdeal (F ≃ₐ[ℚ] F),
    IsGaloisGroup.card_eq_finrank (F ≃ₐ[ℚ] F) ℚ F] at h
  exact h

/-- `Mathlib.RingTheory.RamificationInertia.Ramification`;
residue fields are finite, hence separable. -/
theorem unramifiedAt_iff_ramificationIdx (P : Prime F) :
    Algebra.IsUnramifiedAt ℤ P.asIdeal ↔ P.asIdeal.ramificationIdx ℤ = 1 := by
  exact Ideal.ramificationIdx_eq_one_iff.symm

/-- `Mathlib.NumberTheory.RamificationInertia.Unramified`;
global nonramification means all primes over p are nonramified. -/
theorem unramifiedIn_iff_forall (p : ℕ) (hp : p.Prime) :
    Algebra.IsUnramifiedIn (𝓞 F) (rationalIdeal p) ↔
      ∀ P : Prime F, P.asIdeal.LiesOver (rationalIdeal p) →
        Algebra.IsUnramifiedAt ℤ P.asIdeal := by
  constructor
  · intro h P hP
    exact h P.asIdeal inferInstance hP
  · intro h Q hQ hQp
    have := hQp
    have hp0 : rationalIdeal p ≠ ⊥ := by
      simpa [rationalIdeal, Ideal.span_singleton_eq_bot] using hp.ne_zero
    exact h ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q⟩ hQp

/-- The identity satisfies the Frobenius congruences if and only if the residue
extension has degree `1`. The equivalence includes ramified primes. -/
theorem one_isArithFrobAt_iff (P : Prime F) :
    IsArithFrobAt ℤ (1 : F ≃ₐ[ℚ] F) P.asIdeal ↔
      P.asIdeal.inertiaDeg ℤ = 1 := by
  have : Finite (ℤ ⧸ P.asIdeal.under ℤ) :=
    .of_injective _ Ideal.algebraMap_quotient_injective
  let := Fintype.ofFinite (ℤ ⧸ P.asIdeal.under ℤ)
  rw [Ideal.inertiaDeg_eq_of_isMaximal (P.asIdeal.under ℤ) P.asIdeal,
    ← FiniteField.orderOf_frobeniusAlgHom, orderOf_eq_one_iff]
  constructor
  · intro h
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [FiniteField.frobeniusAlgHom_apply, AlgHom.one_apply,
      Nat.card_eq_fintype_card, MulSemiringAction.toAlgHom_apply, one_smul] using
        (h.mk_apply x).symm
  · intro h x
    have hx := DFunLike.congr_fun h (Ideal.Quotient.mk P.asIdeal x)
    rw [← Ideal.Quotient.eq]
    simpa only [FiniteField.frobeniusAlgHom_apply, AlgHom.one_apply,
      Nat.card_eq_fintype_card, MulSemiringAction.toAlgHom_apply, one_smul, map_pow]
        using hx.symm

/-- The order of the chosen Frobenius equals the residue degree, by the residue
Frobenius and the faithful unramified decomposition action. -/
theorem orderOf_arithFrob (P : Prime F)
    (hP : Algebra.IsUnramifiedAt ℤ P.asIdeal) :
    orderOf (arithFrob F P) = P.asIdeal.inertiaDeg ℤ := by
  have := hP
  have he : P.asIdeal.ramificationIdx ℤ = 1 :=
    Ideal.ramificationIdx_eq_one P.asIdeal ℤ
  have : Finite (ℤ ⧸ P.asIdeal.under ℤ) :=
    .of_injective _ Ideal.algebraMap_quotient_injective
  let := Fintype.ofFinite (ℤ ⧸ P.asIdeal.under ℤ)
  let G := F ≃ₐ[ℚ] F
  let D := MulAction.stabilizer G P.asIdeal
  let φ := Ideal.Quotient.stabilizerHom P.asIdeal (P.asIdeal.under ℤ) G
  have hFrob : IsArithFrobAt ℤ (arithFrob F P) P.asIdeal :=
    IsArithFrobAt.arithFrobAt ℤ G P.asIdeal
  let σ : D := ⟨arithFrob F P, hFrob.mem_stabilizer⟩
  have hI : P.asIdeal.inertia G = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Ideal.card_inertia_eq_ramificationIdxIn (P.asIdeal.under ℤ) P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under ℤ) P.asIdeal G, he]
  have hker : φ.ker = ⊥ := by
    rw [Ideal.Quotient.ker_stabilizerHom]
    refine le_antisymm ?_ bot_le
    intro τ hτ
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hτ' : (τ : G) ∈ P.asIdeal.inertia G := hτ
    exact Subgroup.mem_bot.mp (hI ▸ hτ')
  have hφ : φ σ = FiniteField.frobeniusAlgEquivOfAlgebraic
      (ℤ ⧸ P.asIdeal.under ℤ) ((𝓞 F) ⧸ P.asIdeal) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [φ, Ideal.Quotient.stabilizerHom_apply, MulAction.subgroup_smul_def,
      σ, FiniteField.frobeniusAlgEquivOfAlgebraic_apply,
      Nat.card_eq_fintype_card, MulSemiringAction.toAlgHom_apply] using
        hFrob.mk_apply x
  calc
    orderOf (arithFrob F P) = orderOf σ := orderOf_submonoid σ
    _ = orderOf (φ σ) :=
      (orderOf_injective φ (φ.ker_eq_bot_iff.mp hker) σ).symm
    _ = P.asIdeal.inertiaDeg ℤ := by
      rw [hφ, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
        Ideal.inertiaDeg_eq_of_isMaximal (P.asIdeal.under ℤ) P.asIdeal]

/-- The chosen Frobenius is the identity if and only if the residue degree is `1`. -/
theorem arithFrob_eq_one_iff_inertiaDeg (P : Prime F)
    (hP : Algebra.IsUnramifiedAt ℤ P.asIdeal) :
    arithFrob F P = 1 ↔ P.asIdeal.inertiaDeg ℤ = 1 := by
  rw [← orderOf_eq_one_iff, orderOf_arithFrob F P hP]

/-- The residue-degree/counting equivalence requires nonramification.
In the ramified S₃ model, p=3 has f=1 but only one prime ideal. -/
theorem inertiaDeg_eq_one_iff_ncard (P : Prime F) (p : ℕ) (hp : p.Prime)
    (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunr : Algebra.IsUnramifiedIn (𝓞 F) (rationalIdeal p)) :
    P.asIdeal.inertiaDeg ℤ = 1 ↔
      (Ideal.primesOver (rationalIdeal p) (𝓞 F)).ncard = Module.finrank ℚ F := by
  have hcount := fundamental_count F P p hp hP
  rw [hunr.ramificationIdx_eq_one hP, one_mul] at hcount
  constructor
  · intro hf
    simpa [hf] using hcount
  · intro hg
    rw [hg] at hcount
    exact (mul_eq_left₀ Module.finrank_pos.ne').mp hcount

/-- Counting criterion is unconditional for prime p, because the
definition of splitting retains both e and f. -/
theorem splitsCompletely_iff_ncard (p : ℕ) (hp : p.Prime) :
    splitsCompletely F p ↔
      (Ideal.primesOver (rationalIdeal p) (𝓞 F)).ncard = Module.finrank ℚ F := by
  constructor
  · intro hsplit
    obtain ⟨P, hP⟩ := exists_primeOver F p hp
    obtain ⟨he, hf⟩ := hsplit.2 P hP
    simpa [he, hf] using fundamental_count F P p hp hP
  · intro hg
    refine ⟨hp, fun P hP => ?_⟩
    have hcount := fundamental_count F P p hp hP
    rw [hg] at hcount
    have hef : P.asIdeal.ramificationIdx ℤ * P.asIdeal.inertiaDeg ℤ = 1 :=
      (mul_eq_left₀ Module.finrank_pos.ne').mp hcount
    exact ⟨Nat.dvd_one.mp ⟨P.asIdeal.inertiaDeg ℤ, hef.symm⟩,
      Nat.dvd_one.mp ⟨P.asIdeal.ramificationIdx ℤ,
        by simpa only [mul_comm] using hef.symm⟩⟩

/-- The three-way criterion at any chosen prime above `p`. -/
theorem splitsCompletely_iff_arithFrob_eq_one (P : Prime F) (p : ℕ) (hp : p.Prime)
    (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunr : Algebra.IsUnramifiedIn (𝓞 F) (rationalIdeal p)) :
    splitsCompletely F p ↔ arithFrob F P = 1 := by
  have hPu := (unramifiedIn_iff_forall F p hp).mp hunr P hP
  rw [splitsCompletely_iff_ncard F p hp,
    arithFrob_eq_one_iff_inertiaDeg F P hPu]
  exact (inertiaDeg_eq_one_iff_ncard F P p hp hP hunr).symm

/-- Uniform version over every prime above `p`. -/
theorem splitsCompletely_iff_all_arithFrob_eq_one (p : ℕ) (hp : p.Prime)
    (hunr : Algebra.IsUnramifiedIn (𝓞 F) (rationalIdeal p)) :
    splitsCompletely F p ↔ ∀ P : Prime F,
      P.asIdeal.LiesOver (rationalIdeal p) → arithFrob F P = 1 := by
  constructor
  · intro hsplit P hP
    exact (splitsCompletely_iff_arithFrob_eq_one F P p hp hP hunr).mp hsplit
  · intro h
    obtain ⟨P, hP⟩ := exists_primeOver F p hp
    exact (splitsCompletely_iff_arithFrob_eq_one F P p hp hP hunr).mpr (h P hP)

/-- Complete splitting descends in an actual finite normal tower;
RingTheory/RamificationInertia, e/f tower formulas. -/
theorem splitsCompletely_mono (H : IntermediateField ℚ Galois.Qbar)
    [NumberField H] [IsGalois ℚ H] (hHF : H ≤ F) (p : ℕ)
    (hsplit : splitsCompletely F p) : splitsCompletely H p := by
  let : Algebra H F := (IntermediateField.inclusion hHF).toAlgebra
  have : IsScalarTower ℚ H F := IsScalarTower.of_algHom (IntermediateField.inclusion hHF)
  refine ⟨hsplit.1, ?_⟩
  intro P hP
  have : P.asIdeal.IsPrime := P.isPrime
  have : P.asIdeal.IsMaximal := P.isMaximal
  have : P.asIdeal.LiesOver (rationalIdeal p) := hP
  obtain ⟨Q, hQmax, hQP⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) P.asIdeal
  have : Q.IsMaximal := hQmax
  have : Q.LiesOver P.asIdeal := hQP
  let Q' : Prime F :=
    { asIdeal := Q
      isPrime := inferInstance
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q }
  have hQp : Q'.asIdeal.LiesOver (rationalIdeal p) :=
    Ideal.LiesOver.trans Q P.asIdeal (rationalIdeal p)
  obtain ⟨he, hf⟩ := hsplit.2 Q' hQp
  constructor
  · apply Nat.dvd_one.mp
    exact he ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) P.asIdeal Q
  · apply Nat.dvd_one.mp
    exact hf ▸ Ideal.inertiaDeg_below_dvd (R := ℤ) P.asIdeal Q

end SICLean.L5.FrobeniusSplitting

#check @Ideal.inertiaDeg
#check @Ideal.ramificationIdx
#check @SICLean.L5.FrobeniusSplitting.splitsCompletely_iff_arithFrob_eq_one
#print SICLean.L5.FrobeniusSplitting.splitsCompletely
