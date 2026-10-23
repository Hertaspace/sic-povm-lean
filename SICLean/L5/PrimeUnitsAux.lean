import SICLean.L5.PrimeReductionArithmetic

set_option autoImplicit false

noncomputable section

namespace SICLean.L5.PrimeUnitsAux

open NumberField FinitePlace

variable {L : Type*} [Field L] [NumberField L]

/-- A globally integral field element belongs to every finite valuation ring. -/
theorem integralAt_of_isIntegral (P : Prime L) {x : L} (hx : IsIntegral ℤ x) :
    IntegralAt P x := by
  obtain ⟨a, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 L)).mp hx
  exact integralAt_integer P a

/-- The converse uses all finite primes, via Mathlib's intersection theorem. -/
theorem isIntegral_of_all_integralAt {x : L} (hx : ∀ P : Prime L, IntegralAt P x) :
    IsIntegral ℤ x := by
  apply (IsIntegralClosure.isIntegral_iff (A := 𝓞 L)).mpr
  apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro P
  have h := (integralAt_iff_mem_localRing P x).mp (hx P)
  rw [P.valuationSubringAtPrime_eq_valuationSubring] at h
  exact h

/-- Coprimality with the residue characteristic implies coprimality with the ideal norm. -/
theorem norm_coprime (P : Prime L) {n : ℕ} (hc : (residueChar P).Coprime n) :
    (Ideal.absNorm P.asIdeal).Coprime n := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  change (Nat.card (Residue P)).Coprime n
  rw [residue_card]
  exact hc.pow_left _

/-- Prime-to-characteristic integer roots remain distinct in the residue field. -/
theorem integer_roots_quotient_injective (P : Prime L) {n : ℕ} (hn : n ≠ 0)
    (hc : (residueChar P).Coprime n) {a b : 𝓞 L} (ha : a ^ n = 1) (hb : b ^ n = 1)
    (hab : Ideal.Quotient.mk P.asIdeal a = Ideal.Quotient.mk P.asIdeal b) : a = b := by
  let : NeZero n := ⟨hn⟩
  let u : rootsOfUnity n (𝓞 L) :=
    ⟨Units.ofPowEqOne a n ha hn, (mem_rootsOfUnity n _).mpr (Units.pow_ofPowEqOne ha hn)⟩
  let v : rootsOfUnity n (𝓞 L) :=
    ⟨Units.ofPowEqOne b n hb hn, (mem_rootsOfUnity n _).mpr (Units.pow_ofPowEqOne hb hn)⟩
  have huv : Ideal.rootsOfUnityMapQuot P.asIdeal n u =
      Ideal.rootsOfUnityMapQuot P.asIdeal n v := Units.ext hab
  have heq := Ideal.rootsOfUnityMapQuot_injective n
    (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top) (norm_coprime P hc) huv
  exact congrArg (fun z : rootsOfUnity n (𝓞 L) => ((z : (𝓞 L)ˣ) : 𝓞 L)) heq

end SICLean.L5.PrimeUnitsAux
