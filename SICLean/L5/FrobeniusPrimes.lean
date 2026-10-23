import SICLean.L5.GoodReductionLocal

set_option autoImplicit false

/-!
# Arithmetic Frobenius in a finite Galois subfield of the algebraic closure

[RW-rec, Prop. 4, p. 14]. Algebraicity of the values is [RW26, Thm. 1, p. 3].
The Frobenius below is Mathlib `arithFrobAt` on the ring of integers.
Mathlib: `RingTheory/Frobenius.lean`, `NumberField/Basic.lean`,
`Galois/IsGaloisGroup.lean`.

`arithFrob` is `arithFrobAt` for `ℤ` acting on `𝓞 F`.
It is defined at ramified primes as well. Uniqueness is not asserted here.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace SICLean.L5.FrobeniusPrimes

open GoodReductionLocal

/-- The ordinary ideal (p) in ℤ. `Mathlib.RingTheory.Ideal.Int`. -/
def rationalIdeal (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

variable (F : IntermediateField ℚ Galois.Qbar) [NumberField F] [IsGalois ℚ F]

/-- The native arithmetic Frobenius choice, with no extra class-field data.
Mathlib `arithFrobAt`. -/
def arithFrob (P : Prime F) : F ≃ₐ[ℚ] F :=
  arithFrobAt ℤ (F ≃ₐ[ℚ] F) P.asIdeal

/-- Mathlib `Int.liesOver_span_absNorm`, specialized to the concrete `primeBelow`. -/
theorem liesOver_primeBelow (P : Prime F) :
    P.asIdeal.LiesOver (rationalIdeal (primeBelow F P)) := by
  exact ⟨(under_eq_span_primeBelow F P).symm⟩

/-- Mathlib `IsArithFrobAt.exists_of_isInvariant`. Existence does not require nonramification. -/
theorem exists_frobenius (P : Prime F) :
    ∃ σ : F ≃ₐ[ℚ] F, IsArithFrobAt ℤ σ P.asIdeal := by
  exact IsArithFrobAt.exists_of_isInvariant ℤ (F ≃ₐ[ℚ] F) P.asIdeal

/-- Mathlib `IsArithFrobAt.arithFrobAt`, using the actual integral-ring Galois action. -/
theorem arithFrob_spec (P : Prime F) :
    IsArithFrobAt ℤ (arithFrob F P) P.asIdeal := by
  exact IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) P.asIdeal

/-- Mathlib `IsArithFrobAt.mem_stabilizer` and `IsArithFrobAt.arithFrobAt_mem_stabilizer`. -/
theorem arithFrob_mem_stabilizer (P : Prime F) :
    arithFrob F P ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) P.asIdeal := by
  exact (arithFrob_spec F P).mem_stabilizer

/-- Same stabilizer assertion as equality of actual ideals. -/
theorem arithFrob_smul_prime (P : Prime F) :
    arithFrob F P • P.asIdeal = P.asIdeal := by
  exact MulAction.mem_stabilizer_iff.mp (arithFrob_mem_stabilizer F P)

/-- Mathlib `AlgHom.IsArithFrobAt`, with base residue cardinality computed by
Mathlib `Int.card_ideal_quot`. The exponent is p, not p^f or an inverse Frobenius. -/
theorem arithFrob_sub_pow_mem (P : Prime F) (p : ℕ) (hp : p.Prime)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) (x : 𝓞 F) :
    arithFrob F P • x - x ^ p ∈ P.asIdeal := by
  simpa only [MulSemiringAction.toAlgHom_apply, base_quotient_card F P,
    primeBelow_eq_of_liesOver F P p hp hP]
    using arithFrob_spec F P x

/-- Mathlib `AlgHom.IsArithFrobAt.mk_apply`, in literal residue-ring form. -/
theorem quotient_mk_arithFrob (P : Prime F) (x : 𝓞 F) :
    Ideal.Quotient.mk P.asIdeal (arithFrob F P • x) =
      (Ideal.Quotient.mk P.asIdeal x) ^ primeBelow F P := by
  simpa only [MulSemiringAction.toAlgHom_apply, base_quotient_card F P]
    using (arithFrob_spec F P).mk_apply x

/-- `Mathlib.RingTheory.Frobenius`: the induced residue map is the p-power map. -/
theorem residue_frobenius_apply (P : Prime F) (x : (𝓞 F) ⧸ P.asIdeal) :
    (arithFrob_spec F P).restrict x = x ^ primeBelow F P := by
  simpa only [base_quotient_card F P] using (arithFrob_spec F P).restrict_apply x

/-- Stabilizer action on the valuation ring; no global integrality
or nonramification premise is imposed on the field element. -/
theorem localIntegral_arithFrob_iff (P : Prime F) (x : F) :
    localIntegral F P (arithFrob F P x) ↔ localIntegral F P x := by
  let σ := arithFrob F P
  have hfix : σ • P.asIdeal = P.asIdeal := arithFrob_smul_prime F P
  have hmem (s : 𝓞 F) : σ • s ∈ P.asIdeal ↔ s ∈ P.asIdeal := by
    simpa only [hfix] using (Ideal.smul_mem_pointwise_smul_iff
      (a := σ) (S := P.asIdeal) (x := s))
  constructor
  · intro hx
    obtain ⟨a, s, hs, hx⟩ := (localIntegral_iff_fraction F P _).mp hx
    refine (localIntegral_iff_fraction F P x).mpr ⟨σ⁻¹ • a, σ⁻¹ • s, ?_, ?_⟩
    · intro h
      apply hs
      have h' := (hmem (σ⁻¹ • s)).mpr h
      simpa only [smul_inv_smul] using h'
    · have h := congrArg σ.symm hx
      change σ.symm (σ x) = _ at h
      change x = σ.symm (a : F) / σ.symm (s : F)
      simpa only [AlgEquiv.symm_apply_apply, map_div₀] using h
  · intro hx
    obtain ⟨a, s, hs, hx⟩ := (localIntegral_iff_fraction F P x).mp hx
    refine (localIntegral_iff_fraction F P _).mpr ⟨σ • a, σ • s, ?_, ?_⟩
    · exact fun h => hs ((hmem s).mp h)
    · change σ x = σ (a : F) / σ (s : F)
      simpa only [map_div₀] using congrArg σ hx

/-- Extension of the integer-ring congruence to locally integral fractions,
by clearing denominators. [RW-rec, Prop. 4]. -/
theorem arithFrob_congruentAt (P : Prime F) (x : F)
    (hx : localIntegral F P x) :
    congruentAt F P (arithFrob F P x) (x ^ primeBelow F P) := by
  let σ := arithFrob F P
  let p := primeBelow F P
  obtain ⟨a, s, hs, rfl⟩ := (localIntegral_iff_fraction F P x).mp hx
  have hσs : σ • s ∉ P.asIdeal := by
    intro h
    apply hs
    have hfix : σ • P.asIdeal = P.asIdeal := arithFrob_smul_prime F P
    have hmem : σ • s ∈ P.asIdeal ↔ s ∈ P.asIdeal := by
      simpa only [hfix] using
        (Ideal.smul_mem_pointwise_smul_iff (a := σ) (S := P.asIdeal) (x := s))
    exact hmem.mp h
  have hsp : s ^ p ∉ P.asIdeal := fun h => hs (P.isPrime.mem_of_pow_mem p h)
  have hden : (σ • s) * s ^ p ∉ P.asIdeal := fun h =>
    (P.isPrime.mem_or_mem h).elim hσs hsp
  have hs0 : (s : F) ≠ 0 := by
    intro h
    apply hs
    have h' : s = 0 := NumberField.RingOfIntegers.coe_eq_zero_iff.mp h
    simpa only [h'] using P.asIdeal.zero_mem
  have hσs0 : σ (s : F) ≠ 0 := by
    intro h
    apply hs0
    apply σ.injective
    simpa only [map_zero] using h
  refine (congruentAt_iff_fraction F P _ _).mpr
    ⟨(σ • a) * s ^ p, a ^ p * (σ • s), (σ • s) * s ^ p, hden, ?_, ?_, ?_⟩
  · change σ ((a : F) / (s : F)) =
      (σ (a : F) * (s : F) ^ p) / (σ (s : F) * (s : F) ^ p)
    rw [map_div₀]
    field_simp
  · change ((a : F) / (s : F)) ^ p =
      ((a : F) ^ p * σ (s : F)) / (σ (s : F) * (s : F) ^ p)
    rw [div_pow]
    field_simp
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow]
    have ha := quotient_mk_arithFrob F P a
    have hs' := quotient_mk_arithFrob F P s
    change Ideal.Quotient.mk P.asIdeal (σ • a) =
      (Ideal.Quotient.mk P.asIdeal a) ^ p at ha
    change Ideal.Quotient.mk P.asIdeal (σ • s) =
      (Ideal.Quotient.mk P.asIdeal s) ^ p at hs'
    rw [ha, hs', sub_self]

/-- Mathlib `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`, `apply_of_pow_eq_one`.
The premise is p ∤ m, not p^f ∤ m. -/
theorem arithFrob_rootOfUnity_integer (P : Prime F) (ζ : 𝓞 F) (m : ℕ)
    (hζ : ζ ^ m = 1) (hm : ¬ primeBelow F P ∣ m) :
    arithFrob F P • ζ = ζ ^ primeBelow F P := by
  simpa only [MulSemiringAction.toAlgHom_apply, base_quotient_card F P] using
    (arithFrob_spec F P).apply_of_pow_eq_one hζ ((natCast_not_mem_iff F P m).mpr hm)

/-- Same exact root-of-unity action in F, after integrality of ζ.
m=0 is excluded automatically by the divisibility hypothesis. -/
theorem arithFrob_rootOfUnity (P : Prime F) (ζ : F) (m : ℕ)
    (hζ : ζ ^ m = 1) (hm : ¬ primeBelow F P ∣ m) :
    arithFrob F P ζ = ζ ^ primeBelow F P := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => hm (h ▸ dvd_zero _)
  have hζint : IsIntegral ℤ ζ :=
    IsIntegral.of_pow hm0 (hζ ▸ isIntegral_one)
  let ζint : 𝓞 F := ⟨ζ, hζint⟩
  have hζintpow : ζint ^ m = 1 := by
    apply Subtype.ext
    exact (map_pow (algebraMap (𝓞 F) F) ζint m).trans hζ
  have h := arithFrob_rootOfUnity_integer F P ζint m hζintpow hm
  exact congrArg (fun z : 𝓞 F => (z : F)) h

end SICLean.L5.FrobeniusPrimes

#check @arithFrobAt
#check @IsArithFrobAt.arithFrobAt
#check @AlgHom.IsArithFrobAt.apply_of_pow_eq_one
#print SICLean.L5.FrobeniusPrimes.arithFrob
