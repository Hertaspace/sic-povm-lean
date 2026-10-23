import SICLean.L5.FrobeniusPrimes

set_option autoImplicit false

/-!
# Prime conjugation, Frobenius uniqueness, and subfield restriction

[RW-rec, Prop. 4, pp. 14--15]. Algebraicity of the values is [RW26, Thm. 1, p. 3].
Mathlib: `Frobenius.lean`, `Normal/Defs.lean`, `Normal/Basic.lean`,
`Ideal/Over.lean`, `NumberField/Basic.lean`.

The ideal at a conjugated Frobenius `τστ⁻¹` is `τ(P)`.
Restriction is an automorphism because `H/ℚ` is normal. The chosen
Frobenius equals that restriction when the prime of `H` is unramified.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace SICLean.L5.FrobeniusRestriction

open GoodReductionLocal FrobeniusPrimes

variable (F : IntermediateField ℚ Galois.Qbar) [NumberField F] [IsGalois ℚ F]

/-- The image ideal under `τ`, a nonzero prime. Mathlib `Frobenius.lean`. -/
def conjugatePrime (τ : F ≃ₐ[ℚ] F) (P : Prime F) : Prime F where
  asIdeal := τ • P.asIdeal
  isPrime := by infer_instance
  ne_bot := by
    intro h
    apply P.ne_bot
    calc
      P.asIdeal = τ⁻¹ • (τ • P.asIdeal) := (inv_smul_smul _ _).symm
      _ = ⊥ := by rw [h, Ideal.smul_bot]

/-- The image ideal. -/
theorem conjugatePrime_asIdeal (τ : F ≃ₐ[ℚ] F) (P : Prime F) :
    (conjugatePrime F τ P).asIdeal = τ • P.asIdeal := by
  rfl

/-- Mathlib `Ideal.smul_under`, automorphisms fix the base ℤ. -/
theorem primeBelow_conjugate (τ : F ≃ₐ[ℚ] F) (P : Prime F) :
    primeBelow F (conjugatePrime F τ P) = primeBelow F P := by
  simp only [primeBelow, conjugatePrime, Ideal.under_smul]

/-- The identity acts trivially on prime ideals. -/
theorem conjugatePrime_one (P : Prime F) : conjugatePrime F 1 P = P := by
  apply HeightOneSpectrum.ext
  exact one_smul _ _

/-- The image-ideal convention is a left group action. -/
theorem conjugatePrime_mul (σ τ : F ≃ₐ[ℚ] F) (P : Prime F) :
    conjugatePrime F (σ * τ) P = conjugatePrime F σ (conjugatePrime F τ P) := by
  apply HeightOneSpectrum.ext
  exact mul_smul σ τ P.asIdeal

/-- Mathlib `IsArithFrobAt.conj`.
No uniqueness and no nonramification are needed for this property. -/
theorem isArithFrobAt_conjugate (P : Prime F) (σ τ : F ≃ₐ[ℚ] F)
    (hσ : IsArithFrobAt ℤ σ P.asIdeal) :
    IsArithFrobAt ℤ (τ * σ * τ⁻¹) (conjugatePrime F τ P).asIdeal := by
  exact hσ.conj τ

/-- Invariance of nonramification under an ℤ-algebra automorphism. -/
theorem unramified_conjugate (P : Prime F) (τ : F ≃ₐ[ℚ] F)
    (hP : Algebra.IsUnramifiedAt ℤ P.asIdeal) :
    Algebra.IsUnramifiedAt ℤ (conjugatePrime F τ P).asIdeal := by
  letI := hP
  exact Algebra.FormallyUnramified.of_equiv
    (Localization.localAlgEquiv (τ • P.asIdeal) P.asIdeal
      (MulSemiringAction.toAlgEquiv ℤ (𝓞 F) τ⁻¹)
      (Ideal.pointwise_smul_eq_comap P.asIdeal)).symm

/-- Uniqueness of an arithmetic Frobenius at an unramified prime, using the
faithful action on the ring of integers. Mathlib `Frobenius.lean`. -/
theorem isArithFrobAt_unique (P : Prime F)
    (hP : Algebra.IsUnramifiedAt ℤ P.asIdeal) (σ τ : F ≃ₐ[ℚ] F)
    (hσ : IsArithFrobAt ℤ σ P.asIdeal) (hτ : IsArithFrobAt ℤ τ P.asIdeal) :
    σ = τ := by
  letI := hP
  haveI : FaithfulSMul (F ≃ₐ[ℚ] F) (𝓞 F) :=
    (IsGaloisGroup.of_isFractionRing (F ≃ₐ[ℚ] F) ℤ (𝓞 F) ℚ F).faithful
  exact MulSemiringAction.toAlgHom_injective ℤ (𝓞 F)
    (hσ.eq_of_isUnramifiedAt hτ P.asIdeal.primeCompl_le_nonZeroDivisors)

/-- Equality of the chosen Frobenius elements, by the preceding uniqueness. -/
theorem arithFrob_conjugate (P : Prime F)
    (hP : Algebra.IsUnramifiedAt ℤ P.asIdeal) (τ : F ≃ₐ[ℚ] F) :
    arithFrob F (conjugatePrime F τ P) = τ * arithFrob F P * τ⁻¹ := by
  exact isArithFrobAt_unique F (conjugatePrime F τ P)
    (unramified_conjugate F P τ hP) _ _
    (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) _)
    (isArithFrobAt_conjugate F P (arithFrob F P) τ
      (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) _))

/-- Mathlib `isConj_arithFrobAt`: Mathlib chooses conjugate lifts over the
same base prime even when no unique lift exists. -/
theorem arithFrob_isConj (P Q : Prime F)
    (hPQ : primeBelow F P = primeBelow F Q) :
    IsConj (arithFrob F P) (arithFrob F Q) := by
  apply isConj_arithFrobAt ℤ (F ≃ₐ[ℚ] F) P.asIdeal Q.asIdeal
  calc
    P.asIdeal.under ℤ = Ideal.span {(primeBelow F P : ℤ)} :=
      (Int.ideal_span_absNorm_eq_self _).symm
    _ = Ideal.span {(primeBelow F Q : ℤ)} := by rw [hPQ]
    _ = Q.asIdeal.under ℤ := Int.ideal_span_absNorm_eq_self _

variable (H : IntermediateField ℚ Galois.Qbar) [NumberField H] [IsGalois ℚ H]

/-- Restriction along the inclusion `H ≤ F`.
Mathlib `Normal/Defs.lean`, `IsScalarTower.of_algHom`. -/
def restrictGalois (hHF : H ≤ F) : (F ≃ₐ[ℚ] F) →* (H ≃ₐ[ℚ] H) :=
  letI : Algebra H F := (IntermediateField.inclusion hHF).toAlgebra
  letI : IsScalarTower ℚ H F := IsScalarTower.of_algHom (IntermediateField.inclusion hHF)
  AlgEquiv.restrictNormalHom H

/-- Contraction to `𝓞 H` along the same inclusion.
Mathlib `Ideal/Over.lean`. The ideal is a nonzero prime. -/
def contractPrime (hHF : H ≤ F) (P : Prime F) : Prime H :=
  letI : Algebra H F := (IntermediateField.inclusion hHF).toAlgebra
  { asIdeal := P.asIdeal.under (𝓞 H)
    isPrime := by infer_instance
    ne_bot := by exact Ideal.under_ne_bot (𝓞 H) P.ne_bot }

/-- Mathlib `AlgEquiv.restrictNormal_commutes`, at the common ℚbar embedding. -/
theorem restrictGalois_apply (hHF : H ≤ F) (σ : F ≃ₐ[ℚ] F) (x : H) :
    ((restrictGalois F H hHF σ x : H) : Galois.Qbar) =
      ((σ (IntermediateField.inclusion hHF x) : F) : Galois.Qbar) := by
  letI : Algebra H F := (IntermediateField.inclusion hHF).toAlgebra
  letI : IsScalarTower ℚ H F := IsScalarTower.of_algHom (IntermediateField.inclusion hHF)
  exact congrArg (fun y : F => (y : Galois.Qbar))
    (AlgEquiv.restrictNormal_commutes σ H x)

/-- Transitivity of ideal contraction, `Mathlib.RingTheory.Ideal.Over`. -/
theorem primeBelow_contractPrime (hHF : H ≤ F) (P : Prime F) :
    primeBelow H (contractPrime F H hHF P) = primeBelow F P := by
  letI : Algebra H F := (IntermediateField.inclusion hHF).toAlgebra
  change Ideal.absNorm ((P.asIdeal.under (𝓞 H)).under ℤ) =
    Ideal.absNorm (P.asIdeal.under ℤ)
  rw [Ideal.under_under]

/-- The Frobenius congruence restricts to the subfield.
Nonramification is not a hypothesis of this statement. -/
theorem isArithFrobAt_restrict (hHF : H ≤ F) (P : Prime F) (σ : F ≃ₐ[ℚ] F)
    (hσ : IsArithFrobAt ℤ σ P.asIdeal) :
    IsArithFrobAt ℤ (restrictGalois F H hHF σ) (contractPrime F H hHF P).asIdeal := by
  letI : Algebra H F := (IntermediateField.inclusion hHF).toAlgebra
  letI : IsScalarTower ℚ H F := IsScalarTower.of_algHom (IntermediateField.inclusion hHF)
  have hres (x : 𝓞 H) :
      algebraMap (𝓞 H) (𝓞 F) (restrictGalois F H hHF σ • x) =
        σ • algebraMap (𝓞 H) (𝓞 F) x := by
    apply RingOfIntegers.coe_injective
    exact AlgEquiv.restrictNormal_commutes σ H (x : H)
  intro x
  change algebraMap (𝓞 H) (𝓞 F)
    (restrictGalois F H hHF σ • x -
      x ^ Nat.card (ℤ ⧸ (P.asIdeal.under (𝓞 H)).under ℤ)) ∈ P.asIdeal
  rw [map_sub, map_pow, hres, Ideal.under_under]
  exact hσ (algebraMap (𝓞 H) (𝓞 F) x)

/-- Equality of the selected Frobenius elements uses uniqueness at the
contracted prime. Unramification of the prime of `F` is not a hypothesis. -/
theorem arithFrob_restrict (hHF : H ≤ F) (P : Prime F)
    (hP : Algebra.IsUnramifiedAt ℤ (contractPrime F H hHF P).asIdeal) :
    restrictGalois F H hHF (arithFrob F P) = arithFrob H (contractPrime F H hHF P) := by
  exact isArithFrobAt_unique H (contractPrime F H hHF P) hP _ _
    (isArithFrobAt_restrict F H hHF P (arithFrob F P)
      (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) _))
    (IsArithFrobAt.arithFrobAt ℤ (H ≃ₐ[ℚ] H) _)

/-- Contraction commutes with conjugation in the actual tower. -/
theorem contractPrime_conjugate (hHF : H ≤ F) (P : Prime F) (τ : F ≃ₐ[ℚ] F) :
    contractPrime F H hHF (conjugatePrime F τ P) =
      conjugatePrime H (restrictGalois F H hHF τ) (contractPrime F H hHF P) := by
  letI : Algebra H F := (IntermediateField.inclusion hHF).toAlgebra
  letI : IsScalarTower ℚ H F := IsScalarTower.of_algHom (IntermediateField.inclusion hHF)
  apply HeightOneSpectrum.ext
  ext x
  change algebraMap (𝓞 H) (𝓞 F) x ∈ τ • P.asIdeal ↔
    x ∈ restrictGalois F H hHF τ • P.asIdeal.under (𝓞 H)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_under]
  have hres : τ⁻¹ • algebraMap (𝓞 H) (𝓞 F) x =
      algebraMap (𝓞 H) (𝓞 F) ((restrictGalois F H hHF τ)⁻¹ • x) := by
    apply RingOfIntegers.coe_injective
    change τ⁻¹ (algebraMap H F (x : H)) =
      algebraMap H F ((restrictGalois F H hHF τ)⁻¹ (x : H))
    rw [← map_inv]
    exact (AlgEquiv.restrictNormal_commutes τ⁻¹ H (x : H)).symm
  rw [hres]

/-- Mathlib `AlgEquiv.restrictNormalHom_surjective`, in the actual finite tower. -/
theorem restrictGalois_surjective (hHF : H ≤ F) :
    Function.Surjective (restrictGalois F H hHF) := by
  letI : Algebra H F := (IntermediateField.inclusion hHF).toAlgebra
  letI : IsScalarTower ℚ H F := IsScalarTower.of_algHom (IntermediateField.inclusion hHF)
  exact AlgEquiv.restrictNormalHom_surjective F

end SICLean.L5.FrobeniusRestriction

#check @IsArithFrobAt.conj
#check @AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt
#check @SICLean.L5.FrobeniusRestriction.arithFrob_restrict
#print SICLean.L5.FrobeniusRestriction.restrictGalois
#print SICLean.L5.FrobeniusRestriction.contractPrime
