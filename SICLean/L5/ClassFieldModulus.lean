import SICLean.L5.ActualQuadraticField
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupExistence
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus

set_option autoImplicit false

/-!
# The actual integer modulus, with both real places

K is `ActualField.baseField`, with its embedding into Qbar.
Sources: [RW-rec, §8]; the quadratic field is [RW26, p. 20].
-/

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory

namespace SICLean.L5.ClassFieldModulus

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)

abbrev Base := ActualField.baseField M hM

def realEmbedding (i : Fin 2) : Base M hM →+* ℝ :=
  if i = 0 then ActualField.sigma₁ M hM else ActualField.sigma₂ M hM

def complexEmbedding (i : Fin 2) : Base M hM →+* ℂ :=
  Complex.ofRealHom.comp (realEmbedding M hM i)

/-- Mathlib InfinitePlace.Basic, real embeddings; actual-field dictionary above. -/
theorem complexEmbedding_isReal (i : Fin 2) :
    NumberField.ComplexEmbedding.IsReal (complexEmbedding M hM i) := by
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  simp [complexEmbedding]

/-- The place is constructed from the specified embedding, not chosen by an Artin law. -/
theorem place_isReal (i : Fin 2) :
    (InfinitePlace.mk (complexEmbedding M hM i)).IsReal := by
  exact InfinitePlace.isReal_mk_iff.mpr (complexEmbedding_isReal M hM i)

def realPlace (i : Fin 2) : RayClassRealPlace (Base M hM) :=
  ⟨InfinitePlace.mk (complexEmbedding M hM i), place_isReal M hM i⟩

def finiteExponent (n : ℕ) (v : HeightOneSpectrum (𝓞 (Base M hM))) : ℕ :=
  (Associates.mk v.asIdeal).count
    (Associates.mk (Ideal.span ({(n : 𝓞 (Base M hM))} : Set _))).factors

/-- `Ideal.finite_factors`: the support is finite, including at n = 0.
The arithmetic statements use positive n. -/
theorem finiteExponent_support_finite (n : ℕ) :
    (Function.support (finiteExponent M hM n)).Finite := by
  classical
  let I : Ideal (𝓞 (Base M hM)) :=
    Ideal.span ({(n : 𝓞 (Base M hM))} : Set _)
  by_cases hI : I = 0
  · have hz : finiteExponent M hM n = 0 := by
      funext v
      change (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
      rw [hI, Associates.mk_zero, Associates.factors_zero, Associates.count,
        dite_eq_left v.associates_irreducible]
      rfl
    rw [hz]
    simp
  · have hs : Function.support (finiteExponent M hM n) =
        {v : HeightOneSpectrum (𝓞 (Base M hM)) | v.asIdeal ∣ I} := by
      ext v
      change (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 ↔ _
      exact Associates.count_ne_zero_iff_dvd hI v.irreducible
    rw [hs]
    exact Ideal.finite_factors hI

def modulus (n : ℕ) : RayClassModulus (Base M hM) where
  finitePart := Finsupp.ofSupportFinite (finiteExponent M hM n)
    (finiteExponent_support_finite M hM n)
  infinitePart := Finset.univ

abbrev RayGroup (n : ℕ) := RayClassGroup (modulus M hM n)
abbrev RayIdeal (n : ℕ) := rayClassPrimeToIdeals (modulus M hM n)

def idealClass (n : ℕ) : RayIdeal M hM n →* RayGroup M hM n :=
  QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo (modulus M hM n))

/-- InfinitePlace.embedding_of_isReal agrees with the actual signed embedding. -/
theorem realPlace_embedding (i : Fin 2) :
    (realPlace M hM i).1.embedding_of_isReal (realPlace M hM i).2 =
      realEmbedding M hM i := by
  ext x
  change ((InfinitePlace.mk (complexEmbedding M hM i)).embedding x).re = _
  rw [InfinitePlace.embedding_mk_eq_of_isReal (complexEmbedding_isReal M hM i)]
  rfl

/-- The quadratic field has two distinct real places. [RW-rec, Def. 1]; [RW26, p. 20]. -/
theorem realPlace_ne : realPlace M hM 0 ≠ realPlace M hM 1 := by
  intro h
  have he := congrArg (fun v : RayClassRealPlace (Base M hM) =>
    v.1.embedding_of_isReal v.2) h
  rw [realPlace_embedding, realPlace_embedding] at he
  have hepsilon := RingHom.congr_fun he (ActualField.epsilon M hM)
  simp only [realEmbedding, Fin.isValue, ↓reduceIte,
    one_ne_zero, ActualField.sigma₂_epsilon] at hepsilon
  have hgt := ActualField.epsilon_gt_one M hM
  have hnonzero := ne_of_gt (lt_trans zero_lt_one hgt)
  have hmul := mul_inv_cancel₀ hnonzero
  rw [← hepsilon] at hmul
  nlinarith

/-- Every real place is one of these two. -/
theorem realPlace_exhaustive (v : RayClassRealPlace (Base M hM)) :
    v = realPlace M hM 0 ∨ v = realPlace M hM 1 := by
  by_contra hv
  push Not at hv
  have hcard := InfinitePlace.card_add_two_mul_card_eq_rank (Base M hM)
  rw [(ActualField.baseField_isRealQuadratic M hM).degree_two] at hcard
  have hle : 3 ≤ Fintype.card (RayClassRealPlace (Base M hM)) := by
    calc
      3 = ({realPlace M hM 0, realPlace M hM 1, v} :
          Finset (RayClassRealPlace (Base M hM))).card := by
        simp [realPlace_ne M hM, Ne.symm hv.1, Ne.symm hv.2]
      _ ≤ _ := Finset.card_le_card (Finset.subset_univ _)
  change Fintype.card (RayClassRealPlace (Base M hM)) +
    2 * InfinitePlace.nrComplexPlaces (Base M hM) = 2 at hcard
  omega

/-- The finite part of the modulus. [RW-rec, §8]. -/
theorem modulus_finitePart (n : ℕ) (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    (modulus M hM n).finitePart v = finiteExponent M hM n v := by
  rfl

/-- Both real places, including when their eventual sign classes are trivial. -/
theorem modulus_infinitePart (n : ℕ) :
    (modulus M hM n).infinitePart =
      {realPlace M hM 0, realPlace M hM 1} := by
  ext v
  simpa only [modulus, Finset.mem_univ, Finset.mem_insert,
    Finset.mem_singleton, true_iff] using realPlace_exhaustive M hM v

/-- At finite modulus 1 this is `narrowRayClassModulus`. -/
theorem modulus_at_one :
    modulus M hM 1 = narrowRayClassModulus (Base M hM) := by
  apply RayClassModulus.ext
  · apply Finsupp.ext
    intro v
    simp only [modulus, narrowRayClassModulus, Finsupp.ofSupportFinite_coe,
      Finsupp.coe_zero, Pi.zero_apply, finiteExponent, Nat.cast_one]
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one,
      Associates.factors_one, Associates.count_zero v.associates_irreducible]
  · rfl

/-- Exact bad-prime test for n O_K, with the necessary n>0 hypothesis. -/
theorem support_iff (n : ℕ) (hn : 0 < n)
    (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    v ∈ (modulus M hM n).finitePart.support ↔ (n : 𝓞 (Base M hM)) ∈ v.asIdeal :=
  by
    have hI : Ideal.span ({(n : 𝓞 (Base M hM))} : Set _) ≠ 0 := by
      simpa only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot,
        Nat.cast_eq_zero] using Nat.ne_of_gt hn
    rw [Finsupp.mem_support_iff, modulus_finitePart]
    change (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span ({(n : 𝓞 (Base M hM))} : Set _))).factors ≠ 0 ↔ _
    rw [Associates.count_ne_zero_iff_dvd hI v.irreducible,
      Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]

/-- The ray class group is finite, by `rayClassGroup_finite`. -/
theorem rayGroup_finite (n : ℕ) : Finite (RayGroup M hM n) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal
    (Base M hM) (modulus M hM n)
  let : Finite (RayClass.RayClassGroup m') := inferInstance
  exact Finite.of_equiv (RayClass.RayClassGroup m')
    (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
      (Base M hM) (modulus M hM n)).symm.toEquiv

/-- The ideal quotient map is surjective. -/
theorem idealClass_surjective (n : ℕ) :
    Function.Surjective (idealClass M hM n) := by
  exact QuotientGroup.mk'_surjective _

/-- Positive-generator criterion `mem_rayPrincipalIdealSubgroup_iff`. -/
theorem idealClass_eq_one_iff (n : ℕ) (a : RayIdeal M hM n) :
    idealClass M hM n a = 1 ↔
      ∃ x : (Base M hM)ˣ, IsRayCongruent (modulus M hM n) x ∧
        toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x = a.1 := by
  change (a : RayClassGroup (modulus M hM n)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact mem_rayPrincipalIdealSubgroup_iff (modulus M hM n) a.1

theorem realEmbedding_zero : realEmbedding M hM 0 = ActualField.sigma₁ M hM :=
  by simp [realEmbedding]

theorem realEmbedding_one : realEmbedding M hM 1 = ActualField.sigma₂ M hM :=
  by simp [realEmbedding]

end SICLean.L5.ClassFieldModulus

#check @ClassFieldTheory.RayClassModulus
#check @ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff
#print SICLean.L5.ClassFieldModulus.modulus
