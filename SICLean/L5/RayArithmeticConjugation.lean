import SICLean.L5.RayArithmeticModulus
import SICLean.L5.RayArithmeticConjugationAux
import Mathlib.RingTheory.FractionalIdeal.Operations
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup

set_option autoImplicit false

/-!
# Conjugation on the actual narrow ray class group

Every underlying map is an explicit transport of the quadratic conjugation of the actual
field. The finite modulus is the factorization of the integral ideal `(cm)`, and the
infinite modulus is the specified pair of real places. Source: [RW-rec], for the quadratic
data, the ray ideals and their conjugation, the exchange of sign classes, and the final
real-place identification. No invariance of the actual pseudolattice under
conjugation is assumed, and conjugation on the ray class group is not defined to be
inversion.
-/

noncomputable section
open scoped MatrixGroups NumberField Classical
open NumberField IsDedekindDomain

namespace SICLean.L5.RayArithmeticConjugation

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM

/-- The actual field conjugation on nonzero elements. Source: [RW-rec]. -/
def unitConjugation : Kˣ ≃* Kˣ :=
  Units.mapEquiv (RayArithmeticPlaces.conjugation M hM).toRingEquiv.toMulEquiv

/-- Image of an integral ideal under the specified quadratic conjugation. Source: [RW-rec]. -/
def idealConjugation (a : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  Ideal.map (RayArithmeticPlaces.integerConjugation M hM).toRingHom a

/-- The prime permutation is forward image on ideals: the Mathlib equivalence implements this by
comapping along the inverse ring map. Source: [RW-rec]. -/
def primeConjugation : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.equivOfRingEquiv (RayArithmeticPlaces.integerConjugation M hM)

/-- Precompose the embedding defining a real place by the actual field conjugation; precomposition
preserves realness. Source: [RW-rec]. -/
def realPlaceConjugation (v : ClassFieldTheory.RayClassRealPlace K) :
    ClassFieldTheory.RayClassRealPlace K :=
  ⟨InfinitePlace.mk
      (v.1.embedding.comp (RayArithmeticPlaces.conjugation M hM).toRingHom), by
    apply InfinitePlace.isReal_mk_iff.mpr
    rw [ComplexEmbedding.isReal_iff, ← ComplexEmbedding.conjugate_comp,
      InfinitePlace.conjugate_embedding_eq_of_isReal v.2]⟩

/-- Conjugate a ray modulus by the actual prime permutation and real embedding precomposition.
Source: [RW-rec]. -/
def modulusConjugation (q : ClassFieldTheory.RayClassModulus K) :
    ClassFieldTheory.RayClassModulus K where
  finitePart := Finsupp.mapDomain (primeConjugation M hM) q.finitePart
  infinitePart := q.infinitePart.image (realPlaceConjugation M hM)

/-- Transport fractional ideals by the ring-of-integers conjugation and then pass to their units.
Source: [RW-rec]. -/
def fractionalIdealConjugation :
    ClassFieldTheory.NumberFieldFractionalIdealGroup K ≃*
      ClassFieldTheory.NumberFieldFractionalIdealGroup K :=
  Units.mapEquiv
    (FractionalIdeal.ringEquivOfRingEquiv K K
      (RayArithmeticPlaces.integerConjugation M hM)).toMulEquiv

/-- Source: ideal conjugation, [RW-rec]. [RW26, p. 20]. -/
theorem idealConjugation_involutive :
    Function.Involutive (idealConjugation M hM) := by
  intro a
  unfold idealConjugation
  rw [Ideal.map_map]
  change Ideal.map ((RayArithmeticPlaces.integerConjugation M hM).trans
    (RayArithmeticPlaces.integerConjugation M hM)).toRingHom a = a
  rw [RayArithmeticConjugationAux.integerConjugation_trans]
  simp

/-- Source: the same forward ideal conjugation, [RW-rec]; Mathlib's prime equivalence uses inverse
comap. [RW26, p. 20]. -/
theorem primeConjugation_asIdeal (v : HeightOneSpectrum (𝓞 K)) :
    (primeConjugation M hM v).asIdeal = idealConjugation M hM v.asIdeal := by
  exact RayArithmeticConjugationAux.prime_map _ v

/-- Source: exchange of the two specified real embeddings, [RW-rec]. [RW26, p. 20]. -/
theorem realPlaceConjugation_exchange :
    realPlaceConjugation M hM (RayArithmeticPlaces.realPlace₁ M hM) =
        RayArithmeticPlaces.realPlace₂ M hM ∧
      realPlaceConjugation M hM (RayArithmeticPlaces.realPlace₂ M hM) =
        RayArithmeticPlaces.realPlace₁ M hM := by
  have he₁ : (RayArithmeticPlaces.realPlace₁ M hM).1.embedding =
      RayArithmeticPlaces.complexEmbedding₁ M hM := by
    apply RingHom.ext
    intro x
    rw [← InfinitePlace.embedding_of_isReal_apply (RayArithmeticPlaces.realPlace₁ M hM).2,
      RayArithmeticPlaces.realPlace₁_embedding]
    rfl
  have he₂ : (RayArithmeticPlaces.realPlace₂ M hM).1.embedding =
      RayArithmeticPlaces.complexEmbedding₂ M hM := by
    apply RingHom.ext
    intro x
    rw [← InfinitePlace.embedding_of_isReal_apply (RayArithmeticPlaces.realPlace₂ M hM).2,
      RayArithmeticPlaces.realPlace₂_embedding]
    rfl
  constructor
  · apply Subtype.ext
    change InfinitePlace.mk ((RayArithmeticPlaces.realPlace₁ M hM).1.embedding.comp
      (RayArithmeticPlaces.conjugation M hM).toRingHom) = RayArithmeticPlaces.infinitePlace₂ M hM
    rw [he₁]
    exact congrArg InfinitePlace.mk (RingHom.ext fun x =>
      congrArg Complex.ofReal (RayArithmeticPlaces.sigma₁_conjugation M hM x))
  · apply Subtype.ext
    change InfinitePlace.mk ((RayArithmeticPlaces.realPlace₂ M hM).1.embedding.comp
      (RayArithmeticPlaces.conjugation M hM).toRingHom) = RayArithmeticPlaces.infinitePlace₁ M hM
    rw [he₂]
    exact congrArg InfinitePlace.mk (RingHom.ext fun x =>
      congrArg Complex.ofReal (RayArithmeticPlaces.sigma₂_conjugation M hM x))

/-- Source: the rational integer level is fixed under conjugation, [RW-rec]. [RW26, p. 20]. -/
theorem finiteIdeal_conjugation (m : ℕ) :
    idealConjugation M hM (RayArithmeticModulus.finiteIdeal M hM m) =
      RayArithmeticModulus.finiteIdeal M hM m := by
  simp [idealConjugation, RayArithmeticModulus.finiteIdeal, Ideal.map_span]

/-- Source: conjugation permutes prime factors of `(cm)`, [RW-rec]. [RW26, p. 20]. -/
theorem finitePart_conjugation (m : ℕ) :
    (modulusConjugation M hM (RayArithmeticModulus.modulus M hM m)).finitePart =
      (RayArithmeticModulus.modulus M hM m).finitePart := by
  apply Finsupp.ext
  intro v
  obtain ⟨w, rfl⟩ := (primeConjugation M hM).surjective v
  change (Finsupp.mapDomain (primeConjugation M hM)
    (RayArithmeticModulus.modulus M hM m).finitePart) _ = _
  rw [Finsupp.mapDomain_apply_of_injective (primeConjugation M hM).injective]
  simp only [RayArithmeticModulus.finitePart_apply]
  have h := RayArithmeticConjugationAux.factorization_map
    (RayArithmeticPlaces.integerConjugation M hM) w
    (RayArithmeticModulus.finiteIdeal M hM m)
  change factorization (idealConjugation M hM (RayArithmeticModulus.finiteIdeal M hM m))
    (primeConjugation M hM w).asIdeal = _ at h
  rw [finiteIdeal_conjugation] at h
  exact h.symm

/-- Source: both real places occur in the narrow modulus, [RW-rec]. [RW26, p. 20]. -/
theorem infinitePart_conjugation (m : ℕ) :
    (modulusConjugation M hM (RayArithmeticModulus.modulus M hM m)).infinitePart =
      (RayArithmeticModulus.modulus M hM m).infinitePart := by
  change Finset.image (realPlaceConjugation M hM)
    {RayArithmeticPlaces.realPlace₁ M hM, RayArithmeticPlaces.realPlace₂ M hM} = _
  rw [Finset.image_insert, Finset.image_singleton,
    (realPlaceConjugation_exchange M hM).1, (realPlaceConjugation_exchange M hM).2]
  exact Finset.pair_comm _ _

/-- Source: invariance of the integer narrow modulus, [RW-rec]. [RW26, p. 20]. -/
theorem modulus_conjugation (m : ℕ) :
    modulusConjugation M hM (RayArithmeticModulus.modulus M hM m) =
      RayArithmeticModulus.modulus M hM m := by
  cases h : modulusConjugation M hM (RayArithmeticModulus.modulus M hM m)
  cases hq : RayArithmeticModulus.modulus M hM m
  have hf := finitePart_conjugation M hM m
  have hi := infinitePart_conjugation M hM m
  rw [h, hq] at hf hi
  cases hf
  cases hi
  rfl

/-- Source: finite ray congruence is preserved by quadratic conjugation, [RW-rec]. [RW26, p. 20]. -/
theorem finiteCongruent_conjugation_iff (m : ℕ) (α : Kˣ) :
    RayArithmeticModulus.FiniteCongruent M hM m (unitConjugation M hM α) ↔
      RayArithmeticModulus.FiniteCongruent M hM m α := by
  have hinv : Function.Involutive (unitConjugation M hM) := by
    intro x
    apply Units.ext
    exact RayArithmeticPlaces.conjugation_involutive M hM x
  constructor
  · intro h
    have hh := RayArithmeticConjugationAux.finiteCongruent_conjugation M hM m
      (unitConjugation M hM α) h
    change RayArithmeticModulus.FiniteCongruent M hM m
      (unitConjugation M hM (unitConjugation M hM α)) at hh
    rwa [hinv α] at hh
  · exact RayArithmeticConjugationAux.finiteCongruent_conjugation M hM m α

/-- Source: conjugation preserves nonzero ideals and coprimality to `(cm)`, [RW-rec]. [RW26, p. 20].
-/
theorem idealConjugation_valid_iff (m : ℕ) (a : Ideal (𝓞 K)) :
    (idealConjugation M hM a ≠ ⊥ ↔ a ≠ ⊥) ∧
      (RayArithmeticModulus.CoprimeIdeal M hM m (idealConjugation M hM a) ↔
        RayArithmeticModulus.CoprimeIdeal M hM m a) := by
  have hzero : idealConjugation M hM ⊥ = ⊥ := Ideal.map_bot
  constructor
  · constructor
    · intro h ha
      exact h (ha ▸ hzero)
    · intro h ha
      have hh := congrArg (idealConjugation M hM) ha
      rw [idealConjugation_involutive M hM a, hzero] at hh
      exact h hh
  · change IsCoprime (idealConjugation M hM a) (RayArithmeticModulus.finiteIdeal M hM m) ↔ _
    nth_rw 1 [← finiteIdeal_conjugation M hM m]
    exact RayArithmeticConjugationAux.ideal_map_isCoprime_iff _ _ _

/-- Source: ideals prime to the invariant finite modulus are stable, [RW-rec]. [RW26, p. 20]. -/
theorem primeToIdeals_conjugation (m : ℕ) :
    (ClassFieldTheory.rayClassPrimeToIdeals
        (RayArithmeticModulus.modulus M hM m)).map
        (fractionalIdealConjugation M hM).toMonoidHom =
      ClassFieldTheory.rayClassPrimeToIdeals
        (RayArithmeticModulus.modulus M hM m) := by
  apply RayArithmeticConjugationAux.subgroup_map_eq_of_involutive
  · intro I
    apply Units.ext
    exact RayArithmeticConjugationAux.fractional_conjugation_involutive M hM I
  · intro I hI v hv
    obtain ⟨w, rfl⟩ := (primeConjugation M hM).surjective v
    have hw : w ∈ (RayArithmeticModulus.modulus M hM m).finitePart.support := by
      simpa only [Finsupp.mem_support_iff,
        primeConjugation, RayArithmeticConjugationAux.finitePart_at_conjugate] using hv
    change FractionalIdeal.count K (primeConjugation M hM w)
      (FractionalIdeal.ringEquivOfRingEquiv K K
        (RayArithmeticPlaces.integerConjugation M hM) I.val) = 0
    rw [primeConjugation, RayArithmeticConjugationAux.fractional_count_conjugation]
    exact hI w hw

/-- Concrete restriction to the stable subgroup of ideals prime to the modulus. Source: [RW-rec]. -/
def primeToConjugation (m : ℕ) :
    ClassFieldTheory.rayClassPrimeToIdeals (RayArithmeticModulus.modulus M hM m) ≃*
      ClassFieldTheory.rayClassPrimeToIdeals (RayArithmeticModulus.modulus M hM m) :=
  ((fractionalIdealConjugation M hM).subgroupMap
      (ClassFieldTheory.rayClassPrimeToIdeals
        (RayArithmeticModulus.modulus M hM m))).trans
    (MulEquiv.subgroupCongr (primeToIdeals_conjugation M hM m))

/-- Source: conjugation preserves ray-principal generators and exchanges the positivity conditions,
[RW-rec]. [RW26, p. 20]. -/
theorem principalSubgroup_conjugation (m : ℕ) :
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
        (RayArithmeticModulus.modulus M hM m)).map
        (primeToConjugation M hM m).toMonoidHom =
      ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
        (RayArithmeticModulus.modulus M hM m) := by
  apply RayArithmeticConjugationAux.subgroup_map_eq_of_involutive
  · intro a
    apply Subtype.ext
    apply Units.ext
    exact RayArithmeticConjugationAux.fractional_conjugation_involutive M hM a.val
  · intro a ha
    change a.val ∈ ClassFieldTheory.rayPrincipalIdealSubgroup
      (RayArithmeticModulus.modulus M hM m) at ha
    obtain ⟨α, hα, hprincipal⟩ := (ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff _ _).mp ha
    change (fractionalIdealConjugation M hM a.val) ∈
      ClassFieldTheory.rayPrincipalIdealSubgroup (RayArithmeticModulus.modulus M hM m)
    apply (ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff _ _).mpr
    refine ⟨unitConjugation M hM α, ?_, ?_⟩
    · rw [RayArithmeticModulus.isRayCongruent_iff] at hα ⊢
      refine ⟨(finiteCongruent_conjugation_iff M hM m α).mpr hα.1, ?_, ?_⟩
      · change 0 < ActualField.sigma₁ M hM (RayArithmeticPlaces.conjugation M hM α)
        rw [RayArithmeticPlaces.sigma₁_conjugation]
        exact hα.2.2
      · change 0 < ActualField.sigma₂ M hM (RayArithmeticPlaces.conjugation M hM α)
        rw [RayArithmeticPlaces.sigma₂_conjugation]
        exact hα.2.1
    · change toPrincipalIdeal (𝓞 K) K
        (Units.mapEquiv (RayArithmeticPlaces.conjugation M hM).toRingEquiv.toMulEquiv α) = _
      rw [← RayArithmeticConjugationAux.fractional_principal_conjugation, hprincipal]
      rfl

/-- The induced automorphism of the actual ideal ray-class quotient. Source: [RW-rec]. -/
def rayConjugation (m : ℕ) :
    ClassFieldTheory.RayClassGroup (RayArithmeticModulus.modulus M hM m) ≃*
      ClassFieldTheory.RayClassGroup (RayArithmeticModulus.modulus M hM m) :=
  QuotientGroup.congr
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
      (RayArithmeticModulus.modulus M hM m))
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
      (RayArithmeticModulus.modulus M hM m))
    (primeToConjugation M hM m) (principalSubgroup_conjugation M hM m)

/-- Source: the induced quotient action on its literal representatives, [RW-rec]. [RW26, p. 20]. -/
theorem rayConjugation_mk (m : ℕ)
    (a : ClassFieldTheory.rayClassPrimeToIdeals
      (RayArithmeticModulus.modulus M hM m)) :
    rayConjugation M hM m
        (QuotientGroup.mk'
          (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
            (RayArithmeticModulus.modulus M hM m)) a) =
      QuotientGroup.mk'
        (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
          (RayArithmeticModulus.modulus M hM m))
        (primeToConjugation M hM m a) := by
  rfl

/-- Source: compatibility with actual integral-ideal projection, [RW-rec]. [RW26, p. 20]. -/
theorem rayConjugation_idealClass (m : ℕ) (a : Ideal (𝓞 K))
    (ha : a ≠ ⊥) (hcoprime : RayArithmeticModulus.CoprimeIdeal M hM m a) :
    rayConjugation M hM m
        (RayArithmeticModulus.idealClass M hM m a ha hcoprime) =
      RayArithmeticModulus.idealClass M hM m (idealConjugation M hM a)
        ((idealConjugation_valid_iff M hM m a).1.mpr ha)
        ((idealConjugation_valid_iff M hM m a).2.mpr hcoprime) := by
  unfold RayArithmeticModulus.idealClass
  rw [rayConjugation_mk]
  apply congrArg (QuotientGroup.mk'
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (RayArithmeticModulus.modulus M hM m)))
  apply Subtype.ext
  apply Units.ext
  exact RayArithmeticConjugationAux.fractional_map_coe M hM a

/-- Source: compatibility with the principal fractional ideal of the conjugated generator, [RW-rec].
[RW26, p. 20]. -/
theorem rayConjugation_principalClass (m : ℕ) (α : Kˣ)
    (hfinite : RayArithmeticModulus.FiniteCongruent M hM m α) :
    rayConjugation M hM m
        (RayArithmeticModulus.principalClass M hM m α hfinite) =
      RayArithmeticModulus.principalClass M hM m (unitConjugation M hM α)
        ((finiteCongruent_conjugation_iff M hM m α).mpr hfinite) := by
  unfold RayArithmeticModulus.principalClass
  rw [rayConjugation_mk]
  apply congrArg (QuotientGroup.mk'
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (RayArithmeticModulus.modulus M hM m)))
  apply Subtype.ext
  exact RayArithmeticConjugationAux.fractional_principal_conjugation M hM α

/-- Source: quadratic conjugation has square one on the actual ray-class quotient, [RW-rec]. [RW26,
p. 20]. -/
theorem rayConjugation_involutive (m : ℕ) :
    Function.Involutive (rayConjugation M hM m) := by
  intro x
  induction x using Quotient.inductionOn with
  | h a =>
    change rayConjugation M hM m (rayConjugation M hM m
      (QuotientGroup.mk' _ a)) = QuotientGroup.mk' _ a
    rw [rayConjugation_mk, rayConjugation_mk]
    apply congrArg (QuotientGroup.mk' _)
    apply Subtype.ext
    apply Units.ext
    exact RayArithmeticConjugationAux.fractional_conjugation_involutive M hM a.val

#check @FractionalIdeal.ringEquivOfRingEquiv
#check @QuotientGroup.congr
#print fractionalIdealConjugation
#print rayConjugation

end SICLean.L5.RayArithmeticConjugation
