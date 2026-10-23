import SICLean.L5.ClassFieldExistence
import SICLean.L5.ClassFieldTransportAux

set_option autoImplicit false

/-!
# Transport of the realization into the fixed Qbar

The field K is [RW26, p. 20]. [RW-rec] is applied in an ambient algebraic
closure. The chosen realization lies in `SeparableClosure K` and is transported
along the inclusion of `ActualField.baseField` into Qbar.
Uniqueness here is for embeddings over K.
-/

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory
open SICLean.L5.ClassFieldModulus SICLean.L5.ClassFieldExistence

namespace SICLean.L5.ClassFieldTransport

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (n : ℕ)

def inclusion : Hsep M hM n →ₐ[Base M hM] Galois.Qbar := IsSepClosed.lift

def fieldOverBase : IntermediateField (Base M hM) Galois.Qbar :=
  (inclusion M hM n).fieldRange

def qbarField : IntermediateField ℚ Galois.Qbar :=
  (fieldOverBase M hM n).restrictScalars ℚ

abbrev H := qbarField M hM n

instance (priority := 1200) hAlgebra : Algebra (Base M hM) (H M hM n) :=
  (fieldOverBase M hM n).toSubalgebra.algebra

instance (priority := 1200) hModule : Module (Base M hM) (H M hM n) :=
  (hAlgebra M hM n).toModule

def fieldEquiv : Hsep M hM n ≃ₐ[Base M hM] H M hM n :=
  (inclusion M hM n).equivFieldRange

/-- The pre-existing baseField inclusion is the base map of this lift. -/
theorem inclusion_base (x : Base M hM) :
    inclusion M hM n (algebraMap (Base M hM) (Hsep M hM n) x) =
      (x : Galois.Qbar) := by
  exact (inclusion M hM n).commutes x

theorem base_le : ActualField.baseField M hM ≤ qbarField M hM n := by
  intro x hx
  exact (fieldOverBase M hM n).algebraMap_mem ⟨x, hx⟩

theorem fieldEquiv_coe (x : Hsep M hM n) :
    (fieldEquiv M hM n x : Galois.Qbar) = inclusion M hM n x := by
  rfl

/-- By `AlgHom.fieldRange_eq_of_normal`, the image is independent of the
chosen embedding over K. -/
theorem image_independent (j : Hsep M hM n →ₐ[Base M hM] Galois.Qbar) :
    j.fieldRange = fieldOverBase M hM n := by
  exact AlgHom.fieldRange_eq_of_normal j (inclusion M hM n)

/-- Combine same-closure realization uniqueness with normal-image uniqueness. -/
theorem realization_image_unique
    (R : RayClassSubgroupRealization (Base M hM) (modulus M hM n) ⊥)
    (j : R.extension →ₐ[Base M hM] Galois.Qbar) :
    j.fieldRange = fieldOverBase M hM n := by
  let e : R.extension ≃ₐ[Base M hM] Hsep M hM n :=
    IntermediateField.equivOfEq (realization_field_unique M hM n R)
  have h := image_independent M hM n (j.comp e.symm.toAlgHom)
  rw [← AlgHom.map_fieldRange, AlgEquiv.fieldRange_eq_top,
    ← AlgHom.fieldRange_eq_map] at h
  exact h

theorem finiteDimensional : FiniteDimensional (Base M hM) (H M hM n) := by
  exact (fieldEquiv M hM n).toLinearEquiv.finiteDimensional
attribute [instance] finiteDimensional

theorem numberField : NumberField (H M hM n) := by
  exact NumberField.of_module_finite (Base M hM) (H M hM n)
attribute [instance] numberField

/-- Transport along fieldEquiv using Mathlib's IsAbelianGalois.of_algHom. -/
theorem abelianGalois : IsAbelianGalois (Base M hM) (H M hM n) := by
  exact IsAbelianGalois.of_algHom (fieldEquiv M hM n).symm.toAlgHom
attribute [instance] abelianGalois

def artinEquiv : RayGroup M hM n ≃* (H M hM n ≃ₐ[Base M hM] H M hM n) :=
  (ClassFieldExistence.artinEquiv M hM n).trans
    (AlgEquiv.autCongr (fieldEquiv M hM n))

def artin : RayGroup M hM n →* (H M hM n ≃ₐ[Base M hM] H M hM n) :=
  (artinEquiv M hM n).toMonoidHom

def primeTransport (w : HeightOneSpectrum (𝓞 (Hsep M hM n))) :
    Ideal (𝓞 (H M hM n)) :=
  w.asIdeal.map (RingOfIntegers.mapRingEquiv (fieldEquiv M hM n).toRingEquiv)

def complexEmbedding : H M hM n →+* ℂ :=
  Galois.embed.toRingHom.comp (qbarField M hM n).val.toRingHom

/-- The actual Artin action on the same embedded element. -/
theorem artin_transport (a : RayGroup M hM n) (x : Hsep M hM n) :
    (artin M hM n a (fieldEquiv M hM n x) : Galois.Qbar) =
      inclusion M hM n (ClassFieldExistence.artin M hM n a x) := by
  change (AlgEquiv.autCongr (fieldEquiv M hM n)
    (ClassFieldExistence.artinEquiv M hM n a) (fieldEquiv M hM n x) : Galois.Qbar) = _
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]
  rfl

theorem artin_surjective : Function.Surjective (artin M hM n) := by
  exact (artinEquiv M hM n).surjective

theorem artin_ker : (artin M hM n).ker = ⊥ := by
  exact (artin M hM n).ker_eq_bot (artinEquiv M hM n).injective

/-- Ideals and the lies-over relation are transported with the field,
not reselected independently. The integral map is RingOfIntegers.mapRingEquiv. -/
theorem primeTransport_liesOver (v : HeightOneSpectrum (𝓞 (Base M hM)))
    (w : HeightOneSpectrum (𝓞 (Hsep M hM n)))
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    (primeTransport M hM n w).IsPrime ∧ primeTransport M hM n w ≠ ⊥ ∧
      (primeTransport M hM n w).LiesOver v.asIdeal := by
  let e := RingOfIntegers.mapAlgEquiv (fieldEquiv M hM n)
  change (w.asIdeal.map e).IsPrime ∧ w.asIdeal.map e ≠ ⊥ ∧
    (w.asIdeal.map e).LiesOver v.asIdeal
  exact ⟨Ideal.map_isPrime_of_equiv e,
    (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr w.ne_bot,
    Ideal.LiesOver.of_eq_map_equiv v.asIdeal e rfl⟩

/-- Transport of the unramified-outside-modulus property, including all primes
above a good base prime. Source: the chosen realization's same-named field. -/
theorem unramifiedOutside :
    IsUnramifiedOutsideModulus (Base M hM) (H M hM n) (modulus M hM n) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    exact ClassFieldTransportAux.isUnramifiedIn_of_algEquiv
      (RingOfIntegers.mapAlgEquiv (fieldEquiv M hM n)) v.asIdeal
      ((ClassFieldExistence.unramifiedOutside M hM n).1 v hv)
  · intro v hv hnot
    exact (hnot (Finset.mem_univ _)).elim

set_option maxHeartbeats 1600000 in
/-- Frobenius normalization after transport, at every prime above v. -/
theorem artin_prime_arithFrobAt (v : HeightOneSpectrum (𝓞 (Base M hM)))
    (hv : v ∉ (modulus M hM n).finitePart.support)
    (w : HeightOneSpectrum (𝓞 (H M hM n)))
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    artin M hM n (rayClassOfFinitePrime (modulus M hM n) v hv) =
      arithFrobAt (𝓞 (Base M hM)) (H M hM n ≃ₐ[Base M hM] H M hM n)
        w.asIdeal := by
  let e := RingOfIntegers.mapAlgEquiv (fieldEquiv M hM n)
  let w₀ : HeightOneSpectrum (𝓞 (Hsep M hM n)) :=
    (HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv).symm w
  have hmap : w.asIdeal = w₀.asIdeal.map e := by
    exact (Ideal.map_comap_eq_self_of_equiv e w.asIdeal).symm
  have hw₀ : w₀.asIdeal.LiesOver v.asIdeal := by
    change (w.asIdeal.comap e).LiesOver v.asIdeal
    infer_instance
  have hunram := (unramifiedOutside M hM n).1 v hv w.asIdeal inferInstance hw
  change AlgEquiv.autCongr (fieldEquiv M hM n)
    (ClassFieldExistence.artinEquiv M hM n
      (rayClassOfFinitePrime (modulus M hM n) v hv)) = _
  rw [ClassFieldExistence.artinEquiv_apply,
    ClassFieldExistence.artin_prime_arithFrobAt M hM n v hv w₀ hw₀]
  exact ClassFieldTransportAux.arithFrobAt_autCongr
    (fieldEquiv M hM n) w₀ w hmap hunram

/-- Infinite places are transported by this specified complex embedding. -/
theorem complexEmbedding_base (x : Base M hM) :
    complexEmbedding M hM n (algebraMap (Base M hM) (H M hM n) x) =
      (ActualField.sigma₁ M hM x : ℂ) := by
  change Galois.embed ((algebraMap (Base M hM) (H M hM n) x : H M hM n) :
    Galois.Qbar) = ((Galois.embed (x : Galois.Qbar)).re : ℂ)
  change Galois.embed (x : Galois.Qbar) = _
  exact (Complex.re_add_im (Galois.embed (x : Galois.Qbar))).symm.trans (by
    rw [(ActualField.baseField_isRealQuadratic M hM).real x,
      Complex.ofReal_zero, zero_mul, add_zero])

end SICLean.L5.ClassFieldTransport

#check @AlgHom.fieldRange_of_normal
#check @AlgEquiv.autCongr
#print SICLean.L5.ClassFieldTransport.qbarField
