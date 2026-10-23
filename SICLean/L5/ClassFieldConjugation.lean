import SICLean.L5.ClassFieldTransport
import SICLean.L5.ClassFieldIdealAction
import SICLean.L5.ClassFieldConjugationAux

set_option autoImplicit false

/-!
# Q-normality and Artin conjugation, with the inverse convention

The conjugate of the field under any automorphism of Qbar is the same subfield.
The orientation is ρ⁻¹ Art(a) ρ = Art(ρ⁻¹ a).
Sources: [RW-rec]; the field K is [RW26, p. 20].
The argument transports the conjugated realization back to `SeparableClosure K`,
uses invariance of the modulus, and applies `rayClassSubgroupRealizations_eq`.
Normality is a conclusion.
-/

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory
open SICLean.L5.ClassFieldModulus SICLean.L5.ClassFieldTransport
open SICLean.L5.ClassFieldIdealAction

namespace SICLean.L5.ClassFieldConjugation

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (n : ℕ)

set_option maxHeartbeats 1200000 in
/-- The field conjugate under any Qbar automorphism has the same underlying subfield. -/
theorem qbarField_map (ρ : Galois.QbarAut) :
    (qbarField M hM n).map ρ.toAlgHom = qbarField M hM n := by
  let E : IntermediateField (Base M hM) Galois.Qbar :=
    ((qbarField M hM n).map ρ.toAlgHom).toSubfield.toIntermediateField (by
      intro x
      obtain ⟨y, rfl⟩ := (baseAction M hM ρ).surjective x
      exact ⟨(y : Galois.Qbar), base_le M hM n y.property,
        (baseAction_apply M hM ρ y).symm⟩)
  let : Algebra (Base M hM) E := E.toSubalgebra.algebra
  let : Module (Base M hM) E := E.toSubalgebra.algebra.toModule
  let e : H M hM n ≃+* E :=
    (IntermediateField.equivMap (qbarField M hM n) ρ.toAlgHom).toRingEquiv
  have he (x : Base M hM) :
      e (algebraMap (Base M hM) (H M hM n) x) =
        algebraMap (Base M hM) E (baseAction M hM ρ x) := by
    apply Subtype.ext
    exact (baseAction_apply M hM ρ x).symm
  let : FiniteDimensional ℚ E := e.toRatAlgEquiv.toLinearEquiv.finiteDimensional
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : FiniteDimensional (Base M hM) E :=
    Module.Finite.of_restrictScalars_finite ℚ (Base M hM) E
  let : IsAbelianGalois (Base M hM) E :=
    ClassFieldConjugationAux.isAbelianGalois_transport
      (baseAction M hM ρ).toRingEquiv e he
  let : Algebra (Base M hM) (SeparableClosure (Base M hM)) :=
    ClassFieldExistence.baseSeparableClosureAlgebra M hM
  let : Module (Base M hM) (SeparableClosure (Base M hM)) :=
    (ClassFieldExistence.baseSeparableClosureAlgebra M hM).toModule
  let j : E →ₐ[Base M hM] SeparableClosure (Base M hM) := IsSepClosed.lift
  let : Algebra (Base M hM) j.fieldRange := j.fieldRange.toSubalgebra.algebra
  let : Module (Base M hM) j.fieldRange :=
    (j.fieldRange.toSubalgebra.algebra).toModule
  let F : FiniteAbelianExtension (Base M hM) :=
    ⟨j.fieldRange, j.equivFieldRange.toLinearEquiv.finiteDimensional,
      ClassFieldConjugationAux.isAbelianGalois_transport
        (RingEquiv.refl _) j.equivFieldRange.toRingEquiv j.equivFieldRange.commutes⟩
  let T : H M hM n ≃+* F := e.trans j.equivFieldRange.toRingEquiv
  have hT (x : Base M hM) :
      T (algebraMap (Base M hM) (H M hM n) x) =
        algebraMap (Base M hM) F (baseAction M hM ρ x) := by
    change j.equivFieldRange (e (algebraMap _ _ x)) = _
    rw [he, j.equivFieldRange.commutes]
  let R := ClassFieldConjugationAux.conjugateRealization M hM n ρ F T hT
  let k : R.extension →ₐ[Base M hM] Galois.Qbar :=
    E.val.comp j.equivFieldRange.symm.toAlgHom
  have hk : k.fieldRange = E := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (j.equivFieldRange.symm y).property
    · intro hx
      refine ⟨j.equivFieldRange ⟨x, hx⟩, ?_⟩
      change (j.equivFieldRange.symm (j.equivFieldRange ⟨x, hx⟩) : Galois.Qbar) = x
      rw [j.equivFieldRange.symm_apply_apply]
  have hE : E = fieldOverBase M hM n :=
    hk.symm.trans (realization_image_unique M hM n R k)
  exact congrArg (IntermediateField.restrictScalars ℚ) hE

/-- Membership form usable before installing normality as an instance. -/
theorem mem_conjugate (ρ : Galois.QbarAut) (x : Galois.Qbar) :
    ρ x ∈ qbarField M hM n ↔ x ∈ qbarField M hM n := by
  calc
    ρ x ∈ qbarField M hM n ↔ ρ x ∈ (qbarField M hM n).map ρ.toAlgHom := by
      rw [qbarField_map M hM n ρ]
    _ ↔ x ∈ qbarField M hM n := IntermediateField.map_mem_map _ _

theorem normal : Normal ℚ (H M hM n) := by
  exact IntermediateField.normal_iff_forall_map_eq'.mpr (qbarField_map M hM n)
attribute [instance] normal

theorem finiteDimensional_rat : FiniteDimensional ℚ (H M hM n) := by
  infer_instance

theorem galois : IsGalois ℚ (H M hM n) := by
  exact { }
attribute [instance] galois

def restriction (ρ : Galois.QbarAut) : H M hM n ≃ₐ[ℚ] H M hM n :=
  ρ.restrictNormal (H M hM n)

theorem restriction_apply (ρ : Galois.QbarAut) (x : H M hM n) :
    (restriction M hM n ρ x : Galois.Qbar) = ρ (x : Galois.Qbar) := by
  exact AlgEquiv.restrictNormal_apply (qbarField M hM n) ρ x

theorem restriction_mul (ρ σ : Galois.QbarAut) :
    restriction M hM n (ρ * σ) = restriction M hM n ρ * restriction M hM n σ :=
  (AlgEquiv.restrictNormalHom (H M hM n)).map_mul ρ σ

theorem restriction_inv (ρ : Galois.QbarAut) :
    restriction M hM n ρ⁻¹ = (restriction M hM n ρ)⁻¹ := by
  exact map_inv (AlgEquiv.restrictNormalHom (H M hM n)) ρ

/-- The orientation is rho^-1 Art(a) rho = Art(rho^-1 a).
The restriction is over Q, so rho may move K. -/
theorem artin_conjugation (ρ : Galois.QbarAut) (a : RayGroup M hM n) :
    restriction M hM n ρ⁻¹ * (artin M hM n a).restrictScalars ℚ *
        restriction M hM n ρ =
      (artin M hM n (rayAction M hM n ρ⁻¹ a)).restrictScalars ℚ := by
  have he (x : Base M hM) :
      restriction M hM n ρ⁻¹ (algebraMap (Base M hM) (H M hM n) x) =
        algebraMap (Base M hM) (H M hM n) (baseAction M hM ρ⁻¹ x) := by
    apply Subtype.ext
    rw [restriction_apply]
    exact (baseAction_apply M hM ρ⁻¹ x).symm
  let C := ClassFieldConjugationAux.semilinearAutCongr
    (baseAction M hM ρ⁻¹).toRingEquiv (restriction M hM n ρ⁻¹).toRingEquiv he
  let f := C.toMonoidHom.comp (artin M hM n)
  let g := (artin M hM n).comp (rayAction M hM n ρ⁻¹)
  let : CommGroup (H M hM n ≃ₐ[Base M hM] H M hM n) :=
    { (inferInstance : Group (H M hM n ≃ₐ[Base M hM] H M hM n)) with
      mul_comm := mul_comm' }
  have hfg : f = g := by
    apply rayClassGroup_hom_ext_finitePrime (Base M hM) (modulus M hM n) f g
    intro v hv
    let w₀ := _root_.chosenFinitePlaceExtension (L := H M hM n) v
    let w := _root_.finitePlaceExtensionCentre (K := Base M hM) (L := H M hM n) v w₀
    have hw : w.asIdeal.LiesOver v.asIdeal :=
      _root_.finitePlaceExtensionCentre_liesOver (K := Base M hM) (L := H M hM n) v w₀
    let eO := RingOfIntegers.mapRingEquiv (restriction M hM n ρ⁻¹).toRingEquiv
    let w' := (HeightOneSpectrum.equivOfRingEquiv eO) w
    have hwmap : w'.asIdeal = w.asIdeal.map eO := Ideal.comap_symm eO
    have hw' : w'.asIdeal.LiesOver (primeAction M hM ρ⁻¹ v).asIdeal := by
      rw [hwmap]
      exact ClassFieldConjugationAux.liesOver_map (integerAction M hM ρ⁻¹) eO
        (ClassFieldConjugationAux.integers_compatible
          (baseAction M hM ρ⁻¹).toRingEquiv (restriction M hM n ρ⁻¹).toRingEquiv he)
        v.asIdeal w.asIdeal hw
    have hv' := (ClassFieldConjugationAux.primeAction_good_iff M hM n ρ⁻¹ v).mpr hv
    let : Algebra.IsUnramifiedAt (𝓞 (Base M hM)) w.asIdeal :=
      (unramifiedOutside M hM n).1 v hv w.asIdeal inferInstance hw
    change C (artin M hM n (rayClassOfFinitePrime (modulus M hM n) v hv)) =
      artin M hM n (rayAction M hM n ρ⁻¹ (rayClassOfFinitePrime (modulus M hM n) v hv))
    rw [ClassFieldConjugationAux.rayAction_finitePrime,
      artin_prime_arithFrobAt M hM n v hv w hw,
      artin_prime_arithFrobAt M hM n (primeAction M hM ρ⁻¹ v) hv' w' hw']
    exact ClassFieldConjugationAux.arithFrobAt_semilinearAutCongr
      (baseAction M hM ρ⁻¹).toRingEquiv (restriction M hM n ρ⁻¹).toRingEquiv he w
  have hs : (restriction M hM n ρ⁻¹).symm = restriction M hM n ρ := by
    change (restriction M hM n ρ⁻¹)⁻¹ = restriction M hM n ρ
    simpa only [inv_inv] using (restriction_inv M hM n ρ⁻¹).symm
  have ha := DFunLike.congr_fun hfg a
  apply AlgEquiv.ext
  intro x
  have hx := congrArg (fun σ : H M hM n ≃ₐ[Base M hM] H M hM n => σ x) ha
  change restriction M hM n ρ⁻¹
    (artin M hM n a ((restriction M hM n ρ⁻¹).symm x)) =
      artin M hM n (rayAction M hM n ρ⁻¹ a) x at hx
  simpa only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, hs] using hx

/-- Same law on elements; this avoids any convention about trans versus multiplication. -/
theorem artin_conjugation_apply (ρ : Galois.QbarAut) (a : RayGroup M hM n)
    (x : H M hM n) :
    ρ⁻¹ (artin M hM n a (restriction M hM n ρ x) : Galois.Qbar) =
      (artin M hM n (rayAction M hM n ρ⁻¹ a) x : Galois.Qbar) := by
  have h := congrArg (fun f : H M hM n ≃ₐ[ℚ] H M hM n =>
    (f x : Galois.Qbar)) (artin_conjugation M hM n ρ a)
  simpa only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply,
    restriction_apply] using h

/-- The same law on an ideal representative. -/
theorem artin_conjugation_ideal (ρ : Galois.QbarAut) (a : RayIdeal M hM n) :
    restriction M hM n ρ⁻¹ *
        (artin M hM n (idealClass M hM n a)).restrictScalars ℚ *
        restriction M hM n ρ =
      (artin M hM n (idealClass M hM n (rayIdealAction M hM n ρ⁻¹ a))).restrictScalars ℚ :=
  by
    simpa only [rayAction_ideal] using
      artin_conjugation M hM n ρ (idealClass M hM n a)

end SICLean.L5.ClassFieldConjugation

#check @ClassFieldTheory.rayClassSubgroupRealizations_eq
#check @AlgEquiv.restrictNormalHom
#print SICLean.L5.ClassFieldConjugation.restriction
