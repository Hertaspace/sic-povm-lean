import SICLean.L5.ClassFieldConjugation
import SICLean.L5.ClassFieldSigns
import SICLean.L5.ClassFieldInfiniteAux

set_option autoImplicit false

/-!
# Infinite Artin symbols in the fixed complex embedding

Sources: [RW-rec, Prop. 5, Prop. 7]; [RW26, §2.3, pp. 7--8] for ray and sign
classes, and [RW26, Cor. 1, p. 14] for the analytic identity.
The class-field form of the infinite symbols is recorded here.
The germ, the square root, Φ, and the multiplier keep their existing definitions.
-/

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory
open SICLean.L5.ClassFieldModulus SICLean.L5.ClassFieldTransport
open SICLean.L5.ClassFieldIdealAction SICLean.L5.ClassFieldConjugation
open SICLean.L5.ClassFieldSigns

namespace SICLean.L5.ClassFieldInfinite

def complexConjugation : Galois.QbarAut :=
  (Complex.conjAe.restrictScalars ℚ).restrictNormal Galois.Qbar

/-- Local-global compatibility at a real place, after arithmetic normalization.
Ramified and unramified real places are both included. An unramified real
place has trivial Artin symbol and a real embedding upstairs. -/
theorem local_neg_one_isConj
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : InfinitePlace K) (hv : v.IsReal) (φ : L →+* ℂ)
    (hφ : (InfinitePlace.mk φ).comap (algebraMap K L) = v) :
    NumberField.ComplexEmbedding.IsConj φ
      (GlobalClassFieldTheory.Reciprocity.arithmeticChosenInfinitePlaceArtinMonoidHom
        K L v (-1 : v.Completionˣ)) := by
  classical
  rw [GlobalClassFieldTheory.Reciprocity.arithmeticChosenInfinitePlaceArtinMonoidHom_apply]
  apply NumberField.ComplexEmbedding.IsConj.symm
  let w := chosenInfinitePlaceAbove (L := L) v
  have hw : w.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap (L := L) v
  obtain ⟨g, hg⟩ :=
    InfinitePlace.exists_smul_eq_of_comap_eq (hw.trans hφ.symm)
  by_cases hUnramified : w.IsUnramified K
  · have hwReal : w.IsReal :=
      (InfinitePlace.isUnramified_iff.mp hUnramified).resolve_right (by
        rw [hw]
        exact InfinitePlace.not_isComplex_iff_isReal.mpr hv)
    have hφReal : NumberField.ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.mp
        (hg ▸ (InfinitePlace.isReal_smul_iff.mpr hwReal))
    have hlocal :
        GlobalClassFieldTheory.Reciprocity.chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v (-1 : v.Completionˣ) = 1 := by
      unfold GlobalClassFieldTheory.Reciprocity.chosenInfinitePlaceArtinMonoidHom
        GlobalClassFieldTheory.Reciprocity.infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_left hUnramified]
      rfl
    rw [hlocal]
    exact hφReal.isConjGal_one
  · have hConj :=
      GlobalClassFieldTheory.Reciprocity.chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
        (K := K) (L := L) v hUnramified
    let σ :=
      GlobalClassFieldTheory.Reciprocity.chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v (-1 : v.Completionˣ)
    have hσMem : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w := by
      rw [← InfinitePlace.mk_embedding w, InfinitePlace.mem_stabilizer_mk_iff]
      exact Or.inr hConj
    have hσMem' :
        σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) (InfinitePlace.mk φ) := by
      rw [← hg]
      rw [MulAction.mem_stabilizer_iff] at hσMem ⊢
      calc
        σ • (g • w) = (σ * g) • w := (mul_smul σ g w).symm
        _ = (g * σ) • w := by rw [mul_comm']
        _ = g • (σ • w) := mul_smul g σ w
        _ = g • w := by rw [hσMem]
    have hσNe : σ ≠ 1 :=
      (NumberField.ComplexEmbedding.isConj_ne_one_iff hConj).mpr
        (InfinitePlace.isComplex_iff.mp
          (InfinitePlace.IsRamified.isComplex hUnramified))
    exact (InfinitePlace.mem_stabilizer_mk_iff φ σ).mp hσMem'
      |>.resolve_left hσNe

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (n : ℕ)

def flipEmbedding (τ : Galois.QbarAut) : H M hM n →+* ℂ :=
  Galois.embed.toRingHom.comp (τ.toRingHom.comp (qbarField M hM n).val.toRingHom)

def doubleArtin : H M hM n ≃ₐ[ℚ] H M hM n :=
  (artin M hM n (doubleSign M hM n)).restrictScalars ℚ

/-- The Artin map on idèle classes agrees with the arithmetic global norm residue
for the chosen realization. Rigidity is
`rayArtin_comp_ideleClass_eq_arithmeticGlobalNormResidue`, and the quotient
equivalence is `rayClassGroupEquivOriginalIdele`. -/
theorem artin_ideleClass (x : IdeleClassGroup (Base M hM)) :
    artin M hM n (ideleClassToRay M hM n x) =
      GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
        (Base M hM) (H M hM n) x := by
  let m := GlobalClassFieldComparison.rayClassModulusToOriginal
    (Base M hM) (modulus M hM n)
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
    (Base M hM) (modulus M hM n)
  let a : RayClass.RayClassGroup m →*
      (H M hM n ≃ₐ[Base M hM] H M hM n) :=
    (artin M hM n).comp e.symm.toMonoidHom
  have hprime : ∀ (v : HeightOneSpectrum (𝓞 (Base M hM)))
      (hv : v ∉ m.finitePart.support),
      a (QuotientGroup.mk' m.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup (Base M hM))
          (IdeleGroup.finitePrimeIdele v))) =
        GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := Base M hM) (L := H M hM n) v := by
    intro v hv
    have hvm : v ∉ (modulus M hM n).finitePart.support := hv
    change artin M hM n (e.symm (QuotientGroup.mk' m.congruenceSubgroup
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup (Base M hM))
        (IdeleGroup.finitePrimeIdele v)))) = _
    rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime
      (Base M hM) (modulus M hM n) v hvm]
    simp only [e, MulEquiv.symm_apply_apply]
    let w₀ := _root_.chosenFinitePlaceExtension (L := H M hM n) v
    let w := _root_.finitePlaceExtensionCentre
      (K := Base M hM) (L := H M hM n) v w₀
    have hw : w.asIdeal.LiesOver v.asIdeal :=
      _root_.finitePlaceExtensionCentre_liesOver
        (K := Base M hM) (L := H M hM n) v w₀
    have hunram : Algebra.IsUnramifiedAt (𝓞 (Base M hM)) w.asIdeal :=
      ((ClassFieldTransport.unramifiedOutside M hM n).1 v hvm)
        w.asIdeal inferInstance hw
    exact (artin_prime_arithFrobAt M hM n v hvm w hw).trans
      (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := Base M hM) (L := H M hM n) v w hw hunram).symm
  change a (QuotientGroup.mk' m.congruenceSubgroup x) = _
  exact GlobalClassFieldTheory.GlobalClassFields.rayArtin_comp_ideleClass_eq_arithmeticGlobalNormResidue
    m a hprime x

/-- Arithmetic local-global compatibility at an infinite place. -/
theorem artin_sign_eq_local (i : Fin 2) :
    artin M hM n (signClass M hM n i) =
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenInfinitePlaceArtinMonoidHom
        (Base M hM) (H M hM n) (realPlace M hM i).1
        (-1 : (realPlace M hM i).1.Completionˣ) := by
  rw [signClass, artin_ideleClass]
  exact DFunLike.congr_fun
    (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
      (Base M hM) (H M hM n) (realPlace M hM i).1) (-1)

theorem fixedEmbedding_place_over_first :
    (InfinitePlace.mk (ClassFieldTransport.complexEmbedding M hM n)).comap
        (algebraMap (Base M hM) (H M hM n)) = (realPlace M hM 0).1 := by
  rw [InfinitePlace.comap_mk]
  change InfinitePlace.mk _ = InfinitePlace.mk (ClassFieldModulus.complexEmbedding M hM 0)
  congr 1
  apply RingHom.ext
  intro x
  simpa [ClassFieldModulus.complexEmbedding, realEmbedding_zero] using
    complexEmbedding_base M hM n x

/-- The embedding is `embed ∘ τ` for an automorphism `τ` of Qbar. -/
theorem flipEmbedding_place_over_second (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    (InfinitePlace.mk (flipEmbedding M hM n τ)).comap
        (algebraMap (Base M hM) (H M hM n)) = (realPlace M hM 1).1 := by
  rw [InfinitePlace.comap_mk]
  change InfinitePlace.mk _ = InfinitePlace.mk (ClassFieldModulus.complexEmbedding M hM 1)
  congr 1
  apply RingHom.ext
  intro x
  change Galois.embed (τ (x : Galois.Qbar)) = (realEmbedding M hM 1 x : ℂ)
  rw [realEmbedding_one]
  exact (ActualField.inducesNontrivial_iff M hM τ).mp hτ x

theorem complexConjugation_embed (a : Galois.Qbar) :
    Galois.embed (complexConjugation a) = star (Galois.embed a) := by
  exact (Complex.conjAe.restrictScalars ℚ).restrictNormal_apply Galois.Qbar a

/-- The specified complex conjugation, with trivial sign class allowed. -/
theorem conjugation_restrict_first :
    restriction M hM n complexConjugation =
      (artin M hM n (signClass M hM n 0)).restrictScalars ℚ := by
  have hc := local_neg_one_isConj (realPlace M hM 0).1 (realPlace M hM 0).2
    (ClassFieldTransport.complexEmbedding M hM n) (fixedEmbedding_place_over_first M hM n)
  rw [← artin_sign_eq_local M hM n 0] at hc
  apply AlgEquiv.ext
  intro x
  apply (ClassFieldTransport.complexEmbedding M hM n).injective
  change Galois.embed (restriction M hM n complexConjugation x : Galois.Qbar) = _
  rw [restriction_apply, complexConjugation_embed]
  exact (hc.eq x).symm

/-- Every lift flipping K gives the second real place. -/
theorem flip_conjugation_restrict_second (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    restriction M hM n (τ⁻¹ * complexConjugation * τ) =
      (artin M hM n (signClass M hM n 1)).restrictScalars ℚ := by
  have hc := local_neg_one_isConj (realPlace M hM 1).1 (realPlace M hM 1).2
    (flipEmbedding M hM n τ) (flipEmbedding_place_over_second M hM n τ hτ)
  rw [← artin_sign_eq_local M hM n 1] at hc
  apply AlgEquiv.ext
  intro x
  apply (flipEmbedding M hM n τ).injective
  change Galois.embed (τ (restriction M hM n (τ⁻¹ * complexConjugation * τ) x : Galois.Qbar)) = _
  rw [restriction_apply]
  simp only [AlgEquiv.mul_apply, AlgEquiv.coe_inv, AlgEquiv.apply_symm_apply,
    complexConjugation_embed]
  exact (hc.eq x).symm

/-- Ideal conjugation exchanges the two sign classes. -/
theorem rayAction_sign_flip (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    rayAction M hM n τ (signClass M hM n 0) = signClass M hM n 1 ∧
      rayAction M hM n τ (signClass M hM n 1) = signClass M hM n 0 := by
  have hback : ∀ (σ : Galois.QbarAut),
      Galois.InducesNontrivial (ActualField.baseField M hM) σ →
      rayAction M hM n σ⁻¹ (signClass M hM n 0) = signClass M hM n 1 := by
    intro σ hσ
    apply ClassFieldInfiniteAux.artin_restrict_injective M hM n
    have h := artin_conjugation M hM n σ (signClass M hM n 0)
    rw [← conjugation_restrict_first, ← restriction_mul, ← restriction_mul,
      flip_conjugation_restrict_second M hM n σ hσ] at h
    exact h.symm
  have hs := hback τ hτ
  constructor
  · simpa only [inv_inv] using
      hback τ⁻¹ (ClassFieldInfiniteAux.inducesNontrivial_inv M hM τ hτ)
  · have h := rayAction_inv M hM n τ⁻¹ (signClass M hM n 0)
    simpa only [inv_inv, hs] using h

theorem doubleSign_invariant (ρ : Galois.QbarAut) :
    rayAction M hM n ρ (doubleSign M hM n) = doubleSign M hM n := by
  by_cases hρ : baseAction M hM ρ = 1
  · exact ClassFieldInfiniteAux.rayAction_eq_self_of_baseAction M hM n ρ hρ _
  · obtain ⟨hfirst, hsecond⟩ := rayAction_sign_flip M hM n ρ
      ((ClassFieldInfiniteAux.inducesNontrivial_iff M hM ρ).mpr hρ)
    simpa only [doubleSign, map_mul, hfirst, hsecond] using
      mul_comm (signClass M hM n 1) (signClass M hM n 0)

theorem doubleArtin_sq : doubleArtin M hM n ^ 2 = 1 := by
  change (AlgEquiv.restrictScalarsHom ℚ).comp (artin M hM n) (doubleSign M hM n) ^ 2 = 1
  rw [← map_pow, doubleSign_sq, map_one]

/-- `doubleArtin` is central in Gal(H/Q). -/
theorem doubleArtin_central (σ : H M hM n ≃ₐ[ℚ] H M hM n) :
    σ * doubleArtin M hM n = doubleArtin M hM n * σ := by
  let ρ : Galois.QbarAut := σ.liftNormal Galois.Qbar
  have hρ : restriction M hM n ρ = σ := σ.restrict_liftNormal Galois.Qbar
  have h := artin_conjugation M hM n ρ (doubleSign M hM n)
  rw [doubleSign_invariant] at h
  change restriction M hM n ρ⁻¹ * doubleArtin M hM n *
    restriction M hM n ρ = doubleArtin M hM n at h
  rw [restriction_inv, hρ] at h
  calc
    σ * doubleArtin M hM n = σ * (σ⁻¹ * doubleArtin M hM n * σ) :=
      congrArg (σ * ·) h.symm
    _ = doubleArtin M hM n * σ := by group

/-- The group equation, valid also for t = 1. -/
theorem flip_conjugation_eq_first_mul_double (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    restriction M hM n (τ⁻¹ * complexConjugation * τ) =
      restriction M hM n complexConjugation * doubleArtin M hM n := by
  rw [flip_conjugation_restrict_second M hM n τ hτ, conjugation_restrict_first,
    secondSign_eq_first_mul_double, map_mul]
  rfl

/-- The same equation on an element of the transported class field.
The hypothesis on `a` is membership in that field. -/
theorem flip_conjugation_apply (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ)
    (a : Galois.Qbar) (ha : a ∈ qbarField M hM n) :
    τ⁻¹ (complexConjugation (τ a)) =
      complexConjugation (artin M hM n (doubleSign M hM n) ⟨a, ha⟩ : Galois.Qbar) :=
  by
    have h := congrArg (fun σ : H M hM n ≃ₐ[ℚ] H M hM n =>
      (σ ⟨a, ha⟩ : Galois.Qbar))
        (flip_conjugation_eq_first_mul_double M hM n τ hτ)
    simpa only [AlgEquiv.mul_apply, restriction_apply, doubleArtin,
      AlgEquiv.restrictScalars_apply] using h

end SICLean.L5.ClassFieldInfinite

#check @GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
#check @GlobalClassFieldTheory.Reciprocity.chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
#print SICLean.L5.ClassFieldInfinite.complexConjugation
