import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupHomExtFinitePrime
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.RamificationInertia.Unramified
import SICLean.L5.ClassFieldIdealAction
import SICLean.L5.ClassFieldTransport

set_option autoImplicit false

/-!
# Semilinear transport used by class-field conjugation

The field and the base may both move.  All compatibility assumptions below
are commuting squares of the actual algebra maps.
-/

noncomputable section

namespace SICLean.L5.ClassFieldConjugationAux

section Rings

variable {R R' S S' : Type*}
  [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R' S']

/-- Contraction commutes with a compatible pair of ring equivalences. -/
theorem under_map
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (Q : Ideal S) :
    (Q.map eS.toRingHom).under R' = (Q.under R).map eR.toRingHom := by
  ext r'
  change algebraMap R' S' r' ∈ Q.map eS.toRingHom ↔
    r' ∈ (Q.under R).map eR.toRingHom
  have h := he (eR.symm r')
  rw [eR.apply_symm_apply] at h
  have hs : eS.symm (algebraMap R' S' r') ∈ Q ↔
      algebraMap R' S' r' ∈ Q.map eS := Ideal.symm_apply_mem_of_equiv_iff
  have hr : eR.symm r' ∈ Q.under R ↔
      r' ∈ (Q.under R).map eR := Ideal.symm_apply_mem_of_equiv_iff
  refine hs.symm.trans ((?_ : eS.symm (algebraMap R' S' r') ∈ Q ↔
    eR.symm r' ∈ Q.under R).trans hr)
  change eS.symm (algebraMap R' S' r') ∈ Q ↔
    algebraMap R S (eR.symm r') ∈ Q
  rw [← h, eS.symm_apply_apply]

/-- A compatible equivalence sends a prime over `P` to a prime over `eR(P)`. -/
theorem liesOver_map
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (P : Ideal R) (Q : Ideal S) (h : Q.LiesOver P) :
    (Q.map eS).LiesOver (P.map eR) := by
  constructor
  change P.map eR.toRingHom = (Q.map eS.toRingHom).under R'
  rw [under_map eR eS he Q, ← h.over]

/-- The base residue-field cardinality is unchanged by semilinear transport. -/
theorem card_quotient_under_map
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (Q : Ideal S) :
    Nat.card (R' ⧸ (Q.map eS.toRingHom).under R') =
      Nat.card (R ⧸ Q.under R) := by
  exact (Nat.card_congr
    (Ideal.quotientEquiv (Q.under R) ((Q.map eS.toRingHom).under R')
      eR (under_map eR eS he Q)).toEquiv).symm

/-- Transport the defining arithmetic Frobenius congruence through a square
whose base ring is allowed to change. -/
theorem isArithFrobAt_transport
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (φ : S →ₐ[R] S) (φ' : S' →ₐ[R'] S')
    (hφ : ∀ x : S, φ' (eS x) = eS (φ x))
    (Q : Ideal S) (H : φ.IsArithFrobAt Q) :
    φ'.IsArithFrobAt (Q.map eS.toRingHom) := by
  intro x'
  obtain ⟨x, rfl⟩ := eS.surjective x'
  rw [hφ, card_quotient_under_map eR eS he Q, ← map_pow, ← map_sub]
  exact Ideal.mem_map_of_mem eS.toRingHom (H x)

/-- Conjugation of automorphisms by a compatible semilinear ring equivalence. -/
def semilinearAutCongr
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r)) :
    (S ≃ₐ[R] S) ≃* (S' ≃ₐ[R'] S') where
  toFun σ :=
    { eS.symm.trans (σ.toRingEquiv.trans eS) with
      commutes' := by
        intro r'
        change eS (σ (eS.symm (algebraMap R' S' r'))) = algebraMap R' S' r'
        have h := he (eR.symm r')
        rw [eR.apply_symm_apply] at h
        rw [← h, eS.symm_apply_apply, σ.commutes] }
  invFun σ :=
    { eS.trans (σ.toRingEquiv.trans eS.symm) with
      commutes' := by
        intro r
        change eS.symm (σ (eS (algebraMap R S r))) = algebraMap R S r
        rw [he, σ.commutes, ← he, eS.symm_apply_apply] }
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp
  map_mul' σ τ := by ext x; simp

@[simp]
theorem semilinearAutCongr_apply
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (σ : S ≃ₐ[R] S) (x' : S') :
    semilinearAutCongr eR eS he σ x' = eS (σ (eS.symm x')) := rfl

/-- Formal unramifiedness is invariant under a compatible pair of ring
equivalences, including a change of the base ring. -/
theorem formallyUnramified_transport
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    [Algebra.FormallyUnramified R S] :
    Algebra.FormallyUnramified R' S' := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g hfg
  let : Algebra R B := ((algebraMap R' B).comp eR.toRingHom).toAlgebra
  let f₀ : S →ₐ[R] B :=
    { toRingHom := f.toRingHom.comp eS.toRingHom
      commutes' := by
        intro r
        change f (eS (algebraMap R S r)) = algebraMap R' B (eR r)
        rw [he, f.commutes] }
  let g₀ : S →ₐ[R] B :=
    { toRingHom := g.toRingHom.comp eS.toRingHom
      commutes' := by
        intro r
        change g (eS (algebraMap R S r)) = algebraMap R' B (eR r)
        rw [he, g.commutes] }
  have h₀ : f₀ = g₀ := by
    apply Algebra.FormallyUnramified.ext (I := I) ⟨2, hI⟩
    intro x
    exact AlgHom.congr_fun hfg (eS x)
  ext x'
  obtain ⟨x, rfl⟩ := eS.surjective x'
  exact AlgHom.congr_fun h₀ x

/-- Unramifiedness at a finite prime transports through a compatible
semilinear equivalence. -/
theorem isUnramifiedAt_transport
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt R Q] :
    Algebra.IsUnramifiedAt R' (Q.map eS) := by
  let Q' : Ideal S' := Q.map eS
  have hQ : Q = Q'.comap eS :=
    (Q.comap_map_of_bijective eS eS.bijective).symm
  let eLoc : Localization.AtPrime Q ≃+* Localization.AtPrime Q' :=
    Localization.localRingEquiv Q Q' eS hQ
  apply formallyUnramified_transport eR eLoc
  intro r
  change Localization.localRingHom Q Q' eS hQ
      (algebraMap R (Localization.AtPrime Q) r) =
    algebraMap R' (Localization.AtPrime Q') (eR r)
  rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q)]
  exact (Localization.localRingHom_to_map Q Q' eS hQ
    (algebraMap R S r)).trans
      ((congrArg (algebraMap S' (Localization.AtPrime Q')) (he r)).trans
        (IsScalarTower.algebraMap_apply R' S' (Localization.AtPrime Q') (eR r)).symm)

/-- Equality of the prime ideals transports the dependent unramified predicate. -/
theorem isUnramifiedAt_congr
    (Q₁ Q₂ : Ideal S) [Q₁.IsPrime] [Q₂.IsPrime] (hQ : Q₁ = Q₂) :
    Algebra.IsUnramifiedAt R Q₁ ↔ Algebra.IsUnramifiedAt R Q₂ := by
  subst Q₂
  rfl

/-- Unramifiedness at every prime over a base prime is preserved by
semilinear equivalence. -/
theorem isUnramifiedIn_transport
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (P : Ideal R) (h : Algebra.IsUnramifiedIn S P) :
    Algebra.IsUnramifiedIn S' (P.map eR) := by
  intro Q' hQ' hQP'
  let : Q'.IsPrime := hQ'
  let Q : Ideal S := Q'.comap eS
  have hQP : Q.LiesOver P := by
    constructor
    ext r
    change r ∈ P ↔ eS (algebraMap R S r) ∈ Q'
    calc
      r ∈ P ↔ eR r ∈ P.map eR := Ideal.apply_mem_of_equiv_iff.symm
      _ ↔ algebraMap R' S' (eR r) ∈ Q' := by rw [hQP'.over]; rfl
      _ ↔ eS (algebraMap R S r) ∈ Q' := by rw [he]
  let : Algebra.IsUnramifiedAt R Q := h Q inferInstance hQP
  have hm : Q.map eS = Q' := Ideal.map_comap_eq_self_of_equiv eS Q'
  exact (isUnramifiedAt_congr (R := R') (Q.map eS) Q' hm).mp
    (isUnramifiedAt_transport eR eS he Q)

end Rings

section Fields

variable {K K' L L' : Type*}
  [Field K] [Field K'] [Field L] [Field L']
  [Algebra K L] [Algebra K' L']

/-- Abelian Galois extensions are preserved by compatible equivalences on
both the base field and the extension field. -/
theorem isAbelianGalois_transport
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    [IsAbelianGalois K L] : IsAbelianGalois K' L' := by
  let : IsGalois K' L' := IsGalois.of_equiv_equiv (f := eK) (g := eL) (by
    ext x
    exact (he x).symm)
  let e := semilinearAutCongr eK eL he
  let : IsMulCommutative (L' ≃ₐ[K'] L') := .of_comm fun σ τ =>
    e.symm.injective (by rw [map_mul, map_mul, mul_comm'])
  exact {}

end Fields

open scoped NumberField
open NumberField IsDedekindDomain

section NumberFields

variable {K K' L L' : Type*}
  [Field K] [NumberField K] [Field K'] [NumberField K']
  [Field L] [NumberField L] [Field L'] [NumberField L']
  [Algebra K L] [Algebra K' L']

omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] in
/-- Restrict a commuting square of number fields to their rings of integers. -/
theorem integers_compatible
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (x : 𝓞 K) :
    RingOfIntegers.mapRingEquiv eL (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K') (𝓞 L') (RingOfIntegers.mapRingEquiv eK x) := by
  apply Subtype.ext
  exact he (x : K)

/-- Arithmetic Frobenius congruences transport even when the equivalence
on the base number field is nontrivial. -/
theorem isArithFrobAt_semilinearAutCongr
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    [IsGalois K L] [IsGalois K' L']
    (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L))
    (H : IsArithFrobAt (𝓞 K) σ Q) :
    IsArithFrobAt (𝓞 K') (semilinearAutCongr eK eL he σ)
      (Q.map (RingOfIntegers.mapRingEquiv eL).toRingHom) := by
  apply isArithFrobAt_transport
    (RingOfIntegers.mapRingEquiv eK) (RingOfIntegers.mapRingEquiv eL)
    (integers_compatible eK eL he)
    (RingOfIntegers.mapAlgEquiv σ).toAlgHom
    (RingOfIntegers.mapAlgEquiv (semilinearAutCongr eK eL he σ)).toAlgHom
    _ Q H
  intro x
  apply Subtype.ext
  change eL (σ (eL.symm (eL (x : L)))) = eL (σ (x : L))
  rw [eL.symm_apply_apply]

/-- At an unramified prime the defining arithmetic Frobenius congruence
determines a number-field automorphism uniquely. -/
theorem isArithFrobAt_eq
    [IsGalois K L]
    (σ τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q]
    (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (hτ : IsArithFrobAt (𝓞 K) τ Q) : σ = τ := by
  have hσ' : (RingOfIntegers.mapAlgEquiv σ).toAlgHom.IsArithFrobAt Q := hσ
  have hτ' : (RingOfIntegers.mapAlgEquiv τ).toAlgHom.IsArithFrobAt Q := hτ
  have hInt := hσ'.eq_of_isUnramifiedAt hτ' Q.primeCompl_le_nonZeroDivisors
  have hField : σ.toRingEquiv.toRingHom = τ.toRingEquiv.toRingHom :=
    IsFractionRing.ringHom_ext (A := 𝓞 L) (fun x =>
      congrArg (fun y : 𝓞 L => (y : L)) (AlgHom.congr_fun hInt x))
  ext x
  exact RingHom.congr_fun hField x

/-- Canonical arithmetic Frobenius is natural under a compatible pair of
number-field equivalences, with the base field allowed to move. -/
theorem arithFrobAt_semilinearAutCongr
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    [IsGalois K L] [IsGalois K' L']
    (w : HeightOneSpectrum (𝓞 L))
    [Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal] :
    semilinearAutCongr eK eL he
        (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal) =
      arithFrobAt (𝓞 K') (L' ≃ₐ[K'] L')
        ((HeightOneSpectrum.equivOfRingEquiv
          (RingOfIntegers.mapRingEquiv eL)) w).asIdeal := by
  let w' := (HeightOneSpectrum.equivOfRingEquiv
    (RingOfIntegers.mapRingEquiv eL)) w
  have hw' : w'.asIdeal = w.asIdeal.map (RingOfIntegers.mapRingEquiv eL) :=
    Ideal.comap_symm (RingOfIntegers.mapRingEquiv eL)
  let : Algebra.IsUnramifiedAt (𝓞 K') w'.asIdeal := by
    apply (isUnramifiedAt_congr (R := 𝓞 K') _ _ hw'.symm).mp
    exact isUnramifiedAt_transport
      (RingOfIntegers.mapRingEquiv eK) (RingOfIntegers.mapRingEquiv eL)
      (integers_compatible eK eL he) w.asIdeal
  apply isArithFrobAt_eq _ _ w'.asIdeal
  · rw [hw']
    exact isArithFrobAt_semilinearAutCongr eK eL he _ w.asIdeal
      (IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal)
  · exact IsArithFrobAt.arithFrobAt (𝓞 K') (L' ≃ₐ[K'] L') w'.asIdeal

end NumberFields

open scoped MatrixGroups Classical
open ClassFieldTheory
open SICLean.L5.ClassFieldModulus SICLean.L5.ClassFieldIdealAction

section IdealAction

theorem fractionalIdeal_ringEquiv_coeIdeal
    {R S K L : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [CommRing K] [CommRing L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (f : R ≃+* S) (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K L f
        (I : FractionalIdeal (nonZeroDivisors R) K) =
      (I.map f : FractionalIdeal (nonZeroDivisors S) L) := by
  let : RingHomInvPair (f : R →+* S) f.symm := RingHomInvPair.of_ringEquiv f
  let : RingHomInvPair (f.symm : S →+* R) f := RingHomInvPair.of_ringEquiv f.symm
  ext x
  change
    x ∈ ((I : FractionalIdeal (nonZeroDivisors R) K).val.map
      (IsFractionRing.semilinearEquivOfRingEquiv K L f).toLinearMap) ↔
      x ∈ (I.map f : FractionalIdeal (nonZeroDivisors S) L)
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, hr, rfl⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors R)).mp hy
    refine (FractionalIdeal.mem_coeIdeal (nonZeroDivisors S)).mpr
      ⟨f r, Ideal.mem_map_of_mem f hr, ?_⟩
    exact (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap K L f r).symm
  · intro hx
    obtain ⟨s, hs, rfl⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors S)).mp hx
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_of_equiv f s).mp hs
    refine ⟨algebraMap R K r,
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors R)).mpr ⟨r, hr, rfl⟩, ?_⟩
    exact IsFractionRing.semilinearEquivOfRingEquiv_algebraMap K L f r

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)

theorem baseAction_inv_eq (ρ : Galois.QbarAut) :
    baseAction M hM ρ⁻¹ = (baseAction M hM ρ).symm := by
  exact map_inv (AlgEquiv.restrictNormalHom (Base M hM)) ρ

theorem integerAction_inv_eq (ρ : Galois.QbarAut) :
    integerAction M hM ρ⁻¹ = (integerAction M hM ρ).symm := by
  apply RingEquiv.ext
  intro x
  apply RingOfIntegers.ext
  change baseAction M hM ρ⁻¹ (x : Base M hM) =
    (baseAction M hM ρ).symm (x : Base M hM)
  rw [baseAction_inv_eq]

theorem primeAction_eq_spectrumEquiv (ρ : Galois.QbarAut)
    (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    primeAction M hM ρ v =
      HeightOneSpectrum.equivOfRingEquiv (integerAction M hM ρ) v := by
  apply HeightOneSpectrum.ext
  exact Ideal.map_comap_of_equiv (integerAction M hM ρ)

theorem primeAction_inv (ρ : Galois.QbarAut)
    (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    primeAction M hM ρ⁻¹ (primeAction M hM ρ v) = v := by
  apply HeightOneSpectrum.ext
  change
    (v.asIdeal.map (integerAction M hM ρ)).map
      (integerAction M hM ρ⁻¹) = v.asIdeal
  rw [integerAction_inv_eq]
  exact Ideal.map_of_equiv _

theorem primeAction_inv_rev (ρ : Galois.QbarAut)
    (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    primeAction M hM ρ (primeAction M hM ρ⁻¹ v) = v := by
  simpa only [inv_inv] using primeAction_inv M hM ρ⁻¹ v

theorem primeAction_good_iff (n : ℕ) (ρ : Galois.QbarAut)
    (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    primeAction M hM ρ v ∉ (modulus M hM n).finitePart.support ↔
      v ∉ (modulus M hM n).finitePart.support := by
  simp only [Finsupp.mem_support_iff, finiteExponent_conjugate M hM n ρ v]

theorem fractionalAction_finitePrime (ρ : Galois.QbarAut)
    (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    fractionalAction M hM ρ (finitePrimeFractionalIdeal v) =
      finitePrimeFractionalIdeal (primeAction M hM ρ v) := by
  apply Units.ext
  change FractionalIdeal.ringEquivOfRingEquiv (Base M hM) (Base M hM)
      (integerAction M hM ρ)
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 (Base M hM))) (Base M hM)) =
    ((v.asIdeal.map (integerAction M hM ρ)) :
      FractionalIdeal (nonZeroDivisors (𝓞 (Base M hM))) (Base M hM))
  exact fractionalIdeal_ringEquiv_coeIdeal (integerAction M hM ρ) v.asIdeal

theorem rayAction_finitePrime (n : ℕ) (ρ : Galois.QbarAut)
    (v : HeightOneSpectrum (𝓞 (Base M hM)))
    (hv : v ∉ (modulus M hM n).finitePart.support) :
    rayAction M hM n ρ (rayClassOfFinitePrime (modulus M hM n) v hv) =
      rayClassOfFinitePrime (modulus M hM n) (primeAction M hM ρ v)
        ((primeAction_good_iff M hM n ρ v).mpr hv) := by
  simp only [rayAction, rayClassOfFinitePrime, QuotientGroup.map_mk']
  apply congrArg (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo (modulus M hM n)))
  apply Subtype.ext
  exact fractionalAction_finitePrime M hM ρ v

end IdealAction

section Realization

open SICLean.L5.ClassFieldTransport

set_option maxHeartbeats 1200000 in
/-- Transport the full ray-class realization through a semilinear
equivalence, with the target finite abelian extension kept as a parameter. -/
def conjugateRealization
    (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (n : ℕ)
    (ρ : Galois.QbarAut) (F : FiniteAbelianExtension (Base M hM))
    (T : H M hM n ≃+* F)
    (hT : ∀ x : Base M hM,
      T (algebraMap (Base M hM) (H M hM n) x) =
        algebraMap (Base M hM) F (baseAction M hM ρ x)) :
    RayClassSubgroupRealization (Base M hM) (modulus M hM n) ⊥ := by
  let C := semilinearAutCongr (baseAction M hM ρ).toRingEquiv T hT
  let A : RayGroup M hM n →* (F ≃ₐ[Base M hM] F) :=
    C.toMonoidHom.comp ((artin M hM n).comp (rayAction M hM n ρ⁻¹))
  have hraySurj : Function.Surjective (rayAction M hM n ρ⁻¹) := by
    intro a
    exact ⟨rayAction M hM n ρ a, rayAction_inv M hM n ρ a⟩
  have hsurj : Function.Surjective A :=
    C.surjective.comp ((artin_surjective M hM n).comp hraySurj)
  have hinj : Function.Injective A := by
    have hray : Function.Injective (rayAction M hM n ρ⁻¹) := by
      intro a b hab
      have hab' := congrArg (rayAction M hM n (ρ⁻¹)⁻¹) hab
      simpa only [rayAction_inv] using hab'
    exact C.injective.comp ((artinEquiv M hM n).injective.comp hray)
  refine
    { extension := F
      unramifiedOutsideModulus := ?_
      artin := A
      artin_surjective := hsurj
      artin_ker := A.ker_eq_bot hinj
      artin_frobenius := ?_ }
  · constructor
    · intro v hv
      have hv₀ := (primeAction_good_iff M hM n ρ⁻¹ v).mpr hv
      have h₀ := (unramifiedOutside M hM n).1 (primeAction M hM ρ⁻¹ v) hv₀
      have h := isUnramifiedIn_transport
        (integerAction M hM ρ) (RingOfIntegers.mapRingEquiv T)
        (integers_compatible (baseAction M hM ρ).toRingEquiv T hT)
        (primeAction M hM ρ⁻¹ v).asIdeal h₀
      change Algebra.IsUnramifiedIn (𝓞 F)
        (primeAction M hM ρ (primeAction M hM ρ⁻¹ v)).asIdeal at h
      rw [primeAction_inv_rev] at h
      exact h
    · intro v hv hnot
      exact (hnot (Finset.mem_univ _)).elim
  · intro v hv w hw
    let eO := RingOfIntegers.mapRingEquiv T
    obtain ⟨w₀, rfl⟩ := (HeightOneSpectrum.equivOfRingEquiv eO).surjective w
    have hwmap : ((HeightOneSpectrum.equivOfRingEquiv eO) w₀).asIdeal =
        w₀.asIdeal.map eO := Ideal.comap_symm eO
    have hunder : (w₀.asIdeal.under (𝓞 (Base M hM))).map (integerAction M hM ρ) =
        v.asIdeal := by
      exact (under_map (integerAction M hM ρ) eO
        (integers_compatible (baseAction M hM ρ).toRingEquiv T hT) w₀.asIdeal).symm.trans
          ((congrArg (fun I : Ideal (𝓞 F) => I.under (𝓞 (Base M hM)))
            hwmap.symm).trans hw.over.symm)
    have hw₀ : w₀.asIdeal.LiesOver (primeAction M hM ρ⁻¹ v).asIdeal := by
      constructor
      change v.asIdeal.map (integerAction M hM ρ⁻¹) = _
      rw [← hunder, integerAction_inv_eq]
      exact Ideal.map_of_equiv _
    have hv₀ := (primeAction_good_iff M hM n ρ⁻¹ v).mpr hv
    let : Algebra.IsUnramifiedAt (𝓞 (Base M hM)) w₀.asIdeal :=
      (unramifiedOutside M hM n).1 (primeAction M hM ρ⁻¹ v) hv₀
        w₀.asIdeal inferInstance hw₀
    change C (artin M hM n
      (rayAction M hM n ρ⁻¹ (rayClassOfFinitePrime (modulus M hM n) v hv))) = _
    have hRay := rayAction_finitePrime M hM n ρ⁻¹ v hv
    have hArt := artin_prime_arithFrobAt M hM n
      (primeAction M hM ρ⁻¹ v) hv₀ w₀ hw₀
    exact (congrArg C ((congrArg (artin M hM n) hRay).trans hArt)).trans
      (arithFrobAt_semilinearAutCongr (baseAction M hM ρ).toRingEquiv T hT w₀)

end Realization

end SICLean.L5.ClassFieldConjugationAux
