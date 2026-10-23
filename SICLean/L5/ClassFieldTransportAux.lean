import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option autoImplicit false

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace SICLean.L5.ClassFieldTransportAux

/-- Pull back every upstairs prime along the specified algebra equivalence. -/
theorem isUnramifiedIn_of_algEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (p : Ideal R)
    (hp : Algebra.IsUnramifiedIn A p) : Algebra.IsUnramifiedIn B p := by
  intro Q hQ hQp
  let P := Q.comap e
  have : P.IsPrime := inferInstance
  have : P.LiesOver p := inferInstance
  have : Algebra.IsUnramifiedAt R P := hp P inferInstance inferInstance
  exact Algebra.FormallyUnramified.of_equiv (Localization.localAlgEquiv P Q e rfl)

/-- The arithmetic residue-field power is unchanged by a base-linear field
equivalence. The prime is transported by the induced integer-ring equivalence. -/
theorem isArithFrobAt_autCongr
    {K L E : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (e : L ≃ₐ[K] E) (P : Ideal (𝓞 L)) (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ P) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.autCongr e σ)
      (P.map (RingOfIntegers.mapAlgEquiv e)) := by
  let eO : (𝓞 L) ≃ₐ[𝓞 K] (𝓞 E) := RingOfIntegers.mapAlgEquiv e
  have hbase : (P.map eO).under (𝓞 K) = P.under (𝓞 K) := by
    exact (inferInstance : (P.map eO).LiesOver (P.under (𝓞 K))).over.symm
  have hact (x : 𝓞 E) :
      (AlgEquiv.autCongr e σ) • x = eO (σ • eO.symm x) := by
    apply RingOfIntegers.ext
    change (AlgEquiv.autCongr e σ) (x : E) = e (σ (e.symm (x : E)))
    simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
  intro x
  change (AlgEquiv.autCongr e σ) • x -
    x ^ Nat.card ((𝓞 K) ⧸ (P.map eO).under (𝓞 K)) ∈ P.map eO
  rw [hact, hbase]
  have hx := Ideal.mem_map_of_mem eO (hσ (eO.symm x))
  simpa only [map_sub, map_pow, AlgEquiv.apply_symm_apply,
    MulSemiringAction.toAlgHom_apply] using hx

/-- At an unramified prime the transported arithmetic Frobenius is the
chosen arithmetic Frobenius, by its residue-field characterization. -/
theorem arithFrobAt_autCongr
    {K L E : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (e : L ≃ₐ[K] E) (w : HeightOneSpectrum (𝓞 L))
    (w' : HeightOneSpectrum (𝓞 E))
    (hmap : w'.asIdeal = w.asIdeal.map (RingOfIntegers.mapAlgEquiv e))
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w'.asIdeal) :
    AlgEquiv.autCongr e (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal) =
      arithFrobAt (𝓞 K) (E ≃ₐ[K] E) w'.asIdeal := by
  have hσ := isArithFrobAt_autCongr e w.asIdeal
    (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal)
    (IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal)
  rw [← hmap] at hσ
  have hmaps := hσ.eq_of_isUnramifiedAt
    (IsArithFrobAt.arithFrobAt (𝓞 K) (E ≃ₐ[K] E) w'.asIdeal)
    w'.asIdeal.primeCompl_le_nonZeroDivisors
  have hring :
      (AlgEquiv.autCongr e (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal)).toRingHom =
        (arithFrobAt (𝓞 K) (E ≃ₐ[K] E) w'.asIdeal).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 E)
    intro x
    exact congrArg (fun y : 𝓞 E => (y : E)) (AlgHom.congr_fun hmaps x)
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun hring x)

end SICLean.L5.ClassFieldTransportAux
