import SICLean.L5.ClassFieldModulus
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupExistence
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupRealizationEq

set_option autoImplicit false

/-!
# The full ray class field for the subgroup ⊥

Sources: [RW-rec]; algebraicity of the point values is [RW26, Thm. 1, p. 3].
The Artin map is the realization of the bottom ray-class subgroup.
-/

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory SICLean.L5.ClassFieldModulus

namespace SICLean.L5.ClassFieldExistence

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (n : ℕ)

-- These are the canonical inherited algebra structures, with priorities that
-- stop subtype/tower search from trying to extend Qbar into these closures.
instance (priority := 1200) baseAlgebraicClosureAlgebra :
    Algebra (Base M hM) (AlgebraicClosure (Base M hM)) :=
  @AlgebraicClosure.instAlgebra (Base M hM) _ (Base M hM) _ (Algebra.id _)

instance (priority := 1200) baseSeparableClosureAlgebra :
    Algebra (Base M hM) (SeparableClosure (Base M hM)) :=
  (separableClosure (Base M hM) (AlgebraicClosure (Base M hM))).toSubalgebra.algebra

/-- `rayClassSubgroup_existence` at the bottom subgroup. -/
theorem realization_nonempty :
    Nonempty (RayClassSubgroupRealization (Base M hM) (modulus M hM n) ⊥) :=
  rayClassSubgroup_existence (Base M hM) (modulus M hM n) ⊥

def realization : RayClassSubgroupRealization (Base M hM) (modulus M hM n) ⊥ :=
  Classical.choice (realization_nonempty M hM n)

abbrev Hsep := (realization M hM n).extension

-- Pin the inherited algebra. With an intermediate-field base, generic tower
-- search otherwise explores an irrelevant Qbar -> SeparableClosure K map.
instance (priority := 1200) extensionAlgebra (E : FiniteAbelianExtension (Base M hM)) :
    Algebra (Base M hM) E := E.1.toSubalgebra.algebra

instance (priority := 1200) extensionModule (E : FiniteAbelianExtension (Base M hM)) :
    Module (Base M hM) E := (extensionAlgebra M hM E).toModule

def artin : RayGroup M hM n →* (Hsep M hM n ≃ₐ[Base M hM] Hsep M hM n) :=
  (realization M hM n).artin

/-- The Artin map of the chosen realization is surjective. -/
theorem artin_surjective : Function.Surjective (artin M hM n) :=
  (realization M hM n).artin_surjective

theorem artin_ker : (artin M hM n).ker = ⊥ :=
  (realization M hM n).artin_ker

theorem artin_injective : Function.Injective (artin M hM n) :=
  (artin M hM n).ker_eq_bot_iff.mp (artin_ker M hM n)

def artinEquiv : RayGroup M hM n ≃* (Hsep M hM n ≃ₐ[Base M hM] Hsep M hM n) :=
  MulEquiv.ofBijective (artin M hM n)
    ⟨artin_injective M hM n, artin_surjective M hM n⟩

theorem artinEquiv_apply (a : RayGroup M hM n) :
    artinEquiv M hM n a = artin M hM n a := rfl

theorem artin_eq_one_iff (a : RayGroup M hM n) :
    artin M hM n a = 1 ↔ a = 1 := by
  constructor
  · intro ha
    apply artin_injective M hM n
    exact ha.trans (map_one (artin M hM n)).symm
  · rintro rfl
    exact map_one (artin M hM n)

/-- The realization is unramified outside the modulus. -/
theorem unramifiedOutside :
    IsUnramifiedOutsideModulus (Base M hM) (Hsep M hM n) (modulus M hM n) :=
  (realization M hM n).unramifiedOutsideModulus

/-- `artin_frobenius`: a finite prime is sent to its arithmetic Frobenius. -/
theorem artin_prime (v : HeightOneSpectrum (𝓞 (Base M hM)))
    (hv : v ∉ (modulus M hM n).finitePart.support)
    (w : HeightOneSpectrum (𝓞 (Hsep M hM n)))
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    artin M hM n (rayClassOfFinitePrime (modulus M hM n) v hv) =
      arithmeticFrobeniusAt (K := Base M hM) w :=
  (realization M hM n).artin_frobenius v hv w hw

/-- The symbol is Mathlib's arithmetic Frobenius `arithFrobAt`. -/
theorem artin_prime_arithFrobAt (v : HeightOneSpectrum (𝓞 (Base M hM)))
    (hv : v ∉ (modulus M hM n).finitePart.support)
    (w : HeightOneSpectrum (𝓞 (Hsep M hM n)))
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    artin M hM n (rayClassOfFinitePrime (modulus M hM n) v hv) =
      arithFrobAt (𝓞 (Base M hM))
        (Hsep M hM n ≃ₐ[Base M hM] Hsep M hM n) w.asIdeal :=
  artin_prime M hM n v hv w hw

theorem artin_ideal_eq_one_iff (a : RayIdeal M hM n) :
    artin M hM n (idealClass M hM n a) = 1 ↔
      ∃ x : (Base M hM)ˣ, IsRayCongruent (modulus M hM n) x ∧
        toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x = a.1 := by
  rw [artin_eq_one_iff, idealClass_eq_one_iff]

/-- Two realizations determine the same subfield of `SeparableClosure K`,
by `rayClassSubgroupRealizations_eq`. -/
theorem realization_field_unique
    (R : RayClassSubgroupRealization (Base M hM) (modulus M hM n) ⊥) :
    R.extension.1 = (Hsep M hM n).1 :=
  rayClassSubgroupRealizations_eq (Base M hM) (modulus M hM n) ⊥ R
    (realization M hM n)

/-- The degree of the full ray class field equals the order of the ray class group. -/
theorem degree_eq_card :
    Module.finrank (Base M hM) (Hsep M hM n) = Nat.card (RayGroup M hM n) :=
  (IsGalois.card_aut_eq_finrank (Base M hM) (Hsep M hM n)).symm.trans
    (Nat.card_congr (artinEquiv M hM n).toEquiv).symm

end SICLean.L5.ClassFieldExistence

#check @ClassFieldTheory.rayClassSubgroup_existence
#check @ClassFieldTheory.rayClassSubgroupRealizations_eq
#print ClassFieldTheory.arithmeticFrobeniusAt
