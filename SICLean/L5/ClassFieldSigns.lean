import SICLean.L5.ClassFieldModulus
import SICLean.L5.ClassFieldSignsAux
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

set_option autoImplicit false

/-!
# The two ideal-theoretic sign classes, via explicit idèles

A sign class may be trivial. The principal-ideal characterization is stated
separately from the construction.
Sources: [RW-rec, Prop. 5, Prop. 7]; the embeddings are [RW26, p. 20].
The ray class group is an ideal quotient. `rayClassGroupEquivOriginalIdele`
identifies it with the idèlic quotient.
-/

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory
open SICLean.L5.ClassFieldModulus

namespace SICLean.L5.ClassFieldSigns

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (n : ℕ)

def ideleClassToRay : IdeleClassGroup (Base M hM) →* RayGroup M hM n :=
  (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
    (Base M hM) (modulus M hM n)).symm.toMonoidHom.comp
      (QuotientGroup.mk'
        (GlobalClassFieldComparison.rayClassModulusToOriginal
          (Base M hM) (modulus M hM n)).congruenceSubgroup)

def signClass (i : Fin 2) : RayGroup M hM n :=
  ideleClassToRay M hM n
    (IdeleGroup.infinitePlaceIdeleClass (realPlace M hM i).1
      (-1 : (realPlace M hM i).1.Completionˣ))

def doubleSign : RayGroup M hM n := signClass M hM n 0 * signClass M hM n 1

def FiniteCongruent (x : (Base M hM)ˣ) : Prop :=
  ∀ v, v ∈ (modulus M hM n).finitePart.support →
    finitePlaceUnitEmbedding v x ∈ rayLocalHigherUnitGroup v ((modulus M hM n).finitePart v)

def SingleNegative (i : Fin 2) (x : (Base M hM)ˣ) : Prop :=
  realEmbedding M hM i (x : Base M hM) < 0 ∧
    ∀ j : Fin 2, j ≠ i → 0 < realEmbedding M hM j (x : Base M hM)

def BothNegative (x : (Base M hM)ˣ) : Prop :=
  ∀ i : Fin 2, realEmbedding M hM i (x : Base M hM) < 0

/-- The idèle-class map onto the ray class group is surjective. -/
theorem ideleClassToRay_surjective : Function.Surjective (ideleClassToRay M hM n) :=
  (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
    (Base M hM) (modulus M hM n)).symm.surjective.comp
      (QuotientGroup.mk'_surjective _)

/-- The single negative idele is an involution before applying reciprocity. -/
theorem signClass_sq (i : Fin 2) : signClass M hM n i ^ 2 = 1 := by
  change ideleClassToRay M hM n
    (IdeleGroup.infinitePlaceIdeleClass (realPlace M hM i).1 (-1)) ^ 2 = 1
  rw [← map_pow, ← map_pow]
  simp

theorem signClass_inv (i : Fin 2) : (signClass M hM n i)⁻¹ = signClass M hM n i :=
  by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using signClass_sq M hM n i)

theorem doubleSign_sq : doubleSign M hM n ^ 2 = 1 := by
  change (signClass M hM n 0 * signClass M hM n 1) ^ 2 = 1
  calc
    _ = signClass M hM n 0 ^ 2 * signClass M hM n 1 ^ 2 :=
      _root_.mul_pow (signClass M hM n 0) (signClass M hM n 1) 2
    _ = 1 * 1 := congrArg₂ (· * ·) (signClass_sq M hM n 0) (signClass_sq M hM n 1)
    _ = 1 := one_mul (1 : RayGroup M hM n)

theorem secondSign_eq_first_mul_double :
    signClass M hM n 1 = signClass M hM n 0 * doubleSign M hM n := by
  rw [doubleSign, ← _root_.mul_assoc (signClass M hM n 0)
    (signClass M hM n 0) (signClass M hM n 1)]
  rw [← pow_two, signClass_sq]
  exact (one_mul (signClass M hM n 1)).symm

/-- Weak approximation at the finite congruences and both real signs.
This theorem does not assume that the resulting ideal class is nontrivial. -/
theorem exists_singleNegative (i : Fin 2) :
    ∃ x : (Base M hM)ˣ, FiniteCongruent M hM n x ∧ SingleNegative M hM i x := by
  let m := GlobalClassFieldComparison.rayClassModulusToOriginal
    (Base M hM) (modulus M hM n)
  let a := IdeleGroup.infinitePlaceIdele (realPlace M hM i).1
    (-1 : (realPlace M hM i).1.Completionˣ)
  obtain ⟨x, hx⟩ := RayClass.exists_principal_quotient_mem_primeTo m a
  refine ⟨x, ?_, ?_, ?_⟩
  · intro v hv
    have hf := hx.2 v hv
    change IdeleGroup.finiteComponent v
      (a * (IdeleGroup.principalIdele (Base M hM) x)⁻¹) ∈
        RayClass.localHigherUnitGroup v (m.finitePart v) at hf
    rw [map_mul, map_inv] at hf
    have ha : IdeleGroup.finiteComponent v a = 1 :=
      IdeleGroup.infinitePlaceIdele_finiteComponent _ _ _
    rw [ha, one_mul] at hf
    exact (RayClass.localHigherUnitGroup v (m.finitePart v)).inv_mem hf
  · have hp := (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff m _).1 hx.1
      (realPlace M hM i)
      (by simp [m, GlobalClassFieldComparison.rayClassModulusToOriginal, modulus])
    change IdeleGroup.infiniteComponent (realPlace M hM i).1
      (a * (IdeleGroup.principalIdele (Base M hM) x)⁻¹) ∈
        RayClass.infinitePositiveSubgroup (realPlace M hM i).1 at hp
    have hp := (RayClass.mem_infinitePositiveSubgroup_iff _ _).1 hp
      (realPlace M hM i).2
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      map_mul, map_inv₀, IdeleGroup.infiniteComponent_principalIdele,
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe] at hp
    have ha : IdeleGroup.infiniteComponent (realPlace M hM i).1 a = -1 :=
      IdeleGroup.infinitePlaceIdele_infiniteComponent_same _ _
    rw [ha, Units.val_neg, Units.val_one, map_neg, map_one, neg_one_mul,
      realPlace_embedding] at hp
    exact (inv_neg'').mp (neg_pos.mp hp)
  · intro j hji
    have hp := (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff m _).1 hx.1
      (realPlace M hM j)
      (by simp [m, GlobalClassFieldComparison.rayClassModulusToOriginal, modulus])
    change IdeleGroup.infiniteComponent (realPlace M hM j).1
      (a * (IdeleGroup.principalIdele (Base M hM) x)⁻¹) ∈
        RayClass.infinitePositiveSubgroup (realPlace M hM j).1 at hp
    have hp := (RayClass.mem_infinitePositiveSubgroup_iff _ _).1 hp
      (realPlace M hM j).2
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      map_mul, map_inv₀, IdeleGroup.infiniteComponent_principalIdele,
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe] at hp
    have ha : IdeleGroup.infiniteComponent (realPlace M hM j).1 a = 1 :=
      IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _ _ _
        (ClassFieldSignsAux.realPlace_val_ne M hM hji)
    rw [ha, Units.val_one, map_one, one_mul, realPlace_embedding] at hp
    exact inv_pos.mp hp

/-- A finite-congruent field unit generates an ideal prime to the modulus. -/
theorem principal_primeTo (x : (Base M hM)ˣ) (hx : FiniteCongruent M hM n x) :
    toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x ∈
      rayClassPrimeToIdeals (modulus M hM n) := by
  intro v hv
  rw [← IdeleGroup.fractionalIdeal_principalIdele]
  change FractionalIdeal.count (Base M hM) v
      (((FractionalIdealGroup.factorization (K := Base M hM))
        (FiniteIdeleGroup.valuationVector
          (IdeleGroup.principalIdele (Base M hM) x).2) :
          FractionalIdealGroup (Base M hM)) :
        FractionalIdeal (nonZeroDivisors (𝓞 (Base M hM))) (Base M hM)) = 0
  rw [FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply]
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v
    ((IdeleGroup.principalIdele (Base M hM) x).2 v)).2
  apply RayClass.localHigherUnitGroup_le_integralUnits v
    ((modulus M hM n).finitePart v)
  exact hx v hv

/-- The idelic sign is the ideal class with exactly that negative sign.
Twisting the principal idèle by this sign makes its real components positive. -/
theorem signClass_principal (i : Fin 2) (x : (Base M hM)ˣ)
    (hx : FiniteCongruent M hM n x) (hs : SingleNegative M hM i x) :
    idealClass M hM n
      ⟨toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x, principal_primeTo M hM n x hx⟩ =
        signClass M hM n i := by
  let s := IdeleGroup.infinitePlaceIdele (realPlace M hM i).1
    (-1 : (realPlace M hM i).1.Completionˣ)
  have hfrac : IdeleGroup.fractionalIdeal s = 1 := by
    change FiniteIdeleGroup.fractionalIdeal (1 : FiniteIdeleGroup (Base M hM)) = 1
    exact map_one _
  exact ClassFieldSignsAux.principal_class_from_twist (modulus M hM n) s x
    (ClassFieldSignsAux.sign_twist_primeTo M hM n i x hx hs) hfrac
    (principal_primeTo M hM n x hx)

/-- Ideal characterization of a sign class: the same generator and the same finite congruence. -/
theorem signClass_eq_ideal_iff (i : Fin 2) (a : RayIdeal M hM n) :
    idealClass M hM n a = signClass M hM n i ↔
      ∃ x : (Base M hM)ˣ, FiniteCongruent M hM n x ∧ SingleNegative M hM i x ∧
        toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x = a.1 := by
  constructor
  · intro h
    obtain ⟨r, hr, hs⟩ := exists_singleNegative M hM n i
    have heq : idealClass M hM n a = idealClass M hM n
        ⟨toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) r,
          principal_primeTo M hM n r hr⟩ :=
      h.trans (signClass_principal M hM n i r hr hs).symm
    obtain ⟨y, hy, hI⟩ := ClassFieldSignsAux.exists_generator_of_class_eq
      (modulus M hM n) a r (principal_primeTo M hM n r hr) heq
    refine ⟨y * r, ClassFieldSignsAux.finite_mul _ _ _ hy.1 hr, ?_, hI⟩
    constructor
    · simpa only [Units.val_mul, map_mul] using
        mul_neg_of_pos_of_neg (ClassFieldSignsAux.ray_positive M hM n y hy i) hs.1
    · intro j hj
      simpa only [Units.val_mul, map_mul] using
        mul_pos (ClassFieldSignsAux.ray_positive M hM n y hy j) (hs.2 j hj)
  · rintro ⟨x, hx, hs, hI⟩
    have ha : a = ⟨toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x,
        principal_primeTo M hM n x hx⟩ := Subtype.ext hI.symm
    rw [ha]
    exact signClass_principal M hM n i x hx hs

theorem doubleSign_eq_ideal_iff (a : RayIdeal M hM n) :
    idealClass M hM n a = doubleSign M hM n ↔
      ∃ x : (Base M hM)ˣ, FiniteCongruent M hM n x ∧ BothNegative M hM x ∧
        toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x = a.1 := by
  obtain ⟨r, hr, hs⟩ := exists_singleNegative M hM n 1
  let b : RayIdeal M hM n :=
    ⟨toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) r,
      principal_primeTo M hM n r hr⟩
  have hb : idealClass M hM n b = signClass M hM n 1 :=
    signClass_principal M hM n 1 r hr hs
  have heq : idealClass M hM n a = doubleSign M hM n ↔
      idealClass M hM n (a / b) = signClass M hM n 0 := by
    rw [map_div, hb]
    constructor
    · intro h
      rw [h, doubleSign]
      exact mul_div_cancel_right _ _
    · intro h
      calc
        idealClass M hM n a =
            (idealClass M hM n a / signClass M hM n 1) * signClass M hM n 1 :=
          (div_mul_cancel _ _).symm
        _ = doubleSign M hM n := by rw [h]; rfl
  rw [heq, signClass_eq_ideal_iff]
  constructor
  · rintro ⟨y, hy, hsy, hI⟩
    refine ⟨y * r, ClassFieldSignsAux.finite_mul _ _ _ hy hr, ?_, ?_⟩
    · intro i
      by_cases hi : i = 0
      · subst i
        simpa only [Units.val_mul, map_mul] using
          mul_neg_of_neg_of_pos hsy.1 (hs.2 0 (by decide))
      · have hi1 : i = 1 := by omega
        subst i
        simpa only [Units.val_mul, map_mul] using
          mul_neg_of_pos_of_neg (hsy.2 1 (by decide)) hs.1
    · rw [map_mul, hI]
      exact div_mul_cancel a.1 (toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) r)
  · rintro ⟨x, hx, hsx, hI⟩
    refine ⟨x / r, ClassFieldSignsAux.finite_div _ _ _ hx hr, ?_, ?_⟩
    · constructor
      · simpa only [Units.val_div_eq_div_val, map_div₀] using
          div_neg_of_neg_of_pos (hsx 0) (hs.2 0 (by decide))
      · intro j hj
        have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        simpa only [Units.val_div_eq_div_val, map_div₀] using
          div_pos_of_neg_of_neg (hsx 1) hs.1
    · rw [map_div, hI]
      rfl

/-- The trivial-sign possibility is preserved explicitly. -/
theorem signClass_eq_one_iff (i : Fin 2) :
    signClass M hM n i = 1 ↔
      ∃ x : (Base M hM)ˣ, FiniteCongruent M hM n x ∧ SingleNegative M hM i x ∧
        toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x = 1 := by
  simpa only [map_one, Subgroup.coe_one, eq_comm] using signClass_eq_ideal_iff M hM n i 1

/-- The criterion for the double sign to be trivial, including the case t = 1. -/
theorem doubleSign_eq_one_iff :
    doubleSign M hM n = 1 ↔
      ∃ x : (Base M hM)ˣ, FiniteCongruent M hM n x ∧ BothNegative M hM x ∧
        toPrincipalIdeal (𝓞 (Base M hM)) (Base M hM) x = 1 := by
  simpa only [map_one, Subgroup.coe_one, eq_comm] using doubleSign_eq_ideal_iff M hM n 1

end SICLean.L5.ClassFieldSigns

#check @ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
#check @IdeleGroup.infinitePlaceIdeleClass
#print SICLean.L5.ClassFieldSigns.signClass
