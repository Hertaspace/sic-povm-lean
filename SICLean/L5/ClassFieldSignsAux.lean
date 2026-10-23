import SICLean.L5.ClassFieldModulus
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

set_option autoImplicit false

/-! Helpers for the ideal and idelic sign-class comparison. -/

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory
open SICLean.L5.ClassFieldModulus

namespace SICLean.L5.ClassFieldSignsAux

variable {K : Type*} [Field K] [NumberField K]

/-- A sign twist which makes a principal idèle prime to the modulus
represents the same public ideal ray class as its principal ideal. -/
theorem principal_class_from_twist
    (m : RayClassModulus K) (s : IdeleGroup K) (x : Kˣ)
    (hprime : s * IdeleGroup.principalIdele K x ∈
      RayClass.idelePrimeToModulusSubgroup
        (GlobalClassFieldComparison.rayClassModulusToOriginal K m))
    (hfrac : IdeleGroup.fractionalIdeal s = 1)
    (hI : toPrincipalIdeal (𝓞 K) K x ∈ rayClassPrimeToIdeals m) :
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
      ⟨toPrincipalIdeal (𝓞 K) K x, hI⟩ =
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
        (QuotientGroup.mk'
          (GlobalClassFieldComparison.rayClassModulusToOriginal K m).congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) s)) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let a : RayClass.idelePrimeToModulusSubgroup m' :=
    ⟨s * IdeleGroup.principalIdele K x, hprime⟩
  let G := GlobalClassFieldComparison.rayClassGroupEquivOriginal K m
  let F := RayClass.rayClassGroupEquivIdealRayClassGroup m'
  have hfrac_a : IdeleGroup.fractionalIdeal (a : IdeleGroup K) =
      toPrincipalIdeal (𝓞 K) K x := by
    change IdeleGroup.fractionalIdeal (s * IdeleGroup.principalIdele K x) = _
    rw [map_mul, hfrac, IdeleGroup.fractionalIdeal_principalIdele, one_mul]
  have hprincipal : QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (IdeleGroup.principalIdele K x) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  have hqa : QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (a : IdeleGroup K) =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup K) s := by
    change QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (s * IdeleGroup.principalIdele K x) = _
    rw [map_mul, hprincipal]
    exact mul_one (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) s)
  apply G.injective
  change G (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
      ⟨toPrincipalIdeal (𝓞 K) K x, hI⟩) =
    G (G.symm (F (QuotientGroup.mk' m'.congruenceSubgroup
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) s))))
  rw [G.apply_symm_apply, ← hqa,
    GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo]
  change QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m')
      ⟨toPrincipalIdeal (𝓞 K) K x, hI⟩ =
    QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m')
      (RayClass.primeToIdealMap m' a)
  congr 1
  exact Subtype.ext hfrac_a.symm

theorem finite_mul (m : RayClassModulus K) (x y : Kˣ)
    (hx : ∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v x ∈ rayLocalHigherUnitGroup v (m.finitePart v))
    (hy : ∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v y ∈ rayLocalHigherUnitGroup v (m.finitePart v)) :
    ∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v (x * y) ∈ rayLocalHigherUnitGroup v (m.finitePart v) := by
  intro v hv
  simpa only [map_mul] using
    (rayLocalHigherUnitGroup v (m.finitePart v)).mul_mem (hx v hv) (hy v hv)

theorem finite_div (m : RayClassModulus K) (x y : Kˣ)
    (hx : ∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v x ∈ rayLocalHigherUnitGroup v (m.finitePart v))
    (hy : ∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v y ∈ rayLocalHigherUnitGroup v (m.finitePart v)) :
    ∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v (x / y) ∈ rayLocalHigherUnitGroup v (m.finitePart v) := by
  intro v hv
  simpa only [map_div] using
    (rayLocalHigherUnitGroup v (m.finitePart v)).div_mem (hx v hv) (hy v hv)

/-- Equality of ideal classes differs by one ray-congruent generator. -/
theorem exists_generator_of_class_eq
    (m : RayClassModulus K) (a : rayClassPrimeToIdeals m) (r : Kˣ)
    (hr : toPrincipalIdeal (𝓞 K) K r ∈ rayClassPrimeToIdeals m)
    (h : QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) a =
      QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
        ⟨toPrincipalIdeal (𝓞 K) K r, hr⟩) :
    ∃ y : Kˣ, IsRayCongruent m y ∧
      toPrincipalIdeal (𝓞 K) K (y * r) = a.1 := by
  let b : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 K) K r, hr⟩
  have hq : QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) (a / b) = 1 := by
    rw [map_div, h]
    exact div_self' _
  have hm : a / b ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
    (QuotientGroup.eq_one_iff _).mp hq
  obtain ⟨y, hy, hI⟩ := (mem_rayPrincipalIdealSubgroup_iff m (a / b).1).mp hm
  refine ⟨y, hy, ?_⟩
  rw [map_mul, hI]
  exact div_mul_cancel a.1 (toPrincipalIdeal (𝓞 K) K r)

theorem ray_positive (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (n : ℕ) (x : (Base M hM)ˣ) (hx : IsRayCongruent (modulus M hM n) x)
    (i : Fin 2) : 0 < realEmbedding M hM i (x : Base M hM) := by
  have h := hx.2 (realPlace M hM i) (by simp [modulus])
  rwa [realPlace_embedding] at h

theorem realPlace_val_ne (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    {i j : Fin 2} (hji : j ≠ i) :
    (realPlace M hM j).1 ≠ (realPlace M hM i).1 := by
  intro h
  have h' : realPlace M hM j = realPlace M hM i := Subtype.ext h
  fin_cases i <;> fin_cases j
  · exact hji rfl
  · exact realPlace_ne M hM h'.symm
  · exact realPlace_ne M hM h'
  · exact hji rfl

/-- The single sign idèle cancels exactly the negative real component. -/
theorem sign_twist_primeTo (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (n : ℕ)
    (i : Fin 2) (x : (Base M hM)ˣ)
    (hx : ∀ v, v ∈ (modulus M hM n).finitePart.support →
      finitePlaceUnitEmbedding v x ∈
        rayLocalHigherUnitGroup v ((modulus M hM n).finitePart v))
    (hs : realEmbedding M hM i (x : Base M hM) < 0 ∧
      ∀ j : Fin 2, j ≠ i → 0 < realEmbedding M hM j (x : Base M hM)) :
    IdeleGroup.infinitePlaceIdele (realPlace M hM i).1
      (-1 : (realPlace M hM i).1.Completionˣ) *
      IdeleGroup.principalIdele (Base M hM) x ∈
      RayClass.idelePrimeToModulusSubgroup
        (GlobalClassFieldComparison.rayClassModulusToOriginal
          (Base M hM) (modulus M hM n)) := by
  let s := IdeleGroup.infinitePlaceIdele (realPlace M hM i).1
    (-1 : (realPlace M hM i).1.Completionˣ)
  let p := IdeleGroup.principalIdele (Base M hM) x
  constructor
  · apply (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff _ _).2
    intro v _
    obtain ⟨j, rfl⟩ : ∃ j : Fin 2, v = realPlace M hM j := by
      rcases realPlace_exhaustive M hM v with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    change IdeleGroup.infiniteComponent (realPlace M hM j).1 (s * p) ∈ _
    rw [RayClass.mem_infinitePositiveSubgroup_iff]
    intro hw
    rw [map_mul, Units.val_mul, map_mul]
    have hp : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((IdeleGroup.infiniteComponent (realPlace M hM j).1 p :
          (realPlace M hM j).1.Completionˣ) : (realPlace M hM j).1.Completion) =
        realEmbedding M hM j (x : Base M hM) := by
      rw [IdeleGroup.infiniteComponent_principalIdele,
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
      change (realPlace M hM j).1.embedding_of_isReal (realPlace M hM j).2 _ = _
      rw [realPlace_embedding]
      rfl
    rw [hp]
    by_cases hji : j = i
    · subst j
      change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((IdeleGroup.infiniteComponent (realPlace M hM i).1
          (IdeleGroup.infinitePlaceIdele (realPlace M hM i).1 (-1)) :
            (realPlace M hM i).1.Completionˣ) : (realPlace M hM i).1.Completion) * _
      rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_same]
      simpa using neg_pos.mpr hs.1
    · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((IdeleGroup.infiniteComponent (realPlace M hM j).1
          (IdeleGroup.infinitePlaceIdele (realPlace M hM i).1 (-1)) :
            (realPlace M hM j).1.Completionˣ) : (realPlace M hM j).1.Completion) * _
      rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _ _ _
        (realPlace_val_ne M hM hji)]
      simpa using hs.2 j hji
  · intro v hv
    change (1 : (v.adicCompletion (Base M hM))ˣ) *
      (IdeleGroup.principalIdele (Base M hM) x).2 v ∈
        RayClass.localHigherUnitGroup v ((modulus M hM n).finitePart v)
    rw [one_mul]
    change finitePlaceUnitEmbedding v x ∈
      rayLocalHigherUnitGroup v ((modulus M hM n).finitePart v)
    exact hx v hv

end SICLean.L5.ClassFieldSignsAux
