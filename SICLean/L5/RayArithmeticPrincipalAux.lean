import SICLean.L5.RayArithmeticSigns

set_option autoImplicit false

noncomputable section
open scoped MatrixGroups NumberField Classical nonZeroDivisors
open NumberField ClassFieldTheory

namespace SICLean.L5.RayArithmeticPrincipalAux

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM

/-- Equality of integral ideals can be tested after passing to fractional ideals. -/
theorem principal_eq_fractional_iff (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (b : 𝓞 K) (hb : (b : K) ≠ 0) :
    toPrincipalIdeal (𝓞 K) K (Units.mk0 (b : K) hb) =
        RayArithmeticModulus.fractionalIdeal M hM a ha ↔ a = Ideal.span {b} := by
  rw [toPrincipalIdeal_eq_iff]
  change FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) =
    (a : FractionalIdeal (𝓞 K)⁰ K) ↔ _
  rw [← FractionalIdeal.coeIdeal_span_singleton b]
  exact FractionalIdeal.coeIdeal_injective.eq_iff.trans eq_comm

/-- The integral-ideal class agrees with the class of its chosen generator. -/
theorem idealClass_eq_principalClass (m : ℕ) (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m a)
    (b : 𝓞 K) (hb : (b : K) ≠ 0)
    (hf : RayArithmeticModulus.FiniteCongruent M hM m (Units.mk0 (b : K) hb))
    (he : a = Ideal.span {b}) :
    RayArithmeticModulus.idealClass M hM m a ha hc =
      RayArithmeticModulus.principalClass M hM m (Units.mk0 (b : K) hb) hf := by
  apply congrArg (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo
    (RayArithmeticModulus.modulus M hM m)))
  apply Subtype.ext
  exact ((principal_eq_fractional_iff M hM a ha b hb).mpr he).symm

/-- The rational element 1-cm is negative at both specified real embeddings. -/
theorem one_sub_level_signs (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    ActualField.sigma₁ M hM (1 - (RayArithmeticModulus.level M hM m : K)) < 0 ∧
      ActualField.sigma₂ M hM (1 - (RayArithmeticModulus.level M hM m : K)) < 0 := by
  have h : (4 : ℝ) ≤ (RayArithmeticModulus.level M hM m : ℝ) := by
    exact_mod_cast RayArithmeticModulus.four_le_level M hM m hm
  simp only [map_sub, map_one, map_natCast]
  constructor <;> linarith

/-- Its congruence is global, with the integral witness -1. -/
theorem one_sub_level_congruent (m : ℕ) :
    RayArithmeticModulus.GloballyCongruent M hM m
      (1 - (RayArithmeticModulus.level M hM m : K)) := by
  refine ⟨-1, ?_⟩
  simp only [map_neg, map_one]
  ring

/-- Equal ray classes differ by one ray-congruent principal generator. -/
theorem class_eq_principal_iff (m : ℕ)
    (a : rayClassPrimeToIdeals (RayArithmeticModulus.modulus M hM m))
    (u : Kˣ) (hu : RayArithmeticModulus.FiniteCongruent M hM m u) :
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo
      (RayArithmeticModulus.modulus M hM m)) a =
        RayArithmeticModulus.principalClass M hM m u hu ↔
      ∃ b : Kˣ, IsRayCongruent (RayArithmeticModulus.modulus M hM m) b ∧
        toPrincipalIdeal (𝓞 K) K (b * u) = a.val := by
  let p : rayClassPrimeToIdeals (RayArithmeticModulus.modulus M hM m) :=
    ⟨toPrincipalIdeal (𝓞 K) K u,
      RayArithmeticModulus.principal_mem_primeTo M hM m u hu⟩
  change (a : rayClassPrimeToIdeals (RayArithmeticModulus.modulus M hM m) ⧸
    rayPrincipalIdealSubgroupInPrimeTo (RayArithmeticModulus.modulus M hM m)) = p ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  change a.val / p.val ∈ rayPrincipalIdealSubgroup (RayArithmeticModulus.modulus M hM m) ↔ _
  rw [mem_rayPrincipalIdealSubgroup_iff]
  constructor
  · rintro ⟨b, hb, he⟩
    refine ⟨b, hb, ?_⟩
    change toPrincipalIdeal (𝓞 K) K b = a.val / toPrincipalIdeal (𝓞 K) K u at he
    rw [map_mul, he, div_mul_cancel]
  · rintro ⟨b, hb, he⟩
    refine ⟨b, hb, ?_⟩
    change toPrincipalIdeal (𝓞 K) K b = a.val / toPrincipalIdeal (𝓞 K) K u
    apply (eq_div_iff_mul_eq').mpr
    rw [← map_mul, he]

end SICLean.L5.RayArithmeticPrincipalAux
