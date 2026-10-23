import SICLean.L5.RayArithmeticModulus
import SICLean.L5.ClassFieldModulus

set_option autoImplicit false

/-!
# Auxiliary comparisons for the two ray-class interfaces

These lemmas compare existing factorization APIs and equality transports.
The zero ideal uses the zero-factorization convention on both sides.
-/

noncomputable section
open scoped MatrixGroups NumberField Classical
open NumberField IsDedekindDomain ClassFieldTheory

namespace SICLean.L5.DescentRayClassAux

/-- Associates counts agree with normalized ideal factorization, also at zero. -/
theorem associates_count_eq_factorization {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I : Ideal R) (v : HeightOneSpectrum R) :
    (Associates.mk v.asIdeal).count (Associates.mk I).factors =
      factorization I v.asIdeal := by
  classical
  by_cases hI : I = 0
  · rw [hI, Associates.mk_zero, Associates.factors_zero,
      Associates.count, dite_eq_left v.associates_irreducible, factorization_zero]
    rfl
  · rw [factorization_eq_count]
    exact Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot

/-- Equality transport preserves the underlying fractional ideal. -/
theorem cast_primeTo_coe {F : Type*} [Field F] [NumberField F]
    {q q' : RayClassModulus F} (h : q = q')
    (a : rayClassPrimeToIdeals q) :
    ((MulEquiv.cast (M := fun r : RayClassModulus F => rayClassPrimeToIdeals r) h a :
        rayClassPrimeToIdeals q') : NumberFieldFractionalIdealGroup F) = a.1 := by
  cases h
  rfl

/-- The ray-ideal quotient map commutes with equality transport of moduli. -/
theorem cast_idealClass {F : Type*} [Field F] [NumberField F]
    {q q' : RayClassModulus F} (h : q = q')
    (a : rayClassPrimeToIdeals q) :
    MulEquiv.cast (M := fun r : RayClassModulus F => RayClassGroup r) h
        (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo q) a) =
      QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo q')
        (MulEquiv.cast (M := fun r : RayClassModulus F => rayClassPrimeToIdeals r) h a) := by
  cases h
  rfl

/-- A finite-prime ray class commutes with equality transport of moduli. -/
theorem cast_rayClassOfFinitePrime {F : Type*} [Field F] [NumberField F]
    {q q' : RayClassModulus F} (h : q = q')
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ q.finitePart.support)
    (hv' : v ∉ q'.finitePart.support) :
    MulEquiv.cast (M := fun r : RayClassModulus F => RayClassGroup r) h
        (rayClassOfFinitePrime q v hv) = rayClassOfFinitePrime q' v hv' := by
  cases h
  rfl

/-- The existing arithmetic ideal and class-field exponent use the same factors,
including when the level is zero. -/
theorem finiteExponent_eq_factorization (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (m : ℕ)
    (v : HeightOneSpectrum (𝓞 (ActualField.baseField M hM))) :
    ClassFieldModulus.finiteExponent M hM (RayArithmeticModulus.level M hM m) v =
      factorization (RayArithmeticModulus.finiteIdeal M hM m) v.asIdeal := by
  exact associates_count_eq_factorization (RayArithmeticModulus.finiteIdeal M hM m) v

end SICLean.L5.DescentRayClassAux
