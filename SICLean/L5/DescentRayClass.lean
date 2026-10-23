import SICLean.L5.RayArithmeticSigns
import SICLean.L5.ClassFieldInfinite
import SICLean.L5.DescentRayClassAux

set_option autoImplicit false

/-!
# Comparison of the two ray-class interfaces

The definitions transport the ideal-theoretic quotients along an equality of
moduli. The comparison uses the class field, Artin map, and sign
representatives already constructed, with the maximal-order modulus (cm)
and both real places.

The arithmetic conventions are those of [RW-rec, pp. 13--15] and [RW-rec, p. 18].
[RW26, p. 20, (37)] identifies the quadratic field and its embeddings.
-/

noncomputable section
open scoped MatrixGroups NumberField Classical
open NumberField IsDedekindDomain ClassFieldTheory

namespace SICLean.L5.DescentRayClass

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM

/-- The specified first real places agree.
[RW26, p. 20, (37)]; [RW-rec, p. 3]; [RW-rec, p. 15]. -/
theorem realPlace_zero_eq :
    ClassFieldModulus.realPlace M hM 0 = RayArithmeticPlaces.realPlace₁ M hM := by
  rfl

/-- The specified second real places agree. No real place is selected in
order to force an Artin action.
[RW26, p. 20, (37)]; [RW-rec, p. 3]; [RW-rec, p. 15]. -/
theorem realPlace_one_eq :
    ClassFieldModulus.realPlace M hM 1 = RayArithmeticPlaces.realPlace₂ M hM := by
  rfl

/-- The integral ideal in the class-field finite-exponent definition is the
arithmetic ideal (cm).
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
theorem finiteIdeal_eq (m : ℕ) :
    RayArithmeticModulus.finiteIdeal M hM m =
      Ideal.span ({(RayArithmeticModulus.level M hM m :
        𝓞 (ClassFieldModulus.Base M hM))} : Set _) := by
  rfl

/-- Associates counts and normalized ideal factorization give the same
finite-prime exponents, including the zero-level conventions.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
theorem finiteExponent_eq_factorization (m : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    ClassFieldModulus.finiteExponent M hM (RayArithmeticModulus.level M hM m) v =
      factorization (RayArithmeticModulus.finiteIdeal M hM m) v.asIdeal := by
  exact DescentRayClassAux.finiteExponent_eq_factorization M hM m v

/-- Equality of the whole moduli. The finite parts use the two factorization
descriptions, and the infinite parts use a specified pair and `univ`.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
theorem modulus_eq (m : ℕ) :
    RayArithmeticModulus.modulus M hM m =
      ClassFieldModulus.modulus M hM (RayArithmeticModulus.level M hM m) := by
  apply RayClassModulus.ext
  · apply Finsupp.ext
    intro v
    rw [RayArithmeticModulus.finitePart_apply, ClassFieldModulus.modulus_finitePart,
      finiteExponent_eq_factorization]
  · exact RayArithmeticModulus.infinitePart_eq_univ M hM m

/-- Equality transport of the ray groups. `MulEquiv.cast` uses `modulus_eq`.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
def rayGroupEquiv (m : ℕ) :
    RayArithmeticModulus.Group M hM m ≃*
      ClassFieldModulus.RayGroup M hM (RayArithmeticModulus.level M hM m) :=
  MulEquiv.cast (M := fun q : RayClassModulus K => RayClassGroup q)
    (modulus_eq M hM m)

/-- Equality transport of the prime-to fractional ideal subgroups.
This transports that subgroup.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
def rayIdealEquiv (m : ℕ) :
    rayClassPrimeToIdeals (RayArithmeticModulus.modulus M hM m) ≃*
      ClassFieldModulus.RayIdeal M hM (RayArithmeticModulus.level M hM m) :=
  MulEquiv.cast (M := fun q : RayClassModulus K => rayClassPrimeToIdeals q)
    (modulus_eq M hM m)

/-- Both prime-to conditions refer to the same fractional ideal.
No new coprimality hypothesis is imposed.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
theorem primeTo_iff (m : ℕ) (a : NumberFieldFractionalIdealGroup K) :
    a ∈ rayClassPrimeToIdeals (RayArithmeticModulus.modulus M hM m) ↔
      a ∈ rayClassPrimeToIdeals
        (ClassFieldModulus.modulus M hM (RayArithmeticModulus.level M hM m)) := by
  rw [modulus_eq M hM m]

/-- The quotient maps commute with the subgroup and group transports.
This compares the ideal quotients, with no extra reciprocity hypothesis.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
theorem rayIdealClass_transport (m : ℕ)
    (a : rayClassPrimeToIdeals (RayArithmeticModulus.modulus M hM m)) :
    rayGroupEquiv M hM m
        (QuotientGroup.mk'
          (rayPrincipalIdealSubgroupInPrimeTo (RayArithmeticModulus.modulus M hM m)) a) =
      ClassFieldModulus.idealClass M hM (RayArithmeticModulus.level M hM m)
        (rayIdealEquiv M hM m a) := by
  exact DescentRayClassAux.cast_idealClass (modulus_eq M hM m) a

/-- Comparison for the arithmetic integral-ideal interface. The class-field
prime-to condition is a parameter about the same ideal.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
theorem idealClass_transport (m : ℕ) (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m a)
    (hprimeTo : RayArithmeticModulus.fractionalIdeal M hM a ha ∈
      rayClassPrimeToIdeals
        (ClassFieldModulus.modulus M hM (RayArithmeticModulus.level M hM m))) :
    rayGroupEquiv M hM m (RayArithmeticModulus.idealClass M hM m a ha hc) =
      ClassFieldModulus.idealClass M hM (RayArithmeticModulus.level M hM m)
        ⟨RayArithmeticModulus.fractionalIdeal M hM a ha, hprimeTo⟩ := by
  rw [RayArithmeticModulus.idealClass, rayIdealClass_transport]
  congr 1
  apply Subtype.ext
  exact DescentRayClassAux.cast_primeTo_coe (modulus_eq M hM m) _

/-- Finite-prime ray classes commute with modulus transport. Both
away-from-support conditions are parameters. The Artin normalization is that
of the class-field module.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
theorem rayClassOfFinitePrime_transport (m : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (RayArithmeticModulus.modulus M hM m).finitePart.support)
    (hv' : v ∉ (ClassFieldModulus.modulus M hM
      (RayArithmeticModulus.level M hM m)).finitePart.support) :
    rayGroupEquiv M hM m
        (rayClassOfFinitePrime (RayArithmeticModulus.modulus M hM m) v hv) =
      rayClassOfFinitePrime
        (ClassFieldModulus.modulus M hM (RayArithmeticModulus.level M hM m)) v hv' := by
  exact DescentRayClassAux.cast_rayClassOfFinitePrime (modulus_eq M hM m) v hv hv'

/-- Finite-prime form combining Frobenius normalization with the arithmetic
integral-ideal class. Coprimality and the class-field good-prime condition
are parameters.
[RW26, p. 20, (37)]; [RW-rec, pp. 13--14]. -/
theorem idealClass_finitePrime_transport (m : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m v.asIdeal)
    (hv : v ∉ (ClassFieldModulus.modulus M hM
      (RayArithmeticModulus.level M hM m)).finitePart.support) :
    rayGroupEquiv M hM m
        (RayArithmeticModulus.idealClass M hM m v.asIdeal v.ne_bot hc) =
      rayClassOfFinitePrime
        (ClassFieldModulus.modulus M hM (RayArithmeticModulus.level M hM m)) v hv := by
  rw [idealClass_transport M hM m v.asIdeal v.ne_bot hc
    ((primeTo_iff M hM m _).mp
      (RayArithmeticModulus.fractionalIdeal_mem_primeTo M hM m v.asIdeal v.ne_bot hc))]
  rfl

/-- The arithmetic (-, +) representative gives the first idelic sign class.
Sign classes may be trivial.
[RW26, p. 20, (37)]; [RW-rec, p. 15]; [RW-rec, p. 18]. -/
theorem s₁_transport (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    rayGroupEquiv M hM m (RayArithmeticSigns.s₁ M hM m hm) =
      ClassFieldSigns.signClass M hM (RayArithmeticModulus.level M hM m) 0 := by
  have hf : ClassFieldSigns.FiniteCongruent M hM (RayArithmeticModulus.level M hM m)
      (RayArithmeticSigns.generatorUnit₁ M hM m hm) := by
    unfold ClassFieldSigns.FiniteCongruent
    rw [← modulus_eq M hM m]
    exact (RayArithmeticSigns.generators_finiteCongruent M hM m hm).1.1
  change rayGroupEquiv M hM m (QuotientGroup.mk' _ _) = _
  rw [rayIdealClass_transport]
  apply (ClassFieldSigns.signClass_eq_ideal_iff M hM
    (RayArithmeticModulus.level M hM m) 0 _).mpr
  refine ⟨RayArithmeticSigns.generatorUnit₁ M hM m hm, hf, ?_, ?_⟩
  · constructor
    · exact (RayArithmeticSigns.generator₁_signs M hM m hm).1
    · intro j hj
      have hj1 : j = 1 := by omega
      subst j
      exact (RayArithmeticSigns.generator₁_signs M hM m hm).2
  · symm
    exact DescentRayClassAux.cast_primeTo_coe (modulus_eq M hM m) _

/-- The arithmetic (+, -) representative gives the second idelic sign class.
No nontriviality is assumed.
[RW26, p. 20, (37)]; [RW-rec, p. 15]; [RW-rec, p. 18]. -/
theorem s₂_transport (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    rayGroupEquiv M hM m (RayArithmeticSigns.s₂ M hM m hm) =
      ClassFieldSigns.signClass M hM (RayArithmeticModulus.level M hM m) 1 := by
  have hf : ClassFieldSigns.FiniteCongruent M hM (RayArithmeticModulus.level M hM m)
      (RayArithmeticSigns.generatorUnit₂ M hM m hm) := by
    unfold ClassFieldSigns.FiniteCongruent
    rw [← modulus_eq M hM m]
    exact (RayArithmeticSigns.generators_finiteCongruent M hM m hm).2.1
  change rayGroupEquiv M hM m (QuotientGroup.mk' _ _) = _
  rw [rayIdealClass_transport]
  apply (ClassFieldSigns.signClass_eq_ideal_iff M hM
    (RayArithmeticModulus.level M hM m) 1 _).mpr
  refine ⟨RayArithmeticSigns.generatorUnit₂ M hM m hm, hf, ?_, ?_⟩
  · constructor
    · exact (RayArithmeticSigns.generator₂_signs M hM m hm).2
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      exact (RayArithmeticSigns.generator₂_signs M hM m hm).1
  · symm
    exact DescentRayClassAux.cast_primeTo_coe (modulus_eq M hM m) _

/-- The arithmetic double-negative class transports to `doubleSign`, including
t = 1. [RW26, p. 20, (37)]; [RW-rec, p. 15]; [RW-rec, p. 18]. -/
theorem t_transport (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    rayGroupEquiv M hM m (RayArithmeticSigns.t M hM m hm) =
      ClassFieldSigns.doubleSign M hM (RayArithmeticModulus.level M hM m) := by
  rw [RayArithmeticSigns.t, map_mul, s₁_transport, s₂_transport]
  rfl

/-- The Artin map detects the trivial arithmetic class.
The restriction to ℚ matches the normal-envelope restriction.
[RW26, p. 20, (37)]; [RW-rec, p. 14]. -/
theorem artin_eq_one_iff (m : ℕ) (a : RayArithmeticModulus.Group M hM m) :
    (ClassFieldTransport.artin M hM (RayArithmeticModulus.level M hM m)
      (rayGroupEquiv M hM m a)).restrictScalars ℚ = 1 ↔ a = 1 := by
  constructor
  · intro h
    apply (rayGroupEquiv M hM m).injective
    apply ClassFieldInfiniteAux.artin_restrict_injective M hM
      (RayArithmeticModulus.level M hM m)
    simpa only [← AlgEquiv.restrictScalarsHom_apply, map_one] using h
  · rintro rfl
    simp only [← AlgEquiv.restrictScalarsHom_apply, map_one]

/-- The Artin map detects the arithmetic class t. Both sides are
ℚ-automorphisms, as required by the type of `doubleArtin`. The case t = 1
is included. [RW26, p. 20, (37)]; [RW-rec, p. 14]; [RW-rec, p. 15];
[RW-rec, p. 18]. -/
theorem artin_eq_doubleArtin_iff (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : RayArithmeticModulus.Group M hM m) :
    (ClassFieldTransport.artin M hM (RayArithmeticModulus.level M hM m)
      (rayGroupEquiv M hM m a)).restrictScalars ℚ =
        ClassFieldInfinite.doubleArtin M hM (RayArithmeticModulus.level M hM m) ↔
      a = RayArithmeticSigns.t M hM m hm := by
  constructor
  · intro h
    apply (rayGroupEquiv M hM m).injective
    rw [t_transport]
    exact ClassFieldInfiniteAux.artin_restrict_injective M hM
      (RayArithmeticModulus.level M hM m) h
  · rintro rfl
    rw [t_transport]
    rfl

end SICLean.L5.DescentRayClass
