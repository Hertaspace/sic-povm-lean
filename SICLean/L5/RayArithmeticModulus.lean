import SICLean.L5.RayArithmeticOrder
import SICLean.L5.RayArithmeticPlaces
import SICLean.L5.RayArithmeticModulusAux
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

set_option autoImplicit false

/-!
# The actual modulus cm O_K with both real places

The group is the ideal-theoretic quotient, with the principal-generator criterion proved
from its quotient kernel. Finite congruence is local congruence with the infinite part
removed; its integral/global interpretation is a separate theorem. Source: [RW26, p.
20].
-/

noncomputable section
open scoped MatrixGroups NumberField Classical
open NumberField IsDedekindDomain ClassFieldTheory

namespace SICLean.L5.RayArithmeticModulus

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM

def level (m : ℕ) : ℕ := RayArithmeticOrder.conductor M hM * m

def finiteIdeal (m : ℕ) : Ideal (𝓞 K) := Ideal.span {(level M hM m : 𝓞 K)}

/-- Prime exponents of the literal ideal (cm), not the zero finite modulus. -/
def modulus (m : ℕ) : RayClassModulus K where
  finitePart := Finsupp.comapDomain HeightOneSpectrum.asIdeal
    (factorization (finiteIdeal M hM m)) HeightOneSpectrum.asIdeal_injective.injOn
  infinitePart := {RayArithmeticPlaces.realPlace₁ M hM, RayArithmeticPlaces.realPlace₂ M hM}

def finiteModulus (m : ℕ) : RayClassModulus K :=
  { modulus M hM m with infinitePart := ∅ }

abbrev Group (m : ℕ) := RayClassGroup (modulus M hM m)

def FiniteCongruent (m : ℕ) (a : Kˣ) : Prop :=
  IsRayCongruent (finiteModulus M hM m) a

/-- A global congruence in the maximal order, also for a field-valued input. -/
def GloballyCongruent (m : ℕ) (a : K) : Prop :=
  ∃ b : 𝓞 K, a - 1 = (level M hM m : K) * (b : K)

def CoprimeIdeal (m : ℕ) (a : Ideal (𝓞 K)) : Prop :=
  IsCoprime a (finiteIdeal M hM m)

def fractionalIdeal (a : Ideal (𝓞 K)) (ha : a ≠ ⊥) :
    NumberFieldFractionalIdealGroup K :=
  FractionalIdeal.mk0 K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩

/-- Source: positivity of c and the level, [RW-rec]. [RW26, p. 20]. -/
theorem level_pos (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    0 < level M hM m := by
  exact Nat.mul_pos (RayArithmeticOrder.conductor_pos M hM) hm.1

/-- Source: same level convention; needed for the explicit double-negative representative (1-cm),
including t=1. [RW26, p. 20]. -/
theorem four_le_level (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    4 ≤ level M hM m := by
  have hm4 : 4 ≤ m := Nat.le_of_dvd hm.1 hm.2.1
  exact hm4.trans (Nat.le_mul_of_pos_left m (RayArithmeticOrder.conductor_pos M hM))

/-- Source: (cm) is a nonzero integral ideal, [RW-rec]. [RW26, p. 20]. -/
theorem finiteIdeal_ne_bot (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    finiteIdeal M hM m ≠ ⊥ := by
  rw [finiteIdeal, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
  exact (level_pos M hM m hm).ne'

/-- Source: finite-prime-exponent interface; factorization of cm O_K, [RW-rec] and [RW26, p. 20]. -/
theorem finitePart_apply (m : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (modulus M hM m).finitePart v =
      factorization (finiteIdeal M hM m) v.asIdeal := by
  rfl

/-- Source: reconstruction of the integral finite modulus, same sources. This explicitly identifies
the exponent data with cm O_K. [RW26, p. 20]. -/
theorem finitePart_product (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    ∏ v ∈ (modulus M hM m).finitePart.support,
      v.asIdeal ^ (modulus M hM m).finitePart v = finiteIdeal M hM m := by
  let f := factorization (finiteIdeal M hM m)
  have hb : Set.BijOn HeightOneSpectrum.asIdeal
      (HeightOneSpectrum.asIdeal ⁻¹' (f.support : Set (Ideal (𝓞 K)))) f.support := by
    refine ⟨fun _ hv => hv, HeightOneSpectrum.asIdeal_injective.injOn, ?_⟩
    intro p hp
    have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors (finiteIdeal M hM m) := by
      apply Multiset.count_ne_zero.mp
      simpa only [f, factorization_eq_count] using Finsupp.mem_support_iff.mp hp
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p hp'
    exact ⟨⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩, hp, rfl⟩
  change (Finsupp.comapDomain HeightOneSpectrum.asIdeal f _).prod
    (fun v n => v.asIdeal ^ n) = _
  trans f.prod (fun p n => p ^ n)
  · simpa only [Function.comp_def] using
      Finsupp.prod_comapDomain HeightOneSpectrum.asIdeal f (fun p n => p ^ n) hb
  change ∏ p ∈ (factorization (finiteIdeal M hM m)).support,
    p ^ factorization (finiteIdeal M hM m) p = _
  simp_rw [support_factorization, factorization_eq_count]
  rw [← Finset.prod_multiset_count]
  exact Ideal.prod_normalizedFactors_eq_self (finiteIdeal_ne_bot M hM m hm)

/-- Source: both real places, [RW-rec]; [RW26, p. 20]. -/
theorem infinitePart_eq_univ (m : ℕ) :
    (modulus M hM m).infinitePart = Finset.univ := by
  exact RayArithmeticPlaces.realPlace_pair_eq_univ M hM

/-- Source: local-to-integral ray congruence bridge, [RW-rec]; Integrality is essential in this
equivalence. [RW26, p. 20]. -/
theorem finiteCongruent_iff_global (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m) (a : 𝓞 K)
    (ha : (a : K) ≠ 0) :
    FiniteCongruent M hM m (Units.mk0 (a : K) ha) ↔
      GloballyCongruent M hM m (a : K) := by
  rw [FiniteCongruent,
    RayArithmeticModulusAux.isRayCongruent_iff_sub_mem (finiteModulus M hM m) rfl
      (finiteIdeal M hM m) (finitePart_product M hM m hm) a ha,
    finiteIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have h := congrArg (algebraMap (𝓞 K) K) hb
    simpa only [map_sub, map_one, map_mul, map_natCast] using h
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply RingOfIntegers.coe_injective
    simpa only [map_sub, map_one, map_mul, map_natCast] using hb

/-- Source: positivity conditions translated to the actual embeddings, [RW-rec]; [RW26, p. 20]. -/
theorem isRayCongruent_iff (m : ℕ) (a : Kˣ) :
    IsRayCongruent (modulus M hM m) a ↔
      FiniteCongruent M hM m a ∧
        0 < ActualField.sigma₁ M hM (a : K) ∧
        0 < ActualField.sigma₂ M hM (a : K) := by
  simp [IsRayCongruent, FiniteCongruent, finiteModulus, modulus,
    RayArithmeticPlaces.realPlace₁_embedding,
    RayArithmeticPlaces.realPlace₂_embedding]

/-- Source: prime-to-ideal bridge, [RW-rec]; the ideal may be composite. [RW26, p. 20]. -/
theorem fractionalIdeal_mem_primeTo (m : ℕ) (a : Ideal (𝓞 K))
    (ha : a ≠ ⊥) (hc : CoprimeIdeal M hM m a) :
    fractionalIdeal M hM a ha ∈ rayClassPrimeToIdeals (modulus M hM m) := by
  intro v hv
  change FractionalIdeal.count K v (a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  rw [FractionalIdeal.count_coe K v ha, Int.natCast_eq_zero]
  by_contra hn
  have hdva : v.asIdeal ∣ a := (Associates.count_ne_zero_iff_dvd ha v.irreducible).mp hn
  have hfact : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors
      (finiteIdeal M hM m) := by
    have hv' := Finsupp.mem_support_iff.mp hv
    rw [finitePart_apply, factorization_eq_count] at hv'
    exact Multiset.count_ne_zero.mp hv'
  exact v.prime.not_isUnit
    (hc.isUnit_of_dvd' hdva (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfact))

def idealClass (m : ℕ) (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (hc : CoprimeIdeal M hM m a) : Group M hM m :=
  QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo (modulus M hM m))
    ⟨fractionalIdeal M hM a ha, fractionalIdeal_mem_primeTo M hM m a ha hc⟩

/-- Source: a finite-ray-congruent principal ideal is prime to the finite modulus,
RayPrincipalIdealPrimeTo; [RW-rec]. [RW26, p. 20]. -/
theorem principal_mem_primeTo (m : ℕ) (a : Kˣ)
    (ha : FiniteCongruent M hM m a) :
    toPrincipalIdeal (𝓞 K) K a ∈ rayClassPrimeToIdeals (modulus M hM m) := by
  intro v hv
  rw [← IdeleGroup.fractionalIdeal_principalIdele]
  change FractionalIdeal.count K v
    (((FractionalIdealGroup.factorization («K» := K))
      (FiniteIdeleGroup.valuationVector (IdeleGroup.principalIdele K a).2) :
      FractionalIdealGroup K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  rw [FractionalIdealGroup.count_factorization, FiniteIdeleGroup.valuationVector_apply]
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v
    ((IdeleGroup.principalIdele K a).2 v)).2
  apply RayClass.localHigherUnitGroup_le_integralUnits v ((modulus M hM m).finitePart v)
  exact ha.1 v hv

def principalClass (m : ℕ) (a : Kˣ) (ha : FiniteCongruent M hM m a) : Group M hM m :=
  QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo (modulus M hM m))
    ⟨toPrincipalIdeal (𝓞 K) K a, principal_mem_primeTo M hM m a ha⟩

/-- Source: mem_rayPrincipalIdealSubgroup_iff and quotient kernel; [RW-rec]. No principalness
hypothesis is added. [RW26, p. 20]. -/
theorem class_eq_one_iff (m : ℕ) (a : rayClassPrimeToIdeals (modulus M hM m)) :
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo (modulus M hM m)) a = 1 ↔
      ∃ b : Kˣ, IsRayCongruent (modulus M hM m) b ∧
        toPrincipalIdeal (𝓞 K) K b = a.val := by
  change (a : RayClassGroup (modulus M hM m)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact mem_rayPrincipalIdealSubgroup_iff (modulus M hM m) a.val

/-- Source: rayClassGroup_finite, instantiated at the actual modulus; [RW-rec]. [RW26, p. 20]. -/
theorem group_finite (m : ℕ) : Finite (Group M hM m) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K (modulus M hM m)
  let : Finite (RayClass.RayClassGroup m') := inferInstance
  exact Finite.of_equiv (RayClass.RayClassGroup m')
    (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K (modulus M hM m)).symm.toEquiv

#check @RayClassModulus
#check @RayClassGroup
#check @mem_rayPrincipalIdealSubgroup_iff
#check @rayClassOfFinitePrime
#print modulus
#print idealClass
#print principalClass

end SICLean.L5.RayArithmeticModulus
