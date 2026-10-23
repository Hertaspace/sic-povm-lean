import SICLean.L5.DescentArtin
import SICLean.L5.DescentGoodPrimes
import SICLean.L5.DescentCandidates
import SICLean.L5.OddPrimeSpecialization

set_option autoImplicit false

/-!
# Descent of the normalized values to H

The fixed-field conclusion is [RW-rec, pp. 14--15, Prop. 4].
Algebraicity of the values is [RW26, p. 3, Thm. 1]; their identification
is [RW26, p. 20, (37)].

For each g fixing H, Chebotarev over ℚ supplies a prime outside the finite
bad set. Both ray classes are trivial, both candidates equal U(x), and
avoidance of the difference support upgrades the Frobenius congruence to
equality. The fixed-field theorem then places U(x) in H, including x = 0.
The argument does not compare densities of splitting sets.
-/

noncomputable section
open scoped NumberField MatrixGroups

namespace SICLean.L5.Descent

open GoodReductionLocal FrobeniusPrimes

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (m : ℕ)
local notation "F" => DescentField.field M hM m
local notation "H" => ClassFieldTransport.H M hM (RayArithmeticModulus.level M hM m)
local notation "U" => SplitPrimeValues.normalizedLift
  (ActualField.periodData M hM) (ActualLattice.stableLattice M hM)
local notation "u" => DescentField.normalizedInEnvelope M hM m

/-- Identity-target application of [RW-rec, Thm. 8], with both ray classes
derived from g|H = 1 and neither translated family adjoined.
[RW-rec, Prop. 4]. -/
theorem identity_congruence_at_good (hm : RayArithmeticOrder.ValidLevel M hM m)
    (p : ℕ) (hp : DescentGoodPrimes.GoodPrime M hM m p)
    (g : F ≃ₐ[ℚ] F) (hg : DescentField.restrictH M hM m g = 1)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p)) (hFrob : arithFrob F P = g) :
    ∀ x, congruentAt F P (u x ^ p) (u x) := by
  let : Fact p.Prime := ⟨hp.1⟩
  have hunram := DescentGoodPrimes.goodPrime_unramified M hM m p hp P hP
  have hgK := DescentArtin.fixesK_of_restrictH_eq_one M hM m g hg
  have hsplit := DescentSplitPrimes.splitsCompletely_of_exact_frobenius
    M hM m p hp.1 g hgK P hP hunram hFrob
  have hpair := DescentSplitPrimes.contracted_isSplitPair
    M hM m p hp.1 g hgK P hP hunram hFrob
  have hlevel := DescentGoodPrimes.goodPrime_not_dvd_level M hM m hm p hp
  have hconductor : ¬ p ∣ RayArithmeticOrder.conductor M hM := by
    intro h
    exact hlevel (dvd_mul_of_dvd_left h m)
  have hr := DescentSplitPrimes.contractedPrime_liesOver M hM m p P hP
  have hq := DescentSplitPrimes.conjugate_liesOver M hM p _ hr
  have hcr := DescentSplitPrimes.prime_coprime_level M hM m p hp.1 hlevel _ hr
  have hcq := DescentSplitPrimes.prime_coprime_level M hM m p hp.1 hlevel _ hq
  obtain ⟨hrclass, hqclass⟩ := DescentArtin.both_classes_one
    M hM m p hp.1 hsplit hlevel g hg P hP hunram hFrob hcr hcq
  have hchar : FinitePlace.residueChar P = p :=
    (OddPrimeSpecialization.residueChar_eq_primeBelow F P).trans
      (primeBelow_eq_of_liesOver F P p hp.1 hP)
  exact DescentCandidates.theorem8_identity_of_classes M hM m hm F
    (DescentGoodPrimes.goodPrime_ne_two M hM m p hp)
    (SplitFrobeniusFinite.actual_locallyMaximal M hM hp.1 hconductor)
    hpair hcr hcq hrclass hqclass P hchar u
    (DescentField.coe_normalizedInEnvelope M hM m)

/-- Exclusion of the nonzero differences turns the preceding congruence
into equality at the chosen good prime. [RW-rec, Prop. 4]. -/
theorem fixes_values_at_good (hm : RayArithmeticOrder.ValidLevel M hM m)
    (p : ℕ) (hp : DescentGoodPrimes.GoodPrime M hM m p)
    (g : F ≃ₐ[ℚ] F) (hg : DescentField.restrictH M hM m g = 1)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p)) (hFrob : arithFrob F P = g) :
    ∀ x, g (u x) = u x := by
  intro x
  exact DescentGoodPrimes.eq_of_frobenius_common_target M hM m p hp P hP g hFrob
    x x (identity_congruence_at_good M hM m hm p hp g hg P hP hFrob x)

/-- Fixed values under Gal(F/H). For each g, `exists_good_exact_frobenius`
supplies a good prime, without a density comparison. [RW-rec, Prop. 4]. -/
theorem fixes_normalized_values (hm : RayArithmeticOrder.ValidLevel M hM m)
    (g : F ≃ₐ[ℚ] F) (hg : DescentField.restrictH M hM m g = 1) :
    ∀ x, g (u x) = u x := by
  obtain ⟨p, hp, P, hP, _, hFrob⟩ :=
    DescentGoodPrimes.exists_good_exact_frobenius M hM m g
  exact fixes_values_at_good M hM m hm p hp g hg P hP hFrob

/-- The restriction kernel is the elementwise fixing subgroup, in the shape
used by `FiniteGaloisFixed`. [RW-rec, Prop. 4]. -/
theorem restrictH_eq_one_iff (g : F ≃ₐ[ℚ] F) :
    DescentField.restrictH M hM m g = 1 ↔
      ∀ a : F, (a : Galois.Qbar) ∈ H → g a = a := by
  constructor
  · intro hg a ha
    apply Subtype.ext
    have h := DescentField.restrictH_apply M hM m g ⟨(a : Galois.Qbar), ha⟩
    rw [hg] at h
    exact h.symm
  · intro hg
    apply AlgEquiv.ext
    intro a
    apply Subtype.ext
    change (DescentField.restrictH M hM m g a : Galois.Qbar) = (a : Galois.Qbar)
    rw [DescentField.restrictH_apply]
    exact congrArg (fun b : F => (b : Galois.Qbar))
      (hg (IntermediateField.inclusion (DescentField.classField_le M hM m) a) a.property)

/-- Every element of the finite range is fixed by the fixing subgroup.
There is no value-in-H hypothesis. [RW-rec, Prop. 4]. -/
theorem all_fixers_fix_range (hm : RayArithmeticOrder.ValidLevel M hM m)
    (g : F ≃ₐ[ℚ] F) (hg : ∀ a : F, (a : Galois.Qbar) ∈ H → g a = a) :
    ∀ a ∈ DescentGoodPrimes.values M hM m, g a = a := by
  intro a ha
  obtain ⟨x, rfl⟩ := (DescentGoodPrimes.mem_values_iff M hM m a).mp ha
  exact fixes_normalized_values M hM m hm g ((restrictH_eq_one_iff M hM m g).mpr hg) x

/-- Pointwise membership of the normalized values in H, including the zero class.
[RW-rec, Prop. 4]. -/
theorem normalized_mem_classField (hm : RayArithmeticOrder.ValidLevel M hM m)
    (x : ActualLattice.Group M hM) : U x ∈ H := by
  exact FiniteGaloisFixed.mem_base_of_all_fixers_fix
    (ClassFieldTransport.qbarField M hM (RayArithmeticModulus.level M hM m))
    (DescentField.normalizedValues M hM) (u x)
    (fun g hg => all_fixers_fix_range M hM m hm g hg (u x)
      (DescentGoodPrimes.normalized_mem_values M hM m x))

/-- The same membership for the whole finite set of normalized values.
[RW-rec, Prop. 4]. -/
theorem normalizedValues_subset_classField (hm : RayArithmeticOrder.ValidLevel M hM m) :
    (DescentField.normalizedValues M hM : Set Galois.Qbar) ⊆ H := by
  intro a ha
  obtain ⟨x, rfl⟩ := (DescentField.mem_normalizedValues_iff M hM a).mp ha
  exact normalized_mem_classField M hM m hm x

/-- The normal envelope equals the class field once the values lie in H.
This equality is not an assumption in the definition of F. [RW-rec, Prop. 4]. -/
theorem field_eq_classField (hm : RayArithmeticOrder.ValidLevel M hM m) :
    DescentField.field M hM m = ClassFieldTransport.qbarField M hM
      (RayArithmeticModulus.level M hM m) := by
  apply le_antisymm
  · exact (FiniteGaloisEnvelope.envelope_le_iff _ _ _).mpr
      ⟨le_rfl, normalizedValues_subset_classField M hM m hm⟩
  · exact DescentField.classField_le M hM m

/-- The normalized value as an element of H.
Membership is the preceding theorem. [RW-rec, Prop. 4]. -/
def normalizedInClassField (hm : RayArithmeticOrder.ValidLevel M hM m)
    (x : ActualLattice.Group M hM) : H :=
  ⟨U x, normalized_mem_classField M hM m hm x⟩

/-- The element of H is the same number in the fixed ℚ̄. [RW-rec, Prop. 4]. -/
theorem coe_normalizedInClassField (hm : RayArithmeticOrder.ValidLevel M hM m)
    (x : ActualLattice.Group M hM) :
    (normalizedInClassField M hM m hm x : Galois.Qbar) = U x := by
  rfl

/-- [RW-rec, p. 3, Def. 1]: the zero label is 1. -/
theorem normalizedInClassField_zero (hm : RayArithmeticOrder.ValidLevel M hM m) :
    normalizedInClassField M hM m hm 0 = 1 := by
  apply Subtype.ext
  exact SplitPrimeValues.normalizedLift_zero
    (ActualField.periodData M hM) (ActualLattice.stableLattice M hM)

/-- Restriction to H applied to a normalized value, with the membership
already recorded and with no choice of preimage. [RW-rec, Prop. 4]. -/
theorem restricted_action (hm : RayArithmeticOrder.ValidLevel M hM m)
    (g : F ≃ₐ[ℚ] F) (x : ActualLattice.Group M hM) :
    (DescentField.restrictH M hM m g (normalizedInClassField M hM m hm x) : Galois.Qbar) =
      (g (u x) : Galois.Qbar) := by
  exact DescentField.restrictH_apply M hM m g (normalizedInClassField M hM m hm x)

/-- Absolute Galois action, in the form used for the infinite places.
[RW-rec, Prop. 4]. -/
theorem absolute_restricted_action (hm : RayArithmeticOrder.ValidLevel M hM m)
    (σ : Galois.QbarAut) (x : ActualLattice.Group M hM) :
    (ClassFieldConjugation.restriction M hM (RayArithmeticModulus.level M hM m) σ
      (normalizedInClassField M hM m hm x) : Galois.Qbar) = σ (U x) := by
  exact ClassFieldConjugation.restriction_apply M hM (RayArithmeticModulus.level M hM m)
    σ (normalizedInClassField M hM m hm x)

end SICLean.L5.Descent
