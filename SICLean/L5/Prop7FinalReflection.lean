import SICLean.L5.Descent
import SICLean.L5.OddPrimeSpecialization

set_option autoImplicit false

/-!
# The double-negative class acts by label reflection

[RW-rec, Lemma 8, Prop. 4, pp. 14--15] sign classes; p. 18, Proposition 7
proof. The general Proposition 5/Theorem 9 is not assumed. Chebotarev is again applied
over Q to each prescribed g. Its restriction to H is doubleArtin; both contracted ray
classes are t, so both Theorem 8 candidates are U(-x). The enlarged finite bad set gives
equality. Every statement allows t=1, and zero is retained. No density comparison,
splitting-set difference, or separate trivial-sign branch is introduced.
-/

noncomputable section
open scoped NumberField MatrixGroups

namespace SICLean.L5.Prop7FinalReflection

open GoodReductionLocal FrobeniusPrimes

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (m : ℕ)
local notation "F" => DescentField.field M hM m
local notation "n" => RayArithmeticModulus.level M hM m
local notation "H" => ClassFieldTransport.H M hM n
local notation "U" => SplitPrimeValues.normalizedLift
  (ActualField.periodData M hM) (ActualLattice.stableLattice M hM)
local notation "u" => DescentField.normalizedInEnvelope M hM m

/-- Restriction through the finite envelope agrees with the existing absolute restriction to H
inside the same Qbar. -/
theorem restrict_absolute (σ : Galois.QbarAut) :
    DescentField.restrictH M hM m
      (FiniteGaloisEnvelope.restrictQbarAut (ClassFieldTransport.qbarField M hM n)
        (DescentField.normalizedValues M hM) σ) =
      ClassFieldConjugation.restriction M hM n σ := by
  apply AlgEquiv.ext
  intro a
  apply Subtype.ext
  change (DescentField.restrictH M hM m (σ.restrictNormal F) a : Galois.Qbar) =
    (ClassFieldConjugation.restriction M hM n σ a : Galois.Qbar)
  rw [DescentField.restrictH_apply, AlgEquiv.restrictNormal_apply,
    ClassFieldConjugation.restriction_apply]
  rfl

/-- Normal-extension lifting supplies a finite g for the given H-automorphism; its existence is not
part of a definition. -/
theorem exists_finite_lift_doubleArtin :
    ∃ g : F ≃ₐ[ℚ] F,
      DescentField.restrictH M hM m g = ClassFieldInfinite.doubleArtin M hM n := by
  exact FrobeniusRestriction.restrictGalois_surjective F
    (ClassFieldTransport.qbarField M hM n) (DescentField.classField_le M hM m)
    (ClassFieldInfinite.doubleArtin M hM n)

/-- Exactly the reflection-target Theorem 8 statement after both ray classes have been identified as
t.
-/
theorem reflection_congruence_at_good (hm : RayArithmeticOrder.ValidLevel M hM m)
    (p : ℕ) (hp : DescentGoodPrimes.GoodPrime M hM m p)
    (g : F ≃ₐ[ℚ] F)
    (hg : DescentField.restrictH M hM m g = ClassFieldInfinite.doubleArtin M hM n)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p)) (hFrob : arithFrob F P = g) :
    ∀ x, congruentAt F P (u x ^ p) (u (-x)) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hgK := DescentArtin.fixesK_of_restrictH_eq_doubleArtin M hM m g hg
  have hunram := DescentGoodPrimes.goodPrime_unramified M hM m p hp P hP
  have hsplit := DescentSplitPrimes.splitsCompletely_of_exact_frobenius
    M hM m p hp.1 g hgK P hP hunram hFrob
  have hlevel := DescentGoodPrimes.goodPrime_not_dvd_level M hM m hm p hp
  let r := DescentSplitPrimes.contractedPrime M hM m P
  let q := RayArithmeticConjugation.primeConjugation M hM r
  have hr := DescentSplitPrimes.contractedPrime_liesOver M hM m p P hP
  have hq := DescentSplitPrimes.conjugate_liesOver M hM p r hr
  have hcr := DescentSplitPrimes.prime_coprime_level M hM m p hp.1 hlevel r hr
  have hcq := DescentSplitPrimes.prime_coprime_level M hM m p hp.1 hlevel q hq
  obtain ⟨hrclass, hqclass⟩ := DescentArtin.both_classes_t M hM m hm p hp.1
    hsplit hlevel g hg P hP hunram hFrob hcr hcq
  have hpair := DescentSplitPrimes.contracted_isSplitPair M hM m p hp.1
    g hgK P hP hunram hFrob
  have hc : ¬ p ∣ RayArithmeticOrder.conductor M hM := by
    intro h
    exact hlevel (dvd_mul_of_dvd_left h m)
  have hlocal := SplitFrobeniusFinite.actual_locallyMaximal M hM hp.1 hc
  have hchar : FinitePlace.residueChar P = p := by
    rw [OddPrimeSpecialization.residueChar_eq_primeBelow]
    exact primeBelow_eq_of_liesOver F P p hp.1 hP
  exact DescentCandidates.theorem8_reflection_of_classes M hM m hm F
    (DescentGoodPrimes.goodPrime_ne_two M hM m p hp) hlocal hpair
    hcr hcq hrclass hqclass P hchar u (DescentField.coe_normalizedInEnvelope M hM m)

/-- The same good-prime witness and finite collision exclusion upgrade g(U(x))≡U(-x) to equality for
all labels. -/
theorem reflection_at_good (hm : RayArithmeticOrder.ValidLevel M hM m)
    (p : ℕ) (hp : DescentGoodPrimes.GoodPrime M hM m p)
    (g : F ≃ₐ[ℚ] F)
    (hg : DescentField.restrictH M hM m g = ClassFieldInfinite.doubleArtin M hM n)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p)) (hFrob : arithFrob F P = g) :
    ∀ x, g (u x) = u (-x) := by
  intro x
  exact DescentGoodPrimes.eq_of_frobenius_common_target M hM m p hp P hP
    g hFrob x (-x) (reflection_congruence_at_good M hM m hm p hp g hg P hP hFrob x)

/-- For every finite g fixing K and restricting to t, the normalized values reflect. It does not
require g=t on the larger field F. -/
theorem normalized_reflection_of_restrict (hm : RayArithmeticOrder.ValidLevel M hM m)
    (g : F ≃ₐ[ℚ] F) (hgK : DescentField.restrictK M hM m g = 1)
    (hgH : DescentField.restrictH M hM m g = ClassFieldInfinite.doubleArtin M hM n) :
    ∀ x, g (u x) = u (-x) := by
  obtain ⟨p, hp, hgood, _hsplit, P, hP, _hunram, hFrob⟩ :=
    (DescentSplitPrimes.infinite_exact_frobenius_split M hM m g hgK
      (DescentGoodPrimes.badPrimes M hM m)).nonempty
  exact reflection_at_good M hM m hm p ⟨hp, hgood⟩ g hgH P hP hFrob

/-- Convenient stronger interface: fixing K follows from the displayed restriction to doubleArtin
and K≤H. -/
theorem normalized_reflection (hm : RayArithmeticOrder.ValidLevel M hM m)
    (g : F ≃ₐ[ℚ] F)
    (hgH : DescentField.restrictH M hM m g = ClassFieldInfinite.doubleArtin M hM n) :
    ∀ x, g (u x) = u (-x) := by
  exact normalized_reflection_of_restrict M hM m hm g
    (DescentArtin.fixesK_of_restrictH_eq_doubleArtin M hM m g hgH) hgH

/-- The t-action statement on the values already descended to H. -/
theorem doubleArtin_normalized_action (hm : RayArithmeticOrder.ValidLevel M hM m)
    (x : ActualLattice.Group M hM) :
    ClassFieldInfinite.doubleArtin M hM n (Descent.normalizedInClassField M hM m hm x) =
      Descent.normalizedInClassField M hM m hm (-x) := by
  obtain ⟨g, hg⟩ := exists_finite_lift_doubleArtin M hM m
  apply Subtype.ext
  have hx := congrArg (fun a : F => (a : Galois.Qbar))
    (normalized_reflection M hM m hm g hg x)
  rw [← Descent.restricted_action M hM m hm g x, hg] at hx
  exact hx

/-- The same action in Qbar, using the existing K-Artin map. -/
theorem artin_doubleSign_normalized_action (hm : RayArithmeticOrder.ValidLevel M hM m)
    (x : ActualLattice.Group M hM) :
    (ClassFieldTransport.artin M hM n (ClassFieldSigns.doubleSign M hM n)
      (Descent.normalizedInClassField M hM m hm x) : Galois.Qbar) = U (-x) := by
  change (ClassFieldInfinite.doubleArtin M hM n
    (Descent.normalizedInClassField M hM m hm x) : Galois.Qbar) = U (-x)
  rw [doubleArtin_normalized_action, Descent.coe_normalizedInClassField]

/-- All absolute lifts of t have the same action on U, by actual membership in H, never by a choice
of an unrelated embedding. -/
theorem absolute_normalized_reflection (hm : RayArithmeticOrder.ValidLevel M hM m)
    (σ : Galois.QbarAut)
    (hσ : ClassFieldConjugation.restriction M hM n σ = ClassFieldInfinite.doubleArtin M hM n) :
    ∀ x, σ (U x) = U (-x) := by
  intro x
  have hx := Descent.absolute_restricted_action M hM m hm σ x
  rw [hσ, doubleArtin_normalized_action, Descent.coe_normalizedInClassField] at hx
  exact hx.symm

/-- The same t-action in the original matrix labels and normalization, using actual_valueLift and
labelEquiv.map_neg. -/
theorem doubleArtin_matrix_normalized (hm : RayArithmeticOrder.ValidLevel M hM m)
    (j : L4.SpecialValueGroup M) :
    (ClassFieldInfinite.doubleArtin M hM n
      (Descent.normalizedInClassField M hM m hm (ActualLattice.labelEquiv M hM j)) : Galois.Qbar) =
      ActualValues.matrixLift M hM (-j) / ActualValues.matrixLift M hM 0 := by
  rw [doubleArtin_normalized_action, Descent.coe_normalizedInClassField]
  change SplitPrimeValues.valueLift _ _ _ / SplitPrimeValues.valueLift _ _ 0 = _
  rw [← map_neg (ActualLattice.labelEquiv M hM),
    SplitPrimeValues.actual_valueLift, SplitPrimeValues.actual_valueLift,
    ActualValues.valueLift_label, ← map_zero (ActualLattice.labelEquiv M hM),
    ActualValues.valueLift_label]

end SICLean.L5.Prop7FinalReflection
