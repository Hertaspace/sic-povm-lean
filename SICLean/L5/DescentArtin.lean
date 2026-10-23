import SICLean.L5.DescentSplitPrimes
import SICLean.L5.DescentRayClass

set_option autoImplicit false

/-!
# Arithmetic Frobenius, Artin restriction, and both ray classes

[RW-rec, §8, pp. 13--15]. The arithmetic normalization is
`ClassFieldTransport.artin_prime_arithFrobAt`. Ideal conjugation and
`RayArithmeticSigns.conjugation_t` fix the classes 1 and t.
[RW26, p. 20, (37)] identifies K/I. The comparison of Frobenius with the
Artin symbol is formalized here.

The relative Frobenius has residue cardinality p because p splits in K.
Restrictions and contractions follow the tower K ≤ H ≤ F inside the fixed
ℚ̄. Classes below lie in the arithmetic quotient; `DescentRayClass`
transports them to the Artin quotient.
-/

noncomputable section
open scoped NumberField MatrixGroups

namespace SICLean.L5.DescentArtin

open GoodReductionLocal FrobeniusPrimes FrobeniusSplitting

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (m : ℕ)
local notation "K" => ActualField.baseField M hM
local notation "F" => DescentField.field M hM m
local notation "n" => RayArithmeticModulus.level M hM m
local notation "H" => ClassFieldTransport.H M hM n
local notation "r" P => DescentSplitPrimes.contractedPrime M hM m P

/-- Contraction from F to H along the inclusion, at the prime under P. [RW-rec, §8]. -/
def classFieldPrime (P : Prime F) : Prime H :=
  FrobeniusRestriction.contractPrime F H (DescentField.classField_le M hM m) P

/-- Transitivity identifies the two contraction paths. [RW-rec, §8]. -/
theorem contractPrime_tower (P : Prime F) :
    FrobeniusRestriction.contractPrime H K (ClassFieldTransport.base_le M hM n)
      (classFieldPrime M hM m P) = r P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext x
  rfl

/-- The relative Artin symbol is taken at this contracted prime of K. [RW-rec, §8]. -/
theorem classFieldPrime_liesOver (P : Prime F) :
    (classFieldPrime M hM m P).asIdeal.LiesOver (r P).asIdeal := by
  apply (Ideal.liesOver_iff _ _).mpr
  exact (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (contractPrime_tower M hM m P)).symm

/-- Complete splitting over ℚ gives relative Frobenius exponent p. [RW-rec, §8]. -/
theorem residue_card_of_split (p : ℕ) (hp : p.Prime)
    (hsplit : splitsCompletely K p) (v : FinitePlace.Prime K)
    (hv : v.asIdeal.LiesOver (rationalIdeal p)) : Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  have : v.asIdeal.LiesOver (rationalIdeal p) := hv
  have : Fact p.Prime := ⟨hp⟩
  have : (rationalIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hcard := Ideal.cardQuot_pow_inertiaDeg (rationalIdeal p) v.asIdeal
  have hf := (hsplit.2 v hv).2
  simpa only [hf, pow_one, Submodule.cardQuot_apply, rationalIdeal,
    Int.card_ideal_quot] using hcard.symm

/-- Equality of the relative and absolute Frobenius elements at an unramified
prime of H over a split rational prime. The relative automorphism is over K
and the absolute one is over ℚ, so the comparison restricts scalars. [RW-rec, §8]. -/
theorem relativeFrob_eq_absolute (p : ℕ) (hp : p.Prime)
    (hsplit : splitsCompletely K p) (w : Prime H)
    (hw : w.asIdeal.LiesOver (rationalIdeal p))
    (hunram : Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    (arithFrobAt (𝓞 K) (H ≃ₐ[K] H) w.asIdeal).restrictScalars ℚ = arithFrob H w := by
  let v : FinitePlace.Prime K :=
    ⟨w.asIdeal.under (𝓞 K), inferInstance,
      Ideal.under_ne_bot (𝓞 K) w.ne_bot⟩
  have hv : v.asIdeal.LiesOver (rationalIdeal p) := by
    constructor
    change rationalIdeal p = (w.asIdeal.under (𝓞 K)).under ℤ
    rw [Ideal.under_under]
    exact hw.over
  have hcard : Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) = p :=
    residue_card_of_split M hM p hp hsplit v hv
  have hFrob := IsArithFrobAt.arithFrobAt (𝓞 K) (H ≃ₐ[K] H) w.asIdeal
  refine FrobeniusRestriction.isArithFrobAt_unique H w hunram _ _
    ?_ (arithFrob_spec H w)
  intro x
  change (arithFrobAt (𝓞 K) (H ≃ₐ[K] H) w.asIdeal) • x -
    x ^ Nat.card (ℤ ⧸ w.asIdeal.under ℤ) ∈ w.asIdeal
  rw [base_quotient_card, primeBelow_eq_of_liesOver H w p hp hw]
  simpa only [MulSemiringAction.toAlgHom_apply, hcard] using hFrob x

/-- [RW-rec, p. 14, Prop. 4]: the arithmetic Artin symbol at a good prime of K
equals the absolute Frobenius, since the residue degree over the base is one. -/
theorem rationalFrob_eq_artin (p : ℕ) (hp : p.Prime)
    (hsplit : splitsCompletely K p) (w : Prime H)
    (hw : w.asIdeal.LiesOver (rationalIdeal p))
    (hgood : FrobeniusRestriction.contractPrime H K (ClassFieldTransport.base_le M hM n) w ∉
      (ClassFieldModulus.modulus M hM n).finitePart.support) :
    arithFrob H w =
      (ClassFieldTransport.artin M hM n
        (ClassFieldTheory.rayClassOfFinitePrime (ClassFieldModulus.modulus M hM n)
          (FrobeniusRestriction.contractPrime H K (ClassFieldTransport.base_le M hM n) w)
          hgood)).restrictScalars ℚ := by
  let v := FrobeniusRestriction.contractPrime H K (ClassFieldTransport.base_le M hM n) w
  have hwv : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K))
    infer_instance
  have := hwv
  have := hw
  have hvp : v.asIdeal.LiesOver (rationalIdeal p) :=
    Ideal.LiesOver.tower_bot w.asIdeal v.asIdeal (rationalIdeal p)
  have hrel : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (ClassFieldTransport.unramifiedOutside M hM n).1 v hgood
      w.asIdeal inferInstance hwv
  have habs : Algebra.IsUnramifiedAt ℤ w.asIdeal := by
    apply (unramifiedAt_iff_ramificationIdx H w).mpr
    rw [Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal w.asIdeal,
      (hsplit.2 v hvp).1]
    have := hrel
    simp only [Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 K), one_mul]
  rw [ClassFieldTransport.artin_prime_arithFrobAt M hM n v hgood w hwv]
  exact (relativeFrob_eq_absolute M hM m p hp hsplit w hw habs).symm

/-- The arithmetic integral `idealClass`. Coprimality is a property of the
contracted prime. [RW-rec, §8]. -/
theorem restrict_frobenius_eq_artin (p : ℕ) (hp : p.Prime)
    (hsplit : splitsCompletely K p) (hlevel : ¬ p ∣ n)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m (r P).asIdeal) :
    DescentField.restrictH M hM m (arithFrob F P) =
      (ClassFieldTransport.artin M hM n
        (DescentRayClass.rayGroupEquiv M hM m
          (RayArithmeticModulus.idealClass M hM m (r P).asIdeal (r P).ne_bot hc))).restrictScalars ℚ := by
  let : Algebra H F := (IntermediateField.inclusion (DescentField.classField_le M hM m)).toAlgebra
  let : IsScalarTower ℚ H F :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (DescentField.classField_le M hM m))
  have hPw : P.asIdeal.LiesOver (classFieldPrime M hM m P).asIdeal := by
    change P.asIdeal.LiesOver (P.asIdeal.under (𝓞 H))
    infer_instance
  have := hPw
  have := hP
  have hw : (classFieldPrime M hM m P).asIdeal.LiesOver (rationalIdeal p) :=
    Ideal.LiesOver.tower_bot P.asIdeal (classFieldPrime M hM m P).asIdeal (rationalIdeal p)
  have hwunram : Algebra.IsUnramifiedAt ℤ (classFieldPrime M hM m P).asIdeal := by
    apply (unramifiedAt_iff_ramificationIdx H _).mpr
    have he := Ideal.ramificationIdx_below_dvd (R := ℤ)
      (classFieldPrime M hM m P).asIdeal P.asIdeal
    rw [(unramifiedAt_iff_ramificationIdx F P).mp hunram] at he
    exact Nat.dvd_one.mp he
  have hgood := DescentSplitPrimes.prime_not_mem_modulus_support M hM m p hp hlevel
    (r P) (DescentSplitPrimes.contractedPrime_liesOver M hM m p P hP)
  have hclass := DescentRayClass.idealClass_finitePrime_transport M hM m (r P) hc hgood
  change FrobeniusRestriction.restrictGalois F H (DescentField.classField_le M hM m)
    (arithFrob F P) = _
  rw [FrobeniusRestriction.arithFrob_restrict F H (DescentField.classField_le M hM m)
    P hwunram]
  change arithFrob H (classFieldPrime M hM m P) = _
  rw [hclass]
  have hArtin := rationalFrob_eq_artin M hM m p hp hsplit (classFieldPrime M hM m P) hw
    (by simpa only [contractPrime_tower] using hgood)
  simpa only [contractPrime_tower] using hArtin

/-- Artin injectivity gives the trivial class from g|H = 1. [RW-rec, §8]. -/
theorem class_one_of_restrictH (p : ℕ) (hp : p.Prime)
    (hsplit : splitsCompletely K p) (hlevel : ¬ p ∣ n)
    (g : F ≃ₐ[ℚ] F) (hg : DescentField.restrictH M hM m g = 1)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal) (hFrob : arithFrob F P = g)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m (r P).asIdeal) :
    RayArithmeticModulus.idealClass M hM m (r P).asIdeal (r P).ne_bot hc = 1 := by
  apply (DescentRayClass.artin_eq_one_iff M hM m _).mp
  rw [← restrict_frobenius_eq_artin M hM m p hp hsplit hlevel P hP hunram hc,
    hFrob, hg]

/-- The same identification when g|H = `doubleArtin`, including the case t = 1.
[RW-rec, §8]. -/
theorem class_t_of_restrictH (hm : RayArithmeticOrder.ValidLevel M hM m)
    (p : ℕ) (hp : p.Prime) (hsplit : splitsCompletely K p) (hlevel : ¬ p ∣ n)
    (g : F ≃ₐ[ℚ] F) (hg : DescentField.restrictH M hM m g = ClassFieldInfinite.doubleArtin M hM n)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal) (hFrob : arithFrob F P = g)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m (r P).asIdeal) :
    RayArithmeticModulus.idealClass M hM m (r P).asIdeal (r P).ne_bot hc =
      RayArithmeticSigns.t M hM m hm := by
  apply (DescentRayClass.artin_eq_doubleArtin_iff M hM m hm _).mp
  rw [← restrict_frobenius_eq_artin M hM m p hp hsplit hlevel P hP hunram hc,
    hFrob, hg]

/-- Ideal conjugation fixes the trivial class. [RW-rec, §8]. -/
theorem conjugate_class_one (v : FinitePlace.Prime K)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m v.asIdeal)
    (hc' : RayArithmeticModulus.CoprimeIdeal M hM m
      (RayArithmeticConjugation.primeConjugation M hM v).asIdeal)
    (hv : RayArithmeticModulus.idealClass M hM m v.asIdeal v.ne_bot hc = 1) :
    RayArithmeticModulus.idealClass M hM m
      (RayArithmeticConjugation.primeConjugation M hM v).asIdeal
      (RayArithmeticConjugation.primeConjugation M hM v).ne_bot hc' = 1 := by
  have h := RayArithmeticConjugation.rayConjugation_idealClass M hM m
    v.asIdeal v.ne_bot hc
  rw [hv, map_one] at h
  simpa only [← RayArithmeticConjugation.primeConjugation_asIdeal M hM v] using h.symm

/-- `RayArithmeticSigns.conjugation_t` fixes the class t under quadratic
conjugation, including when t = 1. [RW-rec, §8]. -/
theorem conjugate_class_t (hm : RayArithmeticOrder.ValidLevel M hM m)
    (v : FinitePlace.Prime K)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m v.asIdeal)
    (hc' : RayArithmeticModulus.CoprimeIdeal M hM m
      (RayArithmeticConjugation.primeConjugation M hM v).asIdeal)
    (hv : RayArithmeticModulus.idealClass M hM m v.asIdeal v.ne_bot hc =
      RayArithmeticSigns.t M hM m hm) :
    RayArithmeticModulus.idealClass M hM m
      (RayArithmeticConjugation.primeConjugation M hM v).asIdeal
      (RayArithmeticConjugation.primeConjugation M hM v).ne_bot hc' =
        RayArithmeticSigns.t M hM m hm := by
  have h := RayArithmeticConjugation.rayConjugation_idealClass M hM m
    v.asIdeal v.ne_bot hc
  rw [hv, RayArithmeticSigns.conjugation_t] at h
  simpa only [← RayArithmeticConjugation.primeConjugation_asIdeal M hM v] using h.symm

/-- The two trivial classes used by the identity target.
The second prime is the conjugate of P ∩ K. [RW-rec, §8]. -/
theorem both_classes_one (p : ℕ) (hp : p.Prime)
    (hsplit : splitsCompletely K p) (hlevel : ¬ p ∣ n)
    (g : F ≃ₐ[ℚ] F) (hg : DescentField.restrictH M hM m g = 1)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal) (hFrob : arithFrob F P = g)
    (hcr : RayArithmeticModulus.CoprimeIdeal M hM m (r P).asIdeal)
    (hcq : RayArithmeticModulus.CoprimeIdeal M hM m
      (RayArithmeticConjugation.primeConjugation M hM (r P)).asIdeal) :
    RayArithmeticModulus.idealClass M hM m (r P).asIdeal (r P).ne_bot hcr = 1 ∧
      RayArithmeticModulus.idealClass M hM m
        (RayArithmeticConjugation.primeConjugation M hM (r P)).asIdeal
        (RayArithmeticConjugation.primeConjugation M hM (r P)).ne_bot hcq = 1 := by
  have hr := class_one_of_restrictH M hM m p hp hsplit hlevel g hg P hP hunram hFrob hcr
  exact ⟨hr, conjugate_class_one M hM m (r P) hcr hcq hr⟩

/-- The two classes equal to t used by the reflection target. [RW-rec, §8]. -/
theorem both_classes_t (hm : RayArithmeticOrder.ValidLevel M hM m)
    (p : ℕ) (hp : p.Prime) (hsplit : splitsCompletely K p) (hlevel : ¬ p ∣ n)
    (g : F ≃ₐ[ℚ] F) (hg : DescentField.restrictH M hM m g = ClassFieldInfinite.doubleArtin M hM n)
    (P : Prime F) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hunram : Algebra.IsUnramifiedAt ℤ P.asIdeal) (hFrob : arithFrob F P = g)
    (hcr : RayArithmeticModulus.CoprimeIdeal M hM m (r P).asIdeal)
    (hcq : RayArithmeticModulus.CoprimeIdeal M hM m
      (RayArithmeticConjugation.primeConjugation M hM (r P)).asIdeal) :
    RayArithmeticModulus.idealClass M hM m (r P).asIdeal (r P).ne_bot hcr =
        RayArithmeticSigns.t M hM m hm ∧
      RayArithmeticModulus.idealClass M hM m
        (RayArithmeticConjugation.primeConjugation M hM (r P)).asIdeal
        (RayArithmeticConjugation.primeConjugation M hM (r P)).ne_bot hcq =
          RayArithmeticSigns.t M hM m hm := by
  have hr := class_t_of_restrictH M hM m hm p hp hsplit hlevel g hg P hP hunram hFrob hcr
  exact ⟨hr, conjugate_class_t M hM m hm (r P) hcr hcq hr⟩

/-- Since K ≤ H, an automorphism fixing H fixes K. [RW-rec, §8]. -/
theorem fixesK_of_restrictH_eq_one (g : F ≃ₐ[ℚ] F)
    (hg : DescentField.restrictH M hM m g = 1) : DescentField.restrictK M hM m g = 1 := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [DescentField.restrictK_apply]
  have h := congrArg (fun σ : H ≃ₐ[ℚ] H =>
    (σ (IntermediateField.inclusion (ClassFieldTransport.base_le M hM n) x) : Galois.Qbar)) hg
  rw [DescentField.restrictH_apply] at h
  exact h

/-- `doubleArtin` is a K-automorphism, so any of its lifts to F fixes K.
Membership of U in H is not used, and t may be trivial. [RW-rec, §8]. -/
theorem fixesK_of_restrictH_eq_doubleArtin (g : F ≃ₐ[ℚ] F)
    (hg : DescentField.restrictH M hM m g = ClassFieldInfinite.doubleArtin M hM n) :
    DescentField.restrictK M hM m g = 1 := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [DescentField.restrictK_apply]
  have h := congrArg (fun σ : H ≃ₐ[ℚ] H =>
    (σ (algebraMap K H x) : Galois.Qbar)) hg
  rw [DescentField.restrictH_apply] at h
  exact h.trans (congrArg (fun y : H => (y : Galois.Qbar))
    ((ClassFieldTransport.artin M hM n (ClassFieldSigns.doubleSign M hM n)).commutes x))

end SICLean.L5.DescentArtin
