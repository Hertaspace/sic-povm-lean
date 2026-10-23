import SICLean.L5.DescentField
import SICLean.L5.DescentChebotarev
import SICLean.L5.GoodReductionSeparation

set_option autoImplicit false

/-!
# One finite bad set for the identity and reflection targets

The bad set used with [RW-rec, pp. 14--15, Prop. 4] is
`GoodReductionSupport.comparisonBadPrimes` on the normalized values.
Algebraicity is [RW26, p. 3, Thm. 1], and [RW26, p. 20, (37)] identifies
the values.

B is the comparison bad set of S_F against S_F. It contains the support of
every nonzero difference g(u) - u', including g(u) - u. Its definition does
not assume an equality or membership in H. Denominators, ramified primes,
2, and the prime divisors of cm are included.
-/

noncomputable section
open scoped NumberField MatrixGroups Classical

namespace SICLean.L5.DescentGoodPrimes

open GoodReductionLocal FrobeniusPrimes

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "F" => DescentField.field M hM
local notation "u" => DescentField.normalizedInEnvelope M hM

/-- The finite range, as elements of F by the inclusion into the envelope.
These are the normalized values, not translates and not elements assumed
to lie in H. [RW-rec, Prop. 4]. -/
def values (m : ℕ) : Finset (F m) :=
  letI := Fintype.ofFinite (ActualLattice.Group M hM)
  Finset.univ.image (u m)

/-- Membership in the finite image, with the original labels. [RW-rec, Prop. 4]. -/
theorem mem_values_iff (m : ℕ) (a : F m) :
    a ∈ values M hM m ↔ ∃ x : ActualLattice.Group M hM, u m x = a := by
  simp [values]

/-- Every normalized value belongs, including x = 0. [RW-rec, Prop. 4]. -/
theorem normalized_mem_values (m : ℕ) (x : ActualLattice.Group M hM) :
    u m x ∈ values M hM m := by
  exact (mem_values_iff M hM m _).mpr ⟨x, rfl⟩

/-- [RW-rec, p. 3, Def. 1]: 1 lies in the range. -/
theorem one_mem_values (m : ℕ) : (1 : F m) ∈ values M hM m := by
  exact (mem_values_iff M hM m _).mpr
    ⟨0, DescentField.normalizedInEnvelope_zero M hM m⟩

/-- The finite union `GoodReductionSupport.comparisonBadPrimes`. [RW-rec, Prop. 4]. -/
def badPrimes (m : ℕ) : Finset ℕ :=
  GoodReductionSupport.comparisonBadPrimes (F m)
    (RayArithmeticModulus.level M hM m) (values M hM m) (values M hM m)

/-- A rational prime outside this finite set. -/
def GoodPrime (m p : ℕ) : Prop := p.Prime ∧ p ∉ badPrimes M hM m

/-- 2 belongs to the bad set. [RW-rec, Prop. 4]. -/
theorem two_mem_badPrimes (m : ℕ) : 2 ∈ badPrimes M hM m := by
  simp [badPrimes, GoodReductionSupport.comparisonBadPrimes,
    GoodReductionSupport.badPrimes]

/-- Prime divisors of the level are excluded. [RW-rec, Prop. 4]. -/
theorem level_factors_subset_badPrimes (m : ℕ) :
    (RayArithmeticModulus.level M hM m).primeFactors ⊆ badPrimes M hM m := by
  intro p hp
  apply Finset.mem_union_left
  exact (GoodReductionSupport.mem_badPrimes_iff (F m) _ _ p).mpr
    (Or.inr (Or.inl hp))

/-- Prime divisors of the field discriminant are excluded. [RW-rec, Prop. 4]. -/
theorem ramifiedPrimes_subset_badPrimes (m : ℕ) :
    GoodReductionSupport.ramifiedPrimes (F m) ⊆ badPrimes M hM m := by
  intro p hp
  apply Finset.mem_union_left
  exact (GoodReductionSupport.mem_badPrimes_iff (F m) _ _ p).mpr
    (Or.inr (Or.inr (Or.inl hp)))

/-- Support of a nonzero comparison g(u x) - u y, including the pairs
U(x) and U(-x). [RW-rec, Prop. 4]. -/
theorem comparison_support_subset_badPrimes (m : ℕ) (g : F m ≃ₐ[ℚ] F m)
    (x y : ActualLattice.Group M hM) (hne : g (u m x) - u m y ≠ 0) :
    GoodReductionSupport.primeSupport (F m) (g (u m x) - u m y) ⊆
      badPrimes M hM m := by
  intro p hp
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨g (u m x) - u m y, ?_, hp⟩
  exact (GoodReductionSupport.mem_comparisonDifferences_iff (F m) _ _ _).mpr
    ⟨hne, g, u m x, normalized_mem_values M hM m x,
      u m y, normalized_mem_values M hM m y, rfl⟩

/-- A good prime is odd, as required by [RW-rec, Thm. 8]. -/
theorem goodPrime_ne_two (m p : ℕ) (hp : GoodPrime M hM m p) : p ≠ 2 := by
  intro hp2
  exact hp.2 (hp2 ▸ two_mem_badPrimes M hM m)

/-- Positivity of cm is used here; `Nat.primeFactors 0` does not apply. -/
theorem goodPrime_not_dvd_level (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (p : ℕ) (hp : GoodPrime M hM m p) :
    ¬ p ∣ RayArithmeticModulus.level M hM m := by
  intro hdiv
  apply hp.2
  apply level_factors_subset_badPrimes M hM m
  exact Nat.mem_primeFactors.mpr
    ⟨hp.1, hdiv, (RayArithmeticModulus.level_pos M hM m hm).ne'⟩

/-- Every prime P above a good rational prime is unramified. [RW-rec, Prop. 4]. -/
theorem goodPrime_unramified (m p : ℕ) (hp : GoodPrime M hM m p)
    (P : Prime (F m)) (hP : P.asIdeal.LiesOver (rationalIdeal p)) :
    Algebra.IsUnramifiedAt ℤ P.asIdeal := by
  apply GoodReductionSeparation.goodPrime_unramifiedAt (F m)
    (RayArithmeticModulus.level M hM m) (values M hM m ∪ values M hM m) p
    ⟨hp.1, fun hmem => hp.2 (Finset.mem_union_left _ hmem)⟩ P hP

/-- Denominator avoidance is uniform over all normalized values and their
finite Galois conjugates, at the same P. [RW-rec, Prop. 4]. -/
theorem goodPrime_integral_conjugates (m p : ℕ) (hp : GoodPrime M hM m p)
    (P : Prime (F m)) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (g : F m ≃ₐ[ℚ] F m) (x : ActualLattice.Group M hM) :
    localIntegral (F m) P (g (u m x)) := by
  apply GoodReductionSeparation.goodPrime_conjugates_integral (F m)
    (RayArithmeticModulus.level M hM m) (values M hM m ∪ values M hM m) p
    ⟨hp.1, fun hmem => hp.2 (Finset.mem_union_left _ hmem)⟩ P hP
  exact (GoodReductionSupport.mem_conjugates_iff (F m) _ _).mpr
    ⟨g, u m x, Finset.mem_union_left _ (normalized_mem_values M hM m x), rfl⟩

/-- `comparison_congruent_iff_eq`: congruence becomes equality once the
support of a nonzero difference has been excluded. [RW-rec, Prop. 4]. -/
theorem eq_of_good_congruent (m p : ℕ) (hp : GoodPrime M hM m p)
    (P : Prime (F m)) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (g : F m ≃ₐ[ℚ] F m) (x y : ActualLattice.Group M hM)
    (hc : congruentAt (F m) P (g (u m x)) (u m y)) :
    g (u m x) = u m y := by
  exact (GoodReductionSeparation.comparison_congruent_iff_eq (F m)
    (RayArithmeticModulus.level M hM m) (values M hM m) (values M hM m)
    p hp.1 hp.2 P hP g (u m x) (u m y)
    (normalized_mem_values M hM m x) (normalized_mem_values M hM m y)).mp hc

/-- The arithmetic Frobenius p-power congruence. Local integrality follows
from the finite bad set. [RW-rec, Prop. 4]. -/
theorem goodPrime_frobenius_congruent (m p : ℕ) (hp : GoodPrime M hM m p)
    (P : Prime (F m)) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (g : F m ≃ₐ[ℚ] F m) (hFrob : arithFrob (F m) P = g) :
    ∀ x, congruentAt (F m) P (g (u m x)) (u m x ^ p) := by
  intro x
  have hint : localIntegral (F m) P (u m x) :=
    goodPrime_integral_conjugates M hM m p hp P hP (AlgEquiv.refl) x
  have hc := arithFrob_congruentAt (F m) P (u m x) hint
  rwa [hFrob, primeBelow_eq_of_liesOver (F m) P p hp.1 hP] at hc

/-- Equality when the Frobenius power is congruent to a common target of
[RW-rec, Thm. 8], including the reflection target y = -x. -/
theorem eq_of_frobenius_common_target (m p : ℕ) (hp : GoodPrime M hM m p)
    (P : Prime (F m)) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (g : F m ≃ₐ[ℚ] F m) (hFrob : arithFrob (F m) P = g)
    (x y : ActualLattice.Group M hM)
    (hpow : congruentAt (F m) P (u m x ^ p) (u m y)) :
    g (u m x) = u m y := by
  exact eq_of_good_congruent M hM m p hp P hP g x y
    (congruentAt_trans (F m) P
      (goodPrime_frobenius_congruent M hM m p hp P hP g hFrob x) hpow)

/-- [RW-rec, p. 14, Prop. 4]: the bad set is finite before the action of g
is known, so every prescribed g has a good witness. -/
theorem exists_good_exact_frobenius (m : ℕ) (g : F m ≃ₐ[ℚ] F m) :
    ∃ p : ℕ, GoodPrime M hM m p ∧ ∃ P : Prime (F m),
      P.asIdeal.LiesOver (rationalIdeal p) ∧
      Algebra.IsUnramifiedAt ℤ P.asIdeal ∧ arithFrob (F m) P = g := by
  obtain ⟨p, hp, havoid, P, hP, hunram, hFrob⟩ :=
    DescentChebotarev.exists_exact_frobenius_avoid (F m) g (badPrimes M hM m)
  exact ⟨p, ⟨hp, havoid⟩, P, hP, hunram, hFrob⟩

end SICLean.L5.DescentGoodPrimes
