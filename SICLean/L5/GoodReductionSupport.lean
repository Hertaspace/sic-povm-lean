import SICLean.L5.GoodReductionLocal

set_option autoImplicit false

/-!
# Explicit finite bad-prime sets

[RW-rec, Prop. 4, p. 14]. These are Mathlib-based number-theoretic constructions for the
cited argument. They use the Mathlib files `NumberField/Completion/FinitePlace.lean`,
`DedekindDomain/AdicValuation.lean` and `NumberField/Discriminant/{Defs,Different}.lean`. Zero
has empty support by an explicit x≠0 guard. A nonzero number's support includes zeros
and poles. Denominator support keeps only poles. The finite support theorem is proved
here. It is not an extra hypothesis. The optional comparison set additionally covers
h(u)-v, needed for the double-negative action; the basic set covers h(u)-u.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace SICLean.L5.GoodReductionSupport

open GoodReductionLocal

variable (F : IntermediateField ℚ Galois.Qbar) [NumberField F]

/-- Literal prime-place support, with zero excluded. -/
def placeSupport (x : F) : Set (Prime F) :=
  {P | x ≠ 0 ∧ P.valuation F x ≠ 1}

/-- FinitePlace.hasFiniteMulSupport, transported through the equivalence with HeightOneSpectrum.
This is not an assumption of the definition. -/
theorem placeSupport_finite (x : F) : (placeSupport F x).Finite := by
  by_cases hx : x = 0
  · simp [placeSupport, hx]
  have hfinite := NumberField.FinitePlace.hasFiniteMulSupport hx
  refine (hfinite.image NumberField.FinitePlace.maximalIdeal).subset ?_
  intro P hP
  refine ⟨NumberField.FinitePlace.mk P, ?_, NumberField.FinitePlace.maximalIdeal_mk P⟩
  change NumberField.FinitePlace.mk P x ≠ 1
  rw [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding']
  intro hPone
  apply hP.2
  apply (WithZeroMulInt.toNNReal_eq_one_iff _
    (NumberField.HeightOneSpectrum.absNorm_ne_zero P)
    (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P))).mp
  exact_mod_cast hPone

/-- The finite image of the preceding actual support in rational primes. The proof is used only to
convert a specified set to a finset. -/
def primeSupport (x : F) : Finset ℕ :=
  ((placeSupport_finite F x).image (primeBelow F)).toFinset

/-- Only the poles, projected to rational primes. -/
def denominatorSupport (x : F) : Finset ℕ :=
  (primeSupport F x).filter
    (fun p => ∃ P : Prime F, primeBelow F P = p ∧ 1 < P.valuation F x)

/-- The prime divisors of the nonzero field discriminant, not of an arbitrary polynomial
discriminant (Mathlib `NumberField/Discriminant/Different.lean`). -/
def ramifiedPrimes : Finset ℕ := (NumberField.discr F).natAbs.primeFactors

/-- Finite image membership, with all quantifiers exposed. -/
theorem mem_primeSupport_iff (x : F) (p : ℕ) :
    p ∈ primeSupport F x ↔ x ≠ 0 ∧ ∃ P : Prime F,
      primeBelow F P = p ∧ P.valuation F x ≠ 1 := by
  simp only [primeSupport, Set.Finite.mem_toFinset, Set.mem_image, placeSupport,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, ⟨hx, hP⟩, hp⟩
    exact ⟨hx, P, hp, hP⟩
  · rintro ⟨hx, P, hp, hP⟩
    exact ⟨P, ⟨hx, hP⟩, hp⟩

/-- The explicit nonzero guard prevents infinite support at zero. -/
theorem primeSupport_zero : primeSupport F 0 = ∅ := by
  ext p
  simp [mem_primeSupport_iff]

/-- Every element of the projected support is prime (Mathlib `RingTheory/Ideal/Int.lean`). -/
theorem primeSupport_prime (x : F) (p : ℕ) (hp : p ∈ primeSupport F x) :
    p.Prime := by
  obtain ⟨_, P, rfl, _⟩ := (mem_primeSupport_iff F x p).mp hp
  letI : NeZero P.asIdeal := ⟨P.ne_bot⟩
  exact Nat.absNorm_under_prime P.asIdeal

/-- The pointwise unit conclusion used to rule out nonzero collisions. -/
theorem valuation_eq_one_of_not_mem_primeSupport (P : Prime F) (x : F)
    (hx : x ≠ 0) (hp : primeBelow F P ∉ primeSupport F x) :
    P.valuation F x = 1 := by
  by_contra hP
  exact hp ((mem_primeSupport_iff F x _).mpr ⟨hx, P, rfl, hP⟩)

/-- Poles alone are the excluded denominator primes. -/
theorem mem_denominatorSupport_iff (x : F) (p : ℕ) :
    p ∈ denominatorSupport F x ↔ ∃ P : Prime F,
      primeBelow F P = p ∧ 1 < P.valuation F x := by
  rw [denominatorSupport, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    obtain ⟨P, hP, hv⟩ := h
    refine ⟨(mem_primeSupport_iff F x p).mpr ⟨?_, P, hP, ne_of_gt hv⟩, P, hP, hv⟩
    intro hx
    simp [hx] at hv

/-- No claim of a nonzero residue: x may be zero or vanish at P. -/
theorem localIntegral_of_not_mem_denominatorSupport (P : Prime F) (x : F)
    (hp : primeBelow F P ∉ denominatorSupport F x) : localIntegral F P x := by
  change P.valuation F x ≤ 1
  by_contra hv
  exact hp ((mem_denominatorSupport_iff F x _).mpr ⟨P, rfl, lt_of_not_ge hv⟩)

/-- For prime p, ramification is characterized by divisibility of the actual field discriminant
(Mathlib `NumberField/Discriminant/Different.lean`). -/
theorem mem_ramifiedPrimes_iff (p : ℕ) :
    p ∈ ramifiedPrimes F ↔ p.Prime ∧
      ¬ Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)}) := by
  rw [ramifiedPrimes, Nat.mem_primeFactors_of_ne_zero
    (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F))]
  by_cases hp : p.Prime
  · simp only [hp, true_and]
    rw [← not_iff_not, not_not]
    simpa only [← Int.natCast_dvd, Int.dvd_natAbs] using
      (NumberField.not_dvd_discr_iff_isUnramifiedIn F (𝓞 F)
        (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)))
  · simp [hp]

variable [IsGalois ℚ F]

/-- All values and all their finite Galois conjugates, a literal finite union. Finite-dimensionality
supplies finiteness of the automorphism group. -/
def conjugates (S : Finset F) : Finset F :=
  letI := Fintype.ofFinite (F ≃ₐ[ℚ] F)
  Finset.univ.biUnion (fun h : F ≃ₐ[ℚ] F => S.image (fun u => h u))

/-- All nonzero h(u)-u, explicitly computed before any fixed-point result. -/
def movingDifferences (S : Finset F) : Finset F :=
  letI := Fintype.ofFinite (F ≃ₐ[ℚ] F)
  (Finset.univ.biUnion (fun h : F ≃ₐ[ℚ] F => S.image (fun u => h u - u))).erase 0

/-- The basic finite bad set. M is the supplied conductor/level product; callers must supply M≠0
before concluding p∤M. -/
def badPrimes (M : ℕ) (S : Finset F) : Finset ℕ :=
  {2} ∪ M.primeFactors ∪ ramifiedPrimes F ∪
    (conjugates F S).biUnion (denominatorSupport F) ∪
      (movingDifferences F S).biUnion (primeSupport F)

/-- An ordinary prime outside the displayed finite set. -/
def goodPrime (M : ℕ) (S : Finset F) (p : ℕ) : Prop :=
  p.Prime ∧ p ∉ badPrimes F M S

/-- Nonzero h(u)-v for finite source and target sets; neither equality nor Galois-orbit membership
of v is presupposed. -/
def comparisonDifferences (S T : Finset F) : Finset F :=
  letI := Fintype.ofFinite (F ≃ₐ[ℚ] F)
  (Finset.univ.biUnion (fun h : F ≃ₐ[ℚ] F =>
    S.biUnion (fun u => T.image (fun v => h u - v)))).erase 0

/-- A finite enlargement for comparisons against a second candidate value. For example S={U(x)},
T={U(-x)} in the sign-action argument. -/
def comparisonBadPrimes (M : ℕ) (S T : Finset F) : Finset ℕ :=
  badPrimes F M (S ∪ T) ∪
    (comparisonDifferences F S T).biUnion (primeSupport F)

/-- Finite Galois enumeration, with a single h for the indicated value. -/
theorem mem_conjugates_iff (S : Finset F) (v : F) :
    v ∈ conjugates F S ↔ ∃ h : F ≃ₐ[ℚ] F, ∃ u ∈ S, h u = v := by
  simp [conjugates]

/-- Identity conjugate retains the original finite family. -/
theorem subset_conjugates (S : Finset F) : S ⊆ conjugates F S := by
  intro u hu
  exact (mem_conjugates_iff F S u).mpr ⟨AlgEquiv.refl, u, hu, rfl⟩

/-- Enumerating the full finite Galois group gives a stable set. -/
theorem conjugates_image_eq (S : Finset F) (h : F ≃ₐ[ℚ] F) :
    (conjugates F S).image (fun u => h u) = conjugates F S := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨g, u, hu, rfl⟩ := (mem_conjugates_iff F S w).mp hw
    exact (mem_conjugates_iff F S _).mpr ⟨g.trans h, u, hu, rfl⟩
  · intro hv
    obtain ⟨g, u, hu, rfl⟩ := (mem_conjugates_iff F S v).mp hv
    refine Finset.mem_image.mpr ⟨h.symm (g u), ?_, h.apply_symm_apply _⟩
    exact (mem_conjugates_iff F S _).mpr ⟨g.trans h.symm, u, hu, rfl⟩

/-- Membership does not depend on knowing which h preserves a value. -/
theorem mem_movingDifferences_iff (S : Finset F) (z : F) :
    z ∈ movingDifferences F S ↔ z ≠ 0 ∧
      ∃ h : F ≃ₐ[ℚ] F, ∃ u ∈ S, z = h u - u := by
  simp only [movingDifferences, Finset.mem_erase, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hz, h, u, hu, heq⟩
    exact ⟨hz, h, u, hu, heq.symm⟩
  · rintro ⟨hz, h, u, hu, heq⟩
    exact ⟨hz, h, u, hu, heq.symm⟩

/-- Every component of the concrete bad set exposed separately. -/
theorem mem_badPrimes_iff (M : ℕ) (S : Finset F) (p : ℕ) :
    p ∈ badPrimes F M S ↔ p = 2 ∨ p ∈ M.primeFactors ∨
      p ∈ ramifiedPrimes F ∨
      (∃ u ∈ conjugates F S, p ∈ denominatorSupport F u) ∨
      ∃ z ∈ movingDifferences F S, p ∈ primeSupport F z := by
  simp only [badPrimes, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
    or_assoc]

/-- In particular no composite integer is silently excluded as a prime. -/
theorem badPrimes_prime (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : p ∈ badPrimes F M S) : p.Prime := by
  rcases (mem_badPrimes_iff F M S p).mp hp with htwo | hlevel | hram | hden | hmove
  · simpa [htwo] using Nat.prime_two
  · exact (Nat.mem_primeFactors.mp hlevel).1
  · exact ((mem_ramifiedPrimes_iff F p).mp hram).1
  · obtain ⟨u, _, hu⟩ := hden
    exact primeSupport_prime F u p (Finset.mem_filter.mp hu).1
  · obtain ⟨z, _, hz⟩ := hmove
    exact primeSupport_prime F z p hz

/-- The finite comparison supports cover every actual candidate pair. -/
theorem mem_comparisonDifferences_iff (S T : Finset F) (z : F) :
    z ∈ comparisonDifferences F S T ↔ z ≠ 0 ∧
      ∃ h : F ≃ₐ[ℚ] F, ∃ u ∈ S, ∃ v ∈ T, z = h u - v := by
  simp only [comparisonDifferences, Finset.mem_erase, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hz, h, u, hu, v, hv, heq⟩
    exact ⟨hz, h, u, hu, v, hv, heq.symm⟩
  · rintro ⟨hz, h, u, hu, v, hv, heq⟩
    exact ⟨hz, h, u, hu, v, hv, heq.symm⟩

end SICLean.L5.GoodReductionSupport

#check @NumberField.FinitePlace.hasFiniteMulSupport
#check @NumberField.not_dvd_discr_iff_isUnramifiedIn
#print SICLean.L5.GoodReductionSupport.placeSupport
#print SICLean.L5.GoodReductionSupport.badPrimes
#print SICLean.L5.GoodReductionSupport.comparisonBadPrimes
