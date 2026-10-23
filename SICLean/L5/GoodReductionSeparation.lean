import SICLean.L5.GoodReductionSupport
import SICLean.L5.FrobeniusSplitting
import SICLean.L5.FiniteGaloisFixed

set_option autoImplicit false

/-!
# Good reduction separates finite candidate values

[RW-rec, Prop. 4, pp. 14--15]. Algebraicity of the values is [RW26, Thm. 1, p. 3].
Mathlib: `Completion/FinitePlace.lean` for finite support,
`Discriminant/Different.lean` for nonramification,
`RingTheory/Frobenius.lean` for Frobenius.

The equality criterion assumes the prime lies outside the support of a nonzero
difference, together with the congruence. The final two statements package the
argument over all primes above `p`. They do not assume class-field reciprocity,
Chebotarev, or a density statement.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace SICLean.L5.GoodReductionSeparation

open GoodReductionLocal GoodReductionSupport FrobeniusPrimes FrobeniusRestriction
open FrobeniusSplitting FiniteGaloisEnvelope FiniteGaloisFixed

variable (F : IntermediateField ℚ Galois.Qbar) [NumberField F] [IsGalois ℚ F]

/-- Explicit {2} component of the bad set. -/
theorem goodPrime_ne_two (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) : p ≠ 2 := by
  intro hp2
  exact hp.2 ((mem_badPrimes_iff F M S p).2 (Or.inl hp2))

/-- M≠0 is essential: primeFactors 0 is empty. -/
theorem goodPrime_not_dvd_level (M : ℕ) (hM : M ≠ 0) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) : ¬ p ∣ M := by
  intro hdiv
  exact hp.2 ((mem_badPrimes_iff F M S p).2
    (Or.inr (Or.inl (Nat.mem_primeFactors.mpr ⟨hp.1, hdiv, hM⟩))))

/-- Field discriminant excludes every ramified rational prime. -/
theorem goodPrime_unramifiedIn (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) :
    Algebra.IsUnramifiedIn (𝓞 F) (rationalIdeal p) := by
  by_contra hram
  exact hp.2 ((mem_badPrimes_iff F M S p).2
    (Or.inr (Or.inr (Or.inl ((mem_ramifiedPrimes_iff F p).2 ⟨hp.1, hram⟩)))))

/-- Any prime above this rational prime is nonramified. -/
theorem goodPrime_unramifiedAt (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) :
    Algebra.IsUnramifiedAt ℤ P.asIdeal := by
  exact goodPrime_unramifiedIn F M S p hp P.asIdeal P.isPrime hP

/-- Denominator exclusion holds for the whole finite family and its Galois orbit,
at every prime above `p`. -/
theorem goodPrime_conjugates_integral (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) (u : F)
    (hu : u ∈ conjugates F S) : localIntegral F P u := by
  apply localIntegral_of_not_mem_denominatorSupport F P u
  rw [primeBelow_eq_of_liesOver F P p hp.1 hP]
  intro hden
  exact hp.2 ((mem_badPrimes_iff F M S p).2
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨u, hu, hden⟩)))))

/-- A nonzero moving difference is a local unit, not merely integral. -/
theorem goodPrime_moving_difference_unit (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) (h : F ≃ₐ[ℚ] F)
    (u : F) (hu : u ∈ S) (hne : h u ≠ u) : P.valuation F (h u - u) = 1 := by
  apply valuation_eq_one_of_not_mem_primeSupport F P (h u - u) (sub_ne_zero.mpr hne)
  rw [primeBelow_eq_of_liesOver F P p hp.1 hP]
  intro hsupp
  have hdiff : h u - u ∈ movingDifferences F S :=
    (mem_movingDifferences_iff F S (h u - u)).2
      ⟨sub_ne_zero.mpr hne, h, u, hu, rfl⟩
  exact hp.2 ((mem_badPrimes_iff F M S p).2
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨h u - u, hdiff, hsupp⟩)))))

/-- The generic collision-exclusion lemma, ready for any finite
list of candidates. The zero difference is handled without a support claim. -/
theorem eq_of_congruentAt_of_avoid_support (P : Prime F) (a b : F)
    (hab : congruentAt F P a b)
    (havoid : primeBelow F P ∉ primeSupport F (a - b)) : a = b := by
  by_contra hne
  have hunit := valuation_eq_one_of_not_mem_primeSupport F P (a - b)
    (sub_ne_zero.mpr hne) havoid
  exact (ne_of_lt hab.2.2) hunit

/-- Exact fixed-point criterion for one value of the supplied family. -/
theorem goodPrime_congruent_iff_fixed (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) (h : F ≃ₐ[ℚ] F)
    (u : F) (hu : u ∈ S) : congruentAt F P (h u) u ↔ h u = u := by
  constructor
  · intro hc
    by_contra hne
    exact (ne_of_lt hc.2.2) (goodPrime_moving_difference_unit F M S p hp P hP h u hu hne)
  · intro heq
    rw [heq]
    exact congruentAt_self F P u
      (goodPrime_conjugates_integral F M S p hp P hP u (subset_conjugates F S hu))

/-- One automorphism fixes every value of the family at once. -/
theorem goodPrime_fixes_all (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) (h : F ≃ₐ[ℚ] F)
    (hc : ∀ u ∈ S, congruentAt F P (h u) u) : ∀ u ∈ S, h u = u := by
  intro u hu
  exact (goodPrime_congruent_iff_fixed F M S p hp P hP h u hu).1 (hc u hu)

/-- Combine a genuine Frobenius congruence with the separately
proved special-value p-power congruence, then exclude every nonzero difference. -/
theorem goodPrime_frobenius_fixes_all (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) (h : F ≃ₐ[ℚ] F)
    (hFrob : IsArithFrobAt ℤ h P.asIdeal)
    (hpow : ∀ u ∈ S, congruentAt F P (u ^ p) u) : ∀ u ∈ S, h u = u := by
  have hchoice : h = arithFrob F P :=
    isArithFrobAt_unique F P (goodPrime_unramifiedAt F M S p hp P hP)
      h (arithFrob F P) hFrob (arithFrob_spec F P)
  apply goodPrime_fixes_all F M S p hp P hP h
  intro u hu
  rw [hchoice]
  have hint := goodPrime_conjugates_integral F M S p hp P hP u
    (subset_conjugates F S hu)
  have hc := arithFrob_congruentAt F P u hint
  rw [primeBelow_eq_of_liesOver F P p hp.1 hP] at hc
  exact congruentAt_trans F P hc (hpow u hu)

/-- The same statement for the chosen arithmetic Frobenius. -/
theorem goodPrime_arithFrob_fixes_all (M : ℕ) (S : Finset F) (p : ℕ)
    (hp : goodPrime F M S p) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hpow : ∀ u ∈ S, congruentAt F P (u ^ p) u) :
    ∀ u ∈ S, arithFrob F P u = u := by
  exact goodPrime_frobenius_fixes_all F M S p hp P hP (arithFrob F P)
    (arithFrob_spec F P) hpow

/-- Comparison of distinct target values uses the enlarged comparison bad set. -/
theorem comparison_congruent_iff_eq (M : ℕ) (S T : Finset F) (p : ℕ)
    (hp : p.Prime) (hgood : p ∉ comparisonBadPrimes F M S T) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) (h : F ≃ₐ[ℚ] F)
    (u v : F) (hu : u ∈ S) (hv : v ∈ T) :
    congruentAt F P (h u) v ↔ h u = v := by
  have hbase : goodPrime F M (S ∪ T) p :=
    ⟨hp, fun hmem => hgood (Finset.mem_union_left _ hmem)⟩
  constructor
  · intro hc
    apply eq_of_congruentAt_of_avoid_support F P (h u) v hc
    rw [primeBelow_eq_of_liesOver F P p hp hP]
    intro hsupp
    have hne : h u - v ≠ 0 := by
      intro heq
      simp [heq, primeSupport_zero F] at hsupp
    have hdiff : h u - v ∈ comparisonDifferences F S T :=
      (mem_comparisonDifferences_iff F S T (h u - v)).2 ⟨hne, h, u, hu, v, hv, rfl⟩
    exact hgood (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨h u - v, hdiff, hsupp⟩))
  · intro heq
    rw [heq]
    exact congruentAt_self F P v (goodPrime_conjugates_integral F M (S ∪ T) p hbase
      P hP v (subset_conjugates F (S ∪ T) (Finset.mem_union_right S hv)))

/-- Uniform candidate-function version for t(U(x))=U(-x).
The target function is supplied literally, with membership in finite T. -/
theorem comparison_arithFrob_eq_targets (M : ℕ) (S T : Finset F) (p : ℕ)
    (hp : p.Prime) (hgood : p ∉ comparisonBadPrimes F M S T) (P : Prime F)
    (hP : P.asIdeal.LiesOver (rationalIdeal p)) (target : F → F)
    (htarget : ∀ u ∈ S, target u ∈ T)
    (hpow : ∀ u ∈ S, congruentAt F P (u ^ p) (target u)) :
    ∀ u ∈ S, arithFrob F P u = target u := by
  have hbase : goodPrime F M (S ∪ T) p :=
    ⟨hp, fun hmem => hgood (Finset.mem_union_left _ hmem)⟩
  intro u hu
  apply (comparison_congruent_iff_eq F M S T p hp hgood P hP (arithFrob F P)
    u (target u) hu (htarget u hu)).1
  have hint := goodPrime_conjugates_integral F M (S ∪ T) p hbase P hP u
    (subset_conjugates F (S ∪ T) (Finset.mem_union_left T hu))
  have hc := arithFrob_congruentAt F P u hint
  rw [primeBelow_eq_of_liesOver F P p hp hP] at hc
  exact congruentAt_trans F P hc (hpow u hu)

/-- The original values, as a finite subset of their envelope. -/
def envelopeValues (H : IntermediateField ℚ Galois.Qbar) (S : Finset Galois.Qbar) :
    Finset (envelope H S) := S.attach.image (valueInEnvelope H S)

/-- The all-conjugates generation step. [RW-rec, Prop. 4].
Each prime above `p` supplies a congruence, and one prime then has trivial Frobenius.
That `H` is fixed is a hypothesis. -/
theorem envelope_arithFrob_eq_one
    (H : IntermediateField ℚ Galois.Qbar) [NumberField H] [Normal ℚ H]
    (S : Finset Galois.Qbar) (M p : ℕ)
    (hp : goodPrime (envelope H S) M (envelopeValues H S) p)
    (P : Prime (envelope H S)) (hP : P.asIdeal.LiesOver (rationalIdeal p))
    (hH : ∀ x : envelope H S, (x : Galois.Qbar) ∈ H →
      arithFrob (envelope H S) P x = x)
    (hpow : ∀ Q : Prime (envelope H S), Q.asIdeal.LiesOver (rationalIdeal p) →
      ∀ u : S, congruentAt (envelope H S) Q
        ((valueInEnvelope H S u) ^ p) (valueInEnvelope H S u)) :
    arithFrob (envelope H S) P = 1 := by
  apply finite_aut_eq_one_of_all_conjugates_fix_values H S
    (arithFrob (envelope H S) P) hH
  intro g u
  let Q := conjugatePrime (envelope H S) g⁻¹ P
  have hQbelow : primeBelow (envelope H S) Q = p :=
    (primeBelow_conjugate (envelope H S) g⁻¹ P).trans
      (primeBelow_eq_of_liesOver (envelope H S) P p hp.1 hP)
  have hQ : Q.asIdeal.LiesOver (rationalIdeal p) := by
    rw [← hQbelow]
    exact liesOver_primeBelow (envelope H S) Q
  have hfix := goodPrime_arithFrob_fixes_all (envelope H S) M
    (envelopeValues H S) p hp Q hQ (by
      intro v hv
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
      exact hpow Q hQ w)
  have hu : valueInEnvelope H S u ∈ envelopeValues H S :=
    Finset.mem_image.mpr ⟨u, Finset.mem_attach S u, rfl⟩
  have hval := hfix (valueInEnvelope H S u) hu
  have hconj := arithFrob_conjugate (envelope H S) P
    (goodPrime_unramifiedAt (envelope H S) M (envelopeValues H S) p hp P hP) g⁻¹
  rw [hconj] at hval
  simpa only [inv_inv] using hval

/-- For a prime outside the displayed finite set, complete splitting of `H`
passes to the envelope when the power-congruence hypothesis holds. -/
theorem envelope_splitsCompletely
    (H : IntermediateField ℚ Galois.Qbar) [NumberField H] [IsGalois ℚ H]
    (S : Finset Galois.Qbar) (M p : ℕ)
    (hp : goodPrime (envelope H S) M (envelopeValues H S) p)
    (hH : splitsCompletely H p)
    (hpow : ∀ Q : Prime (envelope H S), Q.asIdeal.LiesOver (rationalIdeal p) →
      ∀ u : S, congruentAt (envelope H S) Q
        ((valueInEnvelope H S u) ^ p) (valueInEnvelope H S u)) :
    splitsCompletely (envelope H S) p := by
  apply (splitsCompletely_iff_all_arithFrob_eq_one (envelope H S) p hp.1
    (goodPrime_unramifiedIn (envelope H S) M (envelopeValues H S) p hp)).2
  intro P hP
  apply envelope_arithFrob_eq_one H S M p hp P hP ?_ hpow
  let hHF := le_envelope H S
  let Q := contractPrime (envelope H S) H hHF P
  have hQbelow : primeBelow H Q = p :=
    (primeBelow_contractPrime (envelope H S) H hHF P).trans
      (primeBelow_eq_of_liesOver (envelope H S) P p hp.1 hP)
  have hQ : Q.asIdeal.LiesOver (rationalIdeal p) := by
    rw [← hQbelow]
    exact liesOver_primeBelow H Q
  have hunr : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    (unramifiedAt_iff_ramificationIdx H Q).2 (hH.2 Q hQ).1
  have hFrobQ : arithFrob H Q = 1 :=
    (arithFrob_eq_one_iff_inertiaDeg H Q hunr).2 (hH.2 Q hQ).2
  have hres : restrictGalois (envelope H S) H hHF (arithFrob (envelope H S) P) = 1 :=
    (arithFrob_restrict (envelope H S) H hHF P hunr).trans hFrobQ
  intro x hx
  let xH : H := ⟨(x : Galois.Qbar), hx⟩
  apply Subtype.ext
  calc
    (arithFrob (envelope H S) P x : Galois.Qbar) =
        ((restrictGalois (envelope H S) H hHF (arithFrob (envelope H S) P) xH : H) :
          Galois.Qbar) :=
      (restrictGalois_apply (envelope H S) H hHF (arithFrob (envelope H S) P) xH).symm
    _ = (x : Galois.Qbar) := by rw [hres]; rfl

end SICLean.L5.GoodReductionSeparation

#check @SICLean.L5.GoodReductionSeparation.eq_of_congruentAt_of_avoid_support
#check @SICLean.L5.GoodReductionSeparation.envelope_arithFrob_eq_one
#check @SICLean.L5.GoodReductionSeparation.envelope_splitsCompletely
#print SICLean.L5.GoodReductionSeparation.envelopeValues
