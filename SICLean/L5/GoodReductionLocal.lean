import SICLean.Galois.AlgebraicClosure

set_option autoImplicit false

/-!
# Finite primes, local congruence, and concrete integer denominators

The field is a subfield of the fixed `Galois.Qbar`.
[RW-rec, Prop. 4, p. 14]. Algebraicity of the values is [RW26, Thm. 1, p. 3].

`valuation` is Mathlib's multiplicative discrete valuation: integral means
value `≤ 1`, a nonzero residue means value `= 1`, and a zero residue means value `< 1`.
Thus `congruentAt` includes local integrality of both entries. No additive
valuation, analytic germ, square root, `Φ`, `φ`, or `μ` is redefined.
-/

noncomputable section

open NumberField IsDedekindDomain

namespace SICLean.L5.GoodReductionLocal

variable (F : IntermediateField ℚ Galois.Qbar) [NumberField F]

/-- The nonzero prime ideals of the actual ring of integers.
Mathlib DedekindDomain/Ideal/Lemmas.lean, `HeightOneSpectrum`. -/
abbrev Prime := HeightOneSpectrum (𝓞 F)

/-- The positive generator of the contraction to ℤ, via its ideal norm.
Mathlib `Int.liesOver_span_absNorm` and `Nat.absNorm_under_prime`. -/
def primeBelow (P : Prime F) : ℕ := Ideal.absNorm (P.asIdeal.under ℤ)

/-- Local integrality in the actual field F.
Mathlib `IsDedekindDomain.HeightOneSpectrum.valuation` and
`IsDedekindDomain.HeightOneSpectrum.valuation_le_one` and
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`. -/
def localIntegral (P : Prime F) (x : F) : Prop := P.valuation F x ≤ 1

/-- Congruence of two locally integral field elements, not a congruence
of arbitrary fractions with unchecked denominators. -/
def congruentAt (P : Prime F) (x y : F) : Prop :=
  localIntegral F P x ∧ localIntegral F P y ∧ P.valuation F (x - y) < 1

/-- A concrete common denominator: the lcm of the rational coordinates in an
integral basis. Mathlib `NumberField/Basic.lean`, `Algebra/GCDMonoid/Finset.lean`. -/
def denominator (x : F) : ℕ :=
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ (𝓞 F))
  Finset.univ.lcm (fun i => ((integralBasis F).repr x i).den)

/-- The rational prime below P is prime (Mathlib `Nat.absNorm_under_prime`). -/
theorem primeBelow_prime (P : Prime F) : (primeBelow F P).Prime := by
  exact Nat.absNorm_under_prime P.asIdeal

/-- Mathlib `Int.liesOver_span_absNorm` and
Ideal/Norm/AbsNorm.lean, `Int.ideal_span_absNorm_eq_self`. -/
theorem under_eq_span_primeBelow (P : Prime F) :
    P.asIdeal.under ℤ = Ideal.span {(primeBelow F P : ℤ)} := by
  exact (Int.ideal_span_absNorm_eq_self _).symm

/-- The same integer-ideal calculation, in the form used below. -/
theorem primeBelow_eq_of_liesOver (P : Prime F) (p : ℕ) (hp : p.Prime)
    (hP : P.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) : primeBelow F P = p := by
  simp [primeBelow, ← hP.over]

/-- Mathlib `RingTheory/Ideal/Int.lean`. The exponent is that of the
arithmetic Frobenius congruence. -/
theorem base_quotient_card (P : Prime F) :
    Nat.card (ℤ ⧸ P.asIdeal.under ℤ) = primeBelow F P := by
  rw [under_eq_span_primeBelow]
  exact Int.card_ideal_quot _

/-- Local integrality at P is equivalent to being a fraction a/s of integers with s ∉ P
(`Mathlib.RingTheory.DedekindDomain.AdicValuation`). -/
theorem localIntegral_iff_fraction (P : Prime F) (x : F) :
    localIntegral F P x ↔ ∃ a s : 𝓞 F, s ∉ P.asIdeal ∧
      x = (a : F) / (s : F) := by
  constructor
  · intro hx
    obtain ⟨a, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer x hx
    have hs0 : (s : 𝓞 F) ≠ 0 := fun h ↦ s.property (h ▸ P.asIdeal.zero_mem)
    have hsF : ((s : 𝓞 F) : F) ≠ 0 := (IsFractionRing.injective (𝓞 F) F).ne hs0
    exact ⟨a, s, s.property, (eq_div_iff hsF).mpr hs⟩
  · rintro ⟨a, s, hs, rfl⟩
    have hsv : P.valuation F (s : F) = 1 := P.valuation_eq_one_iff_notMem.mpr hs
    simpa only [localIntegral, map_div₀, hsv, div_one] using
      P.valuation_le_one (K := F) a

/-- The same localization calculation, with one denominator for both
entries and ideal membership as the conclusion. -/
theorem congruentAt_iff_fraction (P : Prime F) (x y : F) :
    congruentAt F P x y ↔ ∃ a b s : 𝓞 F, s ∉ P.asIdeal ∧
      x = (a : F) / (s : F) ∧ y = (b : F) / (s : F) ∧ a - b ∈ P.asIdeal := by
  constructor
  · rintro ⟨hx, hy, hxy⟩
    obtain ⟨a, s, hs, hxa⟩ := (localIntegral_iff_fraction F P x).mp hx
    obtain ⟨b, t, ht, hyb⟩ := (localIntegral_iff_fraction F P y).mp hy
    have hs0 : s ≠ 0 := fun h ↦ hs (h ▸ P.asIdeal.zero_mem)
    have ht0 : t ≠ 0 := fun h ↦ ht (h ▸ P.asIdeal.zero_mem)
    have hsF : (s : F) ≠ 0 := (IsFractionRing.injective (𝓞 F) F).ne hs0
    have htF : (t : F) ≠ 0 := (IsFractionRing.injective (𝓞 F) F).ne ht0
    have hst : s * t ∉ P.asIdeal := fun h ↦ (P.isPrime.mem_or_mem h).elim hs ht
    have hstval : P.valuation F ((s * t : 𝓞 F) : F) = 1 :=
      P.valuation_eq_one_iff_notMem.mpr hst
    refine ⟨a * t, b * s, s * t, hst, ?_, ?_, ?_⟩
    · rw [hxa]
      push_cast
      field_simp
    · rw [hyb]
      push_cast
      field_simp
    · have hclear : ((a * t - b * s : 𝓞 F) : F) =
          (x - y) * ((s * t : 𝓞 F) : F) := by
        rw [hxa, hyb]
        push_cast
        field_simp
      apply (P.valuation_lt_one_iff_mem (K := F) (a * t - b * s)).mp
      change P.valuation F (((a * t - b * s) : 𝓞 F) : F) < 1
      rw [hclear, map_mul, hstval, mul_one]
      exact hxy
  · rintro ⟨a, b, s, hs, rfl, rfl, hab⟩
    have hsv : P.valuation F (s : F) = 1 := P.valuation_eq_one_iff_notMem.mpr hs
    refine ⟨?_, ?_, ?_⟩
    · simpa only [localIntegral, map_div₀, hsv, div_one] using
        P.valuation_le_one (K := F) a
    · simpa only [localIntegral, map_div₀, hsv, div_one] using
        P.valuation_le_one (K := F) b
    · have hsub : (a : F) / (s : F) - (b : F) / (s : F) =
          ((a - b : 𝓞 F) : F) / (s : F) := by push_cast; ring
      rw [hsub, map_div₀, hsv, div_one]
      exact (P.valuation_lt_one_iff_mem (K := F) (a - b)).mpr hab

/-- Integral-basis coordinates; Rat.den_pos and Finset.lcm_ne_zero_iff. -/
theorem denominator_pos (x : F) : 0 < denominator F x := by
  classical
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ (𝓞 F))
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr fun i _ ↦ Rat.den_ne_zero _

/-- `Mathlib.NumberTheory.NumberField.Basic` and Finset.dvd_lcm.
This is a theorem about the displayed denominator, not part of its definition. -/
theorem denominator_mul_isIntegral (x : F) :
    IsIntegral ℤ ((denominator F x : F) * x) := by
  classical
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ (𝓞 F))
  have hcoeff (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
      ∃ a : ℤ, (denominator F x : ℚ) * (integralBasis F).repr x i = a := by
    obtain ⟨m, hm⟩ : ((integralBasis F).repr x i).den ∣ denominator F x :=
      Finset.dvd_lcm (Finset.mem_univ i)
    refine ⟨(m : ℤ) * ((integralBasis F).repr x i).num, ?_⟩
    rw [hm]
    simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    rw [mul_comm (((integralBasis F).repr x i).den : ℚ) (m : ℚ), mul_assoc,
      Rat.den_mul_eq_num]
  have hsum :
      ∑ i, ((denominator F x : ℚ) * (integralBasis F).repr x i) • integralBasis F i =
        (denominator F x : F) * x := by
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, (integralBasis F).sum_repr]
    simp [Algebra.smul_def]
  rw [← hsum]
  apply IsIntegral.sum
  intro i _
  obtain ⟨a, ha⟩ := hcoeff i
  rw [ha]
  simpa [Algebra.smul_def] using
    (isIntegral_intCast a).mul (RingOfIntegers.basis F i).isIntegral_coe

/-- The integral numerator. It lies in `𝓞 F`. -/
def numerator (x : F) : 𝓞 F :=
  ⟨(denominator F x : F) * x, denominator_mul_isIntegral F x⟩

/-- Concrete reconstruction from the displayed numerator and denominator. -/
theorem numerator_div_denominator (x : F) :
    (numerator F x : F) / (denominator F x : F) = x := by
  change (denominator F x : F) * x / (denominator F x : F) = x
  exact mul_div_cancel_left₀ x (Nat.cast_ne_zero.mpr (denominator_pos F x).ne')

/-- A natural number lies outside P exactly when the prime below P does not divide it
(Mathlib `Int.cast_mem_ideal_iff`). -/
theorem natCast_not_mem_iff (P : Prime F) (n : ℕ) :
    (n : 𝓞 F) ∉ P.asIdeal ↔ ¬ primeBelow F P ∣ n := by
  simpa only [primeBelow, Int.cast_natCast, Int.natCast_dvd_natCast] using
    (Int.cast_mem_ideal_iff (I := P.asIdeal) (d := (n : ℤ))).not

/-- Local integrality after excluding the concrete denominator. -/
theorem localIntegral_of_not_dvd_denominator (P : Prime F) (x : F)
    (h : ¬ primeBelow F P ∣ denominator F x) : localIntegral F P x := by
  apply (localIntegral_iff_fraction F P x).mpr
  exact ⟨numerator F x, (denominator F x : 𝓞 F),
    (natCast_not_mem_iff F P _).mpr h, (numerator_div_denominator F x).symm⟩

/-- A denominator-free test after clearing with any common n.
Neither global integrality of x,y nor n=denominator x is required. -/
theorem congruentAt_iff_cleared (P : Prime F) (x y : F) (n : ℕ)
    (hn : ¬ primeBelow F P ∣ n) (a b : 𝓞 F)
    (ha : (a : F) = (n : F) * x) (hb : (b : F) = (n : F) * y) :
    congruentAt F P x y ↔ a - b ∈ P.asIdeal := by
  have hnP : (n : 𝓞 F) ∉ P.asIdeal := (natCast_not_mem_iff F P n).mpr hn
  have hn0 : n ≠ 0 := fun h ↦ hn (h ▸ dvd_zero _)
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hnv : P.valuation F (n : F) = 1 := by
    simpa only [map_natCast] using (P.valuation_eq_one_iff_notMem (K := F)).mpr hnP
  have hxa : x = (a : F) / ((n : 𝓞 F) : F) := by
    push_cast
    exact (eq_div_iff hnF).mpr (by rw [mul_comm, ← ha])
  have hyb : y = (b : F) / ((n : 𝓞 F) : F) := by
    push_cast
    exact (eq_div_iff hnF).mpr (by rw [mul_comm, ← hb])
  constructor
  · intro h
    apply (P.valuation_lt_one_iff_mem (K := F) (a - b)).mp
    change P.valuation F (((a - b) : 𝓞 F) : F) < 1
    have hclear : ((a - b : 𝓞 F) : F) = (n : F) * (x - y) := by
      push_cast
      change (a : F) - (b : F) = (n : F) * (x - y)
      rw [ha, hb, mul_sub]
    rw [hclear, map_mul, hnv, one_mul]
    exact h.2.2
  · intro hab
    exact (congruentAt_iff_fraction F P x y).mpr ⟨a, b, (n : 𝓞 F), hnP, hxa, hyb, hab⟩

/-- Reflexivity retains the necessary local-integrality premise. -/
theorem congruentAt_self (P : Prime F) (x : F) (hx : localIntegral F P x) :
    congruentAt F P x x := by
  exact ⟨hx, hx, by simp⟩

/-- Elementary valuation-ring symmetry. -/
theorem congruentAt_symm (P : Prime F) {x y : F} (h : congruentAt F P x y) :
    congruentAt F P y x := by
  exact ⟨h.2.1, h.1, (P.valuation F).map_sub_swap x y ▸ h.2.2⟩

/-- Elementary valuation-ring transitivity. -/
theorem congruentAt_trans (P : Prime F) {x y z : F}
    (hxy : congruentAt F P x y) (hyz : congruentAt F P y z) :
    congruentAt F P x z := by
  refine ⟨hxy.1, hyz.2.1, ?_⟩
  have h := (P.valuation F).map_add_lt hxy.2.2 hyz.2.2
  simpa only [sub_add_sub_cancel] using h

end SICLean.L5.GoodReductionLocal

#check @IsDedekindDomain.HeightOneSpectrum.valuation
#check @NumberField.integralBasis
#check @SICLean.L5.GoodReductionLocal.congruentAt_iff_cleared
#print SICLean.L5.GoodReductionLocal.denominator
#print SICLean.L5.GoodReductionLocal.congruentAt
