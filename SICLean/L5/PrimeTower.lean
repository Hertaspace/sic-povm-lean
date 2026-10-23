import SICLean.L5.PrimeReductionArithmetic

set_option autoImplicit false

/-!
# Compatibility in a number-field tower

Mathlib `NumberTheory/RamificationInertia/Valuation.lean`, `valuation_liesOver`, and
`RingTheory/RamificationInertia/Ramification.lean`,
`ramificationIdx'_eq_ramificationIdx`, `ramificationIdx_tower`; `Inertia.lean`,
`inertiaDeg_tower`, `absNorm_pow_inertiaDeg`. `RingTheory/Ideal/GoingUp.lean`, maximal
lies-over, `RingTheory/Ideal/Over.lean`, quotient algebras. [RW-rec, Prop. 4, §4, p. 4,
p. 14] require a common place on a sufficiently large field. All public indices are the
current unprimed definitions. Integral order scales by e; the p-normalized additive
valuation is unchanged. f belongs in residue cardinality, not in the integral-order
formula. No Galois, unramifiedness, Artin map or Frobenius choice is required in this
file.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open NumberField

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M] [Algebra L M]

/-- Relative ramification index for the actual inclusion of integer rings. -/
def relativeRamification (L : Type*) [Field L] {M : Type*} [Field M] [Algebra L M]
    (Q : Prime M) : ℕ := Q.asIdeal.ramificationIdx (𝓞 L)

/-- Relative residue degree for that same inclusion. -/
def relativeResidueDegree (L : Type*) [Field L] {M : Type*} [Field M] [Algebra L M]
    (Q : Prime M) : ℕ := Q.asIdeal.inertiaDeg (𝓞 L)

/-- A fixed lower prime has an upper prime; independently prescribed upper primes need not agree. -/
theorem exists_prime_above (P : Prime L) :
    ∃ Q : Prime M, Q.asIdeal.LiesOver P.asIdeal := by
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) P.asIdeal
  have := hq
  have := hqp
  exact ⟨⟨q, hq.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot q⟩, hqp⟩

variable (P : Prime L) (Q : Prime M) [Q.asIdeal.LiesOver P.asIdeal]

/-- The induced residue-field map is the concrete quotient map of the integer-ring inclusion. -/
def residueMap : Residue P →+* Residue Q :=
  Ideal.quotientMap Q.asIdeal (algebraMap (𝓞 L) (𝓞 M)) (Ideal.over_def Q.asIdeal P.asIdeal).le

/-- Contraction preserves the rational residue characteristic. -/
theorem residueChar_above : residueChar Q = residueChar P := by
  exact (Algebra.ringChar_eq (Residue P) (Residue Q)).symm

/-- Relative e is positive, including at ramified primes. -/
theorem relativeRamification_pos : 0 < relativeRamification L Q := by
  exact Ideal.ramificationIdx_pos Q.asIdeal (𝓞 L)

/-- Relative f is positive, including at inert primes. -/
theorem relativeResidueDegree_pos : 0 < relativeResidueDegree L Q := by
  exact Ideal.inertiaDeg_pos Q.asIdeal (𝓞 L)

/-- Absolute e factors as lower absolute e times relative e. -/
theorem absoluteRamification_tower :
    absoluteRamification Q = absoluteRamification P * relativeRamification L Q := by
  exact Ideal.ramificationIdx_tower (R := ℤ) P.asIdeal Q.asIdeal

/-- The analogous residue-degree tower formula. -/
theorem absoluteResidueDegree_tower :
    absoluteResidueDegree Q = absoluteResidueDegree P * relativeResidueDegree L Q := by
  exact Ideal.inertiaDeg_tower (R := ℤ) P.asIdeal Q.asIdeal

/-- Integral orders scale by relative e, with top handled by positive e. -/
theorem ord_algebraMap (x : L) :
    ord Q (algebraMap L M x) = relativeRamification L Q • ord P x := by
  have he : P.asIdeal.ramificationIdx' Q.asIdeal = relativeRamification L Q :=
    Ideal.ramificationIdx'_eq_ramificationIdx P.asIdeal Q.asIdeal P.ne_bot
  have hval := P.valuation_liesOver M Q x
  rw [he] at hval
  by_cases hx : x = 0
  · subst x
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (relativeRamification_pos (L := L) Q))
    simp [ord, he, succ_nsmul]
  · have hmx : algebraMap L M x ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hx
    simp only [ord, ite_eq_right hx, ite_eq_right hmx, ← hval, WithZero.log_pow]
    simp [← WithTop.coe_nsmul]

/-- Normalized compatibility: no e or f remains. -/
theorem valuation_algebraMap (x : L) :
    valuation Q (algebraMap L M x) = valuation P x := by
  rw [valuation_apply, valuation_apply, valuationFun, valuationFun,
    ord_algebraMap P Q x, absoluteRamification_tower P Q]
  have he : (relativeRamification L Q : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (relativeRamification_pos (L := L) Q))
  have hp : (absoluteRamification P : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (absoluteRamification_pos P))
  cases h : ord P x with
  | top =>
    obtain ⟨e, he'⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (relativeRamification_pos (L := L) Q))
    simp [he', succ_nsmul]
  | coe n =>
    simp only [← WithTop.coe_nsmul, WithTop.map_coe, Int.nsmul_eq_mul,
      Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    congr 1
    field_simp

/-- Bidirectional local-integrality compatibility. -/
theorem integralAt_algebraMap_iff (x : L) :
    IntegralAt Q (algebraMap L M x) ↔ IntegralAt P x := by
  unfold IntegralAt
  rw [valuation_algebraMap P Q]

/-- Bidirectional local-unit compatibility. -/
theorem unitAt_algebraMap_iff (x : L) :
    UnitAt Q (algebraMap L M x) ↔ UnitAt P x := by
  unfold UnitAt
  rw [valuation_algebraMap P Q]

/-- A lower P^n threshold becomes an upper Q^(en) threshold. -/
theorem congruentPow_algebraMap_iff (n : ℕ) (x y : L) :
    CongruentPow Q (relativeRamification L Q * n) (algebraMap L M x) (algebraMap L M y) ↔
      CongruentPow P n x y := by
  unfold CongruentPow
  rw [← map_sub, ord_algebraMap P Q]
  have he := relativeRamification_pos (L := L) Q
  cases h : ord P (x - y) with
  | top =>
    obtain ⟨e, he'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
    simp [he', succ_nsmul]
  | coe z =>
    simp only [← WithTop.coe_nsmul, Int.nsmul_eq_mul, ← WithTop.coe_natCast,
      WithTop.coe_le_coe, Nat.cast_mul]
    exact mul_le_mul_iff_right₀ (show (0 : ℤ) < relativeRamification L Q by exact_mod_cast he)

/-- The residue map agrees with reduction of each integer. -/
theorem residueMap_integer (a : 𝓞 L) :
    residueMap P Q (Ideal.Quotient.mk P.asIdeal a) =
      Ideal.Quotient.mk Q.asIdeal (algebraMap (𝓞 L) (𝓞 M) a) := by
  rfl

/-- The actual residue map is injective. -/
theorem residueMap_injective : Function.Injective (residueMap P Q) := by
  exact (residueMap P Q).injective

/-- The relative residue degree is measured by cardinality. -/
theorem residue_card_tower :
    Nat.card (Residue Q) = Nat.card (Residue P) ^ relativeResidueDegree L Q := by
  exact (Ideal.cardQuot_pow_inertiaDeg P.asIdeal Q.asIdeal).symm

/-- Reduction of field elements commutes with enlarging the finite model. -/
theorem red_algebraMap (x : L) (hx : IntegralAt P x) :
    red Q (algebraMap L M x) ((integralAt_algebraMap_iff P Q x).mpr hx) =
      residueMap P Q (red P x hx) := by
  obtain ⟨a, b, hb, rfl⟩ := (integralAt_iff_fraction P x).mp hx
  have hbQ : algebraMap (𝓞 L) (𝓞 M) b ∉ Q.asIdeal := by
    simpa only [Ideal.mem_of_liesOver Q.asIdeal P.asIdeal] using hb
  have ha : algebraMap L M (a : L) = (algebraMap (𝓞 L) (𝓞 M) a : M) := rfl
  have hb' : algebraMap L M (b : L) = (algebraMap (𝓞 L) (𝓞 M) b : M) := rfl
  simp only [map_div₀, ha, hb', red_fraction P a b hb,
    red_fraction Q (algebraMap (𝓞 L) (𝓞 M) a) (algebraMap (𝓞 L) (𝓞 M) b) hbQ,
    residueMap_integer]

end SICLean.L5.FinitePlace

#check @IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
#check @Ideal.ramificationIdx'_eq_ramificationIdx
#check @Ideal.ramificationIdx_tower
#check @Ideal.inertiaDeg_tower
#check @SICLean.L5.FinitePlace.red_algebraMap
#print SICLean.L5.FinitePlace.residueMap
