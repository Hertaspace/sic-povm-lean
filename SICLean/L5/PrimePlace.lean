import Mathlib

set_option autoImplicit false

/-!
# Finite primes, the integral order and the residue field

The statements use local rather than global integrality. Mathlib
`RingTheory/DedekindDomain/AdicValuation.lean`, `intValuation`, `valuation`, integer
membership. Mathlib `RingTheory/RamificationInertia/{Ramification,Inertia}.lean`,
`Ideal.ramificationIdx`, `Ideal.inertiaDeg`. [RW26, §5.2, pp. 22--23]. The general
dictionary comes from Mathlib. No oddness or unramifiedness is assumed. `ord 0 = ⊤`; the
sign is the negative of Mathlib's multiplicative log.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open NumberField IsDedekindDomain

variable {L : Type*} [Field L] [NumberField L]

/-- An actual nonzero prime of the full ring of integers. -/
abbrev Prime (L : Type*) [Field L] := HeightOneSpectrum (𝓞 L)

/-- Conversion from a nonzero prime ideal to `Prime`. -/
def primeOfIdeal (I : Ideal (𝓞 L)) (hI : I.IsPrime) (hI0 : I ≠ ⊥) : Prime L :=
  ⟨I, hI, hI0⟩

/-- The finite residue field is the actual integer-ring quotient. -/
abbrev Residue (P : Prime L) := 𝓞 L ⧸ P.asIdeal

instance residueField (P : Prime L) : Field (Residue P) :=
  Ideal.Quotient.field P.asIdeal

/-- The residue characteristic is chosen from the quotient, not supplied as an axiom. -/
def residueChar (P : Prime L) : ℕ := ringChar (Residue P)

/-- Absolute ramification index, with the current (unprimed) Mathlib interface. -/
def absoluteRamification (P : Prime L) : ℕ := P.asIdeal.ramificationIdx ℤ

/-- Absolute residue degree. -/
def absoluteResidueDegree (P : Prime L) : ℕ := P.asIdeal.inertiaDeg ℤ

open scoped Classical in
/-- Integral discrete order, including its value at zero. -/
def ord (P : Prime L) (x : L) : WithTop ℤ :=
  if x = 0 then ⊤ else ((-WithZero.log (P.valuation L x) : ℤ) : WithTop ℤ)

/-- A finite prime has a prime residue characteristic. -/
theorem residueChar_prime (P : Prime L) : (residueChar P).Prime := by
  exact CharP.prime_ringChar (Residue P)

/-- The characteristic is that of the actual quotient, which can exceed `ZMod p` in size. -/
theorem residue_charP (P : Prime L) : CharP (Residue P) (residueChar P) := by
  exact inferInstanceAs (CharP (Residue P) (ringChar (Residue P)))

/-- Identification of the rational prime below P. -/
theorem prime_under_int (P : Prime L) :
    P.asIdeal.under ℤ = Ideal.span {(residueChar P : ℤ)} := by
  rw [residueChar, Ideal.ringChar_quot]
  exact (Int.ideal_span_absNorm_eq_self (P.asIdeal.under ℤ)).symm

/-- Residue cardinality; finiteness is the existing number-field quotient instance. -/
theorem residue_card (P : Prime L) :
    Nat.card (Residue P) = residueChar P ^ absoluteResidueDegree P := by
  rw [residueChar, Ideal.ringChar_quot]
  simpa [absoluteResidueDegree, Residue, Ideal.absNorm_apply,
    Submodule.cardQuot_apply] using
      (Ideal.pow_inertiaDeg (Ideal.absNorm (P.asIdeal.under ℤ)) P.asIdeal).symm

/-- Necessary for dividing the integral order by e. -/
theorem absoluteRamification_pos (P : Prime L) : 0 < absoluteRamification P := by
  exact P.asIdeal.ramificationIdx_pos ℤ

/-- The residue extension is nontrivial as a vector space. -/
theorem absoluteResidueDegree_pos (P : Prime L) : 0 < absoluteResidueDegree P := by
  exact Ideal.inertiaDeg_pos P.asIdeal ℤ

/-- Zero retains infinite order. -/
theorem ord_zero (P : Prime L) : ord P 0 = ⊤ := by
  simp [ord]

/-- The multiplicative identity has order zero. -/
theorem ord_one (P : Prime L) : ord P 1 = 0 := by
  simp [ord]

/-- Includes zero factors, so no hidden nonvanishing hypothesis. -/
theorem ord_mul (P : Prime L) (x y : L) : ord P (x * y) = ord P x + ord P y := by
  classical
  by_cases hx : x = 0
  · simp [hx, ord_zero]
  by_cases hy : y = 0
  · simp [hy, ord_zero]
  simp only [ord, ite_eq_right hx, ite_eq_right hy, ite_eq_right (mul_ne_zero hx hy), map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx)
    ((Valuation.ne_zero_iff _).mpr hy), neg_add, WithTop.coe_add]

/-- The additive ultrametric inequality. -/
theorem ord_add (P : Prime L) (x y : L) :
    min (ord P x) (ord P y) ≤ ord P (x + y) := by
  classical
  by_cases hxy : x + y = 0
  · simp [hxy, ord_zero]
  by_cases hx : x = 0
  · simp [hx, ord_zero]
  by_cases hy : y = 0
  · simp [hy, ord_zero]
  have hxv : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hyv : P.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have hxyv : P.valuation L (x + y) ≠ 0 := (Valuation.ne_zero_iff _).mpr hxy
  simp only [ord, ite_eq_right hx, ite_eq_right hy, ite_eq_right hxy]
  rcases le_total (P.valuation L x) (P.valuation L y) with h | h
  · apply (min_le_right _ _).trans
    apply WithTop.coe_le_coe.mpr
    apply neg_le_neg
    apply (WithZero.log_le_log hxyv hyv).mpr
    simpa only [max_eq_right h] using (P.valuation L).map_add x y
  · apply (min_le_left _ _).trans
    apply WithTop.coe_le_coe.mpr
    apply neg_le_neg
    apply (WithZero.log_le_log hxyv hxv).mpr
    simpa only [max_eq_left h] using (P.valuation L).map_add x y

/-- A finite real order can only be extracted for a nonzero field element. -/
theorem ord_ne_top_iff (P : Prime L) (x : L) : ord P x ≠ ⊤ ↔ x ≠ 0 := by
  classical
  simp [ord]

/-- Global integers are integral at every finite prime; converse is local. -/
theorem ord_integer_nonneg (P : Prime L) (a : 𝓞 L) : 0 ≤ ord P (a : L) := by
  classical
  by_cases ha : (a : L) = 0
  · simp [ha, ord_zero]
  have hav : P.valuation L (a : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  simp only [ord, ite_eq_right ha, ← WithTop.coe_zero, WithTop.coe_le_coe, neg_nonneg]
  rw [← WithZero.log_one, WithZero.log_le_log hav one_ne_zero]
  exact P.valuation_le_one a

/-- The first prime-ideal membership bridge, also true for a=0. -/
theorem ord_integer_pos_iff (P : Prime L) (a : 𝓞 L) :
    0 < ord P (a : L) ↔ a ∈ P.asIdeal := by
  classical
  by_cases ha : a = 0
  · simp [ha, ord_zero]
  have haL : (a : L) ≠ 0 := by exact_mod_cast ha
  have hav : P.valuation L (a : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr haL
  simp only [ord, ite_eq_right haL, ← WithTop.coe_zero, WithTop.coe_lt_coe, neg_pos]
  rw [← WithZero.log_one, WithZero.log_lt_log hav one_ne_zero]
  exact P.valuation_lt_one_iff_mem a

/-- The rational prime has integral order e, not generally 1. -/
theorem ord_residueChar (P : Prime L) :
    ord P (residueChar P : L) = (absoluteRamification P : WithTop ℤ) := by
  have hp : residueChar P ≠ 0 := (residueChar_prime P).ne_zero
  have hpL : (residueChar P : L) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hpO : (residueChar P : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hmap : (P.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 L)) =
      Ideal.span {(residueChar P : 𝓞 L)} := by
    rw [prime_under_int, Ideal.map_span, Set.image_singleton]
    simp
  have hm : (P.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 L)) ≠ ⊥ := by
    rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]
    exact hpO
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (P.asIdeal.under ℤ) P.asIdeal hm
  rw [hmap] at he
  have hv : P.valuation L (residueChar P : L) =
      WithZero.exp (-(absoluteRamification P : ℤ)) := by
    change P.valuation L (algebraMap (𝓞 L) L (residueChar P : 𝓞 L)) = _
    rw [P.valuation_of_algebraMap,
      P.intValuation_eq_exp_neg_multiplicity hpO, ← he]
    rfl
  simp [ord, hpL, hv]

end SICLean.L5.FinitePlace

#check @IsDedekindDomain.HeightOneSpectrum.valuation
#check @Ideal.ramificationIdx
#check @Ideal.inertiaDeg
#check @SICLean.L5.FinitePlace.residue_card
#print SICLean.L5.FinitePlace.ord
