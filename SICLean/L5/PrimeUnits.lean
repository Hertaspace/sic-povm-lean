import SICLean.L5.PrimeReductionArithmetic
import SICLean.L5.PrimeUnitsAux

set_option autoImplicit false

/-!
# Roots of unity, global integers and ordinary real coordinates

[RW-rec, p. 5] (p-power roots), p. 8 (eta multiplier), p. 9 (unit use). [RW26, §5.2, p.
3, p. 22, (3)]. These justify applications to the existing q, B, lambda, mu, e; they do
not introduce new analytic definitions. AdicValuation
`mem_integers_of_valuation_le_one`, `IsIntegralClosure.isIntegral_iff`; existing
`L3/ValuationSupport.lean`, `realValue`, `coe_realValue`, `realValue_mul/pow`. No p∤24
hypothesis is imposed on the unit property of eta multipliers.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- Every finite-order nonzero root is a unit, including when p divides n. -/
theorem root_unitAt (P : Prime L) {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    UnitAt P ζ := by
  exact SICLean.L3.ValuationSupport.value_pow_eq_one (valuation P) hn hζ

/-- Explicit integrality evidence for root reduction. -/
theorem root_integralAt (P : Prime L) {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    IntegralAt P ζ := by
  exact unitAt_integral P (root_unitAt P hn hζ)

/-- Its reduction is nonzero even at primes dividing its order. -/
theorem root_red_ne_zero (P : Prime L) {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    red P ζ (root_integralAt P hn hζ) ≠ 0 := by
  exact (red_ne_zero_iff P ζ _).mpr (root_unitAt P hn hζ)

/-- Reduction preserves the power relation, not necessarily the exact order. -/
theorem root_red_pow (P : Prime L) {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    red P ζ (root_integralAt P hn hζ) ^ n = 1 := by
  rw [← red_pow]
  simpa only [hζ] using red_one P

/-- A p-power root reduces to one, including the s=0 case. -/
theorem pPower_root_red_eq_one (P : Prime L) {ζ : L} (s : ℕ)
    (hζ : ζ ^ (residueChar P ^ s) = 1) (hi : IntegralAt P ζ) :
    red P ζ hi = 1 := by
  let : CharP (Residue P) (residueChar P) := residue_charP P
  let : Fact (residueChar P).Prime := ⟨residueChar_prime P⟩
  have hr := root_red_pow P (pow_ne_zero s (residueChar_prime P).ne_zero) hζ
  have hpow : red P ζ hi ^ (residueChar P ^ s * 1) = 1 := by
    simpa only [mul_one] using hr
  simpa only [pow_one] using
    (ExpChar.pow_prime_pow_mul_eq_one_iff (residueChar P) s 1 (red P ζ hi)).mp hpow

/-- Mathlib `Ideal.rootsOfUnityMapQuot_injective`. Exact order needs the coprime hypothesis. -/
theorem primitiveRoot_red (P : Prime L) {ζ : L} {n : ℕ} (hn : n ≠ 0)
    (hζ : IsPrimitiveRoot ζ n) (hc : (residueChar P).Coprime n)
    (hi : IntegralAt P ζ) : IsPrimitiveRoot (red P ζ hi) n := by
  let : NeZero n := ⟨hn⟩
  have hr := hζ.toInteger_isPrimitiveRoot.idealQuotient_mk
    (I := P.asIdeal) (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top)
    (PrimeUnitsAux.norm_coprime P hc)
  rw [← red_integer P hζ.toInteger hi] at hr
  exact hr

/-- Among n-th roots of unity, prime-to-p reduction is injective. -/
theorem roots_red_eq_iff (P : Prime L) {ζ ξ : L} {n : ℕ} (hn : n ≠ 0)
    (hζ : ζ ^ n = 1) (hξ : ξ ^ n = 1) (hc : (residueChar P).Coprime n) :
    red P ζ (root_integralAt P hn hζ) = red P ξ (root_integralAt P hn hξ) ↔ ζ = ξ := by
  constructor
  · intro h
    have hiζ : IsIntegral ℤ ζ :=
      IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hζ ▸ isIntegral_one)
    have hiξ : IsIntegral ℤ ξ :=
      IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hξ ▸ isIntegral_one)
    let a : 𝓞 L := ⟨ζ, hiζ⟩
    let b : 𝓞 L := ⟨ξ, hiξ⟩
    have ha : a ^ n = 1 := by
      apply RingOfIntegers.coe_injective (K := L)
      change ζ ^ n = 1
      exact hζ
    have hb : b ^ n = 1 := by
      apply RingOfIntegers.coe_injective (K := L)
      change ξ ^ n = 1
      exact hξ
    have hab : Ideal.Quotient.mk P.asIdeal a = Ideal.Quotient.mk P.asIdeal b := by
      rw [← red_integer P a (root_integralAt P hn hζ),
        ← red_integer P b (root_integralAt P hn hξ)]
      exact h
    exact congrArg (fun c : 𝓞 L => (c : L))
      (PrimeUnitsAux.integer_roots_quotient_injective P hn hc ha hb hab)
  · rintro rfl
    rfl

/-- Any chosen square root of a global unit is a local unit. Applications use the existing positive
square root e; no new square-root branch is chosen here. -/
theorem squareRoot_unitAt (P : Prime L) {e ε : L} (he : e ^ 2 = ε)
    (hε : IsIntegral ℤ ε) (hεinv : IsIntegral ℤ ε⁻¹) (hε0 : ε ≠ 0) : UnitAt P e := by
  apply (unitAt_iff_integral_inv P e).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hε0
    rw [← he, h, zero_pow (by decide)]
  · apply SICLean.L3.ValuationSupport.nonneg_of_square (valuation P)
    rw [he]
    exact PrimeUnitsAux.integralAt_of_isIntegral P hε
  · apply SICLean.L3.ValuationSupport.nonneg_of_square (valuation P)
    rw [inv_pow, he]
    exact PrimeUnitsAux.integralAt_of_isIntegral P hεinv

/-- The converse to local integrality needs all finite primes. -/
theorem isIntegral_iff_all_integralAt (x : L) :
    IsIntegral ℤ x ↔ ∀ P : Prime L, IntegralAt P x := by
  exact ⟨fun hx P => PrimeUnitsAux.integralAt_of_isIntegral P hx,
    PrimeUnitsAux.isIntegral_of_all_integralAt⟩

/-- Global integer units are precisely the elements of valuation zero everywhere. -/
theorem integer_unit_iff_all_unitAt (x : L) :
    (∃ a : 𝓞 L, IsUnit a ∧ (a : L) = x) ↔ ∀ P : Prime L, UnitAt P x := by
  constructor
  · rintro ⟨a, ha, rfl⟩ P
    exact (localRing_isUnit_iff P (algebraMap (𝓞 L) (LocalRing P) a)).mp
      (ha.map (algebraMap (𝓞 L) (LocalRing P)))
  · intro hx
    obtain ⟨J, hJ⟩ := Ideal.exists_maximal (𝓞 L)
    let P : Prime L := ⟨J, hJ.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hJ (RingOfIntegers.not_isField L)⟩
    have hx0 : x ≠ 0 := ((unitAt_iff_integral_inv P x).mp (hx P)).1
    have hi : IsIntegral ℤ x := (isIntegral_iff_all_integralAt x).mpr
      (fun Q => ((unitAt_iff_integral_inv Q x).mp (hx Q)).2.1)
    have hinv : IsIntegral ℤ x⁻¹ := (isIntegral_iff_all_integralAt x⁻¹).mpr
      (fun Q => ((unitAt_iff_integral_inv Q x).mp (hx Q)).2.2)
    obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 L)).mp hi
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 L)).mp hinv
    refine ⟨a, isUnit_iff_exists_inv.mpr ⟨b, ?_⟩, ha⟩
    apply RingOfIntegers.coe_injective
    simpa only [map_mul, map_one, ha, hb] using mul_inv_cancel₀ hx0

/-- The same ordinary-real coordinate function already used in L3. Zero has a top real coordinate.
-/
def realValuation (P : Prime L) (x : L) : ℝ :=
  SICLean.L3.ValuationSupport.realValue (valuation P) x

/-- Nonvanishing must be proved before returning from ℝ to WithTop ℝ. -/
theorem coe_realValuation (P : Prime L) {x : L} (hx : x ≠ 0) :
    (realValuation P x : WithTop ℝ) = valuation P x := by
  exact SICLean.L3.ValuationSupport.coe_realValue (valuation P) hx

/-- Ordinary real addition for nonzero products, as needed by w_I. -/
theorem realValuation_mul (P : Prime L) {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    realValuation P (x * y) = realValuation P x + realValuation P y := by
  exact SICLean.L3.ValuationSupport.realValue_mul (valuation P) hx hy

/-- Ordinary real coordinates of powers. -/
theorem realValuation_pow (P : Prime L) {x : L} (hx : x ≠ 0) (n : ℕ) :
    realValuation P (x ^ n) = n • realValuation P x := by
  exact SICLean.L3.ValuationSupport.realValue_pow (valuation P) hx n

/-- Without hx, realValue(0)=0 would make this equivalence false. -/
theorem realValuation_zero_iff (P : Prime L) {x : L} (hx : x ≠ 0) :
    realValuation P x = 0 ↔ UnitAt P x := by
  change realValuation P x = 0 ↔ valuation P x = 0
  rw [← coe_realValuation P hx, ← WithTop.coe_zero, WithTop.coe_eq_coe]

/-- Roots of unity contribute zero to the real-valued Fourier argument. -/
theorem root_realValuation_zero (P : Prime L) {ζ : L} {n : ℕ}
    (hn : n ≠ 0) (hζ : ζ ^ n = 1) : realValuation P ζ = 0 := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hζ
    exact zero_ne_one hζ
  exact (realValuation_zero_iff P hζ0).mpr (root_unitAt P hn hζ)

end SICLean.L5.FinitePlace

#check @SICLean.L3.ValuationSupport.value_pow_eq_one
#check @SICLean.L3.ValuationSupport.coe_realValue
#check @Ideal.rootsOfUnityMapQuot_injective
#check @SICLean.L5.FinitePlace.primitiveRoot_red
#print SICLean.L5.FinitePlace.realValuation
