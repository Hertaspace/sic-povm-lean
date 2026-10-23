import SICLean.L5.PrimeReduction

set_option autoImplicit false

/-!
# Arithmetic of actual reductions

All statements are localization/quotient consequences from PrimeReduction. Their use is
[RW-rec, Lemma 1, Thm. 8, §4, p. 4, p. 5, pp. 12--13, (13)]; [RW26, §5.2, pp. 22--23].
These are algebraic field values; no germ or new analytic special-value definition
occurs here.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- A local unit supplies the integrality proof required by `red`. -/
theorem unitAt_integral (P : Prime L) {x : L} (hx : UnitAt P x) : IntegralAt P x := by
  exact le_of_eq hx.symm

/-- Integrality of a negative. -/
theorem integralAt_neg (P : Prime L) {x : L} (hx : IntegralAt P x) : IntegralAt P (-x) := by
  simpa only [IntegralAt, AddValuation.map_neg] using hx

/-- Integrality of a difference. -/
theorem integralAt_sub (P : Prime L) {x y : L} (hx : IntegralAt P x) (hy : IntegralAt P y) :
    IntegralAt P (x - y) := by
  simpa only [sub_eq_add_neg] using integralAt_add P hx (integralAt_neg P hy)

/-- Integrality of nonnegative powers. -/
theorem integralAt_pow (P : Prime L) {x : L} (hx : IntegralAt P x) (n : ℕ) :
    IntegralAt P (x ^ n) := by
  exact (integralAt_iff_mem_localRing P _).mpr
    ((LocalRing P).pow_mem ((integralAt_iff_mem_localRing P x).mp hx) n)

/-- Division needs a local unit denominator. -/
theorem integralAt_div (P : Prime L) {x y : L} (hx : IntegralAt P x) (hy : UnitAt P y) :
    IntegralAt P (x / y) := by
  simpa only [div_eq_mul_inv] using
    integralAt_mul P hx ((unitAt_iff_integral_inv P y).mp hy).2.2

/-- Reduction of zero. -/
theorem red_zero (P : Prime L) : red P 0 (integralAt_integer P 0) = 0 := by
  exact map_zero (reduceRing P)

/-- Reduction of one. -/
theorem red_one (P : Prime L) : red P 1 (integralAt_integer P 1) = 1 := by
  exact map_one (reduceRing P)

/-- Reduction of a sum with its concrete integrality proof. -/
theorem red_add (P : Prime L) {x y : L} (hx : IntegralAt P x) (hy : IntegralAt P y) :
    red P (x + y) (integralAt_add P hx hy) = red P x hx + red P y hy := by
  exact map_add (reduceRing P)
    (⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩ : LocalRing P)
    (⟨y, (integralAt_iff_mem_localRing P y).mp hy⟩ : LocalRing P)

/-- Reduction of a product. -/
theorem red_mul (P : Prime L) {x y : L} (hx : IntegralAt P x) (hy : IntegralAt P y) :
    red P (x * y) (integralAt_mul P hx hy) = red P x hx * red P y hy := by
  exact map_mul (reduceRing P)
    (⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩ : LocalRing P)
    (⟨y, (integralAt_iff_mem_localRing P y).mp hy⟩ : LocalRing P)

/-- Reduction of a negative. -/
theorem red_neg (P : Prime L) {x : L} (hx : IntegralAt P x) :
    red P (-x) (integralAt_neg P hx) = -red P x hx := by
  exact map_neg (reduceRing P)
    (⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩ : LocalRing P)

/-- Reduction of a difference. -/
theorem red_sub (P : Prime L) {x y : L} (hx : IntegralAt P x) (hy : IntegralAt P y) :
    red P (x - y) (integralAt_sub P hx hy) = red P x hx - red P y hy := by
  exact map_sub (reduceRing P)
    (⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩ : LocalRing P)
    (⟨y, (integralAt_iff_mem_localRing P y).mp hy⟩ : LocalRing P)

/-- Reduction commutes with powers, including exponent zero. -/
theorem red_pow (P : Prime L) {x : L} (hx : IntegralAt P x) (n : ℕ) :
    red P (x ^ n) (integralAt_pow P hx n) = red P x hx ^ n := by
  exact map_pow (reduceRing P)
    (⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩ : LocalRing P) n

/-- Reduction commutes with inversion of a local unit. -/
theorem red_inv (P : Prime L) {x : L} (hx : UnitAt P x)
    (hi : IntegralAt P x⁻¹) :
    red P x⁻¹ hi = (red P x (unitAt_integral P hx))⁻¹ := by
  have hx0 : x ≠ 0 := ((unitAt_iff_integral_inv P x).mp hx).1
  apply eq_inv_of_mul_eq_one_left
  rw [← red_mul P hi (unitAt_integral P hx)]
  simpa only [inv_mul_cancel₀ hx0] using red_one P

/-- The ratio rule used by translation ratios and U=E/e. -/
theorem red_div (P : Prime L) {x y : L} (hx : IntegralAt P x) (hy : UnitAt P y) :
    red P (x / y) (integralAt_div P hx hy) =
      red P x hx / red P y (unitAt_integral P hy) := by
  have hi : IntegralAt P y⁻¹ := ((unitAt_iff_integral_inv P y).mp hy).2.2
  calc
    red P (x / y) (integralAt_div P hx hy) =
        red P x hx * red P y⁻¹ hi := by
      simpa only [div_eq_mul_inv] using red_mul P hx hi
    _ = red P x hx / red P y (unitAt_integral P hy) := by
      rw [red_inv P hy hi, div_eq_mul_inv]

/-- Two global integers are congruent mod P^n iff their field values are. -/
theorem congruentPow_integers_iff (P : Prime L) (n : ℕ) (a b : 𝓞 L) :
    CongruentPow P n (a : L) (b : L) ↔ a - b ∈ P.asIdeal ^ n := by
  rw [CongruentPow, ← map_sub (algebraMap (𝓞 L) L)]
  by_cases hab : a - b = 0
  · simp only [hab, map_zero, ord_zero, le_top, Submodule.zero_mem]
  · have hab0 : (algebraMap (𝓞 L) L) (a - b) ≠ 0 :=
      RingOfIntegers.coe_ne_zero_iff.mpr hab
    have hv0 : P.valuation L ((algebraMap (𝓞 L) L) (a - b)) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hab0
    calc
      (n : WithTop ℤ) ≤ ord P ((algebraMap (𝓞 L) L) (a - b)) ↔
          (n : ℤ) ≤ -WithZero.log (P.valuation L ((algebraMap (𝓞 L) L) (a - b))) := by
        simp only [ord, ite_eq_right hab0, ← WithTop.coe_natCast, WithTop.coe_le_coe]
      _ ↔ P.valuation L ((algebraMap (𝓞 L) L) (a - b)) ≤
          WithZero.exp (-(n : ℤ)) := by
        rw [← WithZero.log_le_iff_le_exp hv0]
        omega
      _ ↔ a - b ∈ P.asIdeal ^ n := by
        rw [P.valuation_of_algebraMap]
        exact P.intValuation_le_pow_iff_mem (a - b) n

end SICLean.L5.FinitePlace

#check @SICLean.L5.FinitePlace.red_div
#check @SICLean.L5.FinitePlace.congruentPow_integers_iff
