import SICLean.L5.PrimePlace
import SICLean.L3.ValuationSupport

set_option autoImplicit false

/-!
# The normalized additive valuation

The sources are defined in PrimePlace. The normalization is [RW-rec, p. 4]; [RW26, p. 22]
uses it at p=2. No new global integrality or odd-prime-unit theorem is assumed.
`valuationFun` is an explicit rescaling, and the four valuation laws are separate proof
obligations rather than hypotheses of a model.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- Divide the discrete order by its absolute ramification index; top stays top. -/
def valuationFun (P : Prime L) (x : L) : WithTop ℝ :=
  WithTop.map (fun n : ℤ => (n : ℝ) / (absoluteRamification P : ℝ)) (ord P x)

/-- Rescaling preserves the value at zero. -/
theorem valuationFun_zero (P : Prime L) : valuationFun P 0 = ⊤ := by
  simp [valuationFun, ord_zero]

/-- Rescaling preserves the value at one. -/
theorem valuationFun_one (P : Prime L) : valuationFun P 1 = 0 := by
  simp [valuationFun, ord_one]

/-- Separate constructor obligation, not a hypothesis on P. -/
theorem valuationFun_mul (P : Prime L) (x y : L) :
    valuationFun P (x * y) = valuationFun P x + valuationFun P y := by
  unfold valuationFun
  rw [ord_mul]
  cases ord P x <;> cases ord P y <;>
    simp [← WithTop.coe_add, Int.cast_add, add_div]

/-- Positivity of e is needed for this rescaling. -/
theorem valuationFun_add (P : Prime L) (x y : L) :
    min (valuationFun P x) (valuationFun P y) ≤ valuationFun P (x + y) := by
  have he : 0 < (absoluteRamification P : ℝ) := by
    exact_mod_cast absoluteRamification_pos P
  have hf : Monotone (fun n : ℤ => (n : ℝ) / (absoluteRamification P : ℝ)) := by
    intro a b hab
    exact div_le_div_of_nonneg_right (Int.cast_le.mpr hab) he.le
  have hm := hf.withTop_map
  unfold valuationFun
  rw [min_le_iff]
  rcases min_le_iff.mp (ord_add P x y) with h | h
  · exact Or.inl (hm h)
  · exact Or.inr (hm h)

/-- The actual normalized AddValuation used by downstream Fourier/unit arguments. -/
def valuation (P : Prime L) : AddValuation L (WithTop ℝ) :=
  AddValuation.of (valuationFun P) (valuationFun_zero P) (valuationFun_one P)
    (valuationFun_add P) (valuationFun_mul P)

/-- Being integral here means integral in the local valuation ring. -/
def IntegralAt (P : Prime L) (x : L) : Prop := 0 ≤ valuation P x

/-- Being a local unit is stronger than nonvanishing in L. -/
def UnitAt (P : Prime L) (x : L) : Prop := valuation P x = 0

/-- Congruence mod the local maximal ideal. Residue comparison additionally requires integrality. -/
def Congruent (P : Prime L) (x y : L) : Prop := 0 < valuation P (x - y)

/-- Congruence mod P^n uses the integer order, not the p-normalized order. -/
def CongruentPow (P : Prime L) (n : ℕ) (x y : L) : Prop :=
  (n : WithTop ℤ) ≤ ord P (x - y)

/-- [RW-rec, p. 4] Exact normalization at the rational prime. -/
theorem valuation_residueChar (P : Prime L) : valuation P (residueChar P : L) = 1 := by
  have he : (absoluteRamification P : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (absoluteRamification_pos P))
  change valuationFun P (residueChar P : L) = 1
  simp [valuationFun, ord_residueChar, he]

/-- The explicit function is the function underlying the bundled valuation. -/
theorem valuation_apply (P : Prime L) (x : L) : valuation P x = valuationFun P x := by
  rfl

/-- Includes x=0, where the ordinary real coordinate does not apply. -/
theorem valuation_ne_top_iff (P : Prime L) (x : L) : valuation P x ≠ ⊤ ↔ x ≠ 0 := by
  exact (valuation P).ne_top_iff

/-- Explicit real coordinate only after proving nonvanishing. -/
theorem valuation_eq_coe_ord (P : Prime L) (x : L) (hx : x ≠ 0) :
    valuation P x = (((ord P x).untop₀ : ℝ) / (absoluteRamification P : ℝ) : ℝ) := by
  conv_lhs =>
    rw [valuation_apply, valuationFun,
      ← WithTop.coe_untop₀_of_ne_top ((ord_ne_top_iff P x).mpr hx), WithTop.map_coe]

/-- Bidirectional bridge before localization is introduced. -/
theorem integralAt_iff_ord_nonneg (P : Prime L) (x : L) :
    IntegralAt P x ↔ 0 ≤ ord P x := by
  have he : 0 < (absoluteRamification P : ℝ) := by
    exact_mod_cast absoluteRamification_pos P
  change 0 ≤ valuationFun P x ↔ 0 ≤ ord P x
  unfold valuationFun
  cases ord P x with
  | top => simp
  | coe a =>
    simp only [WithTop.map_coe, ← WithTop.coe_zero, WithTop.coe_le_coe]
    rw [le_div_iff₀ he, zero_mul]
    exact_mod_cast Iff.rfl

/-- Bidirectional unit bridge. -/
theorem unitAt_iff_ord_zero (P : Prime L) (x : L) : UnitAt P x ↔ ord P x = 0 := by
  have he : (absoluteRamification P : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (absoluteRamification_pos P))
  change valuationFun P x = 0 ↔ ord P x = 0
  unfold valuationFun
  cases ord P x with
  | top => simp
  | coe a => simp [he]

/-- Powers of the prime must be measured with the factor 1/e. -/
theorem congruentPow_iff_valuation (P : Prime L) (n : ℕ) (x y : L) :
    CongruentPow P n x y ↔
      (((n : ℝ) / (absoluteRamification P : ℝ) : ℝ) : WithTop ℝ) ≤ valuation P (x - y) := by
  have he : 0 < (absoluteRamification P : ℝ) := by
    exact_mod_cast absoluteRamification_pos P
  unfold CongruentPow
  rw [valuation_apply, valuationFun]
  cases ord P (x - y) with
  | top => simp
  | coe a =>
    simp only [WithTop.map_coe, ← WithTop.coe_natCast, WithTop.coe_le_coe]
    rw [div_le_div_iff_of_pos_right he]
    exact_mod_cast Iff.rfl

/-- Strict positivity agrees with the first discrete-order step. -/
theorem congruent_iff_pow_one (P : Prime L) (x y : L) :
    Congruent P x y ↔ CongruentPow P 1 x y := by
  have he : 0 < (absoluteRamification P : ℝ) := by
    exact_mod_cast absoluteRamification_pos P
  change 0 < valuationFun P (x - y) ↔ (1 : WithTop ℤ) ≤ ord P (x - y)
  unfold valuationFun
  cases ord P (x - y) with
  | top => simp
  | coe a =>
    simp only [WithTop.map_coe, ← WithTop.coe_zero, ← WithTop.coe_one,
      WithTop.coe_lt_coe, WithTop.coe_le_coe]
    rw [div_pos_iff_of_pos_right he, Int.cast_pos]
    omega

/-- Locally invertible iff the element and its inverse are integral. -/
theorem unitAt_iff_integral_inv (P : Prime L) (x : L) :
    UnitAt P x ↔ x ≠ 0 ∧ IntegralAt P x ∧ IntegralAt P x⁻¹ := by
  constructor
  · intro hx
    have hv : valuation P x = 0 := hx
    have hx0 : x ≠ 0 := (valuation_ne_top_iff P x).mp (by simp [hv])
    refine ⟨hx0, ?_, ?_⟩
    · change 0 ≤ valuation P x
      simp [hv]
    · change 0 ≤ valuation P x⁻¹
      rw [(valuation P).map_inv, hv]
      simp
  · rintro ⟨hx0, hx, hxi⟩
    change valuation P x = 0
    apply le_antisymm _ hx
    calc
      valuation P x ≤ valuation P x + valuation P x⁻¹ := le_add_of_nonneg_right hxi
      _ = 0 := by rw [← (valuation P).map_mul, mul_inv_cancel₀ hx0, (valuation P).map_one]

/-- Locally integral elements are closed under addition. -/
theorem integralAt_add (P : Prime L) {x y : L} (hx : IntegralAt P x) (hy : IntegralAt P y) :
    IntegralAt P (x + y) := by
  exact (valuation P).map_le_add hx hy

/-- Locally integral elements are closed under multiplication. -/
theorem integralAt_mul (P : Prime L) {x y : L} (hx : IntegralAt P x) (hy : IntegralAt P y) :
    IntegralAt P (x * y) := by
  change 0 ≤ valuation P (x * y)
  rw [(valuation P).map_mul]
  exact add_nonneg hx hy

end SICLean.L5.FinitePlace

#check @AddValuation.of
#check @SICLean.L3.ValuationSupport.realValue
#check @SICLean.L5.FinitePlace.valuation_residueChar
#print SICLean.L5.FinitePlace.valuationFun
#print SICLean.L5.FinitePlace.valuation
