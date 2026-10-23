import SICLean.L5.PrimeValuation

set_option autoImplicit false

/-!
# Reduction of locally integral field elements

[RW-rec, Lemma 1, §4, p. 4, p. 5]. Mathlib AdicValuation, `valuationSubringAtPrime`, its
localization instance and equality with the valuation ring;
`RingTheory/Localization/Defs.lean`, `IsLocalization.lift`.
`RingTheory/Ideal/Quotient/Defs.lean`, quotient map and kernel. `red P x hx` requires
local integrality. It is not a total reduction of L. The ring homomorphism has an
explicit localization-lift body, so this file does not assume a residue homomorphism or
its desired properties as data.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- The actual localization inside L, supplied by Mathlib. -/
abbrev LocalRing (P : Prime L) := P.valuationSubringAtPrime L

/-- Bidirectional valuation/localization bridge. -/
theorem integralAt_iff_mem_localRing (P : Prime L) (x : L) :
    IntegralAt P x ↔ x ∈ P.valuationSubringAtPrime L := by
  rw [integralAt_iff_ord_nonneg,
    P.valuationSubringAtPrime_eq_valuationSubring, Valuation.mem_valuationSubring_iff]
  by_cases hx : x = 0
  · simp [hx, ord_zero]
  · rw [ord, ite_eq_right hx, ← WithTop.coe_zero, WithTop.coe_le_coe, neg_nonneg]
    simpa using (WithZero.log_le_iff_le_exp ((Valuation.ne_zero_iff _).mpr hx)
      (a := (0 : ℤ)))

/-- Local integrality has a fraction with an integral numerator and denominator outside P. -/
theorem integralAt_iff_fraction (P : Prime L) (x : L) :
    IntegralAt P x ↔ ∃ a b : 𝓞 L, b ∉ P.asIdeal ∧ x = (a : L) / (b : L) := by
  rw [integralAt_iff_mem_localRing]
  change (∃ a b : 𝓞 L, ∃ _ : b ∈ P.asIdeal.primeCompl,
    x = (a : L) * (b : L)⁻¹) ↔ _
  simp only [Ideal.mem_primeCompl_iff, exists_prop, div_eq_mul_inv]

/-- Global integrality implies local integrality, without claiming the converse. -/
theorem integralAt_integer (P : Prime L) (a : 𝓞 L) : IntegralAt P (a : L) := by
  exact (integralAt_iff_ord_nonneg P _).mpr (ord_integer_nonneg P a)

/-- Units among global integers at this prime. -/
theorem unitAt_integer_iff (P : Prime L) (a : 𝓞 L) :
    UnitAt P (a : L) ↔ a ∉ P.asIdeal := by
  rw [unitAt_iff_ord_zero, ← ord_integer_pos_iff]
  exact ⟨fun h => by simp [h],
    fun h => le_antisymm (le_of_not_gt h) (ord_integer_nonneg P a)⟩

/-- A local-ring unit is exactly an element of valuation zero. -/
theorem localRing_isUnit_iff (P : Prime L) (a : LocalRing P) :
    IsUnit a ↔ UnitAt P (a : L) := by
  rw [unitAt_iff_integral_inv]
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
    have hab : (a : L) * (b : L) = 1 := congrArg Subtype.val hb
    refine ⟨left_ne_zero_of_mul_eq_one hab,
      (integralAt_iff_mem_localRing P _).mpr a.property, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hab]
    exact (integralAt_iff_mem_localRing P _).mpr b.property
  · rintro ⟨ha, _, h_inv⟩
    refine isUnit_iff_exists_inv.mpr
      ⟨⟨(a : L)⁻¹, (integralAt_iff_mem_localRing P _).mp h_inv⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ ha)

/-- The maximal ideal is exactly the positive-valuation locus. -/
theorem localRing_mem_maximal_iff (P : Prime L) (a : LocalRing P) :
    a ∈ IsLocalRing.maximalIdeal (LocalRing P) ↔ 0 < valuation P (a : L) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, localRing_isUnit_iff]
  change valuation P (a : L) ≠ 0 ↔ 0 < valuation P (a : L)
  have ha : 0 ≤ valuation P (a : L) :=
    (integralAt_iff_mem_localRing P _).mpr a.property
  exact ⟨fun h => lt_of_le_of_ne ha h.symm, ne_of_gt⟩

/-- The quotient map extends by inverting precisely the denominators outside P. -/
def reduceRing (P : Prime L) : LocalRing P →+* Residue P :=
  IsLocalization.lift (M := P.asIdeal.primeCompl) (g := Ideal.Quotient.mk P.asIdeal)
    (fun s => isUnit_iff_ne_zero.mpr
      (fun hs => s.property (Ideal.Quotient.eq_zero_iff_mem.mp hs)))

/-- Actual field-element reduction with explicit integrality evidence. -/
def red (P : Prime L) (x : L) (hx : IntegralAt P x) : Residue P :=
  reduceRing P ⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩

/-- The localization reduction extends the integer quotient map. -/
theorem reduceRing_integer (P : Prime L) (a : 𝓞 L) :
    reduceRing P (algebraMap (𝓞 L) (LocalRing P) a) = Ideal.Quotient.mk P.asIdeal a := by
  exact IsLocalization.lift_eq _ a

/-- Its kernel is the local maximal ideal, in valuation notation. -/
theorem reduceRing_eq_zero_iff (P : Prime L) (a : LocalRing P) :
    reduceRing P a = 0 ↔ 0 < valuation P (a : L) := by
  have hsurj : Function.Surjective (reduceRing P) := by
    intro r
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨algebraMap (𝓞 L) (LocalRing P) b, reduceRing_integer P b⟩
  rw [← localRing_mem_maximal_iff, ← IsLocalRing.ker_eq_maximalIdeal _ hsurj]
  rfl

/-- Every residue has an integer representative. -/
theorem reduceRing_surjective (P : Prime L) : Function.Surjective (reduceRing P) := by
  intro r
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨algebraMap (𝓞 L) (LocalRing P) a, reduceRing_integer P a⟩

/-- Field-element and integer-element reduction literally agree. -/
theorem red_integer (P : Prime L) (a : 𝓞 L) (ha : IntegralAt P (a : L)) :
    red P (a : L) ha = Ideal.Quotient.mk P.asIdeal a := by
  exact reduceRing_integer P a

/-- Bidirectional local-unit/residue bridge. -/
theorem red_ne_zero_iff (P : Prime L) (x : L) (hx : IntegralAt P x) :
    red P x hx ≠ 0 ↔ UnitAt P x := by
  change ¬reduceRing P ⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩ = 0 ↔ _
  rw [reduceRing_eq_zero_iff]
  exact ⟨fun h => le_antisymm (le_of_not_gt h) hx, fun h => by simp [UnitAt] at h; simp [h]⟩

/-- Two locally integral field elements have the same residue iff their difference is small. -/
theorem red_eq_iff (P : Prime L) (x y : L) (hx : IntegralAt P x) (hy : IntegralAt P y) :
    red P x hx = red P y hy ↔ Congruent P x y := by
  change reduceRing P ⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩ =
    reduceRing P ⟨y, (integralAt_iff_mem_localRing P y).mp hy⟩ ↔ _
  rw [← sub_eq_zero, ← map_sub, reduceRing_eq_zero_iff]
  rfl

/-- Denominator outside P is the precise local integrality condition used here. -/
theorem integralAt_fraction (P : Prime L) (a b : 𝓞 L) (hb : b ∉ P.asIdeal) :
    IntegralAt P ((a : L) / (b : L)) := by
  exact (integralAt_iff_fraction P _).mpr ⟨a, b, hb, rfl⟩

/-- Explicit fraction rule, including numerators in P. -/
theorem red_fraction (P : Prime L) (a b : 𝓞 L) (hb : b ∉ P.asIdeal) :
    red P ((a : L) / (b : L)) (integralAt_fraction P a b hb) =
      Ideal.Quotient.mk P.asIdeal a / Ideal.Quotient.mk P.asIdeal b := by
  have hb0 : (b : L) ≠ 0 := by
    intro h
    have : b = 0 := by exact_mod_cast h
    exact hb (this ▸ P.asIdeal.zero_mem)
  apply (eq_div_iff (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h))).mpr
  change reduceRing P ⟨(a : L) / (b : L),
    (integralAt_iff_mem_localRing P _).mp (integralAt_fraction P a b hb)⟩ *
      Ideal.Quotient.mk P.asIdeal b = Ideal.Quotient.mk P.asIdeal a
  rw [← reduceRing_integer P b, ← map_mul]
  convert reduceRing_integer P a using 1
  congr 1
  exact Subtype.ext (div_mul_cancel₀ _ hb0)

/-- The residue of a locally integral field element vanishes exactly at positive valuation. -/
theorem red_eq_zero_iff (P : Prime L) (x : L) (hx : IntegralAt P x) :
    red P x hx = 0 ↔ 0 < valuation P x := by
  exact reduceRing_eq_zero_iff P ⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩

end SICLean.L5.FinitePlace

#check @IsLocalization.lift
#check @IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
#check @SICLean.L5.FinitePlace.red_eq_iff
#print SICLean.L5.FinitePlace.reduceRing
#print SICLean.L5.FinitePlace.red
