import SICLean.L5.PrimeReductionArithmetic
import SICLean.L5.PrimeCongruenceAux

set_option autoImplicit false

/-!
# Congruences, ideal powers, and finite arithmetic

The main Mathlib input is `intValuation_le_pow_iff_mem`.
[RW-rec, Lemma 1, Thm. 8, §4, pp. 4--7, pp. 12--13, (13)--(14)] use these operations.
`CongruentPow P 0` is a local integrality condition on a difference, not a universal
relation on all of L. No division by p in the residue field.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open NumberField
open scoped BigOperators

variable {L : Type*} [Field L] [NumberField L]

/-- The higher local residue ring, as opposed to the field k_P at n=1. -/
abbrev HigherResidue (P : Prime L) (n : ℕ) :=
  LocalRing P ⧸ (IsLocalRing.maximalIdeal (LocalRing P)) ^ n

/-- Reduction modulo the n-th power of the local maximal ideal, defined on locally integral values.
-/
def redPow (P : Prime L) (n : ℕ) (x : L) (hx : IntegralAt P x) : HigherResidue P n :=
  Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (LocalRing P)) ^ n)
    ⟨x, (integralAt_iff_mem_localRing P x).mp hx⟩

/-- Congruence includes equality because v(0)=top. -/
theorem congruent_refl (P : Prime L) (x : L) : Congruent P x x := by
  simp [Congruent]

/-- Symmetry of local congruence. -/
theorem congruent_symm (P : Prime L) {x y : L} (h : Congruent P x y) :
    Congruent P y x := by
  change 0 < valuation P (y - x)
  rwa [(valuation P).map_sub_swap]

/-- Transitivity of local congruence. -/
theorem congruent_trans (P : Prime L) {x y z : L}
    (hxy : Congruent P x y) (hyz : Congruent P y z) : Congruent P x z := by
  have h := lt_of_lt_of_le (lt_min hxy hyz) ((valuation P).map_add (x - y) (y - z))
  simpa only [Congruent, sub_add_sub_cancel] using h

/-- Addition preserves congruence. -/
theorem congruent_add (P : Prime L) {x x' y y' : L}
    (hx : Congruent P x x') (hy : Congruent P y y') :
    Congruent P (x + y) (x' + y') := by
  have h := lt_of_lt_of_le (lt_min hx hy) ((valuation P).map_add (x - x') (y - y'))
  change 0 < valuation P ((x + y) - (x' + y'))
  have he : (x - x') + (y - y') = (x + y) - (x' + y') := by ring
  rwa [he] at h

/-- Multiplication preserves congruence for locally integral values. -/
theorem congruent_mul (P : Prime L) {x x' y y' : L}
    (hx : IntegralAt P x) (hx' : IntegralAt P x')
    (hy : IntegralAt P y) (hy' : IntegralAt P y')
    (hxx' : Congruent P x x') (hyy' : Congruent P y y') :
    Congruent P (x * y) (x' * y') := by
  apply (red_eq_iff P _ _ (integralAt_mul P hx hy) (integralAt_mul P hx' hy')).mp
  rw [red_mul P hx hy, red_mul P hx' hy', (red_eq_iff P x x' hx hx').mpr hxx',
    (red_eq_iff P y y' hy hy').mpr hyy']

/-- Inverses preserve congruence when both elements are local units. -/
theorem congruent_inv (P : Prime L) {x y : L} (hx : UnitAt P x) (hy : UnitAt P y)
    (hxy : Congruent P x y) : Congruent P x⁻¹ y⁻¹ := by
  have hxi := ((unitAt_iff_integral_inv P x).mp hx).2.2
  have hyi := ((unitAt_iff_integral_inv P y).mp hy).2.2
  apply (red_eq_iff P _ _ hxi hyi).mp
  rw [red_inv P hx hxi, red_inv P hy hyi,
    (red_eq_iff P x y (unitAt_integral P hx) (unitAt_integral P hy)).mpr hxy]

/-- Stronger ideal-power congruence implies weaker congruence. -/
theorem congruentPow_mono (P : Prime L) {m n : ℕ} (hmn : m ≤ n) {x y : L}
    (h : CongruentPow P n x y) : CongruentPow P m x y := by
  exact le_trans (by exact_mod_cast hmn) h

/-- The zero-th ideal power condition is integrality of the difference. -/
theorem congruentPow_zero_iff (P : Prime L) (x y : L) :
    CongruentPow P 0 x y ↔ IntegralAt P (x - y) := by
  simpa only [CongruentPow, Nat.cast_zero] using (integralAt_iff_ord_nonneg P (x - y)).symm

/-- Quotient equality modulo P^n, for integer representatives. -/
theorem integer_quotient_pow_eq_iff (P : Prime L) (n : ℕ) (a b : 𝓞 L) :
    Ideal.Quotient.mk (P.asIdeal ^ n) a = Ideal.Quotient.mk (P.asIdeal ^ n) b ↔
      CongruentPow P n (a : L) (b : L) := by
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).trans
    (congruentPow_integers_iff P n a b).symm

/-- Fourier sums are locally integral when each summand is. -/
theorem integralAt_sum (P : Prime L) {ι : Type*} (s : Finset ι) (f : ι → L)
    (hf : ∀ i ∈ s, IntegralAt P (f i)) : IntegralAt P (∑ i ∈ s, f i) := by
  apply (integralAt_iff_mem_localRing P _).mpr
  exact (P.valuationSubringAtPrime L).toSubring.sum_mem
    (fun i hi => (integralAt_iff_mem_localRing P _).mp (hf i hi))

/-- The analogous closure for finite distribution products. -/
theorem integralAt_prod (P : Prime L) {ι : Type*} (s : Finset ι) (f : ι → L)
    (hf : ∀ i ∈ s, IntegralAt P (f i)) : IntegralAt P (∏ i ∈ s, f i) := by
  apply (integralAt_iff_mem_localRing P _).mpr
  exact (P.valuationSubringAtPrime L).toSubring.prod_mem
    (fun i hi => (integralAt_iff_mem_localRing P _).mp (hf i hi))

/-- Reduction of a finite sum; hypotheses over all indices make the RHS literal. -/
theorem red_sum (P : Prime L) {ι : Type*} (s : Finset ι) (f : ι → L)
    (hf : ∀ i, IntegralAt P (f i)) (hs : IntegralAt P (∑ i ∈ s, f i)) :
    red P (∑ i ∈ s, f i) hs = ∑ i ∈ s, red P (f i) (hf i) := by
  let g : ι → LocalRing P := fun i => ⟨f i, (integralAt_iff_mem_localRing P _).mp (hf i)⟩
  have hg : (⟨∑ i ∈ s, f i, (integralAt_iff_mem_localRing P _).mp hs⟩ : LocalRing P) =
      ∑ i ∈ s, g i := by
    apply Subtype.ext
    simp [g]
  change reduceRing P _ = ∑ i ∈ s, reduceRing P (g i)
  rw [hg, map_sum]

/-- Reduction of a finite product, including the empty product. -/
theorem red_prod (P : Prime L) {ι : Type*} (s : Finset ι) (f : ι → L)
    (hf : ∀ i, IntegralAt P (f i)) (hs : IntegralAt P (∏ i ∈ s, f i)) :
    red P (∏ i ∈ s, f i) hs = ∏ i ∈ s, red P (f i) (hf i) := by
  let g : ι → LocalRing P := fun i => ⟨f i, (integralAt_iff_mem_localRing P _).mp (hf i)⟩
  have hg : (⟨∏ i ∈ s, f i, (integralAt_iff_mem_localRing P _).mp hs⟩ : LocalRing P) =
      ∏ i ∈ s, g i := by
    apply Subtype.ext
    simp [g]
  change reduceRing P _ = ∏ i ∈ s, reduceRing P (g i)
  rw [hg, map_prod]

/-- The bidirectional mod-P^n bridge also covers locally integral non-global integers. -/
theorem redPow_eq_iff (P : Prime L) (n : ℕ) (x y : L)
    (hx : IntegralAt P x) (hy : IntegralAt P y) :
    redPow P n x hx = redPow P n y hy ↔ CongruentPow P n x y := by
  unfold redPow
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact PrimeCongruenceAux.localRing_mem_maximal_pow_iff P n _

/-- At n=1, the higher local quotient and the integer residue field give the same equality test. -/
theorem redPow_one_eq_iff_red_eq (P : Prime L) (x y : L)
    (hx : IntegralAt P x) (hy : IntegralAt P y) :
    redPow P 1 x hx = redPow P 1 y hy ↔ red P x hx = red P y hy := by
  rw [redPow_eq_iff, red_eq_iff, congruent_iff_pow_one]

end SICLean.L5.FinitePlace

#check @IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem
#check @SICLean.L5.FinitePlace.integer_quotient_pow_eq_iff
#check @SICLean.L5.FinitePlace.red_sum
#check @SICLean.L5.FinitePlace.redPow_eq_iff
#print SICLean.L5.FinitePlace.redPow
