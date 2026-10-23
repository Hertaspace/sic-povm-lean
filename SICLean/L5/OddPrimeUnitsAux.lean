import SICLean.L3.PseudolatticeIdeal
import SICLean.L5.PeriodPowerData
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

set_option autoImplicit false

/-!
Elementary arithmetic and primary-group helpers for [RW-rec, Thm. 5]. All declarations
live in a namespace reserved for OddPrimeUnits.
-/

noncomputable section

namespace SICLean.L5.OddPrimeUnitsAux

open L3 NumberField

/-- A nontrivial primary component contains a nonzero element killed by p. No finiteness or
cyclicity is needed for this elementary step. -/
theorem exists_primary_torsion {G : Type*} [AddCommGroup G] (p : ℕ)
    [Nontrivial (AddCommGroup.primaryComponent G p)] :
    ∃ u : AddCommGroup.primaryComponent G p, u ≠ 0 ∧ p • u = 0 := by
  obtain ⟨g, hg⟩ := exists_ne (0 : AddCommGroup.primaryComponent G p)
  obtain ⟨k, hk⟩ := g.property
  have hkg : p ^ k • g = 0 := Subtype.ext hk
  have hex : ∀ k : ℕ, ∀ g : AddCommGroup.primaryComponent G p,
      g ≠ 0 → p ^ k • g = 0 →
      ∃ u : AddCommGroup.primaryComponent G p, u ≠ 0 ∧ p • u = 0 := by
    intro k
    induction k with
    | zero =>
        intro g hg hk
        exact (hg (by simpa using hk)).elim
    | succ k ih =>
        intro g hg hk
        by_cases hz : p ^ k • g = 0
        · exact ih g hg hz
        · refine ⟨p ^ k • g, hz, ?_⟩
          simpa only [pow_succ', mul_smul] using hk
  exact hex k g hg hkg

/-- Norms contract a principal rational-prime congruence back to ℕ. The square exponent comes from
the actual quadratic field degree. -/
theorem prime_dvd_of_natCast_mem {K : Type*} [Field K] [NumberField K]
    (P : PeriodData K) (p n : ℕ) (hp : p.Prime)
    (hn : (n : 𝓞 K) ∈ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) : p ∣ n := by
  have hd : p ^ 2 ∣ n ^ 2 := by
    have hle : Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) ≤
        Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) :=
      (Ideal.span_singleton_le_iff_mem _).mpr hn
    simpa only [Ideal.absNorm_span_natCast, RingOfIntegers.rank, P.finrank_eq_two]
      using Ideal.absNorm_dvd_absNorm_of_le hle
  exact hp.dvd_of_dvd_pow ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hd)

/-- The quadratic equation gives an inverse in the full integer ring. -/
theorem epsilonInteger_isUnit {K : Type*} [Field K] [NumberField K]
    (P : PeriodData K) : IsUnit (epsilonInteger P) := by
  refine isUnit_iff_exists_inv.mpr ⟨(P.N : 𝓞 K) + 2 - epsilonInteger P, ?_⟩
  apply RingOfIntegers.coe_injective
  change P.epsilon * ((P.N : K) + 2 - P.epsilon) = 1
  linear_combination -P.epsilon_polynomial

/-- A unit in a finite quotient has a positive power equal to one. -/
theorem exists_period_power_congruent {K : Type*} [Field K] [NumberField K]
    (P : PeriodData K) (p : ℕ) (hp : p.Prime) :
    ∃ r : ℕ, 0 < r ∧
      epsilonInteger P ^ r - 1 ∈ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  let J : Ideal (𝓞 K) := Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))
  have hJ : J ≠ ⊥ := by
    simpa [J] using (show (p : 𝓞 K) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne_zero)
  have : Finite (𝓞 K ⧸ J) := Ring.HasFiniteQuotients.finiteQuotient hJ
  obtain ⟨u, hu⟩ := (epsilonInteger_isUnit P).map (Ideal.Quotient.mk J)
  refine ⟨orderOf u, orderOf_pos u, ?_⟩
  apply (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
  rw [map_sub, map_pow, map_one, ← hu]
  exact sub_eq_zero.mpr
    (congrArg (fun v : (𝓞 K ⧸ J)ˣ => (v : 𝓞 K ⧸ J)) (pow_orderOf_eq_one u))

/-- Substituting the power congruence in its quadratic equation forces the new trace-minus-two
parameter to vanish modulo the rational prime. -/
theorem prime_dvd_power_order {K : Type*} [Field K] [NumberField K]
    (P : PeriodData K) (p : ℕ) (hp : p.Prime) (r : ℕ) (hr : 0 < r)
    (hc : epsilonInteger P ^ r - 1 ∈ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) :
    p ∣ (PeriodPower.powPeriod P r hr).N := by
  let J : Ideal (𝓞 K) := Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))
  have he : Ideal.Quotient.mk J (epsilonInteger P ^ r) = 1 := by
    have h := (Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr hc
    simpa only [map_sub, map_one, sub_eq_zero] using h
  have hpoly : (epsilonInteger P ^ r) ^ 2 -
      (((PeriodPower.powPeriod P r hr).N : 𝓞 K) + 2) * epsilonInteger P ^ r + 1 = 0 := by
    apply RingOfIntegers.coe_injective
    exact (PeriodPower.powPeriod P r hr).epsilon_polynomial
  have hmod := congrArg (Ideal.Quotient.mk J) hpoly
  have hN : Ideal.Quotient.mk J ((PeriodPower.powPeriod P r hr).N : 𝓞 K) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, map_ofNat, he] at hmod
    linear_combination -hmod
  exact prime_dvd_of_natCast_mem P p _ hp
    ((Ideal.Quotient.eq_zero_iff_mem (I := J)).mp hN)

end SICLean.L5.OddPrimeUnitsAux
