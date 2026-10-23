import SICLean.L5.OddPrimeCyclic
import SICLean.L5.OddPrimeLatticeChain
import SICLean.L5.OddPrimeMaximum
import SICLean.L5.OddPrimeUnitsAux

set_option autoImplicit false

/-!
# [RW-rec, Thm. 5] at every odd finite place

[RW-rec, pp. 8--9], with the finite-homothety argument on pp. 7--8. The proof first
treats p | N by Lemmas 2--3 and Theorem 4, then changes the period to epsilon^r for a
general prime. [RW26] supplies the algebraicity input. The power-period input is
[RW26, Prop. 8, p. 14]. The maximum
argument and positive-period descent use the upstream theorems directly; none of these
results is an assumption or axiom.
-/

noncomputable section
open scoped Classical BigOperators

namespace SICLean.L5.OddPrimeUnits

open L3 OddPrimeValues NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- [RW-rec, p. 9]: an attained global maximum coefficient is zero. The bound ranges over every
lattice, including every step of Lemma3; it is discharged by OddPrimeMaximum, not required by the
final theorem. -/
theorem maximal_coefficient_zero_of_dvd (P : PeriodData K)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hdiv : p ∣ P.N)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (I : StablePseudolattice P) (θ : AddChar (PseudolatticeGroup P I) ℂ)
    (hmax : ∀ (J : StablePseudolattice P) (χ : AddChar (PseudolatticeGroup P J) ℂ),
      ‖valuationFourier P J v χ‖ ≤ ‖valuationFourier P I v θ‖) :
    valuationFourier P I v θ = 0 := by
  obtain ⟨r, lattices, characters, hzero, hcharacters, hsteps, hc, hn, hfaithful⟩ :=
    OddPrimeLatticeChain.lemma3 P I θ p (Fact.out : p.Prime) hdiv
  have hstart : valuationFourier P (lattices 0) v (characters 0) =
      valuationFourier P I v θ := by
    cases hzero
    have hθ : characters 0 = θ := by
      ext x
      exact DFunLike.congr_fun hcharacters x
    rw [hθ]
  have hconstant : ∀ i : Fin (r + 1),
      valuationFourier P (lattices i) v (characters i) = valuationFourier P I v θ := by
    intro i
    induction i using Fin.induction with
    | zero => exact hstart
    | succ i ih =>
        obtain ⟨hstep, hperiod, hcompatible, _⟩ := hsteps i
        apply OddPrimeMaximum.compatible_coefficient_eq_of_maximum P
          (lattices i.castSucc) (lattices i.succ) hstep
          (fun z hz => hperiod ((pseudolatticeScale_mem_iff _ _ _).mpr ⟨z, hz, rfl⟩))
          v (characters i.castSucc) (valuationFourier P I v θ) ih hmax
          (characters i.succ)
        intro x
        exact DFunLike.congr_fun hcompatible x
  have : Nontrivial (AddCommGroup.primaryComponent
    (PseudolatticeGroup P (lattices (Fin.last r))) p) := hn
  obtain ⟨u, hu, hpu⟩ := OddPrimeUnitsAux.exists_primary_torsion
    (G := PseudolatticeGroup P (lattices (Fin.last r))) p
  have hθu : characters (Fin.last r) u.val ≠ 1 := by
    intro h
    apply hu
    apply hfaithful
    simpa using h
  have hpu' : p • u.val = 0 := by
    exact congrArg Subtype.val hpu
  have hfinal : valuationFourier P (lattices (Fin.last r)) v
      (characters (Fin.last r)) = 0 :=
    OddPrimeMaximum.valuationFourier_eq_zero_of_translation P
      (lattices (Fin.last r)) v (characters (Fin.last r)) u.val
      (fun x => OddPrimeCyclic.weight_constant_on_p_cosets P
        (lattices (Fin.last r)) p hodd v hp hc hn x u.val hpu') hθu
  exact (hconstant (Fin.last r)).symm.trans hfinal

/-- [RW-rec, p. 9]: maximality forces all ordinary complex Fourier coefficients to vanish. No chosen
representative is retained as an input. -/
theorem all_coefficients_zero_of_dvd (P : PeriodData K)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hdiv : p ∣ P.N)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (I : StablePseudolattice P) (θ : AddChar (PseudolatticeGroup P I) ℂ) :
    valuationFourier P I v θ = 0 := by
  obtain ⟨J, χ, hmaximum⟩ := OddPrimeMaximum.exists_global_maximum P v
  exact OddPrimeMaximum.all_fourier_zero_of_maximum_zero P v J χ hmaximum
    (maximal_coefficient_zero_of_dvd P p hodd hdiv v hp J χ hmaximum) I θ

/-- [RW-rec, p. 9]: character inversion gives the real-valued weight zero on each lattice. -/
theorem weight_zero_of_dvd (P : PeriodData K)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hdiv : p ∣ P.N)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (I : StablePseudolattice P) (x : PseudolatticeGroup P I) : weight P I v x = 0 := by
  exact (OddPrimeMaximum.weight_zero_iff_fourier_zero P I v).mpr
    (all_coefficients_zero_of_dvd P p hodd hdiv v hp I) x

/-- [RW-rec, Thm. 5]: the case p | N. Nonvanishing from OddPrimeValues prevents a convention at
zero from entering the unit statement. -/
theorem valuation_zero_of_dvd (P : PeriodData K)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hdiv : p ∣ P.N)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (I : StablePseudolattice P) (x : PseudolatticeGroup P I) : v (lift P I x) = 0 := by
  rw [← coe_weight P I v x, weight_zero_of_dvd P p hodd hdiv v hp I x]
  rfl

/-- [RW-rec, p. 9]: the existing integral epsilon is a unit of the full integer ring, before
reduction modulo p. -/
theorem epsilonInteger_isUnit (P : PeriodData K) : IsUnit (epsilonInteger P) := by
  exact OddPrimeUnitsAux.epsilonInteger_isUnit P

/-- [RW-rec, p. 9]: the quotient ring O_K/p O_K is finite; the residue of the actual epsilon is a
unit, so some positive power is 1. No choice of prime ideal above p or unramifiedness is needed. -/
theorem exists_period_power_congruent (P : PeriodData K) (p : ℕ) (hp : p.Prime) :
    ∃ r : ℕ, 0 < r ∧
      epsilonInteger P ^ r - 1 ∈ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  exact OddPrimeUnitsAux.exists_period_power_congruent P p hp

/-- [RW-rec, p. 9]: integer congruence forces divisibility of the new trace-minus-two order. The
existing powPeriod is used literally. [RW26, Prop. 8, p. 14] gives the analytic power law. -/
theorem prime_dvd_power_order (P : PeriodData K) (p : ℕ) (hp : p.Prime)
    (r : ℕ) (hr : 0 < r)
    (hc : epsilonInteger P ^ r - 1 ∈ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) :
    p ∣ (PeriodPower.powPeriod P r hr).N := by
  exact OddPrimeUnitsAux.prime_dvd_power_order P p hp r hr hc

/-- [RW-rec, p. 9]: an auxiliary period exists for every prime, including those already dividing N.
The final theorem only uses odd primes. -/
theorem exists_power_order_divisible (P : PeriodData K) (p : ℕ) (hp : p.Prime) :
    ∃ r : ℕ, ∃ hr : 0 < r, p ∣ (PeriodPower.powPeriod P r hr).N := by
  obtain ⟨r, hr, hc⟩ := exists_period_power_congruent P p hp
  exact ⟨r, hr, prime_dvd_power_order P p hp r hr hc⟩

/-- [RW-rec, p. 4, p. 9, (8)]; [RW26, Prop. 8, p. 14]. The point of the smaller lattice is included
in K/I, rather than
keeping integer row labels fixed. -/
theorem weight_pow (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (r : ℕ) (hr : 0 < r)
    (x : PseudolatticeGroup P I) :
    weight (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr) v
      (PeriodPower.periodPowerInclusion P I r hr x) = r * weight P I v x := by
  unfold weight
  rw [lift_pow, ValuationSupport.realValue_pow v (lift_ne_zero P I x), nsmul_eq_mul]

/-- [RW-rec, p. 9]: descend along a positive power at the same v. The local zero of the power value
is the explicit intermediate input; it is supplied by valuation_zero_of_dvd in the final theorem. -/
theorem valuation_zero_of_power (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (r : ℕ) (hr : 0 < r)
    (x : PseudolatticeGroup P I)
    (hx : v (lift (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr)
      (PeriodPower.periodPowerInclusion P I r hr x)) = 0) : v (lift P I x) = 0 := by
  have hweight : weight (PeriodPower.powPeriod P r hr)
      (PeriodPower.powLattice P I r hr) v
      (PeriodPower.periodPowerInclusion P I r hr x) = 0 := by
    apply WithTop.coe_eq_coe.mp
    simpa only [coe_weight, WithTop.coe_zero] using hx
  rw [weight_pow] at hweight
  have hxweight : weight P I v x = 0 :=
    (mul_eq_zero.mp hweight).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr))
  rw [← coe_weight P I v x, hxweight]
  rfl

/-- [RW-rec, Thm. 5, p. 9]: all actual values, all stable lattices and periods, every odd prime,
every normalized valuation above it. No good-prime, p∤24, p∤N, parity, conductor, or 2-adic input;
[RW26] inputs are precisely those in the header. -/
theorem odd_prime_valuation_zero (P : PeriodData K) (I : StablePseudolattice P)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (x : PseudolatticeGroup P I) : v (lift P I x) = 0 := by
  obtain ⟨r, hr, hdiv⟩ := exists_power_order_divisible P p (Fact.out : p.Prime)
  exact valuation_zero_of_power P I v r hr x
    (valuation_zero_of_dvd (PeriodPower.powPeriod P r hr) p hodd hdiv v hp
      (PeriodPower.powLattice P I r hr) (PeriodPower.periodPowerInclusion P I r hr x))

/-- The exact UnitValued call shape consumed by LocalActualFourier and the later Frobenius blocks;
same [RW-rec] [RW26] provenance as the previous theorem. The property is an output, never a field of
a value definition. -/
theorem odd_prime_unitValued (P : PeriodData K) (I : StablePseudolattice P)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1) :
    LocalFourierSetup.UnitValued v (lift P I) := by
  exact fun x => odd_prime_valuation_zero P I p hodd v hp x

#check @L3.epsilonInteger
#check @PeriodPower.powPeriod
#check @OddPrimeValues.lift_pow
#check @valuation_zero_of_dvd
#check @odd_prime_valuation_zero
#check @odd_prime_unitValued

end SICLean.L5.OddPrimeUnits
