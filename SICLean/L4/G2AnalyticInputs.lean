import SICLean.L4.G2AttractingIdentities
import SICLean.L4.SpecialValueL2c
import SICLean.L4.SpecialValueL2rc

set_option autoImplicit false

/-!
# The two actual-value [RW26] input wrappers

Coordinate transport and final assembly. [RW26, p. 3, (6), (7),
p. 14, Prop. 8]; γ = α³, [RW26, p. 20]. Rank-r arithmetic is reused by rwL2rcPeriod_odd_power.

The file uses the existing rwL2cEquiv/rwL2rcEquiv, Gaussian, pairing, F± and input structures. The
Fourier
multiplier is literally etaMultiplier of the same period matrix, nonzero and common to every u. The
identities precede their off-origin restrictions. The final two outputs accept only hG1 as an
analytic premise, then apply the `_of_sums` theorems.

The period is definitionally rwL2cBase M ^ 3. Rank-r uses the existing rwL2rcPeriod_odd_power, not a
hypothesized odd exponent. The existing base unit-action theorems fill Prop. 8; the period's own
trivial quotient action is not substituted. No finite Fourier inversion, (31), or (36) is repeated.
-/

noncomputable section

open Classical Complex
open scoped BigOperators MatrixGroups

namespace SICLean.L4

/-- Exact finite-sum coordinate transport, including the positive √N. [RW26, (3), (6), p. 3] [RW26,
p. 20]. It uses the existing cardinal/order identity. -/
theorem rwL2c_normalizedValueSum (M : ℕ) [Fact (4 ≤ M)]
    (f : L2c.RWGroup M → ℂ) :
    L2c.normalizedSum M f =
      G2.SpecialValueBridge.normalizedValueSum (rwL2cPeriod M) (rwL2c_admissible M).2
        (fun x => f ((rwL2cEquiv M).symm x)) := by
  letI : Finite (SpecialValueGroup (rwL2cPeriod M)) :=
    specialValueGroup_finite (rwL2cPeriod M) (rwL2c_admissible M).2
  letI : Fintype (SpecialValueGroup (rwL2cPeriod M)) := Fintype.ofFinite _
  have hsqrt : (Real.sqrt (specialValueOrder (rwL2cPeriod M) : ℝ) : ℂ) =
      L2c.sqrtOrder M := by
    rw [(rwL2c_parameters M).1]
    simp only [Int.cast_natCast, L2c.sqrtOrder]
  unfold L2c.normalizedSum G2.SpecialValueBridge.normalizedValueSum
  rw [hsqrt, div_eq_mul_inv, mul_comm]
  congr 1
  exact Fintype.sum_equiv (rwL2cEquiv M).toEquiv f
    (fun x => f ((rwL2cEquiv M).symm x)) (fun x => by simp)

/-- The common μ is specifically etaMultiplier(α³), not etaMultiplier(α). The nonzero assertion is
outside the quantifier over all u, including 0. [RW26, (6), p. 3] [RW26, p. 20]. -/
theorem rwL2c_fourier_of_G1 (hG1 : G1RealConclusion)
    (M : ℕ) [Fact (4 ≤ M)] :
    etaMultiplier (rwL2cPeriod M) ≠ 0 ∧
      ∀ u : L2c.RWGroup M,
        L2c.normalizedSum M (fun x => L2c.pairing M x u * rwL2cPlus M x) =
          etaMultiplier (rwL2cPeriod M) / rwL2cMinus M u := by
  refine ⟨etaMultiplier_ne_zero _ (rwL2c_admissible M).2.1, ?_⟩
  intro u
  rw [rwL2c_normalizedValueSum]
  simpa only [rwL2cPlus, rwL2cMinus, Function.comp_apply, ← rwL2c_pairing,
    AddEquiv.apply_symm_apply] using
    G2.AttractingIdentities.attracting_fourier hG1 (rwL2cPeriod M)
      (rwL2c_admissible M).2 (rwL2cEquiv M u)

/-- The formula in the original coordinates, before restriction. The correction uses the actual
common group order and plus origin. [RW26, (7), p. 3]. -/
theorem rwL2c_pentagon_of_G1 (hG1 : G1RealConclusion)
    (M : ℕ) [Fact (4 ≤ M)] :
    ∀ u v : L2c.RWGroup M,
      L2c.normalizedSum M (fun x => L2c.pairing M x u *
        (rwL2cPlus M x / rwL2cMinus M (x + v))) =
      rwL2cPlus M (u + v) / (rwL2cMinus M u * rwL2cMinus M v) -
        (if u = 0 ∧ v = 0 then (L2b.groupOrder M : ℂ) * rwL2cPlus M 0 else 0) := by
  intro u v
  rw [rwL2c_normalizedValueSum]
  simpa only [rwL2cPlus, rwL2cMinus, Function.comp_apply, ← rwL2c_pairing,
    map_add, map_zero, AddEquiv.apply_symm_apply, AddEquiv.map_eq_zero_iff,
    (rwL2c_parameters M).1, Int.cast_natCast] using
    G2.AttractingIdentities.attracting_pentagon hG1 (rwL2cPeriod M)
      (rwL2c_admissible M).2 (rwL2cEquiv M u) (rwL2cEquiv M v)

/-- Exact hratio call shape of rwL2cAnalyticInput_of_sums. [RW26, (7), p. 3]. -/
theorem rwL2c_ratio_off_origin_of_G1 (hG1 : G1RealConclusion)
    (M : ℕ) [Fact (4 ≤ M)] :
    ∀ u v : L2c.RWGroup M, (u, v) ≠ (0, 0) →
      L2c.normalizedSum M (fun x => L2c.pairing M x u *
        (rwL2cPlus M x / rwL2cMinus M (x + v))) =
      rwL2cPlus M (u + v) / (rwL2cMinus M u * rwL2cMinus M v) := by
  intro u v huv
  have hzero : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨rfl, rfl⟩
    exact huv rfl
  simpa only [if_neg hzero, sub_zero] using rwL2c_pentagon_of_G1 hG1 M u v

/-- Final original input, obtained from `rwL2cAnalyticInput_of_sums` with the preceding common μ
and restricted ratio identity. Its proved rwL2c_epsilon_invariant supplies the base α action, with
γ=α³. [RW26, Thm. 2, p. 3, Prop. 8, p. 14, §4.4, p. 20]. -/
theorem rwL2cAnalyticInput_of_G1 (hG1 : G1RealConclusion)
    (M : ℕ) [Fact (4 ≤ M)] :
    L2c.RWAnalyticInput M (rwL2cPlus M) (rwL2cMinus M) := by
  exact rwL2cAnalyticInput_of_sums M
    ⟨etaMultiplier (rwL2cPeriod M), rwL2c_fourier_of_G1 hG1 M⟩
    (rwL2c_ratio_off_origin_of_G1 hG1 M)

/-- Rank-r exact transport, including the existing true-quotient equivalence and the positive √N.
[RW26, (3), (6), p. 3]. -/
theorem rwL2rc_normalizedValueSum (d r : ℕ) [Fact (L2r.Admissible d r)]
    (f : L2rc.RWGroup d r → ℂ) :
    L2rc.normalizedSum d r f =
      G2.SpecialValueBridge.normalizedValueSum (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
        (fun x => f ((rwL2rcEquiv d r).symm x)) := by
  letI : Finite (SpecialValueGroup (rwL2rcPeriod d r)) :=
    specialValueGroup_finite (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
  letI : Fintype (SpecialValueGroup (rwL2rcPeriod d r)) := Fintype.ofFinite _
  have hsqrt : (Real.sqrt (specialValueOrder (rwL2rcPeriod d r) : ℝ) : ℂ) =
      L2rc.sqrtOrder d r := by
    rw [(rwL2rc_parameters d r).1]
    simp only [Int.cast_natCast, L2rc.sqrtOrder]
  unfold L2rc.normalizedSum G2.SpecialValueBridge.normalizedValueSum
  rw [hsqrt, div_eq_mul_inv, mul_comm]
  congr 1
  exact Fintype.sum_equiv (rwL2rcEquiv d r).toEquiv f
    (fun x => f ((rwL2rcEquiv d r).symm x)) (fun x => by simp)

/-- The same actual period multiplier for all rank-r u, including zero. [RW26, (6), p. 3]. -/
theorem rwL2rc_fourier_of_G1 (hG1 : G1RealConclusion)
    (d r : ℕ) [Fact (L2r.Admissible d r)] :
    etaMultiplier (rwL2rcPeriod d r) ≠ 0 ∧
      ∀ u : L2rc.RWGroup d r,
        L2rc.normalizedSum d r (fun x => L2rc.pairing d r x u * rwL2rcPlus d r x) =
          etaMultiplier (rwL2rcPeriod d r) / rwL2rcMinus d r u := by
  refine ⟨etaMultiplier_ne_zero _ (rwL2rc_admissible d r).2.1, ?_⟩
  intro u
  rw [rwL2rc_normalizedValueSum]
  simpa only [rwL2rcPlus, rwL2rcMinus, Function.comp_apply, ← rwL2rc_pairing,
    AddEquiv.apply_symm_apply] using
    G2.AttractingIdentities.attracting_fourier hG1 (rwL2rcPeriod d r)
      (rwL2rc_admissible d r).2 (rwL2rcEquiv d r u)

/-- The rank-r formula, including both zero parameters. [RW26, (7), p. 3]. -/
theorem rwL2rc_pentagon_of_G1 (hG1 : G1RealConclusion)
    (d r : ℕ) [Fact (L2r.Admissible d r)] :
    ∀ u v : L2rc.RWGroup d r,
      L2rc.normalizedSum d r (fun x => L2rc.pairing d r x u *
        (rwL2rcPlus d r x / rwL2rcMinus d r (x + v))) =
      rwL2rcPlus d r (u + v) / (rwL2rcMinus d r u * rwL2rcMinus d r v) -
        (if u = 0 ∧ v = 0 then (L2r.groupOrder d r : ℂ) * rwL2rcPlus d r 0 else 0) := by
  intro u v
  rw [rwL2rc_normalizedValueSum]
  simpa only [rwL2rcPlus, rwL2rcMinus, Function.comp_apply, ← rwL2rc_pairing,
    map_add, map_zero, AddEquiv.apply_symm_apply, AddEquiv.map_eq_zero_iff,
    (rwL2rc_parameters d r).1, Int.cast_natCast] using
    G2.AttractingIdentities.attracting_pentagon hG1 (rwL2rcPeriod d r)
      (rwL2rc_admissible d r).2 (rwL2rcEquiv d r u) (rwL2rcEquiv d r v)

/-- Exact hratio call shape of rwL2rcAnalyticInput_of_sums. [RW26, (7), p. 3]. -/
theorem rwL2rc_ratio_off_origin_of_G1 (hG1 : G1RealConclusion)
    (d r : ℕ) [Fact (L2r.Admissible d r)] :
    ∀ u v : L2rc.RWGroup d r, (u, v) ≠ (0, 0) →
      L2rc.normalizedSum d r (fun x => L2rc.pairing d r x u *
        (rwL2rcPlus d r x / rwL2rcMinus d r (x + v))) =
      rwL2rcPlus d r (u + v) / (rwL2rcMinus d r u * rwL2rcMinus d r v) := by
  intro u v huv
  have hzero : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨rfl, rfl⟩
    exact huv rfl
  simpa only [if_neg hzero, sub_zero] using rwL2rc_pentagon_of_G1 hG1 d r u v

/-- Final rank-r input. The proof calls the existing `_of_sums`; no Prop. 8 or odd-power premise is
accepted.
rwL2rcPeriod_odd_power supplies the actual positive odd power for the base-unit invariance route.
[RW26, Thm. 2, p. 3, Prop. 8, p. 14]. -/
theorem rwL2rcAnalyticInput_of_G1 (hG1 : G1RealConclusion)
    (d r : ℕ) [Fact (L2r.Admissible d r)] :
    L2rc.RWAnalyticInput d r (rwL2rcPlus d r) (rwL2rcMinus d r) := by
  exact rwL2rcAnalyticInput_of_sums d r
    ⟨etaMultiplier (rwL2rcPeriod d r), rwL2rc_fourier_of_G1 hG1 d r⟩
    (rwL2rc_ratio_off_origin_of_G1 hG1 d r)

#print rwL2cPeriod
#check @rwL2rcPeriod_odd_power
#check @etaMultiplier_ne_zero
#check @rwL2c_epsilon_invariant
#check @rwL2rc_epsilon_invariant
#check @rwL2cAnalyticInput_of_sums
#check @rwL2rcAnalyticInput_of_sums
#print rwL2cAnalyticInput_of_G1
#print rwL2rcAnalyticInput_of_G1
#check @matrixPentagon_of_G1

end SICLean.L4
