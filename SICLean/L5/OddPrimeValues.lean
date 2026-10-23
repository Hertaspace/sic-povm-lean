import SICLean.L5.ActualValueBridge
import SICLean.L5.FiniteAlgebraicTransport
import SICLean.L5.PeriodPowerValues
import SICLean.L5.DistributionNormalized
import SICLean.L5.PrimeUnits
import SICLean.L5.PrimeTower
import SICLean.L5.OddPrimeValuesAux

set_option autoImplicit false

/-!
# The same actual values on every stable pseudolattice

The actual point values are lifted through the fixed complex embedding. The definitions
below lift the existing M72 point values. In particular they do not replace modularPhi,
phiExtended, etaMultiplier, or their slit-plane principal square root, and do not
evaluate a punctured germ at its center. The ordinary complex transform of real
valuations in [RW-rec, §5] is different from the algebraic, pairing-indexed transform in
[RW-rec, §4]. All P, I are quantified: there is no restriction to a chosen class
representative, an invertible ideal, an even N, or a base period. The
valuation-extension obligation below is explicit, so a finite-prime conclusion will not
retain an assumed valuation on Qbar.
-/

noncomputable section
open scoped Classical BigOperators MatrixGroups

namespace SICLean.L5.OddPrimeValues

open L3

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- [RW-rec, Prop. 1, p. 3]; [RW26, Thm. 1, p. 3]. Wrapper of the existing chosen-family
algebraicity statement, with proved G1, for every actual lattice. -/
theorem value_isAlgebraic (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) : IsAlgebraic ℚ (M72.value P I x) := by
  rw [OddPrimeValuesAux.value_matrixEquiv]
  exact FiniteAlgebraicTransport.actual_value_isAlgebraic _ _ _

/-- The fixed-embed preimage of M72.value, not an extra solution of finite equations. -/
def lift (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) : Galois.Qbar :=
  Galois.algebraicLift (M72.value P I x) (value_isAlgebraic P I x)

/-- [RW-rec, §5, p. 7]: w is real only after nonvanishing has been checked. -/
def weight (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (x : PseudolatticeGroup P I) : ℝ :=
  ValuationSupport.realValue v (lift P I x)

/-- [RW-rec, §5, p. 7]: ordinary complex character transform, inverse character and positive
sqrt(N). No local reduction occurs in this definition. -/
def valuationFourier (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ))
    (θ : AddChar (PseudolatticeGroup P I) ℂ) : ℂ :=
  letI : Finite (PseudolatticeGroup P I) := (pseudolatticeGroup_finite_card P I).1
  letI : Fintype (PseudolatticeGroup P I) := Fintype.ofFinite _
  (Real.sqrt (P.N : ℝ) : ℂ)⁻¹ * ∑ x, (weight P I v x : ℂ) * (θ x)⁻¹

/-- Fixed-embed bridge; [RW26, p. 2, p. 3, (2), (4)]; [RW-rec]. -/
theorem embed_lift (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) : Galois.embed (lift P I x) = M72.value P I x := by
  exact Galois.embed_algebraicLift _ _

/-- Nonzero point values, including the prescribed origin. [RW26, Lemma 2, p. 6, p. 12];
[RW-rec, Def. 1]. -/
theorem lift_ne_zero (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) : lift P I x ≠ 0 := by
  intro h
  have hz := congrArg Galois.embed h
  rw [embed_lift, map_zero] at hz
  exact M72.value_ne_zero P I x hz

/-- No empty-preimage shortcut. Specialization of ActualValues.lift_unique; [RW26, p. 2, (2)];
[RW-rec, Def. 1]. -/
theorem lift_of_embed (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) (a : Galois.Qbar)
    (ha : Galois.embed a = M72.value P I x) : a = lift P I x := by
  exact ActualValues.lift_unique _ (value_isAlgebraic P I x) a ha

/-- Identification with the existing matrix lift, not a duplicate matrix definition; [RW26, p. 2, p.
20, (2), (37)]; [RW-rec]. -/
theorem lift_matrix (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : L4.SpecialValueGroup M) :
    lift (ActualField.periodData M hM) (ActualLattice.stableLattice M hM)
      (ActualLattice.labelEquiv M hM x) = FiniteAlgebraicTransport.value M hM x := by
  apply Galois.embed.injective
  change Galois.embed (lift _ _ _) = Galois.embed (FiniteAlgebraicTransport.value M hM x)
  rw [embed_lift, FiniteAlgebraicTransport.embed_value]
  exact ActualValues.value_label M hM x

/-- The zero branch is the same positive sqrt(epsilon), for every lattice; [RW26, p. 3, (4),
footnote 2]; [RW-rec, Def. 1]. No assertion E(0)=epsilon is made. -/
theorem lift_zero_independent (P : PeriodData K) (I J : StablePseudolattice P) :
    lift P I 0 = lift P J 0 := by
  apply Galois.embed.injective
  change Galois.embed (lift P I 0) = Galois.embed (lift P J 0)
  rw [embed_lift, embed_lift, M72.value_zero, M72.value_zero]

/-- [RW-rec, §5] uses w(0)=0, p. 7; [RW26, p. 3, (4)]. The root is a unit because epsilon and its
inverse are integral; no hypothesis that nonzero E-values are units occurs here. -/
theorem zero_value_valuation (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) : v (lift P I 0) = 0 := by
  have hs : (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) ^ 2 = (P.sigma₁ P.epsilon : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one P.epsilon_gt_one))
  have hp : (P.sigma₁ P.epsilon : ℂ) ^ 2 -
      ((P.N : ℂ) + 2) * (P.sigma₁ P.epsilon : ℂ) + 1 = 0 := by
    exact_mod_cast M74.period_polynomial P
  have hquartic : lift P I 0 ^ 4 -
      ((P.N : Galois.Qbar) + 2) * lift P I 0 ^ 2 + 1 = 0 := by
    apply Galois.embed.injective
    change Galois.embed (_ - _ + 1) = Galois.embed 0
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
      map_zero, embed_lift, M72.value_zero, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs]
    exact hp
  exact OddPrimeValuesAux.valuation_zero_of_integral_unit v (lift_ne_zero P I 0)
    (OddPrimeValuesAux.quartic_isIntegral P.N _ hquartic)
    (OddPrimeValuesAux.quartic_inv_isIntegral P.N _ hquartic)

/-- [RW-rec, §5]: nonvanishing justifies the ordinary real coordinate; [RW26, §5.2, p. 22] discusses
the valuation; the general dictionary is ValuationSupport. -/
theorem coe_weight (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (x : PseudolatticeGroup P I) :
    (weight P I v x : WithTop ℝ) = v (lift P I x) := by
  exact ValuationSupport.coe_realValue v (lift_ne_zero P I x)

/-- [RW-rec]: reflection plus w(0)=0 gives oddness on all labels; [RW26, p. 3, (5)]. This is a
valuation identity, not the complex-conjugation theorem. -/
theorem weight_neg (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (x : PseudolatticeGroup P I) :
    weight P I v (-x) = -weight P I v x := by
  by_cases hx : x = 0
  · subst x
    simp [weight, ValuationSupport.realValue, zero_value_valuation P I v]
  let B := M72.chosenBasis P I
  let hM := M74.basis_admissible B (M72.chosenBasis_spec P I).1
  let e := OddPrimeValuesAux.matrixEquiv P I
  have hex : e x ≠ 0 := fun h => hx (e.map_eq_zero_iff.mp h)
  let q := FiniteAlgebraicTransport.gaussian B.matrix hM (e x)
  have hq : q ^ (2 * (L4.specialValueOrder B.matrix).toNat) = 1 := by
    apply Galois.embed.injective
    change Galois.embed (q ^ _) = Galois.embed 1
    rw [map_pow, map_one, FiniteAlgebraicTransport.embed_gaussian]
    exact M74.gaussian_order B.matrix hM (e x)
  have hn : 2 * (L4.specialValueOrder B.matrix).toNat ≠ 0 := by
    have := L4.specialValueOrder_pos B.matrix hM
    omega
  have hproduct : lift P I x * lift P I (-x) = q⁻¹ := by
    apply Galois.embed.injective
    change Galois.embed (_ * _) = Galois.embed (q⁻¹)
    rw [map_mul, map_inv₀, embed_lift, embed_lift,
      OddPrimeValuesAux.value_matrixEquiv, OddPrimeValuesAux.value_matrixEquiv,
      map_neg, FiniteAlgebraicTransport.embed_gaussian]
    rw [L4.specialValue_agree_off_zero B.matrix hM _ (neg_ne_zero.mpr hex)]
    exact L4.specialValue_mixed_reflection B.matrix hM (e x)
  have hvq := ValuationSupport.value_pow_eq_one v hn hq
  have hreal : weight P I v x + weight P I v (-x) = 0 := by
    change ValuationSupport.realValue v (lift P I x) +
      ValuationSupport.realValue v (lift P I (-x)) = 0
    rw [← ValuationSupport.realValue_mul v (lift_ne_zero P I x) (lift_ne_zero P I (-x)),
      hproduct]
    simp [ValuationSupport.realValue, v.map_inv, hvq]
  linarith

/-- [RW-rec, p. 7] gives the quotient valuation in ordinary real coordinates. [RW26, p. 18, (36)]
supplies the finite identities only; additivity is ValuationSupport. -/
theorem ratio_valuation (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (h t : PseudolatticeGroup P I) :
    v (lift P I (t + h) / lift P I t) =
      ((weight P I v (t + h) - weight P I v t : ℝ) : WithTop ℝ) := by
  rw [v.map_div, ← coe_weight P I v (t + h), ← coe_weight P I v t]
  rfl

/-- Same point in K/I, not the same integer row label. [RW-rec, p. 4, p. 9, (8)]; [RW26, Prop. 8, p.
14]. -/
theorem lift_pow (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) (x : PseudolatticeGroup P I) :
    lift (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr)
      (PeriodPower.periodPowerInclusion P I r hr x) = lift P I x ^ r := by
  apply Galois.embed.injective
  change Galois.embed (lift _ _ _) = Galois.embed (lift P I x ^ r)
  rw [embed_lift, map_pow, embed_lift]
  exact PeriodPower.value_pow P I r hr x

/-- [RW-rec, Def. 1(iii), p. 3, p. 7]; [RW26, p. 2, (2)] is the analytic input. Uses the existing
scaleEquiv. -/
theorem weight_scale (P : PeriodData K) (I J : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (a : K) (ha : TotallyPositive P a)
    (hJ : J.val = pseudolatticeScale a I.val) (x : PseudolatticeGroup P I) :
    weight P J v (M72.scaleEquiv P I J a (totallyPositive_ne_zero P a ha) hJ x) =
      weight P I v x := by
  have h : lift P J
      (M72.scaleEquiv P I J a (totallyPositive_ne_zero P a ha) hJ x) = lift P I x := by
    apply Galois.embed.injective
    change Galois.embed (lift _ _ _) = Galois.embed (lift P I x)
    rw [embed_lift, embed_lift]
    exact M72.value_scale P I J a ha hJ x
  simp only [weight, h]

/-- Explicit extension obligation for passing from an arbitrary finite prime to the Qbar proof
model. [RW-rec, p. 4] chooses v on Qbar; no extension is an input to the final unit theorem. -/
theorem exists_valuation_extension {L : Type*} [Field L] [NumberField L]
    (Q : FinitePlace.Prime L) (ι : L →ₐ[ℚ] Galois.Qbar) :
    ∃ v : AddValuation Galois.Qbar (WithTop ℝ),
      v (FinitePlace.residueChar Q : Galois.Qbar) = 1 ∧
      ∀ a : L, v (ι a) = FinitePlace.valuation Q a := by
  exact OddPrimeValuesAux.exists_valuation_extension Q ι

#check @L3.M72.value
#check @L4.modularPhi
#check @L4.phiExtended
#check @L4.etaMultiplier
#check @PeriodPower.value_pow
#check @ActualValues.lift_unique
#check @exists_valuation_extension
#print lift
#print weight
#print valuationFourier

end SICLean.L5.OddPrimeValues
