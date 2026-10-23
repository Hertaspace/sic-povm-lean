import SICLean.L4.SpecialValueUnitAction
import SICLean.L4.SpecialValueL2cAux
import SICLean.L2c.Inputs

set_option autoImplicit false

/-!
# Actual special values in the original L2c interface

The original base is α=((M-1,-1),(1,0)), its period
is α³, and all vectors are rows. The coordinate equivalence is the identity
on integer lifts; the existing Smith labels are not changed.

The two functions below are the specified actual special values transported
to L2c.RWGroup. Fourier (6) and ratio (7) are hypotheses of
`rwL2cAnalyticInput_of_sums` in this file. They are discharged by
`rwL2cAnalyticInput_of_G1` in `SICLean.L4.G2AnalyticInputs` from
`g1RealConclusion`.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L4

/--
[RW26, p. 20, §4.4].
The determinant-one packaging of the already fixed bottom matrix.
-/
def rwL2cBase (M : ℕ) : SL(2, ℤ) :=
  ⟨L2b.alpha M, alpha_det_one M⟩

/--
The literal third power from [RW26, p. 20]. No exponent is chosen.
-/
def rwL2cPeriod (M : ℕ) : SL(2, ℤ) := rwL2cBase M ^ 3

/--
[RW26, p. 20, §4.4]: the packaged period is exactly the matrix γ of `SICLean.L2c`.
-/
theorem rwL2cPeriod_coe (M : ℕ) :
    (rwL2cPeriod M : Matrix (Fin 2) (Fin 2) ℤ) = L2b.gamma M := by
  rw [rwL2cPeriod, Matrix.SpecialLinearGroup.coe_pow]
  rfl

/--
The base and period are both in the positive-c hyperbolic scope.
[RW26, p. 20, p. 2].
-/
theorem rwL2c_admissible (M : ℕ) [Fact (4 ≤ M)] :
    SpecialValueAdmissible (rwL2cBase M) ∧
      SpecialValueAdmissible (rwL2cPeriod M) := by
  have h4 : (4 : ℤ) ≤ (M : ℤ) := by exact_mod_cast Fact.out
  constructor
  · change 0 < (L2b.alpha M) 1 0 ∧
      2 < (L2b.alpha M) 0 0 + (L2b.alpha M) 1 1
    simp only [L2b.alpha, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> omega
  · change 0 < (L2b.gamma M) 1 0 ∧
      2 < (L2b.gamma M) 0 0 + (L2b.gamma M) 1 1
    constructor
    · rw [gamma_apply10]
      nlinarith
    · have ht := L2b.gamma_trace (M := M)
      simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] at ht
      rw [ht]
      have hgo : (0 : ℤ) < (L2b.groupOrder M : ℤ) := by
        have : 0 < L2b.groupOrder M := by
          simp only [L2b.groupOrder, L2b.cofactor]
          exact Nat.mul_pos (pow_pos (by omega) 2) (by omega)
        exact_mod_cast this
      linarith

/--
The period's fixed point is the base unit ε, but its automorphy
factor is ε³. [RW26, p. 20, p. 3, (4)].
-/
theorem rwL2c_parameters (M : ℕ) [Fact (4 ≤ M)] :
    specialValueOrder (rwL2cPeriod M) = (L2b.groupOrder M : ℤ) ∧
      specialValueTau (rwL2cPeriod M) = L2a.epsilon M ∧
      specialValueEpsilon (rwL2cPeriod M) = L2a.epsilon M ^ 3 := by
  have hAdm : SpecialValueAdmissible (rwL2cPeriod M) := (rwL2c_admissible M).2
  have hord : specialValueOrder (rwL2cPeriod M) = (L2b.groupOrder M : ℤ) := by
    rw [specialValueOrder]
    change (rwL2cPeriod M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      (rwL2cPeriod M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 2 = _
    rw [rwL2cPeriod_coe, gamma_apply00, gamma_apply11]
    have h3 : 3 ≤ M := by have := Fact.out (p := 4 ≤ M); omega
    simp only [L2b.groupOrder, L2b.cofactor, Nat.cast_mul, Nat.cast_pow]
    rw [Nat.cast_sub h3]
    ring
  have hcast : (specialValueOrder (rwL2cPeriod M) : ℝ) = (L2b.groupOrder M : ℝ) := by
    rw [hord]; push_cast; ring
  have hEps : specialValueEpsilon (rwL2cPeriod M) = L2a.epsilon M ^ 3 := by
    rw [specialValueEpsilon_formula (rwL2cPeriod M) hAdm, hcast, ← epsilon_cube_eq M]
  have hentry10 : ((rwL2cPeriod M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) =
      (M : ℝ) * ((M : ℝ) - 2) := by
    rw [rwL2cPeriod_coe, gamma_apply10]; push_cast; ring
  have hentry11 : ((rwL2cPeriod M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) =
      -((M : ℝ) - 1) := by
    rw [rwL2cPeriod_coe, gamma_apply11]; push_cast; ring
  refine ⟨hord, ?_, hEps⟩
  have hdef : specialValueEpsilon (rwL2cPeriod M) =
      ((rwL2cPeriod M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) *
        specialValueTau (rwL2cPeriod M) +
        ((rwL2cPeriod M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) := rfl
  have hprod : ((M : ℝ) * ((M : ℝ) - 2)) * specialValueTau (rwL2cPeriod M) +
      (-((M : ℝ) - 1)) = L2a.epsilon M ^ 3 := by
    rw [← hEps, hdef, hentry10, hentry11]
  have hrel := epsilon_cube_relation M
  have hg10 : ((M : ℝ) * ((M : ℝ) - 2)) ≠ 0 := by
    have h4 : (4 : ℝ) ≤ M := by exact_mod_cast Fact.out
    have hM : (0 : ℝ) < M := by linarith
    have hM2 : (0 : ℝ) < M - 2 := by linarith
    exact ne_of_gt (mul_pos hM hM2)
  have heq : ((M : ℝ) * ((M : ℝ) - 2)) * specialValueTau (rwL2cPeriod M) =
      ((M : ℝ) * ((M : ℝ) - 2)) * L2a.epsilon M := by
    linarith
  exact mul_left_cancel₀ hg10 heq

/--
The congruence kernel of `SICLean.L2c` is exactly the row range used here.
[RW26, p. 3, (3)] group argument. This is the already proved L2c lattice comparison.
-/
theorem rwL2c_lattice_eq (M : ℕ) [Fact (4 ≤ M)] :
    specialValueLattice (rwL2cPeriod M) = L2c.lattice M := by
  rw [specialValueLattice, rwL2cPeriod_coe, L2c.lattice_eq_row_range]
  have hfun : L2c.rowLatticeMap M = L2r.rowActionHom (L2b.gamma M - 1) := by
    ext a <;>
      simp [L2c.rowLatticeMap, L2c.rowGamma, L2r.rowActionHom, L2r.rowAction,
        Matrix.sub_apply] <;> ring
  change (L2r.rowActionHom (L2b.gamma M - 1)).range = (L2c.rowLatticeMap M).range
  rw [hfun]

/--
Identity-on-lifts transport between the two proved-equal lattices.
[RW26, p. 3, (3)].
-/
def rwL2cEquiv (M : ℕ) [Fact (4 ≤ M)] :
    L2c.RWGroup M ≃+ SpecialValueGroup (rwL2cPeriod M) :=
  QuotientAddGroup.quotientAddEquivOfEq (rwL2c_lattice_eq M).symm

/--
The coordinate map does not select or alter representatives.
[RW26, p. 3, (3)].
-/
theorem rwL2cEquiv_mk (M : ℕ) [Fact (4 ≤ M)] (u : ℤ × ℤ) :
    rwL2cEquiv M (L2c.mk M u) = specialValueMk (rwL2cPeriod M) u := by
  rw [rwL2cEquiv]
  exact QuotientAddGroup.quotientAddEquivOfEq_mk (rwL2c_lattice_eq M).symm u

/-- Row multiplication by the packaged period is the integer row action of `SICLean.L2c`. -/
private theorem rwL2c_rowAction_period (M : ℕ) (a : ℤ × ℤ) :
    L2r.rowAction (rwL2cPeriod M : Matrix (Fin 2) (Fin 2) ℤ) a = L2c.rowGamma M a := by
  rw [rwL2cPeriod_coe]
  rfl

/-- Nonvanishing of the group order, available from the dimension bound. -/
private theorem rwL2c_groupOrder_ne_zero (M : ℕ) [Fact (4 ≤ M)] :
    L2b.groupOrder M ≠ 0 := by
  have h4 : 4 ≤ M := Fact.out
  simp only [L2b.groupOrder, L2b.cofactor]
  exact Nat.mul_ne_zero (by positivity) (by omega)

/--
[RW26, pp. 2--3, (2), (4)].
This is a specified actual function, not a special-value hypothesis.
-/
def rwL2cPlus (M : ℕ) [Fact (4 ≤ M)] : L2c.RWGroup M → ℂ :=
  specialValuePlus (rwL2cPeriod M) (rwL2c_admissible M).2 ∘ rwL2cEquiv M

/--
The same actual construction with the prescribed minus origin.
[RW26, pp. 2--3].
-/
def rwL2cMinus (M : ℕ) [Fact (4 ≤ M)] : L2c.RWGroup M → ℂ :=
  specialValueMinus (rwL2cPeriod M) (rwL2c_admissible M).2 ∘ rwL2cEquiv M

/--
Exact Gaussian compatibility, including its integer parity power
and the denominator 2N. [RW26, p. 3, p. 20, §4.4, (3)].
-/
theorem rwL2c_gaussian (M : ℕ) [Fact (4 ≤ M)] (u : L2c.RWGroup M) :
    specialValueGaussian (rwL2cPeriod M) (rwL2c_admissible M).2 (rwL2cEquiv M u) =
      L2c.gaussian M u := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  change specialValueGaussian (rwL2cPeriod M) (rwL2c_admissible M).2
      (rwL2cEquiv M (L2c.mk M a)) = L2c.gaussian M (L2c.mk M a)
  rw [rwL2cEquiv_mk, specialValueGaussian_mk, L2c.gaussian_mk]
  unfold specialValueGaussianLift L2c.gaussianLift
  rw [rwL2c_rowAction_period, (rwL2c_parameters M).1]
  have hΩ : specialValueOmega (L2c.rowGamma M a) a = L2c.omega (L2c.rowGamma M a) a := rfl
  rw [hΩ]
  unfold e L2a.e
  congr 1
  have hN : L2b.groupOrder M ≠ 0 := rwL2c_groupOrder_ne_zero M
  have hNc : ((L2b.groupOrder M : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp

/--
Positive-sign pairing compatibility. [RW26, p. 3, p. 20, §4.4, (3)].
-/
theorem rwL2c_pairing (M : ℕ) [Fact (4 ≤ M)] (u v : L2c.RWGroup M) :
    specialValuePairing (rwL2cPeriod M) (rwL2c_admissible M).2
        (rwL2cEquiv M u) (rwL2cEquiv M v) = L2c.pairing M u v := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  refine QuotientAddGroup.induction_on v ?_
  intro b
  change specialValuePairing (rwL2cPeriod M) (rwL2c_admissible M).2
      (rwL2cEquiv M (L2c.mk M a)) (rwL2cEquiv M (L2c.mk M b)) =
    L2c.pairing M (L2c.mk M a) (L2c.mk M b)
  rw [rwL2cEquiv_mk, rwL2cEquiv_mk, specialValuePairing_mk, L2c.pairing_mk]
  unfold specialValuePairingLift L2c.pairingLift
  rw [rwL2c_rowAction_period, (rwL2c_parameters M).1]
  have hΩ : specialValueOmega (L2c.rowGamma M a - a) b =
      L2c.omega (L2c.rowGamma M a - a) b := rfl
  rw [hΩ]
  unfold e L2a.e
  congr 1
  have hN : L2b.groupOrder M ≠ 0 := rwL2c_groupOrder_ne_zero M
  have hNc : ((L2b.groupOrder M : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp

/--
Both concrete branches have the intended formula on every integer
lift, including the separately prescribed lattice branch.
[RW26, p. 2, p. 12, (2), Lemma 2].
-/
theorem rwL2cValues_mk (M : ℕ) [Fact (4 ≤ M)] (u : ℤ × ℤ) :
    rwL2cPlus M (L2c.mk M u) = specialValuePlusLift (rwL2cPeriod M) u ∧
      rwL2cMinus M (L2c.mk M u) = specialValueMinusLift (rwL2cPeriod M) u := by
  constructor
  · rw [rwL2cPlus]
    change specialValuePlus (rwL2cPeriod M) (rwL2c_admissible M).2
      (rwL2cEquiv M (L2c.mk M u)) = _
    rw [rwL2cEquiv_mk, specialValuePlus_mk]
  · rw [rwL2cMinus]
    change specialValueMinus (rwL2cPeriod M) (rwL2c_admissible M).2
      (rwL2cEquiv M (L2c.mk M u)) = _
    rw [rwL2cEquiv_mk, specialValueMinus_mk]

/--
Literal plus branch of Theorem 2 (4). [RW26, p. 3].
-/
theorem rwL2cPlus_zero (M : ℕ) [Fact (4 ≤ M)] :
    rwL2cPlus M 0 = L2c.originPlus M := by
  rw [rwL2cPlus]
  change specialValuePlus (rwL2cPeriod M) (rwL2c_admissible M).2 (rwL2cEquiv M 0) = _
  rw [map_zero, specialValuePlus_zero, (rwL2c_parameters M).2.2]
  unfold L2c.originPlus
  rw [epsilon_cube_eq M]

/--
Literal minus branch of Theorem 2 (4); the outer root is positive.
[RW26, p. 3].
-/
theorem rwL2cMinus_zero (M : ℕ) [Fact (4 ≤ M)] :
    rwL2cMinus M 0 = L2c.originMinus M := by
  rw [rwL2cMinus]
  change specialValueMinus (rwL2cPeriod M) (rwL2c_admissible M).2 (rwL2cEquiv M 0) = _
  rw [map_zero, specialValueMinus_zero, (rwL2c_parameters M).2.2]
  unfold L2c.originMinus
  rw [← Complex.ofReal_inv, ← Real.sqrt_inv, epsilon_cube_inv_eq M]

/--
Both branches are nonzero on all classes. [RW26, p. 6, p. 12, Lemma 2].
-/
theorem rwL2c_values_ne_zero (M : ℕ) [Fact (4 ≤ M)] (u : L2c.RWGroup M) :
    rwL2cPlus M u ≠ 0 ∧ rwL2cMinus M u ≠ 0 := by
  constructor
  · rw [rwL2cPlus]
    exact specialValuePlus_ne_zero (rwL2cPeriod M) _ (rwL2cEquiv M u)
  · rw [rwL2cMinus]
    exact specialValueMinus_ne_zero (rwL2cPeriod M) _ (rwL2cEquiv M u)

/--
Literal footnote 2, [RW26, p. 3]. No equality of the two origins is asserted.
-/
theorem rwL2c_agree_off_zero (M : ℕ) [Fact (4 ≤ M)]
    (u : L2c.RWGroup M) (hu : u ≠ 0) :
    rwL2cPlus M u = rwL2cMinus M u := by
  rw [rwL2cPlus, rwL2cMinus]
  change specialValuePlus (rwL2cPeriod M) (rwL2c_admissible M).2 (rwL2cEquiv M u) =
    specialValueMinus (rwL2cPeriod M) (rwL2c_admissible M).2 (rwL2cEquiv M u)
  apply specialValue_agree_off_zero
  intro h0
  apply hu
  exact (rwL2cEquiv M).injective (by rw [map_zero]; exact h0)

/--
Literal (5), including zero, in the exact existing Gaussian.
[RW26, p. 3, p. 12].
-/
theorem rwL2c_mixed_reflection (M : ℕ) [Fact (4 ≤ M)] (u : L2c.RWGroup M) :
    rwL2cPlus M u * rwL2cMinus M (-u) = (L2c.gaussian M u)⁻¹ := by
  rw [rwL2cPlus, rwL2cMinus]
  change specialValuePlus (rwL2cPeriod M) (rwL2c_admissible M).2 (rwL2cEquiv M u) *
      specialValueMinus (rwL2cPeriod M) (rwL2c_admissible M).2 (rwL2cEquiv M (-u)) =
    (L2c.gaussian M u)⁻¹
  rw [map_neg, specialValue_mixed_reflection, rwL2c_gaussian]

/--
Prop. 8's base α action, with the exact direction of the L2c field.
[RW26, p. 14, p. 20, (38)].
-/
theorem rwL2c_epsilon_invariant (M : ℕ) [Fact (4 ≤ M)] (u : L2c.RWGroup M) :
    rwL2cPlus M u = rwL2cPlus M (L2c.epsilonAction M u) := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  have hrow : L2r.rowAction (rwL2cBase M : Matrix (Fin 2) (Fin 2) ℤ) a =
      L2c.rowAlpha M a := by
    ext <;> simp [L2r.rowAction, L2c.rowAlpha, L2b.alpha, rwL2cBase] <;> ring
  change rwL2cPlus M (L2c.mk M a) = rwL2cPlus M (L2c.epsilonAction M (L2c.mk M a))
  rw [L2c.epsilonAction_mk,
    show rwL2cPlus M (L2c.mk M a) = specialValuePlusLift (rwL2cPeriod M) a from
      (rwL2cValues_mk M a).1,
    show rwL2cPlus M (L2c.mk M (L2c.rowAlpha M a)) =
      specialValuePlusLift (rwL2cPeriod M) (L2c.rowAlpha M a) from
      (rwL2cValues_mk M (L2c.rowAlpha M a)).1]
  rw [← specialValuePlus_mk (rwL2cPeriod M) (rwL2c_admissible M).2 a,
    ← specialValuePlus_mk (rwL2cPeriod M) (rwL2c_admissible M).2 (L2c.rowAlpha M a),
    ← hrow]
  have hinv := specialValuePlus_base_invariant (rwL2cBase M) (rwL2c_admissible M).1 3
    (by norm_num) (specialValueMk (rwL2cBase M ^ 3) a)
  rw [specialValueUnitAction_mk] at hinv
  exact hinv

theorem rwL2cAnalyticInput_of_sums (M : ℕ) [Fact (4 ≤ M)]
    (hfourier : ∃ μ : ℂ, μ ≠ 0 ∧ ∀ u : L2c.RWGroup M,
      L2c.normalizedSum M (fun x => L2c.pairing M x u * rwL2cPlus M x) =
        μ / rwL2cMinus M u)
    (hratio : ∀ u v : L2c.RWGroup M, (u, v) ≠ (0, 0) →
      L2c.normalizedSum M
        (fun x => L2c.pairing M x u * (rwL2cPlus M x / rwL2cMinus M (x + v))) =
          rwL2cPlus M (u + v) / (rwL2cMinus M u * rwL2cMinus M v)) :
    L2c.RWAnalyticInput M (rwL2cPlus M) (rwL2cMinus M) := by
  refine ⟨?_, ?_⟩
  · refine ⟨rwL2cPlus_zero M, rwL2cMinus_zero M, ?_, hfourier, hratio, ?_⟩
    · intro u
      exact rwL2c_mixed_reflection M u
    · intro u hu
      exact rwL2c_agree_off_zero M u hu
  · intro u
    exact rwL2c_epsilon_invariant M u

#print rwL2cBase
#print rwL2cPeriod
#print rwL2cEquiv
#print rwL2cPlus
#print rwL2cMinus
#check rwL2cValues_mk
#check rwL2c_mixed_reflection
#check rwL2c_epsilon_invariant
#check rwL2cAnalyticInput_of_sums

end SICLean.L4
