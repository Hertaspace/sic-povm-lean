import SICLean.L4.SpecialValueReflection
import SICLean.L4.SpecialValueUnitActionAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Positive base action: the second identity of [RW26, Prop. 8]

[RW26, p. 6, p. 14, (18), Prop. 8].

The base A acts on the quotient for A^k. This is not the already trivial
action of A^k itself. The existing cyclic cocycle is reused for k≥2;
k=1 follows from descent in the row quotient. All k>0 include the zero
class by its definition. No assertion concerns k=0 or negative powers.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4

/-- The actual base-row action on G_(A^k), with a well-definedness proof
only. This map itself is defined even at k=0; F is used only for k>0. -/
def specialValueUnitAction (A : SL(2, ℤ)) (k : ℕ) :
    SpecialValueGroup (A ^ k) →+ SpecialValueGroup (A ^ k) :=
  QuotientAddGroup.lift (specialValueLattice (A ^ k))
    ((specialValueMk (A ^ k)).comp (L2r.rowActionHom (A : Matrix (Fin 2) (Fin 2) ℤ)))
    (by
      intro u hu
      change (QuotientAddGroup.mk
        (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u) : SpecialValueGroup (A ^ k)) = 0
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        ((SpecialValueUnitActionAux.base_mem_lattice_iff A k u).mpr hu))

/--
Positive powers remain in the actual constructed positive-c scope.
[RW26, p. 6, p. 14, (18), Prop. 8].
-/
theorem specialValue_pow_admissible (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (k : ℕ) (hk : 0 < k) : SpecialValueAdmissible (A ^ k) := by
  exact SpecialValueUnitActionAux.pow_admissible A hA k hk

/--
Canonical attracting points agree, so no choice-of-root hypothesis
is left for downstream callers. [RW26, p. 14, Prop. 8].
-/
theorem specialValueTau_pow (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (k : ℕ) (hk : 0 < k) : specialValueTau (A ^ k) = specialValueTau A := by
  exact SpecialValueUnitActionAux.tau_pow A hA k hk

/--
The actual automorphy factors have the corresponding powers.
[RW26, p. 6, p. 14, (18), Prop. 8].
-/
theorem specialValueEpsilon_pow (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (k : ℕ) (hk : 0 < k) : specialValueEpsilon (A ^ k) = specialValueEpsilon A ^ k := by
  exact SpecialValueUnitActionAux.epsilon_pow A hA k hk

/--
An equivalence, needed to keep both zero and nonzero classes under
the base action. [RW26, p. 14, Prop. 8] row quotient.
-/
theorem specialValue_base_mem_lattice_iff (A : SL(2, ℤ)) (k : ℕ) (u : ℤ × ℤ) :
    L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u ∈ specialValueLattice (A ^ k) ↔
      u ∈ specialValueLattice (A ^ k) := by
  exact SpecialValueUnitActionAux.base_mem_lattice_iff A k u

/--
The exact scaled special argument underlying cyclic permutation.
[RW26, p. 14, (2), Prop. 8] substitution [RW26, p. 2].
-/
theorem specialValueArgument_base (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (k : ℕ) (hk : 0 < k) (u : ℤ × ℤ) :
    specialValueArgument (A ^ k) (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u) =
      (specialValueEpsilon A : ℂ) * specialValueArgument (A ^ k) u := by
  have hT : 1 < (etaDenom A (specialValueTau A : ℂ)).re := by
    simpa only [specialValue_etaDenom, Complex.ofReal_re] using specialValueEpsilon_gt_one A hA
  have h := modularPhiSpecialArgument_unit A hA.1 hA.2 k hk ![u.1, u.2]
    (specialValueTau A) (specialValueTau_fixedPoint A hA) hT
  rw [SpecialValueUnitActionAux.row_vecMul (A : Matrix (Fin 2) (Fin 2) ℤ) u] at h
  simpa only [specialValueArgument, specialValueTau_pow A hA k hk, specialValue_etaDenom]
    using h

/--
All actual centers required by two explicit chains are regular.
[RW26, p. 14, p. 6, Prop. 8] divisors. This removes, rather than
postulates, the hFactors/hCycled continuity inputs of modularPhi_unit_action.
Off the Γ lattice, division by base units preserves the pseudo-lattice
complement. In particular no intermediate factor algebraicity is assumed.
-/
theorem specialValue_unit_factors_regular (A : SL(2, ℤ))
    (hA : SpecialValueAdmissible A) (k : ℕ) (hk : 2 ≤ k)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice (A ^ k)) :
    let τ : ℂ := (specialValueTau A : ℂ)
    let z := specialValueArgument (A ^ k) u
    let v := L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u
    ∀ j ∈ Finset.range k,
      ContinuousAt (fun w => modularPhi A (if j = 0 then u.1 else 0) 0 w τ)
        (z / etaDenom A τ ^ j) ∧
      ContinuousAt (fun w => modularPhi A
        (if j = 0 then v.1 else if j = 1 then u.1 else 0)
        (if j = 0 then u.1 else 0) w τ)
        (specialValueArgument (A ^ k) v / etaDenom A τ ^ j) := by
  dsimp only
  have hk0 : 0 < k := by omega
  have hAk := specialValue_pow_admissible A hA k hk0
  have hτ := specialValueTau_pow A hA k hk0
  have hv : L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u ∉
      specialValueLattice (A ^ k) := by
    simpa only [specialValue_base_mem_lattice_iff] using hu
  have hz : specialValueArgument (A ^ k) u ∉
      modularPhiPseudoLattice (specialValueTau A : ℂ) := by
    rw [← hτ]
    exact (specialValueArgument_mem_lattice_iff (A ^ k) hAk u).not.mpr hu
  have hw : specialValueArgument (A ^ k)
      (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u) ∉
      modularPhiPseudoLattice (specialValueTau A : ℂ) := by
    rw [← hτ]
    exact (specialValueArgument_mem_lattice_iff (A ^ k) hAk _).not.mpr hv
  have hT : etaDenom A (specialValueTau A : ℂ) ≠ 0 := by
    rw [specialValue_etaDenom]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one
      (specialValueEpsilon_gt_one A hA)))
  intro j _hj
  constructor
  · exact SpecialValueUnitActionAux.continuousAt_off_pseudoLattice A hA _ _ _
      (SpecialValueUnitActionAux.div_pow_not_mem_pseudoLattice A _
        (specialValueTau_fixedPoint A hA) hT _ hz j)
  · exact SpecialValueUnitActionAux.continuousAt_off_pseudoLattice A hA _ _ _
      (SpecialValueUnitActionAux.div_pow_not_mem_pseudoLattice A _
        (specialValueTau_fixedPoint A hA) hT _ hw j)

/--
Actual raw-value invariance for nonzero Γ classes. The Γ centers
come from the descent; the two chains are covered above. [RW26, p. 14, Prop. 8].
Zero uses the separate F branch, not this theorem.
-/
theorem specialValueRaw_base_invariant (A : SL(2, ℤ))
    (hA : SpecialValueAdmissible A) (k : ℕ) (hk : 2 ≤ k)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice (A ^ k)) :
    specialValueRaw (A ^ k) (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u) =
      specialValueRaw (A ^ k) u := by
  have hk0 : 0 < k := by omega
  have hAk := specialValue_pow_admissible A hA k hk0
  have hτ := specialValueTau_pow A hA k hk0
  let v := L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u
  have hv : v ∉ specialValueLattice (A ^ k) := by
    exact (specialValue_base_mem_lattice_iff A k u).not.mpr hu
  have hrow := SpecialValueUnitActionAux.row_vecMul (A : Matrix (Fin 2) (Fin 2) ℤ) u
  have hT : 1 < (etaDenom A (specialValueTau A : ℂ)).re := by
    simpa only [specialValue_etaDenom, Complex.ofReal_re] using specialValueEpsilon_gt_one A hA
  have hcont (w : ℤ × ℤ) (hw : w ∉ specialValueLattice (A ^ k)) :
      ContinuousAt (fun z => modularPhi (A ^ k) w.1 0 z (specialValueTau (A ^ k) : ℂ))
        (specialValueArgument (A ^ k) w) := by
    have h := (specialValuePhi_joint_regular (A ^ k) hAk w hw 0).1.continuousAt
    simp only [add_zero] at h
    exact h.comp
      (f := fun z : ℂ => (z, (specialValueTau (A ^ k) : ℂ)))
      (continuousAt_id.prodMk continuousAt_const)
  have hΓ : ∀ w ∈ ({![u.1, u.2],
      Matrix.vecMul ![u.1, u.2] (A : Matrix (Fin 2) (Fin 2) ℤ)} : Set (Fin 2 → ℤ)),
      ContinuousAt (fun z => modularPhi (A ^ k) (w 0) 0 z (specialValueTau A : ℂ))
        (modularPhiSpecialArgument (A ^ k) w (specialValueTau A : ℂ)) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · simpa only [specialValueArgument, hτ, Matrix.cons_val_zero] using hcont u hu
    · rw [hrow]
      simpa only [specialValueArgument, hτ, Matrix.cons_val_zero] using hcont v hv
  have hreg := specialValue_unit_factors_regular A hA k hk u hu
  have heq := modularPhi_unit_action A hA.1 hA.2 k hk ![u.1, u.2]
    (specialValueTau A) (specialValueTau_fixedPoint A hA) hT hΓ
    (by
      intro j hj
      simpa only [specialValueArgument, hτ, Matrix.cons_val_zero] using (hreg j hj).1)
    (by
      intro j hj
      simpa only [hrow, Matrix.cons_val_zero, specialValueArgument, hτ] using (hreg j hj).2)
  rw [hrow] at heq
  simpa only [specialValueRaw, specialValueArgument, hτ, Matrix.cons_val_zero] using
    congrArg (fun z : ℂ => etaMultiplier (A ^ k) * z) heq

/--
Identity on integer lifts of the actual base action. [RW26, p. 14, Prop. 8] row convention.
-/
theorem specialValueUnitAction_mk (A : SL(2, ℤ)) (k : ℕ) (u : ℤ × ℤ) :
    specialValueUnitAction A k (specialValueMk (A ^ k) u) =
      specialValueMk (A ^ k) (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u) := by
  rfl

/--
Exactly Prop. 8's second identity for every positive exponent and
every class, oriented as the L2 epsilon_invariant field. [RW26, p. 14]. The k=1 quotient argument
and the zero-class constants are
included, without any Fourier or five-term hypothesis.
-/
theorem specialValuePlus_base_invariant (A : SL(2, ℤ))
    (hA : SpecialValueAdmissible A) (k : ℕ) (hk : 0 < k)
    (u : SpecialValueGroup (A ^ k)) :
    specialValuePlus (A ^ k) (specialValue_pow_admissible A hA k hk) u =
      specialValuePlus (A ^ k) (specialValue_pow_admissible A hA k hk)
        (specialValueUnitAction A k u) := by
  refine QuotientAddGroup.induction_on u ?_
  intro v
  change specialValuePlus (A ^ k) _ (specialValueMk (A ^ k) v) =
    specialValuePlus (A ^ k) _ (specialValueUnitAction A k (specialValueMk (A ^ k) v))
  rw [specialValueUnitAction_mk, specialValuePlus_mk, specialValuePlus_mk]
  by_cases hk1 : k = 1
  · subst k
    have hsum : v + (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) v - v) =
        L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) v := by abel
    simpa only [pow_one, hsum] using
      (specialValuePlusLift_periodic A hA v
        (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) v - v)
        (SpecialValueUnitActionAux.row_sub_self_mem A v)).symm
  · unfold specialValuePlusLift
    rw [specialValue_base_mem_lattice_iff]
    split_ifs with hv
    · rfl
    · exact (specialValueRaw_base_invariant A hA k (by omega) v hv).symm

/--
The minus branch of the same identity, with the zero class retained.
[RW26, p. 14, Prop. 8, p. 3, footnote 2].
-/
theorem specialValueMinus_base_invariant (A : SL(2, ℤ))
    (hA : SpecialValueAdmissible A) (k : ℕ) (hk : 0 < k)
    (u : SpecialValueGroup (A ^ k)) :
    specialValueMinus (A ^ k) (specialValue_pow_admissible A hA k hk) u =
      specialValueMinus (A ^ k) (specialValue_pow_admissible A hA k hk)
        (specialValueUnitAction A k u) := by
  refine QuotientAddGroup.induction_on u ?_
  intro v
  change specialValueMinus (A ^ k) _ (specialValueMk (A ^ k) v) =
    specialValueMinus (A ^ k) _ (specialValueUnitAction A k (specialValueMk (A ^ k) v))
  rw [specialValueUnitAction_mk, specialValueMinus_mk, specialValueMinus_mk]
  by_cases hk1 : k = 1
  · subst k
    have hsum : v + (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) v - v) =
        L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) v := by abel
    simpa only [pow_one, hsum] using
      (specialValueMinusLift_periodic A hA v
        (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) v - v)
        (SpecialValueUnitActionAux.row_sub_self_mem A v)).symm
  · unfold specialValueMinusLift
    rw [specialValue_base_mem_lattice_iff]
    split_ifs with hv
    · rfl
    · exact (specialValueRaw_base_invariant A hA k (by omega) v hv).symm

#check @modularPhi_unit_action
#check @modularPhi_unit_product_cycle
#print specialValueUnitAction
#check specialValue_unit_factors_regular
#check specialValuePlus_base_invariant

end SICLean.L4
