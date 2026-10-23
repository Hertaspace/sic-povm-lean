import SICLean.L5.PeriodPowerData
import SICLean.L5.PeriodPowerMatrixAux

set_option autoImplicit false

/-!
# Power periods in the existing integer-row special-value interface

[RW-rec, Prop. 2(8)--(9)], p. 4, and Appendix A pp. 19--20. [RW26, Prop. 8, p. 2, p. 6,
p. 14, (2), (17)--(18)]. The row label changes by u -> u sum_(j<r) A^(-j). Holding u
fixed under A -> A^r would describe a different point in K/I. Both plus and minus use
the already prescribed origin and the existing modularPhi.
-/

noncomputable section
open scoped MatrixGroups BigOperators Classical

namespace SICLean.L5.PeriodPowerMatrix

def powerRowMatrix (A : SL(2, ℤ)) (r : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  ∑ j ∈ Finset.range r, ((A⁻¹ ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)

def powerRow (A : SL(2, ℤ)) (r : ℕ) (u : ℤ × ℤ) : ℤ × ℤ :=
  L2r.rowAction (powerRowMatrix A r) u

/-- [RW-rec, p. 3, p. 4]. The inverse sign is forced by the epsilon^-1-1 convention. -/
theorem powerRowMatrix_difference (A : SL(2, ℤ)) (r : ℕ) :
    powerRowMatrix A r *
        (((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) =
      (((A ^ r)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1 := by
  exact PeriodPowerMatrixAux.sum_matrix_difference A r

/-- Same label source; [RW26, Prop. 8, p. 14]. This also proves that zero classes are preserved and
reflected. -/
theorem powerRow_mem_lattice_iff (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) (u : ℤ × ℤ) :
    powerRow A r u ∈ L4.specialValueLattice (A ^ r) ↔ u ∈ L4.specialValueLattice A := by
  have harg : L4.specialValueArgument (A ^ r) (powerRow A r u) =
      L4.specialValueArgument A u := PeriodPowerMatrixAux.argument_sum A hA r hr u
  rw [← L4.specialValueArgument_mem_lattice_iff (A ^ r)
    (L4.specialValue_pow_admissible A hA r hr),
    harg,
    L4.specialValueTau_pow A hA r hr,
    L4.specialValueArgument_mem_lattice_iff A hA]

def inclusion (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) : L4.SpecialValueGroup A →+ L4.SpecialValueGroup (A ^ r) :=
  QuotientAddGroup.lift (L4.specialValueLattice A)
    ((L4.specialValueMk (A ^ r)).comp (L2r.rowActionHom (powerRowMatrix A r))) (by
      intro u hu
      change L4.specialValueMk (A ^ r) (powerRow A r u) = 0
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        ((powerRow_mem_lattice_iff A hA r hr u).mpr hu))

/-- [RW-rec, p. 4]; [RW26, Prop. 8, p. 14] matrix representative. -/
theorem inclusion_mk (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) (u : ℤ × ℤ) :
    inclusion A hA r hr (L4.specialValueMk A u) =
      L4.specialValueMk (A ^ r) (powerRow A r u) := by
  rfl

/-- Same sources: actual group embedding for the same point, not a cardinality-only identification
of two abstract finite groups. -/
theorem inclusion_injective (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) : Function.Injective (inclusion A hA r hr) := by
  apply (injective_iff_map_eq_zero (inclusion A hA r hr)).mpr
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro u hu
  change inclusion A hA r hr (L4.specialValueMk A u) = 0 at hu
  rw [inclusion_mk] at hu
  exact (QuotientAddGroup.eq_zero_iff u).mpr
    ((powerRow_mem_lattice_iff A hA r hr u).mp
      ((QuotientAddGroup.eq_zero_iff _).mp hu))

/-- [RW26, Prop. 8, p. 2, p. 14, (2)]; [RW-rec, p. 4, (8)]. -/
theorem specialValueArgument_powerRow (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) (u : ℤ × ℤ) :
    L4.specialValueArgument (A ^ r) (powerRow A r u) = L4.specialValueArgument A u := by
  exact PeriodPowerMatrixAux.argument_sum A hA r hr u

/-- [RW-rec, Appendix A, pp. 19--20]; [RW26, p. 3] multiplier convention, and p. 6 cocycle (17).
Positivity fixes the sqrt sign. -/
theorem etaMultiplier_pow (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) : L4.etaMultiplier (A ^ r) = L4.etaMultiplier A ^ r := by
  exact PeriodPowerMatrixAux.etaMultiplier_pow A hA r hr

/-- [RW-rec, Def. 1, p. 3, p. 4, (8)]; [RW26, p. 3, (4), footnote 2]. The root is positive real. -/
theorem sqrt_specialValueEpsilon_pow (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) :
    Real.sqrt (L4.specialValueEpsilon (A ^ r)) = Real.sqrt (L4.specialValueEpsilon A) ^ r := by
  rw [L4.specialValueEpsilon_pow A hA r hr]
  clear hr
  have hε : 0 ≤ L4.specialValueEpsilon A :=
    le_of_lt (lt_trans zero_lt_one (L4.specialValueEpsilon_gt_one A hA))
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg hε r), ih, pow_succ]

/-- [RW-rec, p. 4, (8)]; [RW26, Prop. 8, p. 6, p. 14, (18)]. This raw mu*Phi assertion excludes the
zero class. -/
theorem specialValueRaw_powerRow (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) (u : ℤ × ℤ) (hu : u ∉ L4.specialValueLattice A) :
    L4.specialValueRaw (A ^ r) (powerRow A r u) = L4.specialValueRaw A u ^ r := by
  have hphi := PeriodPowerMatrixAux.phi_power_of_chain A hA r hr u hu
    (fun j => powerRow A j u)
    (PeriodPowerMatrixAux.sumRow_zero A u)
    (fun j => PeriodPowerMatrixAux.sumRow_first_index A j u)
    (fun j => PeriodPowerMatrixAux.sumRow_translation A hA j u)
    (specialValueArgument_powerRow A hA r hr u)
  unfold L4.specialValueRaw
  rw [hphi, etaMultiplier_pow A hA r hr, mul_pow]

/-- [RW-rec, p. 4, (8)]; [RW26, Prop. 8, p. 14]. Callable with the existing specialValuePlus on all
old-period classes. -/
theorem specialValuePlus_pow (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) (x : L4.SpecialValueGroup A) :
    L4.specialValuePlus (A ^ r) (L4.specialValue_pow_admissible A hA r hr)
      (inclusion A hA r hr x) = L4.specialValuePlus A hA x ^ r := by
  refine QuotientAddGroup.induction_on x ?_
  intro u
  change L4.specialValuePlus (A ^ r) _ (inclusion A hA r hr (L4.specialValueMk A u)) =
    L4.specialValuePlus A hA (L4.specialValueMk A u) ^ r
  rw [inclusion_mk, L4.specialValuePlus_mk, L4.specialValuePlus_mk]
  unfold L4.specialValuePlusLift
  rw [powerRow_mem_lattice_iff A hA r hr]
  split_ifs with hu
  · rw [sqrt_specialValueEpsilon_pow A hA r hr, Complex.ofReal_pow]
  · exact specialValueRaw_powerRow A hA r hr u hu

/-- Same sources and [RW26, p. 3, footnote 2]: the minus origin is the inverse of the same positive
real root. -/
theorem specialValueMinus_pow (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) (x : L4.SpecialValueGroup A) :
    L4.specialValueMinus (A ^ r) (L4.specialValue_pow_admissible A hA r hr)
      (inclusion A hA r hr x) = L4.specialValueMinus A hA x ^ r := by
  refine QuotientAddGroup.induction_on x ?_
  intro u
  change L4.specialValueMinus (A ^ r) _ (inclusion A hA r hr (L4.specialValueMk A u)) =
    L4.specialValueMinus A hA (L4.specialValueMk A u) ^ r
  rw [inclusion_mk, L4.specialValueMinus_mk, L4.specialValueMinus_mk]
  unfold L4.specialValueMinusLift
  rw [powerRow_mem_lattice_iff A hA r hr]
  split_ifs with hu
  · rw [sqrt_specialValueEpsilon_pow A hA r hr, Complex.ofReal_pow, inv_pow]
  · exact specialValueRaw_powerRow A hA r hr u hu

/-- [RW-rec, Def. 1, p. 4, p. 3, (8)]; [RW26, p. 3, (4)]. Separate zero calibration; no raw Phi
cancellation here. -/
theorem specialValuePlus_pow_zero (A : SL(2, ℤ)) (hA : L4.SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) :
    L4.specialValuePlus (A ^ r) (L4.specialValue_pow_admissible A hA r hr) 0 =
      (Real.sqrt (L4.specialValueEpsilon A) : ℂ) ^ r := by
  rw [L4.specialValuePlus_zero, sqrt_specialValueEpsilon_pow A hA r hr, Complex.ofReal_pow]

/-- [RW-rec, p. 4, (9)] direct existing matrix interface on the whole larger group; [RW26, Prop. 8,
p. 14]. -/
theorem specialValuePlus_epsilon_invariant (A : SL(2, ℤ))
    (hA : L4.SpecialValueAdmissible A) (r : ℕ) (hr : 0 < r)
    (x : L4.SpecialValueGroup (A ^ r)) :
    L4.specialValuePlus (A ^ r) (L4.specialValue_pow_admissible A hA r hr)
      (L4.specialValueUnitAction A r x) =
      L4.specialValuePlus (A ^ r) (L4.specialValue_pow_admissible A hA r hr) x := by
  exact (L4.specialValuePlus_base_invariant A hA r hr x).symm

#print powerRowMatrix
#print powerRow
#print inclusion
#check @L4.specialValuePlus
#check @L4.specialValueMinus
#check @L4.modularPhi_iterate_fixedPoint
#check specialValuePlus_pow

end SICLean.L5.PeriodPowerMatrix
