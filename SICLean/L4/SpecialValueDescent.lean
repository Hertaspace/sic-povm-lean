import SICLean.L4.SpecialValueDescentAux

set_option autoImplicit false

/-!
# Actual values, regularity and descent

[RW26, p. 2, p. 3, p. 12, (2), Lemma 2, footnote 2].

All centers here refer to the same finite-product modularPhi. Joint
regularity is a conclusion. The raw μΦ is used only outside Λ when
proving periodicity. On Λ the two prescribed constants are used, so
no common-index identity is asserted across a removable-value jump.
Quotient.lift is justified by the nonlattice periodicity and prescribed
lattice constants, with the parameter algebra in SpecialValueDescentAux.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4

/-- The actual nonlattice expression [RW26, (2)] same η multiplier. -/
def specialValueRaw (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℂ :=
  etaMultiplier M * modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ)

/-- [RW26, (2)] plus branch. Lattice values are prescribed separately. -/
def specialValuePlusLift (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℂ :=
  if u ∈ specialValueLattice M then (Real.sqrt (specialValueEpsilon M) : ℂ)
  else specialValueRaw M u

/-- [RW26, (2)] minus branch. The inverse is taken after the positive root. -/
def specialValueMinusLift (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℂ :=
  if u ∈ specialValueLattice M then (Real.sqrt (specialValueEpsilon M) : ℂ)⁻¹
  else specialValueRaw M u

/-- Descent of the explicit plus lift. No analytic property is a field. -/
def specialValuePlus (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    SpecialValueGroup M → ℂ :=
  Quotient.lift (specialValuePlusLift M) (by
    intro u v huv
    have hv : v - u ∈ specialValueLattice M := by
      simpa only [sub_eq_neg_add] using (QuotientAddGroup.leftRel_apply.mp huv)
    have hp := SpecialValueDescentAux.piecewise_periodic M hM
      (Real.sqrt (specialValueEpsilon M) : ℂ) u (v - u) hv
    have huv' : u + (v - u) = v := by abel
    simpa only [huv', specialValuePlusLift, specialValueRaw] using hp.symm)

/-- Descent of the explicit minus lift. -/
def specialValueMinus (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    SpecialValueGroup M → ℂ :=
  Quotient.lift (specialValueMinusLift M) (by
    intro u v huv
    have hv : v - u ∈ specialValueLattice M := by
      simpa only [sub_eq_neg_add] using (QuotientAddGroup.leftRel_apply.mp huv)
    have hp := SpecialValueDescentAux.piecewise_periodic M hM
      (Real.sqrt (specialValueEpsilon M) : ℂ)⁻¹ u (v - u) hv
    have huv' : u + (v - u) = v := by abel
    simpa only [huv', specialValueMinusLift, specialValueRaw] using hp.symm)

/--
The phase needed by diagonal shifts, [RW26, p. 12]. This holds also in the zero class.
-/
theorem specialValue_phase (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    (e (specialValueTau M : ℂ)) ^ u.1 * e (specialValueArgument M u) =
      e (specialValueArgument M u / (specialValueEpsilon M : ℂ)) := by
  exact SpecialValueDescentAux.phase M hM u

/--
Nonzero classes have no vanishing diagonal-shift factor, for any
integer index. [RW26, p. 12].
The off-lattice hypothesis is essential at the crossing r=0 to r=1.
-/
theorem specialValue_index_factors_ne_zero (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M)
    (j : ℤ) :
    1 - (e (specialValueTau M : ℂ)) ^ (u.1 + j) * e (specialValueArgument M u) ≠ 0 := by
  exact SpecialValueDescentAux.index_factors_ne_zero M hM u hu j

/--
Genuine joint regularity of every diagonal shift at the actual
center, plus its actual nonzero value. [RW26, p. 6, p. 12].
This supplies pointwise continuity; a punctured germ alone would not.
-/
theorem specialValuePhi_joint_regular (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M)
    (h : ℤ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M (u.1 + h) h p.1 p.2)
      (specialValueArgument M u, (specialValueTau M : ℂ)) ∧
    modularPhi M (u.1 + h) h (specialValueArgument M u) (specialValueTau M : ℂ) ≠ 0 := by
  exact SpecialValueDescentAux.joint_regular M hM u hu (u.1 + h) h

/--
Raw μΦ periodicity only for nonzero classes. [RW26, p. 12, Lemma 2].
-/
theorem specialValueRaw_periodic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hu : u ∉ specialValueLattice M) (hv : v ∈ specialValueLattice M) :
    specialValueRaw M (u + v) = specialValueRaw M u := by
  exact congrArg (etaMultiplier M * ·) (SpecialValueDescentAux.phi_periodic M hM u v hu hv)

/--
Plus periodicity on all classes, including its separate Λ branch.
[RW26, p. 12, Lemma 2].
-/
theorem specialValuePlusLift_periodic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hv : v ∈ specialValueLattice M) :
    specialValuePlusLift M (u + v) = specialValuePlusLift M u := by
  exact SpecialValueDescentAux.piecewise_periodic M hM _ u v hv

/--
Minus periodicity on all classes. [RW26, p. 12, Lemma 2].
-/
theorem specialValueMinusLift_periodic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hv : v ∈ specialValueLattice M) :
    specialValueMinusLift M (u + v) = specialValueMinusLift M u := by
  exact SpecialValueDescentAux.piecewise_periodic M hM _ u v hv

/--
The downstream representative formula, [RW26, p. 2, p. 12, (2), Lemma 2].
-/
theorem specialValuePlus_mk (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    specialValuePlus M hM (specialValueMk M u) = specialValuePlusLift M u := by
  rfl

/--
The minus representative formula. [RW26, p. 2, p. 12, (2), Lemma 2].
-/
theorem specialValueMinus_mk (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    specialValueMinus M hM (specialValueMk M u) = specialValueMinusLift M u := by
  rfl

/--
Actual plus zero value, [RW26, pp. 2--3, (2), (4)].
-/
theorem specialValuePlus_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    specialValuePlus M hM 0 = (Real.sqrt (specialValueEpsilon M) : ℂ) := by
  simpa [specialValuePlusLift] using specialValuePlus_mk M hM 0

/--
[RW26, pp. 2--3, (2), (4)].
Actual minus zero value. This is a prescribed center,
not the raw Φ value inferred from a punctured identity.
-/
theorem specialValueMinus_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    specialValueMinus M hM 0 = (Real.sqrt (specialValueEpsilon M) : ℂ)⁻¹ := by
  simpa [specialValueMinusLift] using specialValueMinus_mk M hM 0

/-- Literal [RW26, p. 3, footnote 2]. -/
theorem specialValue_agree_off_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : SpecialValueGroup M) (hu : u ≠ 0) :
    specialValuePlus M hM u = specialValueMinus M hM u := by
  revert hu
  refine Quotient.inductionOn u ?_
  intro v hv
  have hvl : v ∉ specialValueLattice M := by
    intro h
    exact hv ((QuotientAddGroup.eq_zero_iff v).mpr h)
  change specialValuePlus M hM (specialValueMk M v) =
    specialValueMinus M hM (specialValueMk M v)
  rw [specialValuePlus_mk, specialValueMinus_mk]
  simp only [specialValuePlusLift, specialValueMinusLift, if_neg hvl]

/--
Nonzero values including the zero class. [RW26, p. 6]; [RW26, p. 12, Lemma 2].
-/
theorem specialValuePlus_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : SpecialValueGroup M) : specialValuePlus M hM u ≠ 0 := by
  refine Quotient.inductionOn u ?_
  intro v
  change specialValuePlus M hM (specialValueMk M v) ≠ 0
  rw [specialValuePlus_mk]
  by_cases hv : v ∈ specialValueLattice M
  · simp only [specialValuePlusLift, if_pos hv, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr
      (lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)))
  · simp only [specialValuePlusLift, if_neg hv, specialValueRaw]
    apply mul_ne_zero (etaMultiplier_ne_zero M hM.1)
    simpa only [add_zero] using (specialValuePhi_joint_regular M hM v hv 0).2

/--
Minus nonvanishing on all classes. [RW26, p. 6, p. 12, Lemma 2].
-/
theorem specialValueMinus_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : SpecialValueGroup M) : specialValueMinus M hM u ≠ 0 := by
  by_cases hu : u = 0
  · subst u
    rw [specialValueMinus_zero]
    apply inv_ne_zero
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr
      (lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM))))
  · rw [← specialValue_agree_off_zero M hM u hu]
    exact specialValuePlus_ne_zero M hM u

/--
The exact nonzero-class [RW26, (2)] interface, with no representative choice.
[RW26, p. 2, p. 12].
-/
theorem specialValue_nonzero_class_formula (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) (hu : specialValueMk M u ≠ 0) :
    specialValuePlus M hM (specialValueMk M u) = specialValueRaw M u ∧
      specialValueMinus M hM (specialValueMk M u) = specialValueRaw M u := by
  have hul : u ∉ specialValueLattice M := by
    intro h
    exact hu ((QuotientAddGroup.eq_zero_iff u).mpr h)
  rw [specialValuePlus_mk, specialValueMinus_mk]
  simp only [specialValuePlusLift, specialValueMinusLift, if_neg hul, and_self]

#check @modularPhi_diagonal_index_fixedPoint
#check @modularPhi_fixedPoint_lattice_value
#print specialValueRaw
#print specialValuePlusLift
#print specialValueMinusLift
#check specialValuePhi_joint_regular
#check specialValue_nonzero_class_formula

end SICLean.L4
