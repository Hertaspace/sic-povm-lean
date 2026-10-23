import SICLean.L5.ActualOriginal
import SICLean.L5.ActualRank
import SICLean.L5.Prop7Final

set_option autoImplicit false

/-!
# Proposition 7 for the actual values, and the two final statements

`matrix_prop7` is Proposition 7 for the actual values. The arithmetic field
and the algebraic lifts are the definitions from the preceding files. The
statement adds no further analytic or reciprocity hypothesis. The label
transport and the final assembly below use this target. Its proof is
`Prop7Final.matrix_prop7_final`: descent to the narrow ray class field
by Chebotarev, the action of the double-sign class,
and the analytic conjugation formula.

Sources: [RW-rec, Prop. 7, pp. 17--18]; [RW26, (37), p. 20; Thm. 7, (39), p. 20].
The rank-r range is the existing admissible range.
No ray class group, Artin map, or density is defined in this file.
-/

noncomputable section
open OpenQuantumProblem23
open scoped MatrixGroups

namespace SICLean.L5.ActualProp7

/-- Proposition 7 for the actual values: an automorphism flipping K sends
every nonzero quotient class to the unit circle.
[RW-rec, Prop. 7, pp. 17--18]; [RW26, (37), p. 20; p. 2, (2)].
The zero class is excluded by `Prop7ForValues`. -/
theorem matrix_prop7 (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    Galois.Prop7ForValues (ActualField.baseField M hM) (ActualValues.matrixLift M hM) := by
  exact Prop7Final.matrix_prop7_final M hM

/-- The same statement on the canonical pseudolattice labels, by the exact
label dictionary. [RW-rec, Prop. 7]; [RW26, p. 20]. -/
theorem pseudolattice_prop7 (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    Galois.Prop7ForValues (ActualField.baseField M hM) (ActualValues.valueLift M hM) := by
  intro σ hσ x hx
  obtain ⟨g, rfl⟩ := (ActualLattice.labelEquiv M hM).surjective x
  rw [ActualValues.valueLift_label M hM g]
  exact matrix_prop7 M hM σ hσ g
    (fun hg => hx ((ActualLattice.labelEquiv_zero_iff M hM g).2 hg))

/-- Fixed-embedding injectivity promotes a chosen lift to every preimage in
`Prop7Actual`. Every complex preimage equals that lift.
[RW-rec, Prop. 7]; [RW26, Thm. 1, p. 3; (37), p. 20]. -/
theorem prop7Actual_of_forValues {J : Type*} [Zero J] (E : J → ℂ)
    (K : IntermediateField ℚ Galois.Qbar) (a : J → Galois.Qbar)
    (hK : Galois.IsRealQuadratic K) (ha : ∀ x, Galois.embed (a x) = E x)
    (h7 : Galois.Prop7ForValues K a) : FinalAssembly.Prop7Actual E := by
  refine ⟨K, hK, ?_⟩
  intro σ hσ x hx b hb
  have hb' : b = a x := Galois.embed.injective (hb.trans (ha x).symm)
  rw [hb']
  exact h7 σ hσ x hx

/-- Matrix form of the final-assembly statement.
[RW-rec, Prop. 7]; [RW26, p. 20]. -/
theorem matrix_prop7Actual (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    FinalAssembly.Prop7Actual (L4.specialValuePlus M hM) := by
  exact prop7Actual_of_forValues (L4.specialValuePlus M hM)
    (ActualField.baseField M hM) (ActualValues.matrixLift M hM)
    (ActualField.baseField_isRealQuadratic M hM)
    (ActualValues.embed_matrixLift M hM) (matrix_prop7 M hM)

/-- The general target at alpha^3 implies the original-chain statement.
[RW26, p. 20]; [RW-rec, Prop. 7]. -/
theorem rwL2c_prop7Actual_of_matrix (M : ℕ) [Fact (4 ≤ M)]
    (h7 : Galois.Prop7ForValues (ActualOriginal.baseField M)
      (ActualValues.matrixLift (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2)) :
    FinalAssembly.Prop7Actual (L4.rwL2cPlus M) := by
  refine prop7Actual_of_forValues (L4.rwL2cPlus M) (ActualOriginal.baseField M)
    (ActualOriginal.valueLift M) (ActualOriginal.baseField_isRealQuadratic M)
    (ActualOriginal.embed_valueLift M) ?_
  intro σ hσ g hg
  rw [ActualOriginal.valueLift_eq_matrixLift M g]
  exact h7 σ hσ (L4.rwL2cEquiv M g)
    (by simpa only [ne_eq, AddEquiv.map_eq_zero_iff] using hg)

/-- The same implication for beta^2*L, with its period eta.
[RW26, (37), p. 20]; [RW-rec, Prop. 7]. -/
theorem rwL2rc_prop7Actual_of_matrix (d r : ℕ) [Fact (L2r.Admissible d r)]
    (h7 : Galois.Prop7ForValues (ActualRank.baseField d r)
      (ActualValues.matrixLift (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2)) :
    FinalAssembly.Prop7Actual (L4.rwL2rcPlus d r) := by
  refine prop7Actual_of_forValues (L4.rwL2rcPlus d r) (ActualRank.baseField d r)
    (ActualRank.valueLift d r) (ActualRank.baseField_isRealQuadratic d r)
    (ActualRank.embed_valueLift d r) ?_
  intro σ hσ g hg
  rw [ActualRank.valueLift_eq_matrixLift d r g]
  exact h7 σ hσ (L4.rwL2rcEquiv d r g)
    (by simpa only [ne_eq, AddEquiv.map_eq_zero_iff] using hg)

/-- The original-chain statement. It follows from
`rwL2c_prop7Actual_of_matrix` and `matrix_prop7`.
[RW-rec, Prop. 7, pp. 17--18]; [RW26, p. 20]. -/
theorem rwL2c_prop7Actual (M : ℕ) [Fact (4 ≤ M)] :
    FinalAssembly.Prop7Actual (L4.rwL2cPlus M) := by
  exact rwL2c_prop7Actual_of_matrix M
    (matrix_prop7 (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2)

/-- The rank-r statement. It follows from `rwL2rc_prop7Actual_of_matrix`
and `matrix_prop7`. [RW-rec, Prop. 7]; [RW26, p. 20]. -/
theorem rwL2rc_prop7Actual (d r : ℕ) [Fact (L2r.Admissible d r)] :
    FinalAssembly.Prop7Actual (L4.rwL2rcPlus d r) := by
  exact rwL2rc_prop7Actual_of_matrix d r
    (matrix_prop7 (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2)

#check @Galois.Prop7ForValues
#print matrix_prop7
#check @FinalAssembly.Prop7Actual
#check @FinalAssembly.zaunerExistence_of_prop7
#check @FinalAssembly.hasRSIC_of_prop7

end SICLean.L5.ActualProp7

namespace SICLean.FinalAssembly

/-- The final statement in every dimension, including dimensions 1--3.
It follows from `zaunerExistence_of_prop7` and
`L5.ActualProp7.rwL2c_prop7Actual` for every `M ≥ 4`.
The arithmetic input is `matrix_prop7`.
[RW-rec, Prop. 7, pp. 17--18]; [RW26, Thm. 7, (39), p. 20]. -/
theorem zaunerExistence : ZaunerExistence := by
  apply zaunerExistence_of_prop7
  intro M hM
  let : Fact (4 ≤ M) := ⟨hM⟩
  exact L5.ActualProp7.rwL2c_prop7Actual M

/-- The rank-r statement on the existing admissible range.
The hypotheses are `1 ≤ r`, `2 * r + 1 < d`, and the divisibility condition.
It follows from `hasRSIC_of_prop7` and
`L5.ActualProp7.rwL2rc_prop7Actual`. The arithmetic input is `matrix_prop7`.
[RW-rec, Prop. 7]; [RW26, (37), p. 20]. -/
theorem hasRSIC (d r : ℕ) (hr : 1 ≤ r) (hd : 2 * r + 1 < d)
    (hdiv : r * (d - r) ∣ d ^ 2 - 1) : HasRSIC d r := by
  apply hasRSIC_of_prop7 ?_ d r hr hd hdiv
  intro d' r' hr' hd' hdiv'
  let : Fact (L2r.Admissible d' r') := ⟨⟨hr', hd', hdiv'⟩⟩
  exact L5.ActualProp7.rwL2rc_prop7Actual d' r'

#print zaunerExistence
#print hasRSIC

end SICLean.FinalAssembly
