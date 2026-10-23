import SICLean.L4.PseudolatticeMatrixValues
import SICLean.L4.SpecialValueReflection
import SICLean.L4.PseudolatticeSignedTransportAux

set_option autoImplicit false

/-!
# Signed conjugation on the actual row quotient

A raw conjugation sends
u to u*R^-1. The value-preserving equivalence sends u to s*u*R^-1,
where s=sign(c_R*tau+d_R). A negative factor changes the label only.
Neither inverse nor complex conjugation is applied to a nonzero value.

[RW26, p. 23, Theorem 11].
Signed conjugation on the row quotient is formalized here. Matrix
background: [RW26, p. 2, p. 3, p. 6, (2), (3), (17), footnote 2]. The signed conjugation formula is
formalized here.
-/

noncomputable section

open scoped Classical MatrixGroups

namespace SICLean.L3.M72

def conjugateMatrix (M R : SL(2, ℤ)) : SL(2, ℤ) := R * M * R⁻¹

def automorphyFactor (M R : SL(2, ℤ)) : ℝ :=
  (R 1 0 : ℝ) * L4.specialValueTau M + (R 1 1 : ℝ)

def automorphySign (M R : SL(2, ℤ)) : ℤ :=
  if 0 < automorphyFactor M R then 1 else -1

def signedRow (M R : SL(2, ℤ)) (u : ℤ × ℤ) : ℤ × ℤ :=
  automorphySign M R • u

def conjugateEquiv (M R : SL(2, ℤ)) :
    L4.SpecialValueGroup M ≃+ L4.SpecialValueGroup (conjugateMatrix M R) where
  toFun := Quotient.lift (fun u : ℤ × ℤ =>
    L4.specialValueMk (conjugateMatrix M R)
      (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u)) (by
        intro u v h
        exact L4.PseudolatticeSignedTransportAux.row_conjugate_rel M R u v h)
  invFun := Quotient.lift (fun u : ℤ × ℤ =>
    L4.specialValueMk M (L2r.rowAction (R : Matrix (Fin 2) (Fin 2) ℤ) u)) (by
      intro u v h
      have hh := L4.PseudolatticeSignedTransportAux.row_conjugate_rel
        (conjugateMatrix M R) R⁻¹ u v h
      have hc : R⁻¹ * conjugateMatrix M R * (R⁻¹)⁻¹ = M := by
        simp [conjugateMatrix, mul_assoc]
      rw [hc] at hh
      simpa only [inv_inv] using hh)
  left_inv := by
    intro g
    refine Quotient.inductionOn g ?_
    intro u
    change L4.specialValueMk M (L2r.rowAction (R : Matrix (Fin 2) (Fin 2) ℤ)
      (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u)) =
        L4.specialValueMk M u
    rw [← L4.PseudolatticeSignedTransportAux.rowAction_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, L4.PseudolatticeSignedTransportAux.rowAction_one]
  right_inv := by
    intro g
    refine Quotient.inductionOn g ?_
    intro u
    change L4.specialValueMk (conjugateMatrix M R)
      (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        (L2r.rowAction (R : Matrix (Fin 2) (Fin 2) ℤ) u)) =
          L4.specialValueMk (conjugateMatrix M R) u
    rw [← L4.PseudolatticeSignedTransportAux.rowAction_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, L4.PseudolatticeSignedTransportAux.rowAction_one]
  map_add' := by
    intro g h
    refine Quotient.inductionOn₂ g h ?_
    intro u v
    exact ((L4.specialValueMk (conjugateMatrix M R)).comp
      (L2r.rowActionHom ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))).map_add u v

def signedConjugateEquiv (M R : SL(2, ℤ)) :
    L4.SpecialValueGroup M ≃+ L4.SpecialValueGroup (conjugateMatrix M R) :=
  (if 0 < automorphyFactor M R then AddEquiv.refl (L4.SpecialValueGroup M)
    else AddEquiv.neg (L4.SpecialValueGroup M)).trans (conjugateEquiv M R)

/--
Raw row map; [RW26, p. 3] row quotient.
-/
theorem conjugateEquiv_mk (M R : SL(2, ℤ)) (u : ℤ × ℤ) :
    conjugateEquiv M R (L4.specialValueMk M u) =
      L4.specialValueMk (conjugateMatrix M R)
        (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u) := by
  rfl

/--
Value-preserving label s*u*R^-1 on the quotient of [RW26, p. 3].
-/
theorem signedConjugateEquiv_mk (M R : SL(2, ℤ)) (u : ℤ × ℤ) :
    signedConjugateEquiv M R (L4.specialValueMk M u) =
      L4.specialValueMk (conjugateMatrix M R)
        (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (signedRow M R u)) := by
  by_cases hj : 0 < automorphyFactor M R
  · simpa [signedConjugateEquiv, signedRow, automorphySign, hj] using
      conjugateEquiv_mk M R u
  · simpa [signedConjugateEquiv, signedRow, automorphySign, hj] using
      conjugateEquiv_mk M R (-u)

/--
Trace/size is unchanged; [RW26, p. 3, (3)].
-/
theorem conjugate_order (M R : SL(2, ℤ)) :
    L4.specialValueOrder (conjugateMatrix M R) = L4.specialValueOrder M := by
  exact L4.PseudolatticeSignedTransportAux.conjugate_order M R

/--
c_tilde=c*j*j'; [RW26, p. 6, (17)].
-/
theorem conjugate_lowerLeft (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) :
    ((conjugateMatrix M R) 1 0 : ℝ) = (M 1 0 : ℝ) * automorphyFactor M R *
      ((R 1 0 : ℝ) * L4.distributionConjugateTau (matrixBasis M) + (R 1 1 : ℝ)) := by
  exact L4.PseudolatticeSignedTransportAux.conjugate_lowerLeft M R hM

/--
Both factors are nonzero with the same sign; [RW26, p. 6, (17)].
-/
theorem automorphyFactor_signs (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) :
    automorphyFactor M R ≠ 0 ∧
      0 < automorphyFactor M R *
        ((R 1 0 : ℝ) * L4.distributionConjugateTau (matrixBasis M) + (R 1 1 : ℝ)) := by
  exact L4.PseudolatticeSignedTransportAux.factor_signs M R hM hC

/--
The attracting fixed point follows R; [RW26, p. 2, (2)].
-/
theorem conjugate_tau (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) :
    L4.specialValueTau (conjugateMatrix M R) =
      L4.distributionRealMobius R (L4.specialValueTau M) := by
  exact L4.PseudolatticeSignedTransportAux.conjugate_tau M R hM hC

/--
The attracting period is identical; [RW26, p. 3, (4)].
-/
theorem conjugate_epsilon (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) :
    L4.specialValueEpsilon (conjugateMatrix M R) = L4.specialValueEpsilon M := by
  exact L4.PseudolatticeSignedTransportAux.conjugate_epsilon M R hM hC

/--
Same actual etaMultiplier, including negative automorphy factors; [RW26, p. 3] mu, (background).
-/
theorem conjugate_multiplier (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) :
    L4.etaMultiplier (conjugateMatrix M R) = L4.etaMultiplier M := by
  by_cases hj : 0 < automorphyFactor M R
  · exact L4.distributionRebase_multiplier (matrixBasis M) (matrixBasis_valid M hM) R
      (L4.PseudolatticeSignedTransportAux.positiveChange M R hM hC hj)
  · simpa [L4.distributionRebase, matrixBasis, conjugateMatrix] using
      L4.distributionRebase_multiplier (matrixBasis M) (matrixBasis_valid M hM) (-R)
        (L4.PseudolatticeSignedTransportAux.negativeChange M R hM hC hj)

/--
Literal signed formula on arbitrary integer labels; [RW26, p. 2, (2)].
-/
theorem conjugate_plusLift (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) (u : ℤ × ℤ) :
    L4.specialValuePlusLift (conjugateMatrix M R)
        (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u) =
      L4.specialValuePlusLift M (signedRow M R u) := by
  by_cases hj : 0 < automorphyFactor M R
  · have hv := L4.PseudolatticeSignedTransportAux.rebase_plusLift
      (matrixBasis M) (matrixBasis_valid M hM) R
      (L4.PseudolatticeSignedTransportAux.positiveChange M R hM hC hj)
      (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u)
    rw [← L4.PseudolatticeSignedTransportAux.rowAction_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, L4.PseudolatticeSignedTransportAux.rowAction_one] at hv
    simpa [matrixBasis, conjugateMatrix, signedRow, automorphySign, hj] using hv
  · have hv := L4.PseudolatticeSignedTransportAux.rebase_plusLift
      (matrixBasis M) (matrixBasis_valid M hM) (-R)
      (L4.PseudolatticeSignedTransportAux.negativeChange M R hM hC hj)
      (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u)
    rw [← L4.PseudolatticeSignedTransportAux.rowAction_mul,
      Matrix.SpecialLinearGroup.coe_neg, mul_neg,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one] at hv
    have hrow : L2r.rowAction (-(1 : Matrix (Fin 2) (Fin 2) ℤ)) u = -u := by
      ext <;> simp [L2r.rowAction]
    rw [hrow] at hv
    simpa [matrixBasis, conjugateMatrix, signedRow, automorphySign, hj] using hv

/--
Same signed formula for the separately normalized minus branch; [RW26, p. 3, footnote 2].
-/
theorem conjugate_minusLift (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) (u : ℤ × ℤ) :
    L4.specialValueMinusLift (conjugateMatrix M R)
        (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u) =
      L4.specialValueMinusLift M (signedRow M R u) := by
  have hmem :
      L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u ∈
          L4.specialValueLattice (conjugateMatrix M R) ↔
        u ∈ L4.specialValueLattice M := by
    constructor
    · intro hu
      have hh := L4.PseudolatticeSignedTransportAux.row_conjugate_mem
        (conjugateMatrix M R) R⁻¹
        (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u) hu
      simp only [inv_inv] at hh
      rw [← L4.PseudolatticeSignedTransportAux.rowAction_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one,
        L4.PseudolatticeSignedTransportAux.rowAction_one] at hh
      simpa [conjugateMatrix, mul_assoc] using hh
    · exact L4.PseudolatticeSignedTransportAux.row_conjugate_mem M R u
  have hs : signedRow M R u ∈ L4.specialValueLattice M ↔ u ∈ L4.specialValueLattice M := by
    by_cases hj : 0 < automorphyFactor M R <;> simp [signedRow, automorphySign, hj]
  have hp := conjugate_plusLift M R hM hC u
  by_cases hu : u ∈ L4.specialValueLattice M
  · simp only [L4.specialValueMinusLift, if_pos (hmem.mpr hu), if_pos (hs.mpr hu),
      conjugate_epsilon M R hM hC]
  · have hv := mt hmem.mp hu
    have hw := mt hs.mp hu
    simpa only [L4.specialValueMinusLift, L4.specialValuePlusLift,
      if_neg hv, if_neg hw] using hp

/--
A value-preserving additive equivalence; [RW26, p. 2, (2)].
-/
theorem signedConjugate_plus (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) (g : L4.SpecialValueGroup M) :
    L4.specialValuePlus (conjugateMatrix M R) hC (signedConjugateEquiv M R g) =
      L4.specialValuePlus M hM g := by
  refine Quotient.inductionOn g ?_
  intro u
  change L4.specialValuePlus _ hC (signedConjugateEquiv M R (L4.specialValueMk M u)) =
    L4.specialValuePlus M hM (L4.specialValueMk M u)
  rw [signedConjugateEquiv_mk, L4.specialValuePlus_mk, L4.specialValuePlus_mk,
    conjugate_plusLift M R hM hC]
  by_cases hj : 0 < automorphyFactor M R <;>
    simp [signedRow, automorphySign, hj]

/--
Minus origin is transported without changing branches; [RW26, p. 3, footnote 2].
-/
theorem signedConjugate_minus (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) (g : L4.SpecialValueGroup M) :
    L4.specialValueMinus (conjugateMatrix M R) hC (signedConjugateEquiv M R g) =
      L4.specialValueMinus M hM g := by
  refine Quotient.inductionOn g ?_
  intro u
  change L4.specialValueMinus _ hC (signedConjugateEquiv M R (L4.specialValueMk M u)) =
    L4.specialValueMinus M hM (L4.specialValueMk M u)
  rw [signedConjugateEquiv_mk, L4.specialValueMinus_mk, L4.specialValueMinus_mk,
    conjugate_minusLift M R hM hC]
  by_cases hj : 0 < automorphyFactor M R <;>
    simp [signedRow, automorphySign, hj]

/--
Signed label transport also fixes the Gaussian; [RW26, p. 3, (3)].
-/
theorem signedConjugate_gaussian (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R)) (g : L4.SpecialValueGroup M) :
    L4.specialValueGaussian (conjugateMatrix M R) hC (signedConjugateEquiv M R g) =
      L4.specialValueGaussian M hM g := by
  apply inv_injective
  rw [← L4.specialValue_mixed_reflection (conjugateMatrix M R) hC,
    ← L4.specialValue_mixed_reflection M hM,
    signedConjugate_plus M R hM hC]
  rw [← (signedConjugateEquiv M R).map_neg, signedConjugate_minus M R hM hC]

/--
Negative j only negates the old label; [RW26, p. 23, Theorem 11].
-/
theorem negative_factor_values (M R : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M)
    (hC : L4.SpecialValueAdmissible (conjugateMatrix M R))
    (hj : automorphyFactor M R < 0) (g : L4.SpecialValueGroup M) :
    L4.specialValuePlus (conjugateMatrix M R) hC (conjugateEquiv M R g) =
        L4.specialValuePlus M hM (-g) ∧
      L4.specialValueMinus (conjugateMatrix M R) hC (conjugateEquiv M R g) =
        L4.specialValueMinus M hM (-g) := by
  have hp := signedConjugate_plus M R hM hC (-g)
  have hm := signedConjugate_minus M R hM hC (-g)
  have hj' : ¬0 < automorphyFactor M R := not_lt_of_ge hj.le
  simpa [signedConjugateEquiv, hj'] using And.intro hp hm

#check @L2r.rowAction
#print conjugateEquiv
#print signedConjugateEquiv
#print signedRow
#check signedConjugate_plus
#check negative_factor_values

end SICLean.L3.M72
