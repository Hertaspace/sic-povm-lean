import SICLean.L4.PseudolatticeMatrixValues

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace SICLean.L4.PseudolatticeSignedTransportAux

open SICLean.L3.M72

theorem rowAction_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (u : ℤ × ℤ) :
    L2r.rowAction (A * B) u = L2r.rowAction B (L2r.rowAction A u) := by
  ext <;> simp [L2r.rowAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rowAction_one (u : ℤ × ℤ) :
    L2r.rowAction (1 : Matrix (Fin 2) (Fin 2) ℤ) u = u := by
  ext <;> simp [L2r.rowAction]

theorem conjugate_order (M R : SL(2, ℤ)) :
    specialValueOrder (R * M * R⁻¹) = specialValueOrder M := by
  have ht : Matrix.trace ((R * M * R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
      ← Matrix.SpecialLinearGroup.coe_mul]
    simp
  simpa [specialValueOrder, Matrix.trace, Matrix.diag, Fin.sum_univ_two] using
    congrArg (fun z : ℤ => z - 2) ht

theorem conjugate_epsilon (M R : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (hC : SpecialValueAdmissible (R * M * R⁻¹)) :
    specialValueEpsilon (R * M * R⁻¹) = specialValueEpsilon M := by
  rw [specialValueEpsilon_formula _ hC, specialValueEpsilon_formula _ hM,
    conjugate_order]

private theorem tau_polynomial (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (M 1 0 : ℝ) * specialValueTau M ^ 2 +
      ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * specialValueTau M - (M 0 1 : ℝ) = 0 := by
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hd : (M 0 0 : ℝ) * (M 1 1 : ℝ) -
      (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by exact_mod_cast det_coe_int M
  have he := specialValueEpsilon_characteristic M hM
  simp only [specialValueEpsilon, specialValueOrder, Int.cast_sub, Int.cast_add,
    Int.cast_ofNat] at he
  nlinarith

private theorem conjugate_lowerLeft_expansion (M R : SL(2, ℤ)) :
    ((R * M * R⁻¹) 1 0 : ℝ) =
      (M 1 0 : ℝ) * (R 1 1 : ℝ) ^ 2 +
      ((M 0 0 : ℝ) - (M 1 1 : ℝ)) * (R 1 0 : ℝ) * (R 1 1 : ℝ) -
      (M 0 1 : ℝ) * (R 1 0 : ℝ) ^ 2 := by
  change (((R : Matrix (Fin 2) (Fin 2) ℤ) * (M : Matrix (Fin 2) (Fin 2) ℤ) *
    ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ℝ) = _
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

theorem conjugate_lowerLeft (M R : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ((R * M * R⁻¹) 1 0 : ℝ) = (M 1 0 : ℝ) *
      ((R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) *
      ((R 1 0 : ℝ) * distributionConjugateTau (matrixBasis M) + (R 1 1 : ℝ)) := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM.1)
  have hp := tau_polynomial M hM
  rw [conjugate_lowerLeft_expansion]
  simp only [distributionConjugateTau, matrixBasis]
  field_simp
  nlinarith [sq_nonneg ((R 1 0 : ℝ))]

theorem factor_signs (M R : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (hC : SpecialValueAdmissible (R * M * R⁻¹)) :
    ((R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) ≠ 0 ∧
      0 < ((R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) *
        ((R 1 0 : ℝ) * distributionConjugateTau (matrixBasis M) + (R 1 1 : ℝ)) := by
  have hcM : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hcC : (0 : ℝ) < ((R * M * R⁻¹) 1 0 : ℝ) := by exact_mod_cast hC.1
  have hh := conjugate_lowerLeft M R hM
  have hp : 0 < ((R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) *
      ((R 1 0 : ℝ) * distributionConjugateTau (matrixBasis M) + (R 1 1 : ℝ)) := by
    apply (mul_pos_iff_of_pos_left hcM).mp
    rw [← mul_assoc, ← hh]
    exact hcC
  refine ⟨?_, hp⟩
  intro hz
  simp [hz] at hp

theorem positiveChange (M R : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (hC : SpecialValueAdmissible (R * M * R⁻¹))
    (hf : 0 < (R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) :
    DistributionPositiveChange (matrixBasis M) R := by
  refine ⟨hf, ?_, hC.1⟩
  exact (mul_pos_iff_of_pos_left hf).mp (factor_signs M R hM hC).2

theorem negativeChange (M R : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (hC : SpecialValueAdmissible (R * M * R⁻¹))
    (hf : ¬0 < (R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) :
    DistributionPositiveChange (matrixBasis M) (-R) := by
  have hl := (lt_or_gt_of_ne (factor_signs M R hM hC).1).resolve_right hf
  have hC' : SpecialValueAdmissible ((-R) * M * (-R)⁻¹) := by simpa using hC
  apply positiveChange M (-R) hM hC'
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
  linarith

private theorem mul10_real (A B : SL(2, ℤ)) :
    ((A * B) 1 0 : ℝ) = (A 1 0 : ℝ) * (B 0 0 : ℝ) +
      (A 1 1 : ℝ) * (B 1 0 : ℝ) := by
  change (((A : Matrix (Fin 2) (Fin 2) ℤ) * (B : Matrix (Fin 2) (Fin 2) ℤ))
    1 0 : ℝ) = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem mul11_real (A B : SL(2, ℤ)) :
    ((A * B) 1 1 : ℝ) = (A 1 0 : ℝ) * (B 0 1 : ℝ) +
      (A 1 1 : ℝ) * (B 1 1 : ℝ) := by
  change (((A : Matrix (Fin 2) (Fin 2) ℤ) * (B : Matrix (Fin 2) (Fin 2) ℤ))
    1 1 : ℝ) = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem conjugate_tau (M R : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (hC : SpecialValueAdmissible (R * M * R⁻¹)) :
    specialValueTau (R * M * R⁻¹) = distributionRealMobius R (specialValueTau M) := by
  have hCR : (R * M * R⁻¹) * R = R * M := by simp [mul_assoc]
  have h0 := congrArg (fun A : SL(2, ℤ) => (A 1 0 : ℝ)) hCR
  have h1 := congrArg (fun A : SL(2, ℤ) => (A 1 1 : ℝ)) hCR
  rw [mul10_real (R * M * R⁻¹) R, mul10_real R M] at h0
  rw [mul11_real (R * M * R⁻¹) R, mul11_real R M] at h1
  have heig : (M 0 0 : ℝ) * specialValueTau M + (M 0 1 : ℝ) =
      specialValueEpsilon M * specialValueTau M := by
    unfold specialValueEpsilon
    nlinarith [tau_polynomial M hM]
  have hrel : ((R * M * R⁻¹) 1 0 : ℝ) *
        ((R 0 0 : ℝ) * specialValueTau M + (R 0 1 : ℝ)) +
      ((R * M * R⁻¹) 1 1 : ℝ) *
        ((R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) =
      specialValueEpsilon M *
        ((R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) := by
    calc
      _ = ((R 1 0 : ℝ) * (M 0 0 : ℝ) + (R 1 1 : ℝ) * (M 1 0 : ℝ)) *
          specialValueTau M +
        ((R 1 0 : ℝ) * (M 0 1 : ℝ) + (R 1 1 : ℝ) * (M 1 1 : ℝ)) := by
          linear_combination (specialValueTau M) * h0 + h1
      _ = _ := by
        unfold specialValueEpsilon at heig ⊢
        linear_combination (R 1 0 : ℝ) * heig
  have heps := conjugate_epsilon M R hM hC
  have heps' : ((R * M * R⁻¹) 1 0 : ℝ) * specialValueTau (R * M * R⁻¹) +
      ((R * M * R⁻¹) 1 1 : ℝ) = specialValueEpsilon M := heps
  have hc : ((R * M * R⁻¹) 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hC.1)
  unfold distributionRealMobius
  apply (eq_div_iff (factor_signs M R hM hC).1).mpr
  apply mul_left_cancel₀ hc
  linear_combination
    ((R 1 0 : ℝ) * specialValueTau M + (R 1 1 : ℝ)) * heps' - hrel

theorem rowPoint_rebase (B : DistributionBasis) (hB : B.Valid)
    (R : SL(2, ℤ)) (hR : DistributionPositiveChange B R) (v : ℤ × ℤ) :
    distributionRowPoint (distributionRebase B R) v =
      distributionRowPoint B (L2r.rowAction (R : Matrix (Fin 2) (Fin 2) ℤ) v) := by
  have hv := distributionRebase_valid B hB R hR
  have hf : (R 1 0 : ℝ) * B.tau + (R 1 1 : ℝ) ≠ 0 := ne_of_gt hR.1
  have hfc : (R 1 0 : ℝ) * distributionConjugateTau B + (R 1 1 : ℝ) ≠ 0 :=
    ne_of_gt hR.2.1
  simp only [distributionRowPoint]
  rw [hv.2.1]
  apply Prod.ext
  · change ((v.1 : ℝ) * (distributionBetaOne (distributionRebase B R)).1 +
        (v.2 : ℝ) * (distributionBetaTwo (distributionRebase B R)).1) / _ = _
    apply congrArg (fun x : ℝ => x / ((distributionPeriod B)⁻¹ - 1))
    simp only [distributionBetaOne, distributionBetaTwo, distributionRebase,
      distributionRealMobius, L2r.rowAction, Int.cast_add, Int.cast_mul]
    field_simp
    ring
  · change ((v.1 : ℝ) * (distributionBetaOne (distributionRebase B R)).2 +
        (v.2 : ℝ) * (distributionBetaTwo (distributionRebase B R)).2) / _ = _
    apply congrArg (fun x : ℝ => x / (distributionPeriod B - 1))
    simp only [distributionBetaOne, distributionBetaTwo]
    rw [hv.2.2]
    simp only [distributionRebase, distributionRealMobius, L2r.rowAction,
      Int.cast_add, Int.cast_mul]
    field_simp
    ring

theorem row_conjugate_mem (M R : SL(2, ℤ)) (u : ℤ × ℤ)
    (hu : u ∈ specialValueLattice M) :
    L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u ∈
      specialValueLattice (R * M * R⁻¹) := by
  have hR : ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * R = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul]
    simp
  have hcomm : ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) * (R⁻¹ : SL(2, ℤ)) =
      (R⁻¹ : SL(2, ℤ)) *
        (((R * M * R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, mul_sub, sub_mul, mul_one,
      ← Matrix.mul_assoc, hR, one_mul]
  rcases hu with ⟨w, hw⟩
  change L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w = u at hw
  refine ⟨L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) w, ?_⟩
  change L2r.rowAction _ _ = _
  rw [← rowAction_mul, ← hcomm, rowAction_mul, hw]

theorem row_conjugate_rel (M R : SL(2, ℤ)) (u v : ℤ × ℤ)
    (h : QuotientAddGroup.leftRel (specialValueLattice M) u v) :
    specialValueMk (R * M * R⁻¹)
        (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u) =
      specialValueMk (R * M * R⁻¹)
        (L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) v) := by
  apply Quotient.sound
  apply QuotientAddGroup.leftRel_apply.mpr
  have hh := row_conjugate_mem M R (-u + v) (QuotientAddGroup.leftRel_apply.mp h)
  have heq : L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (-u + v) =
      -L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u +
        L2r.rowAction ((R⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) v := by
    ext <;> simp [L2r.rowAction] <;> ring
  rw [heq] at hh
  exact hh

/-- All labels, including the separately prescribed origin. -/
theorem rowPoint_plusLift (B : DistributionBasis) (hB : B.Valid) (u : ℤ × ℤ) :
    distributionBasisValue B (distributionRowPoint B u) = specialValuePlusLift B.matrix u := by
  rw [← distributionValue_mk B hB _ (distributionRowPoint_mem B hB u),
    ← rowEquiv_mk B hB u, distributionPlus_eq_specialPlus, specialValuePlus_mk]

theorem rebase_plusLift (B : DistributionBasis) (hB : B.Valid)
    (R : SL(2, ℤ)) (hR : DistributionPositiveChange B R) (v : ℤ × ℤ) :
    specialValuePlusLift (R * B.matrix * R⁻¹) v =
      specialValuePlusLift B.matrix (L2r.rowAction (R : Matrix (Fin 2) (Fin 2) ℤ) v) := by
  have hC := (distributionRebase_valid B hB R hR).1
  change specialValuePlusLift (distributionRebase B R).matrix v = _
  rw [← rowPoint_plusLift (distributionRebase B R) hC v, rowPoint_rebase B hB R hR v,
    distributionRebase_value B hB R hR _
      (distributionRowPoint_mem B hB (L2r.rowAction (R : Matrix (Fin 2) (Fin 2) ℤ) v)),
    rowPoint_plusLift B hB]

end SICLean.L4.PseudolatticeSignedTransportAux
