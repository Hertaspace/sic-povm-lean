import SICLean.L2a.Weyl

/-! # The algebraic core of [RW26, Thm. 7]. -/

noncomputable section

open Matrix

namespace SICLean.L2a

/-- Reindex the two factors by `(u,v) ↦ (u,u+v)`, retaining the zero terms. -/
theorem P_mul_P {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) :
    P M F * P M F = convolutionScalar M • P M F + 1 := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hprod : P M F * P M F =
      (M : ℂ)⁻¹ • ∑ r : Index M, (convolution M F r.1.val r.2.val) • residueD M r := by
    calc
      _ = (M : ℂ)⁻¹ • ((M : ℂ)⁻¹ • ∑ u : Index M, ∑ v : Index M,
          (F u * F v) • (residueD M u * residueD M v)) := by
        simp only [P_eq_sum_residueD hM, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.sum_mul, Matrix.mul_sum, Finset.smul_sum, smul_smul, mul_assoc]
        rw [Finset.sum_comm]
        simp only [mul_assoc, mul_left_comm, mul_comm]
      _ = (M : ℂ)⁻¹ • ((M : ℂ)⁻¹ • ∑ u : Index M, ∑ r : Index M,
          (F u * F (r - u) * convolutionKernel M u r) • residueD M r) := by
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        apply Fintype.sum_equiv (Equiv.addLeft u)
        intro v
        change (F u * F v) • (residueD M u * residueD M v) =
          (F u * F (u + v - u) * convolutionKernel M u (u + v)) • residueD M (u + v)
        have hm := residueD_mul_sub hM u (u + v)
        simp only [add_sub_cancel_left] at hm ⊢
        rw [hm, smul_smul]
      _ = (M : ℂ)⁻¹ • ∑ r : Index M,
          ((M : ℂ)⁻¹ * ∑ u : Index M, F u * F (r - u) * convolutionKernel M u r) •
            residueD M r := by
        rw [Finset.sum_comm]
        simp only [mul_smul, Finset.smul_sum, Finset.sum_smul]
      _ = _ := by simp_rw [convolution_eq_sum_index]
  rw [hprod]
  simp_rw [hA.convolution_eq]
  rw [P_eq_sum_residueD hM]
  simp [add_smul, ite_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    residueD_zero, hn, mul_comm, mul_left_comm, mul_assoc]

/-- Algebraic content of [RW26, Thm. 7], obtained from input A. -/
theorem P_quadratic {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) :
    (P M F - sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ)) *
      (P M F + (sqrtEpsilon M)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ)) = 0 := by
  have hν := sqrtEpsilon_ne_zero hM
  have hc := sqrtEpsilon_sub_inv hM
  have hprod := P_mul_P hM hA
  calc
    _ = (P M F * P M F - convolutionScalar M • P M F) - 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_smul]
      rw [← hc]
      simp only [sub_smul, mul_inv_cancel₀ hν, one_smul]
      match_scalars <;> simp [hν] <;> ring
    _ = 0 := by rw [hprod]; abel

theorem trace_P {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) : (P M F).trace = sqrtEpsilon M ^ 3 := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [P_eq_sum_residueD hM]
  simp only [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  simp_rw [trace_residueD hM]
  simp [mul_ite, hA.origin, hn, mul_assoc, mul_comm, mul_left_comm]

end SICLean.L2a
