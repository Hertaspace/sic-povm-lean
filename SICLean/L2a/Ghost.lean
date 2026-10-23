import SICLean.L2a.Quadratic

/-! # From Input A to the ghost and its exact overlap formula -/

noncomputable section

open Matrix

namespace SICLean.L2a

theorem denominator_sq {M : ℕ} (hM : 4 ≤ M) :
    denominator M ^ 2 = (M : ℂ) + 1 := by
  rw [denominator_eq_sqrt hM]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
  exact_mod_cast hs

theorem rsicConst_one {M : ℕ} (hM : 4 ≤ M) :
    rsicConst M 1 = ((M : ℝ) + 1)⁻¹ := by
  have hm : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hn : (M : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  simp only [rsicConst, Nat.cast_one, one_mul]
  field_simp
  <;> ring

theorem ghostProjector_idempotent {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) :
    ghostProjector M F * ghostProjector M F = ghostProjector M F := by
  have hs := denominator_ne_zero hM
  have hq :
      (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) *
          (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) =
        denominator M • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) := by
    have he :
        (P M F - sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ)) *
            (P M F + (sqrtEpsilon M)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ)) =
          (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) *
              (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) -
            denominator M • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, denominator]
      module
    rw [P_quadratic hM hA] at he
    exact sub_eq_zero.mp he.symm
  simp only [ghostProjector, Matrix.smul_mul, Matrix.mul_smul, hq, smul_smul]
  simp [mul_assoc, hs]

theorem trace_ghostProjector {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) : (ghostProjector M F).trace = 1 := by
  have hs := denominator_ne_zero hM
  have ht : sqrtEpsilon M * (M : ℂ) - sqrtEpsilon M ^ 3 = denominator M := by
    rw [sqrtEpsilon_cube hM, denominator]
    ring
  simp only [ghostProjector, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, trace_P hM hA]
  rw [ht, inv_mul_cancel₀ hs]

theorem ghostProjector_residue_expansion {M : ℕ} [NeZero M] (hM : 4 ≤ M)
    {F : Values M} (hA : RWConvolutionInput M F) :
    ghostProjector M F = (M : ℂ)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ) +
      (M : ℂ)⁻¹ • ∑ h : Index M,
        if h = 0 then 0 else (-F h / denominator M) • residueD M h := by
  classical
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hs := denominator_ne_zero hM
  have ht : (M : ℂ) * sqrtEpsilon M - sqrtEpsilon M ^ 3 = denominator M := by
    rw [sqrtEpsilon_cube hM, denominator]
    ring
  have hall : (∑ h : Index M, (-F h / denominator M) • residueD M h) =
      (-(denominator M)⁻¹) • ∑ h : Index M, F h • residueD M h := by
    simp only [Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    ring
  have hterm (h : Index M) :
      (if h = 0 then 0 else (-F h / denominator M) • residueD M h) =
        (-F h / denominator M) • residueD M h -
          if h = 0 then (-F 0 / denominator M) • residueD M 0 else 0 := by
    by_cases hh : h = 0 <;> simp [hh]
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, residueD_zero, hA.origin, hall]
  rw [ghostProjector, P_eq_sum_residueD hM]
  match_scalars <;> field_simp [hn, hs] <;> linear_combination ht

theorem ghostProjector_expansion {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) :
    ghostProjector M F = (M : ℂ)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ) +
      (M : ℂ)⁻¹ • ∑ i : Fin M, ∑ j : Fin M,
        if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 0
        else coefficient M F i j • D M (toWH i j) := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  rw [ghostProjector_residue_expansion hM hA, ← sum_fin_index]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hz : (((i : ℕ) : ZMod M), ((j : ℕ) : ZMod M)) = (0 : Index M) ↔
      (i : ℕ) = 0 ∧ (j : ℕ) = 0 := by
    change ((_, _) = (0, 0)) ↔ _
    simp only [Prod.mk.injEq, ZMod.natCast_eq_zero_iff]
    constructor
    · rintro ⟨hi, hj⟩
      exact ⟨Nat.eq_zero_of_dvd_of_lt hi i.isLt, Nat.eq_zero_of_dvd_of_lt hj j.isLt⟩
    · rintro ⟨hi, hj⟩
      simp [hi, hj]
  rw [if_congr hz rfl rfl]
  split_ifs
  · rfl
  · simp only [residueD, ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt,
      phasedD, coefficient, valueAt, Int.cast_natCast, smul_smul]
    congr 1
    ring

/-- Opposites here are integer opposites. Canonical residue representatives
may differ by a sign in even dimension. -/
theorem coefficient_mul_neg {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) (i j : ℤ) (hij : ¬ IsZeroLabel M (i, j)) :
    coefficient M F i j * coefficient M F (-i) (-j) = ((M : ℂ) + 1)⁻¹ := by
  have hh : ((i : ZMod M), (j : ZMod M)) ≠ 0 :=
    mt (isZeroLabel_iff_cast i j).mpr hij
  have hr := hA.reflection ((i : ZMod M), (j : ZMod M)) hh
  have hr' : valueAt F i j * valueAt F (-i) (-j) = (gaussianLift M i j)⁻¹ := by
    simpa only [valueAt, Prod.neg_mk, Int.cast_neg, gaussian_eq_lift hM] using hr
  have hg : gaussianLift M i j ≠ 0 := Complex.exp_ne_zero _
  rw [coefficient, coefficient, theta_neg]
  calc
    _ = (theta M i j ^ 2 * (valueAt F i j * valueAt F (-i) (-j))) /
        denominator M ^ 2 := by ring
    _ = _ := by rw [theta_sq, hr', denominator_sq hM, mul_inv_cancel₀ hg, one_div]

theorem coefficient_add_period {M : ℕ} (hM : 4 ≤ M) (F : Values M) (i j a b : ℤ) :
    coefficient M F (i + (M : ℤ) * a) (j + (M : ℤ) * b) =
      (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * coefficient M F i j := by
  unfold coefficient
  rw [theta_add_period hM]
  have hv : valueAt F (i + (M : ℤ) * a) (j + (M : ℤ) * b) = valueAt F i j := by
    simp [valueAt]
  rw [hv]
  ring

/-- Exact coefficients of the overlaps `ov` = Tr(Π̃ D_pᴴ) of `SICLean.Defs`, for all integer labels.
-/
theorem ov_ghostProjector {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) (p : ℤ × ℤ) (hp : ¬ IsZeroLabel M p) :
    ov M (ghostProjector M F) p = coefficient M F (fromWH p).1 (fromWH p).2 := by
  haveI : NeZero M := ⟨by omega⟩
  have hpneg : ¬ IsZeroLabel M (-p) := by simpa [IsZeroLabel] using hp
  have hov := ov_P_toWH hM F (fromWH p).1 (fromWH p).2
  have hback : toWH (fromWH p).1 (fromWH p).2 = p := by simp [toWH, fromWH]
  rw [hback] at hov
  simp only [ghostProjector, ov, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  rw [conjTranspose_D, trace_D, if_neg hpneg]
  rw [← conjTranspose_D p]
  change (denominator M)⁻¹ * (sqrtEpsilon M * 0 - ov M (P M F) p) = _
  rw [hov]
  simp [coefficient, div_eq_mul_inv, mul_comm]

theorem ov_ghostProjector_mul_neg {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) (p : ℤ × ℤ) (hp : ¬ IsZeroLabel M p) :
    ov M (ghostProjector M F) p * ov M (ghostProjector M F) (-p) =
      (rsicConst M 1 : ℂ) := by
  have hpneg : ¬ IsZeroLabel M (-p) := by simpa [IsZeroLabel] using hp
  have hf : ¬ IsZeroLabel M ((fromWH p).1, (fromWH p).2) := by
    simpa [fromWH, IsZeroLabel, and_comm] using hp
  rw [ov_ghostProjector hM hA p hp, ov_ghostProjector hM hA (-p) hpneg]
  change coefficient M F (fromWH p).1 (fromWH p).2 *
      coefficient M F (-(fromWH p).1) (-(fromWH p).2) = _
  rw [coefficient_mul_neg hM hA _ _ hf, rsicConst_one hM]
  push_cast
  rfl

theorem isGhost_of_RW {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) : IsGhost M 1 (ghostProjector M F) := by
  exact ⟨ghostProjector_idempotent hM hA, by simpa using trace_ghostProjector hM hA,
    ov_ghostProjector_mul_neg hM hA⟩

end SICLean.L2a
