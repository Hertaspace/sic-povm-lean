import SICLean.L2a.Algebra

/-! # Periodic phased displacements and finite sums

The phase and displacement separately depend on an integer lift. Their product
descends to `Index M`; all changes of lift below use that product.
-/

noncomputable section

open Matrix

namespace SICLean.L2a

def phasedD (M : ℕ) (i j : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
  theta M i j • D M (toWH i j)

def residueD (M : ℕ) (h : Index M) : Matrix (Fin M) (Fin M) ℂ :=
  phasedD M h.1.val h.2.val

def indexEquiv (M : ℕ) [NeZero M] : (Fin M × Fin M) ≃ Index M where
  toFun p := ((p.1 : ℕ), (p.2 : ℕ))
  invFun h := (finIdx M h.1, finIdx M h.2)
  left_inv p := by
    apply Prod.ext <;> apply fin_ext_of_label <;> apply label_finIdx
  right_inv h := by
    exact Prod.ext (label_finIdx M h.1) (label_finIdx M h.2)

theorem sum_fin_index {M : ℕ} [NeZero M] {A : Type*} [AddCommMonoid A]
    (f : Index M → A) :
    (∑ i : Fin M, ∑ j : Fin M, f ((i : ℕ), (j : ℕ))) = ∑ h : Index M, f h := by
  rw [← Fintype.sum_prod_type']
  exact (indexEquiv M).sum_comp f

theorem phasedD_eq_of_cast_eq {M : ℕ} (hM : 4 ≤ M) (i j k l : ℤ)
    (hi : (i : ZMod M) = (k : ZMod M)) (hj : (j : ZMod M) = (l : ZMod M)) :
    phasedD M i j = phasedD M k l := by
  obtain ⟨a, ha⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub k i M).mp hi.symm
  obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub l j M).mp hj.symm
  have hi' : i = k + (M : ℤ) * a := by linear_combination ha
  have hj' : j = l + (M : ℤ) * b := by linear_combination hb
  rw [hi', hj']
  exact phased_displacement_add_period hM k l a b

theorem residueD_eq_phasedD {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
    residueD M ((i : ZMod M), (j : ZMod M)) = phasedD M i j := by
  haveI : NeZero M := ⟨by omega⟩
  apply phasedD_eq_of_cast_eq hM <;> simp

theorem phasedD_zero (M : ℕ) : phasedD M 0 0 = 1 := by
  simp [phasedD, theta_eq_xi_zpow, quadraticForm, toWH, D_zero]

theorem residueD_zero (M : ℕ) : residueD M 0 = 1 := by
  simpa [residueD] using phasedD_zero M

/-- The product cocycle in the form used by the convolution in [RW26]. -/
theorem phasedD_mul (M : ℕ) (i j r s : ℤ) :
    phasedD M i j * phasedD M (r - i) (s - j) =
      (gaussianLift M i j * e M (-i * r + j * (r - s))) • phasedD M r s := by
  simp only [phasedD, Matrix.smul_mul, Matrix.mul_smul, D_mul_D, smul_smul]
  have ht : toWH i j + toWH (r - i) (s - j) = toWH r s := by
    ext <;> simp [toWH] <;> ring
  rw [ht]
  congr 1
  simp only [theta_eq_xi_zpow, gaussianLift, e_eq_omega_zpow, omega_zpow,
    ← zpow_add₀ (xi_ne_zero M)]
  congr 1
  dsimp [quadraticForm, toWH]
  ring

theorem P_eq_sum_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M) (F : Values M) :
    P M F = (M : ℂ)⁻¹ • ∑ h : Index M, F h • residueD M h := by
  rw [P, ← sum_fin_index]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [residueD, ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt,
    phasedD, valueAt, smul_smul, Int.cast_natCast, mul_comm]

theorem isZeroLabel_iff_cast {M : ℕ} (i j : ℤ) :
    IsZeroLabel M (i, j) ↔ ((i : ZMod M), (j : ZMod M)) = 0 := by
  change (_ ∧ _) ↔ ((i : ZMod M), (j : ZMod M)) = (0, 0)
  simp only [IsZeroLabel, Prod.mk.injEq, Prod.fst_zero, Prod.snd_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem isZeroLabel_toWH {M : ℕ} (i j : ℤ) :
    IsZeroLabel M (toWH i j) ↔ IsZeroLabel M (i, j) := by
  simp only [IsZeroLabel, toWH, dvd_neg, and_comm]

def convolutionKernel (M : ℕ) (u r : Index M) : ℂ :=
  gaussianLift M u.1.val u.2.val *
    e M (-(u.1.val : ℤ) * r.1.val + (u.2.val : ℤ) * (r.1.val - r.2.val))

theorem residueD_mul_sub {M : ℕ} [NeZero M] (hM : 4 ≤ M) (u r : Index M) :
    residueD M u * residueD M (r - u) =
      convolutionKernel M u r • residueD M r := by
  have hr : r - u =
      ((((r.1.val : ℤ) - u.1.val : ℤ) : ZMod M),
        (((r.2.val : ℤ) - u.2.val : ℤ) : ZMod M)) := by
    ext <;> simp
  rw [hr, residueD_eq_phasedD hM]
  exact phasedD_mul M u.1.val u.2.val r.1.val r.2.val

theorem convolution_eq_sum_index {M : ℕ} [NeZero M] (F : Values M) (r : Index M) :
    convolution M F r.1.val r.2.val =
      (M : ℂ)⁻¹ * ∑ u : Index M, F u * F (r - u) * convolutionKernel M u r := by
  rcases r with ⟨r, s⟩
  rw [convolution, ← sum_fin_index]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [valueAt, convolutionKernel, ZMod.val_cast_of_lt i.isLt,
    ZMod.val_cast_of_lt j.isLt, mul_assoc]

theorem trace_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M) (h : Index M) :
    (residueD M h).trace = if h = 0 then (M : ℂ) else 0 := by
  classical
  by_cases hh : h = 0
  · simp [hh, residueD_zero, Matrix.trace_one]
  · have hz : ¬ IsZeroLabel M (toWH h.1.val h.2.val) := by
      rw [isZeroLabel_toWH, isZeroLabel_iff_cast]
      simpa using hh
    rw [residueD, phasedD, Matrix.trace_smul, trace_D, if_neg hz, if_neg hh]
    simp

theorem ov_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M)
    (h : Index M) (i j : ℤ) :
    ov M (residueD M h) (toWH i j) =
      if h = ((i : ZMod M), (j : ZMod M)) then theta M i j * (M : ℂ) else 0 := by
  classical
  by_cases hh : h = ((i : ZMod M), (j : ZMod M))
  · rw [hh, residueD_eq_phasedD hM]
    simp [ov, phasedD, Matrix.smul_mul, D_mul_conjTranspose_D, Matrix.trace_smul,
      Matrix.trace_one]
  · have hz : ¬ IsZeroLabel M (toWH h.1.val h.2.val + -(toWH i j)) := by
      intro hz
      apply hh
      have hz' := (isZeroLabel_iff_cast _ _).mp hz
      have h₁ := congrArg Prod.fst hz'
      have h₂ := congrArg Prod.snd hz'
      simp [toWH] at h₁ h₂
      apply Prod.ext <;> dsimp
      · linear_combination h₂
      · linear_combination -h₁
    rw [residueD, phasedD, ov, Matrix.smul_mul, conjTranspose_D, D_mul_D,
      Matrix.trace_smul, Matrix.trace_smul, trace_D, if_neg hz, if_neg hh]
    simp

theorem ov_P_toWH {M : ℕ} (hM : 4 ≤ M) (F : Values M) (i j : ℤ) :
    ov M (P M F) (toWH i j) = theta M i j * valueAt F i j := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [P_eq_sum_residueD hM]
  simp only [ov, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
    smul_eq_mul]
  change (M : ℂ)⁻¹ * ∑ h : Index M, F h * ov M (residueD M h) (toWH i j) = _
  simp_rw [ov_residueD hM]
  simp [mul_ite, Finset.sum_ite_eq', valueAt, hn, mul_comm, mul_left_comm, mul_assoc]

end SICLean.L2a
