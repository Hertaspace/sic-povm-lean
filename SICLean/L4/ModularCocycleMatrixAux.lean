import SICLean.L4.ModularPhi

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped Topology MatrixGroups UpperHalfPlane

namespace SICLean.L4.ModularCocycleMatrixAux

theorem denom_mul (M N : SL(2, ℤ)) (τ : ℂ) (hN : etaDenom N τ ≠ 0) :
    etaDenom (M * N) τ = etaDenom M (etaMobius N τ) * etaDenom N τ := by
  simp only [etaDenom, etaMobius, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul]
  unfold etaDenom at hN
  field_simp [hN]
  ring

theorem automorphy (M N : SL(2, ℤ)) (τ : ℂ)
    (hN : etaDenom N τ ≠ 0) (hM : etaDenom M (etaMobius N τ) ≠ 0) :
    etaDenom (M * N) τ = etaDenom M (etaMobius N τ) * etaDenom N τ ∧
    etaDenom (M * N) τ ≠ 0 ∧
    etaMobius (M * N) τ = etaMobius M (etaMobius N τ) := by
  have hd := denom_mul M N τ hN
  refine ⟨hd, by rw [hd]; exact mul_ne_zero hM hN, ?_⟩
  unfold etaMobius
  rw [hd]
  simp only [etaDenom, etaMobius, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] at *
  field_simp
  ring

theorem continuousAt_mobius (M : SL(2, ℤ)) (τ : ℂ) (h : etaDenom M τ ≠ 0) :
    ContinuousAt (etaMobius M) τ := by
  unfold etaMobius
  exact (continuous_const.mul continuous_id |>.add continuous_const).continuousAt.div
    (by unfold etaDenom; fun_prop) h

theorem denom_real_im (M : SL(2, ℤ)) (τ : ℝ) :
    (etaDenom M (τ : ℂ)).im = 0 := by
  simp [etaDenom]

theorem mobius_real_im (M : SL(2, ℤ)) (τ : ℝ) :
    (etaMobius M (τ : ℂ)).im = 0 := by
  simp [etaMobius, etaDenom, Complex.div_im]

theorem denom_mobius_real_im (M N : SL(2, ℤ)) (τ : ℝ) :
    (etaDenom M (etaMobius N (τ : ℂ))).im = 0 := by
  simp [etaDenom, mobius_real_im]

theorem domain_of_re_pos (M : SL(2, ℤ)) (τ : ℂ) (h : 0 < (etaDenom M τ).re) :
    τ ∈ modularPhiDomain M := by
  exact Complex.mem_slitPlane_iff.mpr (Or.inl h)

theorem denom_ne_zero_of_re_pos (M : SL(2, ℤ)) (τ : ℂ)
    (h : 0 < (etaDenom M τ).re) : etaDenom M τ ≠ 0 := by
  intro hz
  simp [hz] at h

theorem cocycleDomain_isOpen (M N : SL(2, ℤ)) :
    IsOpen {τ | τ ∈ modularPhiDomain N ∧
      etaMobius N τ ∈ modularPhiDomain M ∧ τ ∈ modularPhiDomain (M * N)} := by
  rw [isOpen_iff_mem_nhds]
  intro τ hτ
  have hn : etaDenom N τ ≠ 0 := Complex.slitPlane_ne_zero hτ.1
  have h₁ := (modularPhiDomain_isOpen N).mem_nhds hτ.1
  have h₂ := (continuousAt_mobius N τ hn).preimage_mem_nhds
    ((modularPhiDomain_isOpen M).mem_nhds hτ.2.1)
  have h₃ := (modularPhiDomain_isOpen (M * N)).mem_nhds hτ.2.2
  exact Filter.inter_mem h₁ (Filter.inter_mem h₂ h₃)

theorem cocycle_real_neighborhood (M N : SL(2, ℤ)) (τ₀ : ℝ)
    (hN : 0 < (etaDenom N (τ₀ : ℂ)).re)
    (hM : 0 < (etaDenom M (etaMobius N (τ₀ : ℂ))).re) :
    0 < (etaDenom (M * N) (τ₀ : ℂ)).re ∧
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (τ₀ : ℂ) δ ⊆
      {τ | τ ∈ modularPhiDomain N ∧
        etaMobius N τ ∈ modularPhiDomain M ∧ τ ∈ modularPhiDomain (M * N)} := by
  have hn := denom_ne_zero_of_re_pos N (τ₀ : ℂ) hN
  have hp : 0 < (etaDenom (M * N) (τ₀ : ℂ)).re := by
    rw [denom_mul M N (τ₀ : ℂ) hn, Complex.mul_re,
      denom_real_im N τ₀, mul_zero, sub_zero]
    exact mul_pos hM hN
  refine ⟨hp, ?_⟩
  exact Metric.isOpen_iff.mp (cocycleDomain_isOpen M N) _
    ⟨domain_of_re_pos N _ hN, domain_of_re_pos M _ hM, domain_of_re_pos (M * N) _ hp⟩

theorem pow_c_recurrence (M : SL(2, ℤ)) (n : ℕ) :
    (M ^ (n + 2)) 1 0 = (M 0 0 + M 1 1) * (M ^ (n + 1)) 1 0 - (M ^ n) 1 0 := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := det_coe_int M
  have h10 (P : SL(2, ℤ)) : (P * M) 1 0 = P 1 0 * M 0 0 + P 1 1 * M 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 (P : SL(2, ℤ)) : (P * M) 1 1 = P 1 0 * M 0 1 + P 1 1 * M 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, h10, pow_succ, h10, h11]
  nlinarith [congrArg (fun x : ℤ => x * (M ^ n) 1 0) hdet]

theorem pow_c_strict (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (n : ℕ) :
    0 ≤ (M ^ n) 1 0 ∧ (M ^ n) 1 0 < (M ^ (n + 1)) 1 0 := by
  induction n with
  | zero => simpa using And.intro (show (0 : ℤ) ≤ 0 from le_rfl) hM
  | succ n ih =>
    have hnpos : 0 < (M ^ (n + 1)) 1 0 := lt_of_le_of_lt ih.1 ih.2
    refine ⟨hnpos.le, ?_⟩
    rw [show n + 1 + 1 = n + 2 by omega, pow_c_recurrence]
    nlinarith

theorem pow_pos_c (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (r : ℕ) (hr : 0 < r) :
    0 < (M ^ r) 1 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have h := pow_c_strict M hM htrace n
  exact lt_of_le_of_lt h.1 h.2

theorem pow_fixedPoint (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) (r : ℕ) :
    etaMobius (M ^ r) (τ₀ : ℂ) = (τ₀ : ℂ) ∧
    etaDenom (M ^ r) (τ₀ : ℂ) = etaDenom M (τ₀ : ℂ) ^ r ∧
    0 < (etaDenom (M ^ r) (τ₀ : ℂ)).re := by
  induction r with
  | zero => simp [etaMobius, etaDenom]
  | succ r ih =>
    have hn := denom_ne_zero_of_re_pos (M ^ r) (τ₀ : ℂ) ih.2.2
    have hm := denom_ne_zero_of_re_pos M (τ₀ : ℂ) hT
    have ha := automorphy M (M ^ r) (τ₀ : ℂ) hn (by simpa [ih.1] using hm)
    rw [pow_succ']
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ih.1, hfix] using ha.2.2
    · rw [ha.1, ih.1, ih.2.1, pow_succ']
    · rw [ha.1, ih.1, Complex.mul_re, denom_real_im M τ₀, zero_mul, sub_zero]
      exact mul_pos hT ih.2.2

theorem inverse_reflection_denom (M R : SL(2, ℤ))
    (hR : (R : Matrix (Fin 2) (Fin 2) ℤ) = !![M 1 1, M 0 1; M 1 0, M 0 0])
    (τ : ℂ) (hτ : etaDenom M τ ≠ 0) :
    etaDenom R (-etaMobius M τ) = (etaDenom M τ)⁻¹ ∧
    etaMobius R (-etaMobius M τ) = -τ := by
  have hd : (M 0 0 : ℂ) * M 1 1 - (M 0 1 : ℂ) * M 1 0 = 1 := by
    exact_mod_cast det_coe_int M
  have hR00 : R 0 0 = M 1 1 := by simp [hR]
  have hR01 : R 0 1 = M 0 1 := by simp [hR]
  have hR10 : R 1 0 = M 1 0 := by simp [hR]
  have hR11 : R 1 1 = M 0 0 := by simp [hR]
  have hden : etaDenom R (-etaMobius M τ) = (etaDenom M τ)⁻¹ := by
    simp only [etaDenom, etaMobius, hR10, hR11]
    unfold etaDenom at hτ
    field_simp [hτ]
    linear_combination hd
  refine ⟨hden, ?_⟩
  change ((R 0 0 : ℂ) * (-etaMobius M τ) + (R 0 1 : ℂ)) /
    etaDenom R (-etaMobius M τ) = -τ
  rw [hden, hR00, hR01]
  rw [div_inv_eq_mul]
  rw [etaMobius, ← neg_div, add_mul, mul_assoc, div_mul_cancel₀ _ hτ]
  unfold etaDenom
  linear_combination -τ * hd

theorem inv_mem_slitPlane (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    z⁻¹ ∈ Complex.slitPlane := by
  have hn := Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero hz)
  rcases Complex.mem_slitPlane_iff.mp hz with hr | hi
  · exact Complex.mem_slitPlane_iff.mpr (Or.inl (by
      simpa [Complex.inv_re] using div_pos hr hn))
  · exact Complex.mem_slitPlane_iff.mpr (Or.inr (by
      simpa [Complex.inv_im] using div_ne_zero (neg_ne_zero.mpr hi) hn.ne'))

theorem a_sub_c_fixedPoint (M : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius M τ = τ) (hτ : etaDenom M τ ≠ 0) :
    (M 0 0 : ℂ) - (M 1 0 : ℂ) * τ = (etaDenom M τ)⁻¹ := by
  have hd : (M 0 0 : ℂ) * M 1 1 - (M 0 1 : ℂ) * M 1 0 = 1 := by
    exact_mod_cast det_coe_int M
  have hf : (M 0 0 : ℂ) * τ + M 0 1 = τ * etaDenom M τ := by
    exact (div_eq_iff hτ).mp hfix
  unfold etaDenom at *
  field_simp [hτ]
  linear_combination (M 1 0 : ℂ) * hf + hd

theorem c_mul_fixedPoint (M A : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius M τ = τ) (hτ : etaDenom M τ ≠ 0) :
    ((A * M) 1 0 : ℂ) = (A 1 0 : ℂ) * (etaDenom M τ)⁻¹ +
      (M 1 0 : ℂ) * etaDenom A τ := by
  rw [← a_sub_c_fixedPoint M τ hfix hτ]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Int.cast_add, Int.cast_mul, etaDenom]
  ring

theorem c_mul_pos_fixedPoint (M A : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hA : 0 ≤ A 1 0) (τ : ℝ)
    (hfix : etaMobius M (τ : ℂ) = (τ : ℂ))
    (hTM : 0 < (etaDenom M (τ : ℂ)).re)
    (hTA : 0 < (etaDenom A (τ : ℂ)).re) :
    0 < (A * M) 1 0 := by
  have hn := denom_ne_zero_of_re_pos M (τ : ℂ) hTM
  have heq := congrArg Complex.re (c_mul_fixedPoint M A (τ : ℂ) hfix hn)
  have hinv : 0 < ((etaDenom M (τ : ℂ))⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hTM (Complex.normSq_pos.mpr hn)
  have hAr : (0 : ℝ) ≤ (A 1 0 : ℝ) := by exact_mod_cast hA
  have hMr : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, zero_mul, sub_zero] at heq
  have hc : (0 : ℝ) < ((A * M) 1 0 : ℝ) := by
    rw [heq]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hAr hinv.le) (mul_pos hMr hTA)
  exact_mod_cast hc

theorem conjugate_fixedPoint (M A : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius M τ = τ)
    (hM : etaDenom M τ ≠ 0) (hA : etaDenom A τ ≠ 0) :
    etaMobius (A * M * A⁻¹) (etaMobius A τ) = etaMobius A τ ∧
    etaDenom (A * M * A⁻¹) (etaMobius A τ) = etaDenom M τ := by
  have hmat : A * M * A⁻¹ * A = A * M := by group
  have hden : etaDenom (A * M * A⁻¹) (etaMobius A τ) = etaDenom M τ := by
    have heq := congrArg (fun N => etaDenom N τ) hmat
    rw [denom_mul _ A _ hA, denom_mul A M _ hM, hfix] at heq
    apply mul_right_cancel₀ hA
    simpa only [mul_comm (etaDenom A τ) (etaDenom M τ)] using heq
  refine ⟨?_, hden⟩
  have hleft := (automorphy (A * M * A⁻¹) A τ hA (by rw [hden]; exact hM)).2.2
  have hright := (automorphy A M τ hM (by rw [hfix]; exact hA)).2.2
  rw [hmat, hright, hfix] at hleft
  exact hleft.symm

end SICLean.L4.ModularCocycleMatrixAux
