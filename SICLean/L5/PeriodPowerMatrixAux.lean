import SICLean.L5.PeriodPowerData
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

noncomputable section
open Complex Set Filter
open scoped Topology MatrixGroups BigOperators Classical UpperHalfPlane

namespace SICLean.L5.PeriodPowerMatrixAux

open L4

/-- Evaluation of an integer row at the fixed basis `(tau, 1)`. -/
def rowEval (τ : ℂ) : (ℤ × ℤ) →+ ℂ where
  toFun u := (u.1 : ℂ) * τ + (u.2 : ℂ)
  map_zero' := by simp
  map_add' := by intro u v; simp; ring

lemma rowEval_matrix (A : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius A τ = τ) (hT : etaDenom A τ ≠ 0) (u : ℤ × ℤ) :
    rowEval τ (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u) =
      etaDenom A τ * rowEval τ u := by
  simpa only [SpecialValueUnitActionAux.row_vecMul, Matrix.cons_val_zero,
    Matrix.cons_val_one, rowEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using
    ModularCocycleUnitAux.row_fixedPoint A ![u.1, u.2] τ hfix hT

lemma rowEval_inverse (A : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius A τ = τ) (hT : etaDenom A τ ≠ 0) (u : ℤ × ℤ) :
    rowEval τ (L2r.rowAction ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u) =
      (etaDenom A τ)⁻¹ * rowEval τ u := by
  apply (mul_left_cancel₀ hT)
  rw [mul_inv_cancel_left₀ hT]
  have h := rowEval_matrix A τ hfix hT
    (L2r.rowAction ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) u)
  rw [← L2r.rowAction_mul', ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, L2r.rowAction_one] at h
  exact h.symm

lemma rowEval_inverse_difference (A : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius A τ = τ) (hT : etaDenom A τ ≠ 0) (u : ℤ × ℤ) :
    rowEval τ (L2r.rowAction
      (((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) u) =
      ((etaDenom A τ)⁻¹ - 1) * rowEval τ u := by
  rw [L2r.rowAction_sub, L2r.rowAction_one, map_sub, rowEval_inverse A τ hfix hT]
  ring

lemma sum_matrix_difference (A : SL(2, ℤ)) (r : ℕ) :
    (∑ j ∈ Finset.range r,
      ((A⁻¹ ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
        (((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) =
      (((A ^ r)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1 := by
  simpa only [← inv_pow, Matrix.SpecialLinearGroup.coe_pow] using
    geom_sum_mul ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) r

lemma rowAction_add (M N : Matrix (Fin 2) (Fin 2) ℤ) (u : ℤ × ℤ) :
    L2r.rowAction (M + N) u = L2r.rowAction M u + L2r.rowAction N u := by
  ext <;> simp [L2r.rowAction] <;> ring

/-- A local spelling of the row sum, independent of the public matrix module. -/
def sumRow (A : SL(2, ℤ)) (r : ℕ) (u : ℤ × ℤ) : ℤ × ℤ :=
  L2r.rowAction (∑ j ∈ Finset.range r,
    ((A⁻¹ ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) u

lemma sumRow_zero (A : SL(2, ℤ)) (u : ℤ × ℤ) : sumRow A 0 u = 0 := by
  simp [sumRow, L2r.rowAction]

lemma sumRow_succ (A : SL(2, ℤ)) (j : ℕ) (u : ℤ × ℤ) :
    sumRow A (j + 1) u = u +
      L2r.rowAction ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (sumRow A j u) := by
  have hsum :
      (∑ k ∈ Finset.range (j + 1),
        ((A⁻¹ ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) =
      (∑ k ∈ Finset.range j,
        ((A⁻¹ ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
          ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) + 1 := by
    simp only [Matrix.SpecialLinearGroup.coe_pow, Finset.sum_range_succ', pow_succ,
      ← Finset.sum_mul, pow_zero]
  rw [sumRow, hsum, rowAction_add, L2r.rowAction_mul', L2r.rowAction_one, add_comm]
  rfl

lemma sumRow_first_index (A : SL(2, ℤ)) (j : ℕ) (u : ℤ × ℤ) :
    A 1 1 * (sumRow A j u).1 - A 1 0 * (sumRow A j u).2 =
      (sumRow A (j + 1) u).1 - u.1 := by
  rw [sumRow_succ]
  simp [L2r.rowAction, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ring

lemma sumRow_translation (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (j : ℕ) (u : ℤ × ℤ) :
    specialValueArgument A u / etaDenom A (specialValueTau A : ℂ) ^ j =
      specialValueArgument A u +
        ((sumRow A j u).1 : ℂ) * (specialValueTau A : ℂ) +
        ((sumRow A j u).2 : ℂ) := by
  let τ : ℂ := (specialValueTau A : ℂ)
  let ε : ℂ := etaDenom A τ
  have hε : ε ≠ 0 := by
    dsimp [ε, τ]
    rw [specialValue_etaDenom]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_trans zero_lt_one (specialValueEpsilon_gt_one A hA)))
  have hε1 : ε ≠ 1 := by
    dsimp only [ε, τ]
    rw [specialValue_etaDenom]
    exact_mod_cast (ne_of_gt (specialValueEpsilon_gt_one A hA))
  have hbalance : specialValueArgument A u / ε =
      specialValueArgument A u + rowEval τ u := by
    change rowEval τ u / (ε⁻¹ - 1) / ε =
      rowEval τ u / (ε⁻¹ - 1) + rowEval τ u
    field_simp [hε, sub_ne_zero.mpr hε1, sub_ne_zero.mpr hε1.symm]
    ring
  have h (k : ℕ) : specialValueArgument A u / ε ^ k =
      specialValueArgument A u + rowEval τ (sumRow A k u) := by
    induction k with
    | zero => simp [sumRow_zero]
    | succ k ih =>
      rw [pow_succ, ← div_div, ih, add_div, hbalance, sumRow_succ, map_add,
        rowEval_inverse A τ (specialValueTau_fixedPoint A hA) hε]
      simp only [div_eq_mul_inv]
      ring
  simpa only [rowEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_assoc] using h j

/-- The geometric row sum labels the identical complex argument. -/
lemma argument_sum (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) (u : ℤ × ℤ) :
    specialValueArgument (A ^ r)
      (L2r.rowAction (∑ j ∈ Finset.range r,
        ((A⁻¹ ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) u) =
      specialValueArgument A u := by
  let τ : ℂ := (specialValueTau A : ℂ)
  have hAr := specialValue_pow_admissible A hA r hr
  have hτ := specialValueTau_pow A hA r hr
  have hT : etaDenom A τ ≠ 0 := by
    rw [specialValue_etaDenom]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_trans zero_lt_one (specialValueEpsilon_gt_one A hA)))
  have hTr : etaDenom (A ^ r) τ ≠ 0 := by
    dsimp only [τ]
    rw [← hτ, specialValue_etaDenom]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_trans zero_lt_one (specialValueEpsilon_gt_one (A ^ r) hAr)))
  have hfixr : etaMobius (A ^ r) τ = τ := by
    simpa only [hτ] using specialValueTau_fixedPoint (A ^ r) hAr
  have hd : (etaDenom A τ)⁻¹ - 1 ≠ 0 := by
    rw [specialValue_etaDenom, sub_ne_zero]
    exact inv_ne_one.mpr (by
      exact_mod_cast (ne_of_gt (specialValueEpsilon_gt_one A hA)))
  have hdr : (etaDenom (A ^ r) τ)⁻¹ - 1 ≠ 0 := by
    dsimp only [τ]
    rw [← hτ, specialValue_etaDenom, sub_ne_zero]
    exact inv_ne_one.mpr (by
      exact_mod_cast (ne_of_gt (specialValueEpsilon_gt_one (A ^ r) hAr)))
  have heq := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ =>
    rowEval τ (L2r.rowAction M u)) (sum_matrix_difference A r)
  rw [L2r.rowAction_mul',
    rowEval_inverse_difference A τ (specialValueTau_fixedPoint A hA) hT,
    rowEval_inverse_difference (A ^ r) τ hfixr hTr] at heq
  simp only [specialValueArgument, modularPhiSpecialArgument, hτ]
  change rowEval τ _ / ((etaDenom (A ^ r) τ)⁻¹ - 1) =
    rowEval τ u / ((etaDenom A τ)⁻¹ - 1)
  apply (div_eq_div_iff hdr hd).mpr
  simpa only [mul_comm] using heq

/-- Equality on the upper half-plane extends to a real point of continuity. -/
lemma real_boundary_eq (τ₀ : ℝ) (F G : ℂ → ℂ)
    (hF : ContinuousAt F (τ₀ : ℂ)) (hG : ContinuousAt G (τ₀ : ℂ))
    (hEq : ∀ z : ℍ, F z = G z) : F (τ₀ : ℂ) = G (τ₀ : ℂ) := by
  let z : ℝ → ℂ := fun y => (τ₀ : ℂ) + (y : ℂ) * Complex.I
  have hz : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 (τ₀ : ℂ)) := by
    have hc : ContinuousAt z 0 := by dsimp [z]; fun_prop
    simpa only [z, Complex.ofReal_zero, zero_mul, add_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun y => F (z y)) =ᶠ[𝓝[>] (0 : ℝ)] (fun y => G (z y)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hzy : 0 < (z y).im := by simpa [z] using hy
    exact hEq ⟨z y, hzy⟩
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl _)
  exact tendsto_nhds_unique (hF.tendsto.comp hz)
    ((hG.tendsto.comp hz).congr' heq.symm)

lemma sqrt_ofReal_mul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Complex.sqrt ((x : ℂ) * (y : ℂ)) =
      Complex.sqrt (x : ℂ) * Complex.sqrt (y : ℂ) := by
  rw [← Complex.ofReal_mul,
    Complex.sqrt_of_nonneg (by exact_mod_cast mul_nonneg hx hy),
    Complex.sqrt_of_nonneg (by exact_mod_cast hx),
    Complex.sqrt_of_nonneg (by exact_mod_cast hy)]
  simp only [Complex.ofReal_re]
  rw [Real.sqrt_mul hx, Complex.ofReal_mul]

/-- Positive automorphy factors remove the square-root sign in the eta cocycle. -/
lemma etaMultiplier_mul_of_fixedPoint (M N : SL(2, ℤ))
    (hM : 0 < M 1 0) (hN : 0 < N 1 0) (hMN : 0 < (M * N) 1 0)
    (τ₀ : ℝ) (hfix : etaMobius N (τ₀ : ℂ) = (τ₀ : ℂ))
    (hTM : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hTN : 0 < (N 1 0 : ℝ) * τ₀ + (N 1 1 : ℝ)) :
    etaMultiplier (M * N) = etaMultiplier M * etaMultiplier N := by
  have hcancel (τ : ℍ) :
      etaMultiplier (M * N) * Complex.sqrt (etaDenom (M * N) τ) =
        etaMultiplier M * etaMultiplier N *
          Complex.sqrt (etaDenom M (etaMobius N τ)) *
          Complex.sqrt (etaDenom N τ) := by
    have h1 := eta_smul_eq (M * N) hMN τ
    have h2 := eta_smul_eq M hM (N • τ)
    have h3 := eta_smul_eq N hN τ
    rw [mul_smul, h2, h3] at h1
    simp only [coe_smul_eq_etaMobius] at h1
    apply mul_right_cancel₀ (ModularForm.eta_ne_zero τ.im_pos)
    calc
      _ = etaMultiplier M * Complex.sqrt (etaDenom M (etaMobius N τ)) *
          (etaMultiplier N * Complex.sqrt (etaDenom N τ) * ModularForm.eta τ) :=
        h1.symm
      _ = _ := by ring
  have hDMre : 0 < (etaDenom M (τ₀ : ℂ)).re := by
    simpa [etaDenom] using hTM
  have hDNre : 0 < (etaDenom N (τ₀ : ℂ)).re := by
    simpa [etaDenom] using hTN
  have hDNne :=
    ModularCocycleMatrixAux.denom_ne_zero_of_re_pos N (τ₀ : ℂ) hDNre
  have hprod : etaDenom (M * N) (τ₀ : ℂ) =
      etaDenom M (τ₀ : ℂ) * etaDenom N (τ₀ : ℂ) := by
    rw [ModularCocycleMatrixAux.denom_mul M N (τ₀ : ℂ) hDNne, hfix]
  have hDMNre : 0 < (etaDenom (M * N) (τ₀ : ℂ)).re := by
    rw [hprod, Complex.mul_re, ModularCocycleMatrixAux.denom_real_im N τ₀,
      mul_zero, sub_zero]
    exact mul_pos hDMre hDNre
  have hcdenom (P : SL(2, ℤ)) : Continuous (etaDenom P) := by
    unfold etaDenom
    fun_prop
  have hsMN : ContinuousAt
      (fun z => Complex.sqrt (etaDenom (M * N) z)) (τ₀ : ℂ) :=
    (Complex.continuousAt_sqrt (Or.inl hDMNre.le)).comp
      (hcdenom _).continuousAt
  have hsN : ContinuousAt
      (fun z => Complex.sqrt (etaDenom N z)) (τ₀ : ℂ) :=
    (Complex.continuousAt_sqrt (Or.inl hDNre.le)).comp
      (hcdenom _).continuousAt
  have hsM : ContinuousAt
      (fun z => Complex.sqrt (etaDenom M (etaMobius N z))) (τ₀ : ℂ) := by
    apply (Complex.continuousAt_sqrt
      (Or.inl (by rw [hfix]; exact hDMre.le))).comp
    exact (hcdenom M).continuousAt.comp
      (ModularCocycleMatrixAux.continuousAt_mobius N (τ₀ : ℂ) hDNne)
  have heq := real_boundary_eq τ₀
    (fun z => etaMultiplier (M * N) * Complex.sqrt (etaDenom (M * N) z))
    (fun z => etaMultiplier M * etaMultiplier N *
      Complex.sqrt (etaDenom M (etaMobius N z)) *
      Complex.sqrt (etaDenom N z))
    (continuousAt_const.mul hsMN)
    ((continuousAt_const.mul hsM).mul hsN) hcancel
  rw [hfix] at heq
  have hsprod : Complex.sqrt (etaDenom (M * N) (τ₀ : ℂ)) =
      Complex.sqrt (etaDenom M (τ₀ : ℂ)) *
        Complex.sqrt (etaDenom N (τ₀ : ℂ)) := by
    rw [hprod]
    simpa [etaDenom] using sqrt_ofReal_mul _ _ hTM.le hTN.le
  have hsMne : Complex.sqrt (etaDenom M (τ₀ : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl
        (ModularCocycleMatrixAux.denom_ne_zero_of_re_pos M (τ₀ : ℂ) hDMre))
  have hsNne : Complex.sqrt (etaDenom N (τ₀ : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hDNne)
  apply mul_right_cancel₀ (mul_ne_zero hsMne hsNne)
  simpa only [hsprod, mul_assoc] using heq

lemma etaMultiplier_pow (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) :
    etaMultiplier (A ^ r) = etaMultiplier A ^ r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  clear hr
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 < n + 1 := Nat.succ_pos n
    have hAn := specialValue_pow_admissible A hA (n + 1) hn
    have hNext :=
      specialValue_pow_admissible A hA (n + 1 + 1) (Nat.succ_pos _)
    have hprod : 0 < (A * A ^ (n + 1)) 1 0 := by
      simpa only [pow_succ'] using hNext.1
    have hfix : etaMobius (A ^ (n + 1)) (specialValueTau A : ℂ) =
        (specialValueTau A : ℂ) := by
      simpa only [specialValueTau_pow A hA (n + 1) hn] using
        specialValueTau_fixedPoint (A ^ (n + 1)) hAn
    have hTA : 0 < (A 1 0 : ℝ) * specialValueTau A + (A 1 1 : ℝ) :=
      lt_trans zero_lt_one (specialValueEpsilon_gt_one A hA)
    have hTAn : 0 < ((A ^ (n + 1)) 1 0 : ℝ) * specialValueTau A +
        ((A ^ (n + 1)) 1 1 : ℝ) := by
      have he := specialValueEpsilon_gt_one (A ^ (n + 1)) hAn
      unfold specialValueEpsilon at he
      rw [specialValueTau_pow A hA (n + 1) hn] at he
      exact lt_trans zero_lt_one he
    calc
      etaMultiplier (A ^ (n + 1 + 1)) =
          etaMultiplier (A * A ^ (n + 1)) := by rw [pow_succ']
      _ = etaMultiplier A * etaMultiplier (A ^ (n + 1)) :=
        etaMultiplier_mul_of_fixedPoint A (A ^ (n + 1)) hA.1 hAn.1 hprod
          (specialValueTau A) hfix hTA hTAn
      _ = etaMultiplier A * etaMultiplier A ^ (n + 1) := by rw [ih]
      _ = etaMultiplier A ^ (n + 1 + 1) := (pow_succ' _ _).symm

/-- Nonlattice iteration with all centers justified by the existing divisor theorem. -/
lemma phi_power_of_chain (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (r : ℕ) (hr : 0 < r) (u : ℤ × ℤ) (hu : u ∉ specialValueLattice A)
    (v : ℕ → ℤ × ℤ) (hv0 : v 0 = 0)
    (hstep : ∀ j, A 1 1 * (v j).1 - A 1 0 * (v j).2 = (v (j + 1)).1 - u.1)
    (htrans : ∀ j, specialValueArgument A u / etaDenom A (specialValueTau A : ℂ) ^ j =
      specialValueArgument A u + ((v j).1 : ℂ) * (specialValueTau A : ℂ) + ((v j).2 : ℂ))
    (harg : specialValueArgument (A ^ r) (v r) = specialValueArgument A u) :
    modularPhi (A ^ r) (v r).1 0 (specialValueArgument (A ^ r) (v r))
        (specialValueTau (A ^ r) : ℂ) =
      modularPhi A u.1 0 (specialValueArgument A u) (specialValueTau A : ℂ) ^ r := by
  let z := specialValueArgument A u
  let P := (v r).1
  let ι : ℕ → ℤ := fun j => P - (v j).1
  have hAr := specialValue_pow_admissible A hA r hr
  have hτ := specialValueTau_pow A hA r hr
  have hz : z ∉ modularPhiPseudoLattice (specialValueTau A : ℂ) :=
    (specialValueArgument_mem_lattice_iff A hA u).not.mpr hu
  have hvr : v r ∉ specialValueLattice (A ^ r) := by
    intro h
    have hp := (specialValueArgument_mem_lattice_iff (A ^ r) hAr (v r)).mpr h
    rw [harg, hτ] at hp
    exact hz hp
  have hT : 0 < (etaDenom A (specialValueTau A : ℂ)).re := by
    rw [specialValue_etaDenom, Complex.ofReal_re]
    exact lt_trans zero_lt_one (specialValueEpsilon_gt_one A hA)
  have hTne : etaDenom A (specialValueTau A : ℂ) ≠ 0 := by
    rw [specialValue_etaDenom]
    exact SpecialValueDescentAux.epsilon_ne_zero A hA
  have hi0 : ι 0 = P := by simp [ι, hv0]
  have hir : ι r = 0 := by simp [ι, P]
  have hit := modularPhi_iterate_fixedPoint A hA.1 hA.2 ι r z (specialValueTau A)
    (specialValueTau_fixedPoint A hA) hT
    (by
      have hc := SpecialValueDescentAux.continuous_phi (A ^ r) hAr (v r) hvr (ι 0) (ι r)
      simpa only [modularPhiConstructed, if_pos hAr.1, hτ, harg] using hc)
    (by
      intro j hj
      have hmem := SpecialValueUnitActionAux.div_pow_not_mem_pseudoLattice A _
        (specialValueTau_fixedPoint A hA) hTne z hz j
      have hc := SpecialValueUnitActionAux.continuousAt_off_pseudoLattice A hA
        (ι j) (ι (j + 1)) _ hmem
      exact hc.comp (f := fun w : ℂ => w / etaDenom A (specialValueTau A : ℂ) ^ j)
        (continuousAt_id.div_const _))
  have hdiag : modularPhi A P (P - u.1) z (specialValueTau A : ℂ) =
      modularPhi A u.1 0 z (specialValueTau A : ℂ) := by
    have hh := modularPhi_diagonal_index_fixedPoint A hA.1 u.1 0 (P - u.1)
      z (specialValueTau A) (specialValueTau_fixedPoint A hA) hT
      (by simpa only [zpow_zero, one_mul, specialValue_etaDenom] using
        SpecialValueDescentAux.phase A hA u)
      (SpecialValueDescentAux.index_factors_ne_zero A hA u hu)
      (SpecialValueDescentAux.continuous_phi A hA u hu (u.1 + (P - u.1)) (0 + (P - u.1)))
      (SpecialValueDescentAux.continuous_phi A hA u hu u.1 0)
    have hm : u.1 + (P - u.1) = P := by ring
    simpa only [hm, zero_add] using hh
  have hfactor (j : ℕ) : modularPhi A (ι j) (ι (j + 1))
      (z / etaDenom A (specialValueTau A : ℂ) ^ j) (specialValueTau A : ℂ) =
      modularPhi A u.1 0 z (specialValueTau A : ℂ) := by
    rw [show z / etaDenom A (specialValueTau A : ℂ) ^ j =
      z + ((v j).1 : ℂ) * (specialValueTau A : ℂ) + ((v j).2 : ℂ) from htrans j]
    rw [modularPhi_shift_integer A hA.1]
    have hm : ι j + (v j).1 = P := by dsimp [ι]; ring
    have hn : ι (j + 1) + A 1 1 * (v j).1 - A 1 0 * (v j).2 = P - u.1 := by
      dsimp only [ι]
      linear_combination hstep j
    rw [hm, hn]
    exact hdiag
  calc
    modularPhi (A ^ r) (v r).1 0 (specialValueArgument (A ^ r) (v r))
        (specialValueTau (A ^ r) : ℂ) =
        ∏ j ∈ Finset.range r, modularPhi A (ι j) (ι (j + 1))
          (z / etaDenom A (specialValueTau A : ℂ) ^ j) (specialValueTau A : ℂ) := by
      simpa only [modularPhiConstructed, if_pos hAr.1, hτ, harg, hi0, hir] using hit
    _ = ∏ _j ∈ Finset.range r, modularPhi A u.1 0 z (specialValueTau A : ℂ) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hfactor j
    _ = modularPhi A u.1 0 (specialValueArgument A u) (specialValueTau A : ℂ) ^ r := by simp [z]

end SICLean.L5.PeriodPowerMatrixAux
