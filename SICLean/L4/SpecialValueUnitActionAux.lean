import SICLean.L4.SpecialValueGeometry

set_option autoImplicit false

/-!
# Helpers for the base action on the special-value row quotient

Commuting row actions preserve the row lattice in both directions. At a
fixed point, multiplication by the automorphy factor preserves the
pseudolattice, so division by its powers preserves its complement.
The latter gives continuity from the actual joint regularity theorem.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.SpecialValueUnitActionAux

private theorem fixedPoint_characteristic (M : SL(2, ℤ)) (τ : ℝ)
    (hfix : etaMobius M (τ : ℂ) = (τ : ℂ))
    (hT : ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) ≠ 0) :
    ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) ^ 2 -
      ((M 0 0 : ℝ) + (M 1 1 : ℝ)) *
        ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) + 1 = 0 := by
  have hd : (M 0 0 : ℝ) * (M 1 1 : ℝ) -
      (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    exact_mod_cast det_coe_int M
  have hden : etaDenom M (τ : ℂ) ≠ 0 := by
    simpa only [etaDenom, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, ne_eq, Complex.ofReal_eq_zero] using hT
  have hfC : (M 0 0 : ℂ) * (τ : ℂ) + (M 0 1 : ℂ) =
      (τ : ℂ) * ((M 1 0 : ℂ) * (τ : ℂ) + (M 1 1 : ℂ)) :=
    (div_eq_iff hden).mp hfix
  have hf : (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) =
      τ * ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) := by
    exact_mod_cast hfC
  linear_combination -(M 1 0 : ℝ) * hf - hd

private theorem fixedPoint_trace_gt_two (M : SL(2, ℤ)) (τ : ℝ)
    (hfix : etaMobius M (τ : ℂ) = (τ : ℂ))
    (hT : 1 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) :
    2 < M 0 0 + M 1 1 := by
  let t : ℝ := (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)
  have ht : 1 < t := hT
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have hc := fixedPoint_characteristic M τ hfix (ne_of_gt htpos)
  change t ^ 2 - ((M 0 0 : ℝ) + (M 1 1 : ℝ)) * t + 1 = 0 at hc
  have htrace : (2 : ℝ) < (M 0 0 : ℝ) + (M 1 1 : ℝ) := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) htpos.le
    nlinarith [sq_pos_of_pos (sub_pos.mpr ht)]
  exact_mod_cast htrace

private theorem pow_base_fixedPoint (A : SL(2, ℤ))
    (hA : SpecialValueAdmissible A) (k : ℕ) :
    etaMobius (A ^ k) (specialValueTau A : ℂ) = (specialValueTau A : ℂ) ∧
    etaDenom (A ^ k) (specialValueTau A : ℂ) =
      ((specialValueEpsilon A ^ k : ℝ) : ℂ) := by
  have hT : 0 < (etaDenom A (specialValueTau A : ℂ)).re := by
    rw [specialValue_etaDenom]
    simpa only [Complex.ofReal_re] using
      lt_trans zero_lt_one (specialValueEpsilon_gt_one A hA)
  have hp := ModularCocycleMatrixAux.pow_fixedPoint A (specialValueTau A)
    (specialValueTau_fixedPoint A hA) hT k
  refine ⟨hp.1, ?_⟩
  simpa only [specialValue_etaDenom, Complex.ofReal_pow] using hp.2.1

lemma pow_admissible (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (k : ℕ) (hk : 0 < k) : SpecialValueAdmissible (A ^ k) := by
  have hp := pow_base_fixedPoint A hA k
  refine ⟨modularPhi_pow_pos_c A hA.1 hA.2 k hk, ?_⟩
  apply fixedPoint_trace_gt_two (A ^ k) (specialValueTau A) hp.1
  have hreal := congrArg Complex.re hp.2
  simp only [etaDenom, Complex.add_re, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hreal
  rw [hreal]
  exact one_lt_pow₀ (specialValueEpsilon_gt_one A hA) (Nat.ne_of_gt hk)

private theorem attracting_unique (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (τ : ℝ)
    (hfix : etaMobius M (τ : ℂ) = (τ : ℂ))
    (hT : 1 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) :
    τ = specialValueTau M := by
  let t : ℝ := (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)
  let ε : ℝ := specialValueEpsilon M
  have ht : 1 < t := hT
  have hε : 1 < ε := specialValueEpsilon_gt_one M hM
  have htchar := fixedPoint_characteristic M τ hfix
    (ne_of_gt (lt_trans zero_lt_one ht))
  change t ^ 2 - ((M 0 0 : ℝ) + (M 1 1 : ℝ)) * t + 1 = 0 at htchar
  have hεchar : ε ^ 2 - ((M 0 0 : ℝ) + (M 1 1 : ℝ)) * ε + 1 = 0 := by
    simpa [ε, specialValueOrder] using specialValueEpsilon_characteristic M hM
  have hfactor : (t - ε) * (t * ε - 1) = 0 := by
    linear_combination ε * htchar - t * hεchar
  have hprod : t * ε - 1 ≠ 0 := by
    have hpos := mul_pos (sub_pos.mpr ht) (sub_pos.mpr hε)
    nlinarith
  have heq : t = ε := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hprod)
  have hc : (M 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hM.1)
  apply mul_left_cancel₀ hc
  dsimp [t, ε, specialValueEpsilon] at heq
  linarith

lemma tau_pow (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (k : ℕ) (hk : 0 < k) : specialValueTau (A ^ k) = specialValueTau A := by
  have hp := pow_base_fixedPoint A hA k
  apply (attracting_unique (A ^ k) (pow_admissible A hA k hk)
    (specialValueTau A) hp.1 ?_).symm
  have hreal := congrArg Complex.re hp.2
  simp only [etaDenom, Complex.add_re, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hreal
  rw [hreal]
  exact one_lt_pow₀ (specialValueEpsilon_gt_one A hA) (Nat.ne_of_gt hk)

lemma epsilon_pow (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (k : ℕ) (hk : 0 < k) : specialValueEpsilon (A ^ k) = specialValueEpsilon A ^ k := by
  apply Complex.ofReal_injective
  rw [← specialValue_etaDenom, tau_pow A hA k hk]
  exact (pow_base_fixedPoint A hA k).2

lemma rowAction_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (u : ℤ × ℤ) :
    L2r.rowAction (M * N) u = L2r.rowAction N (L2r.rowAction M u) := by
  ext <;> simp [L2r.rowAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma rowAction_one (u : ℤ × ℤ) :
    L2r.rowAction (1 : Matrix (Fin 2) (Fin 2) ℤ) u = u := by
  ext <;> simp [L2r.rowAction]

lemma row_vecMul (M : Matrix (Fin 2) (Fin 2) ℤ) (u : ℤ × ℤ) :
    Matrix.vecMul ![u.1, u.2] M =
      ![(L2r.rowAction M u).1, (L2r.rowAction M u).2] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, L2r.rowAction]

lemma rowLattice_stable (A : SL(2, ℤ)) (N : Matrix (Fin 2) (Fin 2) ℤ)
    (hcomm : Commute (A : Matrix (Fin 2) (Fin 2) ℤ) N)
    (u : ℤ × ℤ) (hu : u ∈ L2r.rowLattice N) :
    L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u ∈ L2r.rowLattice N := by
  rcases hu with ⟨w, hw⟩
  refine ⟨L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) w, ?_⟩
  change L2r.rowAction N (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) w) =
    L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u
  rw [← rowAction_mul, hcomm.eq, rowAction_mul]
  exact congrArg (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ)) hw

lemma base_mem_lattice_iff (A : SL(2, ℤ)) (k : ℕ) (u : ℤ × ℤ) :
    L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u ∈ specialValueLattice (A ^ k) ↔
      u ∈ specialValueLattice (A ^ k) := by
  have hc (B : SL(2, ℤ)) (hB : Commute B (A ^ k)) :
      Commute (B : Matrix (Fin 2) (Fin 2) ℤ)
        ((A ^ k : SL(2, ℤ)) - (1 : Matrix (Fin 2) (Fin 2) ℤ)) := by
    unfold Commute SemiconjBy
    rw [mul_sub, sub_mul, mul_one, one_mul]
    exact congrArg (fun C : SL(2, ℤ) => (C : Matrix (Fin 2) (Fin 2) ℤ)) hB.eq
      |> fun h => congrArg (fun C => C - (B : Matrix (Fin 2) (Fin 2) ℤ)) h
  constructor
  · intro hu
    have h := rowLattice_stable A⁻¹ _ (hc A⁻¹ (Commute.self_pow A k).inv_left) _ hu
    rw [← rowAction_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, rowAction_one] at h
    exact h
  · exact rowLattice_stable A _ (hc A (Commute.self_pow A k)) u

lemma row_sub_self_mem (A : SL(2, ℤ)) (u : ℤ × ℤ) :
    L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) u - u ∈ specialValueLattice A := by
  refine ⟨u, ?_⟩
  change L2r.rowAction ((A : Matrix (Fin 2) (Fin 2) ℤ) - 1) u = _
  ext <;> simp [L2r.rowAction, Matrix.sub_apply] <;> ring

lemma pseudoLattice_mul (A : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius A τ = τ) (hT : etaDenom A τ ≠ 0)
    (z : ℂ) (hz : z ∈ modularPhiPseudoLattice τ) :
    etaDenom A τ * z ∈ modularPhiPseudoLattice τ := by
  rcases hz with ⟨a, b, rfl⟩
  refine ⟨(L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) (a, b)).1,
    (L2r.rowAction (A : Matrix (Fin 2) (Fin 2) ℤ) (a, b)).2, ?_⟩
  have h := ModularCocycleUnitAux.row_fixedPoint A ![a, b] τ hfix hT
  rw [row_vecMul (A : Matrix (Fin 2) (Fin 2) ℤ) (a, b)] at h
  exact h.symm

lemma pseudoLattice_pow_mul (A : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius A τ = τ) (hT : etaDenom A τ ≠ 0)
    (z : ℂ) (hz : z ∈ modularPhiPseudoLattice τ) (j : ℕ) :
    etaDenom A τ ^ j * z ∈ modularPhiPseudoLattice τ := by
  induction j with
  | zero => simpa using hz
  | succ j ih =>
    simpa only [pow_succ', mul_assoc] using
      pseudoLattice_mul A τ hfix hT _ ih

lemma div_pow_not_mem_pseudoLattice (A : SL(2, ℤ)) (τ : ℂ)
    (hfix : etaMobius A τ = τ) (hT : etaDenom A τ ≠ 0)
    (z : ℂ) (hz : z ∉ modularPhiPseudoLattice τ) (j : ℕ) :
    z / etaDenom A τ ^ j ∉ modularPhiPseudoLattice τ := by
  intro h
  have hm := pseudoLattice_pow_mul A τ hfix hT _ h j
  rw [mul_div_cancel₀ _ (pow_ne_zero j hT)] at hm
  exact hz hm

lemma continuousAt_off_pseudoLattice (A : SL(2, ℤ)) (hA : SpecialValueAdmissible A)
    (m n : ℤ) (z : ℂ)
    (hz : z ∉ modularPhiPseudoLattice (specialValueTau A : ℂ)) :
    ContinuousAt (fun w => modularPhi A m n w (specialValueTau A : ℂ)) z := by
  have hT : 0 < (A 1 0 : ℝ) * specialValueTau A + (A 1 1 : ℝ) :=
    lt_trans zero_lt_one (specialValueEpsilon_gt_one A hA)
  have hp := modularPhi_real_off_lattice A hA.1 m n (specialValueTau A) hT z hz
  obtain ⟨U, _, hpU, _, hanalytic, _⟩ :=
    modularPhi_joint_unit_neighborhood A hA.1 m n _ hp
  exact (hanalytic _ hpU).continuousAt.comp
    (f := fun w : ℂ => (w, (specialValueTau A : ℂ)))
    (continuousAt_id.prodMk continuousAt_const)

end SICLean.L4.SpecialValueUnitActionAux
