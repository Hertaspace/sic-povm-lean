import SICLean.L4.SpecialValueUnitAction
import SICLean.L2c.Inputs

set_option autoImplicit false

/-!
# Auxiliary arithmetic

Elementary determinant, entry and real-algebra facts for the original
base `α = ((M-1,-1),(1,0))` and its cube `γ`. Nothing here is analytic;
these feed `SpecialValueL2c`.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L4

theorem alpha_det_one (M : ℕ) : (L2b.alpha M).det = 1 := by
  simp only [L2b.alpha, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem gamma_apply00 (M : ℕ) [Fact (4 ≤ M)] :
    L2b.gamma M 0 0 = (M : ℤ) * ((M : ℤ) ^ 2 - 3 * (M : ℤ) + 1) + 1 := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 0) (L2b.gamma_sub_one (M := M))
  simp [L2b.gammaMinusOne] at h
  linarith

theorem gamma_apply01 (M : ℕ) [Fact (4 ≤ M)] :
    L2b.gamma M 0 1 = -((M : ℤ) * ((M : ℤ) - 2)) := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 1) (L2b.gamma_sub_one (M := M))
  simp [L2b.gammaMinusOne] at h
  linarith

theorem gamma_apply10 (M : ℕ) [Fact (4 ≤ M)] :
    L2b.gamma M 1 0 = (M : ℤ) * ((M : ℤ) - 2) := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 1 0) (L2b.gamma_sub_one (M := M))
  simp [L2b.gammaMinusOne] at h
  linarith

theorem gamma_apply11 (M : ℕ) [Fact (4 ≤ M)] :
    L2b.gamma M 1 1 = -((M : ℤ) - 1) := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 1 1) (L2b.gamma_sub_one (M := M))
  simp [L2b.gammaMinusOne] at h
  linarith

theorem epsilon_char (M : ℕ) [Fact (4 ≤ M)] :
    L2a.epsilon M ^ 2 - ((M : ℝ) - 1) * L2a.epsilon M + 1 = 0 := by
  have h4 : (4 : ℝ) ≤ M := by exact_mod_cast Fact.out
  have hs : (Real.sqrt (((M : ℝ) - 1) ^ 2 - 4)) ^ 2 = ((M : ℝ) - 1) ^ 2 - 4 :=
    Real.sq_sqrt (by nlinarith)
  rw [L2a.epsilon]
  field_simp
  nlinarith [hs]

theorem epsilon_gt_one (M : ℕ) [Fact (4 ≤ M)] : 1 < L2a.epsilon M := by
  have h4 : (4 : ℝ) ≤ M := by exact_mod_cast Fact.out
  have hs : 0 ≤ Real.sqrt (((M : ℝ) - 1) ^ 2 - 4) := Real.sqrt_nonneg _
  rw [L2a.epsilon]
  nlinarith


theorem epsilon_cube_eq (M : ℕ) [Fact (4 ≤ M)] :
    L2a.epsilon M ^ 3 =
      (((L2b.groupOrder M : ℝ) + 2 +
        Real.sqrt ((L2b.groupOrder M : ℝ) ^ 2 + 4 * (L2b.groupOrder M : ℝ))) / 2) := by
  set e : ℝ := L2a.epsilon M with he
  set N : ℝ := (L2b.groupOrder M : ℝ) with hNdef
  set a : ℝ := (M : ℝ) - 1 with ha
  have h4 : (4 : ℝ) ≤ M := by exact_mod_cast Fact.out
  have hepos : 0 < e := by rw [he]; linarith [epsilon_gt_one M]
  have hchar : e ^ 2 - a * e + 1 = 0 := by rw [he, ha]; exact epsilon_char M
  have hN : N = (M : ℝ) ^ 2 * ((M : ℝ) - 3) := by
    rw [hNdef]
    simp only [L2b.groupOrder, L2b.cofactor, Nat.cast_mul, Nat.cast_pow]
    congr 1
    exact Nat.cast_sub (by have := Fact.out (p := 4 ≤ M); omega : 3 ≤ M)
  have hNa : N + 2 = a ^ 3 - 3 * a := by
    rw [hN, ha]; ring
  have hsum : e + e⁻¹ = a := by
    have he0 : e ≠ 0 := ne_of_gt hepos
    field_simp [he0]
    nlinarith [hchar]
  have hcube : e ^ 3 + (e ^ 3)⁻¹ = a ^ 3 - 3 * a := by
    have h : e ^ 3 + (e ^ 3)⁻¹ = (e + e⁻¹) ^ 3 - 3 * (e + e⁻¹) := by
      field_simp
      ring
    rw [hsum] at h
    exact h
  have hcubeN : e ^ 3 + (e ^ 3)⁻¹ = N + 2 := by rw [hcube, hNa]
  have he3pos : 0 < e ^ 3 - (e ^ 3)⁻¹ := by
    have he1 : 1 < e := by rw [he]; exact epsilon_gt_one M
    have h1 : 1 < e ^ 3 := by nlinarith
    have h2 : (e ^ 3)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  have hdiff : (e ^ 3 - (e ^ 3)⁻¹) ^ 2 = N ^ 2 + 4 * N := by
    have hx : e ^ 3 * (e ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt (pow_pos hepos 3))
    have hexp : (e ^ 3 - (e ^ 3)⁻¹) ^ 2 =
        (e ^ 3 + (e ^ 3)⁻¹) ^ 2 - 4 * (e ^ 3 * (e ^ 3)⁻¹) := by ring
    rw [hexp, hx, hcubeN]
    ring
  have hsqrt : Real.sqrt (N ^ 2 + 4 * N) = e ^ 3 - (e ^ 3)⁻¹ := by
    rw [← hdiff, Real.sqrt_sq (le_of_lt he3pos)]
  rw [hsqrt]
  rw [show (N + 2 + (e ^ 3 - (e ^ 3)⁻¹)) / 2 = e ^ 3 by
    rw [← hcubeN]; ring]

/-- The cube relation used to invert ε at the fixed point:
`ε³ + (M-1) = M(M-2) ε`. -/
theorem epsilon_cube_relation (M : ℕ) [Fact (4 ≤ M)] :
    L2a.epsilon M ^ 3 + ((M : ℝ) - 1) = (M : ℝ) * ((M : ℝ) - 2) * L2a.epsilon M := by
  set e : ℝ := L2a.epsilon M with he
  set a : ℝ := (M : ℝ) - 1 with ha
  have hchar : e ^ 2 - a * e + 1 = 0 := by rw [he, ha]; exact epsilon_char M
  have hsq : e ^ 2 = a * e - 1 := by linarith
  have hcube : e ^ 3 = (a ^ 2 - 1) * e - a := by
    calc e ^ 3 = e * e ^ 2 := by ring
      _ = e * (a * e - 1) := by rw [hsq]
      _ = a * e ^ 2 - e := by ring
      _ = a * (a * e - 1) - e := by rw [hsq]
      _ = (a ^ 2 - 1) * e - a := by ring
  have ha2 : a ^ 2 - 1 = (M : ℝ) * ((M : ℝ) - 2) := by rw [ha]; ring
  rw [hcube, ha2, ha]
  ring


theorem epsilon_cube_inv_eq (M : ℕ) [Fact (4 ≤ M)] :
    (L2a.epsilon M ^ 3)⁻¹ =
      (((L2b.groupOrder M : ℝ) + 2 -
        Real.sqrt ((L2b.groupOrder M : ℝ) ^ 2 + 4 * (L2b.groupOrder M : ℝ))) / 2) := by
  set e : ℝ := L2a.epsilon M with he
  set N : ℝ := (L2b.groupOrder M : ℝ) with hNdef
  set s : ℝ := Real.sqrt (N ^ 2 + 4 * N) with hsdef
  have hNnonneg : 0 ≤ N := by rw [hNdef]; positivity
  have hssq : s ^ 2 = N ^ 2 + 4 * N := by
    rw [hsdef]; exact Real.sq_sqrt (by nlinarith)
  have heq : ((N + 2 + s) / 2) = e ^ 3 := by
    have h := epsilon_cube_eq M
    rw [← hNdef, ← hsdef] at h
    exact h.symm
  have hepos : 0 < e := lt_trans zero_lt_one (by rw [he]; exact epsilon_gt_one M)
  have he3pos : 0 < e ^ 3 := pow_pos hepos 3
  have hprod : ((N + 2 + s) / 2) * ((N + 2 - s) / 2) = 1 := by
    field_simp
    nlinarith [hssq]
  have hne : ((N + 2 + s) / 2) ≠ 0 := by rw [heq]; exact ne_of_gt he3pos
  have hone : ((N + 2 + s) / 2) * (e ^ 3)⁻¹ = 1 := by
    rw [heq]; exact mul_inv_cancel₀ (ne_of_gt he3pos)
  have hEq : ((N + 2 - s) / 2) = (e ^ 3)⁻¹ := by
    apply mul_left_cancel₀ hne
    rw [hprod, hone]
  exact hEq.symm

end SICLean.L4
