import SICLean.L4.ModularDivisor
import SICLean.L4.ModularCocycle
import SICLean.L2r.Group
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.NumberTheory.Real.Irrational

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L2r

lemma rowAction_mul' (M N : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    rowAction (M * N) v = rowAction N (rowAction M v) := by
  ext <;> simp [rowAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma rowAction_one (v : ℤ × ℤ) : rowAction (1 : Matrix (Fin 2) (Fin 2) ℤ) v = v := by
  ext <;> simp [rowAction]

lemma rowAction_sub (M N : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    rowAction (M - N) v = rowAction M v - rowAction N v := by
  ext <;> simp [rowAction] <;> ring

lemma rowAction_smul (c : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    rowAction (c • M) v = c • rowAction M v := by
  ext <;> simp [rowAction] <;> ring

lemma rowAction_smul_right (c : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    rowAction M (c • v) = c • rowAction M v := by
  ext <;> simp [rowAction] <;> ring

lemma rowAction_sub_right (M : Matrix (Fin 2) (Fin 2) ℤ) (v w : ℤ × ℤ) :
    rowAction M (v - w) = rowAction M v - rowAction M w := by
  ext <;> simp [rowAction] <;> ring

end SICLean.L2r

namespace SICLean.L4

/-- Cayley--Hamilton for `M - 1`: `(M-1)^2 = (tr M - 2) • M`. -/
lemma sub_one_sq (M : SL(2,ℤ)) :
    ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) * ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) =
      (M 0 0 + M 1 1 - 2) • (M : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply] <;>
    nlinarith [det_coe_int M]

lemma rowAction_sub_one_sq (M : SL(2,ℤ)) (u : ℤ×ℤ) :
    L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
      (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u) =
      (M 0 0 + M 1 1 - 2) • L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u := by
  rw [← L2r.rowAction_mul', sub_one_sq, L2r.rowAction_smul]

lemma rowAction_sub_one_eq (M : SL(2,ℤ)) (u : ℤ×ℤ) :
    L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u =
      L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u := by
  rw [L2r.rowAction_sub, L2r.rowAction_one]

/-- Membership in the row lattice of `M - 1`, in the form used by [RW26, (3)]. -/
lemma rowLattice_sub_one_mem_iff (M : SL(2,ℤ)) (hN : 0 < M 0 0 + M 1 1 - 2) (u : ℤ×ℤ) :
    u ∈ L2r.rowLattice ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) ↔
      (M 0 0 + M 1 1 - 2) ∣ (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u).1 - u.1 ∧
      (M 0 0 + M 1 1 - 2) ∣ (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u).2 - u.2 := by
  constructor
  · intro hu
    change ∃ w, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w = u at hu
    obtain ⟨w, hw⟩ := hu
    have hs := rowAction_sub_one_sq M w
    rw [hw, rowAction_sub_one_eq] at hs
    constructor
    · exact ⟨(L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w).1, by simpa using congrArg Prod.fst hs⟩
    · exact ⟨(L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w).2, by simpa using congrArg Prod.snd hs⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨z1, hz1⟩ := h1
    obtain ⟨z2, hz2⟩ := h2
    let z : ℤ×ℤ := (z1, z2)
    have hz : L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u =
        (M 0 0 + M 1 1 - 2) • z := by
      ext
      · simp [z, rowAction_sub_one_eq, hz1]
      · simp [z, rowAction_sub_one_eq, hz2]
    have hsq := rowAction_sub_one_sq M u
    rw [hz, L2r.rowAction_smul_right] at hsq
    have hAz : L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) z =
        L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u := by
      ext
      · have := congrArg Prod.fst hsq
        simp at this ⊢
        omega
      · have := congrArg Prod.snd hsq
        simp at this ⊢
        omega
    change ∃ v, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) v = u
    refine ⟨z - u, ?_⟩
    rw [L2r.rowAction_sub_right, hAz, rowAction_sub_one_eq]
    abel

/-- `M - 1` and `M⁻¹ - 1` have the same row lattice. -/
lemma rowLattice_sub_one_inverse_eq (M : SL(2,ℤ)) :
    L2r.rowLattice ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) =
      L2r.rowLattice (((M⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) := by
  set A : Matrix (Fin 2) (Fin 2) ℤ := (M : Matrix (Fin 2) (Fin 2) ℤ) - 1 with hA
  set B : Matrix (Fin 2) (Fin 2) ℤ := ((M⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1 with hB
  set C : Matrix (Fin 2) (Fin 2) ℤ := -(((M⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) with hC
  set D : Matrix (Fin 2) (Fin 2) ℤ := -(M : Matrix (Fin 2) (Fin 2) ℤ) with hD
  have hmul : (((M⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * (M : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hBC : B = C * A := by
    rw [hB, hC, hA, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one, hmul]
    abel
  have hDA : A = D * B := by
    rw [hA, hB, hD, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one]
    have hmul' : (M : Matrix (Fin 2) (Fin 2) ℤ) * (((M⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [hmul']
    abel
  ext x
  change (∃ v, L2r.rowAction A v = x) ↔ ∃ v, L2r.rowAction B v = x
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨L2r.rowAction D v, ?_⟩
    rw [hDA, L2r.rowAction_mul'] at hv
    exact hv
  · rintro ⟨v, hv⟩
    refine ⟨L2r.rowAction C v, ?_⟩
    rw [hBC, L2r.rowAction_mul'] at hv
    exact hv

/-- The quotient `(ℤ×ℤ)/range(M-1)` has `|tr M - 2|` elements. -/
lemma natCard_rowLattice_sub_one (M : SL(2,ℤ)) (hNpos : 0 < M 0 0 + M 1 1 - 2) :
    Nat.card ((ℤ×ℤ) ⧸ L2r.rowLattice ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)) =
      Int.natAbs (M 0 0 + M 1 1 - 2) := by
  set A : Matrix (Fin 2) (Fin 2) ℤ := (M : Matrix (Fin 2) (Fin 2) ℤ) - 1 with hA
  let f : (ℤ×ℤ) →ₗ[ℤ] (ℤ×ℤ) := AddMonoidHom.toIntLinearMap (L2r.rowActionHom A)
  have hf : ⇑f = fun u => L2r.rowAction A u := by
    funext u; rfl
  have hdetA : A.det = 2 - (M 0 0 + M 1 1) := by
    rw [hA, Matrix.det_fin_two]
    simp [Matrix.sub_apply]
    linear_combination det_coe_int M
  have hmat : LinearMap.toMatrix (Module.Basis.finTwoProd ℤ) (Module.Basis.finTwoProd ℤ) f = A.transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [f, L2r.rowActionHom, L2r.rowAction, LinearMap.toMatrix_apply]
  have hdet : LinearMap.det f = A.det := by
    rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℤ), hmat, Matrix.det_transpose]
  have hdet_ne : A.det ≠ 0 := by
    rw [hdetA]
    omega
  let N : Submodule ℤ (ℤ×ℤ) := (L2r.rowLattice A).toIntSubmodule
  have hN : N = LinearMap.range f := by
    ext x
    rw [LinearMap.mem_range]
    constructor
    · intro hx
      change ∃ u, L2r.rowAction A u = x at hx
      obtain ⟨u, hu⟩ := hx
      exact ⟨u, by simpa [hf] using hu⟩
    · rintro ⟨u, hu⟩
      change ∃ v, L2r.rowAction A v = x
      exact ⟨u, by simpa [hf] using hu⟩
  have hdetf_ne : LinearMap.det f ≠ 0 := by
    rw [hdet]; exact hdet_ne
  have hker : LinearMap.ker f = ⊥ := by
    by_contra h
    exact hdetf_ne ((LinearMap.det_eq_zero_iff_ker_ne_bot (f := f)).mpr h)
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  let e : (ℤ×ℤ) ≃ₗ[ℤ] N := LinearEquiv.ofBijective (f.codRestrict N (by rw [hN]; exact LinearMap.mem_range_self f)) (by
    constructor
    · intro x y hxy
      exact hinj (Subtype.ext_iff.mp hxy)
    · intro y
      have hy : (y : ℤ×ℤ) ∈ LinearMap.range f := by rw [← hN]; exact y.2
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
      exact ⟨x, Subtype.ext hx⟩)
  have hmain := Submodule.natAbs_det_equiv N e.toAddEquiv
  have hcomp : (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e.toAddEquiv : (ℤ×ℤ) →+ N)) = f := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hcomp, hdet] at hmain
  rw [show (L2r.rowLattice A) = N.toAddSubgroup by simp [N]]
  have hq : Nat.card ((ℤ×ℤ) ⧸ N.toAddSubgroup) = Nat.card ((ℤ×ℤ) ⧸ N) := rfl
  rw [hq, ← hmain, hdetA]
  apply Nat.cast_injective (R := ℤ)
  omega

/-- `N(N+4)` is never a square for positive `N`. -/
lemma not_square_N_mul (N : ℤ) (hN : 0 < N) : ¬ IsSquare (N * (N + 4)) := by
  rintro ⟨m, hm⟩
  have h1 : (N+1)^2 < m^2 := by nlinarith
  have h2 : m^2 < (N+2)^2 := by nlinarith
  have habs1 : |N+1| < |m| := (sq_lt_sq.mp h1)
  have habs2 : |m| < |N+2| := (sq_lt_sq.mp h2)
  have hN1 : (0:ℤ) ≤ N+1 := by omega
  have hN2 : (0:ℤ) ≤ N+2 := by omega
  rw [abs_of_nonneg hN1] at habs1
  rw [abs_of_nonneg hN2] at habs2
  omega

/-- A rational linear relation with irrational coefficient has zero coefficients. -/
lemma int_linear_eq_zero {p q : ℤ} {τ : ℝ} (hτ : Irrational τ)
    (h : (p : ℝ) * τ + (q : ℝ) = 0) : p = 0 ∧ q = 0 := by
  rcases eq_or_ne p 0 with hp | hp
  · subst hp
    refine ⟨rfl, ?_⟩
    simpa using h
  · exfalso
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have hτeq : τ = (-(q : ℝ)) / (p : ℝ) := by
      field_simp
      linarith
    exact hτ.ne_rat ((-q : ℚ) / (p : ℚ)) (by
      rw [hτeq]
      push_cast
      ring)

end SICLean.L4
