import SICLean.L3.Pseudolattice
import SICLean.L4.DistributionLattice
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Int.GCD

set_option autoImplicit false

/-!
Arithmetic construction of an admissible basis.
Period stability produces a totally positive lattice vector. Removing
the gcd of its integer coordinates makes it primitive, and Bézout
extends it to a basis. The two real embeddings then identify the
determinant of the period action as ε ε⁻¹ = 1.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L3

universe u

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
private theorem basis_pair_expansion {I : Submodule ℤ K}
    (b : Module.Basis (Fin 2) ℤ I) (x : I) :
    (x : K) = (b.repr x 0 : K) * (b 0 : K) +
      (b.repr x 1 : K) * (b 1 : K) := by
  have h := congrArg (fun y : I => (y : K)) (b.sum_repr x)
  simpa only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul,
    zsmul_eq_mul] using h.symm

private theorem epsilon_mul_mem (P : PeriodData K) (I : StablePseudolattice P)
    {x : K} (hx : x ∈ I.val) : P.epsilon * x ∈ I.val := by
  rw [← I.property.2]
  exact (pseudolatticeScale_mem_iff P.epsilon _ I.val).mpr ⟨x, hx, rfl⟩

private def epsilonMap (P : PeriodData K) (I : StablePseudolattice P) : I.val →ₗ[ℤ] I.val where
  toFun x := ⟨P.epsilon * x, epsilon_mul_mem P I x.property⟩
  map_add' x y := by ext; simp [mul_add]
  map_smul' n x := by ext; simp [zsmul_eq_mul, mul_left_comm]

private theorem epsilonMap_apply (P : PeriodData K) (I : StablePseudolattice P)
    (x : I.val) : (epsilonMap P I x : K) = P.epsilon * x := rfl

private theorem basis_embedding_det_ne_zero (P : PeriodData K)
    (I : StablePseudolattice P) (b : Module.Basis (Fin 2) ℤ I.val) :
    P.sigma₁ (b 0) * P.sigma₂ (b 1) - P.sigma₂ (b 0) * P.sigma₁ (b 1) ≠ 0 := by
  let z : K := b 0
  have hz : z ≠ 0 := by
    intro hz
    exact b.ne_zero 0 (Subtype.ext hz)
  have hz₁ : P.sigma₁ z ≠ 0 := (map_ne_zero P.sigma₁).mpr hz
  have hz₂ : P.sigma₂ z ≠ 0 := (map_ne_zero P.sigma₂).mpr hz
  have he : 0 < P.sigma₁ P.epsilon := lt_trans zero_lt_one P.epsilon_gt_one
  have hei : (P.sigma₁ P.epsilon)⁻¹ < 1 := (inv_lt_one₀ he).mpr P.epsilon_gt_one
  have hd : P.sigma₁ P.epsilon - (P.sigma₁ P.epsilon)⁻¹ ≠ 0 := by linarith [P.epsilon_gt_one]
  have hexp := basis_pair_expansion b (epsilonMap P I (b 0))
  have h₁ := congrArg P.sigma₁ hexp
  have h₂ := congrArg P.sigma₂ hexp
  simp only [epsilonMap_apply, map_mul, map_add, map_intCast, P.epsilon_conj] at h₁ h₂
  intro hdet
  have hp : (P.sigma₁ P.epsilon - (P.sigma₁ P.epsilon)⁻¹) *
      P.sigma₁ z * P.sigma₂ z = 0 := by
    dsimp [z] at *
    have hmul := congrArg₂
      (fun r s : ℝ => r * P.sigma₂ (b 0) - s * P.sigma₁ (b 0)) h₁ h₂
    linear_combination hmul - (b.repr (epsilonMap P I (b 0)) 1 : ℝ) * hdet
  exact mul_ne_zero (mul_ne_zero hd hz₁) hz₂ hp

private theorem exists_totallyPositive_mem (P : PeriodData K)
    (I : StablePseudolattice P) (b : Module.Basis (Fin 2) ℤ I.val) :
    ∃ x : I.val, 0 < P.sigma₁ x ∧ 0 < P.sigma₂ x := by
  let z : I.val := b 0
  have hz : (z : K) ≠ 0 := by
    intro hz
    exact b.ne_zero 0 (Subtype.ext hz)
  have hz₁ : P.sigma₁ (z : K) ≠ 0 := (map_ne_zero P.sigma₁).mpr hz
  have hz₂ : P.sigma₂ (z : K) ≠ 0 := (map_ne_zero P.sigma₂).mpr hz
  have he : 0 < P.sigma₁ P.epsilon := lt_trans zero_lt_one P.epsilon_gt_one
  have hei : (P.sigma₁ P.epsilon)⁻¹ < 1 := (inv_lt_one₀ he).mpr P.epsilon_gt_one
  let w : I.val := epsilonMap P I z - z
  have hw₁ : P.sigma₁ (w : K) = (P.sigma₁ P.epsilon - 1) * P.sigma₁ z := by
    simp [w, epsilonMap_apply, sub_mul]
  have hw₂ : P.sigma₂ (w : K) = ((P.sigma₁ P.epsilon)⁻¹ - 1) * P.sigma₂ z := by
    simp [w, epsilonMap_apply, P.epsilon_conj, sub_mul]
  rcases lt_or_gt_of_ne hz₁ with h₁ | h₁
  · rcases lt_or_gt_of_ne hz₂ with h₂ | h₂
    · exact ⟨-z, by simpa using neg_pos.mpr h₁, by simpa using neg_pos.mpr h₂⟩
    · refine ⟨-w, ?_, ?_⟩
      · simpa only [Submodule.coe_neg, map_neg, neg_pos] using
          (hw₁ ▸ mul_neg_of_pos_of_neg (sub_pos.mpr P.epsilon_gt_one) h₁)
      · simpa only [Submodule.coe_neg, map_neg, neg_pos] using
          (hw₂ ▸ mul_neg_of_neg_of_pos (sub_neg.mpr hei) h₂)
  · rcases lt_or_gt_of_ne hz₂ with h₂ | h₂
    · refine ⟨w, ?_, ?_⟩
      · rw [hw₁]; exact mul_pos (sub_pos.mpr P.epsilon_gt_one) h₁
      · rw [hw₂]; exact mul_pos_of_neg_of_neg (sub_neg.mpr hei) h₂
    · exact ⟨z, h₁, h₂⟩

omit [NumberField K] in
private theorem exists_basis_pair_of_det_unit {I : Submodule ℤ K}
    (b : Module.Basis (Fin 2) ℤ I) (r s t v : ℤ)
    (hdet : IsUnit (r * v - s * t)) :
    ∃ c : Module.Basis (Fin 2) ℤ I,
      c 0 = r • b 0 + t • b 1 ∧ c 1 = s • b 0 + v • b 1 := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![r, s; t, v]
  have hA : IsUnit A.det := by simpa [A, Matrix.det_fin_two] using hdet
  let c := b.map (Matrix.toLinearEquiv b A hA)
  refine ⟨c, ?_, ?_⟩
  · simp [c, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLin_apply, Matrix.mulVec, dotProduct, A, Fin.sum_univ_two]
  · simp [c, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLin_apply, Matrix.mulVec, dotProduct, A, Fin.sum_univ_two]

private theorem exists_basis_totallyPositive_second (P : PeriodData K)
    (I : StablePseudolattice P) :
    ∃ b : Module.Basis (Fin 2) ℤ I.val,
      0 < P.sigma₁ (b 1) ∧ 0 < P.sigma₂ (b 1) := by
  obtain ⟨b⟩ := pseudolattice_exists_basis P I.val I.property.1
  obtain ⟨x, hx₁, hx₂⟩ := exists_totallyPositive_mem P I b
  let m : ℤ := b.repr x 0
  let n : ℤ := b.repr x 1
  have hg : 0 < Int.gcd m n := by
    by_contra h
    have hg0 : Int.gcd m n = 0 := by omega
    have hm : m = 0 := (Int.gcd_eq_zero_iff.mp hg0).1
    have hn : n = 0 := (Int.gcd_eq_zero_iff.mp hg0).2
    have hx := basis_pair_expansion b x
    change (x : K) = (m : K) * (b 0 : K) + (n : K) * (b 1 : K) at hx
    simp only [hm, hn, Int.cast_zero, zero_mul, add_zero] at hx
    have : P.sigma₁ (x : K) = 0 := by rw [hx, map_zero]
    linarith
  obtain ⟨a, d, had, hm, hn⟩ := Int.exists_gcd_one hg
  let u : ℤ := Int.gcdA a d
  let v : ℤ := Int.gcdB a d
  have hbez : a * u + d * v = 1 := by
    simpa [u, v, had] using (Int.gcd_eq_gcd_ab a d).symm
  have hunit : IsUnit (v * d - a * (-u)) := by
    have h : v * d - a * (-u) = 1 := by nlinarith [hbez]
    rw [h]
    exact isUnit_one
  obtain ⟨c, hc₀, hc₁⟩ := exists_basis_pair_of_det_unit b v a (-u) d hunit
  have hx : (x : K) = (Int.gcd m n : K) * (c 1 : K) := by
    rw [basis_pair_expansion b x, hc₁]
    simp only [Submodule.coe_add, Submodule.coe_smul, zsmul_eq_mul]
    change (m : K) * (b 0 : K) + (n : K) * (b 1 : K) = _
    have hmK : (m : K) = (a : K) * (Int.gcd m n : K) := by exact_mod_cast hm
    have hnK : (n : K) = (d : K) * (Int.gcd m n : K) := by exact_mod_cast hn
    rw [hmK, hnK]
    ring
  have hgr : (0 : ℝ) < Int.gcd m n := by exact_mod_cast hg
  refine ⟨c, ?_, ?_⟩
  · have h := congrArg P.sigma₁ hx
    simp only [map_mul, map_natCast] at h
    exact (mul_pos_iff_of_pos_left hgr).mp (h ▸ hx₁)
  · have h := congrArg P.sigma₂ hx
    simp only [map_mul, map_natCast] at h
    exact (mul_pos_iff_of_pos_left hgr).mp (h ▸ hx₂)

private theorem exists_admissible_pseudolattice_basis (P : PeriodData K)
    (I : StablePseudolattice P) :
    ∃ b : Module.Basis (Fin 2) ℤ I.val,
      0 < P.sigma₁ (b 1) ∧ 0 < P.sigma₂ (b 1) ∧
      0 < P.sigma₁ (b 0) * P.sigma₂ (b 1) -
        P.sigma₂ (b 0) * P.sigma₁ (b 1) := by
  obtain ⟨b, hb₁, hb₂⟩ := exists_basis_totallyPositive_second P I
  have hd := basis_embedding_det_ne_zero P I b
  rcases lt_or_gt_of_ne hd with hd | hd
  · obtain ⟨c, hc₀, hc₁⟩ := exists_basis_pair_of_det_unit b (-1) 0 0 1 (by norm_num)
    have hc₀' : c 0 = -b 0 := by simpa using hc₀
    have hc₁' : c 1 = b 1 := by simpa using hc₁
    refine ⟨c, hc₁'.symm ▸ hb₁, hc₁'.symm ▸ hb₂, ?_⟩
    simp only [hc₀', hc₁', Submodule.coe_neg, map_neg, neg_mul]
    linarith
  · exact ⟨b, hb₁, hb₂, hd⟩

private theorem epsilon_embedding_equation (P : PeriodData K)
    (I : StablePseudolattice P) (b : Module.Basis (Fin 2) ℤ I.val)
    (σ : K →+* ℝ) (i : Fin 2) :
    σ P.epsilon * σ (b i) =
      (b.repr (epsilonMap P I (b i)) 0 : ℝ) * σ (b 0) +
      (b.repr (epsilonMap P I (b i)) 1 : ℝ) * σ (b 1) := by
  have h := congrArg σ (basis_pair_expansion b (epsilonMap P I (b i)))
  simpa only [epsilonMap_apply, map_mul, map_add, map_intCast] using h

private theorem exists_epsilon_matrix (P : PeriodData K)
    (I : StablePseudolattice P) (b : Module.Basis (Fin 2) ℤ I.val) :
    ∃ M : SL(2, ℤ),
      P.sigma₁ P.epsilon * P.sigma₁ (b 0) =
        (M 0 0 : ℝ) * P.sigma₁ (b 0) + (M 0 1 : ℝ) * P.sigma₁ (b 1) ∧
      P.sigma₁ P.epsilon * P.sigma₁ (b 1) =
        (M 1 0 : ℝ) * P.sigma₁ (b 0) + (M 1 1 : ℝ) * P.sigma₁ (b 1) ∧
      (P.sigma₁ P.epsilon)⁻¹ * P.sigma₂ (b 0) =
        (M 0 0 : ℝ) * P.sigma₂ (b 0) + (M 0 1 : ℝ) * P.sigma₂ (b 1) ∧
      (P.sigma₁ P.epsilon)⁻¹ * P.sigma₂ (b 1) =
        (M 1 0 : ℝ) * P.sigma₂ (b 0) + (M 1 1 : ℝ) * P.sigma₂ (b 1) := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := fun i j => b.repr (epsilonMap P I (b i)) j
  have h₁ : P.sigma₁ P.epsilon * P.sigma₁ (b 0) =
      (A 0 0 : ℝ) * P.sigma₁ (b 0) + (A 0 1 : ℝ) * P.sigma₁ (b 1) :=
    epsilon_embedding_equation P I b P.sigma₁ 0
  have h₂ : P.sigma₁ P.epsilon * P.sigma₁ (b 1) =
      (A 1 0 : ℝ) * P.sigma₁ (b 0) + (A 1 1 : ℝ) * P.sigma₁ (b 1) :=
    epsilon_embedding_equation P I b P.sigma₁ 1
  have h₁' : (P.sigma₁ P.epsilon)⁻¹ * P.sigma₂ (b 0) =
      (A 0 0 : ℝ) * P.sigma₂ (b 0) + (A 0 1 : ℝ) * P.sigma₂ (b 1) := by
    simpa only [P.epsilon_conj] using epsilon_embedding_equation P I b P.sigma₂ 0
  have h₂' : (P.sigma₁ P.epsilon)⁻¹ * P.sigma₂ (b 1) =
      (A 1 0 : ℝ) * P.sigma₂ (b 0) + (A 1 1 : ℝ) * P.sigma₂ (b 1) := by
    simpa only [P.epsilon_conj] using epsilon_embedding_equation P I b P.sigma₂ 1
  let V : Matrix (Fin 2) (Fin 2) ℝ :=
    !![P.sigma₁ (b 0), P.sigma₂ (b 0); P.sigma₁ (b 1), P.sigma₂ (b 1)]
  let D : Matrix (Fin 2) (Fin 2) ℝ :=
    !![P.sigma₁ P.epsilon, 0; 0, (P.sigma₁ P.epsilon)⁻¹]
  have hAV : A.map (Int.castRingHom ℝ) * V = V * D := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Int.coe_castRingHom,
        V, D, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
        mul_zero, zero_mul, add_zero, zero_add]
    · exact h₁.symm.trans (mul_comm _ _)
    · exact h₁'.symm.trans (mul_comm _ _)
    · exact h₂.symm.trans (mul_comm _ _)
    · exact h₂'.symm.trans (mul_comm _ _)
  have hV : V.det ≠ 0 := by
    simpa only [V, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] using basis_embedding_det_ne_zero P I b
  have he : P.sigma₁ P.epsilon ≠ 0 := ne_of_gt (lt_trans zero_lt_one P.epsilon_gt_one)
  have hD : D.det = 1 := by simp [D, Matrix.det_fin_two, he]
  have hdet := congrArg Matrix.det hAV
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  change (A.map (fun z : ℤ => (z : ℝ))).det * V.det = V.det * D.det at hdet
  rw [← Int.cast_det, hD, mul_one] at hdet
  have ha : (A.det : ℝ) = 1 := by
    apply (mul_right_cancel₀ hV)
    simpa using hdet
  have hA : A.det = 1 := by exact_mod_cast ha
  exact ⟨⟨A, hA⟩, h₁, h₂, h₁', h₂'⟩

private theorem distribution_lattice_eq_embeddingImage (P : PeriodData K)
    (I : StablePseudolattice P) (b : Module.Basis (Fin 2) ℤ I.val)
    (B : L4.DistributionBasis)
    (hb0 : L4.distributionBetaOne B = (P.sigma₁ (b 0), P.sigma₂ (b 0)))
    (hb1 : L4.distributionBetaTwo B = (P.sigma₁ (b 1), P.sigma₂ (b 1))) :
    L4.distributionLattice B = I.val.toAddSubgroup.map
      (P.sigma₁.toAddMonoidHom.prod P.sigma₂.toAddMonoidHom) := by
  let emb := P.sigma₁.toAddMonoidHom.prod P.sigma₂.toAddMonoidHom
  have hb0' : emb (b 0).val = L4.distributionBetaOne B := hb0.symm
  have hb1' : emb (b 1).val = L4.distributionBetaTwo B := hb1.symm
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (L4.distributionLattice_mem_iff B z).mp hz
    refine ⟨((v 0) • b 0 + (v 1) • b 1).val,
      ((v 0) • b 0 + (v 1) • b 1).property, ?_⟩
    change emb ((v 0) • (b 0).val + (v 1) • (b 1).val) = z
    rw [map_add, map_zsmul, map_zsmul, hb0', hb1', ← hv]
  · rintro ⟨x, hx, rfl⟩
    let y : I.val := ⟨x, hx⟩
    refine (L4.distributionLattice_mem_iff B _).mpr ⟨fun i => b.repr y i, ?_⟩
    have hs : (b.repr y 0) • b 0 + (b.repr y 1) • b 1 = y := by
      simpa only [Fin.sum_univ_two] using b.sum_repr y
    have he := congrArg (fun t : I.val => emb t.val) hs
    change emb ((b.repr y 0) • (b 0).val + (b.repr y 1) • (b 1).val) = emb x at he
    rw [map_add, map_zsmul, map_zsmul, hb0', hb1'] at he
    exact he.symm

/-- A stable integer lattice in the quadratic field admits the
distribution presentation, with no independent real scaling. -/
theorem exists_distributionBasis_of_pseudolattice (P : PeriodData K)
    (I : StablePseudolattice P) :
    ∃ B : L4.DistributionBasis, B.Valid ∧
      L4.distributionPeriod B = P.sigma₁ P.epsilon ∧
      L4.distributionLattice B = I.val.toAddSubgroup.map
        (P.sigma₁.toAddMonoidHom.prod P.sigma₂.toAddMonoidHom) := by
  obtain ⟨b, hb₁, hb₂, horient⟩ := exists_admissible_pseudolattice_basis P I
  obtain ⟨M, h₁, h₂, h₁', h₂'⟩ := exists_epsilon_matrix P I b
  let B := L4.distributionBasisFromEmbeddings M (P.sigma₁ (b 0))
    (P.sigma₁ (b 1)) (P.sigma₂ (b 1))
  have h := L4.distributionBasisFromEmbeddings_valid M (P.sigma₁ P.epsilon)
    (P.sigma₁ (b 0)) (P.sigma₁ (b 1)) (P.sigma₂ (b 0)) (P.sigma₂ (b 1))
    P.epsilon_gt_one hb₁ hb₂ horient h₁ h₂ h₁' h₂'
  obtain ⟨hvalid, hperiod, hbeta0, hbeta1⟩ := h
  exact ⟨B, hvalid, hperiod,
    distribution_lattice_eq_embeddingImage P I b B hbeta0 hbeta1⟩

end SICLean.L3
