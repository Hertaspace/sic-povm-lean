import SICLean.L4.ModularDistribution
import SICLean.L4.DistributionCoordinates

set_option autoImplicit false

/-! Elementary quotient and rank-two lattice lemmas for the order-two bridge. -/

noncomputable section

open Set
open scoped MatrixGroups

namespace SICLean.L4

theorem distributionMk_zero_aux (B : DistributionBasis) :
    distributionMk B 0 (distributionPeriodPoints B).zero_mem = 0 := rfl

theorem distributionMk_add_aux (B : DistributionBasis) (x y : ℝ × ℝ)
    (hx : x ∈ distributionPeriodPoints B) (hy : y ∈ distributionPeriodPoints B) :
    distributionMk B (x + y) ((distributionPeriodPoints B).add_mem hx hy) =
      distributionMk B x hx + distributionMk B y hy := rfl

theorem distributionMk_representative_aux (B : DistributionBasis)
    (g : DistributionGroup B) :
    distributionMk B (distributionRepresentative B g) (Quotient.out g).property = g :=
  Quotient.out_eq g

theorem distributionMk_eq_zero_aux (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionMk B x hx = 0 ↔ x ∈ distributionLattice B := by
  rw [← distributionMk_zero_aux B,
    distributionMk_eq_iff B hB x 0 hx (distributionPeriodPoints B).zero_mem, sub_zero]

theorem distributionRepresentative_eq_zero_aux (B : DistributionBasis) (hB : B.Valid)
    (g : DistributionGroup B) :
    distributionRepresentative B g ∈ distributionLattice B ↔ g = 0 := by
  rw [← distributionMk_eq_zero_aux B hB (distributionRepresentative B g) (Quotient.out g).property,
    distributionMk_representative_aux]

theorem distributionRepresentative_sub_aux (B : DistributionBasis) (hB : B.Valid)
    (g h : DistributionGroup B) :
    distributionRepresentative B g - distributionRepresentative B h ∈
      distributionLattice B ↔ g = h := by
  rw [← distributionMk_eq_iff B hB (distributionRepresentative B g)
      (distributionRepresentative B h) (Quotient.out g).property
      (Quotient.out h).property,
    distributionMk_representative_aux, distributionMk_representative_aux]

theorem distributionRepresentative_two_aux (B : DistributionBasis) (hB : B.Valid)
    (h : DistributionGroup B) (hh : h + h = 0) :
    (2 : ℤ) • distributionRepresentative B h ∈ distributionLattice B := by
  have hr : distributionRepresentative B h ∈ distributionPeriodPoints B :=
    (Quotient.out h).property
  have hs : distributionMk B (distributionRepresentative B h + distributionRepresentative B h)
      ((distributionPeriodPoints B).add_mem hr hr) = 0 := by
    calc
      _ = distributionMk B (distributionRepresentative B h) hr +
          distributionMk B (distributionRepresentative B h) hr :=
        distributionMk_add_aux B _ _ hr hr
      _ = h + h := by rw [distributionMk_representative_aux]
      _ = 0 := hh
  have hm := (distributionMk_eq_zero_aux B hB _
    ((distributionPeriodPoints B).add_mem hr hr)).mp hs
  simpa only [two_zsmul] using hm

theorem distribution_sup_zmultiples_eq_aux {G : Type*} [AddCommGroup G]
    (I : AddSubgroup G) (x y : G) (hxy : x - y ∈ I) :
    I ⊔ AddSubgroup.zmultiples x = I ⊔ AddSubgroup.zmultiples y := by
  apply le_antisymm
  · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    have : x - y ∈ I ⊔ AddSubgroup.zmultiples y := AddSubgroup.mem_sup_left hxy
    simpa using (I ⊔ AddSubgroup.zmultiples y).add_mem this
      (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples y))
  · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    have : x - y ∈ I ⊔ AddSubgroup.zmultiples x := AddSubgroup.mem_sup_left hxy
    simpa using (I ⊔ AddSubgroup.zmultiples x).sub_mem
      (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples x)) this

theorem distribution_sup_orderTwo_mem_aux {G : Type*} [AddCommGroup G]
    (I : AddSubgroup G) (r x : G) (hr : (2 : ℤ) • r ∈ I) :
    x ∈ I ⊔ AddSubgroup.zmultiples r ↔ x ∈ I ∨ x - r ∈ I := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    have hk : k = k / 2 * 2 + k % 2 := by omega
    have hm : k % 2 = 0 ∨ k % 2 = 1 := Int.emod_two_eq_zero_or_one k
    rcases hm with hm | hm
    · left
      have he : k • r = (k / 2) • ((2 : ℤ) • r) := by
        rw [smul_smul]
        congr 1
        omega
      rw [he]
      exact I.add_mem hy (I.zsmul_mem hr _)
    · right
      have he0 : k • r = (k / 2 * 2) • r + r := by
        conv_lhs => rw [show k = k / 2 * 2 + 1 by omega]
        rw [add_zsmul, one_zsmul]
      have he : y + k • r - r = y + (k / 2) • ((2 : ℤ) • r) := by
        rw [he0, smul_smul]
        abel
      rw [he]
      exact I.add_mem hy (I.zsmul_mem hr _)
  · rintro (hx | hx)
    · exact AddSubgroup.mem_sup_left hx
    · simpa using (I ⊔ AddSubgroup.zmultiples r).add_mem (AddSubgroup.mem_sup_left hx)
        (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples r))

/-- A half second basis vector in the period group forces the lower entry even. -/
theorem distribution_half_mem_even_aux (C : DistributionBasis) (hC : C.Valid)
    (hw : (C.scale / 2, C.scaleConj / 2) ∈ distributionPeriodPoints C) :
    2 ∣ C.matrix 1 0 := by
  let y := distributionPeriodDifference C (C.scale / 2, C.scaleConj / 2)
  let n : ℤ := distributionIntegerCoordinates C y 0
  have hy : y ∈ distributionLattice C := hw
  have hn : distributionCoordinates C y 0 = (n : ℝ) :=
    (distributionLattice_coordinates C hC y).mp hy 0
  have hs : C.scale ≠ 0 := ne_of_gt hC.2.2.2.2.1
  have hs' : C.scaleConj ≠ 0 := ne_of_gt hC.2.2.2.2.2
  have hspec := distributionBasis_spectral C hC
  have hgap : C.tau - distributionConjugateTau C ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hspec.2.1)
  have hc0 : distributionCoordinates C y 0 = -(C.matrix 1 0 : ℝ) / 2 := by
    change (((((distributionPeriod C)⁻¹ - 1) * (C.scale / 2)) / C.scale -
      (((distributionPeriod C - 1) * (C.scaleConj / 2)) / C.scaleConj)) /
      (C.tau - distributionConjugateTau C)) = -(C.matrix 1 0 : ℝ) / 2
    rw [← hspec.2.2.1]
    dsimp [distributionPeriod]
    field_simp [hs, hs', hgap] <;> ring
  rw [hc0] at hn
  refine ⟨-n, ?_⟩
  have hreal : (C.matrix 1 0 : ℝ) = 2 * ((-n : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hreal

/-- Equality modulo the lattice can be checked on twice the two vectors. -/
theorem distribution_twice_congr_aux (B : DistributionBasis)
    (x w : ℝ × ℝ) (u v r s m n : ℤ)
    (hx : (2 : ℤ) • x = u • distributionBetaOne B + v • distributionBetaTwo B)
    (hw : (2 : ℤ) • w = r • distributionBetaOne B + s • distributionBetaTwo B)
    (hu : u - r = 2 * m) (hv : v - s = 2 * n) :
    x - w ∈ distributionLattice B := by
  apply (distributionLattice_mem_iff B (x - w)).mpr
  refine ⟨![m, n], ?_⟩
  change x - w = m • distributionBetaOne B + n • distributionBetaTwo B
  apply zsmul_right_injective (by norm_num : (2 : ℤ) ≠ 0)
  change (2 : ℤ) • (x - w) =
    (2 : ℤ) • (m • distributionBetaOne B + n • distributionBetaTwo B)
  rw [smul_sub, hx, hw, smul_add, smul_smul, smul_smul]
  rw [← hu, ← hv]
  simp only [sub_zsmul]
  abel

/-- A unimodular change whose second row has prescribed parity. -/
def distributionAdaptMatrix_aux (s : ℤ) : SL(2, ℤ) :=
  ⟨!![0, -1; 1, s], by simp [Matrix.det_fin_two]⟩

theorem distributionAdaptMatrix_c_aux (M : SL(2, ℤ)) (s : ℤ) :
    (distributionAdaptMatrix_aux s * M * (distributionAdaptMatrix_aux s)⁻¹) 1 0 =
      M 1 0 * s ^ 2 + (M 0 0 - M 1 1) * s - M 0 1 := by
  change (((distributionAdaptMatrix_aux s * M * (distributionAdaptMatrix_aux s)⁻¹) :
    Matrix (Fin 2) (Fin 2) ℤ) 1 0) = _
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  simp [distributionAdaptMatrix_aux, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  <;> ring

theorem distributionAdaptMatrix_c_pos_aux (M : SL(2, ℤ)) (hc : 0 < M 1 0)
    (s : ℤ) (hs : |M 0 0 - M 1 1| + |M 0 1| + 1 ≤ s) :
    0 < (distributionAdaptMatrix_aux s * M * (distributionAdaptMatrix_aux s)⁻¹) 1 0 := by
  rw [distributionAdaptMatrix_c_aux]
  have ha := abs_nonneg (M 0 0 - M 1 1)
  have hb := abs_nonneg (M 0 1)
  have hs1 : 1 ≤ s := by omega
  have hs0 : 0 ≤ s := by omega
  have hc1 : 1 ≤ M 1 0 := by omega
  have hq : s ^ 2 ≤ M 1 0 * s ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg s) hc1
  have hlin : -|M 0 0 - M 1 1| * s ≤ (M 0 0 - M 1 1) * s :=
    mul_le_mul_of_nonneg_right (neg_abs_le _) hs0
  have hbound : (|M 0 1| + 1) * s ≤ (s - |M 0 0 - M 1 1|) * s :=
    mul_le_mul_of_nonneg_right (by omega) hs0
  have hprod : |M 0 1| + 1 ≤ (|M 0 1| + 1) * s :=
    le_mul_of_one_le_right (by omega) hs1
  have hb' := le_abs_self (M 0 1)
  nlinarith

theorem distribution_rebase_one_aux (B : DistributionBasis) :
    distributionRebase B 1 = B := by
  cases B
  simp [distributionRebase, distributionRealMobius]

/-- A nonzero half-period has an admissible integral basis with that half-vector. -/
theorem distribution_exists_adapted_raw_aux (B : DistributionBasis) (hB : B.Valid)
    (h : DistributionGroup B) (hh : h ≠ 0 ∧ h + h = 0) :
    ∃ A : SL(2, ℤ), DistributionPositiveChange B A ∧
      2 ∣ (distributionRebase B A).matrix 1 0 ∧
      distributionRepresentative B h -
        ((distributionRebase B A).scale / 2, (distributionRebase B A).scaleConj / 2) ∈
          distributionLattice B := by
  suffices hex : ∃ A : SL(2, ℤ), DistributionPositiveChange B A ∧
      distributionRepresentative B h -
        ((distributionRebase B A).scale / 2,
         (distributionRebase B A).scaleConj / 2) ∈ distributionLattice B by
    obtain ⟨A, hA, hz⟩ := hex
    let C := distributionRebase B A
    have hC : C.Valid := (distributionRebase_valid B hB A hA).1
    have hPC : distributionPeriodPoints C = distributionPeriodPoints B :=
      (distributionRebase_lattice B hB A hA).2
    have hzP := distributionLattice_le_periodPoints B hB hz
    have hwB : (C.scale / 2, C.scaleConj / 2) ∈ distributionPeriodPoints B := by
      have hr : distributionRepresentative B h ∈ distributionPeriodPoints B :=
        (Quotient.out h).property
      have ht := (distributionPeriodPoints B).sub_mem hr hzP
      change distributionRepresentative B h -
        (distributionRepresentative B h - (C.scale / 2, C.scaleConj / 2)) ∈ _ at ht
      simpa only [sub_sub_cancel] using ht
    have hwC : (C.scale / 2, C.scaleConj / 2) ∈ distributionPeriodPoints C := by
      rw [hPC]
      exact hwB
    exact ⟨A, hA, distribution_half_mem_even_aux C hC hwC, hz⟩
  obtain ⟨u, hu⟩ := (distributionLattice_mem_iff B _).mp
    (distributionRepresentative_two_aux B hB h hh.2)
  have hnot : distributionRepresentative B h ∉ distributionLattice B := by
    simpa only [distributionRepresentative_eq_zero_aux B hB] using hh.1
  by_cases hu0 : u 0 % 2 = 0
  · have hv1 : u 1 % 2 = 1 := by
      by_contra hv
      have hv0 : u 1 % 2 = 0 := by omega
      have he := distribution_twice_congr_aux B (distributionRepresentative B h) 0
        (u 0) (u 1) 0 0 (u 0 / 2) (u 1 / 2) hu (by simp)
        (by omega) (by omega)
      exact hnot (by simpa only [sub_zero] using he)
    have hA : DistributionPositiveChange B (1 : SL(2, ℤ)) := by
      simpa [DistributionPositiveChange] using hB.1
    refine ⟨1, hA, ?_⟩
    rw [distribution_rebase_one_aux]
    apply distribution_twice_congr_aux B _ _ (u 0) (u 1) 0 1
      (u 0 / 2) ((u 1 - 1) / 2) hu
    · ext <;> simp [distributionBetaTwo, zsmul_eq_mul] <;> ring
    · omega
    · omega
  · have hu1 : u 0 % 2 = 1 := by omega
    let L : ℤ := |B.matrix 0 0 - B.matrix 1 1| + |B.matrix 0 1| + 1
    let R : ℝ := max (-B.tau) (max (-distributionConjugateTau B) (L : ℝ))
    obtain ⟨k, hk⟩ := exists_int_gt ((R - (u 1 : ℝ)) / 2)
    let s : ℤ := u 1 + 2 * k
    have hs : R < (s : ℝ) := by
      dsimp [s]
      push_cast
      linarith
    have hRτ : -B.tau ≤ R := le_max_left _ _
    have hRτ' : -distributionConjugateTau B ≤ R :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hRL : (L : ℝ) ≤ R :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hsτ : 0 < B.tau + (s : ℝ) := by linarith
    have hsτ' : 0 < distributionConjugateTau B + (s : ℝ) := by linarith
    have hsL : L ≤ s := by
      exact_mod_cast (le_trans hRL (le_of_lt hs))
    let A := distributionAdaptMatrix_aux s
    have hA : DistributionPositiveChange B A := by
      refine ⟨?_, ?_, distributionAdaptMatrix_c_pos_aux B.matrix hB.1 s hsL⟩
      · simpa [A, distributionAdaptMatrix_aux] using hsτ
      · simpa [A, distributionAdaptMatrix_aux] using hsτ'
    refine ⟨A, hA, ?_⟩
    apply distribution_twice_congr_aux B _ _ (u 0) (u 1) 1 s (u 0 / 2) (-k) hu
    · ext <;> simp [distributionRebase, A, distributionAdaptMatrix_aux,
        distributionBetaOne, distributionBetaTwo, zsmul_eq_mul] <;> ring
    · omega
    · dsimp [s]
      ring

end SICLean.L4
