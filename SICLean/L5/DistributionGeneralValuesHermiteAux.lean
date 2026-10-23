import SICLean.L5.PeriodPowerValues
import SICLean.L5.DistributionOrbitGeometry
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Simultaneous Hermite presentations

The integer inclusion matrix has positive determinant because both real
presentations have positive oriented area. A unimodular row operation
puts it in positive upper triangular form and rebases the smaller
lattice. Relative index is the absolute determinant of this inclusion.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical MatrixGroups
open SICLean.L4
namespace SICLean.L5.DistributionGeneralValuesAux
theorem int_hermite (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : 0 < A.det) :
    ∃ (R : SL(2, ℤ)) (n m : ℕ) (k : ℤ), 0 < n ∧ 0 < m ∧
      (R : Matrix (Fin 2) (Fin 2) ℤ) * A = !![(n : ℤ), k; 0, (m : ℤ)] := by
  have hg : 0 < Int.gcd (A 0 0) (A 1 0) := by
    by_contra h
    have hz : Int.gcd (A 0 0) (A 1 0) = 0 := by omega
    obtain ⟨ha, hc⟩ := Int.gcd_eq_zero_iff.mp hz
    simp [Matrix.det_fin_two, ha, hc] at hA
  let n := Int.gcd (A 0 0) (A 1 0)
  obtain ⟨a, c, hac, ha, hc⟩ := Int.exists_gcd_one hg
  change A 0 0 = a * (n : ℤ) at ha
  change A 1 0 = c * (n : ℤ) at hc
  let u : ℤ := Int.gcdA a c
  let v : ℤ := Int.gcdB a c
  have huv : a * u + c * v = 1 := by
    simpa [u, v, hac] using (Int.gcd_eq_gcd_ab a c).symm
  let l : ℤ := -c * A 0 1 + a * A 1 1
  have hdet : A.det = (n : ℤ) * l := by
    rw [Matrix.det_fin_two, ha, hc]
    dsimp [l]
    ring
  have hl : 0 < l := by
    have hgZ : (0 : ℤ) < Int.gcd (A 0 0) (A 1 0) := by exact_mod_cast hg
    rw [hdet] at hA
    exact (mul_pos_iff_of_pos_left hgZ).mp hA
  let R : SL(2, ℤ) := ⟨!![u, v; -c, a], by
    simpa [Matrix.det_fin_two] using (show u * a - v * -c = 1 by nlinarith [huv])⟩
  refine ⟨R, n, l.toNat,
    u * A 0 1 + v * A 1 1, hg, ?_, ?_⟩
  · omega
  · have hl' : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (le_of_lt hl)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> dsimp [R]
    · change u * A 0 0 + v * A 1 0 = (n : ℤ)
      rw [ha, hc]
      linear_combination (n : ℤ) * huv
    · change -c * A 0 0 + a * A 1 0 = 0
      rw [ha, hc]
      ring
    · exact hl'.symm

open DistributionBasisValuesAux

theorem inclusion_intertwine (B C : DistributionBasis) (hB : B.Valid) (hC : C.Valid)
    (hε : distributionPeriod C = distributionPeriod B)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hu : distributionBetaOne C =
      A 0 0 • distributionBetaOne B + A 0 1 • distributionBetaTwo B)
    (hv : distributionBetaTwo C =
      A 1 0 • distributionBetaOne B + A 1 1 • distributionBetaTwo B) :
    (C.matrix : Matrix (Fin 2) (Fin 2) ℤ) * A =
      A * (B.matrix : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hb := sc_inverseAction_basis B hB
  have hc := sc_inverseAction_basis C hC
  have hF := sc_inverseAction_eq B C hε
  have hinv : (↑(C.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) * A =
      A * (↑(B.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) := by
    apply sc_matrix_eq_of_rows B hB
    intro i
    fin_cases i
    · change ((↑(C.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) * A) 0 0 • distributionBetaOne B +
          ((↑(C.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) * A) 0 1 • distributionBetaTwo B =
        (A * (↑(B.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 • distributionBetaOne B +
          (A * (↑(B.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 • distributionBetaTwo B
      calc
        _ = (C.matrix⁻¹) 0 0 • distributionBetaOne C +
            (C.matrix⁻¹) 0 1 • distributionBetaTwo C := by
          rw [hu, hv]
          simp only [Matrix.mul_apply, Fin.sum_univ_two]
          module
        _ = sc_inverseAction C (distributionBetaOne C) := hc.1.symm
        _ = sc_inverseAction B
            (A 0 0 • distributionBetaOne B + A 0 1 • distributionBetaTwo B) := by
          rw [hF, hu]
        _ = _ := by
          rw [map_add, map_zsmul, map_zsmul, hb.1, hb.2]
          simp only [Matrix.mul_apply, Fin.sum_univ_two]
          module
    · change ((↑(C.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 0 • distributionBetaOne B +
          ((↑(C.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 1 • distributionBetaTwo B =
        (A * (↑(B.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 • distributionBetaOne B +
          (A * (↑(B.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 • distributionBetaTwo B
      calc
        _ = (C.matrix⁻¹) 1 0 • distributionBetaOne C +
            (C.matrix⁻¹) 1 1 • distributionBetaTwo C := by
          rw [hu, hv]
          simp only [Matrix.mul_apply, Fin.sum_univ_two]
          module
        _ = sc_inverseAction C (distributionBetaTwo C) := hc.2.symm
        _ = sc_inverseAction B
            (A 1 0 • distributionBetaOne B + A 1 1 • distributionBetaTwo B) := by
          rw [hF, hv]
        _ = _ := by
          rw [map_add, map_zsmul, map_zsmul, hb.1, hb.2]
          simp only [Matrix.mul_apply, Fin.sum_univ_two]
          module
  have hiC : (C.matrix : Matrix (Fin 2) (Fin 2) ℤ) *
      (↑(C.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hiB : (↑(B.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) *
      (B.matrix : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  calc
    _ = (C.matrix : Matrix (Fin 2) (Fin 2) ℤ) *
        (A * (↑(B.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)) *
          (B.matrix : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hiB, Matrix.mul_one]
    _ = (C.matrix : Matrix (Fin 2) (Fin 2) ℤ) *
        ((↑(C.matrix⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) * A) *
          (B.matrix : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [hinv]
    _ = _ := by
      rw [← Matrix.mul_assoc (C.matrix : Matrix (Fin 2) (Fin 2) ℤ) _ A, hiC,
        Matrix.one_mul]

theorem exists_lattice_basis (B : DistributionBasis) (hB : B.Valid) :
    ∃ b : Module.Basis (Fin 2) ℤ (distributionLattice B),
      (b 0 : ℝ × ℝ) = distributionBetaOne B ∧
      (b 1 : ℝ × ℝ) = distributionBetaTwo B := by
  let g : (Fin 2 → ℤ) →+ distributionLattice B :=
    { toFun := fun u => ⟨u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B,
        (distributionLattice_mem_iff B _).2 ⟨u, rfl⟩⟩
      map_zero' := by ext <;> simp
      map_add' := by
        intros
        apply Subtype.ext
        simp only [AddSubgroup.coe_add, Pi.add_apply, add_zsmul]
        abel }
  have hg : Function.Bijective g := by
    constructor
    · intro u t h
      have hu := sc_zcoefficients_unique B hB _ _ _ _ (congrArg Subtype.val h)
      funext i
      fin_cases i
      · exact hu.1
      · exact hu.2
    · intro x
      obtain ⟨u, hu⟩ := (distributionLattice_mem_iff B x.val).1 x.property
      exact ⟨u, Subtype.ext hu.symm⟩
  let e : (Fin 2 → ℤ) ≃+ distributionLattice B := AddEquiv.ofBijective g hg
  let b : Module.Basis (Fin 2) ℤ (distributionLattice B) :=
    (Pi.basisFun ℤ (Fin 2)).map e.toIntLinearEquiv
  refine ⟨b, ?_, ?_⟩ <;> simp [b, e, g, Pi.basisFun_apply]

set_option backward.isDefEq.respectTransparency false in
theorem lattice_relIndex_eq_det (B C : DistributionBasis) (hB : B.Valid) (hC : C.Valid)
    (hle : distributionLattice C ≤ distributionLattice B)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hu : distributionBetaOne C =
      A 0 0 • distributionBetaOne B + A 0 1 • distributionBetaTwo B)
    (hv : distributionBetaTwo C =
      A 1 0 • distributionBetaOne B + A 1 1 • distributionBetaTwo B) :
    (distributionLattice C).relIndex (distributionLattice B) = A.det.natAbs := by
  obtain ⟨b, hb0, hb1⟩ := exists_lattice_basis B hB
  obtain ⟨c, hc0, hc1⟩ := exists_lattice_basis C hC
  have h0 : (⟨c 0, hle (c 0).property⟩ : distributionLattice B) =
      A 0 0 • b 0 + A 0 1 • b 1 := by
    apply Subtype.ext
    simpa [hc0, hb0, hb1] using hu
  have h1 : (⟨c 1, hle (c 1).property⟩ : distributionLattice B) =
      A 1 0 • b 0 + A 1 1 • b 1 := by
    apply Subtype.ext
    simpa [hc1, hb0, hb1] using hv
  let cB : Module.Basis (Fin 2) ℤ
      ((distributionLattice C).addSubgroupOf (distributionLattice B)) :=
    c.map (AddSubgroup.addSubgroupOfEquivOfLe hle).toIntLinearEquiv.symm
  have hcB0 : (cB 0 : distributionLattice B) = A 0 0 • b 0 + A 0 1 • b 1 := by
    exact h0
  have hcB1 : (cB 1 : distributionLattice B) = A 1 0 • b 0 + A 1 1 • b 1 := by
    exact h1
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_natAbs_det b _ cB]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, hcB0, hcB1, mul_comm]

theorem pair_row_comp (A D : Matrix (Fin 2) (Fin 2) ℤ) (v w : ℝ × ℝ) (i : Fin 2) :
    A i 0 • (D 0 0 • v + D 0 1 • w) +
      A i 1 • (D 1 0 • v + D 1 1 • w) =
        (A * D) i 0 • v + (A * D) i 1 • w := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  module

open SICLean.L3
open SICLean.L5.DistributionOrbitGeometry

universe u
variable {K : Type u} [Field K] [NumberField K]

theorem hermite_presentations_aux (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) :
    ∃ (BI BJ : DistributionBasis) (n m : ℕ) (k : ℤ),
      PseudolatticePresentation P I BI ∧ PseudolatticePresentation P J BJ ∧
      0 < n ∧ 0 < m ∧
      BI.tau = ((n : ℝ) * BJ.tau + (k : ℝ)) / (m : ℝ) ∧
      BI.scale = (m : ℝ) * BJ.scale ∧ BI.scaleConj = (m : ℝ) * BJ.scaleConj ∧
      (BI.matrix : Matrix (Fin 2) (Fin 2) ℤ) * !![(n : ℤ), k; 0, (m : ℤ)] =
        !![(n : ℤ), k; 0, (m : ℤ)] * (BJ.matrix : Matrix (Fin 2) (Fin 2) ℤ) ∧
      inclusionIndex I.val J.val = n * m := by
  obtain ⟨C, hC⟩ := exists_pseudolatticePresentation P I
  obtain ⟨BJ, hBJ⟩ := exists_pseudolatticePresentation P J
  have hle : distributionLattice C ≤ distributionLattice BJ := by
    rw [hC.2.2, hBJ.2.2]
    exact AddSubgroup.map_mono hIJ
  obtain ⟨u, hu⟩ := (distributionLattice_mem_iff BJ _).1
    (hle (dBasis_betaOne_mem C))
  obtain ⟨v, hv⟩ := (distributionLattice_mem_iff BJ _).1
    (hle (dBasis_betaTwo_mem C))
  let A : Matrix (Fin 2) (Fin 2) ℤ := ![u, v]
  change distributionBetaOne C = A 0 0 • distributionBetaOne BJ +
    A 0 1 • distributionBetaTwo BJ at hu
  change distributionBetaTwo C = A 1 0 • distributionBetaOne BJ +
    A 1 1 • distributionBetaTwo BJ at hv
  have harea :
      (distributionBetaOne C).1 * (distributionBetaTwo C).2 -
          (distributionBetaOne C).2 * (distributionBetaTwo C).1 =
      (A.det : ℝ) * ((distributionBetaOne BJ).1 * (distributionBetaTwo BJ).2 -
          (distributionBetaOne BJ).2 * (distributionBetaTwo BJ).1) := by
    rw [hu, hv]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    simp only [zsmul_eq_mul, Matrix.det_fin_two, Int.cast_sub, Int.cast_mul]
    ring
  have hdetpos : 0 < (A.det : ℝ) :=
    (mul_pos_iff_of_pos_right (sc_basis_area_pos BJ hBJ.1)).1
      (harea ▸ sc_basis_area_pos C hC.1)
  have hdetposZ : 0 < A.det := by exact_mod_cast hdetpos
  obtain ⟨R, n, m, k, hn, hm, hRA⟩ := int_hermite A hdetposZ
  let H : Matrix (Fin 2) (Fin 2) ℤ := !![(n : ℤ), k; 0, (m : ℤ)]
  change (R : Matrix (Fin 2) (Fin 2) ℤ) * A = H at hRA
  have hCA := inclusion_intertwine BJ C hBJ.1 hC.1
    (hC.2.1.trans hBJ.2.1.symm) A hu hv
  let MI : SL(2, ℤ) := R * C.matrix * R⁻¹
  have hRI : (↑(R⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) * R = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * H =
      H * (BJ.matrix : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← hRA]
    change (((R : Matrix (Fin 2) (Fin 2) ℤ) *
      (C.matrix : Matrix (Fin 2) (Fin 2) ℤ)) *
      (↑(R⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)) *
      ((R : Matrix (Fin 2) (Fin 2) ℤ) * A) = _
    calc
      _ = (R : Matrix (Fin 2) (Fin 2) ℤ) *
          ((C.matrix : Matrix (Fin 2) (Fin 2) ℤ) *
          ((↑(R⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) *
            (R : Matrix (Fin 2) (Fin 2) ℤ))) * A := by
        simp only [Matrix.mul_assoc]
      _ = (R : Matrix (Fin 2) (Fin 2) ℤ) *
          ((C.matrix : Matrix (Fin 2) (Fin 2) ℤ) * A) := by
        rw [hRI]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (R : Matrix (Fin 2) (Fin 2) ℤ) *
          (A * (BJ.matrix : Matrix (Fin 2) (Fin 2) ℤ)) := by rw [hCA]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hw0 : R 0 0 • distributionBetaOne C + R 0 1 • distributionBetaTwo C =
      (n : ℤ) • distributionBetaOne BJ + k • distributionBetaTwo BJ := by
    rw [hu, hv, pair_row_comp, hRA]
    simp [H]
  have hw1 : R 1 0 • distributionBetaOne C + R 1 1 • distributionBetaTwo C =
      (m : ℤ) • distributionBetaTwo BJ := by
    rw [hu, hv, pair_row_comp, hRA]
    simp [H]
  have hscale : C.scale * ((R 1 0 : ℝ) * C.tau + (R 1 1 : ℝ)) =
      (m : ℝ) * BJ.scale := by
    have h := congrArg Prod.fst hw1
    simp only [Prod.fst_add, Prod.smul_fst] at h
    simp only [distributionBetaOne, distributionBetaTwo, zsmul_eq_mul,
      Int.cast_natCast] at h
    nlinarith only [h]
  have hscaleConj : C.scaleConj *
      ((R 1 0 : ℝ) * distributionConjugateTau C + (R 1 1 : ℝ)) =
      (m : ℝ) * BJ.scaleConj := by
    have h := congrArg Prod.snd hw1
    simp only [Prod.snd_add, Prod.smul_snd] at h
    simp only [distributionBetaOne, distributionBetaTwo, zsmul_eq_mul,
      Int.cast_natCast] at h
    nlinarith only [h]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : 0 < (R 1 0 : ℝ) * C.tau + (R 1 1 : ℝ) := by
    apply (mul_pos_iff_of_pos_left (dBasis_scale_pos C hC.1)).1
    rw [hscale]
    exact mul_pos hmR (dBasis_scale_pos BJ hBJ.1)
  have hq : 0 < (R 1 0 : ℝ) * distributionConjugateTau C + (R 1 1 : ℝ) := by
    apply (mul_pos_iff_of_pos_left (dBasis_scaleConj_pos C hC.1)).1
    rw [hscaleConj]
    exact mul_pos hmR (dBasis_scaleConj_pos BJ hBJ.1)
  have hc : 0 < MI 1 0 := by
    have h := congrArg (fun D : Matrix (Fin 2) (Fin 2) ℤ => D 1 0) hH
    simp [H, Matrix.mul_apply, Fin.sum_univ_two] at h
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
    have hright := mul_pos hmZ hBJ.1.1
    nlinarith only [h, hnZ, hright]
  have hR : DistributionPositiveChange C R := ⟨hp, hq, hc⟩
  let BI := distributionRebase C R
  have hBI : PseudolatticePresentation P I BI :=
    ⟨(distributionRebase_valid C hC.1 R hR).1,
      (distributionRebase_valid C hC.1 R hR).2.1.trans hC.2.1,
      (distributionRebase_lattice C hC.1 R hR).1.trans hC.2.2⟩
  have hbetas := rebase_beta C hC.1 R hp hq hc
  change distributionBetaOne BI =
      R 0 0 • distributionBetaOne C + R 0 1 • distributionBetaTwo C ∧
    distributionBetaTwo BI =
      R 1 0 • distributionBetaOne C + R 1 1 • distributionBetaTwo C at hbetas
  have hsBI : BI.scale = (m : ℝ) * BJ.scale := hscale
  have hsBI' : BI.scaleConj = (m : ℝ) * BJ.scaleConj := hscaleConj
  have htau : BI.tau = ((n : ℝ) * BJ.tau + (k : ℝ)) / (m : ℝ) := by
    apply (eq_div_iff hmR.ne').2
    apply mul_left_cancel₀ (dBasis_scale_pos BJ hBJ.1).ne'
    have h := congrArg Prod.fst (hbetas.1.trans hw0)
    simp only [Prod.fst_add, Prod.smul_fst] at h
    simp only [distributionBetaOne, distributionBetaTwo, zsmul_eq_mul,
      Int.cast_natCast] at h
    rw [hsBI] at h
    nlinarith only [h]
  have hindex : inclusionIndex I.val J.val =
      (distributionLattice C).relIndex (distributionLattice BJ) := by
    rw [hC.2.2, hBJ.2.2]
    exact (AddSubgroup.relIndex_map_map_of_injective I.val.toAddSubgroup
      J.val.toAddSubgroup (pseudolatticeEmbedding_injective P)).symm
  have hdet := congrArg Matrix.det hRA
  simp only [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul] at hdet
  have hindex' : inclusionIndex I.val J.val = n * m := by
    rw [hindex, lattice_relIndex_eq_det BJ C hBJ.1 hC.1 hle A hu hv, hdet]
    simp [H, Matrix.det_fin_two, Int.natAbs_mul]
  exact ⟨BI, BJ, n, m, k, hBI, hBJ, hn, hm, htau, hsBI, hsBI', hH, hindex'⟩

end SICLean.L5.DistributionGeneralValuesAux

