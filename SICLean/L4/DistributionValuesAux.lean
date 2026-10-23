import SICLean.L4.DistributionOrderTwo

set_option autoImplicit false

/-! Elementary representative and lattice bridges for the full-x distribution law. The analytic
input is imported from the fixed upstream interfaces. -/

noncomputable section

open Set
open scoped MatrixGroups

namespace SICLean.L4.DistributionValuesAux

theorem mk_representative (B : DistributionBasis) (g : DistributionGroup B) :
    distributionMk B (distributionRepresentative B g) (Quotient.out g).property = g := by
  exact Quotient.out_eq g

theorem mk_add (B : DistributionBasis) (x y : ℝ × ℝ)
    (hx : x ∈ distributionPeriodPoints B) (hy : y ∈ distributionPeriodPoints B) :
    distributionMk B (x + y) (add_mem hx hy) =
      distributionMk B x hx + distributionMk B y hy := by
  exact QuotientAddGroup.mk_add
    ((distributionLattice B).addSubgroupOf (distributionPeriodPoints B))
    (⟨x, hx⟩ : distributionPeriodPoints B) ⟨y, hy⟩

theorem value_eq_of_sub_mem (B : DistributionBasis) (hB : B.Valid)
    (x y : ℝ × ℝ) (hy : y ∈ distributionPeriodPoints B)
    (hxy : x - y ∈ distributionLattice B) :
    distributionBasisValue B x = distributionBasisValue B y := by
  simpa only [add_sub_cancel] using
    distributionBasisValue_periodic B hB y (x - y) hy hxy

theorem half_add_half (B : DistributionBasis) :
    distributionHalfVector B + distributionHalfVector B = distributionBetaTwo B := by
  ext <;> simp [distributionHalfVector, distributionBetaTwo]

theorem half_add_half_mem (B : DistributionBasis) :
    distributionHalfVector B + distributionHalfVector B ∈ distributionLattice B := by
  rw [half_add_half, distributionLattice_mem_iff]
  exact ⟨![0, 1], by simp⟩

theorem sup_zmultiples_eq_of_sub_mem (I : AddSubgroup (ℝ × ℝ))
    (x y : ℝ × ℝ) (hxy : x - y ∈ I) :
    I ⊔ AddSubgroup.zmultiples x = I ⊔ AddSubgroup.zmultiples y := by
  apply le_antisymm
  · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    have h₁ : x - y ∈ I ⊔ AddSubgroup.zmultiples y := AddSubgroup.mem_sup_left hxy
    have h₂ : y ∈ I ⊔ AddSubgroup.zmultiples y :=
      AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples y)
    simpa only [sub_add_cancel] using add_mem h₁ h₂
  · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    have h₁ : x - y ∈ I ⊔ AddSubgroup.zmultiples x := AddSubgroup.mem_sup_left hxy
    have h₂ : x ∈ I ⊔ AddSubgroup.zmultiples x :=
      AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples x)
    simpa only [sub_sub_cancel] using sub_mem h₂ h₁

theorem homothety_inverse (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2)
    (x : ℝ × ℝ) :
    distributionHomothety ρ (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) x) = x := by
  ext <;> simp [distributionHomothety, ne_of_gt hρ.1, ne_of_gt hρ.2]

theorem half_not_mem_lattice (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) :
    distributionHalfVector B ∉ distributionLattice B := by
  intro hh
  have he : distributionMk B (distributionHalfVector B) (distributionHalfVector_mem B hB hc) =
      distributionMk B 0 (AddSubgroup.zero_mem _) :=
    (distributionMk_eq_iff B hB _ _ _ _).mpr (by simpa using hh)
  exact (distributionHalfClass_orderTwo B hB hc).1 he

theorem half_periodDifference_coordinate_zero (B : DistributionBasis) (hB : B.Valid) :
    distributionCoordinates B (distributionPeriodDifference B (distributionHalfVector B)) 0 =
      -(B.matrix 1 0 : ℝ) / 2 := by
  have hs : B.scale ≠ 0 := ne_of_gt hB.2.2.2.2.1
  have hs' : B.scaleConj ≠ 0 := ne_of_gt hB.2.2.2.2.2
  have hτ : B.tau - distributionConjugateTau B ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (distributionBasis_spectral B hB).2.1)
  change ((((distributionPeriod B)⁻¹ - 1) * (B.scale / 2)) / B.scale -
    ((distributionPeriod B - 1) * (B.scaleConj / 2)) / B.scaleConj) /
      (B.tau - distributionConjugateTau B) = _
  rw [← (distributionBasis_spectral B hB).2.2.1]
  unfold distributionPeriod
  field_simp [hs, hs', hτ]
  ring

theorem half_periodDifference_integerCoordinate_zero (B : DistributionBasis)
    (hB : B.Valid) (hc : 2 ∣ B.matrix 1 0) :
    distributionIntegerCoordinates B (distributionPeriodDifference B (distributionHalfVector B)) 0 =
      -(B.matrix 1 0 / 2) := by
  unfold distributionIntegerCoordinates
  rw [half_periodDifference_coordinate_zero B hB]
  have hmul : (B.matrix 1 0 / 2) * 2 = B.matrix 1 0 := Int.ediv_mul_cancel hc
  have hcast : -(B.matrix 1 0 : ℝ) / 2 = (-(B.matrix 1 0 / 2) : ℤ) := by
    have hmul' : ((B.matrix 1 0 / 2 : ℤ) : ℝ) * 2 = (B.matrix 1 0 : ℝ) := by
      exact_mod_cast hmul
    push_cast
    linarith
  rw [hcast, Int.floor_intCast]

theorem half_normalized_argument (B : DistributionBasis) (hB : B.Valid) :
    ((((distributionHalfVector B).1 / B.scale : ℝ) : ℂ)) = 1 / 2 := by
  have hs : B.scale ≠ 0 := ne_of_gt hB.2.2.2.2.1
  change (((B.scale / 2) / B.scale : ℝ) : ℂ) = _
  have hr : (B.scale / 2) / B.scale = (1 / 2 : ℝ) := by
    field_simp
  rw [hr]
  norm_num

/-! The balanced real center and the two exact changes of the floor index. These are coordinate
bridges. -/

theorem periodPoint_balance (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    ((etaDenom B.matrix (B.tau : ℂ))⁻¹ - 1) * ((x.1 / B.scale : ℝ) : ℂ) =
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 : ℂ) *
        (B.tau : ℂ) +
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 1 : ℂ) := by
  have hs : B.scale ≠ 0 := ne_of_gt hB.2.2.2.2.1
  have hf := congrArg Prod.fst (distributionPeriodPoints_expansion B hB x hx)
  dsimp only [distributionBetaOne, distributionBetaTwo] at hf
  simp only [zsmul_eq_mul] at hf
  change ((distributionPeriod B)⁻¹ - 1) * x.1 =
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 : ℝ) *
        (B.scale * B.tau) +
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 1 : ℝ) *
        B.scale at hf
  have hr : ((distributionPeriod B)⁻¹ - 1) * (x.1 / B.scale) =
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 : ℝ) *
        B.tau +
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 1 : ℝ) := by
    calc
      _ = (((distributionPeriod B)⁻¹ - 1) * x.1) / B.scale := by ring
      _ = ((distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 : ℝ) *
          (B.scale * B.tau) +
        (distributionIntegerCoordinates B (distributionPeriodDifference B x) 1 : ℝ) *
          B.scale) / B.scale := by rw [hf]
      _ = _ := by field_simp
  have hden : etaDenom B.matrix (B.tau : ℂ) = (distributionPeriod B : ℂ) := by
    simp [etaDenom, distributionPeriod]
  rw [hden]
  exact_mod_cast hr

theorem half_translate_integerCoordinate_zero (B : DistributionBasis)
    (hB : B.Valid) (hc : 2 ∣ B.matrix 1 0) (x : ℝ × ℝ) :
    distributionIntegerCoordinates B
      (distributionPeriodDifference B (x + distributionHalfVector B)) 0 =
    distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 -
      B.matrix 1 0 / 2 := by
  have hs : B.scale ≠ 0 := ne_of_gt hB.2.2.2.2.1
  have hs' : B.scaleConj ≠ 0 := ne_of_gt hB.2.2.2.2.2
  have ht : B.tau - distributionConjugateTau B ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (distributionBasis_spectral B hB).2.1)
  have hspec := (distributionBasis_spectral B hB).2.2.1.symm
  have hreal : distributionCoordinates B
      (distributionPeriodDifference B (x + distributionHalfVector B)) 0 =
      distributionCoordinates B (distributionPeriodDifference B x) 0 -
        (B.matrix 1 0 : ℝ) / 2 := by
    change (((distributionPeriod B)⁻¹ - 1) * (x.1 + B.scale / 2) / B.scale -
        (distributionPeriod B - 1) * (x.2 + B.scaleConj / 2) / B.scaleConj) /
        (B.tau - distributionConjugateTau B) =
      (((distributionPeriod B)⁻¹ - 1) * x.1 / B.scale -
        (distributionPeriod B - 1) * x.2 / B.scaleConj) /
        (B.tau - distributionConjugateTau B) - (B.matrix 1 0 : ℝ) / 2
    rw [hspec]
    dsimp [distributionPeriod]
    field_simp
    <;> ring
  have hcast : ((B.matrix 1 0 / 2 : ℤ) : ℝ) = (B.matrix 1 0 : ℝ) / 2 := by
    exact_mod_cast Int.cast_div (α := ℝ) hc (by norm_num : (2 : ℝ) ≠ 0)
  simp only [distributionIntegerCoordinates, hreal, ← hcast, Int.floor_sub_intCast]

theorem double_coordinate_zero (B : DistributionBasis)
    (hB : B.Valid) (hc : 2 ∣ B.matrix 1 0) (x : ℝ × ℝ) :
    distributionCoordinates (distributionDoubleBasis B hc) x 0 =
      distributionCoordinates B x 0 := by
  have hs : B.scale ≠ 0 := ne_of_gt hB.2.2.2.2.1
  have hs' : B.scaleConj ≠ 0 := ne_of_gt hB.2.2.2.2.2
  have ht : B.tau - distributionConjugateTau B ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (distributionBasis_spectral B hB).2.1)
  have hconj := (distributionDoubleBasis_valid B hB hc).2.2
  simp only [distributionCoordinates, Matrix.cons_val_zero, hconj]
  dsimp [distributionDoubleBasis]
  field_simp
  <;> ring

theorem double_integerCoordinate_zero (B : DistributionBasis)
    (hB : B.Valid) (hc : 2 ∣ B.matrix 1 0) (x : ℝ × ℝ) :
    distributionIntegerCoordinates (distributionDoubleBasis B hc)
        (distributionPeriodDifference (distributionDoubleBasis B hc) x) 0 =
      distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 := by
  have he := (distributionDoubleBasis_valid B hB hc).2.1
  have hdiff : distributionPeriodDifference (distributionDoubleBasis B hc) x =
      distributionPeriodDifference B x := by
    ext <;> simp [distributionPeriodDifference, he]
  simp only [distributionIntegerCoordinates, hdiff, double_coordinate_zero B hB hc]

/-- The off-J branch uses actual no-pole centers before applying the product formula. -/
theorem double_off (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) (x : ℝ × ℝ)
    (hx : x ∈ distributionPeriodPoints B)
    (hJ : x ∉ distributionLattice (distributionDoubleBasis B hc)) :
    distributionBasisValue B x * distributionBasisValue B (x + distributionHalfVector B) =
      etaKappa B.matrix (distributionDoubleBasis B hc).matrix *
        distributionBasisValue (distributionDoubleBasis B hc) x := by
  let C := distributionDoubleBasis B hc
  let y := x + distributionHalfVector B
  let z : ℂ := ((x.1 / B.scale : ℝ) : ℂ)
  let m := distributionIntegerCoordinates B (distributionPeriodDifference B x) 0
  have hC : C.Valid := (distributionDoubleBasis_valid B hB hc).1
  have he : distributionPeriod C = distributionPeriod B :=
    (distributionDoubleBasis_valid B hB hc).2.1
  have hIC : distributionLattice B ≤ distributionLattice C := by
    rw [distributionDoubleBasis_lattice B hB hc]
    exact le_sup_left
  have hhJ : distributionHalfVector B ∈ distributionLattice C := by
    rw [distributionDoubleBasis_lattice B hB hc]
    exact (show AddSubgroup.zmultiples (distributionHalfVector B) ≤
      distributionLattice B ⊔ AddSubgroup.zmultiples (distributionHalfVector B) from
        le_sup_right) (AddSubgroup.mem_zmultiples (distributionHalfVector B))
  have hxI : x ∉ distributionLattice B := fun h => hJ (hIC h)
  have hyI : y ∉ distributionLattice B := by
    intro hy
    have h := (distributionLattice C).sub_mem (hIC hy) hhJ
    have hsub : y - distributionHalfVector B = x := by
      dsimp [y]
      abel
    exact hJ (hsub ▸ h)
  have hy : y ∈ distributionPeriodPoints B :=
    (distributionPeriodPoints B).add_mem hx (distributionHalfVector_mem B hB hc)
  have hxC : x ∈ distributionPeriodPoints C :=
    distributionPeriodPoints_mono B C he hIC hx
  have hwx : z ∉ modularPhiPseudoLattice (B.tau : ℂ) := by
    intro hw
    exact hxI ((distributionPeriodPoints_first_lattice_iff B hB x hx).mp hw)
  have hwy : ((y.1 / B.scale : ℝ) : ℂ) ∉ modularPhiPseudoLattice (B.tau : ℂ) := by
    intro hw
    exact hyI ((distributionPeriodPoints_first_lattice_iff B hB y hy).mp hw)
  have hwC : ((x.1 / C.scale : ℝ) : ℂ) ∉ modularPhiPseudoLattice (C.tau : ℂ) := by
    intro hw
    exact hJ ((distributionPeriodPoints_first_lattice_iff C hC x hxC).mp hw)
  have hs : B.scale ≠ 0 := ne_of_gt hB.2.2.2.2.1
  have hyz : ((y.1 / B.scale : ℝ) : ℂ) = z + 1 / 2 := by
    have hyr : y.1 / B.scale = x.1 / B.scale + 1 / 2 := by
      dsimp [y, distributionHalfVector]
      field_simp
      <;> ring
    dsimp [z]
    simpa using congrArg Complex.ofReal hyr
  have hCz : ((x.1 / C.scale : ℝ) : ℂ) = 2 * z := by
    have hCr : x.1 / C.scale = 2 * (x.1 / B.scale) := by
      dsimp [C, distributionDoubleBasis]
      field_simp
    dsimp [z]
    exact_mod_cast hCr
  have hCt : (C.tau : ℂ) = 2 * (B.tau : ℂ) := by
    simp [C, distributionDoubleBasis]
  have hTB : 0 < (B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ) :=
    lt_trans zero_lt_one hB.2.2.2.1
  have hTC : 0 < (C.matrix 1 0 : ℝ) * C.tau + (C.matrix 1 1 : ℝ) := by
    change 0 < distributionPeriod C
    rw [he]
    exact hTB
  have hT : 0 < (etaDenom B.matrix (B.tau : ℂ)).re := by
    simpa [etaDenom] using hTB
  have hmy : distributionIntegerCoordinates B (distributionPeriodDifference B y) 0 +
      B.matrix 1 0 / 2 = m := by
    dsimp [y, m]
    rw [half_translate_integerCoordinate_zero B hB hc]
    omega
  have hshift :
      modularPhi B.matrix
          (distributionIntegerCoordinates B (distributionPeriodDifference B y) 0) 0
          ((y.1 / B.scale : ℝ) : ℂ) (B.tau : ℂ) =
        modularPhi B.matrix m (B.matrix 1 0 / 2)
          ((y.1 / B.scale : ℝ) : ℂ) (B.tau : ℂ) := by
    simpa only [hmy] using
      modularDistribution_index_fixedPoint B.matrix hB.1 B.tau hT hB.2.2.1
        (distributionIntegerCoordinates B (distributionPeriodDifference B y) 0)
        (distributionIntegerCoordinates B (distributionPeriodDifference B y) 1)
        (B.matrix 1 0 / 2) ((y.1 / B.scale : ℝ) : ℂ)
        (periodPoint_balance B hB y hy) hwy
  have hn1 := modularPhi_real_off_lattice B.matrix hB.1 m 0 B.tau hTB z hwx
  have hn2 := modularPhi_real_off_lattice B.matrix hB.1 m (B.matrix 1 0 / 2)
    B.tau hTB ((y.1 / B.scale : ℝ) : ℂ) hwy
  have hnJ := modularPhi_real_off_lattice C.matrix hC.1 m 0 C.tau hTC
    ((x.1 / C.scale : ℝ) : ℂ) hwC
  rw [hyz] at hn2
  rw [hCz, hCt] at hnJ
  have hhol1 : (z, (B.tau : ℂ)) ∈ modularPhiHolomorphicDomain B.matrix m 0 :=
    ⟨hn1.1, hn1.2.1⟩
  have hhol2 : (z + 1 / 2, (B.tau : ℂ)) ∈
      modularPhiHolomorphicDomain B.matrix m (0 + B.matrix 1 0 / 2) := by
    simpa only [zero_add] using
      (show (z + 1 / 2, (B.tau : ℂ)) ∈
        modularPhiHolomorphicDomain B.matrix m (B.matrix 1 0 / 2) from
          ⟨hn2.1, hn2.2.1⟩)
  have hholJ : (2 * z, 2 * (B.tau : ℂ)) ∈
      modularPhiHolomorphicDomain (modularDouble B.matrix hc) m 0 :=
    ⟨hnJ.1, hnJ.2.1⟩
  have hprod := modularDistribution_value B.matrix hB.1 hc m 0 z
    (B.tau : ℂ) hhol1 hhol2 hholJ
  simp only [zero_add] at hprod
  rw [distributionBasisValue_off_lattice B x hxI,
    distributionBasisValue_off_lattice B y hyI,
    distributionBasisValue_off_lattice C x hJ]
  rw [hshift, hyz, double_integerCoordinate_zero B hB hc, hCz, hCt]
  change (etaMultiplier B.matrix * modularPhi B.matrix m 0 z (B.tau : ℂ)) *
      (etaMultiplier B.matrix *
        modularPhi B.matrix m (B.matrix 1 0 / 2) (z + 1 / 2) (B.tau : ℂ)) =
    etaKappa B.matrix C.matrix *
      (etaMultiplier C.matrix * modularPhi C.matrix m 0 (2 * z) (2 * (B.tau : ℂ)))
  calc
    _ = etaMultiplier B.matrix ^ 2 *
      (modularPhi B.matrix m 0 z (B.tau : ℂ) *
        modularPhi B.matrix m (B.matrix 1 0 / 2) (z + 1 / 2) (B.tau : ℂ)) := by ring
    _ = etaMultiplier B.matrix ^ 2 *
      modularPhi C.matrix m 0 (2 * z) (2 * (B.tau : ℂ)) := by
        rw [hprod]
        rfl
    _ = _ := by
      unfold etaKappa
      rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀]
      exact etaMultiplier_ne_zero C.matrix hC.1

end SICLean.L4.DistributionValuesAux
