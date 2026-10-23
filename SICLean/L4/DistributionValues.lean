import SICLean.L4.DistributionOrderTwo
import SICLean.L4.DistributionValuesAux

set_option autoImplicit false

/-!
# Full-x distribution for the actual E

Nonlattice x, x∈J, and the two kernel points have separate statements. The all-x result does not
hide its zero-class cases in a definition. κ is the same actual etaKappa. Its exact order is
obtained by reusing `etaKappa_pow_twentyFour`, not by measuring a phase.

[RW26, p. 14, Prop. 9] is background; cf. [RW26, p. 23, Thm. 11]. Nothing here asserts algebraicity
of E; only κ is treated arithmetically.
-/

noncomputable section

open Set
open scoped MatrixGroups

namespace SICLean.L4

open DistributionValuesAux

/-- Same actual multipliers, with the square in the numerator. -/
def distributionKappa (B C : DistributionBasis) : ℂ :=
  etaKappa B.matrix C.matrix

/-- The half point is a nonzero I-class even though it is a zero J-class. Its value uses the
half-point η calculation, not a limiting off-J formula. [RW26, p. 3, μ]. -/
theorem distributionBasisValue_half (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) :
    distributionBasisValue B (distributionHalfVector B) =
      distributionKappa B (distributionDoubleBasis B hc) := by
  have hT : 0 < (etaDenom B.matrix (B.tau : ℂ)).re := by
    have hpos : 0 < distributionPeriod B := lt_trans (by norm_num) hB.2.2.2.1
    simpa [etaDenom, distributionPeriod] using hpos
  rw [distributionBasisValue_off_lattice B _ (half_not_mem_lattice B hB hc),
    half_periodDifference_integerCoordinate_zero B hB hc, half_normalized_argument B hB,
    (modularDistribution_half_fixedPoint B.matrix hB.1 hc hB.2.1 B.tau hT hB.2.2.1).2]
  simp only [distributionKappa, etaKappa, distributionDoubleBasis]
  ring

/-- Same center in the actual quotient group. [RW26, p. 3, (4), footnote 2]. -/
theorem distributionValue_half (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) :
    distributionValue B (distributionHalfClass B hB hc) =
      distributionKappa B (distributionDoubleBasis B hc) := by
  rw [distributionHalfClass, distributionValue_mk B hB]
  exact distributionBasisValue_half B hB hc

/-- The off-J branch uses actual center regularity and a balanced index shift. [RW26, p. 6, (16)].
-/
theorem distributionBasisValue_double_off (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) (x : ℝ × ℝ)
    (hx : x ∈ distributionPeriodPoints B)
    (hJ : x ∉ distributionLattice (distributionDoubleBasis B hc)) :
    distributionBasisValue B x * distributionBasisValue B (x + distributionHalfVector B) =
      distributionKappa B (distributionDoubleBasis B hc) *
        distributionBasisValue (distributionDoubleBasis B hc) x := by
  simpa [distributionKappa] using DistributionValuesAux.double_off B hB hc x hx hJ

/-- Independent zero-class branch: reduce the pair to {0,h} modulo I. [RW26, p. 3, (4), footnote 2].
-/
theorem distributionBasisValue_double_on (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) (x : ℝ × ℝ)
    (hx : x ∈ distributionPeriodPoints B)
    (hJ : x ∈ distributionLattice (distributionDoubleBasis B hc)) :
    distributionBasisValue B x * distributionBasisValue B (x + distributionHalfVector B) =
      distributionKappa B (distributionDoubleBasis B hc) *
        distributionBasisValue (distributionDoubleBasis B hc) x := by
  classical
  have hhalf := distributionHalfVector_mem B hB hc
  have hJhalf : distributionLattice (distributionDoubleBasis B hc) =
      distributionOverlattice B (distributionHalfClass B hB hc) := by
    rw [distributionOverlattice_lift B hB (distributionHalfClass B hB hc)
      (distributionHalfVector B) hhalf rfl]
    exact distributionDoubleBasis_lattice B hB hc
  have hcases := (distributionOverlattice_mem B hB (distributionHalfClass B hB hc)
    (distributionHalfClass_orderTwo B hB hc) x).mp (hJhalf ▸ hJ)
  have hrep := distributionRepresentative_mk B hB (distributionHalfVector B) hhalf
  have htarget := distributionBasisValue_on_lattice (distributionDoubleBasis B hc) x hJ
  rw [(distributionDoubleBasis_valid B hB hc).2.1] at htarget
  rw [htarget]
  rcases hcases with hI | hI
  · rw [distributionBasisValue_on_lattice B x hI]
    have hshift : distributionBasisValue B (x + distributionHalfVector B) =
        distributionBasisValue B (distributionHalfVector B) := by
      simpa only [add_comm x] using
        distributionBasisValue_periodic B hB (distributionHalfVector B) x hhalf hI
    rw [hshift, distributionBasisValue_half B hB hc, mul_comm]
  · have hxhalf : x - distributionHalfVector B ∈ distributionLattice B := by
      have hsum := add_mem hI hrep
      convert hsum using 1
      dsimp only [distributionHalfClass]
      abel
    have hxh : x + distributionHalfVector B ∈ distributionLattice B := by
      have hsum := add_mem hxhalf (half_add_half_mem B)
      convert hsum using 1
      abel
    rw [value_eq_of_sub_mem B hB x (distributionHalfVector B) hhalf hxhalf,
      distributionBasisValue_half B hB hc, distributionBasisValue_on_lattice B _ hxh]

/-- All representatives in an adapted basis, including x=0 and β₂/2. [RW26, p. 14, Prop. 9]. -/
theorem distributionBasisValue_double (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) (x : ℝ × ℝ)
    (hx : x ∈ distributionPeriodPoints B) :
    distributionBasisValue B x * distributionBasisValue B (x + distributionHalfVector B) =
      distributionKappa B (distributionDoubleBasis B hc) *
        distributionBasisValue (distributionDoubleBasis B hc) x := by
  by_cases hJ : x ∈ distributionLattice (distributionDoubleBasis B hc)
  · exact distributionBasisValue_double_on B hB hc x hx hJ
  · exact distributionBasisValue_double_off B hB hc x hx hJ

/-- Arbitrary order-two h and any actual admissible presentation of J. No adapted-basis existence or
distribution identity is assumed. [RW26, p. 14, Prop. 9]. -/
theorem distributionBasisValue_distribution (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (h : DistributionGroup B)
    (hh : h ≠ 0 ∧ h + h = 0)
    (hε : distributionPeriod C = distributionPeriod B)
    (hJ : distributionLattice C = distributionOverlattice B h)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionBasisValue B x *
        distributionBasisValue B (x + distributionRepresentative B h) =
      distributionKappa B C * distributionBasisValue C x := by
  classical
  obtain ⟨A, hA, hc, hrep⟩ := distribution_exists_adapted_basis B hB h hh
  let R := distributionRebase B A
  let D := distributionDoubleBasis R hc
  have hR := distributionRebase_valid B hB A hA
  have hRL := distributionRebase_lattice B hB A hA
  have hD := distributionDoubleBasis_valid R hR.1 hc
  have hεD : distributionPeriod D = distributionPeriod B := hD.2.1.trans hR.2.1
  have hDC : distributionLattice D = distributionLattice C := by
    calc
      distributionLattice D = distributionLattice R ⊔
          AddSubgroup.zmultiples (distributionHalfVector R) :=
        distributionDoubleBasis_lattice R hR.1 hc
      _ = distributionLattice B ⊔ AddSubgroup.zmultiples (distributionHalfVector R) := by
        rw [hRL.1]
      _ = distributionLattice B ⊔ AddSubgroup.zmultiples (distributionRepresentative B h) :=
        (sup_zmultiples_eq_of_sub_mem _ _ _ hrep).symm
      _ = distributionLattice C := hJ.symm
  have hI : distributionLattice B ≤ distributionLattice C := by
    rw [hJ]
    exact le_sup_left
  have hxC := distributionPeriodPoints_mono B C hε hI hx
  have hxR : x ∈ distributionPeriodPoints R := by
    rw [hRL.2]
    exact hx
  have hhR := distributionHalfVector_mem R hR.1 hc
  have hhB : distributionHalfVector R ∈ distributionPeriodPoints B := hRL.2 ▸ hhR
  have hshift : distributionBasisValue B (x + distributionRepresentative B h) =
      distributionBasisValue B (x + distributionHalfVector R) := by
    apply value_eq_of_sub_mem B hB _ _ (add_mem hx hhB)
    convert hrep using 1
    abel
  have hmulR : etaMultiplier R.matrix = etaMultiplier B.matrix :=
    distributionRebase_multiplier B hB A hA
  have hmulD : etaMultiplier D.matrix = etaMultiplier C.matrix :=
    distributionBasis_same_lattice_multiplier C D hC hD.1
      (hεD.trans hε.symm) hDC
  have hκ : distributionKappa R D = distributionKappa B C := by
    unfold distributionKappa etaKappa
    rw [hmulR, hmulD]
  have hvalD : distributionBasisValue D x = distributionBasisValue C x :=
    distributionBasis_same_lattice_value C D hC hD.1 (hεD.trans hε.symm) hDC x hxC
  rw [hshift, ← distributionRebase_value B hB A hA x hx,
    ← distributionRebase_value B hB A hA (x + distributionHalfVector R) (add_mem hx hhB)]
  change distributionBasisValue R x * distributionBasisValue R (x + distributionHalfVector R) = _
  rw [distributionBasisValue_double R hR.1 hc x hxR, hκ, hvalD]

/-- The callable all-x quotient distribution, with the natural set map. The redundant explicit hP
makes its dependent Lean type usable downstream. [RW26, p. 14, Prop. 9]. -/
theorem distributionValue_distribution (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (h : DistributionGroup B)
    (hh : h ≠ 0 ∧ h + h = 0)
    (hε : distributionPeriod C = distributionPeriod B)
    (hJ : distributionLattice C = distributionOverlattice B h)
    (hP : distributionPeriodPoints B ≤ distributionPeriodPoints C)
    (x : DistributionGroup B) :
    distributionValue B x * distributionValue B (x + h) =
      distributionKappa B C * distributionValue C (distributionProject B C hP x) := by
  let y := distributionRepresentative B x
  let t := distributionRepresentative B h
  have hy : y ∈ distributionPeriodPoints B := (Quotient.out x).property
  have ht : t ∈ distributionPeriodPoints B := (Quotient.out h).property
  have hsum : distributionMk B (y + t) (add_mem hy ht) = x + h := by
    rw [mk_add B y t hy ht, mk_representative, mk_representative]
  have htarget : distributionValue C (distributionProject B C hP x) =
      distributionBasisValue C y := distributionValue_mk C hC y (hP hy)
  rw [← hsum, distributionValue_mk B hB, htarget]
  exact distributionBasisValue_distribution B C hB hC h hh hε hJ y hy

/-- The order-two value itself; cancellation uses √ε≠0. [RW26, p. 3, (4)]. -/
theorem distributionValue_orderTwo (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (h : DistributionGroup B)
    (hh : h ≠ 0 ∧ h + h = 0)
    (hε : distributionPeriod C = distributionPeriod B)
    (hJ : distributionLattice C = distributionOverlattice B h) :
    distributionValue B h = distributionKappa B C := by
  have hI : distributionLattice B ≤ distributionLattice C := by
    rw [hJ]
    exact le_sup_left
  have hP := distributionPeriodPoints_mono B C hε hI
  have hz : distributionProject B C hP 0 = 0 :=
    (distributionProject_kernel B C hB hC h hh hP hJ 0).mpr (Or.inl rfl)
  have he := distributionValue_distribution B C hB hC h hh hε hJ hP 0
  rw [zero_add, hz, distributionValue_zero B hB, distributionValue_zero C hC, hε,
    mul_comm (distributionKappa B C)] at he
  have hroot : (Real.sqrt (distributionPeriod B) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (lt_trans zero_lt_one hB.2.2.2.1))
  exact mul_left_cancel₀ hroot he

/-- Explicit x=0 case, after the target zero class is identified. [RW26, p. 3, (4), footnote 2]. -/
theorem distributionValue_distribution_zero (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (h : DistributionGroup B)
    (hh : h ≠ 0 ∧ h + h = 0)
    (hε : distributionPeriod C = distributionPeriod B)
    (hJ : distributionLattice C = distributionOverlattice B h) :
    distributionValue B 0 * distributionValue B h =
      distributionKappa B C * distributionValue C 0 := by
  rw [distributionValue_orderTwo B C hB hC h hh hε hJ,
    distributionValue_zero B hB, distributionValue_zero C hC, hε, mul_comm]

/-- Explicit x=h case, not excluded by an x≠0 hypothesis. [RW26, p. 3, (4), footnote 2]. -/
theorem distributionValue_distribution_at_orderTwo (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (h : DistributionGroup B)
    (hh : h ≠ 0 ∧ h + h = 0)
    (hε : distributionPeriod C = distributionPeriod B)
    (hJ : distributionLattice C = distributionOverlattice B h) :
    distributionValue B h * distributionValue B 0 =
      distributionKappa B C * distributionValue C 0 := by
  rw [mul_comm]
  exact distributionValue_distribution_zero B C hB hC h hh hε hJ

/-- Presentation independence of the exact scalar. [RW26, p. 3, μ]. -/
theorem distributionKappa_basis_independent (B C B' C' : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (hB' : B'.Valid) (hC' : C'.Valid)
    (hεB : distributionPeriod B' = distributionPeriod B)
    (hεC : distributionPeriod C' = distributionPeriod C)
    (hIB : distributionLattice B' = distributionLattice B)
    (hIC : distributionLattice C' = distributionLattice C) :
    distributionKappa B' C' = distributionKappa B C := by
  unfold distributionKappa etaKappa
  rw [distributionBasis_same_lattice_multiplier B B' hB hB' hεB hIB,
    distributionBasis_same_lattice_multiplier C C' hC hC' hεC hIC]

/-- Exact coefficient order for L3.FiniteSystem.multiplier_order. The proof uses
`etaKappa_pow_twentyFour`;
no modulus/approximate-phase argument. [RW26, p. 3, μ]. -/
theorem distributionKappa_pow_twentyFour (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) : distributionKappa B C ^ 24 = 1 := by
  exact etaKappa_pow_twentyFour B.matrix C.matrix hB.1 hC.1

/-- The proof uses `etaKappa_ne_zero`. [RW26, p. 3, μ]. -/
theorem distributionKappa_ne_zero (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) : distributionKappa B C ≠ 0 := by
  exact etaKappa_ne_zero B.matrix C.matrix hB.1 hC.1

/-- Algebraicity only of κ. The proof uses `etaKappa_isAlgebraic`. [RW26, p. 3, μ]. -/
theorem distributionKappa_isAlgebraic (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) : IsAlgebraic ℚ (distributionKappa B C) := by
  exact etaKappa_isAlgebraic B.matrix C.matrix hB.1 hC.1

/-- The finite-family version: J=ρ I_C and the natural map is ρ⁻¹x. Literal equality J=I_C cannot
close an even-order finite family. [RW26, p. 14, Prop. 9]. -/
theorem distributionValue_distribution_scaled (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (h : DistributionGroup B)
    (hh : h ≠ 0 ∧ h + h = 0) (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2)
    (hε : distributionPeriod C = distributionPeriod B)
    (hJ : distributionLattice (distributionScale C ρ) = distributionOverlattice B h)
    (hP : distributionPeriodPoints B ≤ (distributionPeriodPoints C).comap
      (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹))) (x : DistributionGroup B) :
    distributionValue B x * distributionValue B (x + h) =
      distributionKappa B C * distributionValue C (distributionScaledProject B C ρ hP x) := by
  let D := distributionScale C ρ
  have hD := (distributionScale_valid C hC ρ hρ).1
  have hεD : distributionPeriod D = distributionPeriod B :=
    (distributionScale_valid C hC ρ hρ).2.1.trans hε
  have hI : distributionLattice B ≤ distributionLattice D := by
    rw [hJ]
    exact le_sup_left
  have hPD := distributionPeriodPoints_mono B D hεD hI
  have he := distributionValue_distribution B D hB hD h hh hεD hJ hPD x
  have htarget : distributionValue D (distributionProject B D hPD x) =
      distributionValue C (distributionScaledProject B C ρ hP x) := by
    have hsource : distributionValue D (distributionProject B D hPD x) =
        distributionBasisValue D (distributionRepresentative B x) :=
      distributionValue_mk D hD _ (hPD (Quotient.out x).property)
    have hscaled : distributionValue C (distributionScaledProject B C ρ hP x) =
        distributionBasisValue C
          (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) (distributionRepresentative B x)) :=
      distributionValue_mk C hC _ (hP (Quotient.out x).property)
    rw [hsource, hscaled]
    have hscale := distributionBasisValue_scale C hC ρ hρ
      (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) (distributionRepresentative B x))
      (hP (Quotient.out x).property)
    rw [homothety_inverse ρ hρ] at hscale
    exact hscale
  rw [htarget] at he
  exact he

#print distributionKappa
#check etaKappa_pow_twentyFour
#check etaKappa_isAlgebraic
#check distributionValue_distribution
#check distributionValue_distribution_zero
#check distributionValue_distribution_at_orderTwo

end SICLean.L4
