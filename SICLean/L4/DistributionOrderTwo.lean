import SICLean.L4.ModularDistribution
import SICLean.L4.DistributionCoordinates
import SICLean.L4.DistributionOrderTwoAux

set_option autoImplicit false

/-!
# Arbitrary order-two classes and actual overlattices

The geometric existence of an adapted basis is proved separately from the quotient and overlattice
laws, rather than carried by the input data. The target is its own N-element period group. The
natural projection is given a concrete representative formula and is not assumed surjective.

[RW26, p. 14, Prop. 9] is background; the lattice identifications are proved below.
-/

noncomputable section

open Set
open scoped MatrixGroups

namespace SICLean.L4

def distributionOverlattice (B : DistributionBasis) (h : DistributionGroup B) :
    AddSubgroup (ℝ × ℝ) :=
  distributionLattice B ⊔ AddSubgroup.zmultiples (distributionRepresentative B h)

def distributionHalfVector (B : DistributionBasis) : ℝ × ℝ :=
  (B.scale / 2, B.scaleConj / 2)

/-- β₁ is unchanged and β₂ is divided by 2 in both embeddings. -/
def distributionDoubleBasis (B : DistributionBasis) (hc : 2 ∣ B.matrix 1 0) :
    DistributionBasis :=
  { matrix := modularDouble B.matrix hc
    tau := 2 * B.tau
    scale := B.scale / 2
    scaleConj := B.scaleConj / 2 }

/-- A concrete set map using a representative. Its mk law below proves descent when the actual
lattices are nested. No surjectivity is encoded. -/
def distributionProject (B C : DistributionBasis)
    (hP : distributionPeriodPoints B ≤ distributionPeriodPoints C)
    (g : DistributionGroup B) : DistributionGroup C :=
  distributionMk C (distributionRepresentative B g) (hP (Quotient.out g).property)

/-- J is independent of the chosen lift of h. [RW26, p. 14, Prop. 9]. -/
theorem distributionOverlattice_lift (B : DistributionBasis) (hB : B.Valid)
    (h : DistributionGroup B) (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B)
    (he : distributionMk B x hx = h) :
    distributionOverlattice B h = distributionLattice B ⊔ AddSubgroup.zmultiples x := by
  unfold distributionOverlattice
  apply distribution_sup_zmultiples_eq_aux
  have hr := distributionRepresentative_mk B hB x hx
  simpa only [he] using hr

/-- J/I has exactly the cosets 0,h, without identifying G_J with that quotient. [RW26, p. 14, Prop.
9]. -/
theorem distributionOverlattice_mem (B : DistributionBasis) (hB : B.Valid)
    (h : DistributionGroup B) (hh : h ≠ 0 ∧ h + h = 0) (x : ℝ × ℝ) :
    x ∈ distributionOverlattice B h ↔ x ∈ distributionLattice B ∨
      x - distributionRepresentative B h ∈ distributionLattice B := by
  exact distribution_sup_orderTwo_mem_aux (distributionLattice B) _ _
    (distributionRepresentative_two_aux B hB h hh.2)

/-- Same diagonal unit stabilizes J. This is a conclusion about the explicit subgroup, not a
postulated pseudolattice field. [RW26, p. 14, Prop. 9]. -/
theorem distributionOverlattice_period_stable (B : DistributionBasis) (hB : B.Valid)
    (h : DistributionGroup B) (hh : h ≠ 0 ∧ h + h = 0) :
    (distributionOverlattice B h).map (distributionPeriodAction B) =
      distributionOverlattice B h := by
  unfold distributionOverlattice
  rw [AddSubgroup.map_sup, (distributionLattice_period_stable B hB).1,
    AddMonoidHom.map_zmultiples]
  apply distribution_sup_zmultiples_eq_aux
  have hr : distributionRepresentative B h ∈ distributionPeriodPoints B :=
    (Quotient.out h).property
  rw [(distributionLattice_period_stable B hB).2] at hr
  exact hr

/-- I⊂J⊂(1/2)I. [RW26, p. 14, Prop. 9]. -/
theorem distributionOverlattice_bounds (B : DistributionBasis) (hB : B.Valid)
    (h : DistributionGroup B) (hh : h ≠ 0 ∧ h + h = 0) :
    distributionLattice B ≤ distributionOverlattice B h ∧
      ∀ x ∈ distributionOverlattice B h, (2 : ℤ) • x ∈ distributionLattice B := by
  refine ⟨le_sup_left, ?_⟩
  intro x hx
  have hr := distributionRepresentative_two_aux B hB h hh.2
  rcases (distributionOverlattice_mem B hB h hh x).mp hx with hx | hx
  · exact (distributionLattice B).zsmul_mem hx 2
  · convert (distributionLattice B).add_mem
      ((distributionLattice B).zsmul_mem hx 2) hr using 1 <;> abel

/-- The essential arbitrary-h existence theorem, including positivity at both embeddings. Adaptation
is not hidden in a record field. [RW26, p. 14, Prop. 9]. -/
theorem distribution_exists_adapted_basis (B : DistributionBasis) (hB : B.Valid)
    (h : DistributionGroup B) (hh : h ≠ 0 ∧ h + h = 0) :
    ∃ A : SL(2, ℤ), DistributionPositiveChange B A ∧
      2 ∣ (distributionRebase B A).matrix 1 0 ∧
      distributionRepresentative B h - distributionHalfVector (distributionRebase B A) ∈
        distributionLattice B := by
  simpa only [distributionHalfVector] using distribution_exists_adapted_raw_aux B hB h hh

/-- The half vector is a period point exactly in the needed even-c setting. [RW26, p. 2, (2)]. -/
theorem distributionHalfVector_mem (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) :
    distributionHalfVector B ∈ distributionPeriodPoints B := by
  obtain ⟨_, ⟨m, hm⟩, _⟩ := modularDouble_pos_parity B.matrix hB.1 hc
  obtain ⟨k, hk⟩ := hc
  have htwo : (2 : ℤ) • distributionHalfVector B = distributionBetaTwo B := by
    ext <;> simp [distributionHalfVector, distributionBetaTwo, zsmul_eq_mul] <;> ring
  have ht :
      (2 : ℤ) • distributionPeriodDifference B (distributionHalfVector B) =
      (2 : ℤ) • ((-k) • distributionBetaOne B + m • distributionBetaTwo B) := by
    calc
      _ = distributionPeriodDifference B ((2 : ℤ) • distributionHalfVector B) := by
        simp only [map_zsmul]
      _ = distributionPeriodDifference B (distributionBetaTwo B) := by rw [htwo]
      _ = (-B.matrix 1 0) • distributionBetaOne B +
          (B.matrix 0 0 - 1) • distributionBetaTwo B :=
        (distributionPeriodDifference_basis B hB).2
      _ = _ := by
        rw [hk, hm]
        simp only [smul_add, smul_smul, mul_neg, add_sub_cancel_right]
  have he := (zsmul_right_injective (by norm_num : (2 : ℤ) ≠ 0)) ht
  change distributionPeriodDifference B (distributionHalfVector B) ∈ distributionLattice B
  rw [he]
  exact (distributionLattice_mem_iff B _).2 ⟨![-k, m], rfl⟩

def distributionHalfClass (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) : DistributionGroup B :=
  distributionMk B (distributionHalfVector B) (distributionHalfVector_mem B hB hc)

/-- Exact order 2, not merely killed by 2. [RW26, p. 14, Prop. 9]. -/
theorem distributionHalfClass_orderTwo (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) :
    distributionHalfClass B hB hc ≠ 0 ∧
      distributionHalfClass B hB hc + distributionHalfClass B hB hc = 0 := by
  have hp := distributionHalfVector_mem B hB hc
  have hs : B.scale ≠ 0 := ne_of_gt hB.2.2.2.2.1
  have hs' : B.scaleConj ≠ 0 := ne_of_gt hB.2.2.2.2.2
  have hsep : B.tau - distributionConjugateTau B ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (distributionBasis_spectral B hB).2.1)
  have hcoord : distributionCoordinates B (distributionHalfVector B) 1 = (1 : ℝ) / 2 := by
    change
      (B.tau * ((B.scaleConj / 2) / B.scaleConj) -
        distributionConjugateTau B * ((B.scale / 2) / B.scale)) /
        (B.tau - distributionConjugateTau B) = 1 / 2
    field_simp [hs, hs', hsep] <;> ring
  have hn : distributionHalfVector B ∉ distributionLattice B := by
    intro hv
    have hi := ((distributionLattice_coordinates B hB _).mp hv) 1
    rw [hcoord] at hi
    have hi' : (2 : ℝ) *
        (distributionIntegerCoordinates B (distributionHalfVector B) 1 : ℝ) = 1 := by
      linarith
    have hiZ : (2 : ℤ) *
        distributionIntegerCoordinates B (distributionHalfVector B) 1 = 1 := by
      exact_mod_cast hi'
    omega
  constructor
  · exact fun he => hn ((distributionMk_eq_zero_aux B hB _ hp).mp he)
  · have hsum : distributionHalfVector B + distributionHalfVector B =
        distributionBetaTwo B := by
      ext <;> dsimp [distributionHalfVector, distributionBetaTwo] <;> ring
    calc
      _ = distributionMk B (distributionHalfVector B + distributionHalfVector B)
          ((distributionPeriodPoints B).add_mem hp hp) :=
        (distributionMk_add_aux B _ _ hp hp).symm
      _ = 0 := (distributionMk_eq_zero_aux B hB _ _).mpr (by
        rw [hsum]
        exact (distributionLattice_mem_iff B _).2 ⟨![0, 1], by simp⟩)

/-- The target basis has the same ε and the doubled conjugate fixed point. [RW26, p. 14, Prop. 9].
-/
theorem distributionDoubleBasis_valid (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) :
    (distributionDoubleBasis B hc).Valid ∧
      distributionPeriod (distributionDoubleBasis B hc) = distributionPeriod B ∧
      distributionConjugateTau (distributionDoubleBasis B hc) =
        2 * distributionConjugateTau B := by
  obtain ⟨ha, _, hc2, hd⟩ := modularDouble_entries B.matrix hc
  have hpos := (modularDouble_pos_parity B.matrix hB.1 hc).1
  have hcR : (2 : ℝ) * (modularDouble B.matrix hc 1 0 : ℝ) =
      (B.matrix 1 0 : ℝ) := by exact_mod_cast hc2
  have hcn : (modularDouble B.matrix hc 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  have hperiod : distributionPeriod (distributionDoubleBasis B hc) =
      distributionPeriod B := by
    change (modularDouble B.matrix hc 1 0 : ℝ) * (2 * B.tau) +
        (modularDouble B.matrix hc 1 1 : ℝ) =
      (B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)
    rw [hd]
    calc
      _ = (2 * (modularDouble B.matrix hc 1 0 : ℝ)) * B.tau +
          (B.matrix 1 1 : ℝ) := by ring
      _ = _ := by rw [hcR]
  have hconj : distributionConjugateTau (distributionDoubleBasis B hc) =
      2 * distributionConjugateTau B := by
    change
      ((modularDouble B.matrix hc 0 0 : ℝ) -
        (modularDouble B.matrix hc 1 1 : ℝ)) /
        (modularDouble B.matrix hc 1 0 : ℝ) - 2 * B.tau =
      2 * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) /
        (B.matrix 1 0 : ℝ) - B.tau)
    rw [ha, hd, ← hcR]
    field_simp [hcn] <;> ring
  refine ⟨?_, hperiod, hconj⟩
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_⟩
  · change 2 < modularDouble B.matrix hc 0 0 + modularDouble B.matrix hc 1 1
    simpa only [ha, hd] using hB.2.1
  · change etaMobius (modularDouble B.matrix hc) ((2 * B.tau : ℝ) : ℂ) =
      ((2 * B.tau : ℝ) : ℂ)
    have hf := (modularDouble_automorphy B.matrix hc (B.tau : ℂ)).2
    rw [hB.2.2.1] at hf
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hf
  · rw [hperiod]
    exact hB.2.2.2.1
  · exact div_pos hB.2.2.2.2.1 (by norm_num)
  · exact div_pos hB.2.2.2.2.2 (by norm_num)

/-- Exact lattice equality, not just an abstract isomorphism. [RW26, p. 14, Prop. 9]. -/
theorem distributionDoubleBasis_lattice (B : DistributionBasis) (hB : B.Valid)
    (hc : 2 ∣ B.matrix 1 0) :
    distributionLattice (distributionDoubleBasis B hc) =
      distributionLattice B ⊔ AddSubgroup.zmultiples (distributionHalfVector B) := by
  have hconj := (distributionDoubleBasis_valid B hB hc).2.2
  have hb1 : distributionBetaOne (distributionDoubleBasis B hc) =
      distributionBetaOne B := by
    apply Prod.ext
    · change B.scale / 2 * (2 * B.tau) = B.scale * B.tau
      ring
    · change B.scaleConj / 2 *
          distributionConjugateTau (distributionDoubleBasis B hc) =
        B.scaleConj * distributionConjugateTau B
      rw [hconj]
      ring
  have hb2 : distributionBetaTwo (distributionDoubleBasis B hc) =
      distributionHalfVector B := rfl
  have ht : distributionBetaTwo B = (2 : ℤ) • distributionHalfVector B := by
    ext <;> simp [distributionBetaTwo, distributionHalfVector, zsmul_eq_mul] <;> ring
  have hle : AddSubgroup.zmultiples (distributionBetaTwo B) ≤
      AddSubgroup.zmultiples (distributionHalfVector B) := by
    apply AddSubgroup.zmultiples_le.mpr
    rw [ht]
    exact AddSubgroup.zsmul_mem_zmultiples _ _
  change
    AddSubgroup.zmultiples (distributionBetaOne (distributionDoubleBasis B hc)) ⊔
        AddSubgroup.zmultiples (distributionBetaTwo (distributionDoubleBasis B hc)) =
      (AddSubgroup.zmultiples (distributionBetaOne B) ⊔
        AddSubgroup.zmultiples (distributionBetaTwo B)) ⊔
          AddSubgroup.zmultiples (distributionHalfVector B)
  rw [hb1, hb2, sup_assoc, sup_eq_right.mpr hle]

/-- P_I⊂P_J follows from the actual inclusion and common period. [RW26, p. 14, Prop. 9]. -/
theorem distributionPeriodPoints_mono (B C : DistributionBasis)
    (hε : distributionPeriod C = distributionPeriod B)
    (hI : distributionLattice B ≤ distributionLattice C) :
    distributionPeriodPoints B ≤ distributionPeriodPoints C := by
  intro x hx
  change distributionPeriodDifference B x ∈ distributionLattice B at hx
  change distributionPeriodDifference C x ∈ distributionLattice C
  have hD : distributionPeriodDifference C = distributionPeriodDifference B := by
    simp only [distributionPeriodDifference, hε]
  rw [hD]
  exact hI hx

/-- Quotient descent for any source representative. [RW26, p. 14, Prop. 9]. -/
theorem distributionProject_mk (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid)
    (hP : distributionPeriodPoints B ≤ distributionPeriodPoints C)
    (hI : distributionLattice B ≤ distributionLattice C)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionProject B C hP (distributionMk B x hx) = distributionMk C x (hP hx) := by
  unfold distributionProject
  apply (distributionMk_eq_iff C hC _ _ _ _).mpr
  exact hI (distributionRepresentative_mk B hB x hx)

/-- The natural map has kernel {0,h}; no surjectivity assertion. [RW26, p. 14, Prop. 9]. -/
theorem distributionProject_kernel (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (h : DistributionGroup B)
    (hh : h ≠ 0 ∧ h + h = 0)
    (hP : distributionPeriodPoints B ≤ distributionPeriodPoints C)
    (hJ : distributionLattice C = distributionOverlattice B h) (g : DistributionGroup B) :
    distributionProject B C hP g = 0 ↔ g = 0 ∨ g = h := by
  unfold distributionProject
  rw [distributionMk_eq_zero_aux C hC, hJ,
    distributionOverlattice_mem B hB h hh,
    distributionRepresentative_eq_zero_aux B hB,
    distributionRepresentative_sub_aux B hB]

/-- Arbitrary-h closure in the explicit presentation model. This proves existence of a target, not
finiteness of lattice classes. [RW26, p. 14, Prop. 9]. -/
theorem distribution_exists_overlattice_basis (B : DistributionBasis) (hB : B.Valid)
    (h : DistributionGroup B) (hh : h ≠ 0 ∧ h + h = 0) :
    ∃ C : DistributionBasis, C.Valid ∧ distributionPeriod C = distributionPeriod B ∧
      distributionLattice C = distributionOverlattice B h := by
  obtain ⟨A, hA, hc, hr⟩ := distribution_exists_adapted_basis B hB h hh
  have hAB := (distributionRebase_valid B hB A hA).1
  have hAI := (distributionRebase_lattice B hB A hA).1
  refine ⟨distributionDoubleBasis (distributionRebase B A) hc,
    (distributionDoubleBasis_valid _ hAB hc).1,
    (distributionDoubleBasis_valid _ hAB hc).2.1.trans
      (distributionRebase_valid B hB A hA).2.1, ?_⟩
  rw [distributionDoubleBasis_lattice _ hAB hc, hAI]
  exact (distribution_sup_zmultiples_eq_aux (distributionLattice B)
    (distributionRepresentative B h) (distributionHalfVector (distributionRebase B A)) hr).symm

#print distributionProject
#print distributionDoubleBasis
#check distribution_exists_adapted_basis
#check distributionProject_kernel

end SICLean.L4
