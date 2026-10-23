import SICLean.L4.ModularDivisor
import SICLean.L4.DistributionLatticeAux
import SICLean.L4.DistributionLatticeAux2

set_option autoImplicit false

/-!
# Explicit two-embedding lattice coordinates

This is a concrete Minkowski presentation, not a new abstract field library. A genuine real
quadratic pseudolattice is obtained by inserting its two real embeddings. Independent positive
scalings of the two embeddings are harmless and are retained as data.

[RW26, p. 2, (2), p. 12, Lemma 2, p. 14, Prop. 9] are the matrix background.

The period acts diagonally as (ε,ε⁻¹), never by one real scalar on ℝ². The actual group has N
elements. It is not a quotient of another member's group by its order-two subgroup. No analytic,
distribution, finiteness, or algebraicity conclusion is a field of the input data.
-/

noncomputable section

open Set
open scoped MatrixGroups

namespace SICLean.L4

/-- Raw matrix, first fixed point and the two second-basis-vector embeddings. -/
structure DistributionBasis where
  matrix : SL(2, ℤ)
  tau : ℝ
  scale : ℝ
  scaleConj : ℝ

/-- Explicit specialization by the first basis vector's first embedding and both embeddings of the
second basis vector. Compatibility is proved below. -/
def distributionBasisFromEmbeddings (M : SL(2, ℤ)) (β₁ β₂ β₂' : ℝ) :
    DistributionBasis :=
  ⟨M, β₁ / β₂, β₂, β₂'⟩

def distributionPeriod (B : DistributionBasis) : ℝ :=
  (B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)

/-- The other root of cX²+(d-a)X-b, not a chosen conjugation map. -/
def distributionConjugateTau (B : DistributionBasis) : ℝ :=
  ((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau

/-- Raw admissibility conditions only; target analytic laws are not included. -/
def DistributionBasis.Valid (B : DistributionBasis) : Prop :=
  0 < B.matrix 1 0 ∧ 2 < B.matrix 0 0 + B.matrix 1 1 ∧
    etaMobius B.matrix (B.tau : ℂ) = (B.tau : ℂ) ∧
    1 < distributionPeriod B ∧ 0 < B.scale ∧ 0 < B.scaleConj

def distributionBetaOne (B : DistributionBasis) : ℝ × ℝ :=
  (B.scale * B.tau, B.scaleConj * distributionConjugateTau B)

def distributionBetaTwo (B : DistributionBasis) : ℝ × ℝ :=
  (B.scale, B.scaleConj)

/-- The actual rank-two lattice, with no regularity or stability field. -/
def distributionLattice (B : DistributionBasis) : AddSubgroup (ℝ × ℝ) :=
  AddSubgroup.zmultiples (distributionBetaOne B) ⊔
    AddSubgroup.zmultiples (distributionBetaTwo B)

/-- Explicit inverse of the real two-by-two basis matrix. -/
def distributionCoordinates (B : DistributionBasis) (x : ℝ × ℝ) : Fin 2 → ℝ :=
  ![(x.1 / B.scale - x.2 / B.scaleConj) / (B.tau - distributionConjugateTau B),
    (B.tau * (x.2 / B.scaleConj) - distributionConjugateTau B * (x.1 / B.scale)) /
      (B.tau - distributionConjugateTau B)]

/-- A total concrete integer-coordinate prescription. Exactness on the lattice is a theorem, not a
choice of integers satisfying a desired law. -/
def distributionIntegerCoordinates (B : DistributionBasis) (x : ℝ × ℝ) : Fin 2 → ℤ :=
  fun i => ⌊distributionCoordinates B x i⌋

/-- Multiplication by ε⁻¹-1 in both embeddings: second factor is ε-1. -/
def distributionPeriodDifference (B : DistributionBasis) : (ℝ × ℝ) →+ (ℝ × ℝ) :=
  (AddMonoidHom.mulLeft ((distributionPeriod B)⁻¹ - 1)).prodMap
    (AddMonoidHom.mulLeft (distributionPeriod B - 1))

/-- The unit action, distinguished from the difference used in E's index. -/
def distributionPeriodAction (B : DistributionBasis) : (ℝ × ℝ) →+ (ℝ × ℝ) :=
  (AddMonoidHom.mulLeft (distributionPeriod B)).prodMap
    (AddMonoidHom.mulLeft ((distributionPeriod B)⁻¹))

/-- (ε⁻¹-1)⁻¹I = (ε-1)⁻¹I, once period stability has been proved. -/
def distributionPeriodPoints (B : DistributionBasis) : AddSubgroup (ℝ × ℝ) :=
  (distributionLattice B).comap (distributionPeriodDifference B)

/-- `addSubgroupOf` has an unconditional concrete body. The theorem
`distributionLattice_le_periodPoints` ensures it is the full I, not I∩P. -/
abbrev DistributionGroup (B : DistributionBasis) :=
  distributionPeriodPoints B ⧸
    (distributionLattice B).addSubgroupOf (distributionPeriodPoints B)

/-- A representative, not a function chosen to satisfy distribution. -/
def distributionRepresentative (B : DistributionBasis) (g : DistributionGroup B) : ℝ × ℝ :=
  (Quotient.out g).val

def distributionMk (B : DistributionBasis) (x : ℝ × ℝ)
    (hx : x ∈ distributionPeriodPoints B) : DistributionGroup B :=
  QuotientAddGroup.mk (⟨x, hx⟩ : distributionPeriodPoints B)

section BasicAlgebra

lemma dBasis_c_pos (B : DistributionBasis) (hB : B.Valid) :
    0 < (B.matrix 1 0 : ℝ) := by
  exact_mod_cast hB.1

lemma dBasis_trace (B : DistributionBasis) (hB : B.Valid) :
    2 < B.matrix 0 0 + B.matrix 1 1 := hB.2.1

lemma dBasis_fix (B : DistributionBasis) (hB : B.Valid) :
    etaMobius B.matrix (B.tau : ℂ) = (B.tau : ℂ) := hB.2.2.1

lemma dBasis_period_gt (B : DistributionBasis) (hB : B.Valid) :
    1 < distributionPeriod B := hB.2.2.2.1

lemma dBasis_period_pos (B : DistributionBasis) (hB : B.Valid) :
    0 < distributionPeriod B := lt_trans zero_lt_one (dBasis_period_gt B hB)

lemma dBasis_scale_pos (B : DistributionBasis) (hB : B.Valid) : 0 < B.scale :=
  hB.2.2.2.2.1

lemma dBasis_scaleConj_pos (B : DistributionBasis) (hB : B.Valid) : 0 < B.scaleConj :=
  hB.2.2.2.2.2

lemma dBasis_quad (B : DistributionBasis) (hB : B.Valid) :
    (B.matrix 1 0 : ℝ) * B.tau ^ 2 +
        ((B.matrix 1 1 : ℝ) - (B.matrix 0 0 : ℝ)) * B.tau - (B.matrix 0 1 : ℝ) = 0 :=
  dl_quad B.matrix B.tau (dBasis_period_pos B hB) (dBasis_fix B hB)

lemma dBasis_conj_lt (B : DistributionBasis) (hB : B.Valid) :
    distributionConjugateTau B < B.tau :=
  dl_conj_lt B.matrix B.tau (dBasis_c_pos B hB) (dBasis_period_gt B hB) (dBasis_quad B hB)

lemma dBasis_conj_ne (B : DistributionBasis) (hB : B.Valid) :
    B.tau - distributionConjugateTau B ≠ 0 := by
  have := dBasis_conj_lt B hB
  linarith

lemma dBasis_period_inv (B : DistributionBasis) (hB : B.Valid) :
    (distributionPeriod B)⁻¹ =
      (B.matrix 0 0 : ℝ) - (B.matrix 1 0 : ℝ) * B.tau :=
  dl_period_inv B.matrix B.tau (dBasis_quad B hB)

lemma dBasis_conj_period (B : DistributionBasis) (hB : B.Valid) :
    (B.matrix 1 0 : ℝ) * distributionConjugateTau B + (B.matrix 1 1 : ℝ) =
      (distributionPeriod B)⁻¹ :=
  dl_conj_period B.matrix B.tau (ne_of_gt (dBasis_c_pos B hB)) (dBasis_quad B hB)

lemma dBasis_period_inv' (B : DistributionBasis) (hB : B.Valid) :
    ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ =
      (B.matrix 0 0 : ℝ) - (B.matrix 1 0 : ℝ) * B.tau := by
  simpa [distributionPeriod] using dBasis_period_inv B hB

lemma dBasis_period_eq_conj (B : DistributionBasis) (hB : B.Valid) :
    (B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ) =
      (B.matrix 0 0 : ℝ) - (B.matrix 1 0 : ℝ) *
        (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) :=
  dl_period_eq_conj B.matrix B.tau (ne_of_gt (dBasis_c_pos B hB))

lemma dBasis_betaOne_mem (B : DistributionBasis) :
    distributionBetaOne B ∈ distributionLattice B :=
  AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples _)

lemma dBasis_betaTwo_mem (B : DistributionBasis) :
    distributionBetaTwo B ∈ distributionLattice B :=
  AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

/-- Coordinates are the actual inverse of the basis matrix. -/
theorem distributionCoordinates_beta (B : DistributionBasis) (hB : B.Valid)
    (u : Fin 2 → ℝ) :
    distributionCoordinates B
        (u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B) = u := by
  funext i
  have hτ : B.tau - distributionConjugateTau B ≠ 0 := dBasis_conj_ne B hB
  have hs : B.scale ≠ 0 := ne_of_gt (dBasis_scale_pos B hB)
  have hs' : B.scaleConj ≠ 0 := ne_of_gt (dBasis_scaleConj_pos B hB)
  fin_cases i <;>
    simp [distributionCoordinates, distributionBetaOne, distributionBetaTwo] <;>
    field_simp <;> ring

end BasicAlgebra

/-- Spectral arithmetic also proves the stated basis orientation is >0. [RW26, p. 12]. -/
theorem distributionBasis_spectral (B : DistributionBasis) (hB : B.Valid) :
    Irrational B.tau ∧ distributionConjugateTau B < B.tau ∧
      (B.matrix 1 0 : ℝ) * distributionConjugateTau B + (B.matrix 1 1 : ℝ) =
        (distributionPeriod B)⁻¹ ∧
      distributionPeriod B + (distributionPeriod B)⁻¹ =
        (B.matrix 0 0 : ℝ) + (B.matrix 1 1 : ℝ) := by
  refine ⟨?_, dBasis_conj_lt B hB, dBasis_conj_period B hB, ?_⟩
  · exact modularPhi_real_fixedPoint_irrational B.matrix hB.1 hB.2.1 B.tau
      (dBasis_period_pos B hB) (dBasis_fix B hB)
  · exact dl_period_sum B.matrix B.tau (dBasis_quad B hB)

/-- Inverse matrix formula for all real pairs; [RW26, p. 2, (2)]. -/
theorem distributionCoordinates_reconstruct (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) :
    x = distributionCoordinates B x 0 • distributionBetaOne B +
      distributionCoordinates B x 1 • distributionBetaTwo B := by
  have hτ : B.tau - distributionConjugateTau B ≠ 0 := dBasis_conj_ne B hB
  have hs : B.scale ≠ 0 := ne_of_gt (dBasis_scale_pos B hB)
  have hs' : B.scaleConj ≠ 0 := ne_of_gt (dBasis_scaleConj_pos B hB)
  ext <;> simp [distributionCoordinates, distributionBetaOne, distributionBetaTwo] <;>
    field_simp <;> ring

/-- Actual integer span membership. [RW26, p. 2, (2)]. -/
theorem distributionLattice_mem_iff (B : DistributionBasis) (x : ℝ × ℝ) :
    x ∈ distributionLattice B ↔ ∃ u : Fin 2 → ℤ,
      x = u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B := by
  rw [distributionLattice, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rw [AddSubgroup.mem_zmultiples_iff] at hy hz
    obtain ⟨k, rfl⟩ := hy
    obtain ⟨l, rfl⟩ := hz
    exact ⟨![k, l], by simp⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u 0 • distributionBetaOne B,
      AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _,
      u 1 • distributionBetaTwo B,
      AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _, rfl⟩

/-- Floor is exact exactly on the lattice. [RW26, p. 2, (2)]. -/
theorem distributionLattice_coordinates (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) :
    x ∈ distributionLattice B ↔ ∀ i : Fin 2,
      distributionCoordinates B x i = (distributionIntegerCoordinates B x i : ℝ) := by
  constructor
  · intro hx
    rw [distributionLattice_mem_iff] at hx
    obtain ⟨u, rfl⟩ := hx
    intro i
    have hE : (u 0 : ℤ) • distributionBetaOne B + (u 1 : ℤ) • distributionBetaTwo B =
        (u 0 : ℝ) • distributionBetaOne B + (u 1 : ℝ) • distributionBetaTwo B := by
      rw [← Int.cast_smul_eq_zsmul ℝ (u 0) (distributionBetaOne B),
        ← Int.cast_smul_eq_zsmul ℝ (u 1) (distributionBetaTwo B)]
    have hcoord := distributionCoordinates_beta B hB (fun i => (u i : ℝ))
    have hcoe : distributionCoordinates B
        ((u 0 : ℤ) • distributionBetaOne B + (u 1 : ℤ) • distributionBetaTwo B) i =
        (u i : ℝ) := by
      rw [hE]
      exact congrFun hcoord i
    simp only [distributionIntegerCoordinates]
    rw [hcoe, Int.floor_intCast]
  · intro h
    rw [distributionLattice_mem_iff]
    refine ⟨distributionIntegerCoordinates B x, ?_⟩
    have hrec := distributionCoordinates_reconstruct B hB x
    rw [h 0, h 1] at hrec
    calc x = (distributionIntegerCoordinates B x 0 : ℝ) • distributionBetaOne B +
          (distributionIntegerCoordinates B x 1 : ℝ) • distributionBetaTwo B := hrec
      _ = distributionIntegerCoordinates B x 0 • distributionBetaOne B +
          distributionIntegerCoordinates B x 1 • distributionBetaTwo B := by
        rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

/-- ε⁻¹ has matrix (d,-b;-c,a). Signs match E's ε⁻¹-1 convention. [RW26, p. 2, (2)]. -/
theorem distributionPeriodDifference_basis (B : DistributionBasis) (hB : B.Valid) :
    distributionPeriodDifference B (distributionBetaOne B) =
        (B.matrix 1 1 - 1) • distributionBetaOne B -
          B.matrix 0 1 • distributionBetaTwo B ∧
      distributionPeriodDifference B (distributionBetaTwo B) =
        (-B.matrix 1 0) • distributionBetaOne B +
          (B.matrix 0 0 - 1) • distributionBetaTwo B := by
  have hquad := dBasis_quad B hB
  have hc : (B.matrix 1 0 : ℝ) ≠ 0 := ne_of_gt (dBasis_c_pos B hB)
  have h1 := dl_diff_first_tau B.matrix B.tau hquad
  have h2 := dl_diff_second_tau_conj B.matrix B.tau hc hquad
  have hinv := dBasis_period_inv' B hB
  have heq := dBasis_period_eq_conj B hB
  constructor
  · rw [← Int.cast_smul_eq_zsmul ℝ (B.matrix 1 1 - 1) (distributionBetaOne B),
      ← Int.cast_smul_eq_zsmul ℝ (B.matrix 0 1) (distributionBetaTwo B)]
    push_cast
    ext
    · simp [distributionPeriodDifference, distributionBetaOne, distributionBetaTwo,
        distributionPeriod, distributionConjugateTau]
      calc (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ - 1) * (B.scale * B.tau)
          = ((((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ - 1) * B.tau) * B.scale := by ring
        _ = (((B.matrix 1 1 : ℝ) - 1) * B.tau - (B.matrix 0 1 : ℝ)) * B.scale := by rw [h1]
        _ = ((B.matrix 1 1 : ℝ) - 1) * (B.scale * B.tau) - (B.matrix 0 1 : ℝ) * B.scale := by ring
    · simp [distributionPeriodDifference, distributionBetaOne, distributionBetaTwo,
        distributionPeriod, distributionConjugateTau]
      calc (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) - 1) *
            (B.scaleConj * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau))
          = ((((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) - 1) *
            (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau)) * B.scaleConj := by ring
        _ = (((B.matrix 1 1 : ℝ) - 1) *
            (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) - (B.matrix 0 1 : ℝ)) * B.scaleConj := by rw [h2]
        _ = ((B.matrix 1 1 : ℝ) - 1) *
            (B.scaleConj * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau)) -
            (B.matrix 0 1 : ℝ) * B.scaleConj := by ring
  · rw [← Int.cast_smul_eq_zsmul ℝ (-B.matrix 1 0) (distributionBetaOne B),
      ← Int.cast_smul_eq_zsmul ℝ (B.matrix 0 0 - 1) (distributionBetaTwo B)]
    push_cast
    ext
    · simp [distributionPeriodDifference, distributionBetaOne, distributionBetaTwo,
        distributionPeriod, distributionConjugateTau]
      rw [hinv]
      ring
    · simp [distributionPeriodDifference, distributionBetaOne, distributionBetaTwo,
        distributionPeriod, distributionConjugateTau]
      rw [heq]
      ring

/-- Establish the inclusion before treating the quotient as P/I. [RW26, p. 2, (2)]. -/
theorem distributionLattice_le_periodPoints (B : DistributionBasis) (hB : B.Valid) :
    distributionLattice B ≤ distributionPeriodPoints B := by
  intro x hx
  simp only [distributionPeriodPoints, AddSubgroup.mem_comap]
  rw [distributionLattice_mem_iff] at hx
  obtain ⟨u, rfl⟩ := hx
  have hm1 : distributionPeriodDifference B (distributionBetaOne B) ∈
      distributionLattice B := by
    rw [(distributionPeriodDifference_basis B hB).1]
    exact AddSubgroup.sub_mem _ (AddSubgroup.zsmul_mem _ (dBasis_betaOne_mem B) _)
      (AddSubgroup.zsmul_mem _ (dBasis_betaTwo_mem B) _)
  have hm2 : distributionPeriodDifference B (distributionBetaTwo B) ∈
      distributionLattice B := by
    rw [(distributionPeriodDifference_basis B hB).2]
    exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ (dBasis_betaOne_mem B) _)
      (AddSubgroup.zsmul_mem _ (dBasis_betaTwo_mem B) _)
  have hmap : distributionPeriodDifference B
      (u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B) =
      u 0 • distributionPeriodDifference B (distributionBetaOne B) +
        u 1 • distributionPeriodDifference B (distributionBetaTwo B) := by
    rw [map_add, map_zsmul, map_zsmul]
  rw [hmap]
  exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hm1 _)
    (AddSubgroup.zsmul_mem _ hm2 _)

/-- The actual integer indices used in the finite-product definition. [RW26, p. 2, (2)]. -/
theorem distributionPeriodPoints_expansion (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionPeriodDifference B x =
      distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 •
          distributionBetaOne B +
        distributionIntegerCoordinates B (distributionPeriodDifference B x) 1 •
          distributionBetaTwo B := by
  simp only [distributionPeriodPoints, AddSubgroup.mem_comap] at hx
  have h4 := (distributionLattice_coordinates B hB (distributionPeriodDifference B x)).mp hx
  have hrec := distributionCoordinates_reconstruct B hB (distributionPeriodDifference B x)
  have h0 : distributionCoordinates B (distributionPeriodDifference B x) 0 =
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 : ℝ) := h4 0
  have h1 : distributionCoordinates B (distributionPeriodDifference B x) 1 =
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 1 : ℝ) := h4 1
  rw [h0, h1] at hrec
  conv_lhs => rw [hrec]
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

/-- Exact quotient equality, without an analytic hypothesis; [RW26, p. 2, (2)]. -/
theorem distributionMk_eq_iff (B : DistributionBasis) (hB : B.Valid)
    (x y : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B)
    (hy : y ∈ distributionPeriodPoints B) :
    distributionMk B x hx = distributionMk B y hy ↔ x - y ∈ distributionLattice B := by
  rw [distributionMk, distributionMk, QuotientAddGroup.eq_iff_sub_mem]
  simp [AddSubgroup.mem_addSubgroupOf]

/-- The specified quotient representative has the correct lattice class. [RW26, p. 2, (2)]. -/
theorem distributionRepresentative_mk (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionRepresentative B (distributionMk B x hx) - x ∈ distributionLattice B := by
  set g := distributionMk B x hx with hg
  have hout : (Quotient.out g).val - x ∈ distributionLattice B := by
    have hmk : distributionMk B (Quotient.out g).val (Quotient.out g).2 = g :=
      Quotient.out_eq g
    exact (distributionMk_eq_iff B hB (Quotient.out g).val x (Quotient.out g).2 hx).mp (by
      rw [hmk, hg])
  simpa [distributionRepresentative, hg] using hout

/-- Every actual group, including target groups, has N elements. [RW26, p. 2]. In particular G_J
cannot be defined as G_I/⟨h⟩. -/
theorem distributionGroup_finite_card (B : DistributionBasis) (hB : B.Valid) :
    Finite (DistributionGroup B) ∧
      Nat.card (DistributionGroup B) = (B.matrix 0 0 + B.matrix 1 1 - 2).toNat := by
  have hε : distributionPeriod B - 1 ≠ 0 := by
    have := dBasis_period_gt B hB
    linarith
  have hεinv : (distributionPeriod B)⁻¹ - 1 ≠ 0 := by
    have := inv_lt_one_of_one_lt₀ (dBasis_period_gt B hB)
    linarith
  have hf : Function.Bijective (distributionPeriodDifference B) := by
    constructor
    · intro x y hxy
      apply Prod.ext
      · have h := congrArg Prod.fst hxy
        change ((distributionPeriod B)⁻¹ - 1) * x.1 =
          ((distributionPeriod B)⁻¹ - 1) * y.1 at h
        exact mul_left_cancel₀ hεinv h
      · have h := congrArg Prod.snd hxy
        change (distributionPeriod B - 1) * x.2 =
          (distributionPeriod B - 1) * y.2 at h
        exact mul_left_cancel₀ hε h
    · intro x
      refine ⟨(x.1 / ((distributionPeriod B)⁻¹ - 1),
        x.2 / (distributionPeriod B - 1)), ?_⟩
      apply Prod.ext
      · exact mul_div_cancel₀ x.1 hεinv
      · exact mul_div_cancel₀ x.2 hε
  have hinj : Function.Injective (fun u : Fin 2 → ℤ =>
      u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B) := by
    intro u v huv
    have hu := distributionCoordinates_beta B hB (fun i => (u i : ℝ))
    have hv := distributionCoordinates_beta B hB (fun i => (v i : ℝ))
    simp only [Int.cast_smul_eq_zsmul] at hu hv
    have hcoords := congrArg (distributionCoordinates B) huv
    rw [hu, hv] at hcoords
    funext i
    exact_mod_cast congrFun hcoords i
  have hcard := DistributionLatticeAux2.card_comap_quotient_pair
    (distributionLattice B) (distributionBetaOne B) (distributionBetaTwo B)
    (distributionLattice_mem_iff B) hinj (distributionPeriodDifference B) hf
    (distributionLattice_le_periodPoints B hB)
    (B.matrix 1 1 - 1) (-B.matrix 1 0) (-B.matrix 0 1) (B.matrix 0 0 - 1)
    (by simpa only [sub_eq_add_neg, neg_zsmul] using
      (distributionPeriodDifference_basis B hB).1)
    (distributionPeriodDifference_basis B hB).2
  have hdet : (B.matrix 1 1 - 1) * (B.matrix 0 0 - 1) -
      (-B.matrix 1 0) * (-B.matrix 0 1) = -(B.matrix 0 0 + B.matrix 1 1 - 2) := by
    have h := Matrix.SpecialLinearGroup.det_coe B.matrix
    rw [Matrix.det_fin_two] at h
    nlinarith
  have hN : 0 < B.matrix 0 0 + B.matrix 1 1 - 2 := by
    have := dBasis_trace B hB
    omega
  have hcard' : Nat.card (DistributionGroup B) =
      (B.matrix 0 0 + B.matrix 1 1 - 2).toNat := by
    change Nat.card (DistributionGroup B) = _ at hcard
    rw [hdet, Int.natAbs_neg] at hcard
    exact hcard.trans (by omega)
  refine ⟨?_, hcard'⟩
  exact Nat.finite_of_card_ne_zero (by rw [hcard']; omega)

/-- Nonzero real class iff the normalized first embedding is off the pseudolattice. This equivalence
is proved, not assumed. [RW26, p. 6]. -/
theorem distributionPeriodPoints_first_lattice_iff (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    ((x.1 / B.scale : ℝ) : ℂ) ∈ modularPhiPseudoLattice (B.tau : ℂ) ↔
      x ∈ distributionLattice B := by

  have hquad := dBasis_quad B hB
  have hc : (B.matrix 1 0 : ℝ) ≠ 0 := ne_of_gt (dBasis_c_pos B hB)
  have hs : B.scale ≠ 0 := ne_of_gt (dBasis_scale_pos B hB)
  have hs' : B.scaleConj ≠ 0 := ne_of_gt (dBasis_scaleConj_pos B hB)
  have hper : distributionPeriod B ≠ 0 := ne_of_gt (dBasis_period_pos B hB)
  have hper1 : distributionPeriod B - 1 ≠ 0 := by
    have := dBasis_period_gt B hB; linarith
  have hirr : Irrational B.tau :=
    modularPhi_real_fixedPoint_irrational B.matrix hB.1 hB.2.1 B.tau
      (dBasis_period_pos B hB) (dBasis_fix B hB)
  constructor
  · intro hz
    rw [distributionLattice_mem_iff]
    rw [modularPhiPseudoLattice, Set.mem_ofPred_eq] at hz
    obtain ⟨k, l, hkl⟩ := hz
    have hzR : x.1 / B.scale = (k : ℝ) * B.tau + (l : ℝ) := by
      have := congrArg Complex.re hkl
      simpa using this
    simp only [distributionPeriodPoints, AddSubgroup.mem_comap] at hx
    rw [distributionLattice_mem_iff] at hx
    obtain ⟨u, hu⟩ := hx
    have hfst : ((distributionPeriod B)⁻¹ - 1) * x.1 =
        (u 0 : ℝ) * (B.scale * B.tau) + (u 1 : ℝ) * B.scale := by
      have h := congrArg Prod.fst hu
      simpa [distributionPeriodDifference, distributionBetaOne, distributionBetaTwo,
        zsmul_eq_mul] using h
    have hsnd : (distributionPeriod B - 1) * x.2 =
        (u 0 : ℝ) * (B.scaleConj * distributionConjugateTau B) + (u 1 : ℝ) * B.scaleConj := by
      have h := congrArg Prod.snd hu
      simpa [distributionPeriodDifference, distributionBetaOne, distributionBetaTwo,
        zsmul_eq_mul] using h
    have hfst' : (((distributionPeriod B)⁻¹ - 1) * (x.1 / B.scale)) =
        (u 0 : ℝ) * B.tau + (u 1 : ℝ) := by
      have h := congrArg (fun y : ℝ => y / B.scale) hfst
      have hL : (((distributionPeriod B)⁻¹ - 1) * x.1) / B.scale =
          ((distributionPeriod B)⁻¹ - 1) * (x.1 / B.scale) := by ring
      have hR : ((u 0 : ℝ) * (B.scale * B.tau) + (u 1 : ℝ) * B.scale) / B.scale =
          (u 0 : ℝ) * B.tau + (u 1 : ℝ) := by
        field_simp [hs]
      rw [hL, hR] at h
      simpa using h
    have hcoeff : (((distributionPeriod B)⁻¹ - 1) * ((k : ℝ) * B.tau + (l : ℝ))) =
        (u 0 : ℝ) * B.tau + (u 1 : ℝ) := by
      rw [← hzR]
      exact hfst'
    have hexp := dl_inv_sub_mul_linear B.matrix B.tau hquad (k : ℝ) (l : ℝ)
    simp only [distributionPeriod] at hcoeff
    rw [hexp] at hcoeff
    have hzero : (((B.matrix 1 1 : ℝ) - 1) * (k : ℝ) - (B.matrix 1 0 : ℝ) * (l : ℝ) - (u 0 : ℝ)) * B.tau +
        (((B.matrix 0 0 : ℝ) - 1) * (l : ℝ) - (B.matrix 0 1 : ℝ) * (k : ℝ) - (u 1 : ℝ)) = 0 := by
      linarith [hcoeff]
    have hcoef := dl_int_coeff_zero hirr
      (((B.matrix 1 1) - 1) * k - (B.matrix 1 0) * l - u 0)
      (((B.matrix 0 0) - 1) * l - (B.matrix 0 1) * k - u 1) (by
        push_cast
        linarith [hzero])
    have hu0 : (u 0 : ℝ) = ((B.matrix 1 1 : ℝ) - 1) * (k : ℝ) - (B.matrix 1 0 : ℝ) * (l : ℝ) := by
      have h0 : ((B.matrix 1 1 - 1) * k - (B.matrix 1 0) * l - u 0 : ℤ) = 0 := hcoef.1
      have h0R : (((B.matrix 1 1 : ℝ) - 1) * (k : ℝ) - (B.matrix 1 0 : ℝ) * (l : ℝ) - (u 0 : ℝ)) = 0 := by
        exact_mod_cast h0
      linarith
    have hu1 : (u 1 : ℝ) = ((B.matrix 0 0 : ℝ) - 1) * (l : ℝ) - (B.matrix 0 1 : ℝ) * (k : ℝ) := by
      have h0 : ((B.matrix 0 0 - 1) * l - (B.matrix 0 1) * k - u 1 : ℤ) = 0 := hcoef.2
      have h0R : (((B.matrix 0 0 : ℝ) - 1) * (l : ℝ) - (B.matrix 0 1 : ℝ) * (k : ℝ) - (u 1 : ℝ)) = 0 := by
        exact_mod_cast h0
      linarith
    have hsecond : (u 0 : ℝ) * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) + (u 1 : ℝ) =
        (distributionPeriod B - 1) * ((k : ℝ) * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) + (l : ℝ)) := by
      simp only [distributionPeriod]
      rw [dl_sub_mul_linear_conj B.matrix B.tau hc hquad (k : ℝ) (l : ℝ)]
      rw [hu0, hu1]
    refine ⟨![k, l], ?_⟩
    ext
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      have h1 : x.1 = B.scale * ((k : ℝ) * B.tau + (l : ℝ)) := by
        rw [← hzR]
        field_simp
      rw [h1]
      simp [distributionBetaOne, distributionBetaTwo]
      ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      have hx2 : x.2 = B.scaleConj * ((u 0 : ℝ) *
          (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) + (u 1 : ℝ)) /
          (distributionPeriod B - 1) := by
        have hrec : (distributionPeriod B - 1) * x.2 = B.scaleConj *
            ((u 0 : ℝ) * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) + (u 1 : ℝ)) := by
          rw [hsnd]
          simp only [distributionConjugateTau]
          ring
        have h := congrArg (fun y : ℝ => y / (distributionPeriod B - 1)) hrec
        have hx : ((distributionPeriod B - 1) * x.2) / (distributionPeriod B - 1) = x.2 := by
          field_simp [hper1]
        rw [hx] at h
        exact h
      rw [hx2, hsecond]
      simp [distributionBetaOne, distributionBetaTwo, distributionConjugateTau]
      field_simp [hper1]
  · intro hxI
    rw [distributionLattice_mem_iff] at hxI
    obtain ⟨u, rfl⟩ := hxI
    rw [modularPhiPseudoLattice, Set.mem_ofPred_eq]
    refine ⟨u 0, u 1, ?_⟩
    have hx1 : (u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B).1 / B.scale =
        (u 0 : ℝ) * B.tau + (u 1 : ℝ) := by
      simp [distributionBetaOne, distributionBetaTwo]
      push_cast
      field_simp
    rw [hx1]
    push_cast
    ring

/-- The first embedding loses no actual period-point information. [RW26, p. 2, (2)]. -/
theorem distributionPeriodPoints_first_injective (B : DistributionBasis) (hB : B.Valid)
    (x y : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B)
    (hy : y ∈ distributionPeriodPoints B) (hxy : x.1 = y.1) : x = y := by

  simp only [distributionPeriodPoints, AddSubgroup.mem_comap] at hx hy
  rw [distributionLattice_mem_iff] at hx hy
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  have hscale : B.scale ≠ 0 := ne_of_gt (dBasis_scale_pos B hB)
  have hfirst : ((u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B).1) =
      ((v 0 • distributionBetaOne B + v 1 • distributionBetaTwo B).1) := by
    rw [← hu, ← hv]
    simp [distributionPeriodDifference, hxy]
  have hfu : ((u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B).1) =
      B.scale * ((u 0 : ℝ) * B.tau + (u 1 : ℝ)) := by
    simp [distributionBetaOne, distributionBetaTwo]
    push_cast
    ring
  have hfv : ((v 0 • distributionBetaOne B + v 1 • distributionBetaTwo B).1) =
      B.scale * ((v 0 : ℝ) * B.tau + (v 1 : ℝ)) := by
    simp [distributionBetaOne, distributionBetaTwo]
    push_cast
    ring
  have hcoeff : (u 0 : ℝ) * B.tau + (u 1 : ℝ) = (v 0 : ℝ) * B.tau + (v 1 : ℝ) := by
    have h := hfirst
    rw [hfu, hfv] at h
    exact mul_left_cancel₀ hscale h
  have huv : u = v := by
    have hulp := dl_int_coeff_eq (modularPhi_real_fixedPoint_irrational B.matrix hB.1 hB.2.1 B.tau
      (dBasis_period_pos B hB) (dBasis_fix B hB)) (u 0) (u 1) (v 0) (v 1) hcoeff
    funext i
    fin_cases i
    · exact hulp.1
    · exact hulp.2
  have hD : distributionPeriodDifference B x = distributionPeriodDifference B y := by
    rw [hu, hv, huv]
  have hx1 : x.1 = y.1 := hxy
  have hx2 : x.2 = y.2 := by
    have hε : (distributionPeriod B - 1) ≠ 0 := by
      have := dBasis_period_gt B hB
      linarith
    have h := congrArg Prod.snd hD
    change (distributionPeriod B - 1) * x.2 = (distributionPeriod B - 1) * y.2 at h
    exact mul_left_cancel₀ hε h
  ext <;> assumption


/-- The period action preserves the actual lattice. -/
theorem distributionLattice_map_action (B : DistributionBasis) (hB : B.Valid) :
    (distributionLattice B).map (distributionPeriodAction B) = distributionLattice B := by

  have hquad := dBasis_quad B hB
  have hc : (B.matrix 1 0 : ℝ) ≠ 0 := ne_of_gt (dBasis_c_pos B hB)
  have hmul := dl_period_mul_tau B.matrix B.tau hquad
  have hinv := dl_period_inv_mul_conj B.matrix B.tau hc hquad
  have hconj := dl_conj_period B.matrix B.tau hc hquad
  have hdet : (B.matrix 0 0) * (B.matrix 1 1) - (B.matrix 0 1) * (B.matrix 1 0) = (1 : ℤ) := by
    have := dl_det B.matrix
    exact_mod_cast this
  have hA1 : distributionPeriodAction B (distributionBetaOne B) =
      (B.matrix 0 0) • distributionBetaOne B + (B.matrix 0 1) • distributionBetaTwo B := by
    rw [← Int.cast_smul_eq_zsmul ℝ (B.matrix 0 0) (distributionBetaOne B),
        ← Int.cast_smul_eq_zsmul ℝ (B.matrix 0 1) (distributionBetaTwo B)]
    push_cast
    ext
    · simp [distributionPeriodAction, distributionBetaOne, distributionBetaTwo, distributionPeriod]
      calc ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) * (B.scale * B.tau)
          = (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) * B.tau) * B.scale := by ring
        _ = ((B.matrix 0 0 : ℝ) * B.tau + (B.matrix 0 1 : ℝ)) * B.scale := by rw [hmul]
        _ = (B.matrix 0 0 : ℝ) * (B.scale * B.tau) + (B.matrix 0 1 : ℝ) * B.scale := by ring
    · simp [distributionPeriodAction, distributionBetaOne, distributionBetaTwo, distributionPeriod,
        distributionConjugateTau]
      calc (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
            (B.scaleConj * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau)))
          = ((((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
            (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau))) * B.scaleConj := by ring
        _ = ((B.matrix 0 0 : ℝ) * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) +
            (B.matrix 0 1 : ℝ)) * B.scaleConj := by rw [hinv]
        _ = (B.matrix 0 0 : ℝ) * (B.scaleConj * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau)) +
            (B.matrix 0 1 : ℝ) * B.scaleConj := by ring
  have hA2 : distributionPeriodAction B (distributionBetaTwo B) =
      (B.matrix 1 0) • distributionBetaOne B + (B.matrix 1 1) • distributionBetaTwo B := by
    rw [← Int.cast_smul_eq_zsmul ℝ (B.matrix 1 0) (distributionBetaOne B),
        ← Int.cast_smul_eq_zsmul ℝ (B.matrix 1 1) (distributionBetaTwo B)]
    push_cast
    ext
    · simp [distributionPeriodAction, distributionBetaOne, distributionBetaTwo, distributionPeriod]
      ring
    · simp [distributionPeriodAction, distributionBetaOne, distributionBetaTwo, distributionPeriod,
        distributionConjugateTau]
      rw [← hconj]
      ring
  apply le_antisymm
  · rintro y hy
    rw [AddSubgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [distributionLattice_mem_iff] at hx
    obtain ⟨u, rfl⟩ := hx
    have hmap : distributionPeriodAction B
        (u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B) =
        u 0 • distributionPeriodAction B (distributionBetaOne B) +
          u 1 • distributionPeriodAction B (distributionBetaTwo B) := by
      rw [map_add, map_zsmul, map_zsmul]
    rw [hmap, hA1, hA2, distributionLattice_mem_iff]
    refine ⟨![B.matrix 0 0 * u 0 + B.matrix 1 0 * u 1,
      B.matrix 0 1 * u 0 + B.matrix 1 1 * u 1], ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  · intro y hy
    rw [distributionLattice_mem_iff] at hy
    obtain ⟨u, rfl⟩ := hy
    have hper : ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) ≠ 0 := by
      have := dBasis_period_pos B hB
      exact ne_of_gt (by simpa [distributionPeriod] using this)
    have hεdt : ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
        ((B.matrix 1 1 : ℝ) * B.tau - (B.matrix 0 1 : ℝ)) = B.tau := by
      rw [dl_d_tau_sub B.matrix B.tau hquad]
      calc ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
            (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ * B.tau)
          = (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
            ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹) * B.tau := by ring
        _ = 1 * B.tau := by rw [mul_inv_cancel₀ hper]
        _ = B.tau := by ring
    have hεinvd : ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
        ((B.matrix 1 1 : ℝ) * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) -
          (B.matrix 0 1 : ℝ)) =
        (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) := by
      rw [dl_d_conj_sub B.matrix B.tau hc hquad]
      calc ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
            (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
              (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau))
          = (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
            ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))) *
              (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) := by ring
        _ = 1 * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) := by
              rw [inv_mul_cancel₀ hper]
        _ = ((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau := by ring
    have hεac : ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
        ((B.matrix 0 0 : ℝ) - (B.matrix 1 0 : ℝ) * B.tau) = 1 := by
      rw [← dBasis_period_inv' B hB]
      exact mul_inv_cancel₀ (ne_of_gt (dBasis_period_pos B hB))
    have hεinvac : ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
        ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) = 1 :=
      inv_mul_cancel₀ (ne_of_gt (dBasis_period_pos B hB))
    have hz1 : distributionPeriodAction B
        ((B.matrix 1 1) • distributionBetaOne B - (B.matrix 0 1) • distributionBetaTwo B) =
        distributionBetaOne B := by
      rw [← Int.cast_smul_eq_zsmul ℝ (B.matrix 1 1) (distributionBetaOne B),
        ← Int.cast_smul_eq_zsmul ℝ (B.matrix 0 1) (distributionBetaTwo B)]
      push_cast
      ext
      · simp [distributionPeriodAction, distributionBetaOne, distributionBetaTwo, distributionPeriod]
        calc ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
              ((B.matrix 1 1 : ℝ) * (B.scale * B.tau) - (B.matrix 0 1 : ℝ) * B.scale)
            = (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
              ((B.matrix 1 1 : ℝ) * B.tau - (B.matrix 0 1 : ℝ))) * B.scale := by ring
          _ = B.tau * B.scale := by rw [hεdt]
          _ = B.scale * B.tau := by ring
      · simp [distributionPeriodAction, distributionBetaOne, distributionBetaTwo, distributionPeriod,
          distributionConjugateTau]
        calc ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
              ((B.matrix 1 1 : ℝ) * (B.scaleConj * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau)) -
                (B.matrix 0 1 : ℝ) * B.scaleConj)
            = (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
              ((B.matrix 1 1 : ℝ) * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) -
                (B.matrix 0 1 : ℝ))) * B.scaleConj := by ring
          _ = (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) * B.scaleConj := by rw [hεinvd]
          _ = B.scaleConj * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) := by ring
    have hz2 : distributionPeriodAction B
        ((-B.matrix 1 0) • distributionBetaOne B + (B.matrix 0 0) • distributionBetaTwo B) =
        distributionBetaTwo B := by
      rw [← Int.cast_smul_eq_zsmul ℝ (-B.matrix 1 0) (distributionBetaOne B),
        ← Int.cast_smul_eq_zsmul ℝ (B.matrix 0 0) (distributionBetaTwo B)]
      push_cast
      ext
      · simp [distributionPeriodAction, distributionBetaOne, distributionBetaTwo, distributionPeriod]
        calc ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
              (-((B.matrix 1 0 : ℝ) * (B.scale * B.tau)) + (B.matrix 0 0 : ℝ) * B.scale)
            = (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ)) *
              ((B.matrix 0 0 : ℝ) - (B.matrix 1 0 : ℝ) * B.tau)) * B.scale := by ring
          _ = 1 * B.scale := by rw [hεac]
          _ = B.scale := by ring
      · simp [distributionPeriodAction, distributionBetaOne, distributionBetaTwo, distributionPeriod,
          distributionConjugateTau]
        have hinner : (B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ) =
            (B.matrix 0 0 : ℝ) - (B.matrix 1 0 : ℝ) *
              (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau) :=
          dBasis_period_eq_conj B hB
        have h2 : ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
            ((B.matrix 0 0 : ℝ) - (B.matrix 1 0 : ℝ) *
              (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau)) = 1 := by
          rw [← hinner, hεinvac]
        calc ((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
              (-((B.matrix 1 0 : ℝ) * (B.scaleConj * (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau))) +
                (B.matrix 0 0 : ℝ) * B.scaleConj)
            = (((B.matrix 1 0 : ℝ) * B.tau + (B.matrix 1 1 : ℝ))⁻¹ *
              ((B.matrix 0 0 : ℝ) - (B.matrix 1 0 : ℝ) *
                (((B.matrix 0 0 : ℝ) - (B.matrix 1 1 : ℝ)) / (B.matrix 1 0 : ℝ) - B.tau))) * B.scaleConj := by ring
          _ = 1 * B.scaleConj := by rw [h2]
          _ = B.scaleConj := by ring
    refine ⟨u 0 • ((B.matrix 1 1) • distributionBetaOne B - (B.matrix 0 1) • distributionBetaTwo B) +
      u 1 • ((-B.matrix 1 0) • distributionBetaOne B + (B.matrix 0 0) • distributionBetaTwo B), ?_, ?_⟩
    · change u 0 • ((B.matrix 1 1) • distributionBetaOne B - (B.matrix 0 1) • distributionBetaTwo B) +
        u 1 • ((-B.matrix 1 0) • distributionBetaOne B + (B.matrix 0 0) • distributionBetaTwo B) ∈
        distributionLattice B
      rw [distributionLattice_mem_iff]
      refine ⟨![B.matrix 1 1 * u 0 - B.matrix 1 0 * u 1,
        -B.matrix 0 1 * u 0 + B.matrix 0 0 * u 1], ?_⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      module
    · rw [map_add, map_zsmul, map_zsmul, hz1, hz2]

/-- The two conventional period-point groups coincide. -/
theorem distributionPeriodPoints_eq_comap (B : DistributionBasis) (hB : B.Valid) :
    distributionPeriodPoints B = (distributionLattice B).comap
        (distributionPeriodAction B - AddMonoidHom.id (ℝ × ℝ)) := by

  have hmap := distributionLattice_map_action B hB
  have hε : distributionPeriod B ≠ 0 := ne_of_gt (dBasis_period_pos B hB)
  have hεinv : (distributionPeriod B)⁻¹ ≠ 0 := inv_ne_zero hε
  have hAinj : Function.Injective (distributionPeriodAction B) := by
    intro p q h
    ext
    · have h1 := congrArg Prod.fst h
      change distributionPeriod B * p.1 = distributionPeriod B * q.1 at h1
      exact mul_left_cancel₀ hε h1
    · have h2 := congrArg Prod.snd h
      change (distributionPeriod B)⁻¹ * p.2 = (distributionPeriod B)⁻¹ * q.2 at h2
      exact mul_left_cancel₀ hεinv h2
  have hmem : ∀ y : ℝ × ℝ, distributionPeriodAction B y ∈ distributionLattice B ↔
      y ∈ distributionLattice B := by
    intro y
    constructor
    · intro hy
      have : distributionPeriodAction B y ∈ (distributionLattice B).map (distributionPeriodAction B) := by
        rw [hmap]; exact hy
      rw [AddSubgroup.mem_map] at this
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := hAinj hzy
      simpa [this] using hz
    · intro hy
      rw [← hmap]
      exact AddSubgroup.mem_map_of_mem _ hy
  ext x
  simp only [distributionPeriodPoints, AddSubgroup.mem_comap]
  constructor
  · intro hx
    have h2 : (distributionPeriodAction B - AddMonoidHom.id (ℝ × ℝ)) x =
        -(distributionPeriodAction B (distributionPeriodDifference B x)) := by
      ext
      · simp [distributionPeriodAction, distributionPeriodDifference]
        field_simp [hε, hεinv]
        ring
      · simp [distributionPeriodAction, distributionPeriodDifference]
        field_simp [hε, hεinv]
        ring
    rw [h2]
    exact neg_mem ((hmem (distributionPeriodDifference B x)).mpr hx)
  · intro hx
    have h2 : (distributionPeriodAction B - AddMonoidHom.id (ℝ × ℝ)) x =
        -(distributionPeriodAction B (distributionPeriodDifference B x)) := by
      ext
      · simp [distributionPeriodAction, distributionPeriodDifference]
        field_simp [hε, hεinv]
        ring
      · simp [distributionPeriodAction, distributionPeriodDifference]
        field_simp [hε, hεinv]
        ring
    have : -(distributionPeriodAction B (distributionPeriodDifference B x)) ∈
        distributionLattice B := h2 ▸ hx
    exact (hmem (distributionPeriodDifference B x)).mp (by simpa using neg_mem this)

/-- Actual period stability and equality of the two conventional period point groups. [RW26, p. 2,
(2), p. 14, Prop. 9]. -/
theorem distributionLattice_period_stable (B : DistributionBasis) (hB : B.Valid) :
    (distributionLattice B).map (distributionPeriodAction B) = distributionLattice B ∧
      distributionPeriodPoints B = (distributionLattice B).comap
        (distributionPeriodAction B - AddMonoidHom.id (ℝ × ℝ)) :=
  ⟨distributionLattice_map_action B hB, distributionPeriodPoints_eq_comap B hB⟩

/-- A real quadratic K-application inserts its two embeddings in these four scalar equations. This
makes the specialization explicit without assuming any analytic law or requiring a new number-field
library. [RW26, p. 2]. -/
theorem distributionBasisFromEmbeddings_valid (M : SL(2, ℤ))
    (ε β₁ β₂ β₁' β₂' : ℝ) (hε : 1 < ε) (h₂ : 0 < β₂) (h₂' : 0 < β₂')
    (horient : 0 < β₁ * β₂' - β₁' * β₂)
    (h₁ : ε * β₁ = (M 0 0 : ℝ) * β₁ + (M 0 1 : ℝ) * β₂)
    (h₂eq : ε * β₂ = (M 1 0 : ℝ) * β₁ + (M 1 1 : ℝ) * β₂)
    (h₁' : ε⁻¹ * β₁' = (M 0 0 : ℝ) * β₁' + (M 0 1 : ℝ) * β₂')
    (h₂eq' : ε⁻¹ * β₂' = (M 1 0 : ℝ) * β₁' + (M 1 1 : ℝ) * β₂') :
    let B := distributionBasisFromEmbeddings M β₁ β₂ β₂'
    B.Valid ∧ distributionPeriod B = ε ∧
      distributionBetaOne B = (β₁, β₁') ∧ distributionBetaTwo B = (β₂, β₂') := by

  intro B
  have hb₂ : β₂ ≠ 0 := ne_of_gt h₂
  have hb₂' : β₂' ≠ 0 := ne_of_gt h₂'
  set τ : ℝ := β₁ / β₂ with hτdef
  set τ' : ℝ := β₁' / β₂' with hτ'def
  have hβ₁ : β₁ = β₂ * τ := by rw [hτdef]; field_simp
  have hβ₁' : β₁' = β₂' * τ' := by rw [hτ'def]; field_simp
  have hεeq : ε = (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) := by
    have hh : ε * β₂ = ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) * β₂ := by
      rw [h₂eq, hβ₁]; ring
    exact mul_right_cancel₀ hb₂ hh
  have hεinveq : ε⁻¹ = (M 1 0 : ℝ) * τ' + (M 1 1 : ℝ) := by
    have hh : ε⁻¹ * β₂' = ((M 1 0 : ℝ) * τ' + (M 1 1 : ℝ)) * β₂' := by
      rw [h₂eq', hβ₁']; ring
    exact mul_right_cancel₀ hb₂' hh
  have heig : (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) = ε * τ := by
    have hh : ((M 0 0 : ℝ) * τ + (M 0 1 : ℝ)) * β₂ = ε * τ * β₂ := by
      calc ((M 0 0 : ℝ) * τ + (M 0 1 : ℝ)) * β₂
          = (M 0 0 : ℝ) * (β₂ * τ) + (M 0 1 : ℝ) * β₂ := by ring
        _ = (M 0 0 : ℝ) * β₁ + (M 0 1 : ℝ) * β₂ := by rw [← hβ₁]
        _ = ε * β₁ := by rw [← h₁]
        _ = ε * τ * β₂ := by rw [hβ₁]; ring
    exact mul_right_cancel₀ hb₂ hh
  have heig' : (M 0 0 : ℝ) * τ' + (M 0 1 : ℝ) = ε⁻¹ * τ' := by
    have hh : ((M 0 0 : ℝ) * τ' + (M 0 1 : ℝ)) * β₂' = ε⁻¹ * τ' * β₂' := by
      calc ((M 0 0 : ℝ) * τ' + (M 0 1 : ℝ)) * β₂'
          = (M 0 0 : ℝ) * (β₂' * τ') + (M 0 1 : ℝ) * β₂' := by ring
        _ = (M 0 0 : ℝ) * β₁' + (M 0 1 : ℝ) * β₂' := by rw [← hβ₁']
        _ = ε⁻¹ * β₁' := by rw [← h₁']
        _ = ε⁻¹ * τ' * β₂' := by rw [hβ₁']; ring
    exact mul_right_cancel₀ hb₂' hh
  have hcne : (M 1 0 : ℝ) ≠ 0 := by
    intro hc0
    have h1 : ε = (M 1 1 : ℝ) := by
      rw [hc0, zero_mul, zero_add] at hεeq
      exact hεeq
    have h2 : ε⁻¹ = (M 1 1 : ℝ) := by
      rw [hc0, zero_mul, zero_add] at hεinveq
      exact hεinveq
    have hlt : ε⁻¹ < 1 := inv_lt_one_of_one_lt₀ hε
    have hεne : ε ≠ ε⁻¹ := by linarith
    exact hεne (h1.trans h2.symm)
  have hquad : (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ - (M 0 1 : ℝ) = 0 := by
    have h := heig
    rw [hεeq] at h
    linarith
  have hquad' : (M 1 0 : ℝ) * τ' ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ' - (M 0 1 : ℝ) = 0 := by
    have h := heig'
    rw [hεinveq] at h
    linarith
  have hτne : τ ≠ τ' := by
    intro h
    have hlt : ε⁻¹ < 1 := inv_lt_one_of_one_lt₀ hε
    have hεne : ε ≠ ε⁻¹ := by linarith
    apply hεne
    calc ε = (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) := hεeq
      _ = (M 1 0 : ℝ) * τ' + (M 1 1 : ℝ) := by rw [h]
      _ = ε⁻¹ := hεinveq.symm
  have hsum : (M 1 0 : ℝ) * (τ + τ') = (M 0 0 : ℝ) - (M 1 1 : ℝ) := by
    have h : (M 1 0 : ℝ) * (τ ^ 2 - τ' ^ 2) + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * (τ - τ') = 0 := by
      linarith [hquad, hquad']
    have hfac : (τ - τ') * ((M 1 0 : ℝ) * (τ + τ') + ((M 1 1 : ℝ) - (M 0 0 : ℝ))) = 0 := by
      linarith [h]
    have hne : τ - τ' ≠ 0 := sub_ne_zero.mpr hτne
    have := (mul_eq_zero.mp hfac).resolve_left hne
    linarith
  have hconj : ((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - τ = τ' := by
    field_simp
    linarith [hsum]
  have hdiff : (M 1 0 : ℝ) * (τ - τ') = ε - ε⁻¹ := by
    calc (M 1 0 : ℝ) * (τ - τ')
        = ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) - ((M 1 0 : ℝ) * τ' + (M 1 1 : ℝ)) := by ring
      _ = ε - ε⁻¹ := by rw [← hεeq, ← hεinveq]
  have hτpos : 0 < τ - τ' := by
    have hprod : 0 < β₂ * β₂' * (τ - τ') := by
      have : β₂ * β₂' * (τ - τ') = β₁ * β₂' - β₁' * β₂ := by
        rw [hβ₁, hβ₁']; ring
      rw [this]; exact horient
    nlinarith [mul_pos h₂ h₂', hprod]
  have hεdiff : 0 < ε - ε⁻¹ := by
    have hlt : ε⁻¹ < 1 := inv_lt_one_of_one_lt₀ hε
    linarith
  have hcpos : 0 < (M 1 0 : ℝ) := by
    have hcval : (M 1 0 : ℝ) = (ε - ε⁻¹) / (τ - τ') := by
      rw [eq_div_iff (sub_ne_zero.mpr hτne)]
      linarith [hdiff]
    rw [hcval]
    exact div_pos hεdiff hτpos
  have htr : (M 0 0 : ℝ) + (M 1 1 : ℝ) = ε + ε⁻¹ := by
    have hcτ : (M 1 0 : ℝ) * τ = ε - (M 1 1 : ℝ) := by linarith [hεeq]
    have hcτ' : (M 1 0 : ℝ) * τ' = ε⁻¹ - (M 1 1 : ℝ) := by linarith [hεinveq]
    have hs : (M 1 0 : ℝ) * τ + (M 1 0 : ℝ) * τ' = (M 0 0 : ℝ) - (M 1 1 : ℝ) := by
      calc (M 1 0 : ℝ) * τ + (M 1 0 : ℝ) * τ' = (M 1 0 : ℝ) * (τ + τ') := by ring
        _ = (M 0 0 : ℝ) - (M 1 1 : ℝ) := hsum
    linarith [hs, hcτ, hcτ']
  have htrace : 2 < M 0 0 + M 1 1 := by
    have hεpos : 0 < ε := lt_trans zero_lt_one hε
    have hsq : 0 < (ε - 1) ^ 2 := by nlinarith
    have hfrac : 0 < (ε - 1) ^ 2 / ε := div_pos hsq hεpos
    have heq : ε + ε⁻¹ - 2 = (ε - 1) ^ 2 / ε := by
      field_simp [ne_of_gt hεpos]
      ring
    have hreal : (2 : ℝ) < (M 0 0 : ℝ) + (M 1 1 : ℝ) := by
      rw [htr]; linarith
    exact_mod_cast hreal
  have hperne : (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) ≠ 0 := by
    rw [← hεeq]
    exact ne_of_gt (lt_trans zero_lt_one hε)
  have hfixR : ((M 0 0 : ℝ) * τ + (M 0 1 : ℝ)) /
      ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) = τ := by
    rw [heig, ← hεeq]
    field_simp [hperne]
  have hfix : etaMobius M (τ : ℂ) = (τ : ℂ) := by
    have hdenC : ((M 1 0 : ℂ) * (τ : ℂ) + (M 1 1 : ℂ)) ≠ 0 := by
      intro hh
      have h0 : (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) = 0 := by
        have := congrArg Complex.re hh
        simpa using this
      rw [← hεeq] at h0
      linarith [hε]
    rw [etaMobius, etaDenom, div_eq_iff hdenC]
    have hreal : (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) =
        τ * ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) := by
      rw [heig, ← hεeq]
      ring
    have hC := congrArg (fun x : ℝ => (x : ℂ)) hreal
    push_cast at hC
    exact hC
  have hper : distributionPeriod B = ε := by
    show (M 1 0 : ℝ) * (β₁ / β₂) + (M 1 1 : ℝ) = ε
    rw [← hτdef]
    linarith [hεeq]
  have hbOne : distributionBetaOne B = (β₁, β₁') := by
    simp only [distributionBetaOne, distributionBasisFromEmbeddings, distributionConjugateTau]
    ext
    · change β₂ * (β₁ / β₂) = β₁
      field_simp
    · change β₂' * (((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) - (β₁ / β₂)) = β₁'
      rw [← hτdef, hconj, ← hβ₁']
  refine ⟨⟨?_, htrace, ?_, ?_, h₂, h₂'⟩, hper, hbOne, ?_⟩
  · exact_mod_cast hcpos
  · show etaMobius M ((β₁ / β₂ : ℝ) : ℂ) = ((β₁ / β₂ : ℝ) : ℂ)
    rw [← hτdef]
    exact hfix
  · rwa [hper]
  · simp only [distributionBetaTwo]
    constructor <;> rfl

#check AddMonoidHom.mulLeft
#check AddMonoidHom.prodMap
#check AddSubgroup.addSubgroupOf
#check Quotient.out
#print distributionPeriodDifference
#print distributionIntegerCoordinates
#check distributionPeriodPoints_first_lattice_iff

end SICLean.L4
