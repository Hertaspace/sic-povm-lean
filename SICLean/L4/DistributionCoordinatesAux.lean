import SICLean.L4.DistributionBasisValues
import SICLean.L2c.Coordinates
import SICLean.L2rc.Coordinates

set_option autoImplicit false

noncomputable section

open Set
open scoped MatrixGroups

namespace SICLean.L4

/-! Elementary coordinate lemmas used by `DistributionCoordinates`. -/

lemma distributionTau_ne_conjugateTau (B : DistributionBasis) (hB : B.Valid) :
    B.tau ≠ distributionConjugateTau B := by
  have h := (distributionBasis_spectral B hB).2.1
  linarith

lemma distributionPeriod_sub_one_ne_zero (B : DistributionBasis) (hB : B.Valid) :
    distributionPeriod B - 1 ≠ 0 := by
  have h : 1 < distributionPeriod B := hB.2.2.2.1
  linarith

lemma distributionPeriod_inv_sub_one_ne_zero (B : DistributionBasis) (hB : B.Valid) :
    (distributionPeriod B)⁻¹ - 1 ≠ 0 := by
  have h : 1 < distributionPeriod B := hB.2.2.2.1
  have hinv : (distributionPeriod B)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr h
  linarith

lemma distributionScale_ne_zero (B : DistributionBasis) (hB : B.Valid) :
    B.scale ≠ 0 := ne_of_gt hB.2.2.2.2.1

lemma distributionScaleConj_ne_zero (B : DistributionBasis) (hB : B.Valid) :
    B.scaleConj ≠ 0 := ne_of_gt hB.2.2.2.2.2

lemma distributionTau_sub_conjugateTau_ne_zero (B : DistributionBasis) (hB : B.Valid) :
    B.tau - distributionConjugateTau B ≠ 0 :=
  sub_ne_zero.mpr (distributionTau_ne_conjugateTau B hB)

/-- Explicit coordinates of a real linear combination of the two basis vectors. -/
lemma distributionCoordinates_real_combination (B : DistributionBasis) (hB : B.Valid)
    (a b : ℝ) :
    distributionCoordinates B
        (a • distributionBetaOne B + b • distributionBetaTwo B) = ![a, b] := by
  have hs := distributionScale_ne_zero B hB
  have hs' := distributionScaleConj_ne_zero B hB
  have ht := distributionTau_sub_conjugateTau_ne_zero B hB
  funext i
  fin_cases i <;>
    simp [distributionCoordinates, distributionBetaOne, distributionBetaTwo] <;>
    field_simp <;> ring

lemma distributionCoordinates_betaOne (B : DistributionBasis) (hB : B.Valid) :
    distributionCoordinates B (distributionBetaOne B) = ![1, 0] := by
  simpa using distributionCoordinates_real_combination B hB 1 0

lemma distributionCoordinates_betaTwo (B : DistributionBasis) (hB : B.Valid) :
    distributionCoordinates B (distributionBetaTwo B) = ![0, 1] := by
  simpa using distributionCoordinates_real_combination B hB 0 1

/-- The period-difference operator is injective. -/
lemma distributionPeriodDifference_injective (B : DistributionBasis) (hB : B.Valid) :
    Function.Injective (distributionPeriodDifference B) := by
  intro x y hxy
  have h1 : (distributionPeriod B)⁻¹ - 1 ≠ 0 :=
    distributionPeriod_inv_sub_one_ne_zero B hB
  have h2 : distributionPeriod B - 1 ≠ 0 := distributionPeriod_sub_one_ne_zero B hB
  have hx : ((distributionPeriod B)⁻¹ - 1) * x.1 =
      ((distributionPeriod B)⁻¹ - 1) * y.1 := by
    simpa [distributionPeriodDifference] using congrArg Prod.fst hxy
  have hy : (distributionPeriod B - 1) * x.2 =
      (distributionPeriod B - 1) * y.2 := by
    simpa [distributionPeriodDifference] using congrArg Prod.snd hxy
  ext
  · exact mul_left_cancel₀ h1 hx
  · exact mul_left_cancel₀ h2 hy

/-! ### Coefficient uniqueness and lattice coordinates. -/

lemma distributionBetaCoefficients_unique (B : DistributionBasis) (hB : B.Valid)
    (a b a' b' : ℝ)
    (h : a • distributionBetaOne B + b • distributionBetaTwo B =
      a' • distributionBetaOne B + b' • distributionBetaTwo B) :
    a = a' ∧ b = b' := by
  have hc := congrArg (distributionCoordinates B) h
  rw [distributionCoordinates_real_combination B hB a b,
    distributionCoordinates_real_combination B hB a' b'] at hc
  constructor
  · exact congrFun hc 0
  · exact congrFun hc 1

lemma distributionLattice_mem_iff_coordinates (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) :
    x ∈ distributionLattice B ↔
      ∃ z : ℤ × ℤ, distributionCoordinates B x = ![(z.1 : ℝ), (z.2 : ℝ)] := by
  rw [distributionLattice_mem_iff]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(u 0, u 1), ?_⟩
    have hz : ((u 0 : ℤ) • distributionBetaOne B + (u 1 : ℤ) • distributionBetaTwo B) =
        ((u 0 : ℝ) • distributionBetaOne B + (u 1 : ℝ) • distributionBetaTwo B) := by
      rw [Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ]
    rw [hz, distributionCoordinates_real_combination B hB]
  · rintro ⟨z, hz⟩
    refine ⟨![z.1, z.2], ?_⟩
    have hrec := distributionCoordinates_reconstruct B hB x
    rw [hrec, hz]
    have hz' : ((z.1 : ℝ) • distributionBetaOne B + (z.2 : ℝ) • distributionBetaTwo B) =
        ((z.1 : ℤ) • distributionBetaOne B + (z.2 : ℤ) • distributionBetaTwo B) := by
      rw [Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ]
    simpa using hz'

lemma distributionPeriodDifference_smul (B : DistributionBasis) (a : ℝ) (v : ℝ × ℝ) :
    distributionPeriodDifference B (a • v) = a • distributionPeriodDifference B v := by
  ext
  · change ((distributionPeriod B)⁻¹ - 1) * (a * v.1) =
      a * (((distributionPeriod B)⁻¹ - 1) * v.1)
    ring
  · change (distributionPeriod B - 1) * (a * v.2) =
      a * ((distributionPeriod B - 1) * v.2)
    ring

lemma distributionPeriodDifference_combination (B : DistributionBasis) (hB : B.Valid)
    (x y : ℝ) :
    distributionPeriodDifference B
        (x • distributionBetaOne B + y • distributionBetaTwo B) =
      (x * ((B.matrix 1 1 : ℝ) - 1) - y * (B.matrix 1 0 : ℝ)) •
          distributionBetaOne B +
        (x * (-(B.matrix 0 1 : ℝ)) + y * ((B.matrix 0 0 : ℝ) - 1)) •
          distributionBetaTwo B := by
  have h1 := (distributionPeriodDifference_basis B hB).1
  have h2 := (distributionPeriodDifference_basis B hB).2
  rw [map_add, distributionPeriodDifference_smul, distributionPeriodDifference_smul, h1, h2]
  simp_rw [← Int.cast_smul_eq_zsmul ℝ]
  module


/-! ### Row-lattice matrix identities. -/

lemma rowAction_int_forward (a b c d z1 z2 u1 u2 : ℤ)
    (hdet : a * d - b * c = 1)
    (h1 : u1 = z1 * (d - 1) - z2 * c)
    (h2 : u2 = -z1 * b + z2 * (a - 1)) :
    (-(u1 + z1) * (a - 1) + (-(u2 + z2)) * c,
      -(u1 + z1) * b + (-(u2 + z2)) * (d - 1)) = (u1, u2) := by
  ext
  · rw [h1, h2]
    linear_combination -z1 * hdet
  · rw [h1, h2]
    linear_combination -z2 * hdet

lemma rowAction_int_backward (a b c d z1 z2 u1 u2 : ℤ)
    (hdet : a * d - b * c = 1)
    (h1 : u1 = z1 * (a - 1) + z2 * c)
    (h2 : u2 = z1 * b + z2 * (d - 1)) :
    (-(u1 + z1) * (d - 1) - (-(u2 + z2)) * c = u1) ∧
      (-(u1 + z1) * (-b) + (-(u2 + z2)) * (a - 1) = u2) := by
  have hAB : a * d = b * c + 1 := by linarith [hdet]
  constructor
  · rw [h1, h2]
    linear_combination -z1 * hdet
  · rw [h1, h2]
    linear_combination -z2 * hdet

end SICLean.L4
