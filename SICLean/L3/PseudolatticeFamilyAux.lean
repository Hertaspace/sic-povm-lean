import SICLean.L4.DistributionOrderTwo

set_option autoImplicit false

/-!
# Auxiliary inverse-homothety lemmas for the arithmetic finite family

The zero class after inverse scaling is detected by membership in the
scaled target lattice. For an order-two overlattice its two source
classes are precisely zero and the specified order-two class.
-/

noncomputable section

namespace SICLean.L3.PseudolatticeFamilyAux

open SICLean.L4

theorem distributionMk_eq_zero_iff (B : DistributionBasis)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionMk B x hx = 0 ↔ x ∈ distributionLattice B := by
  exact QuotientAddGroup.eq_zero_iff (⟨x, hx⟩ : distributionPeriodPoints B)

theorem distributionHomothety_inv_mem_iff (B : DistributionBasis) (hB : B.Valid)
    (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2) (x : ℝ × ℝ) :
    distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) x ∈ distributionLattice B ↔
      x ∈ distributionLattice (distributionScale B ρ) := by
  rw [(distributionScale_valid B hB ρ hρ).2.2]
  constructor
  · intro hx
    refine ⟨distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) x, hx, ?_⟩
    ext <;> simp [distributionHomothety, ne_of_gt hρ.1, ne_of_gt hρ.2]
  · rintro ⟨y, hy, rfl⟩
    have hinv : distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) (distributionHomothety ρ y) = y := by
      ext <;> simp [distributionHomothety, ne_of_gt hρ.1, ne_of_gt hρ.2]
    rwa [hinv]

theorem distributionScaledProject_kernel (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2)
    (h : DistributionGroup B) (hh : h ≠ 0 ∧ h + h = 0)
    (hP : distributionPeriodPoints B ≤ (distributionPeriodPoints C).comap
      (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)))
    (hJ : distributionLattice (distributionScale C ρ) = distributionOverlattice B h)
    (g : DistributionGroup B) :
    distributionScaledProject B C ρ hP g = 0 ↔ g = 0 ∨ g = h := by
  have hg : distributionMk B (Quotient.out g).val (Quotient.out g).property = g :=
    Quotient.out_eq g
  have hh' : distributionMk B (Quotient.out h).val (Quotient.out h).property = h :=
    Quotient.out_eq h
  refine (distributionMk_eq_zero_iff C _ (hP (Quotient.out g).property)).trans ?_
  rw [distributionHomothety_inv_mem_iff C hC ρ hρ, hJ,
    distributionOverlattice_mem B hB h hh]
  apply or_congr
  · exact (distributionMk_eq_zero_iff B _ (Quotient.out g).property).symm.trans
      (by rw [hg])
  · exact (distributionMk_eq_iff B hB _ _
      (Quotient.out g).property (Quotient.out h).property).symm.trans
      (by rw [hg, hh'])

end SICLean.L3.PseudolatticeFamilyAux
