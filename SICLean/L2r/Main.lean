import SICLean.L2r.Ghost

set_option autoImplicit false

/-! # The two rank-r interfaces to the existence theorem -/

noncomputable section

namespace SICLean

theorem ghostGaloisInput_of_RW_rank {d r : ℕ} [Fact (L2r.Admissible d r)]
    {F : L2r.Values d} (hA : L2r.RWConvolutionInput d r F)
    {τ : ℂ →+* ℂ} (hB : L2r.RWUnitCircleInput d r F τ) :
    GhostGaloisInput d r := by
  exact ⟨L2r.ghostProjector d r F, L2r.isGhost_of_RW_rank d r hA,
    τ, L2r.unimodularFlip_of_RW_rank d r hB⟩

/-- For admissible (d,r): [RW26, (31)], unit invariance, the origin, and B. -/
theorem ghostGaloisInput_of_FQD_rank {d r : ℕ} [Fact (L2r.Admissible d r)]
    {E : L2r.G d r → ℂ} (hE : L2r.FQDInput d r E)
    {τ : ℂ →+* ℂ} (hB : L2r.RWUnitCircleInput d r (L2r.restrict d r E) τ) :
    GhostGaloisInput d r := by
  exact ghostGaloisInput_of_RW_rank
    (L2r.rwConvolutionInput_of_FQD_rank d r hE) hB

/-- The final quantifiers and range agree with `hasRSIC_of_inputs`.
Every Fact is introduced from the three displayed arithmetic conditions. -/
theorem hasRSIC_of_FQD
    (H : ∀ (d r : ℕ) (hr : 1 ≤ r) (hd : 2 * r + 1 < d)
      (hdiv : r * (d - r) ∣ d ^ 2 - 1),
      letI : Fact (L2r.Admissible d r) := ⟨⟨hr, hd, hdiv⟩⟩
      ∃ E : L2r.G d r → ℂ, L2r.FQDInput d r E ∧
        ∃ τ : ℂ →+* ℂ, L2r.RWUnitCircleInput d r (L2r.restrict d r E) τ) :
    ∀ (d r : ℕ), 1 ≤ r → 2 * r + 1 < d → r * (d - r) ∣ d ^ 2 - 1 → HasRSIC d r :=
  by
    apply hasRSIC_of_inputs
    intro d r hr hd hdiv
    letI : Fact (L2r.Admissible d r) := ⟨⟨hr, hd, hdiv⟩⟩
    obtain ⟨E, hE, τ, hB⟩ := H d r hr hd hdiv
    exact ghostGaloisInput_of_FQD_rank hE hB

end SICLean
