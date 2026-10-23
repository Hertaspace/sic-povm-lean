import SICLean.L2rc.Finite
import SICLean.L2r.Main

set_option autoImplicit false

/-! # Interfaces from the rank-r form of [RW26, Thm. 2] to L2r -/

noncomputable section

namespace SICLean

/-- The row-coordinate form of [RW26, Thm. 2] implies the L2r input.
The origin value is the positive radical in [RW26, (4)]. -/
theorem fqdInput_of_theorem2_rank {d r : ℕ} [Fact (L2r.Admissible d r)]
    {Fplus Fminus : L2rc.RWGroup d r → ℂ}
    (h : L2rc.RWAnalyticInput d r Fplus Fminus) :
    L2r.FQDInput d r (L2rc.concreteValues d r Fplus) := by
  exact ⟨L2rc.isFiniteQuantumDilogarithm_of_theorem2 h.theorem2,
    L2rc.concrete_epsilon_invariant h, L2rc.concrete_origin h.theorem2⟩

/-- Admissible parameters, with the same τ for all nonzero d-torsion values. -/
theorem ghostGaloisInput_of_theorem2_rank {d r : ℕ} [Fact (L2r.Admissible d r)]
    {Fplus Fminus : L2rc.RWGroup d r → ℂ}
    (h : L2rc.RWAnalyticInput d r Fplus Fminus) {τ : ℂ →+* ℂ}
    (hB : L2r.RWUnitCircleInput d r
      (L2r.restrict d r (L2rc.concreteValues d r Fplus)) τ) :
    GhostGaloisInput d r := by
  exact ghostGaloisInput_of_FQD_rank (fqdInput_of_theorem2_rank h) hB

/-- The final quantifiers and arithmetic range agree with `hasRSIC_of_inputs`
and `hasRSIC_of_FQD`. Every Fact is constructed from the three displayed bounds. -/
theorem hasRSIC_of_theorem2
    (H : ∀ (d r : ℕ) (hr : 1 ≤ r) (hd : 2 * r + 1 < d)
      (hdiv : r * (d - r) ∣ d ^ 2 - 1),
      letI : Fact (L2r.Admissible d r) := ⟨⟨hr, hd, hdiv⟩⟩
      ∃ Fplus Fminus : L2rc.RWGroup d r → ℂ,
        L2rc.RWAnalyticInput d r Fplus Fminus ∧
          ∃ τ : ℂ →+* ℂ, L2r.RWUnitCircleInput d r
            (L2r.restrict d r (L2rc.concreteValues d r Fplus)) τ) :
    ∀ (d r : ℕ), 1 ≤ r → 2 * r + 1 < d →
      r * (d - r) ∣ d ^ 2 - 1 → HasRSIC d r := by
  apply hasRSIC_of_FQD
  intro d r hr hd hdiv
  letI : Fact (L2r.Admissible d r) := ⟨⟨hr, hd, hdiv⟩⟩
  obtain ⟨Fplus, Fminus, h, τ, hB⟩ := H d r hr hd hdiv
  exact ⟨L2rc.concreteValues d r Fplus, fqdInput_of_theorem2_rank h, τ, hB⟩

end SICLean
