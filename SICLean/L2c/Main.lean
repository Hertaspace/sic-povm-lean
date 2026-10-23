import SICLean.L2c.Finite

set_option autoImplicit false

/-! # L2c interfaces: [RW26, Thm. 2] implies the L2b input -/

noncomputable section

open OpenQuantumProblem23

namespace SICLean

/-- [RW26, (4)--(7)], footnote 2, and [RW26, Prop. 8] for γ=α³ imply the
L2b input. E(x,y)=F⁺(class(x,y−(M−2)x)) is a definition, not an input. -/
theorem fqdInput_of_theorem2 {M : ℕ} [Fact (4 ≤ M)]
    {Fplus Fminus : L2c.RWGroup M → ℂ}
    (h : L2c.RWAnalyticInput M Fplus Fminus) :
    L2b.FQDInput M (L2c.smithValues M Fplus) := by
  exact ⟨L2c.isFiniteQuantumDilogarithm_of_theorem2 h.theorem2,
    L2c.smith_epsilon_invariant h, L2c.smith_origin h.theorem2⟩

/-- The upstream analytic input and the existing common-τ input B,
followed by the already proved zaunerExistence_of_FQD. -/
theorem zaunerExistence_of_theorem2
    (H : ∀ (M : ℕ) (hM : 4 ≤ M),
      letI : Fact (4 ≤ M) := ⟨hM⟩
      ∃ Fplus Fminus : L2c.RWGroup M → ℂ,
        L2c.RWAnalyticInput M Fplus Fminus ∧
          ∃ τ : ℂ →+* ℂ,
            L2a.RWUnitCircleInput M (L2b.restrict M (L2c.smithValues M Fplus)) τ) :
    ZaunerExistence := by
  apply zaunerExistence_of_FQD
  intro M hM
  letI : Fact (4 ≤ M) := ⟨hM⟩
  obtain ⟨Fplus, Fminus, h, τ, hB⟩ := H M hM
  exact ⟨L2c.smithValues M Fplus, fqdInput_of_theorem2 h, τ, hB⟩

end SICLean

#check @SICLean.fqdInput_of_theorem2
#check @SICLean.zaunerExistence_of_theorem2
#print SICLean.fqdInput_of_theorem2
#print SICLean.zaunerExistence_of_theorem2
