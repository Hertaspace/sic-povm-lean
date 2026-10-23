import SICLean.L2b.Convolution

set_option autoImplicit false

/-! # L2b interfaces: finite quantum dilogarithms imply the L2a input -/

noncomputable section

open OpenQuantumProblem23

namespace SICLean

/-- Input A is a consequence of [RW26, (31)], [RW26, (38)], and the origin convention.
`Fact (4 ≤ M)` supplies only the allowed dimension. -/
theorem rwConvolutionInput_of_FQD {M : ℕ} [Fact (4 ≤ M)] {E : L2b.G M → ℂ}
    (hE : L2b.FQDInput M E) : L2a.RWConvolutionInput M (L2b.restrict M E) := by
  exact ⟨L2b.restrict_origin M hE, L2b.restrict_reflection M hE,
    L2b.restrict_convolution M hE⟩

/-- Input B is the L2a input on E∘ι, with one common τ.
The concrete group, metric property and its order are not additional assumptions. -/
theorem zaunerExistence_of_FQD
    (H : ∀ (M : ℕ) (hM : 4 ≤ M),
      letI : Fact (4 ≤ M) := ⟨hM⟩
      ∃ E : L2b.G M → ℂ, L2b.FQDInput M E ∧
        ∃ τ : ℂ →+* ℂ, L2a.RWUnitCircleInput M (L2b.restrict M E) τ) :
    ZaunerExistence := by
  apply zaunerExistence_of_RW
  intro M hM
  let : Fact (4 ≤ M) := ⟨hM⟩
  obtain ⟨E, hE, τ, hB⟩ := H M hM
  exact ⟨L2b.restrict M E, rwConvolutionInput_of_FQD hE, τ, hB⟩

end SICLean
