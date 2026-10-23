import SICLean.L2a.Defs

/-!
# The two explicit inputs for L2a

These structures are propositions passed to theorems. No existence, algebraicity,
analytic property, conjugation law, or action on all of G is hidden in a definition.
-/

noncomputable section

namespace SICLean.L2a

/-- Input A: the origin value, reflection off the origin, and [RW26, (39)] in [RW26, §4.4].
There is no reflection assumption at zero and no nondegeneracy assumption on H. -/
structure RWConvolutionInput (M : ℕ) (F : Values M) : Prop where
  origin : F 0 = sqrtEpsilon M ^ 3
  reflection : ∀ h : Index M, h ≠ 0 → F h * F (-h) = (gaussian M h)⁻¹
  convolution_eq : ∀ h : Index M,
    convolution M F h.1.val h.2.val =
      convolutionScalar M * F h + if h = 0 then (M : ℂ) else 0

/-- Input B: a single ring homomorphism works for all nonzero H-values.
The denominator image ±√(M+1) is automatic for every such homomorphism, so it is
the theorem `map_denominator_eq_or_neg` rather than an independent input. -/
structure RWUnitCircleInput (M : ℕ) (F : Values M) (τ : ℂ →+* ℂ) : Prop where
  norm_F : ∀ h : Index M, h ≠ 0 → ‖τ (F h)‖ = 1

end SICLean.L2a
