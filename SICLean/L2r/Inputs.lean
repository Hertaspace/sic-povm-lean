import SICLean.L2r.Gaussian
import SICLean.L2r.FiniteQD

set_option autoImplicit false

/-!
# Inputs and an intermediate rank-r convolution certificate

Only `FQDInput` and `RWUnitCircleInput` are premises of the final FQD interface.
`RWConvolutionInput` is the target of the character projection and the source of
the ghost; its third field is the twisted convolution in F coordinates.
All dimension restrictions are explicit in the signatures, including structures.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2r

def valueAt {d : ℕ} (F : Values d) (p : ℤ × ℤ) : ℂ := F (label d p)

def restrict (d r : ℕ) [Fact (Admissible d r)] (E : G d r → ℂ) : Values d :=
  E ∘ iota d r

/-- [RW26, Def. 4, (31)], the unit symmetry of [RW26, Prop. 8], and the zero
convention [RW26, (37)]. [RW26, Prop. 10] supplies (31) for this γ.
No metric or lattice property is assumed here. -/
structure FQDInput (d r : ℕ) [Fact (Admissible d r)] (E : G d r → ℂ) : Prop where
  pentagon : L2b.IsFiniteQuantumDilogarithm (gaussian d r) E
  epsilon_invariant : ∀ g : G d r, E g = E (epsilonAut d r g)
  origin : E 0 = originValue d r

/-- The single τ is shared by every nonzero value. This is the form of
[RW-rec, Prop. 7] used here. -/
structure RWUnitCircleInput (d r : ℕ) [Fact (Admissible d r)]
    (F : Values d) (τ : ℂ →+* ℂ) : Prop where
  norm_F : ∀ p : Index d, p ≠ 0 → ‖τ (F p)‖ = 1

/-- E-ratio form of the higher-rank twisted convolution.
The standard representatives contain both actual vectors 0 and lift(p). -/
def twistedRatio (d r : ℕ) [Fact (Admissible d r)] (F : Values d) (p : Index d) : ℂ :=
  letI : NeZero d := admissibleDimensionNeZero d r
  ∑ q : Index d,
    L2a.e d ((r : ℤ) * symplectic (lift p) (shiftedAlpha d r (lift q))) *
      valueAt F (lift q - lift p) / F q

/-- Intermediate certificate derived from `FQDInput`; not an additional premise
of `ghostGaloisInput_of_FQD_rank`. Sources: [RW26, Thm. 5(ii)] and [RW26, (37)]. -/
structure RWConvolutionInput (d r : ℕ) [Fact (Admissible d r)] (F : Values d) : Prop where
  origin : F 0 = originValue d r
  reflection : ∀ p : Index d, p ≠ 0 → F p * F (-p) = (torsionGaussian d r p)⁻¹
  twisted_ratio : ∀ p : Index d,
    twistedRatio d r F p = if p = 0 then (d : ℂ) ^ 2 else 0

end SICLean.L2r
