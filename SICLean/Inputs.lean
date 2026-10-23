import SICLean.Defs

/-!
# The input hypotheses

The reduction in `SICLean.Main` takes the two hypotheses below. They are stated as ordinary
propositions, not as Lean `axiom`s, so every use of them is visible in the theorem statements.
Both are proved later in this repository, and the final theorems
`SICLean.FinalAssembly.zaunerExistence` and `SICLean.FinalAssembly.hasRSIC` have no hypotheses.

* `IsGhost d r G` is the twisted convolution identity. For `r = 1` it comes from
  [RW26, Thm. 7] with [AFK25, Def. 1.43] and [AFK25, Thm. 1.45]. For `r > 1` it comes from
  [AFK26, Thm. 1.2 and Thm. 1.3].
* `UnimodularFlip d r G σ` comes from [RW-rec, Prop. 7], through the dictionary
  between ghost overlaps and finite quantum dilogarithm values.
-/

noncomputable section

open Matrix

namespace SICLean

/-- Ghost data: an idempotent of trace `r` whose overlaps at opposite labels multiply to
`r(d-r)/(d²-1)`. A ghost need not be Hermitian. -/
structure IsGhost (d r : ℕ) (G : Matrix (Fin d) (Fin d) ℂ) : Prop where
  idem : G * G = G
  trace_eq : G.trace = r
  ov_mul_ov_neg : ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p →
    ov d G p * ov d G (-p) = (rsicConst d r : ℂ)

/-- The Galois input: a ring endomorphism `σ` of `ℂ` under which every nontrivial overlap of `G`
acquires the r-SIC modulus. On paper `σ` extends an automorphism of `ℚ̄` that is nontrivial on
the real quadratic field `ℚ(√Δ)`. -/
def UnimodularFlip (d r : ℕ) (G : Matrix (Fin d) (Fin d) ℂ) (σ : ℂ →+* ℂ) : Prop :=
  ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p → Complex.normSq (σ (ov d G p)) = rsicConst d r

/-- The combined input in dimension `d` and rank `r`. -/
def GhostGaloisInput (d r : ℕ) : Prop :=
  ∃ G : Matrix (Fin d) (Fin d) ℂ, IsGhost d r G ∧ ∃ σ : ℂ →+* ℂ, UnimodularFlip d r G σ

end SICLean
