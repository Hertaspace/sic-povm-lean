import SICLean.L2c.Coordinates

set_option autoImplicit false

/-!
# Special-value inputs: [RW26, Thm. 2] and [RW26, Prop. 8]

[RW26, p. 3, (4)--(7)], footnote 2; [RW26, p. 14, Prop. 8], second identity,
with the base matrix α and r = 3. The ± origins and the two denominators are
those of these formulas. No coordinate or metric-group assertion is an input.
-/

noncomputable section

namespace SICLean.L2c

/-- The positive branch of (4), as a real square root followed by ℝ → ℂ. -/
def originPlus (M : ℕ) : ℂ :=
  (Real.sqrt (((L2b.groupOrder M : ℝ) + 2 +
    Real.sqrt ((L2b.groupOrder M : ℝ) ^ 2 + 4 * (L2b.groupOrder M : ℝ))) / 2) : ℂ)

/-- The negative sign inside (4); the outer square root is still positive. -/
def originMinus (M : ℕ) : ℂ :=
  (Real.sqrt (((L2b.groupOrder M : ℝ) + 2 -
    Real.sqrt ((L2b.groupOrder M : ℝ) ^ 2 + 4 * (L2b.groupOrder M : ℝ))) / 2) : ℂ)

/-- [RW26, Thm. 2], together with footnote 2.
In the Fourier formula, μ is one common nonzero complex constant.
The dimension bound is part of the signature.
-/
structure Theorem2Input (M : ℕ) [Fact (4 ≤ M)]
    (Fplus Fminus : RWGroup M → ℂ) : Prop where
  origin_plus : Fplus 0 = originPlus M
  origin_minus : Fminus 0 = originMinus M
  mixed_reflection : ∀ u : RWGroup M,
    Fplus u * Fminus (-u) = (gaussian M u)⁻¹
  fourier : ∃ μ : ℂ, μ ≠ 0 ∧ ∀ u : RWGroup M,
    normalizedSum M (fun x => pairing M x u * Fplus x) = μ / Fminus u
  ratio_sum : ∀ u v : RWGroup M, (u, v) ≠ (0, 0) →
    normalizedSum M (fun x => pairing M x u * (Fplus x / Fminus (x + v))) =
      Fplus (u + v) / (Fminus u * Fminus v)
  agree_off_zero : ∀ u : RWGroup M, u ≠ 0 → Fplus u = Fminus u

/-- The full L2c input. The second field is the second identity of [RW26, Prop. 8]
for F⁺_{α³}(uα) = F⁺_{α³}(u), in the direction of [RW26, (38)].
The identity is recorded for F⁺.
-/
structure RWAnalyticInput (M : ℕ) [Fact (4 ≤ M)]
    (Fplus Fminus : RWGroup M → ℂ) : Prop where
  theorem2 : Theorem2Input M Fplus Fminus
  epsilon_invariant : ∀ u : RWGroup M, Fplus u = Fplus (epsilonAction M u)

end SICLean.L2c

-- These checks display the dimension parameter in the signatures.
#check @SICLean.L2c.Theorem2Input
#check @SICLean.L2c.RWAnalyticInput
#print SICLean.L2c.Theorem2Input
#print SICLean.L2c.RWAnalyticInput
