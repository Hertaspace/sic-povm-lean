import SICLean.L2rc.Coordinates

set_option autoImplicit false

/-!
# Rank-r special-value input

The equations below are [RW26, Thm. 2, (4)--(7)] and footnote 2 on p. 3.
They use the same branch conventions as L2c. The second identity of
[RW26, p. 14, Prop. 8] is taken with the base matrix L = `L2r.alpha d r`.
Its odd power γ is determined by (d,r), not by an input m.

No group, Gaussian, cardinality, coordinate, or FQD property is a field here.
-/

noncomputable section

namespace SICLean.L2rc

/-- The positive branch of [RW26, (4)], with N = tr(γ)-2. -/
def originPlus (d r : ℕ) : ℂ :=
  (Real.sqrt (((L2r.groupOrder d r : ℝ) + 2 +
    Real.sqrt ((L2r.groupOrder d r : ℝ) ^ 2 + 4 * (L2r.groupOrder d r : ℝ))) / 2) : ℂ)

/-- The negative sign inside (4); the outer square root is still positive. -/
def originMinus (d r : ℕ) : ℂ :=
  (Real.sqrt (((L2r.groupOrder d r : ℝ) + 2 -
    Real.sqrt ((L2r.groupOrder d r : ℝ) ^ 2 + 4 * (L2r.groupOrder d r : ℝ))) / 2) : ℂ)

/-- [RW26, Thm. 2] together with footnote 2. In (6), μ is one common
nonzero complex constant. -/
structure Theorem2Input (d r : ℕ) [Fact (L2r.Admissible d r)]
    (Fplus Fminus : RWGroup d r → ℂ) : Prop where
  origin_plus : Fplus 0 = originPlus d r
  origin_minus : Fminus 0 = originMinus d r
  mixed_reflection : ∀ u : RWGroup d r,
    Fplus u * Fminus (-u) = (gaussian d r u)⁻¹
  fourier : ∃ μ : ℂ, μ ≠ 0 ∧ ∀ u : RWGroup d r,
    normalizedSum d r (fun x => pairing d r x u * Fplus x) = μ / Fminus u
  ratio_sum : ∀ u v : RWGroup d r, (u, v) ≠ (0, 0) →
    normalizedSum d r (fun x => pairing d r x u * (Fplus x / Fminus (x + v))) =
      Fplus (u + v) / (Fminus u * Fminus v)
  agree_off_zero : ∀ u : RWGroup d r, u ≠ 0 → Fplus u = Fminus u

/-- Proposition 8 is only needed on its positive branch, F⁺(u)=F⁺(uL).
This is the base action, rather than the already trivial action of γ. -/
structure RWAnalyticInput (d r : ℕ) [Fact (L2r.Admissible d r)]
    (Fplus Fminus : RWGroup d r → ℂ) : Prop where
  theorem2 : Theorem2Input d r Fplus Fminus
  epsilon_invariant : ∀ u : RWGroup d r, Fplus u = Fplus (epsilonAction d r u)

end SICLean.L2rc

#check @SICLean.L2rc.Theorem2Input
#check @SICLean.L2rc.RWAnalyticInput
#print SICLean.L2rc.Theorem2Input
#print SICLean.L2rc.RWAnalyticInput
