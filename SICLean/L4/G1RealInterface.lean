import SICLean.L4.ModularDivisor
import SICLean.L4.FinitePrincipalParts

set_option autoImplicit false

/-!
# G1 real endpoint contract

The real-endpoint statement. [RW26, p. 7, (22), (23)]. This file does not assert `G1RealConclusion`.
That proposition is proved as `g1RealConclusion` in `SICLean.L4.G1RealConclusion`. No G2 theorem is
used.

All path integrals are integrals of f(path(t))*path'(t), as in the rotated integrals. Convergence is
in the conclusion, never in a chain field or a hypothesis. The finite circles are CCW.

Right sides are limits of the displayed meromorphic products on their explicit divisor-free loci, at
fixed τ. The contract includes nontriviality of those filters and existence of the finite limits.
Thus total division at a pole (whose specified Φ representative is 0) cannot substitute for a
removable value. No extra joint-τ regularity theorem is needed here.
-/

noncomputable section

open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4

def g1T (M : SL(2, ℤ)) (τ : ℝ) : ℝ :=
  (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)

def g1S (M : SL(2, ℤ)) (τ w : ℝ) (h ell : ℤ) : ℝ :=
  (M 1 0 : ℝ) * w + (h : ℝ) + (ell : ℝ) * g1T M τ

def g1L (M : SL(2, ℤ)) (τ w y : ℝ) (h ell p : ℤ) : ℝ :=
  g1S M τ w h ell + (M 1 0 : ℝ) * y + ((p : ℝ) - 1) * g1T M τ

/-- n multiplies γτ in the h term, not m. -/
def g1Exponent (M : SL(2, ℤ)) (τ w z : ℂ) (n h ell m : ℤ) : ℂ :=
  (((M 1 0 : ℂ) * z - (n : ℂ) + etaDenom M τ * (m : ℂ)) * w) /
      etaDenom M τ +
    (ell : ℂ) * (z + (m : ℂ) * τ) +
    (h : ℂ) * (z / etaDenom M τ + (n : ℂ) * etaMobius M τ)

/-- The prefactor, built from the actual eta multiplier and the principal square root. -/
def g1Prefactor (M : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  (etaMultiplier M)⁻¹ * Complex.sqrt (etaDenom M τ) *
    e ((etaMobius M τ - τ) / 24)

def g1SingleKernel (M : SL(2, ℤ)) (τ w : ℝ) (n h ell m : ℤ) (z : ℂ) : ℂ :=
  modularPhi M (m + 1) n z (τ : ℂ) *
    e (g1Exponent M (τ : ℂ) (w : ℂ) z n h ell m)

/-- A denominator pole is a regular zero of its reciprocal; it is not an extra forbidden chain
point. Its identification uses inverse charts, not an added nonvanishing hypothesis on the
denominator representative. -/
def g1RatioKernel (M : SL(2, ℤ)) (τ w y : ℝ)
    (n h ell p m : ℤ) (z : ℂ) : ℂ :=
  (modularPhi M (m + 1) n z (τ : ℂ) /
    modularPhi M (m + p) n (z + (y : ℂ)) (τ : ℂ)) *
    e (g1Exponent M (τ : ℂ) (w : ℂ) z n h ell m)

def g1NoPinch (M : SL(2, ℤ)) (τ y : ℝ) (p : ℤ) : Prop :=
  ∀ K J : ℕ,
    Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ)) (-1 - M 1 1 * p) →
      y ≠ -(((p : ℝ) + (K : ℝ)) * g1T M τ + 1 + (J : ℝ)) / (M 1 0 : ℝ)

/-! ## Concrete bent chain Γ_m. -/

def g1BentCrossing (M : SL(2, ℤ)) (τ δ : ℝ) (n m : ℤ) : ℝ :=
  ((n : ℝ) - (m : ℝ) * g1T M τ) / (M 1 0 : ℝ) - δ

def g1LowerDirection (ψ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-Real.pi / 2 + ψ : ℝ) : ℂ))

def g1BentLowerPoint (x ψ r : ℝ) : ℂ :=
  (x : ℂ) - Complex.I + (r : ℂ) * g1LowerDirection ψ

def g1VerticalPoint (x t : ℝ) : ℂ := (x : ℂ) + (t : ℂ) * Complex.I

/-- Outward lower-ray Jacobian. The integral below negates this ray. -/
def g1BentLowerPullback (f : ℂ → ℂ) (x ψ r : ℝ) : ℂ :=
  f (g1BentLowerPoint x ψ r) * g1LowerDirection ψ

def g1VerticalPullback (f : ℂ → ℂ) (x t : ℝ) : ℂ :=
  f (g1VerticalPoint x t) * Complex.I

def g1BentIntegral (f : ℂ → ℂ) (x ψ : ℝ) : ℂ :=
  -(∫ r : ℝ in Ici 0, g1BentLowerPullback f x ψ r) +
    ∫ t : ℝ in Ici (-1), g1VerticalPullback f x t

def G1BentIntegrable (f : ℂ → ℂ) (x ψ : ℝ) : Prop :=
  IntegrableOn (g1BentLowerPullback f x ψ) (Ici 0) ∧
    IntegrableOn (g1VerticalPullback f x) (Ici (-1))

/-! ## Vertical baseline and finitely many circles D_m(y). -/

/-- Only geometric data. No convergence, regularity or integral identity. -/
structure G1VerticalChain where
  crossing : ℝ
  centers : Finset ℝ
  radius : ℝ → ℝ

def g1CirclePullback (f : ℂ → ℂ) (r ρ θ : ℝ) : ℂ :=
  f (circleMap (r : ℂ) ρ θ) *
    (Complex.I * (circleMap (r : ℂ) ρ θ - (r : ℂ)))

def g1ChainIntegral (D : G1VerticalChain) (f : ℂ → ℂ) : ℂ :=
  (∫ t : ℝ, g1VerticalPullback f D.crossing t) +
    ∑ r ∈ D.centers, ∫ θ : ℝ in 0..(2 * Real.pi),
      g1CirclePullback f r (D.radius r) θ

def G1ChainIntegrable (D : G1VerticalChain) (f : ℂ → ℂ) : Prop :=
  Integrable (g1VerticalPullback f D.crossing) ∧
    ∀ r ∈ D.centers,
      IntervalIntegrable (g1CirclePullback f r (D.radius r)) volume 0 (2 * Real.pi)

/-- Circle winding at a real coordinate, with component-independent centers. -/
def g1CircleWinding (D : G1VerticalChain) (x : ℝ) : ℤ :=
  ∑ r ∈ D.centers, if |x - r| < D.radius r then 1 else 0

def g1LeftAssignment (D : G1VerticalChain) (x : ℝ) : ℤ :=
  (if x < D.crossing then 1 else 0) + g1CircleWinding D x

/-- Pure geometry: boundary avoidance and the precise 0/1 assignment. Extra circles at regular
coordinates are permitted. Labels/multiplicities of P,Z are not collapsed in the definitions of Φ.
-/
def G1Separates (D : G1VerticalChain) (P Z : Set ℝ) : Prop :=
  (∀ r ∈ D.centers, 0 < D.radius r) ∧
  (∀ x ∈ P ∪ Z, x ≠ D.crossing ∧
    ∀ r ∈ D.centers, |x - r| ≠ D.radius r) ∧
  (∀ x ∈ P, g1LeftAssignment D x = 0) ∧
  (∀ x ∈ Z, g1LeftAssignment D x = 1)

def g1NumeratorPoles (M : SL(2, ℤ)) (τ : ℝ) (n m : ℤ) : Set ℝ :=
  {x | ∃ K J : ℕ, (K, J) ∈ modularPhiPoleLabels M (m + 1) n ∧
    (x : ℂ) = modularPhiPolePoint M (m + 1) n (τ : ℂ) K J}

def g1InversePoles (M : SL(2, ℤ)) (τ y : ℝ) (n p m : ℤ) : Set ℝ :=
  {x | ∃ K J : ℕ, (K, J) ∈ modularPhiZeroLabels M (m + p) n ∧
    (x : ℂ) = modularPhiZeroPoint M (m + p) n (τ : ℂ) K J - (y : ℂ)}

/-! ## Removable values of the displayed right sides. -/

def g1SingleRawRHS (M : SL(2, ℤ)) (τ : ℝ) (h ell : ℤ) (w : ℂ) : ℂ :=
  (modularPhi M ell (1 - h) w (τ : ℂ))⁻¹

def g1SingleRHSLocus (M : SL(2, ℤ)) (τ : ℝ) (h ell : ℤ) : Set ℂ :=
  {w | (w, (τ : ℂ)) ∈ modularPhiNonvanishingDomain M ell (1 - h)}

def g1SingleRHS (M : SL(2, ℤ)) (τ w : ℝ) (h ell : ℤ) : ℂ :=
  limUnder (𝓝[g1SingleRHSLocus M τ h ell] (w : ℂ))
    (g1SingleRawRHS M τ h ell)

def g1RatioRawRHS (M : SL(2, ℤ)) (τ : ℝ) (h ell p : ℤ) (v : ℂ × ℂ) : ℂ :=
  modularPhi M (p + ell) (-h) (v.1 + v.2) (τ : ℂ) /
    (modularPhi M p 0 v.2 (τ : ℂ) * modularPhi M ell (1 - h) v.1 (τ : ℂ))

def g1RatioRHSLocus (M : SL(2, ℤ)) (τ : ℝ) (h ell p : ℤ) : Set (ℂ × ℂ) :=
  {v | (v.1 + v.2, (τ : ℂ)) ∈ modularPhiNonvanishingDomain M (p + ell) (-h) ∧
    (v.2, (τ : ℂ)) ∈ modularPhiNonvanishingDomain M p 0 ∧
    (v.1, (τ : ℂ)) ∈ modularPhiNonvanishingDomain M ell (1 - h)}

def g1RatioRHS (M : SL(2, ℤ)) (τ w y : ℝ) (h ell p : ℤ) : ℂ :=
  limUnder (𝓝[g1RatioRHSLocus M τ h ell p] ((w : ℂ), (y : ℂ)))
    (g1RatioRawRHS M τ h ell p)

/-- Semantics of “take the removable value”. A bottom filter cannot make the claim vacuous. This is
an output of G1, not a premise. -/
def G1SingleRemovable (M : SL(2, ℤ)) (τ w : ℝ) (h ell : ℤ) : Prop :=
  NeBot (𝓝[g1SingleRHSLocus M τ h ell] (w : ℂ)) ∧
    Tendsto (g1SingleRawRHS M τ h ell)
      (𝓝[g1SingleRHSLocus M τ h ell] (w : ℂ))
      (𝓝 (g1SingleRHS M τ w h ell))

def G1RatioRemovable (M : SL(2, ℤ)) (τ w y : ℝ) (h ell p : ℤ) : Prop :=
  NeBot (𝓝[g1RatioRHSLocus M τ h ell p] ((w : ℂ), (y : ℂ))) ∧
    Tendsto (g1RatioRawRHS M τ h ell p)
      (𝓝[g1RatioRHSLocus M τ h ell p] ((w : ℂ), (y : ℂ)))
      (𝓝 (g1RatioRHS M τ w y h ell p))

/-! ## The G1 interface. The proof is `g1RealConclusion` in `SICLean.L4.G1RealConclusion`. -/

def G1RealConclusion : Prop :=
  ∀ (M : SL(2, ℤ)) (τ : ℝ), 0 < M 1 0 → 0 < g1T M τ →
    (∀ (n h ell : ℤ) (w δ ψ : ℝ),
      0 < g1S M τ w h ell → 0 < δ → 0 < ψ → ψ < Real.pi / 4 →
      G1SingleRemovable M τ w h ell ∧
      (∀ m ∈ Finset.range (M 1 0).toNat,
        G1BentIntegrable (g1SingleKernel M τ w n h ell (m : ℤ))
          (g1BentCrossing M τ δ n (m : ℤ)) ψ) ∧
      (∑ m ∈ Finset.range (M 1 0).toNat,
        g1BentIntegral (g1SingleKernel M τ w n h ell (m : ℤ))
          (g1BentCrossing M τ δ n (m : ℤ)) ψ) =
        g1Prefactor M (τ : ℂ) * g1SingleRHS M τ w h ell) ∧
    (∀ (n h ell p : ℤ) (w y : ℝ),
      0 < g1S M τ w h ell → g1L M τ w y h ell p < 0 →
      g1NoPinch M τ y p →
      G1RatioRemovable M τ w y h ell p ∧
      (∃ D : Fin (M 1 0).toNat → G1VerticalChain,
        ∀ m, G1Separates (D m) (g1NumeratorPoles M τ n (m : ℤ))
          (g1InversePoles M τ y n p (m : ℤ))) ∧
      (∀ D : Fin (M 1 0).toNat → G1VerticalChain,
        (∀ m, G1Separates (D m) (g1NumeratorPoles M τ n (m : ℤ))
          (g1InversePoles M τ y n p (m : ℤ))) →
        (∀ m, G1ChainIntegrable (D m) (g1RatioKernel M τ w y n h ell p (m : ℤ))) ∧
        (∑ m : Fin (M 1 0).toNat,
          g1ChainIntegral (D m) (g1RatioKernel M τ w y n h ell p (m : ℤ))) =
            g1Prefactor M (τ : ℂ) * g1RatioRHS M τ w y h ell p))

#check @g1Exponent
#check @g1ChainIntegral
#check @G1RealConclusion
#print g1NoPinch
#print g1BentIntegral
#print g1RatioRawRHS
#print G1RealConclusion

end SICLean.L4
