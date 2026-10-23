import SICLean.L4.FaddeevContour
import Mathlib.Analysis.Complex.CauchyIntegral
import SICLean.L4.FinitePrincipalPartsAux

set_option autoImplicit false

/-!
# Finite principal parts

The definitions are finite sums and explicitly oriented integrals, with no analytic assumptions
inside. The proofs are supplied by the auxiliary module. `a j` is the coefficient of
`(w-p)^(-(j+1))`, so `a 0` is the residue. The empty principal part has residue zero, irrespective
of `a 0`.

These finite expansions are set up for the product comparison. The intended applications are [RW26,
p. 5, Appendix A.1, p. 28, (57)]. The existing starting points are
`Contour.integral_boundary_rect_inv`, `Contour.integral_boundary_rect_simple_pole`, and
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

Rectangles and full outer circles are counterclockwise. Hole boundaries and the upper semicircle
from left to right are clockwise. No arbitrary curve, winding number, infinite truncation, uniform
cluster estimate or moving chain result is asserted here. In the finite ledger, actual local
expansions and analyticity off the listed centers are hypotheses of the theorem, not fields of an
object postulated to satisfy the residue theorem.
-/

noncomputable section

open Complex Set MeasureTheory
open scoped Interval BigOperators

namespace SICLean.L4.FinitePrincipalParts

/-- Literal negative Laurent polynomial, with order at most `N`. -/
def principalPart (p : ℂ) (N : ℕ) (a : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, a j / (w - p) ^ (j + 1)

/-- The coefficient actually present at exponent `-1`. -/
def residueCoefficient (N : ℕ) (a : ℕ → ℂ) : ℂ := if N = 0 then 0 else a 0

/-- A finite sum, with each center's order specified independently. -/
def finitePrincipalPart {ι : Type*} (s : Finset ι) (p : ι → ℂ)
    (N : ι → ℕ) (a : ι → ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ i ∈ s, principalPart (p i) (N i) (a i) w

/-- Full positively oriented circle: `θ` increases from `0` to `2π`. -/
def circleCCW (p : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ θ : ℝ in 0..(2 * Real.pi),
    f (circleMap p r θ) * (Complex.I * (circleMap p r θ - p))

/-- The same circle as a clockwise boundary of a hole. -/
def circleCW (p : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ θ : ℝ in (2 * Real.pi)..0,
    f (circleMap p r θ) * (Complex.I * (circleMap p r θ - p))

/-- Upper indentation from `p-r` to `p+r`, hence clockwise. -/
def upperArcCW (p : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ θ : ℝ in Real.pi..0,
    f (circleMap p r θ) * (Complex.I * (circleMap p r θ - p))

def closedRectangle (lo hi : ℂ) : Set ℂ :=
  {w | lo.re ≤ w.re ∧ w.re ≤ hi.re ∧ lo.im ≤ w.im ∧ w.im ≤ hi.im}

def openRectangle (lo hi : ℂ) : Set ℂ :=
  {w | lo.re < w.re ∧ w.re < hi.re ∧ lo.im < w.im ∧ w.im < hi.im}

/-- Bottom rightwards, right upwards, top leftwards, left downwards. -/
def rectangleCCW (lo hi : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in lo.re..hi.re, f ((x : ℂ) + (lo.im : ℂ) * Complex.I)) +
    Complex.I * (∫ y : ℝ in lo.im..hi.im,
      f ((hi.re : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ x : ℝ in lo.re..hi.re, f ((x : ℂ) + (hi.im : ℂ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in lo.im..hi.im,
      f ((lo.re : ℂ) + (y : ℂ) * Complex.I))

/-- Implementation bridge to Mathlib `circleIntegral`, whose radius is `|r|`. -/
theorem circleCCW_eq_circleIntegral (p : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (hr : 0 < r) : circleCCW p r f = ∮ w in C(p, r), f w := by
  exact FinitePrincipalPartsAux.circleCCW_eq_circleIntegral p r f hr

/-- `intervalIntegral.integral_symm`: the sign of a hole correction. -/
theorem circleCW_eq_neg (p : ℂ) (r : ℝ) (f : ℂ → ℂ) :
    circleCW p r f = -circleCCW p r f := by
  exact FinitePrincipalPartsAux.circleCW_eq_neg p r f

/-- Project finite principal-part calculation. Only the simple term survives. Mathlib:
`circleIntegral.integral_sub_zpow_of_ne` and `circleIntegral.integral_sub_inv_of_mem_ball`. -/
theorem circleCCW_inverse_power (p : ℂ) (r : ℝ) (k : ℕ) (hr : 0 < r) :
    circleCCW p r (fun w => 1 / (w - p) ^ (k + 1)) =
      if k = 0 then 2 * (Real.pi : ℂ) * Complex.I else 0 := by
  exact FinitePrincipalPartsAux.circleCCW_inverse_power p r k hr

/-- Finite upper-arc calculation, retaining the possibly divergent high-order terms. For `k=0` the
correction is `-πi` [RW26, p. 5]. -/
theorem upperArcCW_inverse_power (p : ℂ) (r : ℝ) (k : ℕ) (hr : 0 < r) :
    upperArcCW p r (fun w => 1 / (w - p) ^ (k + 1)) =
      if k = 0 then -(Real.pi : ℂ) * Complex.I
      else ((-1 : ℂ) ^ k - 1) / ((k : ℂ) * (r : ℂ) ^ k) := by
  exact FinitePrincipalPartsAux.upperArcCW_inverse_power p r k hr

/-- Linearity plus the preceding basis integrals. -/
theorem circleCCW_principalPart (p : ℂ) (r : ℝ) (N : ℕ) (a : ℕ → ℂ)
    (hr : 0 < r) :
    circleCCW p r (principalPart p N a) =
      2 * (Real.pi : ℂ) * Complex.I * residueCoefficient N a := by
  exact FinitePrincipalPartsAux.circleCCW_principalPart p r N a hr

/-- Local expansion version, including orders zero and greater than one. The center value of `f` is
irrelevant to the circle integral. -/
theorem circleCCW_of_local_principalPart (f g : ℂ → ℂ) (p : ℂ) (r : ℝ)
    (N : ℕ) (a : ℕ → ℂ) (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall p r))
    (hfg : ∀ w ∈ Metric.closedBall p r, w ≠ p →
      f w = principalPart p N a w + g w) :
    circleCCW p r f = 2 * (Real.pi : ℂ) * Complex.I * residueCoefficient N a := by
  exact FinitePrincipalPartsAux.circleCCW_of_local_principalPart f g p r N a hr hg hfg

/-- Finite local integral account. Disjointness is explicit, so these are separate holes. [RW26]. -/
theorem finite_circle_ledger {ι : Type*} (s : Finset ι) (f : ℂ → ℂ)
    (p : ι → ℂ) (r : ι → ℝ) (N : ι → ℕ) (a : ι → ℕ → ℂ)
    (g : ι → ℂ → ℂ) (hr : ∀ i ∈ s, 0 < r i)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Metric.closedBall (p i) (r i)) (Metric.closedBall (p j) (r j)))
    (hg : ∀ i ∈ s, AnalyticOnNhd ℂ (g i) (Metric.closedBall (p i) (r i)))
    (hfg : ∀ i ∈ s, ∀ w ∈ Metric.closedBall (p i) (r i), w ≠ p i →
      f w = principalPart (p i) (N i) (a i) w + g i w) :
    (∑ i ∈ s, circleCCW (p i) (r i) f) =
      2 * (Real.pi : ℂ) * Complex.I * ∑ i ∈ s, residueCoefficient (N i) (a i) := by
  exact FinitePrincipalPartsAux.finite_circle_ledger s f p r N a g hr hdisj hg hfg

/-- Finite rectangular ledger with three directly usable conclusions: outer boundary = positive
small circles, outer + hole boundaries = 0, and the explicit sum of simple coefficients. No boundary
pole is allowed. [RW26, p. 5]. All analytic input is stated, rather than assuming the desired
ledger. -/
theorem rectangle_finite_principal_parts {ι : Type*} (s : Finset ι)
    (f : ℂ → ℂ) (lo hi : ℂ) (p : ι → ℂ) (r : ι → ℝ)
    (N : ι → ℕ) (a : ι → ℕ → ℂ) (g : ι → ℂ → ℂ)
    (hre : lo.re < hi.re) (him : lo.im < hi.im)
    (hr : ∀ i ∈ s, 0 < r i)
    (hinside : ∀ i ∈ s, Metric.closedBall (p i) (r i) ⊆ openRectangle lo hi)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Metric.closedBall (p i) (r i)) (Metric.closedBall (p j) (r j)))
    (hf : AnalyticOnNhd ℂ f (closedRectangle lo hi \ (p '' (s : Set ι))))
    (hg : ∀ i ∈ s, AnalyticOnNhd ℂ (g i) (Metric.closedBall (p i) (r i)))
    (hfg : ∀ i ∈ s, ∀ w ∈ Metric.closedBall (p i) (r i), w ≠ p i →
      f w = principalPart (p i) (N i) (a i) w + g i w) :
    rectangleCCW lo hi f = (∑ i ∈ s, circleCCW (p i) (r i) f) ∧
      rectangleCCW lo hi f + (∑ i ∈ s, circleCW (p i) (r i) f) = 0 ∧
      rectangleCCW lo hi f =
        2 * (Real.pi : ℂ) * Complex.I * ∑ i ∈ s, residueCoefficient (N i) (a i) := by
  exact FinitePrincipalPartsAux.rectangle_finite_principal_parts s f lo hi p r N a g hre him hr hinside hdisj hf hg hfg

#check Complex.integral_boundary_rect_eq_zero_of_differentiableOn
#check Contour.integral_boundary_rect_simple_pole
#check DiffContOnCl.circleIntegral_eq_zero
#check circleIntegral
#check hasDerivAt_circleMap
#check circleIntegral.integral_sub_zpow_of_ne
#check circleIntegral.integral_sub_inv_of_mem_ball
#print principalPart
#print rectangle_finite_principal_parts
#print axioms principalPart
#print axioms rectangle_finite_principal_parts

end SICLean.L4.FinitePrincipalParts
