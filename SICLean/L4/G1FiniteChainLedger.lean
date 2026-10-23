import SICLean.L4.G1RatioTailBounds
import SICLean.L4.ModularClusterLedger
import SICLean.L4.G1FiniteChainLedgerAux

set_option autoImplicit false

/-!
# Finite segments, circles and the assignment account

This is the finite residue account for the contour deformations of [RW26, p. 7, p. 13], without a
general closed-curve winding library. The actual finite principal parts and
their circle/rectangle APIs are the existing `FinitePrincipalParts` and `ModularClusterLedger`
interfaces.

The finite support consists of distinct real candidate centers. Orders are full label budgets, not
simple-pole assumptions. At a candidate center the raw representative can differ from its removable
value: all principal-part equations exclude the centers. All integration boundaries avoid them.
Circles may overlap, have regular centers, contain several poles, or cross a baseline. The final
account needs only geometric boundary avoidance and equality of the existing `g1LeftAssignment`.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1FiniteLedger

/-- Union only: both constituents are the contract's existing pole sets. -/
def candidatePoles (M : SL(2, ℤ)) (τ y : ℝ) (n p m : ℤ) : Set ℝ :=
  g1NumeratorPoles M τ n m ∪ g1InversePoles M τ y n p m

/-- Exactly the boundary part of G1Separates, without a prescribed assignment. This does not add a
new chain type or analytic condition. -/
def boundaryAvoids (D : G1VerticalChain) (S : Set ℝ) : Prop :=
  (∀ r ∈ D.centers, 0 < D.radius r) ∧
    ∀ x ∈ S, x ≠ D.crossing ∧ ∀ r ∈ D.centers, |x - r| ≠ D.radius r

def sameAssignment (D₀ D₁ : G1VerticalChain) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, g1LeftAssignment D₀ x = g1LeftAssignment D₁ x

def boundedBy (D : G1VerticalChain) (B : ℝ) : Prop :=
  |D.crossing| < B ∧ ∀ r ∈ D.centers, |r| + D.radius r < B

def closedBox (B R : ℝ) : Set ℂ :=
  FinitePrincipalParts.closedRectangle (g1VerticalPoint (-B) (-R)) (g1VerticalPoint B R)

def verticalSegment (f : ℂ → ℂ) (x R : ℝ) : ℂ :=
  ∫ t : ℝ in -R..R, g1VerticalPullback f x t

/-- Bottom rightwards minus top rightwards. Thus right vertical minus left vertical plus this
expression is counterclockwise. -/
def connectors (f : ℂ → ℂ) (x₀ x₁ R : ℝ) : ℂ :=
  G1RatioTail.horizontalIntegral f x₀ x₁ (-R) -
    G1RatioTail.horizontalIntegral f x₀ x₁ R

def truncatedIntegral (D : G1VerticalChain) (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  verticalSegment f D.crossing R +
    ∑ r ∈ D.centers, FinitePrincipalParts.circleCCW (r : ℂ) (D.radius r) f

def baselineJump (x₀ x₁ a : ℝ) : ℤ :=
  (if a < x₁ then 1 else 0) - (if a < x₀ then 1 else 0)

def principalParts (P : Finset ℝ) (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (z : ℂ) : ℂ :=
  FinitePrincipalParts.finitePrincipalPart P (fun x => (x : ℂ)) N A z

def orderBudget (M : SL(2, ℤ)) (τ w y : ℝ) (n h ell p m : ℤ) (x : ℝ) : ℕ :=
  ModularCluster.poleBudget M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)
    (x : ℂ) (τ : ℂ)

def eraseCircle (D : G1VerticalChain) (r : ℝ) : G1VerticalChain :=
  { D with centers := D.centers.erase r }

/-- The actual contract circle and the existing CCW integral have the same Jacobian and sign. [RW26,
p. 7, p. 13]. -/
theorem circle_eq_circleCCW (f : ℂ → ℂ) (r ρ : ℝ) :
    (∫ θ : ℝ in 0..(2 * Real.pi), g1CirclePullback f r ρ θ) =
      FinitePrincipalParts.circleCCW (r : ℂ) ρ f := by
  rfl

/-- Distinct candidate centers in a bounded real interval form a finite set, including rational T
and cross-class coincidences. [RW26, p. 6, p. 13]. -/
theorem finite_candidates (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y B : ℝ) (n p m : ℤ) (hT : 0 < g1T M τ) :
    ∃ P : Finset ℝ, (P : Set ℝ) = candidatePoles M τ y n p m ∩ Icc (-B) B := by
  let k := G1Pinch.ratioData (0 : ℂ) (y : ℂ) n 0 0 p m
  have hfinite := ModularCluster.boundedCenters_finite M hM k (τ : ℂ)
    (real_mem_modularPhiDomain M τ hT) |B| (abs_nonneg B)
  have htarget : (candidatePoles M τ y n p m ∩ Icc (-B) B).Finite := by
    apply (hfinite.image Complex.re).subset
    intro x hx
    refine ⟨(x : ℂ), ?_, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (abs_le.mpr hx.2).trans (le_abs_self B)
    · rcases hx.1 with ⟨K, J, hlabel, hpoint⟩ | ⟨K, J, hlabel, hpoint⟩
      · refine ⟨(true, K, J), ?_, ?_⟩
        · simpa [ModularCluster.labels, k, G1Pinch.ratioData] using hlabel
        · simpa [ModularCluster.branchPoint, k, G1Pinch.ratioData] using hpoint.symm
      · refine ⟨(false, K, J), ?_, ?_⟩
        · simpa [ModularCluster.labels, k, G1Pinch.ratioData] using hlabel
        · simpa [ModularCluster.branchPoint, k, G1Pinch.ratioData] using hpoint.symm
  exact ⟨htarget.toFinset, htarget.coe_toFinset⟩

/-- The actual ratio kernel supplies the finite expansion; it is not assumed by any final chain
theorem. Full orders are budgets and may have zero leading coefficients. [RW26, p. 6, p. 13]. -/
theorem exists_finite_principalParts (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y B R : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hB : 0 < B) (hR : 0 < R) (P : Finset ℝ)
    (hP : (P : Set ℝ) = candidatePoles M τ y n p m ∩ Icc (-B) B) :
    ∃ (A : ℝ → ℕ → ℂ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g (closedBox B R) ∧
        ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
          g1RatioKernel M τ w y n h ell p m z =
            principalParts P (orderBudget M τ w y n h ell p m) A z + g z := by
  exact G1FiniteChainLedgerAux.exists_finite_principalParts M hM τ w y B R
    n h ell p m hT hB hR P hP

/-- Any one circle: outside principal parts are absorbed in the analytic remainder. No pairwise
disjointness or pole-center hypothesis. [RW26, p. 7, p. 13]. -/
theorem circle_finite_ledger (f g : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (B R r ρ : ℝ) (hρ : 0 < ρ)
    (hinside : Metric.closedBall (r : ℂ) ρ ⊆ closedBox B R)
    (hsafe : ∀ x ∈ P, |x - r| ≠ ρ)
    (hg : AnalyticOnNhd ℂ g (closedBox B R))
    (hfg : ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      f z = principalParts P N A z + g z) :
    FinitePrincipalParts.circleCCW (r : ℂ) ρ f =
      2 * (Real.pi : ℂ) * Complex.I *
        ∑ x ∈ P, if |x - r| < ρ then FinitePrincipalParts.residueCoefficient (N x) (A x) else 0 := by
  exact G1FiniteChainLedgerAux.circle_finite_ledger f g P N A B R r ρ
    hρ hinside hsafe hg hfg

/-- Reorder arbitrary finite circles by the existing circle winding. [RW26, p. 7, p. 13]. -/
theorem circle_sum_winding (f g : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (D : G1VerticalChain) (B R : ℝ)
    (hD : boundaryAvoids D (P : Set ℝ)) (hB : boundedBy D B) (hR : B < R)
    (hg : AnalyticOnNhd ℂ g (closedBox B R))
    (hfg : ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      f z = principalParts P N A z + g z) :
    (∑ r ∈ D.centers, FinitePrincipalParts.circleCCW (r : ℂ) (D.radius r) f) =
      2 * (Real.pi : ℂ) * Complex.I *
        ∑ x ∈ P, (g1CircleWinding D x : ℂ) * FinitePrincipalParts.residueCoefficient (N x) (A x) := by
  have hcircle (r : ℝ) (hr : r ∈ D.centers) := circle_finite_ledger f g P N A B R
    r (D.radius r) (hD.1 r hr)
  have hinside (r : ℝ) (hr : r ∈ D.centers) :
      Metric.closedBall (r : ℂ) (D.radius r) ⊆ closedBox B R := by
    intro z hz
    have hn : ‖z - (r : ℂ)‖ ≤ D.radius r := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    have hre := (Complex.abs_re_le_norm (z - (r : ℂ))).trans hn
    have him := (Complex.abs_im_le_norm (z - (r : ℂ))).trans hn
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero] at hre him
    obtain ⟨hlre, hure⟩ := abs_le.mp hre
    obtain ⟨hlim, huim⟩ := abs_le.mp him
    have hb := hB.2 r hr
    have hr₁ := le_abs_self r
    have hr₂ := neg_le_abs r
    have hbox : -B ≤ z.re ∧ z.re ≤ B ∧ -R ≤ z.im ∧ z.im ≤ R := by
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith [abs_nonneg r]
    simpa [closedBox, FinitePrincipalParts.closedRectangle, g1VerticalPoint] using hbox
  calc
    _ = ∑ r ∈ D.centers, 2 * (Real.pi : ℂ) * Complex.I *
        ∑ x ∈ P, if |x - r| < D.radius r then
          FinitePrincipalParts.residueCoefficient (N x) (A x) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hcircle r hr (hinside r hr) (fun x hx => (hD.2 x hx).2 r hr) hg hfg
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      simp only [g1CircleWinding, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs <;> simp

/-- Orientation only; this holds for either order of the baselines. [RW26, p. 7, p. 13]. -/
theorem rectangle_orientation (f : ℂ → ℂ) (x₀ x₁ R : ℝ) :
    FinitePrincipalParts.rectangleCCW (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) f =
      verticalSegment f x₁ R - verticalSegment f x₀ R + connectors f x₀ x₁ R := by
  simp only [FinitePrincipalParts.rectangleCCW, g1VerticalPoint,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  simp only [verticalSegment, g1VerticalPullback, g1VerticalPoint,
    intervalIntegral.integral_mul_const, connectors, G1RatioTail.horizontalIntegral]
  ring

/-- Finite directed strip account. In particular, right shift = positive residues + top - bottom. No
x₀<x₁ restriction is imposed. [RW26, p. 7, p. 13]. -/
theorem vertical_segment_ledger (f g : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (B R x₀ x₁ : ℝ)
    (hR : 0 < R) (hx₀ : |x₀| < B) (hx₁ : |x₁| < B)
    (hsafe₀ : x₀ ∉ P) (hsafe₁ : x₁ ∉ P)
    (hg : AnalyticOnNhd ℂ g (closedBox B R))
    (hfg : ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      f z = principalParts P N A z + g z) :
    verticalSegment f x₁ R - verticalSegment f x₀ R + connectors f x₀ x₁ R =
      2 * (Real.pi : ℂ) * Complex.I *
        ∑ x ∈ P, (baselineJump x₀ x₁ x : ℂ) * FinitePrincipalParts.residueCoefficient (N x) (A x) := by
  rw [← rectangle_orientation]
  exact G1FiniteChainLedgerAux.rectangle_finite_ledger f g P N A B R x₀ x₁
    hR hx₀ hx₁ hsafe₀ hsafe₁ hg hfg

/-- The finite coefficient is assignment(D₁)-assignment(D₀), not its negative. This analytic-input
lemma is discharged for the actual kernel by exists_finite_principalParts and finite_zero_assignment
below. [RW26, p. 7, p. 13]. -/
theorem finite_chain_ledger (f g : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (D₀ D₁ : G1VerticalChain) (B R : ℝ)
    (hD₀ : boundaryAvoids D₀ (P : Set ℝ)) (hD₁ : boundaryAvoids D₁ (P : Set ℝ))
    (hB₀ : boundedBy D₀ B) (hB₁ : boundedBy D₁ B) (hR : B < R)
    (hg : AnalyticOnNhd ℂ g (closedBox B R))
    (hfg : ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      f z = principalParts P N A z + g z) :
    truncatedIntegral D₁ f R - truncatedIntegral D₀ f R +
        connectors f D₀.crossing D₁.crossing R =
      2 * (Real.pi : ℂ) * Complex.I *
        ∑ x ∈ P, ((g1LeftAssignment D₁ x - g1LeftAssignment D₀ x : ℤ) : ℂ) *
          FinitePrincipalParts.residueCoefficient (N x) (A x) := by
  have hRpos : 0 < R := lt_trans (lt_of_le_of_lt (abs_nonneg _) hB₀.1) hR
  have hsafe₀ : D₀.crossing ∉ P := by
    intro hx
    exact (hD₀.2 D₀.crossing hx).1 rfl
  have hsafe₁ : D₁.crossing ∉ P := by
    intro hx
    exact (hD₁.2 D₁.crossing hx).1 rfl
  have hv := vertical_segment_ledger f g P N A B R D₀.crossing D₁.crossing
    hRpos hB₀.1 hB₁.1 hsafe₀ hsafe₁ hg hfg
  have hc₀ := circle_sum_winding f g P N A D₀ B R hD₀ hB₀ hR hg hfg
  have hc₁ := circle_sum_winding f g P N A D₁ B R hD₁ hB₁ hR hg hfg
  unfold truncatedIntegral
  rw [hc₀, hc₁]
  calc
    _ = (verticalSegment f D₁.crossing R - verticalSegment f D₀.crossing R +
        connectors f D₀.crossing D₁.crossing R) +
        (2 * (Real.pi : ℂ) * Complex.I *
          ∑ x ∈ P, (g1CircleWinding D₁ x : ℂ) *
            FinitePrincipalParts.residueCoefficient (N x) (A x)) -
        (2 * (Real.pi : ℂ) * Complex.I *
          ∑ x ∈ P, (g1CircleWinding D₀ x : ℂ) *
            FinitePrincipalParts.residueCoefficient (N x) (A x)) := by ring
    _ = _ := by
      rw [hv]
      rw [← mul_add, ← mul_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      simp only [← add_mul, ← sub_mul]
      congr 1
      simp only [g1LeftAssignment, baselineJump, Int.cast_sub, Int.cast_add]
      ring

/-- Actual kernel, no expansion or integral identity assumed. This is finite truncation plus
horizontal edges; it does not assert the infinite chain equality by definition. [RW26, p. 7, p. 13].
-/
theorem finite_zero_assignment (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y B R : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (D₀ D₁ : G1VerticalChain)
    (hD₀ : boundaryAvoids D₀ (candidatePoles M τ y n p m))
    (hD₁ : boundaryAvoids D₁ (candidatePoles M τ y n p m))
    (hassign : sameAssignment D₀ D₁ (candidatePoles M τ y n p m))
    (hB₀ : boundedBy D₀ B) (hB₁ : boundedBy D₁ B) (hR : B < R) :
    truncatedIntegral D₁ (g1RatioKernel M τ w y n h ell p m) R -
        truncatedIntegral D₀ (g1RatioKernel M τ w y n h ell p m) R +
        connectors (g1RatioKernel M τ w y n h ell p m) D₀.crossing D₁.crossing R = 0 := by
  obtain ⟨P, hP⟩ := finite_candidates M hM τ y B n p m hT
  have hBpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) hB₀.1
  have hRpos : 0 < R := hBpos.trans hR
  obtain ⟨A, g, hg, hfg⟩ := exists_finite_principalParts M hM τ w y B R
    n h ell p m hT hBpos hRpos P hP
  have hsub : (P : Set ℝ) ⊆ candidatePoles M τ y n p m := by
    rw [hP]
    exact inter_subset_left
  have hb₀ : boundaryAvoids D₀ (P : Set ℝ) :=
    ⟨hD₀.1, fun x hx => hD₀.2 x (hsub hx)⟩
  have hb₁ : boundaryAvoids D₁ (P : Set ℝ) :=
    ⟨hD₁.1, fun x hx => hD₁.2 x (hsub hx)⟩
  rw [finite_chain_ledger _ g P _ A D₀ D₁ B R hb₀ hb₁ hB₀ hB₁ hR hg hfg]
  have hzero : ∀ x ∈ P, g1LeftAssignment D₁ x - g1LeftAssignment D₀ x = 0 := by
    intro x hx
    rw [hassign x (hsub hx)]
    exact sub_self _
  trans (2 * (Real.pi : ℂ) * Complex.I) * 0
  · congr 1
    apply Finset.sum_eq_zero
    intro x hx
    rw [hzero x hx]
    simp only [Int.cast_zero, zero_mul]
  · exact mul_zero _

/-- A regular center alone is insufficient. The whole closed disk must avoid the candidate poles.
[RW26, p. 7, p. 13]. -/
theorem circle_regular_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y r ρ : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ) (hρ : 0 < ρ)
    (hsafe : ∀ x ∈ candidatePoles M τ y n p m, ρ < |x - r|) :
    FinitePrincipalParts.circleCCW (r : ℂ) ρ (g1RatioKernel M τ w y n h ell p m) = 0 := by
  let B := |r| + ρ + 1
  let R := B + 1
  have hB : 0 < B := by dsimp [B]; linarith [abs_nonneg r]
  have hR : 0 < R := by dsimp [R]; linarith
  obtain ⟨P, hP⟩ := finite_candidates M hM τ y B n p m hT
  obtain ⟨A, g, hg, hfg⟩ := exists_finite_principalParts M hM τ w y B R
    n h ell p m hT hB hR P hP
  have hpoles (x : ℝ) (hx : x ∈ P) : x ∈ candidatePoles M τ y n p m := by
    have hx' : x ∈ (P : Set ℝ) := hx
    rw [hP] at hx'
    exact hx'.1
  have hinside : Metric.closedBall (r : ℂ) ρ ⊆ closedBox B R := by
    intro z hz
    have hn : ‖z - (r : ℂ)‖ ≤ ρ := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    have hre := (Complex.abs_re_le_norm (z - (r : ℂ))).trans hn
    have him := (Complex.abs_im_le_norm (z - (r : ℂ))).trans hn
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero] at hre him
    obtain ⟨hlre, hure⟩ := abs_le.mp hre
    obtain ⟨hlim, huim⟩ := abs_le.mp him
    have hbox : -B ≤ z.re ∧ z.re ≤ B ∧ -R ≤ z.im ∧ z.im ≤ R := by
      dsimp [B, R]
      have hr₁ := le_abs_self r
      have hr₂ := neg_le_abs r
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith [abs_nonneg r]
    simpa [closedBox, FinitePrincipalParts.closedRectangle, g1VerticalPoint] using hbox
  rw [circle_finite_ledger _ g P _ A B R r ρ hρ hinside
    (fun x hx => (hsafe x (hpoles x hx)).ne') hg hfg]
  have hsum : (∑ x ∈ P, if |x - r| < ρ then
      FinitePrincipalParts.residueCoefficient (orderBudget M τ w y n h ell p m x) (A x)
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact if_neg (not_lt.mpr (hsafe x (hpoles x hx)).le)
  rw [hsum, mul_zero]

/-- One whole possibly multiple cluster. The residue is the coefficient at exponent -1 of its full
principal part. [RW26, p. 6, p. 13]. -/
theorem circle_isolated_residue (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y r ρ : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ) (hρ : 0 < ρ)
    (hiso : ∀ x ∈ candidatePoles M τ y n p m, |x - r| ≤ ρ → x = r) :
    ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), AnalyticOnNhd ℂ g (Metric.closedBall (r : ℂ) ρ) ∧
      (∀ z ∈ Metric.closedBall (r : ℂ) ρ, z ≠ (r : ℂ) →
        g1RatioKernel M τ w y n h ell p m z =
          FinitePrincipalParts.principalPart (r : ℂ) (orderBudget M τ w y n h ell p m r) A z + g z) ∧
      FinitePrincipalParts.circleCCW (r : ℂ) ρ (g1RatioKernel M τ w y n h ell p m) =
        2 * (Real.pi : ℂ) * Complex.I *
          FinitePrincipalParts.residueCoefficient (orderBudget M τ w y n h ell p m r) A := by
  let k := G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m
  have hτ : (τ : ℂ) ∈ modularPhiDomain M := real_mem_modularPhiDomain M τ hT
  have hbranches : ∀ b ∈ ModularCluster.labels M k,
      dist (ModularCluster.branchPoint M k (τ : ℂ) b) (r : ℂ) ≤ ρ →
      ModularCluster.branchPoint M k (τ : ℂ) b = (r : ℂ) := by
    intro b hb hd
    obtain ⟨x, hx, he⟩ := G1FiniteChainLedgerAux.branch_real_mem M τ w y
      n h ell p m b hb
    change ModularCluster.branchPoint M k (τ : ℂ) b = (x : ℂ) at he
    rw [he] at hd
    have hdist : |x - r| ≤ ρ := by
      simpa only [Complex.dist_eq, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hd
    exact he.trans (congrArg Complex.ofReal (hiso x hx hdist))
  obtain ⟨A, g, hg, hfg, hcircle⟩ := ModularCluster.circleContribution_principalPart
    M hM k (τ : ℂ) (r : ℂ) hτ ρ hρ hbranches
  refine ⟨A, g, hg, ?_, ?_⟩
  · intro z hz hne
    rw [G1Pinch.g1RatioKernel_eq_kernel]
    exact hfg z hz hne
  · have hkernel : g1RatioKernel M τ w y n h ell p m =
        fun z => ModularCluster.kernel M k z (τ : ℂ) := by
      funext z
      exact G1Pinch.g1RatioKernel_eq_kernel M τ w y n h ell p m z
    rw [hkernel]
    exact hcircle

/-- Deleting a correction subtracts its positive CCW contribution. Combined with
circle_isolated_residue this is the exact pole control. [RW26, p. 7, p. 13]. -/
theorem erase_circle_integral (D : G1VerticalChain) (f : ℂ → ℂ) (r : ℝ) (hr : r ∈ D.centers) :
    g1ChainIntegral D f = g1ChainIntegral (eraseCircle D r) f +
      FinitePrincipalParts.circleCCW (r : ℂ) (D.radius r) f := by
  unfold g1ChainIntegral eraseCircle
  simp only
  rw [← Finset.sum_erase_add _ _ hr]
  simp only [FinitePrincipalParts.circleCCW, g1CirclePullback, add_assoc]

#check @G1Separates
#check @g1LeftAssignment
#check @FinitePrincipalParts.rectangle_finite_principal_parts
#check @ModularCluster.exists_local_principalPart
#print baselineJump
#print connectors
#print finite_chain_ledger
#check @finite_zero_assignment

end SICLean.L4.G1FiniteLedger
