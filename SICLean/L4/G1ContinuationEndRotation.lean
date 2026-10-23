import SICLean.L4.G1ContinuationCircles
import SICLean.L4.G1BilateralGeometry
import SICLean.L4.G1ContinuationEndRotationAux
import SICLean.L4.G1ContinuationEndRotationAuxA11
import SICLean.L4.G1ContinuationEndRotationAuxA12

set_option autoImplicit false

/-!
# Successive end rotations, with actual connector integrals

The two seed integral comparisons are `single_seed_end_rotation` and
`ratio_seed_end_rotation`, together with their concrete crossings and separation conditions. Angles
include their endpoints. The full strict w,y window does not imply decay throughout a fixed angular
band. We prove the angular margins on the initial box and near real targets, rotate there, and
transport vertical ratio ends afterwards. The single lower end always keeps its bend at nonreal τ.

[RW26, pp. 28--29, p. 29].
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1Continuation

open G1ContinuationEndRotationAux

def rotation (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

def endArcPoint (a : ℂ) (R θ : ℝ) : ℂ := a + (R : ℂ) * rotation θ

def endArcPullback (f : ℂ → ℂ) (a : ℂ) (R θ : ℝ) : ℂ :=
  f (endArcPoint a R θ) * (Complex.I * (endArcPoint a R θ - a))

def endArcIntegral (f : ℂ → ℂ) (a : ℂ) (R α β : ℝ) : ℂ :=
  ∫ θ : ℝ in α..β, endArcPullback f a R θ

def upperBand (M : SL(2, ℤ)) (h ell : ℤ) (ψ : ℝ) (x : Parameters) : Prop :=
  ∀ θ ∈ Icc (0 : ℝ) ψ,
    0 < (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 * rotation θ).re

def lowerBand (M : SL(2, ℤ)) (h ell p : ℤ) (ψ : ℝ) (x : Parameters) : Prop :=
  ∀ θ ∈ Icc (0 : ℝ) ψ,
    (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1 * rotation θ).re < 0

/-- Exact reflection constant: μ cancels, and the parity is an integer power. -/
def lowerRatioCoefficient (M : SL(2, ℤ)) (n h ell p m : ℤ) (x : Parameters) : ℂ :=
  (-1 : ℂ) ^ (1 - p) * e (modularReflectionPolynomial M (m + 1) n 0 x.1 -
    modularReflectionPolynomial M (m + p) n x.2.2 x.1 +
    g1Exponent M x.1 x.2.1 0 n h ell m)

/-- A01. Initial-box margins hold on the whole closed angular intervals. [RW26, pp. 28--29]. -/
theorem seed_angular_margins (M : SL(2, ℤ)) (h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ ∈ Icc (0 : ℝ) ψ,
      κ ≤ (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 * rotation θ).re ∧
      κ ≤ -(G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p /
        etaDenom M x.1 * rotation θ).re := by
  obtain ⟨κ, hκ, hm⟩ := isCompact_Icc.exists_forall_le'
    (f := fun θ : ℝ => min
      (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 * rotation θ).re
      (-(G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p /
        etaDenom M x.1 * rotation θ).re))
    (by unfold rotation; fun_prop)
    (by
      intro θ hθ
      exact lt_min_iff.mpr (seed_rotated_positive M h ell p ψ σ ρ δ hc x hx θ hθ))
  exact ⟨κ, hκ, fun θ hθ => le_min_iff.mp (hm θ hθ)⟩

/-- A02. Shrink jointly around a real single target before rotating. [RW26, p. 29]. -/
theorem real_single_angular_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w ψ : ℝ) (h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ (U : Set (ℂ × ℂ)) (κ : ℝ), IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ)) ∈ U ∧
      0 < κ ∧ ∀ u ∈ U, ∀ θ ∈ Icc (0 : ℝ) ψ,
        κ ≤ (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 * rotation θ).re := by
  have hden := real_denom M τ₀
  have hne : etaDenom M (τ₀ : ℂ) ≠ 0 := by simpa [hden] using hT.ne'
  apply open_uniform_margin
    (fun u : ℂ × ℂ => fun θ =>
      (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 * rotation θ).re)
    ((τ₀ : ℂ), (w : ℂ)) (Icc 0 ψ) isCompact_Icc
  · intro θ hθ
    unfold G1RatioTail.complexS rotation etaDenom at *
    fun_prop (disch := assumption)
  · intro θ hθ
    have hcast := (G1RatioTail.real_window_casts M τ₀ w 0 h ell 0).1
    rw [hcast, hden, ← Complex.ofReal_div]
    change 0 < (((g1S M τ₀ w h ell / g1T M τ₀ : ℝ) : ℂ) * UpperWindow.rotation θ).re
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      rotation_re]
    exact mul_pos (div_pos hs hT) (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩)

/-- A03. Same joint shrink for both ratio ends, not the whole complex window. [RW26, pp. 28--29]. -/
theorem real_ratio_angular_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y ψ : ℝ) (h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ (U : Set Parameters) (κ : ℝ),
      IsOpen U ∧ ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) ∈ U ∧ 0 < κ ∧
      ∀ x ∈ U, ∀ θ ∈ Icc (0 : ℝ) ψ,
        κ ≤ (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 * rotation θ).re ∧
        κ ≤ -(G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p /
          etaDenom M x.1 * rotation θ).re := by
  have hden := real_denom M τ₀
  have hne : etaDenom M (τ₀ : ℂ) ≠ 0 := by simpa [hden] using hT.ne'
  obtain ⟨U, κ, hU, hx, hκ, hm⟩ := open_uniform_margin
    (fun x : Parameters => fun θ => min
      (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 * rotation θ).re
      (-(G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p /
        etaDenom M x.1 * rotation θ).re))
    ((τ₀ : ℂ), (w : ℂ), (y : ℂ)) (Icc 0 ψ) isCompact_Icc
    (by
      intro θ hθ
      unfold G1RatioTail.complexL G1RatioTail.complexS rotation etaDenom at *
      fun_prop (disch := assumption))
    (by
      intro θ hθ
      obtain ⟨hs', hL'⟩ := G1RatioTail.real_window_casts M τ₀ w y h ell p
      rw [hs', hL', hden, ← Complex.ofReal_div, ← Complex.ofReal_div]
      have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      simp only [show ∀ θ, (rotation θ).re = Real.cos θ from rotation_re]
      change 0 < min ((g1S M τ₀ w h ell / g1T M τ₀) * Real.cos θ)
        (-((g1L M τ₀ w y h ell p / g1T M τ₀) * Real.cos θ))
      exact lt_min (mul_pos (div_pos hs hT) hc)
        (neg_pos.mpr (mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hL hT) hc)))
  exact ⟨U, κ, hU, hx, hκ, fun x hx θ hθ => le_min_iff.mp (hm x hx θ hθ)⟩

/-- A04. Upper sectors avoid actual pole branches beyond one common radius. [RW26, p. 7]. The
numerator and reciprocal denominator have their correct different loci. -/
theorem upper_end_pole_free (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n p : ℤ) (ψ A : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (K : Set Parameters) (hK : IsCompact K)
    (hτ : ∀ x ∈ K, x.1 ∈ UpperWindow.tauRegion M ψ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x ∈ K, ∀ m : Fin (M 1 0).toNat,
      ∀ a ∈ Metric.closedBall (0 : ℂ) A, ∀ R ≥ R₀,
      ∀ θ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ),
        (endArcPoint a R θ, x.1) ∈ modularPhiHolomorphicDomain M ((m : ℤ) + 1) n ∧
        (endArcPoint a R θ + x.2.2, x.1) ∈
          ModularCluster.inversePhiDomain M ((m : ℤ) + p) n := by
  obtain ⟨Y, hY, hy⟩ := UpperWindow.CompactAux.positive_bound hK
    (f := fun x : Parameters => ‖x.2.2‖) (by fun_prop)
  obtain ⟨C, k, R₀, hC, hk, hR₀, hb⟩ := upper_arc_estimates M hM ψ (|A| + Y)
    hψ hψ' (Prod.fst '' K) (hK.image continuous_fst)
    (by rintro τ ⟨x, hx, rfl⟩; exact hτ x hx)
    (G1BilateralGeometry.indexFamily (components M) n p)
  refine ⟨R₀, hR₀, ?_⟩
  intro x hx m a ha R hR θ hθ
  have ha' : ‖a‖ ≤ A := by simpa using ha
  have han : a ∈ Metric.closedBall (0 : ℂ) (|A| + Y) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith [le_abs_self A]
  have hay : a + x.2.2 ∈ Metric.closedBall (0 : ℂ) (|A| + Y) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add (ha'.trans (le_abs_self A)) (hy x hx))
  have hnum := (hb x.1 (mem_image_of_mem _ hx) _ (index_left M n p m) a han R hR θ hθ).1
  have hden := (hb x.1 (mem_image_of_mem _ hx) _ (index_right M n p m)
    (a + x.2.2) hay R hR θ hθ).1
  refine ⟨⟨hnum.1, hnum.2.1⟩, ?_⟩
  simpa only [ModularCluster.inversePhiDomain, mem_setOf_eq, endArcPoint,
    rotation, UpperWindow.rotation, add_right_comm] using And.intro hden.1 hden.2.2

/-- A05. The Jacobian contributes R: this bounds the integral, not only f. [RW26, pp. 28--29]. -/
theorem upper_connector_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ A : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (K : Set Parameters) (hK : IsCompact K)
    (hτ : ∀ x ∈ K, x.1 ∈ UpperWindow.tauRegion M ψ)
    (hband : ∀ x ∈ K, upperBand M h ell ψ x) :
    ∃ C κ R₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R₀ ∧
      ∀ x ∈ K, ∀ m : Fin (M 1 0).toNat, ∀ a ∈ Metric.closedBall (0 : ℂ) A,
      ∀ R ≥ R₀,
        ‖endArcIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell x.1 x.2.1)
          a R (Real.pi / 2) (Real.pi / 2 + ψ)‖ ≤ C * R * Real.exp (-κ * R) ∧
        ‖endArcIntegral (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
          a R (Real.pi / 2) (Real.pi / 2 + ψ)‖ ≤ C * R * Real.exp (-κ * R) := by
  obtain ⟨Y, hY, hy⟩ := UpperWindow.CompactAux.positive_bound hK
    (f := fun x : Parameters => ‖x.2.2‖) (by fun_prop)
  have hdom (x : Parameters) (hx : x ∈ K) : etaDenom M x.1 ≠ 0 :=
    (UpperWindow.tauRegion_properties M hM ψ hψ' x.1 (hτ x hx)).2.2.2.1
  obtain ⟨D, k, R₀, hD, hk, hR₀, hphi⟩ := upper_arc_estimates M hM ψ (|A| + Y)
    hψ hψ' (Prod.fst '' K) (hK.image continuous_fst)
    (by rintro τ ⟨x, hx, rfl⟩; exact hτ x hx)
    (G1BilateralGeometry.indexFamily (components M) n p)
  obtain ⟨μ, hμ, hμb⟩ := (hK.prod isCompact_Icc).exists_forall_le'
    (f := fun q : Parameters × ℝ =>
      (G1RatioTail.complexS M q.1.1 q.1.2.1 h ell / etaDenom M q.1.1 * rotation q.2).re)
    (by
      intro q hq
      have hT := hdom q.1 hq.1
      apply ContinuousAt.continuousWithinAt
      unfold G1RatioTail.complexS etaDenom rotation at *
      fun_prop (disch := assumption))
    (fun q hq => hband q.1 hq.1 q.2 hq.2)
  obtain ⟨B, hB, hbase⟩ := G1BilateralRatioTailsAux.finite_compact_bound (components M)
    (K ×ˢ Metric.closedBall (0 : ℂ) A) (hK.prod (isCompact_closedBall _ _))
    (fun (m : ℤ) (q : Parameters × ℂ) => e (g1Exponent M q.1.1 q.1.2.1 q.2 n h ell m))
    (by
      intro m hm q hq
      have hT := hdom q.1 hq.1
      apply ContinuousAt.continuousWithinAt
      unfold e g1Exponent etaMobius etaDenom at *
      fun_prop (disch := assumption))
  let κ := 2 * Real.pi * μ
  let P := (D + 1) ^ 2
  refine ⟨ψ * P * B, κ, R₀, by dsimp [P]; positivity, by dsimp [κ]; positivity, hR₀, ?_⟩
  intro x hx m a ha R hR
  have hR0 : 0 ≤ R := (hR₀.trans_le hR).le
  have ha' : ‖a‖ ≤ A := by simpa using ha
  have han : a ∈ Metric.closedBall (0 : ℂ) (|A| + Y) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith [le_abs_self A]
  have hay : a + x.2.2 ∈ Metric.closedBall (0 : ℂ) (|A| + Y) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add (ha'.trans (le_abs_self A)) (hy x hx))
  have hker (θ : ℝ) (hθ : θ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ)) :
      ‖UpperWindow.singleKernel M (m : ℤ) n h ell x.1 x.2.1 (endArcPoint a R θ)‖ ≤
        P * B * Real.exp (-κ * R) ∧
      ‖UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2 (endArcPoint a R θ)‖ ≤
        P * B * Real.exp (-κ * R) := by
    have hnum := hphi x.1 (mem_image_of_mem _ hx) _ (index_left M n p m) a han R hR θ hθ
    have hden := hphi x.1 (mem_image_of_mem _ hx) _ (index_right M n p m)
      (a + x.2.2) hay R hR θ hθ
    have hphase : ‖e (g1Exponent M x.1 x.2.1 (endArcPoint a R θ) n h ell (m : ℤ))‖ ≤
        B * Real.exp (-κ * R) := by
      have heq : g1Exponent M x.1 x.2.1 (endArcPoint a R θ) n h ell (m : ℤ) =
          g1Exponent M x.1 x.2.1 a n h ell (m : ℤ) +
            G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 *
              ((R : ℂ) * rotation θ) := by
        rw [G1RatioTail.exponent_affine M x.1 x.2.1 _ n h ell (m : ℤ) (hdom x hx),
          G1RatioTail.exponent_affine M x.1 x.2.1 a n h ell (m : ℤ) (hdom x hx)]
        unfold endArcPoint
        ring
      rw [heq, G1BilateralRatioTailsAux.e_add, norm_mul,
        G1BilateralRatioTailsAux.norm_e (G1RatioTail.complexS M x.1 x.2.1 h ell /
          etaDenom M x.1 * ((R : ℂ) * rotation θ))]
      have hi : (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 *
          ((R : ℂ) * rotation θ)).im = R *
          (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 *
            rotation (θ - Real.pi / 2)).re := by
        rw [mul_left_comm _ (R : ℂ), Complex.mul_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        exact congrArg (fun t => R * t) (upper_rotated_im _ θ)
      rw [hi]
      have hm := hμb (x, θ - Real.pi / 2) ⟨hx, by
        constructor <;> linarith [hθ.1, hθ.2]⟩
      apply mul_le_mul (hbase (m : ℤ) (component_mem M m) (x, a) ⟨hx, ha⟩)
        (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hB.le
      dsimp [κ]
      nlinarith [mul_le_mul_of_nonneg_right hm hR0, Real.pi_pos]
    have hD₁ : D ≤ P := by dsimp [P]; nlinarith
    have hD₂ : D * D ≤ P := by dsimp [P]; nlinarith
    have hn : ‖modularPhi M ((m : ℤ) + 1) n (endArcPoint a R θ) x.1‖ ≤ D := hnum.2.2.1
    have hd : ‖(modularPhi M ((m : ℤ) + p) n (endArcPoint a R θ + x.2.2) x.1)⁻¹‖ ≤ D := by
      simpa only [endArcPoint, rotation, UpperWindow.rotation, add_right_comm] using hden.2.2.2
    constructor
    · change ‖modularPhi M ((m : ℤ) + 1) n (endArcPoint a R θ) x.1 *
        e (g1Exponent M x.1 x.2.1 (endArcPoint a R θ) n h ell (m : ℤ))‖ ≤ _
      rw [norm_mul]
      exact (mul_le_mul (hn.trans hD₁) hphase (norm_nonneg _) (by dsimp [P]; positivity)).trans_eq (by ring)
    · change ‖(modularPhi M ((m : ℤ) + 1) n (endArcPoint a R θ) x.1 /
          modularPhi M ((m : ℤ) + p) n (endArcPoint a R θ + x.2.2) x.1) *
        e (g1Exponent M x.1 x.2.1 (endArcPoint a R θ) n h ell (m : ℤ))‖ ≤ _
      rw [div_eq_mul_inv, norm_mul, norm_mul]
      exact (mul_le_mul ((mul_le_mul hn hd (norm_nonneg _) hD.le).trans hD₂)
        hphase (norm_nonneg _) (by dsimp [P]; positivity)).trans_eq (by ring)
  have harc (f : ℂ → ℂ)
      (hf : ∀ θ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ),
        ‖f (endArcPoint a R θ)‖ ≤ P * B * Real.exp (-κ * R)) :
      ‖endArcIntegral f a R (Real.pi / 2) (Real.pi / 2 + ψ)‖ ≤
        (ψ * P * B) * R * Real.exp (-κ * R) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := Real.pi / 2) (b := Real.pi / 2 + ψ) (f := endArcPullback f a R)
      (C := R * (P * B * Real.exp (-κ * R))) (by
        intro θ hθ
        rw [uIoc_of_le (by linarith : Real.pi / 2 ≤ Real.pi / 2 + ψ)] at hθ
        have hp : ‖endArcPullback f a R θ‖ = R * ‖f (endArcPoint a R θ)‖ := by
          simp [endArcPullback, endArcPoint, rotation, norm_mul,
            Complex.norm_exp, abs_of_nonneg hR0, mul_comm]
        rw [hp]
        exact mul_le_mul_of_nonneg_left (hf θ ⟨hθ.1.le, hθ.2⟩) hR0)
    simpa only [endArcIntegral, add_sub_cancel_left, abs_of_pos hψ, mul_assoc,
      mul_left_comm, mul_comm] using hb
  exact ⟨harc _ (fun θ hθ => (hker θ hθ).1), harc _ (fun θ hθ => (hker θ hθ).2)⟩

/-- A06. Every upper connector disappears along real radii, successively. [RW26, pp. 28--29]. -/
theorem upper_connectors_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hτ : x.1 ∈ UpperWindow.tauRegion M ψ)
    (hband : upperBand M h ell ψ x) (a : ℂ) (m : Fin (M 1 0).toNat) :
    Tendsto (fun R : ℝ => endArcIntegral
      (UpperWindow.singleKernel M (m : ℤ) n h ell x.1 x.2.1)
      a R (Real.pi / 2) (Real.pi / 2 + ψ)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ => endArcIntegral
      (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
      a R (Real.pi / 2) (Real.pi / 2 + ψ)) atTop (𝓝 0) := by
  obtain ⟨C, κ, R₀, hC, hκ, hR₀, hb⟩ := upper_connector_bound M hM n h ell p ψ ‖a‖
    hψ hψ' {x} isCompact_singleton (by simpa only [mem_singleton_iff, forall_eq])
      (by simpa only [mem_singleton_iff, forall_eq])
  have ha : a ∈ Metric.closedBall (0 : ℂ) ‖a‖ := by simp
  have hz : Tendsto (fun R : ℝ => C * R * Real.exp (-κ * R)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_assoc, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 κ hκ).const_mul C
  constructor
  · apply squeeze_zero_norm' (a := fun R : ℝ => C * R * Real.exp (-κ * R)) _ hz
    filter_upwards [eventually_ge_atTop R₀] with R hR
    exact (hb x (mem_singleton x) m a ha R hR).1
  · apply squeeze_zero_norm' (a := fun R : ℝ => C * R * Real.exp (-κ * R)) _ hz
    filter_upwards [eventually_ge_atTop R₀] with R hR
    exact (hb x (mem_singleton x) m a ha R hR).2

/-- A07. Explicit nonzero analytic reflection constant, no unspecified C_m. [RW26, p. 6, p. 7]. -/
theorem lower_coefficient_analytic_nonzero (M : SL(2, ℤ)) (n h ell p m : ℤ) :
    AnalyticOnNhd ℂ (lowerRatioCoefficient M n h ell p m)
      {x : Parameters | x.1 ∈ modularPhiDomain M} ∧
    (∀ x : Parameters, lowerRatioCoefficient M n h ell p m x ≠ 0) ∧
    (∀ (x : Parameters) (z : ℂ), etaDenom M x.1 ≠ 0 →
      modularReflectionPolynomial M (m + 1) n z x.1 -
        modularReflectionPolynomial M (m + p) n (z + x.2.2) x.1 +
        g1Exponent M x.1 x.2.1 z n h ell m =
          G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1 * z +
          modularReflectionPolynomial M (m + 1) n 0 x.1 -
          modularReflectionPolynomial M (m + p) n x.2.2 x.1 +
          g1Exponent M x.1 x.2.1 0 n h ell m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hT := etaDenom_ne_zero_of_mem M hx
    have ht : AnalyticAt ℂ (fun q : Parameters => q.1) x := analyticAt_fst
    have hw : AnalyticAt ℂ (fun q : Parameters => q.2.1) x :=
      analyticAt_fst.comp analyticAt_snd
    have hy : AnalyticAt ℂ (fun q : Parameters => q.2.2) x :=
      analyticAt_snd.comp analyticAt_snd
    have hd : AnalyticAt ℂ (fun q : Parameters => etaDenom M q.1) x :=
      (analyticAt_const.mul ht).add analyticAt_const
    have hm : AnalyticAt ℂ (fun q : Parameters => etaMobius M q.1) x :=
      ((analyticAt_const.mul ht).add analyticAt_const).div hd hT
    have hP (r : ℤ) (f : Parameters → ℂ) (hf : AnalyticAt ℂ f x) :
        AnalyticAt ℂ (fun q : Parameters => modularReflectionPolynomial M r n (f q) q.1) x := by
      unfold modularReflectionPolynomial
      exact analyticAt_const.mul
        (((((analyticAt_const.mul (hf.pow 2)).div hd hT).add
          ((analyticAt_const.sub (analyticAt_const.div hd hT)).mul hf)).add
            (analyticAt_const.mul ht)).sub (analyticAt_const.mul hm))
    have hE : AnalyticAt ℂ
        (fun q : Parameters => g1Exponent M q.1 q.2.1 0 n h ell m) x := by
      unfold g1Exponent
      exact (((((analyticAt_const.sub analyticAt_const).add
        (hd.mul analyticAt_const)).mul hw).div hd hT).add
          (analyticAt_const.mul (analyticAt_const.add (analyticAt_const.mul ht)))).add
            (analyticAt_const.mul ((analyticAt_const.div hd hT).add
              (analyticAt_const.mul hm)))
    unfold lowerRatioCoefficient e
    exact analyticAt_const.mul ((analyticAt_const.mul
      (((hP (m + 1) (fun _ => 0) analyticAt_const).sub
        (hP (m + p) (fun q => q.2.2) hy)).add hE)).cexp')
  · intro x
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (e_ne_zero _)
  · intro x z hT
    simpa only [sub_eq_add_neg, add_assoc] using G1BilateralRatioTailsAux.lower_phase_affine
      M x.1 x.2.1 x.2.2 z n h ell p m hT

/-- A08. Exact normalized asymptotic, uniform on compact moving parameters. [RW26, p. 7]. -/
theorem lower_ratio_uniform_asymptotic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ A : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (K : Set Parameters) (hK : IsCompact K)
    (hτ : ∀ x ∈ K, x.1 ∈ UpperWindow.tauRegion M ψ) :
    ∃ C κ R₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R₀ ∧
      ∀ x ∈ K, ∀ m : Fin (M 1 0).toNat, ∀ a ∈ Metric.closedBall (0 : ℂ) A,
      ∀ R ≥ R₀, ∀ θ ∈ Icc (-Real.pi / 2) (-Real.pi / 2 + ψ),
        let z := endArcPoint a R θ
        (z, x.1) ∈ modularPhiHolomorphicDomain M ((m : ℤ) + 1) n ∧
        (z + x.2.2, x.1) ∈ ModularCluster.inversePhiDomain M ((m : ℤ) + p) n ∧
        ‖UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2 z /
          (lowerRatioCoefficient M n h ell p (m : ℤ) x *
            e (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1 * z)) - 1‖ ≤
          C * Real.exp (-κ * R) := by
  obtain ⟨Y, hY, hy⟩ := UpperWindow.CompactAux.positive_bound hK
    (f := fun x : Parameters => ‖x.2.2‖) (by fun_prop)
  let F := G1BilateralGeometry.indexFamily (components M) n p
  obtain ⟨D, k, R₀, hD, hk, hR₀, hb⟩ := upper_arc_estimates M hM ψ (|A| + Y)
    hψ hψ' (Prod.fst '' K) (hK.image continuous_fst)
    (by rintro τ ⟨x, hx, rfl⟩; exact hτ x hx)
    (F.image fun i => (1 - i.1, 1 - i.2))
  refine ⟨2 * (D + 2) * D, k, R₀, by positivity, hk, hR₀, ?_⟩
  intro x hx m a ha R hR θ hθ
  let z := endArcPoint a R θ
  have ha' : ‖a‖ ≤ A := by simpa using ha
  have han : -a ∈ Metric.closedBall (0 : ℂ) (|A| + Y) := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_neg]
    linarith [le_abs_self A]
  have hay : -(a + x.2.2) ∈ Metric.closedBall (0 : ℂ) (|A| + Y) := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_neg]
    exact (norm_add_le _ _).trans (add_le_add (ha'.trans (le_abs_self A)) (hy x hx))
  have hθ' : θ + Real.pi ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ) := by
    constructor <;> linarith [hθ.1, hθ.2]
  have hz' : -z = -a + (R : ℂ) * UpperWindow.rotation (θ + Real.pi) := by
    rw [rotation_pi]
    change -(a + (R : ℂ) * rotation θ) = _
    change -(a + (R : ℂ) * UpperWindow.rotation θ) = _
    ring
  have hzy' : -(z + x.2.2) = -(a + x.2.2) +
      (R : ℂ) * UpperWindow.rotation (θ + Real.pi) := by
    rw [rotation_pi]
    change -(a + (R : ℂ) * UpperWindow.rotation θ + x.2.2) = _
    ring
  have h₁ := hb x.1 (mem_image_of_mem _ hx) _
    (Finset.mem_image.mpr ⟨_, index_left M n p m, rfl⟩) (-a) han R hR (θ + Real.pi) hθ'
  have h₂ := hb x.1 (mem_image_of_mem _ hx) _
    (Finset.mem_image.mpr ⟨_, index_right M n p m, rfl⟩)
    (-(a + x.2.2)) hay R hR (θ + Real.pi) hθ'
  rw [← hz'] at h₁
  rw [← hzy'] at h₂
  have hn := reflected_unit M ((m : ℤ) + 1) n z x.1 h₁.1
  have hd := reflected_unit M ((m : ℤ) + p) n (z + x.2.2) x.1 h₂.1
  refine ⟨⟨hn.1, hn.2.1⟩, ⟨hd.1, hd.2.2⟩, ?_⟩
  have he := lower_ratio_normalized M hM n h ell p (m : ℤ) x.1 x.2.1 x.2.2 z h₁.1 h₂.1
  rw [lower_factor_affine M hM n h ell p (m : ℤ) x.1 x.2.1 x.2.2 z
    (etaDenom_ne_zero_of_mem M hn.1)] at he
  change UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2 z /
    (lowerRatioCoefficient M n h ell p (m : ℤ) x *
      e (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1 * z)) = _ at he
  rw [he, div_eq_mul_inv]
  have hδ : Real.exp (-k * R) ≤ 1 := Real.exp_le_one_iff.mpr
    (by nlinarith [hR₀.trans_le hR])
  have hpair := ModularSector.product_error_pair
    (modularPhi M (1 - ((m : ℤ) + p)) (1 - n) (-(z + x.2.2)) x.1)
    ((modularPhi M (1 - ((m : ℤ) + 1)) (1 - n) (-z) x.1)⁻¹)
    D (Real.exp (-k * R)) hD.le (Real.exp_pos _).le hδ h₂.2.1
    (by simpa only [ModularSector.upperError, inv_inv, add_comm] using h₁.2.1)
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans hpair

/-- A09. After the upper end, rotate the ratio lower end; R exp(-κR) again. [RW26, pp. 28--29]. -/
theorem lower_ratio_connector_bound_limit (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ A : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (K : Set Parameters) (hK : IsCompact K)
    (hτ : ∀ x ∈ K, x.1 ∈ UpperWindow.tauRegion M ψ)
    (hband : ∀ x ∈ K, lowerBand M h ell p ψ x) :
    ∃ C κ R₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R₀ ∧
      ∀ x ∈ K, ∀ m : Fin (M 1 0).toNat, ∀ a ∈ Metric.closedBall (0 : ℂ) A,
        (∀ R ≥ R₀, ‖endArcIntegral
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
          a R (-Real.pi / 2) (-Real.pi / 2 + ψ)‖ ≤ C * R * Real.exp (-κ * R)) ∧
        Tendsto (fun R : ℝ => endArcIntegral
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
          a R (-Real.pi / 2) (-Real.pi / 2 + ψ)) atTop (𝓝 0) := by
  have hdom (x : Parameters) (hx : x ∈ K) : x.1 ∈ modularPhiDomain M :=
    (UpperWindow.tauRegion_properties M hM ψ hψ' x.1 (hτ x hx)).1
  obtain ⟨D, k, R₀, hD, hk, hR₀, hasym⟩ := lower_ratio_uniform_asymptotic
    M hM n h ell p ψ A hψ hψ' K hK hτ
  obtain ⟨μ, hμ, hμb⟩ := (hK.prod isCompact_Icc).exists_forall_le'
    (f := fun q : Parameters × ℝ =>
      -(G1RatioTail.complexL M q.1.1 q.1.2.1 q.1.2.2 h ell p /
        etaDenom M q.1.1 * rotation q.2).re)
    (by
      intro q hq
      have hT := etaDenom_ne_zero_of_mem M (hdom q.1 hq.1)
      apply ContinuousAt.continuousWithinAt
      unfold G1RatioTail.complexL G1RatioTail.complexS etaDenom rotation at *
      fun_prop (disch := assumption))
    (fun q hq => neg_pos.mpr (hband q.1 hq.1 q.2 hq.2))
  obtain ⟨B, hB, hbase⟩ := G1BilateralRatioTailsAux.finite_compact_bound (components M)
    (K ×ˢ Metric.closedBall (0 : ℂ) A) (hK.prod (isCompact_closedBall _ _))
    (fun (m : ℤ) (q : Parameters × ℂ) => lowerRatioCoefficient M n h ell p m q.1 *
      e (G1RatioTail.complexL M q.1.1 q.1.2.1 q.1.2.2 h ell p / etaDenom M q.1.1 * q.2))
    (by
      intro m hm q hq
      have hc := ((lower_coefficient_analytic_nonzero M n h ell p m).1 q.1
        (hdom q.1 hq.1)).continuousAt.comp continuousAt_fst
      have hT := etaDenom_ne_zero_of_mem M (hdom q.1 hq.1)
      apply ContinuousAt.continuousWithinAt
      apply hc.mul
      unfold G1RatioTail.complexL G1RatioTail.complexS etaDenom e at *
      fun_prop (disch := assumption))
  let κ := 2 * Real.pi * μ
  let C := ψ * (D + 1) * B
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (x : Parameters) (hx : x ∈ K) (m : Fin (M 1 0).toNat)
      (a : ℂ) (ha : a ∈ Metric.closedBall (0 : ℂ) A) (R : ℝ) (hR : R₀ ≤ R) :
      ‖endArcIntegral (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
        a R (-Real.pi / 2) (-Real.pi / 2 + ψ)‖ ≤ C * R * Real.exp (-κ * R) := by
    have hR0 : 0 ≤ R := (hR₀.trans_le hR).le
    have hker (θ : ℝ) (hθ : θ ∈ Icc (-Real.pi / 2) (-Real.pi / 2 + ψ)) :
        ‖UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2
          (endArcPoint a R θ)‖ ≤ (D + 1) * B * Real.exp (-κ * R) := by
      let S := G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1
      let z := endArcPoint a R θ
      let den := lowerRatioCoefficient M n h ell p (m : ℤ) x * e (S * z)
      have hn : den ≠ 0 := mul_ne_zero
        ((lower_coefficient_analytic_nonzero M n h ell p (m : ℤ)).2.1 x) (e_ne_zero _)
      have hq := (hasym x hx m a ha R hR θ hθ).2.2
      have hq' : ‖UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2 z / den‖ ≤ D + 1 := by
        have he : D * Real.exp (-k * R) ≤ D := by
          exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith)) hD.le).trans_eq (mul_one _)
        have ht := norm_le_norm_sub_add
          (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2 z / den) 1
        simp only [norm_one] at ht
        linarith [hq.trans he]
      have hd : ‖den‖ ≤ B * Real.exp (-κ * R) := by
        have heq : S * z = S * a + (R : ℂ) * (S * rotation θ) := by
          dsimp [z, endArcPoint]
          ring
        dsimp only [den]
        rw [heq, G1BilateralRatioTailsAux.e_add, ← mul_assoc, norm_mul,
          G1BilateralRatioTailsAux.norm_e]
        have hi : ((R : ℂ) * (S * rotation θ)).im =
            -R * (S * rotation (θ + Real.pi / 2)).re := by
          rw [Complex.mul_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          simpa only [rotation, UpperWindow.rotation, mul_neg, neg_mul] using
            congrArg (fun t => R * t) (lower_rotated_im S θ)
        rw [hi]
        apply mul_le_mul (hbase (m : ℤ) (component_mem M m) (x, a) ⟨hx, ha⟩)
          (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hB.le
        have hm := hμb (x, θ + Real.pi / 2) ⟨hx, by
          constructor <;> linarith [hθ.1, hθ.2]⟩
        dsimp [κ]
        nlinarith [mul_le_mul_of_nonneg_right hm hR0, Real.pi_pos]
      calc
        _ = ‖UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2 z / den‖ * ‖den‖ := by
          rw [← norm_mul, div_mul_cancel₀ _ hn]
        _ ≤ (D + 1) * (B * Real.exp (-κ * R)) :=
          mul_le_mul hq' hd (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi / 2) (b := -Real.pi / 2 + ψ)
      (f := endArcPullback (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2) a R)
      (C := R * ((D + 1) * B * Real.exp (-κ * R))) (by
        intro θ hθ
        rw [uIoc_of_le (by linarith : -Real.pi / 2 ≤ -Real.pi / 2 + ψ)] at hθ
        have hp : ∀ f : ℂ → ℂ, ‖endArcPullback f a R θ‖ = R * ‖f (endArcPoint a R θ)‖ := by
          intro f
          simp [endArcPullback, endArcPoint, rotation, norm_mul,
            Complex.norm_exp, abs_of_nonneg hR0, mul_comm]
        rw [hp]
        exact mul_le_mul_of_nonneg_left (hker θ ⟨hθ.1.le, hθ.2⟩) hR0)
    simpa only [endArcIntegral, add_sub_cancel_left, abs_of_pos hψ, C, mul_assoc,
      mul_left_comm, mul_comm] using hb
  refine ⟨C, κ, R₀, hC, hκ, hR₀, ?_⟩
  intro x hx m a ha
  refine ⟨hbound x hx m a ha, ?_⟩
  apply squeeze_zero_norm' (a := fun R : ℝ => C * R * Real.exp (-κ * R))
  · filter_upwards [eventually_ge_atTop R₀] with R hR
    exact hbound x hx m a ha R hR
  · simpa only [Real.rpow_one, mul_assoc, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 κ hκ).const_mul C

/-- A10. Keep the tilted single lower tail, with a common Gaussian bound. Bounded translations cover
the finite connecting segments as well. [RW26, pp. 28--29]. -/
theorem single_lower_gaussian_translations (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ A : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hτ : ∀ u ∈ K, u.1 ∈ UpperWindow.tauRegion M ψ) :
    ∃ C a B R₀ : ℝ, 0 < C ∧ 0 < a ∧ 0 < B ∧ 0 < R₀ ∧
      ∀ u ∈ K, a ≤ G1BilateralGeometry.gaussianCoefficient M u.1 ψ ∧
      ∀ m : Fin (M 1 0).toNat, ∀ z₀ ∈ Metric.closedBall (0 : ℂ) A,
      ∀ R ≥ R₀, ‖UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2
        (z₀ + (R : ℂ) * g1LowerDirection ψ)‖ ≤
          C * Real.exp (-a * R ^ 2 + B * R) := by
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  have ht (u : ℂ × ℂ) (hu : u ∈ K) :=
    UpperWindow.tauRegion_properties M hM ψ hψ' u.1 (hτ u hu)
  have hden (u : ℂ × ℂ) (hu : u ∈ K) : etaDenom M u.1 ≠ 0 := (ht u hu).2.2.2.1
  obtain ⟨a, ha, hgauss⟩ := hK.exists_forall_le'
    (f := fun u : ℂ × ℂ => G1BilateralGeometry.gaussianCoefficient M u.1 ψ)
    (by
      intro u hu
      have hd : ContinuousAt (fun u : ℂ × ℂ => etaDenom M u.1) u := by
        unfold etaDenom
        fun_prop
      have harg := (Complex.continuousAt_arg (Or.inl (ht u hu).2.2.1)).comp
        (f := fun u : ℂ × ℂ => etaDenom M u.1) hd
      have hn := norm_ne_zero_iff.mpr (hden u hu)
      exact ((continuousAt_const.div hd.norm hn).mul
        (Real.continuous_sin.continuousAt.comp (continuousAt_const.sub harg))).continuousWithinAt)
    (by
      intro u hu
      unfold G1BilateralGeometry.gaussianCoefficient
      apply mul_pos (div_pos (mul_pos Real.pi_pos hc) (norm_pos_iff.mpr (hden u hu)))
      exact Real.sin_pos_of_pos_of_lt_pi
        (by linarith [(hτ u hu).2.2])
        (by linarith [(hτ u hu).2.1, Real.pi_pos]))
  let P : Set ((ℂ × ℂ) × ℂ) := K ×ˢ Metric.closedBall (0 : ℂ) A
  have hP : IsCompact P := hK.prod (isCompact_closedBall _ _)
  obtain ⟨B, hB, hlin⟩ := G1BilateralRatioTailsAux.finite_compact_bound (components M) P hP
    (fun (m : ℤ) (q : (ℂ × ℂ) × ℂ) => 2 * (Real.pi : ℂ) * Complex.I *
      lowerLinearAt M q.1.1 q.1.2 q.2 ψ n h ell m)
    (by
      intro m hm q hq
      have hT := hden q.1 hq.1
      apply ContinuousAt.continuousWithinAt
      unfold lowerLinearAt G1RatioTail.complexS etaDenom at *
      fun_prop (disch := simp_all))
  obtain ⟨D, hD, hconst⟩ := G1BilateralRatioTailsAux.finite_compact_bound (components M) P hP
    (fun (m : ℤ) (q : (ℂ × ℂ) × ℂ) => 2 * (Real.pi : ℂ) * Complex.I *
      lowerConstantAt M q.1.1 q.1.2 q.2 n h ell m)
    (by
      intro m hm q hq
      have hT := hden q.1 hq.1
      apply ContinuousAt.continuousWithinAt
      unfold lowerConstantAt modularReflectionPolynomial g1Exponent etaMobius etaDenom at *
      fun_prop (disch := assumption))
  obtain ⟨Dφ, k, R₀, hDφ, hk, hR₀, hphi⟩ := upper_arc_estimates M hM ψ A hψ hψ'
    (Prod.fst '' K) (hK.image continuous_fst)
    (by rintro τ ⟨u, hu, rfl⟩; exact hτ u hu)
    ((components M).image fun m => (1 - (m + 1), 1 - n))
  let C := Dφ * ‖(etaMultiplier M) ^ (-2 : ℤ)‖ * Real.exp D
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos hDφ (norm_pos_iff.mpr (zpow_ne_zero _ (etaMultiplier_ne_zero M hM))))
      (Real.exp_pos _)
  refine ⟨C, a, B, R₀, hC, ha, hB, hR₀, ?_⟩
  intro u hu
  refine ⟨hgauss u hu, ?_⟩
  intro m z₀ hz₀ R hR
  have hR0 : 0 ≤ R := (hR₀.trans_le hR).le
  let z := z₀ + (R : ℂ) * g1LowerDirection ψ
  have hz' : -z = -z₀ + (R : ℂ) * UpperWindow.rotation (Real.pi / 2 + ψ) := by
    rw [← reflected_lower_direction]
    dsimp [z]
    ring
  have hp := hphi u.1 (mem_image_of_mem _ hu) _
    (Finset.mem_image.mpr ⟨(m : ℤ), component_mem M m, rfl⟩)
    (-z₀) (by simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hz₀)
    R hR (Real.pi / 2 + ψ) ⟨by linarith, le_rfl⟩
  rw [← hz'] at hp
  have href := point_reflection M hM ((m : ℤ) + 1) n z u.1
    (reflected_unit M _ _ _ _ hp.1) hp.1
  have hnorm : ‖UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2 z‖ =
      ‖(modularPhi M (1 - ((m : ℤ) + 1)) (1 - n) (-z) u.1)⁻¹‖ *
        ‖(etaMultiplier M) ^ (-2 : ℤ)‖ * Real.exp
          ((2 * (Real.pi : ℂ) * Complex.I *
            (modularReflectionPolynomial M ((m : ℤ) + 1) n z u.1 +
              g1Exponent M u.1 u.2 z n h ell (m : ℤ))).re) := by
    change ‖modularPhi M ((m : ℤ) + 1) n z u.1 * e (g1Exponent M u.1 u.2 z n h ell (m : ℤ))‖ = _
    rw [href, div_eq_mul_inv, mul_right_comm, norm_mul,
      G1BilateralSingleTailsAux.norm_reflection_times_e]
    ring
  rw [hnorm]
  have hquad := single_phase_quad M u.1 u.2 z₀ ψ R n h ell (m : ℤ) (hden u hu)
  have hg := G1BilateralGeometry.gaussian_coefficient_exact M u.1 ψ (hden u hu)
  have he : (2 * (Real.pi : ℂ) * Complex.I *
      (modularReflectionPolynomial M ((m : ℤ) + 1) n z u.1 +
        g1Exponent M u.1 u.2 z n h ell (m : ℤ))).re =
      -G1BilateralGeometry.gaussianCoefficient M u.1 ψ * R ^ 2 +
        (2 * (Real.pi : ℂ) * Complex.I * lowerLinearAt M u.1 u.2 z₀ ψ n h ell (m : ℤ)).re * R +
        (2 * (Real.pi : ℂ) * Complex.I * lowerConstantAt M u.1 u.2 z₀ n h ell (m : ℤ)).re := by
    change (2 * (Real.pi : ℂ) * Complex.I *
      (modularReflectionPolynomial M ((m : ℤ) + 1) n
        (z₀ + (R : ℂ) * g1LowerDirection ψ) u.1 +
        g1Exponent M u.1 u.2 (z₀ + (R : ℂ) * g1LowerDirection ψ) n h ell (m : ℤ))).re = _
    rw [hquad]
    have halg (Q L N : ℂ) :
        (2 * (Real.pi : ℂ) * Complex.I * (Q * (R : ℂ) ^ 2 + L * (R : ℂ) + N)).re =
          (2 * (Real.pi : ℂ) * Complex.I * Q).re * R ^ 2 +
          (2 * (Real.pi : ℂ) * Complex.I * L).re * R +
          (2 * (Real.pi : ℂ) * Complex.I * N).re := by
      rw [← Complex.ofReal_pow]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [halg, hg]
  rw [he]
  have hlin' := (Complex.re_le_norm _).trans (hlin (m : ℤ) (component_mem M m) (u, z₀) ⟨hu, hz₀⟩)
  have hconst' := (Complex.re_le_norm _).trans (hconst (m : ℤ) (component_mem M m) (u, z₀) ⟨hu, hz₀⟩)
  have hexp : -G1BilateralGeometry.gaussianCoefficient M u.1 ψ * R ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I * lowerLinearAt M u.1 u.2 z₀ ψ n h ell (m : ℤ)).re * R +
      (2 * (Real.pi : ℂ) * Complex.I * lowerConstantAt M u.1 u.2 z₀ n h ell (m : ℤ)).re ≤
        D + (-a * R ^ 2 + B * R) := by
    nlinarith [mul_le_mul_of_nonneg_right hlin' hR0,
      mul_le_mul_of_nonneg_right (hgauss u hu) (sq_nonneg R)]
  calc
    _ ≤ Dφ * ‖(etaMultiplier M) ^ (-2 : ℤ)‖ * Real.exp (D + (-a * R ^ 2 + B * R)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hp.2.2.2 (norm_nonneg _))
        (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [Real.exp_add]; dsimp [C]; ring

lemma a11_single_domain_lift (M : SL(2, ℤ)) (h ell : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (u : ℂ × ℂ)
    (hu : u ∈ UpperIntegralIdentities.singleDomain M h ell ψ σ ρ δ) :
    (u.1, u.2, UpperWindow.centerY M 0 ρ u.1) ∈
      UpperWindow.domain M h ell 0 ψ σ ρ δ := by
  have hTi := (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 u.1 hu.1).2.1
  have hr := (UpperWindow.radius_margins M ψ σ ρ δ hc).1
  have hcoords : UpperWindow.coords (etaDenom M u.1)
      (UpperWindow.height M 0 u.1 (UpperWindow.centerY M 0 ρ u.1)) = (ρ, ρ) := by
    rw [(UpperWindow.center_equations M hc.1 h ell 0 σ ρ u.1).2,
      show (ρ : ℂ) * (etaDenom M u.1 + 1) =
        (ρ : ℂ) * etaDenom M u.1 + (ρ : ℂ) by ring]
    exact UpperWindow.coords_real_combination (etaDenom M u.1) hTi.ne' ρ ρ
  refine ⟨hu.1, hu.2.1, hu.2.2, ?_, ?_⟩ <;>
    simpa only [hcoords, sub_self, abs_zero] using hr

lemma a11_single_differentiable_of_avoids (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w z : ℂ) (m n h ell : ℤ) (hτ : τ ∈ modularPhiDomain M)
    (hz : ∀ K J : ℕ, z ≠ modularPhiPolePoint M (m + 1) n τ K J) :
    DifferentiableAt ℂ (UpperWindow.singleKernel M m n h ell τ w) z := by
  have hempty : modularPhiPoleIndices M (m + 1) n z τ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ hk
    exact hz K J hk.2
  have hp : (z, τ) ∈ modularPhiHolomorphicDomain M (m + 1) n :=
    ⟨hτ, by simp [modularPhiPoleMultiplicity, hempty]⟩
  have ha := (modularPhi_joint_analytic_no_poles M hM (m + 1) n (z, τ) hp).comp
    (f := fun z : ℂ => (z, τ)) (analyticAt_id.prod analyticAt_const)
  have he : AnalyticAt ℂ (fun z : ℂ => e (g1Exponent M τ w z n h ell m)) z := by
    unfold e g1Exponent
    fun_prop
  exact (ha.mul he).differentiableAt

lemma a11_lower_direction_coordinates (ψ : ℝ) :
    (g1LowerDirection ψ).re = Real.sin ψ ∧
      (g1LowerDirection ψ).im = -Real.cos ψ := by
  have hrot := reflected_lower_direction ψ
  constructor
  · have hh := congrArg Complex.re hrot
    simpa [rotation_re, Real.cos_add] using hh
  · have hh := congrArg Complex.im hrot
    have hh' : -(g1LowerDirection ψ).im = Real.cos ψ := by
      simpa [rotation_im, Real.sin_add] using hh
    linarith

lemma a11_seed_shift_inequalities (v : ℂ) (ψ : ℝ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    let b := (seedCrossing v ψ : ℂ) - Complex.I
    b.re ≤ v.re ∧
      (b - v).re * Real.cos ψ + (b - v).im * Real.sin ψ ≤ 0 := by
  have hcos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi hψ.le
    (by linarith [Real.pi_pos])
  have htan : 0 ≤ Real.tan ψ := by rw [Real.tan_eq_sin_div_cos]; positivity
  have htc : Real.tan ψ * Real.cos ψ = Real.sin ψ := by
    rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hcos.ne']
  dsimp only
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, sub_zero]
  dsimp [seedCrossing]
  constructor
  · nlinarith [mul_nonneg (le_max_left (0 : ℝ) (-v.im - 1)) htan]
  · have hh := mul_le_mul_of_nonneg_right (le_max_right (0 : ℝ) (-v.im - 1)) hsin
    calc
      _ = (-v.im - 1) * Real.sin ψ -
          max 0 (-v.im - 1) * (Real.tan ψ * Real.cos ψ) := by ring
      _ ≤ 0 := by rw [htc]; linarith

lemma a11_upper_single_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ A : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hτ : u.1 ∈ UpperWindow.tauRegion M ψ)
    (hband : ∀ θ ∈ Icc (0 : ℝ) ψ,
      0 < (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 * rotation θ).re) :
    ∃ C k R₀ : ℝ, 0 < C ∧ 0 < k ∧ 0 < R₀ ∧
      ∀ m : Fin (M 1 0).toNat, ∀ a ∈ Metric.closedBall (0 : ℂ) A,
        ∀ R ≥ R₀, ∀ θ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ),
          ‖UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2
            (a + (R : ℂ) * rotation θ)‖ ≤ C * Real.exp (-k * R) := by
  have hT := (UpperWindow.tauRegion_properties M hM ψ hψ' u.1 hτ).2.2.2.1
  obtain ⟨D, kφ, R₀, hD, hkφ, hR₀, hphi⟩ := upper_arc_estimates M hM ψ A hψ hψ'
    {u.1} isCompact_singleton (by simpa only [singleton_subset_iff] using hτ)
    (G1BilateralGeometry.indexFamily (components M) n 0)
  obtain ⟨μ, hμ, hm⟩ := isCompact_Icc.exists_forall_le'
    (f := fun θ : ℝ =>
      (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 * rotation θ).re)
    (by unfold rotation; fun_prop) hband
  obtain ⟨B, hB, hb⟩ := G1BilateralRatioTailsAux.finite_compact_bound (components M)
    (Metric.closedBall (0 : ℂ) A) (isCompact_closedBall _ _)
    (fun (m : ℤ) (a : ℂ) => e (g1Exponent M u.1 u.2 a n h ell m))
    (by intro m hm; unfold e g1Exponent; fun_prop)
  refine ⟨D * B, 2 * Real.pi * μ, R₀, by positivity, by positivity, hR₀, ?_⟩
  intro m a ha R hR θ hθ
  have hR0 : 0 ≤ R := (hR₀.trans_le hR).le
  have hp := (hphi u.1 (mem_singleton _) _ (index_left M n 0 m) a ha R hR θ hθ).2.2.1
  have heq : g1Exponent M u.1 u.2 (a + (R : ℂ) * rotation θ) n h ell (m : ℤ) =
      g1Exponent M u.1 u.2 a n h ell (m : ℤ) +
        G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 *
          ((R : ℂ) * rotation θ) := by
    rw [G1RatioTail.exponent_affine M u.1 u.2 _ n h ell (m : ℤ) hT,
      G1RatioTail.exponent_affine M u.1 u.2 a n h ell (m : ℤ) hT]
    ring
  have hi : (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 *
      ((R : ℂ) * rotation θ)).im = R *
        (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 *
          rotation (θ - Real.pi / 2)).re := by
    rw [mul_left_comm _ (R : ℂ), Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact congrArg (fun t => R * t) (upper_rotated_im _ θ)
  change ‖modularPhi M ((m : ℤ) + 1) n _ u.1 *
    e (g1Exponent M u.1 u.2 (a + (R : ℂ) * rotation θ) n h ell (m : ℤ))‖ ≤ _
  rw [norm_mul, heq, G1BilateralRatioTailsAux.e_add, norm_mul,
    G1BilateralRatioTailsAux.norm_e (G1RatioTail.complexS M u.1 u.2 h ell /
      etaDenom M u.1 * ((R : ℂ) * rotation θ)), hi]
  have he : -2 * Real.pi * (R *
      (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 *
        rotation (θ - Real.pi / 2)).re) ≤ -(2 * Real.pi * μ) * R := by
    have hμθ := hm (θ - Real.pi / 2) ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    nlinarith [mul_le_mul_of_nonneg_right hμθ hR0, Real.pi_pos]
  calc
    _ ≤ D * (B * Real.exp (-(2 * Real.pi * μ) * R)) :=
      mul_le_mul hp (mul_le_mul (hb (m : ℤ) (component_mem M m) a ha)
        (Real.exp_le_exp.mpr he) (Real.exp_pos _).le hB.le) (by positivity) hD.le
    _ = _ := by ring

lemma a11_seed_strips_differentiable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w v : ℂ) (m n h ell : ℤ) (ψ : ℝ)
    (hτ : τ ∈ modularPhiDomain M) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hp : ∀ K J : ℕ,
      v.re < (modularPhiPolePoint M (m + 1) n τ K J).re ∧
      v.im < (modularPhiPolePoint M (m + 1) n τ K J).im) :
    let b := (seedCrossing v ψ : ℂ) - Complex.I
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t →
      DifferentiableAt ℂ (UpperWindow.singleKernel M m n h ell τ w)
        (v + (s : ℂ) * (b - v) + (t : ℂ) * Complex.I) ∧
      DifferentiableAt ℂ (UpperWindow.singleKernel M m n h ell τ w)
        (v + (s : ℂ) * (b - v) + (t : ℂ) * g1LowerDirection ψ) := by
  let b := (seedCrossing v ψ : ℂ) - Complex.I
  have hshift := a11_seed_shift_inequalities v ψ hψ hψ'
  change b.re ≤ v.re ∧
    (b - v).re * Real.cos ψ + (b - v).im * Real.sin ψ ≤ 0 at hshift
  have hcos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ
    (by linarith [Real.pi_pos])
  dsimp only
  intro s hs t ht
  constructor
  · apply a11_single_differentiable_of_avoids M hM τ w _ m n h ell hτ
    intro K J heq
    have hh := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, zero_mul, mul_zero, sub_zero,
      add_zero] at hh
    have hh' : s * (b.re - v.re) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs.1 (sub_nonpos.mpr hshift.1)
    simp only [b, Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero] at hh'
    linarith [(hp K J).1]
  · apply a11_single_differentiable_of_avoids M hM τ w _ m n h ell hτ
    intro K J heq
    let z := v + (s : ℂ) * (b - v) + (t : ℂ) * g1LowerDirection ψ
    have hside : (z - v).re * Real.cos ψ + (z - v).im * Real.sin ψ =
        s * ((b - v).re * Real.cos ψ + (b - v).im * Real.sin ψ) := by
      dsimp [z]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, add_zero,
        (a11_lower_direction_coordinates ψ).1, (a11_lower_direction_coordinates ψ).2]
      ring
    have hle : (z - v).re * Real.cos ψ + (z - v).im * Real.sin ψ ≤ 0 := by
      rw [hside]
      exact mul_nonpos_of_nonneg_of_nonpos hs.1 hshift.2
    have heq' : z = modularPhiPolePoint M (m + 1) n τ K J := heq
    rw [heq'] at hle
    simp only [Complex.sub_re, Complex.sub_im] at hle
    have hr := mul_pos (sub_pos.mpr (hp K J).1) hcos
    have hi := mul_pos (sub_pos.mpr (hp K J).2) hsin
    linarith

lemma a11_upper_ray_integrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hτ : u.1 ∈ UpperWindow.tauRegion M ψ)
    (hband : ∀ θ ∈ Icc (0 : ℝ) ψ,
      0 < (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 * rotation θ).re)
    (m : Fin (M 1 0).toNat) (a : ℂ) (θ : ℝ)
    (hθ : θ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ))
    (hf : ∀ t : ℝ, 0 ≤ t →
      DifferentiableAt ℂ (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
        (a + (t : ℂ) * rotation θ)) :
    IntegrableOn (UpperContour.rayPullback
      (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2) a (rotation θ)) (Ioi 0) := by
  obtain ⟨C, k, R₀, hC, hk, hR₀, hb⟩ :=
    a11_upper_single_bound M hM n h ell ψ ‖a‖ hψ hψ' u hτ hband
  refine G1ContinuationEndRotationAuxA11.integrableOn_Ioi_of_eventual_exp_bound _ C k ?_ hk ?_
  · intro t ht
    have hp : ContinuousAt (fun t : ℝ => a + (t : ℂ) * rotation θ) t := by fun_prop
    exact (((hf t ht).continuousAt.comp
      (f := fun t : ℝ => a + (t : ℂ) * rotation θ) (x := t) hp).mul_const _).continuousWithinAt
  · refine ⟨R₀, fun R hR => ?_⟩
    simpa [UpperContour.rayPullback, rotation, Complex.norm_exp] using
      hb m a (by simp) R hR θ hθ

lemma a11_lower_ray_integrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hτ : u.1 ∈ UpperWindow.tauRegion M ψ)
    (m : Fin (M 1 0).toNat) (z₀ : ℂ)
    (hf : ∀ t : ℝ, 0 ≤ t →
      DifferentiableAt ℂ (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2)
        (z₀ + (t : ℂ) * g1LowerDirection ψ)) :
    IntegrableOn (UpperContour.rayPullback
      (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2) z₀ (g1LowerDirection ψ))
      (Ioi 0) := by
  obtain ⟨C, a, B, R₀, hC, ha, hB, hR₀, hb⟩ :=
    single_lower_gaussian_translations M hM n h ell ψ ‖z₀‖ hψ hψ' {u}
      isCompact_singleton (by simpa only [mem_singleton_iff, forall_eq] using hτ)
  refine G1ContinuationEndRotationAuxA11.integrableOn_Ioi_of_eventual_exp_bound _
    (C * Real.exp ((B + 1) ^ 2 / (4 * a))) 1 ?_ zero_lt_one ?_
  · intro t ht
    have hp : ContinuousAt (fun t : ℝ => z₀ + (t : ℂ) * g1LowerDirection ψ) t := by fun_prop
    exact (((hf t ht).continuousAt.comp
      (f := fun t : ℝ => z₀ + (t : ℂ) * g1LowerDirection ψ) (x := t) hp).mul_const _).continuousWithinAt
  · refine ⟨R₀, fun R hR => ?_⟩
    have hb' := (hb u (mem_singleton _) ).2 m z₀ (by simp) R hR
    have hg := UpperContourLowerArcAux.gaussian_le_exponential a B R ha
    calc
      _ = ‖UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2
          (z₀ + (R : ℂ) * g1LowerDirection ψ)‖ := by
        simp [UpperContour.rayPullback, g1LowerDirection, Complex.norm_exp]
      _ ≤ C * Real.exp (-a * R ^ 2 + B * R) := hb'
      _ ≤ C * (Real.exp ((B + 1) ^ 2 / (4 * a)) * Real.exp (-R)) :=
        mul_le_mul_of_nonneg_left hg hC.le
      _ = _ := by simp only [neg_mul, one_mul]; ring

lemma a11_rotation_pi_div_two : rotation (Real.pi / 2) = Complex.I := by
  change UpperWindow.rotation (Real.pi / 2) = Complex.I
  simpa only [add_zero, UpperWindow.rotation, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one] using rotation_quarter 0

lemma a11_exp_tendsto_zero (C k : ℝ) (hk : 0 < k) :
    Tendsto (fun R : ℝ => C * Real.exp (-k * R)) atTop (𝓝 0) := by
  simpa only [Real.rpow_zero, one_mul, mul_zero] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 k hk).const_mul C

lemma a11_upper_seed_rotation (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hτ : u.1 ∈ UpperWindow.tauRegion M ψ)
    (hband : ∀ θ ∈ Icc (0 : ℝ) ψ,
      0 < (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 * rotation θ).re)
    (m : Fin (M 1 0).toNat) (v : ℂ)
    (hp : ∀ K J : ℕ, v.re < (modularPhiPolePoint M ((m : ℤ) + 1) n u.1 K J).re) :
    UpperContour.rayIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2) v
        Complex.I =
      UpperContour.rayIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2) v
        (Complex.I * UpperWindow.rotation ψ) := by
  let f := UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2
  have hrotI := a11_rotation_pi_div_two
  have hd (t θ : ℝ) (ht : 0 ≤ t)
      (hθ : θ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ)) :
      DifferentiableAt ℂ f (v + (t : ℂ) * rotation θ) := by
    apply a11_single_differentiable_of_avoids M hM u.1 u.2 _ (m : ℤ) n h ell
      (UpperWindow.tauRegion_properties M hM ψ hψ' u.1 hτ).1
    intro K J heq
    have hc : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1
      (by linarith [hθ.2, Real.pi_pos])
    have hr := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, show (rotation θ).re = Real.cos θ from rotation_re θ] at hr
    linarith [mul_nonpos_of_nonneg_of_nonpos ht hc, hp K J]
  have hα : Real.pi / 2 ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ) :=
    ⟨le_rfl, by linarith⟩
  have hβ : Real.pi / 2 + ψ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ) :=
    ⟨by linarith, le_rfl⟩
  have hIa := a11_upper_ray_integrable M hM n h ell ψ hψ hψ' u hτ hband m v _ hα
    (fun t ht => hd t _ ht hα)
  have hIb := a11_upper_ray_integrable M hM n h ell ψ hψ hψ' u hτ hband m v _ hβ
    (fun t ht => hd t _ ht hβ)
  rw [hrotI] at hIa
  change IntegrableOn (UpperContour.rayPullback f v (UpperWindow.rotation _)) (Ioi 0) at hIb
  rw [rotation_quarter] at hIb
  have harc (R : ℝ) :
      UpperContour.arcIntegral f v R (Real.pi / 2) (Real.pi / 2 + ψ) =
        endArcIntegral f v R (Real.pi / 2) (Real.pi / 2 + ψ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp [UpperContour.arcPullback, UpperContour.arcPoint, endArcPullback, endArcPoint,
      rotation, UpperWindow.rotation]
    ring
  have hfinite (R : ℝ) (hR : 0 ≤ R) :
      UpperContour.rayFinite f v Complex.I R +
        endArcIntegral f v R (Real.pi / 2) (Real.pi / 2 + ψ) -
          UpperContour.rayFinite f v (Complex.I * UpperWindow.rotation ψ) R = 0 := by
    have hh := UpperContourLowerArcAux.finite_rotation_of_differentiable f v R
      (Real.pi / 2) (Real.pi / 2 + ψ) hR (by linarith)
      (fun θ hθ t ht => hd t θ ht.1 hθ)
    rw [harc, show UpperWindow.rotation (Real.pi / 2) = Complex.I from hrotI,
      rotation_quarter] at hh
    exact hh
  have hconn := (upper_connectors_tendsto M hM n h ell 0 ψ hψ hψ'
    (u.1, u.2, 0) hτ hband v m).1
  have hlim := ((UpperContourUpperArcAux.rayFinite_tendsto f v _ hIa).add hconn).sub
    (UpperContourUpperArcAux.rayFinite_tendsto f v _ hIb)
  have hzero : Tendsto (fun R : ℝ => UpperContour.rayFinite f v Complex.I R +
      endArcIntegral f v R (Real.pi / 2) (Real.pi / 2 + ψ) -
        UpperContour.rayFinite f v (Complex.I * UpperWindow.rotation ψ) R)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (hfinite R hR).symm
  simpa only [add_zero, sub_eq_zero] using tendsto_nhds_unique hlim hzero

lemma a11_seed_ray_translation (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hτ : u.1 ∈ UpperWindow.tauRegion M ψ)
    (hband : ∀ θ ∈ Icc (0 : ℝ) ψ,
      0 < (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 * rotation θ).re)
    (m : Fin (M 1 0).toNat) (v : ℂ)
    (hp : ∀ K J : ℕ,
      v.re < (modularPhiPolePoint M ((m : ℤ) + 1) n u.1 K J).re ∧
      v.im < (modularPhiPolePoint M ((m : ℤ) + 1) n u.1 K J).im) :
    let f := UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2;
    let b := (seedCrossing v ψ : ℂ) - Complex.I;
    -UpperContour.rayIntegral f v (g1LowerDirection ψ) + UpperContour.rayIntegral f v Complex.I =
      -UpperContour.rayIntegral f b (g1LowerDirection ψ) + UpperContour.rayIntegral f b Complex.I := by
  let f := UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2
  let b := (seedCrossing v ψ : ℂ) - Complex.I
  have hstrips := a11_seed_strips_differentiable M hM u.1 u.2 v (m : ℤ) n h ell ψ
    (UpperWindow.tauRegion_properties M hM ψ hψ' u.1 hτ).1 hψ hψ' hp
  change ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t →
    DifferentiableAt ℂ f (v + (s : ℂ) * (b - v) + (t : ℂ) * Complex.I) ∧
    DifferentiableAt ℂ f (v + (s : ℂ) * (b - v) + (t : ℂ) * g1LowerDirection ψ) at hstrips
  have hU (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (UpperContour.rayPullback f (v + (s : ℂ) * (b - v)) Complex.I) (Ioi 0) := by
    have hi := a11_upper_ray_integrable M hM n h ell ψ hψ hψ' u hτ hband m
      (v + (s : ℂ) * (b - v)) (Real.pi / 2) ⟨le_rfl, by linarith⟩
      (fun t ht => by simpa only [a11_rotation_pi_div_two] using (hstrips s hs t ht).1)
    simpa only [a11_rotation_pi_div_two] using hi
  have hL (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (UpperContour.rayPullback f (v + (s : ℂ) * (b - v))
        (g1LowerDirection ψ)) (Ioi 0) :=
    a11_lower_ray_integrable M hM n h ell ψ hψ hψ' u hτ m
      (v + (s : ℂ) * (b - v)) (fun t ht => (hstrips s hs t ht).2)
  have hball (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      v + (s : ℂ) * (b - v) ∈ Metric.closedBall (0 : ℂ) (‖v‖ + ‖b - v‖) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ ‖v‖ + ‖(s : ℂ) * (b - v)‖ := norm_add_le _ _
      _ = ‖v‖ + s * ‖b - v‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hs.2 (norm_nonneg (b - v))]
  obtain ⟨C, k, R₀, hC, hk, hR₀, hb⟩ := a11_upper_single_bound M hM n h ell ψ
    (‖v‖ + ‖b - v‖) hψ hψ' u hτ hband
  have hconnU : Tendsto
      (fun R : ℝ => UpperContour.rayFinite f (v + (R : ℂ) * Complex.I) (b - v) 1)
      atTop (𝓝 0) := by
    apply G1ContinuationEndRotationAuxA11.connector_tendsto_zero_of_uniform_bound f v b
      Complex.I (fun R => C * Real.exp (-k * R)) (a11_exp_tendsto_zero C k hk)
    filter_upwards [eventually_ge_atTop R₀] with R hR
    intro s hs
    have hh := hb m (v + (s : ℂ) * (b - v)) (hball s hs) R hR (Real.pi / 2)
      ⟨le_rfl, by linarith⟩
    simpa only [a11_rotation_pi_div_two, add_right_comm] using hh
  obtain ⟨D, a, B, S₀, hD, ha, hB, hS₀, hg⟩ :=
    single_lower_gaussian_translations M hM n h ell ψ (‖v‖ + ‖b - v‖) hψ hψ'
      {u} isCompact_singleton (by simpa only [mem_singleton_iff, forall_eq] using hτ)
  have hconnL : Tendsto
      (fun R : ℝ => UpperContour.rayFinite f (v + (R : ℂ) * g1LowerDirection ψ) (b - v) 1)
      atTop (𝓝 0) := by
    apply G1ContinuationEndRotationAuxA11.connector_tendsto_zero_of_uniform_bound f v b
      (g1LowerDirection ψ)
      (fun R => (D * Real.exp ((B + 1) ^ 2 / (4 * a))) * Real.exp (-1 * R))
      (a11_exp_tendsto_zero _ 1 zero_lt_one)
    filter_upwards [eventually_ge_atTop S₀] with R hR
    intro s hs
    have hh := (hg u (mem_singleton _) ).2 m (v + (s : ℂ) * (b - v)) (hball s hs) R hR
    have heq : v + (R : ℂ) * g1LowerDirection ψ + (s : ℂ) * (b - v) =
        (v + (s : ℂ) * (b - v)) + (R : ℂ) * g1LowerDirection ψ := by ring
    rw [heq]
    calc
      _ ≤ D * Real.exp (-a * R ^ 2 + B * R) := hh
      _ ≤ D * (Real.exp ((B + 1) ^ 2 / (4 * a)) * Real.exp (-R)) :=
        mul_le_mul_of_nonneg_left (UpperContourLowerArcAux.gaussian_le_exponential a B R ha) hD.le
      _ = _ := by simp only [neg_mul, one_mul]; ring
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hbase : v + (b - v) = b := by ring
  have htransU := G1ContinuationEndRotationAuxA11.parallel_ray_integral_eq f v b Complex.I
    (fun s hs t ht => (hstrips s hs t ht).1)
    (by simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hU 0 hzero)
    (by simpa only [Complex.ofReal_one, one_mul, hbase] using hU 1 hone) hconnU
  have htransL := G1ContinuationEndRotationAuxA11.parallel_ray_integral_eq f v b (g1LowerDirection ψ)
    (fun s hs t ht => (hstrips s hs t ht).2)
    (by simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hL 0 hzero)
    (by simpa only [Complex.ofReal_one, one_mul, hbase] using hL 1 hone) hconnL
  dsimp only
  linear_combination htransU - htransL

/-- A11. Actual seed comparison: upper end vertical, lower end still bent. [RW26, pp. 28--29]. The
pole-clear geometry of the chosen crossings is stated explicitly. -/
theorem single_seed_end_rotation (M : SL(2, ℤ)) (n h ell : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (u : ℂ × ℂ)
    (hu : u ∈ UpperIntegralIdentities.singleDomain M h ell ψ σ ρ δ) :
    ∃ x : Fin (M 1 0).toNat → ℝ,
      (∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x m) ψ) ∧
      (∑ m : Fin (M 1 0).toNat,
        g1BentIntegral (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2) (x m) ψ) =
        UpperIntegralIdentities.singleLineSum M n h ell ψ δ u := by
  let v : Fin (M 1 0).toNat → ℂ := fun m => UpperWindow.base M (m : ℤ) n δ u.1
  refine ⟨fun m => seedCrossing (v m) ψ, ?_, ?_⟩
  · intro m
    apply bentClear_of_quadrant M u.1 (v m) n (m : ℤ) ψ hc.2.1 hc.2.2.1
    intro K J
    have hq := seed_pole_quadrants M h ell 0 (m : ℤ) n ψ σ ρ δ hc
      (u.1, u.2, UpperWindow.centerY M 0 ρ u.1)
      (a11_single_domain_lift M h ell ψ σ ρ δ hc u hu) K J
    exact ⟨hq.1, hq.2.1⟩
  · have hx := a11_single_domain_lift M h ell ψ σ ρ δ hc u hu
    obtain ⟨κ, hκ, hm⟩ := seed_angular_margins M h ell 0 ψ σ ρ δ hc
      (u.1, u.2, UpperWindow.centerY M 0 ρ u.1) hx
    have hband : ∀ θ ∈ Icc (0 : ℝ) ψ,
        0 < (G1RatioTail.complexS M u.1 u.2 h ell / etaDenom M u.1 * rotation θ).re :=
      fun θ hθ => hκ.trans_le (hm θ hθ).1
    unfold UpperIntegralIdentities.singleLineSum
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      UpperContour.lineIntegral (UpperWindow.singleKernel M (j : ℤ) n h ell u.1 u.2)
        (UpperWindow.base M (j : ℤ) n δ u.1) ψ) (M 1 0).toNat]
    apply Finset.sum_congr rfl
    intro m hm'
    let f := UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2
    have hp (K J : ℕ) :
        (v m).re < (modularPhiPolePoint M ((m : ℤ) + 1) n u.1 K J).re ∧
        (v m).im < (modularPhiPolePoint M ((m : ℤ) + 1) n u.1 K J).im := by
      have hq := seed_pole_quadrants M h ell 0 (m : ℤ) n ψ σ ρ δ hc
        (u.1, u.2, UpperWindow.centerY M 0 ρ u.1) hx K J
      exact ⟨hq.1, hq.2.1⟩
    have hline : Integrable (UpperContour.linePullback f (v m) ψ) :=
      UpperContour.line_integrable .single M h ell 0 (m : ℤ) n ψ σ ρ δ hc
        (u.1, u.2, UpperWindow.centerY M 0 ρ u.1) hx
    have hrot := a11_upper_seed_rotation M hc.1 n h ell ψ hc.2.1 hc.2.2.1 u hu.1
      hband m (v m) (fun K J => (hp K J).1)
    have hshift := a11_seed_ray_translation M hc.1 n h ell ψ hc.2.1 hc.2.2.1 u hu.1
      hband m (v m) hp
    change g1BentIntegral f (seedCrossing (v m) ψ) ψ = UpperContour.lineIntegral f (v m) ψ
    rw [G1ContinuationEndRotationAuxA11.bentIntegral_eq_rays,
      G1ContinuationEndRotationAuxA11.lineIntegral_eq_rays f (v m) ψ hline, ← hrot]
    exact hshift.symm

lemma a12_lower_vertical_exp_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n h ell p : ℤ)
    (x : UpperWindow.Parameters) (v : ℂ) (m : Fin (M 1 0).toNat)
    (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hτ : x.1 ∈ UpperWindow.tauRegion M ψ)
    (hl : (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1).re < 0) :
    ∃ C κ R₀ : ℝ, 0 < κ ∧ 0 < R₀ ∧ ∀ R ≥ R₀,
      ‖UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2
        (v + (R : ℂ) * (-Complex.I))‖ ≤ C * Real.exp (-κ * R) := by
  let L := G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1
  let Q := lowerRatioCoefficient M n h ell p (m : ℤ) x
  let f := UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2
  let B := ‖Q * e (L * v)‖
  obtain ⟨D, k, R₀, hD, hk, hR₀, hb⟩ :=
    lower_ratio_uniform_asymptotic M hM n h ell p ψ ‖v‖ hψ hψ'
      {x} isCompact_singleton (by simpa only [mem_singleton_iff, forall_eq] using hτ)
  refine ⟨(D + 1) * B, -(2 * Real.pi * L.re), R₀,
    by dsimp [L]; nlinarith [Real.pi_pos], hR₀, ?_⟩
  intro R hR
  let z := v + (R : ℂ) * (-Complex.I)
  let den := Q * e (L * z)
  have hrot : rotation (-Real.pi / 2) = -Complex.I := by
    unfold rotation
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_div, neg_div]
  have hθ : -Real.pi / 2 ∈ Icc (-Real.pi / 2) (-Real.pi / 2 + ψ) :=
    ⟨le_rfl, by linarith⟩
  have hq := (hb x (mem_singleton x) m v (by simp) R hR (-Real.pi / 2) hθ).2.2
  simp only [endArcPoint, hrot] at hq
  change ‖f z / den - 1‖ ≤ D * Real.exp (-k * R) at hq
  have hn : den ≠ 0 := mul_ne_zero
    ((lower_coefficient_analytic_nonzero M n h ell p (m : ℤ)).2.1 x) (e_ne_zero _)
  have hδ : D * Real.exp (-k * R) ≤ D := by
    have he : Real.exp (-k * R) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [hR₀.trans_le hR])
    exact (mul_le_mul_of_nonneg_left he hD.le).trans_eq (mul_one _)
  have hq' : ‖f z / den‖ ≤ D + 1 := by
    have ht := norm_le_norm_sub_add (f z / den) (1 : ℂ)
    simp only [norm_one] at ht
    linarith [hq.trans hδ]
  have hp : ‖e (L * z)‖ = ‖e (L * v)‖ * Real.exp ((2 * Real.pi * L.re) * R) := by
    dsimp only [z]
    rw [G1BilateralRatioTailsAux.norm_e, G1BilateralRatioTailsAux.norm_e, ← Real.exp_add]
    congr 1
    simp [Complex.mul_im, Complex.mul_re]
    <;> ring
  have hd : ‖den‖ = B * Real.exp ((2 * Real.pi * L.re) * R) := by
    dsimp only [den, B]
    rw [norm_mul, norm_mul, hp]
    ring
  calc
    ‖f z‖ = ‖f z / den‖ * ‖den‖ := by rw [← norm_mul, div_mul_cancel₀ _ hn]
    _ ≤ (D + 1) * (B * Real.exp ((2 * Real.pi * L.re) * R)) := by
      rw [← hd]
      exact mul_le_mul_of_nonneg_right hq' (norm_nonneg _)
    _ = (D + 1) * B * Real.exp (-(-(2 * Real.pi * L.re)) * R) := by ring

lemma a12_endArcIntegral_eq (f : ℂ → ℂ) (a : ℂ) (R α β : ℝ) :
    endArcIntegral f a R α β = UpperContour.arcIntegral f a R α β := by
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp [endArcPullback, endArcPoint, UpperContour.arcPullback, UpperContour.arcPoint,
    rotation, UpperWindow.rotation, mul_assoc]

lemma a12_ratio_component (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) (m : Fin (M 1 0).toNat) :
    extensionIntegral (seedChain (UpperWindow.base M (m : ℤ) n δ x.1))
      (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2) =
      UpperContour.lineIntegral
        (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)
        (UpperWindow.base M (m : ℤ) n δ x.1) ψ := by
  let f := UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2
  let v := UpperWindow.base M (m : ℤ) n δ x.1
  have hrotu : UpperWindow.rotation (Real.pi / 2) = Complex.I := by
    unfold UpperWindow.rotation
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_div]
  have hrotl : UpperWindow.rotation (-Real.pi / 2) = -Complex.I := by
    unfold UpperWindow.rotation
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_div, neg_div]
  have hrottl : UpperWindow.rotation (-Real.pi / 2 + ψ) =
      -(Complex.I * UpperWindow.rotation ψ) := by
    have hh := reflected_lower_direction ψ
    change -UpperWindow.rotation (-Real.pi / 2 + ψ) = _ at hh
    rw [rotation_quarter] at hh
    exact neg_eq_iff_eq_neg.mp hh
  have hcu : ContinuousOn (UpperContour.rayPullback f v Complex.I) (Ici 0) := by
    intro R hR
    have hf : ContinuousAt f (v + (R : ℂ) * Complex.I) := by
      simpa only [UpperContour.arcPoint, hrotu] using
        (G1ContinuationEndRotationAuxA12.seed_ratio_upper_sector_analyticAt
          M h ell p (m : ℤ) n ψ σ ρ δ hc x hx R (Real.pi / 2) hR
          ⟨le_rfl, by linarith [hc.2.1]⟩).continuousAt
    exact ((hf.comp (f := fun t : ℝ => v + (t : ℂ) * Complex.I)
      (by fun_prop)).mul_const _).continuousWithinAt
  have hcl : ContinuousOn (UpperContour.rayPullback f v (-Complex.I)) (Ici 0) := by
    intro R hR
    have hf : ContinuousAt f (v + (R : ℂ) * (-Complex.I)) := by
      simpa only [UpperContour.arcPoint, hrotl] using
        (G1ContinuationEndRotationAuxA12.seed_ratio_lower_sector_analyticAt
          M h ell p (m : ℤ) n ψ σ ρ δ hc x hx R (-Real.pi / 2) hR
          ⟨le_rfl, by linarith [hc.2.1]⟩).continuousAt
    exact ((hf.comp (f := fun t : ℝ => v + (t : ℂ) * (-Complex.I))
      (by fun_prop)).mul_const _).continuousWithinAt
  have hsign := seed_rotated_positive M h ell p ψ σ ρ δ hc x hx 0 ⟨le_rfl, hc.2.1.le⟩
  have hs : 0 < (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1).re := by
    simpa [UpperWindow.rotation] using hsign.1
  have hl : (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1).re < 0 := by
    simpa [UpperWindow.rotation] using neg_pos.mp hsign.2
  obtain ⟨Cu, ku, Ru, hku, hRu, hbu⟩ :=
    G1ContinuationEndRotationAuxA12.upper_vertical_exp_bound M hc.1 (m : ℤ) n h ell p
      x.1 x.2.1 x.2.2 v ψ hc.2.1 hc.2.2.1 hx.1 hs
  have hiu : IntegrableOn (UpperContour.rayPullback f v Complex.I) (Ioi 0) := by
    apply G1ContinuationEndRotationAuxA12.integrableOn_of_eventual_exp_bound
      _ Cu ku Ru hku hRu.le hcu
    intro R hR
    simpa only [UpperContour.rayPullback, norm_mul, Complex.norm_I, mul_one] using hbu R hR
  obtain ⟨Cl, kl, Rl, hkl, hRl, hbl⟩ :=
    a12_lower_vertical_exp_bound M hc.1 n h ell p x v m ψ hc.2.1 hc.2.2.1 hx.1 hl
  have hil : IntegrableOn (UpperContour.rayPullback f v (-Complex.I)) (Ioi 0) := by
    apply G1ContinuationEndRotationAuxA12.integrableOn_of_eventual_exp_bound
      _ Cl kl Rl hkl hRl.le hcl
    intro R hR
    simpa only [UpperContour.rayPullback, norm_mul, norm_neg, Complex.norm_I, mul_one]
      using hbl R hR
  have hitu := UpperContour.upper_rotated_ray_integrable .ratio M h ell p (m : ℤ) n
    ψ σ ρ δ hc x hx
  have hitl := UpperContour.lower_rotated_ray_integrable .ratio M h ell p (m : ℤ) n
    ψ σ ρ δ hc x hx
  have hbandu : upperBand M h ell ψ x := by
    intro θ hθ
    exact (seed_rotated_positive M h ell p ψ σ ρ δ hc x hx θ hθ).1
  have hbandl : lowerBand M h ell p ψ x := by
    intro θ hθ
    exact neg_pos.mp (seed_rotated_positive M h ell p ψ σ ρ δ hc x hx θ hθ).2
  have hau := (upper_connectors_tendsto M hc.1 n h ell p ψ hc.2.1 hc.2.2.1
    x hx.1 hbandu v m).2
  obtain ⟨C, k, R₀, hC, hk, hR₀, harc⟩ := lower_ratio_connector_bound_limit
    M hc.1 n h ell p ψ ‖v‖ hc.2.1 hc.2.2.1 {x} isCompact_singleton
    (by simpa only [mem_singleton_iff, forall_eq] using hx.1)
    (by simpa only [mem_singleton_iff, forall_eq] using hbandl)
  have hal := (harc x (mem_singleton x) m v (by simp)).2
  have hru := G1ContinuationEndRotationAuxA12.ray_rotation f v
    (Real.pi / 2) (Real.pi / 2 + ψ) (by linarith [hc.2.1])
    (fun θ hθ t ht => (G1ContinuationEndRotationAuxA12.seed_ratio_upper_sector_analyticAt
      M h ell p (m : ℤ) n ψ σ ρ δ hc x hx t θ ht hθ).differentiableAt)
    (by simpa only [hrotu] using hiu) hitu
    (by simpa only [a12_endArcIntegral_eq] using hau)
  have hrl := G1ContinuationEndRotationAuxA12.ray_rotation f v
    (-Real.pi / 2) (-Real.pi / 2 + ψ) (by linarith [hc.2.1])
    (fun θ hθ t ht => (G1ContinuationEndRotationAuxA12.seed_ratio_lower_sector_analyticAt
      M h ell p (m : ℤ) n ψ σ ρ δ hc x hx t θ ht hθ).differentiableAt)
    (by simpa only [hrotl] using hil) hitl
    (by simpa only [a12_endArcIntegral_eq] using hal)
  have hfull := G1ContinuationEndRotationAuxA12.vertical_integral_eq_lineIntegral f v ψ
    (G1ContinuationEndRotationAuxA12.integrable_line_of_rays f v Complex.I hiu hil)
    (UpperContour.line_integrable .ratio M h ell p (m : ℤ) n ψ σ ρ δ hc x hx)
    (by simpa only [hrotu, rotation_quarter] using hru)
    (by simpa only [hrotl, hrottl] using hrl)
  simpa only [seedChain, ofChain, extensionIntegral, g1ChainIntegral,
    Finset.sum_empty, add_zero] using hfull

/-- A12. Actual seed comparison: both ratio ends vertical, finite CCW corrections. [RW26, pp.
28--29]. This is the bridge to upper_ratio, not a postulated branch choice. -/
theorem ratio_seed_end_rotation (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) :
    ∃ D : Fin (M 1 0).toNat → CircleExtension,
      (∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) ∧
      ratioExtensionSum M D n h ell p x = UpperIntegralIdentities.ratioLineSum M n h ell p ψ δ x := by
  refine ⟨fun m => seedChain (UpperWindow.base M (m : ℤ) n δ x.1), ?_, ?_⟩
  · intro m
    exact seedChain_separates M h ell p (m : ℤ) n ψ σ ρ δ hc x hx
  · unfold ratioExtensionSum UpperIntegralIdentities.ratioLineSum
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    exact a12_ratio_component M n h ell p ψ σ ρ δ hc x hx m

#check @G1RatioTail.reflection_difference_affine
#check @UpperWindow.arc_linear_pos
#check @G1BilateralGeometry.gaussianCoefficient
#print endArcPullback
#print lowerRatioCoefficient

end SICLean.L4.G1Continuation
