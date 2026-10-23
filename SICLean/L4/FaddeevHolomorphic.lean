import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphic parameter integrals from local bounds

A Schwarz estimate turns a bound for a holomorphic function on the larger ball into a derivative
bound on the smaller ball. This lets the Faddeev application dominate the kernel itself rather than
expand its parameter derivative into coth factors.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology

namespace SICLean.L4

lemma joint_norm_fderiv_le_of_ball_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} {p q : E} {r B : ℝ} (hr : 0 < r)
    (hq : q ∈ ball p r) (hf : DifferentiableOn ℂ f (ball p (2*r)))
    (hbound : ∀ y ∈ ball p (2*r), ‖f y‖ ≤ B) :
    ‖fderiv ℂ f q‖ ≤ (2*B)/r := by
  have hsub : ball q r ⊆ ball p (2*r) := by
    intro y hy
    simp only [mem_ball] at hy hq ⊢
    calc
      dist y p ≤ dist y q + dist q p := dist_triangle _ _ _
      _ < r + r := add_lt_add hy hq
      _ = 2*r := by ring
  have hq' : q ∈ ball p (2*r) :=
    mem_ball.mpr ((mem_ball.mp hq).trans (by linarith))
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) ?_ hr
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖f y - f q‖ ≤ ‖f y‖ + ‖f q‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hbound y (hsub hy)) (hbound q hq')
    _ = 2*B := by ring

theorem joint_hasFDerivAt_integral_of_locally_dominated_holomorphic
    {F : (ℂ × ℂ) → ℝ → ℂ} {p : ℂ × ℂ} {r : ℝ} {B : ℝ → ℝ}
    (hr : 0 < r)
    (hm : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (F q))
    (hi : Integrable (F p))
    (hdm : AEStronglyMeasurable (fun x => fderiv ℂ (fun q => F q x) p))
    (hh : ∀ x, DifferentiableOn ℂ (fun q => F q x) (ball p (2*r)))
    (hB : ∀ x, ∀ q ∈ ball p (2*r), ‖F q x‖ ≤ B x)
    (hBi : Integrable B) :
    HasFDerivAt (fun q => ∫ x : ℝ, F q x)
      (∫ x : ℝ, fderiv ℂ (fun q => F q x) p) p := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds p hr) hm hi hdm
    (bound := fun x => (2*B x)/r)
  · exact Filter.Eventually.of_forall fun x q hq =>
      joint_norm_fderiv_le_of_ball_bound hr hq (hh x) (hB x)
  · exact (hBi.const_mul 2).div_const r
  · refine Filter.Eventually.of_forall fun x q hq => ?_
    have hq' : q ∈ ball p (2*r) :=
      mem_ball.mpr ((mem_ball.mp hq).trans (by linarith))
    exact ((hh x).differentiableAt (isOpen_ball.mem_nhds hq')).hasFDerivAt

end SICLean.L4
