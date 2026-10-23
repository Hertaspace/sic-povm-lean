import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Analytic identity principles for the upper-product comparison

These statements concern only analytic functions. In particular they do not assume or identify
either definition of the quantum dilogarithm.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace SICLean.L4.ProductIdentity

private def unitArc (t : ℝ) : ℂ :=
  ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

private lemma unitArc_inv (t : ℝ) : (unitArc t)⁻¹ = star (unitArc t) := by
  have hd : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have hn : Complex.normSq (unitArc t) = 1 := by
    simp only [Complex.normSq_apply, unitArc]
    field_simp
    ring
  rw [Complex.inv_def, hn]
  simp

private lemma unitArc_injective : Function.Injective unitArc := by
  have hrec (t : ℝ) : (unitArc t).im = t * (1 + (unitArc t).re) := by
    dsimp [unitArc]
    field_simp
    ring
  have hne (t : ℝ) : 1 + (unitArc t).re ≠ 0 := by
    have hd : (1 + (unitArc t).re) * (1 + t ^ 2) = 2 := by
      dsimp [unitArc]
      field_simp
      ring
    intro hzero
    rw [hzero, zero_mul] at hd
    norm_num at hd
  intro s t hst
  apply mul_right_cancel₀ (hne t)
  rw [← congrArg Complex.re hst, ← hrec s, hst, hrec t]

private lemma continuous_unitArc : Continuous unitArc := by
  have hd (t : ℝ) : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  rw [show unitArc = fun t : ℝ =>
    (((1 - t ^ 2) / (1 + t ^ 2) : ℝ) : ℂ) +
      ((2 * t / (1 + t ^ 2) : ℝ) : ℂ) * Complex.I by
        funext t
        exact (Complex.re_add_im (unitArc t)).symm]
  fun_prop

/-- A unit-circle arc inside the open first quadrant determines an analytic function on the whole
quadrant. The unit condition is written in the form used by the self-dual parameter argument. -/
theorem eqOn_zero_upperQuadrant_of_unit (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f {b : ℂ | 0 < b.re ∧ 0 < b.im})
    (hunit : ∀ b : ℂ, 0 < b.re ∧ 0 < b.im → b⁻¹ = star b → f b = 0) :
    EqOn f 0 {b : ℂ | 0 < b.re ∧ 0 < b.im} := by
  let t₀ : ℝ := 1 / 2
  have hU : IsPreconnected {b : ℂ | 0 < b.re ∧ 0 < b.im} :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hcenter : unitArc t₀ ∈ {b : ℂ | 0 < b.re ∧ 0 < b.im} := by
    norm_num [unitArc, t₀]
  have ht : Tendsto unitArc (𝓝[≠] t₀) (𝓝[≠] (unitArc t₀)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_unitArc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun heq => ht (unitArc_injective heq)
  have hrange : ∀ᶠ t : ℝ in 𝓝[≠] t₀, 0 < t ∧ t < 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num [t₀]) (by norm_num [t₀]))
  have hfrequent : ∃ᶠ b : ℂ in 𝓝[≠] (unitArc t₀), f b = 0 := by
    apply ht.frequently
    apply Filter.Eventually.frequently
    filter_upwards [hrange] with t ht
    apply hunit _ ?_ (unitArc_inv t)
    change 0 < (1 - t ^ 2) / (1 + t ^ 2) ∧ 0 < 2 * t / (1 + t ^ 2)
    constructor
    · apply div_pos ?_ (by positivity)
      nlinarith
    · exact div_pos (mul_pos (by norm_num) ht.1) (by positivity)
  exact hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hcenter hfrequent

/-- Vanishing in the lower half of a strip determines an analytic function on that strip. -/
theorem eqOn_zero_strip_of_lower (a : ℝ) (ha : 0 < a) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a})
    (hzero : ∀ z : ℂ, -a < z.im ∧ z.im < 0 → f z = 0) :
    EqOn f 0 {z : ℂ | |z.im| < a} := by
  have hU : IsPreconnected {z : ℂ | |z.im| < a} := by
    simpa only [abs_lt, Set.ofPred_and] using
      ((convex_halfSpace_im_gt (-a)).inter (convex_halfSpace_im_lt a)).isPreconnected
  let z₀ : ℂ := ((-a / 2 : ℝ) : ℂ) * Complex.I
  have hz₀ : -a < z₀.im ∧ z₀.im < 0 := by
    have him : z₀.im = -a / 2 := by simp [z₀]
    rw [him]
    constructor <;> linarith
  have hzU : z₀ ∈ {z : ℂ | |z.im| < a} := by
    rw [Set.mem_ofPred, abs_lt]
    exact ⟨hz₀.1, hz₀.2.trans ha⟩
  apply hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hzU
  have hV : IsOpen {z : ℂ | -a < z.im ∧ z.im < 0} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  filter_upwards [hV.mem_nhds hz₀] with z hz
  exact hzero z hz

/-- Agreement on the real axis determines an analytic function throughout any horizontal strip
containing that axis. -/
theorem eqOn_zero_strip_of_real (a : ℝ) (ha : 0 < a) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a})
    (hzero : ∀ x : ℝ, f x = 0) : EqOn f 0 {z : ℂ | |z.im| < a} := by
  have hU : IsPreconnected {z : ℂ | |z.im| < a} := by
    simpa only [abs_lt, Set.ofPred_and] using
      ((convex_halfSpace_im_gt (-a)).inter (convex_halfSpace_im_lt a)).isPreconnected
  have hcenter : (0 : ℂ) ∈ {z : ℂ | |z.im| < a} := by simpa using ha
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun heq => hx (Complex.ofReal_eq_zero.mp heq)
  apply hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hcenter
  exact ht.frequently (Filter.Eventually.of_forall hzero).frequently

end SICLean.L4.ProductIdentity
