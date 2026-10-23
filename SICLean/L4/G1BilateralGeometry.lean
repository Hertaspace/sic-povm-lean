import SICLean.L4.G1RatioTailBounds
import SICLean.L4.G1FixedSeparation
import SICLean.L4.G1BilateralGeometryAux

set_option autoImplicit false

/-!
# Full-disk geometry and shared estimates

Bilateral parameter geometry and estimates. `parameterDisk` is the
existing full closed ball; no sign condition on Im τ is added. All φ, Φ, μ and square roots remain
the existing representatives. This file uses proved `bilateral_uniform_asymptotics` directly; no new
proof of the Faddeev estimate is needed.

[RW26, p. 6, Prop. 1--2, (19), p. 7, Lemma 1, (22)--(23)]. Full-disk estimates are formalized here.
No lower-half-plane integral identity or removable right side is asserted.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1BilateralGeometry

open G1BilateralGeometryAux

/-- Arithmetic data only, with the single-function switch literally false. [RW26, p. 7]. -/
def singleData (w : ℂ) (n h ell m : ℤ) : ModularCluster.KernelData where
  m := m
  n := n
  p := 0
  ell := ell
  h := h
  w := w
  y := 0
  ratio := false

/-- The existing cluster representative, not a newly chosen continuation. -/
def singleKernel (M : SL(2, ℤ)) (τ w : ℂ) (n h ell m : ℤ) (z : ℂ) : ℂ :=
  ModularCluster.kernel M (singleData w n h ell m) z τ

/-- Exactly the finite index set needed by a finite G1 component family. -/
def indexFamily (F : Finset ℤ) (n p : ℤ) : Finset (ℤ × ℤ) :=
  (F.image (fun m => (m + 1, n))) ∪ (F.image (fun m => (m + p, n)))

/-- Minus the real quadratic coefficient of the bent lower-tail log modulus. It is a formula, not a
positive-margin assumption. -/
def gaussianCoefficient (M : SL(2, ℤ)) (τ : ℂ) (ψ : ℝ) : ℝ :=
  Real.pi * (M 1 0 : ℝ) / ‖etaDenom M τ‖ *
    Real.sin (2 * ψ - (etaDenom M τ).arg)

/-- G01. Same E_m, including n (not m) in the h term. [RW26, p. 7]. -/
theorem single_phase (M : SL(2, ℤ)) (τ w z : ℂ) (n h ell m : ℤ) :
    ModularCluster.phase M (singleData w n h ell m) z τ =
      g1Exponent M τ w z n h ell m := by
  rfl

/-- G02. Point values, not merely equality of punctured germs. [RW26, p. 7, (22)]. -/
theorem singleKernel_real (M : SL(2, ℤ)) (τ w : ℝ) (n h ell m : ℤ) :
    singleKernel M (τ : ℂ) (w : ℂ) n h ell m =
      g1SingleKernel M τ w n h ell m := by
  funext z
  simp [singleKernel, ModularCluster.kernel, singleData, ModularCluster.phase,
    g1SingleKernel, g1Exponent]

/-- G03. Only the actual numerator pole labels occur for a single kernel. [RW26, p. 6]. -/
theorem single_labels (M : SL(2, ℤ)) (w : ℂ) (n h ell m : ℤ)
    (b : ModularCluster.Label) :
    b ∈ ModularCluster.labels M (singleData w n h ell m) ↔
      b.1 = true ∧ b.2 ∈ modularPhiPoleLabels M (m + 1) n := by
  rcases b with ⟨u, b⟩
  cases u <;> simp [ModularCluster.labels, singleData]

/-- G04. One full disk stays on the existing slit-plane principal branch. [RW26, p. 6, (19)]. -/
theorem full_disk_denom (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ β : ℝ) (hT : 0 < g1T M τ₀) (hβ : 0 < β) (hβ' : β < Real.pi / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
      τ ∈ modularPhiDomain M ∧ g1T M τ₀ / 2 ≤ (etaDenom M τ).re ∧
        ‖etaDenom M τ‖ ≤ 2 * g1T M τ₀ ∧ |(etaDenom M τ).arg| ≤ β := by
  have hT' : 0 < ModularSector.realDenom M τ₀ := hT
  refine ⟨ModularSector.parameterRadius M τ₀ β,
    ModularSector.parameterRadius_pos M hM τ₀ β hT' hβ hβ', ?_⟩
  intro τ hτ
  obtain ⟨hre, hnorm, harg, hdom⟩ :=
    ModularSector.parameterDisk_denom_control M hM τ₀ β hT' hβ hβ' hτ
  exact ⟨hdom, hre, hnorm, harg.trans (by linarith)⟩

/-- G05. Common positive upper-tail margin, on both sides of the real axis. [RW26, p. 7]. -/
theorem single_window_margin (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w : ℝ) (h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).re ∧
          κ ≤ 2 * Real.pi *
            (G1RatioTail.complexS M τ (w : ℂ) h ell / etaDenom M τ).re := by
  let u : ℂ → ℝ := fun τ => 2 * Real.pi *
    (G1RatioTail.complexS M τ (w : ℂ) h ell / etaDenom M τ).re
  have hu : 0 < u (τ₀ : ℂ) := upper_window_pos M τ₀ w h ell hT hs
  obtain ⟨ρ, hρ, hmargin⟩ := disk_of_eventually τ₀
    (fun τ => τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).re ∧ u (τ₀ : ℂ) / 2 ≤ u τ)
    (by
      filter_upwards [domain_eventually M τ₀ hT,
        positive_margin_eventually (upper_window_continuousAt M τ₀ w h ell hT) hu]
        with τ hdom hmargin
      exact ⟨hdom.1, hdom.2, hmargin⟩)
  exact ⟨ρ, u (τ₀ : ℂ) / 2, hρ, half_pos hu, hmargin⟩

/-- G06. Both strict complex windows retain the same positive margin. [RW26, p. 7, p. 13]. -/
theorem ratio_window_margin (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).re ∧
          κ ≤ 2 * Real.pi *
            (G1RatioTail.complexS M τ (w : ℂ) h ell / etaDenom M τ).re ∧
          κ ≤ -(2 * Real.pi *
            (G1RatioTail.complexL M τ (w : ℂ) (y : ℂ) h ell p / etaDenom M τ).re) := by
  let u : ℂ → ℝ := fun τ => 2 * Real.pi *
    (G1RatioTail.complexS M τ (w : ℂ) h ell / etaDenom M τ).re
  let v : ℂ → ℝ := fun τ => -(2 * Real.pi *
    (G1RatioTail.complexL M τ (w : ℂ) (y : ℂ) h ell p / etaDenom M τ).re)
  have hu : 0 < u (τ₀ : ℂ) := upper_window_pos M τ₀ w h ell hT hs
  have hv : 0 < v (τ₀ : ℂ) := lower_window_pos M τ₀ w y h ell p hT hL
  let κ := min (u (τ₀ : ℂ) / 2) (v (τ₀ : ℂ) / 2)
  obtain ⟨ρ, hρ, hmargin⟩ := disk_of_eventually τ₀
    (fun τ => τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).re ∧ κ ≤ u τ ∧ κ ≤ v τ)
    (by
      filter_upwards [domain_eventually M τ₀ hT,
        positive_margin_eventually (upper_window_continuousAt M τ₀ w h ell hT) hu,
        positive_margin_eventually (lower_window_continuousAt M τ₀ w y h ell p hT) hv]
        with τ hdom huτ hvτ
      exact ⟨hdom.1, hdom.2, (min_le_left _ _).trans huτ, (min_le_right _ _).trans hvτ⟩)
  exact ⟨ρ, κ, hρ, lt_min (half_pos hu) (half_pos hv), hmargin⟩

/-- G07. Exact coefficient, determining the sign on the bent lower ray. [RW26, p. 6, Prop. 1, p. 7,
Lemma 1]. -/
theorem gaussian_coefficient_exact (M : SL(2, ℤ)) (τ : ℂ) (ψ : ℝ)
    (hT : etaDenom M τ ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I *
      (-((M 1 0 : ℂ) / (2 * etaDenom M τ)) * g1LowerDirection ψ ^ 2)).re =
        -gaussianCoefficient M τ ψ := by
  have halgebra : 2 * (Real.pi : ℂ) * Complex.I *
      (-((M 1 0 : ℂ) / (2 * etaDenom M τ)) * g1LowerDirection ψ ^ 2) =
      -((Real.pi : ℂ) * (M 1 0 : ℂ)) * Complex.I / etaDenom M τ *
        g1LowerDirection ψ ^ 2 := by ring
  rw [halgebra]
  simp only [gaussianCoefficient, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    Complex.I_im, lower_direction_sq_re, lower_direction_sq_im, mul_zero,
    zero_mul, sub_zero, mul_one, neg_zero, zero_div,
    add_zero, zero_add]
  rw [Real.sin_sub, Complex.cos_arg hT, Complex.sin_arg, Complex.normSq_eq_norm_sq]
  field_simp
  ring

/-- G08. Keep an explicit common sin(2ψ-arg T)>0 margin and Gaussian rate. [RW26, p. 7]. -/
theorem bent_gaussian_margin (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ ψ : ℝ) (hT : 0 < g1T M τ₀) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ ρ σ a : ℝ, 0 < ρ ∧ 0 < σ ∧ 0 < a ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        τ ∈ modularPhiDomain M ∧
          σ ≤ Real.sin (2 * ψ - (etaDenom M τ).arg) ∧
          a ≤ gaussianCoefficient M τ ψ := by
  let s : ℂ → ℝ := fun τ => Real.sin (2 * ψ - (etaDenom M τ).arg)
  let g : ℂ → ℝ := fun τ => gaussianCoefficient M τ ψ
  have harg : ContinuousAt (fun τ : ℂ => (etaDenom M τ).arg) (τ₀ : ℂ) :=
    (Complex.continuousAt_arg (Or.inl (by simpa [denom_real] using hT))).comp
      (denom_continuous M).continuousAt
  have hsc : ContinuousAt s (τ₀ : ℂ) :=
    Real.continuous_sin.continuousAt.comp (continuousAt_const.sub harg)
  have hnorm : ‖etaDenom M (τ₀ : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (denom_real_ne_zero M τ₀ hT)
  have hgc : ContinuousAt g (τ₀ : ℂ) :=
    (continuousAt_const.div (denom_continuous M).continuousAt.norm hnorm).mul hsc
  have hs : 0 < s (τ₀ : ℂ) := by
    dsimp [s]
    rw [denom_real, Complex.arg_ofReal_of_nonneg hT.le, sub_zero]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hg : 0 < g (τ₀ : ℂ) := by
    change 0 < Real.pi * (M 1 0 : ℝ) / ‖etaDenom M (τ₀ : ℂ)‖ * s (τ₀ : ℂ)
    exact mul_pos (div_pos (mul_pos Real.pi_pos hc) (norm_pos_iff.mpr
      (denom_real_ne_zero M τ₀ hT))) hs
  obtain ⟨ρ, hρ, hmargin⟩ := disk_of_eventually τ₀
    (fun τ => τ ∈ modularPhiDomain M ∧ s (τ₀ : ℂ) / 2 ≤ s τ ∧ g (τ₀ : ℂ) / 2 ≤ g τ)
    (by
      filter_upwards [domain_eventually M τ₀ hT,
        positive_margin_eventually hsc hs, positive_margin_eventually hgc hg]
        with τ hdom hsτ hgτ
      exact ⟨hdom.1, hsτ, hgτ⟩)
  exact ⟨ρ, s (τ₀ : ℂ) / 2, g (τ₀ : ℂ) / 2, hρ, half_pos hs, half_pos hg, hmargin⟩

/-- G09. Bounded vertical strips eventually lie in one closed upper sector. [RW26, p. 7, Lemma 1].
-/
theorem upper_strip_sector (a b : ℝ) :
    ∃ α R : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < R ∧
      ∀ x ∈ Icc a b, ∀ t : ℝ, R ≤ t →
        g1VerticalPoint x t ∈ ModularSector.upperSector α (t / 2) := by
  let A := |a| + |b| + 1
  obtain ⟨R, hR, hsector⟩ := shifted_ray_sector A (by dsimp [A]; positivity)
    Complex.I Complex.norm_I (by rw [Complex.arg_I]; constructor <;> linarith [Real.pi_pos])
  refine ⟨Real.pi / 8, R, by positivity, by linarith [Real.pi_pos], hR, ?_⟩
  intro x hx t ht
  have hnorm : ‖(x : ℂ)‖ ≤ A := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hbound := interval_abs_bound a b x hx
    dsimp [A]
    linarith
  simpa only [g1VerticalPoint, add_comm] using hsector (x : ℂ) hnorm t ht

/-- G10. The fixed bent lower ray stays in a common reflected sector. [RW26, p. 7, Lemma 1]. -/
theorem bent_lower_sector (a b ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ α R : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < R ∧
      ∀ x ∈ Icc a b, ∀ r : ℝ, R ≤ r →
        -g1BentLowerPoint x ψ r ∈ ModularSector.upperSector α (r / 2) := by
  let A := |a| + |b| + 1
  have hdir : Real.pi / 4 ≤ (-g1LowerDirection ψ).arg ∧
      (-g1LowerDirection ψ).arg ≤ Real.pi - Real.pi / 4 := by
    rw [reflected_lower_direction_arg ψ hψ hψ']
    constructor <;> linarith [Real.pi_pos]
  obtain ⟨R, hR, hsector⟩ := shifted_ray_sector A (by dsimp [A]; positivity)
    (-g1LowerDirection ψ) (reflected_lower_direction_norm ψ) hdir
  refine ⟨Real.pi / 8, R, by positivity, by linarith [Real.pi_pos], hR, ?_⟩
  intro x hx r hr
  have hnorm : ‖-(x : ℂ) + Complex.I‖ ≤ A := by
    calc
      ‖-(x : ℂ) + Complex.I‖ ≤ ‖-(x : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = |x| + 1 := by simp
      _ ≤ A := by
        have hbound := interval_abs_bound a b x hx
        dsimp [A]
        linarith
  have h := hsector (-(x : ℂ) + Complex.I) hnorm r hr
  have heq : (r : ℂ) * -g1LowerDirection ψ + (-(x : ℂ) + Complex.I) =
      -g1BentLowerPoint x ψ r := by
    unfold g1BentLowerPoint
    ring
  rwa [heq] at h

/-- G11. Direct finite-component specialization of the existing proved
`bilateral_uniform_asymptotics`; constants precede τ,m,z and both indices. [RW26, p. 6, p. 7]. -/
theorem finite_sector_estimates (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (n p : ℤ) (τ₀ α : ℝ) (hT : 0 < g1T M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, τ ∈ modularPhiDomain M ∧
        ∀ i ∈ indexFamily F n p,
          (∀ z ∈ ModularSector.upperSector α R,
            modularPhi M i.1 i.2 z τ ≠ 0 ∧
              ModularSector.upperError M i z τ ≤ C * Real.exp (-k * ‖z‖)) ∧
          (∀ z : ℂ, -z ∈ ModularSector.upperSector α R →
            modularPhi M i.1 i.2 z τ ≠ 0 ∧
              ModularSector.lowerError M i z τ ≤ C * Real.exp (-k * ‖z‖)) := by
  obtain ⟨ρ, C, k, R, hρ, hC, hk, hR, _, _, hest⟩ :=
    ModularSector.bilateral_uniform_asymptotics M hM (indexFamily F n p)
      τ₀ α hT hα hα'
  exact ⟨ρ, C, k, R, hρ, hC, hk, hR, hest⟩

/-- G12. Actual shifted ratio, normalized below by the existing reflection factors. Both errors
include the inverse, with one full-disk rate. [RW26, p. 6, p. 7]. The proof uses
`bounded_shift_ratio_decay`.
-/
theorem finite_shift_ratio_estimates (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (n p : ℤ) (τ₀ α : ℝ) (y : ℂ) (hT : 0 < g1T M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
        (∀ z ∈ ModularSector.upperSector α R,
          let q := modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ
          ‖q - 1‖ + ‖q⁻¹ - 1‖ ≤ C * Real.exp (-k * ‖z‖)) ∧
        (∀ z : ℂ, -z ∈ ModularSector.upperSector α R →
          let q := modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ
          let a := modularReflectionFactor M (m + 1) n z τ /
            modularReflectionFactor M (m + p) n (z + y) τ
          ‖q / a - 1‖ + ‖a * q⁻¹ - 1‖ ≤ C * Real.exp (-k * ‖z‖)) := by
  obtain ⟨ρ, C, k, R, hρ, hC, hk, hR, _, _, hest⟩ :=
    ModularSector.bounded_shift_ratio_decay M hM (indexFamily F n p)
      τ₀ α ‖y‖ hT hα hα' (norm_nonneg y)
  refine ⟨ρ, C, k, R, hρ, hC, hk, hR, ?_⟩
  intro τ hτ m hm
  have hi : (m + 1, n) ∈ indexFamily F n p :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have hj : (m + p, n) ∈ indexFamily F n p :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  exact hest τ hτ (m + 1, n) hi (m + p, n) hj y le_rfl

#check @ModularSector.bilateral_uniform_asymptotics
#check @ModularSector.bounded_shift_ratio_decay
#check @G1RatioTail.real_window_casts
#print singleData
#print gaussianCoefficient
#check @ratio_window_margin

end SICLean.L4.G1BilateralGeometry
