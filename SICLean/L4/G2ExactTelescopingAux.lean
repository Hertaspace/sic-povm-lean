import SICLean.L4.G2KernelConvergence

set_option autoImplicit false

/-!
Generic almost-everywhere and integral algebra for the exact G2 telescope. The circle statements use
Lebesgue measure on the whole real parameter line.
-/

noncomputable section

open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2ExactTelescopingAux

/-- The exceptional parameters are the countable set of integer multiples of π. -/
theorem sin_ne_zero_ae : ∀ᵐ θ : ℝ ∂volume, Real.sin θ ≠ 0 := by
  have hc : {θ : ℝ | Real.sin θ = 0}.Countable := by
    apply (Set.countable_range (fun n : ℤ => (n : ℝ) * Real.pi)).mono
    intro θ hθ
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hθ
    exact ⟨n, hn⟩
  exact hc.ae_notMem volume

theorem vertical_pullback_ae_of_off_real (f g : ℂ → ℂ) (A : ℂ)
    (hfg : ∀ z : ℂ, z.im ≠ 0 → f z = A * g z) (x : ℝ) :
    g1VerticalPullback f x =ᵐ[volume] fun t => A * g1VerticalPullback g x t := by
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with t ht
  have him : (g1VerticalPoint x t).im ≠ 0 := by
    simpa [g1VerticalPoint] using ht
  simp only [g1VerticalPullback, hfg _ him, mul_assoc]

theorem circle_pullback_ae_of_off_real (f g : ℂ → ℂ) (A : ℂ)
    (hfg : ∀ z : ℂ, z.im ≠ 0 → f z = A * g z) (r ρ : ℝ) (hρ : 0 < ρ) :
    g1CirclePullback f r ρ =ᵐ[volume] fun θ => A * g1CirclePullback g r ρ θ := by
  filter_upwards [sin_ne_zero_ae] with θ hθ
  have him : (circleMap (r : ℂ) ρ θ).im ≠ 0 := by
    simpa [circleMap] using mul_ne_zero (ne_of_gt hρ) hθ
  simp only [g1CirclePullback, hfg _ him, mul_assoc]

theorem vertical_pullback_sub (f g : ℂ → ℂ) (x t : ℝ) :
    g1VerticalPullback (fun z => f z - g z) x t =
      g1VerticalPullback f x t - g1VerticalPullback g x t := by
  exact sub_mul _ _ _

theorem circle_pullback_sub (f g : ℂ → ℂ) (r ρ θ : ℝ) :
    g1CirclePullback (fun z => f z - g z) r ρ θ =
      g1CirclePullback f r ρ θ - g1CirclePullback g r ρ θ := by
  exact sub_mul _ _ _

theorem vertical_pullback_const_mul (f : ℂ → ℂ) (A : ℂ) (x t : ℝ) :
    g1VerticalPullback (fun z => A * f z) x t =
      A * g1VerticalPullback f x t := by
  exact mul_assoc _ _ _

theorem circle_pullback_const_mul (f : ℂ → ℂ) (A : ℂ) (r ρ θ : ℝ) :
    g1CirclePullback (fun z => A * f z) r ρ θ =
      A * g1CirclePullback f r ρ θ := by
  exact mul_assoc _ _ _

theorem vertical_pullback_sub_fun (f g : ℂ → ℂ) (x : ℝ) :
    g1VerticalPullback (fun z => f z - g z) x =
      g1VerticalPullback f x - g1VerticalPullback g x := by
  funext t
  exact vertical_pullback_sub f g x t

theorem circle_pullback_sub_fun (f g : ℂ → ℂ) (r ρ : ℝ) :
    g1CirclePullback (fun z => f z - g z) r ρ =
      fun θ => g1CirclePullback f r ρ θ - g1CirclePullback g r ρ θ := by
  funext θ
  exact circle_pullback_sub f g r ρ θ

theorem vertical_pullback_const_mul_fun (f : ℂ → ℂ) (A : ℂ) (x : ℝ) :
    g1VerticalPullback (fun z => A * f z) x =
      fun t => A * g1VerticalPullback f x t := by
  funext t
  exact vertical_pullback_const_mul f A x t

theorem circle_pullback_const_mul_fun (f : ℂ → ℂ) (A : ℂ) (r ρ : ℝ) :
    g1CirclePullback (fun z => A * f z) r ρ =
      fun θ => A * g1CirclePullback f r ρ θ := by
  funext θ
  exact circle_pullback_const_mul f A r ρ θ

theorem chain_integrable_sub (D : G1VerticalChain) (f g : ℂ → ℂ)
    (hf : G1ChainIntegrable D f) (hg : G1ChainIntegrable D g) :
    G1ChainIntegrable D (fun z => f z - g z) := by
  constructor
  · rw [vertical_pullback_sub_fun]
    exact hf.1.sub hg.1
  · intro r hr
    rw [circle_pullback_sub_fun]
    exact (hf.2 r hr).sub (hg.2 r hr)

theorem chain_integrable_const_mul (D : G1VerticalChain) (f : ℂ → ℂ) (A : ℂ)
    (hf : G1ChainIntegrable D f) :
    G1ChainIntegrable D (fun z => A * f z) := by
  constructor
  · rw [vertical_pullback_const_mul_fun]
    exact hf.1.const_mul A
  · intro r hr
    rw [circle_pullback_const_mul_fun]
    exact (hf.2 r hr).const_mul A

theorem chain_integral_sub (D : G1VerticalChain) (f g : ℂ → ℂ)
    (hf : G1ChainIntegrable D f) (hg : G1ChainIntegrable D g) :
    g1ChainIntegral D (fun z => f z - g z) =
      g1ChainIntegral D f - g1ChainIntegral D g := by
  unfold g1ChainIntegral
  simp_rw [vertical_pullback_sub, circle_pullback_sub]
  rw [MeasureTheory.integral_sub hf.1 hg.1]
  have hs : (∑ r ∈ D.centers, ∫ θ : ℝ in 0..(2 * Real.pi),
      g1CirclePullback f r (D.radius r) θ - g1CirclePullback g r (D.radius r) θ) =
      ∑ r ∈ D.centers, ((∫ θ : ℝ in 0..(2 * Real.pi),
        g1CirclePullback f r (D.radius r) θ) -
      ∫ θ : ℝ in 0..(2 * Real.pi), g1CirclePullback g r (D.radius r) θ) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact intervalIntegral.integral_sub (hf.2 r hr) (hg.2 r hr)
  rw [hs, Finset.sum_sub_distrib]
  ring

/-- Homogeneity holds for the total integral, with no integrability premise. -/
theorem chain_integral_const_mul (D : G1VerticalChain) (f : ℂ → ℂ) (A : ℂ) :
    g1ChainIntegral D (fun z => A * f z) = A * g1ChainIntegral D f := by
  unfold g1ChainIntegral
  simp_rw [vertical_pullback_const_mul, circle_pullback_const_mul]
  simp only [MeasureTheory.integral_const_mul, intervalIntegral.integral_const_mul,
    ← Finset.mul_sum, mul_add]

/-- Full-line AE equality is sufficient for all interval integrals in a chain. -/
theorem chain_integral_congr_ae (D : G1VerticalChain) (f g : ℂ → ℂ)
    (hv : g1VerticalPullback f D.crossing =ᵐ[volume]
      g1VerticalPullback g D.crossing)
    (hc : ∀ r ∈ D.centers, g1CirclePullback f r (D.radius r) =ᵐ[volume]
      g1CirclePullback g r (D.radius r)) :
    g1ChainIntegral D f = g1ChainIntegral D g := by
  unfold g1ChainIntegral
  congr 1
  · exact MeasureTheory.integral_congr_ae hv
  · apply Finset.sum_congr rfl
    intro r hr
    exact intervalIntegral.integral_congr_ae ((hc r hr).mono fun θ hθ _ => hθ)

theorem chain_integral_eq_const_mul_of_pullbacks_ae (D : G1VerticalChain)
    (f g : ℂ → ℂ) (A : ℂ)
    (hv : g1VerticalPullback f D.crossing =ᵐ[volume]
      fun t => A * g1VerticalPullback g D.crossing t)
    (hc : ∀ r ∈ D.centers, g1CirclePullback f r (D.radius r) =ᵐ[volume]
      fun θ => A * g1CirclePullback g r (D.radius r) θ) :
    g1ChainIntegral D f = A * g1ChainIntegral D g := by
  calc
    g1ChainIntegral D f = g1ChainIntegral D (fun z => A * g z) := by
      apply chain_integral_congr_ae
      · simpa only [vertical_pullback_const_mul_fun] using hv
      · intro r hr
        simpa only [circle_pullback_const_mul_fun] using hc r hr
    _ = A * g1ChainIntegral D g := chain_integral_const_mul D g A

theorem chain_integral_eq_const_mul_of_off_real (D : G1VerticalChain)
    (f g : ℂ → ℂ) (A : ℂ)
    (hfg : ∀ z : ℂ, z.im ≠ 0 → f z = A * g z)
    (hρ : ∀ r ∈ D.centers, 0 < D.radius r) :
    g1ChainIntegral D f = A * g1ChainIntegral D g := by
  apply chain_integral_eq_const_mul_of_pullbacks_ae
  · exact vertical_pullback_ae_of_off_real f g A hfg D.crossing
  · intro r hr
    exact circle_pullback_ae_of_off_real f g A hfg r (D.radius r) (hρ r hr)

theorem vertical_pullback_translate (f : ℂ → ℂ) (q x t : ℝ) :
    g1VerticalPullback f (x + q) t =
      g1VerticalPullback (fun z => f (z + (q : ℂ))) x t := by
  have hp : g1VerticalPoint (x + q) t = g1VerticalPoint x t + (q : ℂ) := by
    simp only [g1VerticalPoint, Complex.ofReal_add]
    ring
  simp only [g1VerticalPullback, hp]

theorem circle_pullback_translate (f : ℂ → ℂ) (q r ρ θ : ℝ) :
    g1CirclePullback f (r + q) ρ θ =
      g1CirclePullback (fun z => f (z + (q : ℂ))) r ρ θ := by
  have hp : circleMap ((r + q : ℝ) : ℂ) ρ θ =
      circleMap (r : ℂ) ρ θ + (q : ℂ) := by
    simp only [circleMap, Complex.ofReal_add]
    ring
  have hj : circleMap ((r + q : ℝ) : ℂ) ρ θ - ((r + q : ℝ) : ℂ) =
      circleMap (r : ℂ) ρ θ - (r : ℂ) := by
    simp [circleMap]
  unfold g1CirclePullback
  rw [hj, hp]

theorem vertical_pullback_translate_fun (f : ℂ → ℂ) (q x : ℝ) :
    g1VerticalPullback f (x + q) =
      g1VerticalPullback (fun z => f (z + (q : ℂ))) x := by
  funext t
  exact vertical_pullback_translate f q x t

theorem circle_pullback_translate_fun (f : ℂ → ℂ) (q r ρ : ℝ) :
    g1CirclePullback f (r + q) ρ =
      g1CirclePullback (fun z => f (z + (q : ℂ))) r ρ := by
  funext θ
  exact circle_pullback_translate f q r ρ θ

/-- Translating all chain data is equivalent to translating the integrand's input. -/
theorem chain_integrable_translate_iff (D : G1VerticalChain) (q : ℝ) (f : ℂ → ℂ) :
    G1ChainIntegrable
      { crossing := D.crossing + q
        centers := D.centers.image (fun r => r + q)
        radius := fun r => D.radius (r - q) } f ↔
      G1ChainIntegrable D (fun z => f (z + (q : ℂ))) := by
  unfold G1ChainIntegrable
  dsimp only
  rw [vertical_pullback_translate_fun]
  constructor
  · rintro ⟨hv, hc⟩
    refine ⟨hv, ?_⟩
    intro r hr
    have hcircle := hc (r + q) (Finset.mem_image_of_mem (fun s => s + q) hr)
    simpa only [add_sub_cancel_right, circle_pullback_translate_fun] using hcircle
  · rintro ⟨hv, hc⟩
    refine ⟨hv, ?_⟩
    intro r hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    simpa only [add_sub_cancel_right, circle_pullback_translate_fun] using hc s hs

end SICLean.L4.G2ExactTelescopingAux
