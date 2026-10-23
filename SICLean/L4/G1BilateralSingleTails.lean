import SICLean.L4.G1BilateralSingleTailsAux

set_option autoImplicit false

/-!
# Single-function bent chains on a full disk

This module is independent of the ratio separator construction. The bent
chain, direction and pullbacks are exactly the G1 interface. No vertical nonreal lower tail and no
extra upper bound on s are imposed.

[RW26, p. 6, Prop. 1--2, (19), p. 7, Lemma 1, (22), pp. 28--29, Appendix A.2]. Full-disk conclusions
are formalized here. Integral limits and local parameter analyticity use the fixed chain; no
identification with a meromorphic RHS is asserted.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1BilateralSingleTails

open G1BilateralGeometry G1BilateralSingleTailsAux

/-- Exact reflected polynomial plus the existing E_m; no new phase choice. -/
def lowerPhase (M : SL(2, ℤ)) (τ w z : ℂ) (n h ell m : ℤ) : ℂ :=
  modularReflectionPolynomial M (m + 1) n z τ + g1Exponent M τ w z n h ell m

/-- Explicit quadratic coefficient after z=(x-i)+r*dψ. -/
def bentQuadratic (M : SL(2, ℤ)) (τ : ℂ) (ψ : ℝ) : ℂ :=
  -((M 1 0 : ℂ) / (2 * etaDenom M τ)) * g1LowerDirection ψ ^ 2

/-- Explicit linear coefficient in the same polynomial, with all integer indices retained. -/
def bentLinear (M : SL(2, ℤ)) (τ w : ℂ) (x ψ : ℝ) (n h ell m : ℤ) : ℂ :=
  (-((M 1 0 : ℂ) * ((x : ℂ) - Complex.I) / etaDenom M τ) -
    (m : ℂ) - 1 / 2 + (2 * (n : ℂ) - 1) / (2 * etaDenom M τ) +
    G1RatioTail.complexS M τ w h ell / etaDenom M τ) * g1LowerDirection ψ

/-- Concrete full upper-ray majorant (only used for t≥-1). -/
def upperMajorant (C κ R t : ℝ) : ℝ :=
  if t ≤ R then C else C * Real.exp (-κ * t)

/-- Concrete full bent-lower-ray majorant (only used for r≥0). -/
def lowerMajorant (C a B R r : ℝ) : ℝ :=
  if r ≤ R then C else C * Real.exp (-a * r ^ 2 + B * r)

/-- T01. Exact arithmetic expansion of the existing lower phase. [RW26, p. 6, Prop. 1, p. 7]. -/
theorem bent_phase_quadratic (M : SL(2, ℤ)) (τ w : ℂ)
    (x ψ r : ℝ) (n h ell m : ℤ) (hT : etaDenom M τ ≠ 0) :
    lowerPhase M τ w (g1BentLowerPoint x ψ r) n h ell m =
      bentQuadratic M τ ψ * (r : ℂ) ^ 2 +
        bentLinear M τ w x ψ n h ell m * (r : ℂ) +
        lowerPhase M τ w ((x : ℂ) - Complex.I) n h ell m := by
  unfold lowerPhase bentQuadratic bentLinear g1BentLowerPoint
    modularReflectionPolynomial g1Exponent G1RatioTail.complexS
  push_cast
  field_simp
  ring

/-- T02. Uniform Gaussian model, including the actual μ and integer phase. The same positive a is
valid throughout the full disk, before m,r vary. [RW26, p. 6, p. 7]. -/
theorem reflection_gaussian_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ ρ C a B : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < a ∧ 0 < B ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F, ∀ r : ℝ, 0 ≤ r →
        let z := g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r
        ‖modularReflectionFactor M (m + 1) n z τ *
          e (g1Exponent M τ (w : ℂ) z n h ell m)‖ ≤
            C * Real.exp (-a * r ^ 2 + B * r) := by
  obtain ⟨ρ, σ, a, hρ, hσ, ha, hgauss⟩ :=
    bent_gaussian_margin M hM τ₀ ψ hT hψ hψ'
  have hden : ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, etaDenom M τ ≠ 0 :=
    fun τ hτ => Complex.slitPlane_ne_zero (hgauss τ hτ).1
  have hcompact : IsCompact (ModularSector.parameterDisk τ₀ ρ) := isCompact_closedBall _ _
  obtain ⟨B, hB, hBl⟩ := finite_continuous_bound F _ hcompact
    (fun m τ => 2 * (Real.pi : ℂ) * Complex.I *
      bentLinear M τ (w : ℂ) (g1BentCrossing M τ₀ δ n m) ψ n h ell m) (by
        intro m hm τ hτ
        apply ContinuousAt.continuousWithinAt
        have hd := hden τ hτ
        unfold bentLinear G1RatioTail.complexS etaDenom at *
        fun_prop (disch := simp_all))
  obtain ⟨D, hD, hDc⟩ := finite_continuous_bound F _ hcompact
    (fun m τ => 2 * (Real.pi : ℂ) * Complex.I *
      lowerPhase M τ (w : ℂ) ((g1BentCrossing M τ₀ δ n m : ℝ) - Complex.I) n h ell m) (by
        intro m hm
        exact continuousOn_const.mul ((continuousOn_reflectionPolynomial M _ _ _ _ hden).add
          (continuousOn_phase M _ _ _ _ _ _ _ hden)))
  refine ⟨ρ, ‖(etaMultiplier M) ^ (-2 : ℤ)‖ * Real.exp D, a, B, hρ,
    mul_pos (norm_pos_iff.mpr (zpow_ne_zero _ (etaMultiplier_ne_zero M hM))) (Real.exp_pos D),
    ha, hB, ?_⟩
  intro τ hτ m hm r hr
  dsimp only
  rw [norm_reflection_times_e]
  change _ * Real.exp ((2 * (Real.pi : ℂ) * Complex.I *
      lowerPhase M τ (w : ℂ) (g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r) n h ell m).re) ≤ _
  rw [bent_phase_quadratic M τ (w : ℂ) (g1BentCrossing M τ₀ δ n m) ψ r n h ell m (hden τ hτ)]
  have hexpand : (2 * (Real.pi : ℂ) * Complex.I *
      (bentQuadratic M τ ψ * (r : ℂ)^2 +
        bentLinear M τ (w : ℂ) (g1BentCrossing M τ₀ δ n m) ψ n h ell m * (r : ℂ) +
        lowerPhase M τ (w : ℂ) ((g1BentCrossing M τ₀ δ n m : ℝ) - Complex.I) n h ell m)).re =
      -gaussianCoefficient M τ ψ * r^2 +
        (2 * (Real.pi : ℂ) * Complex.I * bentLinear M τ (w : ℂ)
          (g1BentCrossing M τ₀ δ n m) ψ n h ell m).re * r +
        (2 * (Real.pi : ℂ) * Complex.I * lowerPhase M τ (w : ℂ)
          ((g1BentCrossing M τ₀ δ n m : ℝ) - Complex.I) n h ell m).re := by
    have hq := gaussian_coefficient_exact M τ ψ (hden τ hτ)
    change (2 * (Real.pi : ℂ) * Complex.I * bentQuadratic M τ ψ).re = _ at hq
    calc
      _ = (2 * (Real.pi : ℂ) * Complex.I * bentQuadratic M τ ψ).re * r^2 +
          (2 * (Real.pi : ℂ) * Complex.I * bentLinear M τ (w : ℂ)
            (g1BentCrossing M τ₀ δ n m) ψ n h ell m).re * r +
          (2 * (Real.pi : ℂ) * Complex.I * lowerPhase M τ (w : ℂ)
            ((g1BentCrossing M τ₀ δ n m : ℝ) - Complex.I) n h ell m).re := by
        rw [show 2 * (Real.pi : ℂ) * Complex.I *
          (bentQuadratic M τ ψ * (r : ℂ)^2 +
            bentLinear M τ (w : ℂ) (g1BentCrossing M τ₀ δ n m) ψ n h ell m * (r : ℂ) +
            lowerPhase M τ (w : ℂ) ((g1BentCrossing M τ₀ δ n m : ℝ) - Complex.I) n h ell m) =
          (2 * (Real.pi : ℂ) * Complex.I * bentQuadratic M τ ψ) * ((r^2 : ℝ) : ℂ) +
          (2 * (Real.pi : ℂ) * Complex.I * bentLinear M τ (w : ℂ)
            (g1BentCrossing M τ₀ δ n m) ψ n h ell m) * (r : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * lowerPhase M τ (w : ℂ)
            ((g1BentCrossing M τ₀ δ n m : ℝ) - Complex.I) n h ell m by push_cast; ring]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      _ = _ := by rw [hq]
  rw [hexpand]
  have hlin := (Complex.re_le_norm _).trans (hBl m hm τ hτ)
  have hconst := (Complex.re_le_norm _).trans (hDc m hm τ hτ)
  have hcoef := (hgauss τ hτ).2.2
  have hbexp : -gaussianCoefficient M τ ψ * r^2 +
      (2 * (Real.pi : ℂ) * Complex.I * bentLinear M τ (w : ℂ)
        (g1BentCrossing M τ₀ δ n m) ψ n h ell m).re * r +
      (2 * (Real.pi : ℂ) * Complex.I * lowerPhase M τ (w : ℂ)
        ((g1BentCrossing M τ₀ δ n m : ℝ) - Complex.I) n h ell m).re ≤
      D + (-a*r^2+B*r) := by
    nlinarith [mul_le_mul_of_nonneg_right hlin hr,
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg r)]
  calc
    _ ≤ ‖(etaMultiplier M) ^ (-2 : ℤ)‖ * Real.exp (D + (-a*r^2+B*r)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbexp) (norm_nonneg _)
    _ = _ := by rw [Real.exp_add]; ring

/-- T03. Full-disk Φ normalization along the actual bent rays; Φ and its inverse are controlled,
with one finite index family. [RW26, p. 6, p. 7]. -/
theorem bent_normalized_tail (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ δ ψ : ℝ) (n : ℤ) (hT : 0 < g1T M τ₀)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F, ∀ r : ℝ, R ≤ r →
        let z := g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r
        modularPhi M (m + 1) n z τ ≠ 0 ∧
          ModularSector.lowerError M (m + 1, n) z τ ≤ C * Real.exp (-k * r) := by
  obtain ⟨A, hA, hcross⟩ := G1BilateralSingleTailsAux.finite_real_bounds F
    (fun m => g1BentCrossing M τ₀ δ n m)
  obtain ⟨α, R₀, hα, hα', hR₀, hsector⟩ := bent_lower_sector (-A) A ψ hψ hψ'
  obtain ⟨ρ, C, k, R₁, hρ, hC, hk, hR₁, hest⟩ :=
    finite_sector_estimates M hM F n 0 τ₀ α hT hα hα'
  refine ⟨ρ, C, k / 2, max R₀ (2 * R₁), hρ, hC, by positivity,
    lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro τ hτ m hm r hr
  have hs := hsector _ (hcross m hm) r ((le_max_left _ _).trans hr)
  have hr₁ : R₁ ≤ r / 2 := by have := (le_max_right R₀ (2 * R₁)).trans hr; linarith
  have hi : (m + 1, n) ∈ indexFamily F n 0 :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  obtain ⟨hne, he⟩ := ((hest τ hτ).2 (m + 1, n) hi).2 _
    (ModularSector.upperSector_antitone le_rfl hr₁ hs)
  refine ⟨hne, he.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have hz : r / 2 ≤ ‖g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r‖ := by
    simpa only [norm_neg] using hs.1
  nlinarith

/-- T04. The fixed vertical upper pullback has common exponential decay. [RW26, p. 7]. -/
theorem uniform_upper_tail (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ w δ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F, ∀ t : ℝ, R ≤ t →
        ‖g1VerticalPullback (singleKernel M τ (w : ℂ) n h ell m)
          (g1BentCrossing M τ₀ δ n m) t‖ ≤ C * Real.exp (-κ * t) := by
  obtain ⟨A, hA, hcross⟩ := finite_real_bounds F (g1BentCrossing M τ₀ δ n)
  obtain ⟨α, Rg, hα, hα', hRg, hsector⟩ := upper_strip_sector (-A) A
  obtain ⟨ρw, κ, hρw, hκ, hwindow⟩ := single_window_margin M hM τ₀ w h ell hT hs
  obtain ⟨ρs, Cs, ks, Rs, hρs, hCs, hks, hRs, hest⟩ :=
    finite_sector_estimates M hM F n 0 τ₀ α hT hα hα'
  let ρ := min ρw ρs
  have hρ : 0 < ρ := lt_min hρw hρs
  have hsubw : ModularSector.parameterDisk τ₀ ρ ⊆ ModularSector.parameterDisk τ₀ ρw :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hsubs : ModularSector.parameterDisk τ₀ ρ ⊆ ModularSector.parameterDisk τ₀ ρs :=
    Metric.closedBall_subset_closedBall (min_le_right _ _)
  have hden : ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, etaDenom M τ ≠ 0 :=
    fun τ hτ => Complex.slitPlane_ne_zero (hwindow τ (hsubw hτ)).1
  obtain ⟨D, hD, hDc⟩ := finite_continuous_bound F _ (isCompact_closedBall _ _)
    (fun m τ => 2 * (Real.pi : ℂ) * Complex.I *
      g1Exponent M τ (w : ℂ) (g1BentCrossing M τ₀ δ n m : ℝ) n h ell m)
    (by
      intro m hm
      exact continuousOn_const.mul (continuousOn_phase M _ _ _ _ _ _ _ hden))
  refine ⟨ρ, (Cs+1) * Real.exp D, κ, max Rg (max (2*Rs) 1), hρ,
    mul_pos (by linarith) (Real.exp_pos D), hκ,
    lt_of_lt_of_le hRg (le_max_left _ _), ?_⟩
  intro τ hτ m hm t ht
  have htg : Rg ≤ t := (le_max_left _ _).trans ht
  have hts : 2*Rs ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht0 : 0 ≤ t := by linarith
  let z := g1VerticalPoint (g1BentCrossing M τ₀ δ n m) t
  have hz : z ∈ ModularSector.upperSector α Rs := by
    have hg := hsector _ (hcross m hm) t htg
    exact ⟨le_trans (by linarith) hg.1, hg.2⟩
  have hi : (m+1,n) ∈ indexFamily F n 0 := by
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm)
  have he := ((hest τ (hsubs hτ)).2 _ hi).1 z hz
  have hphi : ‖modularPhi M (m+1) n z τ‖ ≤ Cs+1 := by
    have hnorm : ‖modularPhi M (m+1) n z τ‖ ≤
        ‖modularPhi M (m+1) n z τ - 1‖ + 1 := by
      simpa using norm_sub_norm_le (modularPhi M (m+1) n z τ) (1 : ℂ)
    have hfirst : ‖modularPhi M (m+1) n z τ - 1‖ ≤
        ModularSector.upperError M (m+1,n) z τ :=
      le_add_of_nonneg_right (norm_nonneg _)
    have hexp : Real.exp (-ks * ‖z‖) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg z])
    have hsmall := mul_le_mul_of_nonneg_left hexp hCs.le
    linarith [he.2]
  have hc := (Complex.re_le_norm _).trans (hDc m hm τ hτ)
  have hw := (hwindow τ (hsubw hτ)).2.2
  have hphase :
      -(2 * Real.pi * (G1RatioTail.complexS M τ (w : ℂ) h ell / etaDenom M τ).re) * t +
        (2 * (Real.pi : ℂ) * Complex.I *
          g1Exponent M τ (w : ℂ) (g1BentCrossing M τ₀ δ n m : ℝ) n h ell m).re ≤
        D + (-κ * t) := by
    nlinarith [mul_le_mul_of_nonneg_right hw ht0]
  simp only [g1VerticalPullback, norm_mul, Complex.norm_I, mul_one]
  rw [singleKernel_eq, norm_mul, norm_vertical_e M τ (w : ℂ) _ t n h ell m (hden τ hτ)]
  calc
    _ ≤ (Cs+1) * Real.exp (D + (-κ*t)) :=
      mul_le_mul hphi (Real.exp_le_exp.mpr hphase) (Real.exp_pos _).le (by linarith)
    _ = _ := by rw [Real.exp_add]; ring

/-- T05. Gaussian lower pullback, with a common positive angular margin. There is no s-window on
this tail. [RW26, p. 7]. The all-τ quantifier includes negative imaginary parts. -/
theorem uniform_bent_lower_tail (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ ρ C a B R σ : ℝ,
      0 < ρ ∧ 0 < C ∧ 0 < a ∧ 0 < B ∧ 0 < R ∧ 0 < σ ∧
        ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
          σ ≤ Real.sin (2 * ψ - (etaDenom M τ).arg) ∧
          a ≤ gaussianCoefficient M τ ψ ∧
          ∀ m ∈ F, ∀ r : ℝ, R ≤ r →
            ‖g1BentLowerPullback (singleKernel M τ (w : ℂ) n h ell m)
              (g1BentCrossing M τ₀ δ n m) ψ r‖ ≤
                C * Real.exp (-a * r ^ 2 + B * r) := by
  obtain ⟨ρg, σ, ag, hρg, hσ, hag, hmargin⟩ :=
    bent_gaussian_margin M hM τ₀ ψ hT hψ hψ'
  obtain ⟨ρn, Cn, k, R, hρn, hCn, hk, hR, hnorm⟩ :=
    bent_normalized_tail M hM F τ₀ δ ψ n hT hψ hψ'
  obtain ⟨ρb, Cb, ab, B, hρb, hCb, hab, hB, hbound⟩ :=
    reflection_gaussian_bound M hM F τ₀ w δ ψ n h ell hT hψ hψ'
  let a := min ag ab
  refine ⟨min ρg (min ρn ρb), (Cn + 1) * Cb, a, B, R, σ,
    lt_min hρg (lt_min hρn hρb), by positivity,
    lt_min hag hab, hB, hR, hσ, ?_⟩
  intro τ hτ
  have hτg : τ ∈ ModularSector.parameterDisk τ₀ ρg :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hτ
  have hτn : τ ∈ ModularSector.parameterDisk τ₀ ρn :=
    Metric.closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _)) hτ
  have hτb : τ ∈ ModularSector.parameterDisk τ₀ ρb :=
    Metric.closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_right _ _)) hτ
  obtain ⟨hdom, hs, hgauss⟩ := hmargin τ hτg
  refine ⟨hs, (min_le_left ag ab).trans hgauss, ?_⟩
  intro m hm r hr
  let z := g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r
  let A := modularReflectionFactor M (m + 1) n z τ
  have hAn : A ≠ 0 := (ModularSector.reflectionFactor_joint_unit M hM
    (m + 1) n z τ hdom).2
  have hrel : ‖modularPhi M (m + 1) n z τ / A - 1‖ ≤ Cn := by
    have he := (hnorm τ hτn m hm r hr).2
    have hexp : Real.exp (-k * r) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have : 0 ≤ r := hR.le.trans hr; nlinarith)
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans
      (he.trans (by nlinarith))
  have hratio : ‖modularPhi M (m + 1) n z τ / A‖ ≤ Cn + 1 := by
    calc
      _ = ‖(modularPhi M (m + 1) n z τ / A - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖modularPhi M (m + 1) n z τ / A - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ Cn + 1 := by simpa only [norm_one] using add_le_add hrel (le_refl (1 : ℝ))
  have hker : singleKernel M τ (w : ℂ) n h ell m z =
      (modularPhi M (m + 1) n z τ / A) *
        (A * e (g1Exponent M τ (w : ℂ) z n h ell m)) := by
    simp only [singleKernel, ModularCluster.kernel, singleData,
      Bool.false_eq_true, ↓reduceIte, mul_one, ModularCluster.phase, g1Exponent]
    rw [← mul_assoc, div_mul_cancel₀ _ hAn]
  have he := hbound τ hτb m hm r (hR.le.trans hr)
  have hrate : Real.exp (-ab * r ^ 2 + B * r) ≤
      Real.exp (-a * r ^ 2 + B * r) := by
    apply Real.exp_le_exp.mpr
    have := min_le_right ag ab
    nlinarith [sq_nonneg r]
  calc
    _ = ‖singleKernel M τ (w : ℂ) n h ell m z‖ := by
      simp only [g1BentLowerPullback, norm_mul, G1BilateralSingleTailsAux.norm_lower_direction,
        mul_one, z]
    _ = ‖modularPhi M (m + 1) n z τ / A‖ *
        ‖A * e (g1Exponent M τ (w : ℂ) z n h ell m)‖ := by rw [hker, norm_mul]
    _ ≤ (Cn + 1) * (Cb * Real.exp (-ab * r ^ 2 + B * r)) :=
      mul_le_mul hratio he (norm_nonneg _) (by positivity)
    _ ≤ ((Cn + 1) * Cb) * Real.exp (-a * r ^ 2 + B * r) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hrate (show 0 ≤ (Cn + 1) * Cb by positivity)

/-- T06. Actual numerator branches uniformly avoid both entire pieces. For lower τ the far branches
can have Im→-∞: use their cone angle, not the one-sided Im>-1/2 argument. [RW26, p. 6]. -/
theorem bent_branch_gap (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ δ ψ : ℝ) (n : ℤ) (hT : 0 < g1T M τ₀)
    (hδ : 0 < δ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
      ModularSector.parameterDisk τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
        ∀ K J : ℕ, (K, J) ∈ modularPhiPoleLabels M (m + 1) n →
          (∀ t : ℝ, -1 ≤ t →
            ε ≤ dist (g1VerticalPoint (g1BentCrossing M τ₀ δ n m) t)
              (modularPhiPolePoint M (m + 1) n τ K J)) ∧
          (∀ r : ℝ, 0 ≤ r →
            ε ≤ dist (g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r)
              (modularPhiPolePoint M (m + 1) n τ K J)) := by
  have hcψ : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsψ : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ
    (by linarith [Real.pi_pos])
  obtain ⟨ρ, hρ, hgood⟩ := branch_base_neighborhood M F τ₀ δ ψ n hT hδ hcψ hsψ.le
  refine ⟨ρ, δ * Real.cos ψ / 4, hρ, by positivity, ?_, ?_⟩
  · intro τ hτ
    simp only [modularPhiDomain, Set.mem_ofPred_eq, Complex.mem_slitPlane_iff]
    exact Or.inl (hgood τ hτ).1
  · intro τ hτ m hm K J hlabel
    have hg := hgood τ hτ
    have hb := hg.2.2 m hm
    have hr := branch_re_increment M hM τ n m K J hg.1.le
    have hp := branch_projection_increment M hM τ ψ n m K J hg.2.1.le hcψ.le
    constructor
    · intro t ht
      calc
        δ * Real.cos ψ / 4 ≤
            (modularPhiPolePoint M (m + 1) n τ K J).re -
              g1BentCrossing M τ₀ δ n m := by
          nlinarith [Real.cos_le_one ψ]
        _ = (modularPhiPolePoint M (m + 1) n τ K J -
              g1VerticalPoint (g1BentCrossing M τ₀ δ n m) t).re := by
          simp [g1VerticalPoint]
        _ ≤ ‖modularPhiPolePoint M (m + 1) n τ K J -
              g1VerticalPoint (g1BentCrossing M τ₀ δ n m) t‖ := Complex.re_le_norm _
        _ = dist (g1VerticalPoint (g1BentCrossing M τ₀ δ n m) t)
              (modularPhiPolePoint M (m + 1) n τ K J) := by
          rw [dist_eq_norm, norm_sub_rev]
    · intro r hrpos
      have hgap : δ * Real.cos ψ / 2 <
          branchNormalProjection ψ (modularPhiPolePoint M (m + 1) n τ K J) -
            branchNormalProjection ψ (g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r) := by
        rw [branchNormalProjection_bent]
        linarith
      have hnorm := branchNormalProjection_le ψ
        (modularPhiPolePoint M (m + 1) n τ K J -
          g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r) hcψ.le hsψ.le
      rw [branchNormalProjection_sub] at hnorm
      calc
        δ * Real.cos ψ / 4 ≤
            ‖modularPhiPolePoint M (m + 1) n τ K J -
              g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r‖ := by linarith
        _ = dist (g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r)
              (modularPhiPolePoint M (m + 1) n τ K J) := by
          rw [dist_eq_norm, norm_sub_rev]

/-- T07. The actual specified kernel is regular on the complete bent chain throughout a full disk.
[RW26, p. 6]. -/
theorem bent_regular_tube (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hδ : 0 < δ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
      (∀ t : ℝ, -1 ≤ t →
        (g1VerticalPoint (g1BentCrossing M τ₀ δ n m) t, τ) ∈
          ModularCluster.regularDomain M (singleData (w : ℂ) n h ell m)) ∧
      (∀ r : ℝ, 0 ≤ r →
        (g1BentLowerPoint (g1BentCrossing M τ₀ δ n m) ψ r, τ) ∈
          ModularCluster.regularDomain M (singleData (w : ℂ) n h ell m)) := by
  obtain ⟨ρ, ε, hρ, hε, hdom, hgap⟩ := bent_branch_gap M hM F τ₀ δ ψ n hT hδ hψ hψ'
  refine ⟨ρ, hρ, ?_⟩
  intro τ hτ m hm
  constructor
  · intro t ht
    apply branch_single_regular_of_gap M hM τ (w : ℂ) _ n h ell m ε hε (hdom hτ)
    intro K J hKJ
    exact (hgap τ hτ m hm K J hKJ).1 t ht
  · intro r hr
    apply branch_single_regular_of_gap M hM τ (w : ℂ) _ n h ell m ε hε (hdom hτ)
    intro K J hKJ
    exact (hgap τ hτ m hm K J hKJ).2 r hr

/-- T08. Compact pieces have one full-disk bound, including Jacobians. [RW26, p. 6]. -/
theorem bent_compact_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ w δ ψ R : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hδ : 0 < δ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) (hR : 0 ≤ R) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
        (∀ t ∈ Icc (-1) R,
          ‖g1VerticalPullback (singleKernel M τ (w : ℂ) n h ell m)
            (g1BentCrossing M τ₀ δ n m) t‖ ≤ C) ∧
        (∀ r ∈ Icc 0 R,
          ‖g1BentLowerPullback (singleKernel M τ (w : ℂ) n h ell m)
            (g1BentCrossing M τ₀ δ n m) ψ r‖ ≤ C) := by
  obtain ⟨r₀, hr₀, hreg⟩ := bent_regular_tube M hM F τ₀ w δ ψ n h ell hT hδ hψ hψ'
  let P : ℤ → ℝ → ℝ → Prop := fun m ρ C =>
    ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
      (∀ t ∈ Icc (-1) R,
        ‖g1VerticalPullback (singleKernel M τ (w : ℂ) n h ell m)
          (g1BentCrossing M τ₀ δ n m) t‖ ≤ C) ∧
      (∀ r ∈ Icc 0 R,
        ‖g1BentLowerPullback (singleKernel M τ (w : ℂ) n h ell m)
          (g1BentCrossing M τ₀ δ n m) ψ r‖ ≤ C)
  have hmono : ∀ m r s B D, s ≤ r → B ≤ D → P m r B → P m s D := by
    intro m r s B D hsr hBD hm τ hτ
    have hb := hm τ (Metric.closedBall_subset_closedBall hsr hτ)
    exact ⟨fun t ht => (hb.1 t ht).trans hBD, fun t ht => (hb.2 t ht).trans hBD⟩
  have hex : ∀ m ∈ F, ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ P m ρ C := by
    intro m hm
    let x := g1BentCrossing M τ₀ δ n m
    let K : Set ℂ := (g1VerticalPoint x '' Icc (-1) R) ∪
      (g1BentLowerPoint x ψ '' Icc 0 R)
    have hcv : Continuous (g1VerticalPoint x) := by unfold g1VerticalPoint; fun_prop
    have hcl : Continuous (g1BentLowerPoint x ψ) := by unfold g1BentLowerPoint; fun_prop
    have hK : IsCompact K := (isCompact_Icc.image hcv).union (isCompact_Icc.image hcl)
    have hs : ∀ z ∈ K, (z, (τ₀ : ℂ)) ∈
        ModularCluster.regularDomain M (singleData (w : ℂ) n h ell m) := by
      intro z hz
      have hr := hreg (τ₀ : ℂ) (Metric.mem_closedBall_self hr₀.le) m hm
      rcases hz with ⟨t, ht, rfl⟩ | ⟨r, hr', rfl⟩
      · exact hr.1 t ht.1
      · exact hr.2 r hr'.1
    obtain ⟨ρ, B, hρ, hB, hb⟩ := ModularCluster.RegularityAux.compact_slice_bound hK
      (ModularCluster.regularDomain_isOpen M hM (singleData (w : ℂ) n h ell m)) hs
      (ModularCluster.kernel_joint_analytic M hM (singleData (w : ℂ) n h ell m)).continuousOn
    refine ⟨ρ, B * (‖g1LowerDirection ψ‖ + 1), hρ,
      mul_pos hB (by positivity), ?_⟩
    intro τ hτ
    constructor
    · intro t ht
      have hz : g1VerticalPoint x t ∈ K := Or.inl (Set.mem_image_of_mem _ ht)
      have hbound := (hb _ hz τ hτ).2
      dsimp only [g1VerticalPullback, singleKernel]
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hbound.trans (le_mul_of_one_le_right hB.le (by linarith [norm_nonneg (g1LowerDirection ψ)]))
    · intro r hr
      have hz : g1BentLowerPoint x ψ r ∈ K := Or.inr (Set.mem_image_of_mem _ hr)
      have hbound := (hb _ hz τ hτ).2
      dsimp only [g1BentLowerPullback, singleKernel]
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (by linarith : ‖g1LowerDirection ψ‖ ≤ ‖g1LowerDirection ψ‖ + 1) hB.le)
  obtain ⟨ρ, C, hρ, hC, hb⟩ := ModularCluster.RegularityAux.finite_uniform_radius_bound F P hmono hex
  exact ⟨ρ, C, hρ, hC, fun τ hτ m hm => hb m hm τ hτ⟩

/-- T09. The two explicit piecewise majorants are nonnegative and integrable. [RW26, p. 7, pp.
28--29]. Elementary analysis. -/
theorem majorants_integrable (C κ a B R : ℝ) (hC : 0 ≤ C)
    (hκ : 0 < κ) (ha : 0 < a) :
    (∀ t : ℝ, 0 ≤ upperMajorant C κ R t) ∧
    (∀ r : ℝ, 0 ≤ lowerMajorant C a B R r) ∧
    IntegrableOn (upperMajorant C κ R) (Ici (-1)) ∧
    IntegrableOn (lowerMajorant C a B R) (Ici 0) := by
  have hu : IntegrableOn (fun t : ℝ => C * Real.exp (-κ * t)) (Ici (-1)) := by
    exact ((integrableOn_Ici_iff_integrableOn_Ioi).2
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hκ) (-1))).const_mul C
  have hl : IntegrableOn (fun r : ℝ => C * Real.exp (-a * r ^ 2 + B * r))
      (Ici 0) := (integrable_real_quadratic_exp a B ha).integrableOn.const_mul C
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    dsimp [upperMajorant]
    split_ifs <;> positivity
  · intro r
    dsimp [lowerMajorant]
    split_ifs <;> positivity
  · exact integrableOn_if_le _ C R (-1) hu
  · exact integrableOn_if_le _ C R 0 hl

/-- T10. Downstream full-chain majorants: all constants precede τ,m and the pullback variable. This
includes the compact middle, not just tails. [RW26, p. 7]. -/
theorem uniform_bent_majorants (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ ρ C κ a B R : ℝ,
      0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < a ∧ 0 < B ∧ 0 < R ∧
        IntegrableOn (upperMajorant C κ R) (Ici (-1)) ∧
        IntegrableOn (lowerMajorant C a B R) (Ici 0) ∧
        ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
          (∀ t : ℝ, -1 ≤ t →
            ‖g1VerticalPullback (singleKernel M τ (w : ℂ) n h ell m)
              (g1BentCrossing M τ₀ δ n m) t‖ ≤ upperMajorant C κ R t) ∧
          (∀ r : ℝ, 0 ≤ r →
            ‖g1BentLowerPullback (singleKernel M τ (w : ℂ) n h ell m)
              (g1BentCrossing M τ₀ δ n m) ψ r‖ ≤ lowerMajorant C a B R r) := by
  obtain ⟨ρu, Cu, κ, Ru, hρu, hCu, hκ, hRu, hu⟩ :=
    uniform_upper_tail M hM F τ₀ w δ n h ell hT hs
  obtain ⟨ρl, Cl, a, B, Rl, σ, hρl, hCl, ha, hB, hRl, hσ, hl⟩ :=
    uniform_bent_lower_tail M hM F τ₀ w δ ψ n h ell hT hψ hψ'
  let R := max Ru Rl
  have hR : 0 < R := lt_of_lt_of_le hRu (le_max_left _ _)
  obtain ⟨ρc, Cc, hρc, hCc, hc⟩ :=
    bent_compact_bound M hM F τ₀ w δ ψ R n h ell hT hδ hψ hψ' hR.le
  let C := max Cc (max Cu Cl)
  have hC : 0 < C := lt_of_lt_of_le hCc (le_max_left _ _)
  obtain ⟨_, _, hiu, hil⟩ := majorants_integrable C κ a B R hC.le hκ ha
  refine ⟨min ρc (min ρu ρl), C, κ, a, B, R,
    lt_min hρc (lt_min hρu hρl), hC, hκ, ha, hB, hR, hiu, hil, ?_⟩
  intro τ hτ m hm
  have hτc : τ ∈ ModularSector.parameterDisk τ₀ ρc :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hτ
  have hτu : τ ∈ ModularSector.parameterDisk τ₀ ρu :=
    Metric.closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _)) hτ
  have hτl : τ ∈ ModularSector.parameterDisk τ₀ ρl :=
    Metric.closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_right _ _)) hτ
  constructor
  · intro t ht
    dsimp only [upperMajorant]
    split_ifs with htR
    · exact ((hc τ hτc m hm).1 t ⟨ht, htR⟩).trans (le_max_left _ _)
    · refine (hu τ hτu m hm t ?_).trans ?_
      · exact (le_max_left Ru Rl).trans (le_of_not_ge htR)
      · exact mul_le_mul_of_nonneg_right
          ((le_max_left Cu Cl).trans (le_max_right Cc _)) (Real.exp_pos _).le
  · intro r hr
    dsimp only [lowerMajorant]
    split_ifs with hrR
    · exact ((hc τ hτc m hm).2 r ⟨hr, hrR⟩).trans (le_max_left _ _)
    · refine ((hl τ hτl).2.2 m hm r ?_).trans ?_
      · exact (le_max_right Ru Rl).trans (le_of_not_ge hrR)
      · exact mul_le_mul_of_nonneg_right
          ((le_max_right Cu Cl).trans (le_max_right Cc _)) (Real.exp_pos _).le

/-- T11. Actual ordinary integrability throughout one full parameter disk. [RW26, p. 7, (22)]. -/
theorem bent_integrable_full_disk (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset ℤ) (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
      G1BentIntegrable (singleKernel M τ (w : ℂ) n h ell m)
        (g1BentCrossing M τ₀ δ n m) ψ := by
  obtain ⟨ρ₁, hρ₁, hreg⟩ := bent_regular_tube M hM F τ₀ w δ ψ n h ell hT hδ hψ hψ'
  obtain ⟨ρ₂, C, κ, a, B, R, hρ₂, hC, hκ, ha, hB, hR, hu, hl, hb⟩ :=
    uniform_bent_majorants M hM F τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  intro τ hτ m hm
  have hτ₁ : τ ∈ ModularSector.parameterDisk τ₀ ρ₁ :=
    Metric.closedBall_subset_closedBall (min_le_left ρ₁ ρ₂) hτ
  have hτ₂ : τ ∈ ModularSector.parameterDisk τ₀ ρ₂ :=
    Metric.closedBall_subset_closedBall (min_le_right ρ₁ ρ₂) hτ
  obtain ⟨hru, hrl⟩ := hreg τ hτ₁ m hm
  obtain ⟨hbu, hbl⟩ := hb τ hτ₂ m hm
  have hcu : ContinuousOn
      (g1VerticalPullback (singleKernel M τ (w : ℂ) n h ell m)
        (g1BentCrossing M τ₀ δ n m)) (Ici (-1)) := by
    apply kernel_pullback_continuousOn M hM (singleData (w : ℂ) n h ell m) τ Complex.I
    · unfold g1VerticalPoint
      fun_prop
    · exact hru
  have hcl : ContinuousOn
      (g1BentLowerPullback (singleKernel M τ (w : ℂ) n h ell m)
        (g1BentCrossing M τ₀ δ n m) ψ) (Ici 0) := by
    apply kernel_pullback_continuousOn M hM (singleData (w : ℂ) n h ell m)
      τ (g1LowerDirection ψ)
    · unfold g1BentLowerPoint
      fun_prop
    · exact hrl
  refine ⟨hl.mono' (hcl.aestronglyMeasurable measurableSet_Ici) ?_,
    hu.mono' (hcu.aestronglyMeasurable measurableSet_Ici) ?_⟩
  · exact (ae_restrict_mem measurableSet_Ici).mono (fun r hr => hbl r hr)
  · exact (ae_restrict_mem measurableSet_Ici).mono (fun t ht => hbu t ht)

/-- T12. A full-neighborhood ordinary integral limit, and separately both one-sided limits, to the
same real interface integral. This is the direct input; it asserts no lower-half-plane integral
identity. [RW26, p. 7, (22)]. -/
theorem bent_integral_parameter_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell m : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    let f := fun τ : ℂ => g1BentIntegral (singleKernel M τ (w : ℂ) n h ell m)
      (g1BentCrossing M τ₀ δ n m) ψ
    let v := g1BentIntegral (g1SingleKernel M τ₀ w n h ell m)
      (g1BentCrossing M τ₀ δ n m) ψ
    Tendsto f (𝓝 (τ₀ : ℂ)) (𝓝 v) ∧
      Tendsto f (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 v) ∧
      Tendsto f (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ)) (𝓝 v) := by
  obtain ⟨r, C, κ, a, B, R, hr, hC, hκ, ha, hB, hR, hu, hl, hb⟩ :=
    uniform_bent_majorants M hM {m} τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  obtain ⟨s, hs', hreg⟩ := bent_regular_tube M hM {m} τ₀ w δ ψ n h ell hT hδ hψ hψ'
  let ρ := min r s
  have hρ : 0 < ρ := lt_min hr hs'
  have hd : DifferentiableOn ℂ
      (fun τ => g1BentIntegral (singleKernel M τ (w : ℂ) n h ell m)
        (g1BentCrossing M τ₀ δ n m) ψ) (Metric.ball (τ₀ : ℂ) (ρ / 2)) := by
    apply bent_integral_differentiableOn_of_bound M hM (singleData (w : ℂ) n h ell m)
      (τ₀ : ℂ) ρ (g1BentCrossing M τ₀ δ n m) ψ
      (upperMajorant C κ R) (lowerMajorant C a B R) hρ hu hl
    · intro τ hτ
      exact hreg τ (Metric.closedBall_subset_closedBall (min_le_right r s) hτ) m (by simp)
    · intro τ hτ
      exact hb τ (Metric.closedBall_subset_closedBall (min_le_left r s) hτ) m (by simp)
  have hlim : Tendsto
      (fun τ => g1BentIntegral (singleKernel M τ (w : ℂ) n h ell m)
        (g1BentCrossing M τ₀ δ n m) ψ) (𝓝 (τ₀ : ℂ))
      (𝓝 (g1BentIntegral (g1SingleKernel M τ₀ w n h ell m)
        (g1BentCrossing M τ₀ δ n m) ψ)) := by
    simpa only [singleKernel_real] using
      ((hd.analyticOnNhd Metric.isOpen_ball) (τ₀ : ℂ) (Metric.mem_ball_self (half_pos hρ))).continuousAt.tendsto
  exact ⟨hlim, hlim.mono_left nhdsWithin_le_nhds, hlim.mono_left nhdsWithin_le_nhds⟩

/-- T13. Direct finite-sum outlet, with the precise Nat-range convention of G1RealConclusion. Both
sides converge to the same real sum. [RW26, p. 7, (22)]. This is ordinary integral continuity,
without identifying its value. -/
theorem summed_bent_integral_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    let f := fun τ : ℂ => ∑ m ∈ Finset.range (M 1 0).toNat,
      g1BentIntegral (singleKernel M τ (w : ℂ) n h ell (m : ℤ))
        (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ
    let v := ∑ m ∈ Finset.range (M 1 0).toNat,
      g1BentIntegral (g1SingleKernel M τ₀ w n h ell (m : ℤ))
        (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ
    Tendsto f (𝓝 (τ₀ : ℂ)) (𝓝 v) ∧
      Tendsto f (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 v) ∧
      Tendsto f (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ)) (𝓝 v) := by
  dsimp only
  have hsum := tendsto_finsetSum (Finset.range (M 1 0).toNat)
    (fun m _ => (bent_integral_parameter_limits M hM τ₀ w δ ψ n h ell (m : ℤ)
      hT hs hδ hψ hψ').1)
  exact ⟨hsum, hsum.mono_left nhdsWithin_le_nhds, hsum.mono_left nhdsWithin_le_nhds⟩

/-- T14. Local analyticity of the fixed-chain finite sum, as an outlet of the same full-disk
domination. The proof uses the half-radius open disk for differentiability, and its smaller closed
subdisk for
analyticity on a neighborhood. [RW26, p. 6, p. 7, (22)]. This new interface prepares lower-half
identification, but asserts no identity. w and the contour stay fixed. -/
theorem summed_bent_integral_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w δ ψ : ℝ) (n h ell : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hδ : 0 < δ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    let f := fun τ : ℂ => ∑ m ∈ Finset.range (M 1 0).toNat,
      g1BentIntegral (singleKernel M τ (w : ℂ) n h ell (m : ℤ))
        (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ
    ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd ℂ f (ModularSector.parameterDisk τ₀ ρ) := by
  let F : Finset ℤ := (Finset.range (M 1 0).toNat).image Int.ofNat
  obtain ⟨r, C, κ, a, B, R, hr, hC, hκ, ha, hB, hR, hu, hl, hb⟩ :=
    uniform_bent_majorants M hM F τ₀ w δ ψ n h ell hT hs hδ hψ hψ'
  obtain ⟨s, hs', hreg⟩ := bent_regular_tube M hM F τ₀ w δ ψ n h ell hT hδ hψ hψ'
  let ρ := min r s
  have hρ : 0 < ρ := lt_min hr hs'
  have hd (m : ℕ) (hm : m ∈ Finset.range (M 1 0).toNat) : DifferentiableOn ℂ
      (fun τ => g1BentIntegral (singleKernel M τ (w : ℂ) n h ell (m : ℤ))
        (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) (Metric.ball (τ₀ : ℂ) (ρ / 2)) := by
    have hmF : (m : ℤ) ∈ F := Finset.mem_image_of_mem _ hm
    apply bent_integral_differentiableOn_of_bound M hM (singleData (w : ℂ) n h ell (m : ℤ))
      (τ₀ : ℂ) ρ (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ
      (upperMajorant C κ R) (lowerMajorant C a B R) hρ hu hl
    · intro τ hτ
      exact hreg τ (Metric.closedBall_subset_closedBall (min_le_right r s) hτ) (m : ℤ) hmF
    · intro τ hτ
      exact hb τ (Metric.closedBall_subset_closedBall (min_le_left r s) hτ) (m : ℤ) hmF
  have hsum : DifferentiableOn ℂ
      (fun τ : ℂ => ∑ m ∈ Finset.range (M 1 0).toNat,
        g1BentIntegral (singleKernel M τ (w : ℂ) n h ell (m : ℤ))
          (g1BentCrossing M τ₀ δ n (m : ℤ)) ψ) (Metric.ball (τ₀ : ℂ) (ρ / 2)) :=
    DifferentiableOn.fun_sum hd
  refine ⟨ρ / 4, by positivity, (hsum.analyticOnNhd Metric.isOpen_ball).mono ?_⟩
  intro τ hτ
  exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hτ).trans_lt (by linarith))

#check @ModularSector.bilateral_uniform_asymptotics
#check @ModularCluster.kernel_joint_analytic
#check @g1BentIntegral
#print bentLinear
#print upperMajorant
#print lowerMajorant
#check @uniform_bent_majorants
#check @bent_integral_parameter_limits
#check @summed_bent_integral_limits
#check @summed_bent_integral_analytic

end SICLean.L4.G1BilateralSingleTails
