import SICLean.L4.G2RawKernel
import SICLean.L4.G2KernelConvergenceAux

set_option autoImplicit false

/-!
Jacobians, absolute convergence and horizontal closures. [RW26, p. 13]. Only named estimates
fixed_phi_upper_estimate/fixed_phi_lower_estimate from the preceding file are used for the tails,
never a new G1 hypothesis. The statements concern the ratio rawF; rawG needs a bent lower tail.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2

def affinePoint (M : SL(2, ℤ)) (m j : ℤ) (Z : ℂ) : ℂ :=
  (Z - (epsilon M : ℂ) * (m : ℂ) - (j : ℂ) * (length M : ℂ)) / (M 1 0 : ℂ)

/-- dz=dX/c, including the circle contribution. -/
def affineKernel (M : SL(2, ℤ)) (m j : ℤ) (f : ℂ → ℂ) (Z : ℂ) : ℂ :=
  f (affinePoint M m j Z) / (M 1 0 : ℂ)

def horizontalPullback (f : ℂ → ℂ) (T x : ℝ) : ℂ :=
  f ((x : ℂ) + (T : ℂ) * Complex.I)

def horizontalIntegral (f : ℂ → ℂ) (lo hi T : ℝ) : ℂ :=
  ∫ x : ℝ in lo..hi, horizontalPullback f T x

/-- Exact complex affine derivative; [RW26, p. 13]. -/
theorem affinePoint_hasDerivAt (M : SL(2, ℤ)) (m j : ℤ) (Z : ℂ) :
    HasDerivAt (affinePoint M m j) (M 1 0 : ℂ)⁻¹ Z := by
  simpa [affinePoint] using!
    (((hasDerivAt_id Z).sub_const ((epsilon M : ℂ) * (m : ℂ))).sub_const
      ((j : ℂ) * (length M : ℂ))).div_const (M 1 0 : ℂ)

/-- With the common real line parameter t, dz/dt=i/c; [RW26, p. 13]. -/
theorem affine_vertical_jacobian (M : SL(2, ℤ)) (D : G1VerticalChain)
    (m j : ℤ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => affinePoint M m j (g1VerticalPoint D.crossing x))
      (Complex.I / (M 1 0 : ℂ)) t := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add
    (D.crossing : ℂ))
  simpa [affinePoint, g1VerticalPoint] using
    ((h.sub_const ((epsilon M : ℂ) * (m : ℂ))).sub_const
      ((j : ℂ) * (length M : ℂ))).div_const (M 1 0 : ℂ)

/-- With the common circle parameter θ, dz/dθ=i(X-r)/c; [RW26, p. 13]. -/
theorem affine_circle_jacobian (M : SL(2, ℤ)) (m j : ℤ) (r ρ θ : ℝ) :
    HasDerivAt (fun x : ℝ => affinePoint M m j (circleMap (r : ℂ) ρ x))
      (Complex.I * (circleMap (r : ℂ) ρ θ - (r : ℂ)) / (M 1 0 : ℂ)) θ := by
  simpa [affinePoint, mul_comm] using
    (((hasDerivAt_circleMap (r : ℂ) ρ θ).sub_const
      ((epsilon M : ℂ) * (m : ℂ))).sub_const
      ((j : ℂ) * (length M : ℂ))).div_const (M 1 0 : ℂ)

/-- Vertical pullback after t_X=c*t_z; the extra 1/c must remain; [RW26, p. 13]. -/
theorem affine_vertical_pullback (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j : ℤ) (f : ℂ → ℂ) (t : ℝ) :
    g1VerticalPullback (affineKernel M m j f) D.crossing ((M 1 0 : ℝ) * t) =
      g1VerticalPullback f (componentChain M D m j).crossing t / (M 1 0 : ℂ) := by
  rw [g1VerticalPullback, g1VerticalPullback, affineKernel,
    componentChain_verticalPoint M hM]
  dsimp only [affinePoint]
  ring

/-- Circles retain their parameter and orientation; their radii divide by c; [RW26, p. 13]. -/
theorem affine_circle_pullback (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j : ℤ) (f : ℂ → ℂ) (r θ : ℝ) :
    g1CirclePullback f
        ((r - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ))
        (D.radius r / (M 1 0 : ℝ)) θ =
      g1CirclePullback (affineKernel M m j f) r (D.radius r) θ := by
  rw [g1CirclePullback, g1CirclePullback, affineKernel,
    componentChain_circlePoint M hM]
  dsimp only [affinePoint]
  push_cast
  ring

/-- Change of variables for the actual line plus finite circles, not contour homotopy; [RW26, p.
13]. -/
theorem affine_chain_integral (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j : ℤ) (f : ℂ → ℂ)
    (hf : G1ChainIntegrable (componentChain M D m j) f) :
    G1ChainIntegrable D (affineKernel M m j f) ∧
      g1ChainIntegral (componentChain M D m j) f =
        g1ChainIntegral D (affineKernel M m j f) := by
  classical
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hcC : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let q : ℝ → ℝ := fun r =>
    (r - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ)
  have hq : Function.Injective q := by
    intro r s h
    dsimp only [q] at h
    have h' := (div_left_inj' hc.ne').mp h
    linarith
  have hradius (r : ℝ) :
      (componentChain M D m j).radius (q r) = D.radius r / (M 1 0 : ℝ) := by
    dsimp only [componentChain, q]
    congr 2
    field_simp
    ring
  have hcircle (r : ℝ) :
      g1CirclePullback f (q r) ((componentChain M D m j).radius (q r)) =
        g1CirclePullback (affineKernel M m j f) r (D.radius r) := by
    funext θ
    rw [hradius]
    exact affine_circle_pullback M hM D m j f r θ
  have hline (t : ℝ) :
      g1VerticalPullback (affineKernel M m j f) D.crossing t =
        g1VerticalPullback f (componentChain M D m j).crossing
          (t / (M 1 0 : ℝ)) / (M 1 0 : ℂ) := by
    have h := affine_vertical_pullback M hM D m j f (t / (M 1 0 : ℝ))
    simpa only [mul_div_cancel₀ t hc.ne'] using h
  have hlineInt : Integrable (g1VerticalPullback (affineKernel M m j f) D.crossing) := by
    rw [show g1VerticalPullback (affineKernel M m j f) D.crossing =
      (fun t => g1VerticalPullback f (componentChain M D m j).crossing
        (t / (M 1 0 : ℝ)) / (M 1 0 : ℂ)) from funext hline]
    have h := (integrable_comp_div_iff
      (g1VerticalPullback f (componentChain M D m j).crossing) hc.ne').2 hf.1
    simpa only [div_eq_mul_inv] using h.mul_const (M 1 0 : ℂ)⁻¹
  have hlineEq :
      (∫ t : ℝ, g1VerticalPullback (affineKernel M m j f) D.crossing t) =
        ∫ t : ℝ, g1VerticalPullback f (componentChain M D m j).crossing t := by
    simp_rw [hline]
    rw [integral_div, Measure.integral_comp_div, abs_of_pos hc, real_smul]
    push_cast
    field_simp
  refine ⟨⟨hlineInt, ?_⟩, ?_⟩
  · intro r hr
    rw [← hcircle]
    exact hf.2 (q r) (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  · dsimp only [g1ChainIntegral]
    rw [hlineEq]
    congr 1
    change (∑ r ∈ D.centers.image q,
      ∫ θ : ℝ in 0..(2 * Real.pi),
        g1CirclePullback f r ((componentChain M D m j).radius r) θ) = _
    rw [Finset.sum_image (fun r _ s _ hrs => hq hrs)]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hcircle]

/-- Quantitative upper bounds for both raw and final kernels. Derived from fixed_phi_upper_estimate
and the dominant U term of the comb; [RW26, p. 13]. -/
theorem ratio_upper_tail_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ z : ℂ, |z.re| ≤ B → R ≤ z.im →
        ‖rawF M u v m z‖ ≤ C * Real.exp (-2 * Real.pi * rawUpperRate M u * z.im) ∧
        ‖ratioKernel M u v m z‖ ≤
          C * Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) := by
  exact G2KernelConvergenceAux.upper_tail_bound M hM u v m B hB

/-- Quantitative lower bounds: distinct raw/final coefficients, from fixed_phi_lower_estimate and
raw/final_reflection_ratio_norm; [RW26, p. 6, Prop. 1, p. 13]. -/
theorem ratio_lower_tail_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ z : ℂ, |z.re| ≤ B → z.im ≤ -R →
        ‖rawF M u v m z‖ ≤ C * Real.exp (-2 * Real.pi * rawLowerRate M u v * z.im) ∧
        ‖ratioKernel M u v m z‖ ≤
          C * Real.exp (-2 * Real.pi * finalLowerRate M u v * z.im) := by
  exact G2KernelConvergenceAux.lower_tail_bound M hM u v m B hB

/-- A common integrable envelope on each fixed bounded-width strip; [RW26, p. 13]. The strict signs
are supplied by the deep window. -/
theorem ratio_strip_envelope (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (m : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ z : ℂ, |z.re| ≤ B → R ≤ |z.im| →
        ‖rawF M u v m z‖ + ‖ratioKernel M u v m z‖ ≤
          C * Real.exp (-κ * |z.im|) := by
  obtain ⟨Cu, Ru, hCu, hRu, hu⟩ := ratio_upper_tail_bound M hM u v m B hB
  obtain ⟨Cl, Rl, hCl, hRl, hl⟩ := ratio_lower_tail_bound M hM u v m B hB
  have he := epsilon_pos M hM
  obtain ⟨ha, hb, _, _⟩ := raw_and_final_windows M hM u v hwin
  change 0 < rawUpperRate M u at ha
  change rawLowerRate M u v < 0 at hb
  have hs : upperCoefficient M u / epsilon M = rawUpperRate M u + 1 := by
    dsimp only [rawUpperRate]
    field_simp
    ring
  have hf := (final_rate_formula M hM u v).2
  let κ := min (2 * Real.pi * rawUpperRate M u) (-2 * Real.pi * rawLowerRate M u v)
  have hk : 0 < κ := lt_min (by positivity)
    (mul_pos_of_neg_of_neg (by linarith [Real.pi_pos]) hb)
  have hku : κ ≤ 2 * Real.pi * rawUpperRate M u := min_le_left _ _
  have hkl : κ ≤ -2 * Real.pi * rawLowerRate M u v := min_le_right _ _
  refine ⟨2 * (Cu + Cl), κ, max Ru Rl, by positivity, hk,
    lt_max_of_lt_left hRu, ?_⟩
  intro z hz hR
  by_cases hy : 0 ≤ z.im
  · rw [abs_of_nonneg hy] at hR ⊢
    obtain ⟨hraw, hfinal⟩ := hu z hz ((le_max_left _ _).trans hR)
    have hraw' : ‖rawF M u v m z‖ ≤ Cu * Real.exp (-κ * z.im) := by
      refine hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCu.le)
      nlinarith
    have hfinal' : ‖ratioKernel M u v m z‖ ≤ Cu * Real.exp (-κ * z.im) := by
      refine hfinal.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCu.le)
      rw [hs]
      nlinarith [Real.pi_pos]
    nlinarith [Real.exp_pos (-κ * z.im)]
  · have hy' := le_of_not_ge hy
    rw [abs_of_nonpos hy'] at hR ⊢
    obtain ⟨hraw, hfinal⟩ := hl z hz (by linarith [le_max_right Ru Rl])
    have hraw' : ‖rawF M u v m z‖ ≤ Cl * Real.exp (-κ * -z.im) := by
      refine hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCl.le)
      nlinarith
    have hfinal' : ‖ratioKernel M u v m z‖ ≤ Cl * Real.exp (-κ * -z.im) := by
      refine hfinal.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCl.le)
      rw [hf]
      nlinarith [Real.pi_pos]
    nlinarith [Real.exp_pos (-κ * -z.im)]

/-- Original kernels, including j=c, are absolutely integrable on the actual common chains. No
analyticity of the total quotient at isolated real removable representatives is assumed: those
parameter points are null; [RW26, p. 13]. -/
theorem rawF_chain_integrable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : ℤ) (j : Fin ((M 1 0).toNat + 1)) :
    G1ChainIntegrable (componentChain M D m (j : ℤ)) (rawF M u v m) := by
  let E := componentChain M D m (j : ℤ)
  obtain ⟨C, κ, R, _, hk, hR, henv⟩ :=
    ratio_strip_envelope M hM u v hwin m |E.crossing| (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · apply G2KernelConvergenceAux.integrable_of_exponential_decay
      (g1VerticalPullback (rawF M u v m) E.crossing)
      ((G2KernelConvergenceAux.rawF_vertical_continuous M hM u v δ D hD m j).mul
        continuous_const) C κ R hk hR
    intro t ht
    have h := henv (g1VerticalPoint E.crossing t) (by simp [g1VerticalPoint])
      (by simpa [g1VerticalPoint] using ht)
    have hraw := (le_add_of_nonneg_right (norm_nonneg _)).trans h
    simpa [g1VerticalPullback, g1VerticalPoint] using hraw
  · intro r hr
    apply Continuous.intervalIntegrable
    exact (G2KernelConvergenceAux.rawF_circle_continuous M hM u v δ D hD m j r hr).mul
      (by unfold circleMap; fun_prop)

/-- Final kernels at every intermediate j are absolutely integrable, independently of hG1; [RW26, p.
13]. -/
theorem ratio_chain_integrable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : ℤ) (j : Fin (M 1 0).toNat) :
    G1ChainIntegrable (componentChain M D m (j : ℤ)) (ratioKernel M u v m) := by
  let E := componentChain M D m (j : ℤ)
  obtain ⟨C, κ, R, _, hk, hR, henv⟩ :=
    ratio_strip_envelope M hM u v hwin m |E.crossing| (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · apply G2KernelConvergenceAux.integrable_of_exponential_decay
      (g1VerticalPullback (ratioKernel M u v m) E.crossing)
      ((G2KernelConvergenceAux.ratio_vertical_continuous M hM u v δ D hD m j).mul
        continuous_const) C κ R hk hR
    intro t ht
    have h := henv (g1VerticalPoint E.crossing t) (by simp [g1VerticalPoint])
      (by simpa [g1VerticalPoint] using ht)
    have hfinal := (le_add_of_nonneg_left (norm_nonneg _)).trans h
    simpa [g1VerticalPullback, g1VerticalPoint] using hfinal
  · intro r hr
    apply Continuous.intervalIntegrable
    exact (G2KernelConvergenceAux.ratio_circle_continuous M hM u v δ D hD m j r hr).mul
      (by unfold circleMap; fun_prop)

/-- Horizontal parameter x has dz/dx=1; [RW26, p. 13]. -/
theorem horizontal_hasDerivAt (T x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) + (T : ℂ) * Complex.I) 1 x := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((T : ℂ) * Complex.I)

/-- Both horizontal edges tend to zero, for raw and final kernels and any finite width. No choice of
a favorable subsequence of heights; [RW26, p. 13]. -/
theorem horizontal_closures_vanish (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (m : ℤ) (lo hi : ℝ) :
    Tendsto (fun T => horizontalIntegral (rawF M u v m) lo hi T) atTop (𝓝 0) ∧
    Tendsto (fun T => horizontalIntegral (rawF M u v m) lo hi (-T)) atTop (𝓝 0) ∧
    Tendsto (fun T => horizontalIntegral (ratioKernel M u v m) lo hi T) atTop (𝓝 0) ∧
    Tendsto (fun T => horizontalIntegral (ratioKernel M u v m) lo hi (-T)) atTop (𝓝 0) := by
  let B := max |lo| |hi|
  have hB : 0 ≤ B := (abs_nonneg lo).trans (le_max_left _ _)
  obtain ⟨C, κ, R, hC, hk, hR, henv⟩ :=
    ratio_strip_envelope M hM u v hwin m B hB
  have hxB (x : ℝ) (hx : x ∈ Set.uIoc lo hi) : |x| ≤ B := by
    have hlo := abs_le.mp (le_max_left |lo| |hi|)
    have hhi := abs_le.mp (le_max_right |lo| |hi|)
    exact abs_le.mpr ⟨(le_min hlo.1 hhi.1).trans hx.1.le,
      hx.2.trans (max_le hlo.2 hhi.2)⟩
  have hlim : Tendsto (fun T : ℝ => C * Real.exp (-κ * T) * |hi - lo|)
      atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop hk tendsto_id)
    simpa only [neg_mul, mul_zero, zero_mul, Function.comp_apply, id_eq] using
      (ht.const_mul C).mul_const |hi - lo|
  have hzero (f : ℂ → ℂ)
      (hf : ∀ z : ℂ, |z.re| ≤ B → R ≤ |z.im| →
        ‖f z‖ ≤ C * Real.exp (-κ * |z.im|))
      (s : ℝ) (hs : |s| = 1) :
      Tendsto (fun T => horizontalIntegral f lo hi (s * T)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (max R 0)] with T hT
    have hT₀ : 0 ≤ T := (le_max_right _ _).trans hT
    have habs : |s * T| = T := by rw [abs_mul, hs, one_mul, abs_of_nonneg hT₀]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have h := hf ((x : ℂ) + (s * T : ℝ) * Complex.I) (by simpa using hxB x hx)
      (by simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        zero_add, add_zero, habs] using (le_max_left R 0).trans hT)
    simpa [horizontalPullback, habs] using h
  have hraw : ∀ z : ℂ, |z.re| ≤ B → R ≤ |z.im| →
      ‖rawF M u v m z‖ ≤ C * Real.exp (-κ * |z.im|) := by
    intro z hz hR
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (henv z hz hR)
  have hfinal : ∀ z : ℂ, |z.re| ≤ B → R ≤ |z.im| →
      ‖ratioKernel M u v m z‖ ≤ C * Real.exp (-κ * |z.im|) := by
    intro z hz hR
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (henv z hz hR)
  exact ⟨by simpa using hzero _ hraw 1 (by norm_num),
    by simpa using hzero _ hraw (-1) (by norm_num),
    by simpa using hzero _ hfinal 1 (by norm_num),
    by simpa using hzero _ hfinal (-1) (by norm_num)⟩

#print affineKernel
#print G1ChainIntegrable
#check affine_vertical_jacobian
#check affine_circle_jacobian
#check rawF_chain_integrable
#check horizontal_closures_vanish

end SICLean.L4.G2
