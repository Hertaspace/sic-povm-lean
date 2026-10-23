import SICLean.L4.FaddeevRotatedBounds

set_option autoImplicit false

/-!
Auxiliary estimates for the rotated integral. The two sinh parameters are kept independent: rotation
does not preserve the relation `q = p⁻¹`.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4.Sector

def twoSinhKernel (p q z : ℂ) (v t : ℝ) : ℂ :=
  Complex.exp (-2 * Complex.I * z * linePoint v t) /
    (4 * Complex.sinh (p * linePoint v t) *
      Complex.sinh (q * linePoint v t) * linePoint v t)

def twoSinhDerivative (p q z : ℂ) (v t : ℝ) : ℂ :=
  (-2 * Complex.I * linePoint v t) * twoSinhKernel p q z v t

lemma rotatedKernel_eq_twoSinhKernel (b x : ℂ) (θ v t : ℝ) :
    rotatedKernel b x θ v t =
      twoSinhKernel (b * rotation θ) (b⁻¹ * rotation θ) (x * rotation θ) v t := by
  rw [rotatedKernel_eq]
  simp only [twoSinhKernel, amplitude, rotatedDenominator, rotatedPoint,
    div_eq_mul_inv, mul_assoc]

lemma integrable_twoSinhKernel (p q z : ℂ) (v : ℝ)
    (hp : 0 < p.re) (hq : 0 < q.re) (hz : 2 * |z.im| < p.re + q.re)
    (hd : ∀ t : ℝ, 4 * Complex.sinh (p * linePoint v t) *
      Complex.sinh (q * linePoint v t) * linePoint v t ≠ 0) :
    Integrable (twoSinhKernel p q z v) := by
  exact integrable_exp_div_sinh_product_line_mul p q z v hp hq hz hd

lemma integrable_twoSinhDerivative (p q z : ℂ) (v : ℝ)
    (hp : 0 < p.re) (hq : 0 < q.re) (hz : 2 * |z.im| < p.re + q.re)
    (hd : ∀ t : ℝ, 4 * Complex.sinh (p * linePoint v t) *
      Complex.sinh (q * linePoint v t) * linePoint v t ≠ 0) :
    Integrable (twoSinhDerivative p q z v) := by
  exact integrable_derivative_exp_div_sinh_product_line_mul p q z v hp hq hz hd

lemma hasDerivAt_twoSinhKernel (p q z : ℂ) (v t : ℝ) :
    HasDerivAt (fun ζ => twoSinhKernel p q ζ v t) (twoSinhDerivative p q z v t) z := by
  have h := (((hasDerivAt_id z).const_mul (-2 * Complex.I)).mul_const
    (linePoint v t)).cexp
  convert! h.div_const (4 * Complex.sinh (p * linePoint v t) *
    Complex.sinh (q * linePoint v t) * linePoint v t) using 1 <;>
    (try simp only [id_eq, mul_one, twoSinhKernel, twoSinhDerivative]) <;> ring

lemma twoSinhDerivative_add_argument (p q z u : ℂ) (v t : ℝ) :
    twoSinhDerivative p q (z + u) v t =
      Complex.exp (-2 * Complex.I * u * linePoint v t) *
        twoSinhDerivative p q z v t := by
  unfold twoSinhDerivative twoSinhKernel
  rw [show -2 * Complex.I * (z + u) * linePoint v t =
    -2 * Complex.I * u * linePoint v t + -2 * Complex.I * z * linePoint v t by ring,
    Complex.exp_add]
  ring

lemma twoSinhDerivative_local_bound (p q z ζ : ℂ) (v t r : ℝ)
    (hr : 0 ≤ r) (hζ : ‖ζ - z‖ ≤ r) :
    ‖twoSinhDerivative p q ζ v t‖ ≤ Real.exp (2 * r * |v|) *
      (‖twoSinhDerivative p q (z + Complex.I * (r : ℂ)) v t‖ +
       ‖twoSinhDerivative p q (z - Complex.I * (r : ℂ)) v t‖) := by
  have heq : ζ = z + (ζ - z) := by ring
  rw [heq, twoSinhDerivative_add_argument, norm_mul]
  have hb := mul_le_mul_of_nonneg_right (exp_line_norm_bound (ζ - z) v t r hr hζ)
    (norm_nonneg (twoSinhDerivative p q z v t))
  convert hb using 1 <;> try rfl
  simp only [twoSinhDerivative_add_argument, sub_eq_add_neg, norm_mul, Complex.norm_exp]
  have hp : (-2 * Complex.I * (Complex.I * (r : ℂ)) * linePoint v t).re =
      2 * r * t := by
    simp [linePoint, Complex.mul_re, Complex.mul_im] <;> ring
  have hm : (-2 * Complex.I * -(Complex.I * (r : ℂ)) * linePoint v t).re =
      -(2 * r * t) := by
    simp [linePoint, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hp, hm]
  ring

lemma hasDerivAt_integral_twoSinhKernel (p q z : ℂ) (v : ℝ)
    (hp : 0 < p.re) (hq : 0 < q.re) (hz : 2 * |z.im| < p.re + q.re)
    (hd : ∀ t : ℝ, 4 * Complex.sinh (p * linePoint v t) *
      Complex.sinh (q * linePoint v t) * linePoint v t ≠ 0) :
    HasDerivAt (fun ζ => ∫ t : ℝ, twoSinhKernel p q ζ v t)
      (∫ t : ℝ, twoSinhDerivative p q z v t) z := by
  let W := (p.re + q.re) / 2
  let r := (W - |z.im|) / 2
  have hr : 0 < r := by dsimp [r, W]; linarith
  have hgap : |z.im| + |r| < W := by rw [abs_of_pos hr]; dsimp [r, W]; linarith
  have hpz : 2 * |(z + Complex.I * (r : ℂ)).im| < p.re + q.re := by
    have hh : |(z + Complex.I * (r : ℂ)).im| ≤ |z.im| + |r| := by
      simpa using abs_add_le z.im r
    dsimp [W] at hgap
    linarith
  have hmz : 2 * |(z - Complex.I * (r : ℂ)).im| < p.re + q.re := by
    have hh : |(z - Complex.I * (r : ℂ)).im| ≤ |z.im| + |r| := by
      simpa [sub_eq_add_neg] using abs_add_le z.im (-r)
    dsimp [W] at hgap
    linarith
  let B : ℝ → ℝ := fun t => Real.exp (2 * r * |v|) *
    (‖twoSinhDerivative p q (z + Complex.I * (r : ℂ)) v t‖ +
     ‖twoSinhDerivative p q (z - Complex.I * (r : ℂ)) v t‖)
  have hB : Integrable B :=
    ((integrable_twoSinhDerivative p q _ v hp hq hpz hd).norm.add
      (integrable_twoSinhDerivative p q _ v hp hq hmz hd).norm).const_mul _
  have hmeas : ∀ᶠ ζ in 𝓝 z, AEStronglyMeasurable (twoSinhKernel p q ζ v) := by
    filter_upwards [(isOpen_lt (Complex.continuous_im.abs.const_mul 2)
      continuous_const).mem_nhds hz] with ζ hζ
    exact (integrable_twoSinhKernel p q ζ v hp hq hζ hd).aestronglyMeasurable
  have hDmeas := (integrable_twoSinhDerivative p q z v hp hq hz hd).aestronglyMeasurable
  have hD : ∀ᵐ t : ℝ, ∀ ζ ∈ Metric.ball z r,
      HasDerivAt (fun ζ => twoSinhKernel p q ζ v t) (twoSinhDerivative p q ζ v t) ζ :=
    Eventually.of_forall fun t ζ _ => hasDerivAt_twoSinhKernel p q ζ v t
  have hbound : ∀ᵐ t : ℝ, ∀ ζ ∈ Metric.ball z r,
      ‖twoSinhDerivative p q ζ v t‖ ≤ B t := by
    refine Eventually.of_forall fun t ζ hζ => ?_
    exact twoSinhDerivative_local_bound p q z ζ v t r hr.le
      (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hζ))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z hr) hmeas (integrable_twoSinhKernel p q z v hp hq hz hd)
    hDmeas hbound hB hD).2

lemma exists_uniform_parameter_norm_bound {K : Set ℂ} {β κ : ℝ}
    (hK : Family K β κ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ b ∈ K, ‖b‖ ≤ N ∧ ‖b⁻¹‖ ≤ N := by
  obtain ⟨N₁, hN₁⟩ := hK.compact.exists_bound_of_continuousOn
    (f := fun b : ℂ => b) continuousOn_id
  obtain ⟨N₂, hN₂⟩ := hK.compact.exists_bound_of_continuousOn
    (f := fun b : ℂ => b⁻¹)
    (continuousOn_id.inv₀ fun b hb => admissibleB_ne_zero b (hK.admissible b hb))
  refine ⟨max 0 (max N₁ N₂), le_max_left _ _, fun b hb => ⟨?_, ?_⟩⟩
  · exact (hN₁ b hb).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hN₂ b hb).trans ((le_max_right _ _).trans (le_max_right _ _))

lemma hasDerivAt_rotatedIntegral_aux {K : Set ℂ} {β κ lam v : ℝ}
    (hK : Family K β κ) (hlam : UniformMargin K (opening β κ) lam)
    (hv : SafeHeight lam v) {b x : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-(opening β κ)) (opening β κ))
    (hx : 2 * |(x * rotation θ).im| < rotatedRe b θ + rotatedInvRe b θ) :
    HasDerivAt (fun z => ∫ t : ℝ, rotatedKernel b z θ v t)
      (∫ t : ℝ, (-2 * Complex.I * rotatedPoint θ v t) * rotatedKernel b x θ v t) x := by
  have h := hasDerivAt_integral_twoSinhKernel (b * rotation θ) (b⁻¹ * rotation θ)
    (x * rotation θ) v
    (hlam.1.trans_le (hlam.2 b hb θ hθ).1)
    (hlam.1.trans_le (hlam.2 b hb θ hθ).2) hx
    (fun t => by
      simpa only [rotatedDenominator, rotatedPoint, mul_assoc] using
        rotatedDenominator_ne_zero hlam hv hb
          (admissibleB_ne_zero b (hK.admissible b hb)) hθ t)
  have hc := h.comp x ((hasDerivAt_id x).mul_const (rotation θ))
  have hI : (∫ t : ℝ, (-2 * Complex.I * rotatedPoint θ v t) * rotatedKernel b x θ v t) =
      (∫ t : ℝ, twoSinhDerivative (b * rotation θ) (b⁻¹ * rotation θ)
        (x * rotation θ) v t) * rotation θ := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [twoSinhDerivative, rotatedKernel_eq_twoSinhKernel, rotatedPoint]
      ring
  rw [hI]
  simpa only [Function.comp_def, id_eq, one_mul, rotatedKernel_eq_twoSinhKernel] using hc

end SICLean.L4.Sector
