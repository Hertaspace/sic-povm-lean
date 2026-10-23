import SICLean.L5.ConjugationStripAux

set_option autoImplicit false

/-!
# Conjugation on Faddeev's original strip

The normalization is [RW26, §2.1, pp. 4--5]. Conjugation is derived from
this normalization. The strip identity is the input to [RW26, p. 14, Prop. 7],
[RW26, p. 14, Cor. 1], and [RW-rec, p. 4, Prop. 2, (7)].

The argument keeps the same upper horizontal contour: conjugation followed
by x ↦ -x gives `kernel_conj_reflect`. The substitution θ ↦ π - θ sends the
endpoints π → 0 to 0 → π; reversing those endpoints restores the standard
clockwise upper arc and retains the resulting sign. Conjugation is applied
to the kernel and the contour together.

For real b > 0 the constant term of the kernel is recorded by
  R(t) = i*z/t^2 - i*sin(2*z*t)/(2*t*sinh(b*t)*sinh(t/b)),
  logPhi = integral_(0,infinity) R(t) dt
    + i*pi*z^2/2 + i*pi*(b^2+b^(-2))/24.
The residue at zero is -z^2/2-(b^2+b^(-2))/24. Its 1/w term contributes
minus i*pi times that residue on the clockwise upper arc. The arc
contribution also contains i*z/r, which cancels against the integrals
along the real axis. This constant is separate from the strip identity.

The total integral outside `InStrip` is not given as a continuation.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace SICLean.L5.ConjugationStrip

open SICLean.L4

/-- [RW26, pp. 4--5]. The parameter is a positive real number. -/
theorem admissibleB_of_real (b : ℝ) (hb : 0 < b) :
    AdmissibleB (b : ℂ) := by
  simpa only [AdmissibleB, Complex.ofReal_re] using hb

/-- The original convergence strip is conjugation invariant. [RW26, pp. 4--5]. -/
theorem inStrip_conj_iff (b : ℝ) (z : ℂ) :
    InStrip (b : ℂ) ((starRingEnd ℂ) z) ↔ InStrip (b : ℂ) z := by
  simp only [InStrip, Complex.conj_im, abs_neg]

/-- Contour bookkeeping for [RW26, pp. 4--5]. Both sides lie on the same upper line. -/
theorem linePoint_conj_reflect (h x : ℝ) :
    -((starRingEnd ℂ) (linePoint h x)) = linePoint h (-x) := by
  simp [linePoint, add_comm]

/-- The minus sign includes the odd denominator `w`;
the contour, the regular term, and the residue are all retained. -/
theorem kernel_conj_reflect (b : ℝ) (hb : 0 < b) (z : ℂ) (h x : ℝ) :
    (starRingEnd ℂ) (kernel (b : ℂ) z (linePoint h x)) =
      -kernel (b : ℂ) ((starRingEnd ℂ) z) (linePoint h (-x)) := by
  simpa only [linePoint_conj_reflect] using
    ConjugationStripAux.kernel_conj_neg b z (linePoint h x)

/-- The same integral normalization: reflect the upper arc as well as its kernel.
The interval endpoints for the detour are π and 0. -/
theorem arcPoint_conj_reflect (r θ : ℝ) :
    -((starRingEnd ℂ) (arcPoint r θ)) = arcPoint r (Real.pi - θ) := by
  simp only [arcPoint, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, neg_mul]
  rw [show Complex.I * ((Real.pi - θ : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I + -(Complex.I * (θ : ℂ)) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The same normalization, with the tangent `i*w` included.
This is the integrand identity before the orientation substitution. -/
theorem arcKernel_conj_reflect (b : ℝ) (hb : 0 < b) (z : ℂ) (r θ : ℝ) :
    (starRingEnd ℂ) (arcKernel (b : ℂ) z r θ) =
      -arcKernel (b : ℂ) ((starRingEnd ℂ) z) r (Real.pi - θ) := by
  unfold arcKernel
  rw [map_mul, ConjugationStripAux.kernel_conj_neg, map_mul, Complex.conj_I,
    ← arcPoint_conj_reflect r θ]
  ring

/-- [RW26, pp. 4--5]. Uses line integrability and the substitution x ↦ -x. -/
theorem logPhiAtHeight_conj (b : ℝ) (hb : 0 < b) (z : ℂ)
    (hz : InStrip (b : ℂ) z) (h : ℝ)
    (hh : AdmissibleHeight (b : ℂ) h) :
    (starRingEnd ℂ) (logPhiAtHeight (b : ℂ) z h) =
      -logPhiAtHeight (b : ℂ) ((starRingEnd ℂ) z) h := by
  unfold logPhiAtHeight
  rw [← show (∫ x : ℝ, (starRingEnd ℂ) (kernel (b : ℂ) z (linePoint h x))) =
      (starRingEnd ℂ) (∫ x : ℝ, kernel (b : ℂ) z (linePoint h x)) from
    Complex.conjCLE.toContinuousLinearMap.integral_comp_comm
      (integrable_lineKernel _ _ _ (admissibleB_of_real b hb) hz hh)]
  simp_rw [kernel_conj_reflect b hb z h]
  rw [MeasureTheory.integral_neg,
    MeasureTheory.integral_neg_eq_self
      (fun x : ℝ => kernel (b : ℂ) ((starRingEnd ℂ) z) (linePoint h x))]

/-- The same identity for the clockwise upper detour.
The radius stays below the first nonzero pole. -/
theorem detourLog_conj (b : ℝ) (hb : 0 < b) (z : ℂ)
    (hz : InStrip (b : ℂ) z) (r : ℝ) (hr : 0 < r)
    (hrpole : r < poleHeight (b : ℂ)) :
    (starRingEnd ℂ) (detourLog (b : ℂ) z r) =
      -detourLog (b : ℂ) ((starRingEnd ℂ) z) r := by
  have hb' := admissibleB_of_real b hb
  have hr' : AdmissibleHeight (b : ℂ) r := ⟨hr, hrpole⟩
  rw [← logPhi_eq_detour (b : ℂ) z r hb' hz hr',
    ← logPhi_eq_detour (b : ℂ) ((starRingEnd ℂ) z) r hb'
      ((inStrip_conj_iff b z).mpr hz) hr']
  exact logPhiAtHeight_conj b hb z hz _ (canonicalHeight_admissible _ hb')

/-- The same identity at the canonical height used by `phi`. -/
theorem logPhi_conj (b : ℝ) (hb : 0 < b) (z : ℂ)
    (hz : InStrip (b : ℂ) z) :
    (starRingEnd ℂ) (logPhi (b : ℂ) z) =
      -logPhi (b : ℂ) ((starRingEnd ℂ) z) := by
  exact logPhiAtHeight_conj b hb z hz _
    (canonicalHeight_admissible _ (admissibleB_of_real b hb))

/-- Strip form of the conjugation input to [RW26, p. 14, Prop. 7].
The original strip has neither zeros nor poles. -/
theorem phi_conj (b : ℝ) (hb : 0 < b) (z : ℂ)
    (hz : InStrip (b : ℂ) z) :
    (starRingEnd ℂ) (phi (b : ℂ) z) =
      (phi (b : ℂ) ((starRingEnd ℂ) z))⁻¹ := by
  unfold phi
  rw [← Complex.exp_conj, logPhi_conj b hb z hz, Complex.exp_neg]

/-- The same identity and domain, in multiplication form. -/
theorem phi_conj_mul (b : ℝ) (hb : 0 < b) (z : ℂ)
    (hz : InStrip (b : ℂ) z) :
    (starRingEnd ℂ) (phi (b : ℂ) z) *
      phi (b : ℂ) ((starRingEnd ℂ) z) = 1 := by
  rw [phi_conj b hb z hz]
  exact inv_mul_cancel₀ (phi_ne_zero _ _ (admissibleB_of_real b hb)
    ((inStrip_conj_iff b z).mpr hz))

/-- Real-axis consequence of the preceding strip identity.
[RW26, pp. 4--5]. -/
theorem norm_phi_real (b : ℝ) (hb : 0 < b) (x : ℝ) :
    ‖phi (b : ℂ) (x : ℂ)‖ = 1 := by
  have hb' := admissibleB_of_real b hb
  have hw : 0 < stripWidth (b : ℂ) :=
    half_pos (add_pos hb' (admissibleB_inv _ hb'))
  have hz : InStrip (b : ℂ) (x : ℂ) := by simpa only [InStrip,
    Complex.ofReal_im, abs_zero] using hw
  have heq := congrArg (fun w : ℂ => ‖w‖) (phi_conj_mul b hb (x : ℂ) hz)
  simp only [Complex.conj_ofReal, norm_mul, Complex.norm_conj, norm_one] at heq
  nlinarith [norm_nonneg (phi (b : ℂ) (x : ℂ))]

#check SICLean.L4.logPhi_eq_detour
#check SICLean.L4.integrable_lineKernel
#print SICLean.L4.phi
#check phi_conj

end SICLean.L5.ConjugationStrip
