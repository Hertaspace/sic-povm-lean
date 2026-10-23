import SICLean.L4.UpperContourBounds
import SICLean.L4.UpperContourSides
import SICLean.L4.UpperContourLowerArcAux

set_option autoImplicit false

/-!
# Incoming lower-ray rotation and the continuous negative quadratic

The polynomial and multiplier are the
existing modularReflectionPolynomial / etaMultiplier, not fresh phases.
Single and ratio lower bounds are established independently. Radius is ℝ.
[RW26, pp. 28--29].
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContour

open SICLean.L4.UpperContourLowerArcAux

def lowerArcIntegral (f : ℂ → ℂ) (v : ℂ) (ψ r : ℝ) : ℂ :=
  arcIntegral f v r (-Real.pi / 2 + ψ) 0

def singleLowerPolynomial (M : SL(2, ℤ)) (m n h ℓ : ℤ) (τ w z : ℂ) : ℂ :=
  UpperWindow.phase M m n h ℓ τ w z + modularReflectionPolynomial M (m + 1) n z τ

def ratioLowerPolynomial (M : SL(2, ℤ)) (m n h ℓ p : ℤ) (τ w y z : ℂ) : ℂ :=
  UpperWindow.phase M m n h ℓ τ w z + modularReflectionPolynomial M (m + 1) n z τ -
    modularReflectionPolynomial M (m + p) n (z + y) τ

/-- Coefficient of u after z=v+u; no big-O is hidden here. -/
def singleLowerLinear (M : SL(2, ℤ)) (m n h ℓ : ℤ) (τ w v : ℂ) : ℂ :=
  UpperWindow.upperSlope M h ℓ τ w - (M 1 0 : ℂ) * v / etaDenom M τ -
    ((m : ℂ) + 1 / 2) + (2 * (n : ℂ) - 1) / (2 * etaDenom M τ)

/--
Literal quadratic coefficient -c/(2T), using the existing P. [RW26, p. 6, pp. 28--29].
-/
theorem single_lower_polynomial_expand (M : SL(2, ℤ)) (m n h ℓ : ℤ)
    (τ w v u : ℂ) (hT : etaDenom M τ ≠ 0) :
    singleLowerPolynomial M m n h ℓ τ w (v + u) =
      singleLowerPolynomial M m n h ℓ τ w v + singleLowerLinear M m n h ℓ τ w v * u -
        (M 1 0 : ℂ) / (2 * etaDenom M τ) * u ^ 2 := by
  dsimp [singleLowerPolynomial, singleLowerLinear, modularReflectionPolynomial,
    UpperWindow.phase, UpperWindow.upperSlope, UpperWindow.s]
  push_cast
  field_simp
  <;> ring

/--
Both quadratic terms cancel in the ratio, leaving exactly L/T; [RW26, pp. 28--29].
-/
theorem ratio_lower_polynomial_affine (M : SL(2, ℤ)) (m n h ℓ p : ℤ)
    (τ w y v u : ℂ) (hT : etaDenom M τ ≠ 0) :
    ratioLowerPolynomial M m n h ℓ p τ w y (v + u) =
      ratioLowerPolynomial M m n h ℓ p τ w y v +
        UpperWindow.lowerSlope M h ℓ p τ w y * u := by
  dsimp [ratioLowerPolynomial, modularReflectionPolynomial, UpperWindow.phase,
    UpperWindow.lowerSlope, UpperWindow.s, UpperWindow.height]
  push_cast
  field_simp
  <;> ring

/--
The full closed angle interval is inside the negative-sine interval. [RW26, pp. 28--29]. Endpoints
are included.
-/
theorem lower_angle_sine_negative (T : ℂ) (ψ θ : ℝ) (hα : 0 < T.arg)
    (hαψ : T.arg < ψ) (hψ : ψ < Real.pi / 4)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    -Real.pi < -Real.pi + 2 * ψ - T.arg ∧
      -Real.pi + 2 * ψ - T.arg ≤ 2 * θ - T.arg ∧
      2 * θ - T.arg ≤ -T.arg ∧ -T.arg < 0 ∧
      Real.sin (2 * θ - T.arg) < 0 := by
  have hψ0 : 0 < ψ := lt_trans hα hαψ
  have hlow : -Real.pi < -Real.pi + 2 * ψ - T.arg := by linarith
  have hlo : -Real.pi + 2 * ψ - T.arg ≤ 2 * θ - T.arg := by linarith [hθ.1]
  have hhi : 2 * θ - T.arg ≤ -T.arg := by linarith [hθ.2]
  refine ⟨hlow, hlo, hhi, neg_neg_of_pos hα, ?_⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi
    (show 0 < -(2 * θ - T.arg) by linarith)
    (show -(2 * θ - T.arg) < Real.pi by linarith)
  rw [Real.sin_neg] at hs
  linarith

/--
All four reflected Φ and inverse values, uniformly on the unbounded
closed lower sector; [RW26, pp. 28--29].
-/
theorem compact_lower_reflected_phi_bounds (M : SL(2, ℤ)) (h ℓ p n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (K : Set UpperWindow.Parameters) (hK : IsCompact K)
    (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ r : ℝ, 0 ≤ r → ∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      let z := arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ
      ‖modularPhi M (-(m : ℤ)) (1 - n) (-z) x.1‖ ≤ C ∧
        ‖(modularPhi M (-(m : ℤ)) (1 - n) (-z) x.1)⁻¹‖ ≤ C ∧
        ‖modularPhi M (1 - (m : ℤ) - p) (1 - n) (-z - x.2.2) x.1‖ ≤ C ∧
        ‖(modularPhi M (1 - (m : ℤ) - p) (1 - n) (-z - x.2.2) x.1)⁻¹‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := compact_lower_reflected_phi_bounds_all_int
    M h ℓ p n ψ σ ρ δ hc K hK hKU
  exact ⟨C, hC, fun x hx m _hm r hr θ hθ => hbound x hx (m : ℤ) r hr θ hθ⟩

/--
Pointwise reflection only on the safe lower sector. μ is the same
etaMultiplier. [RW26, p. 6, pp. 28--29].
-/
theorem single_lower_reflection (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    let z := arcPoint (UpperWindow.base M m n δ x.1) r θ
    kernel .single M m n h ℓ p x z =
      (etaMultiplier M) ^ (-2 : ℤ) * (-1 : ℂ) ^ (m + 1 + n) *
        e (singleLowerPolynomial M m n h ℓ x.1 x.2.1 z) /
        modularPhi M (-m) (1 - n) (-z) x.1 := by
  simpa only [singleLowerPolynomial] using
    single_lower_reflection_raw M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ

/--
Eta factors cancel in the ratio; sign is (-1)^(1-p); [RW26, pp. 28--29].
-/
theorem ratio_lower_reflection (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    let z := arcPoint (UpperWindow.base M m n δ x.1) r θ
    kernel .ratio M m n h ℓ p x z =
      (-1 : ℂ) ^ (1 - p) * e (ratioLowerPolynomial M m n h ℓ p x.1 x.2.1 x.2.2 z) *
        (modularPhi M (1 - m - p) (1 - n) (-z - x.2.2) x.1 /
          modularPhi M (-m) (1 - n) (-z) x.1) := by
  simpa only [ratioLowerPolynomial] using
    ratio_lower_reflection_raw M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ

/--
Lower ratio has linear exponential decay; [RW26, pp. 28--29].
-/
theorem compact_lower_ratio_kernel_bound (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat, ∀ r : ℝ, 0 ≤ r →
      ∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      ‖kernel .ratio M (m : ℤ) n h ℓ p x
        (arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ)‖ ≤
        C * Real.exp (-2 * Real.pi * lam * r) := by
  obtain ⟨C₀, hC₀, hphi⟩ :=
    compact_lower_reflected_phi_bounds M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨lam, hlam, hslope⟩ :=
    UpperWindow.compact_arc_linear_margin M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨B, hB, hbase⟩ : ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat,
      ‖e (ratioLowerPolynomial M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2
        (UpperWindow.base M (m : ℤ) n δ x.1))‖ ≤ B := by
    have hT : ∀ x ∈ K, etaDenom M x.1 ≠ 0 := by
      intro x hx hz
      have hα : 0 < (etaDenom M x.1).arg := (hKU hx).1.2.1
      simpa [hz] using hα
    have hC : ∀ x ∈ K, (M 1 0 : ℂ) ≠ 0 := by
      intro x hx
      exact_mod_cast hc.1.ne'
    have hcont : ContinuousOn (fun x : UpperWindow.Parameters =>
        fun m : Fin (M 1 0).toNat =>
          e (ratioLowerPolynomial M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2
            (UpperWindow.base M (m : ℤ) n δ x.1))) K := by
      apply continuousOn_pi.mpr
      intro m
      dsimp [ratioLowerPolynomial, modularReflectionPolynomial,
        modularBernoulliTwo, UpperWindow.phase, UpperWindow.base, etaMobius, e, etaDenom]
      fun_prop (disch := first | exact hT | exact hC)
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
    refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro x hx m hm
    let i : Fin (M 1 0).toNat := ⟨m, Finset.mem_range.mp hm⟩
    exact (norm_le_pi_norm (fun j : Fin (M 1 0).toNat =>
      e (ratioLowerPolynomial M (j : ℤ) n h ℓ p x.1 x.2.1 x.2.2
        (UpperWindow.base M (j : ℤ) n δ x.1))) i).trans
          ((hB x hx).trans (le_max_right _ _))
  refine ⟨B * C₀ ^ 2, lam, mul_pos hB (sq_pos_of_pos hC₀), hlam, ?_⟩
  intro x hx m hm r hr θ hθ
  have hT := (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1
    x.1 (hKU hx).1).2.2.2.1
  have hp := hphi x hx m hm r hr θ hθ
  have he : ‖e (ratioLowerPolynomial M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2
      (arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ))‖ ≤
      B * Real.exp (-2 * Real.pi * lam * r) := by
    rw [arcPoint, ratio_lower_polynomial_affine _ _ _ _ _ _ _ _ _ _ _ hT]
    exact (affine_exp_bound _ _ r θ lam hr ((hslope x hx).2 θ hθ)).trans
      (mul_le_mul_of_nonneg_right (hbase x hx m hm) (Real.exp_pos _).le)
  calc
    _ = ‖e (ratioLowerPolynomial M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2
        (arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ))‖ *
        (‖modularPhi M (1 - (m : ℤ) - p) (1 - n)
          (-arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ - x.2.2) x.1‖ *
        ‖(modularPhi M (-(m : ℤ)) (1 - n)
          (-arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ) x.1)⁻¹‖) := by
      rw [ratio_lower_reflection M h ℓ p (m : ℤ) n ψ σ ρ δ hc x (hKU hx) r θ hr hθ]
      simp [norm_mul, norm_div, norm_zpow, div_eq_mul_inv]
    _ ≤ (B * Real.exp (-2 * Real.pi * lam * r)) * (C₀ * C₀) :=
      mul_le_mul he (mul_le_mul hp.2.2.1 hp.2.1 (norm_nonneg _) hC₀.le)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg hB.le (Real.exp_pos _).le)
    _ = _ := by ring

/--
Before taking the angle minimum: retain the signed sine and |T|; [RW26, pp. 28--29].
-/
theorem compact_lower_single_signed_bound (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat, ∀ r : ℝ, 0 ≤ r →
      ∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      ‖kernel .single M (m : ℤ) n h ℓ p x
        (arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ)‖ ≤
        C * Real.exp ((Real.pi * (M 1 0 : ℝ) / ‖etaDenom M x.1‖) * r ^ 2 *
          Real.sin (2 * θ - (etaDenom M x.1).arg) + b * r) := by
  obtain ⟨C₀, hC₀, hphi⟩ :=
    compact_lower_reflected_phi_bounds M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨B, hB, hbase⟩ : ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat,
      ‖e (singleLowerPolynomial M (m : ℤ) n h ℓ x.1 x.2.1
        (UpperWindow.base M (m : ℤ) n δ x.1))‖ ≤ B ∧
      ‖singleLowerLinear M (m : ℤ) n h ℓ x.1 x.2.1
        (UpperWindow.base M (m : ℤ) n δ x.1)‖ ≤ B := by
    have hT : ∀ x ∈ K, etaDenom M x.1 ≠ 0 := by
      intro x hx hz
      have hα : 0 < (etaDenom M x.1).arg := (hKU hx).1.2.1
      simpa [hz] using hα
    have hC : ∀ x ∈ K, (M 1 0 : ℂ) ≠ 0 := by
      intro x hx
      exact_mod_cast hc.1.ne'
    have hT2 : ∀ x ∈ K, (2 : ℂ) * etaDenom M x.1 ≠ 0 := by
      intro x hx
      exact mul_ne_zero (by norm_num) (hT x hx)
    let f : UpperWindow.Parameters → Fin (M 1 0).toNat → ℂ × ℂ := fun x m =>
      (e (singleLowerPolynomial M (m : ℤ) n h ℓ x.1 x.2.1
        (UpperWindow.base M (m : ℤ) n δ x.1)),
      singleLowerLinear M (m : ℤ) n h ℓ x.1 x.2.1
        (UpperWindow.base M (m : ℤ) n δ x.1))
    have hcont : ContinuousOn f K := by
      apply continuousOn_pi.mpr
      intro m
      apply ContinuousOn.prodMk
      · dsimp [f, singleLowerPolynomial, modularReflectionPolynomial,
          modularBernoulliTwo, UpperWindow.phase, UpperWindow.base, etaMobius, e, etaDenom]
        fun_prop (disch := first | exact hT | exact hC | exact hT2)
      · dsimp [f, singleLowerLinear, UpperWindow.upperSlope, UpperWindow.s,
          UpperWindow.base, etaDenom]
        fun_prop (disch := first | exact hT | exact hC | exact hT2)
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
    refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro x hx m hm
    let i : Fin (M 1 0).toNat := ⟨m, Finset.mem_range.mp hm⟩
    have hi : ‖f x i‖ ≤ max 1 B :=
      (norm_le_pi_norm (f x) i).trans ((hB x hx).trans (le_max_right _ _))
    exact ⟨(norm_fst_le (f x i)).trans hi, (norm_snd_le (f x i)).trans hi⟩
  let U : ℝ := max 1 ‖(etaMultiplier M) ^ (-2 : ℤ)‖
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨U * B * C₀, 2 * Real.pi * B, mul_pos (mul_pos hU hB) hC₀,
    by positivity, ?_⟩
  intro x hx m hm r hr θ hθ
  have hT := (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1
    x.1 (hKU hx).1).2.2.2.1
  have hp := hphi x hx m hm r hr θ hθ
  have he : ‖e (singleLowerPolynomial M (m : ℤ) n h ℓ x.1 x.2.1
      (arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ))‖ ≤
      B * Real.exp ((Real.pi * (M 1 0 : ℝ) / ‖etaDenom M x.1‖) * r ^ 2 *
        Real.sin (2 * θ - (etaDenom M x.1).arg) + (2 * Real.pi * B) * r) := by
    rw [arcPoint, single_lower_polynomial_expand _ _ _ _ _ _ _ _ _ hT]
    have he₀ := single_exp_signed_bound
      (singleLowerPolynomial M (m : ℤ) n h ℓ x.1 x.2.1 (UpperWindow.base M (m : ℤ) n δ x.1))
      (singleLowerLinear M (m : ℤ) n h ℓ x.1 x.2.1 (UpperWindow.base M (m : ℤ) n δ x.1))
      (etaDenom M x.1) (M 1 0 : ℝ) r θ hT hr
    simp only [Complex.ofReal_intCast] at he₀
    refine he₀.trans (mul_le_mul (hbase x hx m hm).1 ?_ (Real.exp_pos _).le hB.le)
    apply Real.exp_le_exp.mpr
    have hlin := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbase x hx m hm).2
        (show 0 ≤ 2 * Real.pi by positivity)) hr
    linarith
  have hsign : ‖(-1 : ℂ) ^ ((m : ℤ) + 1 + n)‖ = 1 := by simp
  calc
    _ = ‖(etaMultiplier M) ^ (-2 : ℤ)‖ *
        ‖e (singleLowerPolynomial M (m : ℤ) n h ℓ x.1 x.2.1
          (arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ))‖ *
        ‖(modularPhi M (-(m : ℤ)) (1 - n)
          (-arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ) x.1)⁻¹‖ := by
      rw [single_lower_reflection M h ℓ p (m : ℤ) n ψ σ ρ δ hc x (hKU hx) r θ hr hθ]
      simp only [norm_mul, norm_div, hsign, mul_one, norm_inv, div_eq_mul_inv]
    _ ≤ U * (B * Real.exp ((Real.pi * (M 1 0 : ℝ) / ‖etaDenom M x.1‖) * r ^ 2 *
        Real.sin (2 * θ - (etaDenom M x.1).arg) + (2 * Real.pi * B) * r)) * C₀ :=
      mul_le_mul (mul_le_mul (le_max_right _ _) he (norm_nonneg _) hU.le)
        hp.2.1 (norm_nonneg _) (mul_nonneg hU.le (mul_nonneg hB.le (Real.exp_pos _).le))
    _ = _ := by ring

/--
Uniform negative quadratic coefficient a>0 on K, including θ=0; [RW26, pp. 28--29].
-/
theorem compact_lower_single_gaussian_bound (M : SL(2, ℤ)) (h ℓ p n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (K : Set UpperWindow.Parameters) (hK : IsCompact K)
    (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C a b : ℝ, 0 < C ∧ 0 < a ∧ 0 ≤ b ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat, ∀ r : ℝ, 0 ≤ r →
      ∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      ‖kernel .single M (m : ℤ) n h ℓ p x
        (arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ)‖ ≤
        C * Real.exp (-a * r ^ 2 + b * r) := by
  obtain ⟨C, b, hC, hb, hbound⟩ :=
    compact_lower_single_signed_bound M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨a, ha, hquad⟩ :=
    UpperWindow.compact_quadratic_margin M h ℓ p ψ σ ρ δ hc K hK hKU
  refine ⟨C, a, b, hC, ha, hb, ?_⟩
  intro x hx m hm r hr θ hθ
  refine (hbound x hx m hm r hr θ hθ).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have hq := (hquad x hx).2 θ hθ
  have hq' := mul_le_mul_of_nonneg_right hq (sq_nonneg r)
  nlinarith

/--
Separate finite lower arc integral; [RW26, pp. 28--29].
-/
theorem lowerArc_intervalIntegrable (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r : ℝ) (hr : 0 ≤ r) :
    IntervalIntegrable (arcPullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) r) volume (-Real.pi / 2 + ψ) 0 := by
  apply arcPullback_intervalIntegrable
  · linarith [hc.2.2.1, Real.pi_pos]
  · intro θ hθ
    exact (lower_sector_analyticAt kind M h ℓ p m n ψ σ ρ δ hc x hx r θ hr hθ).continuousAt

/--
The two genuinely different lower arc bounds, with angular length. [RW26, pp. 28--29].
One set of constants is chosen before x,m and the real radius r.
-/
theorem compact_lowerArc_bounds (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C lam a b : ℝ, 0 < C ∧ 0 < lam ∧ 0 < a ∧ 0 ≤ b ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat, ∀ r : ℝ, 0 ≤ r →
      ‖lowerArcIntegral (kernel .ratio M (m : ℤ) n h ℓ p x)
        (UpperWindow.base M (m : ℤ) n δ x.1) ψ r‖ ≤
        (Real.pi / 2 - ψ) * C * r * Real.exp (-2 * Real.pi * lam * r) ∧
      ‖lowerArcIntegral (kernel .single M (m : ℤ) n h ℓ p x)
        (UpperWindow.base M (m : ℤ) n δ x.1) ψ r‖ ≤
        (Real.pi / 2 - ψ) * C * r * Real.exp (-a * r ^ 2 + b * r) := by
  obtain ⟨C₁, lam, hC₁, hlam, hratio⟩ :=
    compact_lower_ratio_kernel_bound M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨C₂, a, b, hC₂, ha, hb, hsingle⟩ :=
    compact_lower_single_gaussian_bound M h ℓ p n ψ σ ρ δ hc K hK hKU
  refine ⟨max C₁ C₂, lam, a, b, lt_of_lt_of_le hC₁ (le_max_left _ _),
    hlam, ha, hb, ?_⟩
  intro x hx m hm r hr
  have hangle : -Real.pi / 2 + ψ ≤ 0 := by linarith [hc.2.2.1, Real.pi_pos]
  have hlength : 0 ≤ Real.pi / 2 - ψ := by linarith
  constructor
  · have hnorm := norm_arcIntegral_le (kernel .ratio M (m : ℤ) n h ℓ p x)
      (UpperWindow.base M (m : ℤ) n δ x.1) r (-Real.pi / 2 + ψ) 0
      (C₁ * Real.exp (-2 * Real.pi * lam * r)) hr hangle (hratio x hx m hm r hr)
    change ‖arcIntegral _ _ r _ _‖ ≤ _
    calc
      _ ≤ (Real.pi / 2 - ψ) * r * (C₁ * Real.exp (-2 * Real.pi * lam * r)) := by
        convert hnorm using 1 <;> ring
      _ ≤ (Real.pi / 2 - ψ) * r * (max C₁ C₂ * Real.exp (-2 * Real.pi * lam * r)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
          (mul_nonneg hlength hr)
      _ = _ := by ring
  · have hnorm := norm_arcIntegral_le (kernel .single M (m : ℤ) n h ℓ p x)
      (UpperWindow.base M (m : ℤ) n δ x.1) r (-Real.pi / 2 + ψ) 0
      (C₂ * Real.exp (-a * r ^ 2 + b * r)) hr hangle (hsingle x hx m hm r hr)
    change ‖arcIntegral _ _ r _ _‖ ≤ _
    calc
      _ ≤ (Real.pi / 2 - ψ) * r * (C₂ * Real.exp (-a * r ^ 2 + b * r)) := by
        convert hnorm using 1 <;> ring
      _ ≤ (Real.pi / 2 - ψ) * r * (max C₁ C₂ * Real.exp (-a * r ^ 2 + b * r)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
          (mul_nonneg hlength hr)
      _ = _ := by ring

/--
Actual lower integral vanishes along all real radii tending to infinity; [RW26, pp. 28--29].
-/
theorem lowerArc_tendsto_zero (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (lowerArcIntegral (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) ψ) atTop (𝓝 0) := by
  obtain ⟨C, k, _hC, hk, hbound⟩ :=
    fixed_lower_kernel_exp_bound kind M h ℓ p m n ψ σ ρ δ hc x hx
  apply tendsto_zero_of_radius_exponential_bound _ ((Real.pi / 2 - ψ) * C) k hk
  intro r hr
  have hnorm := norm_arcIntegral_le (kernel kind M m n h ℓ p x)
    (UpperWindow.base M m n δ x.1) r (-Real.pi / 2 + ψ) 0
    (C * Real.exp (-k * r)) hr (by linarith [hc.2.2.1, Real.pi_pos]) (hbound r hr)
  change ‖arcIntegral _ _ r _ _‖ ≤ _
  convert hnorm using 1 <;> ring

/--
Exact finite wedge: outgoing lower ray + arc - real ray =0.
Negating the ray integrals gives the incoming orientation of V; [RW26, pp. 28--29].
-/
theorem finite_lower_rotation (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r : ℝ) (hr : 0 ≤ r) :
    let f := kernel kind M m n h ℓ p x
    let v := UpperWindow.base M m n δ x.1
    rayFinite f v (UpperWindow.rotation (-Real.pi / 2 + ψ)) r +
      lowerArcIntegral f v ψ r - rayFinite f v 1 r = 0 := by
  change rayFinite _ _ _ r + arcIntegral _ _ r _ _ - rayFinite _ _ 1 r = 0
  have hrot0 : UpperWindow.rotation 0 = 1 := by simp [UpperWindow.rotation]
  rw [← hrot0]
  exact finite_rotation_of_differentiable _ _ r (-Real.pi / 2 + ψ) 0 hr
    (by linarith [hc.2.2.1, Real.pi_pos])
    (fun θ hθ t ht =>
      lower_sector_differentiableAt kind M h ℓ p m n ψ σ ρ δ hc x hx t θ ht.1 hθ)

/--
The new lower ray is absolutely integrable by its own ratio/Gaussian
estimate; [RW26, pp. 28--29].
-/
theorem lower_rotated_ray_integrable (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    IntegrableOn (rayPullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (UpperWindow.rotation (-Real.pi / 2 + ψ))) (Ioi 0) := by
  obtain ⟨C, k, _hC, hk, hbound⟩ :=
    fixed_lower_kernel_exp_bound kind M h ℓ p m n ψ σ ρ δ hc x hx
  have hθ : -Real.pi / 2 + ψ ∈ Icc (-Real.pi / 2 + ψ) 0 :=
    ⟨le_rfl, by linarith [hc.2.2.1, Real.pi_pos]⟩
  apply integrableOn_of_exponential_bound _ C k hk
  · exact (lower_rayPullback_continuousOn kind M h ℓ p m n ψ σ ρ δ hc x hx
      (-Real.pi / 2 + ψ) hθ).mono Ioi_subset_Ici_self
  · intro r hr
    rw [norm_rotated_rayPullback]
    exact hbound r (le_of_lt hr) (-Real.pi / 2 + ψ) hθ

/--
Equality of outward ray integrals; both get a minus sign in V and Λ; [RW26, pp. 28--29].
-/
theorem lower_ray_rotation (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    rayIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) 1 =
      rayIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (UpperWindow.rotation (-Real.pi / 2 + ψ)) := by
  have hold := (v_rays_integrable kind M h ℓ p m n ψ σ ρ δ hc x hx).1
  have hnew := lower_rotated_ray_integrable kind M h ℓ p m n ψ σ ρ δ hc x hx
  have hlimOld : Tendsto
      (rayFinite (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) 1)
      atTop (𝓝 (rayIntegral (kernel kind M m n h ℓ p x)
        (UpperWindow.base M m n δ x.1) 1)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hold tendsto_id
  have hlimNew : Tendsto
      (rayFinite (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (UpperWindow.rotation (-Real.pi / 2 + ψ))) atTop
      (𝓝 (rayIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (UpperWindow.rotation (-Real.pi / 2 + ψ)))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hnew tendsto_id
  have hlim := (hlimNew.add (lowerArc_tendsto_zero kind M h ℓ p m n ψ σ ρ δ hc x hx)).sub hlimOld
  have heq : (fun r : ℝ =>
      rayFinite (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (UpperWindow.rotation (-Real.pi / 2 + ψ)) r +
      lowerArcIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) ψ r -
      rayFinite (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) 1 r)
      =ᶠ[atTop] (fun _ => (0 : ℂ)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact finite_lower_rotation kind M h ℓ p m n ψ σ ρ δ hc x hx r hr
  have hzero := tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds
  linear_combination -hzero

#print singleLowerPolynomial
#print singleLowerLinear
#check lower_angle_sine_negative
#check compact_lowerArc_bounds
#check finite_lower_rotation

end SICLean.L4.UpperContour
