import SICLean.L4.G1PinchGeometry
import SICLean.L4.ModularSectorBilateral

set_option autoImplicit false

/-! Elementary compactness, strip geometry, and exponential estimates used by `G1RatioTailBounds`.
No integral identity is used here. -/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1RatioTailBoundsAux

theorem closedBall_positive_margin {f : ℂ → ℝ} {z : ℂ}
    (hf : ContinuousAt f z) (hz : 0 < f z) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧ ∀ τ ∈ Metric.closedBall z ρ, κ ≤ f τ := by
  have he : ∀ᶠ τ in 𝓝 z, f z / 2 < f τ :=
    hf (lt_mem_nhds (by linarith : f z / 2 < f z))
  obtain ⟨ρ, hρ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp he
  exact ⟨ρ, f z / 2, hρ, by linarith, fun τ hτ => (hsub hτ).le⟩

theorem parameterDisk_mono {τ₀ ρ ρ' : ℝ} (hρ : ρ ≤ ρ') :
    ModularSector.parameterDisk τ₀ ρ ⊆ ModularSector.parameterDisk τ₀ ρ' :=
  Metric.closedBall_subset_closedBall hρ

theorem upperParameterDisk_mono {τ₀ ρ ρ' : ℝ} (hρ : ρ ≤ ρ') :
    ModularSector.upperParameterDisk τ₀ ρ ⊆ ModularSector.upperParameterDisk τ₀ ρ' :=
  fun _ hτ => ⟨parameterDisk_mono hρ hτ.1, hτ.2⟩

theorem real_mem_upperParameterDisk (τ₀ ρ : ℝ) (hρ : 0 ≤ ρ) :
    (τ₀ : ℂ) ∈ ModularSector.upperParameterDisk τ₀ ρ := by
  exact ⟨Metric.mem_closedBall_self hρ, by simp⟩

theorem positive_real_disk (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (hT : 0 < g1T M τ₀) (f : ℂ → ℝ)
    (hf : ContinuousAt f (τ₀ : ℂ)) (hf₀ : 0 < f (τ₀ : ℂ)) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).re ∧ κ ≤ f τ := by
  obtain ⟨r, κ, hr₀, hκ, hmargin⟩ := closedBall_positive_margin hf hf₀
  have hdom : modularPhiDomain M ∈ 𝓝 (τ₀ : ℂ) :=
    (modularPhiDomain_isOpen M).mem_nhds (real_mem_modularPhiDomain M τ₀ hT)
  obtain ⟨r₁, hr₁, hdisk⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hdom
  have hc : ContinuousAt (fun τ : ℂ => (etaDenom M τ).re) (τ₀ : ℂ) := by
    unfold etaDenom
    fun_prop
  obtain ⟨r₂, κ₂, hr₂, hκ₂, hreal⟩ := closedBall_positive_margin hc (by
    simpa [etaDenom, g1T] using hT)
  refine ⟨min r (min r₁ r₂), κ, lt_min hr₀ (lt_min hr₁ hr₂), hκ, ?_⟩
  intro τ hτ
  have hτ' := parameterDisk_mono (min_le_right r (min r₁ r₂)) hτ
  exact ⟨hdisk (parameterDisk_mono (min_le_left r₁ r₂) hτ'),
    lt_of_lt_of_le hκ₂ (hreal τ (parameterDisk_mono (min_le_right r₁ r₂) hτ')),
    hmargin τ (parameterDisk_mono (min_le_left r _) hτ)⟩

theorem exponent_parameter_continuousAt (M : SL(2, ℤ)) (τ w z : ℂ)
    (n h ell m : ℤ) (hT : etaDenom M τ ≠ 0) :
    ContinuousAt (fun τ => g1Exponent M τ w z n h ell m) τ := by
  unfold g1Exponent etaMobius etaDenom
  unfold etaDenom at hT
  fun_prop (disch := assumption)

theorem polynomial_parameter_continuousAt (M : SL(2, ℤ)) (τ z : ℂ)
    (r n : ℤ) (hT : etaDenom M τ ≠ 0) :
    ContinuousAt (fun τ => modularReflectionPolynomial M r n z τ) τ := by
  unfold modularReflectionPolynomial etaMobius etaDenom
  unfold etaDenom at hT
  fun_prop (disch := assumption)

theorem kernel_ratio_eq (M : SL(2, ℤ)) (τ w y z : ℂ) (n h ell p m : ℤ) :
    ModularCluster.kernel M (G1Pinch.ratioData w y n h ell p m) z τ =
      (modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ) *
        e (g1Exponent M τ w z n h ell m) := by
  rfl

theorem finite_compact_bound {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (F : Finset ℤ) (f : ℤ → X → ℂ)
    (hf : ∀ m ∈ F, ContinuousOn (f m) K) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ F, ∀ x ∈ K, ‖f m x‖ ≤ C := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert m F hm ih =>
    obtain ⟨C, hC, hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hf m (Finset.mem_insert_self _ _))
    refine ⟨max C (D + 1), lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (hD x hx).trans (by linarith [le_max_right C (D + 1)])
    · exact (hbound j hj x hx).trans (le_max_left _ _)

theorem continuous_e : Continuous e := by
  unfold e
  fun_prop

theorem norm_e (z : ℂ) : ‖e z‖ = Real.exp (-(2 * Real.pi) * z.im) := by
  simp [e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem e_add (z w : ℂ) : e (z + w) = e z * e w := by
  simp only [e, mul_add, Complex.exp_add]

theorem e_sub (z w : ℂ) : e (z - w) = e z / e w := by
  simp only [e, mul_sub, Complex.exp_sub]

theorem reflectionFactor_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) : modularReflectionFactor M r n z τ ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (etaMultiplier_ne_zero M hM))
    (zpow_ne_zero _ (by norm_num))) (e_ne_zero _)

theorem reflection_exponential_norm (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r s n : ℤ) (z u τ v : ℂ) :
    ‖(modularReflectionFactor M r n z τ / modularReflectionFactor M s n u τ) * e v‖ =
      ‖e (modularReflectionPolynomial M r n z τ -
        modularReflectionPolynomial M s n u τ + v)‖ := by
  rw [e_add, e_sub]
  simp only [modularReflectionFactor, norm_mul, norm_div, norm_zpow,
    norm_neg, norm_one, one_zpow, mul_one]
  rw [mul_div_mul_left _ _ (zpow_ne_zero _ (norm_ne_zero_iff.mpr
    (etaMultiplier_ne_zero M hM)))]

theorem affine_exp_norm (A B : ℂ) (x t : ℝ) :
    ‖e (A * g1VerticalPoint x t + B)‖ =
      ‖e (A * (x : ℂ) + B)‖ * Real.exp (-(2 * Real.pi * A.re) * t) := by
  have h : A * g1VerticalPoint x t + B =
      (A * (x : ℂ) + B) + A * ((t : ℂ) * Complex.I) := by
    unfold g1VerticalPoint
    ring
  rw [h, e_add, norm_mul, norm_e (A * ((t : ℂ) * Complex.I))]
  congr 2
  simp [Complex.mul_im, Complex.mul_re]
  ring

theorem affine_exp_compact_bound (K : Set ℂ) (hK : IsCompact K)
    (F : Finset ℤ) (a b : ℝ) (A : ℂ → ℂ) (B : ℤ → ℂ → ℂ)
    (hA : ContinuousOn A K) (hB : ∀ m ∈ F, ContinuousOn (B m) K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ m ∈ F, ∀ x ∈ Icc a b,
      ‖e (A τ * (x : ℂ) + B m τ)‖ ≤ C := by
  have hf : ∀ m ∈ F, ContinuousOn
      (fun q : ℂ × ℝ => e (A q.1 * (q.2 : ℂ) + B m q.1)) (K ×ˢ Icc a b) := by
    intro m hm
    apply continuous_e.comp_continuousOn
    exact ((hA.comp continuous_fst.continuousOn (fun _ hq => hq.1)).mul
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn).add
        ((hB m hm).comp continuous_fst.continuousOn (fun _ hq => hq.1))
  obtain ⟨C, hC, hbound⟩ := finite_compact_bound (K ×ˢ Icc a b)
    (hK.prod isCompact_Icc) F _ hf
  exact ⟨C, hC, fun τ hτ m hm x hx => hbound m hm (τ, x) ⟨hτ, hx⟩⟩

theorem vertical_strip_sectors (a b R₀ : ℝ) (hR₀ : 0 ≤ R₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ Icc a b, ∀ t : ℝ,
      (R ≤ t → g1VerticalPoint x t ∈ ModularSector.upperSector (Real.pi / 8) R₀) ∧
      (t ≤ -R → -g1VerticalPoint x t ∈ ModularSector.upperSector (Real.pi / 8) R₀) := by
  have hα : 0 < Real.pi / 4 := by positivity
  have hα' : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨R, hR, htrans⟩ := ModularSector.bounded_translation_sector
    (Real.pi / 4) (max |a| |b|) R₀ hα hα'
    (le_trans (abs_nonneg a) (le_max_left _ _)) hR₀
  have hpure : ∀ t : ℝ, R ≤ t →
      (t : ℂ) * Complex.I ∈ ModularSector.upperSector (Real.pi / 4) R := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hR ht
    simp only [ModularSector.upperSector, Set.mem_ofPred_eq, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos ht0, Complex.arg_real_mul _ ht0, Complex.arg_I]
    exact ⟨ht, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  refine ⟨R, hR, ?_⟩
  intro x hx t
  have hx' : |x| ≤ max |a| |b| := by
    apply abs_le.mpr
    constructor
    · linarith [hx.1, neg_abs_le a, le_max_left |a| |b|]
    · linarith [hx.2, le_abs_self b, le_max_right |a| |b|]
  constructor
  · intro ht
    have H := (htrans (x : ℂ) (by simpa using hx') _ (hpure t ht)).1
    have hangle : Real.pi / 4 / 2 = Real.pi / 8 := by ring
    simpa only [hangle, g1VerticalPoint, add_comm] using H
  · intro ht
    have H := (htrans (- (x : ℂ)) (by simpa using hx') _
      (hpure (-t) (by linarith))).1
    have hangle : Real.pi / 4 / 2 = Real.pi / 8 := by ring
    have hpoint : ((-t : ℝ) : ℂ) * Complex.I + -(x : ℂ) = -g1VerticalPoint x t := by
      simp only [Complex.ofReal_neg, g1VerticalPoint]
      ring
    simpa only [hangle, hpoint] using H

theorem quotient_norm_le {q : ℂ} {D : ℝ} (hq : ‖q - 1‖ ≤ D) : ‖q‖ ≤ D + 1 := by
  calc
    ‖q‖ = ‖(q - 1) + 1‖ := by congr 1; ring
    _ ≤ ‖q - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ D + 1 := by simpa using add_le_add_right hq 1

end SICLean.L4.G1RatioTailBoundsAux
