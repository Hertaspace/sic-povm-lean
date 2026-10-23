import Mathlib

set_option autoImplicit false

noncomputable section

open Complex Set Real
open scoped Topology

namespace SICLean.QProductCircleAux

/-- A total extension of a continuous function on a unit circle.  Its values off the
circle do not affect its circle integral. -/
def sphereExtension (c : ℂ) (f : C(Metric.sphere c 1, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ Metric.sphere c 1 then f ⟨z, hz⟩ else 0

@[simp]
lemma sphereExtension_coe (c : ℂ) (f : C(Metric.sphere c 1, ℂ))
    (z : Metric.sphere c 1) : sphereExtension c f z = f z := by
  exact dif_pos z.property

lemma sphereExtension_continuousOn (c : ℂ) (f : C(Metric.sphere c 1, ℂ)) :
    ContinuousOn (sphereExtension c f) (Metric.sphere c 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  simpa [Set.domRestrict_def] using f.continuous

lemma sphereExtension_circleIntegrable (c : ℂ) (f : C(Metric.sphere c 1, ℂ)) :
    CircleIntegrable (sphereExtension c f) c 1 :=
  (sphereExtension_continuousOn c f).circleIntegrable (by norm_num)

@[simp]
lemma sphereExtension_add (c : ℂ) (f g : C(Metric.sphere c 1, ℂ)) :
    sphereExtension c (f + g) = sphereExtension c f + sphereExtension c g := by
  funext z
  by_cases hz : z ∈ Metric.sphere c 1
  · simp only [sphereExtension, dif_pos hz, ContinuousMap.add_apply, Pi.add_apply]
  · simp only [sphereExtension, dif_neg hz, Pi.add_apply, add_zero]

@[simp]
lemma sphereExtension_smul (c a : ℂ) (f : C(Metric.sphere c 1, ℂ)) :
    sphereExtension c (a • f) = a • sphereExtension c f := by
  funext z
  by_cases hz : z ∈ Metric.sphere c 1
  · simp only [sphereExtension, dif_pos hz, ContinuousMap.smul_apply, Pi.smul_apply]
  · simp only [sphereExtension, dif_neg hz, Pi.smul_apply, smul_zero]

/-- The normalized contour integral on the unit circle, as a complex linear map. -/
def normalizedCircleIntegralLM (c : ℂ) : C(Metric.sphere c 1, ℂ) →ₗ[ℂ] ℂ where
  toFun f := (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, 1), sphereExtension c f z
  map_add' f g := by
    simp only [sphereExtension_add, Pi.add_apply,
      circleIntegral.integral_add (sphereExtension_circleIntegrable c f)
        (sphereExtension_circleIntegrable c g), smul_add]
  map_smul' a f := by
    simp only [sphereExtension_smul, Pi.smul_apply, circleIntegral.integral_smul,
      RingHom.id_apply]
    exact smul_comm _ _ _

lemma normalizedCircleIntegralLM_norm_le (c : ℂ) (f : C(Metric.sphere c 1, ℂ)) :
    ‖normalizedCircleIntegralLM c f‖ ≤ ‖f‖ := by
  change ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, 1), sphereExtension c f z‖ ≤ ‖f‖
  simpa using
    (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (f := sphereExtension c f) (c := c) (R := 1) (C := ‖f‖)
      (by norm_num) (fun z hz => by
        simpa only [sphereExtension, dif_pos hz] using f.norm_coe_le_norm ⟨z, hz⟩))

/-- The normalized contour integral is continuous with operator norm at most one. -/
def normalizedCircleIntegralCLM (c : ℂ) : C(Metric.sphere c 1, ℂ) →L[ℂ] ℂ :=
  (normalizedCircleIntegralLM c).mkContinuous 1 fun f => by
    simpa using normalizedCircleIntegralLM_norm_le c f

@[simp]
lemma normalizedCircleIntegralCLM_apply (c : ℂ) (f : C(Metric.sphere c 1, ℂ)) :
    normalizedCircleIntegralCLM c f =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, 1), sphereExtension c f z := rfl

lemma normalizedCircleIntegralCLM_norm_le (c : ℂ) (f : C(Metric.sphere c 1, ℂ)) :
    ‖normalizedCircleIntegralCLM c f‖ ≤ ‖f‖ :=
  normalizedCircleIntegralLM_norm_le c f

lemma norm_normalizedCircleIntegralCLM_le_one (c : ℂ) :
    ‖normalizedCircleIntegralCLM c‖ ≤ 1 := by
  apply (normalizedCircleIntegralCLM c).opNorm_le_bound (by norm_num)
  intro f
  simpa using normalizedCircleIntegralCLM_norm_le c f

/-- Any extension with the same restriction gives the same normalized circle integral. -/
lemma normalizedCircleIntegralCLM_eq_of_restrict (c : ℂ)
    (f : C(Metric.sphere c 1, ℂ)) (g : ℂ → ℂ)
    (h : ∀ w : Metric.sphere c 1, f w = g w) :
    normalizedCircleIntegralCLM c f = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, 1), g z := by
  rw [normalizedCircleIntegralCLM_apply]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  simpa only [sphereExtension, dif_pos hz] using h ⟨z, hz⟩

/-- The Cauchy kernel at the center has normalized circle integral one. -/
lemma normalizedCircleIntegralCLM_eq_one_of_restrict (c : ℂ)
    (f : C(Metric.sphere c 1, ℂ))
    (h : ∀ w : Metric.sphere c 1, f w = ((w : ℂ) - c)⁻¹) :
    normalizedCircleIntegralCLM c f = 1 := by
  rw [normalizedCircleIntegralCLM_eq_of_restrict c f (fun z => (z - c)⁻¹) h,
    circleIntegral.integral_sub_center_inv c (by norm_num : (1 : ℝ) ≠ 0)]
  change (2 * π * I : ℂ)⁻¹ * (2 * π * I : ℂ) = 1
  exact inv_mul_cancel₀
    (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)

end SICLean.QProductCircleAux
