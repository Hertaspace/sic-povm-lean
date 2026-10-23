import SICLean.L4.ModularSectorUpper

set_option autoImplicit false

/-! Elementary full-disk, local-chart and error estimates. -/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.ModularSector

lemma tail_value_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (i : ℤ × ℤ) (z τ : ℂ)
    (hp : (z, τ) ∈ modularPhiNonvanishingDomain M i.1 i.2) :
    modularPhi M i.1 i.2 z τ ≠ 0 :=
  (modularPhi_ne_zero_iff M hM i.1 i.2 z τ hp.1 hp.2.1).2 hp.2.2

lemma lowerError_eq_upperError_reflected (M : SL(2, ℤ)) (i : ℤ × ℤ) (z τ : ℂ)
    (ha : modularPhi M i.1 i.2 z τ ≠ 0)
    (hb : modularPhi M (1 - i.1) (1 - i.2) (-z) τ ≠ 0)
    (hab : modularPhi M i.1 i.2 z τ *
      modularPhi M (1 - i.1) (1 - i.2) (-z) τ = modularReflectionFactor M i.1 i.2 z τ) :
    lowerError M i z τ = upperError M (reflectedIndex i) (-z) τ := by
  unfold lowerError upperError reflectedIndex
  rw [← hab]
  have h₁ : modularPhi M i.1 i.2 z τ /
      (modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) =
      (modularPhi M (1 - i.1) (1 - i.2) (-z) τ)⁻¹ := by field_simp
  have h₂ : (modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) *
      (modularPhi M i.1 i.2 z τ)⁻¹ = modularPhi M (1 - i.1) (1 - i.2) (-z) τ := by
    field_simp
  rw [h₁, h₂, add_comm]

lemma exists_exp_tail (C k ε : ℝ) (hk : 0 < k) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → C * Real.exp (-k * r) < ε := by
  have ht : Tendsto (fun r : ℝ => C * Real.exp (-k * r)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := C) (f := atTop (α := ℝ))).mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hk))
    simpa only [mul_zero, neg_mul, Function.comp_def, id_eq] using h
  obtain ⟨R, hR⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hε))
  exact ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun r hr => hR r (le_trans (le_max_right _ _) hr)⟩

lemma normalized_error (a A : ℂ) :
    ‖a / A - 1‖ + ‖(a / A)⁻¹ - 1‖ = ‖a / A - 1‖ + ‖A * a⁻¹ - 1‖ := by
  simp [div_eq_mul_inv]

lemma product_error_pair (a b : ℂ) (D δ : ℝ) (hD : 0 ≤ D)
    (_hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (ha : ‖a - 1‖ + ‖a⁻¹ - 1‖ ≤ D * δ)
    (hb : ‖b - 1‖ + ‖b⁻¹ - 1‖ ≤ D * δ) :
    ‖a * b - 1‖ + ‖(a * b)⁻¹ - 1‖ ≤ 2 * (D + 2) * D * δ := by
  have hsingle (x y : ℂ) (hx : ‖x - 1‖ ≤ D * δ) (hy : ‖y - 1‖ ≤ D * δ) :
      ‖x * y - 1‖ ≤ (D + 2) * D * δ := by
    have hxn : ‖x‖ ≤ 1 + D := by
      have h := norm_add_le (x - 1) (1 : ℂ)
      simp only [sub_add_cancel, norm_one] at h
      nlinarith [mul_le_of_le_one_right hD hδ']
    calc
      ‖x * y - 1‖ = ‖x * (y - 1) + (x - 1)‖ := by congr 1; ring
      _ ≤ ‖x * (y - 1)‖ + ‖x - 1‖ := norm_add_le _ _
      _ = ‖x‖ * ‖y - 1‖ + ‖x - 1‖ := by rw [norm_mul]
      _ ≤ (1 + D) * (D * δ) + D * δ := by gcongr
      _ = (D + 2) * D * δ := by ring
  have ha₁ : ‖a - 1‖ ≤ D * δ := le_trans (le_add_of_nonneg_right (norm_nonneg _)) ha
  have ha₂ : ‖a⁻¹ - 1‖ ≤ D * δ := le_trans (le_add_of_nonneg_left (norm_nonneg _)) ha
  have hb₁ : ‖b - 1‖ ≤ D * δ := le_trans (le_add_of_nonneg_right (norm_nonneg _)) hb
  have hb₂ : ‖b⁻¹ - 1‖ ≤ D * δ := le_trans (le_add_of_nonneg_left (norm_nonneg _)) hb
  have h₁ := hsingle a b ha₁ hb₁
  have h₂ := hsingle a⁻¹ b⁻¹ ha₂ hb₂
  rw [mul_inv_rev, mul_comm b⁻¹ a⁻¹]
  linarith

lemma chart_unit_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (p : ℂ × ℂ) (hp : p ∈ modularPhiNonvanishingDomain M m n) :
    ∃ (U : Set (ℂ × ℂ)) (κ : ℕ → ℤ), IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, q ∈ modularPhiChartDomain M m n κ ∧
        modularPhiChartNumerator M m n κ q.1 q.2 ≠ 0 ∧
        modularPhiChartDenominator M m n κ q.1 q.2 ≠ 0 ∧
        modularPhi M m n q.1 q.2 = modularPhiChart M m n κ q.1 q.2 := by
  let κ : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M m n j p.1 p.2).1
    (modularPhiFactorPoint M m n j p.1 p.2).2
  have hpκ : p ∈ modularPhiChartDomain M m n κ := by
    refine ⟨hp.1, ?_⟩
    intro j hj
    exact shiftedArgument_inStrip _ _ (modularPhi_sqrt_admissible M p.2 hp.1).1
  have hpreg : p ∈ modularPhiRegularDomain M m n := by
    rw [← modularPhiHolomorphicDomain_eq_regularDomain M hM m n]
    exact ⟨hp.1, hp.2.1⟩
  have hd : modularPhiChartDenominator M m n κ p.1 p.2 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.2
    intro j hj
    exact (continuationDenominator_ne_zero_iff _ _ _
      (modularPhi_sqrt_admissible M p.2 hp.1).1 (hpκ.2 j hj)).2 (hpreg.2 j hj)
  have hn : modularPhiChartNumerator M m n κ p.1 p.2 ≠ 0 := by
    have hf := tail_value_ne_zero M hM (m, n) p.1 p.2 hp
    rw [modularPhi_eq_chart M hM m n κ p hpκ] at hf
    exact (div_ne_zero_iff.mp hf).1
  obtain ⟨han, had⟩ := modularPhiChart_analytic M hM m n κ
  have he : ∀ᶠ q in 𝓝 p, q ∈ modularPhiChartDomain M m n κ ∧
      modularPhiChartNumerator M m n κ q.1 q.2 ≠ 0 ∧
      modularPhiChartDenominator M m n κ q.1 q.2 ≠ 0 := by
    filter_upwards [(modularPhiChartDomain_isOpen M m n κ).mem_nhds hpκ,
      (han p hpκ).continuousAt.eventually_ne hn,
      (had p hpκ).continuousAt.eventually_ne hd] with q hq hqn hqd
    exact ⟨hq, hqn, hqd⟩
  obtain ⟨U, hU, hUopen, hpU⟩ := mem_nhds_iff.1 he
  refine ⟨U, κ, hUopen, hpU, ?_⟩
  intro q hq
  obtain ⟨hqκ, hqn, hqd⟩ := hU hq
  exact ⟨hqκ, hqn, hqd, modularPhi_eq_chart M hM m n κ q hqκ⟩

end SICLean.L4.ModularSector
