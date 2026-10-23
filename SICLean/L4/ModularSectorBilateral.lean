import SICLean.L4.ModularSectorBilateralAux

set_option autoImplicit false

/-!
Twelve proved bilateral and downstream exports.
Full closed disks are included in the bilateral estimates.
[RW26, p. 6, p. 7, (19), Prop. 1--2, Lemma 1]. Local joint units use the existing
charts and only for tail divisor exclusion. The shifted and ratio exports
are stated explicitly.
They make no claim about whole integral kernels or strict tail windows.

The auxiliary
module supplies elementary error estimates and nonvanishing local charts.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.ModularSector

/--
Main full-disk export. One ρ,C,k,R for every τ, index, z and both
tails; [RW26, p. 6, p. 7].
-/
theorem bilateral_uniform_asymptotics (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ρ = parameterRadius M τ₀ α ∧ k = rate M τ₀ α ∧
      ∀ τ ∈ parameterDisk τ₀ ρ, τ ∈ modularPhiDomain M ∧
        ∀ i ∈ F,
          (∀ z ∈ upperSector α R, modularPhi M i.1 i.2 z τ ≠ 0 ∧
            upperError M i z τ ≤ C * Real.exp (-k * ‖z‖)) ∧
          (∀ z : ℂ, -z ∈ upperSector α R → modularPhi M i.1 i.2 z τ ≠ 0 ∧
            lowerError M i z τ ≤ C * Real.exp (-k * ‖z‖)) := by
  obtain ⟨C, R₁, hC, hR₁, hdec⟩ :=
    upper_tail_decay M hM (reflectedFamily F) τ₀ α hT hα hα'
  obtain ⟨R₂, hR₂, hdiv⟩ :=
    tail_divisor_free M hM (reflectedFamily F) τ₀ α hT hα hα'
  obtain ⟨R₃, hR₃, href⟩ := tail_point_reflection M hM F τ₀ α hT hα hα'
  let R := max R₁ (max R₂ R₃)
  have h₁ : R₁ ≤ R := le_max_left _ _
  have h₂ : R₂ ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have h₃ : R₃ ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨parameterRadius M τ₀ α, C, rate M τ₀ α, R,
    parameterRadius_pos M hM τ₀ α hT hα hα', hC,
    (height_safe_rate_pos M τ₀ α hT hα hα').2,
    lt_of_lt_of_le hR₁ h₁, rfl, rfl, ?_⟩
  intro τ hτ
  refine ⟨(parameterDisk_denom_control M hM τ₀ α hT hα hα' hτ).2.2.2, ?_⟩
  intro i hi
  have hiF : i ∈ reflectedFamily F := (reflectedFamily_closed F).1 hi
  have hir : reflectedIndex i ∈ reflectedFamily F :=
    (reflectedFamily_closed F).2 i hiF
  constructor
  · intro z hz
    exact ⟨tail_value_ne_zero M hM i z τ
      (hdiv τ hτ i hiF z (Or.inl (upperSector_antitone le_rfl h₂ hz))).2.2,
      hdec τ hτ i hiF z (upperSector_antitone le_rfl h₁ hz)⟩
  · intro z hz
    have ha := tail_value_ne_zero M hM i z τ
      (hdiv τ hτ i hiF z (Or.inr (upperSector_antitone le_rfl h₂ hz))).2.2
    have hb := tail_value_ne_zero M hM (reflectedIndex i) (-z) τ
      (hdiv τ hτ (reflectedIndex i) hir (-z)
        (Or.inl (upperSector_antitone le_rfl h₂ hz))).2.2
    refine ⟨ha, ?_⟩
    rw [lowerError_eq_upperError_reflected M i z τ ha hb
      (href τ hτ i hi z (upperSector_antitone le_rfl h₃ hz))]
    simpa only [upperError, norm_neg] using
      hdec τ hτ (reflectedIndex i) hir (-z) (upperSector_antitone le_rfl h₁ hz)

/--
Both actual representatives and both normalized lower representatives
are joint analytic at each tail center, including the circle boundary. [RW26, p. 6, (19)]. This does
not assert a global logarithm.
-/
theorem bilateral_tail_joint_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ z : ℂ, (z ∈ upperSector α R ∨ -z ∈ upperSector α R) →
        AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M i.1 i.2 p.1 p.2) (z, τ) ∧
          AnalyticAt ℂ (fun p : ℂ × ℂ => (modularPhi M i.1 i.2 p.1 p.2)⁻¹) (z, τ) ∧
          AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M i.1 i.2 p.1 p.2 /
            modularReflectionFactor M i.1 i.2 p.1 p.2) (z, τ) ∧
          AnalyticAt ℂ (fun p : ℂ × ℂ => modularReflectionFactor M i.1 i.2 p.1 p.2 *
            (modularPhi M i.1 i.2 p.1 p.2)⁻¹) (z, τ) := by
  obtain ⟨R, hR, hdiv⟩ := tail_divisor_free M hM F τ₀ α hT hα hα'
  refine ⟨R, hR, ?_⟩
  intro τ hτ i hi z hz
  have hp := (hdiv τ hτ i hi z hz).2.2
  have ha := modularPhi_joint_analytic_no_poles M hM i.1 i.2 (z, τ) ⟨hp.1, hp.2.1⟩
  have hn := tail_value_ne_zero M hM i z τ hp
  obtain ⟨hA, hAn⟩ := reflectionFactor_joint_unit M hM i.1 i.2 z τ hp.1
  exact ⟨ha, ha.inv hn, ha.div hA hAn, hA.mul (ha.inv hn)⟩

/--
A finite-family common neighborhood around each tail center. It is
not one chart for the whole unbounded sector. [RW26, p. 6].
-/
theorem bilateral_common_unit_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ z : ℂ, (z ∈ upperSector α R ∨ -z ∈ upperSector α R) →
        ∃ U : Set (ℂ × ℂ), IsOpen U ∧ (z, τ) ∈ U ∧
          ∀ i ∈ F, U ⊆ modularPhiNonvanishingDomain M i.1 i.2 ∧
            AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhi M i.1 i.2 p.1 p.2) U ∧
            AnalyticOnNhd ℂ (fun p : ℂ × ℂ => (modularPhi M i.1 i.2 p.1 p.2)⁻¹) U ∧
            ∀ p ∈ U, modularPhi M i.1 i.2 p.1 p.2 ≠ 0 := by
  classical
  obtain ⟨R, hR, hdiv⟩ := tail_divisor_free M hM F τ₀ α hT hα hα'
  refine ⟨R, hR, ?_⟩
  intro τ hτ z hz
  let U : Set (ℂ × ℂ) := ⋂ i ∈ F, modularPhiNonvanishingDomain M i.1 i.2
  have hU : ∀ i ∈ F, U ⊆ modularPhiNonvanishingDomain M i.1 i.2 := by
    intro i hi p hp
    exact Set.mem_iInter₂.mp hp i hi
  refine ⟨U, isOpen_biInter_finset (fun i hi =>
    (modularPhiDivisor_domains_isOpen M hM i.1 i.2).2), ?_, ?_⟩
  · exact Set.mem_iInter₂.mpr (fun i hi => (hdiv τ hτ i hi z hz).2.2)
  · intro i hi
    have hunit : ∀ p ∈ U, modularPhi M i.1 i.2 p.1 p.2 ≠ 0 :=
      fun p hp => tail_value_ne_zero M hM i p.1 p.2 (hU i hi hp)
    have ha : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhi M i.1 i.2 p.1 p.2) U := by
      intro p hp
      exact modularPhi_joint_analytic_no_poles M hM i.1 i.2 p
        ⟨(hU i hi hp).1, (hU i hi hp).2.1⟩
    exact ⟨hU i hi, ha, fun p hp => (ha p hp).inv (hunit p hp), hunit⟩

/--
Concrete local charts with fixed indices and nonzero numerator and
denominator on U. No assertion of a single chart index over the full tail. [RW26, p. 6, (19)].
-/
theorem bilateral_common_charts (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ z : ℂ, (z ∈ upperSector α R ∨ -z ∈ upperSector α R) →
        ∃ (U : Set (ℂ × ℂ)) (κ : (ℤ × ℤ) → ℕ → ℤ), IsOpen U ∧ (z, τ) ∈ U ∧
          ∀ i ∈ F, ∀ p ∈ U,
            p ∈ modularPhiChartDomain M i.1 i.2 (κ i) ∧
              modularPhiChartNumerator M i.1 i.2 (κ i) p.1 p.2 ≠ 0 ∧
              modularPhiChartDenominator M i.1 i.2 (κ i) p.1 p.2 ≠ 0 ∧
              modularPhi M i.1 i.2 p.1 p.2 = modularPhiChart M i.1 i.2 (κ i) p.1 p.2 := by
  classical
  obtain ⟨R, hR, hdiv⟩ := tail_divisor_free M hM F τ₀ α hT hα hα'
  refine ⟨R, hR, ?_⟩
  intro τ hτ z hz
  have he : ∀ i ∈ F, ∃ (U : Set (ℂ × ℂ)) (κ : ℕ → ℤ), IsOpen U ∧ (z, τ) ∈ U ∧
      ∀ p ∈ U, p ∈ modularPhiChartDomain M i.1 i.2 κ ∧
        modularPhiChartNumerator M i.1 i.2 κ p.1 p.2 ≠ 0 ∧
        modularPhiChartDenominator M i.1 i.2 κ p.1 p.2 ≠ 0 ∧
        modularPhi M i.1 i.2 p.1 p.2 = modularPhiChart M i.1 i.2 κ p.1 p.2 := by
    intro i hi
    exact chart_unit_neighborhood M hM i.1 i.2 (z, τ) (hdiv τ hτ i hi z hz).2.2
  choose U κ hU hpU hchart using he
  let V : Set (ℂ × ℂ) := ⋂ i : {i // i ∈ F}, U i.1 i.2
  let κ' : (ℤ × ℤ) → ℕ → ℤ := fun i => if hi : i ∈ F then κ i hi else fun _ => 0
  refine ⟨V, κ', isOpen_iInter_of_finite (fun i => hU i.1 i.2),
    Set.mem_iInter.mpr (fun i => hpU i.1 i.2), ?_⟩
  intro i hi p hp
  simpa only [κ', dif_pos hi] using hchart i hi p (Set.mem_iInter.mp hp ⟨i, hi⟩)

/--
Literal lower-tail reflection form on the full disk. P is the exact
 definition, including its constant term; [RW26, p. 6, Prop. 1]
-/
theorem bilateral_lower_factorization (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ z : ℂ, -z ∈ upperSector α R →
        ∃ ε : ℂ, ‖ε‖ ≤ C * Real.exp (-rate M τ₀ α * ‖z‖) ∧ 1 + ε ≠ 0 ∧
          modularPhi M i.1 i.2 z τ =
            (etaMultiplier M) ^ (-2 : ℤ) * (-1 : ℂ) ^ (i.1 + i.2) *
              e (modularReflectionPolynomial M i.1 i.2 z τ) * (1 + ε) := by
  obtain ⟨ρ, C, k, R, hρ, hC, hk, hR, rfl, rfl, h⟩ :=
    bilateral_uniform_asymptotics M hM F τ₀ α hT hα hα'
  refine ⟨C, R, hC, hR, ?_⟩
  intro τ hτ i hi z hz
  obtain ⟨hn, he⟩ := ((h τ hτ).2 i hi).2 z hz
  have hAn := (reflectionFactor_joint_unit M hM i.1 i.2 z τ (h τ hτ).1).2
  refine ⟨modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ - 1,
    le_trans (le_add_of_nonneg_right (norm_nonneg _)) he, ?_, ?_⟩
  · simpa only [add_sub_cancel] using div_ne_zero hn hAn
  · change modularPhi M i.1 i.2 z τ = modularReflectionFactor M i.1 i.2 z τ * _
    rw [add_sub_cancel]
    field_simp

/--
Uniform ε limits on both tails; no parameter-dependent R is allowed; [RW26, p. 6, p. 7]
-/
theorem bilateral_uniform_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α), ∀ i ∈ F,
        (∀ z ∈ upperSector α R, upperError M i z τ < ε) ∧
        (∀ z : ℂ, -z ∈ upperSector α R → lowerError M i z τ < ε) := by
  obtain ⟨ρ, C, k, R₀, hρ, hC, hk, hR₀, rfl, rfl, h⟩ :=
    bilateral_uniform_asymptotics M hM F τ₀ α hT hα hα'
  intro ε hε
  obtain ⟨R₁, hR₁, he⟩ := exists_exp_tail C (rate M τ₀ α) ε hk hε
  refine ⟨max R₀ R₁, lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro τ hτ i hi
  constructor
  · intro z hz
    exact lt_of_le_of_lt (((h τ hτ).2 i hi).1 z
      (upperSector_antitone le_rfl (le_max_left _ _) hz)).2
      (he ‖z‖ (le_trans (le_max_right _ _) hz.1))
  · intro z hz
    exact lt_of_le_of_lt (((h τ hτ).2 i hi).2 z
      (upperSector_antitone le_rfl (le_max_left _ _) hz)).2
      (he ‖z‖ (by simpa only [norm_neg] using le_trans (le_max_right R₀ R₁) hz.1))

/--
Bounded translations use angle α/2, not the original boundary rays.
[RW26, p. 6, p. 7, (19), Lemma 1].
-/
theorem bounded_translation_sector (α A R₀ : ℝ) (hα : 0 < α)
    (hα' : α < Real.pi / 2) (hA : 0 ≤ A) (hR₀ : 0 ≤ R₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : ℂ, ‖y‖ ≤ A → ∀ z ∈ upperSector α R,
      z + y ∈ upperSector (α / 2) R₀ ∧ ‖z‖ / 2 ≤ ‖z + y‖ := by
  let R₁ := max (2 : ℝ) (2 * A / Real.sin (α / 4))
  let R := max R₁ (2 * R₀ + 1)
  refine ⟨R, lt_of_lt_of_le (by positivity : 0 < 2 * R₀ + 1) (le_max_right _ _), ?_⟩
  intro y hy z hz
  have hz' : z ∈ upperSector α (max (2 * 1) (2 * 1 * A / Real.sin (α / 4))) := by
    simpa only [mul_one, one_mul] using
      upperSector_antitone le_rfl (le_max_left R₁ (2 * R₀ + 1)) hz
  obtain ⟨hx, hnorm⟩ := affine_perturbation_sector α A 1 hα hα' hA zero_lt_one
    1 (Complex.I * y) z one_ne_zero (by simp; positivity) (by simp)
    (by simpa only [norm_mul, Complex.norm_I, one_mul] using hy) hz'
  let q : ℂ := -(Complex.I * z / 1 + Complex.I * y)
  have hq : q ≠ 0 := by
    have hn : 1 ≤ ‖q‖ := by simpa only [q, norm_neg] using hx.1
    intro he
    norm_num [he] at hn
  have hqarg : |q.arg| ≤ Real.pi / 2 - α / 8 - α / 2 := hx.2
  have hmul : Complex.I * q = z + y := by
    simp only [q, div_one, mul_neg, mul_add, ← mul_assoc, Complex.I_mul_I, neg_mul,
      one_mul]
    ring
  have harg : (z + y).arg = Real.pi / 2 + q.arg := by
    rw [← hmul, Complex.arg_mul Complex.I_ne_zero hq, Complex.arg_I]
    simpa only [Complex.arg_I, Set.mem_Ioc] using
      (show -Real.pi < Real.pi / 2 + q.arg ∧ Real.pi / 2 + q.arg ≤ Real.pi by
        constructor <;> linarith [(abs_le.mp hqarg).1, (abs_le.mp hqarg).2, Real.pi_pos])
  have hn : ‖z‖ / 2 ≤ ‖z + y‖ := by
    simpa only [div_one, ← mul_add, norm_mul, Complex.norm_I, one_mul, mul_one] using hnorm
  refine ⟨⟨?_, ?_, ?_⟩, hn⟩
  · have hR : 2 * R₀ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz.1
    linarith
  · rw [harg]
    linarith [(abs_le.mp hqarg).1]
  · rw [harg]
    linarith [(abs_le.mp hqarg).2]

/--
Direct upper-tail call for all bounded complex shifts. Rate
is explicitly halved after |z+y|≥|z|/2; [RW26, p. 6, p. 7, (19)].
-/
theorem bounded_shift_upper_decay (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α A : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) (hA : 0 ≤ A) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ρ = parameterRadius M τ₀ (α / 2) ∧ k = rate M τ₀ (α / 2) / 2 ∧
      ∀ τ ∈ parameterDisk τ₀ ρ, ∀ i ∈ F, ∀ y : ℂ, ‖y‖ ≤ A →
        ∀ z ∈ upperSector α R, modularPhi M i.1 i.2 (z + y) τ ≠ 0 ∧
          upperError M i (z + y) τ ≤ C * Real.exp (-k * ‖z‖) := by
  have hhalf : 0 < α / 2 := by linarith
  have hhalf' : α / 2 < Real.pi / 2 := by linarith
  obtain ⟨ρ, C, k, R₀, hρ, hC, hk, hR₀, rfl, rfl, h⟩ :=
    bilateral_uniform_asymptotics M hM F τ₀ (α / 2) hT hhalf hhalf'
  obtain ⟨R, hR, hshift⟩ := bounded_translation_sector α A R₀ hα hα' hA hR₀.le
  refine ⟨parameterRadius M τ₀ (α / 2), C, rate M τ₀ (α / 2) / 2, R,
    hρ, hC, half_pos hk, hR, rfl, rfl, ?_⟩
  intro τ hτ i hi y hy z hz
  obtain ⟨hzshift, hn⟩ := hshift y hy z hz
  obtain ⟨hne, hdec⟩ := ((h τ hτ).2 i hi).1 (z + y) hzshift
  refine ⟨hne, le_trans hdec ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  nlinarith

/--
Direct lower-tail call, relative to A evaluated at z+y itself; [RW26, p. 6, p. 7, Prop. 1].
-/
theorem bounded_shift_lower_decay (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α A : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) (hA : 0 ≤ A) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ρ = parameterRadius M τ₀ (α / 2) ∧ k = rate M τ₀ (α / 2) / 2 ∧
      ∀ τ ∈ parameterDisk τ₀ ρ, ∀ i ∈ F, ∀ y : ℂ, ‖y‖ ≤ A →
        ∀ z : ℂ, -z ∈ upperSector α R → modularPhi M i.1 i.2 (z + y) τ ≠ 0 ∧
          lowerError M i (z + y) τ ≤ C * Real.exp (-k * ‖z‖) := by
  have hhalf : 0 < α / 2 := by linarith
  have hhalf' : α / 2 < Real.pi / 2 := by linarith
  obtain ⟨ρ, C, k, R₀, hρ, hC, hk, hR₀, rfl, rfl, h⟩ :=
    bilateral_uniform_asymptotics M hM F τ₀ (α / 2) hT hhalf hhalf'
  obtain ⟨R, hR, hshift⟩ := bounded_translation_sector α A R₀ hα hα' hA hR₀.le
  refine ⟨parameterRadius M τ₀ (α / 2), C, rate M τ₀ (α / 2) / 2, R,
    hρ, hC, half_pos hk, hR, rfl, rfl, ?_⟩
  intro τ hτ i hi y hy z hz
  obtain ⟨hzshift, hn⟩ := hshift (-y) (by simpa only [norm_neg] using hy) (-z) hz
  have heq : -z + -y = -(z + y) := by ring
  rw [heq] at hzshift hn
  simp only [norm_neg] at hn
  obtain ⟨hne, hdec⟩ := ((h τ hτ).2 i hi).2 (z + y) hzshift
  refine ⟨hne, le_trans hdec ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  nlinarith

/--
Same constants simultaneously control numerator z and denominator
z+y, with independently selected finite indices; [RW26, p. 6, p. 7].
-/
theorem simultaneous_shift_asymptotics (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α A : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) (hA : 0 ≤ A) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ρ = parameterRadius M τ₀ (α / 2) ∧ k = rate M τ₀ (α / 2) / 2 ∧
      ∀ τ ∈ parameterDisk τ₀ ρ, ∀ i ∈ F, ∀ j ∈ F, ∀ y : ℂ, ‖y‖ ≤ A →
        (∀ z ∈ upperSector α R,
          upperError M i z τ + upperError M j (z + y) τ ≤ C * Real.exp (-k * ‖z‖)) ∧
        (∀ z : ℂ, -z ∈ upperSector α R →
          lowerError M i z τ + lowerError M j (z + y) τ ≤ C * Real.exp (-k * ‖z‖)) := by
  obtain ⟨ρ, C₁, k, R₁, hρ, hC₁, hk, hR₁, rfl, rfl, h₁⟩ :=
    bounded_shift_upper_decay M hM F τ₀ α A hT hα hα' hA
  obtain ⟨ρ, C₂, k, R₂, _, hC₂, _, hR₂, rfl, rfl, h₂⟩ :=
    bounded_shift_lower_decay M hM F τ₀ α A hT hα hα' hA
  refine ⟨parameterRadius M τ₀ (α / 2), 2 * (C₁ + C₂),
    rate M τ₀ (α / 2) / 2, max R₁ R₂,
    hρ, by positivity, hk, lt_of_lt_of_le hR₁ (le_max_left _ _), rfl, rfl, ?_⟩
  intro τ hτ i hi j hj y hy
  have hzero : ‖(0 : ℂ)‖ ≤ A := by simpa using hA
  constructor
  · intro z hz
    have hz' := upperSector_antitone le_rfl (le_max_left R₁ R₂) hz
    have ha := (h₁ τ hτ i hi 0 hzero z hz').2
    have hb := (h₁ τ hτ j hj y hy z hz').2
    simp only [add_zero] at ha
    nlinarith [Real.exp_pos (-(rate M τ₀ (α / 2) / 2) * ‖z‖)]
  · intro z hz
    have hz' := upperSector_antitone le_rfl (le_max_right R₁ R₂) hz
    have ha := (h₂ τ hτ i hi 0 hzero z hz').2
    have hb := (h₂ τ hτ j hj y hy z hz').2
    simp only [add_zero] at ha
    nlinarith [Real.exp_pos (-(rate M τ₀ (α / 2) / 2) * ‖z‖)]

/--
Quotient form directly usable. The lower normalization is
the exact ratio of the old reflection factors, so its quadratic and linear
phases are retained; [RW26, p. 6, p. 7, Prop. 1--2].
-/
theorem bounded_shift_ratio_decay (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α A : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) (hA : 0 ≤ A) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ρ = parameterRadius M τ₀ (α / 2) ∧ k = rate M τ₀ (α / 2) / 2 ∧
      ∀ τ ∈ parameterDisk τ₀ ρ, ∀ i ∈ F, ∀ j ∈ F, ∀ y : ℂ, ‖y‖ ≤ A →
        (∀ z ∈ upperSector α R,
          ‖modularPhi M i.1 i.2 z τ / modularPhi M j.1 j.2 (z + y) τ - 1‖ +
            ‖(modularPhi M i.1 i.2 z τ / modularPhi M j.1 j.2 (z + y) τ)⁻¹ - 1‖ ≤
              C * Real.exp (-k * ‖z‖)) ∧
        (∀ z : ℂ, -z ∈ upperSector α R →
          let q := modularPhi M i.1 i.2 z τ / modularPhi M j.1 j.2 (z + y) τ
          let a := modularReflectionFactor M i.1 i.2 z τ /
            modularReflectionFactor M j.1 j.2 (z + y) τ
          ‖q / a - 1‖ + ‖a * q⁻¹ - 1‖ ≤ C * Real.exp (-k * ‖z‖)) := by
  obtain ⟨ρ, D, k, R, hρ, hD, hk, hR, rfl, rfl, h⟩ :=
    simultaneous_shift_asymptotics M hM F τ₀ α A hT hα hα' hA
  refine ⟨parameterRadius M τ₀ (α / 2), 2 * (D + 2) * D,
    rate M τ₀ (α / 2) / 2, R, hρ, by positivity, hk, hR, rfl, rfl, ?_⟩
  intro τ hτ i hi j hj y hy
  have hδ (z : ℂ) : 0 ≤ Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖) ∧
      Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖) ≤ 1 := by
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg z])⟩
  constructor
  · intro z hz
    have he := (h τ hτ i hi j hj y hy).1 z hz
    have ha : upperError M i z τ ≤
        D * Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖) :=
      le_trans (le_add_of_nonneg_right (by unfold upperError; positivity)) he
    have hb : upperError M j (z + y) τ ≤
        D * Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖) :=
      le_trans (le_add_of_nonneg_left (by unfold upperError; positivity)) he
    have hp := product_error_pair (modularPhi M i.1 i.2 z τ)
      (modularPhi M j.1 j.2 (z + y) τ)⁻¹ D
      (Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖)) hD.le (hδ z).1 (hδ z).2 ha
      (by simpa only [upperError, inv_inv, add_comm] using hb)
    simpa only [div_eq_mul_inv] using hp
  · intro z hz
    have he := (h τ hτ i hi j hj y hy).2 z hz
    have ha : lowerError M i z τ ≤
        D * Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖) :=
      le_trans (le_add_of_nonneg_right (by unfold lowerError; positivity)) he
    have hb : lowerError M j (z + y) τ ≤
        D * Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖) :=
      le_trans (le_add_of_nonneg_left (by unfold lowerError; positivity)) he
    have ha' : ‖modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ - 1‖ +
        ‖(modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ)⁻¹ - 1‖ ≤
        D * Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖) := by
      rw [normalized_error]
      exact ha
    have hb' : ‖(modularPhi M j.1 j.2 (z + y) τ /
        modularReflectionFactor M j.1 j.2 (z + y) τ)⁻¹ - 1‖ +
        ‖((modularPhi M j.1 j.2 (z + y) τ /
        modularReflectionFactor M j.1 j.2 (z + y) τ)⁻¹)⁻¹ - 1‖ ≤
        D * Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖) := by
      rw [inv_inv, add_comm, normalized_error]
      exact hb
    have hp := product_error_pair
      (modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ)
      (modularPhi M j.1 j.2 (z + y) τ /
        modularReflectionFactor M j.1 j.2 (z + y) τ)⁻¹ D
      (Real.exp (-(rate M τ₀ (α / 2) / 2) * ‖z‖)) hD.le (hδ z).1 (hδ z).2 ha' hb'
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm, mul_left_comm, mul_assoc] using hp

/--
Ordinary parameter limits for fixed tail z, from both sides, with
the same real center values of Φ and its inverse. No integral identity
or boundary η limit is asserted here. [RW26, p. 6].
-/
theorem bilateral_parameter_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ i ∈ F, ∀ z : ℂ,
      (z ∈ upperSector α R ∨ -z ∈ upperSector α R) →
        let f := fun τ : ℂ => (modularPhi M i.1 i.2 z τ, (modularPhi M i.1 i.2 z τ)⁻¹)
        Tendsto f (𝓝 (τ₀ : ℂ)) (𝓝 (f (τ₀ : ℂ))) ∧
          Tendsto f (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 (f (τ₀ : ℂ))) ∧
          Tendsto f (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ)) (𝓝 (f (τ₀ : ℂ))) := by
  obtain ⟨R, hR, h⟩ := bilateral_tail_joint_analytic M hM F τ₀ α hT hα hα'
  refine ⟨R, hR, ?_⟩
  intro i hi z hz
  have hτ : (τ₀ : ℂ) ∈ parameterDisk τ₀ (parameterRadius M τ₀ α) :=
    Metric.mem_closedBall_self (parameterRadius_pos M hM τ₀ α hT hα hα').le
  obtain ⟨ha, hai, _, _⟩ := h (τ₀ : ℂ) hτ i hi z hz
  have hg : AnalyticAt ℂ (fun t : ℂ => (z, t)) (τ₀ : ℂ) :=
    analyticAt_const.prod analyticAt_id
  have hc : ContinuousAt (fun t : ℂ =>
      (modularPhi M i.1 i.2 z t, (modularPhi M i.1 i.2 z t)⁻¹)) (τ₀ : ℂ) :=
    ((ha.comp hg).continuousAt).prodMk (hai.comp hg).continuousAt
  exact ⟨hc, hc.mono_left nhdsWithin_le_nhds, hc.mono_left nhdsWithin_le_nhds⟩

end SICLean.L4.ModularSector

#check SICLean.L4.modularPhi_joint_local_quotient
#check SICLean.L4.modularPhi_eq_chart
#check SICLean.L4.modularPhi_joint_analytic_no_poles
#print SICLean.L4.ModularSector.bilateral_uniform_asymptotics
#print SICLean.L4.ModularSector.bounded_shift_ratio_decay
