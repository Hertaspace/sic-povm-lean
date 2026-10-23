import SICLean.L4.ModularSectorFactorsAux

set_option autoImplicit false

/-!
The core finite-product step.
Only earlier interfaces are needed. The parameter disk here is already full;
no sign of Im τ enters the Faddeev argument or finite-product estimates.
The next module packages the closed upper-half-disk result first; [RW26, p. 6, p. 7, (19), Prop.
2(i), Lemma 1]. The finite-product error
inequalities below spell out the elementary step.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.ModularSector

def finiteProductConstant (N : ℕ) (A : ℝ) : ℝ :=
  (N : ℝ) * A * (1 + A) ^ N

/--
The angle budget is α/4; the factor norm loses at most a factor two; [RW26, p. 6, (19)].
This is an explicit affine inequality, not an assumed tail-sector condition.
-/
theorem affine_perturbation_sector (α A B : ℝ) (hα : 0 < α)
    (hα' : α < Real.pi / 2) (hA : 0 ≤ A) (hB : 0 < B)
    (b H z : ℂ) (hb : b ≠ 0) (harg : |b.arg| ≤ α / 8)
    (hbB : ‖b‖ ≤ B) (hH : ‖H‖ ≤ A)
    (hz : z ∈ upperSector α (max (2 * B) (2 * B * A / Real.sin (α / 4)))) :
    Sector.InDecaySector (α / 8) (α / 2) (Complex.I * z / b + H) ∧
      ‖z‖ / (2 * B) ≤ ‖Complex.I * z / b + H‖ := by
  have hp := Real.pi_pos
  have hs : 0 < Real.sin (α / 4) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hzR := hz.1
  have hzlo := hz.2.1
  have hzhi := hz.2.2
  have hzB : 2 * B ≤ ‖z‖ := (le_max_left _ _).trans hzR
  have hzA : 2 * B * A ≤ ‖z‖ * Real.sin (α / 4) :=
    (div_le_iff₀ hs).mp ((le_max_right _ _).trans hzR)
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  let u : ℂ := Complex.I * z / b
  have hu0 : u ≠ 0 := div_ne_zero (mul_ne_zero Complex.I_ne_zero hz0) hb
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hu : ‖u‖ = ‖z‖ / ‖b‖ := by simp [u]
  have huB : ‖z‖ ≤ ‖u‖ * B := by
    have h := mul_le_mul_of_nonneg_left hbB (norm_nonneg u)
    rw [hu, div_mul_cancel₀ _ hbn.ne'] at h
    simpa only [hu] using h
  have huA : A ≤ ‖u‖ * Real.sin (α / 4) / 2 := by
    have h := mul_le_mul_of_nonneg_right huB hs.le
    nlinarith
  have hq : ‖H / u‖ ≤ Real.sin (α / 4) / 2 := by
    rw [norm_div, div_le_iff₀ hun]
    linarith
  obtain ⟨hqarg, hqnorm⟩ := arg_one_add_small (α / 4) (by linarith)
    (by linarith) (H / u) hq
  have hq0 : 1 + H / u ≠ 0 := norm_pos_iff.mp (by linarith)
  have hbinv : (b⁻¹).arg = -b.arg := by
    rw [Complex.arg_inv, if_neg]
    exact ne_of_lt (lt_of_le_of_lt (le_abs_self _) (by linarith))
  have harg1 : ((-Complex.I) * z).arg = -(Real.pi / 2) + z.arg := by
    rw [← Complex.arg_neg_I]
    apply Complex.arg_mul (neg_ne_zero.mpr Complex.I_ne_zero) hz0
    rw [Complex.arg_neg_I]
    constructor <;> linarith
  have hargu : (-u).arg = -(Real.pi / 2) + z.arg - b.arg := by
    have heq : -u = ((-Complex.I) * z) * b⁻¹ := by dsimp [u]; ring
    rw [heq]
    have hbarg := abs_le.mp harg
    rw [Complex.arg_mul (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0)
      (inv_ne_zero hb) (by rw [harg1, hbinv]; constructor <;> linarith), harg1, hbinv]
    ring
  have hfactor : -(u + H) = (-u) * (1 + H / u) := by field_simp
  have hargx : (-(u + H)).arg = (-u).arg + (1 + H / u).arg := by
    rw [hfactor]
    apply Complex.arg_mul (neg_ne_zero.mpr hu0) hq0
    rw [hargu]
    have hbarg := abs_le.mp harg
    have hqarg' := abs_le.mp hqarg
    constructor <;> linarith
  have hnorm : ‖z‖ / (2 * B) ≤ ‖u + H‖ := by
    have ht := norm_sub_norm_le u (-H)
    have ht' : ‖u‖ - ‖H‖ ≤ ‖u + H‖ := by simpa using ht
    have hsle := Real.sin_le_one (α / 4)
    have hAhalf : A ≤ ‖u‖ / 2 := by nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 2 * B)).2
    nlinarith
  refine ⟨⟨?_, ?_⟩, hnorm⟩
  · have : 1 ≤ ‖z‖ / (2 * B) := (le_div_iff₀ (by positivity)).2 (by simpa using hzB)
    exact this.trans hnorm
  · change |(-(u + H)).arg| ≤ Sector.opening (α / 8) (α / 2)
    rw [hargx, hargu, abs_le]
    dsimp [Sector.opening]
    have hbarg := abs_le.mp harg
    have hqarg' := abs_le.mp hqarg
    constructor <;> linarith

/--
One R for all parameters, indices and all c factors; [RW26, p. 6, (19)].
-/
theorem factorArguments_uniform_sector (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ j ∈ Finset.range (M 1 0).toNat, ∀ z ∈ upperSector α R,
        Sector.InDecaySector (α / 8) (α / 2) (modularPhiFactorPoint M i.1 i.2 j z τ).2 ∧
          ‖z‖ / (2 * sqrtUpper M τ₀) ≤ ‖(modularPhiFactorPoint M i.1 i.2 j z τ).2‖ := by
  obtain ⟨A, hA, hbound⟩ := factorOffset_uniform_bound M hM F τ₀ α hT hα hα'
  have hB : 0 < sqrtUpper M τ₀ := Real.sqrt_pos.2 (by linarith)
  refine ⟨factorRadius M τ₀ α A, lt_of_lt_of_le (by positivity : 0 < 2 * sqrtUpper M τ₀)
    (le_max_left _ _), ?_⟩
  intro τ hτ i hi j hj z hz
  have hbmem : Complex.sqrt (etaDenom M τ) ∈
      sqrtParameters M τ₀ (parameterRadius M τ₀ α) := ⟨τ, hτ, rfl⟩
  obtain ⟨_, _, hbB, hbarg⟩ := sqrtParameters_bounds M hM τ₀ α hT hα hα' hbmem
  have hdom := (parameterDisk_denom_control M hM τ₀ α hT hα hα' hτ).2.2.2
  have hb0 := (modularPhi_sqrt_admissible M τ hdom).2.2
  rw [factorPoint_split]
  exact affine_perturbation_sector α A (sqrtUpper M τ₀) hα hα' (by linarith) hB
    _ _ z hb0 hbarg hbB (hbound τ hτ i hi j hj) hz

/--
Factor divisor exclusion is a conclusion; no point-value assumption; [RW26, p. 6, (19)]. Uses
rotated-strip divisor exclusion.
-/
theorem factor_upper_divisor_free (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ j ∈ Finset.range (M 1 0).toNat, ∀ z ∈ upperSector α R,
        phiPoleMultiplicity (modularPhiFactorPoint M i.1 i.2 j z τ).1
            (modularPhiFactorPoint M i.1 i.2 j z τ).2 = 0 ∧
          phiZeroMultiplicity (modularPhiFactorPoint M i.1 i.2 j z τ).1
            (modularPhiFactorPoint M i.1 i.2 j z τ).2 = 0 := by
  obtain ⟨R, hR, hargs⟩ := factorArguments_uniform_sector M hM F τ₀ α hT hα hα'
  refine ⟨R, hR, ?_⟩
  intro τ hτ i hi j hj z hz
  exact phi_divisor_free_decaySector (sqrtParameters_family M hM τ₀ α hT hα hα')
    (margin_uniform M hM τ₀ α hT hα hα') ⟨τ, hτ, rfl⟩
    (hargs τ hτ i hi j hj z hz).1

/--
The actual φ factor, with its actual center value, is a joint unit, by the existing joint charts.
[RW26, p. 6, (19)].
-/
theorem factor_upper_joint_regular (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ j ∈ Finset.range (M 1 0).toNat, ∀ z ∈ upperSector α R,
        AnalyticAt ℂ (fun p : ℂ × ℂ =>
          phiExtended (modularPhiFactorPoint M i.1 i.2 j p.1 p.2).1
            (modularPhiFactorPoint M i.1 i.2 j p.1 p.2).2) (z, τ) ∧
          phiExtended (modularPhiFactorPoint M i.1 i.2 j z τ).1
            (modularPhiFactorPoint M i.1 i.2 j z τ).2 ≠ 0 := by
  obtain ⟨R, hR, hfree⟩ := factor_upper_divisor_free M hM F τ₀ α hT hα hα'
  refine ⟨R, hR, ?_⟩
  intro τ hτ i hi j hj z hz
  have hdom := (parameterDisk_denom_control M hM τ₀ α hT hα hα' hτ).2.2.2
  have hb := (modularPhi_sqrt_admissible M τ hdom).1
  obtain ⟨hp, hz'⟩ := hfree τ hτ i hi j hj z hz
  have hmem : modularPhiFactorPoint M i.1 i.2 j z τ ∈ phiRegularDomain := ⟨hb, hp⟩
  refine ⟨?_, (phiExtended_ne_zero_iff _ _ hb hp).2 hz'⟩
  simpa only [Function.comp_def] using (analyticAt_phiExtended_joint hmem).comp (x := (z, τ))
    ((modularPhiFactorPoint_analytic M i.1 i.2 j) (z, τ) hdom)

/--
Simultaneous forward/inverse factor estimates, with the explicit k; [RW26, p. 6, p. 7, (19), Lemma
1] is only a comparison.
-/
theorem factor_uniform_decay (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ j ∈ Finset.range (M 1 0).toNat, ∀ z ∈ upperSector α R,
        ‖phiExtended (modularPhiFactorPoint M i.1 i.2 j z τ).1
              (modularPhiFactorPoint M i.1 i.2 j z τ).2 - 1‖ +
          ‖(phiExtended (modularPhiFactorPoint M i.1 i.2 j z τ).1
              (modularPhiFactorPoint M i.1 i.2 j z τ).2)⁻¹ - 1‖ ≤
            C * Real.exp (-rate M τ₀ α * ‖z‖) := by
  obtain ⟨R, hR, hargs⟩ := factorArguments_uniform_sector M hM F τ₀ α hT hα hα'
  have hK := sqrtParameters_family M hM τ₀ α hT hα hα'
  have hlam := margin_uniform M hM τ₀ α hT hα hα'
  have hv := (height_safe_rate_pos M τ₀ α hT hα hα').1
  obtain ⟨C, hC, hdecay⟩ := Sector.phiExtended_sector_decay_with_margin hK hlam hv
  refine ⟨C, R, hC, hR, ?_⟩
  intro τ hτ i hi j hj z hz
  obtain ⟨hsector, hnorm⟩ := hargs τ hτ i hi j hj z hz
  apply (hdecay _ ⟨τ, hτ, rfl⟩ _ hsector).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have hB : 0 < sqrtUpper M τ₀ := Real.sqrt_pos.2 (by linarith)
  have h := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * height M τ₀ α by
    linarith [hv.1])
  have heq : 2 * height M τ₀ α * (‖z‖ / (2 * sqrtUpper M τ₀)) =
      rate M τ₀ α * ‖z‖ := by
    dsimp [rate]
    field_simp
  rw [heq] at h
  linarith only [h]

/--
Elementary forward finite-product error, including N=0.
[RW26, p. 6, (19)].
-/
theorem finite_product_error (N : ℕ) (f : ℕ → ℂ) (A δ : ℝ)
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (hf : ∀ j ∈ Finset.range N, ‖f j - 1‖ ≤ A * δ) :
    ‖(∏ j ∈ Finset.range N, f j) - 1‖ ≤ finiteProductConstant N A * δ := by
  induction N with
  | zero => simp [finiteProductConstant]
  | succ N ih =>
    have hfN := hf N (Finset.self_mem_range_succ N)
    have hf' : ∀ j ∈ Finset.range N, ‖f j - 1‖ ≤ A * δ :=
      fun j hj => hf j (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))
    have hnorm : ‖f N‖ ≤ 1 + A := by
      calc
        ‖f N‖ = ‖(f N - 1) + 1‖ := by congr 1; ring
        _ ≤ ‖f N - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + A := by norm_num at *; nlinarith
    have hp : 1 ≤ (1 + A) ^ (N + 1) := one_le_pow₀ (by linarith)
    calc
      ‖(∏ j ∈ Finset.range (N + 1), f j) - 1‖ =
          ‖((∏ j ∈ Finset.range N, f j) - 1) * f N + (f N - 1)‖ := by
            rw [Finset.prod_range_succ]; congr 1; ring
      _ ≤ ‖((∏ j ∈ Finset.range N, f j) - 1) * f N‖ + ‖f N - 1‖ := norm_add_le _ _
      _ = ‖(∏ j ∈ Finset.range N, f j) - 1‖ * ‖f N‖ + ‖f N - 1‖ := by rw [norm_mul]
      _ ≤ (finiteProductConstant N A * δ) * (1 + A) + A * δ := by
        exact add_le_add (mul_le_mul (ih hf') hnorm (norm_nonneg _) (by
          dsimp [finiteProductConstant]; positivity)) hfN
      _ ≤ finiteProductConstant (N + 1) A * δ := by
        dsimp [finiteProductConstant]
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        have := mul_le_mul_of_nonneg_left hp (mul_nonneg hA hδ)
        rw [pow_succ] at this
        nlinarith only [this]

/--
The inverse is controlled from the same factors, with no new R.
[RW26, p. 6, (19)].
-/
theorem finite_inverse_product_error (N : ℕ) (f : ℕ → ℂ) (A δ : ℝ)
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (hf : ∀ j ∈ Finset.range N, ‖(f j)⁻¹ - 1‖ ≤ A * δ) :
    ‖(∏ j ∈ Finset.range N, f j)⁻¹ - 1‖ ≤ finiteProductConstant N A * δ := by
  simpa only [← Finset.prod_inv_distrib] using
    finite_product_error N (fun j => (f j)⁻¹) A δ hA hδ hδ' hf

/--
Joint regularity of the literal finite product. [RW26, p. 6, (19)].
-/
theorem upper_tail_joint_regular (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ z ∈ upperSector α R,
        (z, τ) ∈ modularPhiRegularDomain M i.1 i.2 ∧
          AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M i.1 i.2 p.1 p.2) (z, τ) ∧
          AnalyticAt ℂ (fun p : ℂ × ℂ => (modularPhi M i.1 i.2 p.1 p.2)⁻¹) (z, τ) ∧
          modularPhi M i.1 i.2 z τ ≠ 0 := by
  obtain ⟨R₁, hR₁, hfree⟩ := factor_upper_divisor_free M hM F τ₀ α hT hα hα'
  obtain ⟨R₂, hR₂, hreg⟩ := factor_upper_joint_regular M hM F τ₀ α hT hα hα'
  refine ⟨max R₁ R₂, lt_of_lt_of_le hR₁ (le_max_left _ _), ?_⟩
  intro τ hτ i hi z hz
  have hz₁ := upperSector_antitone (le_refl α) (le_max_left R₁ R₂) hz
  have hz₂ := upperSector_antitone (le_refl α) (le_max_right R₁ R₂) hz
  have hdom := (parameterDisk_denom_control M hM τ₀ α hT hα hα' hτ).2.2.2
  have hmem : (z, τ) ∈ modularPhiRegularDomain M i.1 i.2 :=
    ⟨hdom, fun j hj => (hfree τ hτ i hi j hj z hz₁).1⟩
  have hA := (modularPhi_joint_analytic_regular M hM i.1 i.2) (z, τ) hmem
  have hn : modularPhi M i.1 i.2 z τ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => (hreg τ hτ i hi j hj z hz₂).2)
  exact ⟨hmem, hA, hA.inv hn, hn⟩

/--
Raw full-disk upper-z estimate. C and R precede all moving variables; [RW26, p. 6, p. 7, (19), Lemma
1].
-/
theorem upper_tail_decay (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ z ∈ upperSector α R,
        ‖modularPhi M i.1 i.2 z τ - 1‖ + ‖(modularPhi M i.1 i.2 z τ)⁻¹ - 1‖ ≤
          C * Real.exp (-rate M τ₀ α * ‖z‖) := by
  obtain ⟨A, R, hA, hR, hfactor⟩ := factor_uniform_decay M hM F τ₀ α hT hα hα'
  let C := 2 * finiteProductConstant (M 1 0).toNat A
  have hN : 0 < (M 1 0).toNat := by omega
  have hC : 0 < C := by dsimp [C, finiteProductConstant]; positivity
  refine ⟨C, R, hC, hR, ?_⟩
  intro τ hτ i hi z hz
  let δ := Real.exp (-rate M τ₀ α * ‖z‖)
  have hδ : 0 ≤ δ := (Real.exp_pos _).le
  have hδ' : δ ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hk := (height_safe_rate_pos M τ₀ α hT hα hα').2
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (norm_nonneg z))
  let f := fun j => phiExtended (modularPhiFactorPoint M i.1 i.2 j z τ).1
    (modularPhiFactorPoint M i.1 i.2 j z τ).2
  have hforward : ∀ j ∈ Finset.range (M 1 0).toNat, ‖f j - 1‖ ≤ A * δ := by
    intro j hj
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hfactor τ hτ i hi j hj z hz)
  have hinverse : ∀ j ∈ Finset.range (M 1 0).toNat, ‖(f j)⁻¹ - 1‖ ≤ A * δ := by
    intro j hj
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hfactor τ hτ i hi j hj z hz)
  have hp := finite_product_error _ f A δ hA.le hδ hδ' hforward
  have hi' := finite_inverse_product_error _ f A δ hA.le hδ hδ' hinverse
  change ‖(∏ j ∈ Finset.range (M 1 0).toNat, f j) - 1‖ +
    ‖(∏ j ∈ Finset.range (M 1 0).toNat, f j)⁻¹ - 1‖ ≤ C * δ
  dsimp [C]
  linarith

/--
Tail values and their inverses are uniformly bounded without any
q-product interpretation on the real axis; [RW26, p. 7, Lemma 1]
-/
theorem upper_tail_bounded (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ z ∈ upperSector α R,
        ‖modularPhi M i.1 i.2 z τ‖ + ‖(modularPhi M i.1 i.2 z τ)⁻¹‖ ≤ 3 := by
  obtain ⟨C, R₀, hC, hR₀, hdecay⟩ := upper_tail_decay M hM F τ₀ α hT hα hα'
  have hk := (height_safe_rate_pos M τ₀ α hT hα hα').2
  refine ⟨max R₀ (Real.log C / rate M τ₀ α), lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro τ hτ i hi z hz
  have hz₀ := upperSector_antitone (le_refl α) (le_max_left _ _) hz
  have hlog : Real.log C ≤ rate M τ₀ α * ‖z‖ := by
    have := (div_le_iff₀ hk).mp ((le_max_right _ _).trans hz.1)
    simpa [mul_comm] using this
  have hsmall : C * Real.exp (-rate M τ₀ α * ‖z‖) ≤ 1 := by
    calc
      _ = Real.exp (Real.log C + -rate M τ₀ α * ‖z‖) := by
        rw [Real.exp_add, Real.exp_log hC]
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have herrors := (hdecay τ hτ i hi z hz₀).trans hsmall
  have hf : ‖modularPhi M i.1 i.2 z τ‖ ≤ ‖modularPhi M i.1 i.2 z τ - 1‖ + 1 := by
    simpa using (norm_sub_norm_le (modularPhi M i.1 i.2 z τ) (1 : ℂ))
  have hi' : ‖(modularPhi M i.1 i.2 z τ)⁻¹‖ ≤
      ‖(modularPhi M i.1 i.2 z τ)⁻¹ - 1‖ + 1 := by
    simpa using (norm_sub_norm_le (modularPhi M i.1 i.2 z τ)⁻¹ (1 : ℂ))
  linarith

end SICLean.L4.ModularSector

#check SICLean.L4.Sector.phi_divisor_free_rotatedStrip
#check SICLean.L4.phiExtended_joint_holomorphic
#check SICLean.L4.modularPhi_joint_analytic_regular
#print SICLean.L4.modularPhi
#print SICLean.L4.ModularSector.upper_tail_decay
