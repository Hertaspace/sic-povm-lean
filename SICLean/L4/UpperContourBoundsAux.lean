import SICLean.L4.UpperContourShifts

set_option autoImplicit false

/-! Scalar product estimates and norm identities for the upper contour bounds. -/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContourBoundsAux

theorem lower_factor_pos (r q : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ν : ℕ) : 0 < 1 - r * q ^ ν := by
  have hle : r * q ^ ν ≤ r :=
    mul_le_of_le_one_right hr0 (pow_le_one₀ hq0 hq1.le)
  linarith

theorem lower_multipliable (r q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Multipliable (fun ν : ℕ => 1 - r * q ^ ν) := by
  have hs : Summable (fun ν : ℕ => -r * q ^ ν) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (-r)
  simpa [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs

theorem productLower_pos (r q : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < ∏' ν : ℕ, (1 - r * q ^ ν) := by
  have hs : Summable (fun ν : ℕ => -r * q ^ ν) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (-r)
  have hlog : Summable (fun ν : ℕ => Real.log (1 - r * q ^ ν)) := by
    simpa [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs
  rw [← Real.rexp_tsum_eq_tprod (lower_factor_pos r q hr0 hr1 hq0 hq1) hlog]
  exact Real.exp_pos _

theorem finite_product_lower_of_norm_le (u q : ℂ) (r q₀ : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hq₀0 : 0 ≤ q₀) (hq₀1 : q₀ < 1)
    (hq : ‖q‖ ≤ q₀) (hu : ‖u‖ ≤ r) (N : ℕ) :
    (∏' ν : ℕ, (1 - r * q₀ ^ ν)) ≤ ‖qPochhammerNat u q N‖ := by
  have hpos := lower_factor_pos r q₀ hr0 hr1 hq₀0 hq₀1
  have hanti : Antitone (fun n : ℕ => ∏ ν ∈ Finset.range n, (1 - r * q₀ ^ ν)) := by
    intro m n hmn
    apply Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.range_mono hmn)
    · exact fun ν _ => (hpos ν).le
    · intro ν _ _
      exact sub_le_self _ (mul_nonneg hr0 (pow_nonneg hq₀0 _))
  calc
    (∏' ν : ℕ, (1 - r * q₀ ^ ν))
        ≤ ∏ ν ∈ Finset.range N, (1 - r * q₀ ^ ν) :=
      hanti.le_of_tendsto (lower_multipliable r q₀ hq₀0 hq₀1).hasProd.tendsto_prod_nat N
    _ ≤ ‖qPochhammerNat u q N‖ := by
      rw [qPochhammerNat, norm_prod]
      refine Finset.prod_le_prod₀ (fun ν _ => (hpos ν).le) ?_
      intro ν _
      have hmul : ‖u * q ^ ν‖ ≤ r * q₀ ^ ν := by
        rw [norm_mul, norm_pow]
        exact mul_le_mul hu (pow_le_pow_left₀ (norm_nonneg q) hq ν)
          (by positivity) hr0
      calc
        1 - r * q₀ ^ ν ≤ 1 - ‖u * q ^ ν‖ := sub_le_sub_left hmul 1
        _ ≤ ‖1 - u * q ^ ν‖ := by simpa using norm_sub_norm_le (1 : ℂ) (u * q ^ ν)

theorem finite_product_lower (u q : ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq1 : ‖q‖ < 1) (hu : ‖u‖ ≤ r) (N : ℕ) :
    (∏' ν : ℕ, (1 - r * ‖q‖ ^ ν)) ≤ ‖qPochhammerNat u q N‖ := by
  exact finite_product_lower_of_norm_le u q r ‖q‖ hr0 hr1 (norm_nonneg q) hq1 le_rfl hu N

theorem upper_multipliable (D q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Multipliable (fun ν : ℕ => 1 + D * q ^ ν) := by
  exact Real.multipliable_one_add_of_summable
    ((summable_geometric_of_lt_one hq0 hq1).mul_left D)

theorem productUpper_pos (D q : ℝ) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < ∏' ν : ℕ, (1 + D * q ^ ν) := by
  have hs : Summable (fun ν : ℕ => D * q ^ ν) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left D
  have hpos : ∀ ν : ℕ, 0 < 1 + D * q ^ ν := by
    intro ν
    positivity
  rw [← Real.rexp_tsum_eq_tprod hpos (Real.summable_log_one_add_of_summable hs)]
  exact Real.exp_pos _

theorem finite_product_upper_of_norm_le (v q : ℂ) (D q₀ : ℝ)
    (hD : 0 ≤ D) (hq₀0 : 0 ≤ q₀) (hq₀1 : q₀ < 1)
    (hq : ‖q‖ ≤ q₀) (hv : ‖v‖ ≤ D) (N : ℕ) :
    ‖qPochhammerNat v q N‖ ≤ ∏' ν : ℕ, (1 + D * q₀ ^ ν) := by
  have hone : ∀ ν : ℕ, 1 ≤ 1 + D * q₀ ^ ν := by
    intro ν
    exact le_add_of_nonneg_right (mul_nonneg hD (pow_nonneg hq₀0 ν))
  have hmono : Monotone (fun n : ℕ => ∏ ν ∈ Finset.range n, (1 + D * q₀ ^ ν)) := by
    intro m n hmn
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.range_mono hmn)
      (fun ν _ => zero_le_one.trans (hone ν)) (fun ν _ _ => hone ν)
  calc
    ‖qPochhammerNat v q N‖ ≤ ∏ ν ∈ Finset.range N, (1 + D * q₀ ^ ν) := by
      rw [qPochhammerNat, norm_prod]
      refine Finset.prod_le_prod₀ (fun ν _ => norm_nonneg _) ?_
      intro ν _
      have hmul : ‖v * q ^ ν‖ ≤ D * q₀ ^ ν := by
        rw [norm_mul, norm_pow]
        exact mul_le_mul hv (pow_le_pow_left₀ (norm_nonneg q) hq ν)
          (by positivity) hD
      calc
        ‖1 - v * q ^ ν‖ ≤ 1 + ‖v * q ^ ν‖ := by
          simpa using norm_sub_le (1 : ℂ) (v * q ^ ν)
        _ ≤ 1 + D * q₀ ^ ν := add_le_add le_rfl hmul
    _ ≤ ∏' ν : ℕ, (1 + D * q₀ ^ ν) :=
      hmono.ge_of_tendsto (upper_multipliable D q₀ hq₀0 hq₀1).hasProd.tendsto_prod_nat N

theorem finite_product_upper (v q : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hq1 : ‖q‖ < 1) (hv : ‖v‖ ≤ D) (N : ℕ) :
    ‖qPochhammerNat v q N‖ ≤ ∏' ν : ℕ, (1 + D * ‖q‖ ^ ν) := by
  exact finite_product_upper_of_norm_le v q D ‖q‖ hD (norm_nonneg q) hq1 le_rfl hv N

open UpperContour

lemma norm_ratioShift (M : SL(2, ℤ)) (m n h ℓ p : ℤ)
    (x : UpperWindow.Parameters) (z : ℂ) (j k : ℕ) :
    ‖ratioShift M m n h ℓ p x z j k‖ =
      (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
      (‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat) ^ k *
      (‖qPochhammerNat (UpperWindow.bArg m p x.1 x.2.2 z) (e x.1)
          ((M 1 0).toNat * j)‖ /
        ‖qPochhammerNat (UpperWindow.aArg m x.1 z) (e x.1)
          ((M 1 0).toNat * j)‖) *
      (‖qPochhammerNat (e (etaMobius M x.1) / UpperWindow.cArg M n x.1 x.2.2 z)
          (e (etaMobius M x.1)) ((M 1 0).toNat * k)‖ /
        ‖qPochhammerNat (e (etaMobius M x.1) / UpperWindow.dArg M n x.1 z)
          (e (etaMobius M x.1)) ((M 1 0).toNat * k)‖) := by
  simp only [ratioShift, norm_mul, norm_pow, norm_div, pow_mul]

lemma norm_singleShift (M : SL(2, ℤ)) (m n h ℓ : ℤ)
    (x : UpperWindow.Parameters) (z : ℂ) (j k : ℕ) :
    ‖singleShift M m n h ℓ x z j k‖ =
      (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
      ‖UpperWindow.C M h x.1 x.2.1 / UpperWindow.dArg M n x.1 z‖ ^
        ((M 1 0).toNat * k) *
      ‖e (etaMobius M x.1)‖ ^ triangular ((M 1 0).toNat * k) /
      (‖qPochhammerNat (UpperWindow.aArg m x.1 z) (e x.1)
          ((M 1 0).toNat * j)‖ *
        ‖qPochhammerNat (e (etaMobius M x.1) / UpperWindow.dArg M n x.1 z)
          (e (etaMobius M x.1)) ((M 1 0).toNat * k)‖) := by
  simp only [singleShift, zpow_neg, zpow_natCast]
  simp only [norm_div, norm_mul, norm_pow, norm_inv, norm_neg, div_pow]
  rw [pow_mul]
  ring


lemma shift_norm_bounds (M : SL(2, ℤ)) (m n h ℓ p : ℤ)
    (x : UpperWindow.Parameters) (z : ℂ) (j k : ℕ) (L U D : ℝ)
    (hL : 0 < L) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (ha : L ≤ ‖qPochhammerNat (UpperWindow.aArg m x.1 z) (e x.1)
      ((M 1 0).toNat * j)‖)
    (hd : L ≤ ‖qPochhammerNat (e (etaMobius M x.1) / UpperWindow.dArg M n x.1 z)
      (e (etaMobius M x.1)) ((M 1 0).toNat * k)‖)
    (hb : ‖qPochhammerNat (UpperWindow.bArg m p x.1 x.2.2 z) (e x.1)
      ((M 1 0).toNat * j)‖ ≤ U)
    (hc : ‖qPochhammerNat (e (etaMobius M x.1) / UpperWindow.cArg M n x.1 x.2.2 z)
      (e (etaMobius M x.1)) ((M 1 0).toNat * k)‖ ≤ U)
    (hCd : ‖UpperWindow.C M h x.1 x.2.1 / UpperWindow.dArg M n x.1 z‖ ≤ D) :
    ‖ratioShift M m n h ℓ p x z j k‖ ≤
      (U / L) ^ 2 * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
        (‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat) ^ k ∧
    ‖singleShift M m n h ℓ x z j k‖ ≤
      (1 / (L * L)) * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
        (D ^ ((M 1 0).toNat * k) *
          ‖e (etaMobius M x.1)‖ ^ triangular ((M 1 0).toNat * k)) := by
  have hab := div_le_div₀ hU hb hL ha
  have hdc := div_le_div₀ hU hc hL hd
  have hden := mul_le_mul ha hd hL.le (norm_nonneg _)
  constructor
  · rw [norm_ratioShift]
    calc
      _ ≤ (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
          (‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat) ^ k *
          (U / L) * (U / L) := by gcongr
      _ = _ := by ring
  · rw [norm_singleShift]
    calc
      _ ≤ ((‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
          D ^ ((M 1 0).toNat * k) *
          ‖e (etaMobius M x.1)‖ ^ triangular ((M 1 0).toNat * k)) / (L * L) := by
        apply div_le_div₀ (by positivity) _ (mul_pos hL hL) hden
        gcongr
      _ = _ := by ring

/-- A compact family admits one pair of constants while keeping the exact
pointwise A and B rates. This also supplies the fixed-parameter estimate. -/
theorem compact_exact_template_bounds (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ M₀ D : ℝ, 0 < M₀ ∧ 0 < D ∧
      ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ z ∈ UpperWindow.templates M (m : ℤ) n δ x.1, ∀ j k : ℕ,
        ‖UpperContour.kernel .ratio M (m : ℤ) n h ℓ p x (translate M x.1 z j k)‖ ≤
          M₀ * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
            (‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat) ^ k ∧
        ‖UpperContour.kernel .single M (m : ℤ) n h ℓ p x (translate M x.1 z j k)‖ ≤
          M₀ * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
            (D ^ ((M 1 0).toNat * k) *
              ‖e (etaMobius M x.1)‖ ^ triangular ((M 1 0).toNat * k)) := by
  obtain ⟨η, R, q₀, hη, hR, hq₀0, hq₀1, hparameters⟩ :=
    UpperWindow.compact_parameter_bounds M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨r, D, hr0, hr1, hD, harguments⟩ :=
    UpperWindow.compact_template_arguments M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨H, hH, hkernel⟩ :=
    UpperWindow.compact_template_kernel_bounds M h ℓ p n ψ σ ρ δ hc K hK hKU
  let L := ∏' ν : ℕ, (1 - r * q₀ ^ ν)
  let U := ∏' ν : ℕ, (1 + D * q₀ ^ ν)
  have hL : 0 < L := productLower_pos r q₀ hr0.le hr1 hq₀0.le hq₀1
  have hU : 0 < U := productUpper_pos D q₀ hD.le hq₀0.le hq₀1
  let M₀ := H * (U / L) ^ 2 + H / (L * L) + 1
  have hM₀ : 0 < M₀ := by dsimp [M₀]; positivity
  have hMr : H * (U / L) ^ 2 ≤ M₀ := by
    dsimp [M₀]
    have := div_pos hH (mul_pos hL hL)
    linarith
  have hMs : H / (L * L) ≤ M₀ := by
    dsimp [M₀]
    have := mul_nonneg hH.le (sq_nonneg (U / L))
    linarith
  refine ⟨M₀, D, hM₀, hD, ?_⟩
  intro x hx m hm z hz j k
  have hq : ‖e x.1‖ ≤ q₀ := (hparameters x hx).2.2.2.2.2.2.2.1
  have hQ : ‖e (etaMobius M x.1)‖ ≤ q₀ := (hparameters x hx).2.2.2.2.2.2.2.2.2.1
  obtain ⟨ha, hd, hb, hc', hCd⟩ := harguments x hx m hm z hz
  have hla := finite_product_lower_of_norm_le (UpperWindow.aArg (m : ℤ) x.1 z)
    (e x.1) r q₀ hr0.le hr1 hq₀0.le hq₀1 hq ha ((M 1 0).toNat * j)
  have hld := finite_product_lower_of_norm_le
    (e (etaMobius M x.1) / UpperWindow.dArg M n x.1 z)
    (e (etaMobius M x.1)) r q₀ hr0.le hr1 hq₀0.le hq₀1 hQ hd ((M 1 0).toNat * k)
  have hub := finite_product_upper_of_norm_le (UpperWindow.bArg (m : ℤ) p x.1 x.2.2 z)
    (e x.1) D q₀ hD.le hq₀0.le hq₀1 hq hb ((M 1 0).toNat * j)
  have huc := finite_product_upper_of_norm_le
    (e (etaMobius M x.1) / UpperWindow.cArg M n x.1 x.2.2 z)
    (e (etaMobius M x.1)) D q₀ hD.le hq₀0.le hq₀1 hQ hc' ((M 1 0).toNat * k)
  have hs := shift_norm_bounds M (m : ℤ) n h ℓ p x z j k L U D
    hL hU.le hD.le hla hld hub huc hCd
  have hkr : ‖UpperContour.kernel .ratio M (m : ℤ) n h ℓ p x z‖ ≤ H :=
    (hkernel x hx m hm z hz).2
  have hks : ‖UpperContour.kernel .single M (m : ℤ) n h ℓ p x z‖ ≤ H :=
    (hkernel x hx m hm z hz).1
  constructor
  · rw [ratio_shift_on_templates M h ℓ p (m : ℤ) n ψ σ ρ δ hc x (hKU hx) z hz,
      norm_mul]
    calc
      _ ≤ H * ((U / L) ^ 2 *
          (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
          (‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat) ^ k) :=
        mul_le_mul hkr hs.1 (norm_nonneg _) hH.le
      _ = (H * (U / L) ^ 2) *
          (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
          (‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat) ^ k := by ring
      _ ≤ _ := by gcongr
  · rw [single_shift_on_templates M h ℓ p (m : ℤ) n ψ σ ρ δ hc x (hKU hx) z hz,
      norm_mul]
    calc
      _ ≤ H * ((1 / (L * L)) *
          (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
          (D ^ ((M 1 0).toNat * k) *
            ‖e (etaMobius M x.1)‖ ^ triangular ((M 1 0).toNat * k))) :=
        mul_le_mul hks hs.2 (norm_nonneg _) hH.le
      _ = (H / (L * L)) *
          (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
          (D ^ ((M 1 0).toNat * k) *
            ‖e (etaMobius M x.1)‖ ^ triangular ((M 1 0).toNat * k)) := by ring
      _ ≤ _ := by gcongr

end SICLean.L4.UpperContourBoundsAux
