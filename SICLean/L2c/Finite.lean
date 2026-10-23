import SICLean.L2c.FiniteAux

set_option autoImplicit false

/-!
# From [RW26, Thm. 2] to the function pentagon (31)

(5) and (6) give Fourier proportionality; (5) and (7) give (36) off the origin;
(4) supplies the origin; (36), reflection, and proportionality give (33);
Fourier inversion gives (31).
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2c

local instance classicalEq (A : Type*) : DecidableEq A := Classical.decEq A

private theorem real_plus_formula (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt ((N + 2 + Real.sqrt (N ^ 2 + 4 * N)) / 2) =
      (Real.sqrt (N + 4) + Real.sqrt N) / 2 := by
  have ht : Real.sqrt (N + 4) ^ 2 = N + 4 := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have hr : Real.sqrt (N ^ 2 + 4 * N) = Real.sqrt N * Real.sqrt (N + 4) := by
    rw [show N ^ 2 + 4 * N = N * (N + 4) by ring, Real.sqrt_mul hN]
  have hn : 0 ≤ (Real.sqrt (N + 4) + Real.sqrt N) / 2 := by positivity
  apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) hn).mpr
  rw [hr]
  nlinarith

private theorem real_minus_formula (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt ((N + 2 - Real.sqrt (N ^ 2 + 4 * N)) / 2) =
      (Real.sqrt (N + 4) - Real.sqrt N) / 2 := by
  have ht : Real.sqrt (N + 4) ^ 2 = N + 4 := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have hts : Real.sqrt N ≤ Real.sqrt (N + 4) := Real.sqrt_le_sqrt (by linarith)
  have hr : Real.sqrt (N ^ 2 + 4 * N) = Real.sqrt N * Real.sqrt (N + 4) := by
    rw [show N ^ 2 + 4 * N = N * (N + 4) by ring, Real.sqrt_mul hN]
  have hn : 0 ≤ (Real.sqrt (N + 4) - Real.sqrt N) / 2 := by linarith
  have hrad : 0 ≤ (N + 2 - Real.sqrt (N ^ 2 + 4 * N)) / 2 := by
    rw [hr]
    nlinarith [sq_nonneg (Real.sqrt (N + 4) - Real.sqrt N)]
  apply (Real.sqrt_eq_iff_mul_self_eq hrad hn).mpr
  rw [hr]
  nlinarith

private theorem real_plus_quadratic (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt ((N + 2 + Real.sqrt (N ^ 2 + 4 * N)) / 2) ^ 2 =
      Real.sqrt N * Real.sqrt ((N + 2 + Real.sqrt (N ^ 2 + 4 * N)) / 2) + 1 := by
  rw [real_plus_formula N hN]
  have ht : Real.sqrt (N + 4) ^ 2 = N + 4 := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  nlinarith

private theorem real_plus_mul_minus (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt ((N + 2 + Real.sqrt (N ^ 2 + 4 * N)) / 2) *
      Real.sqrt ((N + 2 - Real.sqrt (N ^ 2 + 4 * N)) / 2) = 1 := by
  rw [real_plus_formula N hN, real_minus_formula N hN]
  have ht : Real.sqrt (N + 4) ^ 2 = N + 4 := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  nlinarith

private theorem nonneg_quadratic_unique (s a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hqa : a ^ 2 = s * a + 1) (hqb : b ^ 2 = s * b + 1) : a = b := by
  have hsa : s < a := by
    by_contra h
    have hh : a ≤ s := le_of_not_gt h
    have hm := mul_le_mul_of_nonneg_right hh ha
    nlinarith
  have hpos : 0 < a + b - s := by linarith
  have hf : (a - b) * (a + b - s) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hf | hf
  · linarith
  · linarith

private theorem sqrt_order_real (M : ℕ) [Fact (4 ≤ M)] :
    Real.sqrt (L2b.groupOrder M : ℝ) = (M : ℝ) * Real.sqrt ((M : ℝ) - 3) := by
  have hM : 4 ≤ M := Fact.out
  have h3 : 3 ≤ M := by omega
  have hc : (L2b.groupOrder M : ℝ) = (M : ℝ) ^ 2 * ((M : ℝ) - 3) := by
    simp only [L2b.groupOrder, L2b.cofactor, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h3]
    norm_num
  rw [hc, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

private theorem sqrtEpsilon_cube_quadratic_real (M : ℕ) [Fact (4 ≤ M)] :
    (Real.sqrt (L2a.epsilon M) ^ 3) ^ 2 =
      Real.sqrt (L2b.groupOrder M : ℝ) * (Real.sqrt (L2a.epsilon M) ^ 3) + 1 := by
  have hM : 4 ≤ M := Fact.out
  have hε : 0 < L2a.epsilon M := lt_trans (by norm_num) (L2a.epsilon_gt_one hM)
  have hu : Real.sqrt (L2a.epsilon M) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hε)
  have hu2 : Real.sqrt (L2a.epsilon M) ^ 2 = L2a.epsilon M :=
    Real.sq_sqrt (le_of_lt hε)
  have hq : Real.sqrt (L2a.epsilon M) ^ 4 -
      ((M : ℝ) - 1) * Real.sqrt (L2a.epsilon M) ^ 2 + 1 = 0 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hu2]
    exact L2a.epsilon_quadratic hM
  have hsub : Real.sqrt (L2a.epsilon M) - (Real.sqrt (L2a.epsilon M))⁻¹ =
      Real.sqrt ((M : ℝ) - 3) := by
    have hc := L2a.sqrtEpsilon_sub_inv hM
    unfold L2a.sqrtEpsilon L2a.convolutionScalar at hc
    rw [← Complex.ofReal_inv, ← Complex.ofReal_sub] at hc
    exact Complex.ofReal_inj.mp hc
  rw [sqrt_order_real M, ← hsub]
  field_simp
  linear_combination (Real.sqrt (L2a.epsilon M) ^ 2 - 1) * hq


theorem originPlus_eq_sqrtEpsilon_cube (M : ℕ) [Fact (4 ≤ M)] :
    originPlus M = L2a.sqrtEpsilon M ^ 3 := by
  have hr : Real.sqrt (((L2b.groupOrder M : ℝ) + 2 +
      Real.sqrt ((L2b.groupOrder M : ℝ) ^ 2 + 4 * (L2b.groupOrder M : ℝ))) / 2) =
      Real.sqrt (L2a.epsilon M) ^ 3 := by
    apply nonneg_quadratic_unique (Real.sqrt (L2b.groupOrder M : ℝ))
    · positivity
    · positivity
    · exact real_plus_quadratic _ (by positivity)
    · exact sqrtEpsilon_cube_quadratic_real M
  simpa only [originPlus, L2a.sqrtEpsilon, Complex.ofReal_pow] using congrArg Complex.ofReal hr

theorem originMinus_eq_inverse (M : ℕ) [Fact (4 ≤ M)] :
    originMinus M = (originPlus M)⁻¹ := by
  have hp : originPlus M * originMinus M = 1 := by
    unfold originPlus originMinus
    rw [← Complex.ofReal_mul]
    exact_mod_cast real_plus_mul_minus (L2b.groupOrder M : ℝ) (by positivity)
  apply eq_inv_of_mul_eq_one_left
  simpa only [mul_comm] using hp

theorem originPlus_quadratic (M : ℕ) [Fact (4 ≤ M)] :
    originPlus M ^ 2 = sqrtOrder M * originPlus M + 1 := by
  unfold originPlus sqrtOrder
  exact_mod_cast real_plus_quadratic (L2b.groupOrder M : ℝ) (by positivity)

theorem originPlus_ne_zero (M : ℕ) [Fact (4 ≤ M)] : originPlus M ≠ 0 := by
  rw [originPlus_eq_sqrtEpsilon_cube M]
  exact pow_ne_zero 3 (L2a.sqrtEpsilon_ne_zero (Fact.out : 4 ≤ M))

variable {M : ℕ} [Fact (4 ≤ M)] {Fplus Fminus : RWGroup M → ℂ}

theorem special_values_ne_zero (h : Theorem2Input M Fplus Fminus) (u : RWGroup M) :
    Fplus u ≠ 0 ∧ Fminus u ≠ 0 := by
  have hq := rw_isMetricGaussian M
  constructor
  · intro hz
    have hr := h.mixed_reflection u
    rw [hz, zero_mul] at hr
    exact inv_ne_zero (hq.nonzero u) hr.symm
  · intro hz
    have hr := h.mixed_reflection (-u)
    rw [neg_neg, hz, mul_zero] at hr
    exact inv_ne_zero (hq.nonzero (-u)) hr.symm

/-- (5), including the origin. The inverse is of F⁻, not F⁺. -/
theorem inverse_minus (h : Theorem2Input M Fplus Fminus) (u : RWGroup M) :
    (Fminus u)⁻¹ = gaussian M u * Fplus (-u) := by
  have hr := h.mixed_reflection (-u)
  rw [neg_neg, (rw_isMetricGaussian M).even] at hr
  apply mul_left_cancel₀ (special_values_ne_zero h u).2
  rw [mul_inv_cancel₀ (special_values_ne_zero h u).2]
  calc
    1 = gaussian M u * (Fplus (-u) * Fminus u) := by
      rw [hr, mul_inv_cancel₀ ((rw_isMetricGaussian M).nonzero u)]
    _ = Fminus u * (gaussian M u * Fplus (-u)) := by ring

private theorem smith_inverse_minus (h : Theorem2Input M Fplus Fminus) (x : L2b.G M) :
    (smithValues M Fminus x)⁻¹ = L2b.gaussian M x * smithValues M Fplus (-x) := by
  simpa only [smithValues, Function.comp_apply, fromSmith_neg, gaussian_fromSmith]
    using inverse_minus h (fromSmith M x)

theorem smith_origin (h : Theorem2Input M Fplus Fminus) :
    smithValues M Fplus 0 = L2a.sqrtEpsilon M ^ 3 := by
  simpa only [smithValues, Function.comp_apply, fromSmith_zero, h.origin_plus]
    using originPlus_eq_sqrtEpsilon_cube M

/-- The origin quadratic supplies the value of [RW26, (7)] at the origin. -/
theorem smith_origin_quadratic (h : Theorem2Input M Fplus Fminus) :
    smithValues M Fplus 0 ^ 2 =
      L2b.sqrtCard (L2b.G M) * smithValues M Fplus 0 + 1 := by
  simpa only [smithValues, Function.comp_apply, fromSmith_zero, h.origin_plus,
    sqrtOrder_eq_sqrtCard] using originPlus_quadratic M

/-- Footnote 2 and (5) away from zero, and (4) at zero. -/
theorem smith_reflection_all (h : Theorem2Input M Fplus Fminus) (x : L2b.G M) :
    smithValues M Fplus x * smithValues M Fplus (-x) * L2b.gaussian M x =
      1 + L2b.sqrtCard (L2b.G M) * smithValues M Fplus 0 *
        (if x = 0 then 1 else 0) := by
  by_cases hx : x = 0
  · subst x
    simpa only [neg_zero, L2b.gaussian_zero, ite_true, mul_one, pow_two, add_comm]
      using smith_origin_quadratic h
  · have hr := smith_mixed_reflection h x
    rw [← smith_agree_off_zero h (-x) (neg_ne_zero.mpr hx)] at hr
    rw [if_neg hx, mul_zero, add_zero, hr]
    exact inv_mul_cancel₀ (L2b.gaussian_ne_zero M x)

/-- (6) transported verbatim; its pairing still has a positive sign. -/
theorem smith_positive_fourier (h : Theorem2Input M Fplus Fminus) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ∀ u : L2b.G M,
      L2b.normalizedSum (fun x =>
        L2b.metricPairing (L2b.gaussian M) x u * smithValues M Fplus x) =
          μ / smithValues M Fminus u := by
  obtain ⟨μ, hμ, hf⟩ := h.fourier
  refine ⟨μ, hμ, ?_⟩
  intro u
  have hu := hf (fromSmith M u)
  rw [normalizedSum_toSmith] at hu
  simpa only [smithValues, Function.comp_def, pairing_fromSmith] using hu

/-- (5) and (6) with u replaced by −x. The scalar is μ, not μ⁻¹. -/
theorem smith_fourier_proportional (h : Theorem2Input M Fplus Fminus) (x : L2b.G M) :
    L2b.fourier (L2b.gaussian M) (smithValues M Fplus) x =
      L2b.fourierScalar (L2b.gaussian M) (smithValues M Fplus) *
        L2b.gaussian M x * smithValues M Fplus x := by
  obtain ⟨μ, hμ, hf⟩ := smith_positive_fourier h
  have hp (w : L2b.G M) :
      L2b.fourier (L2b.gaussian M) (smithValues M Fplus) w =
        μ * L2b.gaussian M w * smithValues M Fplus w := by
    have hw := hf (-w)
    have hi := smith_inverse_minus h (-w)
    simp only [L2b.gaussian_even, neg_neg] at hi
    rw [L2b.fourier]
    calc
      _ = L2b.normalizedSum (fun t =>
          L2b.metricPairing (L2b.gaussian M) t (-w) * smithValues M Fplus t) := by
        apply L2b.core_normalizedSum_congr
        intro t
        ring
      _ = μ / smithValues M Fminus (-w) := hw
      _ = μ * L2b.gaussian M w * smithValues M Fplus w := by
        rw [div_eq_mul_inv, hi]
        ring
  have h0 : smithValues M Fplus 0 ≠ 0 :=
    (special_values_ne_zero h (fromSmith M 0)).1
  have hscalar : L2b.fourierScalar (L2b.gaussian M) (smithValues M Fplus) = μ := by
    rw [L2b.fourierScalar, hp 0, L2b.gaussian_zero, mul_one,
      mul_div_cancel_right₀ _ h0]
  rw [hscalar, hp x]

theorem smith_fourierScalar_ne_zero (h : Theorem2Input M Fplus Fminus) :
    L2b.fourierScalar (L2b.gaussian M) (smithValues M Fplus) ≠ 0 := by
  have h0 : smithValues M Fplus 0 ≠ 0 :=
    (special_values_ne_zero h (fromSmith M 0)).1
  obtain ⟨μ, hμ, hf⟩ := smith_positive_fourier h
  have hf0 : L2b.fourier (L2b.gaussian M) (smithValues M Fplus) 0 ≠ 0 := by
    rw [L2b.core_fourier_zero (L2b.concrete_isMetricGaussian M)]
    have hp := hf 0
    simp only [L2b.core_pairing_zero_right (L2b.concrete_isMetricGaussian M), one_mul] at hp
    rw [hp]
    exact div_ne_zero hμ (special_values_ne_zero h (fromSmith M 0)).2
  exact div_ne_zero hf0 h0

/-- (7) after substituting (u,v)=(x+y,−x), using (5), and cancelling q(x).
This statement does not silently fill the excluded pair (0,0). -/
theorem pentagon36_off_origin (h : Theorem2Input M Fplus Fminus)
    (x y : L2b.G M) (hxy : (x, y) ≠ (0, 0)) :
    L2b.normalizedSum (fun t => smithValues M Fplus t * L2b.gaussian M t *
      smithValues M Fplus (x - t) * L2b.metricPairing (L2b.gaussian M) t y) =
        L2b.gaussian M (x + y) * smithValues M Fplus (-x - y) *
          smithValues M Fplus x * smithValues M Fplus y := by
  have hq := L2b.concrete_isMetricGaussian M
  have hpair : (x + y, -x) ≠ (0, 0) := by
    intro hp
    have hx : x = 0 := neg_eq_zero.mp (congrArg Prod.snd hp)
    have hy : y = 0 := by simpa only [hx, zero_add] using congrArg Prod.fst hp
    exact hxy (Prod.ext hx hy)
  have hr := smith_ratio_sum h (x + y) (-x) hpair
  have hphase (t : L2b.G M) :
      L2b.metricPairing (L2b.gaussian M) t (x + y) * L2b.gaussian M (t - x) =
        L2b.gaussian M x * L2b.gaussian M t *
          L2b.metricPairing (L2b.gaussian M) t y := by
    rw [L2b.core_gaussian_sub hq, hq.add_right, L2b.core_pairing_neg_right hq]
    field_simp [L2b.core_pairing_ne_zero hq t x]
  apply mul_left_cancel₀ (L2b.gaussian_ne_zero M x)
  calc
    _ = L2b.normalizedSum (fun t =>
        L2b.metricPairing (L2b.gaussian M) t (x + y) *
          (smithValues M Fplus t / smithValues M Fminus (t + -x))) := by
      rw [← L2b.core_normalizedSum_mul_left]
      apply L2b.core_normalizedSum_congr
      intro t
      rw [div_eq_mul_inv, smith_inverse_minus h]
      have ht : -(t + -x) = x - t := by abel
      rw [ht]
      have hp := hphase t
      simp only [← sub_eq_add_neg]
      change L2b.gaussian M x * _ =
        L2b.metricPairing (L2b.gaussian M) t (x + y) *
          (smithValues M Fplus t *
            (L2b.gaussian M (t - x) * smithValues M Fplus (x - t)))
      linear_combination -(smithValues M Fplus t * smithValues M Fplus (x - t)) * hp
    _ = smithValues M Fplus (x + y + -x) /
        (smithValues M Fminus (x + y) * smithValues M Fminus (-x)) := hr
    _ = _ := by
      rw [div_eq_mul_inv, mul_inv_rev, smith_inverse_minus h, smith_inverse_minus h,
        L2b.gaussian_even, neg_neg]
      have hy : x + y + -x = y := by abel
      have hn : -(x + y) = -x - y := by abel
      rw [hy, hn]
      ring

theorem pentagon36_origin (h : Theorem2Input M Fplus Fminus) :
    L2b.normalizedSum (fun t => smithValues M Fplus t * L2b.gaussian M t *
      smithValues M Fplus (-t)) =
        smithValues M Fplus 0 ^ 3 -
          (L2b.groupOrder M : ℂ) * smithValues M Fplus 0 := by
  have hs : L2b.sqrtCard (L2b.G M) ^ 2 = (L2b.groupOrder M : ℂ) := by
    simpa only [L2b.card_G] using L2b.core_sqrtCard_sq (A := L2b.G M)
  have hsum :
      L2b.normalizedSum (fun t => smithValues M Fplus t * L2b.gaussian M t *
        smithValues M Fplus (-t)) =
        ((L2b.groupOrder M : ℂ) +
          L2b.sqrtCard (L2b.G M) * smithValues M Fplus 0) /
            L2b.sqrtCard (L2b.G M) := by
    unfold L2b.normalizedSum
    congr 1
    calc
      _ = ∑ t : L2b.G M,
          (1 + L2b.sqrtCard (L2b.G M) * smithValues M Fplus 0 *
            (if t = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← smith_reflection_all h t]
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, mul_ite]
        ring
  rw [hsum]
  calc
    _ = L2b.sqrtCard (L2b.G M) + smithValues M Fplus 0 := by
      apply (div_eq_iff L2b.sqrtCard_ne_zero).2
      linear_combination -hs
    _ = _ := by
      have he := smith_origin_quadratic h
      linear_combination -(smithValues M Fplus 0 + L2b.sqrtCard (L2b.G M)) * he -
        smithValues M Fplus 0 * hs

/-- Full (36), including the term −N E(0) δ(x)δ(y). -/
theorem pentagon36_of_theorem2 (h : Theorem2Input M Fplus Fminus) (x y : L2b.G M) :
    L2b.normalizedSum (fun t => smithValues M Fplus t * L2b.gaussian M t *
      smithValues M Fplus (x - t) * L2b.metricPairing (L2b.gaussian M) t y) =
        L2b.gaussian M (x + y) * smithValues M Fplus (-x - y) *
          smithValues M Fplus x * smithValues M Fplus y -
        (L2b.groupOrder M : ℂ) * smithValues M Fplus 0 *
          (if x = 0 ∧ y = 0 then 1 else 0) := by
  by_cases hxy : x = 0 ∧ y = 0
  · rcases hxy with ⟨rfl, rfl⟩
    simpa only [zero_sub, add_zero, neg_zero, L2b.gaussian_zero,
      L2b.core_pairing_zero_right (L2b.concrete_isMetricGaussian M),
      one_mul, mul_one, ite_true, and_self, pow_succ, pow_zero] using pentagon36_origin h
  · rw [if_neg hxy, mul_zero, sub_zero]
    apply pentagon36_off_origin h x y
    intro hp
    exact hxy ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- (36) with y=−w, in exactly the L2b kernel notation. -/
theorem kernel_fourier_of_theorem2 (h : Theorem2Input M Fplus Fminus) (x w : L2b.G M) :
    L2b.fourier (L2b.gaussian M)
      (L2b.pentagonKernel (L2b.gaussian M) (smithValues M Fplus) x) w =
        L2b.gaussian M (x - w) * smithValues M Fplus (w - x) *
          smithValues M Fplus x * smithValues M Fplus (-w) -
        (L2b.groupOrder M : ℂ) * smithValues M Fplus 0 *
          (if x = 0 ∧ w = 0 then 1 else 0) := by
  have hp := pentagon36_of_theorem2 h x (-w)
  have harg : -x - -w = w - x := by abel
  simp only [harg, ← sub_eq_add_neg, neg_eq_zero] at hp
  unfold L2b.fourier L2b.pentagonKernel
  calc
    _ = L2b.normalizedSum (fun t => smithValues M Fplus t * L2b.gaussian M t *
        smithValues M Fplus (x - t) * L2b.metricPairing (L2b.gaussian M) t (-w)) := by
      apply L2b.core_normalizedSum_congr
      intro t
      ring
    _ = _ := by
      by_cases hxw : x = 0 ∧ w = 0
      · simpa only [if_pos hxw] using hp
      · simpa only [if_neg hxw] using hp

/-- Multiply the preceding identity by Ê(w). Reflection removes both origin
terms and gives [RW26, (33)] with C = −Ê(0). -/
theorem transformed_pentagon_of_theorem2 (h : Theorem2Input M Fplus Fminus)
    (x w : L2b.G M) :
    smithValues M Fplus x * L2b.fourier (L2b.gaussian M) (smithValues M Fplus) (w - x) =
      (-L2b.fourier (L2b.gaussian M) (smithValues M Fplus) 0) *
        L2b.sqrtCard (L2b.G M) * (if w = 0 then 1 else 0) +
      L2b.fourier (L2b.gaussian M) (smithValues M Fplus) w *
        L2b.fourier (L2b.gaussian M)
          (L2b.pentagonKernel (L2b.gaussian M) (smithValues M Fplus) x) w := by
  have he := smith_origin_quadratic h
  have hs : L2b.sqrtCard (L2b.G M) ^ 2 = (L2b.groupOrder M : ℂ) := by
    simpa only [L2b.card_G] using L2b.core_sqrtCard_sq (A := L2b.G M)
  by_cases hw : w = 0
  · subst w
    simp only [zero_sub, ite_true, mul_one]
    by_cases hx : x = 0
    · subst x
      rw [kernel_fourier_of_theorem2 h 0 0]
      simp only [sub_zero, neg_zero, L2b.gaussian_zero,
        one_mul, ite_true, and_self, mul_one]
      have hcub : smithValues M Fplus 0 * smithValues M Fplus 0 *
          smithValues M Fplus 0 - (L2b.groupOrder M : ℂ) * smithValues M Fplus 0 =
            L2b.sqrtCard (L2b.G M) + smithValues M Fplus 0 := by
        linear_combination (smithValues M Fplus 0 + L2b.sqrtCard (L2b.G M)) * he +
          smithValues M Fplus 0 * hs
      rw [hcub]
      ring
    · have hk := kernel_fourier_of_theorem2 h x 0
      simp only [sub_zero, zero_sub, neg_zero, and_true,
        if_neg hx, mul_zero, sub_zero] at hk
      have hr := smith_reflection_all h x
      simp only [if_neg hx, mul_zero, add_zero] at hr
      have hk0 : L2b.fourier (L2b.gaussian M)
          (L2b.pentagonKernel (L2b.gaussian M) (smithValues M Fplus) x) 0 =
            smithValues M Fplus 0 := by
        calc
          _ = smithValues M Fplus 0 *
              (smithValues M Fplus x * smithValues M Fplus (-x) * L2b.gaussian M x) := by
            rw [hk]
            ring
          _ = _ := by rw [hr, mul_one]
      rw [hk0, smith_fourier_proportional h (-x), L2b.gaussian_even,
        smith_fourier_proportional h 0, L2b.gaussian_zero, mul_one]
      linear_combination
        L2b.fourierScalar (L2b.gaussian M) (smithValues M Fplus) * hr -
        L2b.fourierScalar (L2b.gaussian M) (smithValues M Fplus) * he
  · have hxw : ¬ (x = 0 ∧ w = 0) := fun hp => hw hp.2
    rw [if_neg hw, mul_zero, zero_add, kernel_fourier_of_theorem2 h x w,
      if_neg hxw, mul_zero, sub_zero, smith_fourier_proportional h w,
      smith_fourier_proportional h (w - x)]
    have hphase : L2b.gaussian M (x - w) = L2b.gaussian M (w - x) := by
      rw [show x - w = -(w - x) by abel, L2b.gaussian_even]
    rw [hphase]
    have hr := smith_reflection_all h w
    simp only [if_neg hw, mul_zero, add_zero] at hr
    linear_combination
      -(L2b.fourierScalar (L2b.gaussian M) (smithValues M Fplus) *
        L2b.gaussian M (w - x) * smithValues M Fplus (w - x) *
          smithValues M Fplus x) * hr

/-- The reverse direction of L2b.transformed_pentagon, by Fourier inversion.
Only the metric-group hypothesis is needed here. C need not be nonzero. -/
theorem pentagon_of_transformed
    {A : Type*} [AddCommGroup A] [Fintype A] {q E : A → ℂ}
    (hq : L2b.IsMetricGaussian q) {C : ℂ}
    (h : ∀ x w : A,
      E x * L2b.fourier q E (w - x) =
        C * L2b.sqrtCard A * (if w = 0 then 1 else 0) +
          L2b.fourier q E w * L2b.fourier q (L2b.pentagonKernel q E x) w) :
    L2b.Pentagon q E C := by
  intro x y
  have hF :
      L2b.fourier q
        (fun z => L2b.metricPairing q x z * E x * E z) =
      L2b.fourier q
        (fun z => C + L2b.normalizedSum (fun t =>
          E (z - t) * E t * q t * E (x - t))) := by
    funext w
    calc
      L2b.fourier q
          (fun z => L2b.metricPairing q x z * E x * E z) w =
          E x * L2b.fourier q E (w - x) := by
        unfold L2b.fourier
        rw [← L2b.core_normalizedSum_mul_left]
        apply L2b.core_normalizedSum_congr
        intro z
        dsimp only
        rw [L2b.metric_pairing_symmetric q x z]
        have hz : -(w - x) = x + -w := by abel
        rw [hz, hq.add_right]
        ring
      _ = C * L2b.sqrtCard A * (if w = 0 then 1 else 0) +
          L2b.fourier q E w *
            L2b.fourier q (L2b.pentagonKernel q E x) w := h x w
      _ = L2b.fourier q
          (fun z => C + L2b.normalizedSum (fun t =>
            E (z - t) * E t * q t * E (x - t))) w := by
        symm
        unfold L2b.fourier
        simp_rw [add_mul]
        rw [L2b.core_normalizedSum_add]
        congr 1
        · rw [L2b.core_normalizedSum_mul_left,
            L2b.core_character_normalizedSum hq]
          ring
        · change L2b.fourier q (fun z =>
              L2b.normalizedSum (fun t =>
                E (z - t) * E t * q t * E (x - t))) w =
            L2b.fourier q E w *
              L2b.fourier q (L2b.pentagonKernel q E x) w
          rw [← L2b.core_fourier_convolution hq E
            (L2b.pentagonKernel q E x) w]
          congr 1
          funext z
          apply L2b.core_normalizedSum_congr
          intro t
          unfold L2b.pentagonKernel
          ring
  have hi := congrArg (fun f : A → ℂ => L2b.fourier q f (-y)) hF
  simpa only [L2b.fourier_twice hq, neg_neg] using hi

theorem pentagon_constant_ne_zero (h : Theorem2Input M Fplus Fminus) :
    -L2b.fourier (L2b.gaussian M) (smithValues M Fplus) 0 ≠ 0 := by
  apply neg_ne_zero.mpr
  have h0 : smithValues M Fplus 0 ≠ 0 :=
    (special_values_ne_zero h (fromSmith M 0)).1
  rw [smith_fourier_proportional h 0, L2b.gaussian_zero, mul_one]
  exact mul_ne_zero (smith_fourierScalar_ne_zero h) h0

theorem pentagon_of_theorem2 (h : Theorem2Input M Fplus Fminus) :
    L2b.Pentagon (L2b.gaussian M) (smithValues M Fplus)
      (-L2b.fourier (L2b.gaussian M) (smithValues M Fplus) 0) := by
  apply pentagon_of_transformed (L2b.concrete_isMetricGaussian M)
  intro x w
  by_cases hw : w = 0
  · simpa only [if_pos hw] using transformed_pentagon_of_theorem2 h x w
  · simpa only [if_neg hw] using transformed_pentagon_of_theorem2 h x w

theorem isFiniteQuantumDilogarithm_of_theorem2 (h : Theorem2Input M Fplus Fminus) :
    L2b.IsFiniteQuantumDilogarithm (L2b.gaussian M) (smithValues M Fplus) := by
  exact ⟨_, pentagon_constant_ne_zero h, pentagon_of_theorem2 h⟩

theorem smith_epsilon_invariant (h : RWAnalyticInput M Fplus Fminus) (g : L2b.G M) :
    smithValues M Fplus g = smithValues M Fplus (L2b.epsilonAut M g) := by
  change Fplus (fromSmith M g) = Fplus (fromSmith M (L2b.epsilonAut M g))
  rw [h.epsilon_invariant (fromSmith M g)]
  congr 1
  apply (smithEquiv M).injective
  change toSmith M (epsilonAction M (fromSmith M g)) =
    toSmith M (fromSmith M (L2b.epsilonAut M g))
  rw [epsilonAction_toSmith, toSmith_fromSmith, toSmith_fromSmith]

end SICLean.L2c
