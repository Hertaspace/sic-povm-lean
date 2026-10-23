import SICLean.L2rc.GenericAux

set_option autoImplicit false

/-!
# [RW26, Thm. 2] on an arbitrary finite metric group

Source: [RW26, Thm. 2, (4)--(7)], footnote 2.
The group geometry is a hypothesis of the abstract theorems, never a field of
the special-value input. No lower bound on the cardinality is needed.

The derivation follows (4)--(7) and footnote 2, then nonvanishing, reflection,
and Fourier proportionality, then (36), (33), and (31). The last step uses
`L2c.pentagon_of_transformed`, by Fourier inversion.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2rc.Generic

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The positive branch of [RW26, (4)], with N = |A|. -/
def originPlus (A : Type*) [Fintype A] : ℂ :=
  (Real.sqrt (((Fintype.card A : ℝ) + 2 +
    Real.sqrt ((Fintype.card A : ℝ) ^ 2 + 4 * (Fintype.card A : ℝ))) / 2) : ℂ)

/-- The minus sign is inside the radical; the outer square root is positive. -/
def originMinus (A : Type*) [Fintype A] : ℂ :=
  (Real.sqrt (((Fintype.card A : ℝ) + 2 -
    Real.sqrt ((Fintype.card A : ℝ) ^ 2 + 4 * (Fintype.card A : ℝ))) / 2) : ℂ)

/-- [RW26, Thm. 2] and footnote 2. In the Fourier formula, μ is one common
nonzero scalar. The pairing is polarization. -/
structure Theorem2Input (A : Type*) [AddCommGroup A] [Fintype A]
    (q Fplus Fminus : A → ℂ) : Prop where
  origin_plus : Fplus 0 = originPlus A
  origin_minus : Fminus 0 = originMinus A
  mixed_reflection : ∀ u : A, Fplus u * Fminus (-u) = (q u)⁻¹
  fourier : ∃ μ : ℂ, μ ≠ 0 ∧ ∀ u : A,
    L2b.normalizedSum (fun x => L2b.metricPairing q x u * Fplus x) = μ / Fminus u
  ratio_sum : ∀ u v : A, (u, v) ≠ (0, 0) →
    L2b.normalizedSum (fun x => L2b.metricPairing q x u *
      (Fplus x / Fminus (x + v))) = Fplus (u + v) / (Fminus u * Fminus v)
  agree_off_zero : ∀ u : A, u ≠ 0 → Fplus u = Fminus u

variable {A : Type*} [AddCommGroup A] [Fintype A]
variable {q Fplus Fminus : A → ℂ}

theorem originPlus_ne_zero : originPlus A ≠ 0 := by
  unfold originPlus
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

theorem originMinus_eq_inverse : originMinus A = (originPlus A)⁻¹ := by
  have hp : originPlus A * originMinus A = 1 := by
    unfold originPlus originMinus
    rw [← Complex.ofReal_mul]
    exact_mod_cast Aux.real_plus_mul_minus (Fintype.card A : ℝ) (by positivity)
  apply eq_inv_of_mul_eq_one_left
  simpa only [mul_comm] using hp

theorem originPlus_quadratic :
    originPlus A ^ 2 = L2b.sqrtCard A * originPlus A + 1 := by
  unfold originPlus L2b.sqrtCard
  exact_mod_cast Aux.real_plus_quadratic (Fintype.card A : ℝ) (by positivity)

theorem origin_quadratic (h : Theorem2Input A q Fplus Fminus) :
    Fplus 0 ^ 2 = L2b.sqrtCard A * Fplus 0 + 1 := by
  rw [h.origin_plus]
  exact originPlus_quadratic

/-- (5) and the nonvanishing of the Gaussian, at every point including zero. -/
theorem special_values_ne_zero (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (u : A) :
    Fplus u ≠ 0 ∧ Fminus u ≠ 0 := by
  constructor
  · intro hz
    have hr := h.mixed_reflection u
    rw [hz, zero_mul] at hr
    exact inv_ne_zero (hq.nonzero u) hr.symm
  · intro hz
    have hr := h.mixed_reflection (-u)
    rw [neg_neg, hz, mul_zero] at hr
    exact inv_ne_zero (hq.nonzero (-u)) hr.symm

theorem inverse_minus (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (u : A) :
    (Fminus u)⁻¹ = q u * Fplus (-u) := by
  have hr := h.mixed_reflection (-u)
  rw [neg_neg, hq.even] at hr
  apply mul_left_cancel₀ (special_values_ne_zero hq h u).2
  rw [mul_inv_cancel₀ (special_values_ne_zero hq h u).2]
  calc
    1 = q u * (Fplus (-u) * Fminus u) := by
      rw [hr, mul_inv_cancel₀ (hq.nonzero u)]
    _ = Fminus u * (q u * Fplus (-u)) := by ring

theorem reflection_off_zero (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (u : A) (hu : u ≠ 0) :
    Fplus u * Fplus (-u) = (q u)⁻¹ := by
  rw [h.agree_off_zero (-u) (neg_ne_zero.mpr hu)]
  exact h.mixed_reflection u

/-- Footnote 2 is used away from zero; the quadratic from (4) supplies zero. -/
theorem reflection_all (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (u : A) :
    Fplus u * Fplus (-u) * q u =
      1 + L2b.sqrtCard A * Fplus 0 * (if u = 0 then 1 else 0) := by
  by_cases hu : u = 0
  · subst u
    simpa only [neg_zero, L2b.metric_zero hq, ite_true, mul_one, pow_two, add_comm]
      using origin_quadratic h
  · rw [if_neg hu, mul_zero, add_zero, reflection_off_zero hq h u hu]
    exact inv_mul_cancel₀ (hq.nonzero u)

/-- The sign in the Fourier kernel is negative, so (6) is applied at -u. -/
theorem fourier_proportional (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (u : A) :
    L2b.fourier q Fplus u = L2b.fourierScalar q Fplus * q u * Fplus u := by
  obtain ⟨μ, hμ, hf⟩ := h.fourier
  have hp (w : A) : L2b.fourier q Fplus w = μ * q w * Fplus w := by
    have hw := hf (-w)
    have hi := inverse_minus hq h (-w)
    simp only [hq.even, neg_neg] at hi
    rw [L2b.fourier]
    calc
      _ = L2b.normalizedSum (fun t => L2b.metricPairing q t (-w) * Fplus t) := by
        apply L2b.core_normalizedSum_congr
        intro t
        ring
      _ = μ / Fminus (-w) := hw
      _ = μ * q w * Fplus w := by
        rw [div_eq_mul_inv, hi]
        ring
  have h0 := (special_values_ne_zero hq h 0).1
  have hscalar : L2b.fourierScalar q Fplus = μ := by
    rw [L2b.fourierScalar, hp 0, L2b.metric_zero hq, mul_one,
      mul_div_cancel_right₀ _ h0]
  rw [hscalar, hp u]

/-- This identifies the normalized Fourier scalar with the very same μ in (6). -/
theorem fourierScalar_eq_multiplier (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) {μ : ℂ}
    (hf : ∀ u : A, L2b.normalizedSum
      (fun x => L2b.metricPairing q x u * Fplus x) = μ / Fminus u) :
    L2b.fourierScalar q Fplus = μ := by
  have hf0 := hf 0
  simp only [L2b.core_pairing_zero_right hq, one_mul] at hf0
  rw [L2b.fourierScalar, L2b.core_fourier_zero hq, hf0]
  simp only [div_eq_mul_inv, inverse_minus hq h 0, L2b.metric_zero hq,
    neg_zero, one_mul]
  rw [mul_assoc, mul_inv_cancel₀ (special_values_ne_zero hq h 0).1, mul_one]

theorem fourierScalar_ne_zero (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) :
    L2b.fourierScalar q Fplus ≠ 0 := by
  obtain ⟨μ, hμ, hf⟩ := h.fourier
  rw [fourierScalar_eq_multiplier hq h hf]
  exact hμ

/-- (7) at (u,v)=(x+y,-x); its single excluded point is retained. -/
theorem pentagon36_off_origin (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (x y : A)
    (hxy : (x, y) ≠ (0, 0)) :
    L2b.normalizedSum (fun t => Fplus t * q t * Fplus (x - t) *
      L2b.metricPairing q t y) =
        q (x + y) * Fplus (-x - y) * Fplus x * Fplus y := by
  have hpair : (x + y, -x) ≠ (0, 0) := by
    intro hp
    have hx : x = 0 := neg_eq_zero.mp (congrArg Prod.snd hp)
    have hy : y = 0 := by simpa only [hx, zero_add] using congrArg Prod.fst hp
    exact hxy (Prod.ext hx hy)
  have hr := h.ratio_sum (x + y) (-x) hpair
  have hphase (t : A) :
      L2b.metricPairing q t (x + y) * q (t - x) =
        q x * q t *
          L2b.metricPairing q t y := by
    rw [L2b.core_gaussian_sub hq, hq.add_right, L2b.core_pairing_neg_right hq]
    field_simp [L2b.core_pairing_ne_zero hq t x]
  apply mul_left_cancel₀ (hq.nonzero x)
  calc
    _ = L2b.normalizedSum (fun t =>
        L2b.metricPairing q t (x + y) *
          (Fplus t / Fminus (t + -x))) := by
      rw [← L2b.core_normalizedSum_mul_left]
      apply L2b.core_normalizedSum_congr
      intro t
      rw [div_eq_mul_inv, inverse_minus hq h]
      have ht : -(t + -x) = x - t := by abel
      rw [ht]
      have hp := hphase t
      simp only [← sub_eq_add_neg]
      change q x * _ =
        L2b.metricPairing q t (x + y) *
          (Fplus t *
            (q (t - x) * Fplus (x - t)))
      linear_combination -(Fplus t * Fplus (x - t)) * hp
    _ = Fplus (x + y + -x) /
        (Fminus (x + y) * Fminus (-x)) := hr
    _ = _ := by
      rw [div_eq_mul_inv, mul_inv_rev, inverse_minus hq h, inverse_minus hq h,
        hq.even, neg_neg]
      have hy : x + y + -x = y := by abel
      have hn : -(x + y) = -x - y := by abel
      rw [hy, hn]
      ring

/-- The pair excluded from (7) is supplied by (4) and full reflection. -/
theorem pentagon36_origin (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) :
    L2b.normalizedSum (fun t => Fplus t * q t * Fplus (-t)) =
      Fplus 0 ^ 3 - (Fintype.card A : ℂ) * Fplus 0 := by
  have hs : L2b.sqrtCard A ^ 2 = (Fintype.card A : ℂ) := by
    exact L2b.core_sqrtCard_sq (A := A)
  have hsum :
      L2b.normalizedSum (fun t => Fplus t * q t *
        Fplus (-t)) =
        ((Fintype.card A : ℂ) +
          L2b.sqrtCard A * Fplus 0) /
            L2b.sqrtCard A := by
    unfold L2b.normalizedSum
    congr 1
    calc
      _ = ∑ t : A,
          (1 + L2b.sqrtCard A * Fplus 0 *
            (if t = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← reflection_all hq h t]
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, mul_ite]
  rw [hsum]
  calc
    _ = L2b.sqrtCard A + Fplus 0 := by
      apply (div_eq_iff L2b.sqrtCard_ne_zero).2
      linear_combination -hs
    _ = _ := by
      have he := origin_quadratic h
      linear_combination -(Fplus 0 + L2b.sqrtCard A) * he -
        Fplus 0 * hs

/-- Full (36), including the double-delta term. -/
theorem pentagon36_of_theorem2 (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (x y : A) :
    L2b.normalizedSum (fun t => Fplus t * q t * Fplus (x - t) *
      L2b.metricPairing q t y) =
        q (x + y) * Fplus (-x - y) * Fplus x * Fplus y -
          (Fintype.card A : ℂ) * Fplus 0 *
            (if x = 0 ∧ y = 0 then 1 else 0) := by
  by_cases hxy : x = 0 ∧ y = 0
  · rcases hxy with ⟨rfl, rfl⟩
    simpa only [zero_sub, add_zero, neg_zero, L2b.metric_zero hq,
      L2b.core_pairing_zero_right (hq),
      one_mul, mul_one, ite_true, and_self, pow_succ, pow_zero] using pentagon36_origin hq h
  · rw [if_neg hxy, mul_zero, sub_zero]
    apply pentagon36_off_origin hq h x y
    intro hp
    exact hxy ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- Full (36) with y=-w, in the existing Fourier/kernel notation. -/
theorem kernel_fourier_of_theorem2 (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (x w : A) :
    L2b.fourier q (L2b.pentagonKernel q Fplus x) w =
      q (x - w) * Fplus (w - x) * Fplus x * Fplus (-w) -
        (Fintype.card A : ℂ) * Fplus 0 *
          (if x = 0 ∧ w = 0 then 1 else 0) := by
  have hp := pentagon36_of_theorem2 hq h x (-w)
  have harg : -x - -w = w - x := by abel
  simp only [harg, ← sub_eq_add_neg, neg_eq_zero] at hp
  unfold L2b.fourier L2b.pentagonKernel
  calc
    _ = L2b.normalizedSum (fun t => Fplus t * q t *
        Fplus (x - t) * L2b.metricPairing q t (-w)) := by
      apply L2b.core_normalizedSum_congr
      intro t
      ring
    _ = _ := by
      by_cases hxw : x = 0 ∧ w = 0
      · simpa only [if_pos hxw] using hp
      · simpa only [if_neg hxw] using hp

/-- (33), obtained by multiplying the kernel identity by the Fourier transform.
The two zero corrections cancel using full reflection and the origin quadratic. -/
theorem transformed_pentagon_of_theorem2 (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) (x w : A) :
    Fplus x * L2b.fourier q Fplus (w - x) =
      (-L2b.fourier q Fplus 0) * L2b.sqrtCard A *
        (if w = 0 then 1 else 0) +
      L2b.fourier q Fplus w * L2b.fourier q (L2b.pentagonKernel q Fplus x) w := by
  have he := origin_quadratic h
  have hs : L2b.sqrtCard A ^ 2 = (Fintype.card A : ℂ) := by
    exact L2b.core_sqrtCard_sq (A := A)
  by_cases hw : w = 0
  · subst w
    simp only [zero_sub, ite_true, mul_one]
    by_cases hx : x = 0
    · subst x
      rw [kernel_fourier_of_theorem2 hq h 0 0]
      simp only [sub_zero, neg_zero, L2b.metric_zero hq,
        one_mul, ite_true, and_self, mul_one]
      have hcub : Fplus 0 * Fplus 0 *
          Fplus 0 - (Fintype.card A : ℂ) * Fplus 0 =
            L2b.sqrtCard A + Fplus 0 := by
        linear_combination (Fplus 0 + L2b.sqrtCard A) * he +
          Fplus 0 * hs
      rw [hcub]
      ring
    · have hk := kernel_fourier_of_theorem2 hq h x 0
      simp only [sub_zero, zero_sub, neg_zero, and_true,
        if_neg hx, mul_zero, sub_zero] at hk
      have hr := reflection_all hq h x
      simp only [if_neg hx, mul_zero, add_zero] at hr
      have hk0 : L2b.fourier q
          (L2b.pentagonKernel q (Fplus) x) 0 =
            Fplus 0 := by
        calc
          _ = Fplus 0 *
              (Fplus x * Fplus (-x) * q x) := by
            rw [hk]
            ring
          _ = _ := by rw [hr, mul_one]
      rw [hk0, fourier_proportional hq h (-x), hq.even,
        fourier_proportional hq h 0, L2b.metric_zero hq, mul_one]
      linear_combination
        L2b.fourierScalar q (Fplus) * hr -
        L2b.fourierScalar q (Fplus) * he
  · have hxw : ¬ (x = 0 ∧ w = 0) := fun hp => hw hp.2
    rw [if_neg hw, mul_zero, zero_add, kernel_fourier_of_theorem2 hq h x w,
      if_neg hxw, mul_zero, sub_zero, fourier_proportional hq h w,
      fourier_proportional hq h (w - x)]
    have hphase : q (x - w) = q (w - x) := by
      rw [show x - w = -(w - x) by abel, hq.even]
    rw [hphase]
    have hr := reflection_all hq h w
    simp only [if_neg hw, mul_zero, add_zero] at hr
    linear_combination
      -(L2b.fourierScalar q (Fplus) *
        q (w - x) * Fplus (w - x) *
          Fplus x) * hr

theorem pentagon_constant_ne_zero (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) :
    -L2b.fourier q Fplus 0 ≠ 0 := by
  apply neg_ne_zero.mpr
  rw [fourier_proportional hq h 0, L2b.metric_zero hq, mul_one]
  exact mul_ne_zero (fourierScalar_ne_zero hq h) (special_values_ne_zero hq h 0).1

/-- Apply `L2c.pentagon_of_transformed` to [RW26, (33)]. -/
theorem pentagon_of_theorem2 (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) :
    L2b.Pentagon q Fplus (-L2b.fourier q Fplus 0) := by
  apply L2c.pentagon_of_transformed hq
  intro x w
  by_cases hw : w = 0
  · simpa only [if_pos hw] using transformed_pentagon_of_theorem2 hq h x w
  · simpa only [if_neg hw] using transformed_pentagon_of_theorem2 hq h x w

/-- Reusable upstream-to-(31) interface for every finite metric group. -/
theorem isFiniteQuantumDilogarithm_of_theorem2 (hq : L2b.IsMetricGaussian q)
    (h : Theorem2Input A q Fplus Fminus) :
    L2b.IsFiniteQuantumDilogarithm q Fplus := by
  exact ⟨_, pentagon_constant_ne_zero hq h, pentagon_of_theorem2 hq h⟩

/-- Compatibility without changing L2c: its existing input transports to this
generic input on the Smith group. No rank or group-size premise is added. -/
theorem l2c_theorem2Input {M : ℕ} [Fact (4 ≤ M)]
    {Fplus Fminus : L2c.RWGroup M → ℂ}
    (h : L2c.Theorem2Input M Fplus Fminus) :
    Theorem2Input (L2b.G M) (L2b.gaussian M)
      (L2c.smithValues M Fplus) (L2c.smithValues M Fminus) := by
  refine ⟨?_, ?_, L2c.smith_mixed_reflection h, ?_,
    L2c.smith_ratio_sum h, L2c.smith_agree_off_zero h⟩
  · simpa only [L2c.smithValues, Function.comp_apply, L2c.fromSmith_zero,
      originPlus, L2b.card_G, L2c.originPlus] using h.origin_plus
  · simpa only [L2c.smithValues, Function.comp_apply, L2c.fromSmith_zero,
      originMinus, L2b.card_G, L2c.originMinus] using h.origin_minus
  · exact L2c.smith_positive_fourier h

end SICLean.L2rc.Generic
