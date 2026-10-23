import SICLean.L2b.FiniteQDAux
import SICLean.L2b.FiniteQDCore

set_option autoImplicit false

/-!
# Finite quantum dilogarithms: [RW26, Thm. 5] and the zero-inclusive pentagon

[RW26, (33)] through [RW26, (36)]. The affine Fourier argument treats the
origin together with the nonzero labels.
-/

noncomputable section

namespace SICLean.L2b

variable {A : Type*} [AddCommGroup A] [Fintype A]

local instance finiteQDDecidableEq : DecidableEq A := Classical.decEq A

theorem transformed_pentagon {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) (x w : A) :
    E x * fourier q E (w - x) =
      C * sqrtCard A * (if w = 0 then 1 else 0) +
        fourier q E w * fourier q (pentagonKernel q E x) w := by
  exact transformed_pentagon_core hq hC hE x w

theorem fourier_everywhere_ne_zero {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (w : A) :
    fourier q E w ≠ 0 := by
  exact fourier_everywhere_ne_zero_core hq hE w

/-- [RW26, (34)]. This statement precedes the determination of C. -/
theorem reflection_with_constant {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) (u : A) :
    E u * E (-u) * q u =
      sqrtCard A * E 0 * (if u = 0 then 1 else 0) - C / fourier q E 0 := by
  exact reflection_with_constant_core hq hC hE u

theorem fqd_everywhere_ne_zero {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (u : A) : E u ≠ 0 := by
  exact fqd_everywhere_ne_zero_core hq hE u

theorem kernel_fourier_symmetry {q E : A → ℂ} (hq : IsMetricGaussian q)
    (x w : A) :
    fourier q (pentagonKernel q E x) w =
      q (x - w) / q w * fourier q (pentagonKernel q E x) (x - w) := by
  exact kernel_fourier_symmetry_core hq x w

theorem fourier_product_off_zero {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ u : A, u ≠ 0 →
      fourier q E u * fourier q E (-u) = d * q u := by
  exact fourier_product_off_zero_core hq hE

/-- A form of [RW26, (35)], before choosing the nonzero-point product. -/
theorem aux_fqd_relation35 {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hP : Pentagon q E C) (x : A) (hx : x ≠ 0) :
    E x * fourier q E x * fourier q E (-x) =
      C * sqrtCard A * fourier q E x + q x * E x * fourier q E 0 ^ 2 := by
  have h0 := transformed_pentagon hq hC hP x 0
  have h1 := transformed_pentagon hq hC hP x x
  have hk := kernel_fourier_symmetry (E := E) hq x x
  simp only [zero_sub, ite_true, mul_one] at h0
  simp only [sub_self, if_neg hx, mul_zero, zero_add] at h1
  simp only [sub_self, metric_zero hq, one_div] at hk
  have hk' : q x * fourier q (pentagonKernel q E x) x =
      fourier q (pentagonKernel q E x) 0 := by
    rw [hk]
    field_simp [hq.nonzero x]
  linear_combination fourier q E x * h0 - (q x * fourier q E 0) * h1 -
    (fourier q E x * fourier q E 0) * hk'

/-- Proportionality away from zero, from [RW26, (35)]. -/
theorem fourier_proportional_off_zero {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ x : A, x ≠ 0 → fourier q E x = lam * q x * E x := by
  obtain ⟨C, hC, hP⟩ := hE
  obtain ⟨d, hd, hprod⟩ := fourier_product_off_zero hq ⟨C, hC, hP⟩
  have hF (x : A) := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ x
  have hs := sqrtCard_ne_zero (A := A)
  have hrel (x : A) (hx : x ≠ 0) :
      E x * (d - fourier q E 0 ^ 2) * q x =
        C * sqrtCard A * fourier q E x := by
    have h0 := transformed_pentagon hq hC hP x 0
    have h1 := transformed_pentagon hq hC hP x x
    have hk := kernel_fourier_symmetry (E := E) hq x x
    have hp := hprod x hx
    simp only [zero_sub, ite_true, mul_one] at h0
    simp only [sub_self, if_neg hx, mul_zero, zero_add] at h1
    simp only [sub_self, metric_zero hq, one_div] at hk
    have hk' : q x * fourier q (pentagonKernel q E x) x =
        fourier q (pentagonKernel q E x) 0 := by
      rw [hk]
      field_simp [hq.nonzero x]
    linear_combination -E x * hp + fourier q E x * h0 -
      (q x * fourier q E 0) * h1 -
      (fourier q E x * fourier q E 0) * hk'
  by_cases hex : ∃ x : A, x ≠ 0
  · obtain ⟨v, hv⟩ := hex
    have hn : d - fourier q E 0 ^ 2 ≠ 0 := by
      intro h
      have hr := hrel v hv
      rw [h, mul_zero, zero_mul] at hr
      exact mul_ne_zero (mul_ne_zero hC hs) (hF v) hr.symm
    refine ⟨(d - fourier q E 0 ^ 2) / (C * sqrtCard A),
      div_ne_zero hn (mul_ne_zero hC hs), ?_⟩
    intro x hx
    have hr := hrel x hx
    field_simp
    linear_combination -hr
  · refine ⟨1, one_ne_zero, ?_⟩
    intro x hx
    exact (hex ⟨x, hx⟩).elim

/-- Affine form of the Fourier step in [RW26, Thm. 5]. -/
theorem gaussian_times_E_affine_fourier {q E : A → ℂ}
    (hq : IsMetricGaussian q) (hE : IsFiniteQuantumDilogarithm q E) :
    ∃ a b : ℂ, ∀ x : A, q x * E x = a * fourier q E x + b := by
  obtain ⟨C, hC, hP⟩ := hE
  obtain ⟨lam, hlam, hprop⟩ := fourier_proportional_off_zero hq ⟨C, hC, hP⟩
  have hF (x : A) := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ x
  have hEn (x : A) := fqd_everywhere_ne_zero hq ⟨C, hC, hP⟩ x
  let K : A → ℂ := fun x => fourier q (pentagonKernel q E x) 0
  have hK (x : A) (hx : x ≠ 0) : K x = fourier q E 0 / lam := by
    apply (eq_div_iff hlam).2
    apply mul_left_cancel₀ (hEn x)
    have ht := transformed_pentagon hq hC hP x x
    have hk := kernel_fourier_symmetry (E := E) hq x x
    simp only [sub_self, if_neg hx, mul_zero, zero_add] at ht
    simp only [sub_self, metric_zero hq, one_div] at hk
    rw [hprop x hx, hk] at ht
    dsimp [K]
    field_simp [hq.nonzero x] at ht
    linear_combination -ht
  have hKconv : K = fun x => normalizedSum (fun z => E (x - z) * (q z * E z)) := by
    funext x
    simp only [K, fourier, neg_zero, aux_pairing_zero_right hq, mul_one,
      pentagonKernel]
    congr 1
    funext z
    ring
  obtain ⟨b, hb⟩ := aux_fourier_affine_of_off_zero (g := fun _ => 1) hq
    (fourier q E 0 / lam) (by simpa using hK)
  have hprod (y : A) (hy : y ≠ 0) :
      fourier q E y * fourier q (fun x => q x * E x) y = b := by
    have ht := hb y
    rw [hKconv, aux_fourier_convolution hq] at ht
    simpa only [aux_fourier_constant hq, if_neg hy, mul_zero, zero_add] using ht
  let r : ℂ := -lam * C / fourier q E 0
  have hr : r ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hlam) hC) (hF 0)
  have hreflect (y : A) (hy : y ≠ 0) : fourier q E y * E (-y) = r := by
    have ht := reflection_with_constant hq hC hP y
    simp only [if_neg hy, mul_zero, zero_sub] at ht
    rw [hprop y hy]
    dsimp [r]
    linear_combination lam * ht
  have hdual (y : A) (hy : y ≠ 0) :
      fourier q (fun x => q x * E x) y = (b / r) * E (-y) := by
    apply mul_left_cancel₀ (hF y)
    rw [hprod y hy]
    calc
      b = (b / r) * r := by field_simp
      _ = fourier q E y * ((b / r) * E (-y)) := by
        rw [← hreflect y hy]
        ring
  obtain ⟨d, hd⟩ := aux_fourier_affine_of_off_zero hq (b / r) hdual
  refine ⟨b / r, d, ?_⟩
  intro x
  have ht := hd (-x)
  simpa only [fourier_twice hq, aux_fourier_reflection hq, neg_neg] using ht

theorem gaussian_times_E_not_constant_off_zero {q E : A → ℂ}
    (hq : IsMetricGaussian q) (hE : IsFiniteQuantumDilogarithm q E)
    (hcard : 4 < Fintype.card A) :
    ¬ ∃ c : ℂ, ∀ x : A, x ≠ 0 → q x * E x = c := by
  rintro ⟨c, hc⟩
  obtain ⟨C, hC, hP⟩ := hE
  have hF := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ 0
  have hE0 := fqd_everywhere_ne_zero hq ⟨C, hC, hP⟩
  apply gaussian_not_constant_off_zero hq hcard
  refine ⟨-(c ^ 2 * fourier q E 0) / C, ?_⟩
  intro x hx
  have hr := reflection_with_constant hq hC hP x
  have hc1 := hc x hx
  have hc2 := hc (-x) (neg_ne_zero.mpr hx)
  rw [hq.even] at hc2
  simp only [if_neg hx, mul_zero, zero_sub] at hr
  have hqx := hq.nonzero x
  field_simp at hr ⊢
  linear_combination -(fourier q E 0) * (q x * E (-x) * hc1 + c * hc2) +
    q x * hr

/-- Exactly the first half of Thm. 5(iii), also at zero. It is proved before
C and the origin quadratic are determined, following the affine argument. -/
theorem fqd_fourier {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) (u : A) :
    fourier q E u = fourierScalar q E * q u * E u := by
  obtain ⟨lam, hlam, hprop⟩ := fourier_proportional_off_zero hq hE
  obtain ⟨a, b, haff⟩ := gaussian_times_E_affine_fourier hq hE
  have hnot := gaussian_times_E_not_constant_off_zero hq hE hcard
  have hal : a * lam = 1 := by
    by_contra hn
    have hn' : 1 - a * lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
    apply hnot
    refine ⟨b / (1 - a * lam), ?_⟩
    intro x hx
    apply (eq_div_iff hn').2
    have ht := haff x
    rw [hprop x hx] at ht
    linear_combination ht
  have hex : ∃ x : A, x ≠ 0 := by
    by_contra hn
    apply hnot
    refine ⟨0, ?_⟩
    intro x hx
    exact (hn ⟨x, hx⟩).elim
  obtain ⟨v, hv⟩ := hex
  have hb : b = 0 := by
    have ht := haff v
    rw [hprop v hv] at ht
    linear_combination -(q v * E v) * hal - ht
  have hfull (x : A) : fourier q E x = lam * q x * E x := by
    have ht := haff x
    rw [hb, add_zero] at ht
    linear_combination -lam * ht - fourier q E x * hal
  have hscalar : fourierScalar q E = lam := by
    unfold fourierScalar
    apply (div_eq_iff (fqd_everywhere_ne_zero hq hE 0)).2
    simpa [metric_zero hq] using hfull 0
  rw [hscalar]
  exact hfull u

/-- The origin quadratic and the nonzero pentagon constant are forced together. -/
theorem aux_fqd_origin_and_constant {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) {C : ℂ} (hC : C ≠ 0) (hP : Pentagon q E C) :
    E 0 ^ 2 = sqrtCard A * E 0 + 1 ∧ C = -fourier q E 0 := by
  have hE : IsFiniteQuantumDilogarithm q E := ⟨C, hC, hP⟩
  have he := fqd_everywhere_ne_zero hq hE 0
  have hf := fourier_everywhere_ne_zero hq hE 0
  have hs := sqrtCard_ne_zero (A := A)
  have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have hev := fqd_everywhere_ne_zero hq hE v
  have hqv := hq.nonzero v
  have hrel := aux_fqd_relation35 hq hC hP v hv
  rw [fqd_fourier hq hcard hE v, fqd_fourier hq hcard hE (-v),
    hq.even, fourierScalar] at hrel
  field_simp [he, hf, hev, hqv] at hrel
  have hrv := reflection_with_constant hq hC hP v
  simp only [if_neg hv, mul_zero, zero_sub] at hrv
  field_simp at hrv
  have hr0 := reflection_with_constant hq hC hP (0 : A)
  simp only [neg_zero, metric_zero hq, mul_one, ite_true] at hr0
  field_simp at hr0
  have hc : fourier q E 0 * E 0 ^ 2 + C * (sqrtCard A * E 0 + 1) = 0 := by
    linear_combination -hrel + hrv
  have hcf : C + fourier q E 0 = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hs he)
    rw [mul_zero]
    linear_combination hc - hr0
  have hCeq : C = -fourier q E 0 := eq_neg_of_add_eq_zero_left hcf
  refine ⟨?_, hCeq⟩
  rw [hCeq] at hr0
  apply mul_left_cancel₀ hf
  linear_combination hr0

theorem fqd_origin_quadratic {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) :
    E 0 ^ 2 = sqrtCard A * E 0 + 1 := by
  obtain ⟨C, hC, hP⟩ := hE
  exact (aux_fqd_origin_and_constant hq hcard hC hP).1

theorem pentagon_constant_eq {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) :
    C = -fourier q E 0 := by
  exact (aux_fqd_origin_and_constant hq hcard hC hE).2

theorem fqd_reflection {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E)
    (u : A) (hu : u ≠ 0) : E u * E (-u) = (q u)⁻¹ := by
  obtain ⟨C, hC, hP⟩ := hE
  have hr := reflection_with_constant hq hC hP u
  rw [pentagon_constant_eq hq hcard hC hP] at hr
  have hF := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ 0
  simp only [if_neg hu, mul_zero, neg_div, div_self hF, sub_neg_eq_add,
    zero_add] at hr
  exact eq_inv_of_mul_eq_one_left hr

theorem fqd_reflection_all {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) (u : A) :
    E u * E (-u) * q u =
      1 + sqrtCard A * E 0 * (if u = 0 then 1 else 0) := by
  obtain ⟨C, hC, hP⟩ := hE
  have hr := reflection_with_constant hq hC hP u
  rw [pentagon_constant_eq hq hcard hC hP] at hr
  have hF := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ 0
  simpa only [neg_div, div_self hF, sub_neg_eq_add, add_comm] using hr

/-- A zero-inclusive inverse formula used to derive (36) from (33). -/
theorem fqd_inverse_reflection {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) (u : A) :
    (q u * E (-u))⁻¹ = E u - sqrtCard A * (if u = 0 then 1 else 0) := by
  by_cases hu : u = 0
  · subst u
    have he := fqd_everywhere_ne_zero hq hE 0
    have hr := fqd_origin_quadratic hq hcard hE
    simp only [neg_zero, metric_zero hq, one_mul, ite_true, mul_one]
    apply inv_eq_of_mul_eq_one_right
    linear_combination hr
  · have hr := fqd_reflection hq hcard hE u hu
    simp only [if_neg hu, mul_zero, sub_zero]
    apply inv_eq_of_mul_eq_one_right
    calc
      (q u * E (-u)) * E u = q u * (E u * E (-u)) := by ring
      _ = 1 := by rw [hr, mul_inv_cancel₀ (hq.nonzero u)]

/-- [RW26, (36)], including the value at (0,0). -/
theorem fqd_pentagon36 {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) (x y : A) :
    normalizedSum (fun t => E t * q t * E (x - t) * metricPairing q t y) =
      q (x + y) * E (-x - y) * E x * E y -
        (Fintype.card A : ℂ) * E 0 * (if x = 0 ∧ y = 0 then 1 else 0) := by
  obtain ⟨C, hC, hP⟩ := hE
  have hE : IsFiniteQuantumDilogarithm q E := ⟨C, hC, hP⟩
  have hFn (z : A) := fourier_everywhere_ne_zero hq hE z
  have hEn (z : A) := fqd_everywhere_ne_zero hq hE z
  have hCeq := pentagon_constant_eq hq hcard hC hP
  have hk0 (z : A) (hz : z ≠ 0) :
      fourier q (pentagonKernel q E z) 0 = E 0 := by
    have ht := transformed_pentagon hq hC hP z z
    have hk := kernel_fourier_symmetry (E := E) hq z z
    simp only [sub_self, if_neg hz, mul_zero, zero_add] at ht
    simp only [sub_self, metric_zero hq, one_div] at hk
    rw [fqd_fourier hq hcard hE z, hk, fourierScalar] at ht
    field_simp [hFn 0, hEn 0, hEn z, hq.nonzero z] at ht
    linear_combination -ht
  have hk00 : fourier q (pentagonKernel q E 0) 0 = E 0 + sqrtCard A := by
    have ht := transformed_pentagon hq hC hP 0 0
    simp only [sub_self, ite_true, mul_one, hCeq] at ht
    apply mul_left_cancel₀ (hFn 0)
    linear_combination -ht
  have hleft :
      normalizedSum (fun t => E t * q t * E (x - t) * metricPairing q t y) =
        fourier q (pentagonKernel q E x) (-y) := by
    unfold fourier pentagonKernel
    simp only [neg_neg]
    congr 1
    funext t
    ring
  rw [hleft]
  by_cases hy : y = 0
  · subst y
    simp only [neg_zero, add_zero, sub_zero, and_true]
    by_cases hx : x = 0
    · subst x
      rw [hk00]
      simp only [neg_zero, metric_zero hq, one_mul, ite_true, mul_one]
      have he := fqd_origin_quadratic hq hcard hE
      have hs := aux_sqrtCard_sq (A := A)
      linear_combination -(E 0 + sqrtCard A) * he - E 0 * hs
    · rw [hk0 x hx]
      simp only [if_neg hx, mul_zero, sub_zero]
      have hr := fqd_reflection_all hq hcard hE x
      simp only [if_neg hx, mul_zero, add_zero] at hr
      linear_combination -E 0 * hr
  · simp only [hy, and_false, if_false, mul_zero, sub_zero]
    have ht := transformed_pentagon hq hC hP x (-y)
    have hxy : -y - x = -x - y := by abel
    have hqxy : q (-x - y) = q (x + y) := by
      rw [show -x - y = -(x + y) by abel, hq.even]
    simp only [if_neg (neg_ne_zero.mpr hy), mul_zero, zero_add, hxy] at ht
    rw [fqd_fourier hq hcard hE (-x - y), hqxy] at ht
    have hr := fqd_reflection_all hq hcard hE y
    simp only [if_neg hy, mul_zero, add_zero] at hr
    apply mul_left_cancel₀ (hFn (-y))
    rw [← ht, fqd_fourier hq hcard hE (-y), hq.even]
    linear_combination -(fourierScalar q E * q (x + y) * E (-x - y) * E x) * hr

end SICLean.L2b
