import SICLean.L2b.FiniteQDDefs

set_option autoImplicit false

noncomputable section
open scoped BigOperators
namespace SICLean.L2b
variable {A : Type*} [AddCommGroup A] [Fintype A]
local instance finiteQDAuxDecidableEq : DecidableEq A := Classical.decEq A

theorem aux_pairing_zero_left {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) :
    metricPairing q 0 x = 1 := by
  simp [metricPairing, metric_zero hq, hq.nonzero x]

theorem aux_pairing_zero_right {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) :
    metricPairing q x 0 = 1 := by
  rw [metric_pairing_symmetric]
  exact aux_pairing_zero_left hq x

theorem aux_normalizedSum_add (f g : A → ℂ) :
    normalizedSum (fun x => f x + g x) = normalizedSum f + normalizedSum g := by
  simp [normalizedSum, Finset.sum_add_distrib, add_div]

theorem aux_normalizedSum_mul_left (c : ℂ) (f : A → ℂ) :
    normalizedSum (fun x => c * f x) = c * normalizedSum f := by
  simp only [normalizedSum, ← Finset.mul_sum, mul_div_assoc]

theorem aux_normalizedSum_mul_right (f : A → ℂ) (c : ℂ) :
    normalizedSum (fun x => f x * c) = normalizedSum f * c := by
  simp [normalizedSum, Finset.sum_mul, div_mul_eq_mul_div]

theorem aux_normalizedSum_swap (f : A → A → ℂ) :
    normalizedSum (fun x => normalizedSum (f x)) =
      normalizedSum (fun y => normalizedSum (fun x => f x y)) := by
  simp only [normalizedSum, Finset.sum_div]
  rw [Finset.sum_comm]

theorem aux_normalizedSum_translate (f : A → ℂ) (z : A) :
    normalizedSum (fun x => f (x + z)) = normalizedSum f := by
  unfold normalizedSum
  congr 1
  exact Equiv.sum_comp (Equiv.addRight z) f

theorem aux_fourier_add (q f g : A → ℂ) :
    fourier q (fun x => f x + g x) = fun y => fourier q f y + fourier q g y := by
  funext y
  simp only [fourier, add_mul, aux_normalizedSum_add]

theorem aux_fourier_mul_left (q : A → ℂ) (c : ℂ) (f : A → ℂ) :
    fourier q (fun x => c * f x) = fun y => c * fourier q f y := by
  funext y
  simp only [fourier, mul_assoc, aux_normalizedSum_mul_left]

theorem aux_fourier_delta {q : A → ℂ} (hq : IsMetricGaussian q) (c : ℂ) (y : A) :
    fourier q (fun x => if x = 0 then c else 0) y = c / sqrtCard A := by
  simp [fourier, normalizedSum, ite_mul, aux_pairing_zero_left hq]

theorem aux_fourier_constant {q : A → ℂ} (hq : IsMetricGaussian q) (c : ℂ) (y : A) :
    fourier q (fun _ => c) y =
      c * (Fintype.card A : ℂ) / sqrtCard A * (if y = 0 then 1 else 0) := by
  unfold fourier normalizedSum
  rw [← Finset.mul_sum, character_sum hq]
  by_cases hy : y = 0 <;> simp [hy]

theorem aux_fourier_convolution {q : A → ℂ} (hq : IsMetricGaussian q)
    (f g : A → ℂ) (y : A) :
    fourier q (fun x => normalizedSum (fun z => f (x - z) * g z)) y =
      fourier q f y * fourier q g y := by
  unfold fourier
  simp_rw [← aux_normalizedSum_mul_right]
  rw [aux_normalizedSum_swap]
  have h (z : A) :
      normalizedSum (fun x => f (x - z) * g z * metricPairing q x (-y)) =
        normalizedSum (fun x => f x * g z * metricPairing q (x + z) (-y)) := by
    rw [← aux_normalizedSum_translate
      (fun x => f (x - z) * g z * metricPairing q x (-y)) z]
    simp
  simp_rw [h, hq.add_left]
  have hh (z : A) :
      normalizedSum (fun x => f x * g z *
        (metricPairing q x (-y) * metricPairing q z (-y))) =
      normalizedSum (fun x => f x * metricPairing q x (-y)) *
        (g z * metricPairing q z (-y)) := by
    rw [← aux_normalizedSum_mul_right]
    congr 1
    funext x
    ring
  simp_rw [hh]
  conv_rhs => rw [aux_normalizedSum_mul_right]
  exact aux_normalizedSum_mul_left (normalizedSum (fun x => f x * metricPairing q x (-y)))
    (fun z => g z * metricPairing q z (-y))

/-- If two functions agree away from zero, their Fourier transforms differ by a constant. -/
theorem aux_fourier_affine_of_off_zero {q f g : A → ℂ}
    (hq : IsMetricGaussian q) (c : ℂ)
    (h : ∀ x : A, x ≠ 0 → f x = c * g x) :
    ∃ b : ℂ, ∀ y : A, fourier q f y = c * fourier q g y + b := by
  refine ⟨(f 0 - c * g 0) / sqrtCard A, ?_⟩
  have hf : f = fun x => c * g x + if x = 0 then f 0 - c * g 0 else 0 := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, h x hx]
  intro y
  conv_lhs => rw [hf]
  simp only [aux_fourier_add, aux_fourier_mul_left, aux_fourier_delta hq]
theorem aux_pairing_neg_neg {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q (-x) (-y) = metricPairing q x y := by
  simp only [metricPairing, ← neg_add, hq.even]

theorem aux_fourier_reflection {q : A → ℂ} (hq : IsMetricGaussian q)
    (f : A → ℂ) (y : A) :
    fourier q (fun x => f (-x)) y = fourier q f (-y) := by
  unfold fourier normalizedSum
  simp only [neg_neg]
  congr 1
  calc
    (∑ x : A, f (-x) * metricPairing q x (-y)) =
        ∑ x : A, f (-(-x)) * metricPairing q (-x) (-y) :=
      (Equiv.sum_comp (Equiv.neg A) (fun x => f (-x) * metricPairing q x (-y))).symm
    _ = ∑ x : A, f x * metricPairing q x y := by
      simp only [neg_neg, aux_pairing_neg_neg hq]

theorem aux_sqrtCard_sq : sqrtCard A ^ 2 = (Fintype.card A : ℂ) := by
  unfold sqrtCard
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rfl

end SICLean.L2b
