import SICLean.L2b.FiniteQD

set_option autoImplicit false

/-!
# A ratio form derived from [RW26, (36)]

E is F⁺. Only its value at zero is changed to obtain F⁻.
This file adds no external input and does not assume a Shintani--Faddeev dictionary.
-/

noncomputable section

namespace SICLean.L2r

variable {A : Type*} [AddCommGroup A] [Fintype A]

local instance : DecidableEq A := Classical.decEq A

def minusValues (E : A → ℂ) (x : A) : ℂ := if x = 0 then (E 0)⁻¹ else E x

theorem minusValues_ne_zero {q E : A → ℂ} (hq : L2b.IsMetricGaussian q)
    (hE : L2b.IsFiniteQuantumDilogarithm q E) (x : A) : minusValues E x ≠ 0 := by
  unfold minusValues
  split_ifs
  · exact inv_ne_zero (L2b.fqd_everywhere_ne_zero hq hE 0)
  · exact L2b.fqd_everywhere_ne_zero hq hE x

theorem minusValues_inverse {q E : A → ℂ} (hq : L2b.IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : L2b.IsFiniteQuantumDilogarithm q E) (x : A) :
    (minusValues E x)⁻¹ = q x * E (-x) := by
  by_cases hx : x = 0
  · subst x
    simp [minusValues, L2b.metric_zero hq]
  · rw [minusValues, if_neg hx]
    apply inv_eq_of_mul_eq_one_right
    have hr := L2b.fqd_reflection hq hcard hE x hx
    calc
      E x * (q x * E (-x)) = (E x * E (-x)) * q x := by ring
      _ = 1 := by rw [hr, inv_mul_cancel₀ (hq.nonzero x)]

/-- [RW26, Thm. 2, (7)], derived from [RW26, (31)] through [RW26, (36)]. -/
theorem fqd_ratio_pentagon {q E : A → ℂ} (hq : L2b.IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : L2b.IsFiniteQuantumDilogarithm q E)
    (w v : A) (hwv : ¬ (w = 0 ∧ v = 0)) :
    L2b.normalizedSum (fun x => L2b.metricPairing q x w * E x / minusValues E (x + v)) =
      E (w + v) / (minusValues E w * minusValues E v) := by
  have hn : ¬ (-v = 0 ∧ -w = 0) := by
    simpa only [neg_eq_zero, and_comm] using hwv
  have hp := L2b.fqd_pentagon36 hq hcard hE (-v) (-w)
  simp only [if_neg hn, mul_zero, sub_zero] at hp
  have hchar (t : A) :
      L2b.metricPairing q (-t - v) w =
        L2b.metricPairing q (-v) w * L2b.metricPairing q t (-w) := by
    rw [show -t - v = -v + -t by abel, hq.add_left]
    congr 1
    simpa only [neg_neg] using L2b.aux_pairing_neg_neg hq t (-w)
  have hcancel : L2b.metricPairing q (-v) w * q (-v + -w) = q w * q v := by
    have hprod := hq.add_right (-v) w (-w)
    rw [add_neg_cancel, L2b.aux_pairing_zero_right hq,
      L2b.aux_pairing_neg_neg hq] at hprod
    unfold L2b.metricPairing at hprod ⊢
    rw [hq.even] at hprod ⊢
    rw [show -v + -w = -(v + w) by abel, hq.even]
    field_simp [hq.nonzero v, hq.nonzero w] at hprod ⊢
    linear_combination -hprod
  calc
    L2b.normalizedSum (fun x => L2b.metricPairing q x w * E x /
        minusValues E (x + v)) =
      L2b.normalizedSum (fun t => L2b.metricPairing q (-t - v) w *
        E (-t - v) * (q t * E t)) := by
      simp only [div_eq_mul_inv, minusValues_inverse hq hcard hE]
      unfold L2b.normalizedSum
      congr 1
      let e : A ≃ A := (Equiv.neg A).trans (Equiv.addRight (-v))
      exact (Equiv.sum_comp e _).symm.trans (by
        apply Finset.sum_congr rfl
        intro t _
        simp only [e, Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addRight,
          sub_eq_add_neg, neg_neg, add_assoc,
          neg_add_cancel, add_zero, hq.even])
    _ = L2b.metricPairing q (-v) w *
      L2b.normalizedSum (fun t => E t * q t * E (-v - t) *
        L2b.metricPairing q t (-w)) := by
      rw [← L2b.aux_normalizedSum_mul_left]
      congr 1
      funext t
      rw [hchar, show -t - v = -v - t by abel]
      ring
    _ = E (w + v) / (minusValues E w * minusValues E v) := by
      rw [hp, div_eq_mul_inv, mul_inv,
        minusValues_inverse hq hcard hE w, minusValues_inverse hq hcard hE v]
      rw [show -(-v) - -w = w + v by abel]
      linear_combination E (w + v) * E (-v) * E (-w) * hcancel

end SICLean.L2r
