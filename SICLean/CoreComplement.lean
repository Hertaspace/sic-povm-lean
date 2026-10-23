import SICLean.WHBasic

/-!
# Complements of r-SICs

Complementing every projector preserves distinctness and constant pairwise traces, while
changing its rank from `r` to `d - r`.
-/

noncomputable section

open Matrix

namespace SICLean

/-- `P ↦ 1 - P` turns an r-SIC into a `(d-r)`-SIC. -/
theorem hasRSIC_complement {d r : ℕ} (hr0 : 0 < r) (hrd : r < d)
    (h : HasRSIC d r) : HasRSIC d (d - r) := by
  rcases h with ⟨P, hinj, hP, α, hα⟩
  have htrace (j : Fin (d ^ 2)) : (P j).trace = (r : ℂ) := by
    rw [← rank_eq_trace_of_idem (P j) (hP j).2.1, (hP j).2.2]
  have hidem (j : Fin (d ^ 2)) : (1 - P j) * (1 - P j) = 1 - P j := by
    simp [sub_mul, mul_sub, (hP j).2.1]
  refine ⟨fun j => 1 - P j, ?_, ?_, ?_⟩
  · intro j k hjk
    exact hinj (sub_right_injective hjk)
  · intro j
    refine ⟨isHermitian_one.sub (hP j).1, hidem j, ?_⟩
    apply Nat.cast_injective (R := ℂ)
    rw [rank_eq_trace_of_idem (1 - P j) (hidem j), trace_sub,
      trace_one, Fintype.card_fin, htrace j, Nat.cast_sub hrd.le]
  · refine ⟨α + d - 2 * r, ?_⟩
    intro j k hjk
    simp only [sub_mul, mul_sub, one_mul, mul_one, trace_sub,
      trace_one, Fintype.card_fin, htrace j, htrace k, hα hjk]
    ring

end SICLean
