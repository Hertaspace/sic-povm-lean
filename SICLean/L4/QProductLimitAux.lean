import Mathlib

/-!
Finite bilateral sums with Gaussian-binomial coefficients converge by Tannery's
theorem. The argument is independent of the q-product definitions: convergence
of `d` to a nonzero limit bounds both `d n` and its total inverse uniformly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace SICLean.L4.QProductLimitAux

/-- The finite bilateral coefficient used in the symmetric truncations. -/
def bilateralCoeff (d : ℕ → ℂ) (J : ℤ → ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  if -(n : ℤ) ≤ k ∧ k ≤ (n : ℤ) then
    J k * d (2 * n) / (d ((n : ℤ) + k).toNat * d ((n : ℤ) - k).toNat)
  else 0

lemma tsum_bilateralCoeff (d : ℕ → ℂ) (J : ℤ → ℂ) (n : ℕ) :
    (∑' k, bilateralCoeff d J n k) =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        J k * d (2 * n) / (d ((n : ℤ) + k).toNat * d ((n : ℤ) - k).toNat) := by
  rw [tsum_eq_sum (s := Finset.Icc (-(n : ℤ)) (n : ℤ))]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [bilateralCoeff, if_pos (Finset.mem_Icc.mp hk)]
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact if_neg hk

lemma index_add_tendsto (k : ℤ) :
    Tendsto (fun n : ℕ => ((n : ℤ) + k).toNat) atTop atTop := by
  refine tendsto_atTop.2 fun m => ?_
  filter_upwards [eventually_ge_atTop (m + k.natAbs)] with n hn
  have hk : -(k.natAbs : ℤ) ≤ k := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le k
  have hm : (m : ℤ) ≤ (n : ℤ) + k := by omega
  omega

/-- Uniform bounds on the finite factors permit termwise passage to the limit. -/
lemma tendsto_bilateralCoeff_tsum (d : ℕ → ℂ) (J : ℤ → ℂ) (D : ℂ)
    (hd : Tendsto d atTop (𝓝 D)) (hD : D ≠ 0) (hJ : Summable fun k => ‖J k‖) :
    Tendsto (fun n => ∑' k, bilateralCoeff d J n k) atTop (𝓝 ((∑' k, J k) / D)) := by
  have hinv := hd.inv₀ hD
  obtain ⟨A, hA, hAb⟩ := (Metric.isBounded_range_of_tendsto d hd).exists_pos_norm_le
  obtain ⟨B, hB, hBb⟩ :=
    (Metric.isBounded_range_of_tendsto (fun n => (d n)⁻¹) hinv).exists_pos_norm_le
  have hbound : ∀ n k, ‖bilateralCoeff d J n k‖ ≤ (A * B * B) * ‖J k‖ := by
    intro n k
    unfold bilateralCoeff
    split_ifs with hk
    · rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul]
      have ha := hAb _ (mem_range_self (2 * n))
      have hb := hBb _ (mem_range_self ((n : ℤ) + k).toNat)
      have hc := hBb _ (mem_range_self ((n : ℤ) - k).toNat)
      calc
        ‖J k‖ * ‖d (2*n)‖ * (‖(d ((n : ℤ) + k).toNat)⁻¹‖ *
            ‖(d ((n : ℤ) - k).toNat)⁻¹‖) ≤
            (‖J k‖ * A) * (B * B) :=
          mul_le_mul (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
            (mul_le_mul hb hc (norm_nonneg _) hB.le)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
        _ = _ := by ring
    · simp only [norm_zero]
      positivity
  have hpoint (k : ℤ) :
      Tendsto (fun n => bilateralCoeff d J n k) atTop (𝓝 (J k / D)) := by
    have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
      refine tendsto_atTop.2 fun m => ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      omega
    have hplus := hd.comp (index_add_tendsto k)
    have hminus : Tendsto (fun n : ℕ => d ((n : ℤ) - k).toNat) atTop (𝓝 D) := by
      simpa only [sub_eq_add_neg, Function.comp_def] using hd.comp (index_add_tendsto (-k))
    have ht := ((tendsto_const_nhds (x := J k)).mul (hd.comp htwo)).div (hplus.mul hminus)
      (mul_ne_zero hD hD)
    have hlim : J k * D / (D * D) = J k / D := by field_simp
    rw [hlim] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop k.natAbs] with n hn
    have hk₁ : -(k.natAbs : ℤ) ≤ k := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le k
    have hk₂ : k ≤ (k.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact le_abs_self k
    simp only [bilateralCoeff, if_pos (show -(n : ℤ) ≤ k ∧ k ≤ (n : ℤ) by omega)]
    rfl
  have hlim := tendsto_tsum_of_dominated_convergence (hJ.mul_left (A * B * B))
    hpoint (Eventually.of_forall hbound)
  simpa only [tsum_div_const] using hlim

/-- Recover an infinite bilateral product formula from its finite identities. -/
lemma hasSum_of_bilateralCoeff (d : ℕ → ℂ) (J : ℤ → ℂ) (P Q : ℕ → ℂ)
    (D X Y : ℂ) (hd : Tendsto d atTop (𝓝 D)) (hD : D ≠ 0)
    (hP : Tendsto P atTop (𝓝 X)) (hQ : Tendsto Q atTop (𝓝 Y))
    (hJ : Summable fun k => ‖J k‖)
    (hfinite : ∀ᶠ n in atTop, (∑' k, bilateralCoeff d J n k) = P n * Q n) :
    HasSum J (X * Y * D) := by
  have hlim := tendsto_bilateralCoeff_tsum d J D hd hD hJ
  have heq : (∑' k, J k) / D = X * Y :=
    tendsto_nhds_unique hlim ((hP.mul hQ).congr' (hfinite.mono fun _ hn => hn.symm))
  have hs := hJ.of_norm.hasSum
  rw [div_eq_iff hD] at heq
  exact heq ▸ hs

end SICLean.L4.QProductLimitAux
