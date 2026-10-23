import SICLean.L5.ConjugationStrip
import SICLean.L4.FaddeevContinuation

set_option autoImplicit false

/-!
Fixed-index conjugation for the existing continuation charts. Conjugation
exchanges a numerator product with a denominator product. Total inversion
preserves this equality even at the representative's assigned value zero;
no multiplication identity at a zero or pole follows from it.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace SICLean.L5.ConjugationContinuationAux

open SICLean.L4

lemma shiftedArgument_conj (b : ℝ) (z : ℂ) (k : ℤ) :
    (starRingEnd ℂ) (shiftedArgument (b : ℂ) z k) =
      shiftedArgument (b : ℂ) ((starRingEnd ℂ) z) (-k) := by
  simp [shiftedArgument]

lemma continuationFactor_conj (b : ℝ) (w : ℂ) :
    (starRingEnd ℂ) (continuationFactor (b : ℂ) w) =
      continuationFactor (b : ℂ) ((starRingEnd ℂ) w) := by
  simp [continuationFactor, ← Complex.exp_conj, map_ofNat]

lemma positive_argument_conj (b : ℝ) (z : ℂ) (n j : ℕ) :
    (starRingEnd ℂ) (shiftedArgument (b : ℂ) z (n : ℤ) +
      ((j : ℂ) + 1 / 2) * Complex.I * b) =
      shiftedArgument (b : ℂ) ((starRingEnd ℂ) z) (-(n : ℤ)) -
        ((j : ℂ) + 1 / 2) * Complex.I * b := by
  simp [shiftedArgument_conj, map_ofNat]
  ring

lemma phiChart_nat_conj (b : ℝ) (hb : 0 < b) (z : ℂ) (n : ℕ)
    (hz : InStrip (b : ℂ) (shiftedArgument (b : ℂ) z (n : ℤ))) :
    (starRingEnd ℂ) (phiChart (b : ℂ) z (n : ℤ)) =
      (phiChart (b : ℂ) ((starRingEnd ℂ) z) (-(n : ℤ)))⁻¹ := by
  rw [phiChart_neg_nat]
  have hnat : phiChart (b : ℂ) z (n : ℤ) =
      phi (b : ℂ) (shiftedArgument (b : ℂ) z (n : ℤ)) /
        ∏ j ∈ Finset.range n, continuationFactor (b : ℂ)
          (shiftedArgument (b : ℂ) z (n : ℤ) +
            ((j : ℂ) + 1 / 2) * Complex.I * b) := by
    simp [phiChart, continuationNumerator, continuationDenominator]
  rw [hnat, map_div₀, map_prod, ConjugationStrip.phi_conj b hb _ hz,
    shiftedArgument_conj]
  simp only [continuationFactor_conj, positive_argument_conj]
  rw [mul_inv_rev, div_eq_mul_inv, mul_comm]

/-- Reflection uses the chart `-k`, independently of the rounding rule. -/
lemma phiChart_conj (b : ℝ) (hb : 0 < b) (z : ℂ) (k : ℤ)
    (hz : InStrip (b : ℂ) (shiftedArgument (b : ℂ) z k)) :
    (starRingEnd ℂ) (phiChart (b : ℂ) z k) =
      (phiChart (b : ℂ) ((starRingEnd ℂ) z) (-k))⁻¹ := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact phiChart_nat_conj b hb z n hz
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt (neg_pos.mpr hk))
    have hstrip : InStrip (b : ℂ)
        (shiftedArgument (b : ℂ) ((starRingEnd ℂ) z) (n : ℤ)) := by
      rw [← hn, ← shiftedArgument_conj]
      exact (ConjugationStrip.inStrip_conj_iff b _).mpr hz
    have h := phiChart_nat_conj b hb ((starRingEnd ℂ) z) n hstrip
    have hc := congrArg (fun w : ℂ => ((starRingEnd ℂ) w)⁻¹) h
    simpa only [map_inv₀, starRingEnd_self_apply, inv_inv, ← hn, neg_neg] using hc.symm

/-- A total-inverse identity for the concrete representative, derived from
the integral strip identity and the explicit finite continuation products. -/
lemma phiExtended_conj_total (b : ℝ) (hb : 0 < b) (z : ℂ) :
    (starRingEnd ℂ) (phiExtended (b : ℂ) z) =
      (phiExtended (b : ℂ) ((starRingEnd ℂ) z))⁻¹ := by
  let k := continuationIndex (b : ℂ) z
  have hab := ConjugationStrip.admissibleB_of_real b hb
  have hk := shiftedArgument_inStrip (b : ℂ) z hab
  have hkc : InStrip (b : ℂ)
      (shiftedArgument (b : ℂ) ((starRingEnd ℂ) z) (-k)) := by
    rw [← shiftedArgument_conj]
    exact (ConjugationStrip.inStrip_conj_iff b _).mpr hk
  rw [phiExtended_eq_phiChart (b : ℂ) z k hab hk,
    phiExtended_eq_phiChart (b : ℂ) ((starRingEnd ℂ) z) (-k) hab hkc]
  exact phiChart_conj b hb z k hk

end SICLean.L5.ConjugationContinuationAux
