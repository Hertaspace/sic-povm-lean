import SICLean.L4.ModularDistribution
import SICLean.L4.SpecialValueUnitAction

set_option autoImplicit false

/-!
# Zero-orbit specializations of the modular distribution cocycle

The deleted-zero limit of the raw q quotient is kept separate from the
actual, regularized value of `modularPhi`. All analytic input is from L4.
-/

noncomputable section

open SICLean.L4
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L5.DistributionOrbitCocycleAux

lemma qTail_zero_zero (q : ℂ) :
    modularPhiLatticeQTail 0 0 q = qPochhammer q q := by
  simp [modularPhiLatticeQTail, qPochhammerNat, e]

lemma qRegularPart_zero (M : SL(2, ℤ)) (τ : ℂ) :
    modularPhiLatticeQRegularPart M 0 0 τ =
      qPochhammer (e τ) (e τ) /
        qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) := by
  simp only [modularPhiLatticeQRegularPart, zero_div, qTail_zero_zero]

/-- The raw q quotient has a deleted-zero limit, after cancelling the common zero factor. -/
theorem modularPhi_zero_upper_tendsto (M : SL(2, ℤ)) (hc : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Tendsto (fun z => modularPhiQProduct M 0 0 z τ) (𝓝[≠] (0 : ℂ))
      (𝓝 (etaDenom M τ *
        (qPochhammer (e τ) (e τ) /
          qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))))) := by
  have han := m37c_repair_moving_analytic M hc 0 0 0 τ hτ
  simp only [Int.cast_zero, zero_mul, zero_add, sub_zero,
    show ¬ (1 : ℤ) ≤ 0 by norm_num, if_false] at han
  have hemb : AnalyticAt ℂ (fun z : ℂ => (z, τ)) 0 := by fun_prop
  have hslice := han.comp (x := (0 : ℂ)) hemb
  have hlim := hslice.continuousAt.tendsto.mono_left
    (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have heq := m37c_qProduct_eq_repair_germ M hc 0 0 0 0 (by norm_num) 0 τ hτ
  simp only [Int.cast_zero, zero_mul, zero_add, sub_zero,
    show ¬ (1 : ℤ) ≤ 0 by norm_num, if_false] at heq
  have hlim' := hlim.congr' heq.symm
  simpa only [Function.comp_def, modularPhiCommonZeroFactor_zero,
    qRegularPart_zero] using hlim'

/-- The actual zero-center value uses the separately regularized Phi. -/
theorem modularPhi_zero_upper_value (M : SL(2, ℤ)) (hc : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) : modularPhi M 0 0 0 τ = etaPhase M τ := by
  have hvalue := modularPhi_lattice_upper_value M hc 0 0 0 0 (by norm_num) τ hτ
  have hqvalue := m37c_qValue_upper M hc 0 τ hτ
  simpa [m37c_qCorrection, qPochhammerNat] using hvalue.trans hqvalue

/-- The fixed-point limit is an ordinary joint limit of the actual Phi. -/
theorem modularPhi_zero_fixedPoint_tendsto (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hc : 0 < M 1 0) (htr : 2 < M 0 0 + M 1 1)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) :
    Tendsto (fun z : ℂ × ℂ => modularPhi M 0 0 z.1 z.2)
      (𝓝 ((0 : ℂ), (τ₀ : ℂ)))
      (𝓝 ((etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ))) := by
  have hT' : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ) := by
    simpa [etaDenom] using hT
  simpa using modularPhi_fixedPoint_lattice_tendsto M hc htr 0 0 τ₀ hT' hfix
    0 0 (by norm_num)

/-- The unshifted center is the value needed by the singleton zero orbit. -/
theorem modularPhi_zero_fixedPoint_value (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hc : 0 < M 1 0) (htr : 2 < M 0 0 + M 1 1)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) :
    modularPhi M 0 0 0 (τ₀ : ℂ) = (etaMultiplier M)⁻¹ *
      (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) := by
  have hT' : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ) := by
    simpa [etaDenom] using hT
  simpa using modularPhi_fixedPoint_lattice_value_of_nonpos M hc htr 0 0 τ₀
    hT' hfix 0 0 (by norm_num) (by norm_num)

lemma sqrt_nat_pow (x : ℝ) (hx : 0 ≤ x) (r : ℕ) :
    Real.sqrt (x ^ r) = Real.sqrt x ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg hx r), ih, pow_succ]

/-- At a positive real fixed point, the actual zero-center cocycle
determines the principal-root sign in the multiplier power law. -/
theorem etaMultiplier_pow_fixedPoint (M : SL(2, ℤ)) (τ₀ : ℝ) (r : ℕ)
    (hr : 0 < r) (hc : 0 < M 1 0) (htr : 2 < M 0 0 + M 1 1)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) :
    etaMultiplier (M ^ r) = etaMultiplier M ^ r := by
  have hpow := specialValue_pow_admissible M ⟨hc, htr⟩ r hr
  have hp := ModularCocycleMatrixAux.pow_fixedPoint M τ₀ hfix hT r
  have hT' : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ) := by
    simpa [etaDenom] using hT
  have hcont (N : SL(2, ℤ)) (hNc : 0 < N 1 0)
      (hNtr : 2 < N 0 0 + N 1 1)
      (hNfix : etaMobius N (τ₀ : ℂ) = (τ₀ : ℂ))
      (hNT : 0 < (etaDenom N (τ₀ : ℂ)).re) :
      ContinuousAt (fun p : ℂ × ℂ => modularPhi N 0 0 p.1 p.2)
        ((0 : ℂ), (τ₀ : ℂ)) := by
    simpa only [ContinuousAt,
      modularPhi_zero_fixedPoint_value N τ₀ hNc hNtr hNfix hNT] using
      modularPhi_zero_fixedPoint_tendsto N τ₀ hNc hNtr hNfix hNT
  have hL : ContinuousAt
      (fun w => modularPhiConstructed (M ^ r) 0 0 w (τ₀ : ℂ)) (0 : ℂ) := by
    simp only [modularPhiConstructed_of_pos (M ^ r) hpow.1]
    have hemb : ContinuousAt (fun w : ℂ => (w, (τ₀ : ℂ))) 0 := by fun_prop
    have hslice := (hcont (M ^ r) hpow.1 hpow.2 hp.1 hp.2.2).comp
      (x := (0 : ℂ)) hemb
    simpa only [Function.comp_def] using hslice
  have hR (j : ℕ) : ContinuousAt
      (fun w => modularPhi M 0 0 (w / etaDenom M (τ₀ : ℂ) ^ j) (τ₀ : ℂ))
      (0 : ℂ) := by
    have hemb : ContinuousAt
        (fun w : ℂ => (w / etaDenom M (τ₀ : ℂ) ^ j, (τ₀ : ℂ))) 0 := by fun_prop
    simpa only [Function.comp_def] using
      (hcont M hc htr hfix hT).comp_of_eq hemb (by simp)
  have hiter := modularPhi_iterate_fixedPoint M hc htr (fun _ => 0) r 0 τ₀
    hfix hT hL (fun j _ => hR j)
  simp only [modularPhiConstructed_of_pos (M ^ r) hpow.1, zero_div,
    modularPhi_zero_fixedPoint_value (M ^ r) τ₀ hpow.1 hpow.2 hp.1 hp.2.2,
    modularPhi_zero_fixedPoint_value M τ₀ hc htr hfix hT,
    Finset.prod_const, Finset.card_range] at hiter
  have hDpow : ((M ^ r) 1 0 : ℝ) * τ₀ + ((M ^ r) 1 1 : ℝ) =
      ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) ^ r := by
    apply Complex.ofReal_injective
    simpa [etaDenom] using hp.2.1
  have hsqrt :
      (Real.sqrt (((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) ^ r) : ℂ) =
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) ^ r := by
    exact_mod_cast sqrt_nat_pow _ hT'.le r
  rw [hDpow, hsqrt, mul_pow] at hiter
  have hroot : (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) ^ r ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (Real.sqrt_pos.mpr hT').ne'
  have hinv : (etaMultiplier (M ^ r))⁻¹ = (etaMultiplier M ^ r)⁻¹ := by
    apply mul_right_cancel₀ hroot
    simpa only [inv_pow] using hiter
  exact inv_injective hinv

end SICLean.L5.DistributionOrbitCocycleAux
