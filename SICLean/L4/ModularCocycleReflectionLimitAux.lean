import SICLean.L4.ModularCocycleReflectionAux
import SICLean.L4.ModularCocycleUpperAux

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4.ModularCocycleReflectionLimitAux

open ModularCocycleReflectionAux ModularCocycleUpperAux

lemma qProduct_one_one_zero (M : SL(2, ℤ)) (τ : ℂ) :
    modularPhiQProduct M 1 1 0 τ =
      qPochhammer (e τ) (e τ) /
        qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) := by
  simp [modularPhiQProduct, modularPhiQNumerator, modularPhiQDenominator, e]

lemma qDenominator_one_zero_ne_zero (M : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    modularPhiQDenominator M 1 0 τ ≠ 0 := by
  have hη := etaMobius_im_pos M hτ
  simpa [modularPhiQDenominator, e] using
    qPochhammer_q_ne_zero (e (etaMobius M τ))
      (norm_pos_iff.mpr (e_ne_zero _)) (norm_e_lt_one ⟨etaMobius M τ, hη⟩)

lemma qProduct_one_one_analyticAt_zero (M : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticAt ℂ (fun w : ℂ => modularPhiQProduct M 1 1 w τ) 0 := by
  have hden : AnalyticAt ℂ (fun w : ℂ => modularPhiQDenominator M 1 w τ) 0 := by
    change AnalyticAt ℂ
      (fun w : ℂ => modularPhiQNumerator 1 (w / etaDenom M τ) (etaMobius M τ)) 0
    have hdiv : AnalyticAt ℂ (fun w : ℂ => w / etaDenom M τ) 0 := by fun_prop
    exact (qNumerator_analyticAt 1 (etaMobius M τ) (0 / etaDenom M τ)
      (etaMobius_im_pos M hτ)).comp (x := 0) hdiv
  exact (qNumerator_analyticAt 1 τ 0 hτ).div hden (qDenominator_one_zero_ne_zero M τ hτ)

lemma qProduct_zero_zero_shift (M : SL(2, ℤ)) (w τ : ℂ) (hτ : 0 < τ.im) :
    modularPhiQProduct M 0 0 w τ =
      ((1 - e w) / (1 - e (w / etaDenom M τ))) * modularPhiQProduct M 1 1 w τ := by
  have hN : modularPhiQNumerator 0 w τ = (1 - e w) * modularPhiQNumerator 1 w τ := by
    have h := qPochhammer_shift_nat (e w) (e τ) 1
      (norm_pos_iff.mpr (e_ne_zero τ)) (norm_e_lt_one ⟨τ, hτ⟩)
    simpa [modularPhiQNumerator, qPochhammerNat, mul_comm] using h
  have hD : modularPhiQDenominator M 0 w τ =
      (1 - e (w / etaDenom M τ)) * modularPhiQDenominator M 1 w τ := by
    have hη := etaMobius_im_pos M hτ
    have h := qPochhammer_shift_nat (e (w / etaDenom M τ)) (e (etaMobius M τ)) 1
      (norm_pos_iff.mpr (e_ne_zero _)) (norm_e_lt_one ⟨etaMobius M τ, hη⟩)
    simpa [modularPhiQDenominator, qPochhammerNat, mul_comm] using h
  unfold modularPhiQProduct
  rw [hN, hD]
  exact mul_div_mul_comm _ _ _ _

lemma exp_sub_one_slope_tendsto (a : ℂ) :
    Tendsto (fun w : ℂ => (1 - Complex.exp (a * w)) / w)
      (𝓝[≠] 0) (𝓝 (-a)) := by
  have he : HasDerivAt (fun w : ℂ => Complex.exp (a * w)) a 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).const_mul a).cexp using 1 <;> simp
  have h : HasDerivAt (fun w : ℂ => 1 - Complex.exp (a * w)) (-a) 0 := by
    convert! (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub he using 1 <;> simp
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h.tendsto_slope_zero

lemma exp_ratio_tendsto (a b : ℂ) (hb : b ≠ 0) :
    Tendsto (fun w : ℂ => (1 - Complex.exp (a * w)) / (1 - Complex.exp (b * w)))
      (𝓝[≠] 0) (𝓝 (a / b)) := by
  have h := (exp_sub_one_slope_tendsto a).div (exp_sub_one_slope_tendsto b)
    (neg_ne_zero.mpr hb)
  simp only [neg_div_neg_eq] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact div_div_div_cancel_right₀ (by simpa using hw) _ _

lemma e_ratio_tendsto (T : ℂ) (hT : T ≠ 0) :
    Tendsto (fun w : ℂ => (1 - e w) / (1 - e (w / T))) (𝓝[≠] 0) (𝓝 T) := by
  let a : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have h := exp_ratio_tendsto a (a / T) (div_ne_zero ha hT)
  rw [div_div_cancel₀ ha] at h
  convert h using 1
  funext w
  unfold e
  dsimp [a]
  congr 2
  ring

lemma tendsto_neg_zero_nhdsNE :
    Tendsto (fun w : ℂ => -w) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
  simpa only [div_neg, div_one, zero_div, neg_zero] using
    tendsto_div_nhdsNE (-1) 0 (by norm_num)

lemma reflection_base_qProduct (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Complex.exp (reflectionExponent M 1 1 0 τ) =
      etaDenom M τ *
        (qPochhammer (e τ) (e τ) /
          qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))) ^ 2 := by
  have hdom := mem_modularPhiDomain_of_im_pos M hM hτ
  have href :
      (fun w => modularPhi M 1 1 w τ * modularPhi M 0 0 (-w) τ)
        =ᶠ[𝓝[≠] (0 : ℂ)] (fun w => Complex.exp (reflectionExponent M 1 1 w τ)) := by
    simpa only [sub_self] using reflection_exponential_germ M hM 1 1 0 τ hdom
  have h11 := modularPhi_eq_qProduct_germ M hM 1 1 0 τ hτ
  have h00 := tendsto_neg_zero_nhdsNE.eventually (modularPhi_eq_qProduct_germ M hM 0 0 0 τ hτ)
  have heq : (fun w => Complex.exp (reflectionExponent M 1 1 w τ))
      =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun w => modularPhiQProduct M 1 1 w τ *
        (((1 - e (-w)) / (1 - e (-w / etaDenom M τ))) *
          modularPhiQProduct M 1 1 (-w) τ)) := by
    filter_upwards [href, h11, h00] with w hw h11w h00w
    rw [← hw, h11w, h00w, qProduct_zero_zero_shift M (-w) τ hτ]
  have hQ : Tendsto (fun w : ℂ => modularPhiQProduct M 1 1 w τ)
      (𝓝[≠] 0) (𝓝 (modularPhiQProduct M 1 1 0 τ)) :=
    (qProduct_one_one_analyticAt_zero M τ hτ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hR := (e_ratio_tendsto (etaDenom M τ) (etaDenom_ne_zero_upper M hτ)).comp
    tendsto_neg_zero_nhdsNE
  have hlimit := hQ.mul (hR.mul (hQ.comp tendsto_neg_zero_nhdsNE))
  have hExp : Tendsto (fun w : ℂ => Complex.exp (reflectionExponent M 1 1 w τ))
      (𝓝[≠] 0) (𝓝 (Complex.exp (reflectionExponent M 1 1 0 τ))) := by
    apply ContinuousAt.tendsto (by
      unfold reflectionExponent modularPhiFactorPoint modularPhiSArgument modularPhiFactorInput
      fun_prop) |>.mono_left nhdsWithin_le_nhds
  have h := tendsto_nhds_unique hExp (hlimit.congr' heq.symm)
  rw [qProduct_one_one_zero] at h
  convert h using 1 <;> ring

lemma eta_qProduct_square (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) :
    etaDenom M τ *
        (qPochhammer (e τ) (e τ) /
          qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))) ^ 2 =
      (etaMultiplier M) ^ (-2 : ℤ) * e ((etaMobius M τ - τ) / 12) := by
  have hT := etaDenom_ne_zero_upper M hτ
  have hη := etaMobius_im_pos M hτ
  have hden : qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) ≠ 0 :=
    qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _))
      (norm_e_lt_one ⟨etaMobius M τ, hη⟩)
  have hpf := qPochhammer_eta_prefactor M hM (⟨τ, hτ⟩ : ℍ) hden
  have hsq : Complex.sqrt (etaDenom M τ) ^ 2 = etaDenom M τ :=
    (modularPhi_sqrt_admissible M τ (mem_modularPhiDomain_of_im_pos M hM hτ)).2.1
  have he : (e ((etaMobius M τ - τ) / 24)) ^ 2 = e ((etaMobius M τ - τ) / 12) := by
    calc
      _ = e (((etaMobius M τ - τ) / 24) + ((etaMobius M τ - τ) / 24)) := by
        rw [e_add']; ring
      _ = _ := by congr 1; ring
  apply mul_left_cancel₀ hT
  calc
    _ = (etaDenom M τ * (qPochhammer (e τ) (e τ) /
          qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)))) ^ 2 := by ring
    _ = (etaPhase M τ) ^ 2 := congrArg (fun x : ℂ => x ^ 2) hpf
    _ = _ := by
      simp only [etaPhase, mul_pow, hsq, he, zpow_neg, zpow_ofNat, inv_pow]
      ring

lemma reflection_base_normalized_upper (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Complex.exp (reflectionExponent M 1 1 0 τ) =
      (etaMultiplier M) ^ (-2 : ℤ) * e ((etaMobius M τ - τ) / 12) := by
  rw [reflection_base_qProduct M hM τ hτ]
  exact eta_qProduct_square M hM τ hτ

end SICLean.L4.ModularCocycleReflectionLimitAux
