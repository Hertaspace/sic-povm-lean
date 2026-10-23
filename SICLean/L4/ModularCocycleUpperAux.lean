import SICLean.L4.ModularPhi

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4.ModularCocycleUpperAux

lemma analyticAt_e_mul (m : ℤ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => (e q.2) ^ m * e q.1) p := by
  simp_rw [e_int_mul]
  unfold e
  exact ((analyticAt_const.mul (analyticAt_const.mul analyticAt_snd)).cexp').mul
    ((analyticAt_const.mul analyticAt_fst).cexp')

lemma finite_symbol_joint_analytic (m k : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ =>
      qPochhammerIntNumerator ((e p.2) ^ m * e p.1) (e p.2) k) Set.univ ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ =>
      qPochhammerIntDenominator ((e p.2) ^ m * e p.1) (e p.2) k) Set.univ := by
  have hP : ∀ p : ℂ × ℂ, AnalyticAt ℂ (fun q : ℂ × ℂ => e q.2) p := by
    intro p
    unfold e
    exact (analyticAt_const.mul analyticAt_snd).cexp'
  have hprod (r : ℕ) (x : ℂ × ℂ → ℂ) (hx : ∀ p, AnalyticAt ℂ x p) :
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ => qPochhammerNat (x p) (e p.2) r) Set.univ := by
    unfold qPochhammerNat
    apply Finset.analyticOnNhd_fun_prod
    intro j hj p hp
    exact analyticAt_const.sub ((hx p).mul ((hP p).pow j))
  by_cases hk : 0 ≤ k
  · simp only [qPochhammerIntNumerator, qPochhammerIntDenominator, hk, if_true]
    exact ⟨hprod k.toNat _ (analyticAt_e_mul m), analyticOnNhd_const⟩
  · simp only [qPochhammerIntNumerator, qPochhammerIntDenominator, hk, if_false]
    refine ⟨analyticOnNhd_const, hprod (-k).toNat _ ?_⟩
    intro p
    exact (analyticAt_e_mul m p).mul (by
      simp_rw [e_int_mul]
      unfold e
      exact (analyticAt_const.mul (analyticAt_const.mul analyticAt_snd)).cexp')

lemma entire_eventually_ne_zero {f : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) {a : ℂ} (ha : f a ≠ 0) (z : ℂ) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, f w ≠ 0 := by
  have hanta : meromorphicOrderAt f a ≠ ⊤ := by
    rw [(hf a).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr ha)]
    exact WithTop.zero_ne_top
  have hmer : MeromorphicOn f Set.univ := fun w _ => (hf w).meromorphicAt
  have hnt : meromorphicOrderAt f z ≠ ⊤ := by
    exact hmer.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ a) (Set.mem_univ z) hanta
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf z).meromorphicAt).mp hnt

lemma one_sub_mul_e_eventually_ne_zero (A z : ℂ) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, 1 - A * e w ≠ 0 := by
  have hf : ∀ w : ℂ, AnalyticAt ℂ (fun v : ℂ => 1 - A * e v) w := by
    intro w
    unfold e
    fun_prop
  by_cases hA : A = 1
  · subst A
    apply entire_eventually_ne_zero hf (a := Complex.I)
    have he : ‖e Complex.I‖ < 1 := norm_e_lt_one UpperHalfPlane.I
    intro h
    have hh : e Complex.I = 1 := (sub_eq_zero.mp (by simpa using h)).symm
    rw [hh, norm_one] at he
    exact (lt_irrefl _ he)
  · apply entire_eventually_ne_zero hf (a := 0)
    simpa [e] using sub_ne_zero.mpr (Ne.symm hA)

lemma qPochhammerNat_exp_eventually_ne_zero (A q : ℂ) (r : ℕ) (z : ℂ) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, qPochhammerNat (A * e w) q r ≠ 0 := by
  have hev : ∀ᶠ w : ℂ in 𝓝[≠] z, ∀ j ∈ Finset.range r,
      1 - (A * q ^ j) * e w ≠ 0 := by
    exact (Finset.eventually_all _).mpr (fun j hj => one_sub_mul_e_eventually_ne_zero _ z)
  filter_upwards [hev] with w hw
  unfold qPochhammerNat
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hw j hj

lemma finite_denominator_eventually_ne_zero (m k : ℤ) (z τ : ℂ) :
    ∀ᶠ w : ℂ in 𝓝[≠] z,
      qPochhammerIntDenominator ((e τ) ^ m * e w) (e τ) k ≠ 0 := by
  by_cases hk : 0 ≤ k
  · simp [qPochhammerIntDenominator, hk]
  · have h := qPochhammerNat_exp_eventually_ne_zero
      ((e τ) ^ m * (e τ) ^ k) (e τ) (-k).toNat z
    simpa only [qPochhammerIntDenominator, hk, if_false, mul_assoc, mul_left_comm, mul_comm] using h

lemma etaDenom_ne_zero_upper (M : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    etaDenom M τ ≠ 0 := by
  intro hz
  have hi : (M 1 0 : ℝ) * τ.im = 0 := by
    have h := congrArg Complex.im hz
    simpa [etaDenom] using h
  have hcR : (M 1 0 : ℝ) = 0 :=
    (mul_eq_zero.mp hi).resolve_right (ne_of_gt hτ)
  have hc : M 1 0 = 0 := by exact_mod_cast hcR
  have hd : M 1 1 = 0 := by
    have h := congrArg Complex.re hz
    simpa [etaDenom, hc] using h
  have hdet := det_coe_int M
  simp [hc, hd] at hdet

lemma etaMobius_im_pos (M : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (etaMobius M τ).im := by
  have h := coe_smul_eq_etaMobius M (⟨τ, hτ⟩ : ℍ)
  rw [← h]
  exact (M • (⟨τ, hτ⟩ : ℍ)).im_pos

lemma tendsto_div_nhdsNE (a z : ℂ) (ha : a ≠ 0) :
    Tendsto (fun w : ℂ => w / a) (𝓝[≠] z) (𝓝[≠] (z / a)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (show ContinuousAt (fun w : ℂ => w / a) z by fun_prop).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, div_left_inj' ha] using hw

lemma qNumerator_analyticAt (m : ℤ) (τ w : ℂ) (hτ : 0 < τ.im) :
    AnalyticAt ℂ (fun v : ℂ => modularPhiQNumerator m v τ) w := by
  have hP := analyticOnNhd_qPochhammer_joint
    ((e τ) ^ m * e w, e τ) ⟨norm_pos_iff.mpr (e_ne_zero τ), norm_e_lt_one ⟨τ, hτ⟩⟩
  have hx : AnalyticAt ℂ (fun v : ℂ => (e τ) ^ m * e v) w := by
    unfold e
    fun_prop
  have hp := hx.prod (analyticAt_const (v := e τ))
  simpa only [modularPhiQNumerator, Function.comp_def] using hP.comp (x := w) hp

lemma qNumerator_eventually_ne_zero (m : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, modularPhiQNumerator m w τ ≠ 0 := by
  have hwval : modularPhiQNumerator m ((1 - (m : ℂ)) * τ) τ =
      qPochhammer (e τ) (e τ) := by
    unfold modularPhiQNumerator
    have hsplit : e ((1 - (m : ℂ)) * τ) = e τ * (e τ) ^ (-m) := by
      rw [show (1 - (m : ℂ)) * τ = τ + (-m : ℤ) * τ by push_cast; ring,
        e_add', ← e_int_mul]
    rw [hsplit]
    have hcancel : (e τ) ^ m * (e τ) ^ (-m) = 1 := by
      rw [← zpow_add₀ (e_ne_zero τ)]
      simp
    rw [show (e τ) ^ m * (e τ * (e τ) ^ (-m)) =
      ((e τ) ^ m * (e τ) ^ (-m)) * e τ by ring, hcancel, one_mul]
  apply entire_eventually_ne_zero (fun w => qNumerator_analyticAt m τ w hτ)
    (a := (1 - (m : ℂ)) * τ)
  rw [hwval]
  exact qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero τ)) (norm_e_lt_one ⟨τ, hτ⟩)

lemma qDenominator_eventually_ne_zero (M : SL(2, ℤ)) (n : ℤ)
    (z τ : ℂ) (hτ : 0 < τ.im) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, modularPhiQDenominator M n w τ ≠ 0 := by
  have h := qNumerator_eventually_ne_zero n (z / etaDenom M τ)
    (etaMobius M τ) (etaMobius_im_pos M hτ)
  exact (tendsto_div_nhdsNE _ _ (etaDenom_ne_zero_upper M hτ)).eventually h

lemma translation_e_parameter (k : ℤ) (τ : ℂ) :
    e (etaMobius (ModularGroup.T ^ k) τ) = e τ := by
  have he : etaMobius (ModularGroup.T ^ k) τ = τ + (k : ℂ) := by
    simp [etaMobius, etaDenom, ModularGroup.coe_T_zpow]
  rw [he, e_add', e_intCast, mul_one]

lemma translation_qDenominator (k n : ℤ) (w τ : ℂ) :
    modularPhiQDenominator (ModularGroup.T ^ k) n w τ = modularPhiQNumerator n w τ := by
  simp [modularPhiQDenominator, modularPhiQNumerator, translation_e_parameter,
    etaDenom, ModularGroup.coe_T_zpow]

lemma finite_symbol_eq_qProduct_germ (k m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    (fun w => qPochhammerInt ((e τ) ^ m * e w) (e τ) (n - m)) =ᶠ[𝓝[≠] z]
      (fun w => modularPhiQProduct (ModularGroup.T ^ k) m n w τ) := by
  have hnz := qNumerator_eventually_ne_zero n z τ hτ
  filter_upwards [hnz] with w hw
  rw [modularPhiQProduct, translation_qDenominator]
  have harg : ((e τ) ^ m * e w) * (e τ) ^ (n - m) = (e τ) ^ n * e w := by
    calc _ = ((e τ) ^ m * (e τ) ^ (n - m)) * e w := by ring
         _ = _ := by rw [← zpow_add₀ (e_ne_zero τ), add_sub_cancel]
  have hden : qPochhammer (((e τ) ^ m * e w) * (e τ) ^ (n - m)) (e τ) ≠ 0 := by
    rw [harg]
    exact hw
  rw [qPochhammerInt_eq_div _ _ _ (norm_pos_iff.mpr (e_ne_zero τ))
    (norm_e_lt_one ⟨τ, hτ⟩) hden, harg]
  rfl

lemma translation_qProduct_cross_mul (j m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    qPochhammerIntNumerator ((e τ) ^ m * e z) (e τ) (n - m) *
      modularPhiQDenominator (ModularGroup.T ^ j) n z τ =
    modularPhiQNumerator m z τ *
      qPochhammerIntDenominator ((e τ) ^ m * e z) (e τ) (n - m) := by
  rw [translation_qDenominator]
  have h := qPochhammer_shift_int_cleared ((e τ) ^ m * e z) (e τ) (n - m)
    (norm_pos_iff.mpr (e_ne_zero τ)) (norm_e_lt_one ⟨τ, hτ⟩)
  have harg : ((e τ) ^ m * e z) * (e τ) ^ (n - m) = (e τ) ^ n * e z := by
    calc _ = ((e τ) ^ m * (e τ) ^ (n - m)) * e z := by ring
         _ = _ := by rw [← zpow_add₀ (e_ne_zero τ), add_sub_cancel]
  rw [harg] at h
  simpa only [modularPhiQNumerator, mul_comm] using h.symm

lemma qProduct_cocycle_germ (M N : SL(2, ℤ)) (m k n : ℤ) (z τ : ℂ)
    (hτ : 0 < τ.im)
    (hden : etaDenom (M * N) τ = etaDenom M (etaMobius N τ) * etaDenom N τ)
    (hmob : etaMobius (M * N) τ = etaMobius M (etaMobius N τ)) :
    (fun w => modularPhiQProduct (M * N) m n w τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhiQProduct M k n (w / etaDenom N τ) (etaMobius N τ) *
        modularPhiQProduct N m k w τ) := by
  have he := qDenominator_eventually_ne_zero N k z τ hτ
  filter_upwards [he] with w hw
  have hDn : modularPhiQDenominator (M * N) n w τ =
      modularPhiQDenominator M n (w / etaDenom N τ) (etaMobius N τ) := by
    simp only [modularPhiQDenominator, hden, hmob, div_div]
    rw [mul_comm (etaDenom M (etaMobius N τ)) (etaDenom N τ)]
  have hmid : modularPhiQNumerator k (w / etaDenom N τ) (etaMobius N τ) =
      modularPhiQDenominator N k w τ := rfl
  simp only [modularPhiQProduct, hDn, hmid]
  field_simp

/-- The supported finite/positive-c construction agrees with the q quotient
in the upper half-plane. The explicit branches avoid importing its wrapper. -/
lemma constructed_eq_qProduct_germ (M : SL(2, ℤ))
    (hsupport : 0 < M 1 0 ∨ ∃ j : ℤ, M = ModularGroup.T ^ j)
    (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    (fun w => if 0 < M 1 0 then modularPhi M m n w τ
      else qPochhammerInt ((e τ) ^ m * e w) (e τ) (n - m)) =ᶠ[𝓝[≠] z]
      (fun w => modularPhiQProduct M m n w τ) := by
  rcases hsupport with hM | ⟨j, rfl⟩
  · simpa only [hM, if_true] using modularPhi_eq_qProduct_germ M hM m n z τ hτ
  · simpa [ModularGroup.coe_T_zpow] using finite_symbol_eq_qProduct_germ j m n z τ hτ

/-- Denominator-cleared upper-half-plane identity for the explicit branches
of every supported chart. No value at a zero denominator is cancelled. -/
lemma constructed_qProduct_cross_mul (M : SL(2, ℤ))
    (hsupport : 0 < M 1 0 ∨ ∃ j : ℤ, M = ModularGroup.T ^ j)
    (m n : ℤ) (κ : ℕ → ℤ) (p : ℂ × ℂ)
    (hp : p ∈ (if 0 < M 1 0 then modularPhiChartDomain M m n κ else Set.univ))
    (hτ : 0 < p.2.im) :
    (if 0 < M 1 0 then modularPhiChartNumerator M m n κ p.1 p.2
      else qPochhammerIntNumerator ((e p.2) ^ m * e p.1) (e p.2) (n - m)) *
        modularPhiQDenominator M n p.1 p.2 =
      modularPhiQNumerator m p.1 p.2 *
        (if 0 < M 1 0 then modularPhiChartDenominator M m n κ p.1 p.2
          else qPochhammerIntDenominator ((e p.2) ^ m * e p.1) (e p.2) (n - m)) := by
  rcases hsupport with hM | ⟨j, rfl⟩
  · simp only [hM, if_true] at hp ⊢
    exact modularPhiChart_qProduct_cross_mul M hM m n κ p hp hτ
  · simpa [ModularGroup.coe_T_zpow] using translation_qProduct_cross_mul j m n p.1 p.2 hτ

end SICLean.L4.ModularCocycleUpperAux
