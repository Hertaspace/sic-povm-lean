import SICLean.L4.UpperContourGeometry

set_option autoImplicit false

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContourShiftsAux

lemma triangular_twice (N : ℕ) : 2 * (N * (N + 1) / 2) = N * (N + 1) :=
  Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one N)

lemma triangular_succ (N : ℕ) :
    (N + 1) * (N + 1 + 1) / 2 = N * (N + 1) / 2 + (N + 1) := by
  have h := triangular_twice N
  have h' := triangular_twice (N + 1)
  nlinarith

lemma c_cast (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by
  exact_mod_cast Int.toNat_of_nonneg hM.le

lemma mobius_relation (M : SL(2, ℤ)) (τ : ℂ) (hT : etaDenom M τ ≠ 0) :
    (M 1 0 : ℂ) * etaMobius M τ = (M 0 0 : ℂ) - 1 / etaDenom M τ := by
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) -
      (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by exact_mod_cast det_coe_int M
  unfold etaMobius
  field_simp
  dsimp [etaDenom]
  linear_combination -hdet

lemma e_inv_denom (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    e (1 / etaDenom M τ) =
      e (etaMobius M τ) ^ (-((M 1 0).toNat : ℤ)) := by
  rw [zpow_neg, zpow_natCast, ← e_neg_inv_etaDenom_eq_pow M hM τ hT, ← e_neg']
  congr 1
  simp

lemma e_translate (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ z : ℂ) (j k : ℕ) :
    e (z + (j : ℂ) * etaDenom M τ + (k : ℂ)) =
      e z * e τ ^ ((M 1 0).toNat * j) := by
  rw [e_add', e_add', e_natCast, mul_one, ← e_nat_mul,
    e_etaDenom_eq_pow M hM.le, ← pow_mul]

lemma e_translate_div (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ z : ℂ)
    (hT : etaDenom M τ ≠ 0) (j k : ℕ) :
    e ((z + (j : ℂ) * etaDenom M τ + (k : ℂ)) / etaDenom M τ) =
      e (z / etaDenom M τ) *
        e (etaMobius M τ) ^ (-(((M 1 0).toNat * k : ℕ) : ℤ)) := by
  rw [show (z + (j : ℂ) * etaDenom M τ + (k : ℂ)) / etaDenom M τ =
    z / etaDenom M τ + (j : ℂ) + (k : ℂ) * (1 / etaDenom M τ) by
      field_simp]
  rw [e_add', e_add', e_natCast, mul_one, ← e_nat_mul, e_inv_denom M hM τ hT]
  rw [← zpow_natCast _ k, ← zpow_mul]
  congr 2
  push_cast
  ring

lemma e_slope_T (M : SL(2, ℤ)) (hM : 0 < M 1 0) (h ℓ : ℤ)
    (τ w : ℂ) (hT : etaDenom M τ ≠ 0) :
    e (UpperWindow.upperSlope M h ℓ τ w * etaDenom M τ) =
      UpperWindow.A ℓ τ w ^ (M 1 0).toNat := by
  unfold UpperWindow.upperSlope UpperWindow.s UpperWindow.A
  rw [div_mul_cancel₀ _ hT, e_add', e_add', e_intCast, mul_one,
    ← e_int_mul (etaDenom M τ) ℓ, e_etaDenom_eq_pow M hM.le,
    ← c_cast M hM, ← e_nat_mul]
  simp only [mul_zpow, ← zpow_natCast, ← zpow_mul, mul_comm]

lemma e_slope_one (M : SL(2, ℤ)) (hM : 0 < M 1 0) (h ℓ : ℤ)
    (τ w : ℂ) (hT : etaDenom M τ ≠ 0) :
    e (UpperWindow.upperSlope M h ℓ τ w) =
      UpperWindow.C M h τ w ^ (M 1 0).toNat := by
  have heq : UpperWindow.upperSlope M h ℓ τ w =
      ((M 1 0).toNat : ℂ) * ((-h : ℤ) * etaMobius M τ + w / etaDenom M τ) +
        ((ℓ + h * M 0 0 : ℤ) : ℂ) := by
    rw [c_cast M hM]
    have hr := mobius_relation M τ hT
    unfold UpperWindow.upperSlope UpperWindow.s
    push_cast
    field_simp at hr ⊢
    linear_combination h * hr
  rw [heq, e_add', e_intCast, mul_one, ← e_nat_mul, e_add', ← e_int_mul]
  rfl

lemma backward_cleared (d Q : ℂ) (hd : d ≠ 0)
    (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) (N : ℕ) :
    qPochhammer (d * Q ^ (-(N : ℤ))) Q =
      (-d) ^ N * Q ^ (-((N * (N + 1) / 2 : ℕ) : ℤ)) *
        qPochhammerNat (Q / d) Q N * qPochhammer d Q := by
  have hQ : Q ≠ 0 := norm_pos_iff.mp hQ0
  induction N with
  | zero => simp [qPochhammerNat_zero]
  | succ N ih =>
    have hstep := qPochhammer_shift_nat (d * Q ^ (-((N + 1 : ℕ) : ℤ))) Q 1 hQ0 hQ1
    have harg : d * Q ^ (-((N + 1 : ℕ) : ℤ)) * Q ^ 1 =
        d * Q ^ (-(N : ℤ)) := by
      simp only [pow_one, Nat.cast_add, Nat.cast_one, neg_add,
        zpow_add₀ hQ, zpow_neg, zpow_natCast, zpow_one]
      field_simp
    have hfactor : 1 - d * Q ^ (-((N + 1 : ℕ) : ℤ)) =
        (-d) * Q ^ (-((N + 1 : ℕ) : ℤ)) * (1 - (Q / d) * Q ^ N) := by
      simp only [zpow_neg, zpow_natCast, pow_succ]
      field_simp
      ring
    simp only [qPochhammerNat, Finset.prod_range_one, pow_zero, mul_one] at hstep
    rw [harg, hfactor, ih] at hstep
    rw [hstep, qPochhammerNat_succ, triangular_succ, pow_succ]
    rw [show Q ^ (-((N * (N + 1) / 2 + (N + 1) : ℕ) : ℤ)) =
      Q ^ (-((N * (N + 1) / 2 : ℕ) : ℤ)) * Q ^ (-((N + 1 : ℕ) : ℤ)) by
        rw [Nat.cast_add, neg_add, zpow_add₀ hQ]]
    ring

lemma q_single_shift (a d q Q : ℂ) (hd : d ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1)
    (N L : ℕ) (ha : qPochhammerNat a q N ≠ 0) :
    qPochhammer (a * q ^ N) q / qPochhammer (d * Q ^ (-(L : ℤ))) Q =
      (qPochhammer a q / qPochhammer d Q) *
        ((-d) ^ (-(L : ℤ)) * Q ^ (L * (L + 1) / 2)) /
        (qPochhammerNat a q N * qPochhammerNat (Q / d) Q L) := by
  have hforw : qPochhammer (a * q ^ N) q = qPochhammer a q / qPochhammerNat a q N := by
    rw [eq_div_iff ha, mul_comm]
    exact (qPochhammer_shift_nat a q N hq0 hq1).symm
  rw [hforw, backward_cleared d Q hd hQ0 hQ1 L]
  simp only [div_eq_mul_inv, mul_inv, ← zpow_natCast, ← zpow_neg, neg_neg]
  ring

lemma q_ratio_shift (a b c d q Q : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1)
    (N L : ℕ) (ha : qPochhammerNat a q N ≠ 0) (hb : qPochhammerNat b q N ≠ 0) :
    (qPochhammer (a * q ^ N) q / qPochhammer (d * Q ^ (-(L : ℤ))) Q) /
      (qPochhammer (b * q ^ N) q / qPochhammer (c * Q ^ (-(L : ℤ))) Q) =
      ((qPochhammer a q / qPochhammer d Q) / (qPochhammer b q / qPochhammer c Q)) *
        (c / d) ^ L *
        (qPochhammerNat b q N / qPochhammerNat a q N) *
        (qPochhammerNat (Q / c) Q L / qPochhammerNat (Q / d) Q L) := by
  rw [q_single_shift a d q Q hd hq0 hq1 hQ0 hQ1 N L ha,
    q_single_shift b c q Q hc hq0 hq1 hQ0 hQ1 N L hb]
  have hQ : Q ≠ 0 := norm_pos_iff.mp hQ0
  have hcoeff : ((-d) ^ (-(L : ℤ)) * Q ^ (L * (L + 1) / 2)) /
      ((-c) ^ (-(L : ℤ)) * Q ^ (L * (L + 1) / 2)) = (c / d) ^ L := by
    simp only [zpow_neg, zpow_natCast]
    rw [mul_div_mul_right _ _ (pow_ne_zero _ hQ), inv_div_inv, ← div_pow, neg_div_neg_eq]
  rw [show (c / d) ^ L = _ from hcoeff.symm]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

lemma analytic_eventually_ne_zero (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (u z : ℂ) (hu : f u ≠ 0) : ∀ᶠ v in 𝓝[≠] z, f v ≠ 0 := by
  have hm : MeromorphicOn f univ := fun v _ => (hf v (mem_univ v)).meromorphicAt
  have hnt : meromorphicOrderAt f u ≠ ⊤ := by
    rw [(hf u (mem_univ u)).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hu)]
    exact WithTop.zero_ne_top
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (hf z (mem_univ z)).meromorphicAt).mp
      (hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
        (mem_univ u) (mem_univ z) hnt)

lemma finite_exp_eventually_ne_zero (a b q z : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (N : ℕ) :
    ∀ᶠ u in 𝓝[≠] z, qPochhammerNat (a * e (b * u)) q N ≠ 0 := by
  have hq : q ≠ 0 := norm_pos_iff.mp hq0
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let u : ℂ := Complex.log (q / a) / ((2 * (Real.pi : ℂ) * Complex.I) * b)
  have hu : a * e (b * u) = q := by
    unfold e
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (b * u) = Complex.log (q / a) by
      dsimp [u]; field_simp]
    rw [Complex.exp_log (div_ne_zero hq ha)]
    field_simp
  apply analytic_eventually_ne_zero (fun v => qPochhammerNat (a * e (b * v)) q N) ?_ u z
  · rw [hu]
    exact qPochhammerNat_q_ne_zero q N hq0 hq1
  · intro v _
    unfold qPochhammerNat e
    fun_prop

lemma finite_ne_zero_of_norm_lt_one (a q : ℂ) (ha : ‖a‖ < 1)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (N : ℕ) : qPochhammerNat a q N ≠ 0 := by
  intro hzero
  have h := qPochhammer_ne_zero_of_norm_lt_one a q ha hq0 hq1
  rw [qPochhammer_shift_nat a q N hq0 hq1, hzero, zero_mul] at h
  exact h rfl

lemma tendsto_add_const_nhdsNE (a z : ℂ) :
    Tendsto (fun u : ℂ => u + a) (𝓝[≠] z) (𝓝[≠] (z + a)) := by
  apply ContinuousWithinAt.tendsto_nhdsWithin
    (show ContinuousAt (fun u : ℂ => u + a) z by fun_prop).continuousWithinAt
  intro u hu heq
  exact hu (add_right_cancel heq)

lemma dArg_ne_zero (M : SL(2, ℤ)) (n : ℤ) (τ z : ℂ) :
    UpperWindow.dArg M n τ z ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (e_ne_zero _)) (e_ne_zero _)

lemma cArg_ne_zero (M : SL(2, ℤ)) (n : ℤ) (τ y z : ℂ) :
    UpperWindow.cArg M n τ y z ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (e_ne_zero _)) (e_ne_zero _)

lemma cArg_div_dArg (M : SL(2, ℤ)) (n : ℤ) (τ y z : ℂ) :
    UpperWindow.cArg M n τ y z / UpperWindow.dArg M n τ z =
      e (y / etaDenom M τ) := by
  unfold UpperWindow.cArg UpperWindow.dArg
  rw [add_div, e_add']
  field_simp [e_ne_zero]

lemma continuous_finite (q : ℂ) (N : ℕ) : Continuous (fun a => qPochhammerNat a q N) := by
  unfold qPochhammerNat
  fun_prop

lemma continuous_aArg (m : ℤ) (τ : ℂ) : Continuous (UpperWindow.aArg m τ) := by
  unfold UpperWindow.aArg e
  fun_prop

lemma continuous_bArg (m p : ℤ) (τ y : ℂ) : Continuous (UpperWindow.bArg m p τ y) := by
  unfold UpperWindow.bArg e
  fun_prop

lemma continuous_dArg (M : SL(2, ℤ)) (n : ℤ) (τ : ℂ) :
    Continuous (UpperWindow.dArg M n τ) := by
  unfold UpperWindow.dArg e
  fun_prop

lemma continuous_cArg (M : SL(2, ℤ)) (n : ℤ) (τ y : ℂ) :
    Continuous (UpperWindow.cArg M n τ y) := by
  unfold UpperWindow.cArg e
  fun_prop

lemma continuous_dFinite (M : SL(2, ℤ)) (n : ℤ) (τ : ℂ) (N : ℕ) :
    Continuous (fun u => qPochhammerNat (e (etaMobius M τ) / UpperWindow.dArg M n τ u)
      (e (etaMobius M τ)) N) :=
  (continuous_finite _ N).comp
    (continuous_const.div (continuous_dArg M n τ) (dArg_ne_zero M n τ))

lemma continuous_cFinite (M : SL(2, ℤ)) (n : ℤ) (τ y : ℂ) (N : ℕ) :
    Continuous (fun u => qPochhammerNat (e (etaMobius M τ) / UpperWindow.cArg M n τ y u)
      (e (etaMobius M τ)) N) :=
  (continuous_finite _ N).comp
    (continuous_const.div (continuous_cArg M n τ y) (cArg_ne_zero M n τ y))

lemma kernel_continuousAt (kind : UpperContour.Kind) (M : SL(2, ℤ))
    (hM : 0 < M 1 0) (m n h ℓ p : ℤ) (x : UpperWindow.Parameters) (z : ℂ)
    (hn : (z, x.1) ∈ modularPhiNonvanishingDomain M (m + 1) n)
    (hd : (z + x.2.2, x.1) ∈ modularPhiNonvanishingDomain M (m + p) n) :
    ContinuousAt (UpperContour.kernel kind M m n h ℓ p x) z := by
  have hnum : ContinuousAt (fun u => modularPhi M (m + 1) n u x.1) z := by
    have hpair : AnalyticAt ℂ (fun u : ℂ => (u, x.1)) z :=
      analyticAt_id.prod analyticAt_const
    have hc := (modularPhi_joint_analytic_no_poles M hM (m + 1) n (z, x.1)
      ⟨hn.1, hn.2.1⟩).comp (x := z) hpair
    simpa only [Function.comp_def] using hc.continuousAt
  have hden : ContinuousAt (fun u => modularPhi M (m + p) n (u + x.2.2) x.1) z := by
    have hpair : AnalyticAt ℂ (fun u : ℂ => (u + x.2.2, x.1)) z :=
      (analyticAt_id.add analyticAt_const).prod analyticAt_const
    have hc := (modularPhi_joint_analytic_no_poles M hM (m + p) n (z + x.2.2, x.1)
      ⟨hd.1, hd.2.1⟩).comp (x := z) hpair
    simpa only [Function.comp_def] using hc.continuousAt
  have hne : modularPhi M (m + p) n (z + x.2.2) x.1 ≠ 0 :=
    (modularPhi_ne_zero_iff M hM (m + p) n _ _ hd.1 hd.2.1).mpr hd.2.2
  have hphase : ContinuousAt (fun u => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 u)) z := by
    unfold e UpperWindow.phase
    fun_prop
  cases kind with
  | single => exact hnum.mul hphase
  | ratio => exact (hnum.div hden hne).mul hphase

end SICLean.L4.UpperContourShiftsAux
