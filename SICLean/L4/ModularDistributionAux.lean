import SICLean.L4.ModularCocycle
import SICLean.L4.ModularDivisor

set_option autoImplicit false

/-! Auxiliary algebra and analytic continuation for the fixed doubling statements. -/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4.ModularDistributionAux

lemma odd_entries (M : SL(2, ℤ)) (hc : 2 ∣ M 1 0) :
    Odd (M 0 0) ∧ Odd (M 1 1) := by
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨k, hk⟩ := hc
  have heven : Even (M 0 1 * M 1 0) := ⟨M 0 1 * k, by rw [hk]; ring⟩
  have hodd : Odd (M 0 0 * M 1 1) := by
    convert heven.add_one using 1 <;> linarith
  exact Int.odd_mul.mp hodd

lemma e_half : e (1 / 2) = -1 := by
  unfold e
  convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring

lemma e_odd_half (k : ℤ) (hk : Odd k) : e ((k : ℂ) / 2) = -1 := by
  obtain ⟨r, hr⟩ := hk.exists_bit1
  rw [hr]
  push_cast
  rw [show ((2 : ℂ) * r + 1) / 2 = (r : ℂ) + 1 / 2 by ring,
    e_add', e_intCast, e_half, one_mul]

lemma half_mobius (M : SL(2, ℤ)) (hc : 2 ∣ M 1 0) (τ : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    ((M 1 0 / 2 : ℤ) : ℂ) * etaMobius M τ + 1 / (2 * etaDenom M τ) =
      (M 0 0 : ℂ) / 2 := by
  have hhalf : (2 : ℂ) * ((M 1 0 / 2 : ℤ) : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast Int.mul_ediv_cancel' hc
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) -
      (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by
    exact_mod_cast det_coe_int M
  unfold etaMobius
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
  field_simp [hT]
  simp only [etaDenom] at *
  linear_combination ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) * hhalf - hdet

lemma e_double (w : ℂ) : e (2 * w) = e w ^ 2 :=
  EtaMultiplierAux.exp_phase_two_mul w

lemma argument_double (m : ℤ) (z τ : ℂ) :
    ((e τ) ^ m * e z) ^ 2 = (e (2 * τ)) ^ m * e (2 * z) := by
  simp_rw [e_int_mul]
  rw [← e_add', pow_two, ← e_add', ← e_add']
  congr 1
  ring

lemma tendsto_affine_nhdsNE (a b z : ℂ) (ha : a ≠ 0) :
    Tendsto (fun w : ℂ => a * w + b) (𝓝[≠] z) (𝓝[≠] (a * z + b)) := by
  apply ContinuousWithinAt.tendsto_nhdsWithin
    (show ContinuousAt (fun w : ℂ => a * w + b) z by fun_prop).continuousWithinAt
  intro w hw heq
  exact hw (mul_left_cancel₀ ha (add_right_cancel heq))

lemma qPochhammer_neg_one_ne_zero (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer (-1) q ≠ 0 := by
  rw [qPochhammer_neg_one q hq0 hq1]
  exact mul_ne_zero (by norm_num) (qPochhammer_ne_zero_of_norm_lt_one (-q) q
    (by simpa only [norm_neg] using hq1) hq0 hq1)

lemma analyticAt_real_off_lattice (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ₀ : ℝ) (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (z : ℂ) (hz : z ∉ modularPhiPseudoLattice (τ₀ : ℂ)) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2) (z, (τ₀ : ℂ)) := by
  have hp := modularPhi_real_off_lattice M hM m n τ₀ (by simpa [etaDenom] using hT) z hz
  exact modularPhi_joint_analytic_no_poles M hM m n _ ⟨hp.1, hp.2.1⟩

lemma continuousAt_z_real_off_lattice (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ₀ : ℝ) (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (z : ℂ) (hz : z ∉ modularPhiPseudoLattice (τ₀ : ℂ)) :
    ContinuousAt (fun w : ℂ => modularPhi M m n w (τ₀ : ℂ)) z := by
  have hemb : ContinuousAt (fun w : ℂ => (w, (τ₀ : ℂ))) z :=
    continuousAt_id.prodMk continuousAt_const
  have h := (analyticAt_real_off_lattice M hM m n τ₀ hT z hz).continuousAt.comp
    (f := fun w : ℂ => (w, (τ₀ : ℂ))) hemb
  exact h

lemma half_not_mem_pseudoLattice (τ₀ : ℝ) (hτ₀ : Irrational τ₀) :
    (1 / 2 : ℂ) ∉ modularPhiPseudoLattice (τ₀ : ℂ) := by
  rintro ⟨k, l, h⟩
  have hr := congrArg Complex.re h
  norm_num at hr
  by_cases hk : k = 0
  · subst k
    have hl : (2 : ℝ) * (l : ℝ) = 1 := by norm_num at hr; linarith
    have hlZ : (2 : ℤ) * l = 1 := by exact_mod_cast hl
    omega
  · apply hτ₀.ne_rational (1 - 2 * l) (2 * k)
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hk))).mpr
    linarith

/-- Equality above the real axis determines continuous actual center values. -/
lemma eq_at_real_of_upper (f g : ℂ → ℂ) (τ₀ : ℝ)
    (hf : ContinuousAt f (τ₀ : ℂ)) (hg : ContinuousAt g (τ₀ : ℂ))
    (hu : ∀ τ : ℂ, 0 < τ.im → f τ = g τ) : f (τ₀ : ℂ) = g (τ₀ : ℂ) := by
  have hcl : (τ₀ : ℂ) ∈ closure {τ : ℂ | 0 < τ.im} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(τ₀ : ℂ) + (ε / 2 : ℝ) * Complex.I, ?_, ?_⟩
    · simpa using half_pos hε
    · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hε), Complex.norm_I, mul_one]
      exact half_lt_self hε
  exact tendsto_nhds_unique_of_frequently_eq hf hg
    ((mem_closure_iff_frequently.mp hcl).mono hu)

lemma chart_cover (M : SL(2, ℤ)) (m n : ℤ) (p : ℂ × ℂ)
    (hp : p.2 ∈ modularPhiDomain M) :
    ∃ κ : ℕ → ℤ, p ∈ modularPhiChartDomain M m n κ := by
  refine ⟨fun j => continuationIndex (modularPhiFactorPoint M m n j p.1 p.2).1
    (modularPhiFactorPoint M m n j p.1 p.2).2, hp, ?_⟩
  intro j hj
  exact shiftedArgument_inStrip _ _ (modularPhi_sqrt_admissible M p.2 hp).1

lemma chart_den_eventually (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (κ : ℕ → ℤ) (p : ℂ × ℂ)
    (hp : p ∈ modularPhiChartDomain M m n κ) :
    ∀ᶠ w in 𝓝[≠] p.1, modularPhiChartDenominator M m n κ w p.2 ≠ 0 := by
  have hemb : AnalyticAt ℂ (fun w : ℂ => (w, p.2)) p.1 := by fun_prop
  have han : AnalyticAt ℂ (fun w : ℂ => modularPhiChartDenominator M m n κ w p.2) p.1 := by
    have h := ((modularPhiChart_analytic M hM m n κ).2 p hp).comp (x := p.1) hemb
    exact h
  exact ModularCocycleContinuationAux.analytic_eventually_ne_zero han
    (modularPhiChartDenominator_frequently_ne_zero M hM m n κ p hp)

/-- Continue a doubling law from the upper half-plane through the whole
common slit domain. Only compatible analytic quotients are continued. -/
lemma chart_cross_mul_of_upper (M N : SL(2, ℤ)) (hM : 0 < M 1 0) (hN : 0 < N 1 0)
    (m n n₂ : ℤ)
    (hdom : ∀ τ : ℂ, 2 * τ ∈ modularPhiDomain N ↔ τ ∈ modularPhiDomain M)
    (hupper : ∀ z τ : ℂ, 0 < τ.im →
      (fun w => modularPhi M m n w τ * modularPhi M m n₂ (w + 1 / 2) τ)
        =ᶠ[𝓝[≠] z] (fun w => modularPhi N m n (2 * w) (2 * τ)))
    (κ₁ κ₂ κJ : ℕ → ℤ) (z₀ τ₀ : ℂ)
    (h₁ : (z₀, τ₀) ∈ modularPhiChartDomain M m n κ₁)
    (h₂ : (z₀ + 1 / 2, τ₀) ∈ modularPhiChartDomain M m n₂ κ₂)
    (hJ : (2 * z₀, 2 * τ₀) ∈ modularPhiChartDomain N m n κJ) :
    modularPhiChartNumerator M m n κ₁ z₀ τ₀ *
        modularPhiChartNumerator M m n₂ κ₂ (z₀ + 1 / 2) τ₀ *
        modularPhiChartDenominator N m n κJ (2 * z₀) (2 * τ₀) =
      modularPhiChartNumerator N m n κJ (2 * z₀) (2 * τ₀) *
        modularPhiChartDenominator M m n κ₁ z₀ τ₀ *
        modularPhiChartDenominator M m n₂ κ₂ (z₀ + 1 / 2) τ₀ := by
  let ι := (ℕ → ℤ) × (ℕ → ℤ) × (ℕ → ℤ)
  let dbl : ℂ × ℂ → ℂ × ℂ := fun p => (2 * p.1, 2 * p.2)
  let sh : ℂ × ℂ → ℂ × ℂ := fun p => (p.1 + 1 / 2, p.2)
  have hdbl : ∀ p, AnalyticAt ℂ dbl p := fun p =>
    (analyticAt_const.mul analyticAt_fst).prod (analyticAt_const.mul analyticAt_snd)
  have hsh : ∀ p, AnalyticAt ℂ sh p := fun p =>
    (analyticAt_fst.add analyticAt_const).prod analyticAt_snd
  let Ω : Set (ℂ × ℂ) := Set.univ ×ˢ modularPhiDomain M
  let U : ι → Set (ℂ × ℂ) := fun i =>
    {p | dbl p ∈ modularPhiChartDomain N m n i.1 ∧
      p ∈ modularPhiChartDomain M m n i.2.1 ∧
      sh p ∈ modularPhiChartDomain M m n₂ i.2.2}
  let a : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiChartNumerator N m n i.1 (dbl p).1 (dbl p).2
  let b : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiChartNumerator M m n i.2.1 p.1 p.2
  let c : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiChartNumerator M m n₂ i.2.2 (sh p).1 (sh p).2
  let x : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiChartDenominator N m n i.1 (dbl p).1 (dbl p).2
  let y : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiChartDenominator M m n i.2.1 p.1 p.2
  let z : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiChartDenominator M m n₂ i.2.2 (sh p).1 (sh p).2
  have hΩ : IsPreconnected Ω := isPreconnected_univ.prod
    (ModularCocycleAux.modularPhiDomain_isPreconnected M hM.ne')
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    exact ((modularPhiChartDomain_isOpen N m n i.1).preimage (by dsimp [dbl]; fun_prop)).inter
      ((modularPhiChartDomain_isOpen M m n i.2.1).inter
        ((modularPhiChartDomain_isOpen M m n₂ i.2.2).preimage (by dsimp [sh]; fun_prop)))
  have hsub : ∀ i, U i ⊆ Ω := fun _ _ hp => ⟨Set.mem_univ _, hp.2.1.1⟩
  have hcover : ∀ p ∈ Ω, ∃ i, p ∈ U i := by
    intro p hp
    obtain ⟨iJ, hiJ⟩ := chart_cover N m n (dbl p) ((hdom p.2).mpr hp.2)
    obtain ⟨i₁, hi₁⟩ := chart_cover M m n p hp.2
    obtain ⟨i₂, hi₂⟩ := chart_cover M m n₂ (sh p) hp.2
    exact ⟨(iJ, i₁, i₂), hiJ, hi₁, hi₂⟩
  have ha : ∀ i, AnalyticOnNhd ℂ (a i) (U i) := fun i p hp =>
    ((modularPhiChart_analytic N hN m n i.1).1 (dbl p) hp.1).comp (hdbl p)
  have hb : ∀ i, AnalyticOnNhd ℂ (b i) (U i) := fun i p hp =>
    (modularPhiChart_analytic M hM m n i.2.1).1 p hp.2.1
  have hc : ∀ i, AnalyticOnNhd ℂ (c i) (U i) := fun i p hp =>
    ((modularPhiChart_analytic M hM m n₂ i.2.2).1 (sh p) hp.2.2).comp (hsh p)
  have hx : ∀ i, AnalyticOnNhd ℂ (x i) (U i) := fun i p hp =>
    ((modularPhiChart_analytic N hN m n i.1).2 (dbl p) hp.1).comp (hdbl p)
  have hy : ∀ i, AnalyticOnNhd ℂ (y i) (U i) := fun i p hp =>
    (modularPhiChart_analytic M hM m n i.2.1).2 p hp.2.1
  have hz : ∀ i, AnalyticOnNhd ℂ (z i) (U i) := fun i p hp =>
    ((modularPhiChart_analytic M hM m n₂ i.2.2).2 (sh p) hp.2.2).comp (hsh p)
  have hne : ∀ i p, p ∈ U i → ∀ᶠ w in 𝓝[≠] p.1,
      x i (w, p.2) ≠ 0 ∧ y i (w, p.2) ≠ 0 ∧ z i (w, p.2) ≠ 0 := by
    intro i p hp
    have htJ : Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] p.1) (𝓝[≠] (dbl p).1) := by
      simpa [dbl] using tendsto_affine_nhdsNE 2 0 p.1 (by norm_num)
    have ht₂ : Tendsto (fun w : ℂ => w + 1 / 2) (𝓝[≠] p.1) (𝓝[≠] (sh p).1) := by
      simpa [sh] using tendsto_affine_nhdsNE 1 (1 / 2) p.1 one_ne_zero
    have hJ' := htJ.eventually (chart_den_eventually N hN m n i.1 (dbl p) hp.1)
    have h₁' := chart_den_eventually M hM m n i.2.1 p hp.2.1
    have h₂' := ht₂.eventually (chart_den_eventually M hM m n₂ i.2.2 (sh p) hp.2.2)
    filter_upwards [hJ', h₁', h₂'] with w hwJ hw₁ hw₂
    exact ⟨hwJ, hw₁, hw₂⟩
  have hcompat : ∀ i j p, p ∈ U i → p ∈ U j →
      a i p * x j p = a j p * x i p ∧
      b i p * y j p = b j p * y i p ∧
      c i p * z j p = c j p * z i p := by
    intro i j p hi hj
    exact ⟨modularPhiChart_overlap_cross_mul N hN m n i.1 j.1 (dbl p) hi.1 hj.1,
      modularPhiChart_overlap_cross_mul M hM m n i.2.1 j.2.1 p hi.2.1 hj.2.1,
      modularPhiChart_overlap_cross_mul M hM m n₂ i.2.2 j.2.2 (sh p) hi.2.2 hj.2.2⟩
  have hcross : ∀ i p, p ∈ U i → 0 < p.2.im →
      a i p * y i p * z i p = b i p * c i p * x i p := by
    intro i p hp hpu
    have hemb : ContinuousAt (fun w : ℂ => (w, p.2)) p.1 :=
      continuousAt_id.prodMk continuousAt_const
    have hslice {F : (ℂ × ℂ) → ℂ} (hF : ContinuousAt F p) :
        ContinuousAt (fun w => F (w, p.2)) p.1 := by
      have h := hF.comp (f := fun w : ℂ => (w, p.2)) hemb
      exact h
    apply ModularCocycleContinuationAux.cross_mul_of_quotient_germ
      (fun w => a i (w, p.2)) (fun w => b i (w, p.2)) (fun w => c i (w, p.2))
      (fun w => x i (w, p.2)) (fun w => y i (w, p.2)) (fun w => z i (w, p.2)) p.1
      (hslice (ha i p hp).continuousAt) (hslice (hb i p hp).continuousAt)
      (hslice (hc i p hp).continuousAt) (hslice (hx i p hp).continuousAt)
      (hslice (hy i p hp).continuousAt) (hslice (hz i p hp).continuousAt)
      (hne i p hp)
    have hloc : ∀ᶠ w in 𝓝 p.1, (w, p.2) ∈ U i :=
      hemb.tendsto.eventually ((hU i).mem_nhds hp)
    filter_upwards [hupper p.1 p.2 hpu, hloc.filter_mono nhdsWithin_le_nhds] with w hw hwi
    rw [modularPhi_eq_chart M hM m n i.2.1 (w, p.2) hwi.2.1,
      modularPhi_eq_chart M hM m n₂ i.2.2 (sh (w, p.2)) hwi.2.2,
      modularPhi_eq_chart N hN m n i.1 (dbl (w, p.2)) hwi.1] at hw
    exact hw.symm
  obtain ⟨i₀, hi₀⟩ := hcover (0, Complex.I)
    ⟨Set.mem_univ _, upper_mem_modularPhiDomain M hM UpperHalfPlane.I⟩
  have hzero : (fun p => a i₀ p * y i₀ p * z i₀ p - b i₀ p * c i₀ p * x i₀ p)
      =ᶠ[𝓝 (0, Complex.I)] 0 := by
    have hu : IsOpen {p : ℂ × ℂ | 0 < p.2.im} :=
      isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd)
    filter_upwards [(hU i₀).mem_nhds hi₀, hu.mem_nhds (by norm_num)] with p hp hpu
    exact sub_eq_zero.mpr (hcross i₀ p hp hpu)
  exact (ModularCocycleContinuationAux.cocycle_atlas_identity Ω U a b c x y z hΩ hU hsub hcover
    ha hb hc hx hy hz hne hcompat i₀ (0, Complex.I) hi₀ hzero
      (κJ, κ₁, κ₂) (z₀, τ₀) ⟨hJ, h₁, h₂⟩).symm

end SICLean.L4.ModularDistributionAux
