import SICLean.L4.UpperContourBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false

/-! Auxiliary q-product bounds and finite rotation lemmas. -/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContourUpperArcAux
open SICLean.L4.UpperContour

theorem wedge_q_bound (η r qR : ℝ) (hη : 0 < η) (hr : r < 1) (hqR : qR < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ u q : ℂ, ‖u‖ ≤ r → η ≤ ‖q‖ → ‖q‖ ≤ qR →
      ‖qPochhammer u q‖ ≤ B ∧ ‖(qPochhammer u q)⁻¹‖ ≤ B := by
  let S : Set (ℂ × ℂ) := Metric.closedBall (0 : ℂ) r ×ˢ
    (Metric.closedBall (0 : ℂ) qR ∩ {q : ℂ | η ≤ ‖q‖})
  have hS : IsCompact S :=
    (isCompact_closedBall (0 : ℂ) r).prod
      ((isCompact_closedBall (0 : ℂ) qR).inter_right
        (isClosed_le continuous_const continuous_norm))
  have hs (a : ℂ × ℂ) (ha : a ∈ S) :
      ‖a.1‖ < 1 ∧ 0 < ‖a.2‖ ∧ ‖a.2‖ < 1 := by
    simp only [S, Set.mem_prod, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Metric.mem_closedBall, dist_zero_right] at ha
    exact ⟨ha.1.trans_lt hr, hη.trans_le ha.2.2, ha.2.1.trans_lt hqR⟩
  have hc : ContinuousOn (fun a : ℂ × ℂ => qPochhammer a.1 a.2) S := by
    intro a ha
    exact (analyticOnNhd_qPochhammer_joint a (hs a ha).2).continuousAt.continuousWithinAt
  have hz (a : ℂ × ℂ) (ha : a ∈ S) : qPochhammer a.1 a.2 ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one a.1 a.2 (hs a ha).1 (hs a ha).2.1 (hs a ha).2.2
  obtain ⟨B₁, hB₁⟩ := hS.exists_bound_of_continuousOn hc
  obtain ⟨B₂, hB₂⟩ := hS.exists_bound_of_continuousOn (hc.inv₀ hz)
  refine ⟨max 1 (max B₁ B₂), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u q hu hq0 hq1
  have hmem : (u,q) ∈ S := by
    simpa only [S, Set.mem_prod, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Metric.mem_closedBall, dist_zero_right] using And.intro hu (And.intro hq1 hq0)
  exact ⟨(hB₁ (u,q) hmem).trans ((le_max_left B₁ B₂).trans (le_max_right 1 _)),
    (hB₂ (u,q) hmem).trans ((le_max_right B₁ B₂).trans (le_max_right 1 _))⟩

theorem wedge_phi_bound_of_q_bounds (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) (B : ℝ) (hB : 0 < B)
    (_q0 : 0 < ‖e τ‖) (_q1 : ‖e τ‖ < 1)
    (Q0 : 0 < ‖e (etaMobius M τ)‖) (Q1 : ‖e (etaMobius M τ)‖ < 1)
    (r : ℝ) (hr : r < 1)
    (hb : ∀ u q : ℂ, ‖u‖ ≤ r → (q = e τ ∨ q = e (etaMobius M τ)) →
      ‖qPochhammer u q‖ ≤ B ∧ ‖(qPochhammer u q)⁻¹‖ ≤ B)
    (m n : ℤ) (z : ℂ)
    (ha : ‖(e τ) ^ m * e z‖ ≤ r)
    (hd : ‖(e (etaMobius M τ)) ^ n * e (z / etaDenom M τ)‖ ≤ r) :
    ‖modularPhi M m n z τ‖ ≤ B * B ∧ ‖(modularPhi M m n z τ)⁻¹‖ ≤ B * B := by
  have hd0 : modularPhiQDenominator M n z τ ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one _ _ (hd.trans_lt hr) Q0 Q1
  rw [modularPhi_eq_qProduct M hM m n z τ hτ hd0,
    modularPhiQProduct, modularPhiQNumerator, modularPhiQDenominator]
  have hbA := hb ((e τ) ^ m * e z) (e τ) ha (Or.inl rfl)
  have hbD := hb ((e (etaMobius M τ)) ^ n * e (z / etaDenom M τ))
    (e (etaMobius M τ)) hd (Or.inr rfl)
  constructor
  · rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul hbA.1 hbD.2 (norm_nonneg _) hB.le
  · rw [div_eq_mul_inv, mul_inv, norm_mul]
    exact mul_le_mul hbA.2 (by simpa using hbD.1) (norm_nonneg _) hB.le

theorem wedge_compact_upper_phi_bounds (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ r : ℝ, 0 ≤ r → ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      let z := UpperContour.arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ
      ‖modularPhi M ((m : ℤ) + 1) n z x.1‖ ≤ C ∧
        ‖(modularPhi M ((m : ℤ) + 1) n z x.1)⁻¹‖ ≤ C ∧
        ‖modularPhi M ((m : ℤ) + p) n (z + x.2.2) x.1‖ ≤ C ∧
        ‖(modularPhi M ((m : ℤ) + p) n (z + x.2.2) x.1)⁻¹‖ ≤ C := by
  obtain ⟨η, R, qR, hη, hR, hqR0, hqR1, hparams⟩ :=
    UpperWindow.compact_parameter_bounds M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨uR, huR0, huR1, hargs⟩ :=
    UpperWindow.compact_upper_arguments M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨B, hB, hb⟩ := wedge_q_bound η uR qR hη huR1 hqR1
  refine ⟨B * B, mul_pos hB hB, ?_⟩
  intro x hx m hm r hr θ hθ
  rcases hparams x hx with ⟨hτ, hTim, harg0, harg1, hT0, hT1, hq0, hq1, hQ0, hQ1, hw, hy⟩
  rcases hargs x hx m hm r hr θ hθ with ⟨ha, hb', hd, hcc⟩
  have hbX : ∀ u q : ℂ, ‖u‖ ≤ uR → (q = e x.1 ∨ q = e (etaMobius M x.1)) →
      ‖qPochhammer u q‖ ≤ B ∧ ‖(qPochhammer u q)⁻¹‖ ≤ B := by
    intro u q hu hq
    rcases hq with rfl | rfl
    · exact hb u _ hu hq0 hq1
    · exact hb u _ hu hQ0 hQ1
  have hphi := wedge_phi_bound_of_q_bounds M hc.1 x.1 (hη.trans_le hτ) B hB
    (hη.trans_le hq0) (hq1.trans_lt hqR1) (hη.trans_le hQ0) (hQ1.trans_lt hqR1)
    uR huR1 hbX
  exact ⟨(hphi ((m : ℤ) + 1) n _ ha hd).1,
    (hphi ((m : ℤ) + 1) n _ ha hd).2,
    (hphi ((m : ℤ) + p) n _ hb' hcc).1,
    (hphi ((m : ℤ) + p) n _ hb' hcc).2⟩

theorem finite_wedge_of_differentiable
    (f : ℂ → ℂ) (v : ℂ) (a b r : ℝ) (hab : a ≤ b) (hr : 0 ≤ r)
    (hf : ∀ θ ∈ Icc a b, ∀ t ∈ Icc 0 r,
      DifferentiableAt ℂ f (v + (t : ℂ) * UpperWindow.rotation θ)) :
    rayFinite f v (UpperWindow.rotation a) r + arcIntegral f v r a b -
      rayFinite f v (UpperWindow.rotation b) r = 0 := by
  let L₁ : ℝ × ℝ →L[ℝ] ℂ :=
    Complex.ofRealCLM ∘L ContinuousLinearMap.fst ℝ ℝ ℝ
  let L₂ : ℝ × ℝ →L[ℝ] ℂ :=
    Complex.ofRealCLM ∘L ContinuousLinearMap.snd ℝ ℝ ℝ
  let ρ : ℝ × ℝ → ℂ := fun p => UpperWindow.rotation p.1
  let H : ℝ × ℝ → ℂ := fun p => v + (p.2 : ℂ) * ρ p
  let dρ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => (I * ρ p) • L₁
  let dH : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    ρ p • L₂ + (I * (p.2 : ℂ) * ρ p) • L₁
  have hρ (p : ℝ × ℝ) : HasFDerivAt ρ (dρ p) p := by
    simpa [ρ, UpperWindow.rotation, dρ, L₁, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using
      ((L₁.hasFDerivAt (x := p)).const_mul I).cexp
  have hH (p : ℝ × ℝ) : HasFDerivAt H (dH p) p := by
    have hz : HasFDerivAt (fun p : ℝ × ℝ => (p.2 : ℂ)) L₂ p :=
      L₂.hasFDerivAt
    apply (hz.mul (hρ p)).const_add v |>.congr_fderiv
    apply ContinuousLinearMap.ext
    intro q
    simp [dH, dρ, L₁, L₂, ρ, smul_eq_mul]
    ring
  let df : ℝ × ℝ → ℂ := fun p => deriv f (H p)
  let A : ℝ × ℝ → ℂ := fun p => f (H p) * ρ p
  let G : ℝ × ℝ → ℂ := fun p => -(f (H p) * (I * (p.2 : ℂ) * ρ p))
  let dA : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    f (H p) • dρ p + ρ p • (df p • dH p)
  let dJ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    (I * ρ p) • L₂ + (-(p.2 : ℂ) * ρ p) • L₁
  let dG : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    -(f (H p) • dJ p + (I * (p.2 : ℂ) * ρ p) • (df p • dH p))
  have hJ (p : ℝ × ℝ) :
      HasFDerivAt (fun p : ℝ × ℝ => I * (p.2 : ℂ) * ρ p) (dJ p) p := by
    apply ((L₂.hasFDerivAt (x := p)).const_mul I |>.mul (hρ p)).congr_fderiv
    apply ContinuousLinearMap.ext
    intro q
    simp [dJ, dρ, L₁, L₂, smul_eq_mul]
    ring_nf
    simp
    ring
  have hfp (p : ℝ × ℝ) (hp : p ∈ Icc ((a : ℝ), 0) ((b : ℝ), r)) :
      DifferentiableAt ℂ f (H p) :=
    hf p.1 ⟨hp.1.1, hp.2.1⟩ p.2 ⟨hp.1.2, hp.2.2⟩
  have hfc : ContinuousOn (fun p => f (H p)) (Icc ((a : ℝ), 0) ((b : ℝ), r)) := by
    intro p hp
    exact ((hfp p hp).continuousAt.comp (hH p).continuousAt).continuousWithinAt
  have hAc : ContinuousOn A (Icc ((a : ℝ), 0) ((b : ℝ), r)) :=
    hfc.mul (fun p _ => (hρ p).continuousAt.continuousWithinAt)
  have hGc : ContinuousOn G (Icc ((a : ℝ), 0) ((b : ℝ), r)) :=
    (hfc.mul (fun p _ => (hJ p).continuousAt.continuousWithinAt)).neg
  have hderiv (p : ℝ × ℝ) (hp : p ∈ Icc ((a : ℝ), 0) ((b : ℝ), r)) :
      HasFDerivAt (fun p => f (H p)) (df p • dH p) p :=
    (hfp p hp).hasDerivAt.comp_hasFDerivAt p (hH p)
  have hAd (p : ℝ × ℝ) (hp : p ∈ Ioo a b ×ˢ Ioo 0 r) :
      HasFDerivAt A (dA p) p := by
    exact (hderiv p ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩).mul (hρ p)
  have hGd (p : ℝ × ℝ) (hp : p ∈ Ioo a b ×ˢ Ioo 0 r) :
      HasFDerivAt G (dG p) p := by
    exact ((hderiv p ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩).mul (hJ p)).neg
  have hzero (p : ℝ × ℝ) : dA p (1, 0) + dG p (0, 1) = 0 := by
    simp [dA, dG, dρ, dH, dJ, L₁, L₂, smul_eq_mul]
    ring
  have hi : IntegrableOn (fun p => dA p (1, 0) + dG p (0, 1))
      (Icc ((a : ℝ), 0) ((b : ℝ), r)) := by
    simp_rw [hzero]
    exact integrableOn_zero
  have hgreen := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    A G dA dG ((a : ℝ), 0) ((b : ℝ), r) ⟨hab, hr⟩
    hAc hGc hAd hGd hi
  simp only [hzero, integral_zero, A, G, H, ρ, ofReal_zero, mul_zero, zero_mul,
    add_zero, neg_zero, intervalIntegral.integral_zero, sub_zero,
    intervalIntegral.integral_neg] at hgreen
  change (∫ t in 0..r, f (v + (t : ℂ) * UpperWindow.rotation a) *
      UpperWindow.rotation a) +
    (∫ θ in a..b, f (v + (r : ℂ) * UpperWindow.rotation θ) *
      (I * (r : ℂ) * UpperWindow.rotation θ)) -
    (∫ t in 0..r, f (v + (t : ℂ) * UpperWindow.rotation b) *
      UpperWindow.rotation b) = 0
  linear_combination hgreen

theorem kernel_analyticAt (kind : Kind) (M : SL(2, ℤ))
    (hM : 0 < M 1 0) (h ℓ p m n : ℤ) (x : UpperWindow.Parameters) (z : ℂ)
    (hnum : (z, x.1) ∈ modularPhiNonvanishingDomain M (m + 1) n)
    (hden : (z + x.2.2, x.1) ∈ modularPhiNonvanishingDomain M (m + p) n) :
    AnalyticAt ℂ (UpperContour.kernel kind M m n h ℓ p x) z := by
  have hN : AnalyticAt ℂ (fun w : ℂ => modularPhi M (m + 1) n w x.1) z := by
    have hA := modularPhi_joint_analytic_no_poles M hM (m + 1) n
      (z, x.1) ⟨hnum.1, hnum.2.1⟩
    have hP : AnalyticAt ℂ (fun w : ℂ => (w, x.1)) z :=
      analyticAt_id.prod analyticAt_const
    simpa [Function.comp_def] using hA.comp (x := z) hP
  have hD : AnalyticAt ℂ (fun w : ℂ => modularPhi M (m + p) n (w + x.2.2) x.1) z := by
    have hA := modularPhi_joint_analytic_no_poles M hM (m + p) n
      (z + x.2.2, x.1) ⟨hden.1, hden.2.1⟩
    have hP : AnalyticAt ℂ (fun w : ℂ => (w + x.2.2, x.1)) z :=
      (analyticAt_id.add analyticAt_const).prod analyticAt_const
    simpa [Function.comp_def] using hA.comp (x := z) hP
  have hDne : modularPhi M (m + p) n (z + x.2.2) x.1 ≠ 0 :=
    (modularPhi_ne_zero_iff M hM (m + p) n (z + x.2.2) x.1
      hden.1 hden.2.1).mpr hden.2.2
  have hphase : AnalyticAt ℂ (fun w : ℂ => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 w)) z := by
    unfold UpperWindow.phase e
    fun_prop
  cases kind with
  | single => exact hN.mul hphase
  | ratio => exact (hN.div hD hDne).mul hphase

theorem kernel_sector_differentiable (kind : Kind) (M : SL(2, ℤ))
    (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (x : UpperWindow.Parameters) (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ)
    (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ) ∨
      θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    DifferentiableAt ℂ (UpperContour.kernel kind M m n h ℓ p x)
      (UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ) := by
  obtain ⟨hnum, hden⟩ := UpperWindow.sector_divisor_free M h ℓ p m n
    ψ σ ρ δ hc x hx r θ hr hθ
  exact (kernel_analyticAt kind M hc.1 h ℓ p m n x
    (UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ) hnum hden).differentiableAt

theorem finite_upper_rotation (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r : ℝ) (hr : 0 ≤ r) :
    let f := UpperContour.kernel kind M m n h ℓ p x
    let v := UpperWindow.base M m n δ x.1
    rayFinite f v (UpperWindow.rotation (etaDenom M x.1).arg) r +
      arcIntegral f v r (etaDenom M x.1).arg (Real.pi / 2 + ψ) -
      rayFinite f v (UpperWindow.rotation (Real.pi / 2 + ψ)) r = 0 := by
  apply finite_wedge_of_differentiable _ _ _ _ _ (by
    have hlt := hx.1.2.2
    linarith [Real.pi_pos]) hr
  intro θ hθ t ht
  exact kernel_sector_differentiable kind M h ℓ p m n ψ σ ρ δ
    hc x hx t θ ht.1 (Or.inl hθ)

lemma ray_integrable_of_exp_bound
    (f : ℂ → ℂ) (v : ℂ) (θ C k : ℝ) (hk : 0 < k)
    (hcont : ∀ t : ℝ, 0 ≤ t →
      ContinuousAt f (v + (t : ℂ) * UpperWindow.rotation θ))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ‖f (v + (t : ℂ) * UpperWindow.rotation θ)‖ ≤
        C * Real.exp (-k * t)) :
    IntegrableOn (rayPullback f v (UpperWindow.rotation θ)) (Ioi 0) := by
  have hg : ContinuousOn
      (rayPullback f v (UpperWindow.rotation θ)) (Ioi 0) := by
    intro t ht
    have hp : ContinuousAt
        (fun s : ℝ => v + (s : ℂ) * UpperWindow.rotation θ) t := by
      fun_prop
    exact (((hcont t ht.le).comp
      (f := fun s : ℝ => v + (s : ℂ) * UpperWindow.rotation θ)
      (x := t) hp).mul_const _).continuousWithinAt
  have hmajor : IntegrableOn
      (fun t : ℝ => C * Real.exp (-k * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) 0).const_mul C
  refine hmajor.mono' (hg.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa [rayPullback, UpperWindow.rotation, Complex.norm_exp] using hbound t ht.le

lemma rayFinite_tendsto (f : ℂ → ℂ) (v d : ℂ)
    (hf : IntegrableOn (rayPullback f v d) (Ioi 0)) :
    Tendsto (rayFinite f v d) atTop (𝓝 (rayIntegral f v d)) := by
  change Tendsto (fun r : ℝ => ∫ t : ℝ in 0..r, rayPullback f v d t) atTop
    (𝓝 (∫ t : ℝ in Ioi 0, rayPullback f v d t))
  exact intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id

lemma arcIntegral_tendsto_zero_of_exp_bound
    (f : ℂ → ℂ) (v : ℂ) (a b C k : ℝ) (hab : a ≤ b) (hk : 0 < k)
    (hbound : ∀ r : ℝ, 0 ≤ r → ∀ θ ∈ Icc a b,
      ‖f (UpperContour.arcPoint v r θ)‖ ≤ C * Real.exp (-k * r)) :
    Tendsto (fun r : ℝ => arcIntegral f v r a b) atTop (𝓝 0) := by
  have hlim : Tendsto (fun r : ℝ => r * Real.exp (-k * r)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 k hk
  apply squeeze_zero_norm' (a := fun r : ℝ => (C * (b - a)) *
    (r * Real.exp (-k * r))) ?_
    (by simpa using hlim.const_mul (C * (b - a)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := arcPullback f v r) (a := a) (b := b)
    (C := r * (C * Real.exp (-k * r))) (fun θ hθ => by
      rw [uIoc_of_le hab] at hθ
      have heq : ‖arcPullback f v r θ‖ = r * ‖f (UpperContour.arcPoint v r θ)‖ := by
        simp [arcPullback, UpperWindow.rotation, Complex.norm_exp,
          abs_of_nonneg hr, mul_comm]
      rw [heq]
      exact mul_le_mul_of_nonneg_left (hbound r hr θ ⟨hθ.1.le, hθ.2⟩) hr)
  simpa only [arcIntegral, abs_of_nonneg (sub_nonneg.mpr hab),
    mul_assoc, mul_comm, mul_left_comm] using hb

theorem wedge_norm_e (z : ℂ) : ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  rw [e, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem wedge_norm_qarg_add_le (A z u : ℂ) (hu : 0 ≤ u.im) :
    ‖A * e (z + u)‖ ≤ ‖A * e z‖ := by
  rw [e_add', ← mul_assoc, norm_mul]
  have hnorm : ‖e u‖ ≤ 1 := by
    rw [wedge_norm_e, Real.exp_le_one_iff]
    have := Real.pi_pos
    nlinarith
  exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans_eq (mul_one _)

theorem wedge_compact_upper_arguments_all_int (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ x ∈ K, ∀ m : ℤ,
      ∀ r : ℝ, 0 ≤ r → ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
      ‖UpperWindow.aArg m x.1 z‖ ≤ R ∧
      ‖UpperWindow.bArg m p x.1 x.2.2 z‖ ≤ R ∧
      ‖UpperWindow.dArg M n x.1 z‖ ≤ R ∧
      ‖UpperWindow.cArg M n x.1 x.2.2 z‖ ≤ R := by
  obtain ⟨R, hR0, hR1, hv⟩ :=
    UpperWindow.compact_vertex_margin M h ℓ p n ψ σ ρ δ hc K hK hKU
  refine ⟨R, hR0, hR1, ?_⟩
  intro x hx m r hr θ hθ
  have hm0 : 0 ∈ Finset.range (M 1 0).toNat := by
    have hMc := hc.1
    simp only [Finset.mem_range]
    omega
  rcases hv x hx 0 hm0 with ⟨ha0, hb0, hd0, hc0, _⟩
  rcases UpperWindow.vertex_moduli M h ℓ p m n ψ σ ρ δ hc x (hKU hx) with
    ⟨ham, hbm, hdm, hcm⟩
  rcases UpperWindow.vertex_moduli M h ℓ p 0 n ψ σ ρ δ hc x (hKU hx) with
    ⟨haeq0, hbeq0, hdeq0, hceq0⟩
  have haV : ‖UpperWindow.aArg m x.1 (UpperWindow.base M m n δ x.1)‖ ≤ R := by
    rw [ham, ← haeq0]
    exact ha0
  have hbV : ‖UpperWindow.bArg m p x.1 x.2.2 (UpperWindow.base M m n δ x.1)‖ ≤ R := by
    rw [hbm, ← hbeq0]
    exact hb0
  have hdV : ‖UpperWindow.dArg M n x.1 (UpperWindow.base M m n δ x.1)‖ ≤ R := by
    rw [hdm, ← hdeq0]
    exact hd0
  have hcV : ‖UpperWindow.cArg M n x.1 x.2.2 (UpperWindow.base M m n δ x.1)‖ ≤ R := by
    rw [hcm, ← hceq0]
    exact hc0
  have hτ := (hKU hx).1
  rcases UpperWindow.upper_direction_im_nonneg (etaDenom M x.1) ψ θ
    hτ.2.1 hτ.2.2 hc.2.2.1 hθ with ⟨hdi, hdTi⟩
  have hui : 0 ≤ ((r : ℂ) * UpperWindow.rotation θ).im := by
    simpa [Complex.mul_im] using mul_nonneg hr hdi
  have huti : 0 ≤ (((r : ℂ) * UpperWindow.rotation θ) / etaDenom M x.1).im := by
    rw [mul_div_assoc]
    simpa [Complex.mul_im] using mul_nonneg hr hdTi
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (wedge_norm_qarg_add_le _ _ _ hui).trans haV
  · simpa only [UpperWindow.bArg, UpperContour.arcPoint, add_right_comm] using
      (wedge_norm_qarg_add_le ((e x.1) ^ (m + p))
        (UpperWindow.base M m n δ x.1 + x.2.2) _ hui).trans hbV
  · simpa only [UpperWindow.dArg, UpperContour.arcPoint, add_div] using
      (wedge_norm_qarg_add_le ((e (etaMobius M x.1)) ^ n)
        (UpperWindow.base M m n δ x.1 / etaDenom M x.1) _ huti).trans hdV
  · simpa only [UpperWindow.cArg, UpperContour.arcPoint, add_right_comm, add_div] using
      (wedge_norm_qarg_add_le ((e (etaMobius M x.1)) ^ n)
        ((UpperWindow.base M m n δ x.1 + x.2.2) / etaDenom M x.1) _ huti).trans hcV

theorem wedge_compact_upper_phi_bounds_all_int (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ m : ℤ,
      ∀ r : ℝ, 0 ≤ r → ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      let z := UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ
      ‖modularPhi M (m + 1) n z x.1‖ ≤ C ∧
        ‖(modularPhi M (m + 1) n z x.1)⁻¹‖ ≤ C ∧
        ‖modularPhi M (m + p) n (z + x.2.2) x.1‖ ≤ C ∧
        ‖(modularPhi M (m + p) n (z + x.2.2) x.1)⁻¹‖ ≤ C := by
  obtain ⟨η, R, qR, hη, hR, hqR0, hqR1, hparams⟩ :=
    UpperWindow.compact_parameter_bounds M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨uR, huR0, huR1, hargs⟩ :=
    wedge_compact_upper_arguments_all_int M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨B, hB, hb⟩ := wedge_q_bound η uR qR hη huR1 hqR1
  refine ⟨B * B, mul_pos hB hB, ?_⟩
  intro x hx m r hr θ hθ
  rcases hparams x hx with ⟨hτ, hTim, harg0, harg1, hT0, hT1, hq0, hq1, hQ0, hQ1, hw, hy⟩
  rcases hargs x hx m r hr θ hθ with ⟨ha, hb', hd, hcc⟩
  have hbX : ∀ u q : ℂ, ‖u‖ ≤ uR → (q = e x.1 ∨ q = e (etaMobius M x.1)) →
      ‖qPochhammer u q‖ ≤ B ∧ ‖(qPochhammer u q)⁻¹‖ ≤ B := by
    intro u q hu hq
    rcases hq with rfl | rfl
    · exact hb u _ hu hq0 hq1
    · exact hb u _ hu hQ0 hQ1
  have hphi := wedge_phi_bound_of_q_bounds M hc.1 x.1 (hη.trans_le hτ) B hB
    (hη.trans_le hq0) (hq1.trans_lt hqR1) (hη.trans_le hQ0) (hQ1.trans_lt hqR1)
    uR huR1 hbX
  exact ⟨(hphi (m + 1) n _ ha hd).1, (hphi (m + 1) n _ ha hd).2,
    (hphi (m + p) n _ hb' hcc).1, (hphi (m + p) n _ hb' hcc).2⟩

theorem wedge_fixed_m_base_exp_bound (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ P : ℝ, 0 < P ∧ ∀ x ∈ K,
      ‖e (UpperWindow.phase M m n h ℓ x.1 x.2.1 (UpperWindow.base M m n δ x.1))‖ ≤ P := by
  have hcont : ContinuousOn (fun x : UpperWindow.Parameters =>
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 (UpperWindow.base M m n δ x.1))) K := by
    intro x hx
    have hT : etaDenom M x.1 ≠ 0 :=
      (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 (hKU hx).1).2.2.2.1
    have hMc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc.1.ne'
    apply ContinuousAt.continuousWithinAt
    unfold e UpperWindow.phase UpperWindow.base etaMobius etaDenom
    unfold etaDenom at hT
    fun_prop (disch := assumption)
  obtain ⟨P, hP⟩ := hK.exists_bound_of_continuousOn hcont
  exact ⟨max 1 P, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x hx => (hP x hx).trans (le_max_right _ _)⟩

theorem wedge_arc_exp_bound (M : SL(2, ℤ)) (m n h ℓ : ℤ)
    (τ w v : ℂ) (hT : etaDenom M τ ≠ 0) (P lam r θ : ℝ)
    (hP : 0 ≤ P) (hr : 0 ≤ r)
    (hv : ‖e (UpperWindow.phase M m n h ℓ τ w v)‖ ≤ P)
    (hslope : lam ≤ (UpperWindow.upperSlope M h ℓ τ w * UpperWindow.rotation θ).im) :
    ‖e (UpperWindow.phase M m n h ℓ τ w (UpperContour.arcPoint v r θ))‖ ≤
      P * Real.exp (-2 * Real.pi * lam * r) := by
  rw [UpperContour.arcPoint, phase_affine M m n h ℓ τ w v _ hT, e_add', norm_mul,
    wedge_norm_e (UpperWindow.upperSlope M h ℓ τ w * ((r : ℂ) * UpperWindow.rotation θ))]
  have heq : (UpperWindow.upperSlope M h ℓ τ w *
      ((r : ℂ) * UpperWindow.rotation θ)).im =
      r * (UpperWindow.upperSlope M h ℓ τ w * UpperWindow.rotation θ).im := by
    rw [← mul_assoc, mul_comm _ (r : ℂ), mul_assoc]
    simp [Complex.mul_im]
  have he : Real.exp (-2 * Real.pi *
      (UpperWindow.upperSlope M h ℓ τ w * ((r : ℂ) * UpperWindow.rotation θ)).im) ≤
      Real.exp (-2 * Real.pi * lam * r) := by
    apply Real.exp_le_exp.mpr
    rw [heq]
    have hs := mul_le_mul_of_nonneg_left hslope hr
    nlinarith [Real.pi_pos]
  exact mul_le_mul hv he (Real.exp_nonneg _) hP

theorem wedge_kernel_bound_of_phi_exp (kind : Kind) (M : SL(2, ℤ)) (m n h ℓ p : ℤ)
    (x : UpperWindow.Parameters) (z : ℂ) (C P E : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hphi : ‖modularPhi M (m + 1) n z x.1‖ ≤ C ∧
      ‖(modularPhi M (m + p) n (z + x.2.2) x.1)⁻¹‖ ≤ C)
    (hexp : ‖e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)‖ ≤ P * E) :
    ‖UpperContour.kernel kind M m n h ℓ p x z‖ ≤ (C + C * C) * P * E := by
  cases kind with
  | single =>
    simp only [UpperContour.kernel, UpperWindow.singleKernel, norm_mul]
    calc
      _ ≤ C * (P * E) := mul_le_mul hphi.1 hexp (norm_nonneg _) hC
      _ = C * P * E := by ring
      _ ≤ (C + C * C) * P * E :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hC hC)) hP) hE
  | ratio =>
    simp only [UpperContour.kernel, UpperWindow.ratioKernel, div_eq_mul_inv, norm_mul]
    calc
      _ ≤ (C * C) * (P * E) := mul_le_mul
        (mul_le_mul hphi.1 hphi.2 (norm_nonneg _) hC) hexp
        (norm_nonneg _) (mul_nonneg hC hC)
      _ = (C * C) * P * E := by ring
      _ ≤ (C + C * C) * P * E :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) hP) hE

theorem wedge_fixed_m_upper_kernel_bound (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ ∀ x ∈ K,
      ∀ kind : Kind, ∀ r : ℝ, 0 ≤ r →
      ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      ‖UpperContour.kernel kind M m n h ℓ p x (UpperContour.arcPoint (UpperWindow.base M m n δ x.1) r θ)‖ ≤
        C * Real.exp (-2 * Real.pi * lam * r) := by
  obtain ⟨B, hB, hb⟩ :=
    wedge_compact_upper_phi_bounds_all_int M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨P, hP, hp⟩ :=
    wedge_fixed_m_base_exp_bound M h ℓ p m n ψ σ ρ δ hc K hK hKU
  obtain ⟨lam, hlam, hl⟩ :=
    UpperWindow.compact_arc_linear_margin M h ℓ p ψ σ ρ δ hc K hK hKU
  refine ⟨(B + B * B) * P, lam, by positivity, hlam, ?_⟩
  intro x hx kind r hr θ hθ
  have hT : etaDenom M x.1 ≠ 0 :=
    (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 (hKU hx).1).2.2.2.1
  exact wedge_kernel_bound_of_phi_exp kind M m n h ℓ p x _ B P _ hB.le hP.le
    (Real.exp_nonneg _) ⟨(hb x hx m r hr θ hθ).1, (hb x hx m r hr θ hθ).2.2.2⟩
    (wedge_arc_exp_bound M m n h ℓ x.1 x.2.1 _ hT P lam r θ hP.le hr
      (hp x hx) ((hl x hx).1 θ hθ))

theorem wedge_compact_upper_kernel_bound (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat, ∀ kind : Kind, ∀ r : ℝ, 0 ≤ r →
      ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      ‖UpperContour.kernel kind M (m : ℤ) n h ℓ p x
        (UpperContour.arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ)‖ ≤
        C * Real.exp (-2 * Real.pi * lam * r) := by
  obtain ⟨B, hB, hb⟩ :=
    wedge_compact_upper_phi_bounds_all_int M h ℓ p n ψ σ ρ δ hc K hK hKU
  choose P hP hp using fun m : ℕ =>
    wedge_fixed_m_base_exp_bound M h ℓ p (m : ℤ) n ψ σ ρ δ hc K hK hKU
  obtain ⟨lam, hlam, hl⟩ :=
    UpperWindow.compact_arc_linear_margin M h ℓ p ψ σ ρ δ hc K hK hKU
  let Psum : ℝ := 1 + ∑ m ∈ Finset.range (M 1 0).toNat, P m
  have hPsum : 0 < Psum := by
    have hs : 0 ≤ ∑ m ∈ Finset.range (M 1 0).toNat, P m :=
      Finset.sum_nonneg (fun m _ => (hP m).le)
    dsimp [Psum]
    linarith
  refine ⟨(B + B * B) * Psum, lam, by positivity, hlam, ?_⟩
  intro x hx m hm kind r hr θ hθ
  have hT : etaDenom M x.1 ≠ 0 :=
    (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 (hKU hx).1).2.2.2.1
  have hp' : ‖e (UpperWindow.phase M (m : ℤ) n h ℓ x.1 x.2.1
      (UpperWindow.base M (m : ℤ) n δ x.1))‖ ≤ Psum := by
    calc
      _ ≤ P m := hp m x hx
      _ ≤ ∑ j ∈ Finset.range (M 1 0).toNat, P j :=
        Finset.single_le_sum (fun j _ => (hP j).le) hm
      _ ≤ Psum := le_add_of_nonneg_left zero_le_one
  exact wedge_kernel_bound_of_phi_exp kind M (m : ℤ) n h ℓ p x _ B Psum _ hB.le hPsum.le
    (Real.exp_nonneg _) ⟨(hb x hx (m : ℤ) r hr θ hθ).1,
      (hb x hx (m : ℤ) r hr θ hθ).2.2.2⟩
    (wedge_arc_exp_bound M (m : ℤ) n h ℓ x.1 x.2.1 _ hT Psum lam r θ hPsum.le hr
      hp' ((hl x hx).1 θ hθ))

end SICLean.L4.UpperContourUpperArcAux
