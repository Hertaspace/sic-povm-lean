import SICLean.L4.UpperContourGeometry
import SICLean.L4.UpperResidueParametersAux

set_option autoImplicit false

/-!
# Literal q arguments and zero-free products on the initial box

Definitions merely
name explicit expressions. In particular no identity, convergence,
nonvanishing, or desired integral formula is a definition field.

The initial coordinate box is stronger than |A|,|B|<1 alone: all six
arguments a,t,A,B,aA,QC have norm <1. Thus all three displayed Φ values
on the RHS are actual units here. This does not assert the same on the
whole strict continuation window, or at a real boundary.
The existing modularPhi/phiExtended/etaMultiplier and slit-plane sqrt
are used unchanged; the q-product prefactor is not replaced by an eta limit. [RW26, p. 28, p. 29,
(50), (55), (56), (58), Appendix A.2].
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperResidueParameters

def a (p : ℤ) (x : UpperWindow.Parameters) : ℂ := (e x.1) ^ p * e x.2.2

def t (M : SL(2, ℤ)) (x : UpperWindow.Parameters) : ℂ :=
  e (x.2.2 / etaDenom M x.1)

def b (M : SL(2, ℤ)) (x : UpperWindow.Parameters) : ℂ :=
  e (etaMobius M x.1) / t M x

/-- T(q;q)∞/(Q;Q)∞, before the later eta-phase step. -/
def prefactor (M : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  etaDenom M τ * qPochhammer (e τ) (e τ) /
    qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))

def singleProduct (M : SL(2, ℤ)) (h ℓ : ℤ) (x : UpperWindow.Parameters) : ℂ :=
  prefactor M x.1 *
    (qPochhammer (e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1)
      (e (etaMobius M x.1)) / qPochhammer (UpperWindow.A ℓ x.1 x.2.1) (e x.1))

def ratioProduct (M : SL(2, ℤ)) (h ℓ p : ℤ) (x : UpperWindow.Parameters) : ℂ :=
  prefactor M x.1 * (qPochhammer (t M x) (e (etaMobius M x.1)) /
    qPochhammer (a p x) (e x.1)) *
    (qPochhammer (a p x * UpperWindow.A ℓ x.1 x.2.1) (e x.1) /
      qPochhammer (UpperWindow.A ℓ x.1 x.2.1) (e x.1)) *
    (qPochhammer (e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1)
      (e (etaMobius M x.1)) /
      qPochhammer (UpperWindow.B M h x.1 x.2.1 x.2.2) (e (etaMobius M x.1)))

/--
[RW26, p. 29]. The four extra bounds are coordinate-box elaborations.
-/
theorem six_arguments_norm_lt_one (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ‖a p x‖ < 1 ∧ ‖t M x‖ < 1 ∧ ‖UpperWindow.A ℓ x.1 x.2.1‖ < 1 ∧
      ‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ < 1 ∧
      ‖a p x * UpperWindow.A ℓ x.1 x.2.1‖ < 1 ∧
      ‖e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1‖ < 1 := by
  obtain ⟨hdom, hTi, hTr, hT, hq0, hq1, hQ0, hQ1⟩ :=
    UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  obtain ⟨hS1, hS2, hH1, hH2, hSH1, hSH2⟩ :=
    UpperWindow.coordinate_inequalities M h ℓ p ψ σ ρ δ hc x hx
  have hδ := (UpperWindow.radius_margins M ψ σ ρ δ hc).2.2.2.2.1
  have hn := UpperResidueParametersAux.argument_norms M hc.1 p ψ x.1 x.2.2 hx.1
  have hABC := UpperWindow.ABC_norms M hc.1 h ℓ p ψ x.1 x.2.1 x.2.2 hx.1
  have ha : ‖a p x‖ < 1 := by
    rw [a, hn.1]
    exact Real.rpow_lt_one hq0.le hq1 (by linarith)
  have ht : ‖t M x‖ < 1 := by
    rw [t, hn.2]
    exact Real.rpow_lt_one hQ0.le hQ1 (by linarith)
  have hAB := UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx
  refine ⟨ha, ht, hAB.2.1, hAB.2.2.2, ?_, ?_⟩
  · rw [norm_mul]
    nlinarith [norm_nonneg (a p x), norm_nonneg (UpperWindow.A ℓ x.1 x.2.1)]
  · rw [norm_mul, hABC.2.1]
    have heq : ‖e (etaMobius M x.1)‖ *
        Real.rpow ‖e (etaMobius M x.1)‖
          (-(UpperWindow.coords (etaDenom M x.1) (UpperWindow.s M h ℓ x.1 x.2.1)).2) =
        Real.rpow ‖e (etaMobius M x.1)‖
          (1 - (UpperWindow.coords (etaDenom M x.1) (UpperWindow.s M h ℓ x.1 x.2.1)).2) := by
      simp only [Real.rpow_eq_pow, sub_eq_add_neg, Real.rpow_add hQ0, Real.rpow_one]
    rw [heq]
    exact Real.rpow_lt_one hQ0.le hQ1 (by linarith)

/--
[RW26, p. 28, (50), (55), (56), (58)]. Each finite summand denominator is checked separately.
-/
theorem summand_denominators_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) (K J : ℕ) :
    qPochhammerNat (e τ) (e τ) K ≠ 0 ∧
      qPochhammerNat (e (etaMobius M τ)) (e (etaMobius M τ)) J ≠ 0 := by
  have hη := ModularCocycleUpperAux.etaMobius_im_pos M hτ
  exact ⟨qPochhammerNat_q_ne_zero _ K (norm_pos_iff.mpr (e_ne_zero _))
      (norm_e_lt_one ⟨τ, hτ⟩),
    qPochhammerNat_q_ne_zero _ J (norm_pos_iff.mpr (e_ne_zero _))
      (norm_e_lt_one ⟨_, hη⟩)⟩

/--
[RW26, p. 28, p. 29, (55), (56), (58)]. All infinite factors are units.
-/
theorem infinite_products_ne_zero (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    qPochhammer (e x.1) (e x.1) ≠ 0 ∧
      qPochhammer (e (etaMobius M x.1)) (e (etaMobius M x.1)) ≠ 0 ∧
      qPochhammer (a p x) (e x.1) ≠ 0 ∧
      qPochhammer (t M x) (e (etaMobius M x.1)) ≠ 0 ∧
      qPochhammer (UpperWindow.A ℓ x.1 x.2.1) (e x.1) ≠ 0 ∧
      qPochhammer (UpperWindow.B M h x.1 x.2.1 x.2.2) (e (etaMobius M x.1)) ≠ 0 ∧
      qPochhammer (a p x * UpperWindow.A ℓ x.1 x.2.1) (e x.1) ≠ 0 ∧
      qPochhammer (e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1)
        (e (etaMobius M x.1)) ≠ 0 := by
  obtain ⟨hdom, hTi, hTr, hT, hq0, hq1, hQ0, hQ1⟩ :=
    UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  obtain ⟨ha, ht, hA, hB, haA, hQC⟩ :=
    six_arguments_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx
  exact ⟨qPochhammer_q_ne_zero _ hq0 hq1,
    qPochhammer_q_ne_zero _ hQ0 hQ1,
    qPochhammer_ne_zero_of_norm_lt_one _ _ ha hq0 hq1,
    qPochhammer_ne_zero_of_norm_lt_one _ _ ht hQ0 hQ1,
    qPochhammer_ne_zero_of_norm_lt_one _ _ hA hq0 hq1,
    qPochhammer_ne_zero_of_norm_lt_one _ _ hB hQ0 hQ1,
    qPochhammer_ne_zero_of_norm_lt_one _ _ haA hq0 hq1,
    qPochhammer_ne_zero_of_norm_lt_one _ _ hQC hQ0 hQ1⟩

/--
[RW26, p. 29]. Algebra for the two q-binomial substitutions.
-/
theorem argument_identities (M : SL(2, ℤ)) (h ℓ p : ℤ) (x : UpperWindow.Parameters) :
    t M x ≠ 0 ∧
      a p x * UpperWindow.A ℓ x.1 x.2.1 = (e x.1) ^ (p + ℓ) * e (x.2.1 + x.2.2) ∧
      b M x * UpperWindow.B M h x.1 x.2.1 x.2.2 =
        e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1 := by
  refine ⟨e_ne_zero _, ?_, ?_⟩
  · simp only [a, UpperWindow.A, zpow_add₀ (e_ne_zero _), e_add']
    ring
  · unfold b UpperWindow.B
    dsimp [t]
    field_simp [e_ne_zero]

/--
[RW26, p. 29]. No etaMultiplier or real q-boundary limit is assumed.
-/
theorem prefactor_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) : prefactor M τ ≠ 0 := by
  have hη := ModularCocycleUpperAux.etaMobius_im_pos M hτ
  exact div_ne_zero
    (mul_ne_zero (etaDenom_ne_zero M hM ⟨τ, hτ⟩)
      (qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _))
        (norm_e_lt_one ⟨τ, hτ⟩)))
    (qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _))
      (norm_e_lt_one ⟨_, hη⟩))

/--
[RW26, p. 28, p. 29, (55), (56)].
Point values are licensed by nonzero q denominators, not by a germ.
-/
theorem single_phi_eq_product_and_unit (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    modularPhi M ℓ (1 - h) x.2.1 x.1 =
      qPochhammer (UpperWindow.A ℓ x.1 x.2.1) (e x.1) /
        qPochhammer (e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1)
          (e (etaMobius M x.1)) ∧
      (x.2.1, x.1) ∈ modularPhiNonvanishingDomain M ℓ (1 - h) ∧
      modularPhi M ℓ (1 - h) x.2.1 x.1 ≠ 0 := by
  obtain ⟨hq, hQ, ha, ht, hA, hB, haA, hQC⟩ :=
    infinite_products_ne_zero M h ℓ p ψ σ ρ δ hc x hx
  have hd : modularPhiQDenominator M (1 - h) x.2.1 x.1 =
      qPochhammer (e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1)
        (e (etaMobius M x.1)) := by
    simp only [modularPhiQDenominator, UpperWindow.C,
      sub_eq_add_neg, zpow_add₀ (e_ne_zero _), zpow_one, mul_assoc]
  simpa only [modularPhiQProduct, modularPhiQNumerator, UpperWindow.A, hd] using
    UpperResidueParametersAux.phi_unit_of_q_products M hc.1 ℓ (1 - h)
      x.2.1 x.1 hx.1.1 hA (hd.symm ▸ hQC)

/--
[RW26, p. 29]. The y-factor is an actual unit.
-/
theorem ratio_denominator_phi_eq_product_and_unit
    (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    modularPhi M p 0 x.2.2 x.1 =
      qPochhammer (a p x) (e x.1) / qPochhammer (t M x) (e (etaMobius M x.1)) ∧
      (x.2.2, x.1) ∈ modularPhiNonvanishingDomain M p 0 ∧
      modularPhi M p 0 x.2.2 x.1 ≠ 0 := by
  obtain ⟨hq, hQ, ha, ht, hA, hB, haA, hQC⟩ :=
    infinite_products_ne_zero M h ℓ p ψ σ ρ δ hc x hx
  simpa only [modularPhiQProduct, modularPhiQNumerator, modularPhiQDenominator,
    zpow_zero, one_mul, a, t] using
    UpperResidueParametersAux.phi_unit_of_q_products M hc.1 p 0
      x.2.2 x.1 hx.1.1 ha (by simpa [modularPhiQDenominator, t] using ht)

/--
[RW26, p. 29]. The numerator is regular as well.
-/
theorem ratio_numerator_phi_eq_product_and_unit
    (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    modularPhi M (p + ℓ) (-h) (x.2.1 + x.2.2) x.1 =
      qPochhammer (a p x * UpperWindow.A ℓ x.1 x.2.1) (e x.1) /
        qPochhammer (UpperWindow.B M h x.1 x.2.1 x.2.2) (e (etaMobius M x.1)) ∧
      (x.2.1 + x.2.2, x.1) ∈ modularPhiNonvanishingDomain M (p + ℓ) (-h) ∧
      modularPhi M (p + ℓ) (-h) (x.2.1 + x.2.2) x.1 ≠ 0 := by
  obtain ⟨hq, hQ, ha, ht, hA, hB, haA, hQC⟩ :=
    infinite_products_ne_zero M h ℓ p ψ σ ρ δ hc x hx
  have hn : modularPhiQNumerator (p + ℓ) (x.2.1 + x.2.2) x.1 =
      qPochhammer (a p x * UpperWindow.A ℓ x.1 x.2.1) (e x.1) := by
    rw [(argument_identities M h ℓ p x).2.1]
    rfl
  have hd : modularPhiQDenominator M (-h) (x.2.1 + x.2.2) x.1 =
      qPochhammer (UpperWindow.B M h x.1 x.2.1 x.2.2)
        (e (etaMobius M x.1)) := by
    simp only [modularPhiQDenominator, UpperWindow.B, UpperWindow.C, add_div, e_add']
    congr 1
    ring
  simpa only [modularPhiQProduct, hn, hd] using
    UpperResidueParametersAux.phi_unit_of_q_products M hc.1 (p + ℓ) (-h)
      (x.2.1 + x.2.2) x.1 hx.1.1 (hn.symm ▸ haA) (hd.symm ▸ hB)

/--
[RW26, p. 28, p. 29, (55), (56)].
-/
theorem singleProduct_eq_modularPhi (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    singleProduct M h ℓ x =
      prefactor M x.1 * (modularPhi M ℓ (1 - h) x.2.1 x.1)⁻¹ := by
  rw [(single_phi_eq_product_and_unit M h ℓ p ψ σ ρ δ hc x hx).1]
  simp only [singleProduct, inv_div]

/--
[RW26, p. 29]. Denominators justified above.
-/
theorem ratioProduct_eq_modularPhi (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ratioProduct M h ℓ p x = prefactor M x.1 *
      (modularPhi M (p + ℓ) (-h) (x.2.1 + x.2.2) x.1 /
        (modularPhi M p 0 x.2.2 x.1 * modularPhi M ℓ (1 - h) x.2.1 x.1)) := by
  rw [(single_phi_eq_product_and_unit M h ℓ p ψ σ ρ δ hc x hx).1,
    (ratio_denominator_phi_eq_product_and_unit M h ℓ p ψ σ ρ δ hc x hx).1,
    (ratio_numerator_phi_eq_product_and_unit M h ℓ p ψ σ ρ δ hc x hx).1]
  obtain ⟨hq, hQ, ha, ht, hA, hB, haA, hQC⟩ :=
    infinite_products_ne_zero M h ℓ p ψ σ ρ δ hc x hx
  unfold ratioProduct
  field_simp


/--
[RW26, p. 29]. Integer phase error disappears under e.
-/
theorem phase_at_pole (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n h ℓ : ℤ)
    (τ w : ℂ) (hτ : 0 < τ.im) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    e (UpperWindow.phase M m n h ℓ τ w
      (modularPhiPolePoint M (m + 1) n τ k.1 k.2)) =
        UpperWindow.A ℓ τ w ^ k.1 * UpperWindow.C M h τ w ^ k.2 := by
  obtain ⟨r, hr⟩ := UpperResidueParametersAux.phase_pole_integer M hM m n h ℓ τ w hτ k hk
  rw [hr, e_add', e_intCast, mul_one]
  simp only [UpperWindow.A, UpperWindow.C, e_int_mul, ← e_add', e_nat_mul]

/--
[RW26, p. 28, p. 29, (55), (56), (58)]. Joint parameter analyticity on this
initial open set, not analytic continuation to the whole target window.
-/
theorem products_analytic (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) :
    AnalyticOnNhd ℂ (singleProduct M h ℓ) (UpperWindow.domain M h ℓ p ψ σ ρ δ) ∧
      AnalyticOnNhd ℂ (ratioProduct M h ℓ p) (UpperWindow.domain M h ℓ p ψ σ ρ δ) := by
  suffices H : ∀ x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ,
      AnalyticAt ℂ (singleProduct M h ℓ) x ∧ AnalyticAt ℂ (ratioProduct M h ℓ p) x from
    ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩
  intro x hx
  obtain ⟨hdom, hTi, hTr, hT, hq0, hq1, hQ0, hQ1⟩ :=
    UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  obtain ⟨hqq, hQQ, haN, htN, hAN, hBN, haAN, hQCN⟩ :=
    infinite_products_ne_zero M h ℓ p ψ σ ρ δ hc x hx
  have he (f : UpperWindow.Parameters → ℂ) (hf : AnalyticAt ℂ f x) :
      AnalyticAt ℂ (fun z => e (f z)) x :=
    (analyticAt_const.mul hf).cexp'
  have hτ : AnalyticAt ℂ (fun z : UpperWindow.Parameters => z.1) x := analyticAt_fst
  have hw : AnalyticAt ℂ (fun z : UpperWindow.Parameters => z.2.1) x :=
    analyticAt_fst.comp analyticAt_snd
  have hy : AnalyticAt ℂ (fun z : UpperWindow.Parameters => z.2.2) x :=
    analyticAt_snd.comp analyticAt_snd
  have hd : AnalyticAt ℂ (fun z : UpperWindow.Parameters => etaDenom M z.1) x :=
    (analyticAt_const.mul hτ).add analyticAt_const
  have hm : AnalyticAt ℂ (fun z : UpperWindow.Parameters => etaMobius M z.1) x :=
    ((analyticAt_const.mul hτ).add analyticAt_const).div hd hT
  have hq := he _ hτ
  have hQ := he _ hm
  have ha : AnalyticAt ℂ (a p) x := by
    change AnalyticAt ℂ (fun z : UpperWindow.Parameters => (e z.1) ^ p * e z.2.2) x
    simp only [e_int_mul]
    exact (he _ (analyticAt_const.mul hτ)).mul (he _ hy)
  have ht : AnalyticAt ℂ (t M) x := he _ (hy.div hd hT)
  have hA : AnalyticAt ℂ (fun z : UpperWindow.Parameters => UpperWindow.A ℓ z.1 z.2.1) x := by
    simp only [UpperWindow.A, e_int_mul]
    exact (he _ (analyticAt_const.mul hτ)).mul (he _ hw)
  have hC : AnalyticAt ℂ (fun z : UpperWindow.Parameters => UpperWindow.C M h z.1 z.2.1) x := by
    simp only [UpperWindow.C, e_int_mul]
    exact (he _ (analyticAt_const.mul hm)).mul (he _ (hw.div hd hT))
  have hB : AnalyticAt ℂ (fun z : UpperWindow.Parameters => UpperWindow.B M h z.1 z.2.1 z.2.2) x :=
    ht.mul hC
  have hPq (f : UpperWindow.Parameters → ℂ) (hf : AnalyticAt ℂ f x) :
      AnalyticAt ℂ (fun z => qPochhammer (f z) (e z.1)) x := by
    have hP : AnalyticAt ℂ (fun u : ℂ × ℂ => qPochhammer u.1 u.2) (f x, e x.1) :=
      analyticOnNhd_qPochhammer_joint _ ⟨hq0, hq1⟩
    exact hP.comp₂ hf hq
  have hPQ (f : UpperWindow.Parameters → ℂ) (hf : AnalyticAt ℂ f x) :
      AnalyticAt ℂ (fun z => qPochhammer (f z) (e (etaMobius M z.1))) x := by
    have hP : AnalyticAt ℂ (fun u : ℂ × ℂ => qPochhammer u.1 u.2)
        (f x, e (etaMobius M x.1)) := analyticOnNhd_qPochhammer_joint _ ⟨hQ0, hQ1⟩
    exact hP.comp₂ hf hQ
  have hPf : AnalyticAt ℂ (fun z : UpperWindow.Parameters => prefactor M z.1) x :=
    (hd.mul (hPq _ hq)).div (hPQ _ hQ) hQQ
  exact ⟨hPf.mul ((hPQ _ (hQ.mul hC)).div (hPq _ hA) hAN),
    ((hPf.mul ((hPQ _ ht).div (hPq _ ha) haN)).mul
      ((hPq _ (ha.mul hA)).div (hPq _ hA) hAN)).mul
      ((hPQ _ (hQ.mul hC)).div (hPQ _ hB) hBN)⟩

#print prefactor
#print ratioProduct
#check modularPhi_eq_qProduct
#check qPochhammerNat_q_ne_zero
#check six_arguments_norm_lt_one
#check infinite_products_ne_zero
#check products_analytic

end SICLean.L4.UpperResidueParameters
