import SICLean.L4.FaddeevContinuation
import SICLean.L4.QProduct
import SICLean.L4.EtaMultiplier
import SICLean.L4.FinitePrincipalParts
import SICLean.L4.FaddeevProductBridge

set_option autoImplicit false

/-!
# Upper-parameter product comparison

The function being identified is the existing, explicit `phiExtended`. The integral-to-product
bridge first combines its two difference equations on an upper unit-circle arc, uses the real-left
limit to determine normalization, and then applies analytic identity principles in the argument and
parameter. [RW26, p. 5, Appendix A.1, p. 28, (57)]. Also Andersen--Kashaev, arXiv:1109.6295,
Appendix A (44).

The half powers below are exponentials of the displayed arguments. They are not principal square
roots of the already exponentiated bases. The global equality is a fixed-b meromorphic germ
equality. A joint chart comparison uses cross multiplication of analytic numerators/denominators.
Deleting a single point of ℂ² would not remove its other common-zero points. Pointwise division is
asserted only when the product denominator is nonzero.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace SICLean.L4

/-- Parameter window in the first product formula on [RW26, p. 5]. -/
def phiUpperParameterDomain : Set ℂ := {b | AdmissibleB b ∧ 0 < (b ^ 2).im}

def phiProductQ (b : ℂ) : ℂ := e (b ^ 2)

def phiProductQDual (b : ℂ) : ℂ := e (-(b⁻¹) ^ 2)

/-- Literal [RW26] numerator, including `-exp(π i b²)`. -/
def phiProductNumerator (b z : ℂ) : ℂ :=
  qPochhammer
    (-Complex.exp ((Real.pi : ℂ) * Complex.I * b ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * b * z)) (phiProductQ b)

/-- Literal [RW26] denominator, including `-exp(-π i b⁻²)`. -/
def phiProductDenominator (b z : ℂ) : ℂ :=
  qPochhammer
    (-Complex.exp (-(Real.pi : ℂ) * Complex.I * (b⁻¹) ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * b⁻¹ * z)) (phiProductQDual b)

/-- Raw total quotient, used only for comparison on the upper parameter set. At common zeros this
representative can differ from `phiExtended`. -/
def phiUpperProduct (b z : ℂ) : ℂ :=
  phiProductNumerator b z / phiProductDenominator b z

/-- [RW26, p. 5] bases; Mathlib `Complex.norm_exp`, `Complex.exp_ne_zero`. -/
theorem phiProduct_bases_norm (b : ℂ) (hb : b ∈ phiUpperParameterDomain) :
    0 < ‖phiProductQ b‖ ∧ ‖phiProductQ b‖ < 1 ∧
      0 < ‖phiProductQDual b‖ ∧ ‖phiProductQDual b‖ < 1 := by
  have hb0 := admissibleB_ne_zero b hb.1
  have hdual : 0 < (-(b⁻¹) ^ 2).im := by
    have heq : -(b⁻¹) ^ 2 = -(b ^ 2)⁻¹ := by simp only [inv_pow]
    rw [heq, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hb.2 (Complex.normSq_pos.mpr (pow_ne_zero 2 hb0))
  exact ⟨norm_pos_iff.mpr (e_ne_zero _), norm_e_lt_one ⟨b ^ 2, hb.2⟩,
    norm_pos_iff.mpr (e_ne_zero _), norm_e_lt_one ⟨-(b⁻¹) ^ 2, hdual⟩⟩

/-- Joint, not just fixed-parameter, holomorphy of both products. [RW26, p. 5]. -/
theorem phiProduct_joint_analytic :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => phiProductNumerator p.1 p.2)
      {p | p.1 ∈ phiUpperParameterDomain} ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => phiProductDenominator p.1 p.2)
      {p | p.1 ∈ phiUpperParameterDomain} := by
  constructor
  · intro p hp
    have hn := phiProduct_bases_norm p.1 hp
    have h := analyticOnNhd_qPochhammer_joint
      (-Complex.exp ((Real.pi : ℂ) * Complex.I * p.1 ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * p.1 * p.2), phiProductQ p.1)
      ⟨hn.1, hn.2.1⟩
    apply h.comp (f := fun q : ℂ × ℂ =>
      (-Complex.exp ((Real.pi : ℂ) * Complex.I * q.1 ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * q.1 * q.2), phiProductQ q.1))
    apply AnalyticAt.prod
    · exact ((analyticAt_const.mul (analyticAt_fst.pow 2)).cexp').neg.mul
        (((analyticAt_const.mul analyticAt_fst).mul analyticAt_snd).cexp')
    · unfold phiProductQ e
      exact (analyticAt_const.mul (analyticAt_fst.pow 2)).cexp'
  · intro p hp
    have hn := phiProduct_bases_norm p.1 hp
    have hbi : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1⁻¹) p :=
      analyticAt_fst.inv (admissibleB_ne_zero p.1 hp.1)
    have h := analyticOnNhd_qPochhammer_joint
      (-Complex.exp (-(Real.pi : ℂ) * Complex.I * (p.1⁻¹) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * p.1⁻¹ * p.2), phiProductQDual p.1)
      ⟨hn.2.2.1, hn.2.2.2⟩
    apply h.comp (f := fun q : ℂ × ℂ =>
      (-Complex.exp (-(Real.pi : ℂ) * Complex.I * (q.1⁻¹) ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * q.1⁻¹ * q.2), phiProductQDual q.1))
    apply AnalyticAt.prod
    · exact ((analyticAt_const.mul (hbi.pow 2)).cexp').neg.mul
        (((analyticAt_const.mul hbi).mul analyticAt_snd).cexp')
    · unfold phiProductQDual e
      exact (analyticAt_const.mul (hbi.pow 2).neg).cexp'

/-- No denominator is locally identically zero on a fixed-b slice. -/
theorem phiProductDenominator_frequently_ne_zero (b z : ℂ)
    (hb : b ∈ phiUpperParameterDomain) :
    ∃ᶠ w : ℂ in 𝓝 z, phiProductDenominator b w ≠ 0 := by
  have hn := phiProduct_bases_norm b hb
  have harg : -Complex.exp (-(Real.pi : ℂ) * Complex.I * (b⁻¹) ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * b⁻¹ * (-Complex.I * b⁻¹ / 2)) =
      -phiProductQDual b := by
    rw [neg_mul, ← Complex.exp_add]
    congr 1
    unfold phiProductQDual e
    congr 1
    ring
  have hexplicit : phiProductDenominator b (-Complex.I * b⁻¹ / 2) ≠ 0 := by
    unfold phiProductDenominator
    rw [harg]
    exact qPochhammer_ne_zero_of_norm_lt_one _ _ (by simpa using hn.2.2.2)
      hn.2.2.1 hn.2.2.2
  have ha : AnalyticOnNhd ℂ (phiProductDenominator b) Set.univ := by
    intro w _
    exact (phiProduct_joint_analytic.2 (b,w) hb).comp
      (f := fun v : ℂ => (b,v)) (analyticAt_const.prod analyticAt_id)
  by_contra hfrequent
  have hz : phiProductDenominator b =ᶠ[𝓝 z] 0 := by
    filter_upwards [Filter.not_frequently.mp hfrequent] with w hw
    exact not_ne_iff.mp hw
  exact hexplicit (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) hz (Set.mem_univ _))

/-- Fixed-b meromorphy of the comparison quotient, not the identification. -/
theorem phiUpperProduct_meromorphic (b : ℂ) (hb : b ∈ phiUpperParameterDomain) :
    MeromorphicOn (phiUpperProduct b) Set.univ := by
  intro z _
  have hn : AnalyticAt ℂ (phiProductNumerator b) z :=
    (phiProduct_joint_analytic.1 (b,z) hb).comp
      (f := fun v : ℂ => (b,v)) (analyticAt_const.prod analyticAt_id)
  have hd : AnalyticAt ℂ (phiProductDenominator b) z :=
    (phiProduct_joint_analytic.2 (b,z) hb).comp
      (f := fun v : ℂ => (b,v)) (analyticAt_const.prod analyticAt_id)
  exact hn.meromorphicAt.div hd.meromorphicAt

/-- [RW26, p. 5] first product expansion, AK (44). This includes genuine poles and common product
zeros as germs. -/
theorem phiExtended_eq_upperProduct_germ (b z : ℂ)
    (hb : b ∈ phiUpperParameterDomain) :
    phiExtended b =ᶠ[𝓝[≠] z] phiUpperProduct b := by
  have hi : 0 < b.im := by
    have hs : 0 < (b ^ 2).im := hb.2
    have hr : 0 < b.re := hb.1
    simp only [pow_two, Complex.mul_im] at hs
    nlinarith
  apply meromorphic_germ_eq_global (phiExtended b) (phiUpperProduct b)
    (phiExtended_meromorphic b hb.1) (phiUpperProduct_meromorphic b hb) 0 ?_ z
  have hz₀ : InStrip b 0 := by
    have hi' := admissibleB_inv b hb.1
    change |(0 : ℂ).im| < (b.re + (b⁻¹).re) / 2
    simpa only [Complex.zero_im, abs_zero] using half_pos (add_pos hb.1 hi')
  have ha : AnalyticAt ℂ (phiProductDenominator b) 0 :=
    (phiProduct_joint_analytic.2 (b, 0) hb).comp
      (f := fun w : ℂ => (b, w)) (analyticAt_const.prod analyticAt_id)
  have hd : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ), phiProductDenominator b w ≠ 0 := by
    rcases ha.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact False.elim ((phiProductDenominator_frequently_ne_zero b 0 hb)
        (by simpa only [not_not] using hzero))
    · exact hne
  filter_upwards [nhdsWithin_le_nhds ((isOpen_inStrip b).mem_nhds hz₀), hd] with w hw hdw
  have hcross := FaddeevProductBridge.phi_strip_cross_mul b w hb.1 hi hw
  change phi b w * phiProductDenominator b w = phiProductNumerator b w at hcross
  rw [phiExtended_eq_phi b w hb.1 hw, phiUpperProduct]
  exact (eq_div_iff hdw).mpr hcross

/-- The cleared form is still a germ: at a genuine pole the assigned point value of `phiExtended` is 0.
Same source as the product expansion. -/
theorem phiExtended_mul_productDenominator_germ (b z : ℂ)
    (hb : b ∈ phiUpperParameterDomain) :
    (fun w => phiExtended b w * phiProductDenominator b w) =ᶠ[𝓝[≠] z]
      phiProductNumerator b := by
  have ha : AnalyticAt ℂ (phiProductDenominator b) z :=
    (phiProduct_joint_analytic.2 (b, z) hb).comp
      (f := fun w : ℂ => (b, w)) (analyticAt_const.prod analyticAt_id)
  have hd : ∀ᶠ w : ℂ in 𝓝[≠] z, phiProductDenominator b w ≠ 0 := by
    rcases ha.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact False.elim ((phiProductDenominator_frequently_ne_zero b z hb)
        (by simpa only [not_not] using hzero))
    · exact hne
  filter_upwards [phiExtended_eq_upperProduct_germ b z hb, hd] with w hw hdw
  rw [hw, phiUpperProduct, div_mul_cancel₀ _ hdw]

/-- The pointwise version of RW's product, with its essential nonzero denominator hypothesis. -/
theorem phiExtended_eq_upperProduct (b z : ℂ) (hb : b ∈ phiUpperParameterDomain)
    (hd : phiProductDenominator b z ≠ 0) :
    phiExtended b z = phiUpperProduct b z := by
  have hn : AnalyticAt ℂ (phiProductNumerator b) z :=
    (phiProduct_joint_analytic.1 (b, z) hb).comp
      (f := fun w : ℂ => (b, w)) (analyticAt_const.prod analyticAt_id)
  have hden : AnalyticAt ℂ (phiProductDenominator b) z :=
    (phiProduct_joint_analytic.2 (b, z) hb).comp
      (f := fun w : ℂ => (b, w)) (analyticAt_const.prod analyticAt_id)
  have hprod : AnalyticAt ℂ (phiUpperProduct b) z := hn.div hden hd
  have hgerm := phiExtended_eq_upperProduct_germ b z hb
  have ho : 0 ≤ meromorphicOrderAt (phiExtended b) z := by
    rw [meromorphicOrderAt_congr hgerm]
    exact hprod.meromorphicOrderAt_nonneg
  have hp : phiPoleMultiplicity b z = 0 := by
    by_contra hpos
    have hzpos : 0 < z.im := by
      have hex : ∃ m n : ℕ, z = phiPolePoint b m n := by
        by_contra hnone
        apply hpos
        apply (phiPoleMultiplicity_eq_zero_iff b z hb.1).mpr
        simpa only [not_exists] using hnone
      obtain ⟨m, n, rfl⟩ := hex
      exact phiPolePoint_im_pos b hb.1 m n
    have hzero : phiZeroMultiplicity b z = 0 := by
      apply (phiZeroMultiplicity_eq_zero_iff b z hb.1).mpr
      intro m n heq
      have hzneg : z.im < 0 := by
        rw [heq, phiZeroPoint, Complex.neg_im]
        exact neg_neg_of_pos (phiPolePoint_im_pos b hb.1 m n)
      linarith
    rw [phiExtended_order b z hb.1, phiDivisorOrder, hzero] at ho
    have hcast : (0 : ℤ) ≤ -(phiPoleMultiplicity b z : ℤ) := by
      simp only [Nat.cast_zero, zero_sub] at ho
      exact_mod_cast ho
    omega
  exact tendsto_nhds_unique
    ((phiExtended_analyticAt b z hb.1 hp).continuousAt.mono_left nhdsWithin_le_nhds)
    ((hprod.continuousAt.mono_left nhdsWithin_le_nhds).congr' hgerm.symm)

/-- Joint chart identity at all valid centers, including 0/0. This is the form used for pullbacks
and for joint comparisons. [RW26, p. 5]. Neither denominator is assumed nonzero here. -/
theorem phiChart_product_cross_mul (b z : ℂ) (k : ℤ)
    (hb : b ∈ phiUpperParameterDomain)
    (hz : InStrip b (shiftedArgument b z k)) :
    continuationNumerator b z k * phiProductDenominator b z =
      phiProductNumerator b z * continuationDenominator b z k := by
  have hn := analyticAt_continuationNumerator b z k hb.1 hz
  have hd := analyticAt_continuationDenominator b z k
  have hpn : AnalyticAt ℂ (phiProductNumerator b) z :=
    (phiProduct_joint_analytic.1 (b, z) hb).comp
      (f := fun w : ℂ => (b, w)) (analyticAt_const.prod analyticAt_id)
  have hpd : AnalyticAt ℂ (phiProductDenominator b) z :=
    (phiProduct_joint_analytic.2 (b, z) hb).comp
      (f := fun w : ℂ => (b, w)) (analyticAt_const.prod analyticAt_id)
  have hdnz : ∀ᶠ w : ℂ in 𝓝[≠] z, continuationDenominator b w k ≠ 0 := by
    rcases hd.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact False.elim ((continuationDenominator_frequently_ne_zero b z k hb.1 hz)
        (by simpa only [not_not] using hzero))
    · exact hne
  have hcross :
      (fun w : ℂ => continuationNumerator b w k * phiProductDenominator b w) =ᶠ[𝓝[≠] z]
        (fun w => phiProductNumerator b w * continuationDenominator b w k) := by
    filter_upwards [phiExtended_eq_chart b z k hb.1 hz,
      phiExtended_mul_productDenominator_germ b z hb, hdnz] with w hchart hprod hden
    have hc : phiExtended b w * continuationDenominator b w k =
        continuationNumerator b w k := (eq_div_iff hden).mp hchart
    calc
      continuationNumerator b w k * phiProductDenominator b w =
          (phiExtended b w * continuationDenominator b w k) *
            phiProductDenominator b w := by rw [hc]
      _ = (phiExtended b w * phiProductDenominator b w) *
          continuationDenominator b w k := by ring
      _ = phiProductNumerator b w * continuationDenominator b w k := by rw [hprod]
  exact tendsto_nhds_unique
    (((hn.mul hpd).continuousAt).mono_left nhdsWithin_le_nhds)
    ((((hpn.mul hd).continuousAt).mono_left nhdsWithin_le_nhds).congr' hcross.symm)

/-- Common zeros: both q products vanish inside the integral strip, whereas the actual continuation
is nonzero, so a pointwise quotient identity needs nonvanishing hypotheses. Specialization of
[RW26, p. 5], using `phi_ne_zero` and `phiExtended_eq_phi`. -/
theorem phiProduct_common_zero (b : ℂ) (hb : b ∈ phiUpperParameterDomain) :
    let z := Complex.I * b⁻¹ / 2 - Complex.I * b / 2
    phiProductNumerator b z = 0 ∧ phiProductDenominator b z = 0 ∧
      phiExtended b z ≠ 0 := by
  let z := Complex.I * b⁻¹ / 2 - Complex.I * b / 2
  have hb0 := admissibleB_ne_zero b hb.1
  have hn := phiProduct_bases_norm b hb
  have hN : -Complex.exp ((Real.pi : ℂ) * Complex.I * b ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * b * z) = 1 := by
    rw [neg_mul, ← Complex.exp_add]
    have hsum : (Real.pi : ℂ) * Complex.I * b ^ 2 +
        2 * (Real.pi : ℂ) * b * z = (Real.pi : ℂ) * Complex.I := by
      dsimp [z]
      field_simp
      ring
    rw [hsum, Complex.exp_pi_mul_I]
    ring
  have hD : -Complex.exp (-(Real.pi : ℂ) * Complex.I * (b⁻¹) ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * b⁻¹ * z) = 1 := by
    rw [neg_mul, ← Complex.exp_add]
    have hsum : -(Real.pi : ℂ) * Complex.I * (b⁻¹) ^ 2 +
        2 * (Real.pi : ℂ) * b⁻¹ * z = -((Real.pi : ℂ) * Complex.I) := by
      dsimp [z]
      field_simp
      ring
    rw [hsum, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hz : InStrip b z := by
    unfold InStrip stripWidth
    have hzIm : z.im = ((b⁻¹).re - b.re) / 2 := by
      simp [z, Complex.mul_im]
      ring
    rw [hzIm]
    have hbr : 0 < b.re := hb.1
    have hbir : 0 < (b⁻¹).re := admissibleB_inv b hb.1
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold phiProductNumerator
    rw [hN]
    exact (qPochhammer_eq_zero_iff _ _ hn.1 hn.2.1).mpr ⟨0, by simp⟩
  · unfold phiProductDenominator
    rw [hD]
    exact (qPochhammer_eq_zero_iff _ _ hn.2.2.1 hn.2.2.2).mpr ⟨0, by simp⟩
  · rw [phiExtended_eq_phi b z hb.1 hz]
    exact phi_ne_zero b z hb.1 hz

#check analyticOnNhd_qPochhammer_joint
#check phiExtended_joint_local_quotient
#check phiExtended_eq_phi
#check MeromorphicAt.div
#check Complex.exp_ne_zero
#print phiProductNumerator
#print phiProductDenominator
#print phiExtended_eq_upperProduct_germ
#print axioms phiProductNumerator
#print axioms phiExtended_eq_upperProduct_germ

end SICLean.L4
