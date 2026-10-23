import SICLean.L4.ModularCocycle
import SICLean.L4.ModularDivisor
import SICLean.L4.ModularDistributionAux

set_option autoImplicit false

/-!
# The actual Φ doubling identity

The doubling identity is formalized here. [RW26, Prop. 9].
No G1, Fourier, or pentagon input is used.

The double matrix is constructed, not supplied with a distribution law.
The joint identity is a cross product of analytic charts. Germs are
fixed-τ punctured z-germs; point values require actual regular centers.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4

/-- The integer matrix, before its determinant is checked. -/
def modularDoubleMatrix (M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![M 0 0, 2 * M 0 1; M 1 0 / 2, M 1 1]

/--
Determinant arithmetic; [RW26, p. 14, Prop. 9].
Divisibility is essential: `/` is integer Euclidean division.
-/
theorem modularDoubleMatrix_det (M : SL(2, ℤ)) (hc : 2 ∣ M 1 0) :
    (modularDoubleMatrix M).det = 1 := by
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  have hhalf := Int.mul_ediv_cancel' hc
  rw [modularDoubleMatrix, Matrix.det_fin_two]
  change M 0 0 * M 1 1 - (2 * M 0 1) * (M 1 0 / 2) = 1
  linear_combination hdet - M 0 1 * hhalf

/-- The same actual matrix for Φ and η; no arbitrary target matrix. -/
def modularDouble (M : SL(2, ℤ)) (hc : 2 ∣ M 1 0) : SL(2, ℤ) :=
  ⟨modularDoubleMatrix M, modularDoubleMatrix_det M hc⟩

/--
Exact entry contract used by `eta_doubling_quotient`; [RW26, p. 14, Prop. 9].
-/
theorem modularDouble_entries (M : SL(2, ℤ)) (hc : 2 ∣ M 1 0) :
    modularDouble M hc 0 0 = M 0 0 ∧
      modularDouble M hc 0 1 = 2 * M 0 1 ∧
      2 * modularDouble M hc 1 0 = M 1 0 ∧
      modularDouble M hc 1 1 = M 1 1 := by
  exact ⟨rfl, rfl, Int.mul_ediv_cancel' hc, rfl⟩

/--
Positivity and odd a,d follow from c>0, even c and det=1; [RW26, p. 14, Prop. 9].
-/
theorem modularDouble_pos_parity (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : 2 ∣ M 1 0) :
    0 < modularDouble M hc 1 0 ∧ Odd (M 0 0) ∧ Odd (M 1 1) := by
  have hhalf := (modularDouble_entries M hc).2.2.1
  exact ⟨by omega, ModularDistributionAux.odd_entries M hc⟩

/--
Algebraic identities, including total values outside the domain; [RW26, p. 14, Prop. 9].
-/
theorem modularDouble_automorphy (M : SL(2, ℤ)) (hc : 2 ∣ M 1 0) (τ : ℂ) :
    etaDenom (modularDouble M hc) (2 * τ) = etaDenom M τ ∧
      etaMobius (modularDouble M hc) (2 * τ) = 2 * etaMobius M τ := by
  obtain ⟨ha, hb, hc', hd⟩ := modularDouble_entries M hc
  have hcC : (2 : ℂ) * (modularDouble M hc 1 0 : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast hc'
  have hbC : (modularDouble M hc 0 1 : ℂ) = 2 * (M 0 1 : ℂ) := by
    exact_mod_cast hb
  have hden : etaDenom (modularDouble M hc) (2 * τ) = etaDenom M τ := by
    unfold etaDenom
    rw [hd, ← hcC]
    ring
  refine ⟨hden, ?_⟩
  unfold etaMobius
  rw [hden, ha, hbC]
  ring

/--
The complete common slit domain, not merely a real neighborhood; [RW26, p. 2, (1)].
-/
theorem modularDouble_domain (M : SL(2, ℤ)) (hc : 2 ∣ M 1 0) (τ : ℂ) :
    2 * τ ∈ modularPhiDomain (modularDouble M hc) ↔ τ ∈ modularPhiDomain M := by
  change etaDenom (modularDouble M hc) (2 * τ) ∈ Complex.slitPlane ↔ _
  rw [(modularDouble_automorphy M hc τ).1]
  rfl

/--
The two exact minus signs behind q-product pairing; [RW26, p. 28, (57)].
-/
theorem modularDistribution_q_arguments (M : SL(2, ℤ)) (hc : 2 ∣ M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (e τ) ^ m * e (z + 1 / 2) = -((e τ) ^ m * e z) ∧
      (e (etaMobius M τ)) ^ (n + M 1 0 / 2) *
          e ((z + 1 / 2) / etaDenom M τ) =
        -((e (etaMobius M τ)) ^ n * e (z / etaDenom M τ)) := by
  constructor
  · rw [e_add', ModularDistributionAux.e_half]
    ring
  · rw [zpow_add₀ (e_ne_zero _),
      show (z + 1 / 2) / etaDenom M τ =
        z / etaDenom M τ + 1 / (2 * etaDenom M τ) by ring, e_add']
    have hphase : e (((M 1 0 / 2 : ℤ) : ℂ) * etaMobius M τ) *
        e (1 / (2 * etaDenom M τ)) = -1 := by
      rw [← e_add', ModularDistributionAux.half_mobius M hc τ
        (Complex.slitPlane_ne_zero hτ)]
      exact ModularDistributionAux.e_odd_half _ (ModularDistributionAux.odd_entries M hc).1
    simp only [e_int_mul]
    linear_combination (e ((n : ℂ) * etaMobius M τ) * e (z / etaDenom M τ)) * hphase

/--
Pair numerator and denominator separately, so common zeros are legal; [RW26, p. 28, (57)].
-/
theorem modularDistribution_q_products (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : 2 ∣ M 1 0) (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    modularPhiQNumerator m z τ * modularPhiQNumerator m (z + 1 / 2) τ =
        modularPhiQNumerator m (2 * z) (2 * τ) ∧
      modularPhiQDenominator M n z τ *
          modularPhiQDenominator M (n + M 1 0 / 2) (z + 1 / 2) τ =
        modularPhiQDenominator (modularDouble M hc) n (2 * z) (2 * τ) := by
  have hdom := upper_mem_modularPhiDomain M hM (⟨τ, hτ⟩ : ℍ)
  obtain ⟨hnum, hden⟩ := modularDistribution_q_arguments M hc m n z τ hdom
  have hq0 := norm_pos_iff.mpr (e_ne_zero τ)
  have hq1 := norm_e_lt_one (⟨τ, hτ⟩ : ℍ)
  have hσ := ModularCocycleUpperAux.etaMobius_im_pos M hτ
  constructor
  · simp only [modularPhiQNumerator, hnum]
    rw [qPochhammer_sign_pair _ _ hq0 hq1,
      ModularDistributionAux.argument_double, ModularDistributionAux.e_double]
  · simp only [modularPhiQDenominator, hden]
    rw [qPochhammer_sign_pair _ _ (norm_pos_iff.mpr (e_ne_zero _))
      (norm_e_lt_one (⟨etaMobius M τ, hσ⟩ : ℍ)),
      (modularDouble_automorphy M hc τ).1,
      (modularDouble_automorphy M hc τ).2,
      show 2 * z / etaDenom M τ = 2 * (z / etaDenom M τ) by ring,
      ModularDistributionAux.argument_double, ModularDistributionAux.e_double]

/--
Upper-half-plane identification with the actual finite product; [RW26, p. 2, p. 6, (1), (19)].
-/
theorem modularDistribution_upper_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : 2 ∣ M 1 0) (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    (fun w => modularPhi M m n w τ *
        modularPhi M m (n + M 1 0 / 2) (w + 1 / 2) τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhi (modularDouble M hc) m n (2 * w) (2 * τ)) := by
  have hJ := (modularDouble_pos_parity M hM hc).1
  have hτ₂ : 0 < (2 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have hshift : Tendsto (fun w : ℂ => w + 1 / 2) (𝓝[≠] z) (𝓝[≠] (z + 1 / 2)) :=
    by simpa using ModularDistributionAux.tendsto_affine_nhdsNE 1 (1 / 2) z one_ne_zero
  have hdouble : Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] z) (𝓝[≠] (2 * z)) :=
    by simpa using ModularDistributionAux.tendsto_affine_nhdsNE 2 0 z (by norm_num)
  filter_upwards [modularPhi_eq_qProduct_germ M hM m n z τ hτ,
    (modularPhi_eq_qProduct_germ M hM m (n + M 1 0 / 2) (z + 1 / 2) τ hτ).comp_tendsto hshift,
    (modularPhi_eq_qProduct_germ (modularDouble M hc) hJ m n (2 * z) (2 * τ) hτ₂).comp_tendsto hdouble]
    with w hw₁ hw₂ hwJ
  dsimp only [Function.comp_def] at hw₂ hwJ
  rw [hw₁, hw₂, hwJ, modularPhiQProduct, modularPhiQProduct, modularPhiQProduct,
    ← mul_div_mul_comm, (modularDistribution_q_products M hM hc m n w τ hτ).1,
    (modularDistribution_q_products M hM hc m n w τ hτ).2]

/--
Joint continuation via denominator-cleared analytic chart identities; [RW26, p. 6, (19)]. This is
not a deleted-center assertion on ℂ².
-/
theorem modularDistribution_chart_cross_mul (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : 2 ∣ M 1 0) (m n : ℤ) (κ₁ κ₂ κJ : ℕ → ℤ) (z τ : ℂ)
    (h₁ : (z, τ) ∈ modularPhiChartDomain M m n κ₁)
    (h₂ : (z + 1 / 2, τ) ∈ modularPhiChartDomain M m (n + M 1 0 / 2) κ₂)
    (hJ : (2 * z, 2 * τ) ∈ modularPhiChartDomain (modularDouble M hc) m n κJ) :
    modularPhiChartNumerator M m n κ₁ z τ *
        modularPhiChartNumerator M m (n + M 1 0 / 2) κ₂ (z + 1 / 2) τ *
        modularPhiChartDenominator (modularDouble M hc) m n κJ (2 * z) (2 * τ) =
      modularPhiChartNumerator (modularDouble M hc) m n κJ (2 * z) (2 * τ) *
        modularPhiChartDenominator M m n κ₁ z τ *
        modularPhiChartDenominator M m (n + M 1 0 / 2) κ₂ (z + 1 / 2) τ := by
  exact ModularDistributionAux.chart_cross_mul_of_upper M (modularDouble M hc) hM
    (modularDouble_pos_parity M hM hc).1 m n (n + M 1 0 / 2)
    (modularDouble_domain M hc) (modularDistribution_upper_germ M hM hc m n)
    κ₁ κ₂ κJ z τ h₁ h₂ hJ

/--
Full-domain punctured z-germ; τ may be real or in either half-plane; [RW26, p. 2] continuation
domain.
-/
theorem modularDistribution_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : 2 ∣ M 1 0) (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M m n w τ *
        modularPhi M m (n + M 1 0 / 2) (w + 1 / 2) τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhi (modularDouble M hc) m n (2 * w) (2 * τ)) := by
  have hJ := (modularDouble_pos_parity M hM hc).1
  obtain ⟨κ₁, h₁⟩ := ModularDistributionAux.chart_cover M m n (z, τ) hτ
  obtain ⟨κ₂, h₂⟩ := ModularDistributionAux.chart_cover M m (n + M 1 0 / 2) (z + 1 / 2, τ) hτ
  obtain ⟨κJ, hκJ⟩ := ModularDistributionAux.chart_cover (modularDouble M hc) m n
    (2 * z, 2 * τ) ((modularDouble_domain M hc τ).mpr hτ)
  have ht₂ : Tendsto (fun w : ℂ => w + 1 / 2) (𝓝[≠] z) (𝓝[≠] (z + 1 / 2)) := by
    simpa using ModularDistributionAux.tendsto_affine_nhdsNE 1 (1 / 2) z one_ne_zero
  have htJ : Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] z) (𝓝[≠] (2 * z)) := by
    simpa using ModularDistributionAux.tendsto_affine_nhdsNE 2 0 z (by norm_num)
  have hu₁ : ∀ᶠ w in 𝓝 z, (w, τ) ∈ modularPhiChartDomain M m n κ₁ :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      ((modularPhiChartDomain_isOpen M m n κ₁).mem_nhds h₁)
  have hu₂ : ∀ᶠ w in 𝓝 z, (w + 1 / 2, τ) ∈ modularPhiChartDomain M m (n + M 1 0 / 2) κ₂ :=
    ((continuousAt_id.add continuousAt_const).prodMk continuousAt_const).preimage_mem_nhds
      ((modularPhiChartDomain_isOpen M m (n + M 1 0 / 2) κ₂).mem_nhds h₂)
  have huJ : ∀ᶠ w in 𝓝 z, (2 * w, 2 * τ) ∈ modularPhiChartDomain (modularDouble M hc) m n κJ :=
    ((continuousAt_const.mul continuousAt_id).prodMk continuousAt_const).preimage_mem_nhds
      ((modularPhiChartDomain_isOpen (modularDouble M hc) m n κJ).mem_nhds hκJ)
  filter_upwards [hu₁.filter_mono nhdsWithin_le_nhds, hu₂.filter_mono nhdsWithin_le_nhds,
    huJ.filter_mono nhdsWithin_le_nhds,
    ModularDistributionAux.chart_den_eventually M hM m n κ₁ (z, τ) h₁,
    ht₂.eventually (ModularDistributionAux.chart_den_eventually M hM m (n + M 1 0 / 2)
      κ₂ (z + 1 / 2, τ) h₂),
    htJ.eventually (ModularDistributionAux.chart_den_eventually (modularDouble M hc) hJ m n
      κJ (2 * z, 2 * τ) hκJ)] with w hw₁ hw₂ hwJ hd₁ hd₂ hdJ
  rw [modularPhi_eq_chart M hM m n κ₁ (w, τ) hw₁,
    modularPhi_eq_chart M hM m (n + M 1 0 / 2) κ₂ (w + 1 / 2, τ) hw₂,
    modularPhi_eq_chart (modularDouble M hc) hJ m n κJ (2 * w, 2 * τ) hwJ]
  simp only [modularPhiChart]
  rw [← mul_div_mul_comm, div_eq_div_iff (mul_ne_zero hd₁ hd₂) hdJ]
  simpa only [mul_assoc] using modularDistribution_chart_cross_mul M hM hc m n κ₁ κ₂ κJ w τ hw₁ hw₂ hwJ

/--
Actual centers on the no-pole loci. Zeros are allowed; [RW26, p. 6].
-/
theorem modularDistribution_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : 2 ∣ M 1 0) (m n : ℤ) (z τ : ℂ)
    (h₁ : (z, τ) ∈ modularPhiHolomorphicDomain M m n)
    (h₂ : (z + 1 / 2, τ) ∈ modularPhiHolomorphicDomain M m (n + M 1 0 / 2))
    (hJ : (2 * z, 2 * τ) ∈ modularPhiHolomorphicDomain (modularDouble M hc) m n) :
    modularPhi M m n z τ * modularPhi M m (n + M 1 0 / 2) (z + 1 / 2) τ =
      modularPhi (modularDouble M hc) m n (2 * z) (2 * τ) := by
  have hc₁ : ContinuousAt (fun w : ℂ => modularPhi M m n w τ) z :=
    ((modularPhi_joint_analytic_no_poles M hM m n) (z, τ) h₁).continuousAt.comp
      (f := fun w : ℂ => (w, τ))
      (continuousAt_id.prodMk continuousAt_const)
  have hc₂ : ContinuousAt (fun w : ℂ => modularPhi M m (n + M 1 0 / 2) (w + 1 / 2) τ) z :=
    ((modularPhi_joint_analytic_no_poles M hM m (n + M 1 0 / 2)) (z + 1 / 2, τ) h₂).continuousAt.comp
      (f := fun w : ℂ => (w + 1 / 2, τ))
      ((continuousAt_id.add continuousAt_const).prodMk continuousAt_const)
  have hcJ : ContinuousAt (fun w : ℂ => modularPhi (modularDouble M hc) m n (2 * w) (2 * τ)) z :=
    ((modularPhi_joint_analytic_no_poles (modularDouble M hc) (modularDouble_pos_parity M hM hc).1 m n)
      (2 * z, 2 * τ) hJ).continuousAt.comp
        (f := fun w : ℂ => (2 * w, 2 * τ))
        ((continuousAt_const.mul continuousAt_id).prodMk continuousAt_const)
  exact ModularCocycleAux.eq_of_germ (hc₁.mul hc₂) hcJ
    (modularDistribution_germ M hM hc m n z τ h₁.1)

/--
Half-lattice calculation before taking a real fixed point. Retain
the exponential phase; [RW26, p. 3] μ.
Reuses `qPochhammer_doubling_ratio_eq_phase`.
-/
theorem modularDistribution_half_upper (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : 2 ∣ M 1 0) (τ : ℂ) (hτ : 0 < τ.im) :
    modularPhi M 0 (M 1 0 / 2) (1 / 2) τ =
      e ((etaMobius M τ - τ) / 24) *
        (etaMultiplier M / etaMultiplier (modularDouble M hc)) := by
  have hJ := (modularDouble_pos_parity M hM hc).1
  have hdom := upper_mem_modularPhiDomain M hM (⟨τ, hτ⟩ : ℍ)
  have he0 : e 0 = 1 := by simp [e]
  have harg : (e (etaMobius M τ)) ^ (M 1 0 / 2) * e ((1 / 2) / etaDenom M τ) = -1 := by
    simpa only [zero_add, zpow_zero, one_mul, zero_div, he0] using
      (modularDistribution_q_arguments M hc 0 0 0 τ hdom).2
  have hnum : modularPhiQNumerator 0 (1 / 2) τ = qPochhammer (-1) (e τ) := by
    simp only [modularPhiQNumerator, zpow_zero, one_mul, ModularDistributionAux.e_half]
  have hden : modularPhiQDenominator M (M 1 0 / 2) (1 / 2) τ =
      qPochhammer (-1) (e (etaMobius M τ)) := by
    simp only [modularPhiQDenominator, harg]
  have hd := ModularDistributionAux.qPochhammer_neg_one_ne_zero (e (etaMobius M τ))
    (norm_pos_iff.mpr (e_ne_zero _))
    (norm_e_lt_one (⟨etaMobius M τ, ModularCocycleUpperAux.etaMobius_im_pos M hτ⟩ : ℍ))
  rw [modularPhi_eq_qProduct M hM 0 (M 1 0 / 2) (1 / 2) τ hτ (by rwa [hden]),
    modularPhiQProduct, hnum, hden]
  exact qPochhammer_doubling_ratio_eq_phase M (modularDouble M hc) hM hJ
    (modularDouble_entries M hc) (⟨τ, hτ⟩ : ℍ) hd

/--
Balanced common-index shift at an off-lattice center, not a z-germ; [RW26, p. 6, (16)].
The proof uses `modularPhi_diagonal_index_fixedPoint` and off-lattice continuity for regularity.
-/
theorem modularDistribution_index_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ)) (u v k : ℤ) (w : ℂ)
    (hbalance : ((etaDenom M (τ₀ : ℂ))⁻¹ - 1) * w =
      (u : ℂ) * (τ₀ : ℂ) + (v : ℂ))
    (hw : w ∉ modularPhiPseudoLattice (τ₀ : ℂ)) :
    modularPhi M u 0 w (τ₀ : ℂ) = modularPhi M (u + k) k w (τ₀ : ℂ) := by
  have harg : (u : ℂ) * (τ₀ : ℂ) + w = w / etaDenom M (τ₀ : ℂ) - (v : ℂ) := by
    linear_combination -hbalance
  have hphase : (e (τ₀ : ℂ)) ^ u * e w =
      (e (τ₀ : ℂ)) ^ (0 : ℤ) * e (w / etaDenom M (τ₀ : ℂ)) := by
    rw [zpow_zero, one_mul, e_int_mul, ← e_add', harg, sub_eq_add_neg,
      e_add', e_neg', e_intCast]
    simp
  have havoid : ∀ j : ℤ, 1 - (e (τ₀ : ℂ)) ^ (u + j) * e w ≠ 0 := by
    intro j hj
    have heq : (e (τ₀ : ℂ)) ^ (u + j) * e w = 1 := (sub_eq_zero.mp hj).symm
    rw [e_int_mul, ← e_add'] at heq
    obtain ⟨l, hl⟩ := e_eq_one_iff_int heq
    push_cast at hl
    apply hw
    refine ⟨-(u + j), l, ?_⟩
    push_cast
    linear_combination hl
  have hshift := modularPhi_diagonal_index_fixedPoint M hM u 0 k w τ₀ hfix hT hphase havoid
    (by simpa only [zero_add] using
      ModularDistributionAux.continuousAt_z_real_off_lattice M hM (u + k) k τ₀ hT w hw)
    (ModularDistributionAux.continuousAt_z_real_off_lattice M hM u 0 τ₀ hT w hw)
  simpa only [zero_add] using hshift.symm

/--
The two actual half-point values after continuation, including the
index shift needed for E(h). Background: [RW26, p. 12, Lemma 2].
-/
theorem modularDistribution_half_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : 2 ∣ M 1 0) (htrace : 2 < M 0 0 + M 1 1) (τ₀ : ℝ)
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ)) :
    modularPhi M 0 (M 1 0 / 2) (1 / 2) (τ₀ : ℂ) =
        etaMultiplier M / etaMultiplier (modularDouble M hc) ∧
      modularPhi M (-(M 1 0 / 2)) 0 (1 / 2) (τ₀ : ℂ) =
        etaMultiplier M / etaMultiplier (modularDouble M hc) := by
  have hTr : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ) := by simpa [etaDenom] using hT
  have hirr := modularPhi_real_fixedPoint_irrational M hM htrace τ₀ hTr hfix
  have hw := ModularDistributionAux.half_not_mem_pseudoLattice τ₀ hirr
  have hTne : etaDenom M (τ₀ : ℂ) ≠ 0 :=
    ModularCocycleMatrixAux.denom_ne_zero_of_re_pos M (τ₀ : ℂ) hT
  have hcPhi : ContinuousAt (fun τ : ℂ => modularPhi M 0 (M 1 0 / 2) (1 / 2) τ) (τ₀ : ℂ) :=
    (ModularDistributionAux.analyticAt_real_off_lattice M hM 0 (M 1 0 / 2) τ₀ hT (1 / 2) hw).continuousAt.comp
      (f := fun τ : ℂ => (1 / 2, τ)) (continuousAt_const.prodMk continuousAt_id)
  have he : Continuous e := by unfold e; fun_prop
  have hcPhase : ContinuousAt (fun τ : ℂ => e ((etaMobius M τ - τ) / 24) *
      (etaMultiplier M / etaMultiplier (modularDouble M hc))) (τ₀ : ℂ) :=
    (he.continuousAt.comp
      (((ModularCocycleMatrixAux.continuousAt_mobius M (τ₀ : ℂ) hTne).sub continuousAt_id).div_const 24)).mul
      continuousAt_const
  have hfirst : modularPhi M 0 (M 1 0 / 2) (1 / 2) (τ₀ : ℂ) =
      etaMultiplier M / etaMultiplier (modularDouble M hc) := by
    have h := ModularDistributionAux.eq_at_real_of_upper _ _ τ₀ hcPhi hcPhase
      (modularDistribution_half_upper M hM hc)
    simpa only [hfix, sub_self, zero_div, show e 0 = 1 by simp [e], one_mul] using h
  have hca : (2 : ℂ) * ((M 1 0 / 2 : ℤ) : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast Int.mul_ediv_cancel' hc
  have ha : 2 ∣ M 0 0 - 1 := by
    obtain ⟨r, hr⟩ := (ModularDistributionAux.odd_entries M hc).1.exists_bit1
    exact ⟨r, by linarith⟩
  have haa : (2 : ℂ) * (((M 0 0 - 1) / 2 : ℤ) : ℂ) = (M 0 0 : ℂ) - 1 := by
    exact_mod_cast Int.mul_ediv_cancel' ha
  have hinv := ModularCocycleMatrixAux.a_sub_c_fixedPoint M (τ₀ : ℂ) hfix hTne
  have hbalance : ((etaDenom M (τ₀ : ℂ))⁻¹ - 1) * (1 / 2) =
      ((-(M 1 0 / 2) : ℤ) : ℂ) * (τ₀ : ℂ) + (((M 0 0 - 1) / 2 : ℤ) : ℂ) := by
    rw [← hinv]
    push_cast
    linear_combination ((τ₀ : ℂ) / 2) * hca - (1 / 2 : ℂ) * haa
  have hindex := modularDistribution_index_fixedPoint M hM τ₀ hT hfix
    (-(M 1 0 / 2)) ((M 0 0 - 1) / 2) (M 1 0 / 2) (1 / 2) hbalance hw
  refine ⟨hfirst, ?_⟩
  simpa only [neg_add_cancel] using hindex.trans (by simpa only [neg_add_cancel] using hfirst)

#check modularPhi_diagonal_index_fixedPoint
#check etaKappa_pow_twentyFour
#check etaMultiplier_conjugate
#print modularDoubleMatrix
#check modularDistribution_chart_cross_mul
#check modularDistribution_half_fixedPoint

end SICLean.L4
