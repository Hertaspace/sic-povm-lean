import SICLean.L4.G1ContinuationBoundary
import SICLean.L4.EtaMultiplier

set_option autoImplicit false

/-!
# The exact eta prefactor at a real G1 endpoint

The definitions of `g1Prefactor`, `etaPhase`, `etaMultiplier`, `etaDenom`,
and `etaMobius` are used literally. `etaPhase` has no conditional branch: it is the explicit
eta-free expression everywhere, with holomorphy asserted on its slit domain. No new phase,
square-root branch, or q-product representative is introduced. G1 uses the actual
`modularPhi`/`phiExtended`.

The eta-free prefactor has an ordinary complex-neighborhood limit and hence both upper and lower
limits. The q-product expression is identified and limited only from the upper half-plane. Nothing
here asserts a nonzero real-axis limit of either separate infinite product or of eta itself.

[RW26, p. 3, p. 7, (22), (23), p. 29, Appendix A.2]. The prefactor retains the phase e((gamma tau -
tau)/24). The full-neighborhood and lower-side statements are included.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology MatrixGroups UpperHalfPlane

namespace SICLean.L4.G1RealEtaPhase

/-- E01. Algebraic bridge between the real T in the interface and the actual complex eta
denominator. [RW26, p. 3, p. 7, (22), (23)]. -/
theorem etaDenom_real_eq_g1T (M : SL(2, ℤ)) (τ₀ : ℝ) :
    etaDenom M (τ₀ : ℂ) = (g1T M τ₀ : ℂ) := by
  simp [etaDenom, g1T]

/-- E02. Positive real T lies inside the principal-square-root domain; neither the denominator nor
its principal square root vanishes. [RW26, p. 3, p. 7]. These are domain checks for the prefactor.
-/
theorem real_positive_domain_and_nonzero (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT : 0 < g1T M τ₀) :
    (τ₀ : ℂ) ∈ etaPhaseDomain M ∧
      etaDenom M (τ₀ : ℂ) ∈ Complex.slitPlane ∧
      etaDenom M (τ₀ : ℂ) ≠ 0 ∧
      Complex.sqrt (etaDenom M (τ₀ : ℂ)) ≠ 0 := by
  have hmem : (τ₀ : ℂ) ∈ etaPhaseDomain M := real_mem_etaPhaseDomain M τ₀ hT
  have hslit : etaDenom M (τ₀ : ℂ) ∈ Complex.slitPlane := hmem
  have hne : etaDenom M (τ₀ : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hslit
  refine ⟨hmem, hslit, hne, ?_⟩
  rw [Complex.sqrt]
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl hne)

/-- E03. The existing principal complex square root has the positive-real numerical value. [RW26, p.
7, (22), (23)]. No alternative square-root branch is chosen. -/
theorem sqrt_etaDenom_real (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT : 0 < g1T M τ₀) :
    Complex.sqrt (etaDenom M (τ₀ : ℂ)) = (Real.sqrt (g1T M τ₀) : ℂ) := by
  simpa [etaDenom, g1T] using
    EtaMultiplierAux.sqrt_affine_real (M 1 0) (M 1 1) τ₀ hT

/-- E04. The G1 contract and the existing eta-free phase use exactly the same actual multiplier and
principal square root, even as total functions. [RW26, p. 3, p. 7]. The current `etaPhase`
definition has no condition to discharge. -/
theorem g1Prefactor_eq_etaPhase (M : SL(2, ℤ)) (τ : ℂ) :
    g1Prefactor M τ = etaPhase M τ := by
  rfl

/-- E05. The eta-free G1 prefactor is a unit on its ordinary slit domain. [RW26, p. 3, p. 7, (22),
(23)]. -/
theorem prefactor_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : τ ∈ etaPhaseDomain M) :
    g1Prefactor M τ ≠ 0 := by
  have hslit : etaDenom M τ ∈ Complex.slitPlane := hτ
  have hsqrt : Complex.sqrt (etaDenom M τ) ≠ 0 := by
    rw [Complex.sqrt]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hslit))
  unfold g1Prefactor
  exact mul_ne_zero
    (mul_ne_zero (inv_ne_zero (etaMultiplier_ne_zero M hM)) hsqrt) (e_ne_zero _)

/-- E06. Holomorphy is asserted on an ordinary complex domain, including both sides of every
positive-T real point. [RW26, p. 3, p. 7]. -/
theorem prefactor_analyticOnNhd (M : SL(2, ℤ)) :
    AnalyticOnNhd ℂ (g1Prefactor M) (etaPhaseDomain M) := by
  rw [funext (g1Prefactor_eq_etaPhase M)]
  exact etaPhase_analyticOnNhd M

/-- E07. A concrete ordinary ball around a positive-T real point carries the same analytic,
nowhere-zero prefactor. [RW26, p. 7]. The neighborhood is a full ball. -/
theorem real_prefactor_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (hT : 0 < g1T M τ₀) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball (τ₀ : ℂ) ρ ⊆ etaPhaseDomain M ∧
      AnalyticOnNhd ℂ (g1Prefactor M) (Metric.ball (τ₀ : ℂ) ρ) ∧
      ∀ τ ∈ Metric.ball (τ₀ : ℂ) ρ, g1Prefactor M τ ≠ 0 := by
  have hmem : (τ₀ : ℂ) ∈ etaPhaseDomain M := real_mem_etaPhaseDomain M τ₀ hT
  rcases Metric.isOpen_iff.mp (etaPhaseDomain_isOpen M) _ hmem with ⟨ρ, hρ, hball⟩
  exact ⟨ρ, hρ, hball, (prefactor_analyticOnNhd M).mono hball,
    fun τ hτ => prefactor_ne_zero M hM τ (hball hτ)⟩

/-- E08. Exact real value of the prefactor in both G1 identities. [RW26, p. 7, (22), (23)]. The
phase factor is retained. -/
theorem prefactor_real_formula (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT : 0 < g1T M τ₀) :
    g1Prefactor M (τ₀ : ℂ) =
      (etaMultiplier M)⁻¹ * (Real.sqrt (g1T M τ₀) : ℂ) *
        e ((etaMobius M (τ₀ : ℂ) - (τ₀ : ℂ)) / 24) := by
  unfold g1Prefactor
  rw [sqrt_etaDenom_real M τ₀ hT]

/-- E09. Ordinary continuity needed for multiplying either G1 boundary limit. [RW26, p. 7, p. 29].
The two-sided neighborhood is justified by the eta-free expression. -/
theorem prefactor_continuousAt_real (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT : 0 < g1T M τ₀) :
    ContinuousAt (g1Prefactor M) (τ₀ : ℂ) := by
  exact (prefactor_analyticOnNhd M _ (real_mem_etaPhaseDomain M τ₀ hT)).continuousAt

/-- E10. The exact eta transformation rewritten with the G1 contract prefactor, before division.
[RW26, p. 3, p. 29, Appendix A.2]. -/
theorem upper_qProduct_mul_eq_prefactor (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℍ) :
    etaDenom M τ * qPochhammer (e τ) (e τ) =
      g1Prefactor M τ *
        qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) := by
  rw [g1Prefactor_eq_etaPhase]
  exact qPochhammer_eta_prefactor_mul M hM τ

/-- E11. The two products are separately nonzero only at upper-half-plane parameters here; this
licenses the accurate quotient identity there. [RW26, p. 28, (55), (56), p. 29]. No nonzero
real-boundary limit of either separate product is asserted. -/
theorem upper_qProducts_nonzero_and_prefactor (M : SL(2, ℤ))
    (hM : 0 < M 1 0) (τ : ℍ) :
    qPochhammer (e τ) (e τ) ≠ 0 ∧
      qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) ≠ 0 ∧
      etaDenom M τ *
        (qPochhammer (e τ) (e τ) /
          qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))) =
        g1Prefactor M τ := by
  have h1 : qPochhammer (e (τ : ℂ)) (e (τ : ℂ)) ≠ 0 :=
    qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _)) (norm_e_lt_one τ)
  have h2 : qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) ≠ 0 := by
    rw [← coe_smul_eq_etaMobius]
    exact qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _)) (norm_e_lt_one (M • τ))
  exact ⟨h1, h2, by
    rw [g1Prefactor_eq_etaPhase]
    exact qPochhammer_eta_prefactor M hM τ h2⟩

/-- E12. Bridge from the upper residue-summation output to the exact G1 contract prefactor. [RW26,
p. 29, Appendix A.2]. The existing interface is `UpperResidueParameters.prefactor`. -/
theorem upper_prefactor_eq_g1Prefactor (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) :
    UpperResidueParameters.prefactor M τ = g1Prefactor M τ := by
  let τ' : ℍ := ⟨τ, hτ⟩
  have h2 : qPochhammer (e (etaMobius M τ')) (e (etaMobius M τ')) ≠ 0 := by
    rw [← coe_smul_eq_etaMobius]
    exact qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _)) (norm_e_lt_one (M • τ'))
  have h := qPochhammer_eta_prefactor M hM τ' h2
  unfold UpperResidueParameters.prefactor
  rw [mul_div_assoc, g1Prefactor_eq_etaPhase]
  simpa only [τ'] using h

/-- E13. The eta-free prefactor tends to the same contract value in the ordinary complex
neighborhood and from either half-plane. [RW26, p. 7, p. 29]. It makes no assertion about
lower-half-plane q products. -/
theorem prefactor_tendsto_real_and_sides (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT : 0 < g1T M τ₀) :
    Tendsto (g1Prefactor M) (𝓝 (τ₀ : ℂ)) (𝓝 (g1Prefactor M (τ₀ : ℂ))) ∧
      Tendsto (g1Prefactor M)
        (𝓝[UpperHalfPlane.upperHalfPlaneSet] (τ₀ : ℂ))
        (𝓝 (g1Prefactor M (τ₀ : ℂ))) ∧
      Tendsto (g1Prefactor M) (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ))
        (𝓝 (g1Prefactor M (τ₀ : ℂ))) := by
  have hc : ContinuousAt (g1Prefactor M) (τ₀ : ℂ) :=
    prefactor_continuousAt_real M τ₀ hT
  exact ⟨hc.tendsto, hc.tendsto.mono_left nhdsWithin_le_nhds,
    hc.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- E14. The named upper-product prefactor and its literal q-product quotient both tend from above
to the real prefactor of the G1 contract. [RW26, p. 29, p. 7]. Eta is eliminated before the limit is
taken. -/
theorem upper_qProduct_prefactor_tendsto_real (M : SL(2, ℤ))
    (hM : 0 < M 1 0) (τ₀ : ℝ) (hT : 0 < g1T M τ₀) :
    Tendsto (UpperResidueParameters.prefactor M)
      (𝓝[UpperHalfPlane.upperHalfPlaneSet] (τ₀ : ℂ))
      (𝓝 (g1Prefactor M (τ₀ : ℂ))) ∧
      Tendsto
        (fun τ : ℂ => etaDenom M τ *
          (qPochhammer (e τ) (e τ) /
            qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))))
        (𝓝[UpperHalfPlane.upperHalfPlaneSet] (τ₀ : ℂ))
        (𝓝 (g1Prefactor M (τ₀ : ℂ))) := by
  have hbase : Tendsto (g1Prefactor M)
      (𝓝[UpperHalfPlane.upperHalfPlaneSet] (τ₀ : ℂ))
      (𝓝 (g1Prefactor M (τ₀ : ℂ))) :=
    (prefactor_continuousAt_real M τ₀ hT).tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨hbase.congr' ?_, hbase.congr' ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with τ hτmem
    exact (upper_prefactor_eq_g1Prefactor M hM τ hτmem).symm
  · filter_upwards [self_mem_nhdsWithin] with τ hτmem
    exact (upper_qProducts_nonzero_and_prefactor M hM ⟨τ, hτmem⟩).2.2.symm

-- The imported definitions and the downstream bridges.
#print g1T
#print g1Prefactor
#print etaPhase
#print etaMultiplier
#print UpperResidueParameters.prefactor
#check @qPochhammer_eta_prefactor
#check @etaPhase_tendsto_real
#check @qPochhammer_eta_prefactor_tendsto_real
#check @real_prefactor_neighborhood
#check @upper_prefactor_eq_g1Prefactor
#check @prefactor_tendsto_real_and_sides
#check @upper_qProduct_prefactor_tendsto_real

end SICLean.L4.G1RealEtaPhase
