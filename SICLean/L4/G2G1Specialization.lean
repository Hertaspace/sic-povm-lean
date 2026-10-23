import SICLean.L4.G2ExactTelescoping
import SICLean.L4.G2G1SpecializationAux

set_option autoImplicit false

/-!
Specialization of the G1 interface to n=h=0, p'=p-a, y'=y+aτ+b. [RW26, p. 7, (22), (23), p. 13]. G1
is an explicit premise only of the final two integral statements. The RHS locus and limit-to-center
identifications are independent of G1.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2

open G2G1SpecializationAux

/-- Literal point-value expression after the simultaneous (w,y') limit. It is not the definition of
G1's removable value. -/
def phiRatioRHS (M : SL(2, ℤ)) (u v : ℤ × ℤ) : ℂ :=
  modularPhi M (v.1 + (u.1 + 1)) 1
      ((argument M u : ℂ) + (argument M v : ℂ)) (repellingTau M : ℂ) /
    (modularPhi M v.1 1 (argument M v : ℂ) (repellingTau M : ℂ) *
      modularPhi M (u.1 + 1) 1 (argument M u : ℂ) (repellingTau M : ℂ))

def weightedPhiRHS (M : SL(2, ℤ)) (u v : ℤ × ℤ) : ℂ :=
  modularPhi M (v.1 + (u.1 + 1)) 1
      ((argument M u : ℂ) + (argument M v : ℂ)) (repellingTau M : ℂ) /
    (modularPhi M (v.1 + 1) 1 (argument M v : ℂ) (repellingTau M : ℂ) *
      modularPhi M (u.1 + 1) 1 (argument M u : ℂ) (repellingTau M : ℂ))

/-- s and Y-1 after substitution, hence lower coefficient s+Y-1-ε; [RW26, p. 7, (23), p. 13]. No raw
coefficient is substituted for g1L. -/
theorem g1_specialized_coefficients (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    g1T M (repellingTau M) = epsilon M ∧
    g1S M (repellingTau M) (argument M u) 0 (u.1 + 1) = upperCoefficient M u ∧
    (M 1 0 : ℝ) * translatedY M v + epsilon M * ((v.1 - M 0 0 : ℤ) : ℝ) =
      inverseOffset M v - 1 ∧
    g1L M (repellingTau M) (argument M u) (translatedY M v)
        0 (u.1 + 1) (v.1 - M 0 0) =
      upperCoefficient M u + inverseOffset M v - 1 - epsilon M := by
  obtain ⟨hs, hy⟩ := coefficient_formulas M hM u v
  have ht := fixedPoint_translate M hM
  have hy' : (M 1 0 : ℝ) * translatedY M v +
      epsilon M * ((v.1 - M 0 0 : ℤ) : ℝ) = inverseOffset M v - 1 := by
    unfold translatedY
    push_cast
    nlinarith [hy, ht]
  refine ⟨rfl, hs, hy', ?_⟩
  simp only [g1L, hs, show g1T M (repellingTau M) = epsilon M from rfl]
  nlinarith [hy']

/-- Same etaMultiplier and existing principal Complex.sqrt, whose value at positive ε is the
positive real root; fixed-point eta phase is one; [RW26, p. 7, (23)]. -/
theorem g1_fixed_prefactor (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    g1Prefactor M (repellingTau M : ℂ) =
      (etaMultiplier M)⁻¹ * (Real.sqrt (epsilon M) : ℂ) := by
  simp only [g1Prefactor, repellingTau_fixedPoint M hM, sub_self, zero_div,
    e, mul_zero, Complex.exp_zero, mul_one, etaDenom_repelling]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast (epsilon_pos M hM).le)]
  simp

/-- Exact integer variable shift, valid even for total pole representatives; [RW26, p. 6, p. 13]. -/
theorem g1_translated_denominator (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    modularPhi M (m + (v.1 - M 0 0)) 0
      (z + (translatedY M v : ℂ)) (repellingTau M : ℂ) =
    modularPhi M (m + v.1) 1 (z + (argument M v : ℂ)) (repellingTau M : ℂ) := by
  have h := translate_phi M hM (m + (v.1 - M 0 0)) 0
    (z + (argument M v : ℂ)) (repellingTau M : ℂ)
  convert h using 1 <;> simp [translatedY] <;> congr 1 <;> ring

/-- n=h=0, ell=u₁+1, p'=v₁-a, y'=translatedY, for every component; [RW26, p. 7, (23), p. 13]. -/
theorem ratioKernel_eq_g1 (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    ratioKernel M u v m z =
      g1RatioKernel M (repellingTau M) (argument M u) (translatedY M v)
        0 0 (u.1 + 1) (v.1 - M 0 0) m z := by
  simp only [ratioKernel, g1RatioKernel, g1_translated_denominator M hM,
    ← kernelK_eq_g1]
  exact mul_comm _ _

/-- Actual three output centers are units. Balanced lattice cases for u and u+v are included, not
excluded as extra assumptions; [RW26, p. 12, Lemma 2] and the lattice remark. -/
theorem g1_output_centers_units (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hv : specialValueMk M v ≠ 0) :
    ((argument M u : ℂ) + (argument M v : ℂ), (repellingTau M : ℂ)) ∈
      modularPhiNonvanishingDomain M (v.1 + (u.1 + 1)) 1 ∧
    ((argument M v : ℂ), (repellingTau M : ℂ)) ∈ modularPhiNonvanishingDomain M v.1 1 ∧
    ((argument M u : ℂ), (repellingTau M : ℂ)) ∈
      modularPhiNonvanishingDomain M (u.1 + 1) 1 := by
  have hsum := balanced_unit M hM (u + v) 1
  have hi : (u + v).1 + 1 = v.1 + (u.1 + 1) := by
    simp only [Prod.fst_add]
    ring
  refine ⟨?_, nonzero_class_unit M hM v hv v.1 1, balanced_unit M hM u 1⟩
  simpa only [G2G1SpecializationAux.argument_add, Complex.ofReal_add, hi] using hsum

/-- Joint (w,y') center lies in the locus and the raw RHS is continuous there. Thus limUnder is a
genuine ordinary value, not a bottom-filter choice or a fixed-y' 0/0; [RW26, p. 7, (23)]. -/
theorem g1_ratio_rhs_locus (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hv : specialValueMk M v ≠ 0) :
    ((argument M u : ℂ), (translatedY M v : ℂ)) ∈
      g1RatioRHSLocus M (repellingTau M) 0 (u.1 + 1) (v.1 - M 0 0) ∧
    ContinuousAt (g1RatioRawRHS M (repellingTau M) 0 (u.1 + 1) (v.1 - M 0 0))
      ((argument M u : ℂ), (translatedY M v : ℂ)) := by
  obtain ⟨huv, hv', hu⟩ := g1_output_centers_units M hM u v hv
  have hy : (translatedY M v : ℂ) = (argument M v : ℂ) +
      (M 0 0 : ℂ) * (repellingTau M : ℂ) + (M 0 1 : ℂ) := by
    simp [translatedY]
  have hi : v.1 - M 0 0 + (u.1 + 1) = v.1 + (u.1 + 1) - M 0 0 := by ring
  have hlocus : ((argument M u : ℂ), (translatedY M v : ℂ)) ∈
      g1RatioRHSLocus M (repellingTau M) 0 (u.1 + 1) (v.1 - M 0 0) := by
    simp only [g1RatioRHSLocus, Set.mem_ofPred_eq, neg_zero, sub_zero, hy, hi]
    refine ⟨?_, translated_unit M hM v.1 (argument M v : ℂ) hv', hu⟩
    simpa only [add_assoc] using
      translated_unit M hM (v.1 + (u.1 + 1))
        ((argument M u : ℂ) + (argument M v : ℂ)) huv
  exact ⟨hlocus, ratio_raw_continuousAt M hM _ _ _ _ _ hlocus⟩

/-- Three integer variable shifts after justifying the joint removable value. No G1 input is needed
to identify this defined limit; [RW26, p. 7, (23), p. 13]. -/
theorem g1_ratio_rhs_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hv : specialValueMk M v ≠ 0) :
    G1RatioRemovable M (repellingTau M) (argument M u) (translatedY M v)
        0 (u.1 + 1) (v.1 - M 0 0) ∧
    g1RatioRHS M (repellingTau M) (argument M u) (translatedY M v)
        0 (u.1 + 1) (v.1 - M 0 0) = phiRatioRHS M u v := by
  obtain ⟨hlocus, hc⟩ := g1_ratio_rhs_locus M hM u v hv
  haveI := nhdsWithin_neBot_of_mem hlocus
  have ht : Tendsto
      (g1RatioRawRHS M (repellingTau M) 0 (u.1 + 1) (v.1 - M 0 0))
      (𝓝[g1RatioRHSLocus M (repellingTau M) 0 (u.1 + 1) (v.1 - M 0 0)]
        ((argument M u : ℂ), (translatedY M v : ℂ)))
      (𝓝 (g1RatioRawRHS M (repellingTau M) 0 (u.1 + 1) (v.1 - M 0 0)
        ((argument M u : ℂ), (translatedY M v : ℂ)))) :=
    hc.continuousWithinAt.tendsto
  have heq : g1RatioRHS M (repellingTau M) (argument M u) (translatedY M v)
      0 (u.1 + 1) (v.1 - M 0 0) =
      g1RatioRawRHS M (repellingTau M) 0 (u.1 + 1) (v.1 - M 0 0)
        ((argument M u : ℂ), (translatedY M v : ℂ)) := ht.limUnder_eq
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · rw [heq]
    exact ht
  · rw [heq]
    have hn := g1_translated_denominator M hM v (u.1 + 1) (argument M u : ℂ)
    have hd := g1_translated_denominator M hM v 0 0
    simp only [zero_add] at hd
    simp only [g1RatioRawRHS, phiRatioRHS, neg_zero, sub_zero]
    rw [add_comm (v.1 - M 0 0) (u.1 + 1), hn, hd]
    rw [add_comm (u.1 + 1) v.1]

/-- Single RHS also keeps its actual removable center, including u=0; [RW26, p. 7, (22), p. 13]. -/
theorem g1_single_rhs_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    G1SingleRemovable M (repellingTau M) (argument M u) 0 (u.1 + 1) ∧
    g1SingleRHS M (repellingTau M) (argument M u) 0 (u.1 + 1) =
      (modularPhi M (u.1 + 1) 1 (argument M u : ℂ) (repellingTau M : ℂ))⁻¹ := by
  have hlocus : (argument M u : ℂ) ∈
      g1SingleRHSLocus M (repellingTau M) 0 (u.1 + 1) := by
    simpa only [g1SingleRHSLocus, Set.mem_ofPred_eq, sub_zero] using balanced_unit M hM u 1
  have hc := single_raw_continuousAt M hM _ _ _ _ hlocus
  haveI := nhdsWithin_neBot_of_mem hlocus
  have ht : Tendsto (g1SingleRawRHS M (repellingTau M) 0 (u.1 + 1))
      (𝓝[g1SingleRHSLocus M (repellingTau M) 0 (u.1 + 1)] (argument M u : ℂ))
      (𝓝 (g1SingleRawRHS M (repellingTau M) 0 (u.1 + 1) (argument M u : ℂ))) :=
    hc.continuousWithinAt.tendsto
  have heq : g1SingleRHS M (repellingTau M) (argument M u) 0 (u.1 + 1) =
      g1SingleRawRHS M (repellingTau M) 0 (u.1 + 1) (argument M u : ℂ) :=
    ht.limUnder_eq
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · rw [heq]
    exact ht
  · simpa only [g1SingleRawRHS, sub_zero] using heq

/-- Every hypothesis for every j is exhibited, including all components. Separation is the exhibited
`G1Separates` condition, and tails come from the named estimates, not from a new field of hG1;
[RW26, p. 13]. -/
theorem g1_eligible_each_j (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    0 < M 1 0 ∧ 0 < g1T M (repellingTau M) ∧
    0 < g1S M (repellingTau M) (argument M u) 0 (u.1 + 1) ∧
    g1L M (repellingTau M) (argument M u) (translatedY M v)
      0 (u.1 + 1) (v.1 - M 0 0) < 0 ∧
    g1NoPinch M (repellingTau M) (translatedY M v) (v.1 - M 0 0) ∧
    ∀ m : Fin (M 1 0).toNat,
      G1Separates (componentChain M D (m : ℤ) (j : ℤ))
        (g1NumeratorPoles M (repellingTau M) 0 (m : ℤ))
        (g1InversePoles M (repellingTau M) (translatedY M v)
          0 (v.1 - M 0 0) (m : ℤ)) := by
  obtain ⟨_, _, hs, hl⟩ := raw_and_final_windows M hM u v hwin
  refine ⟨hM.1, epsilon_pos M hM, hs, hl,
    translated_noPinch M hM u v hwin, ?_⟩
  intro m
  exact componentChain_g1_separates M hM u v hwin δ D hD (m : ℤ) j

/-- Each fixed j gives one G1 sum over all m, not c² individual G1 evaluations; [RW26, p. 7, (23),
p. 13]. -/
theorem g1_ratio_integral_each_j (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    (∀ m : Fin (M 1 0).toNat,
      G1ChainIntegrable (componentChain M D (m : ℤ) (j : ℤ)) (ratioKernel M u v (m : ℤ))) ∧
    (∑ m : Fin (M 1 0).toNat,
      g1ChainIntegral (componentChain M D (m : ℤ) (j : ℤ)) (ratioKernel M u v (m : ℤ))) =
      (etaMultiplier M)⁻¹ * (Real.sqrt (epsilon M) : ℂ) * phiRatioRHS M u v := by
  obtain ⟨hc, hT, hs, hl, hpinch, hsep⟩ :=
    g1_eligible_each_j M hM u v hwin δ D hD j
  have hcall := ((hG1 M (repellingTau M) hc hT).2
    0 0 (u.1 + 1) (v.1 - M 0 0) (argument M u) (translatedY M v)
    hs hl hpinch).2.2 (fun m => componentChain M D (m : ℤ) (j : ℤ)) hsep
  have hk (m : Fin (M 1 0).toNat) :
      ratioKernel M u v (m : ℤ) =
        g1RatioKernel M (repellingTau M) (argument M u) (translatedY M v)
          0 0 (u.1 + 1) (v.1 - M 0 0) (m : ℤ) :=
    funext (ratioKernel_eq_g1 M hM u v (m : ℤ))
  refine ⟨fun m => ?_, ?_⟩
  · rw [hk]
    exact hcall.1 m
  · simp_rw [hk]
    rw [hcall.2, g1_fixed_prefactor M hM,
      (g1_ratio_rhs_value M hM u v hv).2]

/-- (1-t)/Φ_{p,1}(y)=1/Φ_{p+1,1}(y), with legitimate cancellation on the nonzero class. [RW26, p. 6]
index equations; [RW26, p. 13]. -/
theorem weighted_rhs_shift (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hv : specialValueMk M v ≠ 0) :
    (1 - phaseT M v) * phiRatioRHS M u v = weightedPhiRHS M u v := by
  have hv0 := nonzero_class_unit M hM v hv v.1 1
  have hv1 := nonzero_class_unit M hM v hv (v.1 + 1) 1
  have hc0 := ContinuousAt.comp (f := fun z : ℂ => (z, (repellingTau M : ℂ)))
    (continuousAt_of_unit M hM v.1 1 _ hv0)
    (continuousAt_id.prodMk continuousAt_const)
  have hc1 := ContinuousAt.comp (f := fun z : ℂ => (z, (repellingTau M : ℂ)))
    (continuousAt_of_unit M hM (v.1 + 1) 1 _ hv1)
    (continuousAt_id.prodMk continuousAt_const)
  have ht : 1 - phaseT M v ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (phase_ne_one M hM v hv))
  have hf : 1 - (e (repellingTau M : ℂ)) ^ v.1 * e (argument M v : ℂ) ≠ 0 := by
    rwa [argument_phase M hM v]
  have hcf : ContinuousAt (fun z : ℂ =>
      1 - (e (repellingTau M : ℂ)) ^ v.1 * e z) (argument M v : ℂ) := by
    unfold e
    fun_prop
  have hrec := ModularCocycleAux.eq_of_germ hc1 (hc0.div hcf hf)
    (modularPhi_index_m_germ M hM.1 v.1 1 (argument M v : ℂ)
      (repellingTau M : ℂ) hv0.1)
  change modularPhi M (v.1 + 1) 1 (argument M v : ℂ) (repellingTau M : ℂ) =
    modularPhi M v.1 1 (argument M v : ℂ) (repellingTau M : ℂ) /
      (1 - (e (repellingTau M : ℂ)) ^ v.1 * e (argument M v : ℂ)) at hrec
  rw [argument_phase M hM v] at hrec
  have hb := ne_zero_of_unit M hM v.1 1 _ hv0
  have hu := ne_zero_of_unit M hM (u.1 + 1) 1 _ (balanced_unit M hM u 1)
  unfold phiRatioRHS weightedPhiRHS
  rw [hrec]
  field_simp [hb, hu, ht]

/-- The weighted value for each intermediate j, ready for finite summing; [RW26, p. 13]. -/
theorem weighted_integral_each_j (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    (1 - phaseT M v) * (∑ m : Fin (M 1 0).toNat,
      g1ChainIntegral (componentChain M D (m : ℤ) (j : ℤ)) (ratioKernel M u v (m : ℤ))) =
      (etaMultiplier M)⁻¹ * (Real.sqrt (epsilon M) : ℂ) * weightedPhiRHS M u v := by
  rw [(g1_ratio_integral_each_j hG1 M hM u v hwin hv δ D hD j).2]
  rw [← mul_assoc, mul_comm (1 - phaseT M v), mul_assoc,
    weighted_rhs_shift M hM u v hv]

#print g1_specialized_coefficients
#print g1RatioRHS
#check g1_ratio_rhs_value
#check g1_eligible_each_j
#check g1_ratio_integral_each_j

end SICLean.L4.G2
