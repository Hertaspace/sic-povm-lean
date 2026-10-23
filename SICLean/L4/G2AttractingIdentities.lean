import SICLean.L4.G2DegenerateParameters

set_option autoImplicit false

/-!
# Attracting actual values and the general-matrix statement

The proofs use the upstream G2 interfaces. As in [RW26, p. 13], the
other fixed point is treated in the same way. This file checks the positive-c, slit, eta, and origin
conditions.

The two existing iff theorems transport the derived repelling identities. Reflection (5) is exactly
specialValue_mixed_reflection and is not redeclared or added as a premise. MatrixPentagon is only
the explicit proposition. It chooses no values or witnesses.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4

/-- The full actual-value formula, including -N A at (0,0). Admissibility is quantified inside the
proposition, so that one can use a single theorem `∀ M, MatrixPentagon M` for all of its
representative matrices. [RW26, (7), p. 3]. -/
def MatrixPentagon (M : SL(2, ℤ)) : Prop :=
  ∀ hM : SpecialValueAdmissible M, ∀ u v : SpecialValueGroup M,
    G2.SpecialValueBridge.normalizedValueSum M hM
      (fun x => specialValuePairing M hM x u *
        (specialValuePlus M hM x / specialValueMinus M hM (x + v))) =
    specialValuePlus M hM (u + v) / (specialValueMinus M hM u * specialValueMinus M hM v) -
      (if u = 0 ∧ v = 0 then (specialValueOrder M : ℂ) * specialValuePlus M hM 0 else 0)

namespace G2.AttractingIdentities

open ReflectionGeometry SpecialValueBridge

/-- Same positive c, reflected repelling τ, and reciprocal positive ε. [RW26, p. 2, p. 13]. -/
theorem reflection_parameters (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < (modularInverseReflection M) 1 0 ∧
      repellingTau (modularInverseReflection M) = -specialValueTau M ∧
      0 < epsilon (modularInverseReflection M) ∧
      epsilon (modularInverseReflection M) < 1 ∧
      epsilon (modularInverseReflection M) = (specialValueEpsilon M)⁻¹ := by
  have hR := reflection_admissible M hM
  have hparams := reflection_repelling_parameters M hM
  exact ⟨hR.1, hparams.1, epsilon_pos _ hR, epsilon_lt_one _ hR, hparams.2⟩

/-- Both slit-domain memberships, with both actual positive denominators. The proof uses the
existing principal
Complex.sqrt convention, not a negative-c Φ. [RW26, p. 2, §2.2, p. 6]. -/
theorem reflection_slit_domains (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (specialValueTau M : ℂ) ∈ modularPhiDomain M ∧
      -(specialValueTau M : ℂ) ∈ modularPhiDomain (modularInverseReflection M) ∧
      etaDenom M (specialValueTau M : ℂ) = (specialValueEpsilon M : ℂ) ∧
      etaDenom (modularInverseReflection M) (-(specialValueTau M : ℂ)) =
        (specialValueEpsilon M : ℂ)⁻¹ := by
  have hdom := specialValueTau_mem_domain M hM
  have hR := modularInverseReflection_domain M hM.1 (specialValueTau M : ℂ) hdom
  rw [specialValueTau_fixedPoint M hM, specialValue_etaDenom M] at hR
  exact ⟨hdom, hR.2.2.1, specialValue_etaDenom M, hR.2.1⟩

/-- Exact equality of the same etaMultiplier, including c=1; no equality merely up to an eighth root
of unity. [RW26, p. 3]. -/
theorem reflection_multiplier (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    etaMultiplier (modularInverseReflection M) = etaMultiplier M := by
  exact etaMultiplier_inverse_reflection M hM.1

/-- Plus and minus origins are treated separately; they are never interchanged. [RW26, (4), p. 3].
-/
theorem reflection_origins (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    repellingPlus (modularInverseReflection M) (reflection_admissible M hM) 0 =
        (Real.sqrt (specialValueEpsilon M) : ℂ) ∧
      repellingMinus (modularInverseReflection M) (reflection_admissible M hM) 0 =
        (Real.sqrt (specialValueEpsilon M) : ℂ)⁻¹ ∧
      specialValuePlus M hM 0 =
        repellingPlus (modularInverseReflection M) (reflection_admissible M hM) 0 ∧
      specialValueMinus M hM 0 =
        repellingMinus (modularInverseReflection M) (reflection_admissible M hM) 0 := by
  have hzero := repellingValues_zero (modularInverseReflection M) (reflection_admissible M hM)
  rw [(reflection_repelling_parameters M hM).2, Real.sqrt_inv,
    Complex.ofReal_inv, inv_inv] at hzero
  have hvalues := attractingValues_from_repelling M hM 0
  exact ⟨hzero.1, hzero.2, by simpa only [map_zero] using hvalues.1,
    by simpa only [map_zero] using hvalues.2⟩

/-- Apply attracting_fourier_iff_repelling to SingleFinite.repelling_fourier. One etaMultiplier M
works for every u. [RW26, (6), p. 3, p. 13]. -/
theorem attracting_fourier (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ∀ u : SpecialValueGroup M,
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u * specialValuePlus M hM x) =
        etaMultiplier M / specialValueMinus M hM u := by
  exact (attracting_fourier_iff_repelling M hM).mpr
    (SingleFinite.repelling_fourier hG1 _ (reflection_admissible M hM))

/-- Explicit u=0 specialization with the prescribed minus origin. [RW26, (6), p. 3, (4)]. -/
theorem attracting_fourier_origin (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    normalizedValueSum M hM (fun x => specialValuePairing M hM x 0 * specialValuePlus M hM x) =
      etaMultiplier M / specialValueMinus M hM 0 := by
  exact attracting_fourier hG1 M hM 0

/-- Apply attracting_pentagon_iff_repelling to the full identity. No restriction of (u,v) is made
before transport. [RW26, (7), p. 3]. -/
theorem attracting_pentagon (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ∀ u v : SpecialValueGroup M,
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
        (specialValuePlus M hM x / specialValueMinus M hM (x + v))) =
      specialValuePlus M hM (u + v) / (specialValueMinus M hM u * specialValueMinus M hM v) -
        (if u = 0 ∧ v = 0 then (specialValueOrder M : ℂ) * specialValuePlus M hM 0 else 0) := by
  exact (attracting_pentagon_iff_repelling M hM).mpr
    (DegenerateParameters.repelling_pentagon hG1 _ (reflection_admissible M hM))

/-- Both explicit origin calculations survive the actual-value bridge. No analytic input is needed
for this algebraic special case. [RW26, (7), p. 3]. -/
theorem attracting_pentagon_origin (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    normalizedValueSum M hM (fun x => specialValuePairing M hM x 0 *
      (specialValuePlus M hM x / specialValueMinus M hM (x + 0))) =
        specialValuePlus M hM 0 + (Real.sqrt (specialValueOrder M : ℝ) : ℂ) ∧
      specialValuePlus M hM 0 ^ 3 -
          (specialValuePlus M hM 0 + (Real.sqrt (specialValueOrder M : ℝ) : ℂ)) =
        (specialValueOrder M : ℂ) * specialValuePlus M hM 0 := by
  have hsum :
      normalizedValueSum M hM (fun x => specialValuePairing M hM x 0 *
        (specialValuePlus M hM x / specialValueMinus M hM (x + 0))) =
      normalizedValueSum (modularInverseReflection M) (reflection_admissible M hM)
        (fun x => specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
          x 0 * (repellingPlus (modularInverseReflection M) (reflection_admissible M hM) x /
            repellingMinus (modularInverseReflection M) (reflection_admissible M hM) (x + 0))) := by
    unfold normalizedValueSum
    rw [reflection_order]
    congr 1
    apply G2SpecialValueBridgeAux.sum_reflection M hM
    intro x
    simp only [add_zero]
    rw [← (attractingValues_from_repelling M hM x).1,
      ← (attractingValues_from_repelling M hM x).2]
    congr 1
    simpa only [map_zero] using (reflection_pairing M hM x 0).symm
  have hplus := (reflection_origins M hM).2.2.1
  constructor
  · rw [hsum]
    simpa only [reflection_order, ← hplus] using
      DegenerateParameters.ratio_sum_origin (modularInverseReflection M)
        (reflection_admissible M hM)
  · simpa only [reflection_order, ← hplus] using
      DegenerateParameters.origin_cubic_correction (modularInverseReflection M)
        (reflection_admissible M hM)

/-- Now restrict the full formula, in exactly the `_of_sums` call shape. [RW26, (7), p. 3, p. 13].
-/
theorem attracting_pentagon_off_origin (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ∀ u v : SpecialValueGroup M, (u, v) ≠ (0, 0) →
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
        (specialValuePlus M hM x / specialValueMinus M hM (x + v))) =
      specialValuePlus M hM (u + v) / (specialValueMinus M hM u * specialValueMinus M hM v) := by
  intro u v huv
  have hne : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨rfl, rfl⟩
    exact huv rfl
  simpa only [if_neg hne, sub_zero] using attracting_pentagon hG1 M hM u v

end G2.AttractingIdentities

/-- General-matrix statement for FamilyPentagon: instantiate at every allowed representative matrix,
with
no Theorem 2, Prop. 8 or sum premises. [RW26, (7), p. 3, p. 13]. -/
theorem matrixPentagon_of_G1 (hG1 : G1RealConclusion) :
    ∀ M : SL(2, ℤ), MatrixPentagon M := by
  intro M hM
  exact G2.AttractingIdentities.attracting_pentagon hG1 M hM

#check @G2.SpecialValueBridge.attracting_fourier_iff_repelling
#check @G2.SpecialValueBridge.attracting_pentagon_iff_repelling
#check @specialValue_mixed_reflection
#print MatrixPentagon
#check @matrixPentagon_of_G1

end SICLean.L4
