import SICLean.L5.ConjugationStrip
import SICLean.L5.ConjugationContinuationAux
import SICLean.L4.ModularPhi

set_option autoImplicit false

/-!
# Continued φ and the S factor

Sources: [RW26, p. 5; p. 6; Prop. 7, p. 14].

Germs below are punctured germs in one complex variable. At a pole the
representative `phiExtended` has value zero. A germ identity stays off that
center, so the product of the two center values is a separate statement.
Pointwise multiplication excludes both zeros and poles. The canonical
continuation chart is unchanged. At a half-integer tie the reflected chart
is `-k`, and chart independence identifies it with the original chart.
-/

noncomputable section

open Complex Set Filter
open scoped Topology ComplexOrder

namespace SICLean.L5.ConjugationContinuation

open SICLean.L4

/-- Divisor symmetry under conjugation. [RW26, p. 5], in the (m, n) indexing. -/
theorem phiPolePoint_conj (b : ℝ) (m n : ℕ) :
    (starRingEnd ℂ) (phiPolePoint (b : ℂ) m n) = phiZeroPoint (b : ℂ) m n := by
  simp [phiPolePoint, phiZeroPoint, map_ofNat]
  ring

/-- Same sources, the opposite divisor branch. -/
theorem phiZeroPoint_conj (b : ℝ) (m n : ℕ) :
    (starRingEnd ℂ) (phiZeroPoint (b : ℂ) m n) = phiPolePoint (b : ℂ) m n := by
  rw [phiZeroPoint, map_neg, phiPolePoint_conj, phiZeroPoint, neg_neg]

/-- Same sources, with multiplicities retained at collisions (e.g. b=1). -/
theorem phiPoleMultiplicity_conj (b : ℝ) (hb : 0 < b) (z : ℂ) :
    phiPoleMultiplicity (b : ℂ) ((starRingEnd ℂ) z) =
      phiZeroMultiplicity (b : ℂ) z := by
  have hindices : phiPoleIndices (b : ℂ) ((starRingEnd ℂ) z) =
      phiZeroIndices (b : ℂ) z := by
    ext mn
    change (starRingEnd ℂ) z = phiPolePoint (b : ℂ) mn.1 mn.2 ↔
      z = phiZeroPoint (b : ℂ) mn.1 mn.2
    constructor <;> intro h
    · simpa only [starRingEnd_self_apply, phiPolePoint_conj] using
        congrArg (starRingEnd ℂ) h
    · simpa only [phiZeroPoint_conj] using congrArg (starRingEnd ℂ) h
  unfold phiPoleMultiplicity phiZeroMultiplicity
  rw [hindices]

/-- Same sources. Multiplicities are retained for real parameters. -/
theorem phiZeroMultiplicity_conj (b : ℝ) (hb : 0 < b) (z : ℂ) :
    phiZeroMultiplicity (b : ℂ) ((starRingEnd ℂ) z) =
      phiPoleMultiplicity (b : ℂ) z := by
  simpa only [starRingEnd_self_apply] using
    (phiPoleMultiplicity_conj b hb ((starRingEnd ℂ) z)).symm

/-- The reflected chart is `-k`. [RW26, p. 5]. -/
theorem shiftedArgument_conj (b : ℝ) (z : ℂ) (k : ℤ) :
    (starRingEnd ℂ) (shiftedArgument (b : ℂ) z k) =
      shiftedArgument (b : ℂ) ((starRingEnd ℂ) z) (-k) := by
  exact ConjugationContinuationAux.shiftedArgument_conj b z k

/-- The reflected function is meromorphic: conjugation is applied to both
the source and the target. [RW26, p. 5].
Conjugation of the target alone is antiholomorphic. -/
theorem phiExtended_reflected_meromorphic (b : ℝ) (hb : 0 < b) :
    MeromorphicOn
      (fun z : ℂ => (starRingEnd ℂ) (phiExtended (b : ℂ) ((starRingEnd ℂ) z)))
      Set.univ := by
  have hfun : (fun z : ℂ =>
      (starRingEnd ℂ) (phiExtended (b : ℂ) ((starRingEnd ℂ) z))) =
      (fun z : ℂ => (phiExtended (b : ℂ) z)⁻¹) := by
    funext z
    simpa only [starRingEnd_self_apply] using
      ConjugationContinuationAux.phiExtended_conj_total b hb ((starRingEnd ℂ) z)
  rw [hfun]
  exact (phiExtended_meromorphic (b : ℂ)
    (ConjugationStrip.admissibleB_of_real b hb)).inv

/-- Germ form of the conjugation identity. [RW26, p. 5].
The center value is not evaluated. -/
theorem phiExtended_conj_germ (b : ℝ) (hb : 0 < b) (z : ℂ) :
    (fun w : ℂ => (starRingEnd ℂ) (phiExtended (b : ℂ) w)) =ᶠ[𝓝[≠] z]
      (fun w => (phiExtended (b : ℂ) ((starRingEnd ℂ) w))⁻¹) := by
  exact Filter.Eventually.of_forall
    (ConjugationContinuationAux.phiExtended_conj_total b hb)

/-- Same sources, now at a regular nonzero center. Both divisor
conditions are explicit; the reflected conditions follow from symmetry. -/
theorem phiExtended_conj (b : ℝ) (hb : 0 < b) (z : ℂ)
    (hp : phiPoleMultiplicity (b : ℂ) z = 0)
    (hz : phiZeroMultiplicity (b : ℂ) z = 0) :
    (starRingEnd ℂ) (phiExtended (b : ℂ) z) =
      (phiExtended (b : ℂ) ((starRingEnd ℂ) z))⁻¹ := by
  exact ConjugationContinuationAux.phiExtended_conj_total b hb z

/-- Same sources, safe point-value multiplication form. -/
theorem phiExtended_conj_mul (b : ℝ) (hb : 0 < b) (z : ℂ)
    (hp : phiPoleMultiplicity (b : ℂ) z = 0)
    (hz : phiZeroMultiplicity (b : ℂ) z = 0) :
    (starRingEnd ℂ) (phiExtended (b : ℂ) z) *
      phiExtended (b : ℂ) ((starRingEnd ℂ) z) = 1 := by
  have hne : phiExtended (b : ℂ) ((starRingEnd ℂ) z) ≠ 0 :=
    (phiExtended_ne_zero_iff (b : ℂ) ((starRingEnd ℂ) z)
      (ConjugationStrip.admissibleB_of_real b hb)
      (by rwa [phiPoleMultiplicity_conj b hb])).mpr
      (by rwa [phiZeroMultiplicity_conj b hb])
  rw [phiExtended_conj b hb z hp hz, inv_mul_cancel₀ hne]

/-- Same sources, once nonvanishing is known. The pole value of φ is the
existing one. -/
theorem phiExtended_conj_of_ne_zero (b : ℝ) (hb : 0 < b) (z : ℂ)
    (hz : phiExtended (b : ℂ) z ≠ 0) :
    (starRingEnd ℂ) (phiExtended (b : ℂ) z) =
      (phiExtended (b : ℂ) ((starRingEnd ℂ) z))⁻¹ := by
  have hab := ConjugationStrip.admissibleB_of_real b hb
  have hp : phiPoleMultiplicity (b : ℂ) z = 0 := by
    by_contra hp
    exact hz (phiExtended_pole_value (b : ℂ) z hab hp)
  exact phiExtended_conj b hb z hp ((phiExtended_ne_zero_iff (b : ℂ) z hab hp).mp hz)

/-- On the real axis the continued value has modulus 1. [RW26, p. 5]. -/
theorem norm_phiExtended_real (b : ℝ) (hb : 0 < b) (x : ℝ) :
    ‖phiExtended (b : ℂ) (x : ℂ)‖ = 1 := by
  have hab := ConjugationStrip.admissibleB_of_real b hb
  have hx : InStrip (b : ℂ) (x : ℂ) := by
    simp only [InStrip, Complex.ofReal_im, abs_zero, stripWidth]
    have hbi := admissibleB_inv (b : ℂ) hab
    change 0 < ((b : ℂ).re + ((b : ℂ)⁻¹).re) / 2
    exact half_pos (add_pos hab hbi)
  rw [phiExtended_eq_phi (b : ℂ) (x : ℂ) hab hx]
  exact ConjugationStrip.norm_phi_real b hb x

/-- The S-factor reflection. [RW26, p. 5].
The reflected argument is σ - 1 - conj ζ. -/
theorem modularPhiSArgument_conj (σ : ℝ) (hσ : 0 < σ) (ζ : ℂ) :
    (starRingEnd ℂ) (modularPhiSArgument (σ : ℂ) ζ) =
      modularPhiSArgument (σ : ℂ) ((σ : ℂ) - 1 - (starRingEnd ℂ) ζ) := by
  have hsqrt : Complex.sqrt (σ : ℂ) = (Real.sqrt σ : ℂ) := by
    simpa using Complex.sqrt_of_nonneg (show (0 : ℂ) ≤ (σ : ℂ) by exact_mod_cast hσ.le)
  have hne : (Real.sqrt σ : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hσ).ne'
  have hsq : (Real.sqrt σ : ℂ) ^ 2 = (σ : ℂ) := by
    exact_mod_cast Real.sq_sqrt hσ.le
  simp only [modularPhiSArgument, hsqrt, map_add, map_sub, map_div₀,
    map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  rw [← hsq]
  field_simp
  ring

/-- Same sources: the S-factor identity first as a punctured ζ-germ.
This includes arguments outside the original Faddeev strip. -/
theorem modularPhiS_conj_germ (σ : ℝ) (hσ : 0 < σ) (ζ : ℂ) :
    (fun w : ℂ => (starRingEnd ℂ) (modularPhiS w (σ : ℂ))) =ᶠ[𝓝[≠] ζ]
      (fun w => (modularPhiS ((σ : ℂ) - 1 - (starRingEnd ℂ) w) (σ : ℂ))⁻¹) := by
  have hsqrt : Complex.sqrt (σ : ℂ) = (Real.sqrt σ : ℂ) := by
    simpa using Complex.sqrt_of_nonneg (show (0 : ℂ) ≤ (σ : ℂ) by exact_mod_cast hσ.le)
  apply Filter.Eventually.of_forall
  intro w
  change (starRingEnd ℂ) (phiExtended (Complex.sqrt (σ : ℂ))
    (modularPhiSArgument (σ : ℂ) w)) = _
  rw [hsqrt, ConjugationContinuationAux.phiExtended_conj_total
    (Real.sqrt σ) (Real.sqrt_pos.mpr hσ), modularPhiSArgument_conj σ hσ]
  simp only [modularPhiS, hsqrt]

/-- Same sources, at a nonzero regular S-factor center.
A raw total value at a pole stays off the meromorphic value. -/
theorem modularPhiS_conj (σ : ℝ) (hσ : 0 < σ) (ζ : ℂ)
    (hp : phiPoleMultiplicity (Complex.sqrt (σ : ℂ))
      (modularPhiSArgument (σ : ℂ) ζ) = 0)
    (hz : phiZeroMultiplicity (Complex.sqrt (σ : ℂ))
      (modularPhiSArgument (σ : ℂ) ζ) = 0) :
    (starRingEnd ℂ) (modularPhiS ζ (σ : ℂ)) =
      (modularPhiS ((σ : ℂ) - 1 - (starRingEnd ℂ) ζ) (σ : ℂ))⁻¹ := by
  have hsqrt : Complex.sqrt (σ : ℂ) = (Real.sqrt σ : ℂ) := by
    simpa using Complex.sqrt_of_nonneg (show (0 : ℂ) ≤ (σ : ℂ) by exact_mod_cast hσ.le)
  have h := phiExtended_conj (Real.sqrt σ) (Real.sqrt_pos.mpr hσ)
    (modularPhiSArgument (σ : ℂ) ζ)
    (by simpa only [hsqrt] using hp) (by simpa only [hsqrt] using hz)
  simpa only [modularPhiS, hsqrt, modularPhiSArgument_conj σ hσ] using h

#print SICLean.L4.phiExtended
#check SICLean.L4.phiExtended_eq_phiChart
#check SICLean.L4.phiExtended_unique_germ
#check SICLean.L4.phiExtended_pole_value
#check modularPhiS_conj

end SICLean.L5.ConjugationContinuation
