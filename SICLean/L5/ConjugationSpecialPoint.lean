import SICLean.L5.ConjugationModular
import SICLean.L4.SpecialValueReflection

set_option autoImplicit false

/-!
# Conjugation at the actual attracting Φ centers

Sources: [RW26, p. 2, (2); p. 3, (3); Prop. 1, p. 6; Lemma 2, p. 12;
Prop. 7, Cor. 1, p. 14]; [RW-rec, Prop. 2, (7), p. 4].

The argument, Φ, and μ are the functions already defined. Regularity, the
balanced index exchange, and reflection are the inputs. The exchange
(1-u₁, 1) → (-u₁, 0) is used at the actual off-lattice center. It is a
point identity. The lattice-center value is the branch `specialValuePlus`.
-/

noncomputable section

open Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L5.ConjugationSpecialPoint

open SICLean.L4

/-- The special argument is a real quotient. [RW26, p. 2, (2)]. -/
theorem specialValueArgument_ofReal (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    specialValueArgument M u =
      ((((u.1 : ℝ) * specialValueTau M + (u.2 : ℝ)) /
        ((specialValueEpsilon M)⁻¹ - 1) : ℝ) : ℂ) := by
  simp [specialValueArgument, modularPhiSpecialArgument, specialValue_etaDenom]

/-- Same sources: actual attracting arguments are fixed by conjugation. -/
theorem specialValueArgument_conj (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    (starRingEnd ℂ) (specialValueArgument M u) = specialValueArgument M u := by
  simp only [specialValueArgument_ofReal, Complex.conj_ofReal]

/-- Same sources: label negation negates the actual argument. -/
theorem specialValueArgument_neg (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    specialValueArgument M (-u) = -specialValueArgument M u := by
  simp only [specialValueArgument, modularPhiSpecialArgument, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

/-- Joint regularity gives continuity at this center. [RW26, Lemma 2, p. 12]. -/
theorem specialValuePhi_continuous (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    ContinuousAt (fun z => modularPhi M u.1 0 z (specialValueTau M : ℂ))
      (specialValueArgument M u) := by
  have hreg := (specialValuePhi_joint_regular M hM u hu 0).1.continuousAt
  have hmap : ContinuousAt (fun z : ℂ => (z, (specialValueTau M : ℂ)))
      (specialValueArgument M u) := by fun_prop
  simpa only [Function.comp_def, add_zero] using
    ContinuousAt.comp (f := fun z : ℂ => (z, (specialValueTau M : ℂ))) hreg hmap

/-- Both actual centers are required to evaluate the product germ.
Same sources, applied to -u with diagonal shift 1. -/
theorem specialValuePhi_reflected_continuous (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    ContinuousAt (fun z => modularPhi M (1 - u.1) 1 z (specialValueTau M : ℂ))
      (-specialValueArgument M u) := by
  have hnu : -u ∉ specialValueLattice M := by
    intro h
    exact hu (by simpa using neg_mem h)
  have hreg := (specialValuePhi_joint_regular M hM (-u) hnu 1).1
  rw [specialValueArgument_neg] at hreg
  have hidx : (-u).1 + 1 = 1 - u.1 := by
    simp only [Prod.fst_neg]
    ring
  rw [hidx] at hreg
  have hmap : ContinuousAt (fun z : ℂ => (z, (specialValueTau M : ℂ)))
      (-specialValueArgument M u) := by fun_prop
  simpa only [Function.comp_def] using
    ContinuousAt.comp (f := fun z : ℂ => (z, (specialValueTau M : ℂ)))
      hreg.continuousAt hmap

/-- Conjugation at the attracting center, before the index exchange.
[RW26, p. 5; Prop. 7, p. 14]. -/
theorem specialValuePhi_conj_reflected (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    (starRingEnd ℂ)
      (modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ)) =
      (modularPhi M (1 - u.1) 1 (-specialValueArgument M u) (specialValueTau M : ℂ))⁻¹ := by
  have hT : 0 < (M 1 0 : ℝ) * specialValueTau M + (M 1 1 : ℝ) :=
    lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)
  have hR : ContinuousAt
      (fun z => modularPhi M (1 - u.1) (1 - 0) z (specialValueTau M : ℂ))
      (-((starRingEnd ℂ) (specialValueArgument M u))) := by
    simpa only [sub_zero, specialValueArgument_conj] using
      specialValuePhi_reflected_continuous M hM u hu
  simpa only [sub_zero, specialValueArgument_conj] using
    ConjugationModular.modularPhi_conj M hM.1 u.1 0 (specialValueArgument M u)
      (specialValueTau M) hT (specialValuePhi_continuous M hM u hu) hR

/-- Apply `specialValue_reflection_index` at this center. [RW26, p. 12]. -/
theorem specialValuePhi_conj_neg (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    (starRingEnd ℂ)
      (modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ)) =
      (modularPhi M (-u.1) 0 (specialValueArgument M (-u)) (specialValueTau M : ℂ))⁻¹ := by
  rw [specialValuePhi_conj_reflected M hM u hu, specialValue_reflection_index M hM u hu]

/-- Conjugation of μΦ off the lattice.
[RW26, Prop. 7, p. 14]; [RW-rec, Prop. 2, (7), p. 4]. -/
theorem specialValueRaw_conj_inv (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    (starRingEnd ℂ) (specialValueRaw M u) = (specialValueRaw M (-u))⁻¹ := by
  simp only [specialValueRaw, map_mul, ConjugationPhase.etaMultiplier_conj M hM.1,
    specialValuePhi_conj_neg M hM u hu, Prod.fst_neg, mul_inv]

/-- Same sources, the off-lattice reciprocal in multiplication form. -/
theorem specialValueRaw_conj_mul (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    (starRingEnd ℂ) (specialValueRaw M u) * specialValueRaw M (-u) = 1 := by
  have hnu : -u ∉ specialValueLattice M := by
    intro h
    exact hu (by simpa using neg_mem h)
  have hphi := (specialValuePhi_joint_regular M hM (-u) hnu 0).2
  have hraw : specialValueRaw M (-u) ≠ 0 := by
    apply mul_ne_zero (etaMultiplier_ne_zero M hM.1)
    simpa only [add_zero] using hphi
  rw [specialValueRaw_conj_inv M hM u hu, inv_mul_cancel₀ hraw]

/-- Inversion of the reflection phase selects the positive Gaussian.
[RW26, p. 3, (3); Prop. 1, p. 6]. -/
theorem specialValue_conjugation_phase (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    (-1 : ℂ) ^ u.1 * e (-modularReflectionPolynomial M u.1 0
      (specialValueArgument M u) (specialValueTau M : ℂ)) = specialValueGaussianLift M u := by
  have hsign : ((-1 : ℂ) ^ u.1)⁻¹ = (-1 : ℂ) ^ u.1 := by
    rw [← inv_zpow, inv_neg_one]
  have h := congrArg (fun z : ℂ => z⁻¹) (specialValue_reflection_phase M hM u)
  simpa only [mul_inv, hsign, ← e_neg', inv_inv] using h

/-- The off-lattice Gaussian formula.
[RW26, Cor. 1, (28), p. 14]; [RW-rec, Prop. 2, (7), p. 4]. -/
theorem specialValueRaw_conj_gaussian (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    (starRingEnd ℂ) (specialValueRaw M u) =
      specialValueGaussianLift M u * specialValueRaw M u := by
  have hraw : specialValueRaw M (-u) ≠ 0 := by
    intro hzero
    have h := specialValueRaw_conj_mul M hM u hu
    rw [hzero, mul_zero] at h
    exact zero_ne_one h
  apply mul_right_cancel₀ hraw
  rw [specialValueRaw_conj_mul M hM u hu, mul_assoc,
    specialValueRaw_reflection M hM u hu,
    mul_inv_cancel₀ (specialValueGaussianLift_ne_zero M u)]

/-- For Φ alone the identity retains the factor μ².
[RW26, Prop. 7, Cor. 1, p. 14]. -/
theorem specialValuePhi_conj_phase (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    (starRingEnd ℂ)
      (modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ)) =
      etaMultiplier M ^ 2 * specialValueGaussianLift M u *
        modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ) := by
  have h := congrArg (fun z : ℂ => etaMultiplier M * z)
    (specialValueRaw_conj_gaussian M hM u hu)
  simp only [specialValueRaw, map_mul, ConjugationPhase.etaMultiplier_conj M hM.1] at h
  calc
    (starRingEnd ℂ)
        (modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ)) =
        etaMultiplier M * ((etaMultiplier M)⁻¹ * (starRingEnd ℂ)
          (modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ))) := by
      rw [← mul_assoc, mul_inv_cancel₀ (etaMultiplier_ne_zero M hM.1), one_mul]
    _ = etaMultiplier M * (specialValueGaussianLift M u * (etaMultiplier M *
        modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ))) := h
    _ = etaMultiplier M ^ 2 * specialValueGaussianLift M u *
        modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ) := by ring

#print SICLean.L4.specialValueRaw
#print SICLean.L4.specialValueArgument
#check SICLean.L4.specialValuePhi_joint_regular
#check SICLean.L4.specialValue_reflection_index
#check SICLean.L4.specialValue_reflection_phase
#check specialValueRaw_conj_gaussian

end SICLean.L5.ConjugationSpecialPoint
