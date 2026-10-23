import SICLean.L4.G2ContourChain
import SICLean.L4.ModularCocycle
import SICLean.L4.FaddeevSectorDecay
import SICLean.L4.G2RawKernelAux

set_option autoImplicit false

/-!
Concrete raw kernels and named fixed real-parameter estimates. [RW26].

The estimates below are derived from the named ModularSector estimates, ultimately based on
Sector.phiExtended_uniform_sector_decay, the finite product modularPhi, and
modularPhi_reflection_germ plus the divisor/unit API. They are not fields of G1RealConclusion. No
two-sided parameter limit is needed here. The raw quotient is a total representative; kernel
difference identities are germs first. Their center values at comb roots are not asserted.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2

def shiftLength (M : SL(2, ℤ)) : ℝ := length M / (M 1 0 : ℝ)

def translate (M : SL(2, ℤ)) : ℝ :=
  (M 0 0 : ℝ) * repellingTau M + (M 0 1 : ℝ)

def phaseT (M : SL(2, ℤ)) (v : ℤ × ℤ) : ℂ :=
  e ((argument M v : ℂ) / (epsilon M : ℂ))

def combU (M : SL(2, ℤ)) (m : ℤ) (z : ℂ) : ℂ :=
  (e (repellingTau M : ℂ)) ^ m * e z

def combV (M : SL(2, ℤ)) (z : ℂ) : ℂ := e (z / (epsilon M : ℂ))

def kernelK (M : SL(2, ℤ)) (u : ℤ × ℤ) (m : ℤ) (z : ℂ) : ℂ :=
  e ((((M 1 0 : ℂ) * z + (epsilon M : ℂ) * (m : ℂ)) *
      (argument M u : ℂ)) / (epsilon M : ℂ) +
    ((u.1 + 1 : ℤ) : ℂ) * (z + (m : ℂ) * (repellingTau M : ℂ)))

/-- [RW26, p. 13]. -/
def rawF (M : SL(2, ℤ)) (u v : ℤ × ℤ) (m : ℤ) (z : ℂ) : ℂ :=
  kernelK M u m z / (combV M z - combU M m z) *
    (modularPhi M m 0 z (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 0 (z + (argument M v : ℂ)) (repellingTau M : ℂ))

/-- Single-function raw g_m, to be used with bent lower tails. [RW26, p. 13]. No assertion of
absolute convergence on a vertical lower tail is made. -/
def rawG (M : SL(2, ℤ)) (u : ℤ × ℤ) (m : ℤ) (z : ℂ) : ℂ :=
  kernelK M u m z / (combV M z - combU M m z) *
    modularPhi M m 0 z (repellingTau M : ℂ)

def ratioKernel (M : SL(2, ℤ)) (u v : ℤ × ℤ) (m : ℤ) (z : ℂ) : ℂ :=
  kernelK M u m z * (modularPhi M (m + 1) 0 z (repellingTau M : ℂ) /
    modularPhi M (m + v.1) 1 (z + (argument M v : ℂ)) (repellingTau M : ℂ))

def singleKernel (M : SL(2, ℤ)) (u : ℤ × ℤ) (m : ℤ) (z : ℂ) : ℂ :=
  kernelK M u m z * modularPhi M (m + 1) 0 z (repellingTau M : ℂ)

def rawUpperRate (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℝ :=
  (upperCoefficient M u - epsilon M) / epsilon M

def rawLowerRate (M : SL(2, ℤ)) (u v : ℤ × ℤ) : ℝ :=
  (upperCoefficient M u + inverseOffset M v - 1) / epsilon M

def finalLowerRate (M : SL(2, ℤ)) (u v : ℤ × ℤ) : ℝ :=
  (upperCoefficient M u + inverseOffset M v - 1 - epsilon M) / epsilon M

/-- [RW26, p. 13]. Includes zero classes; only phase_ne_one needs a nonzero class. -/
theorem argument_phase (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    (e (repellingTau M : ℂ)) ^ x.1 * e (argument M x : ℂ) = phaseT M x := by
  have he : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have hl : (epsilon M)⁻¹ - 1 ≠ 0 := by
    have he1 := epsilon_lt_one M hM
    intro hz
    have : epsilon M = 1 := by
      field_simp [he] at hz
      linarith
    linarith
  have hx : argument M x / epsilon M =
      (x.1 : ℝ) * repellingTau M + argument M x + (x.2 : ℝ) := by
    unfold argument
    have he1 : 1 - epsilon M ≠ 0 := ne_of_gt (sub_pos.mpr (epsilon_lt_one M hM))
    field_simp [he, hl, he1]
    ring
  unfold phaseT
  rw [e_int_mul, ← e_add']
  have hxC : (argument M x : ℂ) / (epsilon M : ℂ) =
      (x.1 : ℂ) * (repellingTau M : ℂ) + (argument M x : ℂ) + (x.2 : ℂ) := by
    exact_mod_cast hx
  rw [hxC]
  simp only [e_add', e_intCast, mul_one]

/-- [RW26, p. 7, (22), (23)]. -/
theorem kernelK_eq_g1 (M : SL(2, ℤ)) (u : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    kernelK M u m z = e (g1Exponent M (repellingTau M : ℂ)
      (argument M u : ℂ) z 0 0 (u.1 + 1) m) := by
  simp [kernelK, g1Exponent, etaDenom, epsilon, g1T]

/-- [RW26, p. 13]. -/
theorem kernelK_norm (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    ‖kernelK M u m z‖ =
      Real.exp (-2 * Real.pi * (upperCoefficient M u / epsilon M) * z.im) := by
  have he : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have hs := (coefficient_formulas M hM u u).1
  have hcoef : (M 1 0 : ℝ) * argument M u + ((u.1 : ℝ) + 1) * epsilon M =
      upperCoefficient M u := by
    simpa only [g1S, epsilon, Int.cast_add, Int.cast_one, Int.cast_zero, add_zero] using hs
  rw [kernelK, G2RawKernelAux.rawKernel_norm_e]
  congr 1
  simp only [Complex.add_im, Complex.mul_im, Complex.div_ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, mul_zero, add_zero, zero_add]
  push_cast
  field_simp
  linear_combination -z.im * hcoef

/-- Named fixed-τ upper estimate, derived from the proved Sector.phiExtended_uniform_sector_decay
and finite factorization; [RW26, p. 6, (19), p. 7, Lemma 1]. Point values and inverses. -/
theorem fixed_phi_upper_estimate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (F : Finset (ℤ × ℤ)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ i ∈ F, ∀ z : ℂ, |z.re| ≤ B → R ≤ z.im →
        (z, (repellingTau M : ℂ)) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ‖modularPhi M i.1 i.2 z (repellingTau M : ℂ) - 1‖ +
          ‖(modularPhi M i.1 i.2 z (repellingTau M : ℂ))⁻¹ - 1‖ ≤
            C * Real.exp (-κ * z.im) := by
  exact G2RawKernelAux.fixed_phi_upper_estimate M hM F B hB

/-- Named lower estimate: the preceding upper estimate + reflection and actual-center regularity. No
hidden G1 premise; [RW26, p. 6, Prop. 1]. -/
theorem fixed_phi_lower_estimate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (F : Finset (ℤ × ℤ)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ i ∈ F, ∀ z : ℂ, |z.re| ≤ B → z.im ≤ -R →
        (z, (repellingTau M : ℂ)) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ‖modularPhi M i.1 i.2 z (repellingTau M : ℂ) /
          modularReflectionFactor M i.1 i.2 z (repellingTau M : ℂ) - 1‖ +
        ‖modularReflectionFactor M i.1 i.2 z (repellingTau M : ℂ) *
          (modularPhi M i.1 i.2 z (repellingTau M : ℂ))⁻¹ - 1‖ ≤
            C * Real.exp (κ * z.im) := by
  exact G2RawKernelAux.fixed_phi_lower_estimate M hM F B hB

/-- Quadratic terms cancel; the remaining coefficient is Y/ε; [RW26, p. 6, Prop. 1, p. 13] ratio
calculation. -/
theorem raw_reflection_ratio_norm (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    ‖modularReflectionFactor M m 0 z (repellingTau M : ℂ) /
      modularReflectionFactor M (m + v.1) 0 (z + (argument M v : ℂ))
        (repellingTau M : ℂ)‖ =
      Real.exp (-2 * Real.pi * (inverseOffset M v / epsilon M) * z.im) := by
  have he : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have hv := (coefficient_formulas M hM v v).2
  rw [G2RawKernelAux.rawKernel_reflection_norm M hM]
  congr 1
  rw [Complex.sub_im, G2RawKernelAux.rawKernel_polynomial_im M hM, G2RawKernelAux.rawKernel_polynomial_im M hM]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    add_zero, Int.cast_add, Int.cast_zero]
  field_simp
  linear_combination -2 * z.im * hv

/-- The final quotient coefficient is (Y-1-ε)/ε, not (Y-1)/ε; [RW26, p. 7, (23), p. 13]. Uses the
same reflection factor as above. -/
theorem final_reflection_ratio_norm (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    ‖modularReflectionFactor M (m + 1) 0 z (repellingTau M : ℂ) /
      modularReflectionFactor M (m + v.1) 1 (z + (argument M v : ℂ))
        (repellingTau M : ℂ)‖ =
      Real.exp (-2 * Real.pi *
        ((inverseOffset M v - 1 - epsilon M) / epsilon M) * z.im) := by
  have he : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have hv := (coefficient_formulas M hM v v).2
  rw [G2RawKernelAux.rawKernel_reflection_norm M hM]
  congr 1
  rw [Complex.sub_im, G2RawKernelAux.rawKernel_polynomial_im M hM, G2RawKernelAux.rawKernel_polynomial_im M hM]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    add_zero, Int.cast_add, Int.cast_one, Int.cast_zero]
  field_simp
  linear_combination -2 * z.im * hv

/-- [RW26, p. 13]. -/
theorem raw_rate_formulas (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    rawUpperRate M u = (sIndex M u : ℝ) / length M ∧
      rawLowerRate M u v =
        ((sIndex M u + sIndex M v - specialValueOrder M : ℤ) : ℝ) / length M := by
  have he : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have hl : length M ≠ 0 := ne_of_gt (length_pos M hM)
  have hsq := length_sq M hM
  constructor
  · unfold rawUpperRate upperCoefficient scale
    field_simp
    ring
  · unfold rawLowerRate upperCoefficient inverseOffset scale
    push_cast
    field_simp
    dsimp [length] at *
    nlinarith

/-- Exact G1 p',y' substitution; [RW26, p. 7, (23), p. 13]. -/
theorem final_rate_formula (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    g1L M (repellingTau M) (argument M u) (translatedY M v)
        0 (u.1 + 1) (v.1 - M 0 0) / epsilon M = finalLowerRate M u v ∧
      finalLowerRate M u v = rawLowerRate M u v - 1 := by
  have he : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have hs := (coefficient_formulas M hM u v).1
  have hv := (coefficient_formulas M hM u v).2
  have ht := fixedPoint_translate M hM
  constructor
  · unfold finalLowerRate g1L
    rw [hs]
    unfold translatedY
    change (upperCoefficient M u +
      (M 1 0 : ℝ) * (argument M v + (M 0 0 : ℝ) * repellingTau M + (M 0 1 : ℝ)) +
      (((v.1 - M 0 0 : ℤ) : ℝ) - 1) * epsilon M) / epsilon M = _
    push_cast
    congr 1
    linear_combination hv + ht
  · unfold finalLowerRate rawLowerRate
    field_simp

/-- Global point identity from the exact integer variable shift, including the prescribed total
representatives; [RW26, p. 12, p. 13]. -/
theorem rawF_period (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    rawF M u v (m + M 1 0) (z - (epsilon M : ℂ)) = rawF M u v m z := by
  have heps : (epsilon M : ℂ) = (M 1 0 : ℂ) * (repellingTau M : ℂ) + (M 1 1 : ℂ) := by
    simp [epsilon, g1T]
  have hK : kernelK M u (m + M 1 0) (z - (epsilon M : ℂ)) = kernelK M u m z := by
    unfold kernelK
    have heq :
        (((M 1 0 : ℂ) * (z - (epsilon M : ℂ)) + (epsilon M : ℂ) * ((m + M 1 0 : ℤ) : ℂ)) *
          (argument M u : ℂ)) / (epsilon M : ℂ) +
          ((u.1 + 1 : ℤ) : ℂ) * (z - (epsilon M : ℂ) + ((m + M 1 0 : ℤ) : ℂ) * (repellingTau M : ℂ)) =
        ((((M 1 0 : ℂ) * z + (epsilon M : ℂ) * (m : ℂ)) *
          (argument M u : ℂ)) / (epsilon M : ℂ) +
          ((u.1 + 1 : ℤ) : ℂ) * (z + (m : ℂ) * (repellingTau M : ℂ))) +
          ((-((u.1 + 1) * M 1 1) : ℤ) : ℂ) := by
      push_cast
      rw [heps]
      ring
    rw [heq, e_add', e_intCast, mul_one]
  have hU : combU M (m + M 1 0) (z - (epsilon M : ℂ)) = combU M m z := by
    unfold combU
    simp only [e_int_mul, ← e_add']
    have heq : ((m + M 1 0 : ℤ) : ℂ) * (repellingTau M : ℂ) + (z - (epsilon M : ℂ)) =
        ((m : ℂ) * (repellingTau M : ℂ) + z) + ((-(M 1 1) : ℤ) : ℂ) := by
      push_cast
      rw [heps]
      ring
    rw [heq, e_add', e_intCast, mul_one]
  have hV : combV M (z - (epsilon M : ℂ)) = combV M z := by
    unfold combV
    have hene : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
    rw [sub_div, div_self hene, sub_eq_add_neg, e_add']
    have hneg : e (-1 : ℂ) = 1 := by simpa using e_intCast (-1)
    rw [hneg, mul_one]
  unfold rawF
  rw [hK, hU, hV, G2RawKernelAux.modularPhi_period M hM m 0 z]
  have hidx : m + M 1 0 + v.1 = m + v.1 + M 1 0 := by ring
  have hz' : z - (epsilon M : ℂ) + (argument M v : ℂ) =
      (z + (argument M v : ℂ)) - (epsilon M : ℂ) := by ring
  rw [hidx, hz', G2RawKernelAux.modularPhi_period M hM (m + v.1) 0
    (z + (argument M v : ℂ))]

/-- Single-function companion; same source as rawF_period, [RW26, p. 13]. -/
theorem rawG_period (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    rawG M u (m + M 1 0) (z - (epsilon M : ℂ)) = rawG M u m z := by
  have heps : (epsilon M : ℂ) = (M 1 0 : ℂ) * (repellingTau M : ℂ) + (M 1 1 : ℂ) := by
    simp [epsilon, g1T]
  have hK : kernelK M u (m + M 1 0) (z - (epsilon M : ℂ)) = kernelK M u m z := by
    unfold kernelK
    have heq :
        (((M 1 0 : ℂ) * (z - (epsilon M : ℂ)) + (epsilon M : ℂ) * ((m + M 1 0 : ℤ) : ℂ)) *
          (argument M u : ℂ)) / (epsilon M : ℂ) +
          ((u.1 + 1 : ℤ) : ℂ) * (z - (epsilon M : ℂ) + ((m + M 1 0 : ℤ) : ℂ) * (repellingTau M : ℂ)) =
        ((((M 1 0 : ℂ) * z + (epsilon M : ℂ) * (m : ℂ)) *
          (argument M u : ℂ)) / (epsilon M : ℂ) +
          ((u.1 + 1 : ℤ) : ℂ) * (z + (m : ℂ) * (repellingTau M : ℂ))) +
          ((-((u.1 + 1) * M 1 1) : ℤ) : ℂ) := by
      push_cast
      rw [heps]
      ring
    rw [heq, e_add', e_intCast, mul_one]
  have hU : combU M (m + M 1 0) (z - (epsilon M : ℂ)) = combU M m z := by
    unfold combU
    simp only [e_int_mul, ← e_add']
    have heq : ((m + M 1 0 : ℤ) : ℂ) * (repellingTau M : ℂ) + (z - (epsilon M : ℂ)) =
        ((m : ℂ) * (repellingTau M : ℂ) + z) + ((-(M 1 1) : ℤ) : ℂ) := by
      push_cast
      rw [heps]
      ring
    rw [heq, e_add', e_intCast, mul_one]
  have hV : combV M (z - (epsilon M : ℂ)) = combV M z := by
    unfold combV
    have hene : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
    rw [sub_div, div_self hene, sub_eq_add_neg, e_add']
    have hneg : e (-1 : ℂ) = 1 := by simpa using e_intCast (-1)
    rw [hneg, mul_one]
  unfold rawG
  rw [hK, hU, hV, G2RawKernelAux.modularPhi_period M hM m 0 z]

/-- Both multipliers are q, hence cancel in the quotient. [RW26, p. 13]. -/
theorem translated_phase_factors (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    kernelK M u (m + 1 - M 0 0) (z + (translate M : ℂ)) =
        e (repellingTau M : ℂ) * kernelK M u m z ∧
      combV M (z + (translate M : ℂ)) -
          combU M (m + 1 - M 0 0) (z + (translate M : ℂ)) =
        e (repellingTau M : ℂ) * (combV M z - combU M m z) := by
  have he : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have heC : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast he
  have hl : (epsilon M)⁻¹ - 1 ≠ 0 := by
    intro hz
    have he1 := epsilon_lt_one M hM
    field_simp [he] at hz
    linarith
  have ha : (epsilon M - 1) * argument M u =
      -((u.1 : ℝ) * repellingTau M + (u.2 : ℝ)) * epsilon M := by
    have hx : argument M u * ((epsilon M)⁻¹ - 1) =
        (u.1 : ℝ) * repellingTau M + (u.2 : ℝ) := by
      unfold argument
      exact div_mul_cancel₀ _ hl
    field_simp [he] at hx
    linear_combination -hx
  have haC : ((epsilon M : ℂ) - 1) * (argument M u : ℂ) =
      -((u.1 : ℂ) * (repellingTau M : ℂ) + (u.2 : ℂ)) * (epsilon M : ℂ) := by
    exact_mod_cast ha
  have htC : (M 1 0 : ℂ) *
      ((M 0 0 : ℂ) * (repellingTau M : ℂ) + (M 0 1 : ℂ)) =
      (M 0 0 : ℂ) * (epsilon M : ℂ) - 1 := by
    exact_mod_cast fixedPoint_translate M hM
  have hE : ((((M 1 0 : ℂ) * (z + (translate M : ℂ)) +
        (epsilon M : ℂ) * ((m + 1 - M 0 0 : ℤ) : ℂ)) *
        (argument M u : ℂ)) / (epsilon M : ℂ) +
      ((u.1 + 1 : ℤ) : ℂ) * ((z + (translate M : ℂ)) +
        ((m + 1 - M 0 0 : ℤ) : ℂ) * (repellingTau M : ℂ))) =
      ((((M 1 0 : ℂ) * z + (epsilon M : ℂ) * (m : ℂ)) *
        (argument M u : ℂ)) / (epsilon M : ℂ) +
      ((u.1 + 1 : ℤ) : ℂ) * (z + (m : ℂ) * (repellingTau M : ℂ))) +
      (repellingTau M : ℂ) + (((u.1 + 1) * M 0 1 - u.2 : ℤ) : ℂ) := by
    dsimp [translate]
    push_cast
    field_simp [heC]
    linear_combination (argument M u : ℂ) * htC + haC
  have hV : combV M (z + (translate M : ℂ)) =
      e (repellingTau M : ℂ) * combV M z := by
    have htdiv : (translate M : ℂ) / (epsilon M : ℂ) = (repellingTau M : ℂ) := by
      simpa only [etaMobius, etaDenom, epsilon, g1T, translate,
        Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using
        repellingTau_fixedPoint M hM
    simp only [combV, add_div, htdiv, e_add']
    ring
  have hU : combU M (m + 1 - M 0 0) (z + (translate M : ℂ)) =
      e (repellingTau M : ℂ) * combU M m z := by
    have hUE : (((m + 1 - M 0 0 : ℤ) : ℂ) * (repellingTau M : ℂ)) +
        (z + (translate M : ℂ)) =
        (repellingTau M : ℂ) + ((m : ℂ) * (repellingTau M : ℂ) + z) + (M 0 1 : ℂ) := by
      simp only [translate, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_intCast]
      push_cast
      ring
    simp only [combU, e_int_mul]
    rw [← e_add', hUE]
    simp only [e_add', e_intCast, mul_one]
  constructor
  · simp only [kernelK, hE, e_add', e_intCast, mul_one]
    ring
  · rw [hV, hU, mul_sub]

/-- Meromorphic identity, not a point identity at a comb zero; [RW26, p. 13]. -/
theorem rawF_difference_germ (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (z : ℂ) (m : ℤ) :
    (fun ζ => rawF M u v m ζ -
      rawF M u v (m + 1 - M 0 0) (ζ + (translate M : ℂ))) =ᶠ[𝓝[≠] z]
      (fun ζ => (1 - phaseT M v) * ratioKernel M u v m ζ) := by
  have hene : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
  have heone : (epsilon M : ℂ) ≠ 1 := by exact_mod_cast (epsilon_lt_one M hM).ne
  have hinv : (epsilon M : ℂ)⁻¹ ≠ 1 := inv_ne_one.mpr heone
  have hτ : (repellingTau M : ℂ) ∈ modularPhiDomain M :=
    real_mem_modularPhiDomain M _ (epsilon_pos M hM)
  have heps : etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
    simp [etaDenom, epsilon, g1T]
  have hcomb : ∀ᶠ w : ℂ in 𝓝[≠] z, combV M w - combU M m w ≠ 0 := by
    have h := G2RawKernelAux.e_affine_difference_eventually_ne_zero
      (epsilon M : ℂ)⁻¹ 0 1 ((m : ℂ) * (repellingTau M : ℂ)) z hinv
    simpa only [combV, combU, e_int_mul, ← e_add', div_eq_mul_inv, zero_add,
      add_zero, one_mul, mul_one, mul_comm, add_comm] using h
  have hU : ∀ᶠ w : ℂ in 𝓝[≠] z, 1 - combU M m w ≠ 0 := by
    have h := G2RawKernelAux.e_affine_eventually_ne_one 1
      ((m : ℂ) * (repellingTau M : ℂ)) z one_ne_zero
    filter_upwards [h] with w hw
    apply sub_ne_zero.mpr
    simpa only [one_mul, combU, e_int_mul, ← e_add', add_comm] using hw.symm
  have hU' : ∀ᶠ w : ℂ in 𝓝[≠] z,
      1 - (e (repellingTau M : ℂ)) ^ (m + v.1) * e (w + (argument M v : ℂ)) ≠ 0 := by
    have h := G2RawKernelAux.e_affine_eventually_ne_one 1
      (((m + v.1 : ℤ) : ℂ) * (repellingTau M : ℂ) + (argument M v : ℂ)) z one_ne_zero
    filter_upwards [h] with w hw
    apply sub_ne_zero.mpr
    simpa only [one_mul, e_int_mul, ← e_add', add_assoc, add_left_comm, add_comm] using hw.symm
  have hV' : ∀ᶠ w : ℂ in 𝓝[≠] z,
      1 - e ((w + (argument M v : ℂ)) / (epsilon M : ℂ)) ≠ 0 := by
    have h := G2RawKernelAux.e_affine_eventually_ne_one (epsilon M : ℂ)⁻¹
      ((argument M v : ℂ) / (epsilon M : ℂ)) z (inv_ne_zero hene)
    filter_upwards [h] with w hw
    apply sub_ne_zero.mpr
    rw [add_div]
    simpa only [div_eq_mul_inv, mul_comm] using hw.symm
  have ht : Tendsto (fun w : ℂ => w + (argument M v : ℂ)) (𝓝[≠] z)
      (𝓝[≠] (z + (argument M v : ℂ))) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin (by fun_prop)
    intro w hw heq
    exact hw (add_right_cancel heq)
  have hm := modularPhi_index_m_germ M hM.1 m 0 z _ hτ
  have hn := modularPhi_index_n_germ M hM.1 (m + 1) 0 z _ hτ
  have hmp := (modularPhi_index_m_germ M hM.1 (m + v.1) 0
    (z + (argument M v : ℂ)) _ hτ).comp_tendsto ht
  have hnp := (modularPhi_index_n_germ M hM.1 (m + v.1 + 1) 0
    (z + (argument M v : ℂ)) _ hτ).comp_tendsto ht
  have hnd := (modularPhi_index_n_germ M hM.1 (m + v.1) 0
    (z + (argument M v : ℂ)) _ hτ).comp_tendsto ht
  simp only [repellingTau_fixedPoint M hM, heps, zpow_zero, one_mul, zero_add] at hn hnp hnd
  simp only [Function.comp_def] at hmp hnp hnd
  filter_upwards [hcomb, hU, hU', hV', hm, hn, hmp, hnp, hnd,
    ht.eventually (G2RawKernelAux.phi_eventually_ne_zero M hM.1 (m + v.1) 0
      (z + (argument M v : ℂ)) _ hτ)]
    with w hwcomb hwU hwU' hwV' hwm hwn hwmp hwnp hwnd hwB
  have hpU : (e (repellingTau M : ℂ)) ^ (m + v.1) * e (w + (argument M v : ℂ)) =
      phaseT M v * combU M m w := by
    rw [zpow_add₀ (e_ne_zero _), e_add']
    rw [← argument_phase M hM v]
    unfold combU
    ring
  have hpV : e ((w + (argument M v : ℂ)) / (epsilon M : ℂ)) =
      phaseT M v * combV M w := by
    rw [add_div, e_add']
    unfold phaseT combV
    ring
  rw [hpU] at hwU' hwmp
  rw [hpV] at hwV' hwnp hwnd
  change modularPhi M (m + 1) 0 w (repellingTau M : ℂ) =
    modularPhi M m 0 w (repellingTau M : ℂ) / (1 - combU M m w) at hwm
  change modularPhi M (m + 1) 1 w (repellingTau M : ℂ) =
    (1 - combV M w) * modularPhi M (m + 1) 0 w (repellingTau M : ℂ) at hwn
  have hsnum : modularPhi M (m + 1 - M 0 0) 0 (w + (translate M : ℂ))
      (repellingTau M : ℂ) = modularPhi M (m + 1) 1 w (repellingTau M : ℂ) := by
    simpa only [translate, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast, zero_add]
      using G2RawKernelAux.modularPhi_translate M hM m 0 w
  have hsden : modularPhi M (m + 1 - M 0 0 + v.1) 0
      (w + (translate M : ℂ) + (argument M v : ℂ)) (repellingTau M : ℂ) =
      modularPhi M (m + v.1 + 1) 1 (w + (argument M v : ℂ)) (repellingTau M : ℂ) := by
    have hidx : m + 1 - M 0 0 + v.1 = m + v.1 + 1 - M 0 0 := by ring
    have hz' : w + (translate M : ℂ) + (argument M v : ℂ) =
        (w + (argument M v : ℂ)) +
          ((M 0 0 : ℂ) * (repellingTau M : ℂ) + (M 0 1 : ℂ)) := by
      simp only [translate, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]
      ring
    rw [hidx, hz']
    simpa only [zero_add] using G2RawKernelAux.modularPhi_translate M hM (m + v.1) 0
      (w + (argument M v : ℂ))
  have hph := translated_phase_factors M hM u m w
  dsimp only [rawF, ratioKernel]
  rw [hph.1, hph.2, hsnum, hsden, hwn, hwnp, hwm, hwmp, hwnd]
  exact G2RawKernelAux.ratio_difference _ _ _ _ _ _ _ (e_ne_zero _)
    hwcomb hwU hwU' hwV' hwB

/-- Point-value corollary only off the real divisor/comb axis; [RW26, p. 13]. -/
theorem rawF_difference_nonreal (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    rawF M u v m z - rawF M u v (m + 1 - M 0 0) (z + (translate M : ℂ)) =
      (1 - phaseT M v) * ratioKernel M u v m z := by
  have hcomb : ∀ m : ℤ, ∀ ζ : ℂ, ζ.im ≠ 0 → combV M ζ - combU M m ζ ≠ 0 := by
    intro r ζ hζ
    unfold combV combU
    rw [e_int_mul, ← e_add']
    apply G2RawKernelAux.e_sub_ne_zero_of_im_ne
    simp only [Complex.div_ofReal_im, Complex.add_im, Complex.mul_im,
      Complex.intCast_im, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add]
    intro heq
    have hene := (epsilon_pos M hM).ne'
    have heq' := (div_eq_iff hene).mp heq
    have hm : ζ.im * (1 - epsilon M) = 0 := by nlinarith [heq']
    exact mul_ne_zero hζ (sub_pos.mpr (epsilon_lt_one M hM)).ne' hm
  have hphi : ∀ r s : ℤ, ∀ ζ : ℂ, ζ.im ≠ 0 →
      ContinuousAt (fun w => modularPhi M r s w (repellingTau M : ℂ)) ζ ∧
        modularPhi M r s ζ (repellingTau M : ℂ) ≠ 0 := by
    intro r s ζ hζ
    exact G2RawKernelAux.phi_nonreal_unit M hM.1 r s _ (epsilon_pos M hM) ζ hζ
  have hraw : ∀ r : ℤ, ∀ ζ : ℂ, ζ.im ≠ 0 → ContinuousAt (rawF M u v r) ζ := by
    intro r ζ hζ
    have hp0 := hphi r 0 ζ hζ
    have hp1 := hphi (r + v.1) 0 (ζ + (argument M v : ℂ)) (by simpa using hζ)
    have hp1c : ContinuousAt (fun w : ℂ =>
        modularPhi M (r + v.1) 0 (w + (argument M v : ℂ)) (repellingTau M : ℂ)) ζ :=
      hp1.1.comp (f := fun w : ℂ => w + (argument M v : ℂ)) (by fun_prop)
    apply ContinuousAt.mul
    · apply ContinuousAt.div (f := fun w : ℂ => kernelK M u r w)
        (g := fun w : ℂ => combV M w - combU M r w) _ _ (hcomb r ζ hζ)
      · unfold kernelK e
        fun_prop
      · unfold combV combU e
        fun_prop
    · exact hp0.1.div hp1c hp1.2
  have hleft : ContinuousAt (fun w => rawF M u v m w -
      rawF M u v (m + 1 - M 0 0) (w + (translate M : ℂ))) z :=
    (hraw m z hz).sub ((hraw (m + 1 - M 0 0) (z + (translate M : ℂ))
      (by simpa using hz)).comp (f := fun w : ℂ => w + (translate M : ℂ)) (by fun_prop))
  have hright : ContinuousAt (fun w => (1 - phaseT M v) * ratioKernel M u v m w) z := by
    have hp0 := hphi (m + 1) 0 z hz
    have hp1 := hphi (m + v.1) 1 (z + (argument M v : ℂ)) (by simpa using hz)
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.mul
    · unfold kernelK e
      fun_prop
    · exact hp0.1.div (hp1.1.comp (f := fun w : ℂ => w + (argument M v : ℂ)) (by fun_prop)) hp1.2
  exact ModularCocycleAux.eq_of_germ hleft hright (rawF_difference_germ M hM u v z m)

/-- Single-function germ only. Its bent-chain integration is in `G2SingleBent`. [RW26, p. 13]. -/
theorem rawG_difference_germ (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    (fun ζ => rawG M u m ζ -
      rawG M u (m + 1 - M 0 0) (ζ + (translate M : ℂ))) =ᶠ[𝓝[≠] z]
      (fun ζ => singleKernel M u m ζ) := by
  have hene : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
  have heone : (epsilon M : ℂ) ≠ 1 := by exact_mod_cast (epsilon_lt_one M hM).ne
  have hinv : (epsilon M : ℂ)⁻¹ ≠ 1 := inv_ne_one.mpr heone
  have hτ : (repellingTau M : ℂ) ∈ modularPhiDomain M :=
    real_mem_modularPhiDomain M _ (epsilon_pos M hM)
  have heps : etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
    simp [etaDenom, epsilon, g1T]
  have hcomb : ∀ᶠ w : ℂ in 𝓝[≠] z, combV M w - combU M m w ≠ 0 := by
    have h := G2RawKernelAux.e_affine_difference_eventually_ne_zero
      (epsilon M : ℂ)⁻¹ 0 1 ((m : ℂ) * (repellingTau M : ℂ)) z hinv
    simpa only [combV, combU, e_int_mul, ← e_add', div_eq_mul_inv, zero_add,
      add_zero, one_mul, mul_one, mul_comm, add_comm] using h
  have hU : ∀ᶠ w : ℂ in 𝓝[≠] z, 1 - combU M m w ≠ 0 := by
    have h := G2RawKernelAux.e_affine_eventually_ne_one 1
      ((m : ℂ) * (repellingTau M : ℂ)) z one_ne_zero
    filter_upwards [h] with w hw
    apply sub_ne_zero.mpr
    simpa only [one_mul, combU, e_int_mul, ← e_add', add_comm] using hw.symm
  have hm := modularPhi_index_m_germ M hM.1 m 0 z _ hτ
  have hn := modularPhi_index_n_germ M hM.1 (m + 1) 0 z _ hτ
  simp only [repellingTau_fixedPoint M hM, heps, zpow_zero, one_mul, zero_add] at hn
  filter_upwards [hcomb, hU, hm, hn] with w hwcomb hwU hwm hwn
  change modularPhi M (m + 1) 0 w (repellingTau M : ℂ) =
    modularPhi M m 0 w (repellingTau M : ℂ) / (1 - combU M m w) at hwm
  change modularPhi M (m + 1) 1 w (repellingTau M : ℂ) =
    (1 - combV M w) * modularPhi M (m + 1) 0 w (repellingTau M : ℂ) at hwn
  have hsnum : modularPhi M (m + 1 - M 0 0) 0 (w + (translate M : ℂ))
      (repellingTau M : ℂ) = modularPhi M (m + 1) 1 w (repellingTau M : ℂ) := by
    simpa only [translate, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast, zero_add]
      using G2RawKernelAux.modularPhi_translate M hM m 0 w
  have hph := translated_phase_factors M hM u m w
  dsimp only [rawG, singleKernel]
  rw [hph.1, hph.2, hsnum, hwn, hwm]
  exact G2RawKernelAux.single_difference _ _ _ _ _ (e_ne_zero _) hwcomb hwU

#check @Sector.phiExtended_uniform_sector_decay
#check @modularPhi_shift_integer
#check @modularPhi_reflection_germ
#print rawF
#print rawG
#print finalLowerRate
#check rawF_difference_germ

end SICLean.L4.G2
