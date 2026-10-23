import SICLean.L4.M74Coefficients
import SICLean.L4.M74EquationsAux

set_option autoImplicit false

/-!
# Actual Q1/Q2 and the two zero-class branches

Proofs identify the actual point values and transport the identities.
The actual point remains pseudolatticeFamilyPoint, defined with the same
modularPhi and etaMultiplier. The bridge to specialValuePlus
uses its actual point values, including the separate zero prescription;
no punctured-germ equality is promoted to a center equality here.

Only mixed reflection holds at zero. Q2 with two E/plus values is stated
off zero, and the same formula does not hold at zero.
The final three statements match IsSolution.q1, q2, q4 verbatim.
There is no Q3 theorem or unconditional IsSolution construction.
[RW26, p. 2, p. 3, p. 12, (2), (4)--(5), Lemma 2, footnote 2].
The Q4 scalar uses the squared eta multiplier. [RW26, p. 23, Theorem 11].
-/

noncomputable section

open scoped Classical

namespace SICLean.L3.M74

universe u

variable {K : Type u} [Field K] [NumberField K] {P : PeriodData K}

/--
Equality of actual point values, not merely of punctured germs.
The zero case uses the prescribed positive root on both sides; [RW26, p. 2, p. 3, p. 12, (2), (4),
Lemma 2].
-/
theorem basisValue_eq_plus (B : L4.DistributionBasis) (hB : B.Valid)
    (x : L4.DistributionGroup B) :
    L4.distributionValue B x =
      L4.specialValuePlus B.matrix (basis_admissible B hB) ((basisRowEquiv B hB).symm x) := by
  obtain ⟨y, rfl⟩ := (basisRowEquiv B hB).surjective x
  refine Quotient.inductionOn y ?_
  intro v
  change L4.distributionValue B (basisRowEquiv B hB (L4.specialValueMk B.matrix v)) =
    L4.specialValuePlus B.matrix (basis_admissible B hB)
      ((basisRowEquiv B hB).symm (basisRowEquiv B hB (L4.specialValueMk B.matrix v)))
  rw [AddEquiv.symm_apply_apply, basisRowEquiv_mk, L4.distributionValue_mk B hB,
    L4.specialValuePlus_mk]
  unfold L4.specialValuePlusLift
  by_cases hv : v ∈ L4.specialValueLattice B.matrix
  · rw [if_pos hv, L4.distributionBasisValue_on_lattice B _
      ((L4.distributionRowPoint_lattice_iff B hB v).mpr hv), basis_epsilon B hB]
  · rw [if_neg hv, L4.distributionRowPoint_value B hB v hv]
    unfold L4.specialValueRaw L4.specialValueArgument
    rw [basis_tau B hB]

/--
Mixed reflection plus off-zero agreement gives the two-E formula.
No Fourier or five-term premise is required; [RW26, p. 3, p. 12, (5), footnote 2].
-/
theorem basisValue_q2 (B : L4.DistributionBasis) (hB : B.Valid)
    (x : L4.DistributionGroup B) (hx : x ≠ 0) :
    L4.distributionValue B x * L4.distributionValue B (-x) = (basisGaussian B hB x)⁻¹ := by
  have hy : (basisRowEquiv B hB).symm x ≠ 0 := by
    intro hy
    apply hx
    have := congrArg (basisRowEquiv B hB) hy
    simpa using this
  rw [basisValue_eq_plus B hB x, basisValue_eq_plus B hB (-x), map_neg,
    L4.specialValue_agree_off_zero B.matrix (basis_admissible B hB) _
      (neg_ne_zero.mpr hy)]
  exact L4.specialValue_mixed_reflection B.matrix (basis_admissible B hB)
    ((basisRowEquiv B hB).symm x)

/-- Literal F-minus prescription, distinct from the E/plus point at zero. -/
def familyMinusPoint (F : FinitePseudolatticeFamily P) :
    Coordinate (Fin F.size) (PseudolatticeFamilyGroup F) → ℂ :=
  fun c => if c.2 = 0 then (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)⁻¹
    else pseudolatticeFamilyPoint F c

/--
Identifies the new explicit two-branch prescription with the existing
actual F-minus; it is not a function chosen to satisfy reflection; [RW26, p. 2, p. 3, (2), (4),
footnote 2].
-/
theorem familyMinusPoint_eq_minus (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (x : PseudolatticeFamilyGroup F i) :
    familyMinusPoint F ⟨i, x⟩ =
      L4.specialValueMinus (pseudolatticeFamilyBasis F i).matrix
        (basis_admissible (pseudolatticeFamilyBasis F i) (familyBasis_valid F i))
        ((basisRowEquiv (pseudolatticeFamilyBasis F i) (familyBasis_valid F i)).symm x) := by
  by_cases hx : x = 0
  · subst x
    simp only [familyMinusPoint, if_true, map_zero, L4.specialValueMinus_zero]
    rw [← basis_epsilon _ (familyBasis_valid F i), familyBasis_period F i]
  · rw [familyMinusPoint, if_neg hx]
    change L4.distributionValue (pseudolatticeFamilyBasis F i) x = _
    rw [basisValue_eq_plus _ (familyBasis_valid F i)]
    apply L4.specialValue_agree_off_zero
    intro hy
    apply hx
    have := congrArg (basisRowEquiv (pseudolatticeFamilyBasis F i)
      (familyBasis_valid F i)) hy
    simpa using this

/--
The actual Q1 coordinate is the positive sqrt(epsilon), at every i; [RW26, p. 3, (4)].
-/
theorem familyPoint_zero (F : FinitePseudolatticeFamily P) :
    ∀ i, pseudolatticeFamilyPoint F ⟨i, 0⟩ = (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) := by
  intro i
  change L4.distributionValue (pseudolatticeFamilyBasis F i) 0 = _
  rw [L4.distributionValue_zero _ (familyBasis_valid F i), familyBasis_period F i]

/--
The second prescribed zero branch is its inverse; [RW26, p. 3, (4), footnote 2].
-/
theorem familyMinusPoint_zero (F : FinitePseudolatticeFamily P) :
    ∀ i, familyMinusPoint F ⟨i, 0⟩ = (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)⁻¹ := by
  intro i
  exact if_pos rfl

/--
Branch agreement is restricted to nonzero quotient labels; [RW26, p. 3, footnote 2].
-/
theorem familyPoint_eq_minus_off_zero (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (x : PseudolatticeFamilyGroup F i) (hx : x ≠ 0) :
    pseudolatticeFamilyPoint F ⟨i, x⟩ = familyMinusPoint F ⟨i, x⟩ := by
  exact (if_neg hx).symm

/--
The zero branches must never be identified: epsilon > 1; [RW26, p. 3, (4), footnote 2].
-/
theorem familyPoint_zero_branches_ne (F : FinitePseudolatticeFamily P) :
    ∀ i, pseudolatticeFamilyPoint F ⟨i, 0⟩ ≠ familyMinusPoint F ⟨i, 0⟩ := by
  intro i
  rw [familyPoint_zero F i, familyMinusPoint_zero F i]
  exact L4.M74EquationsAux.period_sqrt_ne_inv P

/--
Actual mixed reflection includes zero; its second factor remains F-minus.
[RW26, p. 3, p. 12, (5)].
-/
theorem familyPoint_mixed_reflection (F : FinitePseudolatticeFamily P) :
    ∀ i (x : PseudolatticeFamilyGroup F i),
      pseudolatticeFamilyPoint F ⟨i, x⟩ * familyMinusPoint F ⟨i, -x⟩ =
        (familyGaussian F i x)⁻¹ := by
  intro i x
  rw [familyMinusPoint_eq_minus F i (-x)]
  change L4.distributionValue (pseudolatticeFamilyBasis F i) x * _ = _
  rw [basisValue_eq_plus _ (familyBasis_valid F i), map_neg]
  exact L4.specialValue_mixed_reflection _ _ _

/--
Q1 for the same actual family point, with the positive sqrtN.
 [RW26, p. 3, (4)].
-/
theorem familyPoint_q1 (F : FinitePseudolatticeFamily P) :
    ∀ i, pseudolatticeFamilyPoint F ⟨i, 0⟩ ^ 2 -
      (Real.sqrt (P.N : ℝ) : ℂ) * pseudolatticeFamilyPoint F ⟨i, 0⟩ - 1 = 0 := by
  intro i
  rw [familyPoint_zero F i]
  exact_mod_cast period_sqrt_normalization P

/--
The minus zero branch satisfies the other polynomial sign; [RW26, p. 3, (4)].
-/
theorem familyMinusPoint_zero_polynomial (F : FinitePseudolatticeFamily P) :
    ∀ i, familyMinusPoint F ⟨i, 0⟩ ^ 2 +
      (Real.sqrt (P.N : ℝ) : ℂ) * familyMinusPoint F ⟨i, 0⟩ - 1 = 0 := by
  intro i
  rw [familyMinusPoint_zero F i]
  exact L4.M74EquationsAux.period_sqrt_inv_polynomial P

/--
Q2 is exactly mixed reflection off zero; all nonzero order-two labels
are retained. [RW26, p. 3, (5), footnote 2].
-/
theorem familyPoint_q2 (F : FinitePseudolatticeFamily P) :
    ∀ i (x : PseudolatticeFamilyGroup F i), x ≠ 0 →
      pseudolatticeFamilyPoint F ⟨i, x⟩ * pseudolatticeFamilyPoint F ⟨i, -x⟩ =
        (familyGaussian F i x)⁻¹ := by
  intro i x hx
  change L4.distributionValue (pseudolatticeFamilyBasis F i) x *
    L4.distributionValue (pseudolatticeFamilyBasis F i) (-x) = _
  exact basisValue_q2 _ (familyBasis_valid F i) x hx

/--
A precise guard against deleting the exceptional zero branch; [RW26, p. 3, (4)--(5), footnote 2].
-/
theorem familyPoint_q2_at_zero_fails (F : FinitePseudolatticeFamily P) :
    ∀ i, pseudolatticeFamilyPoint F ⟨i, 0⟩ * pseudolatticeFamilyPoint F ⟨i, 0⟩ ≠
      (familyGaussian F i 0)⁻¹ := by
  intro i
  rw [familyPoint_zero F i, familyGaussian_zero F i, inv_one]
  exact L4.M74EquationsAux.period_sqrt_mul_ne_one P

/--
Direct IsSolution.q1 input, including the exact scalar map.
 [RW26, p. 3, (4)].
-/
theorem system_q1 (F : FinitePseudolatticeFamily P) :
    ∀ i, pseudolatticeFamilyPoint F ⟨i, 0⟩ ^ 2 -
      algebraMap (coefficientField F) ℂ (system F).sqrtN *
        pseudolatticeFamilyPoint F ⟨i, 0⟩ - 1 = 0 := by
  rw [system_sqrtN_map F]
  exact familyPoint_q1 F

/--
Direct IsSolution.q2 input, without strengthening it to zero.
 [RW26, p. 3, (5)].
-/
theorem system_q2 (F : FinitePseudolatticeFamily P) :
    ∀ i (x : PseudolatticeFamilyGroup F i), x ≠ 0 →
      pseudolatticeFamilyPoint F ⟨i, x⟩ * pseudolatticeFamilyPoint F ⟨i, -x⟩ =
        algebraMap (coefficientField F) ℂ ((system F).gaussian i x)⁻¹ := by
  intro i x hx
  rw [map_inv₀, system_gaussian_map F i x]
  exact familyPoint_q2 F i x hx

/--
Transfer the Q4 to the exact coefficient system.
This is only wiring, includes x=0,h, and requires no new five-term theorem.
[RW26, p. 23].
-/
theorem system_q4 (F : FinitePseudolatticeFamily P) :
    ∀ i (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i)
      (x : PseudolatticeFamilyGroup F i),
      pseudolatticeFamilyPoint F ⟨i, x⟩ * pseudolatticeFamilyPoint F ⟨i, x + h.val⟩ =
        algebraMap (coefficientField F) ℂ ((system F).multiplier i h) *
          pseudolatticeFamilyPoint F ⟨(system F).target i h, (system F).project i h x⟩ := by
  intro i h x
  rw [system_multiplier_map F i h]
  exact pseudolatticeFamily_q4 F i h x

#check @L4.specialValue_mixed_reflection
#check @FiniteSystem.IsSolution.mk
#print familyMinusPoint
#check @system_q1
#check @system_q2
#check @system_q4

end SICLean.L3.M74
