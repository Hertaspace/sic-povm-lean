import SICLean.L4.M75Doubling
import SICLean.L3.ValuationSupport

set_option autoImplicit false

/-!
# Actual finite-family Q3 and its order-two split

FamilyPentagon explicitly asks for the full
attracting (7) on each representative matrix of the already finite family.
It neither assumes Q3 nor enlarges the coefficient field by E coordinates.
Q4 is already exactly M74.system_q4; it is not restated here. [RW26, p. 3, p. 23, (3), (7), Theorem
11].
The Q4 substitution uses the squared eta multiplier. [RW26, Theorem 11].
The purely combinatorial pair selection already exists in ValuationSupport;
no new pair-selection axiom, parity assumption or surjectivity is introduced.
-/

noncomputable section

open scoped Classical BigOperators
open SICLean.L4.G2.SpecialValueBridge

namespace SICLean.L3.M75.Family

universe u

variable {K : Type u} [Field K] [NumberField K] {P : PeriodData K}

/--
Only subtype enumeration: OrderTwo is a definition, so its underlying finite
subtype is instantiated locally.
-/
local instance orderTwoFintype (F : FinitePseudolatticeFamily P) (i : Fin F.size) :
    Fintype (OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :=
  inferInstanceAs (Fintype {h : PseudolatticeFamilyGroup F i // h ≠ 0 ∧ h + h = 0})

/--
Explicit finite list of actual matrix hypotheses (7). Expanding
Doubling.MatrixPentagon displays its full all-parameter formula.
-/
def FamilyPentagon (F : FinitePseudolatticeFamily P) : Prop :=
  ∀ i : Fin F.size,
    Doubling.MatrixPentagon (pseudolatticeFamilyBasis F i).matrix
      (M74.basis_admissible (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i))

/-- Pullback of the existing positive-sign pairing by the specified row map. -/
def familyPairing (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (x y : PseudolatticeFamilyGroup F i) : ℂ :=
  L4.specialValuePairing (pseudolatticeFamilyBasis F i).matrix
    (M74.basis_admissible (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i))
    ((M74.basisRowEquiv (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i)).symm x)
    ((M74.basisRowEquiv (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i)).symm y)

/-- Counting normalization uses the same P.N for every i. -/
def familyNormalizedSum (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (f : PseudolatticeFamilyGroup F i → ℂ) : ℂ :=
  (Real.sqrt (P.N : ℝ) : ℂ)⁻¹ * ∑ x, f x

/-- Concrete summand, with actual E in both factors and actual Gaussian. -/
def doublingSummand (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (u s : PseudolatticeFamilyGroup F i) : ℂ :=
  M74.familyGaussian F i s * pseudolatticeFamilyPoint F ⟨i, u + s⟩ *
    pseudolatticeFamilyPoint F ⟨i, u - s⟩

/--
Normalized sum transport, including the common positive square root; [RW26, p. 3, (3), (7)].
-/
theorem familyNormalizedSum_eq_matrix (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (f : PseudolatticeFamilyGroup F i → ℂ) :
    familyNormalizedSum F i f =
      normalizedValueSum (pseudolatticeFamilyBasis F i).matrix
        (M74.basis_admissible (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i))
        (fun x => f (M74.basisRowEquiv (pseudolatticeFamilyBasis F i)
          (M74.familyBasis_valid F i) x)) := by
  let : Fintype (L4.SpecialValueGroup (pseudolatticeFamilyBasis F i).matrix) :=
    @Fintype.ofFinite _ (L4.specialValueGroup_finite _
      (M74.basis_admissible _ (M74.familyBasis_valid F i)))
  unfold familyNormalizedSum normalizedValueSum
  rw [M74.familyBasis_order F i]
  simp only [Int.cast_natCast]
  congr 1
  exact ((M74.basisRowEquiv _ (M74.familyBasis_valid F i)).toEquiv.sum_comp f).symm

/--
Pins the new family pairing to the literal row formula used numerically; [RW26, p. 3, (3)].
-/
theorem familyPairing_mk (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (v w : ℤ × ℤ) :
    familyPairing F i
      (M74.basisRowEquiv (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i)
        (L4.specialValueMk (pseudolatticeFamilyBasis F i).matrix v))
      (M74.basisRowEquiv (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i)
        (L4.specialValueMk (pseudolatticeFamilyBasis F i).matrix w)) =
      L4.specialValuePairingLift (pseudolatticeFamilyBasis F i).matrix v w := by
  simp only [familyPairing, AddEquiv.symm_apply_apply, L4.specialValuePairing_mk]

/--
Full family identity (7), with both branches and the origin term.
This theorem is transport, conditional on h7. [RW26, p. 3, (7)].
-/
theorem family_pentagon (F : FinitePseudolatticeFamily P) (h7 : FamilyPentagon F)
    (i : Fin F.size) (u v : PseudolatticeFamilyGroup F i) :
    familyNormalizedSum F i (fun x => familyPairing F i x u *
      (pseudolatticeFamilyPoint F ⟨i, x⟩ / M74.familyMinusPoint F ⟨i, x + v⟩)) =
      pseudolatticeFamilyPoint F ⟨i, u + v⟩ /
        (M74.familyMinusPoint F ⟨i, u⟩ * M74.familyMinusPoint F ⟨i, v⟩) -
          (if u = 0 ∧ v = 0 then (P.N : ℂ) * pseudolatticeFamilyPoint F ⟨i, 0⟩ else 0) := by
  rw [familyNormalizedSum_eq_matrix]
  simp only [familyPairing, M74.familyMinusPoint_eq_minus,
    pseudolatticeFamilyPoint, L4.distributionFamilyPoint,
    pseudolatticeFamilyLabel, AddEquiv.refl_apply,
    M74.basisValue_eq_plus _ (M74.familyBasis_valid F i), map_add,
    AddEquiv.symm_apply_apply, map_zero]
  have h := h7 i
    ((M74.basisRowEquiv _ (M74.familyBasis_valid F i)).symm u)
    ((M74.basisRowEquiv _ (M74.familyBasis_valid F i)).symm v)
  simpa only [M74.familyBasis_order, Int.cast_natCast, AddEquiv.map_eq_zero_iff] using h

/--
Family version of reflection at -z; the zero branch remains inverse sqrt.
 [RW26, p. 3, (5), footnote 2].
-/
theorem family_minus_inv (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (z : PseudolatticeFamilyGroup F i) :
    (M74.familyMinusPoint F ⟨i, z⟩)⁻¹ =
      M74.familyGaussian F i z * pseudolatticeFamilyPoint F ⟨i, -z⟩ := by
  simpa only [M74.familyMinusPoint_eq_minus, M74.familyGaussian, M74.basisGaussian,
    pseudolatticeFamilyPoint, L4.distributionFamilyPoint,
    pseudolatticeFamilyLabel, AddEquiv.refl_apply,
    M74.basisValue_eq_plus _ (M74.familyBasis_valid F i), map_neg] using
    (Doubling.minus_inv _ (M74.basis_admissible _ (M74.familyBasis_valid F i))
      ((M74.basisRowEquiv _ (M74.familyBasis_valid F i)).symm z))

/--
In particular this gives 1=χ(u)^4 at a nonzero order-two u; [RW26, p. 3, (3)].
-/
theorem family_gaussian_double (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (u : PseudolatticeFamilyGroup F i) :
    M74.familyGaussian F i (u + u) = M74.familyGaussian F i u ^ 4 := by
  simp only [M74.familyGaussian, M74.basisGaussian, map_add, Gaussian.gaussian_double]

/--
Actual Q3 for all u≠0, conditional only on the full representative (7).
[RW26, p. 22, p. 23, Theorem 10], even case.
-/
theorem familyPoint_q3 (F : FinitePseudolatticeFamily P) (h7 : FamilyPentagon F) :
    ∀ i (u : PseudolatticeFamilyGroup F i), u ≠ 0 →
      (Real.sqrt (P.N : ℝ) : ℂ) * pseudolatticeFamilyPoint F ⟨i, u + u⟩ =
        pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 2 * ∑ s : PseudolatticeFamilyGroup F i,
          M74.familyGaussian F i s * pseudolatticeFamilyPoint F ⟨i, u + s⟩ *
            pseudolatticeFamilyPoint F ⟨i, u - s⟩ := by
  intro i u hu
  let e := M74.basisRowEquiv (pseudolatticeFamilyBasis F i) (M74.familyBasis_valid F i)
  let : Fintype (L4.SpecialValueGroup (pseudolatticeFamilyBasis F i).matrix) :=
    @Fintype.ofFinite _ (L4.specialValueGroup_finite _
      (M74.basis_admissible _ (M74.familyBasis_valid F i)))
  have hu' : e.symm u ≠ 0 := by
    intro hz
    apply hu
    have h := congrArg e hz
    simpa using h
  have hd := Doubling.doubling _
    (M74.basis_admissible _ (M74.familyBasis_valid F i)) (h7 i) (e.symm u) hu'
  rw [← e.toEquiv.sum_comp (fun s : PseudolatticeFamilyGroup F i =>
    M74.familyGaussian F i s * pseudolatticeFamilyPoint F ⟨i, u + s⟩ *
      pseudolatticeFamilyPoint F ⟨i, u - s⟩)]
  simpa only [e, M74.familyBasis_order, Int.cast_natCast,
    M74.familyGaussian, M74.basisGaussian, pseudolatticeFamilyPoint,
    L4.distributionFamilyPoint, pseudolatticeFamilyLabel, AddEquiv.refl_apply,
    M74.basisValue_eq_plus _ (M74.familyBasis_valid F i),
    AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    map_add, map_sub, AddEquiv.symm_apply_apply] using hd

/--
The `IsSolution.q3` field over the already defined coefficient field; [RW26, p. 23, Theorem 11].
-/
theorem system_q3 (F : FinitePseudolatticeFamily P) (h7 : FamilyPentagon F) :
    ∀ i (u : PseudolatticeFamilyGroup F i), u ≠ 0 →
      algebraMap (M74.coefficientField F) ℂ (M74.system F).sqrtN *
          pseudolatticeFamilyPoint F ⟨i, u + u⟩ =
        pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 2 * ∑ s : PseudolatticeFamilyGroup F i,
          algebraMap (M74.coefficientField F) ℂ ((M74.system F).gaussian i s) *
            pseudolatticeFamilyPoint F ⟨i, u + s⟩ * pseudolatticeFamilyPoint F ⟨i, u - s⟩ := by
  simp only [M74.system_sqrtN_map, M74.system_gaussian_map]
  exact familyPoint_q3 F h7

/--
The pair {s,-s} really has equal terms, also with zero E arguments; [RW26, p. 22, Theorem 10]
(finite algebra).
-/
theorem doublingSummand_neg (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (u s : PseudolatticeFamilyGroup F i) :
    doublingSummand F i u (-s) = doublingSummand F i u s := by
  simp only [doublingSummand, M74.familyGaussian_neg, sub_eq_add_neg, neg_neg]
  ring

/--
The s=0 term produces E(u)^4 after the outside E(u)^2; [RW26, p. 22, Theorem 10].
-/
theorem doublingSummand_zero (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (u : PseudolatticeFamilyGroup F i) :
    doublingSummand F i u 0 = pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 2 := by
  simp [doublingSummand, M74.familyGaussian_zero, pow_two]

/--
The fixed points of negation give the squared product in the split; [RW26, p. 23].
-/
theorem doublingSummand_orderTwo (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (u : PseudolatticeFamilyGroup F i)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 2 * doublingSummand F i u h.val =
      M74.familyGaussian F i h.val *
        (pseudolatticeFamilyPoint F ⟨i, u⟩ * pseudolatticeFamilyPoint F ⟨i, u + h.val⟩) ^ 2 := by
  have hh : -h.val = h.val := neg_eq_iff_add_eq_zero.mpr h.property.2
  rw [doublingSummand, sub_eq_add_neg, hh]
  ring

/--
Literal zero / nonzero 2-torsion / unordered-pair split.
T selects one of s,-s and contains no 2-torsion. No assumption on 2u; [RW26, p. 23].
-/
theorem doubling_split (F : FinitePseudolatticeFamily P) (h7 : FamilyPentagon F)
    (i : Fin F.size) (u : PseudolatticeFamilyGroup F i) (hu : u ≠ 0) :
    ∃ T : Finset (PseudolatticeFamilyGroup F i),
      (∀ s ∈ T, s + s ≠ 0) ∧
      (∀ s, s + s ≠ 0 → (s ∈ T ↔ -s ∉ T)) ∧
      (Real.sqrt (P.N : ℝ) : ℂ) * pseudolatticeFamilyPoint F ⟨i, u + u⟩ =
        pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 4 +
          (∑ h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i,
            M74.familyGaussian F i h.val *
              (pseudolatticeFamilyPoint F ⟨i, u⟩ *
                pseudolatticeFamilyPoint F ⟨i, u + h.val⟩) ^ 2) +
          2 * pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 2 * ∑ s ∈ T, doublingSummand F i u s := by
  obtain ⟨T, hT, hpair, hsum⟩ := ValuationSupport.exists_neg_pair_sum
    (doublingSummand F i u) (doublingSummand_neg F i u)
  change (∑ s, doublingSummand F i u s) = doublingSummand F i u 0 +
    (∑ h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i,
      doublingSummand F i u h.val) + 2 * ∑ s ∈ T, doublingSummand F i u s at hsum
  refine ⟨T, hT, hpair, ?_⟩
  have hq := familyPoint_q3 F h7 i u hu
  change (Real.sqrt (P.N : ℝ) : ℂ) * pseudolatticeFamilyPoint F ⟨i, u + u⟩ =
    pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 2 *
      ∑ s, doublingSummand F i u s at hq
  rw [hsum, doublingSummand_zero, mul_add, mul_add, Finset.mul_sum] at hq
  simp_rw [doublingSummand_orderTwo] at hq
  calc
    _ = _ := hq
    _ = _ := by ring

/--
The Q4 identity uses κ² times the target E², including at u=0.
No projection surjectivity is required. [RW26, p. 23].
-/
theorem doubling_split_q4 (F : FinitePseudolatticeFamily P) (h7 : FamilyPentagon F)
    (i : Fin F.size) (u : PseudolatticeFamilyGroup F i) (hu : u ≠ 0) :
    ∃ T : Finset (PseudolatticeFamilyGroup F i),
      (∀ s ∈ T, s + s ≠ 0) ∧
      (∀ s, s + s ≠ 0 → (s ∈ T ↔ -s ∉ T)) ∧
      (Real.sqrt (P.N : ℝ) : ℂ) * pseudolatticeFamilyPoint F ⟨i, u + u⟩ =
        pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 4 +
          (∑ h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i,
            M74.familyGaussian F i h.val *
              L4.distributionFamilyKappa (pseudolatticeFamilyBasis F)
                (pseudolatticeFamilyTarget F) i h ^ 2 *
              pseudolatticeFamilyPoint F
                ⟨pseudolatticeFamilyTarget F i h, pseudolatticeFamilyProject F i h u⟩ ^ 2) +
          2 * pseudolatticeFamilyPoint F ⟨i, u⟩ ^ 2 * ∑ s ∈ T, doublingSummand F i u s := by
  obtain ⟨T, hT, hpair, hsplit⟩ := doubling_split F h7 i u hu
  refine ⟨T, hT, hpair, ?_⟩
  rw [hsplit]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  rw [pseudolatticeFamily_q4, mul_pow]
  ring

#print FamilyPentagon
#print familyPairing
#print familyNormalizedSum
#print doublingSummand
#check @M74.system_q4
#check @system_q3
#check @ValuationSupport.exists_neg_pair_sum

end SICLean.L3.M75.Family
