import SICLean.L5.Prop7FinalReflection
import SICLean.L5.Prop7FinalConjugation

set_option autoImplicit false

/-!
# The general Proposition 7, in the actual-value formulation

The final algebraic assembly uses the descent and reflection interfaces. [RW-rec, Prop.
7, p. 17, p. 18]. [RW26, p. 2, p. 3, p. 20, (2), (4), (37), footnote 2]. [RW26, Prop. 7,
Cor. 1, p. 14]; [RW-rec, p. 4, (7)]. For every flip tau put g=tau^-1 c tau. The existing
infinite-place class-field identity gives g|H=c|H * doubleArtin. Descent plus reflection
therefore gives g(U(x))=c(U(-x)); the analytic conjugation law gives 1/(e E(x)) off
zero. The separate real-root block proves g(e)=e by reality of tau(e), not preservation
of a positive square root. Thus g(E(x))=E(x)^-1 and the image under tau has unit norm.
-/

noncomputable section
open scoped MatrixGroups

namespace SICLean.L5.Prop7Final

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM
local notation "c" => ClassFieldInfinite.complexConjugation
local notation "e" => ActualValues.valueLift M hM 0
local notation "E" => ActualValues.valueLift M hM
local notation "U" => SplitPrimeValues.normalizedLift
  (ActualField.periodData M hM) (ActualLattice.stableLattice M hM)

/-- `actual_valueLift` identifies both numerator and origin with the actual Qbar values, before
using any Artin action. -/
theorem normalizedLift_eq_valueLift_div_origin (x : ActualLattice.Group M hM) :
    U x = E x / e := by
  simp only [SplitPrimeValues.normalizedLift, SplitPrimeValues.actual_valueLift]

/-- Matrix labels, their negation, and their actual zero share the existing arithmetic
normalization; no arbitrary finite-group map. -/
theorem normalizedLift_label (j : L4.SpecialValueGroup M) :
    U (ActualLattice.labelEquiv M hM j) =
      ActualValues.matrixLift M hM j / ActualValues.matrixLift M hM 0 := by
  have hzero : e = ActualValues.matrixLift M hM 0 := by
    simpa only [map_zero] using ActualValues.valueLift_label M hM 0
  rw [normalizedLift_eq_valueLift_div_origin, ActualValues.valueLift_label, hzero]

/-- Complex conjugation is identity on the actual real quadratic K under the fixed embedding. -/
theorem complexConjugation_fixes_base (a : K) : c (a : Galois.Qbar) = (a : Galois.Qbar) := by
  apply Galois.embed.injective
  change Galois.embed (c (a : Galois.Qbar)) = Galois.embed (a : Galois.Qbar)
  rw [ClassFieldInfinite.complexConjugation_embed]
  apply Complex.ext <;> simp [(ActualField.baseField_isRealQuadratic M hM).real a]

/-- Every conjugated conjugation still fixes K, because tau preserves K and c is identity there. -/
theorem conjugatedConjugation_fixes_base (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial K τ) (a : K) :
    (τ⁻¹ * c * τ) (a : Galois.Qbar) = (a : Galois.Qbar) := by
  obtain ⟨κ, _, hrestrict⟩ := hτ
  change τ.symm (c (τ (a : Galois.Qbar))) = (a : Galois.Qbar)
  rw [hrestrict a, complexConjugation_fixes_base M hM (κ a), ← hrestrict a]
  exact τ.symm_apply_apply _

/-- The exact composition order c after t. This uses `flip_conjugation_eq_first_mul_double`, actual
descent and t's action. The zero class is allowed here because the values are normalized. -/
theorem flip_normalized_action (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (τ : Galois.QbarAut) (hτ : Galois.InducesNontrivial K τ)
    (x : ActualLattice.Group M hM) : (τ⁻¹ * c * τ) (U x) = c (U (-x)) := by
  change τ⁻¹ (c (τ (U x))) = c (U (-x))
  rw [ClassFieldInfinite.flip_conjugation_apply M hM
    (RayArithmeticModulus.level M hM m) τ hτ (U x)
    (Descent.normalized_mem_classField M hM m hm x)]
  exact congrArg c
    (Prop7FinalReflection.artin_doubleSign_normalized_action M hM m hm x)

/-- Only nonzero labels admit this reciprocal formula; the plus-value origin is sqrt(epsilon) rather
than its inverse. -/
theorem flip_normalized_reciprocal (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (τ : Galois.QbarAut) (hτ : Galois.InducesNontrivial K τ)
    (x : ActualLattice.Group M hM) (hx : x ≠ 0) :
    (τ⁻¹ * c * τ) (U x) = 1 / (e * E x) := by
  rw [flip_normalized_action M hM m hm τ hτ x]
  exact Prop7FinalConjugation.conjugation_normalized_neg M hM x hx

/-- Removes the normalization using the independently proved `conjugated_conjugation_origin`. No
assumption e∈H is required. -/
theorem flip_value_inverse (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (τ : Galois.QbarAut) (hτ : Galois.InducesNontrivial K τ)
    (x : ActualLattice.Group M hM) (hx : x ≠ 0) :
    (τ⁻¹ * c * τ) (E x) = (E x)⁻¹ := by
  have h := flip_normalized_reciprocal M hM m hm τ hτ x hx
  rw [normalizedLift_eq_valueLift_div_origin, map_div₀,
    Prop7FinalConjugation.conjugated_conjugation_origin M hM τ hτ] at h
  apply (div_left_inj' (Prop7FinalConjugation.origin_ne_zero M hM)).mp
  calc
    (τ⁻¹ * c * τ) (E x) / e = 1 / (e * E x) := h
    _ = (E x)⁻¹ / e := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]

/-- Applies tau to the preceding equality; c is still the fixed complex conjugation, with no
continuity assumption on tau. -/
theorem flip_value_conjugate_inverse (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (τ : Galois.QbarAut) (hτ : Galois.InducesNontrivial K τ)
    (x : ActualLattice.Group M hM) (hx : x ≠ 0) : c (τ (E x)) = (τ (E x))⁻¹ := by
  have h := congrArg τ (flip_value_inverse M hM m hm τ hτ x hx)
  simpa only [AlgEquiv.mul_apply, AlgEquiv.coe_inv, AlgEquiv.apply_symm_apply,
    map_inv₀] using h

/-- The same identity in the one fixed complex embedding. -/
theorem flip_embed_conj_eq_inv (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (τ : Galois.QbarAut) (hτ : Galois.InducesNontrivial K τ)
    (x : ActualLattice.Group M hM) (hx : x ≠ 0) :
    star (Galois.embed (τ (E x))) = (Galois.embed (τ (E x)))⁻¹ := by
  rw [← ClassFieldInfinite.complexConjugation_embed,
    flip_value_conjugate_inverse M hM m hm τ hτ x hx, map_inv₀]

/-- [RW-rec]: choose the explicit valid defaultLevel, then use nonvanishing and the
conjugate-inverse equation. -/
theorem pseudolattice_unit_norm (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial K τ) (x : ActualLattice.Group M hM) (hx : x ≠ 0) :
    ‖Galois.embed (τ (E x))‖ = 1 := by
  apply Prop7FinalConjugation.norm_eq_one_of_conj_eq_inv
  · exact (map_ne_zero Galois.embed).mpr
      ((map_ne_zero τ).mpr (ActualValues.valueLift_ne_zero M hM x))
  · exact flip_embed_conj_eq_inv M hM (DescentField.defaultLevel M hM)
      (DescentField.defaultLevel_valid M hM) τ hτ x hx

/-- General Proposition 7 on the actual lattice labels, with the full universal quantifier over
flips and nonzero labels. -/
theorem pseudolattice_prop7_final :
    Galois.Prop7ForValues (ActualField.baseField M hM) (ActualValues.valueLift M hM) := by
  exact pseudolattice_unit_norm M hM

/-- Final label transport by ActualLattice.labelEquiv and ActualValues.valueLift_label, preserving
the zero exclusion exactly. -/
theorem matrix_unit_norm (τ : Galois.QbarAut) (hτ : Galois.InducesNontrivial K τ)
    (j : L4.SpecialValueGroup M) (hj : j ≠ 0) :
    ‖Galois.embed (τ (ActualValues.matrixLift M hM j))‖ = 1 := by
  have hx : ActualLattice.labelEquiv M hM j ≠ 0 :=
    fun hx => hj ((ActualLattice.labelEquiv_zero_iff M hM j).mp hx)
  simpa only [ActualValues.valueLift_label] using
    pseudolattice_unit_norm M hM τ hτ (ActualLattice.labelEquiv M hM j) hx

/-- The target, with exactly the same binders and result type as the existing matrix_prop7. -/
theorem matrix_prop7_final (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    Galois.Prop7ForValues (ActualField.baseField M hM) (ActualValues.matrixLift M hM) := by
  exact matrix_unit_norm M hM

end SICLean.L5.Prop7Final
