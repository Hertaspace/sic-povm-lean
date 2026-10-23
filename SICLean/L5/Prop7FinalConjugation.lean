import SICLean.L5.ActualValueBridge
import SICLean.L5.ActualOriginal
import SICLean.L5.ConjugationSpecialValue
import SICLean.L5.ClassFieldInfinite
import SICLean.L5.SplitPrimeValues
import SICLean.L5.Prop7FinalConjugationAux

set_option autoImplicit false

/-!
# Final Proposition 7: actual origin and complex conjugation

The local symbols below abbreviate the existing actual Qbar values and the existing
normalization. In particular, `e` is the value at zero, and `c` is the fixed complex
conjugation from ClassFieldInfinite. No analytic value, root branch, normalization, or
class field is defined in this file. Sources: [RW-rec, Def. 1, Prop. 2(7), Prop. 7, p.
3, p. 4, p. 17, p. 18]. [RW26, Prop. 7, Cor. 1(28), p. 2, p. 3, p. 14, (2), (4),
footnote 2]. The positive root is prescribed only in the fixed embedding. An arbitrary
flip sends its square to the positive second embedding of epsilon, which forces a real
image but does not select a positive sign. The reciprocal identity for two plus values
is restricted to nonzero labels throughout.
-/

noncomputable section
open scoped MatrixGroups

namespace SICLean.L5.Prop7FinalConjugation

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)

local notation "c" => ClassFieldInfinite.complexConjugation
local notation "e" => ActualValues.valueLift M hM 0
local notation "E" => ActualValues.valueLift M hM
local notation "U" => SplitPrimeValues.normalizedLift
  (ActualField.periodData M hM) (ActualLattice.stableLattice M hM)

/-- The actual origin is nonzero; [RW26, p. 3, (4), footnote 2]; [RW-rec, Def. 1, p. 3]. The Qbar
assertion is a fixed-embedding bridge, not an additional assertion in these sources. -/
theorem origin_ne_zero : e ≠ 0 := by
  exact ActualValues.valueLift_ne_zero M hM 0

/-- The origin squares to the actual field period, including in Qbar. [RW26, p. 3, (4), footnote 2];
[RW-rec, Def. 1, p. 3]. Equality of the chosen lifts is the fixed-embedding bridge; the origin is
not epsilon itself. -/
theorem origin_sq : e ^ 2 = (ActualField.epsilon M hM : Galois.Qbar) := by
  apply Galois.embed.injective
  change Galois.embed (e ^ 2) = Galois.embed (ActualField.epsilon M hM : Galois.Qbar)
  rw [map_pow, ActualValues.embed_valueLift, ActualValues.value_zero,
    ActualField.embed_epsilon, ← Complex.ofReal_pow,
    Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one (L4.specialValueEpsilon_gt_one M hM)))]

/-- The positive sign belongs to the fixed complex embedding; [RW26, p. 3, (4), footnote 2];
[RW-rec, Def. 1, p. 3]. This is the existing value-zero theorem transported through embed. -/
theorem embed_origin :
    Galois.embed e = (Real.sqrt (L4.specialValueEpsilon M) : ℂ) := by
  exact (ActualValues.embed_valueLift M hM 0).trans (ActualValues.value_zero M hM)

/-- Complex conjugation fixes the prescribed real origin; [RW26, p. 3, p. 14, (4), (28)]; [RW-rec,
Def. 1, Prop. 7, p. 3, p. 18]. The Qbar equality is the fixed-embedding bridge from this real value.
-/
theorem conjugation_origin : c e = e := by
  apply Galois.embed.injective
  change Galois.embed (c e) = Galois.embed e
  rw [ClassFieldInfinite.complexConjugation_embed, embed_origin]
  exact Complex.conj_ofReal _

/-- The analytic reciprocal law is lifted on the actual arithmetic labels. [RW26, Prop. 7, Cor. 1,
p. 14, p. 3, footnote 2]; [RW-rec, Prop. 2(7), Prop. 7, p. 4, p. 18]. The nonzero hypothesis
excludes the different plus origin. -/
theorem conjugation_value_neg_mul (x : ActualLattice.Group M hM) (hx : x ≠ 0) :
    c (E (-x)) * E x = 1 := by
  obtain ⟨y, rfl⟩ := (ActualLattice.labelEquiv M hM).surjective x
  have hy : y ≠ 0 := by
    intro hy
    apply hx
    rw [hy, map_zero]
  apply Galois.embed.injective
  change Galois.embed (c (E (-(ActualLattice.labelEquiv M hM y))) *
    E (ActualLattice.labelEquiv M hM y)) = Galois.embed 1
  rw [map_mul, map_one, ClassFieldInfinite.complexConjugation_embed,
    ← (ActualLattice.labelEquiv M hM).map_neg,
    ActualValues.embed_valueLift, ActualValues.embed_valueLift,
    ActualValues.value_label, ActualValues.value_label]
  simpa only [starRingEnd_apply, neg_neg] using
    ConjugationSpecialValue.specialValuePlus_conj_mul_neg M hM (-y) (neg_ne_zero.mpr hy)

/-- The exact normalized reciprocal needed after the double-sign action. [RW26, Prop. 7, Cor. 1, p.
14, p. 3, footnote 2]; [RW-rec, Prop. 7, p. 18]. This is an algebraic bridge using the existing
normalizedLift, not an extra definition of the normalized value. -/
theorem conjugation_normalized_neg (x : ActualLattice.Group M hM) (hx : x ≠ 0) :
    c (U (-x)) = 1 / (e * E x) := by
  change c (SplitPrimeValues.valueLift _ _ (-x) / SplitPrimeValues.valueLift _ _ 0) = _
  rw [SplitPrimeValues.actual_valueLift, SplitPrimeValues.actual_valueLift,
    map_div₀, conjugation_origin,
    eq_inv_of_mul_eq_one_left (conjugation_value_neg_mul M hM x hx)]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]

/-- Every flip has the second real embedding on the actual epsilon. [RW26, p. 20] dictionary;
[RW-rec, p. 3] setup, and p. 17 Prop. 7. This is the explicit restriction/embedding bridge. -/
theorem embed_flip_epsilon (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    Galois.embed (τ (ActualField.epsilon M hM : Galois.Qbar)) =
      (ActualField.sigma₂ M hM (ActualField.epsilon M hM) : ℂ) := by
  exact (ActualField.inducesNontrivial_iff M hM τ).mp hτ (ActualField.epsilon M hM)

/-- The conjugate period is the positive inverse. Total positivity is [RW-rec, p. 18]; [RW26, p. 3,
p. 20, (4)]; [RW-rec, p. 3] is the setup. This specializes the existing two-embedding period
identities. -/
theorem conjugate_epsilon_positive :
    ActualField.sigma₂ M hM (ActualField.epsilon M hM) =
        (L4.specialValueEpsilon M)⁻¹ ∧
      0 < ActualField.sigma₂ M hM (ActualField.epsilon M hM) := by
  rw [ActualField.sigma₂_epsilon, ActualField.sigma₁_epsilon]
  exact ⟨rfl, inv_pos.mpr (lt_trans zero_lt_one (L4.specialValueEpsilon_gt_one M hM))⟩

/-- An arbitrary flipped root has the positive second-embedding square. [RW26, p. 3, p. 20, (4)];
[RW-rec, Def. 1, Prop. 7, p. 3, p. 18]. This square identity is the algebraic bridge behind total
realness. -/
theorem flip_origin_sq (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    Galois.embed (τ e) ^ 2 =
      (ActualField.sigma₂ M hM (ActualField.epsilon M hM) : ℂ) := by
  calc
    Galois.embed (τ e) ^ 2 = Galois.embed (τ (e ^ 2)) := by simp only [map_pow]
    _ = _ := by rw [origin_sq, embed_flip_epsilon M hM τ hτ]

/-- Reality follows from the positive square and makes no sign choice. [RW26, p. 3, (4)] supplies
the root normalization; [RW-rec, Prop. 7, p. 18] states total realness. There is no independent
theorem for this elementary complex algebra bridge from the square identity to vanishing imaginary
part. -/
theorem flip_origin_im_eq_zero (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    (Galois.embed (τ e)).im = 0 := by
  exact Prop7FinalConjugationAux.im_eq_zero_of_sq_eq_pos_real _ _
    (conjugate_epsilon_positive M hM).2 (flip_origin_sq M hM τ hτ)

/-- Conjugation fixes either real sign of the flipped root. [RW26, p. 3, (4)] supplies the root
normalization; [RW-rec, Prop. 7, p. 18]. The Qbar equality is a fixed-embedding bridge from reality,
not positivity of the flipped root. -/
theorem conjugation_flip_origin (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    c (τ e) = τ e := by
  apply Galois.embed.injective
  change Galois.embed (c (τ e)) = Galois.embed (τ e)
  rw [ClassFieldInfinite.complexConjugation_embed]
  apply Complex.ext
  · rfl
  · simp only [Complex.star_def, Complex.conj_im,
      flip_origin_im_eq_zero M hM τ hτ, neg_zero]

/-- The conjugated conjugation fixes e, as needed to remove normalization. [RW26, p. 3, (4)]
supplies the root normalization; [RW-rec, Prop. 7, p. 18]. No class-field membership or Artin
assertion is required for this algebraic root bridge. -/
theorem conjugated_conjugation_origin (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    (τ⁻¹ * c * τ) e = e := by
  simp only [AlgEquiv.mul_apply, conjugation_flip_origin M hM τ hτ,
    AlgEquiv.coe_inv, AlgEquiv.symm_apply_apply]

/-- Matrix labels recover exactly the same nonzero reciprocal law. [RW26, Prop. 7, Cor. 1, p. 14, p.
3, footnote 2]; [RW-rec, Prop. 2(7), p. 4]. The matrixLift equality is the existing arithmetic-label
Qbar bridge. -/
theorem matrixLift_conjugation_neg_mul (x : L4.SpecialValueGroup M) (hx : x ≠ 0) :
    c (ActualValues.matrixLift M hM (-x)) * ActualValues.matrixLift M hM x = 1 := by
  have h := conjugation_value_neg_mul M hM (ActualLattice.labelEquiv M hM x)
    (fun h => hx ((ActualLattice.labelEquiv M hM).map_eq_zero_iff.mp h))
  simpa only [← (ActualLattice.labelEquiv M hM).map_neg,
    ActualValues.valueLift_label] using h

/-- Elementary step from `star z = z⁻¹` to `‖z‖ = 1`, used in the proof of [RW-rec, Prop. 7, p. 18]
together with the reciprocal law of [RW26, Prop. 7, p. 14]. The hypothesis `z ≠ 0` is explicit. -/
theorem norm_eq_one_of_conj_eq_inv (z : ℂ) (hz : z ≠ 0)
    (hconj : star z = z⁻¹) : ‖z‖ = 1 := by
  exact Prop7FinalConjugationAux.norm_eq_one_of_conj_eq_inv z hz hconj

end SICLean.L5.Prop7FinalConjugation
