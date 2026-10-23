import SICLean.Final.Unconditional
import SICLean.L4.M75Gaussian

set_option autoImplicit false

noncomputable section

open Classical
open scoped BigOperators MatrixGroups

namespace SICLean.L5.FiniteFourierAux

open L4 L3.M75.Gaussian

variable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)

lemma pairing_neg_right (x y : SpecialValueGroup M) :
    specialValuePairing M hM x (-y) = (specialValuePairing M hM x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← pairing_add_right, add_neg_cancel, pairing_zero_right]

lemma pairing_neg_left (x y : SpecialValueGroup M) :
    specialValuePairing M hM (-x) y = (specialValuePairing M hM x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← pairing_add_left, add_neg_cancel, pairing_zero_left]

lemma pairing_neg_swap (x y : SpecialValueGroup M) :
    specialValuePairing M hM x (-y) = specialValuePairing M hM y (-x) := by
  rw [pairing_neg_right, pairing_neg_right, pairing_symmetric M hM x y]

lemma sum_pairing [Fintype (SpecialValueGroup M)] (u : SpecialValueGroup M) :
    (∑ x, specialValuePairing M hM x u) =
      if u = 0 then (specialValueOrder M : ℂ) else 0 := by
  calc
    _ = G2.StripCounting.groupSum M hM (fun x => specialValuePairing M hM x u) := by
      unfold G2.StripCounting.groupSum
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      rfl
    _ = _ := G2.DegenerateParameters.groupSum_pairing M hM u

lemma sum_kernel_product [Fintype (SpecialValueGroup M)] (x y : SpecialValueGroup M) :
    (∑ t, specialValuePairing M hM x (-t) * specialValuePairing M hM t (-y)) =
      if x = -y then (specialValueOrder M : ℂ) else 0 := by
  simp_rw [pairing_neg_swap M hM x, ← pairing_add_right]
  rw [sum_pairing]
  congr 1
  apply propext
  constructor <;> intro h
  · have : x + y = 0 := by simpa [add_comm] using congrArg Neg.neg h
    exact eq_neg_of_add_eq_zero_left this
  · rw [h, neg_neg, add_neg_cancel]

lemma origin_difference :
    specialValuePlus M hM 0 - specialValueMinus M hM 0 =
      (Real.sqrt (specialValueOrder M : ℝ) : ℂ) := by
  have h := G2.DegenerateParameters.origin_difference (modularInverseReflection M)
    (G2.ReflectionGeometry.reflection_admissible M hM)
  simpa only [G2.ReflectionGeometry.reflection_order,
    ← (G2.AttractingIdentities.reflection_origins M hM).2.2.1,
    ← (G2.AttractingIdentities.reflection_origins M hM).2.2.2] using h

end SICLean.L5.FiniteFourierAux
