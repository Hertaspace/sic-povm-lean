import SICLean.L5.LocalFourierSetup
import SICLean.L5.FiniteAlgebraicTransport

set_option autoImplicit false

/-!
# Valuation-ring operations for the concrete local Fourier calls

These helpers only express closure under ring operations. They impose no integrality or
unit hypothesis on the actual special-value function.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L5.LocalActualFourierAux

open L4

variable {L : Type*} [Field L] (v : AddValuation L (WithTop ℝ))

lemma value_mul_nonneg {a b : L} (ha : 0 ≤ v a) (hb : 0 ≤ v b) :
    0 ≤ v (a * b) := by
  rw [v.map_mul]
  exact add_nonneg ha hb

lemma value_inv_nonneg_of_zero {a : L} (ha : v a = 0) :
    0 ≤ v a⁻¹ := by
  simp only [v.map_inv, ha, neg_zero, le_refl]

lemma value_add_nonneg {a b : L} (ha : 0 ≤ v a) (hb : 0 ≤ v b) :
    0 ≤ v (a + b) :=
  v.map_le_add ha hb

lemma value_sub_nonneg {a b : L} (ha : 0 ≤ v a) (hb : 0 ≤ v b) :
    0 ≤ v (a - b) :=
  v.map_le_sub ha hb

lemma delta_nonneg (v : AddValuation Galois.Qbar (WithTop ℝ))
    (M : SL(2, ℤ)) (x : L4.SpecialValueGroup M) :
    0 ≤ v (FiniteAlgebraicTransport.delta M x) := by
  classical
  by_cases hx : x = 0 <;> simp [FiniteAlgebraicTransport.delta, hx]

/-- Scalar multiplication in the existing fixed-Qbar finite sum. -/
lemma fourier_const_mul (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (c : Galois.Qbar) (f : SpecialValueGroup M → Galois.Qbar)
    (y : SpecialValueGroup M) :
    FiniteAlgebraicTransport.fourier M hM (fun t => c * f t) y =
      c * FiniteAlgebraicTransport.fourier M hM f y := by
  classical
  let : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  let : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  unfold FiniteAlgebraicTransport.fourier FiniteAlgebraicTransport.normalizedSum
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  ring

end SICLean.L5.LocalActualFourierAux
