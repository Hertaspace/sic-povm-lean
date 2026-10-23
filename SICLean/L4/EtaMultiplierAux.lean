import SICLean.L4.QProduct

set_option autoImplicit false

/-!
Elementary exponential, square-root and product identities used by the fixed η-multiplier
statements. This module does not depend on `EtaMultiplier` and does not introduce a second
multiplier or a second η function.
-/

noncomputable section

open scoped UpperHalfPlane

namespace SICLean.L4.EtaMultiplierAux

local notation "E" => fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)

theorem exp_phase_add (z w : ℂ) : E (z + w) = E z * E w := by
  simp only [mul_add, Complex.exp_add]

theorem exp_phase_sub (z w : ℂ) : E (z - w) = E z / E w := by
  simp only [mul_sub, Complex.exp_sub]

theorem exp_phase_zero : E 0 = 1 := by simp

theorem exp_phase_two_mul (z : ℂ) : E (2 * z) = E z ^ 2 := by
  rw [show 2 * z = z + z by ring, exp_phase_add]
  ring

theorem sqrt_mul_self (z : ℂ) : Complex.sqrt z * Complex.sqrt z = z := by
  simpa only [Complex.sqrt, sq, Nat.cast_ofNat] using
    Complex.cpow_nat_inv_pow z (n := 2) (by decide)

theorem sqrt_affine_real (c d : ℤ) (t : ℝ) (ht : 0 < (c : ℝ) * t + (d : ℝ)) :
    Complex.sqrt ((c : ℂ) * (t : ℂ) + (d : ℂ)) =
      (Real.sqrt ((c : ℝ) * t + (d : ℝ)) : ℂ) := by
  have h : (c : ℂ) * (t : ℂ) + (d : ℂ) = (((c : ℝ) * t + (d : ℝ)) : ℂ) := by
    simp
  rw [h, Complex.sqrt_of_nonneg]
  · simp
  · exact_mod_cast ht.le

theorem eta_eq_exp_mul_qPochhammer (z : ℂ) :
    ModularForm.eta z = E (z / 24) * qPochhammer (E z) (E z) := by
  unfold ModularForm.eta qPochhammer
  congr 1
  · simp only [Function.Periodic.qParam]
    congr 1
    push_cast
    ring
  · apply tprod_congr
    intro n
    rw [ModularForm.eta_q_eq_pow]
    simp [pow_succ']

theorem qPochhammer_neg_one_eq_eta_double (τ : ℍ) :
    qPochhammer (-1) (E τ) =
      2 * (ModularForm.eta (2 * (τ : ℂ)) / ModularForm.eta τ) / E ((τ : ℂ) / 24) := by
  have hq0 : 0 < ‖E τ‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hq1 : ‖E τ‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hQ := qPochhammer_q_ne_zero (E τ) hq0 hq1
  have he : E ((τ : ℂ) / 24) ≠ 0 := Complex.exp_ne_zero _
  rw [qPochhammer_neg_one (E τ) hq0 hq1, qPochhammer_neg_q (E τ) hq0 hq1,
    eta_eq_exp_mul_qPochhammer, eta_eq_exp_mul_qPochhammer, exp_phase_two_mul,
    show 2 * (τ : ℂ) / 24 = 2 * ((τ : ℂ) / 24) by ring, exp_phase_two_mul]
  field_simp

end SICLean.L4.EtaMultiplierAux
