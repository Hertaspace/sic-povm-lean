import SICLean.L4.SpecialValueReflection

set_option autoImplicit false

/-!
# Integer-row computations for the concrete Gaussian

The sign in [RW26, (3)] is absorbed into a half-integral phase. Polarization
then differs from the literal positive-sign pairing by the integer u₂v₁.
All declarations belong to this auxiliary namespace.
-/

noncomputable section

open scoped MatrixGroups
open SICLean.L4

namespace SICLean.L4.M75GaussianAux

def gaussianPhase (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℂ :=
  (specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u : ℂ) /
      (2 * (specialValueOrder M : ℂ)) + ((u.1 + u.2 + u.1 * u.2 : ℤ) : ℂ) / 2

theorem gaussianLift_eq_exp (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    specialValueGaussianLift M u = e (gaussianPhase M u) := by
  unfold specialValueGaussianLift gaussianPhase
  rw [← e_half_int, ← e_add']
  congr 1
  ring

theorem pairingLift_add_left (M : SL(2, ℤ)) (u v w : ℤ × ℤ) :
    specialValuePairingLift M (u + v) w =
      specialValuePairingLift M u w * specialValuePairingLift M v w := by
  have h :
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (u + v) -
        (u + v)) w =
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) w +
        specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) v - v) w := by
    simp only [specialValueOmega, L2r.rowAction, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub]
    ring
  unfold specialValuePairingLift
  rw [h, Int.cast_add, add_div, e_add']

theorem pairingLift_add_right (M : SL(2, ℤ)) (u v w : ℤ × ℤ) :
    specialValuePairingLift M u (v + w) =
      specialValuePairingLift M u v * specialValuePairingLift M u w := by
  have h :
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) (v + w) =
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) v +
        specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) w := by
    simp only [specialValueOmega, Prod.fst_add, Prod.snd_add]
    ring
  unfold specialValuePairingLift
  rw [h, Int.cast_add, add_div, e_add']

theorem gaussianPhase_add (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    gaussianPhase M (u + v) = gaussianPhase M u + gaussianPhase M v +
      (specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) v : ℂ) /
        (specialValueOrder M : ℂ) + ((u.2 * v.1 : ℤ) : ℂ) := by
  have hN : (specialValueOrder M : ℂ) ≠ 0 := by
    exact_mod_cast (specialValueOrder_pos M hM).ne'
  unfold gaussianPhase
  simp only [specialValueOmega, L2r.rowAction, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub]
  push_cast
  field_simp [hN]
  simp only [specialValueOrder]
  push_cast
  ring

theorem gaussianLift_add (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    specialValueGaussianLift M (u + v) =
      specialValueGaussianLift M u * specialValueGaussianLift M v *
        specialValuePairingLift M u v := by
  rw [gaussianLift_eq_exp, gaussianPhase_add M hM, e_add', e_intCast, mul_one,
    e_add', e_add', ← gaussianLift_eq_exp, ← gaussianLift_eq_exp]
  rfl

theorem pairingLift_symmetric (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    specialValuePairingLift M u v = specialValuePairingLift M v u := by
  apply mul_left_cancel₀
    (mul_ne_zero (specialValueGaussianLift_ne_zero M u) (specialValueGaussianLift_ne_zero M v))
  calc
    specialValueGaussianLift M u * specialValueGaussianLift M v *
        specialValuePairingLift M u v = specialValueGaussianLift M (u + v) :=
      (gaussianLift_add M hM u v).symm
    _ = specialValueGaussianLift M (v + u) := by rw [add_comm]
    _ = specialValueGaussianLift M u * specialValueGaussianLift M v *
        specialValuePairingLift M v u := by
      rw [gaussianLift_add M hM]
      ring

theorem pairingLift_self (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    specialValuePairingLift M u u = specialValueGaussianLift M u ^ 2 := by
  have hN : (specialValueOrder M : ℂ) ≠ 0 := by
    exact_mod_cast (specialValueOrder_pos M hM).ne'
  have hphase : 2 * gaussianPhase M u =
      (specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) u : ℂ) /
        (specialValueOrder M : ℂ) + ((u.1 + u.2 + u.1 * u.2 : ℤ) : ℂ) := by
    unfold gaussianPhase
    simp only [specialValueOmega, Prod.fst_sub, Prod.snd_sub]
    push_cast
    field_simp [hN]
    ring
  rw [gaussianLift_eq_exp, e_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [hphase, e_add', e_intCast, mul_one]
  rfl

end SICLean.L4.M75GaussianAux
