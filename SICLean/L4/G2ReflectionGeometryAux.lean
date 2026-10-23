import SICLean.L4.SpecialValueReflection

set_option autoImplicit false

/-!
# Elementary row, lattice, and phase computations for inverse reflection

This file does not import `G2ReflectionGeometry`. Its row equivalence has the same literal function
as the equivalence in that file, so its lattice and representative formulas can be transferred by
definitional reduction.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2ReflectionGeometryAux

/-- The literal action of the diagonal reflection on integer rows. -/
def rowReflection : (ℤ × ℤ) ≃+ (ℤ × ℤ) where
  toFun x := (x.1, -x.2)
  invFun x := (x.1, -x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [add_comm]

@[simp] theorem rowReflection_apply (x : ℤ × ℤ) :
    rowReflection x = (x.1, -x.2) := rfl

@[simp] theorem rowReflection_involutive (x : ℤ × ℤ) :
    rowReflection (rowReflection x) = x := by simp

theorem reflection_involutive (M : SL(2, ℤ)) :
    modularInverseReflection (modularInverseReflection M) = M := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularInverseReflection, modularInverseReflectionMatrix]

theorem reflection_order (M : SL(2, ℤ)) :
    specialValueOrder (modularInverseReflection M) = specialValueOrder M := by
  simp [specialValueOrder, modularInverseReflection, modularInverseReflectionMatrix]
  ring

/-- An explicit witness for the reflected lattice generator. -/
theorem rowReflection_generator (M : SL(2, ℤ)) (w : ℤ × ℤ) :
    rowReflection (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w) =
      L2r.rowAction
        (((modularInverseReflection M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1)
        (-rowReflection (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w)) := by
  have hd := det_coe_int M
  ext
  · simp [rowReflection, L2r.rowAction, modularInverseReflection,
      modularInverseReflectionMatrix, Matrix.sub_apply]
    linear_combination w.1 * hd
  · simp [rowReflection, L2r.rowAction, modularInverseReflection,
      modularInverseReflectionMatrix, Matrix.sub_apply]
    linear_combination -w.2 * hd

/-- Reflection carries the actual row range onto the reflected row range. -/
theorem rowReflection_lattice (M : SL(2, ℤ)) :
    (specialValueLattice M).map rowReflection.toAddMonoidHom =
      specialValueLattice (modularInverseReflection M) := by
  apply le_antisymm
  · rintro v ⟨x, hx, rfl⟩
    change ∃ w, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w = x at hx
    obtain ⟨w, rfl⟩ := hx
    exact ⟨_, (rowReflection_generator M w).symm⟩
  · intro v hv
    refine ⟨rowReflection v, ?_, by simp⟩
    change ∃ w, L2r.rowAction
      (((modularInverseReflection M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) w = v at hv
    obtain ⟨w, rfl⟩ := hv
    have h := rowReflection_generator (modularInverseReflection M) w
    rw [reflection_involutive M] at h
    exact ⟨_, h.symm⟩

/-- The Gaussian's alternating numerator is unchanged, as an integer. -/
theorem gaussianNumerator_reflection (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    specialValueOmega
      (L2r.rowAction (modularInverseReflection M : Matrix (Fin 2) (Fin 2) ℤ)
        (u.1, -u.2)) (u.1, -u.2) =
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u := by
  simp [specialValueOmega, L2r.rowAction, modularInverseReflection,
    modularInverseReflectionMatrix]
  ring

/-- The parity factor is also unchanged, including negative integer powers. -/
theorem gaussianParity_reflection (u : ℤ × ℤ) :
    (-1 : ℂ) ^ (u.1 + -u.2 + u.1 * -u.2) =
      (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) := by
  have he : u.1 + -u.2 + u.1 * -u.2 =
      (u.1 + u.2 + u.1 * u.2) + 2 * (-u.2 * (u.1 + 1)) := by ring
  rw [he, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

/-- Representative-level transport of the literal [RW26] Gaussian. -/
theorem gaussianLift_reflection (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    specialValueGaussianLift (modularInverseReflection M) (u.1, -u.2) =
      specialValueGaussianLift M u := by
  unfold specialValueGaussianLift
  rw [gaussianNumerator_reflection, reflection_order]
  exact congrArg (fun z => z * e
    ((specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u : ℂ) /
      (2 * (specialValueOrder M : ℂ)))) (gaussianParity_reflection u)

/-- The pairing's two integer numerators differ by an integer multiple of N. -/
theorem pairingNumerator_reflection (M : SL(2, ℤ)) (u v : ℤ × ℤ) :
    specialValueOmega
      (L2r.rowAction (modularInverseReflection M : Matrix (Fin 2) (Fin 2) ℤ)
          (u.1, -u.2) - (u.1, -u.2)) (v.1, -v.2) =
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) v -
        specialValueOrder M * specialValueOmega u v := by
  simp [specialValueOmega, specialValueOrder, L2r.rowAction,
    modularInverseReflection, modularInverseReflectionMatrix]
  ring

/-- Representative-level transport of the positive-sign [RW26] character. -/
theorem pairingLift_reflection (M : SL(2, ℤ)) (u v : ℤ × ℤ) :
    specialValuePairingLift (modularInverseReflection M) (u.1, -u.2) (v.1, -v.2) =
      specialValuePairingLift M u v := by
  unfold specialValuePairingLift
  rw [pairingNumerator_reflection, reflection_order]
  by_cases hN : (specialValueOrder M : ℂ) = 0
  · simp [hN]
  · have he :
        ((specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) v -
            specialValueOrder M * specialValueOmega u v : ℤ) : ℂ) /
          (specialValueOrder M : ℂ) =
        (specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) v : ℂ) /
          (specialValueOrder M : ℂ) + (-specialValueOmega u v : ℤ) := by
      push_cast
      field_simp
      ring
    rw [he, e_add', e_intCast, mul_one]

end SICLean.L4.G2ReflectionGeometryAux
