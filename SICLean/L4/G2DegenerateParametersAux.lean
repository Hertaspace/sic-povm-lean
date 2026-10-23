import SICLean.L4.G2SpecialValueBridge

set_option autoImplicit false

noncomputable section

open scoped BigOperators MatrixGroups

namespace SICLean.L4.G2DegenerateParametersAux

open G2 G2.SpecialValueBridge G2.ReflectionGeometry

/-- An integral exponential phase detects divisibility of its numerator. -/
lemma e_div_eq_one_dvd (n N : ℤ) (hN : N ≠ 0)
    (h : e ((n : ℂ) / (N : ℂ)) = 1) : N ∣ n := by
  obtain ⟨k, hk⟩ := e_eq_one_iff_int h
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hk' : (n : ℂ) = (N : ℂ) * (k : ℂ) := by
    rw [div_eq_iff hNc] at hk
    simpa only [mul_comm] using hk
  exact ⟨k, by exact_mod_cast hk'⟩

lemma pairingLift_add_left (M : SL(2, ℤ)) (x y u : ℤ × ℤ) :
    specialValuePairingLift M (x + y) u =
      specialValuePairingLift M x u * specialValuePairingLift M y u := by
  unfold specialValuePairingLift
  rw [← e_add']
  congr 1
  rw [← add_div]
  congr 1
  simp only [specialValueOmega, L2r.rowAction, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

/-- Test both basis rows. The two divisibilities imply the full row-lattice criterion; no cyclic
coordinate or scalar zero-class test is used. -/
lemma pairingLift_kernel_mem (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (h : ∀ x : ℤ × ℤ, specialValuePairingLift M x u = 1) :
    u ∈ specialValueLattice M := by
  have hN : specialValueOrder M ≠ 0 := ne_of_gt (specialValueOrder_pos M hM)
  have h₁ := e_div_eq_one_dvd _ _ hN (h (1, 0))
  have h₂ := e_div_eq_one_dvd _ _ hN (h (0, 1))
  change specialValueOrder M ∣ specialValueOmega
    (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (1, 0) - (1, 0)) u at h₁
  change specialValueOrder M ∣ specialValueOmega
    (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (0, 1) - (0, 1)) u at h₂
  apply (specialValueLattice_mem_iff M hM u).mpr
  constructor
  · have heq : (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u).1 - u.1 =
        specialValueOmega
          (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (0, 1) - (0, 1)) u +
          specialValueOrder M * u.1 := by
      simp [specialValueOmega, L2r.rowAction, specialValueOrder]
      ring
    rw [heq]
    exact dvd_add h₂ (dvd_mul_right (specialValueOrder M) u.1)
  · have heq : (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u).2 - u.2 =
        -specialValueOmega
          (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (1, 0) - (1, 0)) u +
          specialValueOrder M * u.2 := by
      simp [specialValueOmega, L2r.rowAction, specialValueOrder]
      ring
    rw [heq]
    exact dvd_add (dvd_neg.mpr h₁) (dvd_mul_right (specialValueOrder M) u.2)

lemma repelling_agree_off_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) (hx : x ≠ 0) :
    repellingPlus M hM x = repellingMinus M hM x := by
  rw [repellingPlus_reflection, repellingMinus_reflection]
  apply specialValue_agree_off_zero
  exact fun h => hx ((reflectionEquiv M).injective (by simpa using h))

lemma repellingMinus_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) : repellingMinus M hM x ≠ 0 := by
  rw [repellingMinus_reflection]
  exact specialValueMinus_ne_zero _ _ _

lemma sqrt_epsilon_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (Real.sqrt (epsilon M) : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (epsilon_pos M hM))

lemma sqrt_order_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (Real.sqrt (specialValueOrder M : ℝ) : ℂ) ≠ 0 := by
  have hN : (0 : ℝ) < specialValueOrder M := by
    exact_mod_cast specialValueOrder_pos M hM
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hN)

lemma sqrt_order_sq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (Real.sqrt (specialValueOrder M : ℝ) : ℂ) ^ 2 = (specialValueOrder M : ℂ) := by
  have hN : (0 : ℝ) ≤ specialValueOrder M := by
    exact_mod_cast (specialValueOrder_pos M hM).le
  exact_mod_cast Real.sq_sqrt hN

end SICLean.L4.G2DegenerateParametersAux
