import SICLean.L2a.Inputs

/-! # Scalar, phase, and operator statements. -/

noncomputable section

open Matrix

namespace SICLean.L2a

theorem epsilon_gt_one {M : ℕ} (hM : 4 ≤ M) : 1 < epsilon M := by
  have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hs := Real.sqrt_nonneg (((M : ℝ) - 1) ^ 2 - 4)
  unfold epsilon
  rw [one_lt_div (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem epsilon_quadratic {M : ℕ} (hM : 4 ≤ M) :
    epsilon M ^ 2 - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
  have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hnng : (0 : ℝ) ≤ ((M : ℝ) - 1) ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hnng
  unfold epsilon
  field_simp
  nlinarith

theorem sqrtEpsilon_ne_zero {M : ℕ} (hM : 4 ≤ M) : sqrtEpsilon M ≠ 0 := by
  have h1 : (0 : ℝ) < epsilon M := lt_trans (by norm_num) (epsilon_gt_one hM)
  intro h
  apply absurd (Real.sqrt_eq_zero'.mp (Complex.ofReal_eq_zero.mp h))
  exact (not_le.mpr h1)

theorem sqrtEpsilon_sub_inv {M : ℕ} (hM : 4 ≤ M) :
    sqrtEpsilon M - (sqrtEpsilon M)⁻¹ = convolutionScalar M := by
  have hε : (1 : ℝ) < epsilon M := epsilon_gt_one hM
  have hε0 : (0 : ℝ) < epsilon M := by linarith
  have hw2 : Real.sqrt (epsilon M) ^ 2 = epsilon M := Real.sq_sqrt (le_of_lt hε0)
  have hw1 : (1 : ℝ) ≤ Real.sqrt (epsilon M) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have h4 : Real.sqrt (epsilon M) ^ 4 = (epsilon M) ^ 2 := by
    rw [show ((4 : ℕ)) = 2 * 2 from rfl, pow_mul, hw2]
  have hwq : Real.sqrt (epsilon M) ^ 4 - ((M : ℝ) - 1) * Real.sqrt (epsilon M) ^ 2 + 1 = 0 := by
    rw [h4, hw2]
    exact epsilon_quadratic hM
  have key : (Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹) ^ 2 = ((M : ℝ) - 3) := by
    have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
    field_simp
    nlinarith
  have hnn : (0 : ℝ) ≤ Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹ := by
    have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
    by_contra hc
    push_neg at hc
    have h8 := mul_lt_mul_of_pos_right hc hwpos
    simp only [zero_mul] at h8
    rw [mul_comm, mul_sub, mul_inv_cancel₀ (ne_of_gt hwpos)] at h8
    nlinarith
  have hfin : Real.sqrt (((M : ℝ) - 3)) = Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹ :=
    (Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hnn).mpr (by rw [← pow_two]; exact key.symm)
  have h2 : (Real.sqrt ((M : ℝ) - 3) : ℂ)
      = (Real.sqrt (epsilon M) : ℂ) - ((Real.sqrt (epsilon M) : ℝ) : ℂ)⁻¹ := by
    rw [hfin, Complex.ofReal_sub, Complex.ofReal_inv]
  simp only [sqrtEpsilon, convolutionScalar]
  exact h2.symm

theorem sqrtEpsilon_cube {M : ℕ} (hM : 4 ≤ M) :
    sqrtEpsilon M ^ 3 = ((M : ℂ) - 1) * sqrtEpsilon M - (sqrtEpsilon M)⁻¹ := by
  have hν : sqrtEpsilon M ≠ 0 := sqrtEpsilon_ne_zero hM
  have hε0 : (0 : ℝ) < epsilon M := lt_trans (by norm_num) (epsilon_gt_one hM)
  have h2 : sqrtEpsilon M * sqrtEpsilon M = (epsilon M : ℂ) := by
    simp only [sqrtEpsilon]
    exact_mod_cast Real.mul_self_sqrt (le_of_lt hε0)
  have hq : epsilon M * epsilon M - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
    have h := epsilon_quadratic hM
    linear_combination h
  have hq2 : (epsilon M : ℂ) * (epsilon M : ℂ) - ((M : ℂ) - 1) * (epsilon M : ℂ) + 1 = 0 := by
    exact_mod_cast hq
  apply mul_right_cancel₀ hν
  have hν3 : sqrtEpsilon M ^ 3 * sqrtEpsilon M = sqrtEpsilon M ^ 4 := by
    rw [pow_succ, show ((4 : ℕ)) = 2 + 2 from rfl, pow_add, pow_two]
    ring
  have hq3 : sqrtEpsilon M ^ 4 - ((M : ℂ) - 1) * sqrtEpsilon M ^ 2 + 1 = 0 := by
    rw [show ((4 : ℕ)) = 2 + 2 from rfl, pow_add, pow_two, h2]
    exact hq2
  rw [hν3, sub_mul, mul_assoc, inv_mul_cancel₀ hν]
  linear_combination hq3

theorem denominator_eq_sqrt {M : ℕ} (hM : 4 ≤ M) :
    denominator M = (Real.sqrt ((M : ℝ) + 1) : ℂ) := by
  have hε : (1 : ℝ) < epsilon M := epsilon_gt_one hM
  have hε0 : (0 : ℝ) < epsilon M := by linarith
  have hw2 : Real.sqrt (epsilon M) ^ 2 = epsilon M := Real.sq_sqrt (le_of_lt hε0)
  have hw1 : (1 : ℝ) ≤ Real.sqrt (epsilon M) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have h4 : Real.sqrt (epsilon M) ^ 4 = (epsilon M) ^ 2 := by
    rw [show ((4 : ℕ)) = 2 * 2 from rfl, pow_mul, hw2]
  have hq : epsilon M * epsilon M - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
    have h := epsilon_quadratic hM
    linear_combination h
  have key : (Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹) ^ 2 = ((M : ℝ) + 1) := by
    have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
    field_simp
    nlinarith [hw2]
  have hnn : (0 : ℝ) ≤ Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹ := by
    have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
    have := inv_nonneg.mpr (le_of_lt hwpos)
    linarith
  have hfin : Real.sqrt (((M : ℝ) + 1)) = Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹ :=
    (Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hnn).mpr (by rw [← pow_two]; exact key.symm)
  have h2 : (Real.sqrt ((M : ℝ) + 1) : ℂ)
      = (Real.sqrt (epsilon M) : ℂ) + ((Real.sqrt (epsilon M) : ℝ) : ℂ)⁻¹ := by
    rw [hfin, Complex.ofReal_add, Complex.ofReal_inv]
  simp only [denominator, sqrtEpsilon]
  exact h2.symm

theorem denominator_ne_zero {M : ℕ} (hM : 4 ≤ M) : denominator M ≠ 0 := by
  rw [denominator_eq_sqrt hM]
  intro h
  have h1 : Real.sqrt ((M : ℝ) + 1) = 0 := Complex.ofReal_eq_zero.mp h
  have h2 : ((M : ℝ) + 1) ≤ 0 := Real.sqrt_eq_zero'.mp h1
  have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  linarith

/-- B's denominator clause is redundant for a ring homomorphism of ℂ. -/
theorem map_denominator_eq_or_neg {M : ℕ} (hM : 4 ≤ M) (τ : ℂ →+* ℂ) :
    τ (denominator M) = (Real.sqrt ((M : ℝ) + 1) : ℂ) ∨
      τ (denominator M) = -(Real.sqrt ((M : ℝ) + 1) : ℂ) := by
  refine sq_eq_sq_iff_eq_or_eq_neg.mp ?_
  have hn : (0 : ℝ) ≤ ((M : ℝ) + 1) := by
    have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hsq : denominator M ^ 2 = ((M : ℂ) + 1) := by
    rw [denominator_eq_sqrt hM]
    exact_mod_cast Real.sq_sqrt hn
  rw [← map_pow τ _ 2, hsq, map_add, map_natCast, map_one]
  exact_mod_cast (Real.sq_sqrt hn).symm

theorem e_eq_omega_zpow (M : ℕ) (n : ℤ) : e M n = omega M ^ n := by
  rw [e, omega_exp]

/-- Phases agree when the exponents are congruent modulo `M`. -/
theorem e_eq_of_dvd {M : ℕ} {n n' : ℤ} (h : ((M : ℕ) : ℤ) ∣ n - n') : e M n = e M n' := by
  by_cases hM : M = 0
  · subst hM
    have hn : n = n' := sub_eq_zero.mp (Int.zero_dvd.mp h)
    rw [hn]
  · rw [e_eq_omega_zpow, e_eq_omega_zpow]
    obtain ⟨q, hq⟩ := h
    have hn : n = n' + ((M : ℕ) : ℤ) * q := by linear_combination hq
    rw [hn, zpow_add₀ (omega_ne_zero M), _root_.zpow_mul, zpow_natCast,
      omega_pow_d_of_ne_zero M hM, _root_.one_zpow, mul_one]

theorem gaussian_eq_lift {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
    gaussian M ((i : ZMod M), (j : ZMod M)) = gaussianLift M i j := by
  have hne : M ≠ 0 := by omega
  haveI : NeZero M := ⟨hne⟩
  have hA : ((M : ℕ) : ℤ) ∣ (((i : ZMod M).val : ℕ) : ℤ) - i := by
    have hv : (((i : ZMod M).val : ℕ) : ℤ) = i % ((M : ℕ) : ℤ) := ZMod.val_intCast i
    refine ⟨-(i / ((M : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv i ((M : ℕ) : ℤ)]
  have hB : ((M : ℕ) : ℤ) ∣ (((j : ZMod M).val : ℕ) : ℤ) - j := by
    have hv : (((j : ZMod M).val : ℕ) : ℤ) = j % ((M : ℕ) : ℤ) := ZMod.val_intCast j
    refine ⟨-(j / ((M : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv j ((M : ℕ) : ℤ)]
  have hdvd : ((M : ℕ) : ℤ) ∣ quadraticForm (((i : ZMod M).val : ℕ) : ℤ)
      (((j : ZMod M).val : ℕ) : ℤ) - quadraticForm i j := by
    have h1 : quadraticForm (((i : ZMod M).val : ℕ) : ℤ) (((j : ZMod M).val : ℕ) : ℤ)
        - quadraticForm i j
        = ((((i : ZMod M).val : ℕ) : ℤ) - i) * ((((i : ZMod M).val : ℕ) : ℤ) + i)
          - ((((i : ZMod M).val : ℕ) : ℤ) - i) * j
          - (((i : ZMod M).val : ℕ) : ℤ) * ((((j : ZMod M).val : ℕ) : ℤ) - j)
          + ((((j : ZMod M).val : ℕ) : ℤ) - j) * ((((j : ZMod M).val : ℕ) : ℤ) + j) := by
      unfold quadraticForm; ring
    rw [h1]
    exact dvd_add (dvd_sub
      (dvd_sub (dvd_mul_of_dvd_left hA _) (dvd_mul_of_dvd_left hA _))
      (dvd_mul_of_dvd_right hB _))
      (dvd_mul_of_dvd_left hB _)
  unfold gaussian gaussianLift
  exact e_eq_of_dvd hdvd

theorem e_mul (M : ℕ) (n n' : ℤ) : e M n * e M n' = e M (n + n') := by
  rw [e_eq_omega_zpow, e_eq_omega_zpow, e_eq_omega_zpow, ← zpow_add₀ (omega_ne_zero M)]

theorem e_inv (M : ℕ) (n : ℤ) : (e M n)⁻¹ = e M (-n) := by
  rw [e_eq_omega_zpow, e_eq_omega_zpow, ← _root_.zpow_neg]

/-- The polarization of i²-ij+j²; no nondegeneracy is claimed. -/
theorem pairing_eq_exp {M : ℕ} (hM : 4 ≤ M) (i j k l : ℤ) :
    pairing M ((i : ZMod M), (j : ZMod M)) ((k : ZMod M), (l : ZMod M)) =
      e M (2 * i * k - i * l - j * k + 2 * j * l) := by
  have h1 : ((i : ZMod M), (j : ZMod M)) + ((k : ZMod M), (l : ZMod M))
      = (((i + k : ℤ) : ZMod M), ((j + l : ℤ) : ZMod M)) := by
    push_cast
    rfl
  have hg1 : gaussian M (((i : ZMod M), (j : ZMod M)) + ((k : ZMod M), (l : ZMod M)))
      = gaussianLift M (i + k) (j + l) := by
    rw [h1]
    exact gaussian_eq_lift hM (i + k) (j + l)
  rw [pairing, hg1, gaussian_eq_lift hM i j, gaussian_eq_lift hM k l]
  rw [gaussianLift, gaussianLift, gaussianLift, div_eq_inv_mul, mul_inv]
  rw [e_inv, e_inv, e_mul, e_mul]
  congr 1
  unfold quadraticForm
  ring

/-- Powers of `-1` in ℂ depend only on the exponent modulo two. -/
theorem negOne_zpow_eq_of_two_dvd {e e' : ℤ} (h : (2 : ℤ) ∣ e - e') :
    (-1 : ℂ) ^ e = (-1 : ℂ) ^ e' := by
  obtain ⟨n, hn⟩ := h
  have he : e = e' + 2 * n := by linear_combination hn
  have h2 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
  rw [he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul, h2, _root_.one_zpow, mul_one]

theorem xi_zpow_exp (M : ℕ) (z : ℤ) :
    xi M ^ z = (-1 : ℂ) ^ z *
      Complex.exp (Real.pi * Complex.I * (z : ℂ) / (M : ℂ)) := by
  have hx : xi M = (-1 : ℂ) * Complex.exp (Real.pi * Complex.I / (M : ℂ)) := by
    rw [xi]
    ring
  have key : Complex.exp (Real.pi * Complex.I * (z : ℂ) / (M : ℂ))
      = Complex.exp (Real.pi * Complex.I / (M : ℂ)) ^ z := by
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  rw [hx, mul_zpow, key]

theorem theta_eq_xi_zpow (M : ℕ) (i j : ℤ) :
    theta M i j = xi M ^ quadraticForm i j := by
  have h1 : (2 : ℤ) ∣ i - i * i := by
    obtain ⟨q, hq⟩ := Int.two_dvd_mul_add_one i
    exact ⟨-q + i, by linear_combination -hq⟩
  have h2 : (2 : ℤ) ∣ j - j * j := by
    obtain ⟨q, hq⟩ := Int.two_dvd_mul_add_one j
    exact ⟨-q + j, by linear_combination -hq⟩
  have hexp : (i + j + i * j) - quadraticForm i j
      = (i - i * i) + (j - j * j) + 2 * (i * j) := by
    unfold quadraticForm; ring
  have hpar : (2 : ℤ) ∣ (i + j + i * j) - quadraticForm i j := by
    rw [hexp]
    exact dvd_add (dvd_add h1 h2) (dvd_mul_right (2 : ℤ) (i * j))
  rw [theta, xi_zpow_exp, negOne_zpow_eq_of_two_dvd hpar]

theorem theta_neg (M : ℕ) (i j : ℤ) : theta M (-i) (-j) = theta M i j := by
  rw [theta_eq_xi_zpow, theta_eq_xi_zpow]
  congr 1
  unfold quadraticForm
  ring

theorem theta_sq (M : ℕ) (i j : ℤ) : theta M i j ^ 2 = gaussianLift M i j := by
  rw [theta_eq_xi_zpow, pow_two, ← zpow_add₀ (xi_ne_zero M)]
  rw [show quadraticForm i j + quadraticForm i j = 2 * quadraticForm i j from by ring]
  rw [← omega_zpow, ← e_eq_omega_zpow, gaussianLift]

/-- The phase `theta M i j` is a `2M`-th root of unity. -/
theorem theta_pow_two_mul {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
    theta M i j ^ (2 * M) = 1 := by
  rw [theta_eq_xi_zpow, ← zpow_natCast (xi M ^ quadraticForm i j) (2 * M),
    ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, xi_zpow_two_mul_d, _root_.one_zpow]

theorem map_theta_norm {M : ℕ} (hM : 4 ≤ M) (τ : ℂ →+* ℂ) (i j : ℤ) :
    ‖τ (theta M i j)‖ = 1 := by
  have hx : τ (theta M i j) ^ (2 * M) = 1 := by
    rw [← map_pow τ, theta_pow_two_mul hM, map_one]
  have hn : ‖τ (theta M i j)‖ ^ (2 * M) = 1 := by
    rw [← Complex.norm_pow, hx]
    simp
  have hn0 : (2 * M : ℕ) ≠ 0 := by omega
  have key : ∀ a : ℝ, 0 ≤ a → a ^ (2 * M) = 1 → a = 1 := by
    intro a ha h
    rcases lt_trichotomy a 1 with h1 | h1 | h1
    · exfalso
      rcases lt_or_ge (0 : ℝ) a with h0 | h0
      · have hin : 1 < a⁻¹ := (one_lt_inv_iff₀).mpr ⟨h0, h1⟩
        have h2 := one_lt_pow₀ hin hn0
        rw [inv_pow, h] at h2
        norm_num at h2
      · have h0e : a = 0 := le_antisymm h0 ha
        rw [h0e, zero_pow hn0] at h
        norm_num at h
    · exact h1
    · have h2 := one_lt_pow₀ h1 hn0
      rw [h] at h2
      linarith
  exact key ‖τ (theta M i j)‖ (norm_nonneg _) hn

theorem xi_pow_M {M : ℕ} (hM : 4 ≤ M) :
    xi M ^ ((M : ℕ) : ℤ) = (-1 : ℂ) ^ (((M : ℕ) + 1 : ℕ) : ℤ) := by
  have hMn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hkey : (M : ℂ) * (Real.pi * Complex.I / (M : ℂ)) = Real.pi * Complex.I := by
    field_simp
  have hexp : Complex.exp (Real.pi * Complex.I / (M : ℂ)) ^ (M : ℕ) = -1 := by
    rw [← Complex.exp_nat_mul, hkey, Complex.exp_pi_mul_I]
  have hR : (-1 : ℂ) ^ (((M + 1 : ℕ) : ℤ)) = (-1 : ℂ) ^ ((M : ℕ) : ℤ) * (-1 : ℂ) := by
    have hc : ((M + 1 : ℕ) : ℤ) = ((M : ℕ) : ℤ) + 1 := by omega
    rw [hc, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [zpow_natCast, xi, neg_pow, hexp, hR, zpow_natCast]

theorem xi_zpow_mul_M {M : ℕ} (hM : 4 ≤ M) (k : ℤ) :
    xi M ^ ((M : ℤ) * k) = (-1 : ℂ) ^ (((M : ℤ) + 1) * k) := by
  have hc : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
  rw [_root_.zpow_mul, xi_pow_M hM, hc, ← _root_.zpow_mul]

/-- The precise sign under a change of lift, needed when M is even. -/
theorem theta_add_period {M : ℕ} (hM : 4 ≤ M) (i j a b : ℤ) :
    theta M (i + (M : ℤ) * a) (j + (M : ℤ) * b) =
      (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j := by
  have hQ : quadraticForm (i + (M : ℤ) * a) (j + (M : ℤ) * b)
      = quadraticForm i j + (M : ℤ) * (2 * (i * a) - i * b - j * a + 2 * (j * b)
        + (M : ℤ) * quadraticForm a b) := by
    unfold quadraticForm; ring
  have hE : (-1 : ℂ) ^ (((M : ℤ) + 1) * (2 * (i * a) - i * b - j * a + 2 * (j * b)
        + (M : ℤ) * quadraticForm a b))
      = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) := by
    refine negOne_zpow_eq_of_two_dvd ?_
    obtain ⟨t, hts⟩ := Int.two_dvd_mul_add_one M
    push_cast at hts
    refine ⟨((M : ℤ) + 1) * (i * a + j * b - i * b - j * a) + t * quadraticForm a b, ?_⟩
    unfold quadraticForm
    linear_combination (a * a - a * b + b * b) * hts
  rw [theta_eq_xi_zpow, theta_eq_xi_zpow, hQ, zpow_add₀ (xi_ne_zero M),
    xi_zpow_mul_M hM, hE,
    mul_comm ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)))]

/-- Multiplying the phase by its displacement removes the lift sign. -/
theorem phased_displacement_add_period {M : ℕ} (hM : 4 ≤ M) (i j a b : ℤ) :
    theta M (i + (M : ℤ) * a) (j + (M : ℤ) * b) •
        D M (toWH (i + (M : ℤ) * a) (j + (M : ℤ) * b)) =
      theta M i j • D M (toWH i j) := by
  have hto : toWH (i + (M : ℤ) * a) (j + (M : ℤ) * b)
      = toWH i j + (M : ℤ) • ((-b, a) : ℤ × ℤ) := by
    show (-(j + (M : ℤ) * b), i + (M : ℤ) * a)
        = ((-j + (M : ℤ) * (-b), i + (M : ℤ) * a) : ℤ × ℤ)
    rw [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have hE : xi M ^ ((M : ℤ) * ((toWH i j).1 * ((-b, a) : ℤ × ℤ).2
        + ((-b, a) : ℤ × ℤ).1 * (toWH i j).2)
        + (M : ℤ) ^ 2 * (((-b, a) : ℤ × ℤ).1 * ((-b, a) : ℤ × ℤ).2))
      = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) := by
    show xi M ^ ((M : ℤ) * (-j * a + -b * i) + (M : ℤ) ^ 2 * (-b * a))
      = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
    have hexp2 : (M : ℤ) * (-j * a + -b * i) + (M : ℤ) ^ 2 * (-b * a)
        = (M : ℤ) * (-j * a + -b * i + (M : ℤ) * (-b * a)) := by
      ring
    rw [hexp2, xi_zpow_mul_M hM]
    refine negOne_zpow_eq_of_two_dvd ?_
    obtain ⟨t, hts⟩ := Int.two_dvd_mul_add_one M
    push_cast at hts
    refine ⟨-((M : ℤ) + 1) * (j * a + i * b) - t * (b * a), ?_⟩
    linear_combination (-(b * a)) * hts
  have hone : (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
      * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) = 1 := by
    have h2 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
    rw [← _root_.zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      show ((M : ℤ) + 1) * (i * b + j * a) + ((M : ℤ) + 1) * (i * b + j * a)
        = 2 * (((M : ℤ) + 1) * (i * b + j * a)) from by ring,
      _root_.zpow_mul, h2, _root_.one_zpow]
  have hs : ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j)
      * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) = theta M i j := by
    have hrw : ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j)
        * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
        = ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
          * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))) * theta M i j := by
      ring
    rw [hrw, hone, one_mul]
  rw [hto, D_add_smul, smul_smul, theta_add_period hM, hE, hs]

theorem qPower_mul_pPower {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
    qPower M i * pPower M j = xi M ^ (-(i * j)) • D M (toWH i j) := by
  haveI : NeZero M := ⟨by omega⟩
  ext a b
  simp only [Matrix.mul_apply, qPower, pPower, D, toWH, Matrix.smul_apply, smul_eq_mul]
  push_cast
  by_cases hL : ((b : ℕ) : ZMod M) = ((a : ℕ) : ZMod M) + (j : ZMod M)
  · have hR : ((a : ℕ) : ZMod M) = ((b : ℕ) : ZMod M) + (-(j : ZMod M)) := by
      linear_combination -hL
    obtain ⟨t, ht⟩ := exists_sub_of_label hL
    have hsum : (∑ k : Fin M, (if a = k then omega M ^ (i * ((k : ℕ) : ℤ)) else 0)
        * (if ((b : ℕ) : ZMod M) = ((k : ℕ) : ZMod M) + (j : ZMod M) then 1 else 0))
        = omega M ^ (i * ((a : ℕ) : ℤ)) := by
      refine (Finset.sum_eq_single (s := Finset.univ) a ?_ ?_).trans ?_
      · intro k _ hk
        rw [if_neg (Ne.symm hk), zero_mul]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
      · show (if a = a then omega M ^ (i * ((a : ℕ) : ℤ)) else 0)
            * (if ((b : ℕ) : ZMod M) = ((a : ℕ) : ZMod M) + (j : ZMod M) then 1 else 0)
            = omega M ^ (i * ((a : ℕ) : ℤ))
        rw [if_pos rfl, if_pos hL, mul_one]
    rw [hsum, if_pos hR, omega_zpow, omega_zpow,
      ← _root_.zpow_add₀ (xi_ne_zero M), ← _root_.zpow_add₀ (xi_ne_zero M)]
    refine xi_zpow_eq_of_dvd ⟨-(i * t), ?_⟩
    push_cast
    linear_combination -(2 * i) * ht
  · have hR : ¬(((a : ℕ) : ZMod M) = ((b : ℕ) : ZMod M) + (-(j : ZMod M))) := by
      intro hc
      exact hL (by linear_combination -hc)
    rw [if_neg hR, mul_zero]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases hk : a = k
    · subst hk
      rw [if_pos rfl, if_neg hL, mul_zero]
    · rw [if_neg hk, zero_mul]

theorem heisenbergPhase_mul_xi (M : ℕ) (i j : ℤ) :
    heisenbergPhase M i j * xi M ^ (-(i * j)) = theta M i j := by
  rw [heisenbergPhase, theta, xi_zpow_exp]
  have hre : ((-1 : ℂ) ^ (i + j)
        * Complex.exp (Real.pi * Complex.I * ((i ^ 2 + j ^ 2 : ℤ) : ℂ) / (M : ℂ)))
      * ((-1 : ℂ) ^ (-(i * j))
        * Complex.exp (Real.pi * Complex.I * ((-(i * j) : ℤ) : ℂ) / (M : ℂ)))
      = ((-1 : ℂ) ^ (i + j)) * ((-1 : ℂ) ^ (-(i * j)))
        * (Complex.exp (Real.pi * Complex.I * ((i ^ 2 + j ^ 2 : ℤ) : ℂ) / (M : ℂ))
          * Complex.exp (Real.pi * Complex.I * ((-(i * j) : ℤ) : ℂ) / (M : ℂ))) := by
    ring
  have hd : (2 : ℤ) ∣ (i + j + -(i * j)) - (i + j + i * j) := ⟨-(i * j), by ring⟩
  rw [hre, ← Complex.exp_add, ← _root_.zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    negOne_zpow_eq_of_two_dvd hd]
  congr 1
  congr 1
  unfold quadraticForm
  push_cast
  ring

theorem P_eq_heisenberg {M : ℕ} (hM : 4 ≤ M) (F : Values M) :
    P M F = (M : ℂ)⁻¹ • ∑ i : Fin M, ∑ j : Fin M,
      (heisenbergPhase M i j * valueAt F i j) • (qPower M i * pPower M j) := by
  have key : ∀ i j : Fin M,
      (heisenbergPhase M (i : ℤ) (j : ℤ) * valueAt F i j)
        • (qPower M (i : ℤ) * pPower M (j : ℤ))
        = (theta M (i : ℤ) (j : ℤ) * valueAt F i j) • D M (toWH (i : ℤ) (j : ℤ)) := by
    intro i j
    have hrw : (heisenbergPhase M (i : ℤ) (j : ℤ) * valueAt F i j)
          * xi M ^ (-((i : ℤ) * (j : ℤ)))
        = theta M (i : ℤ) (j : ℤ) * valueAt F i j := by
      rw [← heisenbergPhase_mul_xi]
      ring
    rw [qPower_mul_pPower hM, smul_smul, hrw]
  rw [P]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  exact (key i j).symm

/-- Extend the M² input equations to integer lifts using periodicity. -/
theorem convolution_eq_of_input {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) (r s : ℤ) :
    convolution M F r s = convolutionScalar M * valueAt F r s +
      if IsZeroLabel M (r, s) then (M : ℂ) else 0 := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨t₁, ht₁⟩ : (M : ℤ) ∣ r - ((r : ZMod M).val : ℤ) := by
    refine ⟨r / (M : ℤ), ?_⟩
    rw [ZMod.val_intCast]
    linear_combination -(Int.emod_add_mul_ediv r (M : ℤ))
  obtain ⟨t₂, ht₂⟩ : (M : ℤ) ∣ s - ((s : ZMod M).val : ℤ) := by
    refine ⟨s / (M : ℤ), ?_⟩
    rw [ZMod.val_intCast]
    linear_combination -(Int.emod_add_mul_ediv s (M : ℤ))
  have key : ∀ i j : Fin M,
      valueAt F (i : ℤ) (j : ℤ) * valueAt F (r - (i : ℤ)) (s - (j : ℤ))
          * gaussianLift M (i : ℤ) (j : ℤ)
          * e M (-(i : ℤ) * r + (j : ℤ) * (r - s))
        = valueAt F (i : ℤ) (j : ℤ)
            * valueAt F (((r : ZMod M).val : ℤ) - (i : ℤ))
              (((s : ZMod M).val : ℤ) - (j : ℤ))
            * gaussianLift M (i : ℤ) (j : ℤ)
            * e M (-(i : ℤ) * ((r : ZMod M).val : ℤ)
              + (j : ℤ) * (((r : ZMod M).val : ℤ) - ((s : ZMod M).val : ℤ))) := by
    intro i j
    have h1 : ((r - (i : ℤ) : ℤ) : ZMod M)
        = ((((r : ZMod M).val : ℤ) - (i : ℤ) : ℤ) : ZMod M) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-t₁, by linear_combination -ht₁⟩
    have h2 : ((s - (j : ℤ) : ℤ) : ZMod M)
        = ((((s : ZMod M).val : ℤ) - (j : ℤ) : ℤ) : ZMod M) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-t₂, by linear_combination -ht₂⟩
    have hv : valueAt F (r - (i : ℤ)) (s - (j : ℤ))
        = valueAt F (((r : ZMod M).val : ℤ) - (i : ℤ))
            (((s : ZMod M).val : ℤ) - (j : ℤ)) := by
      unfold valueAt
      rw [h1, h2]
    have he : e M (-(i : ℤ) * r + (j : ℤ) * (r - s))
        = e M (-(i : ℤ) * ((r : ZMod M).val : ℤ)
          + (j : ℤ) * (((r : ZMod M).val : ℤ) - ((s : ZMod M).val : ℤ))) := by
      refine e_eq_of_dvd ⟨-(i : ℤ) * t₁ + (j : ℤ) * (t₁ - t₂), ?_⟩
      linear_combination ((j : ℤ) - (i : ℤ)) * ht₁ - (j : ℤ) * ht₂
    rw [hv, he]
  have hconv : convolution M F r s
      = convolution M F ((r : ZMod M).val) ((s : ZMod M).val) := by
    unfold convolution
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    exact key i j
  have h0 : convolution M F ((r : ZMod M).val) ((s : ZMod M).val)
      = convolutionScalar M * F ((r : ZMod M), (s : ZMod M))
        + if ((r : ZMod M), (s : ZMod M)) = 0 then (M : ℂ) else 0 :=
    hA.convolution_eq ((r : ZMod M), (s : ZMod M))
  have hzero : ((r : ZMod M), (s : ZMod M)) = (0 : Index M) ↔ IsZeroLabel M (r, s) := by
    constructor
    · intro h
      have hp := Prod.ext_iff.mp h
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r M).mp hp.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd s M).mp hp.2⟩
    · intro h
      rw [Prod.ext_iff]
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r M).mpr h.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd s M).mpr h.2⟩
  have hite : (if ((r : ZMod M), (s : ZMod M)) = 0 then (M : ℂ) else 0)
      = if IsZeroLabel M (r, s) then (M : ℂ) else 0 := by
    by_cases h : ((r : ZMod M), (s : ZMod M)) = (0 : Index M)
    · rw [if_pos h, if_pos (hzero.mp h)]
    · rw [if_neg h, if_neg (mt hzero.mpr h)]
  rw [hconv, h0, hite]
  rfl

end SICLean.L2a
