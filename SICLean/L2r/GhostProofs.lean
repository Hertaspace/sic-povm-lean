import SICLean.L2r.GhostDefs
import SICLean.L2r.PhaseAux

/-! # Auxiliary proofs for the rank-r ghost interface

Helper lemmas live here so the interface file does not import them in a cycle.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SICLean.L2r

@[simp] theorem label_lift {d : ℕ} [NeZero d] (p : Index d) : label d (lift p) = p := by
  ext <;> simp [label, lift]

@[simp] theorem label_neg (d : ℕ) (p : ℤ × ℤ) : label d (-p) = -label d p := by
  ext <;> simp [label]

@[simp] theorem label_sub (d : ℕ) (p q : ℤ × ℤ) :
    label d (p - q) = label d p - label d q := by
  ext <;> simp [label]

theorem label_eq_zero_iff (d : ℕ) (p : ℤ × ℤ) :
    label d p = 0 ↔ IsZeroLabel d p := by
  exact (L2a.isZeroLabel_iff_cast (M := d) p.1 p.2).symm

theorem phase_ne_zero (d r : ℕ) (p : ℤ × ℤ) : phase d r p ≠ 0 := by
  exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (xi_ne_zero d))

theorem rw_values_ne_zero (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : Index d) : F p ≠ 0 := by
  by_cases hp : p = 0
  · subst p
    rw [hA.origin, originValue]
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (lt_trans (by norm_num) (unit_properties (Fact.out : Admissible d r)).2.2)).ne'
  · have hr := hA.reflection p hp
    have hg : torsionGaussian d r p ≠ 0 := Complex.exp_ne_zero _
    intro h
    rw [h, zero_mul] at hr
    exact inv_ne_zero hg hr.symm

theorem nu_ne_zero (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : ℤ × ℤ) : nu d r F p ≠ 0 := by
  exact div_ne_zero (phase_ne_zero d r p) (rw_values_ne_zero d r hA _)

theorem twistLift_not_zero (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ)
    (hp : ¬ IsZeroLabel d p) : ¬ IsZeroLabel d (twistLift d r p) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  have hmap : label d (twistLift d r p) = twistEquiv d r (label d p) := by
    change label d (twistLift d r p) = label d (twistLift d r (lift (label d p)))
    ext <;> simp [twistLift, label, lift]
  intro h
  apply hp
  apply (label_eq_zero_iff d p).mp
  apply (twistEquiv d r).injective
  rw [map_zero, ← hmap]
  exact (label_eq_zero_iff d _).mpr h

private theorem phase_sign_sq (z : ℤ) : ((-1 : ℂ) ^ z) ^ 2 = 1 := by
  rw [← zpow_natCast _ 2, ← _root_.zpow_mul]
  change (-1 : ℂ) ^ (z * 2 : ℤ) = 1
  rw [mul_comm z (2 : ℤ), _root_.zpow_mul]
  norm_num

private theorem phase_sign_xi (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ) :
    (-1 : ℂ) ^ (1 + phaseSignExponent d p) =
      xi d ^ ((d : ℤ) * (p.1 + p.2 + p.1 * p.2)) := by
  rw [L2a.xi_zpow_mul_M (phaseAux_dimension_ge_four (Fact.out : Admissible d r))]
  apply L2a.negOne_zpow_eq_of_two_dvd
  refine ⟨(d : ℤ) + 1, ?_⟩
  unfold phaseSignExponent
  ring

private theorem phase_eq_xi_zpow (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ) :
    phase d r p =
      -xi d ^ ((d : ℤ) * (p.1 + p.2 + p.1 * p.2) -
        (r : ℤ) * quadraticForm d r p) := by
  have hs : (-1 : ℂ) ^ phaseSignExponent d p =
      -xi d ^ ((d : ℤ) * (p.1 + p.2 + p.1 * p.2)) := by
    have hh := phase_sign_xi d r p
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one, neg_one_mul] at hh
    exact neg_eq_iff_eq_neg.mp hh
  rw [phase, hs, neg_mul, ← zpow_add₀ (xi_ne_zero d)]
  congr 2
  ring

theorem ghostProof_phase_neg (d r : ℕ) (p : ℤ × ℤ) : phase d r (-p) = phase d r p := by
  rcases p with ⟨x, y⟩
  unfold phase
  congr 1
  · apply L2a.negOne_zpow_eq_of_two_dvd
    refine ⟨-((d : ℤ) + 1) * (x + y), ?_⟩
    simp only [phaseSignExponent, Prod.neg_mk]
    ring
  · congr 1
    simp only [quadraticForm, Prod.neg_mk]
    ring

theorem ghostProof_phase_pow (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ) :
    phase d r p ^ (2 * d) = 1 := by
  rw [phase, mul_pow]
  have hs : ((-1 : ℂ) ^ phaseSignExponent d p) ^ (2 * d) = 1 := by
    rw [pow_mul, phase_sign_sq, one_pow]
  have hx : (xi d ^ (-(r : ℤ) * quadraticForm d r p)) ^ (2 * d) = 1 := by
    rw [← zpow_natCast _ (2 * d), ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, xi_zpow_two_mul_d, _root_.one_zpow]
  rw [hs, hx, mul_one]

theorem ghostProof_phase_sq (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ) :
    phase d r p ^ 2 = (torsionGaussian d r (label d p))⁻¹ := by
  rw [phase, mul_pow, phase_sign_sq, one_mul,
    ← zpow_natCast _ 2, ← _root_.zpow_mul,
    phaseAux_torsionGaussian_lift, L2a.e_inv, L2a.e_eq_omega_zpow, omega_zpow]
  congr 1
  ring

theorem ghostProof_nu_zero (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) :
    nu d r F 0 = -(originValue d r)⁻¹ ∧
      nu d r F 0 + (nu d r F 0)⁻¹ = -(gap d r : ℂ) * rootLevel d r := by
  have hz : phase d r 0 = -1 := by
    simp only [phase, phaseSignExponent, quadraticForm, Prod.fst_zero, Prod.snd_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero, mul_one, zpow_zero]
    convert L2a.negOne_zpow_eq_of_two_dvd
      (show (2 : ℤ) ∣ ((d : ℤ) + ((d : ℤ) + 1)) - 1 from ⟨d, by ring⟩) using 1
    norm_num
  have hn : nu d r F 0 = -(originValue d r)⁻¹ := by
    have hl : label d (0 : ℤ × ℤ) = 0 := by ext <;> simp [label]
    rw [nu, valueAt, hl, hz, hA.origin]
    rw [neg_div, one_div]
  refine ⟨hn, ?_⟩
  rw [hn, inv_neg, inv_inv]
  linear_combination -(normalizer_identities (Fact.out : Admissible d r)).2

theorem ghostProof_nu_mul_neg (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : ℤ × ℤ)
    (hp : ¬ IsZeroLabel d p) : nu d r F p * nu d r F (-p) = 1 := by
  have hl : label d p ≠ 0 := mt (label_eq_zero_iff d p).mp hp
  have hr := hA.reflection (label d p) hl
  have hg : torsionGaussian d r (label d p) ≠ 0 := Complex.exp_ne_zero _
  simp only [nu, valueAt, label_neg, ghostProof_phase_neg]
  calc
    _ = phase d r p ^ 2 / (F (label d p) * F (-label d p)) := by ring
    _ = 1 := by rw [hr, ghostProof_phase_sq, div_self (inv_ne_zero hg)]

private theorem phase_add_period (d r : ℕ) [Fact (Admissible d r)]
    (p k : ℤ × ℤ) :
    phase d r (p + (d : ℤ) • k) =
      xi d ^ symplectic (p + (d : ℤ) • k) p * phase d r p := by
  have hA : Admissible d r := Fact.out
  let K : ℤ := ((d : ℤ) + (r : ℤ) * ell d r - 1) * (p.1 * k.2 + p.2 * k.1) +
    (d : ℤ) * (k.1 + k.2 + (d : ℤ) * k.1 * k.2 - (r : ℤ) * quadraticForm d r k) +
    2 * (p.2 * k.1 - (r : ℤ) * p.1 * k.1 - (r : ℤ) * p.2 * k.2)
  rw [phase_eq_xi_zpow, phase_eq_xi_zpow, mul_neg]
  congr 1
  rw [← zpow_add₀ (xi_ne_zero d)]
  have he : (d : ℤ) * ((p + (d : ℤ) • k).1 + (p + (d : ℤ) • k).2 +
        (p + (d : ℤ) • k).1 * (p + (d : ℤ) • k).2) -
        (r : ℤ) * quadraticForm d r (p + (d : ℤ) • k) =
      (symplectic (p + (d : ℤ) • k) p +
        ((d : ℤ) * (p.1 + p.2 + p.1 * p.2) - (r : ℤ) * quadraticForm d r p)) +
        (d : ℤ) * K := by
    change (d : ℤ) * ((p.1 + (d : ℤ) * k.1) + (p.2 + (d : ℤ) * k.2) +
        (p.1 + (d : ℤ) * k.1) * (p.2 + (d : ℤ) * k.2)) -
      (r : ℤ) * quadraticForm d r (p + (d : ℤ) • k) = _
    dsimp [K, symplectic, quadraticForm]
    ring
  rw [he, zpow_add₀ (xi_ne_zero d), L2a.xi_zpow_mul_M (phaseAux_dimension_ge_four hA)]
  have hs : (-1 : ℂ) ^ (((d : ℤ) + 1) * K) = 1 := by
    apply (L2a.negOne_zpow_eq_of_two_dvd (e' := 0) ?_).trans (by norm_num)
    simp only [sub_zero]
    obtain ⟨t, ht⟩ := phaseAux_parity_ell hA
    obtain ⟨u, hu⟩ := Int.two_dvd_mul_add_one (d : ℤ)
    refine ⟨t * (p.1 * k.2 + p.2 * k.1) +
      u * (k.1 + k.2 + (d : ℤ) * k.1 * k.2 - (r : ℤ) * quadraticForm d r k) +
      ((d : ℤ) + 1) * (p.2 * k.1 - (r : ℤ) * p.1 * k.1 - (r : ℤ) * p.2 * k.2), ?_⟩
    dsimp [K]
    linear_combination (p.1 * k.2 + p.2 * k.1) * ht +
      (k.1 + k.2 + (d : ℤ) * k.1 * k.2 - (r : ℤ) * quadraticForm d r k) * hu
  rw [hs, mul_one]

private theorem phase_period_factor_zero (d r : ℕ) [Fact (Admissible d r)]
    (p k : ℤ × ℤ) (hp : IsZeroLabel d p) :
    xi d ^ symplectic (p + (d : ℤ) • k) p = 1 := by
  rcases hp with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have he : symplectic (p + (d : ℤ) • k) p =
      (d : ℤ) * ((d : ℤ) * (-k.1 * b + k.2 * a)) := by
    change -(p.1 + (d : ℤ) * k.1) * p.2 + (p.2 + (d : ℤ) * k.2) * p.1 = _
    rw [ha, hb]
    ring
  rw [he, L2a.xi_zpow_mul_M (phaseAux_dimension_ge_four (Fact.out : Admissible d r))]
  apply (L2a.negOne_zpow_eq_of_two_dvd (e' := 0) ?_).trans (by norm_num)
  simp only [sub_zero]
  obtain ⟨u, hu⟩ := Int.two_dvd_mul_add_one (d : ℤ)
  refine ⟨u * (-k.1 * b + k.2 * a), ?_⟩
  linear_combination (-k.1 * b + k.2 * a) * hu

theorem ghostProof_coefficient_add_period (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (p k : ℤ × ℤ) :
    coefficient d r F (p + (d : ℤ) • k) =
      xi d ^ symplectic (p + (d : ℤ) • k) p * coefficient d r F p := by
  have hl : label d (p + (d : ℤ) • k) = label d p := by
    change (((p.1 + (d : ℤ) * k.1 : ℤ) : ZMod d),
      ((p.2 + (d : ℤ) * k.2 : ℤ) : ZMod d)) = ((p.1 : ZMod d), (p.2 : ZMod d))
    simp
  have hz (z : ℤ × ℤ) : IsZeroLabel d z ↔ label d z = 0 := by
    simp [IsZeroLabel, label, Prod.ext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hp : IsZeroLabel d (p + (d : ℤ) • k) ↔ IsZeroLabel d p := by
    rw [hz, hl, hz]
  by_cases h : IsZeroLabel d p
  · rw [coefficient, if_pos (hp.mpr h), coefficient, if_pos h,
      phase_period_factor_zero d r p k h, one_mul]
  · rw [coefficient, if_neg (mt hp.mp h), coefficient, if_neg h, nu, nu,
      phase_add_period]
    have hv : valueAt F (p + (d : ℤ) • k) = valueAt F p := by
      unfold valueAt
      rw [hl]
    rw [hv]
    ring

theorem ghostProof_summand_add_period (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (p k : ℤ × ℤ) :
    coefficient d r F (p + (d : ℤ) • k) •
        D d (twistInverseLift d r (p + (d : ℤ) • k)) =
      coefficient d r F p • D d (twistInverseLift d r p) := by
  have hA : Admissible d r := Fact.out
  have ht : twistInverseLift d r (p + (d : ℤ) • k) =
      twistInverseLift d r p + (d : ℤ) • twistInverseLift d r k := by
    apply Prod.ext
    · rfl
    · change twistScalar d r * (p.2 + (d : ℤ) * k.2) =
        twistScalar d r * p.2 + (d : ℤ) * (twistScalar d r * k.2)
      ring
  have hs : xi d ^ symplectic (p + (d : ℤ) • k) p *
      xi d ^ ((d : ℤ) *
        ((twistInverseLift d r p).1 * (twistInverseLift d r k).2 +
          (twistInverseLift d r k).1 * (twistInverseLift d r p).2) +
        (d : ℤ) ^ 2 * ((twistInverseLift d r k).1 * (twistInverseLift d r k).2)) = 1 := by
    rw [← zpow_add₀ (xi_ne_zero d)]
    have he : symplectic (p + (d : ℤ) • k) p +
        ((d : ℤ) *
          ((twistInverseLift d r p).1 * (twistInverseLift d r k).2 +
            (twistInverseLift d r k).1 * (twistInverseLift d r p).2) +
          (d : ℤ) ^ 2 * ((twistInverseLift d r k).1 * (twistInverseLift d r k).2)) =
        (d : ℤ) * ((twistScalar d r + 1) * p.1 * k.2 +
          (twistScalar d r - 1) * k.1 * p.2 + (d : ℤ) * twistScalar d r * k.1 * k.2) := by
      dsimp [symplectic, twistInverseLift]
      ring
    rw [he, L2a.xi_zpow_mul_M (phaseAux_dimension_ge_four hA)]
    apply (L2a.negOne_zpow_eq_of_two_dvd (e' := 0) ?_).trans (by norm_num)
    simp only [sub_zero]
    obtain ⟨t, ht⟩ := phaseAux_parity_twist hA
    obtain ⟨v, hv⟩ := Int.two_dvd_mul_add_one (d : ℤ)
    refine ⟨t * (p.1 * k.2 + k.1 * p.2) - ((d : ℤ) + 1) * k.1 * p.2 +
      v * twistScalar d r * k.1 * k.2, ?_⟩
    linear_combination (p.1 * k.2 + k.1 * p.2) * ht +
      (twistScalar d r * k.1 * k.2) * hv
  rw [ghostProof_coefficient_add_period, ht, D_add_smul, smul_smul]
  have he : (xi d ^ symplectic (p + (d : ℤ) • k) p * coefficient d r F p) *
      xi d ^ ((d : ℤ) *
        ((twistInverseLift d r p).1 * (twistInverseLift d r k).2 +
          (twistInverseLift d r k).1 * (twistInverseLift d r p).2) +
        (d : ℤ) ^ 2 * ((twistInverseLift d r k).1 * (twistInverseLift d r k).2)) =
      coefficient d r F p := by
    rw [mul_right_comm, hs, one_mul]
  rw [he]

/-- The combined phase identity, valid also at the actual vectors q=0,p. -/
theorem ghostProof_phase_ratio (d r : ℕ) [Fact (Admissible d r)] (p q : ℤ × ℤ) :
    xi d ^ (twistScalar d r * symplectic p q) * phase d r q / phase d r (q - p) =
      (-1 : ℂ) ^ (1 + phaseSignExponent d p) *
        xi d ^ ((r : ℤ) * quadraticForm d r p) *
        L2a.e d ((r : ℤ) * symplectic p (shiftedAlpha d r q)) := by
  have hA : Admissible d r := Fact.out
  have hn : (level d r : ℤ) = (ell d r : ℤ) + 2 := by
    have := level_ge_five hA
    simp only [ell]
    omega
  rw [phase_eq_xi_zpow, phase_eq_xi_zpow, phase_sign_xi d r p,
    L2a.e_eq_omega_zpow, omega_zpow]
  simp only [mul_neg, neg_div_neg_eq]
  simp only [← zpow_add₀ (xi_ne_zero d), ← zpow_sub₀ (xi_ne_zero d)]
  have hexp : twistScalar d r * symplectic p q +
        ((d : ℤ) * (q.1 + q.2 + q.1 * q.2) - (r : ℤ) * quadraticForm d r q) -
        ((d : ℤ) * ((q - p).1 + (q - p).2 + (q - p).1 * (q - p).2) -
          (r : ℤ) * quadraticForm d r (q - p)) =
      ((d : ℤ) * (p.1 + p.2 + p.1 * p.2) + (r : ℤ) * quadraticForm d r p +
        2 * ((r : ℤ) * symplectic p (shiftedAlpha d r q))) +
      (d : ℤ) * (((r : ℤ) + 1) * p.2 * q.1 +
        (1 - (r : ℤ)) * p.1 * q.2 - 2 * p.1 * p.2) := by
    simp only [twistScalar, symplectic, quadraticForm, shiftedAlpha, shift,
      Prod.fst_sub, Prod.snd_sub]
    rw [hn]
    ring
  rw [hexp, zpow_add₀ (xi_ne_zero d),
    L2a.xi_zpow_mul_M (phaseAux_dimension_ge_four hA)]
  have hs : (-1 : ℂ) ^ (((d : ℤ) + 1) *
      (((r : ℤ) + 1) * p.2 * q.1 + (1 - (r : ℤ)) * p.1 * q.2 - 2 * p.1 * p.2)) = 1 := by
    suffices hh : (2 : ℤ) ∣ (((d : ℤ) + 1) *
        (((r : ℤ) + 1) * p.2 * q.1 + (1 - (r : ℤ)) * p.1 * q.2 - 2 * p.1 * p.2)) by
      simpa using L2a.negOne_zpow_eq_of_two_dvd (e' := 0) (by simpa using hh)
    have hr := phaseAux_parity_rank hA
    have hr' : (2 : ℤ) ∣ ((d : ℤ) + 1) * (1 - (r : ℤ)) := by
      have he : ((d : ℤ) + 1) * (1 - (r : ℤ)) =
          2 * ((d : ℤ) + 1) - ((d : ℤ) + 1) * ((r : ℤ) + 1) := by ring
      rw [he]
      exact dvd_sub (dvd_mul_right _ _) hr
    have he : ((d : ℤ) + 1) *
        (((r : ℤ) + 1) * p.2 * q.1 + (1 - (r : ℤ)) * p.1 * q.2 - 2 * p.1 * p.2) =
        ((d : ℤ) + 1) * ((r : ℤ) + 1) * (p.2 * q.1) +
          ((d : ℤ) + 1) * (1 - (r : ℤ)) * (p.1 * q.2) -
          2 * (((d : ℤ) + 1) * p.1 * p.2) := by ring
    rw [he]
    exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hr _) (dvd_mul_of_dvd_left hr' _))
      (dvd_mul_right _ _)
  rw [hs, mul_one]

theorem ghostProof_normalized_convolution (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : Index d) (hp : p ≠ 0) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ q : Index d,
      xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
        nu d r F (lift q) / nu d r F (lift q - lift p)) = 0 := by
  letI : NeZero d := admissibleDimensionNeZero d r
  let c : ℂ := (-1 : ℂ) ^ (1 + phaseSignExponent d (lift p)) *
    xi d ^ ((r : ℤ) * quadraticForm d r (lift p))
  have ht (q : Index d) :
      xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
        nu d r F (lift q) / nu d r F (lift q - lift p) =
      c * (L2a.e d ((r : ℤ) * symplectic (lift p) (shiftedAlpha d r (lift q))) *
        valueAt F (lift q - lift p) / F q) := by
    calc
      _ = (xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
          phase d r (lift q) / phase d r (lift q - lift p)) *
            (valueAt F (lift q - lift p) / F q) := by
        simp only [nu, valueAt, label_lift]
        field_simp [phase_ne_zero, rw_values_ne_zero d r hA]
      _ = _ := by rw [ghostProof_phase_ratio]; dsimp [c]; ring
  simp_rw [ht]
  rw [← Finset.mul_sum]
  change c * twistedRatio d r F p = 0
  rw [hA.twisted_ratio p, if_neg hp, mul_zero]

theorem ghostProof_coefficient_convolution (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : Index d) (hp : p ≠ 0) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ q : Index d, if q = 0 ∨ q = p then 0 else
      xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
        nu d r F (lift p - lift q) * nu d r F (lift q)) =
      (gap d r : ℂ) * rootLevel d r * nu d r F (lift p) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  let f : Index d → ℂ := fun q =>
    xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
      nu d r F (lift q) / nu d r F (lift q - lift p)
  let g : Index d → ℂ := fun q => if q = 0 ∨ q = p then 0 else
    xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
      nu d r F (lift p - lift q) * nu d r F (lift q)
  have hrec (q : Index d) (hq : q ≠ p) :
      (nu d r F (lift q - lift p))⁻¹ = nu d r F (lift p - lift q) := by
    have hn : ¬ IsZeroLabel d (lift p - lift q) := by
      intro h
      have he : p - q = 0 := by
        simpa only [label_sub, label_lift] using (label_eq_zero_iff d _).mpr h
      exact hq (sub_eq_zero.mp he).symm
    have hr := ghostProof_nu_mul_neg d r hA (lift p - lift q) hn
    rw [show -(lift p - lift q) = lift q - lift p by abel] at hr
    exact inv_eq_of_mul_eq_one_left hr
  have h0 : f 0 = nu d r F 0 * nu d r F (lift p) := by
    dsimp [f]
    have hl : lift (0 : Index d) = 0 := by ext <;> simp [lift]
    rw [hl]
    simp only [symplectic, Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul,
      neg_zero, add_zero, zpow_zero, one_mul, zero_sub, div_eq_mul_inv]
    have hr := ghostProof_nu_mul_neg d r hA (lift p) (by
      intro hc
      exact hp (by simpa using (label_eq_zero_iff d _).mpr hc))
    rw [inv_eq_of_mul_eq_one_left hr]
  have hself : f p = nu d r F (lift p) / nu d r F 0 := by
    dsimp [f]
    have hs : symplectic (lift p) (lift p) = 0 := by unfold symplectic; ring
    rw [hs, mul_zero, zpow_zero, one_mul, sub_self]
  have hterm (q : Index d) : f q = g q +
      (if q = 0 then f 0 else 0) + (if q = p then f p else 0) := by
    by_cases hq0 : q = 0
    · subst q
      simp [g, hp, Ne.symm hp]
    · by_cases hqp : q = p
      · subst q
        simp [g, hp]
      · simp only [g, if_neg hq0, if_neg hqp, if_neg (not_or.mpr ⟨hq0, hqp⟩), add_zero,
          f, div_eq_mul_inv, hrec q hqp]
        ring
  have hs := ghostProof_normalized_convolution d r hA p hp
  change (∑ q : Index d, f q) = 0 at hs
  have hs' := congrArg (fun h : Index d → ℂ => ∑ q : Index d, h q) (funext hterm)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs'
  rw [hs, h0, hself] at hs'
  change (∑ q : Index d, g q) = _
  have hn := (ghostProof_nu_zero d r hA).2
  rw [div_eq_mul_inv] at hs'
  linear_combination -hs' - nu d r F (lift p) * hn

/-! The coefficient and displacement always descend together. -/

private theorem ghost_label_lift {d : ℕ} [NeZero d] (p : Index d) : label d (lift p) = p := by
  ext <;> simp [label, lift]

private theorem ghost_label_zero_iff {d : ℕ} (p : ℤ × ℤ) :
    label d p = 0 ↔ IsZeroLabel d p := by
  simp [label, IsZeroLabel, Prod.ext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

private theorem ghost_label_twistInverse (d r : ℕ) [Fact (Admissible d r)]
    (p : ℤ × ℤ) :
    label d (twistInverseLift d r p) = (twistEquiv d r).symm (label d p) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  change label d (twistInverseLift d r p) =
    label d (twistInverseLift d r (lift (label d p)))
  ext <;> simp [label, twistInverseLift, lift]

private theorem ghost_label_twist (d r : ℕ) [Fact (Admissible d r)]
    (p : ℤ × ℤ) :
    label d (twistLift d r p) = twistEquiv d r (label d p) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  change label d (twistLift d r p) = label d (twistLift d r (lift (label d p)))
  ext <;> simp [label, twistLift, lift]

private theorem ghost_twist_zero_iff (d r : ℕ) [Fact (Admissible d r)]
    (p : ℤ × ℤ) :
    IsZeroLabel d (twistInverseLift d r p) ↔ IsZeroLabel d p := by
  rw [← ghost_label_zero_iff, ghost_label_twistInverse, ← ghost_label_zero_iff]
  exact (twistEquiv d r).symm.map_eq_zero_iff

private theorem ghost_summand_eq (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (p q : ℤ × ℤ) (h : label d p = label d q) :
    coefficient d r F p • D d (twistInverseLift d r p) =
      coefficient d r F q • D d (twistInverseLift d r q) := by
  obtain ⟨a, ha⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub q.1 p.1 d).mp (congrArg Prod.fst h).symm
  obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub q.2 p.2 d).mp (congrArg Prod.snd h).symm
  have he : p = q + (d : ℤ) • (a, b) := by
    apply Prod.ext
    · dsimp; linear_combination ha
    · dsimp; linear_combination hb
  rw [he, ghostProof_summand_add_period]

private theorem ghost_xi_phaseModulus (d r : ℕ) [Fact (Admissible d r)] :
    xi d ^ (phaseModulus d : ℤ) = 1 := by
  haveI : NeZero d := admissibleDimensionNeZero d r
  by_cases he : Even d
  · simpa [phaseModulus, he] using xi_zpow_two_mul_d d
  · have ho : Odd d := Nat.not_even_iff_odd.mp he
    have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    rw [phaseModulus, if_neg he, zpow_natCast, xi, ho.neg_pow,
      ← Complex.exp_nat_mul]
    rw [show (d : ℂ) * (Real.pi * Complex.I / d) = Real.pi * Complex.I by field_simp,
      Complex.exp_pi_mul_I]
    ring

private theorem ghost_D_twist_inverse (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ) :
    D d (twistInverseLift d r (twistLift d r p)) = D d p := by
  obtain ⟨k, hk⟩ := twist_inverse_mod_phase (Fact.out : Admissible d r)
  have hm : (d : ℤ) ∣ (phaseModulus d : ℤ) := by
    by_cases he : Even d <;> simp [phaseModulus, he]
  obtain ⟨m, hm⟩ := hm
  have harg : twistInverseLift d r (twistLift d r p) =
      p + (d : ℤ) • (0, m * k * p.2) := by
    ext <;> simp only [twistInverseLift, twistLift, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero]
    linear_combination p.2 * hk + k * p.2 * hm
  rw [harg, D_add_smul]
  have hexp : (d : ℤ) * (p.1 * (m * k * p.2) + (0 : ℤ) * p.2) +
      (d : ℤ) ^ 2 * ((0 : ℤ) * (m * k * p.2)) =
      (phaseModulus d : ℤ) * (p.1 * k * p.2) := by
    linear_combination -p.1 * k * p.2 * hm
  rw [hexp, zpow_mul, ghost_xi_phaseModulus d r, one_zpow, one_smul]

private theorem ghost_expansion (d r : ℕ) [Fact (Admissible d r)] (F : Values d) :
    letI : NeZero d := admissibleDimensionNeZero d r
    ghostProjector d r F = (d : ℂ)⁻¹ •
      ∑ p : Index d, coefficient d r F (lift p) • D d (twistInverseLift d r (lift p)) := by
  classical
  letI : NeZero d := admissibleDimensionNeZero d r
  have hterm (p : Index d) :
      coefficient d r F (lift p) • D d (twistInverseLift d r (lift p)) =
        (if p = 0 then (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) else 0) +
          (rootLevel d r)⁻¹ •
            (if p = 0 then 0 else nu d r F (lift p) • D d (twistInverseLift d r (lift p))) := by
    have hz : IsZeroLabel d (lift p) ↔ p = 0 := by
      rw [← ghost_label_zero_iff, ghost_label_lift]
    by_cases hp : p = 0
    · subst hp
      simp [coefficient, lift, twistInverseLift, D_zero, IsZeroLabel]
    · simp [coefficient, hz, hp, div_eq_mul_inv, smul_smul, mul_comm]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ← Finset.smul_sum, smul_add, smul_smul]
  simp [ghostProjector, div_eq_mul_inv, mul_comm]

private theorem ghost_trace_D (d r : ℕ) [Fact (Admissible d r)] (p : Index d) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (D d (twistInverseLift d r (lift p))).trace = if p = 0 then (d : ℂ) else 0 := by
  classical
  letI : NeZero d := admissibleDimensionNeZero d r
  by_cases hp : p = 0
  · subst hp
    simp [lift, twistInverseLift, D_zero, Matrix.trace_one]
  · have hz : ¬ IsZeroLabel d (twistInverseLift d r (lift p)) := by
      rw [ghost_twist_zero_iff, ← ghost_label_zero_iff, ghost_label_lift]
      exact hp
    rw [trace_D, if_neg hz, if_neg hp]

private theorem ghost_ov_term (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (q : Index d) (p : ℤ × ℤ) :
    letI : NeZero d := admissibleDimensionNeZero d r
    ov d (coefficient d r F (lift q) • D d (twistInverseLift d r (lift q))) p =
      if q = label d (twistLift d r p) then coefficient d r F (twistLift d r p) * d else 0 := by
  classical
  letI : NeZero d := admissibleDimensionNeZero d r
  have heq : label d (twistInverseLift d r (lift q)) = label d p ↔
      q = label d (twistLift d r p) := by
    rw [ghost_label_twistInverse, ghost_label_lift, ghost_label_twist]
    constructor
    · intro h
      have he := congrArg (twistEquiv d r) h
      simpa using he
    · intro h
      rw [h]
      simp
  by_cases hq : q = label d (twistLift d r p)
  · rw [if_pos hq, ghost_summand_eq d r F (lift q) (twistLift d r p)
      ((ghost_label_lift q).trans hq), ghost_D_twist_inverse]
    simp [ov, D_mul_conjTranspose_D, Matrix.trace_smul,
      Matrix.trace_one]
  · have hz : ¬ IsZeroLabel d (twistInverseLift d r (lift q) + -p) := by
      intro hz
      apply hq
      apply heq.mp
      have hl := (ghost_label_zero_iff _).mpr hz
      have ha : label d (twistInverseLift d r (lift q) + -p) =
          label d (twistInverseLift d r (lift q)) - label d p := by
        ext <;> simp [label, sub_eq_add_neg]
      rwa [ha, sub_eq_zero] at hl
    rw [if_neg hq, ov, Matrix.smul_mul, conjTranspose_D, D_mul_D,
      Matrix.trace_smul, Matrix.trace_smul, trace_D, if_neg hz]
    simp

private theorem ghost_coefficient_mul_neg (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : ℤ × ℤ)
    (hp : ¬ IsZeroLabel d p) :
    coefficient d r F (-p) * coefficient d r F p = (level d r : ℂ)⁻¹ := by
  have hn : ¬ IsZeroLabel d (-p) := by simpa [IsZeroLabel] using hp
  have hr := rootLevel_sq (Fact.out : Admissible d r)
  rw [coefficient, coefficient, if_neg hn, if_neg hp]
  calc
    _ = (nu d r F p * nu d r F (-p)) / rootLevel d r ^ 2 := by ring
    _ = _ := by rw [ghostProof_nu_mul_neg d r hA p hp, hr.1, one_div]

private theorem ghost_level_relation (d r : ℕ) [Fact (Admissible d r)] :
    (level d r : ℂ) * (r : ℂ) * ((d : ℂ) - r) = (d : ℂ) ^ 2 - 1 := by
  have ha := (Fact.out : Admissible d r)
  have hdr : r ≤ d := by have := ha.main_range; omega
  have hsq : 1 ≤ d ^ 2 := by have := ha.main_range; have := ha.rank_pos; nlinarith
  have hh := congrArg (fun n : ℕ => (n : ℂ)) (level_identity ha)
  push_cast [Nat.cast_sub hdr, Nat.cast_sub hsq] at hh
  exact hh

private theorem ghost_full_convolution (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : Index d) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ q : Index d,
      xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
        coefficient d r F (lift p - lift q) * coefficient d r F (lift q)) =
      (d : ℂ) * coefficient d r F (lift p) := by
  classical
  letI : NeZero d := admissibleDimensionNeZero d r
  have hzero : lift (0 : Index d) = (0 : ℤ × ℤ) := by simp [lift]
  have hcoefzero : coefficient d r F (0 : ℤ × ℤ) = r := by
    simp [coefficient, IsZeroLabel]
  have hn := rootLevel_sq (Fact.out : Admissible d r)
  have hl : (level d r : ℂ) ≠ 0 := by
    rw [← hn.1]
    exact pow_ne_zero _ hn.2
  have hz (q : Index d) : IsZeroLabel d (lift q) ↔ q = 0 := by
    rw [← ghost_label_zero_iff, ghost_label_lift]
  have hdiff (q : Index d) : IsZeroLabel d (lift p - lift q) ↔ p = q := by
    rw [← ghost_label_zero_iff]
    have he : label d (lift p - lift q) = p - q := by
      ext <;> simp [label, lift]
    rw [he, sub_eq_zero]
  by_cases hp : p = 0
  · subst hp
    have hterm (q : Index d) :
        xi d ^ (twistScalar d r * symplectic (lift (0 : Index d)) (lift q)) *
            coefficient d r F (lift (0 : Index d) - lift q) * coefficient d r F (lift q) =
          (level d r : ℂ)⁻¹ + if q = 0 then (r : ℂ) ^ 2 - (level d r : ℂ)⁻¹ else 0 := by
      by_cases hq : q = 0
      · subst hq
        simp [lift, symplectic, coefficient, IsZeroLabel, pow_two]
      · have hqz : ¬ IsZeroLabel d (lift q) := (hz q).not.mpr hq
        simpa [lift, symplectic, hq] using ghost_coefficient_mul_neg d r hA (lift q) hqz
    rw [Finset.sum_congr rfl (fun q _ => hterm q)]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, ZMod.card, nsmul_eq_mul, Nat.cast_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hzero, hcoefzero]
    have hc := ghost_level_relation d r
    field_simp
    linear_combination -hc
  · have hpz : ¬ IsZeroLabel d (lift p) := (hz p).not.mpr hp
    have hterm (q : Index d) :
        xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
            coefficient d r F (lift p - lift q) * coefficient d r F (lift q) =
          (if q = 0 ∨ q = p then 0 else
            xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
              nu d r F (lift p - lift q) * nu d r F (lift q)) / rootLevel d r ^ 2 +
            (if q = 0 then (r : ℂ) * coefficient d r F (lift p) else 0) +
            (if q = p then (r : ℂ) * coefficient d r F (lift p) else 0) := by
      by_cases hq0 : q = 0
      · subst hq0
        rw [hzero, sub_zero, hcoefzero]
        simp [symplectic, Ne.symm hp, mul_comm]
      · by_cases hqp : q = p
        · subst hqp
          rw [sub_self, hcoefzero]
          have hsym : symplectic (lift q) (lift q) = 0 := by
            simp [symplectic, mul_comm]
          simp [hsym, hp, mul_comm]
        · have hqz : ¬ IsZeroLabel d (lift q) := (hz q).not.mpr hq0
          have hdz : ¬ IsZeroLabel d (lift p - lift q) := (hdiff q).not.mpr (Ne.symm hqp)
          simp only [hq0, hqp, or_self, if_false, add_zero,
            coefficient, if_neg hqz, if_neg hdz]
          ring
    rw [Finset.sum_congr rfl (fun q _ => hterm q)]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ghostProof_coefficient_convolution d r hA p hp, coefficient, if_neg hpz]
    have hg : (gap d r : ℂ) = (d : ℂ) - 2 * r := by simp [gap]
    rw [hg]
    field_simp
    <;> ring

private theorem ghost_product_term (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (p q : Index d) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (coefficient d r F (lift (p - q)) • D d (twistInverseLift d r (lift (p - q)))) *
        (coefficient d r F (lift q) • D d (twistInverseLift d r (lift q))) =
      (xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
        coefficient d r F (lift p - lift q) * coefficient d r F (lift q)) •
          D d (twistInverseLift d r (lift p)) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  have hl : label d (lift (p - q)) = label d (lift p - lift q) := by
    ext <;> simp [label, lift]
  rw [ghost_summand_eq d r F (lift (p - q)) (lift p - lift q) hl]
  simp only [Matrix.smul_mul, Matrix.mul_smul, D_mul_D, smul_smul]
  have ha : twistInverseLift d r (lift p - lift q) + twistInverseLift d r (lift q) =
      twistInverseLift d r (lift p) := by
    ext <;> simp [twistInverseLift] <;> ring
  have he : (twistInverseLift d r (lift p - lift q)).2 * (twistInverseLift d r (lift q)).1 -
        (twistInverseLift d r (lift p - lift q)).1 * (twistInverseLift d r (lift q)).2 =
      twistScalar d r * symplectic (lift p) (lift q) := by
    simp only [twistInverseLift, symplectic, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [ha, he]
  congr 1
  ring

theorem ghostProof_ghostProjector_idempotent (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) :
    ghostProjector d r F * ghostProjector d r F = ghostProjector d r F := by
  classical
  letI : NeZero d := admissibleDimensionNeZero d r
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  let term : Index d → Matrix (Fin d) (Fin d) ℂ := fun p =>
    coefficient d r F (lift p) • D d (twistInverseLift d r (lift p))
  have hprod : (∑ p : Index d, term p) * (∑ p : Index d, term p) =
      (d : ℂ) • ∑ p : Index d, term p := by
    calc
      _ = ∑ q : Index d, ∑ u : Index d, term u * term q := by
        simp only [Matrix.sum_mul, Matrix.mul_sum]
      _ = ∑ q : Index d, ∑ p : Index d, term (p - q) * term q := by
        apply Finset.sum_congr rfl
        intro q _
        apply Fintype.sum_equiv (Equiv.addRight q)
        intro u
        simp
      _ = ∑ p : Index d,
          (∑ q : Index d,
            xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
              coefficient d r F (lift p - lift q) * coefficient d r F (lift q)) •
                D d (twistInverseLift d r (lift p)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        simp only [term, ghost_product_term, Finset.sum_smul]
      _ = _ := by
        simp_rw [ghost_full_convolution d r hA]
        simp only [term, Finset.smul_sum, smul_smul]
  simp only [ghost_expansion]
  change ((d : ℂ)⁻¹ • ∑ p : Index d, term p) *
      ((d : ℂ)⁻¹ • ∑ p : Index d, term p) = (d : ℂ)⁻¹ • ∑ p : Index d, term p
  rw [Matrix.smul_mul, Matrix.mul_smul, hprod, smul_smul, smul_smul]
  congr 1
  field_simp

theorem ghostProof_trace_ghostProjector (d r : ℕ) [Fact (Admissible d r)] (F : Values d) :
    (ghostProjector d r F).trace = r := by
  classical
  letI : NeZero d := admissibleDimensionNeZero d r
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  rw [ghost_expansion]
  simp only [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  simp_rw [ghost_trace_D]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [coefficient, lift, IsZeroLabel, hd, mul_comm]

theorem ghostProof_ov_ghostProjector (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (p : ℤ × ℤ) (hp : ¬ IsZeroLabel d p) :
    ov d (ghostProjector d r F) p = coefficient d r F (twistLift d r p) := by
  classical
  letI : NeZero d := admissibleDimensionNeZero d r
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  rw [ghost_expansion]
  have he : ov d ((d : ℂ)⁻¹ • ∑ q : Index d,
      coefficient d r F (lift q) • D d (twistInverseLift d r (lift q))) p =
      (d : ℂ)⁻¹ * ∑ q : Index d,
        ov d (coefficient d r F (lift q) • D d (twistInverseLift d r (lift q))) p := by
    simp only [ov, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
      smul_eq_mul]
  rw [he]
  simp_rw [ghost_ov_term]
  simp [hd, mul_comm]

theorem ghostProof_coefficient_mul_neg (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : ℤ × ℤ)
    (hp : ¬ IsZeroLabel d p) :
    coefficient d r F p * coefficient d r F (-p) = (rsicConst d r : ℂ) := by
  have hneg : ¬ IsZeroLabel d (-p) := by simpa [IsZeroLabel] using hp
  simp only [coefficient, if_neg hp, if_neg hneg]
  calc
    _ = (nu d r F p * nu d r F (-p)) / rootLevel d r ^ 2 := by ring
    _ = (rsicConst d r : ℂ) := by
      rw [ghostProof_nu_mul_neg d r hA p hp, (rootLevel_sq (Fact.out : Admissible d r)).1,
        rsicConst_eq_inv_level (Fact.out : Admissible d r)]
      simp

theorem ghostProof_isGhost_of_RW_rank (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) :
    IsGhost d r (ghostProjector d r F) := by
  refine ⟨ghostProof_ghostProjector_idempotent d r hA, ghostProof_trace_ghostProjector d r F, ?_⟩
  intro p hp
  have hneg : ¬ IsZeroLabel d (-p) := by simpa [IsZeroLabel] using hp
  rw [ghostProof_ov_ghostProjector d r F p hp, ghostProof_ov_ghostProjector d r F (-p) hneg]
  have he : twistLift d r (-p) = -twistLift d r p := by
    ext <;> simp [twistLift]
  rw [he]
  exact ghostProof_coefficient_mul_neg d r hA _ (twistLift_not_zero d r p hp)

theorem ghostProof_map_phase_norm (d r : ℕ) [Fact (Admissible d r)]
    (τ : ℂ →+* ℂ) (p : ℤ × ℤ) : ‖τ (phase d r p)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 2 * d)
  · rw [← map_pow, ghostProof_phase_pow, map_one]
  · have hd := phaseAux_dimension_ge_four (Fact.out : Admissible d r)
    omega

theorem ghostProof_map_rootLevel_eq_or_neg (d r : ℕ) [Fact (Admissible d r)] (τ : ℂ →+* ℂ) :
    τ (rootLevel d r) = rootLevel d r ∨ τ (rootLevel d r) = -rootLevel d r := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, (rootLevel_sq (Fact.out : Admissible d r)).1, map_natCast]

theorem ghostProof_map_coefficient_normSq (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput d r F τ)
    (p : ℤ × ℤ) (hp : ¬ IsZeroLabel d p) :
    Complex.normSq (τ (coefficient d r F p)) = rsicConst d r := by
  have hl : label d p ≠ 0 := mt (label_eq_zero_iff d p).mp hp
  have hF : ‖τ (valueAt F p)‖ = 1 := hB.norm_F _ hl
  have hd : Complex.normSq (τ (rootLevel d r)) = level d r := by
    rcases ghostProof_map_rootLevel_eq_or_neg d r τ with h | h
    · rw [h, rootLevel, Complex.normSq_ofReal]
      exact Real.mul_self_sqrt (Nat.cast_nonneg _)
    · rw [h, Complex.normSq_neg, rootLevel, Complex.normSq_ofReal]
      exact Real.mul_self_sqrt (Nat.cast_nonneg _)
  simp only [coefficient, if_neg hp, nu, map_div₀, Complex.normSq_div,
    Complex.normSq_eq_norm_sq, ghostProof_map_phase_norm d r τ, hF, one_pow, one_div]
  rw [← Complex.normSq_eq_norm_sq, hd, rsicConst_eq_inv_level (Fact.out : Admissible d r)]
  simp

theorem ghostProof_unimodularFlip_of_RW_rank (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput d r F τ) :
    UnimodularFlip d r (ghostProjector d r F) τ := by
  intro p hp
  rw [ghostProof_ov_ghostProjector d r F p hp]
  exact ghostProof_map_coefficient_normSq d r hB _ (twistLift_not_zero d r p hp)

end SICLean.L2r
