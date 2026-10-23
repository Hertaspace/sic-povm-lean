import SICLean.Defs

/-!
# Basic Weyl–Heisenberg facts
-/

noncomputable section

open Matrix

namespace SICLean

variable {d : ℕ}

/-- `ω_d = ξ_d²`. -/
theorem omega_eq_xi_sq (d : ℕ) : omega d = xi d ^ 2 := by
  simp only [omega, xi, pow_two, neg_mul_neg]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- `ξ_d ≠ 0`, so integer powers of `ξ_d` behave. -/
theorem xi_ne_zero (d : ℕ) : xi d ≠ 0 :=
  neg_ne_zero.mpr (Complex.exp_ne_zero _)

/-! ## Helper lemmas

Entrywise identities for `D_p` reduce, via `omega d = xi d ^ 2`, to equalities of integer
powers of `xi d`; two exponents differing by a multiple of `2d` give equal powers because
`xi d ^ (2d) = 1`.  Integer labels are compared through `ZMod d`.
-/

/-- If two entries of `Fin d` have equal labels then they are equal. -/
theorem fin_ext_of_label [NeZero d] {i j : Fin d}
    (h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d)) : i = j := by
  have hv : (ZMod.val ((i : ℕ) : ZMod d)) = (ZMod.val ((j : ℕ) : ZMod d)) := by
    rw [h]
  rw [ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt] at hv
  exact Fin.val_injective hv

/-- A label equality `i ≡ j + a (mod d)` gives an integer witness. -/
theorem exists_sub_of_label {d : ℕ} {i j : ℕ} {a : ℤ}
    (h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (a : ZMod d)) :
    ∃ t : ℤ, (i : ℤ) = (j : ℤ) + a + (d : ℤ) * t := by
  have h' : (((i : ℤ) - (j : ℤ) - a : ℤ) : ZMod d) = 0 := by
    push_cast
    rw [h]
    ring
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
  exact ⟨t, by linear_combination ht⟩

/-- `omega d ^ d = 1` for `d ≠ 0`. -/
theorem omega_pow_d_of_ne_zero (d : ℕ) (hd : d ≠ 0) : omega d ^ (d : ℕ) = 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [omega]
  rw [← Complex.exp_nat_mul, mul_comm, div_mul_cancel₀ _ hd']
  exact Complex.exp_two_pi_mul_I

/-- `xi d ^ (2d) = 1`. -/
theorem xi_zpow_two_mul_d (d : ℕ) : xi d ^ ((2 * d : ℕ) : ℤ) = 1 := by
  by_cases hd : d = 0
  · simp [hd]
  · rw [zpow_natCast, pow_mul, ← omega_eq_xi_sq]
    exact omega_pow_d_of_ne_zero d hd

/-- Powers of `omega` are even powers of `xi`. -/
theorem omega_zpow (d : ℕ) (z : ℤ) : omega d ^ z = xi d ^ (2 * z) := by
  rw [omega_eq_xi_sq]
  exact (zpow_mul (xi d) 2 z).symm

/-- Powers of `xi` agree when the exponents differ by a multiple of `2d`. -/
theorem xi_zpow_eq_of_dvd {d : ℕ} {e e' : ℤ} (h : ((2 * d : ℕ) : ℤ) ∣ (e - e')) :
    xi d ^ e = xi d ^ e' := by
  obtain ⟨n, hn⟩ := h
  have he : e = e' + ((2 * d : ℕ) : ℤ) * n := by linear_combination hn
  rw [he, zpow_add₀ (xi_ne_zero d), _root_.zpow_mul, xi_zpow_two_mul_d, _root_.one_zpow,
    mul_one]

/-- `conj (xi d) = (xi d)⁻¹`. -/
theorem star_xi (d : ℕ) : star (xi d) = (xi d)⁻¹ := by
  have hc : (starRingEnd ℂ) (Real.pi * Complex.I / (d : ℂ)) =
      -(Real.pi * Complex.I / (d : ℂ)) := by
    have hd : (starRingEnd ℂ) ((d : ℕ) : ℂ) = ((d : ℕ) : ℂ) := by simp
    rw [div_eq_mul_inv, (starRingEnd ℂ).map_mul, Complex.conj_inv, hd,
      (starRingEnd ℂ).map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hL : star (xi d) = -Complex.exp (-(Real.pi * Complex.I / (d : ℂ))) := by
    simp only [Complex.star_def, xi, map_neg, ← Complex.exp_conj, hc]
  have hR : (xi d)⁻¹ = -Complex.exp (-(Real.pi * Complex.I / (d : ℂ))) := by
    simp only [xi, ← neg_inv, ← Complex.exp_neg]
  rw [hL, hR]

/-- `conj (omega d) = (omega d)⁻¹`. -/
theorem star_omega (d : ℕ) : star (omega d) = (omega d)⁻¹ := by
  rw [omega_eq_xi_sq, star_pow, star_xi, ← inv_pow]

/-- The unique index in `Fin d` with a given label. -/
def finIdx (d : ℕ) [NeZero d] (r : ZMod d) : Fin d :=
  ⟨ZMod.val r, ZMod.val_lt r⟩

theorem label_finIdx (d : ℕ) [NeZero d] (r : ZMod d) : ((finIdx d r : ℕ) : ZMod d) = r := by
  have h1 : (finIdx d r : ℕ) < d := ZMod.val_lt r
  refine ZMod.val_injective d ?_
  rw [ZMod.val_cast_of_lt h1]
  rfl

/-- A sum over `Fin d` of a function supported at a single label. -/
theorem sum_label_single (d : ℕ) [NeZero d] (F : Fin d → ℂ) (r : ZMod d) :
    ∑ k : Fin d, (if ((k : ℕ) : ZMod d) = r then F k else 0) = F (finIdx d r) := by
  have h : ∑ k : Fin d, (if ((k : ℕ) : ZMod d) = r then F k else 0)
      = (if ((finIdx d r : ℕ) : ZMod d) = r then F (finIdx d r) else 0) :=
    Fintype.sum_eq_single
      (f := fun k : Fin d => if ((k : ℕ) : ZMod d) = r then F k else 0)
      (finIdx d r) (by
        intro k hk
        rw [if_neg]
        intro hcon
        exact hk (fin_ext_of_label (hcon.trans (label_finIdx d r).symm)))
  rwa [if_pos (label_finIdx d r)] at h

/-- `D_0 = 1`. -/
theorem D_zero : D d (0, 0) = 1 := by
  ext i j
  by_cases hd : d = 0
  · exact absurd i.isLt (by omega)
  haveI : NeZero d := ⟨hd⟩
  have hD : (D d (0, 0)) i j = if ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) then 1 else 0 := by
    simp only [D]
    push_cast
    simp
  rw [hD, Matrix.one_apply]
  by_cases h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d)
  · simp [fin_ext_of_label h]
  · rw [if_neg h, if_neg]
    intro hij
    exact h (by rw [hij])

/-- `star` commutes with integer powers in `ℂ`. -/
theorem star_zpow (x : ℂ) (z : ℤ) : star (x ^ z) = (star x) ^ z := by
  cases z with
  | ofNat n =>
      show star (x ^ ((n : ℕ) : ℤ)) = (star x) ^ ((n : ℕ) : ℤ)
      rw [zpow_natCast, star_pow, zpow_natCast]
  | negSucc n =>
      rw [zpow_negSucc, Complex.star_def, Complex.conj_inv, ← Complex.star_def, star_pow,
        ← zpow_negSucc]

/-- `D_pᴴ = D_{-p}` for integer labels. -/
theorem conjTranspose_D (p : ℤ × ℤ) : (D d p)ᴴ = D d (-p) := by
  ext i j
  by_cases hd : d = 0
  · exact absurd i.isLt (by omega)
  haveI : NeZero d := ⟨hd⟩
  simp only [Matrix.conjTranspose_apply, D]
  push_cast
  rw [show (-p).1 = -(p.1) from rfl, show (-p).2 = -(p.2) from rfl]
  have hnc : ∀ a : ℤ, ((-a : ℤ) : ZMod d) = (-(a : ZMod d)) := fun a => by push_cast; rfl
  rw [hnc]
  by_cases h : ((j : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) + (p.1 : ZMod d)
  · rw [if_pos h, if_pos (show ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (-(p.1) : ZMod d) by
      linear_combination -h)]
    obtain ⟨t, ht⟩ := exists_sub_of_label h
    rw [star_mul, star_zpow, star_zpow, star_omega, star_xi, _root_.inv_zpow, _root_.inv_zpow,
      ← _root_.zpow_neg, ← _root_.zpow_neg, omega_zpow, omega_zpow,
      ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
    refine xi_zpow_eq_of_dvd ⟨p.2 * t, ?_⟩
    push_cast
    linear_combination 2 * p.2 * ht
  · rw [if_neg h, star_zero, if_neg]
    intro hcon
    exact h (by linear_combination -hcon)

/-- `D_p D_q = ξ_d^{p₂q₁ - p₁q₂} D_{p+q}`. -/
theorem D_mul_D (p q : ℤ × ℤ) :
    D d p * D d q = xi d ^ (p.2 * q.1 - p.1 * q.2) • D d (p + q) := by
  ext i j
  by_cases hd : d = 0
  · exact absurd i.isLt (by omega)
  haveI : NeZero d := ⟨hd⟩
  simp only [Matrix.mul_apply, D, Matrix.smul_apply, smul_eq_mul]
  push_cast
  rw [show (p + q).1 = p.1 + q.1 from rfl, show (p + q).2 = p.2 + q.2 from rfl]
  have h2 : ((p.1 + q.1 : ℤ) : ZMod d) = ((p.1 : ℤ) : ZMod d) + ((q.1 : ℤ) : ZMod d) := by
    rw [Int.cast_add]
  rw [h2]
  by_cases h : ((i : ℕ) : ZMod d) =
      ((j : ℕ) : ZMod d) + (((p.1 : ℤ) : ZMod d) + ((q.1 : ℤ) : ZMod d))
  · rw [if_pos h]
    have key : ∀ k : Fin d,
        (if ((i : ℕ) : ZMod d) = ((k : ℕ) : ZMod d) + (p.1 : ZMod d) then
              xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) else 0) *
          (if ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d) then
              xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ)) else 0)
          = (if ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d) then
              xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) *
                (xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ))) else 0) := by
      intro k
      by_cases hk : ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d)
      · rw [if_pos hk, if_pos hk, if_pos (show ((i : ℕ) : ZMod d) =
            ((k : ℕ) : ZMod d) + (p.1 : ZMod d) by
            linear_combination h - hk), mul_assoc]
      · rw [if_neg hk, if_neg hk, mul_zero]
    rw [Finset.sum_congr rfl (fun k _ => key k),
      sum_label_single d (fun k => xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) *
        (xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ))))
        (((j : ℕ) : ZMod d) + (q.1 : ZMod d))]
    obtain ⟨t, ht⟩ := exists_sub_of_label (label_finIdx d (((j : ℕ) : ZMod d) + (q.1 : ZMod d)))
    rw [omega_zpow, omega_zpow, omega_zpow]
    simp only [mul_assoc]
    rw [← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d),
      ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
    refine xi_zpow_eq_of_dvd ⟨p.2 * t, ?_⟩
    push_cast
    linear_combination 2 * p.2 * ht
  · rw [if_neg h, mul_zero]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases hk : ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d)
    · rw [if_pos hk, if_neg (show ¬(((i : ℕ) : ZMod d) = ((k : ℕ) : ZMod d) + (p.1 : ZMod d)) by
        intro hc
        exact h (by linear_combination hc + hk)), zero_mul]
    · rw [if_neg hk, mul_zero]

/-- Each `D_p` is unitary. -/
theorem D_mul_conjTranspose_D (p : ℤ × ℤ) : D d p * (D d p)ᴴ = 1 := by
  rw [conjTranspose_D, D_mul_D, show (-p).1 = -(p.1) from rfl, show (-p).2 = -(p.2) from rfl,
    show p.2 * (-(p.1)) - p.1 * (-(p.2)) = 0 from by ring,
    show p + -p = ((0 : ℤ), (0 : ℤ)) from (add_neg_cancel p).trans rfl,
    zpow_zero, one_smul, D_zero]

/-- Periodicity up to a phase: `D_{p + d v} = ξ_d^{d(p₁v₂ + v₁p₂) + d² v₁v₂} D_p`. -/
theorem D_add_smul (p v : ℤ × ℤ) :
    D d (p + (d : ℤ) • v) =
      xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * p.2) + (d : ℤ) ^ 2 * (v.1 * v.2)) • D d p := by
  by_cases hd : d = 0
  · subst hd
    ext i j
    exact absurd i.isLt (by omega)
  ext i j
  haveI : NeZero d := ⟨hd⟩
  simp only [D, Matrix.smul_apply, smul_eq_mul]
  rw [show (p + (d : ℤ) • v).1 = p.1 + (d : ℤ) * v.1 from rfl,
    show (p + (d : ℤ) • v).2 = p.2 + (d : ℤ) * v.2 from rfl]
  push_cast
  simp only [ZMod.natCast_self, zero_mul, add_zero]
  by_cases h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (p.1 : ZMod d)
  · rw [if_pos h, if_pos h]
    rw [omega_zpow, omega_zpow, ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d),
      ← zpow_add₀ (xi_ne_zero d)]
    refine xi_zpow_eq_of_dvd ⟨v.2 * ((j : ℕ) : ℤ), ?_⟩
    push_cast
    linear_combination (d : ℤ) * v.2 * ((j : ℕ) : ℤ)
  · rw [if_neg h, if_neg h, mul_zero]

/-- `ω_d ^ z = 1` whenever `d ∣ z`. -/
theorem omega_zpow_dvd (d : ℕ) {z : ℤ} (h : (d : ℤ) ∣ z) : omega d ^ z = 1 := by
  by_cases hd : d = 0
  · subst hd
    have h1 : omega 0 = 1 := by
      rw [omega]
      simp
    rw [h1, _root_.one_zpow]
  · obtain ⟨c, hc⟩ := h
    rw [hc, _root_.zpow_mul, zpow_natCast, omega_pow_d_of_ne_zero d hd, _root_.one_zpow]

/-- Powers of `ω_d` are exponentials. -/
theorem omega_exp (d : ℕ) (z : ℤ) :
    omega d ^ z = Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (d : ℂ)) := by
  cases z with
  | ofNat n =>
      show omega d ^ ((n : ℕ) : ℤ) = Complex.exp (2 * ↑Real.pi * Complex.I * ((n : ℕ) : ℂ) / ↑d)
      rw [zpow_natCast]
      simp only [omega]
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
  | negSucc n =>
      rw [zpow_negSucc]
      simp only [omega]
      rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
      congr 1
      push_cast
      ring

/-- `ω_d ^ a ≠ 1` when `d ∤ a`. -/
theorem omega_ne_one_of_not_dvd [NeZero d] {a : ℤ} (ha : ¬ (d : ℤ) ∣ a) : omega d ^ a ≠ 1 := by
  intro h
  apply ha
  have h1 : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (d : ℂ)) = 1 := by
    rw [← omega_exp d a, h]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have h2c : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2c hπ) Complex.I_ne_zero
  have h2 : (2 * Real.pi * Complex.I : ℂ) * (a : ℂ)
      = (2 * Real.pi * Complex.I : ℂ) * ((k : ℂ) * (d : ℂ)) := by
    have h3 := (div_eq_iff hd0).mp hk
    linear_combination h3
  have h4 : (a : ℂ) = ((k * (d : ℕ) : ℤ) : ℂ) := by
    have := mul_left_cancel₀ hpi h2
    push_cast
    push_cast at this
    linear_combination this
  exact ⟨k, (Int.cast_injective h4).trans (mul_comm _ _)⟩

/-- Geometric sum of a nontrivial character over `Fin d`. -/
theorem sum_omega_pow_eq_zero [NeZero d] {a : ℤ} (ha : ¬ (d : ℤ) ∣ a) :
    ∑ i : Fin d, omega d ^ (a * ((i : ℕ) : ℤ)) = 0 := by
  have h1 : omega d ^ a ≠ 1 := omega_ne_one_of_not_dvd ha
  rw [Fin.sum_univ_eq_sum_range (fun k => omega d ^ (a * ((k : ℕ) : ℤ))) d]
  have hterm : ∀ i ∈ Finset.range d, omega d ^ (a * ((i : ℕ) : ℤ)) = (omega d ^ a) ^ i := by
    intro i _
    rw [_root_.zpow_mul, zpow_natCast]
  have h5 : (omega d ^ a) ^ (d : ℕ) = omega d ^ (a * ((d : ℕ) : ℤ)) := by
    rw [← zpow_natCast, ← _root_.zpow_mul]
  rw [Finset.sum_congr rfl (fun i hi => hterm i hi), geom_sum_eq h1, h5, mul_comm,
    omega_zpow_dvd d ⟨a, rfl⟩]
  ring

/-- `Tr D_p` vanishes unless `p ≡ 0 (mod d)`. -/
theorem trace_D [NeZero d] (p : ℤ × ℤ) :
    (D d p).trace = if IsZeroLabel d p then (d : ℂ) * xi d ^ (p.1 * p.2) else 0 := by
  have htr : (D d p).trace = ∑ i, (D d p) i i := by
    show ∑ i, Matrix.diag (D d p) i = ∑ i, (D d p) i i
    rw [Finset.sum_congr rfl (fun i _ => Matrix.diag_apply (D d p) i)]
  rw [htr]
  by_cases h1 : (d : ℤ) ∣ p.1
  · have hp1 : ((p.1 : ℤ) : ZMod d) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd p.1 d).mpr h1
    have entry : ∀ i : Fin d, (D d p) i i = xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) := by
      intro i
      show (if (((i : ℕ) : ℤ) : ZMod d) = (((i : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
          xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) else 0)
        = xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ))
      rw [hp1, add_zero, if_pos rfl]
    rw [Finset.sum_congr rfl (fun i _ => entry i)]
    by_cases h2 : (d : ℤ) ∣ p.2
    · rw [if_pos ⟨h1, h2⟩]
      obtain ⟨c, hc⟩ := h2
      have homega : ∀ i : Fin d, omega d ^ (p.2 * ((i : ℕ) : ℤ)) = 1 := by
        intro i
        exact omega_zpow_dvd d ⟨c * (i : ℕ), by
          push_cast
          linear_combination ((i : ℕ) : ℤ) * hc⟩
      simp_rw [homega, mul_one]
      simp
    · have hmc : ∀ i : Fin d, xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ))
          = omega d ^ (p.2 * ((i : ℕ) : ℤ)) * xi d ^ (p.1 * p.2) := fun _ => mul_comm _ _
      rw [if_neg (fun hc => h2 hc.2), Finset.sum_congr rfl (fun i _ => hmc i),
        ← Finset.sum_mul, sum_omega_pow_eq_zero h2, zero_mul]
  · have hp1 : ¬ (((p.1 : ℤ) : ZMod d) = 0) := fun hc => h1 ((ZMod.intCast_zmod_eq_zero_iff_dvd p.1 d).mp hc)
    have entry : ∀ i : Fin d, (D d p) i i = 0 := by
      intro i
      show (if (((i : ℕ) : ℤ) : ZMod d) = (((i : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
          xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) else 0) = 0
      rw [if_neg]
      intro h
      exact hp1 (show ((p.1 : ℤ) : ZMod d) = (0 : ZMod d) from by linear_combination -h)
    rw [Finset.sum_congr rfl (fun i _ => entry i), Finset.sum_const_zero, if_neg (fun hc => h1 hc.1)]

/-- `ω_d ≠ 0`. -/
theorem omega_ne_zero (d : ℕ) : omega d ≠ 0 := by
  show Complex.exp _ ≠ 0
  exact Complex.exp_ne_zero _

/-- The character sum `∑_{s ∈ (ℤ/d)²} ω_d^{u₂s₁ - u₁s₂}` vanishes for `u ≢ 0 (mod d)`. -/
theorem sum_omega_symplectic [NeZero d] (u : ℤ × ℤ) (hu : ¬ IsZeroLabel d u) :
    ∑ s : Fin d × Fin d, omega d ^ (u.2 * ((s.1 : ℕ) : ℤ) - u.1 * ((s.2 : ℕ) : ℤ)) = 0 := by
  have hsplit : ∀ a b : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ) - u.1 * ((b : ℕ) : ℤ))
      = omega d ^ (u.2 * ((a : ℕ) : ℤ)) * omega d ^ ((-u.1) * ((b : ℕ) : ℤ)) := by
    intro a b
    rw [zpow_sub₀ (omega_ne_zero d), div_eq_mul_inv, ← _root_.zpow_neg, ← neg_mul]
  by_cases h2 : (d : ℤ) ∣ u.2
  · have h1 : ¬ ((d : ℤ) ∣ u.1) := fun hc => hu ⟨hc, h2⟩
    have h1n : ¬ ((d : ℤ) ∣ (-u.1)) := fun hc => h1 (dvd_neg.mp hc)
    rw [Fintype.sum_prod_type' (fun a b : Fin d => omega d ^ (u.2 * ((a : ℕ) : ℤ)
      - u.1 * ((b : ℕ) : ℤ)))]
    refine Finset.sum_eq_zero ?_
    intro a _
    have hbeta : ∑ b : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ) - u.1 * ((b : ℕ) : ℤ))
        = ∑ b : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ))
          * omega d ^ ((-u.1) * ((b : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun b _ => hsplit a b)
    have hmc : ∀ b : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ)) * omega d ^ ((-u.1) * ((b : ℕ) : ℤ))
        = omega d ^ ((-u.1) * ((b : ℕ) : ℤ)) * omega d ^ (u.2 * ((a : ℕ) : ℤ)) :=
      fun _ => mul_comm _ _
    rw [hbeta, Finset.sum_congr rfl (fun b _ => hmc b), ← Finset.sum_mul,
      sum_omega_pow_eq_zero h1n, zero_mul]
  · rw [Fintype.sum_prod_type' (fun a b : Fin d => omega d ^ (u.2 * ((a : ℕ) : ℤ)
      - u.1 * ((b : ℕ) : ℤ))), Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro b _
    have hbeta : ∑ a : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ) - u.1 * ((b : ℕ) : ℤ))
        = ∑ a : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ))
          * omega d ^ ((-u.1) * ((b : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun a _ => hsplit a b)
    rw [hbeta, ← Finset.sum_mul, sum_omega_pow_eq_zero h2, zero_mul]

/-- Expansion in the displacement basis: `A = d⁻¹ ∑_p Tr(A D_pᴴ) D_p`, `p ∈ {0,…,d-1}²`. -/
theorem eq_sum_ov_smul_D [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) :
    A = (d : ℂ)⁻¹ • ∑ p : Fin d × Fin d,
      ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) • D d (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) := by
  ext i j
  -- Step 0: the D entries in double-cast form.
  have hDxy : ∀ x y : Fin d, (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j
      = (if ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((x : ℕ) : ZMod d) then
          xi d ^ (((x : ℕ) : ℤ) * ((y : ℕ) : ℤ)) * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))
        else 0) := by
    intro x y
    show (if (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (((x : ℕ) : ℤ) : ZMod d) then
        xi d ^ (((x : ℕ) : ℤ) * ((y : ℕ) : ℤ))
          * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)) else 0) = _
    push_cast
    rfl
  -- Step 1: the overlap formula.
  have hov : ∀ a b : Fin d, ov d A (((a : ℕ) : ℤ), ((b : ℕ) : ℤ))
      = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
        * ∑ s : Fin d, omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
          * A s (finIdx d (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d))) := by
    intro a b
    have hDt : (D d (((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))ᴴ
        = D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ)) := by
      rw [conjTranspose_D, show (-(((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))
        = (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ)) from rfl]
    show (A * (D d (((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))ᴴ).trace = _
    rw [hDt]
    have h1 : ∀ s : Fin d, Matrix.diag (A * D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) s
        = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
          * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d)))) := by
      intro s
      rw [Matrix.diag_apply, Matrix.mul_apply]
      have hD : ∀ k : Fin d, (D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) k s
          = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
            * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
              * (if ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d) then
                (1 : ℂ) else 0)) := by
        intro k
        simp only [D]
        push_cast
        rw [neg_mul_neg]
        by_cases hc : ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ZMod d))
        · rw [if_pos hc, if_pos hc, mul_one]
        · rw [if_neg hc, if_neg hc, mul_zero, mul_zero]
      have hpull : ∀ k : Fin d, A s k * (D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) k s
          = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
            * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
              * (if ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d) then
                A s k else 0)) := by
        intro k
        rw [hD k]
        by_cases hc : ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d)
        · rw [if_pos hc, if_pos hc, mul_one]
          ring
        · rw [if_neg hc, if_neg hc]
          ring
      rw [Finset.sum_congr rfl (fun k _ => hpull k), ← Finset.mul_sum,
        Finset.sum_congr rfl (fun k _ => by rw [mul_ite, mul_zero]),
        sum_label_single d (fun k => omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ)) * A s k)
          (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d))]
    show (∑ s, Matrix.diag (A * D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) s) = _
    rw [Finset.sum_congr rfl (fun s _ => h1 s), ← Finset.mul_sum]
  -- Step 2: the p₁-collapse.
  set r : Fin d := finIdx d (((i : ℕ) : ZMod d) - ((j : ℕ) : ZMod d)) with hrdef
  have hr : ((r : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) - ((j : ℕ) : ZMod d) := label_finIdx d _
  have hsum : ∑ p : Fin d × Fin d,
      ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))
        * (D d (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))) i j = (d : ℂ) * A i j := by
    rw [Fintype.sum_prod_type' (fun x y : Fin d =>
      ov d A (((x : ℕ) : ℤ), ((y : ℕ) : ℤ)) * (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j)]
    have hzero : ∀ x : Fin d, x ≠ r → ∑ y : Fin d,
        (ov d A (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))
          * (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j) = 0 := by
      intro x hx
      refine Finset.sum_eq_zero ?_
      intro y _
      rw [hDxy x y, if_neg (show ¬(((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((x : ℕ) : ZMod d)) by
        intro hcon
        exact hx (fin_ext_of_label (show ((x : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) by
          rw [hr]
          linear_combination -hcon))), mul_zero]
    rw [Fintype.sum_eq_single r hzero,
      Finset.sum_congr rfl (fun y _ => by
        rw [hDxy r y, if_pos (show ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((r : ℕ) : ZMod d) by
          linear_combination -hr), hov r y])]
    -- per-y summand algebra
    have hph : ∀ y s : Fin d, xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
          * (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ))
            * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
              * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))))
        = omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ)) := by
      intro y s
      rw [omega_zpow, omega_zpow, omega_zpow,
        ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
      refine xi_zpow_eq_of_dvd (⟨0, ?_⟩ : ((2 * d : ℕ) : ℤ) ∣ _)
      push_cast
      ring
    have htaux : ∀ y s : Fin d,
        (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ))
              * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)))))
          * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)))
        = omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
          * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) := by
      intro y s
      rw [mul_assoc,
        mul_right_comm (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ)))
          (A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))))
          (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))),
        ← mul_assoc, hph y s]
    have hterm : ∀ y : Fin d,
        (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * ∑ s' : Fin d, omega d ^ (-((y : ℕ) : ℤ) * ((s' : ℕ) : ℤ))
              * A s' (finIdx d (((s' : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))))
          * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)))
        = ∑ s : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) := by
      intro y
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun s _ => htaux y s)]
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_comm]
    have hpull2 : ∀ s : Fin d,
        ∑ y : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)))
        = (∑ y : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ)))
          * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) :=
      fun s => (Finset.sum_mul _ _ _).symm
    rw [Finset.sum_congr rfl (fun s _ => hpull2 s)]
    -- inner character sum
    have hinner : ∀ s : Fin d, ∑ y : Fin d,
        omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
        = if s = i then (d : ℂ) else 0 := by
      intro s
      by_cases hs : s = i
      · rw [hs]
        have hdvd : (d : ℤ) ∣ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) + ((r : ℕ) : ℤ)) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          rw [hr]
          ring
        rw [Finset.sum_congr rfl (fun y _ => omega_zpow_dvd d
          (dvd_mul_of_dvd_left hdvd _))]
        simp
      · have hnd : ¬((d : ℤ) ∣ (((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ))) := by
          intro hc
          have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
          push_cast at h0
          rw [hr] at h0
          exact hs (fin_ext_of_label (show ((s : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) by
            linear_combination -h0))
        rw [sum_omega_pow_eq_zero hnd, if_neg hs]
    rw [Finset.sum_congr rfl (fun s _ => by rw [hinner s, ite_mul, zero_mul])]
    rw [Fintype.sum_eq_single i (fun s hs => by rw [if_neg hs]),
      if_pos rfl]
    have hkj : finIdx d (((i : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)) = j :=
      fin_ext_of_label (show ((j : ℕ) : ZMod d)
          = ((finIdx d (((i : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)) : ℕ) : ZMod d) from by
        rw [label_finIdx]
        push_cast
        linear_combination hr).symm
    rw [hkj]
  -- Step 3: conclude.
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hsum, inv_mul_cancel_left₀ (by exact_mod_cast (NeZero.ne d) : (d : ℂ) ≠ 0)]

/-- A ring endomorphism of `ℂ` permutes the displacement operators:
`σ(D_p) = D_{(p₁, k p₂)}` for some `k` coprime to `d`. -/
theorem exists_map_D [NeZero d] (σ : ℂ →+* ℂ) :
    ∃ k : ℤ, IsCoprime k (d : ℤ) ∧ ∀ p : ℤ × ℤ, (D d p).map σ = D d (p.1, k * p.2) := by
  have h2d : (2 * d : ℕ) ≠ 0 := fun h => NeZero.ne d (by simpa using h)
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))) (2 * d) :=
    Complex.isPrimitiveRoot_exp (2 * d) h2d
  have he : Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))
      = Complex.exp (Real.pi * Complex.I / d) := by
    congr 1
    have hd : ((d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    field_simp [hd]
    push_cast
    ring
  have hinj : Function.Injective σ := RingHom.injective σ
  have hσprim : IsPrimitiveRoot (σ (Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)))) (2 * d) :=
    (IsPrimitiveRoot.map_iff_of_injective (f := σ.toMonoidHom) hinj).mpr hprim
  obtain ⟨m, _, hm⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hprim hσprim.pow_eq_one
  have hcop : Nat.Coprime m (2 * d) := by
    refine (hprim.pow_iff_coprime (Nat.pos_of_ne_zero h2d) m).mp ?_
    rw [hm]
    exact hσprim
  have h2m : ¬ 2 ∣ m := by
    intro h2m
    have hg : 2 ∣ Nat.gcd m (2 * d) := Nat.dvd_gcd h2m ⟨d, by ring⟩
    rw [show Nat.gcd m (2 * d) = 1 from hcop] at hg
    norm_num at hg
  have hneg1 : (-1 : ℂ) ^ m = -1 := by
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact absurd (by rw [ht]; exact ⟨t, by ring⟩) h2m
    · exact Odd.neg_one_pow ⟨t, ht⟩
  refine ⟨(m : ℤ), (Nat.Coprime.coprime_mul_left_right hcop).cast, ?_⟩
  intro p
  ext i j
  simp only [Matrix.map_apply, D]
  by_cases hc : (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d)
  · rw [if_pos hc, if_pos hc]
    have hw : Complex.exp (2 * Real.pi * Complex.I / d)
        = Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)) ^ (2 : ℕ) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      have hd : ((d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
      field_simp [hd]
      push_cast
      ring
    have hx : σ (xi d) = xi d ^ ((m : ℕ) : ℤ) := by
      show σ (-Complex.exp (Real.pi * Complex.I / d))
        = (-Complex.exp (Real.pi * Complex.I / d)) ^ ((m : ℕ) : ℤ)
      rw [map_neg, ← he, ← hm]
      rw [show (-Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))) ^ ((m : ℕ) : ℤ)
          = (-1 : ℂ) * Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)) ^ m from by
        rw [neg_eq_neg_one_mul, mul_zpow, zpow_natCast, zpow_natCast, hneg1]]
      rw [neg_one_mul]
    have hw' : σ (omega d) = omega d ^ ((m : ℕ) : ℤ) := by
      show σ (Complex.exp (2 * Real.pi * Complex.I / d))
        = Complex.exp (2 * Real.pi * Complex.I / d) ^ ((m : ℕ) : ℤ)
      rw [hw, map_pow, ← hm, ← _root_.pow_mul, _root_.zpow_natCast, ← _root_.pow_mul,
        Nat.mul_comm m 2]
    rw [map_mul, map_zpow₀ σ (xi d) (p.1 * p.2), map_zpow₀ σ (omega d) (p.2 * ((j : ℕ) : ℤ)),
      hx, hw', ← _root_.zpow_mul, ← _root_.zpow_mul]
    congr 1
    · congr 1
      ring
    · congr 1
      ring
  · rw [if_neg hc, if_neg hc]
    exact map_zero σ


/-- For an idempotent matrix over `ℂ`, rank equals trace. -/
theorem rank_eq_trace_of_idem (A : Matrix (Fin d) (Fin d) ℂ) (hA : A * A = A) :
    ((A.rank : ℕ) : ℂ) = A.trace := by
  have he : IsIdempotentElem A.mulVecLin := by
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hA]
  have htrL : A.trace = LinearMap.trace ℂ (Fin d → ℂ) A.mulVecLin := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin d))]
    congr 1
    ext i j
    simp [Matrix.mulVecLin, LinearMap.toMatrix]
  have hr : A.rank = Module.finrank ℂ (LinearMap.range A.mulVecLin) := by
    rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d))]
    rfl
  have hp : LinearMap.IsProj (LinearMap.range A.mulVecLin) A.mulVecLin :=
    LinearMap.IsIdempotentElem.isProj_range A.mulVecLin he
  rw [htrL, LinearMap.IsProj.trace hp, ← hr]

/-- A rank-one Hermitian projector is `ψ ψᴴ` for a unit vector `ψ`. -/
theorem exists_unit_of_rank_one (A : Matrix (Fin d) (Fin d) ℂ) (hH : A.IsHermitian)
    (hA : A * A = A) (h1 : A.rank = 1) :
    ∃ ψ : Fin d → ℂ, ∑ i, Complex.normSq (ψ i) = 1 ∧ ∀ i j, A i j = ψ i * star (ψ j) := by
  have hcj : ∀ k l, A l k = star (A k l) := fun k l => by
    have h1' : Matrix.conjTranspose A l k = A l k := by rw [show Matrix.conjTranspose A = A from hH]
    rw [Matrix.conjTranspose_apply] at h1'
    exact h1'.symm
  have htr : (1 : ℂ) = A.trace := by
    have h2 := rank_eq_trace_of_idem A hA
    rw [h1] at h2
    exact_mod_cast h2
  obtain ⟨k, hk⟩ : ∃ k, A k k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : A.trace = (0:ℂ) := by
      show ∑ i, Matrix.diag A i = 0
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Matrix.diag_apply]
      exact hcon i
    rw [hz] at htr
    exact absurd htr (by norm_num)
  set u : Fin d → ℂ := fun i => A i k with hu
  have hAu : A *ᵥ u = u := by
    funext i
    have h2 : (A * A) i k = A i k := congrFun (congrFun hA i) k
    rw [Matrix.mul_apply] at h2
    show ∑ l, A i l * u l = u i
    simpa [hu] using h2
  have hrk : Module.finrank ℂ (LinearMap.range A.mulVecLin) = 1 := by
    have h5 : A.rank = Module.finrank ℂ (LinearMap.range A.mulVecLin) := by
      rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d))]
      rfl
    rw [← h5]
    exact h1
  have huMem : u ∈ LinearMap.range A.mulVecLin := by
    refine ⟨u, ?_⟩
    show A *ᵥ u = u
    exact hAu
  have hspan : LinearMap.range A.mulVecLin = Submodule.span ℂ {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrk huMem (fun h => hk (congrFun h k))
  have hcol : ∀ j, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j (1:ℂ), ?_⟩
    funext i
    show (A *ᵥ Pi.single j (1:ℂ)) i = A i j
    simp [Matrix.mulVec, Matrix.mulVec_single]
  have hdec : ∀ j, ∃ c : ℂ, ∀ i, A i j = c * u i := by
    intro j
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hcol j)
    exact ⟨c, fun i => by simpa using (congrFun hc i).symm⟩
  have hform : ∀ i j, A i j = A i k * A k j / A k k := by
    intro i j
    obtain ⟨c, hc⟩ := hdec j
    have hik : A i j = c * A i k := hc i
    have hkj : A k j = c * A k k := hc k
    rw [hik, hkj]
    field_simp [hk]
  -- A k k = ofReal (∑ normSq (A k l)), positive
  have hkksum : A k k = ∑ l, ((Complex.normSq (A k l) : ℝ) : ℂ) := by
    have h2 : (A * A) k k = A k k := congrFun (congrFun hA k) k
    rw [Matrix.mul_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hcj k l]
    simp only [Complex.star_def, Complex.mul_conj]
  have hsumnn : 0 ≤ ∑ l, Complex.normSq (A k l) :=
    Finset.sum_nonneg (fun l _ => Complex.normSq_nonneg _)
  have hrne : (∑ l, Complex.normSq (A k l)) ≠ 0 := by
    intro hz
    apply hk
    rw [hkksum, ← Complex.ofReal_sum, hz]
    simp
  obtain ⟨r, hr0, hrc⟩ : ∃ r : ℝ, 0 < r ∧ ((r : ℂ) = A k k) := by
    refine ⟨∑ l, Complex.normSq (A k l), lt_of_le_of_ne hsumnn (Ne.symm hrne), ?_⟩
    rw [hkksum]
    exact Complex.ofReal_sum _ _
  -- the column sum equals the row sum
  have hcolsum : ∑ i, Complex.normSq (A i k) = r := by
    have h7 : ((∑ i, Complex.normSq (A i k) : ℝ) : ℂ) = A k k := by
      rw [Complex.ofReal_sum, hkksum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcj k i]
      simp only [Complex.star_def, Complex.normSq_conj]
    exact Complex.ofReal_inj.mp (h7.trans hrc.symm)
  refine ⟨fun i => A i k / ((Real.sqrt r : ℂ)), ?_, ?_⟩
  · have hdiv : ∀ i, Complex.normSq (A i k / ((Real.sqrt r : ℂ)))
        = Complex.normSq (A i k) / r := by
      intro i
      rw [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt hr0.le]
    show ∑ i, Complex.normSq (A i k / ((Real.sqrt r : ℂ))) = 1
    rw [Finset.sum_congr rfl (fun i _ => hdiv i), ← Finset.sum_div, hcolsum, div_self hr0.ne']
  · intro i j
    rw [hform i j, hcj j k, ← hrc]
    show A i k * star (A j k) / ((r : ℝ) : ℂ)
      = A i k / ((Real.sqrt r : ℂ)) * star (A j k / ((Real.sqrt r : ℂ)))
    have hsd : star (A j k / ((Real.sqrt r : ℂ)))
        = star (A j k) / star ((Real.sqrt r : ℂ)) := star_div₀ _ _
    have hs : star ((Real.sqrt r : ℂ)) = ((Real.sqrt r : ℂ)) := by simp
    rw [hsd, hs, div_mul_div_comm]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr0.le]

end SICLean
