import SICLean.WHBasic

/-!
# The Weyl–Heisenberg orbit of an r-SIC fiducial

The proof uses displacement-basis Fourier expansion. All labels remain integer pairs
until the final finite orbit is indexed by `Fin (d ^ 2)`.
-/

noncomputable section

open Matrix

namespace SICLean

private def orbitLabel {d : ℕ} (p : Fin d × Fin d) : ℤ × ℤ :=
  ((p.1 : ℕ), (p.2 : ℕ))

private def orbitSymp (p q : ℤ × ℤ) : ℤ := p.2 * q.1 - p.1 * q.2

private def orbitMatrix {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) :=
  D d p * P * (D d p)ᴴ

private theorem orbit_D_adjoint_mul {d : ℕ} (p : ℤ × ℤ) :
    (D d p)ᴴ * D d p = 1 := by
  simpa only [conjTranspose_D, neg_neg] using D_mul_conjTranspose_D (d := d) (-p)

private theorem orbit_trace {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) :
    (orbitMatrix P p).trace = P.trace := by
  rw [orbitMatrix, Matrix.trace_mul_cycle, orbit_D_adjoint_mul, Matrix.one_mul]

private theorem orbit_idem {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P * P = P) (p : ℤ × ℤ) :
    orbitMatrix P p * orbitMatrix P p = orbitMatrix P p := by
  dsimp [orbitMatrix]
  calc
    D d p * P * (D d p)ᴴ * (D d p * P * (D d p)ᴴ) =
        D d p * (P * ((D d p)ᴴ * D d p) * P) * (D d p)ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = D d p * P * (D d p)ᴴ := by
      rw [orbit_D_adjoint_mul, Matrix.mul_one, hP]

private theorem orbit_hermitian {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hH : P.IsHermitian) (p : ℤ × ℤ) : (orbitMatrix P p).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose (D d p) hH

private theorem orbit_D_conjugate {d : ℕ} (p s : ℤ × ℤ) :
    D d p * D d s * (D d p)ᴴ = omega d ^ orbitSymp p s • D d s := by
  rw [conjTranspose_D, D_mul_D, Matrix.smul_mul, D_mul_D, smul_smul]
  have hl : p + s + -p = s := by ext <;> simp
  rw [hl]
  congr 1
  rw [← zpow_add₀ (xi_ne_zero d)]
  have he : p.2 * s.1 - p.1 * s.2 +
      ((p + s).2 * (-p).1 - (p + s).1 * (-p).2) =
      2 * orbitSymp p s := by
    dsimp [orbitSymp]
    ring
  rw [he, _root_.zpow_mul, show xi d ^ (2 : ℤ) = omega d by
    simpa using (omega_eq_xi_sq d).symm]

private theorem orbit_trace_D {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (p s : ℤ × ℤ) :
    (orbitMatrix P p * D d s).trace =
      omega d ^ orbitSymp (-p) s * (P * D d s).trace := by
  dsimp [orbitMatrix]
  calc
    (D d p * P * (D d p)ᴴ * D d s).trace =
        (P * ((D d p)ᴴ * D d s * D d p)).trace := by
      calc
        _ = (D d p * (P * (D d p)ᴴ * D d s)).trace := by
          simp only [Matrix.mul_assoc]
        _ = ((P * (D d p)ᴴ * D d s) * D d p).trace :=
          Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    _ = (P * (omega d ^ orbitSymp (-p) s • D d s)).trace := by
      rw [conjTranspose_D, show D d (-p) * D d s * D d p =
        omega d ^ orbitSymp (-p) s • D d s by
          simpa only [conjTranspose_D, neg_neg] using orbit_D_conjugate (d := d) (-p) s]
    _ = omega d ^ orbitSymp (-p) s * (P * D d s).trace := by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

private theorem orbit_trace_D_of_hermitian {d : ℕ}
    {P : Matrix (Fin d) (Fin d) ℂ} (hH : P.IsHermitian) (s : ℤ × ℤ) :
    (P * D d s).trace = star (ov d P s) := by
  rw [ov, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.trace_mul_comm]

private theorem orbit_expansion {d : ℕ} [NeZero d]
    (P : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) :
    orbitMatrix P p = (d : ℂ)⁻¹ • ∑ s : Fin d × Fin d,
      (ov d P (orbitLabel s) * omega d ^ orbitSymp p (orbitLabel s)) •
        D d (orbitLabel s) := by
  calc
    _ = D d p * ((d : ℂ)⁻¹ • ∑ s : Fin d × Fin d,
        ov d P (orbitLabel s) • D d (orbitLabel s)) * (D d p)ᴴ := by
      exact congrArg (fun A => D d p * A * (D d p)ᴴ) (eq_sum_ov_smul_D P)
    _ = _ := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
        orbit_D_conjugate, smul_smul]

private theorem orbit_trace_product_fourier {d : ℕ} [NeZero d]
    {P : Matrix (Fin d) (Fin d) ℂ} (hH : P.IsHermitian) (p q : ℤ × ℤ) :
    (orbitMatrix P p * orbitMatrix P q).trace = (d : ℂ)⁻¹ *
      ∑ s : Fin d × Fin d, (Complex.normSq (ov d P (orbitLabel s)) : ℂ) *
        omega d ^ orbitSymp (q - p) (orbitLabel s) := by
  calc
    _ = (d : ℂ)⁻¹ * ∑ s : Fin d × Fin d,
        (ov d P (orbitLabel s) * omega d ^ orbitSymp q (orbitLabel s)) *
          (orbitMatrix P p * D d (orbitLabel s)).trace := by
      rw [orbit_expansion P q]
      simp only [Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_smul,
        Matrix.trace_sum, smul_eq_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [orbit_trace_D, orbit_trace_D_of_hermitian hH]
      have he : orbitSymp (q - p) (orbitLabel s) =
          orbitSymp q (orbitLabel s) + orbitSymp (-p) (orbitLabel s) := by
        dsimp [orbitSymp]
        ring
      rw [he, zpow_add₀ (show omega d ≠ 0 by
          rw [omega_eq_xi_sq]; exact pow_ne_zero _ (xi_ne_zero d)),
        Complex.normSq_eq_conj_mul_self]
      change (ov d P (orbitLabel s) * _) * (_ * star (ov d P (orbitLabel s))) =
        (star (ov d P (orbitLabel s)) * ov d P (orbitLabel s)) * _
      ring

private theorem orbit_fin_eq_of_dvd_sub {d : ℕ} (p q : Fin d)
    (h : (d : ℤ) ∣ (q : ℤ) - (p : ℤ)) : p = q := by
  have hz : ((p : ℕ) : ZMod d) = ((q : ℕ) : ZMod d) := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (p : ℤ) (q : ℤ) d).2 h
  apply Fin.ext
  have hm := (ZMod.natCast_eq_natCast_iff' (p : ℕ) (q : ℕ) d).1 hz
  simpa only [Nat.mod_eq_of_lt p.isLt, Nat.mod_eq_of_lt q.isLt] using hm

private theorem orbit_label_zero_iff {d : ℕ} [NeZero d] (s : Fin d × Fin d) :
    IsZeroLabel d (orbitLabel s) ↔ s = 0 := by
  constructor
  · intro hs
    apply Prod.ext
    · exact (orbit_fin_eq_of_dvd_sub (0 : Fin d) s.1 (by simpa [orbitLabel] using hs.1)).symm
    · exact (orbit_fin_eq_of_dvd_sub (0 : Fin d) s.2 (by simpa [orbitLabel] using hs.2)).symm
  · rintro rfl
    simp [IsZeroLabel, orbitLabel]

private theorem orbit_label_sub_nonzero {d : ℕ} {p q : Fin d × Fin d} (hpq : p ≠ q) :
    ¬ IsZeroLabel d (orbitLabel q - orbitLabel p) := by
  intro hz
  apply hpq
  exact Prod.ext (orbit_fin_eq_of_dvd_sub p.1 q.1 hz.1)
    (orbit_fin_eq_of_dvd_sub p.2 q.2 hz.2)

private theorem orbit_fourier_sum {d r : ℕ} [NeZero d]
    {P : Matrix (Fin d) (Fin d) ℂ} (ht : P.trace = r)
    (hov : ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p →
      Complex.normSq (ov d P p) = rsicConst d r)
    (u : ℤ × ℤ) (hu : ¬ IsZeroLabel d u) :
    (∑ s : Fin d × Fin d, (Complex.normSq (ov d P (orbitLabel s)) : ℂ) *
      omega d ^ orbitSymp u (orbitLabel s)) = (r : ℂ) ^ 2 - rsicConst d r := by
  have hc (s : Fin d × Fin d) :
      (Complex.normSq (ov d P (orbitLabel s)) : ℂ) =
        (rsicConst d r : ℂ) + if s = 0 then (r : ℂ) ^ 2 - rsicConst d r else 0 := by
    by_cases hs : s = 0
    · subst s
      simp [orbitLabel, ov, D_zero, ht, Complex.normSq_natCast, pow_two]
    · rw [if_neg hs, add_zero, hov _ (fun hz => hs ((orbit_label_zero_iff s).1 hz))]
  calc
    _ = ∑ s : Fin d × Fin d,
        ((rsicConst d r : ℂ) * omega d ^ orbitSymp u (orbitLabel s) +
          if s = 0 then (r : ℂ) ^ 2 - rsicConst d r else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hc s]
      by_cases hsz : s = 0
      · subst s
        simp [orbitSymp, orbitLabel]
      · simp [hsz]
    _ = (rsicConst d r : ℂ) *
        (∑ s : Fin d × Fin d, omega d ^ orbitSymp u (orbitLabel s)) +
          ((r : ℂ) ^ 2 - rsicConst d r) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ = _ := by
      rw [show (∑ s : Fin d × Fin d, omega d ^ orbitSymp u (orbitLabel s)) = 0 from
        sum_omega_symplectic u hu]
      simp

private theorem orbit_trace_product_distinct {d r : ℕ} [NeZero d]
    {P : Matrix (Fin d) (Fin d) ℂ} (hH : P.IsHermitian) (ht : P.trace = r)
    (hov : ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p →
      Complex.normSq (ov d P p) = rsicConst d r)
    {p q : Fin d × Fin d} (hpq : p ≠ q) :
    (orbitMatrix P (orbitLabel p) * orbitMatrix P (orbitLabel q)).trace =
      (d : ℂ)⁻¹ * ((r : ℂ) ^ 2 - rsicConst d r) := by
  rw [orbit_trace_product_fourier hH, orbit_fourier_sum ht hov _
    (orbit_label_sub_nonzero hpq)]

private theorem orbit_off_diagonal_ne_rank {d r : ℕ} (hd : 2 ≤ d)
    (hr : 1 ≤ r) (hrd : r < d) :
    (d : ℂ)⁻¹ * ((r : ℂ) ^ 2 - rsicConst d r) ≠ (r : ℂ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrdR : (r : ℝ) < d := by exact_mod_cast hrd
  have hd2R : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 ≤ rsicConst d r := by
    unfold rsicConst
    apply div_nonneg
    · exact mul_nonneg (le_of_lt hrR) (le_of_lt (sub_pos.mpr hrdR))
    · nlinarith
  have hlt : (d : ℝ)⁻¹ * ((r : ℝ) ^ 2 - rsicConst d r) < r := by
    rw [inv_mul_lt_iff₀ hdR]
    nlinarith
  intro he
  have heR : (d : ℝ)⁻¹ * ((r : ℝ) ^ 2 - rsicConst d r) = r := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_pow, Complex.ofReal_natCast] using he
  exact (ne_of_lt hlt) heR

private theorem orbit_rank {d r : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P * P = P) (ht : P.trace = r) (p : ℤ × ℤ) :
    (orbitMatrix P p).rank = r := by
  have hc : (((orbitMatrix P p).rank : ℕ) : ℂ) = (r : ℂ) := by
    rw [rank_eq_trace_of_idem _ (orbit_idem hP p), orbit_trace, ht]
  exact_mod_cast hc

/-- A Hermitian rank-`r` projector with the constant nonzero displacement overlap
has a Weyl–Heisenberg orbit forming an r-SIC. -/
theorem hasRSIC_of_fiducial {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r < d)
    {P : Matrix (Fin d) (Fin d) ℂ} (hH : P.IsHermitian) (hP : P * P = P)
    (ht : P.trace = r)
    (hov : ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p →
      Complex.normSq (ov d P p) = rsicConst d r) : HasRSIC d r := by
  have : NeZero d := ⟨by omega⟩
  let Q : (Fin d × Fin d) → Matrix (Fin d) (Fin d) ℂ :=
    fun p => orbitMatrix P (orbitLabel p)
  have hQinj : Function.Injective Q := by
    intro p q he
    by_contra hpq
    have hcross := orbit_trace_product_distinct hH ht hov hpq
    change (Q p * Q q).trace = _ at hcross
    rw [← he, orbit_idem hP, orbit_trace, ht] at hcross
    exact orbit_off_diagonal_ne_rank hd hr hrd hcross.symm
  let e : Fin (d ^ 2) ≃ (Fin d × Fin d) :=
    Fintype.equivOfCardEq (by simp [pow_two])
  refine ⟨fun j => Q (e j), ?_, ?_, ?_⟩
  · exact hQinj.comp e.injective
  · intro j
    exact ⟨orbit_hermitian hH _, orbit_idem hP _, orbit_rank hP ht _⟩
  · refine ⟨(d : ℂ)⁻¹ * ((r : ℂ) ^ 2 - rsicConst d r), ?_⟩
    intro j k hjk
    exact orbit_trace_product_distinct hH ht hov (fun he => hjk (e.injective he))

end SICLean
