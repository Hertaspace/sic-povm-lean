import SICLean.Inputs
import SICLean.WHBasic

/-!
# From the Galois input to a Hermitian fiducial

Integer lifts are retained throughout. A coprime diagonal label map is surjective
only modulo `d`; `D_add_smul` supplies the phase when a lift is changed.
-/

noncomputable section

open Matrix

namespace SICLean

private theorem galois_xi_normSq (d : ℕ) (n : ℤ) :
    Complex.normSq (xi d ^ n) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_zpow]
  have h : ‖xi d‖ = 1 := by
    simp [xi, Complex.norm_exp]
  rw [h]
  simp

theorem map_rsicConst (d r : ℕ) (σ : ℂ →+* ℂ) :
    σ (rsicConst d r : ℂ) = (rsicConst d r : ℂ) := by
  simp [rsicConst, map_div₀]

theorem rsicConst_pos {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r < d) :
    0 < rsicConst d r := by
  have hd' : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrd' : (r : ℝ) < d := by exact_mod_cast hrd
  unfold rsicConst
  exact div_pos (mul_pos hr' (sub_pos.mpr hrd')) (by nlinarith)

private theorem galois_ov_adj {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (p : ℤ × ℤ) : ov d Aᴴ p = star (ov d A (-p)) := by
  simp only [ov, ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [conjTranspose_D, trace_mul_comm]

theorem map_ov_of_map_D {d : ℕ} (σ : ℂ →+* ℂ) (k : ℤ)
    (hD : ∀ p : ℤ × ℤ, (D d p).map σ = D d (p.1, k * p.2))
    (A : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) :
    σ (ov d A p) = ov d (A.map σ) (p.1, k * p.2) := by
  simp only [ov, conjTranspose_D, AddMonoidHom.map_trace, Matrix.map_mul]
  rw [hD]
  congr 2
  simp

private theorem galois_ov_phase {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    {p q : ℤ × ℤ} {z : ℂ} (h : D d q = z • D d p) :
    ov d A q = star z * ov d A p := by
  simp only [ov, h, conjTranspose_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

private theorem galois_lift {d : ℕ} {k : ℤ} (hk : IsCoprime k (d : ℤ))
    (q : ℤ × ℤ) : ∃ p v : ℤ × ℤ,
      q = (p.1, k * p.2) + (d : ℤ) • v ∧
      (IsZeroLabel d p → IsZeroLabel d q) := by
  obtain ⟨a, b, hab⟩ := hk
  refine ⟨(q.1, a * q.2), (0, b * q.2), ?_, ?_⟩
  · apply Prod.ext
    · change q.1 = q.1 + (d : ℤ) * 0
      simp
    · change q.2 = k * (a * q.2) + (d : ℤ) * (b * q.2)
      calc
        q.2 = (a * k + b * (d : ℤ)) * q.2 := by rw [hab, one_mul]
        _ = k * (a * q.2) + (d : ℤ) * (b * q.2) := by ring
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    have heq : q.2 = k * (a * q.2) + (d : ℤ) * (b * q.2) := by
      calc
        q.2 = (a * k + b * (d : ℤ)) * q.2 := by rw [hab, one_mul]
        _ = _ := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right h₂ k) (dvd_mul_right _ _)

private theorem galois_eq_of_ov [NeZero d]
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ p : Fin d × Fin d,
      ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) =
      ov d B (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))) : A = B := by
  rw [eq_sum_ov_smul_D A, eq_sum_ov_smul_D B]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [h p]

/-- The Galois image is a Hermitian idempotent with rational trace and the
prescribed displacement overlap moduli. No commutation of `σ` with star is assumed. -/
theorem map_fiducial_of_ghost_flip {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hrd : r < d) {G : Matrix (Fin d) (Fin d) ℂ} (hG : IsGhost d r G)
    {σ : ℂ →+* ℂ} (hσ : UnimodularFlip d r G σ) :
    (G.map σ).IsHermitian ∧
    G.map σ * G.map σ = G.map σ ∧
    (G.map σ).trace = r ∧
    ∀ q : ℤ × ℤ, ¬ IsZeroLabel d q →
      Complex.normSq (ov d (G.map σ) q) = rsicConst d r := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨k, hk, hD⟩ := exists_map_D (d := d) σ
  let P := G.map σ
  have ht : P.trace = r := by
    change (G.map σ).trace = r
    rw [← AddMonoidHom.map_trace, hG.trace_eq, map_natCast]
  have hm (p : ℤ × ℤ) :
      σ (ov d G p) = ov d P (p.1, k * p.2) := map_ov_of_map_D σ k hD G p
  have hcpos := rsicConst_pos hd hr hrd
  have hconj (p : ℤ × ℤ) (hp : ¬ IsZeroLabel d p) :
      ov d P (-(p.1, k * p.2)) = star (ov d P (p.1, k * p.2)) := by
    have hnonzero : σ (ov d G p) ≠ 0 := by
      intro hz
      have hh := hσ p hp
      rw [hz, Complex.normSq_zero] at hh
      linarith
    have hprod : σ (ov d G p) * σ (ov d G (-p)) = (rsicConst d r : ℂ) := by
      rw [← map_mul, hG.ov_mul_ov_neg p hp, map_rsicConst]
    have hnorm : σ (ov d G p) * star (σ (ov d G p)) = (rsicConst d r : ℂ) := by
      change σ (ov d G p) * starRingEnd ℂ (σ (ov d G p)) = _
      rw [Complex.mul_conj, hσ p hp]
    have hh := mul_left_cancel₀ hnonzero (hprod.trans hnorm.symm)
    rw [hm p, hm (-p)] at hh
    simpa using hh
  have hmod (q : ℤ × ℤ) (hq : ¬ IsZeroLabel d q) :
      Complex.normSq (ov d P q) = rsicConst d r := by
    obtain ⟨p, v, hqeq, hpq⟩ := galois_lift hk q
    have hp : ¬ IsZeroLabel d p := fun hp => hq (hpq hp)
    have hphase : D d q =
        xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * (k * p.2)) +
          (d : ℤ) ^ 2 * (v.1 * v.2)) • D d (p.1, k * p.2) := by
      rw [hqeq, D_add_smul]
    rw [galois_ov_phase P hphase, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      galois_xi_normSq, one_mul, ← hm p]
    exact hσ p hp
  have hH : P.IsHermitian := by
    apply galois_eq_of_ov
    intro s
    let q : ℤ × ℤ := (((s.1 : ℕ) : ℤ), ((s.2 : ℕ) : ℤ))
    change ov d Pᴴ q = ov d P q
    by_cases hq : IsZeroLabel d q
    · have hqzero : q = (0, 0) := by
        have h₁ : (s.1 : ℤ) = 0 := by
          have hlt : (s.1 : ℤ) < d := by exact_mod_cast s.1.isLt
          have hnn : (0 : ℤ) ≤ s.1 := by positivity
          exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnn hlt hq.1
        have h₂ : (s.2 : ℤ) = 0 := by
          have hlt : (s.2 : ℤ) < d := by exact_mod_cast s.2.isLt
          have hnn : (0 : ℤ) ≤ s.2 := by positivity
          exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnn hlt hq.2
        exact Prod.ext h₁ h₂
      simp [hqzero, ov, D_zero, trace_conjTranspose, ht]
    · obtain ⟨p, v, hqeq, hpq⟩ := galois_lift hk q
      have hp : ¬ IsZeroLabel d p := fun hp => hq (hpq hp)
      have hphase : D d q =
          xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * (k * p.2)) +
            (d : ℤ) ^ 2 * (v.1 * v.2)) • D d (p.1, k * p.2) := by
        rw [hqeq, D_add_smul]
      rw [galois_ov_phase Pᴴ hphase, galois_ov_phase P hphase,
        galois_ov_adj, hconj p hp, star_star]
  refine ⟨hH, ?_, ht, hmod⟩
  rw [← Matrix.map_mul, hG.idem]

end SICLean
