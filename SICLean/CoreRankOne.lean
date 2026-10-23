import SICLean.WHBasic

/-!
# From a rank-one WH fiducial to the SIC statement

The orbit is constructed as vectors, with the normalization and squared overlap
conditions stated exactly as in `OpenQuantumProblem23.HasSICPOVM`.
-/

noncomputable section

open Matrix

namespace SICLean

private theorem rankOne_norm_xi (d : ℕ) : ‖xi d‖ = 1 := by
  simp [xi, Complex.norm_exp]

private theorem rankOne_normSq_xi_zpow (d : ℕ) (n : ℤ) :
    Complex.normSq (xi d ^ n) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_zpow, rankOne_norm_xi]
  simp

private theorem rankOne_dot_eq_sum_normSq {d : ℕ} (ψ : Fin d → ℂ) :
    star ψ ⬝ᵥ ψ = ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) := by
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

private theorem rankOne_normalized {d : ℕ} (ψ : Fin d → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    OpenQuantumProblem23.IsNormalized (OpenQuantumProblem23.mkStateVector ψ) := by
  have hn : ‖OpenQuantumProblem23.mkStateVector ψ‖ ^ 2 = 1 := by
    simpa only [PiLp.norm_sq_eq_of_L2, Complex.sq_norm] using hψ
  unfold OpenQuantumProblem23.IsNormalized
  nlinarith [norm_nonneg (OpenQuantumProblem23.mkStateVector ψ)]

private theorem rankOne_dot_mulVec {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) :
    star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ) = star ψ ⬝ᵥ ((Aᴴ * B) *ᵥ ψ) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

private theorem rankOne_trace_mul {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    {ψ : Fin d → ℂ} (hψ : ∀ i j, P i j = ψ i * star (ψ j))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (P * A).trace = star ψ ⬝ᵥ (A *ᵥ ψ) := by
  simp only [trace, diag, mul_apply, hψ, mulVec, dotProduct, Pi.star_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem rankOne_orbit_normalized {d : ℕ} (ψ : Fin d → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) (p : ℤ × ℤ) :
    OpenQuantumProblem23.IsNormalized
      (OpenQuantumProblem23.mkStateVector (D d p *ᵥ ψ)) := by
  apply rankOne_normalized
  apply Complex.ofReal_injective
  rw [← rankOne_dot_eq_sum_normSq, rankOne_dot_mulVec]
  have hD : (D d p)ᴴ * D d p = 1 := by
    simpa only [conjTranspose_D, neg_neg] using
      (D_mul_conjTranspose_D (d := d) (-p))
  rw [hD, one_mulVec, rankOne_dot_eq_sum_normSq, hψ]

private theorem rankOne_orbit_overlap {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    {ψ : Fin d → ℂ} (hψ : ∀ i j, P i j = ψ i * star (ψ j))
    (p q : ℤ × ℤ) :
    OpenQuantumProblem23.overlapSq
      (OpenQuantumProblem23.mkStateVector (D d p *ᵥ ψ))
      (OpenQuantumProblem23.mkStateVector (D d q *ᵥ ψ)) =
      Complex.normSq (ov d P (p - q)) := by
  change Complex.normSq (star (D d p *ᵥ ψ) ⬝ᵥ (D d q *ᵥ ψ)) = _
  rw [rankOne_dot_mulVec, conjTranspose_D, D_mul_D, smul_mulVec, dotProduct_smul]
  change Complex.normSq ((xi d ^ ((-p).2 * q.1 - (-p).1 * q.2)) *
    (star ψ ⬝ᵥ (D d (-p + q) *ᵥ ψ))) = _
  rw [Complex.normSq_mul, rankOne_normSq_xi_zpow, one_mul]
  unfold ov
  rw [conjTranspose_D, rankOne_trace_mul hψ]
  congr 3
  abel_nf

private def rankOne_label {d : ℕ} (p : Fin d × Fin d) : ℤ × ℤ :=
  (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))

private theorem rankOne_fin_eq_of_dvd_sub {d : ℕ} {i j : Fin d}
    (h : (d : ℤ) ∣ (i : ℤ) - (j : ℤ)) : i = j := by
  have hm : (j : ℤ) ≡ (i : ℤ) [ZMOD (d : ℤ)] := Int.modEq_iff_dvd.mpr h
  have hi : (i : ℤ) % d = (i : ℤ) := Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
  have hj : (j : ℤ) % d = (j : ℤ) := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  rw [Int.ModEq, hi, hj] at hm
  apply Fin.ext
  exact_mod_cast hm.symm

private theorem rankOne_label_sub_nonzero {d : ℕ} {p q : Fin d × Fin d} (hpq : p ≠ q) :
    ¬ IsZeroLabel d (rankOne_label p - rankOne_label q) := by
  rintro ⟨h₁, h₂⟩
  apply hpq
  apply Prod.ext
  · exact rankOne_fin_eq_of_dvd_sub h₁
  · exact rankOne_fin_eq_of_dvd_sub h₂

private theorem rankOne_rsicConst {d : ℕ} (hd : 2 ≤ d) :
    rsicConst d 1 = OpenQuantumProblem23.sicOverlapSq d := by
  unfold rsicConst OpenQuantumProblem23.sicOverlapSq
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (d : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hsucc : (d : ℝ) + 1 ≠ 0 := by linarith
  norm_num only [Nat.cast_one, one_mul]
  field_simp [hden, hsucc]
  ring

/-- A Hermitian rank-one WH fiducial with the prescribed displacement overlaps
gives a SIC family in the exact vector formulation of the formal conjecture. -/
theorem hasSICPOVM_of_fiducial {d : ℕ} (hd : 2 ≤ d)
    {P : Matrix (Fin d) (Fin d) ℂ} (hH : P.IsHermitian) (hP : P * P = P)
    (ht : P.trace = 1)
    (hov : ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p →
      Complex.normSq (ov d P p) = rsicConst d 1) :
    OpenQuantumProblem23.HasSICPOVM d := by
  have hrank : P.rank = 1 := by
    have hc : (P.rank : ℂ) = 1 := (rank_eq_trace_of_idem P hP).trans ht
    exact_mod_cast hc
  obtain ⟨ψ, hψ, hPψ⟩ := exists_unit_of_rank_one P hH hP hrank
  let e : Fin (d ^ 2) ≃ Fin d × Fin d := Fintype.equivOfCardEq (by simp [pow_two])
  refine ⟨fun j => OpenQuantumProblem23.mkStateVector
    (D d (rankOne_label (e j)) *ᵥ ψ), ?_, ?_⟩
  · intro j
    exact rankOne_orbit_normalized ψ hψ _
  · intro j k hjk
    rw [rankOne_orbit_overlap hPψ]
    rw [hov _ (rankOne_label_sub_nonzero (e.injective.ne hjk))]
    exact rankOne_rsicConst hd

end SICLean
