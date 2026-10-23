import SICLean.L2a.Ghost

/-! # L2a interface: A and B imply the rank-one input -/

noncomputable section

open OpenQuantumProblem23

namespace SICLean.L2a

/-- B is stated on F; rational operations and root-of-unity phases suffice
to transfer it to all nonzero coefficients. No continuity of τ is used. -/
theorem map_coefficient_normSq {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ)
    (i j : ℤ) (hij : ¬ IsZeroLabel M (i, j)) :
    Complex.normSq (τ (coefficient M F i j)) = rsicConst M 1 := by
  have hh : ((i : ZMod M), (j : ZMod M)) ≠ 0 :=
    mt (isZeroLabel_iff_cast i j).mpr hij
  have hF : ‖τ (valueAt F i j)‖ = 1 := hB.norm_F _ hh
  have hd : Complex.normSq (τ (denominator M)) = (M : ℝ) + 1 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
    rcases map_denominator_eq_or_neg hM τ with h | h
    · rw [h, Complex.normSq_ofReal]
      nlinarith
    · rw [h, Complex.normSq_neg, Complex.normSq_ofReal]
      nlinarith
  rw [coefficient, map_div₀, map_neg, map_mul, Complex.normSq_div,
    Complex.normSq_neg, Complex.normSq_mul, hd]
  simp only [Complex.normSq_eq_norm_sq, map_theta_norm hM τ, hF, one_pow, one_mul,
    rsicConst_one hM, one_div]

theorem unimodularFlip_of_RW {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ) :
    UnimodularFlip M 1 (ghostProjector M F) τ := by
  intro p hp
  have hf : ¬ IsZeroLabel M ((fromWH p).1, (fromWH p).2) := by
    simpa [fromWH, IsZeroLabel, and_comm] using hp
  rw [ov_ghostProjector hM hA p hp]
  exact map_coefficient_normSq hM hB _ _ hf

end SICLean.L2a

namespace SICLean

open L2a

/-- The finite M-torsion inputs, with the same τ at every nonzero label,
give the rank-one `GhostGaloisInput`. -/
theorem ghostGaloisInput_of_RW {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ) :
    GhostGaloisInput M 1 := by
  exact ⟨ghostProjector M F, isGhost_of_RW hM hA, τ, unimodularFlip_of_RW hM hA hB⟩

/-- For each M ≥ 4, one common F and τ satisfying A and B yield
`zaunerExistence_of_inputs`. -/
theorem zaunerExistence_of_RW
    (H : ∀ M : ℕ, 4 ≤ M → ∃ F : Values M,
      RWConvolutionInput M F ∧ ∃ τ : ℂ →+* ℂ, RWUnitCircleInput M F τ) :
    ZaunerExistence := by
  apply zaunerExistence_of_inputs
  intro M hM
  obtain ⟨F, hA, τ, hB⟩ := H M hM
  exact ghostGaloisInput_of_RW hM hA hB

end SICLean
