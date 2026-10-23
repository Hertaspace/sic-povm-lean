import SICLean.L2r.GhostProofs

set_option autoImplicit false

/-!
# F coefficients, the ghost, and a common flip

Reality and parity are not used for the rank-one input, and are not assumed here.
An auxiliary multiplier cancels, and the construction uses F directly.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2r

theorem phase_neg (d r : ℕ) (p : ℤ × ℤ) : phase d r (-p) = phase d r p := by
  exact ghostProof_phase_neg d r p

theorem phase_pow (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ) :
    phase d r p ^ (2 * d) = 1 := by
  exact ghostProof_phase_pow d r p

theorem phase_sq (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ) :
    phase d r p ^ 2 = (torsionGaussian d r (label d p))⁻¹ := by
  exact ghostProof_phase_sq d r p

theorem nu_zero (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) :
    nu d r F 0 = -(originValue d r)⁻¹ ∧
      nu d r F 0 + (nu d r F 0)⁻¹ = -(gap d r : ℂ) * rootLevel d r := by
  exact ghostProof_nu_zero d r hA

theorem nu_mul_neg (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : ℤ × ℤ)
    (hp : ¬ IsZeroLabel d p) : nu d r F p * nu d r F (-p) = 1 := by
  exact ghostProof_nu_mul_neg d r hA p hp

theorem coefficient_add_period (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (p k : ℤ × ℤ) :
    coefficient d r F (p + (d : ℤ) • k) =
      xi d ^ symplectic (p + (d : ℤ) • k) p * coefficient d r F p := by
  exact ghostProof_coefficient_add_period d r F p k

theorem summand_add_period (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (p k : ℤ × ℤ) :
    coefficient d r F (p + (d : ℤ) • k) •
        D d (twistInverseLift d r (p + (d : ℤ) • k)) =
      coefficient d r F p • D d (twistInverseLift d r p) := by
  exact ghostProof_summand_add_period d r F p k

/-- The combined phase identity, valid also at the actual vectors q=0,p. -/
theorem phase_ratio (d r : ℕ) [Fact (Admissible d r)] (p q : ℤ × ℤ) :
    xi d ^ (twistScalar d r * symplectic p q) * phase d r q / phase d r (q - p) =
      (-1 : ℂ) ^ (1 + phaseSignExponent d p) *
        xi d ^ ((r : ℤ) * quadraticForm d r p) *
        L2a.e d ((r : ℤ) * symplectic p (shiftedAlpha d r q)) := by
  exact ghostProof_phase_ratio d r p q

theorem normalized_convolution (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : Index d) (hp : p ≠ 0) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ q : Index d,
      xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
        nu d r F (lift q) / nu d r F (lift q - lift p)) = 0 := by
  exact ghostProof_normalized_convolution d r hA p hp

theorem coefficient_convolution (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : Index d) (hp : p ≠ 0) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ q : Index d, if q = 0 ∨ q = p then 0 else
      xi d ^ (twistScalar d r * symplectic (lift p) (lift q)) *
        nu d r F (lift p - lift q) * nu d r F (lift q)) =
      (gap d r : ℂ) * rootLevel d r * nu d r F (lift p) := by
  exact ghostProof_coefficient_convolution d r hA p hp

theorem ghostProjector_idempotent (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) :
    ghostProjector d r F * ghostProjector d r F = ghostProjector d r F := by
  exact ghostProof_ghostProjector_idempotent d r hA

theorem trace_ghostProjector (d r : ℕ) [Fact (Admissible d r)] (F : Values d) :
    (ghostProjector d r F).trace = r := by
  exact ghostProof_trace_ghostProjector d r F

theorem ov_ghostProjector (d r : ℕ) [Fact (Admissible d r)] (F : Values d)
    (p : ℤ × ℤ) (hp : ¬ IsZeroLabel d p) :
    ov d (ghostProjector d r F) p = coefficient d r F (twistLift d r p) := by
  exact ghostProof_ov_ghostProjector d r F p hp

theorem coefficient_mul_neg (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) (p : ℤ × ℤ)
    (hp : ¬ IsZeroLabel d p) :
    coefficient d r F p * coefficient d r F (-p) = (rsicConst d r : ℂ) := by
  exact ghostProof_coefficient_mul_neg d r hA p hp

theorem isGhost_of_RW_rank (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} (hA : RWConvolutionInput d r F) :
    IsGhost d r (ghostProjector d r F) := by
  exact ghostProof_isGhost_of_RW_rank d r hA

theorem map_phase_norm (d r : ℕ) [Fact (Admissible d r)]
    (τ : ℂ →+* ℂ) (p : ℤ × ℤ) : ‖τ (phase d r p)‖ = 1 := by
  exact ghostProof_map_phase_norm d r τ p

theorem map_rootLevel_eq_or_neg (d r : ℕ) [Fact (Admissible d r)] (τ : ℂ →+* ℂ) :
    τ (rootLevel d r) = rootLevel d r ∨ τ (rootLevel d r) = -rootLevel d r := by
  exact ghostProof_map_rootLevel_eq_or_neg d r τ

theorem map_coefficient_normSq (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput d r F τ)
    (p : ℤ × ℤ) (hp : ¬ IsZeroLabel d p) :
    Complex.normSq (τ (coefficient d r F p)) = rsicConst d r := by
  exact ghostProof_map_coefficient_normSq d r hB p hp

theorem unimodularFlip_of_RW_rank (d r : ℕ) [Fact (Admissible d r)]
    {F : Values d} {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput d r F τ) :
    UnimodularFlip d r (ghostProjector d r F) τ := by
  exact ghostProof_unimodularFlip_of_RW_rank d r hB

end SICLean.L2r
