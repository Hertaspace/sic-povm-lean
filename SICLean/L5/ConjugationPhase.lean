import SICLean.L4.EtaMultiplier
import SICLean.L4.SpecialValueGeometry

set_option autoImplicit false

/-!
# The η multiplier and the principal square root

Sources: [RW26, p. 3; Prop. 7, p. 14].
μ is the η quotient at i, and `etaMultiplier_pow_twentyFour` gives the
relation μ^24 = 1.

Square roots are `Complex.sqrt` on `Complex.slitPlane`.
The statements use the L4 interfaces and Mathlib's principal complex power.
-/

noncomputable section

open Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L5.ConjugationPhase

open SICLean.L4

/-- Finite order implies norm one. [RW26, p. 3]. -/
theorem norm_of_pow_eq_one (z : ℂ) (n : ℕ) (hn : 0 < n) (hz : z ^ n = 1) :
    ‖z‖ = 1 := by
  exact Complex.norm_eq_one_of_pow_eq_one hz (Nat.ne_of_gt hn)

/-- Finite order gives conjugation as inversion. The exponent is positive. -/
theorem conj_of_pow_eq_one (z : ℂ) (n : ℕ) (hn : 0 < n) (hz : z ^ n = 1) :
    (starRingEnd ℂ) z = z⁻¹ := by
  exact (Complex.inv_eq_conj (norm_of_pow_eq_one z n hn hz)).symm

/-- The norm of μ is 1, from μ^24 = 1. [RW26, p. 3]. -/
theorem etaMultiplier_norm (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    ‖etaMultiplier M‖ = 1 := by
  exact norm_of_pow_eq_one _ 24 (by norm_num) (etaMultiplier_pow_twentyFour M hM)

/-- Same sources, in the form needed by the actual μΦ product. -/
theorem etaMultiplier_conj (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    (starRingEnd ℂ) (etaMultiplier M) = (etaMultiplier M)⁻¹ := by
  exact conj_of_pow_eq_one _ 24 (by norm_num) (etaMultiplier_pow_twentyFour M hM)

/-- Multiplication form. The factor μ stays with Φ. -/
theorem etaMultiplier_conj_mul (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    (starRingEnd ℂ) (etaMultiplier M) * etaMultiplier M = 1 := by
  rw [etaMultiplier_conj M hM]
  exact inv_mul_cancel₀ (etaMultiplier_ne_zero M hM)

/-- Conjugation of the affine factor. [RW26, p. 3]. -/
theorem etaDenom_conj (M : SL(2, ℤ)) (z : ℂ) :
    (starRingEnd ℂ) (etaDenom M z) = etaDenom M ((starRingEnd ℂ) z) := by
  simp [etaDenom]

/-- Real matrix entries commute with conjugation. -/
theorem etaMobius_conj (M : SL(2, ℤ)) (z : ℂ) :
    (starRingEnd ℂ) (etaMobius M z) = etaMobius M ((starRingEnd ℂ) z) := by
  simp [etaMobius, etaDenom]

/-- The slit domain `etaPhaseDomain` is stable under conjugation. -/
theorem etaPhaseDomain_conj_iff (M : SL(2, ℤ)) (z : ℂ) :
    (starRingEnd ℂ) z ∈ etaPhaseDomain M ↔ z ∈ etaPhaseDomain M := by
  simp [etaPhaseDomain, ← etaDenom_conj, Complex.mem_slitPlane_iff]

/-- Conjugation of the principal square root on the slit plane. [RW26, p. 3].
The negative real cut is excluded. -/
theorem sqrt_conj_slit (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    (starRingEnd ℂ) (Complex.sqrt z) = Complex.sqrt ((starRingEnd ℂ) z) := by
  simpa only [Complex.sqrt, map_inv₀, Complex.conj_ofNat] using
    (Complex.conj_cpow z (2⁻¹ : ℂ) (Complex.slitPlane_arg_ne_pi hz)).symm

/-- Same sources: positive real automorphy factor selects the positive
real square root inside the slit plane. -/
theorem sqrt_etaDenom_real (M : SL(2, ℤ)) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) :
    Complex.sqrt (etaDenom M (τ : ℂ)) =
      (Real.sqrt ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) : ℂ) := by
  exact EtaMultiplierAux.sqrt_affine_real (M 1 0) (M 1 1) τ hT

/-- The phase at a real fixed point. [RW26, p. 3; Prop. 7, p. 14]. -/
theorem etaPhase_conj_real_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ : ℂ) = (τ : ℂ)) :
    (starRingEnd ℂ) (etaPhase M (τ : ℂ)) =
      etaMultiplier M * (Real.sqrt ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) : ℂ) := by
  rw [etaPhase_real_fixedPoint M τ hT hfix, map_mul, map_inv₀,
    etaMultiplier_conj M hM, inv_inv, Complex.conj_ofReal]

/-- The prescribed zero-class root is real.
[RW26, p. 2, (2); p. 3, (4)]; [RW-rec, Def. 1]. -/
theorem specialValue_sqrt_conj (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (starRingEnd ℂ) (Real.sqrt (specialValueEpsilon M) : ℂ) =
      (Real.sqrt (specialValueEpsilon M) : ℂ) := by
  exact Complex.conj_ofReal _

#print SICLean.L4.etaMultiplier
#check SICLean.L4.etaMultiplier_pow_twentyFour
#check SICLean.L4.etaPhase_real_fixedPoint
#check etaMultiplier_conj

end SICLean.L5.ConjugationPhase
