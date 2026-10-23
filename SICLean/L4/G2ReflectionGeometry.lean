import SICLean.L4.G2RepellingGeometry
import SICLean.L4.SpecialValueReflection
import SICLean.L4.G2ReflectionGeometryAux

set_option autoImplicit false

/-!
# The explicit inverse-reflection row equivalence

The matrix is the existing `modularInverseReflection`, namely δM⁻¹δ with δ=diag(1,-1). The row map
has a concrete body; the quotient equivalence is induced by that map. No analytic value or desired
identity is chosen here. The repelling branch is the one already defined. Only it has 1-ε>0.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2.ReflectionGeometry

/-- [RW26, (3), p. 3]. The literal row action by δ, including its literal inverse. -/
def rowReflection : (ℤ × ℤ) ≃+ (ℤ × ℤ) where
  toFun x := (x.1, -x.2)
  invFun x := (x.1, -x.2)
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp
  map_add' := by intro x y; ext <;> simp [add_comm]

/-- [RW26, §2.2, p. 6] supplies the inverse-reflection context. -/
theorem reflection_involutive (M : SL(2, ℤ)) :
    modularInverseReflection (modularInverseReflection M) = M := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- [RW26] fixed-point scope, p.2. -/
theorem reflection_admissible (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    SpecialValueAdmissible (modularInverseReflection M) := by
  simpa [SpecialValueAdmissible, modularInverseReflection,
    modularInverseReflectionMatrix, add_comm] using hM

/-- [RW26, p. 2, p. 3]. The integer N, hence the sum normalization, is unchanged. -/
theorem reflection_order (M : SL(2, ℤ)) :
    specialValueOrder (modularInverseReflection M) = specialValueOrder M := by
  simp [specialValueOrder, modularInverseReflection, modularInverseReflectionMatrix, add_comm]

/-- Uses the fixed-point quadratic of [RW26, p. 2]. -/
theorem reflection_tau (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    specialValueTau (modularInverseReflection M) = -repellingTau M := by
  change ((M 1 1 : ℝ) - (M 0 0 : ℝ) +
      Real.sqrt (((M 1 1 : ℝ) + (M 0 0 : ℝ)) ^ 2 - 4)) /
      (2 * (M 1 0 : ℝ)) =
    -(((M 0 0 : ℝ) - (M 1 1 : ℝ) -
      Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)) /
      (2 * (M 1 0 : ℝ)))
  rw [add_comm (M 1 1 : ℝ) (M 0 0 : ℝ)]
  ring

/-- [RW26, p. 2]. The target of a repelling source is the attracting branch. -/
theorem reflection_epsilon (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    specialValueEpsilon (modularInverseReflection M) = (epsilon M)⁻¹ := by
  have hsum : specialValueEpsilon (modularInverseReflection M) + epsilon M =
      (specialValueOrder M : ℝ) + 2 := by
    rw [specialValueEpsilon_formula _ (reflection_admissible M hM),
      reflection_order, epsilon_formula M hM]
    ring
  apply (mul_right_cancel₀ (ne_of_gt (epsilon_pos M hM)))
  rw [inv_mul_cancel₀ (ne_of_gt (epsilon_pos M hM))]
  rw [show specialValueEpsilon (modularInverseReflection M) =
    (specialValueOrder M : ℝ) + 2 - epsilon M by linarith only [hsum]]
  nlinarith only [epsilon_characteristic M hM]

/-- An attracting source gives a repelling transformed matrix. [RW26, p. 2]. -/
theorem reflection_repelling_parameters (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) :
    repellingTau (modularInverseReflection M) = -specialValueTau M ∧
      epsilon (modularInverseReflection M) = (specialValueEpsilon M)⁻¹ := by
  constructor
  · have h := congrArg (fun t : ℝ => -t)
      (reflection_tau (modularInverseReflection M) (reflection_admissible M hM))
    simpa only [reflection_involutive, neg_neg] using h.symm
  · have h := congrArg (fun t : ℝ => t⁻¹)
      (reflection_epsilon (modularInverseReflection M) (reflection_admissible M hM))
    simpa only [reflection_involutive, inv_inv] using h.symm

/-- Both roots are positive real roots, cast into ℂ after taking the root. [RW26, (4), p. 3]. -/
theorem reflection_sqrt (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (Real.sqrt (specialValueEpsilon (modularInverseReflection M)) : ℂ) =
      (Real.sqrt (epsilon M) : ℂ)⁻¹ := by
  rw [reflection_epsilon M hM, Real.sqrt_inv, Complex.ofReal_inv]

/-- Both actual slit domains, with their positive denominators. Reuses
`modularInverseReflection_domain`, not a negative-c definition of Φ. [RW26, p. 2, p. 6]. -/
theorem reflection_domains (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (repellingTau M : ℂ) ∈ modularPhiDomain M ∧
      -(repellingTau M : ℂ) ∈ modularPhiDomain (modularInverseReflection M) ∧
      etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) ∧
      etaDenom (modularInverseReflection M) (-(repellingTau M : ℂ)) =
        (epsilon M : ℂ)⁻¹ := by
  have hden : etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
    simp [etaDenom, epsilon, g1T, Complex.ofReal_add, Complex.ofReal_mul]
  have hdom : (repellingTau M : ℂ) ∈ modularPhiDomain M := by
    change etaDenom M (repellingTau M : ℂ) ∈ Complex.slitPlane
    rw [hden]
    exact Complex.ofReal_mem_slitPlane.mpr (epsilon_pos M hM)
  have hR := modularInverseReflection_domain M hM.1 (repellingTau M : ℂ) hdom
  rw [repellingTau_fixedPoint M hM, hden] at hR
  exact ⟨hdom, hR.2.2.1, hden, hR.2.1⟩

/-- [RW26, (3), p. 3, Lemma 2, p. 12] supplies the inverse-lattice algebra; equality of the two row
ranges uses invertibility. This algebraic equality needs no hyperbolicity hypothesis. -/
theorem rowReflection_lattice (M : SL(2, ℤ)) :
    (specialValueLattice M).map rowReflection.toAddMonoidHom =
      specialValueLattice (modularInverseReflection M) := by
  exact G2ReflectionGeometryAux.rowReflection_lattice M

/-- The quotient map is explicitly induced by x↦(x₁,-x₂), not chosen by cardinality. [RW26, (3), p.
3]. -/
def reflectionEquiv (M : SL(2, ℤ)) :
    SpecialValueGroup M ≃+ SpecialValueGroup (modularInverseReflection M) :=
  QuotientAddGroup.congr (specialValueLattice M)
    (specialValueLattice (modularInverseReflection M)) rowReflection (rowReflection_lattice M)

/-- Representative-level computation for the concrete quotient map. [RW26, (3), p. 3]. -/
theorem reflectionEquiv_mk (M : SL(2, ℤ)) (x : ℤ × ℤ) :
    reflectionEquiv M (specialValueMk M x) =
      specialValueMk (modularInverseReflection M) (x.1, -x.2) := by
  rfl

/-- Exact Gaussian transport, including the parity factor. [RW26, (3), p. 3]. -/
theorem reflection_gaussian (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    specialValueGaussian (modularInverseReflection M) (reflection_admissible M hM)
      (reflectionEquiv M x) = specialValueGaussian M hM x := by
  refine Quotient.inductionOn x ?_
  intro u
  change specialValueGaussian (modularInverseReflection M) (reflection_admissible M hM)
    (reflectionEquiv M (specialValueMk M u)) =
      specialValueGaussian M hM (specialValueMk M u)
  rw [reflectionEquiv_mk, specialValueGaussian_mk, specialValueGaussian_mk]
  exact G2ReflectionGeometryAux.gaussianLift_reflection M u

/-- Equality is of characters; their displayed rational exponents can differ by an integer. [RW26,
(3), p. 3]. -/
theorem reflection_pairing (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x u : SpecialValueGroup M) :
    specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
      (reflectionEquiv M x) (reflectionEquiv M u) = specialValuePairing M hM x u := by
  refine Quotient.inductionOn₂ x u ?_
  intro v w
  change specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
    (reflectionEquiv M (specialValueMk M v)) (reflectionEquiv M (specialValueMk M w)) =
      specialValuePairing M hM (specialValueMk M v) (specialValueMk M w)
  rw [reflectionEquiv_mk, reflectionEquiv_mk,
    specialValuePairing_mk, specialValuePairing_mk]
  exact G2ReflectionGeometryAux.pairingLift_reflection M v w

#check @QuotientAddGroup.congr
#check @modularInverseReflection_domain
#check @etaMultiplier_inverse_reflection
#check @modularPhi_inverse_reflection_fixedPoint
#print rowReflection
#print reflectionEquiv
#check reflection_repelling_parameters
#check reflection_pairing

end SICLean.L4.G2.ReflectionGeometry
