import SICLean.L5.ActualValueBridge
import SICLean.L5.FiniteAlgebraicTransport
import SICLean.L5.PrimeValuation
import Mathlib.RingTheory.Valuation.Integral

set_option autoImplicit false

noncomputable section

namespace SICLean.L5.OddPrimeValuesAux

open L3
open scoped Classical MatrixGroups WithZero

/-- An integer integral element lies in every valuation ring. -/
theorem valuation_nonneg_of_isIntegral {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℝ)) {x : F} (hx : IsIntegral ℤ x) : 0 ≤ v x := by
  have hi : IsIntegral v.toValuation.integer x := hx.tower_top
  exact (Valuation.integer.integers v.toValuation).mem_of_integral hi

/-- Integrality of an element and its inverse forces valuation zero. -/
theorem valuation_zero_of_integral_unit {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℝ)) {x : F} (hx : x ≠ 0)
    (hi : IsIntegral ℤ x) (hiinv : IsIntegral ℤ x⁻¹) : v x = 0 := by
  apply le_antisymm _ (valuation_nonneg_of_isIntegral v hi)
  calc
    v x ≤ v x + v x⁻¹ := le_add_of_nonneg_right (valuation_nonneg_of_isIntegral v hiinv)
    _ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]

/-- The reciprocal quartic satisfied by the prescribed square root is monic. -/
theorem quartic_isIntegral {F : Type*} [Field F] (n : ℕ) (x : F)
    (hx : x ^ 4 - ((n : F) + 2) * x ^ 2 + 1 = 0) : IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ 4 -
    (Polynomial.C ((n : ℤ) + 2) * Polynomial.X ^ 2 - Polynomial.C 1), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    compute_degree!
  · change Polynomial.aeval x (Polynomial.X ^ 4 -
      (Polynomial.C ((n : ℤ) + 2) * Polynomial.X ^ 2 - Polynomial.C 1)) = 0
    simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X,
      map_add, map_natCast, map_ofNat, map_one]
    linear_combination hx

/-- Its constant coefficient is one, so its inverse is also integral. -/
theorem quartic_inv_isIntegral {F : Type*} [Field F] (n : ℕ) (x : F)
    (hx : x ^ 4 - ((n : F) + 2) * x ^ 2 + 1 = 0) : IsIntegral ℤ x⁻¹ := by
  have hi := quartic_isIntegral n x hx
  have hinv : x⁻¹ = ((n : F) + 2) * x - x ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination -hx
  rw [hinv]
  exact ((isIntegral_natCast (R := ℤ) n).add (isIntegral_natCast 2)).mul hi |>.sub (hi.pow 3)

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The existing presentation gives matrix labels for any actual pseudolattice. -/
def matrixEquiv (P : PeriodData K) (I : StablePseudolattice P) :
    PseudolatticeGroup P I ≃+ L4.SpecialValueGroup (M72.chosenBasis P I).matrix :=
  (pseudolatticeGroupEquiv P I _ (M72.chosenBasis_spec P I)).trans
    (M74.basisRowEquiv _ (M72.chosenBasis_spec P I).1).symm

/-- Equality of the same complex point values, including the origin. -/
theorem value_matrixEquiv (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) :
    M72.value P I x = L4.specialValuePlus (M72.chosenBasis P I).matrix
      (M74.basis_admissible _ (M72.chosenBasis_spec P I).1) (matrixEquiv P I x) := by
  rw [M72.value_eq_distribution P I _ (M72.chosenBasis_spec P I), M74.basisValue_eq_plus]
  rfl

/-- Negative logarithm of a nonarchimedean norm, with zero retained as top. -/
def logNormValue {F : Type*} [NormedField F] (c : ℝ) (x : F) : WithTop ℝ :=
  if x = 0 then ⊤ else ((-Real.log ‖x‖ / c : ℝ) : WithTop ℝ)

/-- The logarithmic construction is a genuine real additive valuation. -/
def logNormValuation {F : Type*} [NormedField F] [IsUltrametricDist F]
    (c : ℝ) (hc : 0 < c) : AddValuation F (WithTop ℝ) := by
  classical
  refine AddValuation.of (logNormValue c) (by simp [logNormValue])
    (by simp [logNormValue]) ?_ ?_
  · intro x y
    by_cases hxy : x + y = 0
    · simp [logNormValue, hxy]
    by_cases hx : x = 0
    · simp [hx, logNormValue]
    by_cases hy : y = 0
    · simp [hy, logNormValue]
    simp only [logNormValue, ite_eq_right hx, ite_eq_right hy, ite_eq_right hxy]
    rcases le_total ‖x‖ ‖y‖ with h | h
    · apply (min_le_right _ _).trans
      apply WithTop.coe_le_coe.mpr
      apply div_le_div_of_nonneg_right _ hc.le
      apply neg_le_neg
      apply Real.log_le_log (norm_pos_iff.mpr hxy)
      simpa only [max_eq_right h] using IsUltrametricDist.norm_add_le_max x y
    · apply (min_le_left _ _).trans
      apply WithTop.coe_le_coe.mpr
      apply div_le_div_of_nonneg_right _ hc.le
      apply neg_le_neg
      apply Real.log_le_log (norm_pos_iff.mpr hxy)
      simpa only [max_eq_left h] using IsUltrametricDist.norm_add_le_max x y
  · intro x y
    by_cases hx : x = 0
    · simp [hx, logNormValue]
    by_cases hy : y = 0
    · simp [hy, logNormValue]
    simp only [logNormValue, ite_eq_right hx, ite_eq_right hy, ite_eq_right (mul_ne_zero hx hy),
      norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy),
      neg_add, add_div, WithTop.coe_add]

theorem logNormValuation_apply {F : Type*} [NormedField F] [IsUltrametricDist F]
    (c : ℝ) (hc : 0 < c) (x : F) :
    logNormValuation c hc x = logNormValue c x := rfl

/-- The scale converting the ideal-norm absolute value to v(p)=1 is positive. -/
theorem normalization_pos {L : Type*} [Field L] [NumberField L]
    (Q : FinitePlace.Prime L) :
    0 < (FinitePlace.absoluteRamification Q : ℝ) * Real.log (Ideal.absNorm Q.asIdeal : ℝ) := by
  apply mul_pos
  · exact_mod_cast FinitePlace.absoluteRamification_pos Q
  · apply Real.log_pos
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm Q

/-- The logarithmic absolute value agrees exactly with the normalization. -/
theorem logNormValue_embedding {L : Type*} [Field L] [NumberField L]
    (Q : FinitePlace.Prime L) (a : L) :
    logNormValue ((FinitePlace.absoluteRamification Q : ℝ) *
      Real.log (Ideal.absNorm Q.asIdeal : ℝ)) (NumberField.FinitePlace.embedding Q a) =
      FinitePlace.valuation Q a := by
  by_cases ha : a = 0
  · simp [ha, logNormValue]
  have hmap : NumberField.FinitePlace.embedding Q a ≠ 0 :=
    (map_ne_zero (NumberField.FinitePlace.embedding Q)).mpr ha
  have hv : Q.valuation L a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hlog : Real.log (Ideal.absNorm Q.asIdeal : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm Q
  rw [logNormValue, ite_eq_right hmap, NumberField.FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow, NNReal.coe_natCast,
    Real.log_zpow, FinitePlace.valuation_apply, FinitePlace.valuationFun,
    FinitePlace.ord, ite_eq_right ha, WithTop.map_coe, Int.cast_neg]
  rw [← neg_mul, mul_div_mul_right _ _ hlog]

/-- Extend through an algebraic closure of the finite-place completion. The spectral norm supplies
the norm extension; no prime of Qbar is assumed. -/
theorem exists_valuation_extension {L : Type*} [Field L] [NumberField L]
    (Q : FinitePlace.Prime L) (ι : L →ₐ[ℚ] Galois.Qbar) :
    ∃ v : AddValuation Galois.Qbar (WithTop ℝ),
      v (FinitePlace.residueChar Q : Galois.Qbar) = 1 ∧
      ∀ a : L, v (ι a) = FinitePlace.valuation Q a := by
  let C := Q.adicCompletion L
  let E := AlgebraicClosure C
  let : NontriviallyNormedField C := Valued.toNontriviallyNormedField C ℤᵐ⁰
  let : NormedField E := spectralNorm.normedField C E
  let : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := C) (L := E))
  let : Algebra L Galois.Qbar := ι.toRingHom.toAlgebra
  let : IsScalarTower ℚ L Galois.Qbar := IsScalarTower.of_algHom ι
  let : Algebra.IsAlgebraic L Galois.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let j : Galois.Qbar →ₐ[L] E := IsAlgClosed.lift
  let c := (FinitePlace.absoluteRamification Q : ℝ) * Real.log (Ideal.absNorm Q.asIdeal : ℝ)
  let v : AddValuation Galois.Qbar (WithTop ℝ) :=
    AddValuation.comap j.toRingHom (logNormValuation c (normalization_pos Q))
  have hj (a : L) : j (ι a) = algebraMap C E (NumberField.FinitePlace.embedding Q a) := by
    calc
      j (ι a) = algebraMap L E a := j.commutes a
      _ = _ := by rw [IsScalarTower.algebraMap_apply L C E]; rfl
  have hn (a : L) : ‖j (ι a)‖ = ‖NumberField.FinitePlace.embedding Q a‖ := by
    change spectralNorm C E (j (ι a)) = _
    rw [hj a, spectralNorm_extends]
  have hrestrict (a : L) : v (ι a) = FinitePlace.valuation Q a := by
    change logNormValue c (j (ι a)) = _
    have heq : j (ι a) = 0 ↔ NumberField.FinitePlace.embedding Q a = 0 := by
      rw [map_eq_zero, map_eq_zero, map_eq_zero]
    unfold logNormValue
    rw [heq, hn a]
    exact logNormValue_embedding Q a
  refine ⟨v, ?_, hrestrict⟩
  simpa only [map_natCast] using
    (hrestrict (FinitePlace.residueChar Q : L)).trans (FinitePlace.valuation_residueChar Q)

end SICLean.L5.OddPrimeValuesAux
