import SICLean.L5.ActualQuadraticField
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

set_option autoImplicit false

/-!
Elementary support for the fixed trace-minus-identity conjugation and for the real
embedding attached to a place constructed from a real ring hom.
-/

noncomputable section

namespace SICLean.L5.RayArithmeticPlacesAux

open NumberField ActualQuadraticFieldAux

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem trace_sub_involutive (hK : Module.finrank ℚ K = 2) :
    Function.Involutive (fun x : K => algebraMap ℚ K (Algebra.trace ℚ K x) - x) := by
  intro x
  simp only [map_sub, Algebra.trace_algebraMap, hK, two_smul, map_add]
  ring

theorem trace_sub_mul (hK : Module.finrank ℚ K = 2) (x y : K) :
    algebraMap ℚ K (Algebra.trace ℚ K (x * y)) - x * y =
      (algebraMap ℚ K (Algebra.trace ℚ K x) - x) *
        (algebraMap ℚ K (Algebra.trace ℚ K y) - y) := by
  obtain ⟨κ, hκ⟩ := quadratic_exists_nontrivial_aut hK
  have h (z : K) : algebraMap ℚ K (Algebra.trace ℚ K z) - z = κ z := by
    rw [quadratic_trace_eq_add hK κ hκ]
    abel
  rw [h, h, h, map_mul]

theorem trace_sub_add (x y : K) :
    algebraMap ℚ K (Algebra.trace ℚ K (x + y)) - (x + y) =
      (algebraMap ℚ K (Algebra.trace ℚ K x) - x) +
        (algebraMap ℚ K (Algebra.trace ℚ K y) - y) := by
  simp only [map_add]
  ring

theorem trace_sub_rat (hK : Module.finrank ℚ K = 2) (q : ℚ) :
    algebraMap ℚ K (Algebra.trace ℚ K (algebraMap ℚ K q)) - algebraMap ℚ K q =
      algebraMap ℚ K q := by
  simp only [Algebra.trace_algebraMap, hK, two_smul, map_add]
  abel

theorem trace_sub_ne_id (hK : Module.finrank ℚ K = 2) :
    (fun x : K => algebraMap ℚ K (Algebra.trace ℚ K x) - x) ≠ id := by
  obtain ⟨κ, hκ⟩ := quadratic_exists_nontrivial_aut hK
  intro h
  apply hκ
  ext x
  change κ x = x
  have hx := congrFun h x
  dsimp only [id_eq] at hx
  rw [quadratic_trace_eq_add hK κ hκ] at hx
  linear_combination hx

omit [Algebra ℚ K] in
theorem ofReal_comp_isReal (f : K →+* ℝ) :
    ComplexEmbedding.IsReal (Complex.ofRealHom.comp f) := by
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  simp

omit [Algebra ℚ K] in
theorem embedding_of_mk_ofReal (f : K →+* ℝ)
    (h : (InfinitePlace.mk (Complex.ofRealHom.comp f)).IsReal) :
    (InfinitePlace.mk (Complex.ofRealHom.comp f)).embedding_of_isReal h = f := by
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (ofReal_comp_isReal f)]
  rfl

open scoped MatrixGroups in
theorem sigma₁_ne_sigma₂ (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    ActualField.sigma₁ M hM ≠ ActualField.sigma₂ M hM := by
  intro h
  have heq := RingHom.congr_fun h (ActualField.epsilon M hM)
  rw [ActualField.sigma₂_epsilon] at heq
  have hgt := ActualField.epsilon_gt_one M hM
  have hinv : (ActualField.sigma₁ M hM (ActualField.epsilon M hM))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hgt
  linarith

end SICLean.L5.RayArithmeticPlacesAux
