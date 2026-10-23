import SICLean.L3.Pseudolattice
import SICLean.L3.PeriodDataExistenceAux

set_option autoImplicit false

/-!
# Every positive order is realized by period data

Algebraicity is stated for an arbitrary `P : PeriodData K` whose `P.N` equals
the group order. This file supplies one such `P` for every `N > 0`. The field
is ℚ[X]/(X² − (N+2)X + 1). Its discriminant N(N+4) lies strictly between
(N+1)² and (N+2)², so the polynomial has no rational root. The two real roots
((N+2) ± √(N(N+4)))/2 give the two real embeddings, and their product is 1.

The period satisfies ε² − (N+2)ε + 1 = 0, with ε > 1 and conjugate 1/ε.
See also [RW26, p. 2, (2)].
-/

noncomputable section

namespace SICLean.L3.PeriodDataExistence

set_option backward.isDefEq.respectTransparency false in
/-- The existence statement used by the final assembly. The field is a
conclusion, so no number field or embedding is assumed. -/
theorem exists_periodData (N : ℕ) (hN : 0 < N) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (P : PeriodData K), P.N = N := by
  let f := PeriodDataExistenceAux.periodPolynomial N
  let : Fact (Irreducible f) :=
    ⟨PeriodDataExistenceAux.periodPolynomial_irreducible N hN⟩
  let K := AdjoinRoot f
  let : Module.Finite ℚ K :=
    (PeriodDataExistenceAux.periodPolynomial_monic N).finite_adjoinRoot
  let : NumberField K := NumberField.of_module_finite ℚ K
  refine ⟨K, inferInstance, inferInstance, {
    sigma₁ := AdjoinRoot.lift (algebraMap ℚ ℝ)
      (PeriodDataExistenceAux.epsilonPlus N)
      (PeriodDataExistenceAux.epsilonPlus_isRoot N)
    sigma₂ := AdjoinRoot.lift (algebraMap ℚ ℝ)
      (PeriodDataExistenceAux.epsilonMinus N)
      (PeriodDataExistenceAux.epsilonMinus_isRoot N)
    finrank_eq_two := ?_
    epsilon := AdjoinRoot.root f
    N := N
    N_pos := hN
    epsilon_polynomial := ?_
    epsilon_gt_one := ?_
    epsilon_conj := ?_ }, rfl⟩
  · calc Module.finrank ℚ K = f.natDegree :=
        (AdjoinRoot.powerBasis
          (PeriodDataExistenceAux.periodPolynomial_monic N).ne_zero).finrank
      _ = 2 := PeriodDataExistenceAux.periodPolynomial_natDegree N
  · have h : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    change Polynomial.aeval (AdjoinRoot.root f)
      (Polynomial.X ^ 2 - Polynomial.C ((N : ℚ) + 2) * Polynomial.X + 1) = 0 at h
    simpa only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, map_one, map_natCast, map_ofNat] using h
  · rw [AdjoinRoot.lift_root]
    exact PeriodDataExistenceAux.epsilonPlus_gt_one N hN
  · rw [AdjoinRoot.lift_root, AdjoinRoot.lift_root]
    exact PeriodDataExistenceAux.epsilonMinus_eq_inv N

end SICLean.L3.PeriodDataExistence
