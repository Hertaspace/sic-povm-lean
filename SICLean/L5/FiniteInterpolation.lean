import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import SICLean.L5.FiniteInterpolationAux

/-!
# Finite interpolation for Lemma 1

These are the finite polynomial consequences of the coset-moment congruences
in [RW-rec, Lemma 1]. The coefficient field may be any field of characteristic `p`;
it need not be the prime field, and it need not be finite.
The one-variable moment cutoff uses `2 * r < p - 1`, so the same cutoff applies at `p = 2`.
-/

set_option autoImplicit false

noncomputable section

namespace SICLean.L5.FiniteInterpolation

open Polynomial
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p]

/-- The canonical embedding of the prime field into the coefficient field. -/
def primeField : ZMod p →+* k :=
  ZMod.castHom (dvd_refl p) k

/-- The concrete Lagrange polynomial on all prime-field points. -/
def interpolant (f : ZMod p → k) : k[X] :=
  Lagrange.interpolate Finset.univ (primeField p k) f

/-- A one-variable monomial moment, with the prime-field points viewed in `k`. -/
def moment (f : ZMod p → k) (r : ℕ) : k :=
  ∑ t : ZMod p, (primeField p k t) ^ r * f t

/-- The one-variable instance of the strict degree cutoff in [RW-rec, (14)]. -/
def HasVanishingLowMoments (f : ZMod p → k) : Prop :=
  ∀ r : ℕ, 2 * r < p - 1 → moment p k f r = 0

/-- The function obtained from two factors on the chosen two-dimensional coset. -/
def separableFunction (f g : ZMod p → k) : ZMod p × ZMod p → k :=
  fun u => f u.1 * g u.2

/-- A two-variable monomial moment. -/
def planeMoment (F : ZMod p × ZMod p → k) (a b : ℕ) : k :=
  ∑ u : ZMod p × ZMod p,
    (primeField p k u.1) ^ a * (primeField p k u.2) ^ b * F u

/-- The two-variable instance of the strict total-degree cutoff in [RW-rec, (14)]. -/
def HasVanishingPlaneMoments (F : ZMod p × ZMod p → k) : Prop :=
  ∀ a b : ℕ, a + b < p - 1 → planeMoment p k F a b = 0

/-- Helper for [RW-rec, Lemma 1]: the interpolation nodes remain distinct in any
coefficient field of characteristic `p`. -/
theorem primeField_injective : Function.Injective (primeField p k) := by
  exact ZMod.castHom_injective k

/-- [RW-rec, Lemma 1]: the specified Lagrange polynomial represents every
function on the prime field, with values allowed in the larger field `k`. -/
theorem eval_interpolant (f : ZMod p → k) (t : ZMod p) :
    (interpolant p k f).eval (primeField p k t) = f t := by
  classical
  exact Lagrange.eval_interpolate_at_node f
    (primeField_injective p k).injOn (Finset.mem_univ t)

/-- [RW-rec, Lemma 1]: the representing polynomial has natural degree at most
`p - 1`, including the zero function. -/
theorem natDegree_interpolant_le (f : ZMod p → k) :
    (interpolant p k f).natDegree ≤ p - 1 := by
  classical
  apply natDegree_le_of_degree_le
  simpa only [interpolant, Finset.card_univ, ZMod.card] using
    Lagrange.degree_interpolate_le (s := Finset.univ) f
      (primeField_injective p k).injOn

/-- Helper for [RW-rec, Lemma 1]: a polynomial of degree at most
`p - 1` is determined by its values on the `p` prime-field points. -/
theorem eq_interpolant_of_natDegree_le (A : k[X])
    (hA : A.natDegree ≤ p - 1) :
    A = interpolant p k (fun t => A.eval (primeField p k t)) := by
  classical
  apply Lagrange.eq_interpolate (primeField_injective p k).injOn
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply lt_of_le_of_lt (degree_le_natDegree : A.degree ≤ _)
  simpa only [Finset.card_univ, ZMod.card, Nat.cast_lt] using
    (show A.natDegree < p by omega)

/-- Helper for the leading-coefficient test in [RW-rec, Lemma 1]: exponent zero
has sum `p = 0` in `k`, rather than the value `-1` for positive multiples of
`p - 1`. -/
theorem sum_primeField_pow_zero :
    (∑ t : ZMod p, (primeField p k t) ^ (0 : ℕ)) = 0 := by
  simp only [pow_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_one]
  exact CharP.cast_eq_zero k p

/-- Helper for [RW-rec, Lemma 1]: all prime-field power sums, with the
exponent-zero case separated explicitly. -/
theorem sum_primeField_pow (n : ℕ) :
    (∑ t : ZMod p, (primeField p k t) ^ n) =
      if n = 0 then 0 else if p - 1 ∣ n then -1 else 0 := by
  exact FiniteInterpolationAux.sum_primeField_pow p k n

/-- [RW-rec, Lemma 1]: the test monomial extracts the negative leading
coefficient. The nonzero and degree hypotheses are both explicit. -/
theorem leadingCoeff_moment (A : k[X]) (hA : A ≠ 0)
    (hdegree : A.natDegree ≤ p - 1) :
    (∑ t : ZMod p,
      (primeField p k t) ^ (p - 1 - A.natDegree) *
        A.eval (primeField p k t)) = -A.leadingCoeff := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  calc
    _ = ∑ i ∈ Finset.range (A.natDegree + 1),
        A.coeff i * ∑ t : ZMod p,
          (primeField p k t) ^ (p - 1 - A.natDegree + i) := by
      simp_rw [eval_eq_sum_range, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro t ht
      rw [pow_add]
      ring
    _ = -A.leadingCoeff := by
      rw [Finset.sum_eq_single A.natDegree]
      · rw [Nat.sub_add_cancel hdegree, sum_primeField_pow]
        simp only [show p - 1 ≠ 0 by omega, ↓reduceIte, dvd_refl,
          mul_neg, mul_one, coeff_natDegree]
      · intro i hi hne
        have hi' : i < A.natDegree := by
          have := Finset.mem_range.mp hi
          omega
        have hlt : p - 1 - A.natDegree + i < p - 1 := by omega
        rw [sum_primeField_pow]
        split_ifs with hz hdiv
        · exact mul_zero _
        · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hdiv
          omega
        · exact mul_zero _
      · simp

/-- [RW-rec, Lemma 1]: vanishing below the half-degree cutoff forces the
interpolation polynomial to have degree at most `(p - 1) / 2`. -/
theorem natDegree_interpolant_le_half_of_lowMoments (f : ZMod p → k)
    (hmoments : HasVanishingLowMoments p k f) :
    (interpolant p k f).natDegree ≤ (p - 1) / 2 := by
  by_cases hzero : interpolant p k f = 0
  · simp [hzero]
  by_contra hlarge
  have hdegree := natDegree_interpolant_le p k f
  have hcut : 2 * (p - 1 - (interpolant p k f).natDegree) < p - 1 := by omega
  have hmoment := hmoments (p - 1 - (interpolant p k f).natDegree) hcut
  have hleading := leadingCoeff_moment p k (interpolant p k f) hzero hdegree
  simp_rw [eval_interpolant] at hleading
  have : -(interpolant p k f).leadingCoeff = 0 := hleading.symm.trans hmoment
  exact (leadingCoeff_ne_zero.mpr hzero) (neg_eq_zero.mp this)

/-- [RW-rec, Lemma 1(i)]: either the function is
identically zero or its support contains strictly more than half the points.
The doubled cardinality expresses the strict inequality without rounding. -/
theorem eq_zero_or_support_large_of_lowMoments (f : ZMod p → k)
    (hmoments : HasVanishingLowMoments p k f) :
    f = 0 ∨ p < 2 * Nat.card {t : ZMod p // f t ≠ 0} := by
  classical
  by_cases hf : f = 0
  · exact Or.inl hf
  right
  have hA : interpolant p k f ≠ 0 := by
    intro hzero
    apply hf
    funext t
    simpa only [hzero, eval_zero, Pi.zero_apply] using (eval_interpolant p k f t).symm
  have hroots : Fintype.card {t : ZMod p // f t = 0} ≤
      (interpolant p k f).natDegree := by
    by_contra hcard
    apply hA
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (interpolant p k f)
      (f := fun t : {t : ZMod p // f t = 0} => primeField p k t.val)
      ((primeField_injective p k).comp Subtype.val_injective)
    · intro t
      simpa only [Function.comp_apply, eval_interpolant] using t.property
    · omega
  have hdegree := natDegree_interpolant_le_half_of_lowMoments p k f hmoments
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card]
  omega

/-- [RW-rec, Lemma 1]: two polynomial representatives of reciprocal functions
have degree sum at least `p` if the first representative is nonconstant.
Individual degree bounds are unnecessary for this lower bound. -/
theorem reciprocal_natDegree_add_ge (A B : k[X])
    (hreciprocal : ∀ t : ZMod p,
      A.eval (primeField p k t) * B.eval (primeField p k t) = 1)
    (hnonconstant : 0 < A.natDegree) :
    p ≤ A.natDegree + B.natDegree := by
  classical
  by_contra hsmall
  have hA : A ≠ 0 := by
    intro hz
    have := hreciprocal 0
    simp [hz] at this
  have hB : B ≠ 0 := by
    intro hz
    have := hreciprocal 0
    simp [hz] at this
  have hprod : A * B - 1 = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (A * B - 1)
      (primeField_injective p k)
    · intro t
      simp only [eval_sub, eval_mul, eval_one, hreciprocal t, sub_self]
    · rw [ZMod.card]
      calc
        _ ≤ max (A * B).natDegree (1 : k[X]).natDegree := natDegree_sub_le _ _
        _ = A.natDegree + B.natDegree := by rw [natDegree_mul hA hB]; simp
        _ < p := by omega
  have hdegree := congrArg Polynomial.natDegree (sub_eq_zero.mp hprod)
  rw [natDegree_mul hA hB, natDegree_one] at hdegree
  omega

/-- [RW-rec, Lemma 1(ii)]: simultaneous low
moments for a nowhere-zero function and its pointwise inverse force constancy. -/
theorem eq_const_of_lowMoments_and_reciprocal (f : ZMod p → k)
    (hnonzero : ∀ t : ZMod p, f t ≠ 0)
    (hmoments : HasVanishingLowMoments p k f)
    (hinverse : HasVanishingLowMoments p k (fun t => (f t)⁻¹)) :
    ∃ c : k, c ≠ 0 ∧ ∀ t : ZMod p, f t = c := by
  have hdegree : (interpolant p k f).natDegree = 0 := by
    by_contra hpos
    have hreciprocal := reciprocal_natDegree_add_ge p k (interpolant p k f)
      (interpolant p k (fun t => (f t)⁻¹))
      (by intro t; simp only [eval_interpolant, mul_inv_cancel₀ (hnonzero t)])
      (Nat.pos_of_ne_zero hpos)
    have hf := natDegree_interpolant_le_half_of_lowMoments p k f hmoments
    have hi := natDegree_interpolant_le_half_of_lowMoments p k
      (fun t => (f t)⁻¹) hinverse
    have hp : 0 < p := (Fact.out : p.Prime).pos
    omega
  have hconstant (t : ZMod p) : f t = (interpolant p k f).coeff 0 := by
    rw [← eval_interpolant p k f t]
    simpa only [eval_C] using congrArg (Polynomial.eval (primeField p k t))
      (eq_C_of_natDegree_eq_zero hdegree)
  refine ⟨(interpolant p k f).coeff 0, ?_, hconstant⟩
  rw [← hconstant 0]
  exact hnonzero 0

/-- Helper for [RW-rec, Lemma 1]: a separable two-variable monomial moment
factors as the product of the corresponding one-variable moments. -/
theorem planeMoment_separableFunction (f g : ZMod p → k) (a b : ℕ) :
    planeMoment p k (separableFunction p k f g) a b =
      moment p k f a * moment p k g b := by
  classical
  simp only [planeMoment, separableFunction, Fintype.sum_prod_type, moment]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- [RW-rec, Lemma 1]: nonzero factors with vanishing product moments have
interpolation degrees whose sum is at most `p - 1`. -/
theorem natDegree_add_le_of_separable_lowMoments (f g : ZMod p → k)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hmoments : HasVanishingPlaneMoments p k (separableFunction p k f g)) :
    (interpolant p k f).natDegree + (interpolant p k g).natDegree ≤ p - 1 := by
  have hA : interpolant p k f ≠ 0 := by
    intro hzero
    apply hf
    funext t
    simpa only [hzero, eval_zero, Pi.zero_apply] using (eval_interpolant p k f t).symm
  have hB : interpolant p k g ≠ 0 := by
    intro hzero
    apply hg
    funext t
    simpa only [hzero, eval_zero, Pi.zero_apply] using (eval_interpolant p k g t).symm
  by_contra hlarge
  have hAf := natDegree_interpolant_le p k f
  have hBg := natDegree_interpolant_le p k g
  have hcut : (p - 1 - (interpolant p k f).natDegree) +
      (p - 1 - (interpolant p k g).natDegree) < p - 1 := by omega
  have hmoment := hmoments _ _ hcut
  rw [planeMoment_separableFunction] at hmoment
  have hleft : moment p k f (p - 1 - (interpolant p k f).natDegree) =
      -(interpolant p k f).leadingCoeff := by
    simpa only [moment, eval_interpolant] using
      leadingCoeff_moment p k (interpolant p k f) hA hAf
  have hright : moment p k g (p - 1 - (interpolant p k g).natDegree) =
      -(interpolant p k g).leadingCoeff := by
    simpa only [moment, eval_interpolant] using
      leadingCoeff_moment p k (interpolant p k g) hB hBg
  rw [hleft, hright] at hmoment
  exact (mul_ne_zero (neg_ne_zero.mpr (leadingCoeff_ne_zero.mpr hA))
    (neg_ne_zero.mpr (leadingCoeff_ne_zero.mpr hB))) hmoment

/-- [RW-rec, Lemma 1(iii)]: low product
moments and reciprocal product moments force at least one factor to be
constant, over an arbitrary characteristic-`p` coefficient field. -/
theorem one_factor_constant_of_separable_lowMoments (f g : ZMod p → k)
    (hf : ∀ t : ZMod p, f t ≠ 0) (hg : ∀ t : ZMod p, g t ≠ 0)
    (hmoments : HasVanishingPlaneMoments p k (separableFunction p k f g))
    (hinverse : HasVanishingPlaneMoments p k
      (fun u => (separableFunction p k f g u)⁻¹)) :
    (∃ c : k, c ≠ 0 ∧ ∀ t : ZMod p, f t = c) ∨
      (∃ c : k, c ≠ 0 ∧ ∀ t : ZMod p, g t = c) := by
  have hconst (u : ZMod p → k) (hu : ∀ t, u t ≠ 0)
      (hdegree : (interpolant p k u).natDegree = 0) :
      ∃ c : k, c ≠ 0 ∧ ∀ t : ZMod p, u t = c := by
    have hvalue (t : ZMod p) : u t = (interpolant p k u).coeff 0 := by
      rw [← eval_interpolant p k u t]
      simpa only [eval_C] using congrArg (Polynomial.eval (primeField p k t))
        (eq_C_of_natDegree_eq_zero hdegree)
    refine ⟨(interpolant p k u).coeff 0, ?_, hvalue⟩
    rw [← hvalue 0]
    exact hu 0
  by_cases hdf : (interpolant p k f).natDegree = 0
  · exact Or.inl (hconst f hf hdf)
  by_cases hdg : (interpolant p k g).natDegree = 0
  · exact Or.inr (hconst g hg hdg)
  exfalso
  have hfn : f ≠ 0 := by
    intro hzero
    exact hf 0 (congrFun hzero 0)
  have hgn : g ≠ 0 := by
    intro hzero
    exact hg 0 (congrFun hzero 0)
  have hfin : (fun t => (f t)⁻¹) ≠ 0 := by
    intro hzero
    exact inv_ne_zero (hf 0) (congrFun hzero 0)
  have hgin : (fun t => (g t)⁻¹) ≠ 0 := by
    intro hzero
    exact inv_ne_zero (hg 0) (congrFun hzero 0)
  have hinv : HasVanishingPlaneMoments p k
      (separableFunction p k (fun t => (f t)⁻¹) (fun t => (g t)⁻¹)) := by
    change HasVanishingPlaneMoments p k (fun u => (f u.1)⁻¹ * (g u.2)⁻¹)
    simpa only [separableFunction, mul_inv] using hinverse
  have hsum := natDegree_add_le_of_separable_lowMoments p k f g hfn hgn hmoments
  have hisum := natDegree_add_le_of_separable_lowMoments p k
    (fun t => (f t)⁻¹) (fun t => (g t)⁻¹) hfin hgin hinv
  have hrecf := reciprocal_natDegree_add_ge p k (interpolant p k f)
    (interpolant p k (fun t => (f t)⁻¹))
    (by intro t; simp only [eval_interpolant, mul_inv_cancel₀ (hf t)])
    (Nat.pos_of_ne_zero hdf)
  have hrecg := reciprocal_natDegree_add_ge p k (interpolant p k g)
    (interpolant p k (fun t => (g t)⁻¹))
    (by intro t; simp only [eval_interpolant, mul_inv_cancel₀ (hg t)])
    (Nat.pos_of_ne_zero hdg)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  omega

/-- Helper packaging [RW-rec, Lemma 1] for a single chosen coset: only this
function's displayed factorization is required; no global separability
hypothesis on other cosets is imposed. -/
theorem one_factor_constant_of_factorization (F : ZMod p × ZMod p → k)
    (f g : ZMod p → k)
    (hfactor : ∀ u : ZMod p × ZMod p, F u = f u.1 * g u.2)
    (hnonzero : ∀ u : ZMod p × ZMod p, F u ≠ 0)
    (hmoments : HasVanishingPlaneMoments p k F)
    (hinverse : HasVanishingPlaneMoments p k (fun u => (F u)⁻¹)) :
    (∃ c : k, c ≠ 0 ∧ ∀ t : ZMod p, f t = c) ∨
      (∃ c : k, c ≠ 0 ∧ ∀ t : ZMod p, g t = c) := by
  have hF : F = separableFunction p k f g := funext hfactor
  rw [hF] at hnonzero hmoments hinverse
  apply one_factor_constant_of_separable_lowMoments p k f g ?_ ?_ hmoments hinverse
  · intro t ht
    exact hnonzero (t, 0) (by simp [separableFunction, ht])
  · intro t ht
    exact hnonzero (0, t) (by simp [separableFunction, ht])

end SICLean.L5.FiniteInterpolation
