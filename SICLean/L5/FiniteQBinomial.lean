import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Data.Nat.Choose.Basic
import SICLean.L5.FiniteQBinomialAux

set_option autoImplicit false

/-!
# Finite q-binomial polynomials for the local Fourier argument

Finite algebra from [RW-rec, Lemma 1]. The coefficients are defined in `ℤ[X]`
by the q-Pascal recursion, and then specialized in a commutative ring, so an
integral element is not introduced as a quotient. The finite Pochhammer symbol
is `(t;q)_j = ∏ r < j, (1 - q^r t)`: in particular `(q;q)_j` runs through the
powers `1, ..., j`. The recurrence uses `q^j` at positive column `j`, as in
[RW-rec, Lemma 1]. The quotient comparison uses the numerator `(q^i;q⁻¹)_j`.

There are no valuation, residue-field, or Fourier-integrality assumptions here.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.FiniteQBinomial

/-- Integral q-binomial polynomial, defined by the q-Pascal recursion of
[RW-rec, Lemma 1], with the usual boundary values. -/
def qBinomialPoly : ℕ → ℕ → Polynomial ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | i + 1, j + 1 =>
      qBinomialPoly i j + Polynomial.X ^ (j + 1) * qBinomialPoly i (j + 1)

/-- Specialization of the integral q-binomial polynomial at a ring element. -/
def qBinomial {R : Type*} [CommRing R] (q : R) (i j : ℕ) : R :=
  (qBinomialPoly i j).eval₂ (Int.castRingHom R) q

/-- The finite Pochhammer symbol `(t;q)_j` of [RW-rec, Lemma 1]. -/
def finitePochhammer {R : Type*} [CommRing R] (t q : R) (j : ℕ) : R :=
  ∏ r ∈ Finset.range j, (1 - q ^ r * t)

/-- The polynomial in `X` whose value at `t` is `(t;q)_j`.
This is the single-coordinate factor expanded in [RW-rec, Lemma 1]. -/
def finitePochhammerPoly {R : Type*} [CommRing R] (q : R) (j : ℕ) :
    Polynomial R :=
  ∏ r ∈ Finset.range j, (1 - Polynomial.C (q ^ r) * Polynomial.X)

/-- Explicit coefficient in the finite q-binomial expansion of `(X;q)_j`.
For the expansion use the base `q⁻¹`; see [RW-rec, Lemma 1]. -/
def finitePochhammerCoeff {R : Type*} [CommRing R] (q : R) (j a : ℕ) : R :=
  (-1 : R) ^ a * q ^ (a.choose 2) * qBinomial q j a

/-- Algebraic boundary helper for the q-Pascal recursion in [RW-rec, Lemma 1]. -/
theorem qBinomialPoly_zero_right (i : ℕ) : qBinomialPoly i 0 = 1 := by
  cases i <;> rfl

/-- The q-Pascal identity in [RW-rec, Lemma 1].
The positive-column condition avoids interpreting `j - 1` as a negative index. -/
theorem qBinomialPoly_pascal (i j : ℕ) (hj : 0 < j) :
    qBinomialPoly (i + 1) j =
      qBinomialPoly i (j - 1) + Polynomial.X ^ j * qBinomialPoly i j := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rfl

/-- Polynomial form of the off-diagonal vanishing in [RW-rec, Lemma 1]. -/
theorem qBinomialPoly_eq_zero_of_lt (i j : ℕ) (hij : i < j) :
    qBinomialPoly i j = 0 := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero => omega
      | succ j => rfl
  | succ i ih =>
      cases j with
      | zero => omega
      | succ j =>
          simp only [qBinomialPoly, ih j (by omega), ih (j + 1) (by omega),
            mul_zero, add_zero]

/-- Algebraic diagonal helper for the recursion and vanishing in [RW-rec, Lemma 1]. -/
theorem qBinomialPoly_self (i : ℕ) : qBinomialPoly i i = 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [qBinomialPoly, ih, qBinomialPoly_eq_zero_of_lt i (i + 1)
        (Nat.lt_succ_self i), mul_zero, add_zero]

/-- Ring specialization of the q-Pascal identity in [RW-rec, Lemma 1]. -/
theorem qBinomial_pascal {R : Type*} [CommRing R] (q : R)
    (i j : ℕ) (hj : 0 < j) :
    qBinomial q (i + 1) j =
      qBinomial q i (j - 1) + q ^ j * qBinomial q i j := by
  simp only [qBinomial, qBinomialPoly_pascal i j hj, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]

/-- Specialization at `q = 1`, used for the ordinary binomial reduction in
[RW-rec, Lemma 1].  The conclusion is valid in every commutative ring. -/
theorem qBinomial_one {R : Type*} [CommRing R] (i j : ℕ) :
    qBinomial (1 : R) i j = (i.choose j : R) := by
  induction i generalizing j with
  | zero =>
      cases j <;> simp [qBinomial, qBinomialPoly]
  | succ i ih =>
      cases j with
      | zero => simp [qBinomial, qBinomialPoly_zero_right]
      | succ j =>
          rw [qBinomial_pascal _ i (j + 1) (Nat.succ_pos j)]
          simp [ih, Nat.choose_succ_succ]

/-- Algebraic base-change helper for the reduction statement in [RW-rec, Lemma 1]. -/
theorem map_qBinomial {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (q : R) (i j : ℕ) :
    φ (qBinomial q i j) = qBinomial (φ q) i j := by
  induction i generalizing j with
  | zero => cases j <;> simp [qBinomial, qBinomialPoly]
  | succ i ih =>
      cases j with
      | zero => simp [qBinomial, qBinomialPoly_zero_right]
      | succ j =>
          simp only [qBinomial_pascal _ i (j + 1) (Nat.succ_pos j), map_add,
            map_mul, map_pow, ih]

/-- The reduction mechanism of [RW-rec, Lemma 1]: any ring homomorphism sending
`q` to `1` sends the q-binomial coefficient to the ordinary binomial coefficient. -/
theorem map_qBinomial_eq_choose {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (q : R) (hq : φ q = 1) (i j : ℕ) :
    φ (qBinomial q i j) = (i.choose j : S) := by
  rw [map_qBinomial, hq, qBinomial_one]

/-- Algebraic finite-product helper for the Pochhammer definition in [RW-rec, Lemma 1]. -/
theorem finitePochhammer_succ {R : Type*} [CommRing R] (t q : R) (j : ℕ) :
    finitePochhammer t q (j + 1) =
      finitePochhammer t q j * (1 - q ^ j * t) := by
  exact Finset.prod_range_succ _ _

/-- The denominator normalization in [RW-rec, Lemma 1]: `(q;q)_j` starts
with `1 - q` and ends with `1 - q^j`, so it has no `1 - q^0` factor. -/
theorem finitePochhammer_self {R : Type*} [CommRing R] (q : R) (j : ℕ) :
    finitePochhammer q q j = ∏ r ∈ Finset.range j, (1 - q ^ (r + 1)) := by
  simp only [finitePochhammer, pow_succ]

/-- Denominator-free comparison with the numerator in [RW-rec, Lemma 1].
It also holds off the diagonal and at roots of unity with zero denominator.
Only `q ≠ 0` is needed to interpret the inverse base. -/
theorem finitePochhammer_mul_qBinomial {K : Type*} [Field K]
    (q : K) (hq : q ≠ 0) (i j : ℕ) :
    finitePochhammer q q j * qBinomial q i j =
      finitePochhammer (q ^ i) q⁻¹ j := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero => simp [finitePochhammer, qBinomial, qBinomialPoly]
      | succ j =>
          simp only [qBinomial, qBinomialPoly, Polynomial.eval₂_zero, mul_zero, pow_zero]
          symm
          apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos j))
          simp
  | succ i ih =>
      cases j with
      | zero => simp [finitePochhammer, qBinomial, qBinomialPoly_zero_right]
      | succ j =>
          rw [qBinomial_pascal _ i (j + 1) (Nat.succ_pos j), Nat.add_one_sub_one]
          have hd : finitePochhammer q q (j + 1) =
              finitePochhammer q q j * (1 - q ^ (j + 1)) := by
            rw [finitePochhammer_succ, pow_succ]
          calc
            _ = (1 - q ^ (j + 1)) * (finitePochhammer q q j * qBinomial q i j) +
                q ^ (j + 1) * (finitePochhammer q q (j + 1) * qBinomial q i (j + 1)) := by
                  rw [hd]
                  ring
            _ = _ := by
              rw [ih j, ih (j + 1)]
              exact FiniteQBinomialAux.numerator_pascal q hq i j

/-- The quotient formula of [RW-rec, Lemma 1], under its necessary
nonzero-denominator hypothesis.  The q-binomial coefficient itself was
defined by the integral polynomial, not by this quotient. -/
theorem qBinomial_eq_finitePochhammer_div {K : Type*} [Field K]
    (q : K) (hq : q ≠ 0) (i j : ℕ) (hden : finitePochhammer q q j ≠ 0) :
    qBinomial q i j = finitePochhammer (q ^ i) q⁻¹ j / finitePochhammer q q j := by
  apply (eq_div_iff hden).mpr
  rw [mul_comm, finitePochhammer_mul_qBinomial q hq]

/-- Algebraic polynomial-evaluation helper for the expansion and substitution
in [RW-rec, Lemma 1]. -/
theorem finitePochhammerPoly_eval {R : Type*} [CommRing R]
    (t q : R) (j : ℕ) :
    (finitePochhammerPoly q j).eval t = finitePochhammer t q j := by
  simp [finitePochhammerPoly, finitePochhammer, Polynomial.eval_prod]

/-- Explicit single-coordinate form of the polynomial expansion in [RW-rec, Lemma 1].
The exponent `a.choose 2` is `a(a-1)/2`. -/
theorem finitePochhammerPoly_expansion {R : Type*} [CommRing R]
    (q : R) (j : ℕ) :
    finitePochhammerPoly q j =
      ∑ a ∈ Finset.range (j + 1),
        Polynomial.C (finitePochhammerCoeff q j a) * Polynomial.X ^ a := by
  unfold finitePochhammerPoly
  simp only [Polynomial.C_pow]
  apply FiniteQBinomialAux.product_expansion
    (Polynomial.C q) (fun n a => Polynomial.C (finitePochhammerCoeff q n a))
  · intro n
    simp [finitePochhammerCoeff, qBinomial, qBinomialPoly_zero_right]
  · intro n a ha
    simp [finitePochhammerCoeff, qBinomial, qBinomialPoly_eq_zero_of_lt n a ha]
  · intro n a
    have hc : finitePochhammerCoeff q (n + 1) (a + 1) =
        q ^ (a + 1) * finitePochhammerCoeff q n (a + 1) -
          q ^ a * finitePochhammerCoeff q n a := by
      have hchoose : (a + 1).choose 2 = a.choose 2 + a := by
        rw [show 2 = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
        exact Nat.add_comm _ _
      simp only [finitePochhammerCoeff,
        qBinomial_pascal q n (a + 1) (Nat.succ_pos a), Nat.add_one_sub_one]
      rw [hchoose]
      simp only [pow_add, pow_succ]
      ring
    simpa only [map_sub, map_mul, map_pow] using congrArg Polynomial.C hc

/-- Finite weighted polynomial identity underlying [RW-rec, Lemma 1].
The bounded multi-index `a` satisfies `0 ≤ a ν ≤ j ν` in every coordinate.
The inner positive-kernel sum is the unnormalized Fourier sum at frequency
`-a` for the negative kernel; the normalized transform introduces
the factor `√|H|` of [RW-rec, Lemma 1].
This identity does not include Fourier normalization or a valuation. -/
theorem qBinomial_weighted_sum {K α ι : Type*} [Field K]
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (q : K) (hq : q ≠ 0) (f : α → K) (xIndex : α → ι → ℕ) (j : ι → ℕ) :
    (∏ ν : ι, finitePochhammer q q (j ν)) *
        (∑ x : α, f x * ∏ ν : ι, qBinomial q (xIndex x ν) (j ν)) =
      ∑ a : (ν : ι) → Fin (j ν + 1),
        (∏ ν : ι, finitePochhammerCoeff q⁻¹ (j ν) (a ν).val) *
          (∑ x : α, f x * q ^ (∑ ν : ι, (a ν).val * xIndex x ν)) := by
  classical
  have hcoordinate (x : α) (ν : ι) :
      finitePochhammer q q (j ν) * qBinomial q (xIndex x ν) (j ν) =
        ∑ a : Fin (j ν + 1),
          finitePochhammerCoeff q⁻¹ (j ν) a.val * (q ^ xIndex x ν) ^ a.val := by
    rw [finitePochhammer_mul_qBinomial q hq]
    rw [← finitePochhammerPoly_eval, finitePochhammerPoly_expansion]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact (Fin.sum_univ_eq_sum_range
      (fun a => finitePochhammerCoeff q⁻¹ (j ν) a * (q ^ xIndex x ν) ^ a)
      (j ν + 1)).symm
  calc
    _ = ∑ x : α, f x * ∏ ν : ι,
        (∑ a : Fin (j ν + 1),
          finitePochhammerCoeff q⁻¹ (j ν) a.val * (q ^ xIndex x ν) ^ a.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp_rw [← hcoordinate]
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∑ x : α, ∑ a : (ν : ι) → Fin (j ν + 1),
        f x * ∏ ν : ι,
          (finitePochhammerCoeff q⁻¹ (j ν) (a ν).val *
            (q ^ xIndex x ν) ^ (a ν).val) := by
      simp_rw [Fintype.prod_sum, Finset.mul_sum]
    _ = ∑ a : (ν : ι) → Fin (j ν + 1), ∑ x : α,
        f x * ∏ ν : ι,
          (finitePochhammerCoeff q⁻¹ (j ν) (a ν).val *
            (q ^ xIndex x ν) ^ (a ν).val) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.prod_mul_distrib]
      simp_rw [← pow_mul, Nat.mul_comm (xIndex x _) (a _).val]
      rw [Finset.prod_pow_eq_pow_sum]
      ring

end SICLean.L5.FiniteQBinomial
