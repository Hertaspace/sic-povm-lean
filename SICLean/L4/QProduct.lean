import Mathlib
import SICLean.L4.QProductLimitAux
import SICLean.L4.QProductAnalyticAux

set_option autoImplicit false

/-!
# Q products and the summation base

Definitions are literal products or
summands; no convergence, nonvanishing or identity is included in a definition.
Only `0 < ‖q‖ < 1` is claimed. The total definition outside this domain is not
an analytic continuation. The formulas below are stated for `0 < ‖q‖ < 1`.

[RW26, p. 28, Appendix A.1]. Basic finite-product and
convergence lemmas below support these formulas.

The integer symbol is a concrete finite numerator divided by a concrete finite
denominator. In Lean division is total with `0 / 0 = 0`, so the quotient forms of
[RW26, (49), (52)] are stated with nonvanishing hypotheses, and cleared identities
are given first. The zero-free assertions are
proved separately, including the diagonal denominators in every summand.

The Euler product series is stated for all complex `x` when `0 < ‖q‖ < 1`,
[RW26, (55)]. Jacobi uses an unordered
`HasSum` over `ℤ`, with absolute convergence, not just symmetric partial sums.
The last six statements expose exactly the two double sums needed in G1.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators

namespace SICLean.L4

/-- [RW26, p. 28] `(x;q)∞`, beginning at exponent zero. -/
def qPochhammer (x q : ℂ) : ℂ := ∏' j : ℕ, (1 - x * q ^ j)

/-- [RW26, (50)] empty product. -/
def qPochhammerNat (x q : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, (1 - x * q ^ j)

/-- Numerator of the finite integer symbol, [RW26, (50)--(51)]. -/
def qPochhammerIntNumerator (x q : ℂ) (k : ℤ) : ℂ :=
  if 0 ≤ k then qPochhammerNat x q k.toNat else 1

/--
For negative `k`, the exponents are `k...,-1`, i.e. [RW26, (51)] reverse
order. There is no infinite-product quotient in this definition.
-/
def qPochhammerIntDenominator (x q : ℂ) (k : ℤ) : ℂ :=
  if 0 ≤ k then 1 else qPochhammerNat (x * q ^ k) q (-k).toNat

/-- [RW26, (50)--(51)] total division at a finite denominator zero. -/
def qPochhammerInt (x q : ℂ) (k : ℤ) : ℂ :=
  qPochhammerIntNumerator x q k / qPochhammerIntDenominator x q k

/-- The summand of [RW26, (56)]. -/
def eulerInverseTerm (x q : ℂ) (n : ℕ) : ℂ :=
  x ^ n / qPochhammerNat q q n

/-- [RW26, (55)]. The triangular exponent uses natural division. -/
def eulerTerm (x q : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * q ^ (n * (n - 1) / 2) * x ^ n / qPochhammerNat q q n

/-- [RW26, (58)]. `a` is unrestricted. -/
def qBinomialTerm (a x q : ℂ) (n : ℕ) : ℂ :=
  qPochhammerNat a q n * x ^ n / qPochhammerNat q q n

/--
[RW26, (59)]. All three powers have integer exponents;
`k*(k+1)` is even also for negative `k`.
-/
def jacobiTripleTerm (x q : ℂ) (k : ℤ) : ℂ :=
  (-1 : ℂ) ^ k * q ^ (k * (k + 1) / 2) * x ^ k

/--
The second factor has
`Q^(J*(J+1)/2) C^J`, so the Euler argument is `Q*C`, not `C`.
-/
def singleResidueSeriesTerm (A C q Q : ℂ) (p : ℕ × ℕ) : ℂ :=
  eulerInverseTerm A q p.1 * eulerTerm (Q * C) Q p.2

/--
The two independent q-binomial factors.
-/
def ratioResidueSeriesTerm (a A q b B Q : ℂ) (p : ℕ × ℕ) : ℂ :=
  qBinomialTerm a A q p.1 * qBinomialTerm b B Q p.2

/-- [RW26, (50)] empty-index case. -/
theorem qPochhammerNat_zero (x q : ℂ) : qPochhammerNat x q 0 = 1 := by
  simp [qPochhammerNat]

/-- [RW26, (50)] one-step split. -/
theorem qPochhammerNat_succ (x q : ℂ) (n : ℕ) :
    qPochhammerNat x q (n + 1) = qPochhammerNat x q n * (1 - x * q ^ n) := by
  simp [qPochhammerNat, Finset.prod_range_succ]

/-- [RW26, (52)] nonnegative indices; valid at zero factors. -/
theorem qPochhammerNat_add (x q : ℂ) (m n : ℕ) :
    qPochhammerNat x q (m + n) =
      qPochhammerNat x q m * qPochhammerNat (x * q ^ m) q n := by
  simp only [qPochhammerNat]
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- Finite-product zero classification from [RW26, (50)]. -/
theorem qPochhammerNat_eq_zero_iff (x q : ℂ) (n : ℕ) :
    qPochhammerNat x q n = 0 ↔ ∃ j ∈ Finset.range n, x * q ^ j = 1 := by
  simp only [qPochhammerNat, Finset.prod_eq_zero_iff, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, sub_eq_zero.mpr h.symm⟩

/-- Nonzero diagonal denominators for [RW26, (55), (56), (58)]. -/
theorem qPochhammerNat_q_ne_zero (q : ℂ) (n : ℕ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammerNat q q n ≠ 0 := by
  rw [qPochhammerNat]
  refine Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_
  intro h
  have hq : q * q ^ j = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖q * q ^ j‖ = 1 := by rw [hq]; simp
  rw [norm_mul, norm_pow] at hnorm
  have h2 : ‖q‖ ^ (j + 1) = 1 := by
    rw [pow_succ']
    exact hnorm
  have hlt : ‖q‖ ^ (j + 1) < 1 := pow_lt_one₀ (norm_nonneg q) hq1 (by omega)
  linarith

/-- [RW26, (50)] agreement of the two finite index types. -/
theorem qPochhammerInt_ofNat (x q : ℂ) (n : ℕ) :
    qPochhammerInt x q (n : ℤ) = qPochhammerNat x q n := by
  simp [qPochhammerInt, qPochhammerIntNumerator, qPochhammerIntDenominator,
    Int.toNat_natCast]

/-- [RW26, (51)] includes `n=0` and total inverse at zeros. -/
theorem qPochhammerInt_neg_nat (x q : ℂ) (n : ℕ) :
    qPochhammerInt x q (-(n : ℤ)) =
      (qPochhammerNat (x * q ^ (-(n : ℤ))) q n)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [qPochhammerInt, qPochhammerIntNumerator, qPochhammerIntDenominator,
      qPochhammerNat_zero]
  · have hneg : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
    have htoNat : (-(-(n : ℤ))).toNat = n := by
      rw [neg_neg, Int.toNat_natCast]
    have hn0 : n ≠ 0 := by omega
    simp [qPochhammerInt, qPochhammerIntNumerator, qPochhammerIntDenominator, hneg, htoNat,
      hn0]

private lemma addA (x q : ℂ) (a b : ℕ) (_hq : q ≠ 0) :
    qPochhammerIntNumerator x q ((a:ℤ) + (b:ℤ)) *
        qPochhammerIntDenominator x q (a:ℤ) *
        qPochhammerIntDenominator (x * q ^ (a:ℤ)) q (b:ℤ) =
      qPochhammerIntNumerator x q (a:ℤ) *
        qPochhammerIntNumerator (x * q ^ (a:ℤ)) q (b:ℤ) *
        qPochhammerIntDenominator x q ((a:ℤ) + (b:ℤ)) := by
  have ha : (0:ℤ) ≤ (a:ℤ) := by exact_mod_cast Nat.zero_le a
  have hb : (0:ℤ) ≤ (b:ℤ) := by exact_mod_cast Nat.zero_le b
  have hab : (0:ℤ) ≤ (a:ℤ) + (b:ℤ) := by omega
  simp only [qPochhammerIntNumerator, qPochhammerIntDenominator]
  simp only [if_pos ha, if_pos hb, if_pos hab]
  rw [← Int.natCast_add, Int.toNat_natCast]
  rw [qPochhammerNat_add]
  simp

private lemma addD (x q : ℂ) (a b : ℕ) (hq : q ≠ 0) :
    qPochhammerIntNumerator x q (Int.negSucc a + Int.negSucc b) *
        qPochhammerIntDenominator x q (Int.negSucc a) *
        qPochhammerIntDenominator (x * q ^ (Int.negSucc a)) q (Int.negSucc b) =
      qPochhammerIntNumerator x q (Int.negSucc a) *
        qPochhammerIntNumerator (x * q ^ (Int.negSucc a)) q (Int.negSucc b) *
        qPochhammerIntDenominator x q (Int.negSucc a + Int.negSucc b) := by
  have h1 : ¬ (0:ℤ) ≤ Int.negSucc a := by rw [Int.negSucc_eq]; omega
  have h2 : ¬ (0:ℤ) ≤ Int.negSucc b := by rw [Int.negSucc_eq]; omega
  have h3 : Int.negSucc a + Int.negSucc b = Int.negSucc (a + b + 1) := by
    rw [Int.negSucc_eq, Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring
  have h4 : ¬ (0:ℤ) ≤ Int.negSucc a + Int.negSucc b := by rw [h3]; rw [Int.negSucc_eq]; omega
  simp only [qPochhammerIntNumerator, qPochhammerIntDenominator]
  simp only [if_neg h1, if_neg h2, if_neg h4]
  rw [h3]
  have ea : Int.negSucc a = -((a+1:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  have eb : Int.negSucc b = -((b+1:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  have eab : Int.negSucc (a+b+1) = -((a+b+2:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  rw [ea, eb, eab]
  simp only [neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast]
  have hAB : (q ^ (a + 1))⁻¹ * (q ^ (b + 1))⁻¹ = (q ^ (a + b + 2))⁻¹ := by
    rw [← mul_inv, ← pow_add, show a + 1 + (b + 1) = a + b + 2 by omega]
  rw [mul_assoc x, hAB]
  have hnat := qPochhammerNat_add (x * (q ^ (a+b+2))⁻¹) q (b+1) (a+1)
  have hqpow : x * (q ^ (a+b+2))⁻¹ * q ^ (b+1) = x * (q ^ (a+1))⁻¹ := by
    field_simp [hq]; ring
  rw [hqpow] at hnat
  rw [show b + 1 + (a + 1) = a + b + 2 by omega] at hnat
  rw [hnat]
  ring

private lemma addB1 (x q : ℂ) (b c : ℕ) (hq : q ≠ 0) :
    qPochhammerIntNumerator x q (((b+1+c:ℕ):ℤ) + Int.negSucc b) *
        qPochhammerIntDenominator x q (((b+1+c:ℕ):ℤ)) *
        qPochhammerIntDenominator (x * q ^ (((b+1+c:ℕ):ℤ))) q (Int.negSucc b) =
      qPochhammerIntNumerator x q (((b+1+c:ℕ):ℤ)) *
        qPochhammerIntNumerator (x * q ^ (((b+1+c:ℕ):ℤ))) q (Int.negSucc b) *
        qPochhammerIntDenominator x q (((b+1+c:ℕ):ℤ) + Int.negSucc b) := by
  have hsum : (((b+1+c:ℕ):ℤ) + Int.negSucc b) = (c:ℤ) := by
    rw [Int.negSucc_eq]; push_cast; ring
  have h1 : ¬ (0:ℤ) ≤ Int.negSucc b := by rw [Int.negSucc_eq]; omega
  have h4 : (0:ℤ) ≤ (((b+1+c:ℕ):ℤ) + Int.negSucc b) := by rw [hsum]; exact_mod_cast Nat.zero_le c
  have hpos : (0:ℤ) ≤ ((b+1+c:ℕ):ℤ) := by exact_mod_cast Nat.zero_le (b+1+c)
  simp only [qPochhammerIntNumerator, qPochhammerIntDenominator]
  simp only [if_pos hpos, if_neg h1, if_pos h4]
  rw [hsum]
  have eb : Int.negSucc b = -((b+1:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  rw [eb]
  simp only [neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast]
  have hbase : x * q ^ (b + 1 + c) * (q ^ (b + 1))⁻¹ = x * q ^ c := by
    rw [mul_assoc, ← pow_sub₀ q hq (by omega : b + 1 ≤ b + 1 + c)]
    congr 2
    omega
  rw [hbase]
  have hnat := qPochhammerNat_add x q c (b+1)
  rw [show b + 1 + c = c + (b + 1) by omega]
  rw [hnat]
  ring

private lemma addB2 (x q : ℂ) (a c : ℕ) (hq : q ≠ 0) :
    qPochhammerIntNumerator x q ((a:ℤ) + Int.negSucc (a+c)) *
        qPochhammerIntDenominator x q (a:ℤ) *
        qPochhammerIntDenominator (x * q ^ (a:ℤ)) q (Int.negSucc (a+c)) =
      qPochhammerIntNumerator x q (a:ℤ) *
        qPochhammerIntNumerator (x * q ^ (a:ℤ)) q (Int.negSucc (a+c)) *
        qPochhammerIntDenominator x q ((a:ℤ) + Int.negSucc (a+c)) := by
  have hsum : ((a:ℤ) + Int.negSucc (a+c)) = Int.negSucc c := by
    rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring
  have h2 : ¬ (0:ℤ) ≤ Int.negSucc (a+c) := by rw [Int.negSucc_eq]; omega
  have h4 : ¬ (0:ℤ) ≤ ((a:ℤ) + Int.negSucc (a+c)) := by rw [hsum]; rw [Int.negSucc_eq]; omega
  have hposa : (0:ℤ) ≤ (a:ℤ) := by exact_mod_cast Nat.zero_le a
  simp only [qPochhammerIntNumerator, qPochhammerIntDenominator]
  simp only [if_pos hposa, if_neg h2, if_neg h4]
  rw [hsum]
  have eac : Int.negSucc (a+c) = -(((a+c)+1:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  have ec : Int.negSucc c = -((c+1:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  rw [eac, ec]
  simp only [neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast]
  have hbase : x * q ^ a * (q ^ (a+c+1))⁻¹ = x * (q ^ (c+1))⁻¹ := by
    field_simp [hq]; ring
  rw [hbase]
  have hnat := qPochhammerNat_add (x * (q ^ (c+1))⁻¹) q (c+1) a
  have hqpow : x * (q ^ (c+1))⁻¹ * q ^ (c+1) = x := by
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero (c+1) hq), mul_one]
  rw [hqpow] at hnat
  rw [show c+1+a = a+c+1 by omega] at hnat
  rw [hnat]
  ring

private lemma addC1 (x q : ℂ) (a d : ℕ) (hq : q ≠ 0) :
    qPochhammerIntNumerator x q (Int.negSucc a + (((a+1+d:ℕ):ℤ))) *
        qPochhammerIntDenominator x q (Int.negSucc a) *
        qPochhammerIntDenominator (x * q ^ (Int.negSucc a)) q (((a+1+d:ℕ):ℤ)) =
      qPochhammerIntNumerator x q (Int.negSucc a) *
        qPochhammerIntNumerator (x * q ^ (Int.negSucc a)) q (((a+1+d:ℕ):ℤ)) *
        qPochhammerIntDenominator x q (Int.negSucc a + (((a+1+d:ℕ):ℤ))) := by
  have hsum : Int.negSucc a + (((a+1+d:ℕ):ℤ)) = (d:ℤ) := by
    rw [Int.negSucc_eq]; push_cast; ring
  have h1 : ¬ (0:ℤ) ≤ Int.negSucc a := by rw [Int.negSucc_eq]; omega
  have h4 : (0:ℤ) ≤ Int.negSucc a + (((a+1+d:ℕ):ℤ)) := by rw [hsum]; exact_mod_cast Nat.zero_le d
  have hposb : (0:ℤ) ≤ ((a+1+d:ℕ):ℤ) := by exact_mod_cast Nat.zero_le (a+1+d)
  simp only [qPochhammerIntNumerator, qPochhammerIntDenominator]
  simp only [if_pos hposb, if_neg h1, if_pos h4]
  rw [hsum]
  have ea : Int.negSucc a = -((a+1:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  rw [ea]
  simp only [neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast]
  have hnat := qPochhammerNat_add (x * (q ^ (a+1))⁻¹) q (a+1) d
  have hqpow : x * (q ^ (a+1))⁻¹ * q ^ (a+1) = x := by
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero (a+1) hq), mul_one]
  rw [hqpow] at hnat
  rw [hnat]
  ring

private lemma addC2 (x q : ℂ) (b c : ℕ) (hq : q ≠ 0) :
    qPochhammerIntNumerator x q (Int.negSucc (b+c) + (b:ℤ)) *
        qPochhammerIntDenominator x q (Int.negSucc (b+c)) *
        qPochhammerIntDenominator (x * q ^ (Int.negSucc (b+c))) q (b:ℤ) =
      qPochhammerIntNumerator x q (Int.negSucc (b+c)) *
        qPochhammerIntNumerator (x * q ^ (Int.negSucc (b+c))) q (b:ℤ) *
        qPochhammerIntDenominator x q (Int.negSucc (b+c) + (b:ℤ)) := by
  have hsum : Int.negSucc (b+c) + (b:ℤ) = Int.negSucc c := by
    rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring
  have h1 : ¬ (0:ℤ) ≤ Int.negSucc (b+c) := by rw [Int.negSucc_eq]; omega
  have h4 : ¬ (0:ℤ) ≤ Int.negSucc (b+c) + (b:ℤ) := by rw [hsum]; rw [Int.negSucc_eq]; omega
  have hposb : (0:ℤ) ≤ (b:ℤ) := by exact_mod_cast Nat.zero_le b
  simp only [qPochhammerIntNumerator, qPochhammerIntDenominator]
  simp only [if_pos hposb, if_neg h1, if_neg h4]
  rw [hsum]
  have ea : Int.negSucc (b+c) = -(((b+c)+1:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  have ec : Int.negSucc c = -((c+1:ℕ):ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  rw [ea, ec]
  simp only [neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast]
  have hnat := qPochhammerNat_add (x * (q ^ (b+c+1))⁻¹) q b (c+1)
  have hqpow : x * (q ^ (b+c+1))⁻¹ * q ^ b = x * (q ^ (c+1))⁻¹ := by
    field_simp [hq]; ring
  rw [hqpow] at hnat
  rw [show b + (c + 1) = b + c + 1 by omega] at hnat
  rw [hnat]
  ring

/-- [RW26, (52)] cleared before cancellation, hence valid even at finite zeros. -/
theorem qPochhammerInt_add_cleared (x q : ℂ) (m n : ℤ) (hq : q ≠ 0) :
    qPochhammerIntNumerator x q (m + n) *
        qPochhammerIntDenominator x q m *
        qPochhammerIntDenominator (x * q ^ m) q n =
      qPochhammerIntNumerator x q m *
        qPochhammerIntNumerator (x * q ^ m) q n *
        qPochhammerIntDenominator x q (m + n) := by
  rcases m with a | a <;> rcases n with b | b
  · exact addA x q a b hq
  · by_cases hab : b + 1 ≤ a
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      exact addB1 x q b c hq
    · have hlt : a ≤ b := by omega
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hlt
      exact addB2 x q a c hq
  · by_cases hab : a + 1 ≤ b
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      exact addC1 x q a d hq
    · have hlt : b ≤ a := by omega
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hlt
      exact addC2 x q b c hq
  · exact addD x q a b hq

/-- [RW26, (52)] pointwise quotient form; all finite denominators are explicit. -/
theorem qPochhammerInt_add (x q : ℂ) (m n : ℤ) (hq : q ≠ 0)
    (hd₁ : qPochhammerIntDenominator x q m ≠ 0)
    (hd₂ : qPochhammerIntDenominator (x * q ^ m) q n ≠ 0)
    (hd₃ : qPochhammerIntDenominator x q (m + n) ≠ 0) :
    qPochhammerInt x q (m + n) =
      qPochhammerInt x q m * qPochhammerInt (x * q ^ m) q n := by
  have h := qPochhammerInt_add_cleared x q m n hq
  unfold qPochhammerInt
  rw [div_mul_div_comm]
  field_simp [hd₁, hd₂, hd₃]
  linear_combination h

/-- [RW26, (54)]. This inverse identity respects total division. -/
theorem qPochhammerInt_neg (x q : ℂ) (k : ℤ) (hq : q ≠ 0) :
    qPochhammerInt x q (-k) = (qPochhammerInt (x * q ^ (-k)) q k)⁻¹ := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hk1 : ¬ (0:ℤ) ≤ k := by omega
    have hnk : (0:ℤ) ≤ -k := by omega
    have hqpow : x * q ^ (-k) * q ^ k = x := by
      rw [mul_assoc, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, mul_one]
    simp only [qPochhammerInt, qPochhammerIntNumerator, qPochhammerIntDenominator]
    rw [if_pos hnk, if_neg hk1, if_pos hnk, if_neg hk1]
    rw [hqpow]
    simp
  · simp [qPochhammerInt, qPochhammerIntNumerator, qPochhammerIntDenominator, qPochhammerNat_zero]
  · have hk0 : ¬ (0:ℤ) ≤ -k := by omega
    have hkn : (0:ℤ) ≤ k := by omega
    simp only [qPochhammerInt, qPochhammerIntNumerator, qPochhammerIntDenominator]
    rw [if_neg hk0, if_pos hkn, if_neg hk0, if_pos hkn]
    simp

/-- [RW26, (53)] monomial factors are nonzero. -/
theorem qPochhammerInt_inv_base (x q : ℂ) (k : ℤ) (hx : x ≠ 0) (hq : q ≠ 0) :
    qPochhammerInt x q⁻¹ k =
      (-1 : ℂ) ^ k * x ^ k * q ^ (-(k * (k - 1) / 2)) *
        qPochhammerInt x⁻¹ q k := by
  have tri_step_aux (k : ℤ) :
      (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
    rw [show (k + 1) * (k + 1 - 1) = k * (k - 1) + 2 * k by ring]
    exact Int.add_mul_ediv_left _ _ (by norm_num)

  have tri_double_aux (k : ℤ) :
      k * (k - 1) / 2 * 2 = k * (k - 1) := by
    exact Int.ediv_mul_cancel (Int.even_mul_pred_self k).two_dvd

  have tri_neg_aux (k : ℤ) :
      (-k) * (-k - 1) / 2 = k * k - k * (k - 1) / 2 := by
    have h := tri_double_aux k
    have he : (-k) * (-k - 1) = (k * (k - 1) / 2 + k) * 2 := by
      nlinarith
    rw [he, Int.mul_ediv_cancel _ (by norm_num)]
    nlinarith

  have qPochhammerNat_inv_base_aux (x q : ℂ) (n : ℕ)
      (hx : x ≠ 0) (hq : q ≠ 0) :
      qPochhammerNat x q⁻¹ n =
        (-1 : ℂ) ^ (n : ℤ) * x ^ (n : ℤ) * q ^ (-((n : ℤ) * ((n : ℤ) - 1) / 2)) *
          qPochhammerNat x⁻¹ q n := by
    induction n with
    | zero => simp [qPochhammerNat_zero]
    | succ n ih =>
      rw [qPochhammerNat_succ, qPochhammerNat_succ, ih]
      rw [Nat.cast_add, Nat.cast_one, tri_step_aux]
      rw [neg_add, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        zpow_add₀ hx, zpow_add₀ hq]
      simp only [zpow_one, zpow_neg, zpow_natCast, inv_pow]
      have hf : 1 - x * (q ^ n)⁻¹ =
          -x * (q ^ n)⁻¹ * (1 - x⁻¹ * q ^ n) := by
        field_simp
        ring
      rw [hf]
      ring
  rcases k with n | n
  · change qPochhammerInt x q⁻¹ (n : ℤ) =
      (-1 : ℂ) ^ (n : ℤ) * x ^ (n : ℤ) * q ^ (-((n : ℤ) * ((n : ℤ) - 1) / 2)) *
        qPochhammerInt x⁻¹ q (n : ℤ)
    rw [qPochhammerInt_ofNat, qPochhammerInt_ofNat]
    exact qPochhammerNat_inv_base_aux x q n hx hq
  · have he : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    rw [he, qPochhammerInt_neg_nat, qPochhammerInt_neg_nat]
    have hqpow : (q⁻¹) ^ (-((n + 1 : ℕ) : ℤ)) = q ^ ((n + 1 : ℕ) : ℤ) := by simp
    rw [hqpow]
    rw [qPochhammerNat_inv_base_aux (x * q ^ ((n + 1 : ℕ) : ℤ)) q (n + 1)
      (mul_ne_zero hx (zpow_ne_zero _ hq)) hq]
    have harg : (x * q ^ ((n + 1 : ℕ) : ℤ))⁻¹ =
        x⁻¹ * q ^ (-((n + 1 : ℕ) : ℤ)) := by rw [mul_inv, ← zpow_neg]
    rw [harg]
    simp only [mul_inv, mul_zpow, ← zpow_neg, ← zpow_mul, neg_neg, tri_neg_aux]
    have hexp (a b : ℤ) : -(a - b) = -a + b := by ring
    rw [hexp, zpow_add₀ hq]
    ring

/--
Convergence obligation for the infinite product, using
`multipliable_one_add_of_summable` and `summable_geometric_of_norm_lt_one`.
-/
theorem hasProd_qPochhammer (x q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    HasProd (fun j : ℕ => 1 - x * q ^ j) (qPochhammer x q) := by
  have hs : Summable fun j : ℕ => ‖(-x) * q ^ j‖ := by
    have h := (summable_geometric_of_lt_one (norm_nonneg q) hq1).mul_left ‖x‖
    simpa [norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc] using h
  have hm := multipliable_one_add_of_summable (f := fun j : ℕ => -x * q ^ j) hs
  simpa [qPochhammer, sub_eq_add_neg] using hm.hasProd

/-- Ordered finite truncations converge to the same unordered product. -/
theorem tendsto_qPochhammerNat (x q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    Tendsto (qPochhammerNat x q) atTop (𝓝 (qPochhammer x q)) := by
  exact (hasProd_qPochhammer x q hq0 hq1).tendsto_prod_nat

/-- Compact uniform version, needed before exchanging parameter limits. -/
theorem hasProdUniformlyOn_qPochhammer (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hKD : K ⊆ {p | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1}) :
    HasProdUniformlyOn (fun j (p : ℂ × ℂ) => 1 - p.1 * p.2 ^ j)
      (fun p => qPochhammer p.1 p.2) K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using
      (tendstoUniformlyOn_empty (F := fun (n : Finset ℕ) (p : ℂ × ℂ) =>
        ∏ i ∈ n, (1 - p.1 * p.2 ^ i)) (f := fun p : ℂ × ℂ => qPochhammer p.1 p.2))
  · obtain ⟨q0, hq0K, -, hB⟩ := hK.exists_sSup_image_eq_and_ge hne
      (show ContinuousOn (fun p : ℂ × ℂ => ‖p.2‖) K from by fun_prop)
    obtain ⟨x0, hx0K, -, hA⟩ := hK.exists_sSup_image_eq_and_ge hne
      (show ContinuousOn (fun p : ℂ × ℂ => ‖p.1‖) K from by fun_prop)
    have hr : ‖q0.2‖ < 1 := (hKD hq0K).2
    have hu : Summable fun n : ℕ => ‖x0.1‖ * ‖q0.2‖ ^ n :=
      (summable_geometric_of_lt_one (norm_nonneg _) hr).mul_left ‖x0.1‖
    have hbound : ∀ᶠ (n : ℕ) in atTop, ∀ p ∈ K, ‖-p.1 * p.2 ^ n‖ ≤ ‖x0.1‖ * ‖q0.2‖ ^ n := by
      filter_upwards with n p hp
      have hp2 : ‖p.2‖ ≤ ‖q0.2‖ := hB p hp
      have hp1 : ‖p.1‖ ≤ ‖x0.1‖ := hA p hp
      calc ‖-p.1 * p.2 ^ n‖ = ‖p.1‖ * ‖p.2‖ ^ n := by
              rw [norm_mul, norm_pow, norm_neg]
        _ ≤ ‖x0.1‖ * ‖q0.2‖ ^ n := by
            exact mul_le_mul hp1 (pow_le_pow_left₀ (norm_nonneg p.2) hp2 n)
              (pow_nonneg (norm_nonneg p.2) n) (norm_nonneg x0.1)
    have hcont : ∀ n : ℕ, ContinuousOn (fun p : ℂ × ℂ => -p.1 * p.2 ^ n) K := by
      intro n
      exact (by fun_prop : ContinuousOn (fun p : ℂ × ℂ => -p.1 * p.2 ^ n) K)
    have h := hu.hasProdUniformlyOn_nat_one_add
      (f := fun n (p : ℂ × ℂ) => -p.1 * p.2 ^ n) hK hbound hcont
    simpa [qPochhammer, sub_eq_add_neg] using h

/--
Joint local uniform version of [RW26]'s product. Mathlib comparison:
`ModularForm.multipliableLocallyUniformlyOn_one_sub_pow` treats only `x=q`.
-/
theorem hasProdLocallyUniformlyOn_qPochhammer :
    HasProdLocallyUniformlyOn (fun j (p : ℂ × ℂ) => 1 - p.1 * p.2 ^ j)
      (fun p => qPochhammer p.1 p.2) {p | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1} := by
  have hopen : IsOpen {p : ℂ × ℂ | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1} := by
    rw [setOf_and]
    exact (isOpen_lt continuous_const continuous_snd.norm).inter
      (isOpen_lt continuous_snd.norm continuous_const)
  apply hasProdLocallyUniformlyOn_of_forall_compact hopen
  intro K hKsub hK
  exact hasProdUniformlyOn_qPochhammer K hK hKsub

/-- Joint holomorphy obligation for the general product, not just two
separate one-variable statements. -/
theorem differentiableOn_qPochhammer_joint :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => qPochhammer p.1 p.2)
      {p | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1} := by
  intro p hp
  exact (SICLean.QProductAnalyticAux.analyticAt_tprod_one_sub p hp.2).differentiableAt.differentiableWithinAt

/-- Joint analytic version for subsequent explicit local quotient charts.
This needs a genuine multivariable analytic argument; the single-variable
`DifferentiableOn.analyticOnNhd` is not by itself that argument. -/
theorem analyticOnNhd_qPochhammer_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => qPochhammer p.1 p.2)
      {p | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1} := by
  intro p hp
  exact SICLean.QProductAnalyticAux.analyticAt_tprod_one_sub p hp.2

/-- Entire in `x` for fixed admissible `q`. -/
theorem differentiable_qPochhammer_x (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    Differentiable ℂ (fun x => qPochhammer x q) := by
  have hmap : MapsTo (fun x : ℂ => (x,q)) univ {p | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1} := by
    intro x hx; exact ⟨hq0,hq1⟩
  have h := hasProdLocallyUniformlyOn_qPochhammer.comp (fun x : ℂ => (x,q)) hmap (by fun_prop)
  have hd : DifferentiableOn ℂ (fun x => qPochhammer x q) univ :=
    h.differentiableOn (Eventually.of_forall fun n => by
      exact (by fun_prop : DifferentiableOn ℂ (fun x : ℂ => ∏ i ∈ n, (1 - x * q ^ i)) univ)) isOpen_univ
  exact differentiableOn_univ.mp hd

/-- Holomorphic in the base on the punctured open unit disc. -/
theorem differentiableOn_qPochhammer_q (x : ℂ) :
    DifferentiableOn ℂ (fun q => qPochhammer x q) {q | 0 < ‖q‖ ∧ ‖q‖ < 1} := by
  have hopen : IsOpen {q : ℂ | 0 < ‖q‖ ∧ ‖q‖ < 1} := by
    rw [setOf_and]
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hmap : MapsTo (fun q : ℂ => (x,q)) {q | 0 < ‖q‖ ∧ ‖q‖ < 1}
      {p | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1} := by
    intro q hq; exact hq
  have h := hasProdLocallyUniformlyOn_qPochhammer.comp (fun q : ℂ => (x,q)) hmap (by fun_prop)
  exact h.differentiableOn (Eventually.of_forall fun n => by
      exact (by fun_prop : DifferentiableOn ℂ (fun q : ℂ => ∏ i ∈ n, (1 - x * q ^ i))
        {q | 0 < ‖q‖ ∧ ‖q‖ < 1})) hopen

private lemma mul_q_pow_eq_one_iff (x q : ℂ) (hq0 : 0 < ‖q‖) (j : ℕ) :
    x * q ^ j = 1 ↔ x = q ^ (-(j : ℤ)) := by
  have hq : q ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hq0)
  constructor
  · intro h
    have h' : x * q ^ (j:ℤ) = 1 := by simpa using h
    have hqj : q ^ (j:ℤ) * q ^ (-(j:ℤ)) = 1 := by
      rw [← zpow_add₀ hq]; simp
    calc x = x * (q ^ (j:ℤ) * q ^ (-(j:ℤ))) := by rw [hqj, mul_one]
      _ = (x * q ^ (j:ℤ)) * q ^ (-(j:ℤ)) := by ring
      _ = q ^ (-(j:ℤ)) := by rw [h', one_mul]
  · intro h
    rw [h, ← zpow_natCast q j, ← zpow_add₀ hq]
    simp

/-- Exact zero classification of [RW26]'s product, including `x=1`. -/
theorem qPochhammer_eq_zero_iff (x q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer x q = 0 ↔ ∃ j : ℕ, x = q ^ (-(j : ℤ)) := by
  have hq : q ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hq0)
  constructor
  · intro h
    by_contra hx
    have hnz : qPochhammer x q ≠ 0 := by
      have htn := tprod_one_add_ne_zero_of_summable (f := fun j : ℕ => -x * q ^ j) ?_ ?_
      · simpa [qPochhammer, sub_eq_add_neg] using htn
      · intro j
        have hne : x * q ^ j ≠ 1 := by
          intro h1
          exact hx ⟨j, (mul_q_pow_eq_one_iff x q hq0 j).mp h1⟩
        rw [show (1:ℂ) + -x * q ^ j = 1 - x * q ^ j by ring]
        exact sub_ne_zero.mpr hne.symm
      · have hs : Summable fun j : ℕ => ‖(-x) * q ^ j‖ := by
          have h := (summable_geometric_of_lt_one (norm_nonneg q) hq1).mul_left ‖x‖
          simpa [norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc] using h
        simpa [qPochhammer, sub_eq_add_neg] using hs
    exact hnz h
  · rintro ⟨j, rfl⟩
    apply tprod_of_exists_eq_zero
    refine ⟨j, ?_⟩
    rw [← zpow_natCast q j, ← zpow_add₀ hq]
    simp

/-- Nonvanishing is a conclusion, not built into `qPochhammer`. -/
theorem qPochhammer_ne_zero_iff (x q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer x q ≠ 0 ↔ ∀ j : ℕ, x * q ^ j ≠ 1 := by
  rw [ne_eq, qPochhammer_eq_zero_iff x q hq0 hq1]
  constructor
  · rintro h j hj
    exact h ⟨j, (mul_q_pow_eq_one_iff x q hq0 j).mp hj⟩
  · rintro h ⟨j, hj⟩
    exact h j ((mul_q_pow_eq_one_iff x q hq0 j).mpr hj)

/-- The `|x|<1` denominators in Euler and q-binomial sums are nonzero. -/
theorem qPochhammer_ne_zero_of_norm_lt_one (x q : ℂ)
    (hx : ‖x‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer x q ≠ 0 := by
  rw [qPochhammer_ne_zero_iff x q hq0 hq1]
  intro j h
  have hnorm : ‖x * q ^ j‖ = 1 := by rw [h]; simp
  rw [norm_mul, norm_pow] at hnorm
  have hqj : ‖q‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg q) hq1.le
  have hle : ‖x‖ * ‖q‖ ^ j ≤ ‖x‖ := by
    calc ‖x‖ * ‖q‖ ^ j ≤ ‖x‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hqj (norm_nonneg x)
      _ = ‖x‖ := mul_one _
  linarith

/-- Diagonal nonvanishing, for η and the G1 prefactors. -/
theorem qPochhammer_q_ne_zero (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer q q ≠ 0 :=
  qPochhammer_ne_zero_of_norm_lt_one q q hq1 hq0 hq1

/-- Constant product from [RW26]'s definition; independent of the base. -/
theorem qPochhammer_zero (q : ℂ) : qPochhammer 0 q = 1 := by
  simp [qPochhammer]

/-- [RW26, (49)--(50)] multiplicative form valid also at common zeros. -/
theorem qPochhammer_shift_nat (x q : ℂ) (n : ℕ)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer x q = qPochhammerNat x q n * qPochhammer (x * q ^ n) q := by
  let f : ℕ → ℂ := fun i => 1 - x * q ^ i
  have hshift := hasProd_qPochhammer (x * q ^ n) q hq0 hq1
  have hshift' : HasProd (fun j => f (j + n)) (qPochhammer (x * q ^ n) q) :=
    hshift.congr_fun (fun j => by
      dsimp [f]
      rw [show x * q ^ n * q ^ j = x * q ^ (j + n) by rw [pow_add]; ring])
  have h := hshift'.prod_range_mul (f := f) (k := n)
  have heq := (hasProd_qPochhammer x q hq0 hq1).unique h
  exact heq

/-- [RW26, (49)--(51)] cleared integer shift, with no cancellation assumptions. -/
theorem qPochhammer_shift_int_cleared (x q : ℂ) (k : ℤ)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammerIntDenominator x q k * qPochhammer x q =
      qPochhammerIntNumerator x q k * qPochhammer (x * q ^ k) q := by
  by_cases hk : (0:ℤ) ≤ k
  · have hden : qPochhammerIntDenominator x q k = 1 := by
      simp [qPochhammerIntDenominator, hk]
    have hnum : qPochhammerIntNumerator x q k = qPochhammerNat x q k.toNat := by
      simp [qPochhammerIntNumerator, hk]
    rw [hden, hnum, one_mul]
    have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
    have hkpow : q ^ k = q ^ k.toNat := by
      conv_lhs => rw [← Int.toNat_of_nonneg hk]
      rw [zpow_natCast]
    rw [hkpow]
    exact qPochhammer_shift_nat x q k.toNat hq0 hq1
  · have hkneg : k < 0 := by omega
    have hq : q ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hq0)
    have hm : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hnum : qPochhammerIntNumerator x q k = 1 := by
      simp [qPochhammerIntNumerator, hk]
    have hden : qPochhammerIntDenominator x q k =
        qPochhammerNat (x * q ^ k) q (-k).toNat := by
      simp [qPochhammerIntDenominator, hk]
    rw [hnum, hden, one_mul]
    have hshift := qPochhammer_shift_nat (x * q ^ k) q (-k).toNat hq0 hq1
    have hbase : x * q ^ k * q ^ ((-k).toNat) = x := by
      rw [← zpow_natCast q ((-k).toNat), mul_assoc, ← zpow_add₀ hq]
      have : k + ((-k).toNat : ℕ) = 0 := by omega
      rw [this, zpow_zero, mul_one]
    rw [hbase] at hshift
    rw [hshift]

/-- Pointwise integer shift, after checking its finite denominator. -/
theorem qPochhammer_shift_int (x q : ℂ) (k : ℤ)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hd : qPochhammerIntDenominator x q k ≠ 0) :
    qPochhammer x q = qPochhammerInt x q k * qPochhammer (x * q ^ k) q := by
  have h := qPochhammer_shift_int_cleared x q k hq0 hq1
  unfold qPochhammerInt
  field_simp [hd] at h ⊢
  linear_combination h

/-- [RW26, (49)] quotient form only away from the shifted infinite zero set. -/
theorem qPochhammerInt_eq_div (x q : ℂ) (k : ℤ)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hs : qPochhammer (x * q ^ k) q ≠ 0) :
    qPochhammerInt x q k = qPochhammer x q / qPochhammer (x * q ^ k) q := by
  have hd : qPochhammerIntDenominator x q k ≠ 0 := by
    by_cases hk : (0:ℤ) ≤ k
    · simp [qPochhammerIntDenominator, hk]
    · intro hd0
      have hnum : qPochhammerIntNumerator x q k = 1 := by
        simp [qPochhammerIntNumerator, hk]
      have h := qPochhammer_shift_int_cleared x q k hq0 hq1
      rw [hd0, zero_mul, hnum, one_mul] at h
      exact hs h.symm
  have hshift := qPochhammer_shift_int x q k hq0 hq1 hd
  unfold qPochhammerInt
  rw [hshift]
  field_simp [hd, hs]
  exact (mul_div_cancel₀ _ hd).symm

/--
Residue-class grouping of [RW26]'s product. `c` is strictly positive.
-/
theorem qPochhammer_residue_classes (x q : ℂ) (c : ℕ) (hc : 0 < c)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer x q =
      ∏ r ∈ Finset.range c, qPochhammer (x * q ^ r) (q ^ c) := by
  letI : NeZero c := ⟨by omega⟩
  let f : ℕ → ℂ := fun n => 1 - x * q ^ n
  have hq2 : ‖q ^ c‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq1 hc.ne'
  have hq02 : 0 < ‖q ^ c‖ := by rw [norm_pow]; positivity
  have hP : Multipliable f := (hasProd_qPochhammer x q hq0 hq1).multipliable
  have hmult : Multipliable (fun p : ℕ × Fin c => f (p.1 * c + p.2)) := by
    have h := (Equiv.multipliable_iff (Nat.divModEquiv c).symm).mpr hP
    convert h using 1
    ext p
    simp [Nat.divModEquiv_symm_apply]
  have hfib : ∀ m : ℕ, Multipliable (fun r : Fin c => f (m * c + r)) := by
    intro m
    exact (hasProd_fintype (fun r : Fin c => f (m * c + r))).multipliable
  have hsplit := hmult.tprod_prod' hfib
  have hreindex : (∏' p : ℕ × Fin c, f (p.1 * c + p.2)) = ∏' n, f n := by
    simpa [f, Nat.divModEquiv] using (Equiv.tprod_eq (Nat.divModEquiv c).symm f)
  rw [show qPochhammer x q = ∏' n, f n by rfl, ← hreindex, hsplit]
  have hfin : ∀ m : ℕ, (∏' r : Fin c, f (m * c + r)) =
      ∏ r ∈ Finset.range c, (1 - (x * q ^ r) * (q ^ c) ^ m) := by
    intro m
    rw [tprod_fintype, Fin.prod_univ_eq_prod_range (fun i => f (m * c + i)) c]
    apply Finset.prod_congr rfl
    intro r hr
    dsimp [f]
    rw [pow_add, pow_mul]
    ring
  simp_rw [hfin]
  rw [Multipliable.tprod_finsetProd]
  · rfl
  · intro r hr
    exact (hasProd_qPochhammer (x * q ^ r) (q ^ c) hq02 hq2).multipliable

/--
The order-two distribution product,
in multiplicative form, including zero factors.
-/
theorem qPochhammer_sign_pair (x q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer x q * qPochhammer (-x) q = qPochhammer (x ^ 2) (q ^ 2) := by
  have h1 := hasProd_qPochhammer x q hq0 hq1
  have h2 := hasProd_qPochhammer (-x) q hq0 hq1
  have hmul := h1.mul h2
  have hq2 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q, hq1]
  have hq02 : 0 < ‖q ^ 2‖ := by rw [norm_pow]; positivity
  have h3 := hasProd_qPochhammer (x ^ 2) (q ^ 2) hq02 hq2
  have heq := hmul.unique (h3.congr_fun (fun j => by
    rw [pow_two, ← pow_mul, show 2 * j = j * 2 by omega, pow_mul]
    ring))
  exact heq

/--
Both constant factors 2
must cancel in the ratio used at a zero class.
-/
theorem qPochhammer_neg_one (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer (-1) q = 2 * qPochhammer (-q) q := by
  have h := qPochhammer_shift_nat (-1) q 1 hq0 hq1
  have hnat : qPochhammerNat (-1) q 1 = 2 := by simp [qPochhammerNat]; norm_num
  rw [h, hnat]
  ring_nf

/-- Same passage: `(-q;q)∞ (q;q)∞ = (q²;q²)∞`, before division. -/
theorem qPochhammer_neg_q_mul (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer (-q) q * qPochhammer q q = qPochhammer (q ^ 2) (q ^ 2) := by
  rw [mul_comm]
  exact qPochhammer_sign_pair q q hq0 hq1

/-- Same passage, quotient justified by `qPochhammer_q_ne_zero`. -/
theorem qPochhammer_neg_q (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer (-q) q = qPochhammer (q ^ 2) (q ^ 2) / qPochhammer q q := by
  have h := qPochhammer_neg_q_mul q hq0 hq1
  have hz := qPochhammer_q_ne_zero q hq0 hq1
  rw [← h]
  field_simp [hz]

private lemma denom_lower (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ∀ᶠ n : ℕ in atTop, ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q n‖ := by
  have hL : 0 < ‖qPochhammer q q‖ := norm_pos_iff.mpr (qPochhammer_q_ne_zero q hq0 hq1)
  have ht : Tendsto (fun n => ‖qPochhammerNat q q n‖) atTop (𝓝 ‖qPochhammer q q‖) :=
    (tendsto_qPochhammerNat q q hq0 hq1).norm
  have hev : ∀ᶠ n : ℕ in atTop,
      |‖qPochhammerNat q q n‖ - ‖qPochhammer q q‖| < ‖qPochhammer q q‖ / 2 :=
    (Metric.tendsto_nhds.mp ht) (‖qPochhammer q q‖ / 2) (by positivity)
  filter_upwards [hev] with n hn
  have := abs_lt.mp hn
  linarith

/-- Absolute convergence for [RW26, (56)]. -/
theorem summable_norm_eulerInverseTerm (x q : ℂ)
    (hx : ‖x‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    Summable (fun n => ‖eulerInverseTerm x q n‖) := by
  have hL : 0 < ‖qPochhammer q q‖ := norm_pos_iff.mpr (qPochhammer_q_ne_zero q hq0 hq1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (denom_lower q hq0 hq1)
  rw [← summable_nat_add_iff N]
  refine Summable.of_nonneg_of_le
    (f := fun n => (2 / ‖qPochhammer q q‖) * ‖x‖ ^ N * ‖x‖ ^ n) ?_ ?_ ?_
  · intro n; positivity
  · intro n
    rw [eulerInverseTerm, norm_div, norm_pow]
    have hden : ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q (n + N)‖ := hN (n + N) (by omega)
    have hx0 : 0 ≤ ‖x‖ ^ (n + N) := pow_nonneg (norm_nonneg x) _
    have hdpos : 0 < ‖qPochhammer q q‖ / 2 := by positivity
    calc ‖x‖ ^ (n + N) / ‖qPochhammerNat q q (n + N)‖
        ≤ ‖x‖ ^ (n + N) / (‖qPochhammer q q‖ / 2) := div_le_div_of_nonneg_left hx0 hdpos hden
      _ = (2 / ‖qPochhammer q q‖) * ‖x‖ ^ (n + N) := by field_simp
      _ = (2 / ‖qPochhammer q q‖) * ‖x‖ ^ N * ‖x‖ ^ n := by rw [pow_add]; ring
  · exact (summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left _

private lemma differentiableOn_tsum_eulerInverse (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    DifferentiableOn ℂ (fun x => ∑' n, eulerInverseTerm x q n) (Metric.ball (0:ℂ) 1) := by
  have hL : 0 < ‖qPochhammer q q‖ := norm_pos_iff.mpr (qPochhammer_q_ne_zero q hq0 hq1)
  have hloc : HasSumLocallyUniformlyOn (fun n x => eulerInverseTerm x q n)
      (fun x => ∑' n, eulerInverseTerm x q n) (Metric.ball (0:ℂ) 1) := by
    apply hasSumLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simpa [hasSumUniformlyOn_iff_tendstoUniformlyOn] using
        (tendstoUniformlyOn_empty (F := fun (n : Finset ℕ) (x : ℂ) =>
          ∑ i ∈ n, eulerInverseTerm x q i) (f := fun x : ℂ => ∑' n, eulerInverseTerm x q n))
    · obtain ⟨x0, hx0K, -, hB⟩ := hK.exists_sSup_image_eq_and_ge hne
        (show ContinuousOn (fun x : ℂ => ‖x‖) K from by fun_prop)
      have hr : ‖x0‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hKsub hx0K
      have hu : Summable fun n : ℕ => (2 / ‖qPochhammer q q‖) * ‖x0‖ ^ n :=
        (summable_geometric_of_lt_one (norm_nonneg x0) hr).mul_left _
      refine HasSumUniformlyOn.of_norm_le_summable_eventually (u := fun n => (2 / ‖qPochhammer q q‖) * ‖x0‖ ^ n) hu ?_
      have hdenEv : ∀ᶠ n : ℕ in cofinite, ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q n‖ := by
        rw [Nat.cofinite_eq_atTop]
        exact denom_lower q hq0 hq1
      filter_upwards [hdenEv] with n hn x hx
      have hn' : ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q n‖ := hn
      rw [eulerInverseTerm, norm_div, norm_pow]
      have hxnorm : ‖x‖ ≤ ‖x0‖ := hB x hx
      have hnum : ‖x‖ ^ n ≤ ‖x0‖ ^ n := pow_le_pow_left₀ (norm_nonneg x) hxnorm n
      have hdpos : 0 < ‖qPochhammer q q‖ / 2 := by positivity
      calc ‖x‖ ^ n / ‖qPochhammerNat q q n‖
          ≤ ‖x‖ ^ n / (‖qPochhammer q q‖ / 2) :=
            div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg x) n) hdpos hn'
        _ ≤ ‖x0‖ ^ n / (‖qPochhammer q q‖ / 2) :=
            div_le_div_of_nonneg_right hnum hdpos.le
        _ = (2 / ‖qPochhammer q q‖) * ‖x0‖ ^ n := by field_simp
  have h' : TendstoLocallyUniformlyOn (fun n : Finset ℕ => fun x : ℂ =>
      ∑ i ∈ n, eulerInverseTerm x q i) (fun x => ∑' n, eulerInverseTerm x q n) atTop
      (Metric.ball (0:ℂ) 1) := hloc
  exact h'.differentiableOn (Eventually.of_forall fun n => by
    refine DifferentiableOn.fun_sum ?_
    intro i hi
    simp only [eulerInverseTerm]
    fun_prop) Metric.isOpen_ball

private lemma eulerInverse_functional (x q : ℂ) (hx : ‖x‖ < 1)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (∑' n, eulerInverseTerm (q*x) q n) =
      (∑' n, eulerInverseTerm x q n) - x * (∑' n, eulerInverseTerm x q n) := by
  let a : ℕ → ℂ := fun n => eulerInverseTerm x q n
  let b : ℕ → ℂ := fun n => x * a n
  let a' : ℕ → ℂ := fun n => eulerInverseTerm (q*x) q n
  have hq : q ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hq0)
  have hqx : ‖q * x‖ < 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg q, norm_nonneg x]
  have hFa : HasSum a (∑' n, a n) :=
    (Summable.of_norm (summable_norm_eulerInverseTerm x q hx hq0 hq1)).hasSum
  have hFq : HasSum a' (∑' n, a' n) :=
    (Summable.of_norm (summable_norm_eulerInverseTerm (q*x) q hqx hq0 hq1)).hasSum
  have ha0 : a 0 = 1 := by simp [a, eulerInverseTerm, qPochhammerNat]
  have ha'0 : a' 0 = 1 := by simp [a', eulerInverseTerm, qPochhammerNat]
  have hb : HasSum b (x * ∑' n, a n) := hFa.mul_left x
  have hshiftA : HasSum (fun n => a (n+1)) ((∑' n, a n) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hFa
    simpa [ha0] using h
  have hshiftA' : HasSum (fun n => a' (n+1)) ((∑' n, a' n) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hFq
    simpa [ha'0] using h
  have hsub : HasSum (fun n => a (n+1) - b n) (((∑' n, a n) - 1) - x * ∑' n, a n) :=
    hshiftA.sub hb
  have hpt : ∀ n, a' (n+1) = a (n+1) - b n := by
    intro n
    dsimp [a, b, a']
    have hd1 : qPochhammerNat q q n ≠ 0 := qPochhammerNat_q_ne_zero q n hq0 hq1
    have hd2 : qPochhammerNat q q (n+1) ≠ 0 := qPochhammerNat_q_ne_zero q (n+1) hq0 hq1
    have hd : 1 - q * q ^ n ≠ 0 := by
      intro h
      apply hd2
      rw [qPochhammerNat_succ, h, mul_zero]
    simp only [eulerInverseTerm]
    rw [qPochhammerNat_succ, mul_pow, pow_succ]
    field_simp [hd1, hd2]
    have hd' : 1 - q ^ n * q ≠ 0 := by simpa [mul_comm] using hd
    field_simp [hd']
    ring
  have hsame : HasSum (fun n => a' (n+1)) (((∑' n, a n) - 1) - x * ∑' n, a n) :=
    hsub.congr_fun (fun n => hpt n)
  have heq := hshiftA'.unique hsame
  dsimp [a', a] at heq ⊢
  linear_combination heq

/--
[RW26, (56)].
The denominator is nonzero by `qPochhammer_ne_zero_of_norm_lt_one`.
-/
theorem hasSum_eulerInverse (x q : ℂ)
    (hx : ‖x‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    HasSum (eulerInverseTerm x q) (qPochhammer x q)⁻¹ := by
  let F : ℂ → ℂ := fun y => ∑' n, eulerInverseTerm y q n
  let P : ℂ → ℂ := fun y => qPochhammer y q
  have hFdiff : DifferentiableOn ℂ F (Metric.ball (0:ℂ) 1) :=
    differentiableOn_tsum_eulerInverse q hq0 hq1
  have hPdiff : DifferentiableOn ℂ P (Metric.ball (0:ℂ) 1) :=
    (differentiable_qPochhammer_x q hq0 hq1).differentiableOn
  have hHdiff : DifferentiableOn ℂ (fun y => F y * P y) (Metric.ball (0:ℂ) 1) :=
    hFdiff.mul hPdiff
  have hcont : ContinuousAt (fun y => F y * P y) 0 :=
    (hHdiff.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  have hF0 : F 0 = 1 := by
    dsimp [F]
    rw [tsum_eq_single 0]
    · simp [eulerInverseTerm, qPochhammerNat]
    · intro b hb
      have h0 : (0:ℂ)^b = 0 := zero_pow hb
      simp [eulerInverseTerm, h0]
  have hP0 : P 0 = 1 := by dsimp [P]; exact qPochhammer_zero q
  have hH0 : F 0 * P 0 = 1 := by rw [hF0, hP0, one_mul]
  have hHstep : ∀ y, ‖y‖ < 1 → F (q*y) * P (q*y) = F y * P y := by
    intro y hy
    have hFE := eulerInverse_functional y q hy hq0 hq1
    have hP := qPochhammer_shift_nat y q 1 hq0 hq1
    have hP' : P y = (1 - y) * P (q*y) := by
      dsimp [P]
      simpa [qPochhammerNat, mul_comm] using hP
    dsimp [F, P] at hFE ⊢
    calc (∑' n, eulerInverseTerm (q * y) q n) * qPochhammer (q * y) q
        = ((∑' n, eulerInverseTerm y q n) - y * ∑' n, eulerInverseTerm y q n) *
            qPochhammer (q * y) q := by rw [hFE]
      _ = (1 - y) * (∑' n, eulerInverseTerm y q n) * qPochhammer (q * y) q := by ring
      _ = (∑' n, eulerInverseTerm y q n) * ((1 - y) * qPochhammer (q * y) q) := by ring
      _ = (∑' n, eulerInverseTerm y q n) * qPochhammer y q := by rw [← hP']
  have hiter : ∀ y, ‖y‖ < 1 → ∀ n : ℕ, F (q^n * y) * P (q^n * y) = F y * P y := by
    intro y hy n
    induction n with
    | zero => simp
    | succ n ih =>
        have hball : ‖q^n * y‖ < 1 := by
          have h1 : ‖q‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg q) hq1.le
          rw [norm_mul, norm_pow]
          calc ‖q‖ ^ n * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
            _ = ‖y‖ := one_mul _
            _ < 1 := hy
        calc F (q ^ (n+1) * y) * P (q ^ (n+1) * y)
            = F (q * (q^n * y)) * P (q * (q^n * y)) := by rw [pow_succ]; ring_nf
          _ = F (q^n * y) * P (q^n * y) := hHstep (q^n * y) hball
          _ = F y * P y := ih
  have hlim : Tendsto (fun n => q^n * x) atTop (𝓝 0) := by
    have hqpow : Tendsto (fun n : ℕ => q^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1
    simpa [mul_comm] using hqpow.mul_const x
  have htend : Tendsto (fun n => F (q^n*x) * P (q^n*x)) atTop (𝓝 (F 0 * P 0)) :=
    hcont.tendsto.comp hlim
  have htend_const : Tendsto (fun _ : ℕ => F x * P x) atTop (𝓝 (F 0 * P 0)) :=
    htend.congr' (Eventually.of_forall fun n => hiter x hx n)
  have hHx : F x * P x = 1 := by
    have hEq := tendsto_nhds_unique tendsto_const_nhds htend_const
    rw [hH0] at hEq
    exact hEq
  have hFx : F x = (P x)⁻¹ := eq_inv_of_mul_eq_one_left hHx
  have hFsum : HasSum (fun n => eulerInverseTerm x q n) (F x) :=
    (Summable.of_norm (summable_norm_eulerInverseTerm x q hx hq0 hq1)).hasSum
  rw [show F x = (qPochhammer x q)⁻¹ by simpa [P] using hFx] at hFsum
  exact hFsum

/-- Multiplicative version of [RW26, (56)] cancellation. -/
theorem hasSum_eulerInverse_mul (x q : ℂ)
    (hx : ‖x‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    HasSum (fun n => qPochhammer x q * eulerInverseTerm x q n) 1 := by
  have h := (hasSum_eulerInverse x q hx hq0 hq1).mul_left (qPochhammer x q)
  have hz := qPochhammer_ne_zero_of_norm_lt_one x q hx hq0 hq1
  simpa [mul_inv_cancel₀ hz] using h

/--
[RW26, (55)] for every complex `x`.
-/
theorem summable_norm_eulerTerm (x q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    Summable (fun n => ‖eulerTerm x q n‖) := by
  have hL : 0 < ‖qPochhammer q q‖ := norm_pos_iff.mpr (qPochhammer_q_ne_zero q hq0 hq1)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (denom_lower q hq0 hq1)
  have ht : Tendsto (fun n : ℕ => ‖q‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) (1 / (2 * (‖x‖ + 1))) (by positivity)
  have hNle : ‖q‖ ^ N ≤ 1 / (2 * (‖x‖ + 1)) := by
    have h := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg (norm_nonneg q) N)] at h
    exact h.le
  have hkey : ‖x‖ * ‖q‖ ^ N ≤ 1 / 2 := by
    have hxnon : 0 ≤ ‖x‖ := norm_nonneg x
    have hdenpos : 0 < 2 * (‖x‖ + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hNle hxnon
    calc ‖x‖ * ‖q‖ ^ N ≤ ‖x‖ * (1 / (2 * (‖x‖ + 1))) := hmul
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ hdenpos]
          nlinarith
  have hkey' : ‖x‖ * ‖q‖ ^ (N + 1) ≤ 1 / 2 := by
    have hpowle : ‖q‖ ^ (N + 1) ≤ ‖q‖ ^ N := by
      rw [pow_succ]
      calc ‖q‖ ^ N * ‖q‖ ≤ ‖q‖ ^ N * 1 :=
            mul_le_mul_of_nonneg_left hq1.le (pow_nonneg (norm_nonneg q) N)
        _ = ‖q‖ ^ N := mul_one _
    calc ‖x‖ * ‖q‖ ^ (N + 1) ≤ ‖x‖ * ‖q‖ ^ N :=
          mul_le_mul_of_nonneg_left hpowle (norm_nonneg x)
      _ ≤ 1 / 2 := hkey
  rw [← summable_nat_add_iff (max (2 * N + 3) M)]
  refine Summable.of_nonneg_of_le
    (f := fun n => (2 / ‖qPochhammer q q‖) * (1/2 : ℝ) ^ n) ?_ ?_ ?_
  · intro n; positivity
  · intro n
    set k := n + max (2 * N + 3) M with hk
    have hMmax : M ≤ max (2 * N + 3) M := le_max_right _ _
    have hNmax : 2 * N + 3 ≤ max (2 * N + 3) M := le_max_left _ _
    have hmaxk : max (2 * N + 3) M ≤ k := by rw [hk]; exact Nat.le_add_left _ _
    have hkM : M ≤ k := hMmax.trans hmaxk
    have hkN : 2 * N + 3 ≤ k := hNmax.trans hmaxk
    have hden : ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q k‖ := hM k hkM
    rw [eulerTerm, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one]
    norm_num
    have hq_exp_le : ‖q‖ ^ (k * (k - 1) / 2) ≤ ‖q‖ ^ ((N + 1) * k) := by
      have hle : (N + 1) * k ≤ k * (k - 1) / 2 := by
        have h2 : 2 * (N + 1) ≤ k - 1 := by omega
        have h2k : 2 * (N + 1) * k ≤ (k - 1) * k := Nat.mul_le_mul_right k h2
        have hprod : k * (k - 1) = (k - 1) * k := by ring
        rw [hprod, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        nlinarith
      rw [show k * (k - 1) / 2 = (N + 1) * k + (k * (k - 1) / 2 - (N + 1) * k) by omega]
      rw [pow_add]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg q) ((N + 1) * k))
        (pow_le_one₀ (norm_nonneg q) hq1.le)
    have hnum_le : ‖q‖ ^ (k * (k - 1) / 2) * ‖x‖ ^ k ≤ (1/2 : ℝ) ^ k := by
      calc ‖q‖ ^ (k * (k - 1) / 2) * ‖x‖ ^ k ≤ ‖q‖ ^ ((N + 1) * k) * ‖x‖ ^ k :=
            mul_le_mul_of_nonneg_right hq_exp_le (pow_nonneg (norm_nonneg x) k)
        _ = (‖x‖ * ‖q‖ ^ (N + 1)) ^ k := by rw [mul_pow, pow_mul]; ring
        _ ≤ (1/2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hkey' k
    have hdpos : 0 < ‖qPochhammer q q‖ / 2 := by positivity
    calc ‖q‖ ^ (k * (k - 1) / 2) * ‖x‖ ^ k / ‖qPochhammerNat q q k‖
        ≤ ‖q‖ ^ (k * (k - 1) / 2) * ‖x‖ ^ k / (‖qPochhammer q q‖ / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (norm_nonneg q) _) (pow_nonneg (norm_nonneg x) _)) hdpos hden
      _ ≤ (1/2 : ℝ) ^ k / (‖qPochhammer q q‖ / 2) :=
          div_le_div_of_nonneg_right hnum_le hdpos.le
      _ = (2 / ‖qPochhammer q q‖) * ((1/2 : ℝ) ^ k) := by field_simp
      _ ≤ (2 / ‖qPochhammer q q‖) * ((1/2 : ℝ) ^ n) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : n ≤ k)
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ) < 1)).mul_left
      (2 / ‖qPochhammer q q‖)

private lemma eulerTerm_step (x q : ℂ) (n : ℕ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    q^(n+1) * eulerTerm x q (n+1) - x * (q^n * eulerTerm x q n) = eulerTerm x q (n+1) := by
  have hd1 : qPochhammerNat q q n ≠ 0 := qPochhammerNat_q_ne_zero q n hq0 hq1
  have hd2 : qPochhammerNat q q (n+1) ≠ 0 := qPochhammerNat_q_ne_zero q (n+1) hq0 hq1
  have hd : 1 - q * q^n ≠ 0 := by
    intro h; apply hd2; rw [qPochhammerNat_succ, h, mul_zero]
  simp only [eulerTerm]
  rw [qPochhammerNat_succ]
  have hsum1 : (n+1) * n / 2 = ∑ i ∈ Finset.range (n+1), i := by
    rw [Finset.sum_range_id]; simp
  have h1 : (n+1) * n / 2 = n * (n - 1) / 2 + n := by
    rw [hsum1, Finset.sum_range_succ, Finset.sum_range_id n]
  simp only [Nat.add_sub_cancel]
  rw [show q ^ ((n+1) * n / 2) = q ^ (n * (n - 1) / 2) * q ^ n by rw [← pow_add, h1]]
  field_simp [hd1, hd2]
  have hd' : 1 - q ^ n * q ≠ 0 := by simpa [mul_comm] using hd
  field_simp [hd']
  ring

private lemma eulerEntire_functional (x q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (∑' n, eulerTerm x q n) = (1 - x) * (∑' n, eulerTerm (q*x) q n) := by
  let e : ℕ → ℂ := fun n => eulerTerm x q n
  let d : ℕ → ℂ := fun n => q^n * e n
  have hsumE : Summable e := Summable.of_norm (summable_norm_eulerTerm x q hq0 hq1)
  have hsumD : Summable d := by
    have h : Summable (fun n => eulerTerm (q*x) q n) :=
      Summable.of_norm (summable_norm_eulerTerm (q*x) q hq0 hq1)
    convert h using 1
    ext n
    dsimp [d, e, eulerTerm]
    rw [mul_pow]
    ring
  have hE : HasSum e (∑' n, e n) := hsumE.hasSum
  have hD : HasSum d (∑' n, d n) := hsumD.hasSum
  have he0 : e 0 = 1 := by simp [e, eulerTerm, qPochhammerNat]
  have hd0 : d 0 = 1 := by simp [d, he0]
  have hshiftD : HasSum (fun n => d (n+1)) ((∑' n, d n) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hD
    simpa [hd0] using h
  have hxD : HasSum (fun n => x * d n) (x * ∑' n, d n) := hD.mul_left x
  have hsub : HasSum (fun n => d (n+1) - x * d n) (((∑' n, d n) - 1) - x * ∑' n, d n) :=
    hshiftD.sub hxD
  have hshiftE : HasSum (fun n => e (n+1)) ((∑' n, e n) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hE
    simpa [he0] using h
  have hpt : ∀ n, d (n+1) - x * d n = e (n+1) := by
    intro n
    dsimp [d, e]
    exact eulerTerm_step x q n hq0 hq1
  have hsame : HasSum (fun n => e (n+1)) (((∑' n, d n) - 1) - x * ∑' n, d n) :=
    hsub.congr_fun (fun n => (hpt n).symm)
  have heq := hshiftE.unique hsame
  dsimp [d, e] at heq ⊢
  have hDq : (∑' n, q ^ n * eulerTerm x q n) = ∑' n, eulerTerm (q*x) q n := by
    apply tsum_congr
    intro n
    simp only [eulerTerm]
    rw [mul_pow]
    ring
  rw [hDq] at heq
  linear_combination heq

private lemma differentiable_tsum_euler (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    Differentiable ℂ (fun x => ∑' n, eulerTerm x q n) := by
  have hL : 0 < ‖qPochhammer q q‖ := norm_pos_iff.mpr (qPochhammer_q_ne_zero q hq0 hq1)
  have ht : Tendsto (fun n : ℕ => ‖q‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1
  have hloc : HasSumLocallyUniformlyOn (fun n x => eulerTerm x q n)
      (fun x => ∑' n, eulerTerm x q n) (Set.univ : Set ℂ) := by
    apply hasSumLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simpa [hasSumUniformlyOn_iff_tendstoUniformlyOn] using
        (tendstoUniformlyOn_empty (F := fun (n : Finset ℕ) (x : ℂ) =>
          ∑ i ∈ n, eulerTerm x q i) (f := fun x : ℂ => ∑' n, eulerTerm x q n))
    · obtain ⟨x0, hx0K, -, hB⟩ := hK.exists_sSup_image_eq_and_ge hne
        (show ContinuousOn (fun x : ℂ => ‖x‖) K from by fun_prop)
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) (1 / (2 * (‖x0‖ + 1))) (by positivity)
      have hNle : ‖q‖ ^ N ≤ 1 / (2 * (‖x0‖ + 1)) := by
        have h := hN N le_rfl
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg (norm_nonneg q) N)] at h
        exact h.le
      have hkey : ‖x0‖ * ‖q‖ ^ N ≤ 1 / 2 := by
        have hxnon : 0 ≤ ‖x0‖ := norm_nonneg x0
        have hdenpos : 0 < 2 * (‖x0‖ + 1) := by positivity
        calc ‖x0‖ * ‖q‖ ^ N ≤ ‖x0‖ * (1 / (2 * (‖x0‖ + 1))) :=
              mul_le_mul_of_nonneg_left hNle hxnon
          _ ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ hdenpos]; nlinarith
      have hkey' : ‖x0‖ * ‖q‖ ^ (N+1) ≤ 1 / 2 := by
        have hpowle : ‖q‖ ^ (N+1) ≤ ‖q‖ ^ N := by
          rw [pow_succ]
          calc ‖q‖ ^ N * ‖q‖ ≤ ‖q‖ ^ N * 1 := mul_le_mul_of_nonneg_left hq1.le (pow_nonneg (norm_nonneg q) N)
            _ = ‖q‖ ^ N := mul_one _
        exact (mul_le_mul_of_nonneg_left hpowle (norm_nonneg x0)).trans hkey
      have hu : Summable fun n : ℕ => (2 / ‖qPochhammer q q‖) * (1/2 : ℝ) ^ n :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ) < 1)).mul_left _
      refine HasSumUniformlyOn.of_norm_le_summable_eventually (u := fun n => (2 / ‖qPochhammer q q‖) * (1/2 : ℝ) ^ n) hu ?_
      have hdenEv : ∀ᶠ n : ℕ in cofinite, ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q n‖ := by
        rw [Nat.cofinite_eq_atTop]; exact denom_lower q hq0 hq1
      have hge : ∀ᶠ n : ℕ in cofinite, 2 * N + 3 ≤ n := by
        rw [Nat.cofinite_eq_atTop]; exact eventually_ge_atTop _
      filter_upwards [hdenEv, hge] with n hn hNn x hx
      have hden : ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q n‖ := hn
      rw [eulerTerm, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one]
      norm_num
      have hq_exp_le : ‖q‖ ^ (n * (n - 1) / 2) ≤ ‖q‖ ^ ((N + 1) * n) := by
        have hle : (N + 1) * n ≤ n * (n - 1) / 2 := by
          have h2 : 2 * (N + 1) ≤ n - 1 := by omega
          have h2k : 2 * (N + 1) * n ≤ (n - 1) * n := Nat.mul_le_mul_right n h2
          have hprod : n * (n - 1) = (n - 1) * n := by ring
          rw [hprod, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
          nlinarith
        rw [show n * (n - 1) / 2 = (N + 1) * n + (n * (n - 1) / 2 - (N + 1) * n) by omega]
        rw [pow_add]
        exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg q) ((N + 1) * n))
          (pow_le_one₀ (norm_nonneg q) hq1.le)
      have hxle : ‖x‖ ≤ ‖x0‖ := hB x hx
      have hnum_le : ‖q‖ ^ (n * (n - 1) / 2) * ‖x‖ ^ n ≤ (1/2 : ℝ) ^ n := by
        calc ‖q‖ ^ (n * (n - 1) / 2) * ‖x‖ ^ n
            ≤ ‖q‖ ^ (n * (n - 1) / 2) * ‖x0‖ ^ n :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hxle n) (pow_nonneg (norm_nonneg q) _)
          _ ≤ ‖q‖ ^ ((N + 1) * n) * ‖x0‖ ^ n :=
              mul_le_mul_of_nonneg_right hq_exp_le (pow_nonneg (norm_nonneg x0) n)
          _ = (‖x0‖ * ‖q‖ ^ (N + 1)) ^ n := by rw [mul_pow, pow_mul]; ring
          _ ≤ (1/2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hkey' n
      have hdpos : 0 < ‖qPochhammer q q‖ / 2 := by positivity
      calc ‖q‖ ^ (n * (n - 1) / 2) * ‖x‖ ^ n / ‖qPochhammerNat q q n‖
          ≤ ‖q‖ ^ (n * (n - 1) / 2) * ‖x‖ ^ n / (‖qPochhammer q q‖ / 2) :=
            div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (norm_nonneg q) _) (pow_nonneg (norm_nonneg x) _)) hdpos hden
        _ ≤ (1/2 : ℝ) ^ n / (‖qPochhammer q q‖ / 2) :=
            div_le_div_of_nonneg_right hnum_le hdpos.le
        _ = (2 / ‖qPochhammer q q‖) * ((1/2 : ℝ) ^ n) := by field_simp
  have h' : TendstoLocallyUniformlyOn (fun n : Finset ℕ => fun x : ℂ =>
      ∑ i ∈ n, eulerTerm x q i) (fun x => ∑' n, eulerTerm x q n) atTop
      (Set.univ : Set ℂ) := hloc
  exact differentiableOn_univ.mp (h'.differentiableOn (Eventually.of_forall fun n => by
    refine DifferentiableOn.fun_sum ?_
    intro i hi
    simp only [eulerTerm]
    fun_prop) isOpen_univ)

/-- Euler's entire product series, with no `‖x‖ < 1` hypothesis. -/
theorem hasSum_euler (x q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    HasSum (eulerTerm x q) (qPochhammer x q) := by
  let E : ℂ → ℂ := fun y => ∑' n, eulerTerm y q n
  let P : ℂ → ℂ := fun y => qPochhammer y q
  have hEdiff : Differentiable ℂ E := differentiable_tsum_euler q hq0 hq1
  have hEdiffOn : DifferentiableOn ℂ E (Metric.ball (0:ℂ) 1) := hEdiff.differentiableOn
  have hPdiff : DifferentiableOn ℂ P (Metric.ball (0:ℂ) 1) :=
    (differentiable_qPochhammer_x q hq0 hq1).differentiableOn
  have hPd : Differentiable ℂ P := differentiable_qPochhammer_x q hq0 hq1
  have hPne : ∀ y ∈ Metric.ball (0:ℂ) 1, P y ≠ 0 := by
    intro y hy
    exact qPochhammer_ne_zero_of_norm_lt_one y q
      (by simpa [Metric.mem_ball, dist_zero_right] using hy) hq0 hq1
  have hHdiff : DifferentiableOn ℂ (fun y => E y / P y) (Metric.ball (0:ℂ) 1) :=
    hEdiffOn.div hPdiff hPne
  have hcont : ContinuousAt (fun y => E y / P y) 0 :=
    (hHdiff.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  have hE0 : E 0 = 1 := by
    dsimp [E]
    rw [tsum_eq_single 0]
    · simp [eulerTerm, qPochhammerNat]
    · intro b hb
      have h0 : (0:ℂ)^b = 0 := zero_pow hb
      simp [eulerTerm, h0]
  have hP0 : P 0 = 1 := by dsimp [P]; exact qPochhammer_zero q
  have hH0 : E 0 / P 0 = 1 := by rw [hE0, hP0, div_one]
  have hHstep : ∀ y, ‖y‖ < 1 → E (q*y) / P (q*y) = E y / P y := by
    intro y hy
    have hy1 : y ≠ 1 := by intro h; rw [h] at hy; norm_num at hy
    have h1y : 1 - y ≠ 0 := sub_ne_zero.mpr hy1.symm
    have hFE := eulerEntire_functional y q hq0 hq1
    have hEqy : E (q*y) = E y / (1 - y) := by
      dsimp [E]
      rw [hFE]
      field_simp [h1y]
    have hP := qPochhammer_shift_nat y q 1 hq0 hq1
    have hPy : P (q*y) = P y / (1 - y) := by
      have hP' : P y = (1 - y) * P (q*y) := by
        dsimp [P]; simpa [qPochhammerNat, mul_comm] using hP
      rw [hP']
      field_simp [h1y]
    rw [hEqy, hPy]
    field_simp [h1y]
  have hiter : ∀ y, ‖y‖ < 1 → ∀ n : ℕ, E (q^n * y) / P (q^n * y) = E y / P y := by
    intro y hy n
    induction n with
    | zero => simp
    | succ n ih =>
        have hball : ‖q^n * y‖ < 1 := by
          have h1 : ‖q‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg q) hq1.le
          rw [norm_mul, norm_pow]
          calc ‖q‖ ^ n * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
            _ = ‖y‖ := one_mul _
            _ < 1 := hy
        calc E (q ^ (n+1) * y) / P (q ^ (n+1) * y)
            = E (q * (q^n * y)) / P (q * (q^n * y)) := by rw [pow_succ]; ring_nf
          _ = E (q^n * y) / P (q^n * y) := hHstep (q^n * y) hball
          _ = E y / P y := ih
  have hball_eq : ∀ y, ‖y‖ < 1 → E y = P y := by
    intro y hy
    have hHx : E y / P y = 1 := by
      have hlim : Tendsto (fun n => q^n * y) atTop (𝓝 0) := by
        have hqpow : Tendsto (fun n : ℕ => q^n) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1
        simpa [mul_comm] using hqpow.mul_const y
      have htend : Tendsto (fun n => E (q^n*y) / P (q^n*y)) atTop (𝓝 (E 0 / P 0)) :=
        hcont.tendsto.comp hlim
      have htend_const : Tendsto (fun _ : ℕ => E y / P y) atTop (𝓝 (E 0 / P 0)) :=
        htend.congr' (Eventually.of_forall fun n => hiter y hy n)
      have hEq := tendsto_nhds_unique tendsto_const_nhds htend_const
      rw [hH0] at hEq
      exact hEq
    rw [div_eq_one_iff_eq] at hHx
    · exact hHx
    · exact hPne y (by simpa [Metric.mem_ball, dist_zero_right] using hy)
  have hEP : E x = P x := by
    have hEana : AnalyticOnNhd ℂ E univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr hEdiff
    have hPana : AnalyticOnNhd ℂ P univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr hPd
    have hevent : E =ᶠ[𝓝 (0:ℂ)] P := by
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) one_pos] with y hy
      exact hball_eq y (by simpa [Metric.mem_ball, dist_zero_right] using hy)
    have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hEana hPana
      isPreconnected_univ (mem_univ 0) hevent
    exact hEqOn (mem_univ x)
  have hEsum : HasSum (fun n => eulerTerm x q n) (E x) :=
    (Summable.of_norm (summable_norm_eulerTerm x q hq0 hq1)).hasSum
  rw [show E x = qPochhammer x q by simpa [P] using hEP] at hEsum
  exact hEsum

/-- Absolute convergence for [RW26, (58)] terminating numerator cases. -/
theorem summable_norm_qBinomialTerm (a x q : ℂ)
    (hx : ‖x‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    Summable (fun n => ‖qBinomialTerm a x q n‖) := by
  have hL : 0 < ‖qPochhammer q q‖ := norm_pos_iff.mpr (qPochhammer_q_ne_zero q hq0 hq1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (denom_lower q hq0 hq1)
  have hA : ∀ᶠ n : ℕ in atTop, ‖qPochhammerNat a q n‖ ≤ ‖qPochhammer a q‖ + 1 :=
    Filter.Tendsto.eventually_le_const (by linarith)
      (tendsto_qPochhammerNat a q hq0 hq1).norm
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hA
  rw [← summable_nat_add_iff (max N K)]
  refine Summable.of_nonneg_of_le
    (f := fun n => ((2 / ‖qPochhammer q q‖) * (‖qPochhammer a q‖ + 1) * ‖x‖ ^ (max N K)) * ‖x‖ ^ n) ?_ ?_ ?_
  · intro n; positivity
  · intro n
    set k := n + max N K with hk
    have hkN : N ≤ k := by
      have : N ≤ max N K := le_max_left _ _
      omega
    have hkK : K ≤ k := by
      have : K ≤ max N K := le_max_right _ _
      omega
    have hden : ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q k‖ := hN k hkN
    have hnumA : ‖qPochhammerNat a q k‖ ≤ ‖qPochhammer a q‖ + 1 := hK k hkK
    rw [qBinomialTerm, norm_div, norm_mul, norm_pow]
    have hdpos : 0 < ‖qPochhammer q q‖ / 2 := by positivity
    have hC : 0 ≤ ‖qPochhammer a q‖ + 1 := by positivity
    calc ‖qPochhammerNat a q k‖ * ‖x‖ ^ k / ‖qPochhammerNat q q k‖
        ≤ (‖qPochhammer a q‖ + 1) * ‖x‖ ^ k / ‖qPochhammerNat q q k‖ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnumA (pow_nonneg (norm_nonneg x) k)) (norm_nonneg _)
      _ ≤ (‖qPochhammer a q‖ + 1) * ‖x‖ ^ k / (‖qPochhammer q q‖ / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hC (pow_nonneg (norm_nonneg x) k)) hdpos hden
      _ = ((2 / ‖qPochhammer q q‖) * (‖qPochhammer a q‖ + 1) * ‖x‖ ^ (max N K)) * ‖x‖ ^ n := by
          rw [hk, pow_add]
          ring
  · exact (summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left _

private lemma qBinomial_step (a x q : ℂ) (n : ℕ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qBinomialTerm a x q (n+1) - x * qBinomialTerm a x q n =
      q^(n+1) * qBinomialTerm a x q (n+1) - a*x * (q^n * qBinomialTerm a x q n) := by
  have hd1 : qPochhammerNat q q n ≠ 0 := qPochhammerNat_q_ne_zero q n hq0 hq1
  have hd2 : qPochhammerNat q q (n+1) ≠ 0 := qPochhammerNat_q_ne_zero q (n+1) hq0 hq1
  have hd : 1 - q * q ^ n ≠ 0 := by
    intro h; apply hd2; rw [qPochhammerNat_succ, h, mul_zero]
  simp only [qBinomialTerm]
  rw [qPochhammerNat_succ, qPochhammerNat_succ]
  field_simp [hd1, hd2]
  have hd' : 1 - q ^ n * q ≠ 0 := by simpa [mul_comm] using hd
  field_simp [hd']
  ring

private lemma qBinomial_functional (a x q : ℂ) (hx : ‖x‖ < 1)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (1 - x) * (∑' n, qBinomialTerm a x q n) =
      (1 - a*x) * (∑' n, qBinomialTerm a (q*x) q n) := by
  let b : ℕ → ℂ := fun n => qBinomialTerm a x q n
  let d : ℕ → ℂ := fun n => q ^ n * b n
  have hsumB : Summable b := Summable.of_norm (summable_norm_qBinomialTerm a x q hx hq0 hq1)
  have hsumD : Summable d := by
    have h : Summable (fun n => qBinomialTerm a (q*x) q n) :=
      Summable.of_norm (summable_norm_qBinomialTerm a (q*x) q (by rw [norm_mul]; nlinarith [norm_nonneg q, norm_nonneg x]) hq0 hq1)
    convert h using 1
    ext n
    dsimp [d, b, qBinomialTerm]
    rw [mul_pow]; ring
  have hB : HasSum b (∑' n, b n) := hsumB.hasSum
  have hD : HasSum d (∑' n, d n) := hsumD.hasSum
  have hb0 : b 0 = 1 := by simp [b, qBinomialTerm, qPochhammerNat]
  have hd0 : d 0 = 1 := by simp [d, hb0]
  have hshiftB : HasSum (fun n => b (n+1)) ((∑' n, b n) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hB
    simpa [hb0] using h
  have hxB : HasSum (fun n => x * b n) (x * ∑' n, b n) := hB.mul_left x
  have hleft : HasSum (fun n => b (n+1) - x * b n) (((∑' n, b n) - 1) - x * ∑' n, b n) :=
    hshiftB.sub hxB
  have hshiftD : HasSum (fun n => d (n+1)) ((∑' n, d n) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hD
    simpa [hd0] using h
  have haxD : HasSum (fun n => a*x * d n) (a*x * ∑' n, d n) := hD.mul_left (a*x)
  have hright : HasSum (fun n => d (n+1) - a*x * d n) (((∑' n, d n) - 1) - a*x * ∑' n, d n) :=
    hshiftD.sub haxD
  have hpt : ∀ n, b (n+1) - x * b n = d (n+1) - a*x * d n := by
    intro n
    dsimp [d, b]
    exact qBinomial_step a x q n hq0 hq1
  have hsame : HasSum (fun n => b (n+1) - x * b n) (((∑' n, d n) - 1) - a*x * ∑' n, d n) :=
    hright.congr_fun (fun n => hpt n)
  have heq := hleft.unique hsame
  dsimp [d, b] at heq ⊢
  have hDq : (∑' n, q ^ n * qBinomialTerm a x q n) = ∑' n, qBinomialTerm a (q*x) q n := by
    apply tsum_congr
    intro n
    simp only [qBinomialTerm]
    rw [mul_pow]; ring
  rw [hDq] at heq
  linear_combination heq

private lemma differentiableOn_tsum_qBinomial (a q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    DifferentiableOn ℂ (fun x => ∑' n, qBinomialTerm a x q n) (Metric.ball (0:ℂ) 1) := by
  have hL : 0 < ‖qPochhammer q q‖ := norm_pos_iff.mpr (qPochhammer_q_ne_zero q hq0 hq1)
  have hbdd : Bornology.IsBounded (Set.range fun n => qPochhammerNat a q n) :=
    Metric.isBounded_range_of_tendsto _ (tendsto_qPochhammerNat a q hq0 hq1)
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  have hloc : HasSumLocallyUniformlyOn (fun n x => qBinomialTerm a x q n)
      (fun x => ∑' n, qBinomialTerm a x q n) (Metric.ball (0:ℂ) 1) := by
    apply hasSumLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simpa [hasSumUniformlyOn_iff_tendstoUniformlyOn] using
        (tendstoUniformlyOn_empty (F := fun (n : Finset ℕ) (x : ℂ) =>
          ∑ i ∈ n, qBinomialTerm a x q i) (f := fun x : ℂ => ∑' n, qBinomialTerm a x q n))
    · obtain ⟨x0, hx0K, -, hB⟩ := hK.exists_sSup_image_eq_and_ge hne
        (show ContinuousOn (fun x : ℂ => ‖x‖) K from by fun_prop)
      have hr : ‖x0‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hKsub hx0K
      have hu : Summable fun n : ℕ => (2*C / ‖qPochhammer q q‖) * ‖x0‖ ^ n :=
        (summable_geometric_of_lt_one (norm_nonneg x0) hr).mul_left _
      refine HasSumUniformlyOn.of_norm_le_summable_eventually (u := fun n => (2*C / ‖qPochhammer q q‖) * ‖x0‖ ^ n) hu ?_
      have hdenEv : ∀ᶠ n : ℕ in cofinite, ‖qPochhammer q q‖ / 2 ≤ ‖qPochhammerNat q q n‖ := by
        rw [Nat.cofinite_eq_atTop]; exact denom_lower q hq0 hq1
      filter_upwards [hdenEv] with n hn x hx
      rw [qBinomialTerm, norm_div, norm_mul, norm_pow]
      have hnumA : ‖qPochhammerNat a q n‖ ≤ C := hC _ (Set.mem_range_self n)
      have hxnorm : ‖x‖ ≤ ‖x0‖ := hB x hx
      have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (Set.mem_range_self 0))
      have hnum : ‖qPochhammerNat a q n‖ * ‖x‖ ^ n ≤ C * ‖x0‖ ^ n := by
        calc ‖qPochhammerNat a q n‖ * ‖x‖ ^ n ≤ C * ‖x‖ ^ n :=
              mul_le_mul_of_nonneg_right hnumA (pow_nonneg (norm_nonneg x) n)
          _ ≤ C * ‖x0‖ ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hxnorm n) hC0
      have hdpos : 0 < ‖qPochhammer q q‖ / 2 := by positivity
      calc ‖qPochhammerNat a q n‖ * ‖x‖ ^ n / ‖qPochhammerNat q q n‖
          ≤ C * ‖x0‖ ^ n / ‖qPochhammerNat q q n‖ :=
            div_le_div_of_nonneg_right hnum (norm_nonneg _)
        _ ≤ C * ‖x0‖ ^ n / (‖qPochhammer q q‖ / 2) :=
            div_le_div_of_nonneg_left (mul_nonneg hC0 (pow_nonneg (norm_nonneg x0) n)) hdpos hn
        _ = ((2*C) / ‖qPochhammer q q‖) * ‖x0‖ ^ n := by field_simp
  have h' : TendstoLocallyUniformlyOn (fun n : Finset ℕ => fun x : ℂ =>
      ∑ i ∈ n, qBinomialTerm a x q i) (fun x => ∑' n, qBinomialTerm a x q n) atTop
      (Metric.ball (0:ℂ) 1) := hloc
  exact h'.differentiableOn (Eventually.of_forall fun n => by
    refine DifferentiableOn.fun_sum ?_
    intro i hi
    simp only [qBinomialTerm]
    fun_prop) Metric.isOpen_ball



private lemma qBinomial_tsum_mul (a x q : ℂ) (hx : ‖x‖ < 1)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (∑' n, qBinomialTerm a x q n) * qPochhammer x q = qPochhammer (a*x) q := by
  let B : ℂ → ℂ := fun y => ∑' n, qBinomialTerm a y q n
  let P : ℂ → ℂ := fun y => qPochhammer y q
  let D : ℂ → ℂ := fun y => qPochhammer (a*y) q
  let E : ℂ → ℂ := fun y => B y * P y - D y
  have hBdiff : DifferentiableOn ℂ B (Metric.ball (0:ℂ) 1) := by
    dsimp [B]
    exact differentiableOn_tsum_qBinomial a q hq0 hq1
  have hPdiff : DifferentiableOn ℂ P (Metric.ball (0:ℂ) 1) :=
    (differentiable_qPochhammer_x q hq0 hq1).differentiableOn
  have hDdiff : DifferentiableOn ℂ D (Metric.ball (0:ℂ) 1) := by
    dsimp [D]
    exact ((differentiable_qPochhammer_x q hq0 hq1).comp
      (by fun_prop : Differentiable ℂ (fun y : ℂ => a*y))).differentiableOn
  have hEdiff : DifferentiableOn ℂ E (Metric.ball (0:ℂ) 1) :=
    (hBdiff.mul hPdiff).sub hDdiff
  have hEcont : ContinuousAt E 0 :=
    (hEdiff.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  have hB0 : B 0 = 1 := by
    dsimp [B]
    rw [tsum_eq_single 0]
    · simp [qBinomialTerm, qPochhammerNat]
    · intro b hb
      have h0 : (0:ℂ)^b = 0 := zero_pow hb
      simp [qBinomialTerm, h0]
  have hE0 : E 0 = 0 := by
    dsimp [E, P, D]
    simp [hB0, qPochhammer_zero]
  have hEfun : ∀ y, ‖y‖ < 1 → E y = (1 - a*y) * E (q*y) := by
    intro y hy
    have hBfun := qBinomial_functional a y q hy hq0 hq1
    have hPshift := qPochhammer_shift_nat y q 1 hq0 hq1
    have hP' : P y = (1 - y) * P (q*y) := by
      dsimp [P]; simpa [qPochhammerNat, mul_comm] using hPshift
    have hDshift := qPochhammer_shift_nat (a*y) q 1 hq0 hq1
    have hD' : D y = (1 - a*y) * D (q*y) := by
      dsimp [D]
      rw [hDshift]
      have harg : a * y * q ^ 1 = a * (q * y) := by ring
      rw [harg]
      simp [qPochhammerNat]
    dsimp [E]
    calc B y * P y - D y
        = B y * ((1-y) * P (q*y)) - D y := by rw [hP']
      _ = ((1-y) * B y) * P (q*y) - D y := by ring
      _ = ((1-a*y) * B (q*y)) * P (q*y) - D y := by
          have : (1-y) * B y = (1-a*y) * B (q*y) := by
            dsimp [B]; exact hBfun
          rw [this]
      _ = (1-a*y) * (B (q*y) * P (q*y)) - (1-a*y) * D (q*y) := by rw [hD']; ring
      _ = (1-a*y) * (B (q*y) * P (q*y) - D (q*y)) := by rw [mul_sub]
  have hiter : ∀ n : ℕ, E x = qPochhammerNat (a*x) q n * E (q^n * x) := by
    intro n
    induction n with
    | zero => simp [qPochhammerNat]
    | succ n ih =>
        have hball : ‖q^n * x‖ < 1 := by
          have h1 : ‖q‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg q) hq1.le
          rw [norm_mul, norm_pow]
          calc ‖q‖ ^ n * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
            _ = ‖x‖ := one_mul _
            _ < 1 := hx
        rw [ih, hEfun (q^n * x) hball, qPochhammerNat_succ]
        have harg : q * (q^n * x) = q^(n+1) * x := by rw [pow_succ]; ring
        rw [harg]
        ring
  have hElim : Tendsto (fun n => E (q^n * x)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => q^n * x) atTop (𝓝 0) := by
      have hqpow : Tendsto (fun n : ℕ => q^n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1
      simpa [mul_comm] using hqpow.mul_const x
    have := hEcont.tendsto.comp hlim
    simpa [hE0, Function.comp_def] using this
  have hA : Tendsto (fun n => qPochhammerNat (a*x) q n) atTop (𝓝 (qPochhammer (a*x) q)) :=
    tendsto_qPochhammerNat (a*x) q hq0 hq1
  have hprod : Tendsto (fun n => qPochhammerNat (a*x) q n * E (q^n*x)) atTop (𝓝 0) := by
    have := hA.mul hElim
    simpa using this
  have hconst : Tendsto (fun _ : ℕ => E x) atTop (𝓝 0) :=
    hprod.congr' (Eventually.of_forall fun n => (hiter n).symm)
  have hEx : E x = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  have hBP : B x * P x = qPochhammer (a*x) q := by
    have := sub_eq_zero.mp hEx
    simpa [E, D] using this
  exact hBP


/-- [RW26, (58)] multiplicative form first. -/
theorem hasSum_qBinomial_mul (a x q : ℂ)
    (hx : ‖x‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    HasSum (fun n => qPochhammer x q * qBinomialTerm a x q n)
      (qPochhammer (a * x) q) := by
  have hsum : HasSum (fun n => qBinomialTerm a x q n) (∑' n, qBinomialTerm a x q n) :=
    (Summable.of_norm (summable_norm_qBinomialTerm a x q hx hq0 hq1)).hasSum
  have h := hsum.mul_left (qPochhammer x q)
  have hmul := qBinomial_tsum_mul a x q hx hq0 hq1
  rw [mul_comm] at hmul
  rw [hmul] at h
  exact h

/-- [RW26, (58)] quotient form with its denominator displayed as a hypothesis. -/
theorem hasSum_qBinomial (a x q : ℂ)
    (hx : ‖x‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hd : qPochhammer x q ≠ 0) :
    HasSum (qBinomialTerm a x q) (qPochhammer (a * x) q / qPochhammer x q) := by
  have hmul := qBinomial_tsum_mul a x q hx hq0 hq1
  have hB : (∑' n, qBinomialTerm a x q n) = qPochhammer (a * x) q / qPochhammer x q := by
    rw [← hmul]
    field_simp [hd]
  have hsum : HasSum (fun n => qBinomialTerm a x q n) (∑' n, qBinomialTerm a x q n) :=
    (Summable.of_norm (summable_norm_qBinomialTerm a x q hx hq0 hq1)).hasSum
  rw [hB] at hsum
  exact hsum

/-- Absolute convergence for [RW26, (59)] all `ℤ`. -/
theorem summable_norm_jacobiTripleTerm (x q : ℂ)
    (hx : x ≠ 0) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    Summable (fun k : ℤ => ‖jacobiTripleTerm x q k‖) := by
  have summable_raw_euler_aux (a q : ℂ)
      (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
      Summable (fun n : ℕ => ‖q ^ (n * (n - 1) / 2) * a ^ n‖) := by
    obtain ⟨C, hC⟩ := ((tendsto_qPochhammerNat q q hq0 hq1).norm).bddAbove_range
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_norm_eulerTerm a q hq0 hq1).mul_right C)
    have hd := qPochhammerNat_q_ne_zero q n hq0 hq1
    have heq : (-1 : ℂ) ^ n * q ^ (n * (n - 1) / 2) * a ^ n =
        eulerTerm a q n * qPochhammerNat q q n := by
      rw [eulerTerm, div_mul_cancel₀ _ hd]
    have heqnorm := congrArg norm heq
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at heqnorm
    rw [norm_mul, norm_pow, norm_pow, heqnorm]
    exact mul_le_mul_of_nonneg_left (hC (Set.mem_range_self n)) (norm_nonneg _)
  apply Summable.of_nat_of_neg
  · apply (summable_raw_euler_aux (q * x) q hq0 hq1).congr
    intro n
    have hsum1 : (n+1) * n / 2 = ∑ i ∈ Finset.range (n+1), i := by
      rw [Finset.sum_range_id]; simp
    have htri : n * (n+1) / 2 = n * (n - 1) / 2 + n := by
      rw [mul_comm n (n+1), hsum1, Finset.sum_range_succ, Finset.sum_range_id n]
    have he : (n : ℤ) * ((n : ℤ) + 1) / 2 = ((n * (n + 1) / 2 : ℕ) : ℤ) := by
      push_cast
      rfl
    simp only [jacobiTripleTerm, norm_mul, zpow_natCast, he,
      norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, htri, pow_add, mul_pow]
    ring
  · apply (summable_raw_euler_aux x⁻¹ q hq0 hq1).congr
    intro n
    have hnum : (-(n : ℤ)) * (-(n : ℤ) + 1) = ((n * (n - 1) : ℕ) : ℤ) := by
      cases n with
      | zero => simp
      | succ n => simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring
    have he : (-(n : ℤ)) * (-(n : ℤ) + 1) / 2 = ((n * (n - 1) / 2 : ℕ) : ℤ) := by
      rw [hnum, Int.natCast_div]
      norm_num
    simp only [jacobiTripleTerm, norm_mul, zpow_natCast, he,
      norm_pow, norm_neg, norm_one, one_pow, inv_one, one_mul, norm_inv, zpow_neg, inv_pow]

/-- [RW26, (59)] `q*x`, inverse `x` and diagonal factors in that order. -/
theorem hasSum_jacobiTriple (x q : ℂ)
    (hx : x ≠ 0) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    HasSum (jacobiTripleTerm x q)
      (qPochhammer (q * x) q * qPochhammer x⁻¹ q * qPochhammer q q) := by
  have finite_jacobi_succ (x q : ℂ) (hx : x ≠ 0) (hq : q ≠ 0) (k : ℤ) :
      jacobiTripleTerm x q (k+1) = -(q ^ (k+1) * x) * jacobiTripleTerm x q k := by
    have he : (k+1)*(k+1+1)/2 = k*(k+1)/2 + (k+1) := by
      rw [show (k+1)*(k+1+1) = k*(k+1)+(k+1)*2 by ring,
        Int.add_mul_ediv_right _ _ (by norm_num)]
    simp only [jacobiTripleTerm, he]
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add₀ hq, zpow_add₀ hx]
    simp only [zpow_one, neg_mul]
    ring

  have finite_jacobi_neg_succ (x q : ℂ) (hx : x ≠ 0) (hq : q ≠ 0) (n : ℕ) :
      jacobiTripleTerm x q (-(n+1 : ℤ)) =
        -(q^n*x⁻¹) * jacobiTripleTerm x q (-(n : ℤ)) := by
    have h := finite_jacobi_succ x q hx hq (-(n+1 : ℤ))
    have hk : -(n+1 : ℤ)+1 = -(n:ℤ) := by omega
    rw [hk] at h
    have hz : q ^ (-(n:ℤ)) * q^n = 1 := by
      rw [← zpow_natCast q n, ← zpow_add₀ hq]
      simp
    have hm : -(q^n*x⁻¹) * -(q^(-(n:ℤ))*x) = 1 := by
      calc _ = (q^(-(n:ℤ))*q^n)*(x*x⁻¹) := by ring
           _ = 1 := by rw [hz, mul_inv_cancel₀ hx, mul_one]
    rw [h, ← mul_assoc, hm, one_mul]

  have finite_reflect_half (x q : ℂ) (hx : x ≠ 0) (hq : q ≠ 0) (n : ℕ) :
      jacobiTripleTerm x q (-(n:ℤ)) *
        qPochhammerNat (q ^ (1-(n:ℤ)) * x) q n = qPochhammerNat x⁻¹ q n := by
    induction n with
    | zero => simp [qPochhammerNat, jacobiTripleTerm]
    | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one]
      rw [finite_jacobi_neg_succ x q hx hq]
      have hex : 1-((n:ℤ)+1) = -(n:ℤ) := by omega
      rw [hex]
      have hp := qPochhammerNat_add (q ^ (-(n:ℤ))*x) q 1 n
      have harg : (q ^ (-(n:ℤ))*x)*q^1 = q^(1-(n:ℤ))*x := by
        calc _ = (q^(-(n:ℤ))*q^(1:ℤ))*x := by simp only [pow_one, zpow_one]; ring
             _ = _ := by rw [← zpow_add₀ hq]; congr 2; omega
      rw [harg] at hp
      rw [Nat.add_comm 1 n] at hp
      rw [hp]
      have hone : qPochhammerNat (q^(-(n:ℤ))*x) q 1 = 1-q^(-(n:ℤ))*x := by
        simp [qPochhammerNat]
      rw [hone]
      have hz : q^n*q^(-(n:ℤ)) = 1 := by
        rw [← zpow_natCast q n, ← zpow_add₀ hq]; simp
      have hm : -(q^n*x⁻¹)*(1-q^(-(n:ℤ))*x) = 1-x⁻¹*q^n := by
        calc _ = (q^n*q^(-(n:ℤ)))*(x*x⁻¹)-x⁻¹*q^n := by ring
             _ = _ := by rw [hz, mul_inv_cancel₀ hx]; ring
      calc -(q^n*x⁻¹)*jacobiTripleTerm x q (-(n:ℤ))*
            ((1-q^(-(n:ℤ))*x)*qPochhammerNat (q^(1-(n:ℤ))*x) q n)
          = (jacobiTripleTerm x q (-(n:ℤ))*qPochhammerNat (q^(1-(n:ℤ))*x) q n)*
              (-(q^n*x⁻¹)*(1-q^(-(n:ℤ))*x)) := by ring
        _ = qPochhammerNat x⁻¹ q n * (1-x⁻¹*q^n) := by rw [ih, hm]
        _ = _ := (qPochhammerNat_succ x⁻¹ q n).symm

  have finite_terminating_qBinomial (M : ℕ) (y q : ℂ)
      (hy : ‖y‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
      (∑ n ∈ Finset.range (M+1), qBinomialTerm (q^(-(M:ℤ))) y q n) =
        qPochhammerNat (q^(-(M:ℤ))*y) q M := by
    have hq : q ≠ 0 := norm_pos_iff.mp hq0
    have hz : q^(-(M:ℤ))*q^M = 1 := by
      rw [← zpow_natCast q M, ← zpow_add₀ hq]; simp
    have hvan : ∀ n ∉ Finset.range (M+1), qBinomialTerm (q^(-(M:ℤ))) y q n = 0 := by
      intro n hn
      have hnM : M < n := by simpa using hn
      have hp : qPochhammerNat (q^(-(M:ℤ))) q n = 0 := by
        apply (qPochhammerNat_eq_zero_iff _ _ _).mpr
        exact ⟨M, Finset.mem_range.mpr hnM, hz⟩
      rw [qBinomialTerm, hp]
      simp
    have hsum := hasSum_qBinomial (q^(-(M:ℤ))) y q hy hq0 hq1
      (qPochhammer_ne_zero_of_norm_lt_one y q hy hq0 hq1)
    have heq := hsum.unique (hasSum_sum_of_ne_finset_zero hvan)
    have hp := qPochhammer_shift_nat (q^(-(M:ℤ))*y) q M hq0 hq1
    have harg : q^(-(M:ℤ))*y*q^M = y := by
      calc _ = (q^(-(M:ℤ))*q^M)*y := by ring
           _ = y := by rw [hz, one_mul]
    rw [harg] at hp
    rw [hp] at heq
    simpa [qPochhammer_ne_zero_of_norm_lt_one y q hy hq0 hq1] using heq.symm

  have finite_terminating_term_cleared (N n : ℕ) (x q : ℂ)
      (hx : x ≠ 0) (hq : q ≠ 0) (hn : n ≤ 2*N) :
      jacobiTripleTerm x q (-(N:ℤ)) * qPochhammerNat (q^(-((2*N:ℕ):ℤ))) q n *
          (q^(N+1)*x)^n * qPochhammerNat q q (2*N-n) =
        jacobiTripleTerm x q ((n:ℤ)-(N:ℤ)) * qPochhammerNat q q (2*N) := by
    induction n with
    | zero => simp [qPochhammerNat_zero]
    | succ n ih =>
      have hn' : n ≤ 2*N := by omega
      have hs : 2*N-n = (2*N-(n+1))+1 := by omega
      have hpow1 : q^(-((2*N:ℕ):ℤ))*q^n*q^(N+1) = q^((n:ℤ)-(N:ℤ)+1) := by
        simp only [← zpow_natCast]
        rw [← zpow_add₀ hq, ← zpow_add₀ hq]
        congr 1
        push_cast
        ring
      have hpow2 : q^((n:ℤ)-(N:ℤ)+1)*q^(2*N-n) = q^(N+1) := by
        simp only [← zpow_natCast]
        rw [← zpow_add₀ hq]
        congr 1
        have hcast : ((2*N-n:ℕ):ℤ) = 2*(N:ℤ)-(n:ℤ) := by omega
        rw [hcast]
        push_cast
        ring
      have hfac : (1-q^(-((2*N:ℕ):ℤ))*q^n)*(q^(N+1)*x) =
          -(q^((n:ℤ)-(N:ℤ)+1)*x)*(1-q^(2*N-n)) := by
        calc _ = q^(N+1)*x-(q^(-((2*N:ℕ):ℤ))*q^n*q^(N+1))*x := by ring
             _ = -(q^((n:ℤ)-(N:ℤ)+1)*x)+(q^((n:ℤ)-(N:ℤ)+1)*q^(2*N-n))*x := by
               rw [hpow1, hpow2]; ring
             _ = _ := by ring
      have hd : qPochhammerNat q q (2*N-n) =
          qPochhammerNat q q (2*N-(n+1))*(1-q^(2*N-n)) := by
        conv_lhs => rw [hs, qPochhammerNat_succ]
        rw [← pow_succ', ← hs]
      rw [qPochhammerNat_succ, pow_succ]
      calc jacobiTripleTerm x q (-(N:ℤ)) *
            (qPochhammerNat (q^(-((2*N:ℕ):ℤ))) q n*(1-q^(-((2*N:ℕ):ℤ))*q^n)) *
            ((q^(N+1)*x)^n*(q^(N+1)*x)) * qPochhammerNat q q (2*N-(n+1))
          = jacobiTripleTerm x q (-(N:ℤ))*qPochhammerNat (q^(-((2*N:ℕ):ℤ))) q n *
              (q^(N+1)*x)^n * (((1-q^(-((2*N:ℕ):ℤ))*q^n)*(q^(N+1)*x))*
              qPochhammerNat q q (2*N-(n+1))) := by ring
        _ = -(q^((n:ℤ)-(N:ℤ)+1)*x) *
            (jacobiTripleTerm x q (-(N:ℤ))*qPochhammerNat (q^(-((2*N:ℕ):ℤ))) q n *
              (q^(N+1)*x)^n*qPochhammerNat q q (2*N-n)) := by rw [hfac, hd]; ring
        _ = -(q^((n:ℤ)-(N:ℤ)+1)*x) *
            (jacobiTripleTerm x q ((n:ℤ)-(N:ℤ))*qPochhammerNat q q (2*N)) := by rw [ih hn']
        _ = _ := by
          rw [show ((n+1:ℕ):ℤ)-(N:ℤ) = (n:ℤ)-(N:ℤ)+1 by omega,
            finite_jacobi_succ x q hx hq]
          ring

  have finite_terminating_term (N n : ℕ) (x q : ℂ)
      (hx : x ≠ 0) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hn : n ≤ 2*N) :
      jacobiTripleTerm x q (-(N:ℤ)) *
          qBinomialTerm (q^(-((2*N:ℕ):ℤ))) (q^(N+1)*x) q n =
        jacobiTripleTerm x q ((n:ℤ)-(N:ℤ)) * qPochhammerNat q q (2*N) /
          (qPochhammerNat q q n * qPochhammerNat q q (2*N-n)) := by
    have hd1 := qPochhammerNat_q_ne_zero q n hq0 hq1
    have hd2 := qPochhammerNat_q_ne_zero q (2*N-n) hq0 hq1
    have h := finite_terminating_term_cleared N n x q hx (norm_pos_iff.mp hq0) hn
    unfold qBinomialTerm
    field_simp [hd1, hd2]
    linear_combination h

  have finite_jacobi_range (N : ℕ) (x q : ℂ)
      (hx : x ≠ 0) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
      (hy : ‖q^(N+1)*x‖ < 1) :
      (∑ n ∈ Finset.range (2*N+1),
        jacobiTripleTerm x q ((n:ℤ)-(N:ℤ)) * qPochhammerNat q q (2*N) /
          (qPochhammerNat q q n * qPochhammerNat q q (2*N-n))) =
        qPochhammerNat (q*x) q N * qPochhammerNat x⁻¹ q N := by
    have hq : q ≠ 0 := norm_pos_iff.mp hq0
    have harg : q^(-((2*N:ℕ):ℤ))*(q^(N+1)*x) = q^(1-(N:ℤ))*x := by
      calc _ = (q^(-((2*N:ℕ):ℤ))*q^(N+1))*x := by ring
           _ = _ := by
             rw [← zpow_natCast q (N+1), ← zpow_add₀ hq]
             congr 2
             push_cast
             ring
    have harg2 : (q^(1-(N:ℤ))*x)*q^N = q*x := by
      calc _ = (q^(1-(N:ℤ))*q^N)*x := by ring
           _ = _ := by rw [← zpow_natCast q N, ← zpow_add₀ hq]; simp
    calc (∑ n ∈ Finset.range (2*N+1),
          jacobiTripleTerm x q ((n:ℤ)-(N:ℤ)) * qPochhammerNat q q (2*N) /
            (qPochhammerNat q q n * qPochhammerNat q q (2*N-n)))
        = ∑ n ∈ Finset.range (2*N+1), jacobiTripleTerm x q (-(N:ℤ))*
            qBinomialTerm (q^(-((2*N:ℕ):ℤ))) (q^(N+1)*x) q n := by
              apply Finset.sum_congr rfl
              intro n hn
              exact (finite_terminating_term N n x q hx hq0 hq1 (by simpa using hn)).symm
      _ = jacobiTripleTerm x q (-(N:ℤ)) *
          (∑ n ∈ Finset.range (2*N+1), qBinomialTerm (q^(-((2*N:ℕ):ℤ))) (q^(N+1)*x) q n) := by
            rw [Finset.mul_sum]
      _ = jacobiTripleTerm x q (-(N:ℤ))*qPochhammerNat (q^(1-(N:ℤ))*x) q (2*N) := by
        rw [finite_terminating_qBinomial (2*N) (q^(N+1)*x) q hy hq0 hq1, harg]
      _ = qPochhammerNat (q*x) q N * qPochhammerNat x⁻¹ q N := by
        rw [show 2*N=N+N by omega, qPochhammerNat_add, harg2,
          ← mul_assoc, finite_reflect_half x q hx hq N, mul_comm]

  have finite_jacobi_Icc (N : ℕ) (x q : ℂ)
      (hx : x ≠ 0) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
      (hy : ‖q^(N+1)*x‖ < 1) :
      (∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        jacobiTripleTerm x q k * qPochhammerNat q q (2*N) /
          (qPochhammerNat q q ((N:ℤ)+k).toNat * qPochhammerNat q q ((N:ℤ)-k).toNat)) =
        qPochhammerNat (q*x) q N * qPochhammerNat x⁻¹ q N := by
    have hreindex : (∑ n ∈ Finset.range (2*N+1),
        jacobiTripleTerm x q ((n:ℤ)-(N:ℤ)) * qPochhammerNat q q (2*N) /
          (qPochhammerNat q q n * qPochhammerNat q q (2*N-n))) =
      (∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        jacobiTripleTerm x q k * qPochhammerNat q q (2*N) /
          (qPochhammerNat q q ((N:ℤ)+k).toNat * qPochhammerNat q q ((N:ℤ)-k).toNat)) := by
      refine Finset.sum_bij (fun n _ => (n:ℤ)-(N:ℤ)) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Icc]
        omega
      · intro n hn m hm h
        omega
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        refine ⟨((N:ℤ)+k).toNat, ?_, ?_⟩
        · simp only [Finset.mem_range]
          omega
        · omega
      · intro n hn
        simp only [Finset.mem_range] at hn
        have h1 : ((N:ℤ)+((n:ℤ)-(N:ℤ))).toNat = n := by omega
        have h2 : ((N:ℤ)-((n:ℤ)-(N:ℤ))).toNat = 2*N-n := by omega
        rw [h1, h2]
    rw [← hreindex]
    exact finite_jacobi_range N x q hx hq0 hq1 hy

  have hasSum_finite_jacobi (N : ℕ) (x q : ℂ)
      (hx : x ≠ 0) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
      (hy : ‖q^(N+1)*x‖ < 1) :
      HasSum (fun k : ℤ => if -(N:ℤ) ≤ k ∧ k ≤ (N:ℤ) then
        jacobiTripleTerm x q k * qPochhammerNat q q (2*N) /
          (qPochhammerNat q q ((N:ℤ)+k).toNat * qPochhammerNat q q ((N:ℤ)-k).toNat)
        else 0)
        (qPochhammerNat (q*x) q N * qPochhammerNat x⁻¹ q N) := by
    let f : ℤ → ℂ := fun k => if -(N:ℤ) ≤ k ∧ k ≤ (N:ℤ) then
        jacobiTripleTerm x q k * qPochhammerNat q q (2*N) /
          (qPochhammerNat q q ((N:ℤ)+k).toNat * qPochhammerNat q q ((N:ℤ)-k).toNat)
        else 0
    have hvan : ∀ k ∉ Finset.Icc (-(N:ℤ)) (N:ℤ), f k = 0 := by
      intro k hk
      have h : ¬ (-(N:ℤ) ≤ k ∧ k ≤ (N:ℤ)) := by simpa only [Finset.mem_Icc] using hk
      simp [f, h]
    have hs : HasSum f (∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), f k) :=
      hasSum_sum_of_ne_finset_zero hvan
    have he : (∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), f k) =
        qPochhammerNat (q*x) q N * qPochhammerNat x⁻¹ q N := by
      calc _ = ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
            jacobiTripleTerm x q k * qPochhammerNat q q (2*N) /
              (qPochhammerNat q q ((N:ℤ)+k).toNat * qPochhammerNat q q ((N:ℤ)-k).toNat) := by
                apply Finset.sum_congr rfl
                intro k hk
                simp [f, Finset.mem_Icc.mp hk]
           _ = _ := finite_jacobi_Icc N x q hx hq0 hq1 hy
    rw [he] at hs
    exact hs
  have hpow : Tendsto (fun n : ℕ => q ^ (n + 1) * x) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1).mul_const (q * x)
    simpa only [pow_succ, mul_assoc, zero_mul] using h
  have hevent : ∀ᶠ n : ℕ in atTop, ‖q ^ (n + 1) * x‖ < 1 := by
    exact hpow.eventually (isOpen_lt continuous_norm continuous_const |>.mem_nhds (by simp))
  apply QProductLimitAux.hasSum_of_bilateralCoeff (qPochhammerNat q q)
    (jacobiTripleTerm x q) (qPochhammerNat (q*x) q) (qPochhammerNat x⁻¹ q)
    (qPochhammer q q) (qPochhammer (q*x) q) (qPochhammer x⁻¹ q)
    (tendsto_qPochhammerNat q q hq0 hq1) (qPochhammer_q_ne_zero q hq0 hq1)
    (tendsto_qPochhammerNat (q*x) q hq0 hq1)
    (tendsto_qPochhammerNat x⁻¹ q hq0 hq1)
    (summable_norm_jacobiTripleTerm x q hx hq0 hq1)
  filter_upwards [hevent] with n hn
  exact (hasSum_finite_jacobi n x q hx hq0 hq1 hn).tsum_eq

/--
Absolute convergence of the single-function residue double sum.
`C` is unrestricted.
-/
theorem summable_norm_singleResidueSeriesTerm (A C q Q : ℂ)
    (hA : ‖A‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖singleResidueSeriesTerm A C q Q p‖) := by
  have hprod : Summable fun p : ℕ × ℕ =>
      ‖eulerInverseTerm A q p.1‖ * ‖eulerTerm (Q*C) Q p.2‖ :=
    Summable.mul_of_nonneg (summable_norm_eulerInverseTerm A q hA hq0 hq1)
      (summable_norm_eulerTerm (Q*C) Q hQ0 hQ1) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  simpa [singleResidueSeriesTerm, norm_mul] using hprod

/-- Same source: the two Euler sums, with the common denominator cleared. -/
theorem hasSum_singleResidue_mul (A C q Q : ℂ)
    (hA : ‖A‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) :
    HasSum (fun p => qPochhammer A q * singleResidueSeriesTerm A C q Q p)
      (qPochhammer (Q * C) Q) := by
  have h1 := (hasSum_eulerInverse A q hA hq0 hq1).mul_left (qPochhammer A q)
  have h2 := hasSum_euler (Q*C) Q hQ0 hQ1
  have hsum0 : Summable (fun p : ℕ × ℕ =>
      eulerInverseTerm A q p.1 * eulerTerm (Q*C) Q p.2) :=
    Summable.of_norm (summable_norm_singleResidueSeriesTerm A C q Q hA hq0 hq1 hQ0 hQ1)
  have hsum : Summable (fun p : ℕ × ℕ =>
      (qPochhammer A q * eulerInverseTerm A q p.1) * eulerTerm (Q*C) Q p.2) := by
    have := hsum0.mul_left (qPochhammer A q)
    simpa [mul_assoc] using this
  have hprod := h1.mul h2 hsum
  have hPA : qPochhammer A q ≠ 0 := qPochhammer_ne_zero_of_norm_lt_one A q hA hq0 hq1
  simpa [singleResidueSeriesTerm, mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel₀ hPA] using hprod

/-- Same source: unordered double sum, quotient form. -/
theorem hasSum_singleResidue (A C q Q : ℂ)
    (hA : ‖A‖ < 1) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) (hd : qPochhammer A q ≠ 0) :
    HasSum (singleResidueSeriesTerm A C q Q) (qPochhammer (Q * C) Q / qPochhammer A q) := by
  have h := hasSum_singleResidue_mul A C q Q hA hq0 hq1 hQ0 hQ1
  have hdiv := h.div_const (qPochhammer A q)
  have hfun : (fun i => qPochhammer A q * singleResidueSeriesTerm A C q Q i /
      qPochhammer A q) = singleResidueSeriesTerm A C q Q := by
    funext p
    simp only [singleResidueSeriesTerm]
    field_simp [hd]
  rw [hfun] at hdiv
  exact hdiv

/--
Absolute convergence of both q-binomial factors.
Numerator parameters are arbitrary.
-/
theorem summable_norm_ratioResidueSeriesTerm (a A q b B Q : ℂ)
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖ratioResidueSeriesTerm a A q b B Q p‖) := by
  have hprod : Summable fun p : ℕ × ℕ =>
      ‖qBinomialTerm a A q p.1‖ * ‖qBinomialTerm b B Q p.2‖ :=
    Summable.mul_of_nonneg (summable_norm_qBinomialTerm a A q hA hq0 hq1)
      (summable_norm_qBinomialTerm b B Q hB hQ0 hQ1) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  simpa [ratioResidueSeriesTerm, norm_mul] using hprod

/-- Same source: double q-binomial sum with both denominators cleared. -/
theorem hasSum_ratioResidue_mul (a A q b B Q : ℂ)
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) :
    HasSum (fun p => (qPochhammer A q * qPochhammer B Q) *
      ratioResidueSeriesTerm a A q b B Q p)
      (qPochhammer (a * A) q * qPochhammer (b * B) Q) := by
  have h1 := hasSum_qBinomial_mul a A q hA hq0 hq1
  have h2 := hasSum_qBinomial_mul b B Q hB hQ0 hQ1
  have hsum0 : Summable (fun p : ℕ × ℕ =>
      qBinomialTerm a A q p.1 * qBinomialTerm b B Q p.2) :=
    Summable.of_norm (summable_norm_ratioResidueSeriesTerm a A q b B Q hA hB hq0 hq1 hQ0 hQ1)
  have hsum : Summable (fun p : ℕ × ℕ =>
      (qPochhammer A q * qBinomialTerm a A q p.1) *
        (qPochhammer B Q * qBinomialTerm b B Q p.2)) := by
    have := hsum0.mul_left (qPochhammer A q * qPochhammer B Q)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hprod := h1.mul h2 hsum
  simpa [ratioResidueSeriesTerm, mul_assoc, mul_comm, mul_left_comm] using hprod

/-- Same source: double q-binomial sum, quotient form after nonzero checks. -/
theorem hasSum_ratioResidue (a A q b B Q : ℂ)
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1)
    (hdA : qPochhammer A q ≠ 0) (hdB : qPochhammer B Q ≠ 0) :
    HasSum (ratioResidueSeriesTerm a A q b B Q)
      (qPochhammer (a * A) q / qPochhammer A q *
        (qPochhammer (b * B) Q / qPochhammer B Q)) := by
  have h := hasSum_ratioResidue_mul a A q b B Q hA hB hq0 hq1 hQ0 hQ1
  have hdiv := h.div_const (qPochhammer A q * qPochhammer B Q)
  have hfun : (fun p => (qPochhammer A q * qPochhammer B Q) *
      ratioResidueSeriesTerm a A q b B Q p / (qPochhammer A q * qPochhammer B Q)) =
      ratioResidueSeriesTerm a A q b B Q := by
    funext p
    rw [ratioResidueSeriesTerm]
    field_simp [hdA, hdB]
  rw [hfun] at hdiv
  have hsum_eq : qPochhammer (a * A) q * qPochhammer (b * B) Q /
      (qPochhammer A q * qPochhammer B Q) =
      qPochhammer (a * A) q / qPochhammer A q *
        (qPochhammer (b * B) Q / qPochhammer B Q) := by
    field_simp [hdA, hdB]
  rw [hsum_eq] at hdiv
  exact hdiv

end SICLean.L4

-- Actual pinned Mathlib types, including the absolute-convergence/Fubini
-- infrastructure required before any infinite residue-sum rearrangement.
#check HasProdLocallyUniformlyOn
#check HasProdUniformlyOn
#check multipliable_one_add_of_summable
#check ModularForm.multipliableLocallyUniformlyOn_one_sub_pow
#check Summable.of_norm
#check summable_mul_of_summable_norm
#check HasSum.mul
#check tsum_mul_tsum_of_summable_norm
#check Summable.tsum_prod
#check Summable.tsum_comm
#check Equiv.hasSum_iff
#check Equiv.tsum_eq
#check HasSum
#print SICLean.L4.qPochhammerIntDenominator
#print SICLean.L4.jacobiTripleTerm
#check SICLean.L4.analyticOnNhd_qPochhammer_joint
#check SICLean.L4.hasSum_ratioResidue
