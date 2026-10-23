import SICLean.L5.LocalFourierSetup
import SICLean.L5.FiniteQBinomial
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.RootsOfUnity.Lemmas

set_option autoImplicit false

/-!
# Cyclotomic valuation estimates for local Lemma 1

[RW-rec, p. 5, p. 6]. These are valuation statements about the existing integral
q-binomial polynomials, not a second q-Pascal implementation. The source cites KW04
(arXiv:math/0103125), Lemma 3.5 and Corollary 3.12, at [RW-rec]; the statements here
follow the argument in [RW-rec].
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalCyclotomicValuation

open LocalFourierSetup FiniteQBinomial FiniteCosetMoments

variable {L : Type*} [Field L] [CharZero L]
variable {p s : ℕ} [Fact p.Prime]

/-- The real sum of valuations of factors with exponents from 1 through j. All uses impose
`j < p^s`, so these factors are nonzero. -/
def pochhammerValue (v : AddValuation L (WithTop ℝ)) (z : L) (j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range j, (v (1 - z ^ (r + 1))).untop₀

/-- [RW-rec, p. 5]: roots of unity have valuation zero. -/
theorem primitive_value_zero (v : AddValuation L (WithTop ℝ))
    (hs : 1 ≤ s) {z : L} (hz : IsPrimitiveRoot z (p ^ s)) : v z = 0 := by
  have hn : p ^ s ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hzt : v z ≠ ⊤ := v.ne_top_iff.mpr (hz.ne_zero hn)
  have hh := congrArg v hz.pow_eq_one
  rw [v.map_pow, v.map_one, ← WithTop.coe_untop₀_of_ne_top hzt] at hh
  have hreal : (p ^ s : ℕ) • (v z).untop₀ = (0 : ℝ) := by
    exact WithTop.coe_injective (by simpa only [WithTop.coe_nsmul, WithTop.coe_zero] using hh)
  have hzero : (v z).untop₀ = 0 :=
    (smul_eq_zero.mp hreal).resolve_left (by exact_mod_cast hn)
  rw [← WithTop.coe_untop₀_of_ne_top hzt, hzero]
  rfl

/-- [RW-rec]: a p-power root reduces to one in the actual residue field. -/
theorem primitive_reduce_one (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hs : 1 ≤ s) {z : L}
    (hz : IsPrimitiveRoot z (p ^ s)) : reduce v z = 1 := by
  haveI := residue_charP v hp
  have hzv : 0 ≤ v z := le_of_eq (primitive_value_zero v hs hz).symm
  let zi : integers v := ⟨z, hzv⟩
  have hpow : zi ^ (p ^ s) = 1 := Subtype.ext hz.pow_eq_one
  have hred : (reduce v z) ^ (p ^ s) = 1 := by
    rw [reduce_eq_residue v z hzv]
    change (IsLocalRing.residue (integers v) zi) ^ (p ^ s) = 1
    rw [← map_pow, hpow, map_one]
  simpa only [Nat.mul_one, pow_one] using
    (ExpChar.pow_prime_pow_mul_eq_one_iff p s 1 (reduce v z)).mp (by simpa using hred)

/-- [RW-rec]: the factors before the order are nonzero. -/
theorem cyclotomic_factor_ne_zero (hs : 1 ≤ s) {z : L}
    (hz : IsPrimitiveRoot z (p ^ s)) {r : ℕ} (hr : 0 < r) (hrq : r < p ^ s) :
    1 - z ^ r ≠ 0 := by
  exact sub_ne_zero.mpr (hz.pow_ne_one_of_pos_of_lt (Nat.ne_of_gt hr) hrq).symm

/-- [RW-rec]: every such factor has strictly positive valuation. -/
theorem cyclotomic_factor_value_pos (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hs : 1 ≤ s) {z : L}
    (hz : IsPrimitiveRoot z (p ^ s)) {r : ℕ} (hr : 0 < r) (hrq : r < p ^ s) :
    0 < v (1 - z ^ r) := by
  have hz0 := primitive_value_zero v hs hz
  have hzv : 0 ≤ v z := le_of_eq hz0.symm
  have hzr : 0 ≤ v (z ^ r) := by simp [hz0]
  apply (reduce_eq_iff v 1 (z ^ r) (by simp) hzr).mp
  rw [reduce_eq_residue v 1 (by simp), reduce_eq_residue v (z ^ r) hzr]
  let zi : integers v := ⟨z, hzv⟩
  change IsLocalRing.residue (integers v) 1 =
    IsLocalRing.residue (integers v) (zi ^ r)
  rw [map_one, map_pow]
  have hred : IsLocalRing.residue (integers v) zi = 1 := by
    exact (reduce_eq_residue v z hzv).symm.trans (primitive_reduce_one v hp hs hz)
  rw [hred, one_pow]

/-- [RW-rec]: the real sum agrees with the valuation of the existing product. -/
theorem value_finitePochhammer (v : AddValuation L (WithTop ℝ))
    (hs : 1 ≤ s) {z : L} (hz : IsPrimitiveRoot z (p ^ s))
    {j : ℕ} (hj : j < p ^ s) :
    v (finitePochhammer z z j) = (pochhammerValue v z j : WithTop ℝ) := by
  induction j with
  | zero => simp [finitePochhammer, pochhammerValue]
  | succ j ih =>
      have hfactor : v (1 - z ^ (j + 1)) ≠ ⊤ :=
        v.ne_top_iff.mpr (cyclotomic_factor_ne_zero hs hz (by omega) hj)
      rw [finitePochhammer_succ, v.map_mul, ih (by omega), ← pow_succ]
      unfold pochhammerValue
      rw [Finset.sum_range_succ, WithTop.coe_add,
        WithTop.coe_untop₀_of_ne_top hfactor]

/-- [RW-rec]: the full product is p^s and its normalized valuation is s. -/
theorem pochhammerValue_full (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hs : 1 ≤ s) {z : L}
    (hz : IsPrimitiveRoot z (p ^ s)) :
    pochhammerValue v z (p ^ s - 1) = (s : ℝ) := by
  have hq : 0 < p ^ s := pow_pos (Fact.out : p.Prime).pos _
  have horder : p ^ s - 1 + 1 = p ^ s := Nat.sub_add_cancel hq
  have hz' : IsPrimitiveRoot z (p ^ s - 1 + 1) := horder.symm ▸ hz
  have hprod : finitePochhammer z z (p ^ s - 1) = ((p ^ s : ℕ) : L) := by
    calc
      finitePochhammer z z (p ^ s - 1) = ((p ^ s - 1 : ℕ) : L) + 1 := by
        simpa only [finitePochhammer, ← pow_succ] using hz'.prod_one_sub_pow_eq_order
      _ = ((p ^ s : ℕ) : L) := by exact_mod_cast horder
  have hval := value_finitePochhammer v hs hz (Nat.sub_lt hq Nat.zero_lt_one)
  rw [hprod, Nat.cast_pow, AddValuation.map_pow, hp] at hval
  have hv : ((s : ℝ) : WithTop ℝ) = (pochhammerValue v z (p ^ s - 1) : WithTop ℝ) := by
    simpa using hval
  exact WithTop.coe_injective hv.symm

/-- [RW-rec]: pairing the exponents r and p^s-r preserves valuation. -/
theorem cyclotomic_factor_value_reflection (v : AddValuation L (WithTop ℝ))
    (hs : 1 ≤ s) {z : L} (hz : IsPrimitiveRoot z (p ^ s))
    {r : ℕ} (hr : 0 < r) (hrq : r < p ^ s) :
    v (1 - z ^ r) = v (1 - z ^ (p ^ s - r)) := by
  have he : z ^ r * (1 - z ^ (p ^ s - r)) = -(1 - z ^ r) := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hrq), hz.pow_eq_one]
    ring
  have hv := congrArg v he
  simpa only [AddValuation.map_mul, AddValuation.map_pow,
    primitive_value_zero v hs hz, nsmul_zero, zero_add, AddValuation.map_neg] using hv.symm

/-- [RW-rec]: complementary partial products have valuations summing to s. -/
theorem pochhammerValue_reflection (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hs : 1 ≤ s) {z : L}
    (hz : IsPrimitiveRoot z (p ^ s)) {j : ℕ} (hj : j < p ^ s) :
    pochhammerValue v z j + pochhammerValue v z (p ^ s - 1 - j) = (s : ℝ) := by
  let f : ℕ → ℝ := fun r => (v (1 - z ^ (r + 1))).untop₀
  have hcomp : pochhammerValue v z (p ^ s - 1 - j) =
      ∑ r ∈ Finset.range (p ^ s - 1 - j), f (j + r) := by
    change (∑ r ∈ Finset.range (p ^ s - 1 - j), f r) = _
    rw [← Finset.sum_range_reflect f (p ^ s - 1 - j)]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < p ^ s - 1 - j := Finset.mem_range.mp hr
    have ha : 0 < p ^ s - 1 - j - 1 - r + 1 := by omega
    have hb : p ^ s - 1 - j - 1 - r + 1 < p ^ s := by omega
    have hreflect := cyclotomic_factor_value_reflection v hs hz ha hb
    have heq : p ^ s - (p ^ s - 1 - j - 1 - r + 1) = j + r + 1 := by omega
    dsimp [f]
    rw [hreflect, heq]
  have hadd : j + (p ^ s - 1 - j) = p ^ s - 1 := by omega
  calc
    pochhammerValue v z j + pochhammerValue v z (p ^ s - 1 - j) =
        (∑ r ∈ Finset.range j, f r) +
          ∑ r ∈ Finset.range (p ^ s - 1 - j), f (j + r) := by
            rw [hcomp]
            rfl
    _ = ∑ r ∈ Finset.range (p ^ s - 1), f r := by
      rw [← Finset.sum_range_add, hadd]
    _ = (s : ℝ) := pochhammerValue_full v hp hs hz

/-- [RW-rec]: strict monotonicity, including j=0. -/
theorem pochhammerValue_strictMono (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hs : 1 ≤ s) {z : L}
    (hz : IsPrimitiveRoot z (p ^ s)) {i j : ℕ} (hij : i < j) (hj : j < p ^ s) :
    pochhammerValue v z i < pochhammerValue v z j := by
  have hpos (r : ℕ) (hr : r ∈ Finset.range j) :
      0 < (v (1 - z ^ (r + 1))).untop₀ := by
    have hr' := Finset.mem_range.mp hr
    have hrq : r + 1 < p ^ s := by omega
    have hne := v.ne_top_iff.mpr (cyclotomic_factor_ne_zero hs hz (by omega) hrq)
    have hv := cyclotomic_factor_value_pos v hp hs hz (by omega) hrq
    rw [← WithTop.coe_untop₀_of_ne_top hne] at hv
    exact_mod_cast hv
  unfold pochhammerValue
  apply Finset.sum_lt_sum_of_subset (Finset.range_mono (Nat.le_of_lt hij))
    (Finset.mem_range.mpr hij) (by simp) (hpos i (Finset.mem_range.mpr hij))
  intro r hr _
  exact (hpos r hr).le

/-- [RW-rec]: the strict degree range makes the denominator valuation smaller than ds/2. This uses
d=1 or d=2, not arbitrary rank. -/
theorem low_multiIndex_value_lt (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hodd : p ≠ 2) (hs : 1 ≤ s) {z : L}
    (hz : IsPrimitiveRoot z (p ^ s)) {d : ℕ} (hd : d = 1 ∨ d = 2)
    (j : Fin d → ℕ) (hj : ∀ i, j i < p ^ s)
    (hdeg : 2 * totalDegree j < d * (p ^ s - 1)) :
    (∑ i, pochhammerValue v z (j i)) < ((d * s : ℕ) : ℝ) / 2 := by
  rcases hd with rfl | rfl
  · simp only [totalDegree, Fin.sum_univ_one, one_mul] at hdeg ⊢
    have hlt : j 0 < p ^ s - 1 - j 0 := by omega
    have hcomp : p ^ s - 1 - j 0 < p ^ s := by omega
    have hm := pochhammerValue_strictMono v hp hs hz hlt hcomp
    have hr := pochhammerValue_reflection v hp hs hz (hj 0)
    linarith
  · simp only [totalDegree, Fin.sum_univ_two] at hdeg ⊢
    have hlt : j 1 < p ^ s - 1 - j 0 := by omega
    have hcomp : p ^ s - 1 - j 0 < p ^ s := by omega
    have hm := pochhammerValue_strictMono v hp hs hz hlt hcomp
    have hr := pochhammerValue_reflection v hp hs hz (hj 0)
    push_cast
    linarith

/-- [RW-rec]: integrality comes from `qBinomialPoly`, not its quotient. -/
theorem qBinomial_value_nonneg (v : AddValuation L (WithTop ℝ))
    {z : L} (hz : 0 ≤ v z) (i j : ℕ) :
    0 ≤ v (qBinomial z i j) := by
  let zi : integers v := ⟨z, hz⟩
  have he : ((qBinomial zi i j : integers v) : L) = qBinomial z i j := by
    exact map_qBinomial (integers v).subtype zi i j
  rw [← he]
  exact (qBinomial zi i j).property

/-- [RW-rec]: reuse `map_qBinomial_eq_choose` with z reducing to one. -/
theorem qBinomial_reduce (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hs : 1 ≤ s) {z : L}
    (hz : IsPrimitiveRoot z (p ^ s)) (i j : ℕ) :
    reduce v (qBinomial z i j) = (Nat.choose i j : Residue v) := by
  have hzv : 0 ≤ v z := le_of_eq (primitive_value_zero v hs hz).symm
  let zi : integers v := ⟨z, hzv⟩
  have he : ((qBinomial zi i j : integers v) : L) = qBinomial z i j := by
    exact map_qBinomial (integers v).subtype zi i j
  have hred : IsLocalRing.residue (integers v) zi = 1 :=
    (reduce_eq_residue v z hzv).symm.trans (primitive_reduce_one v hp hs hz)
  rw [← he, reduce_eq_residue v _ (qBinomial zi i j).property]
  exact map_qBinomial_eq_choose (IsLocalRing.residue (integers v)) zi hred i j

/-- [RW-rec]: the already defined Pochhammer expansion coefficients are integral. -/
theorem finitePochhammerCoeff_value_nonneg (v : AddValuation L (WithTop ℝ))
    {z : L} (hz : v z = 0) (j a : ℕ) :
    0 ≤ v (finitePochhammerCoeff z⁻¹ j a) := by
  have hzi : 0 ≤ v z⁻¹ := by simp [hz]
  unfold finitePochhammerCoeff
  rw [v.map_mul, v.map_mul]
  have hsign : v ((-1 : L) ^ a) = 0 := by simp
  have hpower : 0 ≤ v ((z⁻¹) ^ (a.choose 2)) := by simp [hz]
  rw [hsign, zero_add]
  exact add_nonneg hpower (qBinomial_value_nonneg v hzi j a)

#check @low_multiIndex_value_lt
#check @FiniteQBinomial.qBinomial_weighted_sum
#check @FiniteQBinomial.map_qBinomial_eq_choose

end SICLean.L5.LocalCyclotomicValuation
