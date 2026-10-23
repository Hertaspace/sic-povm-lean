import SICLean.L4.Faddeev
import SICLean.L4.FaddeevContinuationAux
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

/-!
# Continuation of `phi`

The fifteen definitions and the statements below are the interface. Their proofs, including
coincident divisor branches and the joint analytic quotient, are supplied below.

[RW26, §2.1, pp. 4--5]. The divisor is Andersen--Kashaev, arXiv:1109.6295, Appendix A, (45). The
local parameter charts are included.

The definitions below contain only the defined strip integral, integer rounding and finite products.
No existence/meromorphy hypothesis is built into `phiExtended`. In particular it is not a choice of
a function postulated to have the desired analytic properties.

At a pole, complex total division assigns the representative the value 0. This convention has no
analytic significance. Difference equations and inversion are therefore equalities on punctured
neighborhoods, including at a center where a pole meets a zero. They are not pointwise identities at
every complex argument. `MeromorphicAt` ignores the center value.

The local quotient theorem is genuinely about the two complex variables `(b,z)`. Its fixed-index
numerator and denominator are explicit below. Denominator nonvanishing on each parameter slice is an
explicit conclusion, not an implicit assumption of a new “joint meromorphic” structure.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace SICLean.L4

/-- Nearest vertical `ib` translate, with a fixed tie-breaking rule. Only parameters with
`AdmissibleB b` are used in the statements. -/
def continuationIndex (b z : ℂ) : ℤ :=
  ⌊z.im / b.re + (1 / 2 : ℝ)⌋

/-- Translate by a fixed integer, independent of the rounding operation. -/
def shiftedArgument (b z : ℂ) (k : ℤ) : ℂ := z - (k : ℂ) * Complex.I * b

/-- The multiplicative factor from the proved `b` difference equation. -/
def continuationFactor (b w : ℂ) : ℂ :=
  1 + Complex.exp (2 * (Real.pi : ℂ) * b * w)

/-- Numerator of a fixed-index continuation chart. -/
def continuationNumerator (b z : ℂ) (k : ℤ) : ℂ :=
  let w := shiftedArgument b z k
  if 0 ≤ k then phi b w
  else phi b w * ∏ j ∈ Finset.range (-k).toNat,
    continuationFactor b (w - ((j : ℂ) + 1 / 2) * Complex.I * b)

/-- Denominator of a fixed-index continuation chart. -/
def continuationDenominator (b z : ℂ) (k : ℤ) : ℂ :=
  let w := shiftedArgument b z k
  if 0 ≤ k then ∏ j ∈ Finset.range k.toNat,
    continuationFactor b (w + ((j : ℂ) + 1 / 2) * Complex.I * b)
  else 1

/-- A chart is meaningful where its shifted argument is in the original strip. Its value at a pole
is the total-division representative 0. -/
def phiChart (b z : ℂ) (k : ℤ) : ℂ :=
  continuationNumerator b z k / continuationDenominator b z k

/-- Concrete continuation candidate. Meromorphy and chart independence are theorems below, not parts
of this definition. -/
def phiExtended (b z : ℂ) : ℂ := phiChart b z (continuationIndex b z)

/-- Positive divisor branch: a pole, with repeated indices retained. -/
def phiPolePoint (b : ℂ) (m n : ℕ) : ℂ :=
  Complex.I * (b + b⁻¹) / 2 + (m : ℂ) * Complex.I * b +
    (n : ℂ) * Complex.I * b⁻¹

/-- Negative divisor branch: a zero, with repeated indices retained. -/
def phiZeroPoint (b : ℂ) (m n : ℕ) : ℂ := -phiPolePoint b m n

def phiPoleIndices (b z : ℂ) : Set (ℕ × ℕ) :=
  {mn | z = phiPolePoint b mn.1 mn.2}

def phiZeroIndices (b z : ℂ) : Set (ℕ × ℕ) :=
  {mn | z = phiZeroPoint b mn.1 mn.2}

/-- `Nat.card` is used only together with the explicit finiteness theorem. -/
def phiPoleMultiplicity (b z : ℂ) : ℕ := Nat.card (phiPoleIndices b z)

def phiZeroMultiplicity (b z : ℂ) : ℕ := Nat.card (phiZeroIndices b z)

/-- Positive means a zero, negative means a pole, as in Mathlib. -/
def phiDivisorOrder (b z : ℂ) : ℤ :=
  (phiZeroMultiplicity b z : ℤ) - (phiPoleMultiplicity b z : ℤ)

/-- Zeros are included in this domain. Poles are excluded. -/
def phiRegularDomain : Set (ℂ × ℂ) :=
  {p | AdmissibleB p.1 ∧ phiPoleMultiplicity p.1 p.2 = 0}

lemma shiftedArgument_im (b z : ℂ) (k : ℤ) :
    (shiftedArgument b z k).im = z.im - (k : ℝ) * b.re := by
  simp [shiftedArgument, Complex.mul_im, Complex.mul_re]

lemma shiftedArgument_zero (b z : ℂ) : shiftedArgument b z 0 = z := by
  simp [shiftedArgument]

lemma shiftedArgument_succ (b z : ℂ) (k : ℤ) :
    shiftedArgument b z (k + 1) = shiftedArgument b z k - Complex.I * b := by
  simp only [shiftedArgument, Int.cast_add, Int.cast_one]
  ring

lemma analyticAt_phi_of_inStrip (b z : ℂ) (hb : AdmissibleB b) (hz : InStrip b z) :
    AnalyticAt ℂ (phi b) z :=
  (differentiableOn_phi b hb).analyticOnNhd (isOpen_inStrip b) z hz

lemma phiPolePoint_im (b : ℂ) (m n : ℕ) :
    (phiPolePoint b m n).im =
      stripWidth b + (m : ℝ) * b.re + (n : ℝ) * (b⁻¹).re := by
  simp [phiPolePoint, stripWidth, Complex.mul_im, Complex.mul_re]

lemma phiPolePoint_im_pos (b : ℂ) (hb : AdmissibleB b) (m n : ℕ) :
    0 < (phiPolePoint b m n).im := by
  rw [phiPolePoint_im]
  have hb' : 0 < b.re := hb
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hw : 0 < stripWidth b := by unfold stripWidth; linarith
  positivity

lemma analyticAt_shiftedArgument (b z : ℂ) (k : ℤ) :
    AnalyticAt ℂ (fun w => shiftedArgument b w k) z := by
  unfold shiftedArgument
  fun_prop

lemma analyticAt_continuationFactor (b z : ℂ) :
    AnalyticAt ℂ (continuationFactor b) z := by
  unfold continuationFactor
  fun_prop

lemma analyticAt_continuationDenominator (b z : ℂ) (k : ℤ) :
    AnalyticAt ℂ (fun w => continuationDenominator b w k) z := by
  classical
  unfold continuationDenominator
  split_ifs
  · apply Finset.analyticAt_fun_prod
    intro j _
    apply (analyticAt_continuationFactor b _).comp
    exact (analyticAt_shiftedArgument b z k).add analyticAt_const
  · exact analyticAt_const

lemma analyticAt_continuationNumerator (b z : ℂ) (k : ℤ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z k)) :
    AnalyticAt ℂ (fun w => continuationNumerator b w k) z := by
  classical
  have hphi : AnalyticAt ℂ (fun w => phi b (shiftedArgument b w k)) z :=
    (analyticAt_phi_of_inStrip b _ hb hz).comp
      (f := fun w : ℂ => shiftedArgument b w k) (analyticAt_shiftedArgument b z k)
  unfold continuationNumerator
  split_ifs
  · exact hphi
  · apply hphi.mul
    apply Finset.analyticAt_fun_prod
    intro j _
    apply (analyticAt_continuationFactor b _).comp
    exact (analyticAt_shiftedArgument b z k).sub analyticAt_const

lemma meromorphicAt_phiChart (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hz : InStrip b (shiftedArgument b z k)) :
    MeromorphicAt (fun w => phiChart b w k) z :=
  (analyticAt_continuationNumerator b z k hb hz).meromorphicAt.div
    (analyticAt_continuationDenominator b z k).meromorphicAt

lemma continuationFactor_eq_zero_iff (b u : ℂ) (hb : b ≠ 0) :
    continuationFactor b u = 0 ↔
      ∃ n : ℤ, u = ((n : ℂ) + 1 / 2) * Complex.I * b⁻¹ := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · intro hu
    have he : Complex.exp (2 * (Real.pi : ℂ) * b * u) =
        Complex.exp ((Real.pi : ℂ) * Complex.I) := by
      rw [Complex.exp_pi_mul_I]
      change 1 + Complex.exp (2 * (Real.pi : ℂ) * b * u) = 0 at hu
      linear_combination hu
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    refine ⟨n, ?_⟩
    apply mul_left_cancel₀ (a := 2 * (Real.pi : ℂ) * b) (by simp [hp, hb])
    calc
      2 * (Real.pi : ℂ) * b * u = _ := hn
      _ = 2 * (Real.pi : ℂ) * b *
          (((n : ℂ) + 1 / 2) * Complex.I * b⁻¹) := by field_simp; ring
  · rintro ⟨n, rfl⟩
    have he : 2 * (Real.pi : ℂ) * b *
        (((n : ℂ) + 1 / 2) * Complex.I * b⁻¹) =
        (Real.pi : ℂ) * Complex.I + n * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp
      ring
    change 1 + Complex.exp (2 * (Real.pi : ℂ) * b *
      (((n : ℂ) + 1 / 2) * Complex.I * b⁻¹)) = 0
    rw [he, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I]
    ring

lemma meromorphicOrderAt_continuationFactor_add (b c z : ℂ) (hb : b ≠ 0) :
    meromorphicOrderAt (fun w => continuationFactor b (w + c)) z =
      if continuationFactor b (z + c) = 0 then 1 else 0 := by
  classical
  have ha : AnalyticAt ℂ (fun w => continuationFactor b (w + c)) z :=
    (analyticAt_continuationFactor b _).comp (analyticAt_id.add analyticAt_const)
  rw [ha.meromorphicOrderAt_eq]
  split_ifs with h
  · have hd : HasDerivAt (fun w => continuationFactor b (w + c))
        (Complex.exp (2 * (Real.pi : ℂ) * b * (z + c)) *
          (2 * (Real.pi : ℂ) * b)) z := by
      simpa [continuationFactor] using
        (((hasDerivAt_id z).add_const c).const_mul (2 * (Real.pi : ℂ) * b)).cexp.const_add 1
    have he : Complex.exp (2 * (Real.pi : ℂ) * b * (z + c)) = -1 := by
      change 1 + Complex.exp (2 * (Real.pi : ℂ) * b * (z + c)) = 0 at h
      linear_combination h
    have hdn : deriv (fun w => continuationFactor b (w + c)) z ≠ 0 := by
      rw [hd.deriv, he]
      exact mul_ne_zero (by norm_num) (mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hb)
    rw [ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h hdn]
    rfl
  · rw [ha.analyticOrderAt_eq_zero.mpr h]
    rfl

lemma meromorphicOrderAt_continuationFactor_shifted_add (b z : ℂ) (k : ℤ) (c : ℂ)
    (hb : b ≠ 0) :
    meromorphicOrderAt (fun w => continuationFactor b (shiftedArgument b w k + c)) z =
      if continuationFactor b (shiftedArgument b z k + c) = 0 then 1 else 0 := by
  have heq (w : ℂ) : shiftedArgument b w k + c =
      w + (-(k : ℂ) * Complex.I * b + c) := by unfold shiftedArgument; ring
  simp_rw [heq]
  exact meromorphicOrderAt_continuationFactor_add b _ z hb

lemma continuationFactor_neg_eq_zero_iff (b u : ℂ) :
    continuationFactor b (-u) = 0 ↔ continuationFactor b u = 0 := by
  have he : continuationFactor b (-u) =
      Complex.exp (-(2 * (Real.pi : ℂ) * b * u)) * continuationFactor b u := by
    unfold continuationFactor
    rw [mul_add, show -(2 * (Real.pi : ℂ) * b * u) =
      2 * (Real.pi : ℂ) * b * -u by ring, ← Complex.exp_add]
    ring_nf
    simp [add_comm]
  rw [he, mul_eq_zero]
  simp [Complex.exp_ne_zero]

lemma continuationFactor_positive_zero_iff (b z : ℂ) (a j : ℕ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z a)) (hj : j < a) :
    continuationFactor b (shiftedArgument b z a +
      ((j : ℂ) + 1 / 2) * Complex.I * b) = 0 ↔
      ∃ n : ℕ, z = phiPolePoint b (a - 1 - j) n := by
  have hb' : 0 < b.re := hb
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hmc : ((a - 1 - j : ℕ) : ℂ) = (a : ℂ) - (j : ℂ) - 1 := by
    have hnat : a - 1 - j + j + 1 = a := by omega
    have hc : ((a - 1 - j : ℕ) : ℂ) + (j : ℂ) + 1 = a := by exact_mod_cast hnat
    linear_combination hc
  constructor
  · intro hf
    obtain ⟨n, hn⟩ := (continuationFactor_eq_zero_iff b _ (admissibleB_ne_zero b hb)).mp hf
    have hn0 : 0 ≤ n := by
      have him := congrArg Complex.im hn
      norm_num [Complex.mul_im, Complex.mul_re] at him
      have hstrip := (abs_lt.mp hz).1
      unfold stripWidth at hstrip
      rw [Complex.inv_re] at hi hstrip
      by_contra hn0
      have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    lift n to ℕ using hn0
    refine ⟨n, ?_⟩
    unfold shiftedArgument at hn
    simp only [Int.cast_natCast] at hn
    unfold phiPolePoint
    rw [hmc]
    linear_combination hn
  · rintro ⟨n, rfl⟩
    apply (continuationFactor_eq_zero_iff b _ (admissibleB_ne_zero b hb)).mpr
    refine ⟨n, ?_⟩
    simp only [shiftedArgument, phiPolePoint, Int.cast_natCast, hmc]
    ring

lemma shiftedArgument_neg (b z : ℂ) (k : ℤ) :
    shiftedArgument b (-z) (-k) = -shiftedArgument b z k := by
  simp only [shiftedArgument, Int.cast_neg]
  ring

lemma continuationFactor_negative_zero_iff (b z : ℂ) (a j : ℕ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z (-(a : ℤ))))
    (hj : j < a) :
    continuationFactor b (shiftedArgument b z (-(a : ℤ)) -
      ((j : ℂ) + 1 / 2) * Complex.I * b) = 0 ↔
      ∃ n : ℕ, -z = phiPolePoint b (a - 1 - j) n := by
  have hs : shiftedArgument b (-z) a = -shiftedArgument b z (-(a : ℤ)) := by
    simpa only [neg_neg] using shiftedArgument_neg b z (-(a : ℤ))
  have hzn : InStrip b (shiftedArgument b (-z) a) := by
    simpa only [hs, InStrip, Complex.neg_im, abs_neg] using hz
  have h := continuationFactor_positive_zero_iff b (-z) a j hb hzn hj
  have he : shiftedArgument b (-z) a + ((j : ℂ) + 1 / 2) * Complex.I * b =
      -(shiftedArgument b z (-(a : ℤ)) - ((j : ℂ) + 1 / 2) * Complex.I * b) := by
    rw [hs]
    ring
  rw [he, continuationFactor_neg_eq_zero_iff] at h
  exact h

lemma phiPolePoint_first_index_lt (b z : ℂ) (a m n : ℕ) (hb : AdmissibleB b)
    (hz : InStrip b (shiftedArgument b z a)) (heq : z = phiPolePoint b m n) : m < a := by
  have hb' : 0 < b.re := hb
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hu := (abs_lt.mp hz).2
  rw [shiftedArgument_im, heq, phiPolePoint_im] at hu
  simp only [Int.cast_natCast] at hu
  by_contra hm
  have hm' : (a : ℝ) ≤ m := by exact_mod_cast (show a ≤ m by omega)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma phiZeroIndices_empty_of_nonneg_shift (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hk : 0 ≤ k) (hz : InStrip b (shiftedArgument b z k)) :
    phiZeroIndices b z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨m, n⟩ hmn
  have hp := phiPolePoint_im b m n
  have hb' : 0 < b.re := hb
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have hstrip := (abs_lt.mp hz).1
  rw [shiftedArgument_im] at hstrip
  have heq : z = -phiPolePoint b m n := hmn
  have him := congrArg Complex.im heq
  simp only [Complex.neg_im] at him
  rw [him, hp] at hstrip
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma phiPoleIndices_empty_of_nonpos_shift (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hk : k ≤ 0) (hz : InStrip b (shiftedArgument b z k)) :
    phiPoleIndices b z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨m, n⟩ hmn
  have hb' : 0 < b.re := hb
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
  have hstrip := (abs_lt.mp hz).2
  rw [shiftedArgument_im, hmn, phiPolePoint_im] at hstrip
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma continuation_prod_pos_step (b w : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), continuationFactor b
      (w - Complex.I * b + ((j : ℂ) + 1 / 2) * Complex.I * b)) =
    (∏ j ∈ Finset.range n, continuationFactor b
      (w + ((j : ℂ) + 1 / 2) * Complex.I * b)) *
      continuationFactor b (w - Complex.I * b / 2) := by
  rw [Finset.prod_range_succ']
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  · congr 1
    norm_num
    ring

lemma continuation_prod_neg_step (b w : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), continuationFactor b
      (w + Complex.I * b - ((j : ℂ) + 1 / 2) * Complex.I * b)) =
    (∏ j ∈ Finset.range n, continuationFactor b
      (w - ((j : ℂ) + 1 / 2) * Complex.I * b)) *
      continuationFactor b (w + Complex.I * b / 2) := by
  rw [Finset.prod_range_succ']
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  · congr 1
    norm_num
    ring

lemma inStrip_shiftedArgument_between (b z : ℂ) (k j l : ℤ) (hb : AdmissibleB b)
    (hkj : k ≤ j) (hjl : j ≤ l)
    (hk : InStrip b (shiftedArgument b z k))
    (hl : InStrip b (shiftedArgument b z l)) :
    InStrip b (shiftedArgument b z j) := by
  simp only [InStrip, shiftedArgument_im, abs_lt] at hk hl ⊢
  have hkj' : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
  have hjl' : (j : ℝ) ≤ (l : ℝ) := by exact_mod_cast hjl
  change 0 < b.re at hb
  constructor <;> nlinarith [hk.1, hk.2, hl.1, hl.2]

lemma phi_shiftedArgument_step (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k))
    (hk1 : InStrip b (shiftedArgument b z (k + 1))) :
    phi b (shiftedArgument b z (k + 1)) =
      continuationFactor b (shiftedArgument b z k - Complex.I * b / 2) *
        phi b (shiftedArgument b z k) := by
  have hm : shiftedArgument b z k - Complex.I * b / 2 - Complex.I * b / 2 =
      shiftedArgument b z (k + 1) := by rw [shiftedArgument_succ]; ring
  have hp : shiftedArgument b z k - Complex.I * b / 2 + Complex.I * b / 2 =
      shiftedArgument b z k := by ring
  have h := phi_difference_b b (shiftedArgument b z k - Complex.I * b / 2) hb
    (by rw [hm]; exact hk1) (by rw [hp]; exact hk)
  simpa only [hm, hp, continuationFactor] using h

lemma continuation_step_factor_ne_zero (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k))
    (hk1 : InStrip b (shiftedArgument b z (k + 1))) :
    continuationFactor b (shiftedArgument b z k - Complex.I * b / 2) ≠ 0 := by
  intro hf
  have hd := phi_shiftedArgument_step b z k hb hk hk1
  rw [hf, zero_mul] at hd
  exact phi_ne_zero b _ hb hk1 hd

lemma continuationDenominator_nat_step (b z : ℂ) (n : ℕ) :
    continuationDenominator b z ((n : ℤ) + 1) =
      continuationDenominator b z (n : ℤ) *
        continuationFactor b (shiftedArgument b z (n : ℤ) - Complex.I * b / 2) := by
  have hn : 0 ≤ (n : ℤ) := by omega
  have hn1 : 0 ≤ (n : ℤ) + 1 := by omega
  have hnat : ((n : ℤ) + 1).toNat = n + 1 := by omega
  simp only [continuationDenominator, if_pos hn, if_pos hn1, hnat,
    Int.toNat_natCast, shiftedArgument_succ]
  exact continuation_prod_pos_step b (shiftedArgument b z (n : ℤ)) n

lemma phiChart_nat_step (b z : ℂ) (n : ℕ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z (n : ℤ)))
    (hk1 : InStrip b (shiftedArgument b z ((n : ℤ) + 1))) :
    phiChart b z ((n : ℤ) + 1) = phiChart b z (n : ℤ) := by
  have hn : 0 ≤ (n : ℤ) := by omega
  have hn1 : 0 ≤ (n : ℤ) + 1 := by omega
  unfold phiChart
  rw [continuationDenominator_nat_step]
  simp only [continuationNumerator, if_pos hn, if_pos hn1]
  rw [phi_shiftedArgument_step b z (n : ℤ) hb hk hk1, mul_comm
    (continuationFactor b _) (phi b _)]
  exact mul_div_mul_right _ _ (continuation_step_factor_ne_zero b z (n : ℤ) hb hk hk1)

lemma continuationNumerator_neg_nat (b z : ℂ) (n : ℕ) :
    continuationNumerator b z (-(n : ℤ)) =
      phi b (shiftedArgument b z (-(n : ℤ))) *
        ∏ j ∈ Finset.range n, continuationFactor b
          (shiftedArgument b z (-(n : ℤ)) - ((j : ℂ) + 1 / 2) * Complex.I * b) := by
  cases n with
  | zero => simp [continuationNumerator]
  | succ n =>
    have hn : ¬ 0 ≤ -((n + 1 : ℕ) : ℤ) := by omega
    simp only [continuationNumerator, if_neg hn, neg_neg, Int.toNat_natCast]

lemma continuationDenominator_neg_nat (b z : ℂ) (n : ℕ) :
    continuationDenominator b z (-(n : ℤ)) = 1 := by
  cases n with
  | zero => simp [continuationDenominator]
  | succ n =>
    have hn : ¬ 0 ≤ -((n + 1 : ℕ) : ℤ) := by omega
    simp only [continuationDenominator, if_neg hn]

lemma phiChart_neg_nat (b z : ℂ) (n : ℕ) :
    phiChart b z (-(n : ℤ)) =
      phi b (shiftedArgument b z (-(n : ℤ))) *
        ∏ j ∈ Finset.range n, continuationFactor b
          (shiftedArgument b z (-(n : ℤ)) - ((j : ℂ) + 1 / 2) * Complex.I * b) := by
  rw [phiChart, continuationNumerator_neg_nat, continuationDenominator_neg_nat, div_one]

lemma phiChart_neg_step (b z : ℂ) (n : ℕ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z (-(n : ℤ))))
    (hk1 : InStrip b (shiftedArgument b z (-((n + 1 : ℕ) : ℤ)))) :
    phiChart b z (-((n + 1 : ℕ) : ℤ)) = phiChart b z (-(n : ℤ)) := by
  have hs : shiftedArgument b z (-((n + 1 : ℕ) : ℤ)) =
      shiftedArgument b z (-(n : ℤ)) + Complex.I * b := by
    unfold shiftedArgument
    push_cast
    ring
  have hm : shiftedArgument b z (-(n : ℤ)) + Complex.I * b / 2 - Complex.I * b / 2 =
      shiftedArgument b z (-(n : ℤ)) := by ring
  have hp : shiftedArgument b z (-(n : ℤ)) + Complex.I * b / 2 + Complex.I * b / 2 =
      shiftedArgument b z (-((n + 1 : ℕ) : ℤ)) := by rw [hs]; ring
  have hd := phi_difference_b b (shiftedArgument b z (-(n : ℤ)) + Complex.I * b / 2) hb
    (by rw [hm]; exact hk) (by rw [hp]; exact hk1)
  simp only [hm, hp] at hd
  change phi b (shiftedArgument b z (-(n : ℤ))) =
    continuationFactor b (shiftedArgument b z (-(n : ℤ)) + Complex.I * b / 2) *
      phi b (shiftedArgument b z (-((n + 1 : ℕ) : ℤ))) at hd
  rw [phiChart_neg_nat, phiChart_neg_nat, hs, continuation_prod_neg_step]
  rw [hd, hs]
  ring

lemma phiChart_step (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k))
    (hk1 : InStrip b (shiftedArgument b z (k + 1))) :
    phiChart b z (k + 1) = phiChart b z k := by
  rcases le_or_gt 0 k with hpos | hneg
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    exact phiChart_nat_step b z n hb hk hk1
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hneg
    have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    have hn1 : Int.negSucc n + 1 = -(n : ℤ) := by omega
    have hd := phiChart_neg_step b z n hb
      (by simpa only [hn1] using hk1) (by simpa only [hn] using hk)
    rw [hn1, hn]
    exact hd.symm

lemma phiChart_pointwise (b z : ℂ) (k l : ℤ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k))
    (hl : InStrip b (shiftedArgument b z l)) :
    phiChart b z k = phiChart b z l := by
  wlog hkl : k ≤ l generalizing k l
  · exact (this l k hl hk (by omega)).symm
  have h : ∀ j : ℤ, k ≤ j → j ≤ l → phiChart b z k = phiChart b z j := by
    intro j hkj
    induction j, hkj using Int.leInduction with
    | base => intro _; rfl
    | succ j hkj ih =>
      intro hjl
      have hjl' : j ≤ l := by omega
      have hj := inStrip_shiftedArgument_between b z k j l hb hkj hjl' hk hl
      have hj1 := inStrip_shiftedArgument_between b z k (j + 1) l hb (by omega) hjl hk hl
      exact (ih hjl').trans (phiChart_step b z j hb hj hj1).symm
  exact h l hkl le_rfl

lemma phiZeroIndices_eq_pole_neg (b z : ℂ) :
    phiZeroIndices b z = phiPoleIndices b (-z) := by
  ext mn
  change z = -phiPolePoint b mn.1 mn.2 ↔ -z = phiPolePoint b mn.1 mn.2
  constructor <;> intro h <;> simpa using congrArg Neg.neg h

lemma phiPolePoint_mul_neg_I_mul (b : ℂ) (hb : b ≠ 0) (m n : ℕ) :
    phiPolePoint b m n * (-Complex.I * b) =
      (b ^ 2 + 1) / 2 + ((m : ℂ) * b ^ 2 + (n : ℂ)) := by
  unfold phiPolePoint
  field_simp
  ring_nf
  simp [Complex.I_sq]

lemma phiPolePoint_injective_of_im_sq_ne_zero (b : ℂ) (hb : AdmissibleB b)
    (hi : (b ^ 2).im ≠ 0) :
    Function.Injective (fun mn : ℕ × ℕ => phiPolePoint b mn.1 mn.2) := by
  intro mn pq heq
  have heq' := congrArg (fun w : ℂ => w * (-Complex.I * b)) heq
  rw [phiPolePoint_mul_neg_I_mul b (admissibleB_ne_zero b hb),
    phiPolePoint_mul_neg_I_mul b (admissibleB_ne_zero b hb)] at heq'
  have hlin : (mn.1 : ℂ) * b ^ 2 + (mn.2 : ℂ) =
      (pq.1 : ℂ) * b ^ 2 + (pq.2 : ℂ) := add_left_cancel heq'
  have hmi : (mn.1 : ℝ) * (b ^ 2).im = (pq.1 : ℝ) * (b ^ 2).im := by
    simpa [Complex.mul_im] using congrArg Complex.im hlin
  have hm : mn.1 = pq.1 := by exact_mod_cast (mul_right_cancel₀ hi hmi)
  have hn : mn.2 = pq.2 := by
    rw [hm] at hlin
    exact_mod_cast (add_left_cancel hlin)
  exact Prod.ext hm hn

lemma phiPolePoint_one (m n : ℕ) :
    phiPolePoint 1 m n = Complex.I * ((m : ℂ) + (n : ℂ) + 1) := by
  simp only [phiPolePoint, inv_one, mul_one]
  ring

open scoped Classical in
lemma natCard_eq_sum_fst_exists (s : Set (ℕ × ℕ)) (a : ℕ)
    (hbound : ∀ p ∈ s, p.1 < a) (hinj : Set.InjOn Prod.fst s) :
    Nat.card s = ∑ m ∈ Finset.range a,
      if ∃ n : ℕ, (m, n) ∈ s then 1 else 0 := by
  classical
  let t : Finset ℕ := (Finset.range a).filter (fun m => ∃ n : ℕ, (m, n) ∈ s)
  have himg : Prod.fst '' s = (t : Set ℕ) := by
    ext m
    constructor
    · rintro ⟨⟨k,n⟩, hkn, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hbound (k,n) hkn), ⟨n,hkn⟩⟩
    · intro hmt
      obtain ⟨_, n, hmn⟩ := Finset.mem_filter.mp hmt
      exact ⟨(m,n), hmn, rfl⟩
  calc
    Nat.card s = Nat.card (Prod.fst '' s) := (Nat.card_image_of_injOn hinj).symm
    _ = t.card := by
      rw [himg]
      exact Nat.subtype_card t (fun _ => Iff.rfl)
    _ = ∑ m ∈ Finset.range a, if ∃ n : ℕ, (m, n) ∈ s then 1 else 0 :=
      Finset.card_filter _ _

lemma phiPoleIndices_injOn_fst (b z : ℂ) (hb : AdmissibleB b) :
    Set.InjOn Prod.fst (phiPoleIndices b z) := by
  intro mn hmn pq hpq hfst
  have heq : phiPolePoint b mn.1 mn.2 = phiPolePoint b pq.1 pq.2 :=
    hmn.symm.trans hpq
  unfold phiPolePoint at heq
  rw [hfst] at heq
  have hs : (mn.2 : ℂ) * Complex.I * b⁻¹ =
      (pq.2 : ℂ) * Complex.I * b⁻¹ := add_left_cancel heq
  have hn : mn.2 = pq.2 := by
    exact_mod_cast (mul_right_cancel₀ Complex.I_ne_zero
      (mul_right_cancel₀ (inv_ne_zero (admissibleB_ne_zero b hb)) hs))
  exact Prod.ext hfst hn

open scoped Classical in
lemma phiPoleMultiplicity_eq_sum_fst (b z : ℂ) (a : ℕ) (hb : AdmissibleB b)
    (hbound : ∀ p ∈ phiPoleIndices b z, p.1 < a) :
    phiPoleMultiplicity b z = ∑ m ∈ Finset.range a,
      if ∃ n : ℕ, z = phiPolePoint b m n then 1 else 0 := by
  exact natCard_eq_sum_fst_exists (phiPoleIndices b z) a hbound
    (phiPoleIndices_injOn_fst b z hb)

lemma meromorphicOrderAt_continuationProduct (b z : ℂ) (k : ℤ)
    (s : Finset ℕ) (c : ℕ → ℂ) (hb : b ≠ 0) :
    meromorphicOrderAt (fun w => ∏ j ∈ s,
      continuationFactor b (shiftedArgument b w k + c j)) z =
      ∑ j ∈ s, if continuationFactor b (shiftedArgument b z k + c j) = 0
        then (1 : WithTop ℤ) else 0 := by
  classical
  rw [meromorphicOrderAt_fun_prod]
  · apply Finset.sum_congr rfl
    intro j _
    exact meromorphicOrderAt_continuationFactor_shifted_add b z k (c j) hb
  · intro j _
    exact ((analyticAt_continuationFactor b _).comp
      (f := fun w : ℂ => shiftedArgument b w k + c j)
      ((analyticAt_shiftedArgument b z k).add analyticAt_const)).meromorphicAt

open scoped Classical in
lemma phiPoleMultiplicity_eq_sum_reflected (b z : ℂ) (a : ℕ) (hb : AdmissibleB b)
    (hz : InStrip b (shiftedArgument b z a)) :
    (∑ j ∈ Finset.range a,
      if ∃ n : ℕ, z = phiPolePoint b (a - 1 - j) n then (1 : WithTop ℤ) else 0) =
      (phiPoleMultiplicity b z : WithTop ℤ) := by
  classical
  rw [Finset.sum_range_reflect
    (fun m => if ∃ n : ℕ, z = phiPolePoint b m n then (1 : WithTop ℤ) else 0) a]
  have hc := phiPoleMultiplicity_eq_sum_fst b z a hb
    (fun p hp => phiPolePoint_first_index_lt b z a p.1 p.2 hb hz hp)
  rw [hc]
  push_cast
  rfl

lemma meromorphicOrderAt_continuationDenominator_nat (b z : ℂ) (a : ℕ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z a)) :
    meromorphicOrderAt (fun w => continuationDenominator b w a) z =
      (phiPoleMultiplicity b z : WithTop ℤ) := by
  classical
  simp only [continuationDenominator, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]
  rw [meromorphicOrderAt_continuationProduct b z (a : ℤ) (Finset.range a)
    (fun j => ((j : ℂ) + 1 / 2) * Complex.I * b) (admissibleB_ne_zero b hb)]
  convert phiPoleMultiplicity_eq_sum_reflected b z a hb hz using 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [continuationFactor_positive_zero_iff b z a j hb hz (Finset.mem_range.mp hj)]

lemma meromorphicOrderAt_continuationNegativeProduct (b z : ℂ) (a : ℕ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z (-(a : ℤ)))) :
    meromorphicOrderAt (fun w => ∏ j ∈ Finset.range a,
      continuationFactor b (shiftedArgument b w (-(a : ℤ)) -
        ((j : ℂ) + 1 / 2) * Complex.I * b)) z =
      (phiZeroMultiplicity b z : WithTop ℤ) := by
  classical
  simp_rw [sub_eq_add_neg]
  rw [meromorphicOrderAt_continuationProduct b z (-(a : ℤ)) (Finset.range a)
    (fun j => -(((j : ℂ) + 1 / 2) * Complex.I * b)) (admissibleB_ne_zero b hb)]
  have hzn : InStrip b (shiftedArgument b (-z) a) := by
    have hs : shiftedArgument b (-z) a = -shiftedArgument b z (-(a : ℤ)) := by
      simpa only [neg_neg] using shiftedArgument_neg b z (-(a : ℤ))
    simpa only [hs, InStrip, Complex.neg_im, abs_neg] using hz
  have hc : phiZeroMultiplicity b z = phiPoleMultiplicity b (-z) := by
    simp only [phiZeroMultiplicity, phiZeroIndices_eq_pole_neg, phiPoleMultiplicity]
  rw [hc]
  convert phiPoleMultiplicity_eq_sum_reflected b (-z) a hb hzn using 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← sub_eq_add_neg, continuationFactor_negative_zero_iff b z a j hb hz
    (Finset.mem_range.mp hj)]

lemma meromorphicOrderAt_phi_shiftedArgument (b z : ℂ) (k : ℤ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z k)) :
    meromorphicOrderAt (fun w => phi b (shiftedArgument b w k)) z = 0 := by
  have ha : AnalyticAt ℂ (fun w => phi b (shiftedArgument b w k)) z :=
    (analyticAt_phi_of_inStrip b _ hb hz).comp
      (f := fun w : ℂ => shiftedArgument b w k) (analyticAt_shiftedArgument b z k)
  rw [ha.meromorphicOrderAt_eq,
    ha.analyticOrderAt_eq_zero.mpr (phi_ne_zero b _ hb hz)]
  rfl

/-- Rounding really reaches the strip. The strict surplus is `Re(b⁻¹)/2`, even at a rounding tie. -/
theorem shiftedArgument_inStrip (b z : ℂ) (hb : AdmissibleB b) :
    InStrip b (shiftedArgument b z (continuationIndex b z)) := by
  have hlow := Int.floor_le (z.im / b.re + (1 / 2 : ℝ))
  have hupp := Int.lt_floor_add_one (z.im / b.re + (1 / 2 : ℝ))
  change ((continuationIndex b z : ℤ) : ℝ) ≤ z.im / b.re + 1 / 2 at hlow
  change z.im / b.re + 1 / 2 < ((continuationIndex b z : ℤ) : ℝ) + 1 at hupp
  have hlow' : (continuationIndex b z : ℝ) - 1 / 2 ≤ z.im / b.re := by linarith
  have hupp' : z.im / b.re < (continuationIndex b z : ℝ) + 1 / 2 := by linarith
  have hl := (le_div_iff₀ hb).mp hlow'
  have hu := (div_lt_iff₀ hb).mp hupp'
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  unfold InStrip
  rw [shiftedArgument_im, abs_lt]
  unfold stripWidth
  constructor <;> nlinarith

lemma phiExtended_eq_phiChart (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k)) :
    phiExtended b z = phiChart b z k :=
  phiChart_pointwise b z (continuationIndex b z) k hb
    (shiftedArgument_inStrip b z hb) hk

lemma phiExtended_eq_chart_nhds (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k)) :
    phiExtended b =ᶠ[𝓝 z] (fun w => phiChart b w k) := by
  have hsk : ContinuousAt (fun w : ℂ => shiftedArgument b w k) z :=
    (analyticAt_shiftedArgument b z k).continuousAt
  have hek : ∀ᶠ w : ℂ in 𝓝 z, InStrip b (shiftedArgument b w k) :=
    hsk.eventually ((isOpen_inStrip b).mem_nhds hk)
  exact hek.mono (fun w hw => phiExtended_eq_phiChart b w k hb hw)

/-- Fixed-index charts agree as meromorphic germs on overlapping strips. -/
theorem phiChart_overlap (b z : ℂ) (k l : ℤ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k))
    (hl : InStrip b (shiftedArgument b z l)) :
    (fun w : ℂ => phiChart b w k) =ᶠ[𝓝[≠] z] (fun w => phiChart b w l) := by
  have hsk := (analyticAt_shiftedArgument b z k).continuousAt
  have hsl := (analyticAt_shiftedArgument b z l).continuousAt
  have hek : ∀ᶠ w : ℂ in 𝓝 z, InStrip b (shiftedArgument b w k) :=
    hsk.eventually ((isOpen_inStrip b).mem_nhds hk)
  have hel : ∀ᶠ w : ℂ in 𝓝 z, InStrip b (shiftedArgument b w l) :=
    hsl.eventually ((isOpen_inStrip b).mem_nhds hl)
  exact (((hek.and hel).mono
    (fun w hw => phiChart_pointwise b w k l hb hw.1 hw.2)).filter_mono nhdsWithin_le_nhds)

/-- The discontinuous rounding selector can be replaced locally by a fixed index. This is a germ
assertion and does not assert the selector is continuous. -/
theorem phiExtended_eq_chart (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k)) :
    phiExtended b =ᶠ[𝓝[≠] z] (fun w => phiChart b w k) := by
  exact (phiExtended_eq_chart_nhds b z k hb hk).filter_mono nhdsWithin_le_nhds

theorem phiExtended_eq_phi (b z : ℂ) (hb : AdmissibleB b) (hz : InStrip b z) :
    phiExtended b z = phi b z := by
  have h := phiExtended_eq_phiChart b z 0 hb (by simpa [shiftedArgument] using hz)
  simpa [phiChart, continuationNumerator, continuationDenominator, shiftedArgument] using h

theorem phiExtended_meromorphic (b : ℂ) (hb : AdmissibleB b) :
    MeromorphicOn (phiExtended b) Set.univ := by
  intro z _
  exact (meromorphicAt_phiChart b z (continuationIndex b z) hb
    (shiftedArgument_inStrip b z hb)).congr (phiExtended_eq_chart b z
      (continuationIndex b z) hb (shiftedArgument_inStrip b z hb)).symm

theorem phiPoleIndices_finite (b z : ℂ) (hb : AdmissibleB b) :
    (phiPoleIndices b z).Finite := by
  have hbi : 0 < (b⁻¹).re := admissibleB_inv b hb
  change 0 < b.re at hb
  obtain ⟨M, hM⟩ := exists_nat_gt (z.im / b.re)
  obtain ⟨N, hN⟩ := exists_nat_gt (z.im / (b⁻¹).re)
  refine ((Set.finite_lt_nat M).prod (Set.finite_lt_nat N)).subset ?_
  rintro ⟨m, n⟩ hmn
  have him := congrArg Complex.im hmn
  rw [phiPolePoint_im] at him
  dsimp [stripWidth] at him
  have hmreal : (m : ℝ) < M := by
    apply lt_of_le_of_lt ?_ hM
    apply (le_div_iff₀ hb).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hbi.le]
  have hnreal : (n : ℝ) < N := by
    apply lt_of_le_of_lt ?_ hN
    apply (le_div_iff₀ hbi).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hb.le]
  exact ⟨by exact_mod_cast hmreal, by exact_mod_cast hnreal⟩

theorem phiZeroIndices_finite (b z : ℂ) (hb : AdmissibleB b) :
    (phiZeroIndices b z).Finite := by
  rw [phiZeroIndices_eq_pole_neg]
  exact phiPoleIndices_finite b (-z) hb

lemma phiPoleMultiplicity_eq_zero_iff (b z : ℂ) (hb : AdmissibleB b) :
    phiPoleMultiplicity b z = 0 ↔ ∀ m n : ℕ, z ≠ phiPolePoint b m n := by
  change (phiPoleIndices b z).ncard = 0 ↔ _
  rw [Set.ncard_eq_zero (phiPoleIndices_finite b z hb), Set.eq_empty_iff_forall_notMem]
  simp only [phiPoleIndices, Set.mem_ofPred_eq, Prod.forall]

lemma continuousAt_phiPolePoint (p : ℂ × ℂ) (hp : AdmissibleB p.1) (m n : ℕ) :
    ContinuousAt (fun q : ℂ × ℂ => phiPolePoint q.1 m n) p := by
  have hbi : ContinuousAt (fun q : ℂ × ℂ => q.1⁻¹) p :=
    continuousAt_fst.inv₀ (admissibleB_ne_zero p.1 hp)
  unfold phiPolePoint
  fun_prop

/-- A single finite set of branch indices suffices on a bounded `z` disk for all `b` in a
sufficiently small neighborhood. Since zero branches are negatives of pole branches, this controls
both multisets. -/
theorem phiDivisor_uniform_local_finiteness (b₀ : ℂ) (hb : AdmissibleB b₀)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, 0 < r ∧
      (∀ b : ℂ, dist b b₀ < r → AdmissibleB b) ∧
      {mn : ℕ × ℕ | ∃ b : ℂ, dist b b₀ < r ∧
        ‖phiPolePoint b mn.1 mn.2‖ ≤ R}.Finite := by
  have _hR := hR
  let a : ℝ := b₀.re / 2
  let c : ℝ := (b₀⁻¹).re / 2
  have ha : 0 < a := half_pos hb
  have hc : 0 < c := half_pos (admissibleB_inv b₀ hb)
  have hre : ContinuousAt (fun b : ℂ => b.re) b₀ :=
    Complex.continuous_re.continuousAt
  have hrei : ContinuousAt (fun b : ℂ => (b⁻¹).re) b₀ :=
    Complex.continuous_re.continuousAt.comp
      (continuousAt_id.inv₀ (admissibleB_ne_zero b₀ hb))
  have hS : {b : ℂ | a < b.re ∧ c < (b⁻¹).re} ∈ 𝓝 b₀ := by
    have hba : a < b₀.re := by dsimp [a] at ha ⊢; linarith
    have hbc : c < (b₀⁻¹).re := by dsimp [c] at hc ⊢; linarith
    filter_upwards [continuousAt_const.eventually_lt hre hba,
      continuousAt_const.eventually_lt hrei hbc] with b hba hbc
    exact ⟨hba, hbc⟩
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨r, hr, ?_, ?_⟩
  · intro b hbr
    exact lt_trans ha (hrs hbr).1
  · obtain ⟨M, hM⟩ := exists_nat_gt (R / a)
    obtain ⟨N, hN⟩ := exists_nat_gt (R / c)
    refine ((Set.finite_lt_nat M).prod (Set.finite_lt_nat N)).subset ?_
    rintro ⟨m, n⟩ ⟨b, hbr, hnorm⟩
    have hba : a < b.re := (hrs hbr).1
    have hbc : c < (b⁻¹).re := (hrs hbr).2
    have hbpos : 0 < b.re := lt_trans ha hba
    have hbipos : 0 < (b⁻¹).re := lt_trans hc hbc
    have himle : (phiPolePoint b m n).im ≤ R :=
      (Complex.im_le_norm _).trans hnorm
    rw [phiPolePoint_im] at himle
    dsimp [stripWidth] at himle
    have hmprod : (m : ℝ) * a ≤ (m : ℝ) * b.re :=
      mul_le_mul_of_nonneg_left hba.le (Nat.cast_nonneg m)
    have hnprod : (n : ℝ) * c ≤ (n : ℝ) * (b⁻¹).re :=
      mul_le_mul_of_nonneg_left hbc.le (Nat.cast_nonneg n)
    have hmreal : (m : ℝ) < M := by
      apply lt_of_le_of_lt ?_ hM
      apply (le_div_iff₀ ha).mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hbipos.le]
    have hnreal : (n : ℝ) < N := by
      apply lt_of_le_of_lt ?_ hN
      apply (le_div_iff₀ hc).mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hbpos.le]
    exact ⟨by exact_mod_cast hmreal, by exact_mod_cast hnreal⟩

/-- Upper and lower divisor branches never cancel for `Re b > 0`. -/
theorem phiDivisor_disjoint (b : ℂ) (hb : AdmissibleB b) :
    Disjoint (Set.range (fun mn : ℕ × ℕ => phiPolePoint b mn.1 mn.2))
      (Set.range (fun mn : ℕ × ℕ => phiZeroPoint b mn.1 mn.2)) := by
  rw [Set.disjoint_left]
  rintro z ⟨⟨m, n⟩, rfl⟩ ⟨⟨m', n'⟩, heq⟩
  have hp := phiPolePoint_im_pos b hb m n
  have hp' := phiPolePoint_im_pos b hb m' n'
  have hi := congrArg Complex.im heq
  simp only [phiZeroPoint, Complex.neg_im] at hi
  linarith

lemma meromorphicOrderAt_phiChart (b z : ℂ) (k : ℤ) (hb : AdmissibleB b)
    (hz : InStrip b (shiftedArgument b z k)) :
    meromorphicOrderAt (fun w => phiChart b w k) z =
      (phiDivisorOrder b z : WithTop ℤ) := by
  classical
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have hz0 : phiZeroMultiplicity b z = 0 := by
      simp [phiZeroMultiplicity, phiZeroIndices_empty_of_nonneg_shift b z a hb
        (by omega) hz]
    have hn : meromorphicOrderAt (fun w => continuationNumerator b w a) z = 0 := by
      simpa only [continuationNumerator, Nat.cast_nonneg, ↓reduceIte] using
        meromorphicOrderAt_phi_shiftedArgument b z a hb hz
    change meromorphicOrderAt ((fun w => continuationNumerator b w a) /
      (fun w => continuationDenominator b w a)) z = _
    rw [meromorphicOrderAt_div (analyticAt_continuationNumerator b z a hb hz).meromorphicAt
      (analyticAt_continuationDenominator b z a).meromorphicAt, hn,
      meromorphicOrderAt_continuationDenominator_nat b z a hb hz]
    simp [phiDivisorOrder, hz0]
  · obtain ⟨a, rfl⟩ := Int.eq_negSucc_of_lt_zero hk
    have hk' : Int.negSucc a = -((a + 1 : ℕ) : ℤ) := by omega
    rw [hk'] at hz ⊢
    have hp0 : phiPoleMultiplicity b z = 0 := by
      simp [phiPoleMultiplicity, phiPoleIndices_empty_of_nonpos_shift b z
        (-((a + 1 : ℕ) : ℤ)) hb (by omega) hz]
    simp_rw [phiChart_neg_nat]
    have hphi : AnalyticAt ℂ
        (fun w => phi b (shiftedArgument b w (-((a + 1 : ℕ) : ℤ)))) z :=
      (analyticAt_phi_of_inStrip b _ hb hz).comp
        (f := fun w : ℂ => shiftedArgument b w (-((a + 1 : ℕ) : ℤ)))
        (analyticAt_shiftedArgument b z (-((a + 1 : ℕ) : ℤ)))
    have hprod : MeromorphicAt (fun w : ℂ => ∏ j ∈ Finset.range (a + 1),
        continuationFactor b (shiftedArgument b w (-((a + 1 : ℕ) : ℤ)) -
          ((j : ℂ) + 1 / 2) * Complex.I * b)) z := by
      apply MeromorphicAt.fun_prod
      intro j _
      apply AnalyticAt.meromorphicAt
      apply (analyticAt_continuationFactor b _).comp
        (f := fun w : ℂ => shiftedArgument b w (-((a + 1 : ℕ) : ℤ)) -
          ((j : ℂ) + 1 / 2) * Complex.I * b)
      exact (analyticAt_shiftedArgument b z _).sub analyticAt_const
    rw [fun_meromorphicOrderAt_mul hphi.meromorphicAt hprod,
      meromorphicOrderAt_phi_shiftedArgument b z _ hb hz,
      meromorphicOrderAt_continuationNegativeProduct b z (a + 1) hb hz]
    simp [phiDivisorOrder, hp0]

/-- Exact order, including coincident branches (for example `b = 1`). -/
theorem phiExtended_order (b z : ℂ) (hb : AdmissibleB b) :
    meromorphicOrderAt (phiExtended b) z = (phiDivisorOrder b z : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr (phiExtended_eq_chart b z (continuationIndex b z) hb
    (shiftedArgument_inStrip b z hb))]
  exact meromorphicOrderAt_phiChart b z (continuationIndex b z) hb
    (shiftedArgument_inStrip b z hb)

lemma phiZeroMultiplicity_eq_zero_iff (b z : ℂ) (hb : AdmissibleB b) :
    phiZeroMultiplicity b z = 0 ↔ ∀ m n : ℕ, z ≠ phiZeroPoint b m n := by
  rw [← not_iff_not]
  change phiZeroMultiplicity b z ≠ 0 ↔ ¬∀ m n : ℕ, z ≠ phiZeroPoint b m n
  rw [← Nat.pos_iff_ne_zero]
  change 0 < Nat.card (phiZeroIndices b z) ↔ _
  rw [Set.natCard_pos (phiZeroIndices_finite b z hb)]
  simp [phiZeroIndices, Set.Nonempty, Prod.exists]

lemma continuationDenominator_nat_eq_zero_iff (b z : ℂ) (a : ℕ) (hb : AdmissibleB b)
    (hz : InStrip b (shiftedArgument b z a)) :
    continuationDenominator b z (a : ℤ) = 0 ↔ ∃ m n : ℕ, z = phiPolePoint b m n := by
  classical
  simp only [continuationDenominator, Int.natCast_nonneg, if_pos, Int.toNat_natCast]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hf⟩
    obtain ⟨n, hn⟩ := (continuationFactor_positive_zero_iff b z a j hb hz
      (Finset.mem_range.mp hj)).mp hf
    exact ⟨a - 1 - j, n, hn⟩
  · rintro ⟨m, n, hmn⟩
    have hm : m < a := phiPolePoint_first_index_lt b z a m n hb hz hmn
    have hj : a - 1 - m < a := by omega
    refine ⟨a - 1 - m, Finset.mem_range.mpr hj, ?_⟩
    apply (continuationFactor_positive_zero_iff b z a (a - 1 - m) hb hz hj).mpr
    refine ⟨n, ?_⟩
    have hm' : a - 1 - (a - 1 - m) = m := by omega
    rwa [hm']

lemma continuationDenominator_eq_zero_iff_pole (b z : ℂ) (k : ℤ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z k)) :
    continuationDenominator b z k = 0 ↔ ∃ m n : ℕ, z = phiPolePoint b m n := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact continuationDenominator_nat_eq_zero_iff b z a hb hz
  · have hempty := phiPoleIndices_empty_of_nonpos_shift b z k hb hk.le hz
    have hd : continuationDenominator b z k = 1 := by
      simp only [continuationDenominator, if_neg (not_le.mpr hk)]
    rw [hd]
    simp only [one_ne_zero, false_iff]
    rintro ⟨m, n, hmn⟩
    have hmem : (m, n) ∈ phiPoleIndices b z := hmn
    rw [hempty] at hmem
    exact hmem

lemma continuationNumerator_neg_nat_eq_zero_iff (b z : ℂ) (a : ℕ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z (-(a : ℤ)))) :
    continuationNumerator b z (-(a : ℤ)) = 0 ↔ ∃ m n : ℕ, z = phiZeroPoint b m n := by
  classical
  have hs : shiftedArgument b (-z) (a : ℤ) = -shiftedArgument b z (-(a : ℤ)) := by
    simp only [shiftedArgument, Int.cast_neg]
    ring
  have hzs : InStrip b (shiftedArgument b (-z) (a : ℤ)) := by
    rw [hs]
    simpa [InStrip] using hz
  have hprod : (∏ j ∈ Finset.range a, continuationFactor b
      (shiftedArgument b z (-(a : ℤ)) - ((j : ℂ) + 1 / 2) * Complex.I * b)) = 0 ↔
      continuationDenominator b (-z) (a : ℤ) = 0 := by
    simp only [continuationDenominator, Int.natCast_nonneg, if_pos,
      Int.toNat_natCast, Finset.prod_eq_zero_iff]
    apply exists_congr
    intro j
    apply and_congr_right
    intro _
    have harg : shiftedArgument b (-z) (a : ℤ) + ((j : ℂ) + 1 / 2) * Complex.I * b =
        -(shiftedArgument b z (-(a : ℤ)) - ((j : ℂ) + 1 / 2) * Complex.I * b) := by
      rw [hs]
      ring
    rw [harg, continuationFactor_neg_eq_zero_iff]
  rw [continuationNumerator_neg_nat, mul_eq_zero]
  simp only [phi_ne_zero b _ hb hz, false_or]
  rw [hprod, continuationDenominator_nat_eq_zero_iff b (-z) a hb hzs]
  constructor <;> rintro ⟨m, n, hmn⟩ <;> refine ⟨m, n, ?_⟩ <;>
    simpa [phiZeroPoint] using congrArg Neg.neg hmn

lemma continuationNumerator_eq_zero_iff_zero (b z : ℂ) (k : ℤ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z k)) :
    continuationNumerator b z k = 0 ↔ ∃ m n : ℕ, z = phiZeroPoint b m n := by
  rcases le_or_gt 0 k with hk | hk
  · simp only [continuationNumerator, if_pos hk]
    constructor
    · intro hf
      exact False.elim (phi_ne_zero b _ hb hz hf)
    · rintro ⟨m, n, hmn⟩
      have hempty := phiZeroIndices_empty_of_nonneg_shift b z k hb hk hz
      have hmem : (m, n) ∈ phiZeroIndices b z := hmn
      rw [hempty] at hmem
      exact hmem.elim
  · obtain ⟨a, rfl⟩ := Int.eq_negSucc_of_lt_zero hk
    have ha : Int.negSucc a = -((a + 1 : ℕ) : ℤ) := by omega
    rw [ha] at hz ⊢
    exact continuationNumerator_neg_nat_eq_zero_iff b z (a + 1) hb hz

lemma continuationDenominator_ne_zero_iff (b z : ℂ) (k : ℤ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z k)) :
    continuationDenominator b z k ≠ 0 ↔ phiPoleMultiplicity b z = 0 := by
  rw [ne_eq, continuationDenominator_eq_zero_iff_pole b z k hb hz]
  simpa only [not_exists] using (phiPoleMultiplicity_eq_zero_iff b z hb).symm

lemma continuationNumerator_ne_zero_iff (b z : ℂ) (k : ℤ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z k)) :
    continuationNumerator b z k ≠ 0 ↔ phiZeroMultiplicity b z = 0 := by
  rw [ne_eq, continuationNumerator_eq_zero_iff_zero b z k hb hz]
  simpa only [not_exists] using (phiZeroMultiplicity_eq_zero_iff b z hb).symm

theorem phiExtended_analyticAt (b z : ℂ) (hb : AdmissibleB b)
    (hp : phiPoleMultiplicity b z = 0) :
    AnalyticAt ℂ (phiExtended b) z := by
  let k := continuationIndex b z
  have hk : InStrip b (shiftedArgument b z k) := shiftedArgument_inStrip b z hb
  have hd : continuationDenominator b z k ≠ 0 :=
    (continuationDenominator_ne_zero_iff b z k hb hk).mpr hp
  have ha : AnalyticAt ℂ (fun w => phiChart b w k) z :=
    (analyticAt_continuationNumerator b z k hb hk).div
      (analyticAt_continuationDenominator b z k) hd
  exact ha.congr (phiExtended_eq_chart_nhds b z k hb hk).symm

/-- A point-value statement is made only away from poles. -/
theorem phiExtended_ne_zero_iff (b z : ℂ) (hb : AdmissibleB b)
    (hp : phiPoleMultiplicity b z = 0) :
    phiExtended b z ≠ 0 ↔ phiZeroMultiplicity b z = 0 := by
  let k := continuationIndex b z
  have hk : InStrip b (shiftedArgument b z k) := shiftedArgument_inStrip b z hb
  have hd : continuationDenominator b z k ≠ 0 :=
    (continuationDenominator_ne_zero_iff b z k hb hk).mpr hp
  rw [phiExtended_eq_phiChart b z k hb hk, phiChart, div_ne_zero_iff]
  exact (and_iff_left hd).trans (continuationNumerator_ne_zero_iff b z k hb hk)

/-- This records only the chosen representative's value at a pole. -/
theorem phiExtended_pole_value (b z : ℂ) (hb : AdmissibleB b)
    (hp : phiPoleMultiplicity b z ≠ 0) : phiExtended b z = 0 := by
  let k := continuationIndex b z
  have hk : InStrip b (shiftedArgument b z k) := shiftedArgument_inStrip b z hb
  have hd : continuationDenominator b z k = 0 := by
    by_contra hd
    exact hp ((continuationDenominator_ne_zero_iff b z k hb hk).mp hd)
  rw [phiExtended_eq_phiChart b z k hb hk, phiChart, hd, div_zero]

lemma meromorphic_germ_eq_global (f g : ℂ → ℂ)
    (hf : MeromorphicOn f Set.univ) (hg : MeromorphicOn g Set.univ)
    (z₀ : ℂ) (h₀ : f =ᶠ[𝓝[≠] z₀] g) (z : ℂ) :
    f =ᶠ[𝓝[≠] z] g := by
  have hd : MeromorphicOn (fun w => f w - g w) Set.univ := hf.fun_sub hg
  have htop₀ : meromorphicOrderAt (fun w => f w - g w) z₀ = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [h₀] with w hw
    exact sub_eq_zero.mpr hw
  have htop : meromorphicOrderAt (fun w => f w - g w) z = ⊤ := by
    by_contra hnot
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ z) (Set.mem_univ z₀) hnot) htop₀
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop] with w hw
  exact sub_eq_zero.mp hw

lemma phiExtended_difference_of_strip (b c z : ℂ) (hb : AdmissibleB b)
    (hc : 0 < c.re) (hwidth : c.re < b.re + (b⁻¹).re)
    (hdiff : ∀ w : ℂ,
      InStrip b (w - Complex.I * c / 2) →
      InStrip b (w + Complex.I * c / 2) →
      phi b (w - Complex.I * c / 2) =
        continuationFactor c w * phi b (w + Complex.I * c / 2)) :
    ∀ᶠ w : ℂ in 𝓝[≠] z,
      phiExtended b (w - Complex.I * c / 2) =
        continuationFactor c w * phiExtended b (w + Complex.I * c / 2) := by
  have hmer : MeromorphicOn (phiExtended b) Set.univ := phiExtended_meromorphic b hb
  have hm : MeromorphicOn (fun w => phiExtended b (w - Complex.I * c / 2)) Set.univ := by
    intro w _
    exact (hmer _ (Set.mem_univ _)).comp_analyticAt
      (g := fun x => x - Complex.I * c / 2) (by fun_prop)
  have hp : MeromorphicOn (fun w => phiExtended b (w + Complex.I * c / 2)) Set.univ := by
    intro w _
    exact (hmer _ (Set.mem_univ _)).comp_analyticAt
      (g := fun x => x + Complex.I * c / 2) (by fun_prop)
  have hcf : MeromorphicOn (continuationFactor c) Set.univ := by
    intro w _
    exact (analyticAt_continuationFactor c w).meromorphicAt
  apply meromorphic_germ_eq_global _ _ hm (hcf.fun_mul hp) 0 ?_ z
  have hh : (Complex.I * c / 2).im = c.re / 2 := by simp [Complex.mul_im]
  have hminus : InStrip b ((0 : ℂ) - Complex.I * c / 2) := by
    simp only [InStrip, zero_sub, Complex.neg_im, abs_neg, hh, abs_of_pos (half_pos hc)]
    unfold stripWidth
    linarith
  have hplus : InStrip b ((0 : ℂ) + Complex.I * c / 2) := by
    simp only [InStrip, zero_add, hh, abs_of_pos (half_pos hc)]
    unfold stripWidth
    linarith
  have hmn : ∀ᶠ w : ℂ in 𝓝 (0 : ℂ), InStrip b (w - Complex.I * c / 2) :=
    ((isOpen_inStrip b).preimage (continuous_id.sub continuous_const)).mem_nhds hminus
  have hpn : ∀ᶠ w : ℂ in 𝓝 (0 : ℂ), InStrip b (w + Complex.I * c / 2) :=
    ((isOpen_inStrip b).preimage (continuous_id.add continuous_const)).mem_nhds hplus
  filter_upwards [nhdsWithin_le_nhds hmn, nhdsWithin_le_nhds hpn] with w hwm hwp
  rw [phiExtended_eq_phi b _ hb hwm, phiExtended_eq_phi b _ hb hwp]
  exact hdiff w hwm hwp

theorem phiExtended_difference_b (b z : ℂ) (hb : AdmissibleB b) :
    ∀ᶠ w : ℂ in 𝓝[≠] z,
      phiExtended b (w - Complex.I * b / 2) =
        continuationFactor b w * phiExtended b (w + Complex.I * b / 2) := by
  refine phiExtended_difference_of_strip b b z hb hb ?_
    (fun w hm hp => phi_difference_b b w hb hm hp)
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  linarith

theorem phiExtended_difference_inv_b (b z : ℂ) (hb : AdmissibleB b) :
    ∀ᶠ w : ℂ in 𝓝[≠] z,
      phiExtended b (w - Complex.I * b⁻¹ / 2) =
        continuationFactor b⁻¹ w * phiExtended b (w + Complex.I * b⁻¹ / 2) := by
  refine phiExtended_difference_of_strip b b⁻¹ z hb (admissibleB_inv b hb) ?_
    (fun w hm hp => phi_difference_inv_b b w hb hm hp)
  have hb' : 0 < b.re := hb
  linarith

theorem phiExtended_inversion (b z : ℂ) (hb : AdmissibleB b) :
    ∀ᶠ w : ℂ in 𝓝[≠] z,
      phiExtended b w * phiExtended b (-w) =
        Complex.exp (Complex.I * (Real.pi : ℂ) * w ^ 2 +
          Complex.I * (Real.pi : ℂ) * (b ^ 2 + (b⁻¹) ^ 2) / 12) := by
  have hmer : MeromorphicOn (phiExtended b) Set.univ := phiExtended_meromorphic b hb
  have hn : MeromorphicOn (fun w => phiExtended b (-w)) Set.univ := by
    intro w _
    exact (hmer _ (Set.mem_univ _)).comp_analyticAt (g := fun x => -x) (by fun_prop)
  have he : MeromorphicOn (fun w : ℂ =>
      Complex.exp (Complex.I * (Real.pi : ℂ) * w ^ 2 +
        Complex.I * (Real.pi : ℂ) * (b ^ 2 + (b⁻¹) ^ 2) / 12)) Set.univ := by
    intro w _
    apply AnalyticAt.meromorphicAt
    fun_prop
  apply meromorphic_germ_eq_global _ _ (hmer.fun_mul hn) he 0 ?_ z
  have hb' : 0 < b.re := hb
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hzero : InStrip b 0 := by
    simp only [InStrip, Complex.zero_im, abs_zero]
    unfold stripWidth
    positivity
  filter_upwards [nhdsWithin_le_nhds ((isOpen_inStrip b).mem_nhds hzero)] with w hw
  have hneg : InStrip b (-w) := by simpa only [InStrip, Complex.neg_im, abs_neg] using hw
  rw [phiExtended_eq_phi b w hb hw, phiExtended_eq_phi b (-w) hb hneg]
  exact phi_inversion b w hb hw

lemma phiPoleMultiplicity_inv (b z : ℂ) :
    phiPoleMultiplicity b z = phiPoleMultiplicity b⁻¹ z := by
  have hswap (m n : ℕ) : phiPolePoint b⁻¹ m n = phiPolePoint b n m := by
    simp only [phiPolePoint, inv_inv]
    ring
  let e : phiPoleIndices b z ≃ phiPoleIndices b⁻¹ z := {
    toFun := fun mn => ⟨mn.val.swap, by
      change z = phiPolePoint b⁻¹ mn.val.2 mn.val.1
      rw [hswap]
      exact mn.property⟩
    invFun := fun mn => ⟨mn.val.swap, by
      change z = phiPolePoint b mn.val.2 mn.val.1
      rw [← hswap]
      exact mn.property⟩
    left_inv := by rintro ⟨⟨m, n⟩, hmn⟩; rfl
    right_inv := by rintro ⟨⟨m, n⟩, hmn⟩; rfl }
  exact Nat.card_congr e

/-- The representative convention is the same on both sides, even at poles. -/
theorem phiExtended_self_dual (b z : ℂ) (hb : AdmissibleB b) :
    phiExtended b z = phiExtended b⁻¹ z := by
  have hbi : AdmissibleB b⁻¹ := admissibleB_inv b hb
  have hfg : phiExtended b =ᶠ[𝓝[≠] z] phiExtended b⁻¹ := by
    apply meromorphic_germ_eq_global _ _ (phiExtended_meromorphic b hb)
      (phiExtended_meromorphic b⁻¹ hbi) 0 ?_ z
    have hb' : 0 < b.re := hb
    have hi : 0 < (b⁻¹).re := hbi
    have hzero : InStrip b 0 := by
      simp only [InStrip, Complex.zero_im, abs_zero]
      unfold stripWidth
      positivity
    filter_upwards [nhdsWithin_le_nhds ((isOpen_inStrip b).mem_nhds hzero)] with w hw
    have hwi : InStrip b⁻¹ w := by
      simpa only [InStrip, stripWidth, inv_inv, add_comm] using hw
    rw [phiExtended_eq_phi b w hb hw, phiExtended_eq_phi b⁻¹ w hbi hwi]
    exact phi_self_dual b w hb hw
  by_cases hp : phiPoleMultiplicity b z = 0
  · have hpi : phiPoleMultiplicity b⁻¹ z = 0 := by
      rw [← phiPoleMultiplicity_inv b z]
      exact hp
    exact tendsto_nhds_unique
      ((phiExtended_analyticAt b z hb hp).continuousAt.mono_left nhdsWithin_le_nhds)
      (((phiExtended_analyticAt b⁻¹ z hbi hpi).continuousAt.mono_left
        nhdsWithin_le_nhds).congr' hfg.symm)
  · have hpi : phiPoleMultiplicity b⁻¹ z ≠ 0 := by
      rw [← phiPoleMultiplicity_inv b z]
      exact hp
    rw [phiExtended_pole_value b z hb hp, phiExtended_pole_value b⁻¹ z hbi hpi]

/-- Strip agreement determines the meromorphic germ, not arbitrary assigned values at exceptional
centers of another representative. -/
theorem phiExtended_unique_germ (b z : ℂ) (f : ℂ → ℂ) (hb : AdmissibleB b)
    (hf : MeromorphicOn f Set.univ)
    (hstrip : ∀ w : ℂ, InStrip b w → f w = phi b w) :
    f =ᶠ[𝓝[≠] z] phiExtended b := by
  apply meromorphic_germ_eq_global f (phiExtended b) hf
    (phiExtended_meromorphic b hb) 0 ?_ z
  have hb' : 0 < b.re := hb
  have hi : 0 < (b⁻¹).re := admissibleB_inv b hb
  have hzero : InStrip b 0 := by
    simp only [InStrip, Complex.zero_im, abs_zero]
    unfold stripWidth
    positivity
  filter_upwards [nhdsWithin_le_nhds ((isOpen_inStrip b).mem_nhds hzero)] with w hw
  exact (hstrip w hw).trans (phiExtended_eq_phi b w hb hw).symm

theorem isOpen_phiRegularDomain : IsOpen phiRegularDomain := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  rcases hp with ⟨hb, hpole⟩
  let R : ℝ := ‖p.2‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨r, hr, hadm, hfin⟩ := phiDivisor_uniform_local_finiteness p.1 hb R hR
  let S : Set (ℕ × ℕ) := {mn | ∃ b : ℂ, dist b p.1 < r ∧
    ‖phiPolePoint b mn.1 mn.2‖ ≤ R}
  have hS : S.Finite := hfin
  have hnear : ∀ᶠ q : ℂ × ℂ in 𝓝 p, dist q.1 p.1 < r :=
    (continuousAt_fst.dist continuousAt_const).eventually_lt continuousAt_const
      (by simpa using hr)
  have hbound : ∀ᶠ q : ℂ × ℂ in 𝓝 p, ‖q.2‖ < R :=
    continuousAt_snd.norm.eventually_lt continuousAt_const (by dsimp [R]; linarith)
  have hpne := (phiPoleMultiplicity_eq_zero_iff p.1 p.2 hb).mp hpole
  have havoid : ∀ᶠ q : ℂ × ℂ in 𝓝 p,
      ∀ mn ∈ S, q.2 ≠ phiPolePoint q.1 mn.1 mn.2 := by
    apply hS.eventually_all.mpr
    intro mn _
    have hc : ContinuousAt (fun q : ℂ × ℂ => q.2 - phiPolePoint q.1 mn.1 mn.2) p :=
      continuousAt_snd.sub (continuousAt_phiPolePoint p hb mn.1 mn.2)
    have hne : p.2 - phiPolePoint p.1 mn.1 mn.2 ≠ 0 := sub_ne_zero.mpr (hpne mn.1 mn.2)
    simpa only [sub_ne_zero] using hc.eventually_ne hne
  change ∀ᶠ q : ℂ × ℂ in 𝓝 p, AdmissibleB q.1 ∧ phiPoleMultiplicity q.1 q.2 = 0
  filter_upwards [hnear, hbound, havoid] with q hnear hbound havoid
  have hqb : AdmissibleB q.1 := hadm q.1 hnear
  refine ⟨hqb, (phiPoleMultiplicity_eq_zero_iff q.1 q.2 hqb).mpr ?_⟩
  intro m n heq
  have hmn : (m, n) ∈ S := ⟨q.1, hnear, by rw [← heq]; exact hbound.le⟩
  exact havoid (m, n) hmn heq

lemma analyticAt_shiftedArgument_joint (p : ℂ × ℂ) (k : ℤ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => shiftedArgument q.1 q.2 k) p := by
  unfold shiftedArgument
  exact analyticAt_snd.sub (analyticAt_const.mul analyticAt_fst)

lemma analyticAt_continuationFactor_joint (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => continuationFactor q.1 q.2) p := by
  unfold continuationFactor
  exact analyticAt_const.add (((analyticAt_const.mul analyticAt_fst).mul analyticAt_snd).cexp')

lemma analyticAt_continuationDenominator_joint (p : ℂ × ℂ) (k : ℤ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => continuationDenominator q.1 q.2 k) p := by
  classical
  unfold continuationDenominator
  split_ifs
  · apply Finset.analyticAt_fun_prod
    intro j _
    have ht : AnalyticAt ℂ (fun q : ℂ × ℂ => shiftedArgument q.1 q.2 k +
        ((j : ℂ) + 1 / 2) * Complex.I * q.1) p :=
      (analyticAt_shiftedArgument_joint p k).add (analyticAt_const.mul analyticAt_fst)
    exact (analyticAt_continuationFactor_joint _).comp
      (f := fun q : ℂ × ℂ => (q.1, shiftedArgument q.1 q.2 k +
        ((j : ℂ) + 1 / 2) * Complex.I * q.1)) (analyticAt_fst.prod ht)
  · exact analyticAt_const

lemma analyticAt_continuationNumerator_joint (p : ℂ × ℂ) (k : ℤ)
    (hb : AdmissibleB p.1) (hz : InStrip p.1 (shiftedArgument p.1 p.2 k)) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => continuationNumerator q.1 q.2 k) p := by
  classical
  have hs := analyticAt_shiftedArgument_joint p k
  have hphi : AnalyticAt ℂ (fun q : ℂ × ℂ => phi q.1 q.2)
      (p.1, shiftedArgument p.1 p.2 k) :=
    JointAnalytic.differentiableOn_analyticOnNhd differentiableOn_phi_joint
      isOpen_parameterDomain _ ⟨hb, hz⟩
  have hc : AnalyticAt ℂ (fun q : ℂ × ℂ => phi q.1 (shiftedArgument q.1 q.2 k)) p :=
    hphi.comp (f := fun q : ℂ × ℂ => (q.1, shiftedArgument q.1 q.2 k))
      (analyticAt_fst.prod hs)
  unfold continuationNumerator
  split_ifs
  · exact hc
  · apply hc.mul
    apply Finset.analyticAt_fun_prod
    intro j _
    have ht : AnalyticAt ℂ (fun q : ℂ × ℂ => shiftedArgument q.1 q.2 k -
        ((j : ℂ) + 1 / 2) * Complex.I * q.1) p :=
      hs.sub (analyticAt_const.mul analyticAt_fst)
    exact (analyticAt_continuationFactor_joint _).comp
      (f := fun q : ℂ × ℂ => (q.1, shiftedArgument q.1 q.2 k -
        ((j : ℂ) + 1 / 2) * Complex.I * q.1)) (analyticAt_fst.prod ht)

lemma isOpen_continuationChartDomain (k : ℤ) :
    IsOpen {q : ℂ × ℂ | AdmissibleB q.1 ∧ InStrip q.1 (shiftedArgument q.1 q.2 k)} := by
  change IsOpen ((fun q : ℂ × ℂ => (q.1, shiftedArgument q.1 q.2 k)) ⁻¹' parameterDomain)
  apply isOpen_parameterDomain.preimage
  unfold shiftedArgument
  fun_prop

lemma continuationDenominator_frequently_ne_zero (b z : ℂ) (k : ℤ)
    (hb : AdmissibleB b) (hz : InStrip b (shiftedArgument b z k)) :
    ∃ᶠ w : ℂ in 𝓝 z, continuationDenominator b w k ≠ 0 := by
  have hmer := (analyticAt_continuationDenominator b z k).meromorphicAt
  have hnt : meromorphicOrderAt (fun w => continuationDenominator b w k) z ≠ ⊤ := by
    by_cases hk : 0 ≤ k
    · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [meromorphicOrderAt_continuationDenominator_nat b z a hb hz]
      simp
    · have hfun : (fun w => continuationDenominator b w k) = fun _ => (1 : ℂ) := by
        funext w
        simp only [continuationDenominator, if_neg hk]
      rw [hfun, meromorphicOrderAt_const]
      simp
  exact ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp hnt).frequently
    |>.filter_mono nhdsWithin_le_nhds

theorem phiExtended_joint_holomorphic :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => phiExtended p.1 p.2) phiRegularDomain := by
  intro p hp
  let k := continuationIndex p.1 p.2
  have hs : InStrip p.1 (shiftedArgument p.1 p.2 k) := shiftedArgument_inStrip _ _ hp.1
  have hD : continuationDenominator p.1 p.2 k ≠ 0 :=
    (continuationDenominator_ne_zero_iff p.1 p.2 k hp.1 hs).mpr hp.2
  have hA := (analyticAt_continuationNumerator_joint p k hp.1 hs).div
    (analyticAt_continuationDenominator_joint p k) hD
  have heq : (fun q : ℂ × ℂ => phiExtended q.1 q.2) =ᶠ[𝓝 p]
      (fun q => continuationNumerator q.1 q.2 k / continuationDenominator q.1 q.2 k) := by
    filter_upwards [(isOpen_continuationChartDomain k).mem_nhds ⟨hp.1, hs⟩] with q hq
    exact phiExtended_eq_phiChart q.1 q.2 k hq.1 hq.2
  exact (hA.congr heq.symm).differentiableAt.differentiableWithinAt

/-- An explicit two-variable analytic quotient around every admissible point, including a pole.
Agreement is required only where the denominator is nonzero. Each fixed-`b` denominator has nonzero
values arbitrarily close to every point of the chart, so an identically zero denominator cannot make
this vacuous. -/
theorem phiExtended_joint_local_quotient (p : ℂ × ℂ) (hp : AdmissibleB p.1) :
    ∃ (k : ℤ) (U : Set (ℂ × ℂ)), IsOpen U ∧ p ∈ U ∧
      (∀ q ∈ U, AdmissibleB q.1 ∧ InStrip q.1 (shiftedArgument q.1 q.2 k)) ∧
      AnalyticOnNhd ℂ (fun q : ℂ × ℂ => continuationNumerator q.1 q.2 k) U ∧
      AnalyticOnNhd ℂ (fun q : ℂ × ℂ => continuationDenominator q.1 q.2 k) U ∧
      (∀ q ∈ U, ∃ᶠ w : ℂ in 𝓝 q.2, continuationDenominator q.1 w k ≠ 0) ∧
      (∀ q ∈ U, continuationDenominator q.1 q.2 k ≠ 0 →
        phiExtended q.1 q.2 =
          continuationNumerator q.1 q.2 k / continuationDenominator q.1 q.2 k) := by
  let k := continuationIndex p.1 p.2
  let U : Set (ℂ × ℂ) :=
    {q | AdmissibleB q.1 ∧ InStrip q.1 (shiftedArgument q.1 q.2 k)}
  have hpU : p ∈ U := ⟨hp, shiftedArgument_inStrip _ _ hp⟩
  refine ⟨k, U, isOpen_continuationChartDomain k, hpU, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hq
  · intro q hq
    exact analyticAt_continuationNumerator_joint q k hq.1 hq.2
  · intro q _
    exact analyticAt_continuationDenominator_joint q k
  · intro q hq
    exact continuationDenominator_frequently_ne_zero q.1 q.2 k hq.1 hq.2
  · intro q hq _
    exact phiExtended_eq_phiChart q.1 q.2 k hq.1 hq.2

/-- A useful nonresonant case. Real rational `b²` is deliberately not included. -/
theorem phiDivisor_simple_of_im_sq_ne_zero (b : ℂ) (hb : AdmissibleB b)
    (hi : (b ^ 2).im ≠ 0) (m n : ℕ) :
    phiPoleMultiplicity b (phiPolePoint b m n) = 1 ∧
      phiZeroMultiplicity b (phiZeroPoint b m n) = 1 := by
  have hp : phiPoleIndices b (phiPolePoint b m n) = {(m, n)} := by
    ext mn
    change phiPolePoint b m n = phiPolePoint b mn.1 mn.2 ↔ mn = (m, n)
    constructor
    · intro h
      exact (@phiPolePoint_injective_of_im_sq_ne_zero b hb hi (m,n) mn h).symm
    · rintro rfl
      rfl
  have hz : phiZeroIndices b (phiZeroPoint b m n) = {(m, n)} := by
    ext mn
    change -phiPolePoint b m n = -phiPolePoint b mn.1 mn.2 ↔ mn = (m, n)
    rw [neg_inj]
    constructor
    · intro h
      exact (@phiPolePoint_injective_of_im_sq_ne_zero b hb hi (m,n) mn h).symm
    · rintro rfl
      rfl
  constructor
  · change Nat.card (phiPoleIndices b (phiPolePoint b m n)) = 1
    rw [hp]
    exact Nat.card_unique
  · change Nat.card (phiZeroIndices b (phiZeroPoint b m n)) = 1
    rw [hz]
    exact Nat.card_unique

/-- The resonant case `b = 1`: the order at `±i(j+1)` is `±(j+1)`. Divisor points need
not be simple. -/
theorem phiDivisor_at_one (j : ℕ) :
    phiPoleMultiplicity 1 (Complex.I * ((j : ℂ) + 1)) = j + 1 ∧
      phiZeroMultiplicity 1 (-Complex.I * ((j : ℂ) + 1)) = j + 1 := by
  have hmem (mn : ℕ × ℕ) :
      mn ∈ Finset.antidiagonal j ↔
        Complex.I * ((j : ℂ) + 1) = phiPolePoint 1 mn.1 mn.2 := by
    rw [Finset.mem_antidiagonal]
    constructor
    · intro h
      have hc : (mn.1 : ℂ) + (mn.2 : ℂ) = (j : ℂ) := by exact_mod_cast h
      rw [phiPolePoint_one, hc]
    · intro h
      have him := congrArg Complex.im h
      simp [phiPolePoint_one, Complex.mul_im] at him
      exact_mod_cast (by linarith : (mn.1 : ℝ) + (mn.2 : ℝ) = (j : ℝ))
  have hp : phiPoleMultiplicity 1 (Complex.I * ((j : ℂ) + 1)) = j + 1 := by
    change Nat.card {mn : ℕ × ℕ //
      Complex.I * ((j : ℂ) + 1) = phiPolePoint 1 mn.1 mn.2} = j + 1
    rw [Nat.subtype_card (Finset.antidiagonal j) hmem, Finset.Nat.card_antidiagonal]
  refine ⟨hp, ?_⟩
  unfold phiZeroMultiplicity
  rw [phiZeroIndices_eq_pole_neg]
  simpa [phiPoleMultiplicity] using hp

-- Check actual Mathlib types; these commands are type checks.
#check phi_difference_b
#check differentiableOn_phi_joint
#check MeromorphicOn
#check meromorphicOrderAt
#check meromorphicOrderAt_eq_int_iff
#check AnalyticOnNhd
#check Nat.card
#check Int.floor
#print phiExtended
#print phiExtended_order
#print phiExtended_joint_local_quotient

end SICLean.L4
