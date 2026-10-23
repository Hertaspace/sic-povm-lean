import SICLean.L4.ModularCocycleReflectionAux
import SICLean.L4.ModularCocycleReflectionLimitAux
import SICLean.L4.ModularCocycleAux

set_option autoImplicit false
noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4.ModularCocycleReflectionPhaseAux
open ModularCocycleReflectionAux

/-- Rational form of one exponent summand after the square root is squared. -/
def rationalTerm (M : SL(2, ℤ)) (r n : ℤ) (j : ℕ) (z τ : ℂ) : ℂ :=
  -Complex.I * (Real.pi : ℂ) *
      (modularPhiFactorInput M r n j z τ - (etaDenom M τ - 1) / 2) ^ 2 /
        etaDenom M τ +
    Complex.I * (Real.pi : ℂ) * (etaDenom M τ + (etaDenom M τ)⁻¹) / 12

def rationalExponent (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (M 1 0).toNat, rationalTerm M r n j z τ

def polynomial (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * ((M 1 0 : ℂ) * z ^ 2 / etaDenom M τ +
    (2 * (r : ℂ) - 1 - (2 * (n : ℂ) - 1) / etaDenom M τ) * z +
    ((r : ℂ) ^ 2 - (r : ℂ) + 1 / 6) * τ -
    ((n : ℂ) ^ 2 - (n : ℂ) + 1 / 6) * etaMobius M τ)

lemma reflectionExponent_eq_rational (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M) :
    reflectionExponent M r n z τ = rationalExponent M r n z τ := by
  have hb := modularPhi_sqrt_admissible M τ hτ
  unfold reflectionExponent rationalExponent
  apply Finset.sum_congr rfl
  intro j hj
  have harg : (modularPhiFactorPoint M r n j z τ).2 ^ 2 =
      -(modularPhiFactorInput M r n j z τ - (etaDenom M τ - 1) / 2) ^ 2 / etaDenom M τ := by
    set b := Complex.sqrt (etaDenom M τ) with hbdef
    have hb2 : b ^ 2 = etaDenom M τ := hb.2.1
    have hbne : b ≠ 0 := hb.2.2
    change (Complex.I * modularPhiFactorInput M r n j z τ / b -
      Complex.I * b / 2 + Complex.I / (2 * b)) ^ 2 = _
    have hlin : Complex.I * modularPhiFactorInput M r n j z τ / b -
        Complex.I * b / 2 + Complex.I / (2 * b) =
        Complex.I * (modularPhiFactorInput M r n j z τ - (etaDenom M τ - 1) / 2) / b := by
      field_simp [hbne]
      linear_combination -hb2
    rw [hlin, div_pow, mul_pow, Complex.I_sq, hb2]
    ring
  rw [harg]
  simp only [rationalTerm, hb.2.1, inv_pow]
  ring

lemma sum_centered_input (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ) (τ : ℂ) :
    (∑ j ∈ Finset.range (M 1 0).toNat,
      (modularPhiFactorInput M r n j 0 τ - (etaDenom M τ - 1) / 2)) =
      ((r : ℂ) - 1 / 2) * etaDenom M τ - (n : ℂ) + 1 / 2 := by
  have hc : ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hM.le
  simp only [modularPhiFactorInput, zero_add]
  simp_rw [add_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, sum_range_natCast, sum_index M hM r n]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc, etaDenom]
  ring

lemma rationalExponent_z (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ) (z τ : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    rationalExponent M r n z τ = rationalExponent M r n 0 τ -
      Complex.I * (Real.pi : ℂ) * ((M 1 0 : ℂ) * z ^ 2 / etaDenom M τ +
        (2 * (r : ℂ) - 1 - (2 * (n : ℂ) - 1) / etaDenom M τ) * z) := by
  have hc : ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hM.le
  have heach (j : ℕ) : rationalTerm M r n j z τ = rationalTerm M r n j 0 τ -
      Complex.I * (Real.pi : ℂ) / etaDenom M τ *
        (z ^ 2 + 2 * z * (modularPhiFactorInput M r n j 0 τ - (etaDenom M τ - 1) / 2)) := by
    simp only [rationalTerm, modularPhiFactorInput]
    ring
  simp only [rationalExponent, heach, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_centered_input M hM r n]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc]
  field_simp [hT]
  ring

lemma rationalExponent_m_succ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hT : etaDenom M τ ≠ 0) :
    rationalExponent M (r + 1) n z τ = rationalExponent M r n z τ -
      Complex.I * (Real.pi : ℂ) * (2 * z + 2 * (r : ℂ) * τ +
        2 * (modularPhiIndex M r n 0 : ℂ) + 1) := by
  let c := (M 1 0).toNat
  have hc : (c : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.le
  have hcC : (c : ℂ) = (M 1 0 : ℂ) := by exact_mod_cast hc
  have hshift (j : ℕ) : modularPhiFactorInput M (r + 1) n j z τ =
      modularPhiFactorInput M r n (j + 1) z τ := by
    have hidx : modularPhiIndex M (r + 1) n j = modularPhiIndex M r n (j + 1) := by
      unfold modularPhiIndex
      congr 1
      push_cast
      ring
    simp only [modularPhiFactorInput, hidx]
    push_cast
    ring
  have hshiftTerm (j : ℕ) : rationalTerm M (r + 1) n j z τ =
      rationalTerm M r n (j + 1) z τ := by simp only [rationalTerm, hshift]
  have hlastInput : modularPhiFactorInput M r n c z τ =
      modularPhiFactorInput M r n 0 z τ + etaDenom M τ := by
    have hidx : modularPhiIndex M r n c = modularPhiIndex M r n 0 + M 1 1 := by
      simp only [modularPhiIndex, hc, Nat.cast_zero, add_zero]
      rw [show M 1 1 * (r + M 1 0) - n = (M 1 1 * r - n) + M 1 1 * M 1 0 by ring,
        Int.add_mul_ediv_right _ _ hM.ne']
    simp only [modularPhiFactorInput, hidx, hcC, etaDenom]
    push_cast
    ring
  have hlast : rationalTerm M r n c z τ = rationalTerm M r n 0 z τ -
      Complex.I * (Real.pi : ℂ) * (2 * z + 2 * (r : ℂ) * τ +
        2 * (modularPhiIndex M r n 0 : ℂ) + 1) := by
    simp only [rationalTerm, hlastInput]
    simp only [modularPhiFactorInput, Nat.cast_zero, add_zero]
    field_simp [hT]
    ring
  have hsum : (∑ j ∈ Finset.range c, rationalTerm M r n (j + 1) z τ) =
      (∑ j ∈ Finset.range c, rationalTerm M r n j z τ) +
        rationalTerm M r n c z τ - rationalTerm M r n 0 z τ := by
    have h₁ := Finset.sum_range_succ (fun j => rationalTerm M r n j z τ) c
    have h₂ := Finset.sum_range_succ' (fun j => rationalTerm M r n j z τ) c
    linear_combination h₁ - h₂
  simp only [rationalExponent, hshiftTerm]
  rw [hsum, hlast]
  ring

lemma exp_int_phase (u : ℂ) (k : ℤ) :
    Complex.exp (-Complex.I * (Real.pi : ℂ) * (2 * u + 2 * (k : ℂ) + 1)) = -e (-u) := by
  have hx : -Complex.I * (Real.pi : ℂ) * (2 * u + 2 * (k : ℂ) + 1) =
      2 * (Real.pi : ℂ) * Complex.I * (-u) +
        2 * (Real.pi : ℂ) * Complex.I * ((-k : ℤ) : ℂ) - (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hx, sub_eq_add_neg, Complex.exp_add, Complex.exp_add, Complex.exp_neg_pi_mul_I]
  change e (-u) * e ((-k : ℤ) : ℂ) * (-1) = _
  rw [e_intCast]
  ring

lemma exp_rationalExponent_m_succ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hT : etaDenom M τ ≠ 0) :
    Complex.exp (rationalExponent M (r + 1) n z τ) =
      Complex.exp (rationalExponent M r n z τ) * (-e (-z - (r : ℂ) * τ)) := by
  rw [rationalExponent_m_succ M hM r n z τ hT, sub_eq_add_neg, Complex.exp_add]
  rw [show -(Complex.I * (Real.pi : ℂ) * (2 * z + 2 * (r : ℂ) * τ +
    2 * (modularPhiIndex M r n 0 : ℂ) + 1)) =
      -Complex.I * (Real.pi : ℂ) * (2 * (z + (r : ℂ) * τ) +
        2 * (modularPhiIndex M r n 0 : ℂ) + 1) by ring, exp_int_phase]
  congr 2
  ring

lemma exp_rationalExponent_n_succ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    Complex.exp (rationalExponent M r (n + 1) z τ) =
      Complex.exp (rationalExponent M r n z τ) *
        (-e (z / etaDenom M τ + (n : ℂ) * etaMobius M τ)) := by
  classical
  have hp := modularPhiResidue_permutation M hM r n
  let c := (M 1 0).toNat
  have hmem : (0 : ℕ) ∈ Finset.range c := by
    dsimp [c]
    simp only [Finset.mem_range]
    omega
  rw [← hp.2.1] at hmem
  obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp hmem
  have hrzero : modularPhiResidue M r n j = 0 := by
    have := (hp.1 j).1
    omega
  have hindex (i : ℕ) : modularPhiIndex M r (n + 1) i =
      if modularPhiResidue M r n i = 0 then modularPhiIndex M r n i - 1
      else modularPhiIndex M r n i := by
    have hres := hp.1 i
    have hdef : M 1 1 * (r + (i : ℤ)) - n =
        M 1 0 * modularPhiIndex M r n i + modularPhiResidue M r n i := by
      unfold modularPhiResidue
      ring
    change (M 1 1 * (r + (i : ℤ)) - (n + 1)) / M 1 0 = _
    by_cases hr : modularPhiResidue M r n i = 0
    · rw [if_pos hr, Int.ediv_eq_iff_of_pos hM]
      constructor <;> nlinarith
    · have hpos : 0 < modularPhiResidue M r n i := by omega
      rw [if_neg hr, Int.ediv_eq_iff_of_pos hM]
      constructor <;> nlinarith
  let delta := Complex.I * (Real.pi : ℂ) *
    (2 * modularPhiFactorInput M r n j z τ / etaDenom M τ - 1)
  have hterm (i : ℕ) (hi : i ∈ Finset.range c) :
      rationalTerm M r (n + 1) i z τ =
        rationalTerm M r n i z τ + if i = j then delta else 0 := by
    by_cases hij : i = j
    · subst i
      have hinput : modularPhiFactorInput M r (n + 1) j z τ =
          modularPhiFactorInput M r n j z τ - 1 := by
        simp only [modularPhiFactorInput, hindex j, if_pos hrzero, Int.cast_sub, Int.cast_one]
        ring
      simp only [if_true]
      dsimp only [rationalTerm, delta]
      rw [hinput]
      field_simp [etaDenom_ne_zero_of_mem M hτ]
      ring
    · have hri : modularPhiResidue M r n i ≠ 0 := by
        intro hz
        apply hij
        apply hp.2.2 hi hj
        change (modularPhiResidue M r n i).toNat = (modularPhiResidue M r n j).toNat
        rw [hz, hrzero]
      simp only [if_neg hij, add_zero, rationalTerm, modularPhiFactorInput,
        hindex i, if_neg hri]
  have hsum : rationalExponent M r (n + 1) z τ = rationalExponent M r n z τ + delta := by
    unfold rationalExponent
    change (∑ i ∈ Finset.range c, rationalTerm M r (n + 1) i z τ) = _
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    have hjc : j ∈ Finset.range c := hj
    simp only [Finset.sum_ite_eq', hjc, if_true]
    rfl
  rw [hsum, Complex.exp_add]
  have hdelta : delta = -Complex.I * (Real.pi : ℂ) *
      (2 * (-(modularPhiFactorInput M r n j z τ / etaDenom M τ)) + 2 * (0 : ℤ) + 1) := by
    dsimp [delta]
    push_cast
    ring
  rw [hdelta, exp_int_phase, neg_neg, e_factorInput_div_etaDenom M hM r n j z τ hτ,
    hrzero, add_zero, e_add', ← e_int_mul]

def normalizedFactor (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) : ℂ :=
  (etaMultiplier M) ^ (-2 : ℤ) * (-1 : ℂ) ^ (r + n) * e (polynomial M r n z τ)

lemma polynomial_m_succ (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) :
    polynomial M (r + 1) n z τ = polynomial M r n z τ + (-z - (r : ℂ) * τ) := by
  unfold polynomial
  push_cast
  ring

lemma polynomial_n_succ (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) :
    polynomial M r (n + 1) z τ = polynomial M r n z τ +
      (z / etaDenom M τ + (n : ℂ) * etaMobius M τ) := by
  unfold polynomial
  push_cast
  ring

lemma normalizedFactor_m_succ (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) :
    normalizedFactor M (r + 1) n z τ =
      normalizedFactor M r n z τ * (-e (-z - (r : ℂ) * τ)) := by
  simp only [normalizedFactor, polynomial_m_succ, e_add']
  rw [show r + 1 + n = (r + n) + 1 by omega, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [zpow_one]
  ring

lemma normalizedFactor_n_succ (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) :
    normalizedFactor M r (n + 1) z τ = normalizedFactor M r n z τ *
      (-e (z / etaDenom M τ + (n : ℂ) * etaMobius M τ)) := by
  simp only [normalizedFactor, polynomial_n_succ, e_add']
  rw [show r + (n + 1) = (r + n) + 1 by omega, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [zpow_one]
  ring

lemma int_eq_of_succ (A B C : ℤ → ℂ) (hbase : A 1 = B 1)
    (hA : ∀ k, A (k + 1) = A k * C k) (hB : ∀ k, B (k + 1) = B k * C k)
    (hC : ∀ k, C k ≠ 0) : ∀ k, A k = B k := by
  have hstep (k : ℤ) : (A (k + 1) = B (k + 1)) ↔ (A k = B k) := by
    rw [hA, hB]
    constructor
    · exact mul_right_cancel₀ (hC k)
    · intro h
      rw [h]
  have hzero : A 0 = B 0 := (hstep 0).mp hbase
  intro k
  induction k using Int.induction_on with
  | zero => exact hzero
  | succ k ih => exact (hstep k).mpr ih
  | pred k ih => exact (hstep (-(k : ℤ) - 1)).mp (by simpa using ih)

lemma reflection_base_normalized (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M) :
    Complex.exp (reflectionExponent M 1 1 0 τ) =
      (etaMultiplier M) ^ (-2 : ℤ) * e ((etaMobius M τ - τ) / 12) := by
  apply ModularCocycleAux.eqOn_domain_of_upper M hM
    (exp_reflectionExponent_analytic M 1 1 0) ?_ ?_ hτ
  · intro ρ hρ
    have hT := etaDenom_ne_zero_of_mem M hρ
    have he : AnalyticAt ℂ (etaMobius M) ρ := by
      unfold etaMobius etaDenom
      exact (analyticAt_const.mul analyticAt_id |>.add analyticAt_const).div
        ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hT
    unfold e
    exact analyticAt_const.mul ((analyticAt_const.mul ((he.sub analyticAt_id).div_const (c := 12))).cexp')
  · exact ModularCocycleReflectionLimitAux.reflection_base_normalized_upper M hM

lemma exp_rationalExponent_z (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ)
    (z τ : ℂ) (hT : etaDenom M τ ≠ 0) :
    Complex.exp (rationalExponent M r n z τ) =
      Complex.exp (rationalExponent M r n 0 τ) *
        e (polynomial M r n z τ - polynomial M r n 0 τ) := by
  have hp : 2 * (Real.pi : ℂ) * Complex.I *
      (polynomial M r n z τ - polynomial M r n 0 τ) =
      -(Complex.I * (Real.pi : ℂ) * ((M 1 0 : ℂ) * z ^ 2 / etaDenom M τ +
        (2 * (r : ℂ) - 1 - (2 * (n : ℂ) - 1) / etaDenom M τ) * z)) := by
    unfold polynomial
    ring
  rw [rationalExponent_z M hM r n z τ hT, sub_eq_add_neg, Complex.exp_add]
  rw [← hp]
  rfl

lemma normalizedFactor_z (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) :
    normalizedFactor M r n z τ = normalizedFactor M r n 0 τ *
      e (polynomial M r n z τ - polynomial M r n 0 τ) := by
  have he : e (polynomial M r n z τ) = e (polynomial M r n 0 τ) *
      e (polynomial M r n z τ - polynomial M r n 0 τ) := by
    rw [← e_add']
    congr 1
    ring
  simp only [normalizedFactor]
  rw [he]
  ring

lemma exp_rationalExponent_base (M : SL(2, ℤ)) (hM : 0 < M 1 0) (z τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M) :
    Complex.exp (rationalExponent M 1 1 z τ) = normalizedFactor M 1 1 z τ := by
  have hp0 : polynomial M 1 1 0 τ = (etaMobius M τ - τ) / 12 := by
    unfold polynomial
    norm_num
    ring
  have hb0 : Complex.exp (rationalExponent M 1 1 0 τ) = normalizedFactor M 1 1 0 τ := by
    rw [← reflectionExponent_eq_rational M 1 1 0 τ hτ, reflection_base_normalized M hM τ hτ]
    simp only [normalizedFactor, hp0]
    norm_num
  rw [exp_rationalExponent_z M hM 1 1 z τ (etaDenom_ne_zero_of_mem M hτ),
    normalizedFactor_z M 1 1 z τ, hb0]

/-- Exact normalization of the finite raw Faddeev reflection phase. -/
theorem reflection_exponent_normalized (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    Complex.exp (reflectionExponent M r n z τ) = normalizedFactor M r n z τ := by
  have hbase (n : ℤ) : Complex.exp (rationalExponent M 1 n z τ) =
      normalizedFactor M 1 n z τ := by
    apply int_eq_of_succ
      (fun j => Complex.exp (rationalExponent M 1 j z τ))
      (fun j => normalizedFactor M 1 j z τ)
      (fun j => -e (z / etaDenom M τ + (j : ℂ) * etaMobius M τ))
      (exp_rationalExponent_base M hM z τ hτ)
      (fun j => exp_rationalExponent_n_succ M hM 1 j z τ hτ)
      (fun j => normalizedFactor_n_succ M 1 j z τ)
      (fun j => neg_ne_zero.mpr (e_ne_zero _)) n
  rw [reflectionExponent_eq_rational M r n z τ hτ]
  exact int_eq_of_succ
    (fun j => Complex.exp (rationalExponent M j n z τ))
    (fun j => normalizedFactor M j n z τ)
    (fun j => -e (-z - (j : ℂ) * τ)) (hbase n)
    (fun j => exp_rationalExponent_m_succ M hM j n z τ (etaDenom_ne_zero_of_mem M hτ))
    (fun j => normalizedFactor_m_succ M j n z τ)
    (fun j => neg_ne_zero.mpr (e_ne_zero _)) r

end SICLean.L4.ModularCocycleReflectionPhaseAux
