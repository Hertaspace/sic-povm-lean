import SICLean.Final.Unconditional
import SICLean.L5.ActualQuadraticFieldAux

set_option autoImplicit false

/-!
# The actual quadratic field of an admissible matrix

The field and its two real embeddings are constructed directly.
The field is Q(tau) in the fixed Qbar. The second embedding is the trace
minus the first embedding.

Sources: [RW26, p. 2, (2); p. 3, (4); (37), p. 20]; [RW-rec, Def. 1].
No ray class group, Artin map, or density is defined here.
-/

noncomputable section
open scoped MatrixGroups

namespace SICLean.L5.ActualField

open ActualQuadraticFieldAux

/-- Algebraicity of the specified attracting root. [RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem tau_isAlgebraic (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    IsAlgebraic ℚ (L4.specialValueTau M : ℂ) := by
  exact ActualQuadraticFieldAux.tau_isAlgebraic M hM

def tauLift (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) : Galois.Qbar :=
  Galois.algebraicLift (L4.specialValueTau M : ℂ) (tau_isAlgebraic M hM)

/-- The same complex number is lifted. [RW26, p. 20]. -/
theorem embed_tauLift (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    Galois.embed (tauLift M hM) = (L4.specialValueTau M : ℂ) := by
  exact Galois.embed_algebraicLift _ _

def baseField (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    IntermediateField ℚ Galois.Qbar :=
  IntermediateField.adjoin ℚ ({tauLift M hM} : Set Galois.Qbar)

/-- Real quadraticity, with the fixed embedding real.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem baseField_isRealQuadratic (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) : Galois.IsRealQuadratic (baseField M hM) := by
  constructor
  · apply adjoin_finrank_eq_two (tauLift M hM) (tauPoly M)
      (tauPoly_ne_zero M hM) (tauPoly_natDegree M hM)
    · apply Galois.embed.injective
      have hreal := tau_poly_real M hM
      have hcomplex :
          (M 1 0 : ℂ) * (L4.specialValueTau M : ℂ) ^ 2 +
            ((M 1 1 : ℂ) - (M 0 0 : ℂ)) * (L4.specialValueTau M : ℂ) +
            (-(M 0 1 : ℂ)) = 0 := by
        exact_mod_cast hreal
      simpa [tauPoly, embed_tauLift] using hcomplex
    · rintro ⟨q, hq⟩
      have hcomplex : (q : ℂ) = (L4.specialValueTau M : ℂ) := by
        simpa [embed_tauLift] using congrArg Galois.embed hq
      have hreal : (q : ℝ) = L4.specialValueTau M := by
        simpa using congrArg Complex.re hcomplex
      exact (L4.specialValueTau_irrational M hM).ne_rat q hreal.symm
  · exact real_adjoin (tauLift M hM) (by simp [embed_tauLift])

instance baseField_numberField (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    NumberField (baseField M hM) := by
  exact { to_charZero := inferInstance
          to_finiteDimensional := Module.finite_of_finrank_eq_succ
            (n := 1) (baseField_isRealQuadratic M hM).degree_two }

/-- The generator lies in the field it generates. [RW26, p. 20]. -/
theorem tauLift_mem_baseField (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    tauLift M hM ∈ baseField M hM := by
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

def tau (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) : baseField M hM :=
  ⟨tauLift M hM, tauLift_mem_baseField M hM⟩

def epsilon (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) : baseField M hM :=
  (M 1 0 : baseField M hM) * tau M hM + (M 1 1 : baseField M hM)

def conjugateTau (M : SL(2, ℤ)) : ℝ :=
  ((M 0 0 : ℝ) - (M 1 1 : ℝ) -
    Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)) / (2 * (M 1 0 : ℝ))

def sigma₁ (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    baseField M hM →+* ℝ where
  toFun x := (Galois.embed (x : Galois.Qbar)).re
  map_one' := by simp
  map_mul' := by
    intro x y
    change (Galois.embed ((x : Galois.Qbar) * (y : Galois.Qbar))).re = _
    simp only [map_mul, Complex.mul_re, (baseField_isRealQuadratic M hM).real,
      mul_zero, sub_zero]
  map_zero' := by simp
  map_add' := by simp [map_add]

def sigma₂ (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    baseField M hM →+* ℝ where
  toFun x := (Algebra.trace ℚ (baseField M hM) x : ℝ) - sigma₁ M hM x
  map_one' := trace_sub_map_one (baseField_isRealQuadratic M hM).degree_two (sigma₁ M hM)
  map_mul' := trace_sub_map_mul (baseField_isRealQuadratic M hM).degree_two (sigma₁ M hM)
  map_zero' := trace_sub_map_zero (sigma₁ M hM)
  map_add' := trace_sub_map_add (sigma₁ M hM)

/-- First embedding of the generator. [RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem sigma₁_tau (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    sigma₁ M hM (tau M hM) = L4.specialValueTau M := by
  change (Galois.embed (tauLift M hM)).re = _
  rw [embed_tauLift, Complex.ofReal_re]

/-- Conjugate embedding, sending tau to the other quadratic root.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem sigma₂_tau (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    sigma₂ M hM (tau M hM) = conjugateTau M := by
  have hK := (baseField_isRealQuadratic M hM).degree_two
  obtain ⟨κ, hκ⟩ := quadratic_exists_nontrivial_aut hK
  have hfix : κ (tau M hM) ≠ tau M hM :=
    nontrivial_not_fixed_adjoin (tauLift M hM) κ hκ
  have hc : (M 1 0 : ℚ) ≠ 0 := by exact_mod_cast hM.1.ne'
  have hrel : algebraMap ℚ (baseField M hM) (M 1 0 : ℚ) * tau M hM ^ 2 +
      algebraMap ℚ (baseField M hM) ((M 1 1 - M 0 0 : ℤ) : ℚ) * tau M hM +
      algebraMap ℚ (baseField M hM) (-(M 0 1 : ℚ)) = 0 := by
    apply (sigma₁ M hM).injective
    simpa only [map_add, map_sub, map_mul, map_pow, map_zero, RingHom.map_rat_algebraMap,
      map_intCast, map_neg, Int.cast_sub, sigma₁_tau] using tau_poly_real M hM
  have htrace := trace_of_quadratic_relation hK κ hκ (tau M hM) hfix
    (M 1 0 : ℚ) ((M 1 1 - M 0 0 : ℤ) : ℚ) (-(M 0 1 : ℚ)) hc hrel
  change (Algebra.trace ℚ (baseField M hM) (tau M hM) : ℝ) -
    sigma₁ M hM (tau M hM) = conjugateTau M
  rw [htrace, sigma₁_tau]
  push_cast
  dsimp only [conjugateTau, L4.specialValueTau]
  field_simp
  ring

/-- The field element c*tau+d embeds to the corresponding complex value.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem embed_epsilon (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    Galois.embed (epsilon M hM : Galois.Qbar) = (L4.specialValueEpsilon M : ℂ) := by
  change Galois.embed ((M 1 0 : Galois.Qbar) * tauLift M hM + (M 1 1 : Galois.Qbar)) = _
  simp only [map_add, map_mul, map_intCast, embed_tauLift]
  simp only [L4.specialValueEpsilon, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_intCast]

/-- The attracting embedding of epsilon. [RW26, p. 3, (4)]; [RW-rec, Def. 1]. -/
theorem sigma₁_epsilon (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    sigma₁ M hM (epsilon M hM) = L4.specialValueEpsilon M := by
  change (Galois.embed (epsilon M hM : Galois.Qbar)).re = _
  rw [embed_epsilon, Complex.ofReal_re]

/-- The conjugate embedding sends epsilon to its inverse.
[RW26, p. 3, (4)]; [RW-rec, Def. 1]. -/
theorem sigma₂_epsilon (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    sigma₂ M hM (epsilon M hM) = (sigma₁ M hM (epsilon M hM))⁻¹ := by
  rw [epsilon, map_add, map_mul, map_intCast, map_intCast, sigma₂_tau]
  change (M 1 0 : ℝ) * conjugateTau M + (M 1 1 : ℝ) =
    (sigma₁ M hM (epsilon M hM))⁻¹
  rw [sigma₁_epsilon]
  apply eq_inv_of_mul_eq_one_left
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hM.1.ne'
  have hsum : (M 1 0 : ℝ) * conjugateTau M + (M 1 1 : ℝ) +
      L4.specialValueEpsilon M = (M 0 0 : ℝ) + (M 1 1 : ℝ) := by
    dsimp only [conjugateTau, L4.specialValueEpsilon, L4.specialValueTau]
    field_simp
    ring
  have hp := L4.specialValueEpsilon_characteristic M hM
  simp only [L4.specialValueOrder, Int.cast_sub, Int.cast_add, Int.cast_ofNat] at hp
  linear_combination L4.specialValueEpsilon M * hsum - hp

/-- The order is a positive natural number. [RW26, p. 3]; [RW-rec, Def. 1]. -/
theorem order_nat (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    0 < (L4.specialValueOrder M).toNat ∧
      L4.specialValueOrder M = ((L4.specialValueOrder M).toNat : ℤ) := by
  have hpos := L4.specialValueOrder_pos M hM
  exact ⟨by omega, (Int.toNat_of_nonneg hpos.le).symm⟩

/-- The period polynomial in this field K. [RW26, p. 2; p. 3, (4)]; [RW-rec, Def. 1]. -/
theorem epsilon_polynomial (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    epsilon M hM ^ 2 -
      (((L4.specialValueOrder M).toNat : baseField M hM) + 2) * epsilon M hM + 1 = 0 := by
  apply (sigma₁ M hM).injective
  simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat, map_one,
    map_zero, sigma₁_epsilon]
  have hn : ((L4.specialValueOrder M).toNat : ℝ) = (L4.specialValueOrder M : ℝ) := by
    exact_mod_cast (order_nat M hM).2.symm
  rw [hn]
  exact L4.specialValueEpsilon_characteristic M hM

/-- The attracting embedding of epsilon is greater than 1.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem epsilon_gt_one (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    1 < sigma₁ M hM (epsilon M hM) := by
  rw [sigma₁_epsilon]
  exact L4.specialValueEpsilon_gt_one M hM

def periodData (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    L3.PeriodData (baseField M hM) where
  sigma₁ := sigma₁ M hM
  sigma₂ := sigma₂ M hM
  finrank_eq_two := (baseField_isRealQuadratic M hM).degree_two
  epsilon := epsilon M hM
  N := (L4.specialValueOrder M).toNat
  N_pos := (order_nat M hM).1
  epsilon_polynomial := epsilon_polynomial M hM
  epsilon_gt_one := epsilon_gt_one M hM
  epsilon_conj := sigma₂_epsilon M hM

/-- Epsilon is totally positive, and both epsilon and its inverse are integral.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem epsilon_totallyPositive_unit (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) :
    L3.TotallyPositive (periodData M hM) (epsilon M hM) ∧
      IsIntegral ℤ (epsilon M hM) ∧ IsIntegral ℤ ((epsilon M hM)⁻¹) := by
  let P := periodData M hM
  have hpos : 0 < sigma₁ M hM (epsilon M hM) :=
    lt_trans zero_lt_one (epsilon_gt_one M hM)
  have hinv : (epsilon M hM)⁻¹ = ((P.N : baseField M hM) + 2) - epsilon M hM := by
    apply inv_eq_of_mul_eq_one_right
    change epsilon M hM *
      ((((L4.specialValueOrder M).toNat : baseField M hM) + 2) - epsilon M hM) = 1
    linear_combination -(epsilon_polynomial M hM)
  refine ⟨⟨hpos, ?_⟩, P.epsilon_integral, ?_⟩
  · change 0 < sigma₂ M hM (epsilon M hM)
    rw [sigma₂_epsilon]
    exact inv_pos.mpr hpos
  · rw [hinv]
    exact ((isIntegral_natCast P.N : IsIntegral ℤ (P.N : baseField M hM)).add
      (isIntegral_natCast 2 : IsIntegral ℤ (2 : baseField M hM))).sub P.epsilon_integral

/-- An automorphism flips K exactly when it acts as the second real embedding
on every element. [RW26, p. 20]; [RW-rec, Prop. 7]. -/
theorem inducesNontrivial_iff (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (σ : Galois.QbarAut) :
    Galois.InducesNontrivial (baseField M hM) σ ↔
      ∀ x : baseField M hM, Galois.embed (σ (x : Galois.Qbar)) = (sigma₂ M hM x : ℂ) := by
  apply inducesNontrivial_iff_trace_sub (baseField M hM)
    (baseField_isRealQuadratic M hM).degree_two (sigma₁ M hM) ?_ σ
  intro x
  apply Complex.ext
  · rfl
  · exact (baseField_isRealQuadratic M hM).real x

#check @Galois.IsRealQuadratic
#check @Galois.InducesNontrivial
#check @L3.PeriodData
#check @Algebra.trace
#print baseField
#print sigma₂
#print periodData

end SICLean.L5.ActualField
