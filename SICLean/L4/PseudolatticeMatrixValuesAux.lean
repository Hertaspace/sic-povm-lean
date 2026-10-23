import SICLean.L4.PseudolatticeHomothety

set_option autoImplicit false

/-!
# Arithmetic for the canonical matrix pseudolattice

The two generators are ((epsilon-d)/c,1).  The first embedding selects
the attracting fixed point, and the conjugate embedding selects the
other root.  The integral matrix and its inverse preserve their span.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L4.PseudolatticeMatrixValuesAux

open SICLean.L3

universe u
variable {K : Type u} [Field K] [NumberField K]

def tauK (P : PeriodData K) (M : SL(2, ℤ)) : K :=
  (P.epsilon - (M 1 1 : K)) / (M 1 0 : K)

def lattice (P : PeriodData K) (M : SL(2, ℤ)) : Submodule ℤ K :=
  Submodule.span ℤ ({tauK P M, 1} : Set K)

theorem trace_int (P : PeriodData K) (M : SL(2, ℤ))
    (hN : specialValueOrder M = (P.N : ℤ)) :
    M 0 0 + M 1 1 = (P.N : ℤ) + 2 := by
  unfold specialValueOrder at hN
  omega

theorem det_int (M : SL(2, ℤ)) :
    M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using M.det_coe

theorem c_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (M 1 0 : K) ≠ 0 := by
  exact_mod_cast (ne_of_gt hM.1)

theorem epsilon_mul_tauK (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (hN : specialValueOrder M = (P.N : ℤ)) :
    P.epsilon * tauK P M = (M 0 0 : K) * tauK P M + (M 0 1 : K) := by
  have ht : (M 0 0 : K) + (M 1 1 : K) = (P.N : K) + 2 := by
    exact_mod_cast trace_int P M hN
  have hd : (M 0 0 : K) * (M 1 1 : K) - (M 0 1 : K) * (M 1 0 : K) = 1 := by
    exact_mod_cast det_int M
  unfold tauK
  field_simp [c_ne_zero (K := K) M hM]
  linear_combination P.epsilon_polynomial - P.epsilon * ht + hd

theorem epsilon_eq_c_tauK_add_d (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) :
    P.epsilon = (M 1 0 : K) * tauK P M + (M 1 1 : K) := by
  unfold tauK
  field_simp [c_ne_zero (K := K) M hM]
  ring

private theorem root_gt_trace_sub_one (T x : ℝ) (hT : 2 < T) (hx : 1 < x)
    (hp : x ^ 2 - T * x + 1 = 0) : T - 1 < x := by
  by_contra h
  have hmul := mul_nonneg (le_of_lt (sub_pos.mpr hx)) (sub_nonneg.mpr (le_of_not_gt h))
  nlinarith

private theorem root_unique (T x y : ℝ) (hT : 2 < T) (hx : 1 < x) (hy : 1 < y)
    (hpx : x ^ 2 - T * x + 1 = 0) (hpy : y ^ 2 - T * y + 1 = 0) : x = y := by
  have hxx := root_gt_trace_sub_one T x hT hx hpx
  have hyy := root_gt_trace_sub_one T y hT hy hpy
  have hp : (x - y) * (x + y - T) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with h | h
  · linarith
  · linarith

theorem epsilon_eq_embedding (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (hN : specialValueOrder M = (P.N : ℤ)) :
    specialValueEpsilon M = P.sigma₁ P.epsilon := by
  have hp : (P.sigma₁ P.epsilon) ^ 2 - ((P.N : ℝ) + 2) * P.sigma₁ P.epsilon + 1 = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat, map_one,
      map_zero] using congrArg P.sigma₁ P.epsilon_polynomial
  have hN' : (specialValueOrder M : ℝ) = (P.N : ℝ) := by exact_mod_cast hN
  have hq := specialValueEpsilon_characteristic M hM
  rw [hN'] at hq
  exact root_unique ((P.N : ℝ) + 2) _ _ (by
    have hpos : (0 : ℝ) < P.N := by exact_mod_cast P.N_pos
    linarith)
    (specialValueEpsilon_gt_one M hM) P.epsilon_gt_one hq hp

theorem sigma_one_tauK (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (hN : specialValueOrder M = (P.N : ℤ)) :
    P.sigma₁ (tauK P M) = specialValueTau M := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM.1)
  simp only [tauK, map_div₀, map_sub, map_intCast]
  rw [← epsilon_eq_embedding P M hM hN]
  unfold specialValueEpsilon
  field_simp [hc]
  ring

theorem sigma_two_tauK (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (hN : specialValueOrder M = (P.N : ℤ)) :
    P.sigma₂ (tauK P M) =
      distributionConjugateTau ⟨M, specialValueTau M, 1, 1⟩ := by
  have ht : (M 0 0 : ℝ) + (M 1 1 : ℝ) = (P.N : ℝ) + 2 := by
    exact_mod_cast trace_int P M hN
  have hp : (P.sigma₁ P.epsilon) ^ 2 - ((P.N : ℝ) + 2) * P.sigma₁ P.epsilon + 1 = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat, map_one,
      map_zero] using congrArg P.sigma₁ P.epsilon_polynomial
  have he : P.sigma₁ P.epsilon ≠ 0 := ne_of_gt (lt_trans zero_lt_one P.epsilon_gt_one)
  have hi : (P.sigma₁ P.epsilon)⁻¹ = (M 0 0 : ℝ) + (M 1 1 : ℝ) - P.sigma₁ P.epsilon := by
    apply (mul_eq_one_iff_inv_eq₀ he).mp
    nlinarith
  change P.sigma₂ (tauK P M) = ((M 0 0 : ℝ) - (M 1 1 : ℝ)) / (M 1 0 : ℝ) -
    specialValueTau M
  rw [← sigma_one_tauK P M hM hN]
  simp only [tauK, map_div₀, map_sub, map_intCast]
  rw [P.epsilon_conj, hi]
  ring

theorem tauK_embedding (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (hN : specialValueOrder M = (P.N : ℤ)) :
    pseudolatticeEmbedding P (tauK P M) =
      distributionBetaOne ⟨M, specialValueTau M, 1, 1⟩ ∧
      specialValueEpsilon M = P.sigma₁ P.epsilon := by
  refine ⟨?_, epsilon_eq_embedding P M hM hN⟩
  apply Prod.ext
  · simpa [pseudolatticeEmbedding, distributionBetaOne] using sigma_one_tauK P M hM hN
  · simpa [pseudolatticeEmbedding, distributionBetaOne] using sigma_two_tauK P M hM hN

theorem tauK_linearIndependent (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (hN : specialValueOrder M = (P.N : ℤ)) :
    LinearIndependent ℚ ![tauK P M, (1 : K)] := by
  rw [linearIndependent_fin2]
  change (1 : K) ≠ 0 ∧ ∀ q : ℚ, q • (1 : K) ≠ tauK P M
  refine ⟨one_ne_zero, ?_⟩
  intro q hq
  have hq' : (q : K) = tauK P M := by simpa [Algebra.smul_def] using hq
  have hs := congrArg P.sigma₁ hq'
  apply (specialValueTau_irrational M hM).ne_rat q
  rw [← sigma_one_tauK P M hM hN]
  simpa only [map_ratCast] using hs.symm

theorem lattice_isLattice (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (hN : specialValueOrder M = (P.N : ℤ)) :
    Submodule.IsLattice ℚ (lattice P M) := by
  refine ⟨Submodule.fg_span (Set.toFinite _), ?_⟩
  have hs := (tauK_linearIndependent P M hM hN).span_eq_top_of_card_eq_finrank'
    (by simpa using P.finrank_eq_two.symm)
  apply eq_top_iff.mpr
  rw [← hs]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  fin_cases i <;> apply Submodule.subset_span <;> simp

theorem tauK_mem (P : PeriodData K) (M : SL(2, ℤ)) : tauK P M ∈ lattice P M :=
  Submodule.subset_span (by simp)

theorem one_mem (P : PeriodData K) (M : SL(2, ℤ)) : (1 : K) ∈ lattice P M :=
  Submodule.subset_span (by simp)

theorem integral_combination_mem (P : PeriodData K) (M : SL(2, ℤ)) (r s : ℤ) :
    (r : K) * tauK P M + (s : K) ∈ lattice P M := by
  have hr : (r : K) * tauK P M ∈ lattice P M := by
    simpa only [zsmul_eq_mul] using (lattice P M).smul_mem r (tauK_mem P M)
  have hs : (s : K) ∈ lattice P M := by
    simpa only [zsmul_eq_mul, mul_one] using (lattice P M).smul_mem s (one_mem P M)
  exact (lattice P M).add_mem hr hs

theorem lattice_periodStable (P : PeriodData K) (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (hN : specialValueOrder M = (P.N : ℤ)) :
    PeriodStable P (lattice P M) := by
  have he := epsilon_mul_tauK P M hM hN
  have he' := epsilon_eq_c_tauK_add_d P M hM
  have hd : (M 0 0 : K) * (M 1 1 : K) - (M 0 1 : K) * (M 1 0 : K) = 1 := by
    exact_mod_cast det_int M
  change (lattice P M).map (LinearMap.mulLeft ℤ P.epsilon) = lattice P M
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change P.epsilon * tauK P M ∈ lattice P M
      rw [he]
      exact integral_combination_mem P M (M 0 0) (M 0 1)
    · change P.epsilon * 1 ∈ lattice P M
      rw [mul_one, he']
      exact integral_combination_mem P M (M 1 0) (M 1 1)
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨(M 1 1 : K) * tauK P M - (M 0 1 : K), ?_, ?_⟩
      · change (M 1 1 : K) * tauK P M - (M 0 1 : K) ∈ lattice P M
        simpa only [Int.cast_neg, sub_eq_add_neg] using
          integral_combination_mem P M (M 1 1) (-M 0 1)
      · change P.epsilon * ((M 1 1 : K) * tauK P M - (M 0 1 : K)) = tauK P M
        calc
          _ = (M 1 1 : K) * (P.epsilon * tauK P M) - (M 0 1 : K) * P.epsilon := by ring
          _ = tauK P M := by rw [he, he']; linear_combination tauK P M * hd
    · refine ⟨-(M 1 0 : K) * tauK P M + (M 0 0 : K), ?_, ?_⟩
      · change -(M 1 0 : K) * tauK P M + (M 0 0 : K) ∈ lattice P M
        simpa only [Int.cast_neg] using integral_combination_mem P M (-M 1 0) (M 0 0)
      · change P.epsilon * (-(M 1 0 : K) * tauK P M + (M 0 0 : K)) = 1
        calc
          _ = -(M 1 0 : K) * (P.epsilon * tauK P M) + (M 0 0 : K) * P.epsilon := by ring
          _ = 1 := by rw [he, he']; linear_combination hd

end SICLean.L4.PseudolatticeMatrixValuesAux
