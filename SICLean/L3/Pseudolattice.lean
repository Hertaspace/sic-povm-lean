import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Algebra.Operations
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# Arithmetic pseudolattices and positive homothety

A pseudolattice is a full finitely generated integer submodule of the number
field, using `Submodule.IsLattice ℚ`, rather than an arbitrary pair of
real-scaled coordinates. No class-group finiteness or analytic conclusion is
an input.
-/

noncomputable section

namespace SICLean.L3

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Raw quadratic field, two real embeddings, and the specified period.
The polynomial, positivity, and conjugate equations are arithmetic input,
not finiteness or distribution conclusions. -/
structure PeriodData (K : Type u) [Field K] [NumberField K] where
  sigma₁ : K →+* ℝ
  sigma₂ : K →+* ℝ
  finrank_eq_two : Module.finrank ℚ K = 2
  epsilon : K
  N : ℕ
  N_pos : 0 < N
  epsilon_polynomial : epsilon ^ 2 - ((N : K) + 2) * epsilon + 1 = 0
  epsilon_gt_one : 1 < sigma₁ epsilon
  epsilon_conj : sigma₂ epsilon = (sigma₁ epsilon)⁻¹

/-- Actual multiplication of a `K`-contained integer submodule. -/
def pseudolatticeScale (lam : K) (I : Submodule ℤ K) : Submodule ℤ K :=
  I.map (LinearMap.mulLeft ℤ lam)

/-- The period acts by multiplication in the number field. -/
def PeriodStable (P : PeriodData K) (I : Submodule ℤ K) : Prop :=
  pseudolatticeScale P.epsilon I = I

/-- Full integer lattices stable under the fixed period. In particular,
neither invertibility over `ℤ[ε]` nor maximal-order stability is assumed. -/
abbrev StablePseudolattice (P : PeriodData K) :=
  { I : Submodule ℤ K // Submodule.IsLattice ℚ I ∧ PeriodStable P I }

def TotallyPositive (P : PeriodData K) (lam : K) : Prop :=
  0 < P.sigma₁ lam ∧ 0 < P.sigma₂ lam

/-- A homothety by one actual field element, in the direction `I = λJ`. -/
def PositiveHomothetic (P : PeriodData K) (I J : Submodule ℤ K) : Prop :=
  ∃ lam : K, TotallyPositive P lam ∧ I = pseudolatticeScale lam J

/-- The pair used by the later real-coordinate homothety. -/
def pseudolatticeScales (P : PeriodData K) (lam : K) : ℝ × ℝ :=
  (P.sigma₁ lam, P.sigma₂ lam)

/- The period is a nonzero unit; its first embedding is > 1. -/
theorem PeriodData.epsilon_ne_zero (P : PeriodData K) : P.epsilon ≠ 0 := by
  intro h
  have hpoly := P.epsilon_polynomial
  rw [h, mul_zero, sub_zero] at hpoly
  norm_num at hpoly

/- The monic polynomial X²-(N+2)X+1 makes ε integral over ℤ. -/
theorem PeriodData.epsilon_integral (P : PeriodData K) : IsIntegral ℤ P.epsilon := by
  refine ⟨Polynomial.X ^ 2 -
      (Polynomial.C (((P.N : ℤ) + 2)) * Polynomial.X - Polynomial.C 1), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    compute_degree!
  · change Polynomial.aeval P.epsilon
      (Polynomial.X ^ 2 -
        (Polynomial.C (((P.N : ℤ) + 2)) * Polynomial.X - Polynomial.C 1)) = 0
    simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      map_add, map_ofNat]
    norm_num
    linear_combination P.epsilon_polynomial

/-- Nonrationality follows from the two incompatible rational images of
the period. Degree two then makes ε a generator of `K/ℚ`. -/
theorem PeriodData.epsilon_adjoin_eq_top (P : PeriodData K) :
    Algebra.adjoin ℚ ({P.epsilon} : Set K) = ⊤ := by
  have hint : IsIntegral ℤ P.epsilon := P.epsilon_integral
  have halg : IsAlgebraic ℚ P.epsilon := IsAlgebraic.of_finite ℚ P.epsilon
  have hnonmem : P.epsilon ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    have h1 : P.sigma₁ P.epsilon = (q : ℝ) := by
      rw [← hq]
      exact map_ratCast P.sigma₁ q
    have h2 : P.sigma₂ P.epsilon = (q : ℝ) := by
      rw [← hq]
      exact map_ratCast P.sigma₂ q
    have hqpos : 1 < (q : ℝ) := h1 ▸ P.epsilon_gt_one
    have hinv : (q : ℝ) = (q : ℝ)⁻¹ := by
      calc (q : ℝ) = P.sigma₂ P.epsilon := h2.symm
        _ = (P.sigma₁ P.epsilon)⁻¹ := P.epsilon_conj
        _ = (q : ℝ)⁻¹ := by rw [h1]
    have hqne : (q : ℝ) ≠ 0 := by positivity
    have hsquare : (q : ℝ) * (q : ℝ) = 1 := by
      have hmul := congrArg (fun t : ℝ => t * (q : ℝ)) hinv
      simpa [inv_mul_cancel₀ hqne] using hmul
    nlinarith [hqpos, hsquare]
  have hdeg : (minpoly ℚ P.epsilon).natDegree = 2 := by
    apply le_antisymm
    · have hle := minpoly.natDegree_le (A := ℚ) (B := K) (x := P.epsilon)
      rwa [P.finrank_eq_two] at hle
    · rw [minpoly.two_le_natDegree_iff halg.isIntegral]
      exact hnonmem
  let S : IntermediateField ℚ K := IntermediateField.adjoin ℚ ({P.epsilon} : Set K)
  have hfinS : Module.finrank ℚ S = 2 := by
    have h := IntermediateField.adjoin.finrank (K := ℚ) (L := K) (x := P.epsilon)
      halg.isIntegral
    rw [hdeg] at h
    exact h
  have hsub : S.toSubalgebra.toSubmodule = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Subalgebra.finrank_toSubmodule,
      IntermediateField.finrank_eq_finrank_subalgebra, hfinS, P.finrank_eq_two]
  have hSsubalg : S.toSubalgebra = ⊤ := by
    rw [← Algebra.toSubmodule_eq_top]
    exact hsub
  have hS : S = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj]
    simpa using hSsubalg
  exact Algebra.adjoin_eq_top_of_intermediateField (S := ({P.epsilon} : Set K))
    (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact halg) hS

/- Total positivity is positivity at the two real embeddings. -/
theorem totallyPositive_ne_zero (P : PeriodData K) (lam : K)
    (hlam : TotallyPositive P lam) : lam ≠ 0 := by
  intro h
  subst h
  unfold TotallyPositive at hlam
  simp at hlam

/- Unpack actual field multiplication on the integer submodule. -/
theorem pseudolatticeScale_mem_iff (lam x : K) (I : Submodule ℤ K) :
    x ∈ pseudolatticeScale lam I ↔ ∃ y ∈ I, lam * y = x := by
  simp [pseudolatticeScale, LinearMap.mulLeft_apply]

/- Multiplication by 1 fixes a lattice. -/
theorem pseudolatticeScale_one (I : Submodule ℤ K) :
    pseudolatticeScale 1 I = I := by
  simp [pseudolatticeScale]

/- Composition of field homotheties. -/
theorem pseudolatticeScale_mul (lam μ : K) (I : Submodule ℤ K) :
    pseudolatticeScale (lam * μ) I = pseudolatticeScale lam (pseudolatticeScale μ I) := by
  simp only [pseudolatticeScale]
  rw [LinearMap.mulLeft_mul, Submodule.map_comp]

/- Undo a nonzero field homothety. -/
theorem pseudolatticeScale_inv (lam : K) (hlam : lam ≠ 0) (I : Submodule ℤ K) :
    pseudolatticeScale lam⁻¹ (pseudolatticeScale lam I) = I ∧
      pseudolatticeScale lam (pseudolatticeScale lam⁻¹ I) = I := by
  constructor
  · rw [← pseudolatticeScale_mul, inv_mul_cancel₀ hlam, pseudolatticeScale_one]
  · rw [← pseudolatticeScale_mul, mul_inv_cancel₀ hlam, pseudolatticeScale_one]

/- Nonzero field scaling preserves a full integer lattice. -/
theorem pseudolatticeScale_isLattice (I : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (lam : K) (hlam : lam ≠ 0) :
    Submodule.IsLattice ℚ (pseudolatticeScale lam I) := by
  letI : Submodule.IsLattice ℚ I := hI
  constructor
  · exact hI.fg.map (LinearMap.mulLeft ℤ lam)
  · have hsurj : Function.Surjective (LinearMap.mulLeft ℚ lam) := fun x =>
      ⟨lam⁻¹ * x, by
        change lam * (lam⁻¹ * x) = x
        rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]⟩
    calc Submodule.span ℚ ((pseudolatticeScale lam I : Submodule ℤ K) : Set K)
        = Submodule.span ℚ ((LinearMap.mulLeft ℚ lam) '' (I : Set K)) := rfl
      _ = (Submodule.span ℚ (I : Set K)).map (LinearMap.mulLeft ℚ lam) :=
        (Submodule.map_span _ _).symm
      _ = ⊤ := by
        rw [hI.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

/- Scalar multiplication commutes with the period action. -/
theorem pseudolatticeScale_periodStable (P : PeriodData K) (I : Submodule ℤ K)
    (hI : PeriodStable P I) (lam : K) :
    PeriodStable P (pseudolatticeScale lam I) := by
  unfold PeriodStable
  rw [← pseudolatticeScale_mul, mul_comm, pseudolatticeScale_mul, hI]

/- A pseudolattice has integer rank two; `Submodule.IsLattice.rank'` transfers the rational rank. -/
theorem pseudolattice_finrank (P : PeriodData K) (I : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) : Module.finrank ℤ I = 2 := by
  letI : Submodule.IsLattice ℚ I := hI
  have hrank : Module.rank ℤ I = (2 : Cardinal) := by
    rw [Submodule.IsLattice.rank' ℚ I, ← Module.finrank_eq_rank, P.finrank_eq_two]
    norm_num
  exact Module.finrank_eq_of_rank_eq hrank

/- The rank-two integer lattice has a two-element basis before admissibility is imposed. -/
theorem pseudolattice_exists_basis (P : PeriodData K) (I : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) : Nonempty (Module.Basis (Fin 2) ℤ I) := by
  letI : Submodule.IsLattice ℚ I := hI
  have hfr : Module.finrank ℤ I = 2 := pseudolattice_finrank P I hI
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ I) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hfr]
  exact ⟨(Module.Free.chooseBasis ℤ I).reindex (Fintype.equivFinOfCardEq hcard)⟩

/- The scalar 1 is totally positive. -/
theorem positiveHomothetic_refl (P : PeriodData K) (I : Submodule ℤ K) :
    PositiveHomothetic P I I := by
  refine ⟨1, ⟨by simp, by simp⟩, ?_⟩
  exact (pseudolatticeScale_one I).symm

/- Inverse totally positive homothety. -/
theorem positiveHomothetic_symm (P : PeriodData K) (I J : Submodule ℤ K)
    (h : PositiveHomothetic P I J) : PositiveHomothetic P J I := by
  obtain ⟨lam, hpos, hIJ⟩ := h
  have hlam : lam ≠ 0 := totallyPositive_ne_zero P lam hpos
  refine ⟨lam⁻¹, ⟨?_, ?_⟩, ?_⟩
  · simp only [map_inv₀]
    exact inv_pos.mpr hpos.1
  · simp only [map_inv₀]
    exact inv_pos.mpr hpos.2
  · have hinv := (pseudolatticeScale_inv lam hlam J).1
    rw [← hIJ] at hinv
    exact hinv.symm

/- Product of totally positive homotheties. -/
theorem positiveHomothetic_trans (P : PeriodData K) (I J L : Submodule ℤ K)
    (hIJ : PositiveHomothetic P I J) (hJL : PositiveHomothetic P J L) :
    PositiveHomothetic P I L := by
  obtain ⟨lam, hpos, hIJ⟩ := hIJ
  obtain ⟨mu, hpos', hJL⟩ := hJL
  refine ⟨lam * mu, ⟨?_, ?_⟩, ?_⟩
  · rw [map_mul]
    exact mul_pos hpos.1 hpos'.1
  · rw [map_mul]
    exact mul_pos hpos.2 hpos'.2
  · rw [hIJ, hJL]
    exact (pseudolatticeScale_mul lam mu L).symm

def stablePseudolatticeSetoid (P : PeriodData K) : Setoid (StablePseudolattice P) where
  r I J := PositiveHomothetic P I.1 J.1
  iseqv :=
    { refl := fun I => positiveHomothetic_refl P I.1
      symm := fun h => positiveHomothetic_symm P _ _ h
      trans := fun hIJ hJL => positiveHomothetic_trans P _ _ _ hIJ hJL }

abbrev StablePseudolatticeClass (P : PeriodData K) :=
  Quotient (stablePseudolatticeSetoid P)

/-- This constructor packages only the lattice and stability conclusions
of the two scale lemmas above. -/
def stablePseudolatticeScale (P : PeriodData K) (lam : K) (hlam : lam ≠ 0)
    (I : StablePseudolattice P) : StablePseudolattice P :=
  ⟨pseudolatticeScale lam I.1,
    ⟨pseudolatticeScale_isLattice I.1 I.2.1 lam hlam,
      pseudolatticeScale_periodStable P I.1 I.2.2 lam⟩⟩

end SICLean.L3
