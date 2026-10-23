import SICLean.L4.G2AnalyticInputs
import SICLean.L4.M78Specializations
import SICLean.L3.PeriodDataExistence
import SICLean.Galois.L2Inputs
import SICLean.Statement

set_option autoImplicit false

/-!
# Final assembly: G1 and Proposition 7 give both existence theorems

`G1RealConclusion` yields Fourier (6), the five-term identity (7) for every
admissible matrix, and the analytic input of both chains. Identity (7) yields
algebraicity of every actual special value. Algebraicity together with
[RW-rec, Prop. 7] yields the unit-circle input of L2a and L2r.

The remaining hypothesis is [RW-rec, Prop. 7], stated in `Prop7Actual` for the
values `rwL2cPlus` and `rwL2rcPlus`. The values enter through `embed`.
The proposition, with K = ℚ(√Δ), implies this input. It is proved in `SICLean.L5.ActualProp7`.
-/

noncomputable section

open OpenQuantumProblem23
open scoped MatrixGroups

namespace SICLean.FinalAssembly

/-- G1 yields `MatrixPentagon` for every admissible matrix. -/
theorem doubling_matrixPentagon_of_G1 (hG1 : L4.G1RealConclusion)
    (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    L3.M75.Doubling.MatrixPentagon M hM := by
  exact L4.matrixPentagon_of_G1 hG1 M hM

/-- (7) for every matrix of an arbitrary finite pseudolattice family. -/
theorem familyPentagon_of_G1 (hG1 : L4.G1RealConclusion)
    {K : Type} [Field K] [NumberField K] {P : L3.PeriodData K}
    (F : L3.FinitePseudolatticeFamily P) :
    L3.M75.Family.FamilyPentagon F := by
  intro i
  exact doubling_matrixPentagon_of_G1 hG1 _ _

/-- Original chain: every actual value is algebraic, from G1 alone. -/
theorem rwL2c_values_isAlgebraic_of_G1 (hG1 : L4.G1RealConclusion)
    (M : ℕ) [Fact (4 ≤ M)] (g : L2c.RWGroup M) :
    IsAlgebraic ℚ (L4.rwL2cPlus M g) ∧ IsAlgebraic ℚ (L4.rwL2cMinus M g) := by
  have hM : 4 ≤ M := Fact.out
  have hN : 0 < L2b.groupOrder M := by
    simp only [L2b.groupOrder, L2b.cofactor]
    exact Nat.mul_pos (pow_pos (by omega) 2) (by omega)
  obtain ⟨K, hK, hNF, P, hP⟩ :=
    L3.PeriodDataExistence.exists_periodData (L2b.groupOrder M) hN
  let : Field K := hK
  let : NumberField K := hNF
  let F := L3.chosenPseudolatticeFamily P
  exact L3.M78.Specializations.l2c_values_isAlgebraic F
    (familyPentagon_of_G1 hG1 F) M hP g

/-- Rank-r chain: every actual value is algebraic, from G1 alone. -/
theorem rwL2rc_values_isAlgebraic_of_G1 (hG1 : L4.G1RealConclusion)
    (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2rc.RWGroup d r) :
    IsAlgebraic ℚ (L4.rwL2rcPlus d r g) ∧ IsAlgebraic ℚ (L4.rwL2rcMinus d r g) := by
  have h := Fact.out (p := L2r.Admissible d r)
  have hlevel : 5 ≤ L2r.level d r := L2r.level_ge_five h
  have hd : 0 < d := by
    have := h.main_range
    omega
  have hco : 0 < L2r.cofactor d r := by
    simp only [L2r.cofactor]
    omega
  have hN : 0 < L2r.groupOrder d r := by
    exact Nat.mul_pos (pow_pos hd 2) hco
  obtain ⟨K, hK, hNF, P, hP⟩ :=
    L3.PeriodDataExistence.exists_periodData (L2r.groupOrder d r) hN
  let : Field K := hK
  let : NumberField K := hNF
  let F := L3.chosenPseudolatticeFamily P
  exact L3.M78.Specializations.l2rc_values_isAlgebraic F
    (familyPentagon_of_G1 hG1 F) d r hP g

/-- [RW-rec, Prop. 7] for given complex values:
for some real quadratic K ⊂ ℚbar, every automorphism of ℚbar inducing the
nontrivial automorphism of K sends each value of a nonzero class to the unit
circle. Nothing is asserted at the zero class. -/
def Prop7Actual {J : Type*} [Zero J] (E : J → ℂ) : Prop :=
  ∃ K : IntermediateField ℚ Galois.Qbar, Galois.IsRealQuadratic K ∧
    ∀ σ : Galois.QbarAut, Galois.InducesNontrivial K σ →
      ∀ x : J, x ≠ 0 → ∀ a : Galois.Qbar, Galois.embed a = E x →
        ‖Galois.embed (σ a)‖ = 1

/-- Algebraicity plus Prop7Actual is the one-witness interface for `Galois.Prop7Input`. -/
theorem prop7Input_of_actual {J : Type*} [Zero J] (E : J → ℂ)
    (hAlg : ∀ x, IsAlgebraic ℚ (E x)) (h7 : Prop7Actual E) :
    Galois.Prop7Input E := by
  obtain ⟨K, hK, h7⟩ := h7
  obtain ⟨σ, hσ⟩ := Galois.exists_nontrivial_lift K hK
  refine ⟨hAlg, K, hK, σ, hσ, ?_⟩
  intro x hx
  exact h7 σ hσ x hx (Galois.algebraicLift (E x) (hAlg x))
    (Galois.embed_algebraicLift (E x) (hAlg x))

/-- SIC-POVMs exist in every dimension, given G1 and Proposition 7 for the
actual values of the original chain. -/
theorem zaunerExistence_of_G1_prop7 (hG1 : L4.G1RealConclusion)
    (H7 : ∀ (M : ℕ) (hM : 4 ≤ M),
      letI : Fact (4 ≤ M) := ⟨hM⟩
      Prop7Actual (L4.rwL2cPlus M)) :
    ZaunerExistence := by
  apply zaunerExistence_of_theorem2
  intro M hM
  let : Fact (4 ≤ M) := ⟨hM⟩
  refine ⟨L4.rwL2cPlus M, L4.rwL2cMinus M,
    L4.rwL2cAnalyticInput_of_G1 hG1 M, ?_⟩
  apply Galois.unitCircleInput_L2c
  exact prop7Input_of_actual (L4.rwL2cPlus M)
    (fun g => (rwL2c_values_isAlgebraic_of_G1 hG1 M g).1) (H7 M hM)

/-- Rank-r SICs exist in the whole admissible range, given G1 and
Proposition 7 for the actual values of the rank-r chain. -/
theorem hasRSIC_of_G1_prop7 (hG1 : L4.G1RealConclusion)
    (H7 : ∀ (d r : ℕ) (hr : 1 ≤ r) (hd : 2 * r + 1 < d)
      (hdiv : r * (d - r) ∣ d ^ 2 - 1),
      letI : Fact (L2r.Admissible d r) := ⟨⟨hr, hd, hdiv⟩⟩
      Prop7Actual (L4.rwL2rcPlus d r)) :
    ∀ (d r : ℕ), 1 ≤ r → 2 * r + 1 < d → r * (d - r) ∣ d ^ 2 - 1 →
      HasRSIC d r := by
  apply hasRSIC_of_theorem2
  intro d r hr hd hdiv
  let : Fact (L2r.Admissible d r) := ⟨⟨hr, hd, hdiv⟩⟩
  refine ⟨L4.rwL2rcPlus d r, L4.rwL2rcMinus d r,
    L4.rwL2rcAnalyticInput_of_G1 hG1 d r, ?_⟩
  apply Galois.unitCircleInput_L2rc
  exact prop7Input_of_actual (L4.rwL2rcPlus d r)
    (fun g => (rwL2rc_values_isAlgebraic_of_G1 hG1 d r g).1)
    (H7 d r hr hd hdiv)

end SICLean.FinalAssembly
