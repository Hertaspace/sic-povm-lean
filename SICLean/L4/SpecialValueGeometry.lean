import SICLean.L4.ModularDivisor
import SICLean.L4.ModularCocycle
import SICLean.L2r.Group
import SICLean.L4.SpecialValueGeometryAux

set_option autoImplicit false

/-!
# Attracting fixed point and the row quotient

All declarations in this file are proved.
[RW26, pp. 2--3, p. 12, (2)--(3), Lemma 2]. These are elementary interfaces, not analytic inputs.

The hypotheses specify c>0 and trace>2 only. In particular neither
periodicity nor nonvanishing is part of an admissibility definition.
`specialValueLattice` reuses the existing L2r row-lattice construction.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4

/-- The geometric scope of [RW26, p. 2, (2)]. -/
def SpecialValueAdmissible (M : SL(2, ℤ)) : Prop :=
  0 < M 1 0 ∧ 2 < M 0 0 + M 1 1

/-- N=tr(M)-2, kept as an integer. Positivity is `specialValueOrder_pos`. -/
def specialValueOrder (M : SL(2, ℤ)) : ℤ := M 0 0 + M 1 1 - 2

/-- The attracting root, not an unspecified chosen fixed point. -/
def specialValueTau (M : SL(2, ℤ)) : ℝ :=
  ((M 0 0 : ℝ) - (M 1 1 : ℝ) +
    Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)) / (2 * (M 1 0 : ℝ))

/-- The actual automorphy factor cτ+d at that root. -/
def specialValueEpsilon (M : SL(2, ℤ)) : ℝ :=
  (M 1 0 : ℝ) * specialValueTau M + (M 1 1 : ℝ)

/-- Integer vectors are rows throughout, as in [RW26, (3)]. -/
def specialValueLattice (M : SL(2, ℤ)) : AddSubgroup (ℤ × ℤ) :=
  L2r.rowLattice ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)

abbrev SpecialValueGroup (M : SL(2, ℤ)) := (ℤ × ℤ) ⧸ specialValueLattice M

def specialValueMk (M : SL(2, ℤ)) : (ℤ × ℤ) →+ SpecialValueGroup M :=
  QuotientAddGroup.mk' (specialValueLattice M)

/-- Exactly the argument of [RW26, (2)], using the existing definition. -/
def specialValueArgument (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℂ :=
  modularPhiSpecialArgument M ![u.1, u.2] (specialValueTau M : ℂ)

/-- Real form of the fixed-point relation `aτ+b = τ(cτ+d)`. -/
lemma specialValueTau_real_relation (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (M 0 0 : ℝ) * specialValueTau M + (M 0 1 : ℝ) =
      specialValueTau M * ((M 1 0 : ℝ) * specialValueTau M + (M 1 1 : ℝ)) := by
  have hc : (0:ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hdet : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    exact_mod_cast det_coe_int M
  have htr : (2:ℝ) < (M 0 0 : ℝ) + (M 1 1 : ℝ) := by exact_mod_cast hM.2
  have hsq : (Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)) ^ 2 =
      ((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4 := by
    rw [Real.sq_sqrt]; nlinarith
  rw [specialValueTau]
  field_simp
  ring_nf at hsq ⊢
  nlinarith [hsq, hdet]

/-- [RW26, pp. 2--3]. -/
theorem specialValueOrder_pos (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < specialValueOrder M := by
  have h := hM.2
  unfold specialValueOrder
  omega

/-- The explicit root is fixed. [RW26, p. 2]. -/
theorem specialValueTau_fixedPoint (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    etaMobius M (specialValueTau M : ℂ) = (specialValueTau M : ℂ) := by
  have hc : (0:ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have htr : (2:ℝ) < (M 0 0 : ℝ) + (M 1 1 : ℝ) := by exact_mod_cast hM.2
  have hdet : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    exact_mod_cast det_coe_int M
  have hsq : (Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)) ^ 2 =
      ((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4 := by
    rw [Real.sq_sqrt]; nlinarith
  have hreal := specialValueTau_real_relation M hM
  have htauDenom : (M 1 0 : ℝ) * specialValueTau M + (M 1 1 : ℝ) =
      ((M 0 0 : ℝ) + (M 1 1 : ℝ) +
        Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)) / 2 := by
    rw [specialValueTau]
    field_simp
    ring
  have hden : ((M 1 0 : ℝ) * specialValueTau M + (M 1 1 : ℝ)) ≠ 0 := by
    rw [htauDenom]
    have hs := Real.sqrt_nonneg (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)
    positivity
  have hdenC : ((M 1 0 : ℂ) * (specialValueTau M : ℂ) + (M 1 1 : ℂ)) ≠ 0 := by
    intro h
    apply hden
    exact_mod_cast h
  rw [etaMobius, etaDenom]
  rw [div_eq_iff hdenC]
  exact_mod_cast hreal

/-- [RW26, p. 3, (4), Theorem 2]. -/
theorem specialValueEpsilon_formula (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    specialValueEpsilon M = ((specialValueOrder M : ℝ) + 2 +
      Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2 := by
  have hc : (0:ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have harg : (specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ) =
      ((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4 := by
    rw [specialValueOrder]
    push_cast
    ring
  rw [harg, specialValueEpsilon, specialValueTau, specialValueOrder]
  field_simp
  push_cast
  ring

/--
Attracting branch. [RW26, p. 3, (4)].
-/
theorem specialValueEpsilon_gt_one (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    1 < specialValueEpsilon M := by
  rw [specialValueEpsilon_formula M hM]
  have hN : (0:ℝ) < (specialValueOrder M : ℝ) := by exact_mod_cast specialValueOrder_pos M hM
  have hs := Real.sqrt_nonneg ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))
  nlinarith

/-- The characteristic equation. [RW26, p. 2]. -/
theorem specialValueEpsilon_characteristic (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) :
    specialValueEpsilon M ^ 2 - ((specialValueOrder M : ℝ) + 2) *
      specialValueEpsilon M + 1 = 0 := by
  rw [specialValueEpsilon_formula M hM]
  have hN : (0:ℝ) < (specialValueOrder M : ℝ) := by exact_mod_cast specialValueOrder_pos M hM
  have hsq : (Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) ^ 2 =
      (specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ) := by
    rw [Real.sq_sqrt]; nlinarith
  nlinarith

/-- The same characteristic relation in the form used for the argument. -/
lemma specialValueEpsilon_sq_relation (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (specialValueEpsilon M - 1) ^ 2 = (specialValueOrder M : ℝ) * specialValueEpsilon M := by
  have hchar := specialValueEpsilon_characteristic M hM
  nlinarith

/-- [RW26, p. 12]. -/
theorem specialValueTau_irrational (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    Irrational (specialValueTau M) := by
  have hN : 0 < M 0 0 + M 1 1 - 2 := specialValueOrder_pos M hM
  let s : ℝ := Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)
  have hz : ((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4 = (((M 0 0 + M 1 1) ^ 2 - 4 : ℤ) : ℝ) := by
    push_cast; ring
  have hzeq : ((M 0 0 + M 1 1) ^ 2 - 4 : ℤ) = (M 0 0 + M 1 1 - 2) * (M 0 0 + M 1 1 - 2 + 4) := by ring
  have hs : Irrational s := by
    dsimp only [s]
    rw [hz]
    apply irrational_sqrt_intCast_iff.mpr
    constructor
    · rw [hzeq]; exact not_square_N_mul _ hN
    · rw [hzeq]; nlinarith
  have hsum : Irrational (s + ((M 0 0 : ℝ) - (M 1 1 : ℝ))) := by
    have := hs.add_intCast ((M 0 0) - (M 1 1))
    simpa using this
  have hm : ((2 * M 1 0 : ℤ)) ≠ 0 := by
    have : (0:ℤ) < M 1 0 := hM.1
    omega
  have hdiv : Irrational ((s + ((M 0 0 : ℝ) - (M 1 1 : ℝ))) / ((2 * M 1 0 : ℤ) : ℝ)) :=
    hsum.div_intCast hm
  convert hdiv using 1
  rw [specialValueTau]
  push_cast
  ring

/--
Cast bridge to the actual Φ domain, [RW26, p. 2].
-/
theorem specialValue_etaDenom (M : SL(2, ℤ)) :
    etaDenom M (specialValueTau M : ℂ) = (specialValueEpsilon M : ℂ) := by
  rw [etaDenom, specialValueEpsilon]
  push_cast
  ring

/--
The real point is inside the slit domain, not only on its boundary.
[RW26, p. 2].
-/
theorem specialValueTau_mem_domain (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (specialValueTau M : ℂ) ∈ modularPhiDomain M := by
  apply real_mem_modularPhiDomain
  change (0:ℝ) < specialValueEpsilon M
  linarith [specialValueEpsilon_gt_one M hM]

/--
The two literal descriptions of Λ in [RW26, p. 3, (3)]. No congruence is assumed of F.
-/
theorem specialValueLattice_mem_iff (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    u ∈ specialValueLattice M ↔
      specialValueOrder M ∣ (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u).1 - u.1 ∧
      specialValueOrder M ∣ (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u).2 - u.2 := by
  simpa [specialValueLattice, specialValueOrder] using
    rowLattice_sub_one_mem_iff M (specialValueOrder_pos M hM) u

/--
Row ranges agree; this invokes no Φ for the negative-c inverse.
[RW26, p. 12, Lemma 2].
-/
theorem specialValueLattice_inverse_eq (M : SL(2, ℤ)) :
    specialValueLattice M =
      L2r.rowLattice (((M⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) := by
  simpa [specialValueLattice] using rowLattice_sub_one_inverse_eq M

/--
Exact zero-class criterion, including both directions. [RW26, p. 12, Lemma 2].
-/
theorem specialValueArgument_mem_lattice_iff (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) :
    specialValueArgument M u ∈ modularPhiPseudoLattice (specialValueTau M : ℂ) ↔
      u ∈ specialValueLattice M := by
  rw [specialValueLattice_mem_iff M hM u]
  set τ : ℝ := specialValueTau M with hτdef
  set ε : ℝ := specialValueEpsilon M with hεdef
  set N : ℤ := specialValueOrder M with hNdef
  have hNpos : 0 < N := specialValueOrder_pos M hM
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hτirr : Irrational τ := specialValueTau_irrational M hM
  have hεgt : 1 < ε := specialValueEpsilon_gt_one M hM
  have hεne0 : ε ≠ 0 := by linarith
  have hεne1 : ε ≠ 1 := ne_of_gt hεgt
  have hrel0 := specialValueTau_real_relation M hM
  have hrel : (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) = τ * ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) := by
    simpa [← hτdef] using hrel0
  have hsqrel0 := specialValueEpsilon_sq_relation M hM
  have hsqrel : (ε - 1) ^ 2 = (N : ℝ) * ε := by
    simpa [← hεdef, ← hNdef] using hsqrel0
  let w : ℤ × ℤ := L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u
  let v : ℤ × ℤ := L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u
  let U : ℝ := (u.1 : ℝ) * τ + (u.2 : ℝ)
  have hvdef : v = w - u := by
    dsimp [v, w]
    rw [rowAction_sub_one_eq]
  have hv1 : v.1 = (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u).1 - u.1 := by
    have := congrArg Prod.fst (rowAction_sub_one_eq M u)
    simpa [v] using this
  have hv2 : v.2 = (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u).2 - u.2 := by
    have := congrArg Prod.snd (rowAction_sub_one_eq M u)
    simpa [v] using this
  have hεdef' : ε = (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) := by
    rw [hεdef, hτdef, specialValueEpsilon]
  have hwτ : (w.1 : ℝ) * τ + (w.2 : ℝ) = ε * U := by
    dsimp [w, U]
    simp only [L2r.rowAction]
    push_cast
    rw [hεdef']
    ring_nf at hrel ⊢
    linear_combination (u.1 : ℝ) * hrel
  have hvτ : (v.1 : ℝ) * τ + (v.2 : ℝ) = (ε - 1) * U := by
    rw [hvdef]
    simp only [Prod.fst_sub, Prod.snd_sub]
    push_cast
    nlinarith [hwτ]
  have hArgReal : U / (ε⁻¹ - 1) = -(((v.1 : ℝ) * τ + (v.2 : ℝ)) / N) := by
    rw [hvτ]
    have hE : ε / (ε - 1) = (ε - 1) / N := by
      field_simp [hεne1, hNne]
      nlinarith [hsqrel]
    calc
      U / (ε⁻¹ - 1) = -U * (ε / (ε - 1)) := by
        field_simp [hεne0, hεne1]
        ring
      _ = -U * ((ε - 1) / N) := by rw [hE]
      _ = -(((ε - 1) * U) / N) := by ring
  have hArg : specialValueArgument M u = -(((v.1 : ℂ) * (τ : ℂ) + (v.2 : ℂ)) / N) := by
    rw [specialValueArgument, modularPhiSpecialArgument]
    have h1 : (τ : ℂ) = (specialValueTau M : ℂ) := by rw [hτdef]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h1, specialValue_etaDenom M]
    exact_mod_cast hArgReal
  constructor
  · intro hmem
    obtain ⟨k, l, hkl⟩ := hmem
    rw [hArg] at hkl
    have hreal : -(((v.1 : ℝ) * τ + (v.2 : ℝ)) / N) = (k : ℝ) * τ + (l : ℝ) := by
      have := congrArg Complex.re hkl
      simpa using this
    have heq : ((v.1 + N * k : ℤ) : ℝ) * τ + ((v.2 + N * l : ℤ) : ℝ) = 0 := by
      field_simp [hNne] at hreal
      push_cast
      linarith
    have hcoef := int_linear_eq_zero hτirr heq
    have hvk : v.1 = -(N * k) := by linarith [hcoef.1]
    have hvl : v.2 = -(N * l) := by linarith [hcoef.2]
    constructor
    · rw [← hv1]
      exact ⟨-k, by rw [hvk]; ring⟩
    · rw [← hv2]
      exact ⟨-l, by rw [hvl]; ring⟩
  · rintro ⟨h1, h2⟩
    rw [← hv1] at h1
    rw [← hv2] at h2
    obtain ⟨k, hk⟩ := h1
    obtain ⟨l, hl⟩ := h2
    refine ⟨-k, -l, ?_⟩
    rw [hArg]
    have hkR : (v.1 : ℝ) = (N : ℝ) * (k : ℝ) := by exact_mod_cast hk
    have hlR : (v.2 : ℝ) = (N : ℝ) * (l : ℝ) := by exact_mod_cast hl
    have hreal_goal : -(((v.1 : ℝ) * τ + (v.2 : ℝ)) / N) = (-k : ℝ) * τ + (-l : ℝ) := by
      rw [hkR, hlR]
      field_simp [hNne]
      ring
    exact_mod_cast hreal_goal

/-- Cardinality of the quotient, before the finiteness statement below. -/
lemma specialValueGroup_natCard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    Nat.card (SpecialValueGroup M) = (specialValueOrder M).toNat := by
  have hcard := natCard_rowLattice_sub_one M (specialValueOrder_pos M hM)
  have hmain : Nat.card ((ℤ×ℤ) ⧸ specialValueLattice M) = Int.natAbs (M 0 0 + M 1 1 - 2) := by
    simpa [specialValueLattice] using hcard
  rw [show Nat.card (SpecialValueGroup M) = Nat.card ((ℤ×ℤ) ⧸ specialValueLattice M) from rfl]
  rw [hmain]
  apply Nat.cast_injective (R := ℤ)
  have ht : (0:ℤ) ≤ M 0 0 + M 1 1 - 2 := by
    have := specialValueOrder_pos M hM
    rw [specialValueOrder] at this
    omega
  rw [specialValueOrder]
  rw [Int.natAbs_of_nonneg ht, Int.toNat_of_nonneg ht]

/--
[RW26, p. 3]. Finiteness is stated
separately before Nat.card, which would be zero for an infinite type.
-/
theorem specialValueGroup_finite (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    Finite (SpecialValueGroup M) := by
  apply Nat.finite_of_card_ne_zero
  rw [specialValueGroup_natCard M hM]
  have := specialValueOrder_pos M hM
  omega

/--
[RW26, p. 3] |G|=N; determinant argument.
-/
theorem specialValueGroup_card (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    Nat.card (SpecialValueGroup M) = (specialValueOrder M).toNat :=
  specialValueGroup_natCard M hM

#check @QuotientAddGroup.quotientAddEquivOfEq
#check @L2r.rowLattice
#check @modularPhiSpecialArgument
#check @modularPhi_real_off_lattice
#print specialValueTau
#print specialValueLattice
#check specialValueArgument_mem_lattice_iff

end SICLean.L4
