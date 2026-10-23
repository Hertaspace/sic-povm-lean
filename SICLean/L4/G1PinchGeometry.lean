import SICLean.L4.G1RealInterface
import SICLean.L4.ModularClusterRegularity
import SICLean.L4.G1PinchGeometryAux

set_option autoImplicit false

/-!
# The exact pinch arithmetic and the existing G1 interfaces

The divisor families are those of [RW26, p. 6]. This file proves the all-component
equivalence. The exact interface types are in `G1RealInterface.lean`, in particular its existing
`g1NoPinch`, `g1NumeratorPoles`, `g1InversePoles`, `G1VerticalChain`, and `G1Separates`.

The converse uses the unique m modulo c with dm congruent to n and its K=J=0 numerator branch. It
does not assume that T is irrational or that different labels give distinct locations. `ratioData`
is only literal arithmetic data for the already defined ModularCluster kernel. No new special
function, no-pinch predicate, analytic input, or integral identity is introduced here.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G1Pinch

open G1PinchGeometryAux

/-- The existing cluster kernel data, with the exact G1 indices.

[RW26, p. 7]. -/
def ratioData (w y : ℂ) (n h ell p m : ℤ) : ModularCluster.KernelData where
  m := m
  n := n
  p := p
  ell := ell
  h := h
  w := w
  y := y
  ratio := true

/-- The cluster phase is the already specified E_m, including n in the h-term.

[RW26, p. 7]. -/
theorem phase_eq_g1Exponent (M : SL(2, ℤ)) (τ w y z : ℂ)
    (n h ell p m : ℤ) :
    ModularCluster.phase M (ratioData w y n h ell p m) z τ =
      g1Exponent M τ w z n h ell m := by
  rfl

/-- Pointwise bridge to the actual G1 ratio representative, even at a denominator Φ pole. It changes
neither Φ nor total division.

[RW26, p. 7]. -/
theorem g1RatioKernel_eq_kernel (M : SL(2, ℤ)) (τ w y : ℝ)
    (n h ell p m : ℤ) (z : ℂ) :
    g1RatioKernel M τ w y n h ell p m z =
      ModularCluster.kernel M (ratioData (w : ℂ) (y : ℂ) n h ell p m) z (τ : ℂ) := by
  simp only [g1RatioKernel, ModularCluster.kernel, ratioData, ite_true,
    div_eq_mul_inv, ModularCluster.phase, g1Exponent]

/-- The numerator set has the exact real affine coordinates, retaining admissible labels even when
locations merge.

[RW26, p. 6]. -/
theorem mem_numeratorPoles_iff (M : SL(2, ℤ)) (τ x : ℝ) (n m : ℤ) :
    x ∈ g1NumeratorPoles M τ n m ↔
      ∃ K J : ℕ,
        Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ)) (M 1 1 * m - n) ∧
        x = ((n : ℝ) - (m : ℝ) * g1T M τ +
          (K : ℝ) * g1T M τ + (J : ℝ)) / (M 1 0 : ℝ) := by
  simp only [g1NumeratorPoles, Set.mem_ofPred_eq, modularPhiPoleLabels,
    polePoint_succ_ofReal, Complex.ofReal_inj, add_sub_cancel_right]

/-- Inverse-denominator poles are actual zero branches translated by -y. A denominator Φ pole is not
a member merely because its specified Φ value is zero.

[RW26, p. 6]. -/
theorem mem_inversePoles_iff (M : SL(2, ℤ)) (τ y x : ℝ) (n p m : ℤ) :
    x ∈ g1InversePoles M τ y n p m ↔
      ∃ K J : ℕ,
        Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ))
          (n - 1 - M 1 1 * (m + p)) ∧
        x = ((n : ℝ) - 1 - ((m : ℝ) + (p : ℝ)) * g1T M τ -
          (K : ℝ) * g1T M τ - (J : ℝ)) / (M 1 0 : ℝ) - y := by
  simp only [g1InversePoles, Set.mem_ofPred_eq, modularPhiZeroLabels,
    zeroPoint_ofReal, ← Complex.ofReal_sub, Complex.ofReal_inj]
  push_cast
  rfl

/-- A collision gives the sum label appearing in the literal exclusion set. No injectivity of either
branch family is used.

[RW26, p. 6]. -/
theorem collision_sum_label (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (n p m : ℤ) (K J K' J' : ℕ)
    (hP : (K, J) ∈ modularPhiPoleLabels M (m + 1) n)
    (hZ : (K', J') ∈ modularPhiZeroLabels M (m + p) n)
    (heq : modularPhiPolePoint M (m + 1) n (τ : ℂ) K J =
      modularPhiZeroPoint M (m + p) n (τ : ℂ) K' J' - (y : ℂ)) :
    Int.ModEq (M 1 0)
        (((J : ℤ) + (J' : ℤ)) + M 1 1 * ((K : ℤ) + (K' : ℤ)))
        (-1 - M 1 1 * p) ∧
      y = -(((p : ℝ) + (K : ℝ) + (K' : ℝ)) * g1T M τ +
        1 + (J : ℝ) + (J' : ℝ)) / (M 1 0 : ℝ) := by
  change Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ))
    (M 1 1 * (m + 1 - 1) - n) at hP
  change Int.ModEq (M 1 0) ((J' : ℤ) + M 1 1 * (K' : ℤ))
    (n - 1 - M 1 1 * (m + p)) at hZ
  constructor
  · convert hP.add hZ using 1 <;> ring
  · rw [polePoint_succ_ofReal, zeroPoint_ofReal] at heq
    have heqR := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.ofReal_re] at heqR
    push_cast at heqR
    have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    apply (eq_div_iff hc).2
    field_simp [hc] at heqR
    linear_combination heqR

/-- Determinant one gives exactly one base component, not a c-fold multiplicity.

[RW26, p. 6]. -/
theorem exists_unique_baseIndex (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n : ℤ) :
    ∃! m : Fin (M 1 0).toNat, Int.ModEq (M 1 0) (M 1 1 * (m : ℤ)) n := by
  have hdet := det_coe_int M
  have hinv (x : ℤ) :
      Int.ModEq (M 1 0) (M 0 0 * (M 1 1 * x)) x := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-M 0 1 * x, ?_⟩
    linear_combination -x * hdet
  let r : ℤ := (M 0 0 * n) % M 1 0
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hM)
  have hrc : r < M 1 0 := Int.emod_lt_of_pos _ hM
  have hri : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
  let m : Fin (M 1 0).toNat := ⟨r.toNat, by omega⟩
  have hmi : (m : ℤ) = r := hri
  have hm : Int.ModEq (M 1 0) (M 1 1 * (m : ℤ)) n := by
    rw [hmi]
    apply ((Int.mod_modEq (M 0 0 * n) (M 1 0)).mul_left (M 1 1)).trans
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hinv n
  refine ⟨m, hm, ?_⟩
  intro m' hm'
  have hmod : Int.ModEq (M 1 0) (m' : ℤ) (m : ℤ) :=
    (hinv (m' : ℤ)).symm.trans
      (((hm'.trans hm.symm).mul_left (M 0 0)).trans (hinv (m : ℤ)))
  have hmi0 : 0 ≤ (m : ℤ) := Int.natCast_nonneg m.val
  have hmi'0 : 0 ≤ (m' : ℤ) := Int.natCast_nonneg m'.val
  have hmilt : (m : ℤ) < M 1 0 := by
    have h := m.isLt
    omega
  have hmi'lt : (m' : ℤ) < M 1 0 := by
    have h := m'.isLt
    omega
  have heq : (m' : ℤ) = (m : ℤ) := by
    simpa only [Int.ModEq, Int.emod_eq_of_lt hmi'0 hmi'lt,
      Int.emod_eq_of_lt hmi0 hmilt] using hmod
  apply Fin.ext
  exact_mod_cast heq

/-- Every excluded value creates a collision in the base component, with the numerator label (0,0).
Valid also at rational T.

[RW26, p. 6]. -/
theorem excluded_label_collision (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (n p : ℤ) (m : Fin (M 1 0).toNat)
    (hm : Int.ModEq (M 1 0) (M 1 1 * (m : ℤ)) n) (K J : ℕ)
    (hlabel : Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ))
      (-1 - M 1 1 * p))
    (hy : y = -(((p : ℝ) + (K : ℝ)) * g1T M τ + 1 + (J : ℝ)) /
      (M 1 0 : ℝ)) :
    ∃ x : ℝ,
      x = ((n : ℝ) - ((m : ℤ) : ℝ) * g1T M τ) / (M 1 0 : ℝ) ∧
      x ∈ g1NumeratorPoles M τ n (m : ℤ) ∧
      x ∈ g1InversePoles M τ y n p (m : ℤ) := by
  refine ⟨((n : ℝ) - ((m : ℤ) : ℝ) * g1T M τ) / (M 1 0 : ℝ), rfl, ?_, ?_⟩
  · rw [mem_numeratorPoles_iff]
    refine ⟨0, 0, ?_, ?_⟩
    · convert (hm.sub (Int.ModEq.refl n)).symm using 1 <;> simp only [Nat.cast_zero,
        mul_zero, zero_add, sub_self]
    · simp
  · rw [mem_inversePoles_iff]
    refine ⟨K, J, ?_, ?_⟩
    · convert hlabel.add (hm.sub (Int.ModEq.refl (M 1 1 * (m : ℤ)))) using 1 <;> ring
    · rw [hy]
      push_cast
      ring

/-- Exact all-m iff required. Neither a fixed-point condition nor an irrationality assumption
occurs.

[RW26, p. 6]. -/
theorem noPinch_iff_all_disjoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (n p : ℤ) :
    g1NoPinch M τ y p ↔
      ∀ m : Fin (M 1 0).toNat,
        Disjoint (g1NumeratorPoles M τ n (m : ℤ))
          (g1InversePoles M τ y n p (m : ℤ)) := by
  constructor
  · intro hnp m
    rw [Set.disjoint_left]
    rintro x ⟨K, J, hP, hxP⟩ ⟨K', J', hZ, hxZ⟩
    have hc := collision_sum_label M hM τ y n p (m : ℤ) K J K' J' hP hZ
      (hxP.symm.trans hxZ)
    apply hnp (K + K') (J + J')
    · simpa only [Nat.cast_add] using hc.1
    · simpa only [Nat.cast_add, add_assoc] using hc.2
  · intro hd K J hlabel hy
    obtain ⟨m, hm, _⟩ := exists_unique_baseIndex M hM n
    obtain ⟨x, _, hxP, hxZ⟩ :=
      excluded_label_collision M hM τ y n p m hm K J hlabel hy
    exact Set.disjoint_left.mp (hd m) hxP hxZ

/-- The exclusion also separates every integer-indexed component. The finite-index version above is
the actual G1 interface type.

[RW26, p. 6]. -/
theorem noPinch_iff_all_int_disjoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (n p : ℤ) :
    g1NoPinch M τ y p ↔
      ∀ m : ℤ, Disjoint (g1NumeratorPoles M τ n m) (g1InversePoles M τ y n p m) := by
  constructor
  · intro hnp m
    rw [Set.disjoint_left]
    rintro x ⟨K, J, hP, hxP⟩ ⟨K', J', hZ, hxZ⟩
    have hc := collision_sum_label M hM τ y n p m K J K' J' hP hZ
      (hxP.symm.trans hxZ)
    apply hnp (K + K') (J + J')
    · simpa only [Nat.cast_add] using hc.1
    · simpa only [Nat.cast_add, add_assoc] using hc.2
  · intro hd
    exact (noPinch_iff_all_disjoint M hM τ y n p).2 (fun m => hd (m : ℤ))

/-- Per-component bridge to existing labeled cross-class predicate. Same-class collisions are
permitted on both sides.

[RW26, p. 6]. -/
theorem crossSeparated_iff_disjoint (M : SL(2, ℤ)) (τ y : ℝ) (w : ℂ)
    (n h ell p m : ℤ) :
    ModularCluster.crossSeparated M (ratioData w (y : ℂ) n h ell p m) (τ : ℂ) ↔
      Disjoint (g1NumeratorPoles M τ n m) (g1InversePoles M τ y n p m) := by
  rw [disjoint_iff_no_collision]
  constructor
  · intro hs K J K' J' hP hZ heq
    have hclasses := hs (true, K, J)
      (by simpa [ModularCluster.labels, ratioData] using hP) (false, K', J')
      (by simpa [ModularCluster.labels, ratioData] using hZ)
      (by simpa [ModularCluster.branchPoint, ratioData] using heq)
    cases hclasses
  · intro hn b hb b' hb' heq
    rcases b with ⟨bt, K, J⟩
    rcases b' with ⟨bt', K', J'⟩
    cases bt <;> cases bt'
    · rfl
    · exfalso
      apply hn K' J' K J
      · simpa [ModularCluster.labels, ratioData] using hb'
      · simpa [ModularCluster.labels, ratioData] using hb
      · simpa [ModularCluster.branchPoint, ratioData] using heq.symm
    · exfalso
      apply hn K J K' J'
      · simpa [ModularCluster.labels, ratioData] using hb
      · simpa [ModularCluster.labels, ratioData] using hb'
      · simpa [ModularCluster.branchPoint, ratioData] using heq
    · rfl

/-- The exact arithmetic condition supplies the hypotheses already used, simultaneously in all G1
components.

[RW26, p. 6]. -/
theorem noPinch_iff_all_crossSeparated (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (w : ℂ) (n h ell p : ℤ) :
    g1NoPinch M τ y p ↔
      ∀ m : Fin (M 1 0).toNat,
        ModularCluster.crossSeparated M
          (ratioData w (y : ℂ) n h ell p (m : ℤ)) (τ : ℂ) := by
  rw [noPinch_iff_all_disjoint M hM τ y n p]
  exact forall_congr' fun m =>
    (crossSeparated_iff_disjoint M τ y w n h ell p (m : ℤ)).symm

/-- Pure geometry: the existing zero/one assignment cannot separate a common point. No integrability
is an input.

[RW26, p. 7, p. 13]. -/
theorem separates_disjoint (D : G1VerticalChain) (P Z : Set ℝ)
    (hD : G1Separates D P Z) : Disjoint P Z := by
  rw [Set.disjoint_left]
  intro x hxP hxZ
  have hzero := hD.2.2.1 x hxP
  have hone := hD.2.2.2 x hxZ
  omega

#check @ratioData
#check @noPinch_iff_all_disjoint
#check @crossSeparated_iff_disjoint
#check @noPinch_iff_all_crossSeparated
#print ratioData

end SICLean.L4.G1Pinch
