import SICLean.L4.G1PinchGeometry
import SICLean.L4.G1FixedSeparationAux

set_option autoImplicit false

/-!
# Concrete fixed separating chains and their upper neighborhoods

The divisor sets are those of [RW26, p. 6]. This
file gives the parameter-dependent construction.

The chain type is exactly the existing `G1VerticalChain`. `ExplicitChain` is only a specification of
its baseline, centers, radii and disjoint disks. `SeparatesAt` extends the existing `G1Separates` to
nonreal branch locations; its real specialization is an iff below. There is no second no-pinch
predicate, no analytic/convergence field and no assumed integral equality.

Every label in a rational multiple cluster satisfies `TracksClusters`. Circles for different m need
not be disjoint. One parameter radius is chosen before the finite component and the varying complex
parameter. The auxiliary stability argument works on a full closed parameter ball. The public
declarations retain their fixed upper-neighborhood statements.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G1FixedSeparation

/-- v_m(T₀).

[RW26, p. 6]. -/
def numeratorBase (M : SL(2, ℤ)) (τ : ℝ) (n m : ℤ) : ℝ :=
  ((n : ℝ) - (m : ℝ) * g1T M τ) / (M 1 0 : ℝ)

/-- u_m(T₀)-y.

[RW26, p. 6]. -/
def inverseBase (M : SL(2, ℤ)) (τ y : ℝ) (n p m : ℤ) : ℝ :=
  ((n : ℝ) - 1 - ((m : ℝ) + (p : ℝ)) * g1T M τ) / (M 1 0 : ℝ) - y

/-- Literal geometric construction. The centers are distinct locations; labels are never removed
from either actual divisor family. No `G1Separates`, regularity, bound or integral assertion is a
field.

[RW26, p. 6, p. 7, p. 13]. -/
def ExplicitChain (M : SL(2, ℤ)) (τ y : ℝ) (n p m : ℤ)
    (D : G1VerticalChain) : Prop :=
  D.crossing < numeratorBase M τ n m ∧
  D.crossing ∉ g1InversePoles M τ y n p m ∧
  (D.centers : Set ℝ) = g1InversePoles M τ y n p m ∩ Ioi D.crossing ∧
  (∀ r ∈ D.centers,
    0 < D.radius r ∧ D.radius r < r - D.crossing ∧
      (∀ x ∈ g1NumeratorPoles M τ n m, D.radius r < |x - r|) ∧
      (∀ x ∈ g1InversePoles M τ y n p m, x ≠ r → D.radius r < |x - r|)) ∧
  (∀ r ∈ D.centers, ∀ r' ∈ D.centers, r ≠ r' →
    Disjoint (Metric.closedBall (r : ℂ) (D.radius r))
      (Metric.closedBall (r' : ℂ) (D.radius r')))

/-- The same finite CCW-circle count as `g1CircleWinding`, now evaluated at a complex branch
location.

[RW26, p. 7, p. 13]. -/
def circleWindingAt (D : G1VerticalChain) (z : ℂ) : ℤ :=
  ∑ r ∈ D.centers, if dist z (r : ℂ) < D.radius r then 1 else 0

/-- Direct extension of the existing baseline-plus-circle assignment.

[RW26, p. 7, p. 13]. -/
def leftAssignmentAt (D : G1VerticalChain) (z : ℂ) : ℤ :=
  (if z.re < D.crossing then 1 else 0) + circleWindingAt D z

/-- The existing G1 separation geometry at the actual complex divisor branches. At real τ,y this is
equivalent to `G1Separates`, not a stronger analytic notion.

[RW26, p. 6, p. 7, p. 13]. -/
def SeparatesAt (D : G1VerticalChain) (M : SL(2, ℤ)) (τ y : ℂ)
    (n p m : ℤ) : Prop :=
  let P : Set ℂ := (fun q : ℕ × ℕ => modularPhiPolePoint M (m + 1) n τ q.1 q.2) ''
    modularPhiPoleLabels M (m + 1) n
  let Z : Set ℂ := (fun q : ℕ × ℕ => modularPhiZeroPoint M (m + p) n τ q.1 q.2 - y) ''
    modularPhiZeroLabels M (m + p) n
  (∀ r ∈ D.centers, 0 < D.radius r) ∧
  (∀ z ∈ P ∪ Z, z.re ≠ D.crossing ∧
    ∀ r ∈ D.centers, dist z (r : ℂ) ≠ D.radius r) ∧
  (∀ z ∈ P, leftAssignmentAt D z = 0) ∧
  (∀ z ∈ Z, leftAssignmentAt D z = 1)

/-- Every inverse-denominator label stays in precisely its original selected cluster disk. This
includes all coalescing labels at rational T₀. No individual residue or simple-pole assumption
occurs.

[RW26, p. 6, p. 7, p. 13]. -/
def TracksClusters (D : G1VerticalChain) (M : SL(2, ℤ)) (τ₀ y : ℝ)
    (τ : ℂ) (n p m : ℤ) : Prop :=
  ∀ r ∈ D.centers, ∀ K J : ℕ,
    (K, J) ∈ modularPhiZeroLabels M (m + p) n →
      (dist (modularPhiZeroPoint M (m + p) n τ K J - (y : ℂ)) (r : ℂ) < D.radius r ↔
        modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ) = (r : ℂ))

/-- A closed upper half-disk, including its real center.

[RW26, p. 7, p. 13]. -/
def upperParameterBall (τ₀ ρ : ℝ) : Set ℂ :=
  Metric.closedBall (τ₀ : ℂ) ρ ∩ {τ : ℂ | 0 ≤ τ.im}

/-- Every numerator pole lies weakly to the right of v_m(T₀), including merged rational-parameter
poles.

[RW26, p. 6, p. 7, p. 13]. -/
theorem numerator_ge_base (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℝ) (hT : 0 < g1T M τ) (n m : ℤ) :
    ∀ x ∈ g1NumeratorPoles M τ n m, numeratorBase M τ n m ≤ x := by
  intro x hx
  obtain ⟨K, J, -, rfl⟩ := (G1Pinch.mem_numeratorPoles_iff M τ x n m).mp hx
  have hc : (0 : ℝ) < M 1 0 := by exact_mod_cast hM
  unfold numeratorBase
  apply (div_le_div_iff_of_pos_right hc).mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg K) hT.le, (Nat.cast_nonneg J : (0 : ℝ) ≤ J)]

/-- Every inverse-denominator pole is at most u_m(T₀)-y.

[RW26, p. 6, p. 7, p. 13]. -/
theorem inverse_le_base (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (hT : 0 < g1T M τ) (n p m : ℤ) :
    ∀ x ∈ g1InversePoles M τ y n p m, x ≤ inverseBase M τ y n p m := by
  intro x hx
  obtain ⟨K, J, -, rfl⟩ := (G1Pinch.mem_inversePoles_iff M τ y x n p m).mp hx
  have hc : (0 : ℝ) < M 1 0 := by exact_mod_cast hM
  unfold inverseBase
  apply sub_le_sub_right
  apply (div_le_div_iff_of_pos_right hc).mpr
  have hK : 0 ≤ (K : ℝ) * g1T M τ := mul_nonneg (Nat.cast_nonneg K) hT.le
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  linarith

/-- Only finitely many distinct inverse poles need CCW corrections. The finiteness comes from
labeled local finiteness plus the one-sided bound; rational multiplicities are allowed.

[RW26, p. 6, p. 7, p. 13]. -/
theorem inverse_right_finite (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y x : ℝ) (hT : 0 < g1T M τ) (n p m : ℤ) :
    (g1InversePoles M τ y n p m ∩ Ioi x).Finite := by
  let k := G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m
  let R := |x| + |inverseBase M τ y n p m|
  have hR : 0 ≤ R := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hfin := ModularCluster.boundedCenters_finite M hM k (τ : ℂ)
    (real_mem_modularPhiDomain M τ hT) R hR
  have himage : ((fun r : ℝ => (r : ℂ)) ''
      (g1InversePoles M τ y n p m ∩ Ioi x)).Finite := by
    apply hfin.subset
    rintro z ⟨r, ⟨hr, hxr⟩, rfl⟩
    change x < r at hxr
    have hupper := inverse_le_base M hM τ y hT n p m r hr
    have hbound : |r| ≤ R := by
      apply abs_le.mpr
      constructor
      · have := neg_abs_le x
        dsimp [R]
        linarith [abs_nonneg (inverseBase M τ y n p m)]
      · have := le_abs_self (inverseBase M τ y n p m)
        dsimp [R]
        linarith [abs_nonneg x]
    obtain ⟨K, J, hlabel, heq⟩ := hr
    refine ⟨by simpa using hbound, (false, K, J), ?_, ?_⟩
    · simp [k, ModularCluster.labels, G1Pinch.ratioData, hlabel]
    · simpa [k, ModularCluster.branchPoint, G1Pinch.ratioData] using heq.symm
  exact himage.of_finite_image Complex.ofReal_injective.injOn

/-- A baseline can be chosen strictly left of the numerator family and off the inverse family. No
no-pinch hypothesis is needed just to select the baseline.

[RW26, p. 6, p. 7, p. 13]. -/
theorem exists_crossing (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (hT : 0 < g1T M τ) (n p m : ℤ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      numeratorBase M τ n m - δ ∉ g1InversePoles M τ y n p m := by
  let v := numeratorBase M τ n m
  have hfin := inverse_right_finite M hM τ y (v - 1) hT n p m
  obtain ⟨x, hx, hnot⟩ :=
    (Set.Ioo_infinite (show v - 1 < v by linarith)).exists_notMem_finite hfin
  refine ⟨v - x, by linarith [hx.2], by linarith [hx.1], ?_⟩
  have heq : numeratorBase M τ n m - (v - x) = x := by dsimp [v]; ring
  rw [heq]
  intro hxZ
  exact hnot ⟨hxZ, hx.1⟩

/-- Actual geometric construction of a baseline and disjoint fixed disks. No proof of separation is
hidden in a data constructor.

[RW26, p. 6, p. 7, p. 13]. -/
theorem exists_explicitChain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (hT : 0 < g1T M τ) (n p m : ℤ)
    (hpinch : g1NoPinch M τ y p) :
    ∃ D : G1VerticalChain, ExplicitChain M τ y n p m D := by
  obtain ⟨δ, hδ, -, havoid⟩ := exists_crossing M hM τ y hT n p m
  let x := numeratorBase M τ n m - δ
  let S := g1InversePoles M τ y n p m ∩ Ioi x
  have hS : S.Finite := inverse_right_finite M hM τ y x hT n p m
  let k := G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m
  let R := |x| + |inverseBase M τ y n p m|
  have hR : 0 ≤ R := add_nonneg (abs_nonneg _) (abs_nonneg _)
  obtain ⟨ρ, C, hρ, -, hC, hpos, hdisj, hiso, -⟩ :=
    ModularCluster.exists_fixed_circles M hM k (τ : ℂ)
      (real_mem_modularPhiDomain M τ hT) R hR
  have hself : (τ : ℂ) ∈ Metric.closedBall (τ : ℂ) ρ :=
    Metric.mem_closedBall_self hρ.le
  have hCR (r : ℝ) (hr : r ∈ S) : (r : ℂ) ∈ C.centers := by
    change (r : ℂ) ∈ (C.centers : Set ℂ)
    rw [hC]
    have hrbound := inverse_le_base M hM τ y hT n p m r hr.1
    have hx : x < r := hr.2
    have hnorm : |r| ≤ R := by
      apply abs_le.mpr
      constructor
      · dsimp [R]
        linarith [neg_abs_le x, abs_nonneg (inverseBase M τ y n p m)]
      · dsimp [R]
        linarith [le_abs_self (inverseBase M τ y n p m), abs_nonneg x]
    obtain ⟨K, J, hlabel, heq⟩ := hr.1
    refine ⟨by simpa using hnorm, (false, K, J), ?_, ?_⟩
    · simp [k, ModularCluster.labels, G1Pinch.ratioData, hlabel]
    · simpa [k, ModularCluster.branchPoint, G1Pinch.ratioData] using heq.symm
  let rad : ℝ → ℝ := fun r => min (C.radius (r : ℂ) / 2) ((r - x) / 2)
  have hradpos (r : ℝ) (hr : r ∈ S) : 0 < rad r :=
    lt_min (half_pos (hpos _ (hCR r hr)).1) (half_pos (sub_pos.mpr hr.2))
  have hradC (r : ℝ) (hr : r ∈ S) : rad r < C.radius (r : ℂ) := by
    have hp := (hpos _ (hCR r hr)).1
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hradx (r : ℝ) (hr : r ∈ S) : rad r < r - x := by
    have hx : x < r := hr.2
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsep := (G1Pinch.noPinch_iff_all_int_disjoint M hM τ y n p).mp hpinch m
  refine ⟨⟨x, hS.toFinset, rad⟩, ?_, havoid, ?_, ?_, ?_⟩
  · dsimp [x]
    linarith
  · exact hS.coe_toFinset
  · intro r hr
    change r ∈ hS.toFinset at hr
    have hrS : r ∈ S := hS.mem_toFinset.mp hr
    refine ⟨hradpos r hrS, hradx r hrS, ?_, ?_⟩
    · intro a ha
      have hne : a ≠ r := by
        intro heq
        exact Set.disjoint_left.mp hsep ha (heq ▸ hrS.1)
      obtain ⟨K, J, hlabel, heq⟩ := ha
      have hb : (true, K, J) ∈ ModularCluster.labels M k := by
        simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hlabel
      have hp : ModularCluster.branchPoint M k (τ : ℂ) (true, K, J) = (a : ℂ) := by
        simpa [k, ModularCluster.branchPoint, G1Pinch.ratioData] using heq.symm
      have hneC : ModularCluster.branchPoint M k (τ : ℂ) (true, K, J) ≠ (r : ℂ) := by
        simpa [hp] using (Complex.ofReal_injective.ne hne)
      have hbnd := (hiso _ (hCR r hrS) _ hb _ hself).2 hneC
      have hd : C.radius (r : ℂ) < |a - r| := by
        simpa [hp, Complex.dist_eq, ← Complex.ofReal_sub] using hbnd
      exact (hradC r hrS).trans hd
    · intro a ha hne
      obtain ⟨K, J, hlabel, heq⟩ := ha
      have hb : (false, K, J) ∈ ModularCluster.labels M k := by
        simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hlabel
      have hp : ModularCluster.branchPoint M k (τ : ℂ) (false, K, J) = (a : ℂ) := by
        simpa [k, ModularCluster.branchPoint, G1Pinch.ratioData] using heq.symm
      have hneC : ModularCluster.branchPoint M k (τ : ℂ) (false, K, J) ≠ (r : ℂ) := by
        simpa [hp] using (Complex.ofReal_injective.ne hne)
      have hbnd := (hiso _ (hCR r hrS) _ hb _ hself).2 hneC
      have hd : C.radius (r : ℂ) < |a - r| := by
        simpa [hp, Complex.dist_eq, ← Complex.ofReal_sub] using hbnd
      exact (hradC r hrS).trans hd
  · intro r hr r' hr' hne
    have hrS : r ∈ S := hS.mem_toFinset.mp hr
    have hrS' : r' ∈ S := hS.mem_toFinset.mp hr'
    exact (hdisj _ (hCR r hrS) _ (hCR r' hrS') (Complex.ofReal_injective.ne hne)).mono
      (Metric.closedBall_subset_closedBall (hradC r hrS).le)
      (Metric.closedBall_subset_closedBall (hradC r' hrS').le)

/-- The construction satisfies the already fixed interface predicate. Its circles are positive CCW
corrections, including whole multiple poles.

[RW26, p. 7, p. 13]. -/
theorem explicitChain_separates (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (hT : 0 < g1T M τ) (n p m : ℤ) (D : G1VerticalChain)
    (hD : ExplicitChain M τ y n p m D) :
    G1Separates D (g1NumeratorPoles M τ n m) (g1InversePoles M τ y n p m) := by
  obtain ⟨hcross, havoid, hcenters, hradius, -⟩ := hD
  have hcenter (r : ℝ) (hr : r ∈ D.centers) :
      r ∈ g1InversePoles M τ y n p m ∧ D.crossing < r := by
    have : r ∈ (D.centers : Set ℝ) := hr
    rwa [hcenters] at this
  have hnum (x : ℝ) (hx : x ∈ g1NumeratorPoles M τ n m) : D.crossing < x :=
    hcross.trans_le (numerator_ge_base M hM τ hT n m x hx)
  have hinv (x : ℝ) (hx : x ∈ g1InversePoles M τ y n p m) : x ≠ D.crossing := by
    rintro rfl
    exact havoid hx
  have hzero (x : ℝ)
      (hx : ∀ r ∈ D.centers, D.radius r < |x - r|) : g1CircleWinding D x = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    exact if_neg (not_lt.mpr (hx r hr).le)
  refine ⟨fun r hr => (hradius r hr).1, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · refine ⟨(hnum x hx).ne', fun r hr => ((hradius r hr).2.2.1 x hx).ne'⟩
    · refine ⟨hinv x hx, ?_⟩
      intro r hr
      by_cases heq : x = r
      · subst x
        simpa using (hradius r hr).1.ne
      · exact ((hradius r hr).2.2.2 x hx heq).ne'
  · intro x hx
    rw [g1LeftAssignment, if_neg (not_lt.mpr (hnum x hx).le),
      hzero x (fun r hr => (hradius r hr).2.2.1 x hx)]
    simp
  · intro x hx
    rcases lt_or_gt_of_ne (hinv x hx) with hleft | hright
    · rw [g1LeftAssignment, if_pos hleft, hzero x]
      · simp
      · intro r hr
        exact (hradius r hr).2.2.2 x hx (ne_of_lt (hleft.trans (hcenter r hr).2))
    · have hxc : x ∈ D.centers := by
        change x ∈ (D.centers : Set ℝ)
        rw [hcenters]
        exact ⟨hx, hright⟩
      have hw : g1CircleWinding D x = 1 := by
        unfold g1CircleWinding
        rw [Finset.sum_eq_single x]
        · simp [(hradius x hxc).1]
        · intro r hr hne
          exact if_neg (not_lt.mpr ((hradius r hr).2.2.2 x hx hne.symm).le)
        · exact fun h => (h hxc).elim
      simp [g1LeftAssignment, not_lt.mpr hright.le, hw]

/-- Exact restriction to the existing real assignment, without adding any geometric or analytic
hypotheses.

[RW26, p. 7, p. 13]. -/
theorem assignmentsAt_ofReal (D : G1VerticalChain) (x : ℝ) :
    circleWindingAt D (x : ℂ) = g1CircleWinding D x ∧
      leftAssignmentAt D (x : ℂ) = g1LeftAssignment D x := by
  have hcircle : circleWindingAt D (x : ℂ) = g1CircleWinding D x := by
    simp [circleWindingAt, g1CircleWinding, Complex.dist_eq, ← Complex.ofReal_sub]
  exact ⟨hcircle, by simp [leftAssignmentAt, g1LeftAssignment, hcircle]⟩

/-- Thus the complex-parameter geometry is a literal extension of the existing `G1Separates`
contract.

[RW26, p. 7, p. 13]. -/
theorem separatesAt_ofReal_iff (D : G1VerticalChain) (M : SL(2, ℤ))
    (τ y : ℝ) (n p m : ℤ) :
    SeparatesAt D M (τ : ℂ) (y : ℂ) n p m ↔
      G1Separates D (g1NumeratorPoles M τ n m) (g1InversePoles M τ y n p m) := by
  have hpReal (K J : ℕ) :
      ((modularPhiPolePoint M (m + 1) n (τ : ℂ) K J).re : ℂ) =
        modularPhiPolePoint M (m + 1) n (τ : ℂ) K J := by
    apply Complex.ext <;> simp [modularPhiPolePoint, etaDenom]
  have hzReal (K J : ℕ) :
      ((modularPhiZeroPoint M (m + p) n (τ : ℂ) K J - (y : ℂ)).re : ℂ) =
        modularPhiZeroPoint M (m + p) n (τ : ℂ) K J - (y : ℂ) := by
    apply Complex.ext <;> simp [modularPhiZeroPoint, etaDenom]
  have hP : (fun q : ℕ × ℕ => modularPhiPolePoint M (m + 1) n (τ : ℂ) q.1 q.2) ''
      modularPhiPoleLabels M (m + 1) n =
        Complex.ofReal '' g1NumeratorPoles M τ n m := by
    ext z
    constructor
    · rintro ⟨⟨K, J⟩, hlabel, rfl⟩
      exact ⟨_, ⟨K, J, hlabel, hpReal K J⟩, hpReal K J⟩
    · rintro ⟨x, ⟨K, J, hlabel, hx⟩, rfl⟩
      exact ⟨(K, J), hlabel, hx.symm⟩
  have hZ : (fun q : ℕ × ℕ => modularPhiZeroPoint M (m + p) n (τ : ℂ) q.1 q.2 -
      (y : ℂ)) '' modularPhiZeroLabels M (m + p) n =
        Complex.ofReal '' g1InversePoles M τ y n p m := by
    ext z
    constructor
    · rintro ⟨⟨K, J⟩, hlabel, rfl⟩
      exact ⟨_, ⟨K, J, hlabel, hzReal K J⟩, hzReal K J⟩
    · rintro ⟨x, ⟨K, J, hlabel, hx⟩, rfl⟩
      exact ⟨(K, J), hlabel, hx.symm⟩
  simp only [SeparatesAt, hP, hZ, G1Separates, ← Set.image_union,
    Set.forall_mem_image, Complex.ofReal_re, (assignmentsAt_ofReal _ _).2,
    Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- One fixed chain works throughout a closed upper parameter half-disk. The per-label iff keeps
every branch in a merged cluster inside the same disk. This is geometry, independent of the strict
integral windows and of all tail estimates.

[RW26, p. 6, p. 7, p. 13]. -/
theorem explicitChain_stable_upper (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (hT : 0 < g1T M τ₀) (n p m : ℤ) (D : G1VerticalChain)
    (hD : ExplicitChain M τ₀ y n p m D) :
    ∃ ρ : ℝ, 0 < ρ ∧ upperParameterBall τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ τ ∈ upperParameterBall τ₀ ρ,
        g1T M τ₀ / 2 < (etaDenom M τ).re ∧
          SeparatesAt D M τ (y : ℂ) n p m ∧ TracksClusters D M τ₀ y τ n p m := by
  let k := G1Pinch.ratioData 0 (y : ℂ) n 0 0 p m
  have hy : k.y.im = 0 := rfl
  have hsep₀ := (separatesAt_ofReal_iff D M τ₀ y n p m).mpr
    (explicitChain_separates M hM τ₀ y hT n p m D hD)
  have hmem (σ : ℂ) (b : ModularCluster.Label) (hb : b ∈ ModularCluster.labels M k) :
      ModularCluster.branchPoint M k σ b ∈
        ((fun q : ℕ × ℕ => modularPhiPolePoint M (m + 1) n σ q.1 q.2) ''
          modularPhiPoleLabels M (m + 1) n) ∪
        ((fun q : ℕ × ℕ => modularPhiZeroPoint M (m + p) n σ q.1 q.2 - (y : ℂ)) ''
          modularPhiZeroLabels M (m + p) n) := by
    rcases b with ⟨b, K, J⟩
    cases b
    · right
      refine ⟨(K, J), ?_, rfl⟩
      simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hb
    · left
      refine ⟨(K, J), ?_, rfl⟩
      simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hb
  obtain ⟨ρ, hρ, hdom, hstable⟩ :=
    G1FixedSeparationAux.exists_stable_geometry M hM k hy τ₀ hT D
      (fun b hb => hsep₀.2.1 _ (hmem (τ₀ : ℂ) b hb))
  refine ⟨ρ, hρ, fun τ hτ => hdom hτ.1, ?_⟩
  intro τ hτ
  obtain ⟨hden, hgeom⟩ := hstable τ hτ.1
  have hassign (b : ModularCluster.Label) (hb : b ∈ ModularCluster.labels M k) :
      leftAssignmentAt D (ModularCluster.branchPoint M k τ b) =
        leftAssignmentAt D (ModularCluster.branchPoint M k (τ₀ : ℂ) b) := by
    simp only [leftAssignmentAt, circleWindingAt, (hgeom b hb).2.1]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    simp only [((hgeom b hb).2.2 r hr).2]
  refine ⟨hden, ⟨hsep₀.1, ?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · obtain ⟨⟨K, J⟩, hlabel, rfl⟩ := hz
      have hb : (true, K, J) ∈ ModularCluster.labels M k := by
        simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hlabel
      exact ⟨(hgeom _ hb).1, fun r hr => ((hgeom _ hb).2.2 r hr).1⟩
    · obtain ⟨⟨K, J⟩, hlabel, rfl⟩ := hz
      have hb : (false, K, J) ∈ ModularCluster.labels M k := by
        simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hlabel
      exact ⟨(hgeom _ hb).1, fun r hr => ((hgeom _ hb).2.2 r hr).1⟩
  · rintro z ⟨⟨K, J⟩, hlabel, rfl⟩
    have hb : (true, K, J) ∈ ModularCluster.labels M k := by
      simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hlabel
    exact (hassign _ hb).trans (hsep₀.2.2.1 _ ⟨(K, J), hlabel, rfl⟩)
  · rintro z ⟨⟨K, J⟩, hlabel, rfl⟩
    have hb : (false, K, J) ∈ ModularCluster.labels M k := by
      simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hlabel
    exact (hassign _ hb).trans (hsep₀.2.2.2 _ ⟨(K, J), hlabel, rfl⟩)
  · intro r hr K J hlabel
    have hb : (false, K, J) ∈ ModularCluster.labels M k := by
      simpa [k, ModularCluster.labels, G1Pinch.ratioData] using hlabel
    have hcircle := ((hgeom _ hb).2.2 r hr).2
    change (dist (modularPhiZeroPoint M (m + p) n τ K J - (y : ℂ)) (r : ℂ) < D.radius r ↔
      dist (modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ)) (r : ℂ) < D.radius r)
      at hcircle
    apply hcircle.trans
    let z₀ := modularPhiZeroPoint M (m + p) n (τ₀ : ℂ) K J - (y : ℂ)
    have hz₀ : (z₀.re : ℂ) = z₀ := by
      simpa [k, ModularCluster.branchPoint, G1Pinch.ratioData, z₀] using
        (G1FixedSeparationAux.branchPoint_ofReal M k hy τ₀ (false, K, J)).symm
    have hzZ : z₀.re ∈ g1InversePoles M τ₀ y n p m := ⟨K, J, hlabel, hz₀⟩
    change dist z₀ (r : ℂ) < D.radius r ↔ z₀ = (r : ℂ)
    constructor
    · intro hinside
      by_contra hne
      have hneR : z₀.re ≠ r := by
        intro heq
        exact hne (hz₀.symm.trans (congrArg Complex.ofReal heq))
      have hrad := (hD.2.2.2.1 r hr).2.2.2 z₀.re hzZ hneR
      have hdist : dist z₀ (r : ℂ) = |z₀.re - r| := by
        rw [← hz₀]
        simp [Complex.dist_eq, ← Complex.ofReal_sub]
      rw [hdist] at hinside
      exact (not_lt_of_ge hrad.le) hinside
    · intro heq
      simpa [heq] using (hD.2.2.2.1 r hr).1

/-- The exact existence part of G1RealConclusion, strengthened by a common upper parameter radius
and fixed, saturated circles for every m: Fin c. The radius precedes m and τ. No s>0 or L<0 is
needed for geometric existence.

[RW26, p. 6, p. 7, p. 13]. -/
theorem exists_fixedSeparatingFamily (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ y : ℝ) (hT : 0 < g1T M τ₀) (n p : ℤ)
    (hpinch : g1NoPinch M τ₀ y p) :
    ∃ (ρ : ℝ) (D : Fin (M 1 0).toNat → G1VerticalChain),
      0 < ρ ∧ upperParameterBall τ₀ ρ ⊆ modularPhiDomain M ∧
        (∀ τ ∈ upperParameterBall τ₀ ρ, g1T M τ₀ / 2 < (etaDenom M τ).re) ∧
        ∀ m : Fin (M 1 0).toNat,
          ExplicitChain M τ₀ y n p (m : ℤ) (D m) ∧
          G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
            (g1InversePoles M τ₀ y n p (m : ℤ)) ∧
          ∀ τ ∈ upperParameterBall τ₀ ρ,
            SeparatesAt (D m) M τ (y : ℂ) n p (m : ℤ) ∧
              TracksClusters (D m) M τ₀ y τ n p (m : ℤ) := by
  have hc : 0 < (M 1 0).toNat := by omega
  have : Nonempty (Fin (M 1 0).toNat) := ⟨⟨0, hc⟩⟩
  choose D hD using fun m : Fin (M 1 0).toNat =>
    exists_explicitChain M hM τ₀ y hT n p (m : ℤ) hpinch
  choose ρ hρ hdom hstable using fun m : Fin (M 1 0).toNat =>
    explicitChain_stable_upper M hM τ₀ y hT n p (m : ℤ) (D m) (hD m)
  let r := Finset.univ.inf' Finset.univ_nonempty ρ
  have hr : 0 < r := by
    exact (Finset.lt_inf'_iff _).mpr (by simpa using hρ)
  have hrle (m : Fin (M 1 0).toNat) : r ≤ ρ m :=
    Finset.inf'_le _ (Finset.mem_univ m)
  have hsub (m : Fin (M 1 0).toNat) :
      upperParameterBall τ₀ r ⊆ upperParameterBall τ₀ (ρ m) := by
    intro τ hτ
    exact ⟨le_trans hτ.1 (hrle m), hτ.2⟩
  let m₀ : Fin (M 1 0).toNat := ⟨0, hc⟩
  refine ⟨r, D, hr, fun τ hτ => hdom m₀ (hsub m₀ hτ), ?_, ?_⟩
  · intro τ hτ
    exact (hstable m₀ τ (hsub m₀ hτ)).1
  · intro m
    exact ⟨hD m, explicitChain_separates M hM τ₀ y hT n p (m : ℤ) (D m) (hD m),
      fun τ hτ => (hstable m τ (hsub m hτ)).2⟩

/-- Bridge from the explicit divisor geometry to actual joint regular domain on the same baseline
and circles. Denominator Φ poles are permitted because their reciprocals have analytic zero values.

[RW26, p. 6, p. 7, p. 13]. -/
theorem separatesAt_regularDomain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n h ell p m : ℤ) (D : G1VerticalChain)
    (hτ : τ ∈ modularPhiDomain M) (hD : SeparatesAt D M τ y n p m) :
    (∀ t : ℝ,
      (g1VerticalPoint D.crossing t, τ) ∈
        ModularCluster.regularDomain M (G1Pinch.ratioData w y n h ell p m)) ∧
      ∀ r ∈ D.centers, ∀ θ : ℝ,
        (circleMap (r : ℂ) (D.radius r) θ, τ) ∈
          ModularCluster.regularDomain M (G1Pinch.ratioData w y n h ell p m) := by
  have havoid : ∀ z : ℂ,
      (z.re = D.crossing ∨ ∃ r ∈ D.centers, dist z (r : ℂ) = D.radius r) →
      (z, τ) ∈ ModularCluster.regularDomain M (G1Pinch.ratioData w y n h ell p m) := by
    intro z hz
    apply (ModularCluster.regularDomain_iff_no_labels M hM _ z τ).mpr
    refine ⟨hτ, ?_⟩
    intro b hb heq
    have hmem : z ∈
        ((fun q : ℕ × ℕ => modularPhiPolePoint M (m + 1) n τ q.1 q.2) ''
          modularPhiPoleLabels M (m + 1) n) ∪
        ((fun q : ℕ × ℕ => modularPhiZeroPoint M (m + p) n τ q.1 q.2 - y) ''
          modularPhiZeroLabels M (m + p) n) := by
      rcases b with ⟨b, K, J⟩
      cases b
      · right
        refine ⟨(K, J), ?_, ?_⟩
        · simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
        · simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using heq.symm
      · left
        refine ⟨(K, J), ?_, ?_⟩
        · simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
        · simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using heq.symm
    obtain ⟨hcross, hcircles⟩ := hD.2.1 z hmem
    rcases hz with hz | ⟨r, hr, hz⟩
    · exact hcross hz
    · exact hcircles r hr hz
  constructor
  · intro t
    apply havoid
    left
    simp [g1VerticalPoint]
  · intro r hr θ
    apply havoid
    right
    refine ⟨r, hr, ?_⟩
    simp [Complex.dist_eq, abs_of_pos (hD.1 r hr)]

/-- No pinch is both necessary and sufficient for the precise existing G1 chain-family existence
clause. This does not assert any integral identity, convergence, removable value, or
G1RealConclusion itself.

[RW26, p. 6, p. 7, p. 13]. -/
theorem noPinch_iff_exists_separatingFamily (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℝ) (hT : 0 < g1T M τ) (n p : ℤ) :
    g1NoPinch M τ y p ↔
      ∃ D : Fin (M 1 0).toNat → G1VerticalChain,
        ∀ m, G1Separates (D m) (g1NumeratorPoles M τ n (m : ℤ))
          (g1InversePoles M τ y n p (m : ℤ)) := by
  constructor
  · intro hpinch
    obtain ⟨ρ, D, -, -, -, hD⟩ :=
      exists_fixedSeparatingFamily M hM τ y hT n p hpinch
    exact ⟨D, fun m => (hD m).2.1⟩
  · rintro ⟨D, hD⟩
    apply (G1Pinch.noPinch_iff_all_disjoint M hM τ y n p).mpr
    intro m
    exact G1Pinch.separates_disjoint (D m) _ _ (hD m)

#check @exists_fixedSeparatingFamily
#check @separatesAt_regularDomain
#check @noPinch_iff_exists_separatingFamily
#print ExplicitChain
#print SeparatesAt
#print TracksClusters

end SICLean.L4.G1FixedSeparation
