import SICLean.L4.G1ContinuationGeometry
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
Auxiliaries for complex separating circles. Real shadows reduce an infinite vertical boundary to
finitely many labels on a joint parameter neighborhood. A connected smaller ball preserves every
side and circle-membership test. Subordinate polygonal covers keep a single fixed chain on every
whole edge.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups unitInterval

namespace SICLean.L4.G1ContinuationCirclesAux

/-- The separation criterion, keeping the actual labels at complex parameters. -/
theorem separatesAt_iff_labels (D : G1VerticalChain) (M : SL(2, ℤ))
    (τ y : ℂ) (n p m : ℤ) :
    G1FixedSeparation.SeparatesAt D M τ y n p m ↔
      (∀ r ∈ D.centers, 0 < D.radius r) ∧
      (∀ b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p m),
        let z := ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p m) τ b
        (z.re ≠ D.crossing ∧ ∀ r ∈ D.centers, dist z (r : ℂ) ≠ D.radius r) ∧
          G1FixedSeparation.leftAssignmentAt D z = if b.1 then 0 else 1) := by
  constructor
  · rintro ⟨hr, ha, hP, hZ⟩
    refine ⟨hr, ?_⟩
    rintro ⟨b, K, J⟩ hb
    cases b
    · have hl : (K, J) ∈ modularPhiZeroLabels M (m + p) n := by
        simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
      have hz : modularPhiZeroPoint M (m + p) n τ K J - y ∈
          (fun q : ℕ × ℕ => modularPhiZeroPoint M (m + p) n τ q.1 q.2 - y) ''
            modularPhiZeroLabels M (m + p) n := ⟨(K, J), hl, rfl⟩
      simpa only [ModularCluster.branchPoint, G1Pinch.ratioData, Bool.false_eq_true, if_false, if_true] using
        ⟨ha _ (Or.inr hz), hZ _ hz⟩
    · have hl : (K, J) ∈ modularPhiPoleLabels M (m + 1) n := by
        simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
      have hz : modularPhiPolePoint M (m + 1) n τ K J ∈
          (fun q : ℕ × ℕ => modularPhiPolePoint M (m + 1) n τ q.1 q.2) ''
            modularPhiPoleLabels M (m + 1) n := ⟨(K, J), hl, rfl⟩
      simpa only [ModularCluster.branchPoint, G1Pinch.ratioData, Bool.false_eq_true, if_false, if_true] using
        ⟨ha _ (Or.inl hz), hP _ hz⟩
  · rintro ⟨hr, hb⟩
    have hP (K J : ℕ) (hl : (K, J) ∈ modularPhiPoleLabels M (m + 1) n) :
        ((modularPhiPolePoint M (m + 1) n τ K J).re ≠ D.crossing ∧
          ∀ r ∈ D.centers, dist (modularPhiPolePoint M (m + 1) n τ K J) (r : ℂ) ≠
            D.radius r) ∧
        G1FixedSeparation.leftAssignmentAt D (modularPhiPolePoint M (m + 1) n τ K J) = 0 := by
      simpa only [ModularCluster.branchPoint, G1Pinch.ratioData, Bool.false_eq_true, if_false, if_true] using
        hb (true, K, J) (by simpa [ModularCluster.labels, G1Pinch.ratioData] using hl)
    have hZ (K J : ℕ) (hl : (K, J) ∈ modularPhiZeroLabels M (m + p) n) :
        ((modularPhiZeroPoint M (m + p) n τ K J - y).re ≠ D.crossing ∧
          ∀ r ∈ D.centers, dist (modularPhiZeroPoint M (m + p) n τ K J - y) (r : ℂ) ≠
            D.radius r) ∧
        G1FixedSeparation.leftAssignmentAt D (modularPhiZeroPoint M (m + p) n τ K J - y) = 1 := by
      simpa only [ModularCluster.branchPoint, G1Pinch.ratioData, Bool.false_eq_true, if_false, if_true] using
        hb (false, K, J) (by simpa [ModularCluster.labels, G1Pinch.ratioData] using hl)
    refine ⟨hr, ?_, ?_, ?_⟩
    · rintro z (⟨⟨K, J⟩, hl, rfl⟩ | ⟨⟨K, J⟩, hl, rfl⟩)
      · exact (hP K J hl).1
      · exact (hZ K J hl).1
    · rintro z ⟨⟨K, J⟩, hl, rfl⟩
      exact (hP K J hl).2
    · rintro z ⟨⟨K, J⟩, hl, rfl⟩
      exact (hZ K J hl).2

theorem inverse_re (M : SL(2, ℤ)) (τ y : ℂ) (n p m : ℤ) (K J : ℕ) :
    (modularPhiZeroPoint M (m + p) n τ K J - y).re =
      ((n : ℝ) - 1 - ((m : ℝ) + (p : ℝ) + (K : ℝ)) *
        (etaDenom M τ).re - (J : ℝ)) / (M 1 0 : ℝ) - y.re := by
  simp [modularPhiZeroPoint]
  ring

def branch (M : SL(2, ℤ)) (n p m : ℤ) (q : ℂ × ℂ)
    (b : ModularCluster.Label) : ℂ :=
  ModularCluster.branchPoint M (G1Pinch.ratioData 0 q.2 n 0 0 p m) q.1 b

def branchLabels (M : SL(2, ℤ)) (n p m : ℤ) : Set ModularCluster.Label :=
  ModularCluster.labels M (G1Pinch.ratioData 0 0 n 0 0 p m)

theorem branch_continuous (M : SL(2, ℤ)) (n p m : ℤ) (b : ModularCluster.Label) :
    Continuous (fun q : ℂ × ℂ => branch M n p m q b) := by
  rcases b with ⟨b, K, J⟩
  cases b <;> unfold branch ModularCluster.branchPoint G1Pinch.ratioData <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;>
    simp only [modularPhiZeroPoint, modularPhiPolePoint, etaDenom] <;> fun_prop

theorem branch_shadow (M : SL(2, ℤ)) (n p m : ℤ) (q : ℂ × ℂ)
    (b : ModularCluster.Label) :
    branch M n p m ((q.1.re : ℂ), (q.2.re : ℂ)) b =
      ((branch M n p m q b).re : ℂ) := by
  rcases b with ⟨b, K, J⟩
  cases b <;> apply Complex.ext <;>
    simp [branch, ModularCluster.branchPoint, G1Pinch.ratioData,
      modularPhiPolePoint, modularPhiZeroPoint, etaDenom]

/-- Local finiteness for a whole vertical strip, with both parameters moving. The real shadow
converts this to the existing bounded-label theorem. -/
theorem finite_strip_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n p m : ℤ) (q₀ : ℂ × ℂ) (hT : 0 < (etaDenom M q₀.1).re)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ρ : ℝ, 0 < ρ ∧
      {b | b ∈ branchLabels M n p m ∧ ∃ q ∈ Metric.closedBall q₀ ρ,
        |(branch M n p m q b).re| ≤ R}.Finite := by
  let k := G1Pinch.ratioData 0 (q₀.2.re : ℂ) n 0 0 p m
  have hT₀ : 0 < g1T M q₀.1.re := by simpa [g1T, etaDenom] using hT
  obtain ⟨ρ, hρ, _, hfin⟩ := ModularCluster.exists_uniform_finite_labels M hM k
    (q₀.1.re : ℂ) (real_mem_modularPhiDomain M q₀.1.re hT₀) (R + 1) (by positivity)
  refine ⟨min ρ 1, lt_min hρ one_pos, hfin.subset ?_⟩
  rintro b ⟨hb, q, hq, hbound⟩
  refine ⟨hb, (q.1.re : ℂ), ?_, ?_⟩
  · apply Metric.mem_closedBall.mpr
    calc
      dist (q.1.re : ℂ) (q₀.1.re : ℂ) = |(q.1 - q₀.1).re| := by
        simp [Complex.dist_eq, ← Complex.ofReal_sub]
      _ ≤ ‖q.1 - q₀.1‖ := Complex.abs_re_le_norm _
      _ ≤ dist q q₀ := by simpa [dist_eq_norm] using norm_fst_le (q - q₀)
      _ ≤ min ρ 1 := Metric.mem_closedBall.mp hq
      _ ≤ ρ := min_le_left _ _
  · have hy : |q.2.re - q₀.2.re| ≤ 1 := by
      calc
        |q.2.re - q₀.2.re| = |(q.2 - q₀.2).re| := rfl
        _ ≤ ‖q.2 - q₀.2‖ := Complex.abs_re_le_norm _
        _ ≤ dist q q₀ := by simpa [dist_eq_norm] using norm_snd_le (q - q₀)
        _ ≤ min ρ 1 := Metric.mem_closedBall.mp hq
        _ ≤ 1 := min_le_right _ _
    have hshadow := branch_shadow M n p m q b
    rcases b with ⟨b, K, J⟩
    cases b
    · have he : ModularCluster.branchPoint M k (q.1.re : ℂ) (false, K, J) =
          (branch M n p m ((q.1.re : ℂ), (q.2.re : ℂ)) (false, K, J)) +
            ((q.2.re - q₀.2.re : ℝ) : ℂ) := by
        simp [k, branch, ModularCluster.branchPoint, G1Pinch.ratioData]
      rw [he, hshadow]
      calc
        ‖(((branch M n p m q (false, K, J)).re : ℝ) : ℂ) +
            ((q.2.re - q₀.2.re : ℝ) : ℂ)‖ ≤
            |(branch M n p m q (false, K, J)).re| + |q.2.re - q₀.2.re| := by
          simpa only [Complex.norm_real, Real.norm_eq_abs] using norm_add_le
            (((branch M n p m q (false, K, J)).re : ℝ) : ℂ)
            ((q.2.re - q₀.2.re : ℝ) : ℂ)
        _ ≤ R + 1 := add_le_add hbound hy
    · have he : ModularCluster.branchPoint M k (q.1.re : ℂ) (true, K, J) =
          branch M n p m ((q.1.re : ℂ), (q.2.re : ℂ)) (true, K, J) := rfl
      rw [he, hshadow]
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        hbound.trans (le_add_of_nonneg_right zero_le_one)

/-- All labels preserve their baseline side and circle membership on one joint neighborhood. Local
finiteness is used before selecting the radius. -/
theorem stable_geometry (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n p m : ℤ)
    (q₀ : ℂ × ℂ) (hT : 0 < (etaDenom M q₀.1).re)
    (x : ℝ) (s : Finset (ℂ × ℝ))
    (ha : ∀ b ∈ branchLabels M n p m,
      (branch M n p m q₀ b).re ≠ x ∧
        ∀ cr ∈ s, dist (branch M n p m q₀ b) cr.1 ≠ cr.2) :
    ∀ᶠ q in 𝓝 q₀, ∀ b ∈ branchLabels M n p m,
      (branch M n p m q b).re ≠ x ∧
      ((branch M n p m q b).re < x ↔ (branch M n p m q₀ b).re < x) ∧
      ∀ cr ∈ s, dist (branch M n p m q b) cr.1 ≠ cr.2 ∧
        (dist (branch M n p m q b) cr.1 < cr.2 ↔
          dist (branch M n p m q₀ b) cr.1 < cr.2) := by
  let R : ℝ := |x| + ∑ cr ∈ s, (‖cr.1‖ + |cr.2|) + 1
  have hsum : 0 ≤ ∑ cr ∈ s, (‖cr.1‖ + |cr.2|) :=
    Finset.sum_nonneg fun cr _ => add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hxR : |x| ≤ R := by dsimp [R]; linarith
  have hcrR (cr : ℂ × ℝ) (hcr : cr ∈ s) : cr.2 + ‖cr.1‖ ≤ R := by
    have := Finset.single_le_sum
      (fun a (_ : a ∈ s) => add_nonneg (norm_nonneg a.1) (abs_nonneg a.2)) hcr
    dsimp [R]
    linarith [le_abs_self cr.2, abs_nonneg x]
  obtain ⟨ρ₀, hρ₀, hfin⟩ := finite_strip_neighborhood M hM n p m q₀ hT R hR
  let F : Set ModularCluster.Label := {b | b ∈ branchLabels M n p m ∧
    ∃ q ∈ Metric.closedBall q₀ ρ₀, |(branch M n p m q b).re| ≤ R}
  have hFfin : F.Finite := hfin
  have hFev : ∀ᶠ q in 𝓝 q₀, ∀ b ∈ F,
      (branch M n p m q b).re ≠ x ∧
        ∀ cr ∈ s, dist (branch M n p m q b) cr.1 ≠ cr.2 := by
    apply hFfin.eventually_all.mpr
    intro b hb
    refine ((Complex.continuous_re.comp (branch_continuous M n p m b)).continuousAt.eventually_ne
      (ha b hb.1).1).and ?_
    apply s.eventually_all.mpr
    intro cr hcr
    exact (((branch_continuous M n p m b).dist continuous_const).continuousAt.eventually_ne
      ((ha b hb.1).2 cr hcr))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hFev
  let ρ := min ρ₀ (δ / 2)
  have hρ : 0 < ρ := lt_min hρ₀ (by linarith)
  have hρδ : ρ < δ := (min_le_right _ _).trans_lt (by linarith)
  have hsub : Metric.closedBall q₀ ρ ⊆ Metric.closedBall q₀ ρ₀ :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hsmall : ∀ q ∈ Metric.closedBall q₀ ρ, ∀ b ∈ F,
      (branch M n p m q b).re ≠ x ∧
        ∀ cr ∈ s, dist (branch M n p m q b) cr.1 ≠ cr.2 := by
    intro q hq
    exact hδsub ((Metric.mem_closedBall.mp hq).trans_lt hρδ)
  have hno : ∀ q ∈ Metric.closedBall q₀ ρ, ∀ b ∈ branchLabels M n p m,
      (branch M n p m q b).re ≠ x ∧
        ∀ cr ∈ s, dist (branch M n p m q b) cr.1 ≠ cr.2 := by
    intro q hq b hb
    constructor
    · intro he
      have hbF : b ∈ F := ⟨hb, q, hsub hq, by simpa [he] using hxR⟩
      exact (hsmall q hq b hbF).1 he
    · intro cr hcr he
      have hbnd : |(branch M n p m q b).re| ≤ R := by
        calc
          |(branch M n p m q b).re| ≤ ‖branch M n p m q b‖ := Complex.abs_re_le_norm _
          _ ≤ dist (branch M n p m q b) cr.1 + ‖cr.1‖ := by
            simpa only [dist_zero_right] using dist_triangle (branch M n p m q b) cr.1 0
          _ ≤ R := by rw [he]; exact hcrR cr hcr
      exact (hsmall q hq b ⟨hb, q, hsub hq, hbnd⟩).2 cr hcr he
  filter_upwards [Metric.ball_mem_nhds q₀ hρ] with q hq
  have hqc : q ∈ Metric.closedBall q₀ ρ := Metric.ball_subset_closedBall hq
  have hq₀ : q₀ ∈ Metric.closedBall q₀ ρ := Metric.mem_closedBall_self hρ.le
  have hconn := (convex_closedBall q₀ ρ).isPreconnected
  intro b hb
  refine ⟨(hno q hqc b hb).1, ?_, ?_⟩
  · exact G1FixedSeparationAux.lt_iff_of_no_eq _ hconn _
      (Complex.continuous_re.comp (branch_continuous M n p m b)).continuousOn x
      (fun v hv => (hno v hv b hb).1) q q₀ hqc hq₀
  · intro cr hcr
    refine ⟨(hno q hqc b hb).2 cr hcr, ?_⟩
    exact G1FixedSeparationAux.lt_iff_of_no_eq _ hconn _
      ((branch_continuous M n p m b).dist continuous_const).continuousOn cr.2
      (fun v hv => (hno v hv b hb).2 cr hcr) q q₀ hqc hq₀

/-- Two finite circle families may have coincident centers and different radii. Their individual
membership tests, hence their full integer sum, are fixed. -/
theorem separation_eventually (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n p m : ℤ)
    (q₀ : ℂ × ℂ) (hT : 0 < (etaDenom M q₀.1).re)
    (D : G1VerticalChain) (C : ModularCluster.Circles)
    (ha : ∀ b ∈ branchLabels M n p m,
      let z := branch M n p m q₀ b
      (z.re ≠ D.crossing ∧
        (∀ r ∈ D.centers, dist z (r : ℂ) ≠ D.radius r) ∧
        ∀ a ∈ C.centers, dist z a ≠ C.radius a) ∧
      G1FixedSeparation.leftAssignmentAt D z +
        ∑ a ∈ C.centers, (if dist z a < C.radius a then 1 else 0 : ℤ) =
          if b.1 then 0 else 1) :
    ∀ᶠ q in 𝓝 q₀, ∀ b ∈ branchLabels M n p m,
      let z := branch M n p m q b
      (z.re ≠ D.crossing ∧
        (∀ r ∈ D.centers, dist z (r : ℂ) ≠ D.radius r) ∧
        ∀ a ∈ C.centers, dist z a ≠ C.radius a) ∧
      G1FixedSeparation.leftAssignmentAt D z +
        ∑ a ∈ C.centers, (if dist z a < C.radius a then 1 else 0 : ℤ) =
          if b.1 then 0 else 1 := by
  let s : Finset (ℂ × ℝ) :=
    (D.centers.image fun r : ℝ => ((r : ℂ), D.radius r)) ∪
      (C.centers.image fun a : ℂ => (a, C.radius a))
  have hreal (r : ℝ) (hr : r ∈ D.centers) : ((r : ℂ), D.radius r) ∈ s :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  have hextra (a : ℂ) (ha : a ∈ C.centers) : (a, C.radius a) ∈ s :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hgeom := stable_geometry M hM n p m q₀ hT D.crossing s (by
    intro b hb
    refine ⟨(ha b hb).1.1, ?_⟩
    intro cr hcr
    change cr ∈ (D.centers.image fun r : ℝ => ((r : ℂ), D.radius r)) ∪
      (C.centers.image fun a : ℂ => (a, C.radius a)) at hcr
    rcases Finset.mem_union.mp hcr with hbase | hex
    · obtain ⟨r, hrD, heq⟩ := Finset.mem_image.mp hbase
      simpa only [← heq] using (ha b hb).1.2.1 r hrD
    · obtain ⟨a, haC, heq⟩ := Finset.mem_image.mp hex
      simpa only [← heq] using (ha b hb).1.2.2 a haC)
  filter_upwards [hgeom] with q hq
  intro b hb
  obtain ⟨hne, hside, hcir⟩ := hq b hb
  refine ⟨⟨hne, fun r hr => (hcir _ (hreal r hr)).1,
    fun a hc => (hcir _ (hextra a hc)).1⟩, ?_⟩
  have hbase : G1FixedSeparation.circleWindingAt D (branch M n p m q b) =
      G1FixedSeparation.circleWindingAt D (branch M n p m q₀ b) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [(hcir _ (hreal r hr)).2]
  have hC : (∑ a ∈ C.centers,
      (if dist (branch M n p m q b) a < C.radius a then 1 else 0 : ℤ)) =
      ∑ a ∈ C.centers,
        (if dist (branch M n p m q₀ b) a < C.radius a then 1 else 0 : ℤ) := by
    apply Finset.sum_congr rfl
    intro a hc
    simp only [(hcir _ (hextra a hc)).2]
  simpa only [G1FixedSeparation.leftAssignmentAt, hside, hbase, hC] using (ha b hb).2

open G1Continuation

theorem polygon_joinedIn (P : Polygon) (S : Set (ℂ × ℂ))
    (v₀ v₁ : ℂ × ℂ) (hP : PolygonIn P S v₀ v₁) : JoinedIn S v₀ v₁ := by
  have hedges (i : Fin P.length) :
      JoinedIn S (P.vertex i.castSucc) (P.vertex i.succ) := by
    apply JoinedIn.ofLine (f := polygonPoint P i)
    · unfold polygonPoint
      fun_prop
    · simp [polygonPoint]
    · simp [polygonPoint]
    · rintro _ ⟨t, ht, rfl⟩
      exact hP.2.2.2 i t ht
  have hv₀ : P.vertex 0 ∈ S := by
    simpa [polygonPoint] using hP.2.2.2 ⟨0, hP.1⟩ 0 (by constructor <;> norm_num)
  have hchain (i : Fin (P.length + 1)) : JoinedIn S (P.vertex 0) (P.vertex i) := by
    refine Fin.induction ?_ (fun i hi => ?_) i
    · exact JoinedIn.refl hv₀
    · exact hi.trans (hedges i)
  simpa [hP.2.1, hP.2.2.1] using hchain (Fin.last P.length)

theorem polygon_subordinate_open_cover {ι : Type*}
    (S : Set (ℂ × ℂ)) (v₀ v₁ : ℂ × ℂ) (hjoin : JoinedIn S v₀ v₁)
    (V : ι → Set (ℂ × ℂ)) (hV : ∀ j, IsOpen (V j))
    (hVS : ∀ j, V j ⊆ S) (hcover : S ⊆ ⋃ j, V j) :
    ∃ (P : Polygon) (k : Fin P.length → ι),
      PolygonIn P S v₀ v₁ ∧
        ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, polygonPoint P i s ∈ V (k i) := by
  let γ := hjoin.somePath
  have hlocal (t : I) : ∃ j r, 0 < r ∧ Metric.ball (γ t) r ⊆ V j := by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover (hjoin.somePath_mem t))
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (hV j) _ hj
    exact ⟨j, r, hr, hsub⟩
  choose j r hr hsub using hlocal
  let c (t : I) := γ ⁻¹' Metric.ball (γ t) (r t)
  obtain ⟨t, ht₀, htmono, ⟨n, hn⟩, htsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (c := c)
      (fun u => Metric.isOpen_ball.preimage γ.continuous)
      (by
        intro u _
        exact Set.mem_iUnion.mpr ⟨u, by simpa [c] using hr u⟩)
  choose b hb using htsub
  let N := n + 1
  let P : Polygon := ⟨N, fun i => γ (t i.val)⟩
  let k (i : Fin P.length) := j (b i.val)
  have hsegments (i : Fin P.length) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      polygonPoint P i s ∈ V (k i) := by
    have hleft : γ (t i.val) ∈ Metric.ball (γ (b i.val)) (r (b i.val)) :=
      hb i.val ⟨le_rfl, htmono (Nat.le_succ _)⟩
    have hright : γ (t (i.val + 1)) ∈ Metric.ball (γ (b i.val)) (r (b i.val)) :=
      hb i.val ⟨htmono (Nat.le_succ _), le_rfl⟩
    apply hsub (b i.val)
    have hconv := (convex_ball (γ (b i.val)) (r (b i.val)))
      hleft hright (sub_nonneg.mpr hs.2) hs.1 (by ring : 1 - s + s = (1 : ℝ))
    have hsmul (q : ℝ) (v : ℂ × ℂ) : q • v = (q : ℂ) • v := by
      ext <;> simp [Complex.real_smul]
    simpa only [polygonPoint, P, Fin.val_castSucc, Fin.val_succ,
      hsmul, Complex.ofReal_sub, Complex.ofReal_one] using hconv
  refine ⟨P, k, ?_, hsegments⟩
  refine ⟨Nat.succ_pos _, ?_, ?_, ?_⟩
  · change γ (t 0) = v₀
    rw [ht₀]
    exact γ.source
  · change γ (t N) = v₁
    rw [hn N (by omega)]
    exact γ.target
  · intro i s hs
    exact hVS (k i) (hsegments i s hs)

/-! Finite principal-part accounts for arbitrary complex circle centers. -/

open FinitePrincipalParts G1FiniteChainLedgerAux

def circleCount {ι : Type*} (s : Finset ι) (c : ι → ℂ) (r : ι → ℝ) (z : ℂ) : ℤ :=
  ∑ i ∈ s, if dist z (c i) < r i then 1 else 0

def assignment {ι : Type*} (s : Finset ι) (c : ι → ℂ) (r : ι → ℝ)
    (x : ℝ) (z : ℂ) : ℤ := (if z.re < x then 1 else 0) + circleCount s c r z

def truncated {ι : Type*} (s : Finset ι) (c : ι → ℂ) (r : ι → ℝ)
    (x : ℝ) (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  G1FiniteLedger.verticalSegment f x R + ∑ i ∈ s, circleCCW (c i) (r i) f

theorem assignment_zero_constraints {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (r : ι → ℝ) (x : ℝ) (z : ℂ)
    (hbase : z.re ≠ x) (hsafe : ∀ i ∈ s, dist z (c i) ≠ r i)
    (hzero : assignment s c r x z = 0) :
    x < z.re ∧ ∀ i ∈ s, r i < dist z (c i) := by
  have hnonneg : 0 ≤ circleCount s c r z := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> norm_num
  have hnotleft : ¬ z.re < x := by
    intro hz
    simp only [assignment, if_pos hz] at hzero
    omega
  have hc : circleCount s c r z = 0 := by
    simpa only [assignment, if_neg hnotleft, zero_add] using hzero
  refine ⟨lt_of_le_of_ne (le_of_not_gt hnotleft) hbase.symm, ?_⟩
  intro i hi
  have hninside : ¬ dist z (c i) < r i := by
    intro hin
    have hle : (if dist z (c i) < r i then (1 : ℤ) else 0) ≤ circleCount s c r z := by
      unfold circleCount
      exact Finset.single_le_sum (f := fun j => if dist z (c j) < r j then (1 : ℤ) else 0)
        (fun j _ => by split_ifs <;> norm_num) hi
    simp only [if_pos hin, hc] at hle
    omega
  exact lt_of_le_of_ne (le_of_not_gt hninside) (hsafe i hi).symm

theorem circle_finite_account (f g : ℂ → ℂ) (P : Finset ℂ)
    (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (S : Set ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hinside : Metric.closedBall c r ⊆ S)
    (hsafe : ∀ p ∈ P, dist p c ≠ r) (hg : AnalyticOnNhd ℂ g S)
    (hfg : ∀ z ∈ S, z ∉ P → f z = finitePrincipalPart P id N A z + g z) :
    circleCCW c r f = 2 * (Real.pi : ℂ) * Complex.I *
      ∑ p ∈ P, if dist p c < r then residueCoefficient (N p) (A p) else 0 := by
  have hne (w : ℂ) (hw : w ∈ Metric.sphere c r) (p : ℂ) (hp : p ∈ P) : w ≠ p := by
    intro he
    subst w
    exact hsafe p hp hw
  have hP : CircleIntegrable (finitePrincipalPart P id N A) c r := by
    apply ContinuousOn.circleIntegrable hr.le
    apply continuousOn_finsetSum
    intro p hp
    exact principalPart_continuousOn _ _ _ (fun w hw => hne w hw p hp)
  have hgd : AnalyticOnNhd ℂ g (Metric.closedBall c r) := hg.mono hinside
  have hgi : CircleIntegrable g c r :=
    (hgd.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hr.le
  have hgz : (∮ w in C(c, r), g w) = 0 := by
    apply DiffContOnCl.circleIntegral_eq_zero hr.le
    apply DifferentiableOn.diffContOnCl
    exact hgd.differentiableOn.mono Metric.closure_ball_subset_closedBall
  rw [circleCCW_eq_circleIntegral _ _ _ hr]
  calc
    _ = ∮ w in C(c, r), finitePrincipalPart P id N A w + g w := by
      apply circleIntegral.integral_congr hr.le
      intro w hw
      apply hfg w (hinside (Metric.sphere_subset_closedBall hw))
      intro hp
      exact hne w hw w hp rfl
    _ = ∮ w in C(c, r), finitePrincipalPart P id N A w := by
      rw [circleIntegral.integral_add hP hgi, hgz, add_zero]
    _ = _ := by
      unfold finitePrincipalPart
      rw [circleIntegral.integral_fun_sum]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        exact circle_integral_principalPart c p r (N p) (A p) hr (hsafe p hp)
      · intro p hp
        exact (principalPart_continuousOn _ _ _
          (fun w hw => hne w hw p hp)).circleIntegrable hr.le

theorem rectangle_finite_account_of_lt (f g : ℂ → ℂ) (P : Finset ℂ)
    (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (S : Set ℂ) (R x₀ x₁ : ℝ)
    (hR : 0 < R) (horder : x₀ < x₁)
    (hsafe₀ : ∀ p ∈ P, p.re ≠ x₀) (hsafe₁ : ∀ p ∈ P, p.re ≠ x₁)
    (hheight : ∀ p ∈ P, |p.im| < R)
    (hrect : closedRectangle (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) ⊆ S)
    (hg : AnalyticOnNhd ℂ g S)
    (hfg : ∀ z ∈ S, z ∉ P → f z = finitePrincipalPart P id N A z + g z) :
    rectangleCCW (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) f =
      2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P,
        if x₀ < p.re ∧ p.re < x₁ then residueCoefficient (N p) (A p) else 0 := by
  let lo := g1VerticalPoint x₀ (-R)
  let hi := g1VerticalPoint x₁ R
  have hre : lo.re < hi.re := by simpa [lo, hi, g1VerticalPoint] using horder
  have him : lo.im < hi.im := by simp [lo, hi, g1VerticalPoint]; linarith
  have hclosed (z : ℂ) (hz : z ∈ closedRectangle lo hi) :
      x₀ ≤ z.re ∧ z.re ≤ x₁ ∧ -R ≤ z.im ∧ z.im ≤ R := by
    simpa [closedRectangle, lo, hi, g1VerticalPoint] using hz
  have hopen (z : ℂ) : z ∈ openRectangle lo hi ↔
      x₀ < z.re ∧ z.re < x₁ ∧ -R < z.im ∧ z.im < R := by
    simp [openRectangle, lo, hi, g1VerticalPoint]
  have hne (p : ℂ) (hp : p ∈ P) (z : ℂ) (hz : z ∈ rectangleBoundary lo hi) : z ≠ p := by
    intro he
    subst z
    obtain ⟨hpl, hpu, _, _⟩ := hclosed p hz.1
    have hleft : x₀ < p.re := lt_of_le_of_ne hpl (hsafe₀ p hp).symm
    have hright : p.re < x₁ := lt_of_le_of_ne hpu (hsafe₁ p hp)
    exact hz.2 ((hopen p).mpr ⟨hleft, hright, (abs_lt.mp (hheight p hp)).1,
      (abs_lt.mp (hheight p hp)).2⟩)
  have hPc : ContinuousOn (finitePrincipalPart P id N A) (rectangleBoundary lo hi) := by
    apply continuousOn_finsetSum
    intro p hp
    exact principalPart_continuousOn _ _ _ (fun z hz => hne p hp z hz)
  have hgc : ContinuousOn g (rectangleBoundary lo hi) :=
    (hg.mono hrect).continuousOn.mono (fun z hz => hz.1)
  have hgz : rectangleCCW lo hi g = 0 :=
    rectangleCCW_eq_zero lo hi hre.le him.le (hg.mono hrect).differentiableOn
  have hterm (p : ℂ) (hp : p ∈ P) :
      rectangleCCW lo hi (principalPart p (N p) (A p)) =
        2 * (Real.pi : ℂ) * Complex.I *
          (if x₀ < p.re ∧ p.re < x₁ then residueCoefficient (N p) (A p) else 0) := by
    by_cases hin : x₀ < p.re ∧ p.re < x₁
    · rw [if_pos hin]
      apply rectangleCCW_principalPart
      exact (hopen p).mpr ⟨hin.1, hin.2, (abs_lt.mp (hheight p hp)).1,
        (abs_lt.mp (hheight p hp)).2⟩
    · rw [if_neg hin, mul_zero]
      apply rectangleCCW_eq_zero lo hi hre.le him.le
      intro z hz
      apply AnalyticAt.differentiableWithinAt
      apply principalPart_analyticAt
      intro he
      subst z
      obtain ⟨hpl, hpu, _, _⟩ := hclosed p hz
      exact hin ⟨lt_of_le_of_ne hpl (hsafe₀ p hp).symm,
        lt_of_le_of_ne hpu (hsafe₁ p hp)⟩
  change rectangleCCW lo hi f = _
  calc
    _ = rectangleCCW lo hi (fun z => finitePrincipalPart P id N A z + g z) := by
      apply rectangleCCW_congr lo hi hre.le him.le
      intro z hz
      exact hfg z (hrect hz.1) (fun hp => hne z hp z hz rfl)
    _ = rectangleCCW lo hi (finitePrincipalPart P id N A) := by
      rw [rectangleCCW_add lo hi hre.le him.le hPc hgc, hgz, add_zero]
    _ = _ := by
      unfold finitePrincipalPart
      rw [rectangleCCW_fun_sum P lo hi hre.le him.le]
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hterm
      · intro p hp
        exact principalPart_continuousOn _ _ _ (fun z hz => hne p hp z hz)

theorem rectangle_finite_account (f g : ℂ → ℂ) (P : Finset ℂ)
    (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (S : Set ℂ) (R x₀ x₁ : ℝ)
    (hR : 0 < R) (hsafe₀ : ∀ p ∈ P, p.re ≠ x₀) (hsafe₁ : ∀ p ∈ P, p.re ≠ x₁)
    (hheight : ∀ p ∈ P, |p.im| < R)
    (hrect : closedRectangle (g1VerticalPoint (min x₀ x₁) (-R))
      (g1VerticalPoint (max x₀ x₁) R) ⊆ S)
    (hg : AnalyticOnNhd ℂ g S)
    (hfg : ∀ z ∈ S, z ∉ P → f z = finitePrincipalPart P id N A z + g z) :
    rectangleCCW (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) f =
      2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P,
        (G1FiniteLedger.baselineJump x₀ x₁ p.re : ℂ) * residueCoefficient (N p) (A p) := by
  have hasc (a b : ℝ) (hab : a < b)
      (hsafea : ∀ p ∈ P, p.re ≠ a) (hsafeb : ∀ p ∈ P, p.re ≠ b)
      (hrectab : closedRectangle (g1VerticalPoint a (-R)) (g1VerticalPoint b R) ⊆ S) :
      rectangleCCW (g1VerticalPoint a (-R)) (g1VerticalPoint b R) f =
        2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P,
          (G1FiniteLedger.baselineJump a b p.re : ℂ) * residueCoefficient (N p) (A p) := by
    rw [rectangle_finite_account_of_lt f g P N A S R a b hR hab hsafea hsafeb hheight hrectab hg hfg]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    change (if a < p.re ∧ p.re < b then _ else _) =
      (baselineJump a b p.re : ℂ) * _
    rw [baselineJump_ascending a b p.re hab (hsafea p hp)]
    split_ifs <;> simp
  rcases lt_trichotomy x₀ x₁ with hord | heq | hord
  · exact hasc x₀ x₁ hord hsafe₀ hsafe₁ (by simpa [min_eq_left hord.le, max_eq_right hord.le] using hrect)
  · subst x₁
    simp [rectangleCCW, g1VerticalPoint, G1FiniteLedger.baselineJump]
  · rw [rectangleCCW_swap_baselines, hasc x₁ x₀ hord hsafe₁ hsafe₀
      (by simpa [min_eq_right hord.le, max_eq_left hord.le] using hrect),
      ← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hswap : G1FiniteLedger.baselineJump x₀ x₁ p.re =
        -G1FiniteLedger.baselineJump x₁ x₀ p.re := by
      unfold G1FiniteLedger.baselineJump
      ring
    rw [hswap, Int.cast_neg, neg_mul]

theorem circle_sum_account {ι : Type*} (s : Finset ι) (c : ι → ℂ) (r : ι → ℝ)
    (f g : ℂ → ℂ) (P : Finset ℂ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (S : Set ℂ)
    (hr : ∀ i ∈ s, 0 < r i) (hinside : ∀ i ∈ s, Metric.closedBall (c i) (r i) ⊆ S)
    (hsafe : ∀ p ∈ P, ∀ i ∈ s, dist p (c i) ≠ r i)
    (hg : AnalyticOnNhd ℂ g S)
    (hfg : ∀ z ∈ S, z ∉ P → f z = finitePrincipalPart P id N A z + g z) :
    (∑ i ∈ s, circleCCW (c i) (r i) f) = 2 * (Real.pi : ℂ) * Complex.I *
      ∑ p ∈ P, (circleCount s c r p : ℂ) * residueCoefficient (N p) (A p) := by
  calc
    _ = ∑ i ∈ s, 2 * (Real.pi : ℂ) * Complex.I *
        ∑ p ∈ P, if dist p (c i) < r i then residueCoefficient (N p) (A p) else 0 := by
      exact Finset.sum_congr rfl (fun i hi => circle_finite_account f g P N A S
        (c i) (r i) (hr i hi) (hinside i hi) (fun p hp => hsafe p hp i hi) hg hfg)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      simp only [circleCount, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp

theorem finite_zero_of_principal_parts {ι : Type*} (s₀ s₁ : Finset ι)
    (c₀ c₁ : ι → ℂ) (r₀ r₁ : ι → ℝ) (x₀ x₁ : ℝ)
    (f g : ℂ → ℂ) (P : Finset ℂ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (S : Set ℂ) (R : ℝ)
    (hR : 0 < R) (hr₀ : ∀ i ∈ s₀, 0 < r₀ i) (hr₁ : ∀ i ∈ s₁, 0 < r₁ i)
    (hinside₀ : ∀ i ∈ s₀, Metric.closedBall (c₀ i) (r₀ i) ⊆ S)
    (hinside₁ : ∀ i ∈ s₁, Metric.closedBall (c₁ i) (r₁ i) ⊆ S)
    (hsafe₀ : ∀ p ∈ P, p.re ≠ x₀ ∧ ∀ i ∈ s₀, dist p (c₀ i) ≠ r₀ i)
    (hsafe₁ : ∀ p ∈ P, p.re ≠ x₁ ∧ ∀ i ∈ s₁, dist p (c₁ i) ≠ r₁ i)
    (hheight : ∀ p ∈ P, |p.im| < R)
    (hrect : closedRectangle (g1VerticalPoint (min x₀ x₁) (-R))
      (g1VerticalPoint (max x₀ x₁) R) ⊆ S)
    (hg : AnalyticOnNhd ℂ g S)
    (hfg : ∀ z ∈ S, z ∉ P → f z = finitePrincipalPart P id N A z + g z)
    (hassign : ∀ p ∈ P, assignment s₀ c₀ r₀ x₀ p = assignment s₁ c₁ r₁ x₁ p) :
    truncated s₁ c₁ r₁ x₁ f R - truncated s₀ c₀ r₀ x₀ f R +
      G1FiniteLedger.connectors f x₀ x₁ R = 0 := by
  have hv := rectangle_finite_account f g P N A S R x₀ x₁ hR
    (fun p hp => (hsafe₀ p hp).1) (fun p hp => (hsafe₁ p hp).1) hheight hrect hg hfg
  rw [G1FiniteLedger.rectangle_orientation] at hv
  have hc₀ := circle_sum_account s₀ c₀ r₀ f g P N A S hr₀ hinside₀
    (fun p hp => (hsafe₀ p hp).2) hg hfg
  have hc₁ := circle_sum_account s₁ c₁ r₁ f g P N A S hr₁ hinside₁
    (fun p hp => (hsafe₁ p hp).2) hg hfg
  unfold truncated
  rw [hc₀, hc₁]
  calc
    _ = (G1FiniteLedger.verticalSegment f x₁ R - G1FiniteLedger.verticalSegment f x₀ R +
        G1FiniteLedger.connectors f x₀ x₁ R) +
        (2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P, (circleCount s₁ c₁ r₁ p : ℂ) *
          residueCoefficient (N p) (A p)) -
        (2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P, (circleCount s₀ c₀ r₀ p : ℂ) *
          residueCoefficient (N p) (A p)) := by ring
    _ = 0 := by
      rw [hv, ← mul_add, ← mul_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply mul_eq_zero.mpr
      right
      apply Finset.sum_eq_zero
      intro p hp
      have he : G1FiniteLedger.baselineJump x₀ x₁ p.re +
          circleCount s₁ c₁ r₁ p - circleCount s₀ c₀ r₀ p = 0 := by
        have hh := hassign p hp
        unfold assignment G1FiniteLedger.baselineJump at *
        omega
      rw [← add_mul, ← sub_mul, ← Int.cast_add, ← Int.cast_sub, he]
      simp


end SICLean.L4.G1ContinuationCirclesAux
