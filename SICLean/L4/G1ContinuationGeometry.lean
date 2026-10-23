import SICLean.L4.UpperIntegralIdentities
import SICLean.L4.G1ChainTransfer
import SICLean.L4.G1ContinuationGeometryAux

set_option autoImplicit false

/-!
# Explicit strict windows, pinch hyperplanes, and finite complex detours

The no-collision predicate is the existing
`ModularCluster.crossSeparated`; its real specialization is the existing `g1NoPinch`. No
route-existence, local-finiteness, holomorphy, or monodromy assumption is introduced. `Polygon`
stores only finitely many vertices. `PolygonIn` is literal geometry.

Analytic continuation: [RW26, p. 29]. This file proves the geometric steps. Joint compact
finiteness is proved here.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1Continuation

open G1ContinuationGeometryAux

abbrev Parameters := UpperWindow.Parameters

def singleWindow (M : SL(2, ℤ)) (τ : ℂ) (h ell : ℤ) : Set ℂ :=
  {w | 0 < (G1RatioTail.complexS M τ w h ell / etaDenom M τ).re}

def strictRatioWindow (M : SL(2, ℤ)) (τ : ℂ) (h ell p : ℤ) : Set (ℂ × ℂ) :=
  {v | v.1 ∈ singleWindow M τ h ell ∧
    (G1RatioTail.complexL M τ v.1 v.2 h ell p / etaDenom M τ).re < 0}

def pinchLabels (M : SL(2, ℤ)) (p : ℤ) : Set (ℕ × ℕ) :=
  {k | Int.ModEq (M 1 0) ((k.2 : ℤ) + M 1 1 * (k.1 : ℤ))
    (-1 - M 1 1 * p)}

def pinchValue (M : SL(2, ℤ)) (τ : ℂ) (p : ℤ) (k : ℕ × ℕ) : ℂ :=
  -(((p : ℂ) + (k.1 : ℂ)) * etaDenom M τ + 1 + (k.2 : ℂ)) / (M 1 0 : ℂ)

def pinchHyperplane (M : SL(2, ℤ)) (τ : ℂ) (p : ℤ) (k : ℕ × ℕ) : Set (ℂ × ℂ) :=
  {v | v.2 = pinchValue M τ p k}

def ratioFiber (M : SL(2, ℤ)) (τ : ℂ) (n h ell p : ℤ) : Set (ℂ × ℂ) :=
  {v | v ∈ strictRatioWindow M τ h ell p ∧
    ∀ m : Fin (M 1 0).toNat,
      ModularCluster.crossSeparated M (G1Pinch.ratioData v.1 v.2 n h ell p (m : ℤ)) τ}

def singleTube (M : SL(2, ℤ)) (h ell : ℤ) (ψ : ℝ) : Set (ℂ × ℂ) :=
  {u | u.1 ∈ UpperWindow.tauRegion M ψ ∧ u.2 ∈ singleWindow M u.1 h ell}

def ratioTube (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ : ℝ) : Set Parameters :=
  {x | x.1 ∈ UpperWindow.tauRegion M ψ ∧ x.2 ∈ ratioFiber M x.1 n h ell p}

structure Polygon where
  length : ℕ
  vertex : Fin (length + 1) → ℂ × ℂ

def polygonPoint (P : Polygon) (i : Fin P.length) (t : ℝ) : ℂ × ℂ :=
  (1 - (t : ℂ)) • P.vertex i.castSucc + (t : ℂ) • P.vertex i.succ

def PolygonIn (P : Polygon) (U : Set (ℂ × ℂ)) (v₀ v₁ : ℂ × ℂ) : Prop :=
  0 < P.length ∧ P.vertex 0 = v₀ ∧ P.vertex (Fin.last P.length) = v₁ ∧
    ∀ i : Fin P.length, ∀ t ∈ Icc (0 : ℝ) 1, polygonPoint P i t ∈ U

def detourPoint (v : ℂ × ℂ) (r θ : ℝ) : ℂ × ℂ :=
  (v.1, v.2 + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- G01. [RW26, p. 29]. -/
theorem single_window_open_convex (M : SL(2, ℤ)) (τ : ℂ) (h ell : ℤ) :
    IsOpen (singleWindow M τ h ell) ∧ Convex ℝ (singleWindow M τ h ell) := by
  constructor
  · exact isOpen_lt continuous_const (by unfold G1RatioTail.complexS; fun_prop)
  · intro x hx y hy a b ha hb hab
    change 0 < (G1RatioTail.complexS M τ (a • x + b • y) h ell / etaDenom M τ).re
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have heq : G1RatioTail.complexS M τ (a • x + b • y) h ell / etaDenom M τ =
        a • (G1RatioTail.complexS M τ x h ell / etaDenom M τ) +
        b • (G1RatioTail.complexS M τ y h ell / etaDenom M τ) := by
      simp only [G1RatioTail.complexS, Complex.real_smul, div_eq_mul_inv]
      linear_combination -((h : ℂ) + (ell : ℂ) * etaDenom M τ) * (etaDenom M τ)⁻¹ * hab'
    rw [heq, Complex.add_re, Complex.smul_re, Complex.smul_re]
    exact (convex_Ioi (0 : ℝ)) hx hy ha hb hab

/-- G02. [RW26, p. 29]. Nonemptiness is an output. -/
theorem strict_ratio_open_convex_nonempty (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hT : etaDenom M τ ≠ 0) (h ell p : ℤ) :
    IsOpen (strictRatioWindow M τ h ell p) ∧
      Convex ℝ (strictRatioWindow M τ h ell p) ∧
      (strictRatioWindow M τ h ell p).Nonempty := by
  have hS := single_window_open_convex M τ h ell
  refine ⟨hS.1.preimage continuous_fst |>.inter
    (isOpen_lt (show Continuous (fun v : ℂ × ℂ =>
      (G1RatioTail.complexL M τ v.1 v.2 h ell p / etaDenom M τ).re) by
        unfold G1RatioTail.complexL G1RatioTail.complexS; fun_prop) continuous_const), ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    refine ⟨hS.2 hx.1 hy.1 ha hb hab, ?_⟩
    change (G1RatioTail.complexL M τ (a • x + b • y).1
      (a • x + b • y).2 h ell p / etaDenom M τ).re < 0
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have heq : G1RatioTail.complexL M τ (a • x + b • y).1
        (a • x + b • y).2 h ell p / etaDenom M τ =
        a • (G1RatioTail.complexL M τ x.1 x.2 h ell p / etaDenom M τ) +
        b • (G1RatioTail.complexL M τ y.1 y.2 h ell p / etaDenom M τ) := by
      simp only [G1RatioTail.complexL, G1RatioTail.complexS, Prod.fst_add,
        Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Complex.real_smul, div_eq_mul_inv]
      linear_combination -((h : ℂ) + (ell : ℂ) * etaDenom M τ +
        ((p : ℂ) - 1) * etaDenom M τ) * (etaDenom M τ)⁻¹ * hab'
    rw [heq, Complex.add_re, Complex.smul_re, Complex.smul_re]
    exact (convex_Iio (0 : ℝ)) hx.2 hy.2 ha hb hab
  · have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
    refine ⟨((etaDenom M τ - (h : ℂ) - (ell : ℂ) * etaDenom M τ) / (M 1 0 : ℂ),
      (-1 - (p : ℂ)) * etaDenom M τ / (M 1 0 : ℂ)), ?_, ?_⟩
    · change 0 < (G1RatioTail.complexS M τ _ h ell / etaDenom M τ).re
      have heq : G1RatioTail.complexS M τ
          ((etaDenom M τ - (h : ℂ) - (ell : ℂ) * etaDenom M τ) /
            (M 1 0 : ℂ)) h ell = etaDenom M τ := by
        unfold G1RatioTail.complexS
        field_simp
        ring
      rw [heq, div_self hT]
      norm_num
    · have heq : G1RatioTail.complexL M τ
          ((etaDenom M τ - (h : ℂ) - (ell : ℂ) * etaDenom M τ) / (M 1 0 : ℂ))
          ((-1 - (p : ℂ)) * etaDenom M τ / (M 1 0 : ℂ)) h ell p =
          -etaDenom M τ := by
        unfold G1RatioTail.complexL G1RatioTail.complexS
        field_simp
        ring
      rw [heq, neg_div, div_self hT]
      norm_num

/-- G03. Complex version. [RW26, p. 6, p. 29]. -/
theorem crossSeparated_iff_deleted_hyperplanes (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n h ell p : ℤ) :
    (∀ m : Fin (M 1 0).toNat,
      ModularCluster.crossSeparated M (G1Pinch.ratioData w y n h ell p (m : ℤ)) τ) ↔
      ∀ k ∈ pinchLabels M p, (w, y) ∉ pinchHyperplane M τ p k := by
  constructor
  · intro hs k hk heq
    change y = pinchValue M τ p k at heq
    obtain ⟨m, hm, _⟩ := G1Pinch.exists_unique_baseIndex M hM n
    apply (crossSeparated_iff_no_collision M τ w y n h ell p (m : ℤ)).mp (hs m)
      0 0 k.1 k.2
    · change Int.ModEq (M 1 0) ((0 : ℤ) + M 1 1 * 0)
        (M 1 1 * ((m : ℤ) + 1 - 1) - n)
      convert (hm.sub (Int.ModEq.refl n)).symm using 1 <;> ring
    · change Int.ModEq (M 1 0) ((k.2 : ℤ) + M 1 1 * (k.1 : ℤ))
        (n - 1 - M 1 1 * ((m : ℤ) + p))
      change Int.ModEq (M 1 0) ((k.2 : ℤ) + M 1 1 * (k.1 : ℤ))
        (-1 - M 1 1 * p) at hk
      convert hk.add (hm.sub (Int.ModEq.refl (M 1 1 * (m : ℤ)))) using 1 <;> ring
    · apply (collision_iff M hM τ y n p (m : ℤ) 0 0 k.1 k.2).mpr
      simpa only [Nat.zero_add, pinchValue] using heq
  · intro hn m
    apply (crossSeparated_iff_no_collision M τ w y n h ell p (m : ℤ)).mpr
    intro K J K' J' hP hZ heq
    apply hn (K + K', J + J') (sum_label M n p (m : ℤ) K J K' J' hP hZ)
    exact (collision_iff M hM τ y n p (m : ℤ) K J K' J').mp heq

/-- G04. Exact old predicate, including rational T₀ and merged labels. [RW26, p. 6]. -/
theorem real_deleted_iff_noPinch (M : SL(2, ℤ)) (τ y : ℝ) (w : ℂ) (p : ℤ) :
    (∀ k ∈ pinchLabels M p, (w, (y : ℂ)) ∉ pinchHyperplane M (τ : ℂ) p k) ↔
      g1NoPinch M τ y p := by
  simp only [pinchLabels, pinchHyperplane, pinchValue, Set.mem_ofPred_eq,
    G1PinchGeometryAux.etaDenom_ofReal, g1NoPinch]
  constructor
  · intro h K J hlabel heq
    apply h (K, J) hlabel
    exact_mod_cast heq
  · intro h k hlabel heq
    apply h k.1 k.2 hlabel
    exact_mod_cast heq

/-- G05. Joint labeled local finiteness, stronger than just fixed τ. [RW26, p. 29]. -/
theorem pinch_joint_compact_finite (M : SL(2, ℤ)) (hM : 0 < M 1 0) (p : ℤ)
    (K : Set Parameters) (hK : IsCompact K)
    (hT : ∀ x ∈ K, 0 < (etaDenom M x.1).re) :
    {k | k ∈ pinchLabels M p ∧ ∃ x ∈ K, x.2.2 = pinchValue M x.1 p k}.Finite := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  -- Compactness gives one positive lower bound before any label is chosen.
  obtain ⟨a, ha, haK⟩ := hK.exists_forall_le'
    (show ContinuousOn (fun x : Parameters => (etaDenom M x.1).re) K by
      unfold etaDenom; fun_prop) hT
  let B : Parameters → ℝ := fun x =>
    (-(M 1 0 : ℂ) * x.2.2 - (p : ℂ) * etaDenom M x.1 - 1).re
  obtain ⟨b, hb⟩ := hK.bddAbove_image
    (show ContinuousOn B K by dsimp [B]; unfold etaDenom; fun_prop)
  obtain ⟨N, hN⟩ := exists_nat_gt (b / min a 1)
  apply (Set.finite_Iic (N, N)).subset
  rintro k ⟨hk, x, hx, heq⟩
  have heq' : (k.1 : ℝ) * (etaDenom M x.1).re + (k.2 : ℝ) = B x := by
    have hcomplex : (k.1 : ℂ) * etaDenom M x.1 + (k.2 : ℂ) =
        -(M 1 0 : ℂ) * x.2.2 - (p : ℂ) * etaDenom M x.1 - 1 := by
      rw [heq]
      unfold pinchValue
      field_simp
      ring
    have hh := congrArg Complex.re hcomplex
    simpa [B] using hh
  have hB : B x ≤ b := hb ⟨x, hx, rfl⟩
  have hmin : 0 < min a 1 := lt_min ha zero_lt_one
  have hNb : b < (N : ℝ) * min a 1 := (div_lt_iff₀ hmin).1 hN
  have ha' := haK x hx
  have hk0 : (0 : ℝ) ≤ (k.1 : ℝ) := Nat.cast_nonneg _
  have hk1 : (0 : ℝ) ≤ (k.2 : ℝ) := Nat.cast_nonneg _
  have hka : (k.1 : ℝ) * min a 1 ≤ (k.1 : ℝ) * (etaDenom M x.1).re :=
    mul_le_mul_of_nonneg_left (le_trans (min_le_left _ _) ha') hk0
  have hkj : (k.2 : ℝ) * min a 1 ≤ (k.2 : ℝ) :=
    mul_le_of_le_one_right hk1 (min_le_right _ _)
  constructor <;> apply Nat.le_of_lt <;> apply Nat.cast_lt (α := ℝ) |>.mp <;> nlinarith

/-- G06. The deleted target is an ordinary open set, not a punctured germ. [RW26, p. 29]. -/
theorem ratio_fiber_and_tube_open (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hT : 0 < (etaDenom M τ).re) (n h ell p : ℤ) (ψ : ℝ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    IsOpen (ratioFiber M τ n h ell p) ∧ IsOpen (ratioTube M n h ell p ψ) := by
  have _ := hψ
  let D : Set Parameters := {x | 0 < (etaDenom M x.1).re ∧
    x.2 ∈ strictRatioWindow M x.1 h ell p}
  have hD : IsOpen D := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hden : etaDenom M x.1 ≠ 0 := by
      intro hz
      have := hx.1
      simp [hz] at this
    have hcT : Continuous (fun z : Parameters => (etaDenom M z.1).re) := by fun_prop
    have hcS : ContinuousAt (fun z : Parameters =>
        (G1RatioTail.complexS M z.1 z.2.1 h ell / etaDenom M z.1).re) x := by
      unfold G1RatioTail.complexS
      fun_prop (disch := assumption)
    have hcL : ContinuousAt (fun z : Parameters =>
        (G1RatioTail.complexL M z.1 z.2.1 z.2.2 h ell p / etaDenom M z.1).re) x := by
      unfold G1RatioTail.complexL G1RatioTail.complexS
      fun_prop (disch := assumption)
    filter_upwards [hcT.continuousAt.eventually (lt_mem_nhds hx.1),
      hcS.eventually (lt_mem_nhds hx.2.1), hcL.eventually (gt_mem_nhds hx.2.2)]
      with z hzT hzS hzL
    exact ⟨hzT, hzS, hzL⟩
  let A : (ℕ × ℕ) → Set Parameters := fun k =>
    {x | k ∈ pinchLabels M p ∧ x.2.2 = pinchValue M x.1 p k}
  have hA : ∀ k, IsClosed (A k) := by
    intro k
    by_cases hk : k ∈ pinchLabels M p
    · simpa [A, hk] using (isClosed_eq (f := fun x : Parameters => x.2.2)
        (g := fun x => pinchValue M x.1 p k) (by fun_prop)
        (by unfold pinchValue; fun_prop))
    · simp [A, hk]
  let W : Set Parameters := {x | x ∈ D ∧ ∀ k, x ∉ A k}
  have hW : IsOpen W := by
    apply G1ContinuationGeometryAux.isOpen_delete_of_compact_finite D hD A hA
    intro K hK hKD
    have hfin := pinch_joint_compact_finite M hM p K hK (fun x hx => (hKD hx).1)
    apply hfin.subset
    rintro k ⟨x, hxK, hk, hx⟩
    exact ⟨hk, x, hxK, hx⟩
  have hWeq (x : Parameters) : x ∈ W ↔
      0 < (etaDenom M x.1).re ∧ x.2 ∈ ratioFiber M x.1 n h ell p := by
    constructor
    · rintro ⟨hx, ha⟩
      refine ⟨hx.1, hx.2, ?_⟩
      apply (crossSeparated_iff_deleted_hyperplanes M hM x.1 x.2.1 x.2.2 n h ell p).mpr
      intro k hk heq
      exact ha k ⟨hk, heq⟩
    · rintro ⟨hpos, hstrict, hcross⟩
      refine ⟨⟨hpos, hstrict⟩, ?_⟩
      rintro k ⟨hk, heq⟩
      exact (crossSeparated_iff_deleted_hyperplanes M hM x.1 x.2.1 x.2.2 n h ell p).mp
        hcross k hk heq
  constructor
  · have heq : ratioFiber M τ n h ell p =
        (fun v : ℂ × ℂ => (τ, v)) ⁻¹' W := by
      ext v
      rw [mem_preimage, hWeq]
      simp only [hT, true_and]
    rw [heq]
    exact hW.preimage (continuous_const.prodMk continuous_id)
  · have heq : ratioTube M n h ell p ψ =
        {x : Parameters | x.1 ∈ UpperWindow.tauRegion M ψ} ∩ W := by
      ext x
      rw [mem_inter_iff, hWeq]
      constructor
      · intro hx
        exact ⟨hx.1, (UpperWindow.tauRegion_properties M hM ψ hψ' x.1 hx.1).2.2.1, hx.2⟩
      · rintro ⟨hτ, hpos, hf⟩
        exact ⟨hτ, hf⟩
    rw [heq]
    exact ((UpperWindow.tauRegion_isOpen M hM ψ).preimage continuous_fst).inter hW

/-- G07. Only finitely many forbidden hyperplanes meet the compact straight path. [RW26, p. 29]. -/
theorem segment_meets_finitely_many_pinches (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hT : 0 < (etaDenom M τ).re) (p : ℤ) (v₀ v₁ : ℂ × ℂ) :
    {k | k ∈ pinchLabels M p ∧ ∃ t ∈ Icc (0 : ℝ) 1,
      (1 - (t : ℂ)) • v₀ + (t : ℂ) • v₁ ∈ pinchHyperplane M τ p k}.Finite := by
  let f : ℝ → Parameters := fun t => (τ, (1 - (t : ℂ)) • v₀ + (t : ℂ) • v₁)
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hfinite := pinch_joint_compact_finite M hM p (f '' Icc (0 : ℝ) 1)
    (isCompact_Icc.image hfc) (by rintro x ⟨t, ht, rfl⟩; exact hT)
  refine hfinite.subset ?_
  rintro k ⟨hk, t, ht, hp⟩
  exact ⟨hk, f t, mem_image_of_mem f ht, hp⟩

/-- G08. A small complex semicircle avoids all pinches, even a merged center. [RW26, p. 29]. This is
a geometric output, not an assumed detour. -/
theorem small_complex_detour (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hT : 0 < (etaDenom M τ).re) (n h ell p : ℤ)
    (v : ℂ × ℂ) (hv : v ∈ strictRatioWindow M τ h ell p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      detourPoint v r θ ∈ ratioFiber M τ n h ell p ∧ dist (detourPoint v r θ) v < ε := by
  let K : Set Parameters := {τ} ×ˢ ({v.1} ×ˢ Metric.closedBall v.2 1)
  have hK : IsCompact K := isCompact_singleton.prod
    (isCompact_singleton.prod (isCompact_closedBall _ _))
  have hKT : ∀ x ∈ K, 0 < (etaDenom M x.1).re := by
    rintro x ⟨hx, _⟩
    simpa only [mem_singleton_iff.mp hx] using hT
  let F : Set (ℕ × ℕ) :=
    {k | k ∈ pinchLabels M p ∧ ∃ x ∈ K, x.2.2 = pinchValue M x.1 p k}
  have hF : F.Finite := pinch_joint_compact_finite M hM p K hK hKT
  let V : Set ℂ := (pinchValue M τ p '' F) \ {v.2}
  -- Removing the center value handles all labels merging at that center.
  have hV : V.Finite := (hF.image _).sdiff
  have hvV : v.2 ∈ Vᶜ := by simp [V]
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hV.isClosed.isOpen_compl.mem_nhds hvV)
  have hden : etaDenom M τ ≠ 0 := by
    intro hz
    simp [hz] at hT
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.mp
    ((strict_ratio_open_convex_nonempty M hM τ hden h ell p).1.mem_nhds hv)
  let r : ℝ := min ε (min 1 (min δ η)) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r < ε := by
    have := min_le_left ε (min 1 (min δ η))
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    have := (min_le_right ε (min 1 (min δ η))).trans (min_le_left 1 (min δ η))
    dsimp [r]
    linarith
  have hrδ : r < δ := by
    have := ((min_le_right ε (min 1 (min δ η))).trans
      (min_le_right 1 (min δ η))).trans (min_le_left δ η)
    dsimp [r]
    linarith
  have hrη : r < η := by
    have := ((min_le_right ε (min 1 (min δ η))).trans
      (min_le_right 1 (min δ η))).trans (min_le_right δ η)
    dsimp [r]
    linarith
  refine ⟨r, hr, hre, ?_⟩
  intro θ _
  have hdistY : dist (detourPoint v r θ).2 v.2 = r := by
    simp [detourPoint, dist_eq_norm, Complex.norm_exp_I_mul_ofReal,
      Complex.norm_real, abs_of_pos hr]
  have hdist : dist (detourPoint v r θ) v = r := by
    change max (dist v.1 v.1) (dist (detourPoint v r θ).2 v.2) = r
    simp [hdistY, hr.le]
  refine ⟨⟨hηU (by simpa [Metric.mem_ball, hdist] using hrη), ?_⟩,
    by simpa [hdist] using hre⟩
  apply (crossSeparated_iff_deleted_hyperplanes M hM τ v.1
    (detourPoint v r θ).2 n h ell p).mpr
  intro k hk hpinch
  have heq : (detourPoint v r θ).2 = pinchValue M τ p k := hpinch
  have hkF : k ∈ F := by
    refine ⟨hk, (τ, detourPoint v r θ), ?_, heq⟩
    exact ⟨rfl, rfl, by simpa [Metric.mem_closedBall, hdistY] using hr1.le⟩
  have hyV : (detourPoint v r θ).2 ∈ Vᶜ :=
    hδV (by simpa [Metric.mem_ball, hdistY] using hrδ)
  apply hyV
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact mem_image_of_mem _ hkF
  · simp only [mem_singleton_iff]
    intro heq'
    have : r = 0 := by simpa [heq'] using hdistY.symm
    exact hr.ne' this

/-- G09. Actual finite polygon, with every segment avoiding every hyperplane. [RW26, p. 29]. -/
theorem polygonal_route_exists (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hT : 0 < (etaDenom M τ).re) (n h ell p : ℤ)
    (v₀ v₁ : ℂ × ℂ) (hv₀ : v₀ ∈ ratioFiber M τ n h ell p)
    (hv₁ : v₁ ∈ ratioFiber M τ n h ell p) :
    ∃ P : Polygon, PolygonIn P (ratioFiber M τ n h ell p) v₀ v₁ := by
  have hden : etaDenom M τ ≠ 0 := by
    intro heq
    simp [heq] at hT
  have hU := strict_ratio_open_convex_nonempty M hM τ hden h ell p
  have h₀ := (crossSeparated_iff_deleted_hyperplanes M hM τ v₀.1 v₀.2 n h ell p).mp hv₀.2
  have h₁ := (crossSeparated_iff_deleted_hyperplanes M hM τ v₁.1 v₁.2 n h ell p).mp hv₁.2
  -- One Baire choice avoids the bad real lines from both endpoints.
  obtain ⟨u, hu, hleft, hright⟩ :=
    G1ContinuationGeometryAux.exists_two_segment_avoiding_countable
      (fun k : {k // k ∈ pinchLabels M p} => pinchValue M τ p k.val)
      hU.1 hU.2.1 hv₀.1 hv₁.1
      (fun k => h₀ k.val k.property) (fun k => h₁ k.val k.property)
  have hmem (z : ℂ × ℂ) (hz : z ∈ strictRatioWindow M τ h ell p)
      (hne : ∀ k : {k // k ∈ pinchLabels M p}, z.2 ≠ pinchValue M τ p k.val) :
      z ∈ ratioFiber M τ n h ell p := by
    refine ⟨hz, (crossSeparated_iff_deleted_hyperplanes M hM τ z.1 z.2 n h ell p).mpr ?_⟩
    intro k hk
    exact hne ⟨k, hk⟩
  let P : Polygon := ⟨2, ![v₀, u, v₁]⟩
  refine ⟨P, by norm_num [P], rfl, rfl, ?_⟩
  intro i t ht
  fin_cases i
  · exact hmem _ (hleft t ht).1 (hleft t ht).2
  · exact hmem _ (hright t ht).1 (hright t ht).2

/-- G10. Common positive clearance precedes every path point and every label. [RW26, p. 29]. -/
theorem route_uniform_clearance (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hT : 0 < (etaDenom M τ).re) (n h ell p : ℤ)
    (v₀ v₁ : ℂ × ℂ) (P : Polygon)
    (hP : PolygonIn P (ratioFiber M τ n h ell p) v₀ v₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : Fin P.length, ∀ t ∈ Icc (0 : ℝ) 1,
      let v := polygonPoint P i t
      ε ≤ (G1RatioTail.complexS M τ v.1 h ell / etaDenom M τ).re ∧
      ε ≤ -(G1RatioTail.complexL M τ v.1 v.2 h ell p / etaDenom M τ).re ∧
      ∀ k ∈ pinchLabels M p, ε ≤ ‖v.2 - pinchValue M τ p k‖ := by
  let K : Set (ℂ × ℂ) := ⋃ i : Fin P.length,
    (fun t : ℝ => polygonPoint P i t) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    apply isCompact_Icc.image
    unfold polygonPoint
    fun_prop
  have hKU : K ⊆ ratioFiber M τ n h ell p := by
    intro v hv
    rcases mem_iUnion.mp hv with ⟨i, t, ht, rfl⟩
    exact hP.2.2.2 i t ht
  have hden : etaDenom M τ ≠ 0 := by
    intro hz
    simp [hz] at hT
  obtain ⟨a, ha, hsa⟩ := hK.exists_forall_le'
    (f := fun v : ℂ × ℂ =>
      (G1RatioTail.complexS M τ v.1 h ell / etaDenom M τ).re)
    (by unfold G1RatioTail.complexS; fun_prop)
    (fun v hv => (hKU hv).1.1)
  obtain ⟨b, hb, hlb⟩ := hK.exists_forall_le'
    (f := fun v : ℂ × ℂ =>
      -(G1RatioTail.complexL M τ v.1 v.2 h ell p / etaDenom M τ).re)
    (by unfold G1RatioTail.complexL G1RatioTail.complexS; fun_prop)
    (fun v hv => neg_pos.mpr (hKU hv).1.2)
  -- A neighborhood of the entire compact path excludes every pinch value.
  obtain ⟨c, hc, hcc⟩ := hK.exists_thickening_subset_open
    (ratio_fiber_and_tube_open M hM τ hT n h ell p (Real.pi / 8)
      (by positivity) (by nlinarith [Real.pi_pos])).1 hKU
  refine ⟨min a (min b c), lt_min ha (lt_min hb hc), ?_⟩
  intro i t ht
  have hvK : polygonPoint P i t ∈ K := mem_iUnion.mpr ⟨i, t, ht, rfl⟩
  refine ⟨(min_le_left _ _).trans (hsa _ hvK),
    ((min_le_right _ _).trans (min_le_left _ _)).trans (hlb _ hvK), ?_⟩
  intro k hk
  apply le_trans ((min_le_right _ _).trans (min_le_right _ _))
  by_contra! hdist
  have hdist' : dist ((polygonPoint P i t).1, pinchValue M τ p k)
      (polygonPoint P i t) < c := by
    change dist ((polygonPoint P i t).1, pinchValue M τ p k)
      ((polygonPoint P i t).1, (polygonPoint P i t).2) < c
    rw [dist_prod_same_left, dist_eq_norm, norm_sub_rev]
    exact hdist
  have hf := hcc (Metric.mem_thickening_iff.mpr ⟨polygonPoint P i t, hvK, hdist'⟩)
  have hd := (crossSeparated_iff_deleted_hyperplanes M hM τ
    (polygonPoint P i t).1 (pinchValue M τ p k) n h ell p).mp hf.2 k hk
  exact hd rfl

/-- G11. The actual fixed-τ seed sits inside the target, and is nonempty. [RW26, p. 28, p. 29]. -/
theorem initial_fibers_inside_target (M : SL(2, ℤ)) (n h ell p : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (τ : ℂ) (hτ : τ ∈ UpperWindow.tauRegion M ψ) :
    (∃ w : ℂ, (τ, w) ∈ UpperIntegralIdentities.singleDomain M h ell ψ σ ρ δ) ∧
    (∀ w, (τ, w) ∈ UpperIntegralIdentities.singleDomain M h ell ψ σ ρ δ →
      w ∈ singleWindow M τ h ell) ∧
    (∃ v : ℂ × ℂ, (τ, v) ∈ UpperWindow.domain M h ell p ψ σ ρ δ) ∧
    (∀ v, (τ, v) ∈ UpperWindow.domain M h ell p ψ σ ρ δ →
      v ∈ ratioFiber M τ n h ell p) := by
  have hcenter := UpperWindow.center_mem_domain M h ell p ψ σ ρ δ hc τ hτ
  refine ⟨⟨UpperWindow.centerW M h ell σ τ, hcenter.1, hcenter.2.1,
      hcenter.2.2.1⟩, ?_,
    ⟨(UpperWindow.centerW M h ell σ τ, UpperWindow.centerY M p ρ τ), hcenter⟩, ?_⟩
  · intro w hw
    have him : (etaDenom M τ).im ≠ 0 :=
      (im_etaDenom_pos_of_im_pos M hc.1 hτ.1).ne'
    have heq := (UpperWindow.center_equations M hc.1 h ell 0 σ ρ τ).2
    have hH : UpperWindow.coords (etaDenom M τ)
        (UpperWindow.height M 0 τ (UpperWindow.centerY M 0 ρ τ)) = (ρ, ρ) := by
      rw [heq]
      simpa only [mul_add, mul_one] using
        UpperWindow.coords_real_combination (etaDenom M τ) him ρ ρ
    have hr := (UpperWindow.radius_margins M ψ σ ρ δ hc).1
    have hlift : (τ, w, UpperWindow.centerY M 0 ρ τ) ∈
        UpperWindow.domain M h ell 0 ψ σ ρ δ := by
      refine ⟨hw.1, hw.2.1, hw.2.2, ?_, ?_⟩ <;>
        simpa only [hH, sub_self, abs_zero] using hr
    exact (seed_strict M h ell 0 ψ σ ρ δ hc _ hlift).1
  · intro v hv
    refine ⟨seed_strict M h ell p ψ σ ρ δ hc (τ, v) hv, ?_⟩
    intro m
    apply (crossSeparated_iff_no_collision M τ v.1 v.2 n h ell p (m : ℤ)).mpr
    intro K J K' J' hP hZ heq
    have hd := UpperWindow.no_pinch M h ell p (m : ℤ) n ψ σ ρ δ hc (τ, v) hv
    exact Set.disjoint_left.mp hd ⟨(K, J), hP, rfl⟩ ⟨(K', J'), hZ, heq.symm⟩

/-- G12. The single-function continuation uses an actual segment in w. [RW26, p. 29]. -/
theorem single_segment_inside_window (M : SL(2, ℤ)) (τ : ℂ) (h ell : ℤ)
    (w₀ w₁ : ℂ) (hw₀ : w₀ ∈ singleWindow M τ h ell)
    (hw₁ : w₁ ∈ singleWindow M τ h ell) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - (t : ℂ)) * w₀ + (t : ℂ) * w₁ ∈ singleWindow M τ h ell := by
  intro t ht
  have hh := (single_window_open_convex M τ h ell).2 hw₀ hw₁
    (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  simpa only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one] using hh

#check @G1Pinch.noPinch_iff_all_crossSeparated
#check @UpperIntegralIdentities.initial_fibers
#check @ModularCluster.crossSeparated
#print ratioFiber
#print pinchValue
#print PolygonIn

end SICLean.L4.G1Continuation
