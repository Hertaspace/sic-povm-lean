import SICLean.L4.G1BilateralSeparation
import SICLean.L4.G1BilateralRatioTailsAux

set_option autoImplicit false

/-!
# Ratio tails, dominated chains and ordinary limits

Bilateral tail and fixed-chain theorems. Tail bounds do not require no-pinch;
compact/whole-chain assertions take the contract's exact geometric separation for a fixed finite
family. The radius may depend on that family. Every full disk includes lower-half-plane parameters.

[RW26, p. 6, p. 7, p. 13, pp. 28--29, Appendix A.2]. Bilateral uniformity and the ordinary integral
limit are formalized here. Full-disk statements are included. No integral equality to g1Prefactor or
any right side is asserted.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1BilateralRatioTails

open G1BilateralRatioTailsAux

/-- Concrete compact-middle plus two-tail majorant on the full real line. -/
def verticalMajorant (C κ R t : ℝ) : ℝ :=
  if |t| ≤ R then C else C * Real.exp (-κ * |t|)

/-- R01. Common upper-strip decay on a full disk, for finite components. [RW26, p. 7, p. 13]. Only
s>0 is needed. -/
theorem uniform_upper_strip (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (hs : 0 < g1S M τ₀ w h ell) (hab : a ≤ b) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
        ∀ x ∈ Icc a b, ∀ t : ℝ, R ≤ t →
          ‖G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m
            (g1VerticalPoint x t)‖ ≤ C * Real.exp (-κ * t) := by
  obtain ⟨ρw, κw, hρw, hκw, hw⟩ :=
    G1BilateralGeometry.single_window_margin M hM τ₀ w h ell hT hs
  obtain ⟨ρ, C, κ, R, hρ, hC, hκ, hR, hb⟩ := uniform_tail_bound M hM
    τ₀ w y a b n h ell p F hT false ⟨ρw, κw, hρw, hκw, fun τ hτ =>
      ⟨(hw τ hτ).1, (hw τ hτ).2.2⟩⟩
  refine ⟨ρ, C, κ, R, hρ, hC, hκ, hR, ?_⟩
  intro τ hτ m hm x hx t ht
  have ht0 : 0 ≤ t := hR.le.trans ht
  simpa only [abs_of_nonneg ht0] using
    hb τ hτ m hm x hx t (by simpa only [abs_of_nonneg ht0] using ht) ht0

/-- R02. Lower-strip decay with exponent +κt for negative t. Quadratic terms cancel using the
existing exact reflection-difference theorem. [RW26, p. 6, p. 7]. -/
theorem uniform_lower_strip (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (hL : g1L M τ₀ w y h ell p < 0) (hab : a ≤ b) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F,
        ∀ x ∈ Icc a b, ∀ t : ℝ, t ≤ -R →
          ‖G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m
            (g1VerticalPoint x t)‖ ≤ C * Real.exp (κ * t) := by
  obtain ⟨ρw, κw, hρw, hκw, hw⟩ := lower_window_margin M hM τ₀ w y h ell p hT hL
  obtain ⟨ρ, C, κ, R, hρ, hC, hκ, hR, hb⟩ := uniform_tail_bound M hM
    τ₀ w y a b n h ell p F hT true ⟨ρw, κw, hρw, hκw, fun τ hτ =>
      ⟨(hw τ hτ).1, (hw τ hτ).2.2⟩⟩
  refine ⟨ρ, C, κ, R, hρ, hC, hκ, hR, ?_⟩
  intro τ hτ m hm x hx t ht
  have ht0 : t ≤ 0 := by linarith
  have hmag : R ≤ |t| := by rw [abs_of_nonpos ht0]; linarith
  have hb' := hb τ hτ m hm x hx t hmag ht0
  simpa only [abs_of_nonpos ht0, mul_neg, neg_mul, neg_neg] using hb'

/-- R03. One disk and rate control both strict complex windows and tails. [RW26, p. 7, p. 13]. -/
theorem uniform_two_tail_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (hs : 0 < g1S M τ₀ w h ell)
    (hL : g1L M τ₀ w y h ell p < 0) (hab : a ≤ b) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
        τ ∈ modularPhiDomain M ∧
        κ ≤ 2 * Real.pi *
          (G1RatioTail.complexS M τ (w : ℂ) h ell / etaDenom M τ).re ∧
        κ ≤ -(2 * Real.pi *
          (G1RatioTail.complexL M τ (w : ℂ) (y : ℂ) h ell p / etaDenom M τ).re) ∧
        ∀ m ∈ F, ∀ x ∈ Icc a b, ∀ t : ℝ, R ≤ |t| →
          ‖G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m
            (g1VerticalPoint x t)‖ ≤ C * Real.exp (-κ * |t|) := by
  obtain ⟨ρu, Cu, κu, Ru, hρu, hCu, hκu, hRu, hu⟩ :=
    uniform_upper_strip M hM τ₀ w y a b n h ell p F hT hs hab
  obtain ⟨ρl, Cl, κl, Rl, hρl, hCl, hκl, hRl, hl⟩ :=
    uniform_lower_strip M hM τ₀ w y a b n h ell p F hT hL hab
  obtain ⟨ρw, κw, hρw, hκw, hw⟩ :=
    G1BilateralGeometry.ratio_window_margin M hM τ₀ w y h ell p hT hs hL
  let ρ := min ρu (min ρl ρw)
  let κ := min κu (min κl κw)
  have hκu' : κ ≤ κu := min_le_left _ _
  have hκl' : κ ≤ κl := (min_le_right _ _).trans (min_le_left _ _)
  have hκw' : κ ≤ κw := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, max Cu Cl, κ, max Ru Rl, lt_min hρu (lt_min hρl hρw),
    lt_of_lt_of_le hCu (le_max_left _ _), lt_min hκu (lt_min hκl hκw),
    lt_of_lt_of_le hRu (le_max_left _ _), ?_⟩
  intro τ hτ
  have hτu := disk_mono (min_le_left ρu (min ρl ρw)) hτ
  have hτl := disk_mono ((min_le_right ρu (min ρl ρw)).trans (min_le_left ρl ρw)) hτ
  have hτw := disk_mono ((min_le_right ρu (min ρl ρw)).trans (min_le_right ρl ρw)) hτ
  obtain ⟨hd, _, hwu, hwl⟩ := hw τ hτw
  refine ⟨hd, hκw'.trans hwu, hκw'.trans hwl, ?_⟩
  intro m hm x hx t ht
  by_cases ht0 : 0 ≤ t
  · have htR : Ru ≤ t := by simpa only [abs_of_nonneg ht0] using (le_max_left Ru Rl).trans ht
    have hb := hu τ hτu m hm x hx t htR
    exact hb.trans (by
      simpa only [abs_of_nonneg ht0] using
        decay_mono hCu.le (le_max_left Cu Cl) hκu' (abs_nonneg t))
  · have ht0' : t ≤ 0 := le_of_not_ge ht0
    have htR : t ≤ -Rl := by
      have := (le_max_right Ru Rl).trans ht
      rw [abs_of_nonpos ht0'] at this
      linarith
    have hb := hl τ hτl m hm x hx t htR
    have he : κl * t = -κl * |t| := by rw [abs_of_nonpos ht0']; ring
    rw [he] at hb
    exact hb.trans (decay_mono hCl.le (le_max_right _ _) hκl' (abs_nonneg t))

/-- R04. Both finite closing edges are integrable and their integrals have the stated decay; segment
length is retained. [RW26, p. 13, pp. 28--29]. -/
theorem uniform_horizontal_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y a b : ℝ) (n h ell p : ℤ) (F : Finset ℤ)
    (hT : 0 < g1T M τ₀) (hs : 0 < g1S M τ₀ w h ell)
    (hL : g1L M τ₀ w y h ell p < 0) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m ∈ F, ∀ t : ℝ, R ≤ |t| →
        IntervalIntegrable (fun x : ℝ =>
          G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m
            (g1VerticalPoint x t)) volume a b ∧
        ‖G1RatioTail.horizontalIntegral
          (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m) a b t‖ ≤
            |b - a| * C * Real.exp (-κ * |t|) := by
  obtain ⟨ρ, C, κ, R, hρ, hC, hκ, hR, hb⟩ := uniform_two_tail_bound M hM
    τ₀ w y (min a b) (max a b) n h ell p F hT hs hL (min_le_max : min a b ≤ max a b)
  refine ⟨ρ, C, κ, R, hρ, hC, hκ, hR, ?_⟩
  intro τ hτ m hm t ht
  have hpoint : ∀ x ∈ Set.uIcc a b,
      ‖G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m
        (g1VerticalPoint x t)‖ ≤ C * Real.exp (-κ * |t|) := by
    intro x hx
    exact (hb τ hτ).2.2.2 m hm x hx t ht
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m
        (g1VerticalPoint x t)) (volume.restrict (Set.uIcc a b)) :=
    ((kernel_measurable M hM τ (w : ℂ) (y : ℂ) n h ell p m (hb τ hτ).1).comp
      (show Measurable (fun x : ℝ => g1VerticalPoint x t) by unfold g1VerticalPoint; fun_prop)).aestronglyMeasurable
  have hi : IntegrableOn (fun x : ℝ =>
      G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p m
        (g1VerticalPoint x t)) (Set.uIcc a b) :=
    (integrableOn_const (s := Icc (min a b) (max a b))
      (C := C * Real.exp (-κ * |t|)) (μ := volume)
      (by simp only [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono' hmeas
      ((ae_restrict_mem measurableSet_uIcc).mono hpoint)
  refine ⟨hi.intervalIntegrable, ?_⟩
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hpoint x (Set.uIoc_subset_uIcc hx))
  simpa only [G1RatioTail.horizontalIntegral, mul_comm, mul_left_comm, mul_assoc] using hn

/-- R05. The compact middle on each fixed contract baseline is controlled on one full disk. No tail
window is needed for this compact assertion. [RW26, p. 6]. -/
theorem family_compact_vertical_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y R : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀) (hR : 0 ≤ R)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m : Fin (M 1 0).toNat,
        ∀ t ∈ Icc (-R) R,
          ‖g1VerticalPullback
            (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
            (D m).crossing t‖ ≤ C := by
  obtain ⟨ρ, hρ, hreg⟩ :=
    G1BilateralSeparation.family_regular_tube M hM τ₀ w y n h ell p hT D hD
  let K := ModularSector.parameterDisk τ₀ ρ ×ˢ Icc (-R) R
  let f : Fin (M 1 0).toNat → (ℂ × ℝ) → ℂ := fun m q =>
    g1VerticalPullback
      (G1RatioTail.complexKernel M q.1 (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
      (D m).crossing q.2
  have hc : ∀ m ∈ Finset.univ, ContinuousOn (f m) K := by
    intro m _ q hq
    exact (vertical_joint_continuousAt M hM (w : ℂ) (y : ℂ) n h ell p (m : ℤ)
      (D m).crossing q.2 ((hreg q.1 hq.1 m).1 q.2)).continuousWithinAt
  obtain ⟨C, hC, hbound⟩ := finite_compact_bound Finset.univ K
    ((isCompact_closedBall _ _).prod isCompact_Icc) f hc
  exact ⟨ρ, C, hρ, hC, fun τ hτ m t ht => hbound m (Finset.mem_univ m) (τ, t) ⟨hτ, ht⟩⟩

/-- R06. Explicit nonnegative, integrable common full-line majorant for every baseline, including
the compact middle and the Jacobian. [RW26, p. 7]. -/
theorem family_vertical_majorant (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ ρ C κ R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      (∀ t : ℝ, 0 ≤ verticalMajorant C κ R t) ∧
      Integrable (verticalMajorant C κ R) ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m : Fin (M 1 0).toNat, ∀ t : ℝ,
        ‖g1VerticalPullback
          (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
          (D m).crossing t‖ ≤ verticalMajorant C κ R t := by
  let A := ∑ m : Fin (M 1 0).toNat, |(D m).crossing|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcross (m : Fin (M 1 0).toNat) : (D m).crossing ∈ Icc (-A) A := by
    have hm : |(D m).crossing| ≤ A := Finset.single_le_sum
      (fun m _ => abs_nonneg (D m).crossing) (Finset.mem_univ m)
    exact abs_le.mp hm
  let F : Finset ℤ := Finset.univ.image (fun m : Fin (M 1 0).toNat => (m : ℤ))
  have hF (m : Fin (M 1 0).toNat) : (m : ℤ) ∈ F :=
    Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
  obtain ⟨ρt, Ct, κ, R, hρt, hCt, hκ, hR, ht⟩ := uniform_two_tail_bound M hM
    τ₀ w y (-A) A n h ell p F hT hs hL (by linarith)
  obtain ⟨ρc, Cc, hρc, hCc, hc⟩ := family_compact_vertical_bound M hM
    τ₀ w y R n h ell p hT hR.le D hD
  refine ⟨min ρt ρc, max Ct Cc, κ, R, lt_min hρt hρc,
    lt_of_lt_of_le hCt (le_max_left _ _), hκ, hR, ?_, ?_, ?_⟩
  · intro t
    unfold verticalMajorant
    split_ifs <;> positivity
  · exact abs_majorant_integrable _ _ _ hκ
  · intro τ hτ m t
    by_cases hmid : |t| ≤ R
    · rw [verticalMajorant, if_pos hmid]
      exact (hc τ (disk_mono (min_le_right _ _) hτ) m t (abs_le.mp hmid)).trans
        (le_max_right _ _)
    · rw [verticalMajorant, if_neg hmid, norm_vertical]
      exact ((ht τ (disk_mono (min_le_left _ _) hτ)).2.2.2 (m : ℤ) (hF m)
        (D m).crossing (hcross m) t (le_of_not_ge hmid)).trans
          (decay_mono hCt.le (le_max_left _ _) le_rfl (abs_nonneg t))

/-- R07. Explicit integrable circle majorant, simultaneously for all components and circles; no
simplicity assumption at enclosed poles. [RW26, p. 6]. -/
theorem family_circle_majorant (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      IntervalIntegrable (fun _ : ℝ => C) volume 0 (2 * Real.pi) ∧
      ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ, ∀ m : Fin (M 1 0).toNat,
        ∀ r ∈ (D m).centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖g1CirclePullback
            (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
            r ((D m).radius r) θ‖ ≤ C := by
  obtain ⟨ρ, C, hρ, hC, hb⟩ :=
    G1BilateralSeparation.family_circle_bound M hM τ₀ w y n h ell p hT D hD
  exact ⟨ρ, C, hρ, hC, intervalIntegrable_const, hb⟩

/-- R08. G1ChainIntegrable is proved as an output throughout the full disk. [RW26, p. 7, (23)]. -/
theorem family_chain_integrable (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ ∈ ModularSector.parameterDisk τ₀ ρ,
      ∀ m : Fin (M 1 0).toNat,
        G1ChainIntegrable (D m)
          (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ)) := by
  obtain ⟨ρv, C, κ, R, hρv, _, _, _, _, hi, hb⟩ :=
    family_vertical_majorant M hM τ₀ w y n h ell p hT hs hL D hD
  obtain ⟨ρr, hρr, hr⟩ :=
    G1BilateralSeparation.family_regular_tube M hM τ₀ w y n h ell p hT D hD
  refine ⟨min ρv ρr, lt_min hρv hρr, ?_⟩
  intro τ hτ m
  have hτv := disk_mono (min_le_left ρv ρr) hτ
  have hτr := disk_mono (min_le_right ρv ρr) hτ
  refine ⟨hi.mono' (vertical_continuous M hM τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ)
    (D m).crossing (hr τ hτr m).1).aestronglyMeasurable
      (Eventually.of_forall (hb τ hτv m)), ?_⟩
  intro r hrmem
  have hc : Continuous (g1CirclePullback
      (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
      r ((D m).radius r)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (circle_joint_continuousAt M hM (w : ℂ) (y : ℂ) n h ell p (m : ℤ)
      r ((D m).radius r) θ ((hr τ hτr m).2 r hrmem θ)).comp
        (f := fun θ : ℝ => (τ, θ)) (continuousAt_const.prodMk continuousAt_id)
  exact hc.intervalIntegrable _ _

/-- R09. Pointwise pullback limits to the same actual real representative. No value is inferred just
from a punctured-germ identity. [RW26, p. 6]. Full-neighborhood conclusion uses joint regularity. -/
theorem family_pullbacks_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∀ m : Fin (M 1 0).toNat,
      (∀ t : ℝ, Tendsto (fun τ : ℂ => g1VerticalPullback
        (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
        (D m).crossing t) (𝓝 (τ₀ : ℂ))
          (𝓝 (g1VerticalPullback (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))
            (D m).crossing t))) ∧
      (∀ r ∈ (D m).centers, ∀ θ : ℝ, Tendsto (fun τ : ℂ => g1CirclePullback
        (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
        r ((D m).radius r) θ) (𝓝 (τ₀ : ℂ))
          (𝓝 (g1CirclePullback (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))
            r ((D m).radius r) θ))) := by
  obtain ⟨ρ, hρ, hr⟩ :=
    G1BilateralSeparation.family_regular_tube M hM τ₀ w y n h ell p hT D hD
  have hτ := disk_self τ₀ ρ hρ.le
  intro m
  constructor
  · intro t
    have hc := (vertical_joint_continuousAt M hM (w : ℂ) (y : ℂ) n h ell p (m : ℤ)
      (D m).crossing t ((hr (τ₀ : ℂ) hτ m).1 t)).comp
        (f := fun τ : ℂ => (τ, t)) (continuousAt_id.prodMk continuousAt_const)
    simpa only [Function.comp_def, G1RatioTail.complexKernel_real] using hc.tendsto
  · intro r hrmem θ
    have hc := (circle_joint_continuousAt M hM (w : ℂ) (y : ℂ) n h ell p (m : ℤ)
      r ((D m).radius r) θ ((hr (τ₀ : ℂ) hτ m).2 r hrmem θ)).comp
        (f := fun τ : ℂ => (τ, θ)) (continuousAt_id.prodMk continuousAt_const)
    simpa only [Function.comp_def, G1RatioTail.complexKernel_real] using hc.tendsto

/-- R10. Each whole circle integral has full, upper and lower ordinary limits; no termwise
simple-residue limit is taken. [RW26, p. 6]. The proof uses
`circleContribution_tendsto{,_upper,_lower}`. -/
theorem family_circle_integral_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∀ m : Fin (M 1 0).toNat, ∀ r ∈ (D m).centers,
      let f := fun τ : ℂ => ∫ θ : ℝ in 0..(2 * Real.pi),
        g1CirclePullback
          (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
          r ((D m).radius r) θ
      let v := ∫ θ : ℝ in 0..(2 * Real.pi),
        g1CirclePullback (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))
          r ((D m).radius r) θ
      Tendsto f (𝓝 (τ₀ : ℂ)) (𝓝 v) ∧
        Tendsto f (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 v) ∧
        Tendsto f (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ)) (𝓝 v) := by
  obtain ⟨ρ, hρ, hreg⟩ :=
    G1BilateralSeparation.family_regular_tube M hM τ₀ w y n h ell p hT D hD
  intro m r hrmem
  have hrad : 0 < (D m).radius r := (hD m).1 r hrmem
  have hsafe : ∀ z ∈ Metric.sphere (r : ℂ) ((D m).radius r),
      (z, (τ₀ : ℂ)) ∈ ModularCluster.regularDomain M
        (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p (m : ℤ)) := by
    intro z hz
    have hz' : z ∈ Set.range (circleMap (r : ℂ) ((D m).radius r)) := by
      rw [range_circleMap, abs_of_pos hrad]
      exact hz
    obtain ⟨θ, rfl⟩ := hz'
    exact (hreg (τ₀ : ℂ) (disk_self τ₀ ρ hρ.le) m).2 r hrmem θ
  have hc := ModularCluster.circleContribution_tendsto M hM
    (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
    (τ₀ : ℂ) (r : ℂ) ((D m).radius r) hrad hsafe
  change Tendsto (fun τ : ℂ => ∫ θ : ℝ in 0..(2 * Real.pi),
      g1CirclePullback
        (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
        r ((D m).radius r) θ) _
    (𝓝 (∫ θ : ℝ in 0..(2 * Real.pi),
      g1CirclePullback
        (G1RatioTail.complexKernel M (τ₀ : ℂ) (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
        r ((D m).radius r) θ)) at hc
  rw [G1RatioTail.complexKernel_real] at hc
  exact ⟨hc, hc.mono_left nhdsWithin_le_nhds, hc.mono_left nhdsWithin_le_nhds⟩

/-- R11. Fixed-chain ordinary integral limits from the full neighborhood and from each side, to the
exact contract's real integral. This is an input to the real-integral comparison used below. [RW26,
p. 7, (23)]. -/
theorem family_chain_integral_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    ∀ m : Fin (M 1 0).toNat,
      let f := fun τ : ℂ => g1ChainIntegral (D m)
        (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
      let v := g1ChainIntegral (D m) (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))
      Tendsto f (𝓝 (τ₀ : ℂ)) (𝓝 v) ∧
        Tendsto f (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 v) ∧
        Tendsto f (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ)) (𝓝 v) := by
  obtain ⟨ρv, C, κ, R, hρv, _, _, _, _, hi, hb⟩ :=
    family_vertical_majorant M hM τ₀ w y n h ell p hT hs hL D hD
  obtain ⟨ρi, hρi, hint⟩ :=
    family_chain_integrable M hM τ₀ w y n h ell p hT hs hL D hD
  have hlim := family_pullbacks_tendsto M hM τ₀ w y n h ell p hT D hD
  have hcir := family_circle_integral_limits M hM τ₀ w y n h ell p hT D hD
  intro m
  have hv : Tendsto (fun τ : ℂ => ∫ t : ℝ, g1VerticalPullback
      (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
      (D m).crossing t) (𝓝 (τ₀ : ℂ))
      (𝓝 (∫ t : ℝ, g1VerticalPullback (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))
        (D m).crossing t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (verticalMajorant C κ R)
    · filter_upwards [disk_nhds τ₀ ρi hρi] with τ hτ
      exact (hint τ hτ m).1.aestronglyMeasurable
    · filter_upwards [disk_nhds τ₀ ρv hρv] with τ hτ
      exact Eventually.of_forall (hb τ hτ m)
    · exact hi
    · exact Eventually.of_forall (hlim m).1
  have hfull := hv.add (tendsto_finsetSum (D m).centers (fun r hr => (hcir m r hr).1))
  exact ⟨hfull, hfull.mono_left nhdsWithin_le_nhds, hfull.mono_left nhdsWithin_le_nhds⟩

/-- R12. The finite sum used by the G1 contract has the same two-sided ordinary limit. [RW26, p. 7,
(23)]. No prefactor, removable right side, or integral identity is asserted. -/
theorem summed_chain_integral_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    let f := fun τ : ℂ => ∑ m : Fin (M 1 0).toNat,
      g1ChainIntegral (D m)
        (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
    let v := ∑ m : Fin (M 1 0).toNat,
      g1ChainIntegral (D m) (g1RatioKernel M τ₀ w y n h ell p (m : ℤ))
    Tendsto f (𝓝 (τ₀ : ℂ)) (𝓝 v) ∧
      Tendsto f (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 v) ∧
      Tendsto f (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ)) (𝓝 v) := by
  have hlim := family_chain_integral_limits M hM τ₀ w y n h ell p hT hs hL D hD
  have hfull := tendsto_finsetSum Finset.univ (fun m _ => (hlim m).1)
  exact ⟨hfull, hfull.mono_left nhdsWithin_le_nhds, hfull.mono_left nhdsWithin_le_nhds⟩

/-- R13. Local parameter analyticity of the same fixed-chain finite sum. Choose a closed subdisk
inside the regular/majorant disk; no contour moves with τ. [RW26, p. 6, p. 7, (23)]. This argument
uses full-disk domination and the actual joint kernel charts, without using a right-hand side
identity.
Spectral parameters w,y stay fixed and real. -/
theorem summed_chain_integral_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (n h ell p : ℤ) (hT : 0 < g1T M τ₀)
    (hs : 0 < g1S M τ₀ w h ell) (hL : g1L M τ₀ w y h ell p < 0)
    (D : Fin (M 1 0).toNat → G1VerticalChain)
    (hD : ∀ m, G1Separates (D m) (g1NumeratorPoles M τ₀ n (m : ℤ))
      (g1InversePoles M τ₀ y n p (m : ℤ))) :
    let f := fun τ : ℂ => ∑ m : Fin (M 1 0).toNat,
      g1ChainIntegral (D m)
        (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
    ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd ℂ f (ModularSector.parameterDisk τ₀ ρ) := by
  obtain ⟨ρr, hρr, hr⟩ :=
    G1BilateralSeparation.family_regular_tube M hM τ₀ w y n h ell p hT D hD
  obtain ⟨ρv, Cv, κ, R, hρv, _, _, _, _, hiv, hv⟩ :=
    family_vertical_majorant M hM τ₀ w y n h ell p hT hs hL D hD
  obtain ⟨ρc, Cc, hρc, _, hic, hc⟩ :=
    family_circle_majorant M hM τ₀ w y n h ell p hT D hD
  let ρ := min ρr (min ρv ρc)
  have hρ : 0 < ρ := lt_min hρr (lt_min hρv hρc)
  have hsubr : ModularSector.parameterDisk τ₀ ρ ⊆ ModularSector.parameterDisk τ₀ ρr :=
    disk_mono (min_le_left _ _)
  have hsubv : ModularSector.parameterDisk τ₀ ρ ⊆ ModularSector.parameterDisk τ₀ ρv :=
    disk_mono ((min_le_right _ _).trans (min_le_left _ _))
  have hsubc : ModularSector.parameterDisk τ₀ ρ ⊆ ModularSector.parameterDisk τ₀ ρc :=
    disk_mono ((min_le_right _ _).trans (min_le_right _ _))
  have hsingle (m : Fin (M 1 0).toNat) : AnalyticOnNhd ℂ
      (fun τ : ℂ => g1ChainIntegral (D m)
        (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ)))
      (ModularSector.parameterDisk τ₀ (ρ / 2)) := by
    let K : ℂ × ℂ → ℂ := fun q =>
      G1RatioTail.complexKernel M q.2 (w : ℂ) (y : ℂ) n h ell p (m : ℤ) q.1
    have hz : Continuous (g1VerticalPoint (D m).crossing) := by
      unfold g1VerticalPoint
      fun_prop
    have hline := pullback_integral_analytic (K := K)
      (z := g1VerticalPoint (D m).crossing) (j := fun _ => Complex.I)
      (c := (τ₀ : ℂ)) (R := ρ) (B := verticalMajorant Cv κ R) hρ hz continuous_const
      (fun τ hτ t => kernel_analytic M hM (w : ℂ) (y : ℂ) n h ell p (m : ℤ)
        ((hr τ (hsubr hτ) m).1 t))
      (Eventually.of_forall (fun t τ hτ => hv τ (hsubv hτ) m t)) hiv
    have hcircles : ∀ r ∈ (D m).centers, AnalyticOnNhd ℂ
        (fun τ : ℂ => ∫ θ : ℝ in 0..(2 * Real.pi),
          g1CirclePullback
            (G1RatioTail.complexKernel M τ (w : ℂ) (y : ℂ) n h ell p (m : ℤ))
            r ((D m).radius r) θ) (ModularSector.parameterDisk τ₀ (ρ / 2)) := by
      intro r hrmem
      let z : ℝ → ℂ := circleMap (r : ℂ) ((D m).radius r)
      let j : ℝ → ℂ := fun θ => Complex.I * (z θ - (r : ℂ))
      have hj : Continuous j := continuous_const.mul ((continuous_circleMap _ _).sub continuous_const)
      have hbi : Integrable (fun _ : ℝ => Cc)
          (volume.restrict (Ioc 0 (2 * Real.pi))) := hic.1
      have hcircle := pullback_integral_analytic
        (μ := volume.restrict (Ioc 0 (2 * Real.pi))) (K := K) (z := z) (j := j)
        (c := (τ₀ : ℂ)) (R := ρ) (B := fun _ => Cc) hρ (continuous_circleMap _ _) hj
        (fun τ hτ θ => kernel_analytic M hM (w : ℂ) (y : ℂ) n h ell p (m : ℤ)
          ((hr τ (hsubr hτ) m).2 r hrmem θ))
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ τ hτ
          exact hc τ (hsubc hτ) m r hrmem θ ⟨hθ.1.le, hθ.2⟩) hbi
      simpa only [intervalIntegral.integral_of_le
        (show (0 : ℝ) ≤ 2 * Real.pi by positivity), K, z, j, g1CirclePullback,
        ModularSector.parameterDisk] using hcircle
    have hcir := Finset.analyticOnNhd_fun_sum (D m).centers hcircles
    intro τ hτ
    have ha := (hline τ hτ).add (hcir τ hτ)
    apply ha.congr
    filter_upwards [] with u
    simp only [g1ChainIntegral, Pi.add_apply, Finset.sum_apply, K, g1VerticalPullback]
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  simpa only [Finset.sum_apply] using
    Finset.analyticOnNhd_fun_sum Finset.univ (fun m _ => hsingle m)

#check @G1RatioTail.complexKernel_real
#check @G1RatioTail.reflection_difference_affine
#check @ModularCluster.circleContribution_tendsto_lower
#print verticalMajorant
#check @family_vertical_majorant
#check @family_chain_integrable
#check @summed_chain_integral_limits
#check @summed_chain_integral_analytic

end SICLean.L4.G1BilateralRatioTails
