import SICLean.L4.ModularSectorFactors
import SICLean.L4.ModularCocycle
import SICLean.L4.ModularDivisor

set_option autoImplicit false

/-!
The closed upper half-plane
parameter disk is the first packaged asymptotic theorem. Full-disk helpers
are elementary reflection and divisor checks, not an integral continuation.
[RW26, p. 6, p. 7, (19), Prop. 1, Prop. 2(i), Lemma 1].
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.ModularSector

def reflectedIndex (i : ℤ × ℤ) : ℤ × ℤ := (1 - i.1, 1 - i.2)

def reflectedFamily (F : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  F ∪ F.image reflectedIndex

/-- Concrete real-valued errors, not predicates asserting a decay bound. -/
def upperError (M : SL(2, ℤ)) (i : ℤ × ℤ) (z τ : ℂ) : ℝ :=
  ‖modularPhi M i.1 i.2 z τ - 1‖ + ‖(modularPhi M i.1 i.2 z τ)⁻¹ - 1‖

/-- Both relative errors use the existing exact reflection factor. -/
def lowerError (M : SL(2, ℤ)) (i : ℤ × ℤ) (z τ : ℂ) : ℝ :=
  ‖modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ - 1‖ +
    ‖modularReflectionFactor M i.1 i.2 z τ * (modularPhi M i.1 i.2 z τ)⁻¹ - 1‖

/--
The finite family used before choosing a common R is reflection-closed; [RW26, p. 6, Prop. 1].
-/
theorem reflectedFamily_closed (F : Finset (ℤ × ℤ)) :
    F ⊆ reflectedFamily F ∧
      ∀ i ∈ reflectedFamily F, reflectedIndex i ∈ reflectedFamily F := by
  constructor
  · exact Finset.subset_union_left
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hjj : reflectedIndex (reflectedIndex j) = j := by
        ext <;> simp [reflectedIndex]
      rw [hjj]
      exact Finset.mem_union_left _ hj

/--
A is a joint analytic unit, without claiming it is uniformly bounded. [RW26, p. 6, Prop. 1].
It uses `modularReflectionPolynomial`, `modularReflectionFactor`, and `etaMultiplier_ne_zero`.
-/
theorem reflectionFactor_joint_unit (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularReflectionFactor M r n p.1 p.2) (z, τ) ∧
      modularReflectionFactor M r n z τ ≠ 0 := by
  have hd0 : etaDenom M τ ≠ 0 := Complex.slitPlane_ne_zero hτ
  have hden : AnalyticAt ℂ (fun p : ℂ × ℂ => etaDenom M p.2) (z, τ) := by
    unfold etaDenom
    exact (analyticAt_const.mul analyticAt_snd).add analyticAt_const
  have hmob : AnalyticAt ℂ (fun p : ℂ × ℂ => etaMobius M p.2) (z, τ) := by
    unfold etaMobius
    exact ((analyticAt_const.mul analyticAt_snd).add analyticAt_const).div hden hd0
  have ht1 : AnalyticAt ℂ
      (fun p : ℂ × ℂ => (M 1 0 : ℂ) * p.1 ^ 2 / etaDenom M p.2) (z, τ) :=
    (analyticAt_const.mul (analyticAt_fst.pow 2)).div hden hd0
  have ht2 : AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        (2 * (r : ℂ) - 1 - (2 * (n : ℂ) - 1) / etaDenom M p.2) * p.1) (z, τ) :=
    (analyticAt_const.sub (analyticAt_const.div hden hd0)).mul analyticAt_fst
  have ht3 : AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        modularBernoulliTwo (r : ℂ) * p.2 - modularBernoulliTwo (n : ℂ) * etaMobius M p.2)
      (z, τ) :=
    (analyticAt_const.mul analyticAt_snd).sub (analyticAt_const.mul hmob)
  have hP : AnalyticAt ℂ
      (fun p : ℂ × ℂ => modularReflectionPolynomial M r n p.1 p.2) (z, τ) := by
    have h := (analyticAt_const (v := -(1 / 2 : ℂ))).mul ((ht1.add ht2).add ht3)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [modularReflectionPolynomial, Pi.mul_apply, neg_mul]
    ring
  have hexp : AnalyticAt ℂ Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * modularReflectionPolynomial M r n z τ) := by
    rw [analyticAt_iff_eventually_differentiableAt]
    exact Eventually.of_forall fun _ => Complex.differentiableAt_exp
  have hlin : AnalyticAt ℂ
      (fun b : ℂ => 2 * (Real.pi : ℂ) * Complex.I * b)
      (modularReflectionPolynomial M r n z τ) :=
    (analyticAt_const (v := 2 * (Real.pi : ℂ) * Complex.I)).mul analyticAt_id
  have he1 : AnalyticAt ℂ e (modularReflectionPolynomial M r n z τ) := by
    unfold e
    exact hexp.comp hlin
  have he1' : AnalyticAt ℂ e
      ((fun p : ℂ × ℂ => modularReflectionPolynomial M r n p.1 p.2) (z, τ)) := he1
  have he : AnalyticAt ℂ
      (fun p : ℂ × ℂ => e (modularReflectionPolynomial M r n p.1 p.2)) (z, τ) :=
    AnalyticAt.comp (g := e)
      (f := fun p : ℂ × ℂ => modularReflectionPolynomial M r n p.1 p.2)
      (x := (z, τ)) he1' hP
  constructor
  · have h : AnalyticAt ℂ
        (fun p : ℂ × ℂ => (etaMultiplier M) ^ (-2 : ℤ) *
          ((-1 : ℂ) ^ (r + n) * e (modularReflectionPolynomial M r n p.1 p.2)))
        (z, τ) :=
      (analyticAt_const (v := (etaMultiplier M) ^ (-2 : ℤ))).mul
        ((analyticAt_const (v := (-1 : ℂ) ^ (r + n))).mul he)
    simpa only [modularReflectionFactor, mul_assoc] using h
  · unfold modularReflectionFactor
    exact mul_ne_zero
      (mul_ne_zero (zpow_ne_zero _ (etaMultiplier_ne_zero M hM))
        (zpow_ne_zero _ (by norm_num)))
      (e_ne_zero _)

/--
Only a label-preserving swap of the existing counts, not a new order
calculation. [RW26, p. 6] divisor sets.
-/
theorem divisor_multiplicity_reflection (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) :
    modularPhiPoleMultiplicity M r n z τ =
        modularPhiZeroMultiplicity M (1 - r) (1 - n) (-z) τ ∧
      modularPhiZeroMultiplicity M r n z τ =
        modularPhiPoleMultiplicity M (1 - r) (1 - n) (-z) τ := by
  have hpt : ∀ (a b : ℤ) (K J : ℕ),
      modularPhiZeroPoint M (1 - a) (1 - b) τ K J =
        -modularPhiPolePoint M a b τ K J := by
    intro a b K J
    unfold modularPhiZeroPoint modularPhiPolePoint
    push_cast
    ring
  have hPgen : ∀ (a b : ℤ) (w : ℂ),
      modularPhiPoleIndices M a b w τ =
        modularPhiZeroIndices M (1 - a) (1 - b) (-w) τ := by
    intro a b w
    have hlabel : modularPhiPoleLabels M a b =
        modularPhiZeroLabels M (1 - a) (1 - b) := by
      ext p
      unfold modularPhiPoleLabels modularPhiZeroLabels
      have h : ((1 - b : ℤ) - 1 - M 1 1 * (1 - a)) =
          M 1 1 * (a - 1) - b := by ring
      rw [h]
    ext p
    unfold modularPhiPoleIndices modularPhiZeroIndices
    rw [hlabel]
    constructor
    · rintro ⟨hl, hz⟩
      exact ⟨hl, by rw [hpt a b]; rw [hz]⟩
    · rintro ⟨hl, hz⟩
      refine ⟨hl, ?_⟩
      rw [hpt a b] at hz
      exact neg_inj.mp hz
  have hP : modularPhiPoleIndices M r n z τ =
      modularPhiZeroIndices M (1 - r) (1 - n) (-z) τ := hPgen r n z
  have hZ : modularPhiZeroIndices M r n z τ =
      modularPhiPoleIndices M (1 - r) (1 - n) (-z) τ := by
    have h := hPgen (1 - r) (1 - n) (-z)
    have hr : (1 - (1 - r) : ℤ) = r := by ring
    have hn : (1 - (1 - n) : ℤ) = n := by ring
    rw [hr, hn] at h
    simpa only [neg_neg] using h.symm
  constructor
  · unfold modularPhiPoleMultiplicity modularPhiZeroMultiplicity
    rw [hP]
  · unfold modularPhiZeroMultiplicity modularPhiPoleMultiplicity
    rw [hZ]

/--
Counts vanish in both tails, uniformly in τ;
no pseudolattice-exclusion hypothesis is imposed; [RW26, p. 6].
-/
theorem tail_divisor_free (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ z : ℂ, (z ∈ upperSector α R ∨ -z ∈ upperSector α R) →
        modularPhiPoleMultiplicity M i.1 i.2 z τ = 0 ∧
          modularPhiZeroMultiplicity M i.1 i.2 z τ = 0 ∧
          (z, τ) ∈ modularPhiNonvanishingDomain M i.1 i.2 := by
  obtain ⟨R, hR, hfac⟩ :=
    factor_upper_divisor_free M hM (reflectedFamily F) τ₀ α hT hα hα'
  have hclosed := reflectedFamily_closed F
  refine ⟨R, hR, ?_⟩
  intro τ hτdisk i hi z hz
  have hτD : τ ∈ modularPhiDomain M :=
    (parameterDisk_denom_control M hM τ₀ α hT hα hα' hτdisk).2.2.2
  have hi' : i ∈ reflectedFamily F := hclosed.1 hi
  have hrefl : reflectedIndex i ∈ reflectedFamily F := hclosed.2 i hi'
  have hmul0 : modularPhiPoleMultiplicity M i.1 i.2 z τ = 0 ∧
      modularPhiZeroMultiplicity M i.1 i.2 z τ = 0 := by
    rcases hz with hz | hz
    · have hf : ∀ j ∈ Finset.range (M 1 0).toNat,
          phiPoleMultiplicity (modularPhiFactorPoint M i.1 i.2 j z τ).1
              (modularPhiFactorPoint M i.1 i.2 j z τ).2 = 0 ∧
            phiZeroMultiplicity (modularPhiFactorPoint M i.1 i.2 j z τ).1
              (modularPhiFactorPoint M i.1 i.2 j z τ).2 = 0 :=
        fun j hj => hfac τ hτdisk i hi' j hj z hz
      have hm := modularPhi_multiplicity_pullback M hM i.1 i.2 z τ hτD
      refine ⟨?_, ?_⟩
      · rw [hm.1]
        exact Finset.sum_eq_zero fun j hj => (hf j hj).1
      · rw [hm.2]
        exact Finset.sum_eq_zero fun j hj => (hf j hj).2
    · have hf : ∀ j ∈ Finset.range (M 1 0).toNat,
          phiPoleMultiplicity
              (modularPhiFactorPoint M (reflectedIndex i).1 (reflectedIndex i).2 j (-z) τ).1
              (modularPhiFactorPoint M (reflectedIndex i).1 (reflectedIndex i).2 j (-z) τ).2 = 0 ∧
            phiZeroMultiplicity
              (modularPhiFactorPoint M (reflectedIndex i).1 (reflectedIndex i).2 j (-z) τ).1
              (modularPhiFactorPoint M (reflectedIndex i).1 (reflectedIndex i).2 j (-z) τ).2 = 0 :=
        fun j hj => hfac τ hτdisk (reflectedIndex i) hrefl j hj (-z) hz
      have hm := modularPhi_multiplicity_pullback M hM (reflectedIndex i).1
        (reflectedIndex i).2 (-z) τ hτD
      have hp0 : modularPhiPoleMultiplicity M (reflectedIndex i).1
          (reflectedIndex i).2 (-z) τ = 0 := by
        rw [hm.1]
        exact Finset.sum_eq_zero fun j hj => (hf j hj).1
      have hz0 : modularPhiZeroMultiplicity M (reflectedIndex i).1
          (reflectedIndex i).2 (-z) τ = 0 := by
        rw [hm.2]
        exact Finset.sum_eq_zero fun j hj => (hf j hj).2
      have hs := divisor_multiplicity_reflection M i.1 i.2 z τ
      exact ⟨by rw [hs.1]; exact hz0, by rw [hs.2]; exact hp0⟩
  exact ⟨hmul0.1, hmul0.2, hτD, hmul0.1, hmul0.2⟩

/--
Point values, obtained after continuity at both centers, not by
evaluating a punctured germ. [RW26, p. 6, Prop. 1].
The argument uses `modularPhi_reflection_normalized` and the tail vanishing above.
-/
theorem tail_point_reflection (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ z : ℂ, -z ∈ upperSector α R →
        modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ =
          modularReflectionFactor M i.1 i.2 z τ := by
  obtain ⟨R, hR, htail⟩ :=
    tail_divisor_free M hM (reflectedFamily F) τ₀ α hT hα hα'
  have hclosed := reflectedFamily_closed F
  refine ⟨R, hR, ?_⟩
  intro τ hτdisk i hi z hz
  have hi' : i ∈ reflectedFamily F := hclosed.1 hi
  have hrefl : reflectedIndex i ∈ reflectedFamily F := hclosed.2 i hi'
  have ht_i := htail τ hτdisk i hi' z (Or.inr hz)
  have ht_r := htail τ hτdisk (reflectedIndex i) hrefl (-z) (Or.inl hz)
  have hτD : τ ∈ modularPhiDomain M := ht_i.2.2.1
  have hA_i : AnalyticAt ℂ
      (fun p : ℂ × ℂ => modularPhi M i.1 i.2 p.1 p.2) (z, τ) :=
    (modularPhi_joint_analytic_no_poles M hM i.1 i.2) (z, τ) ⟨hτD, ht_i.1⟩
  have hA_r : AnalyticAt ℂ
      (fun p : ℂ × ℂ => modularPhi M (reflectedIndex i).1 (reflectedIndex i).2 p.1 p.2)
      (-z, τ) :=
    (modularPhi_joint_analytic_no_poles M hM (reflectedIndex i).1
      (reflectedIndex i).2) (-z, τ) ⟨hτD, ht_r.1⟩
  have hL : ContinuousAt (fun w : ℂ => modularPhi M i.1 i.2 w τ) z := by
    have hpair : ContinuousAt (fun w : ℂ => (w, τ)) z :=
      ContinuousAt.prodMk continuousAt_id continuousAt_const
    exact ContinuousAt.comp (g := fun p : ℂ × ℂ => modularPhi M i.1 i.2 p.1 p.2)
      (f := fun w : ℂ => (w, τ)) (x := z) hA_i.continuousAt hpair
  have hR' : ContinuousAt (fun w : ℂ => modularPhi M (1 - i.1) (1 - i.2) (-w) τ) z := by
    have hpair : ContinuousAt (fun w : ℂ => (-w, τ)) z :=
      ContinuousAt.prodMk continuousAt_neg continuousAt_const
    exact ContinuousAt.comp
      (g := fun p : ℂ × ℂ => modularPhi M (reflectedIndex i).1 (reflectedIndex i).2 p.1 p.2)
      (f := fun w : ℂ => (-w, τ)) (x := z) hA_r.continuousAt hpair
  have hnorm := modularPhi_reflection_normalized M hM i.1 i.2 z τ hτD hL hR'
  have hμ : etaMultiplier M ≠ 0 := etaMultiplier_ne_zero M hM
  have hkey : (etaMultiplier M * etaMultiplier M) *
      (modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) =
      (-1 : ℂ) ^ (i.1 + i.2) * e (modularReflectionPolynomial M i.1 i.2 z τ) := by
    calc
      (etaMultiplier M * etaMultiplier M) *
          (modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) =
          (etaMultiplier M * modularPhi M i.1 i.2 z τ) *
            (etaMultiplier M * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) := by ring
      _ = _ := hnorm
  have hgoal : modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ =
      (etaMultiplier M * etaMultiplier M)⁻¹ *
        ((-1 : ℂ) ^ (i.1 + i.2) * e (modularReflectionPolynomial M i.1 i.2 z τ)) := by
    rw [← hkey]
    field_simp [hμ]
  have hpow : (etaMultiplier M) ^ (-2 : ℤ) =
      (etaMultiplier M * etaMultiplier M)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
    ring
  rw [hgoal]
  unfold modularReflectionFactor
  rw [hpow]
  ring

/--
Closed upper-half-disk version of the upper asymptotic. A single
ρ,C,k,R is chosen before τ,(r,n),z; [RW26, p. 6, p. 7, (19), Lemma 1].
-/
theorem upper_half_upper_decay (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ρ = parameterRadius M τ₀ α ∧ k = rate M τ₀ α ∧
      ∀ τ ∈ upperParameterDisk τ₀ ρ, ∀ i ∈ F, ∀ z ∈ upperSector α R,
        upperError M i z τ ≤ C * Real.exp (-k * ‖z‖) := by
  obtain ⟨C, R, hC, hR, hdec⟩ := upper_tail_decay M hM F τ₀ α hT hα hα'
  refine ⟨parameterRadius M τ₀ α, C, rate M τ₀ α, R,
    parameterRadius_pos M hM τ₀ α hT hα hα', hC,
    (height_safe_rate_pos M τ₀ α hT hα hα').2, hR, rfl, rfl, ?_⟩
  intro τ hτ i hi z hz
  exact hdec τ hτ.1 i hi z hz

/--
Both lower relative errors, sharing the parameter neighborhood and
the explicit rate; [RW26, p. 6, p. 7, Prop. 1, Lemma 1].
-/
theorem upper_half_lower_decay (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ρ = parameterRadius M τ₀ α ∧ k = rate M τ₀ α ∧
      ∀ τ ∈ upperParameterDisk τ₀ ρ, ∀ i ∈ F, ∀ z : ℂ,
        -z ∈ upperSector α R → lowerError M i z τ ≤ C * Real.exp (-k * ‖z‖) := by
  obtain ⟨ρ, C, k, R₁, hρ, hC, hk, hR₁, hρeq, hkeq, hup⟩ :=
    upper_half_upper_decay M hM (reflectedFamily F) τ₀ α hT hα hα'
  obtain ⟨R₂, hR₂, hpt⟩ :=
    tail_point_reflection M hM (reflectedFamily F) τ₀ α hT hα hα'
  obtain ⟨R₃, hR₃, htail⟩ :=
    tail_divisor_free M hM (reflectedFamily F) τ₀ α hT hα hα'
  have hclosed := reflectedFamily_closed F
  refine ⟨ρ, C, k, max (max R₁ R₂) R₃, hρ, hC, hk, ?_, hρeq, hkeq, ?_⟩
  · exact lt_of_lt_of_le hR₁
      (le_trans (le_max_left R₁ R₂) (le_max_left (max R₁ R₂) R₃))
  · intro τ hτ i hi z hz
    have hτ' : τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α) := hρeq ▸ hτ.1
    have hi' : i ∈ reflectedFamily F := hclosed.1 hi
    have hrefl : reflectedIndex i ∈ reflectedFamily F := hclosed.2 i hi'
    have hz₁ : -z ∈ upperSector α R₁ :=
      upperSector_antitone le_rfl
        (le_trans (le_max_left R₁ R₂) (le_max_left (max R₁ R₂) R₃)) hz
    have hz₂ : -z ∈ upperSector α R₂ :=
      upperSector_antitone le_rfl (le_trans (le_max_right R₁ R₂) (le_max_left _ _)) hz
    have hz₃ : -z ∈ upperSector α R₃ :=
      upperSector_antitone le_rfl (le_max_right (max R₁ R₂) R₃) hz
    have ht := htail τ hτ' i hi' z (Or.inr hz₃)
    have hne : modularPhi M i.1 i.2 z τ ≠ 0 :=
      (modularPhi_ne_zero_iff M hM i.1 i.2 z τ ht.2.2.1 ht.1).2 ht.2.1
    have hpt_i := hpt τ hτ' i hi' z hz₂
    have h1 : modularPhi M i.1 i.2 z τ / (modularPhi M i.1 i.2 z τ *
        modularPhi M (1 - i.1) (1 - i.2) (-z) τ) =
        (modularPhi M (1 - i.1) (1 - i.2) (-z) τ)⁻¹ := by
      field_simp [hne]
    have h2 : (modularPhi M i.1 i.2 z τ * modularPhi M (1 - i.1) (1 - i.2) (-z) τ) *
        (modularPhi M i.1 i.2 z τ)⁻¹ =
        modularPhi M (1 - i.1) (1 - i.2) (-z) τ := by
      field_simp [hne]
    have hEq : lowerError M i z τ = upperError M (reflectedIndex i) (-z) τ := by
      unfold lowerError upperError reflectedIndex
      rw [← hpt_i, h1, h2]
      ring
    rw [hEq]
    have hh := hup τ hτ (reflectedIndex i) hrefl (-z) hz₁
    simpa [hkeq, norm_neg] using hh

/--
First canonical export: the full upper-half-disk conclusion,
with the same constants for both tails and both inverses; [RW26, p. 6, p. 7, Prop. 1--2, Lemma 1].
-/
theorem upper_half_uniform_asymptotics (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ ρ C k R : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < k ∧ 0 < R ∧
      ρ = parameterRadius M τ₀ α ∧ k = rate M τ₀ α ∧
      ∀ τ ∈ upperParameterDisk τ₀ ρ, τ ∈ modularPhiDomain M ∧
        ∀ i ∈ F,
          (∀ z ∈ upperSector α R, modularPhi M i.1 i.2 z τ ≠ 0 ∧
            upperError M i z τ ≤ C * Real.exp (-k * ‖z‖)) ∧
          (∀ z : ℂ, -z ∈ upperSector α R → modularPhi M i.1 i.2 z τ ≠ 0 ∧
            lowerError M i z τ ≤ C * Real.exp (-k * ‖z‖)) := by
  obtain ⟨ρu, Cu, ku, Ru, hρu, hCu, hku, hRu, hρueq, hkueq, hup⟩ :=
    upper_half_upper_decay M hM F τ₀ α hT hα hα'
  obtain ⟨ρl, Cl, kl, Rl, hρl, hCl, hkl, hRl, hρleq, hkleq, hlow⟩ :=
    upper_half_lower_decay M hM F τ₀ α hT hα hα'
  obtain ⟨Rd, hRd, htail⟩ := tail_divisor_free M hM F τ₀ α hT hα hα'
  refine ⟨parameterRadius M τ₀ α, max Cu Cl, rate M τ₀ α,
    max (max Ru Rl) Rd, parameterRadius_pos M hM τ₀ α hT hα hα',
    lt_of_lt_of_le hCu (le_max_left _ _),
    (height_safe_rate_pos M τ₀ α hT hα hα').2, ?_, rfl, rfl, ?_⟩
  · exact lt_of_lt_of_le hRu
      (le_trans (le_max_left Ru Rl) (le_max_left (max Ru Rl) Rd))
  · intro τ hτ
    have hτD : τ ∈ modularPhiDomain M :=
      (parameterDisk_denom_control M hM τ₀ α hT hα hα' hτ.1).2.2.2
    have hτu : τ ∈ upperParameterDisk τ₀ ρu := by rw [hρueq]; exact hτ
    have hτl : τ ∈ upperParameterDisk τ₀ ρl := by rw [hρleq]; exact hτ
    refine ⟨hτD, ?_⟩
    intro i hi
    constructor
    · intro z hz
      have hzRu : z ∈ upperSector α Ru :=
        upperSector_antitone le_rfl
          (le_trans (le_max_left Ru Rl) (le_max_left (max Ru Rl) Rd)) hz
      have hzRd : z ∈ upperSector α Rd :=
        upperSector_antitone le_rfl (le_max_right (max Ru Rl) Rd) hz
      have hub := hup τ hτu i hi z hzRu
      have hub' : upperError M i z τ ≤ max Cu Cl * Real.exp (-rate M τ₀ α * ‖z‖) :=
        le_trans (by simpa [hkueq] using hub)
          (mul_le_mul_of_nonneg_right (le_max_left Cu Cl) (Real.exp_pos _).le)
      have ht := htail τ hτ.1 i hi z (Or.inl hzRd)
      have hne : modularPhi M i.1 i.2 z τ ≠ 0 :=
        (modularPhi_ne_zero_iff M hM i.1 i.2 z τ hτD ht.1).2 ht.2.1
      exact ⟨hne, hub'⟩
    · intro z hz
      have hzRl : -z ∈ upperSector α Rl :=
        upperSector_antitone le_rfl
          (le_trans (le_max_right Ru Rl) (le_max_left (max Ru Rl) Rd)) hz
      have hzRd : -z ∈ upperSector α Rd :=
        upperSector_antitone le_rfl (le_max_right (max Ru Rl) Rd) hz
      have hlb := hlow τ hτl i hi z hzRl
      have hlb' : lowerError M i z τ ≤ max Cu Cl * Real.exp (-rate M τ₀ α * ‖z‖) :=
        le_trans (by simpa [hkleq] using hlb)
          (mul_le_mul_of_nonneg_right (le_max_right Cu Cl) (Real.exp_pos _).le)
      have ht := htail τ hτ.1 i hi z (Or.inr hzRd)
      have hne : modularPhi M i.1 i.2 z τ ≠ 0 :=
        (modularPhi_ne_zero_iff M hM i.1 i.2 z τ hτD ht.1).2 ht.2.1
      exact ⟨hne, hlb'⟩

/--
Literal A(1+ε), with A using polynomial verbatim; [RW26, p. 6, p. 7, Prop. 1, Lemma 1].
-/
theorem upper_half_lower_factorization (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ τ ∈ upperParameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ z : ℂ, -z ∈ upperSector α R →
        ∃ ε : ℂ, ‖ε‖ ≤ C * Real.exp (-rate M τ₀ α * ‖z‖) ∧ 1 + ε ≠ 0 ∧
          modularPhi M i.1 i.2 z τ =
            (etaMultiplier M) ^ (-2 : ℤ) * (-1 : ℂ) ^ (i.1 + i.2) *
              e (modularReflectionPolynomial M i.1 i.2 z τ) * (1 + ε) := by
  obtain ⟨ρ, C, k, R₁, hρ, hC, hk, hR₁, hρeq, hkeq, hlow⟩ :=
    upper_half_lower_decay M hM F τ₀ α hT hα hα'
  obtain ⟨Rd, hRd, htail⟩ := tail_divisor_free M hM F τ₀ α hT hα hα'
  refine ⟨C, max R₁ Rd, hC, lt_of_lt_of_le hR₁ (le_max_left R₁ Rd), ?_⟩
  intro τ hτ i hi z hz
  have hzR₁ : -z ∈ upperSector α R₁ :=
    upperSector_antitone le_rfl (le_max_left R₁ Rd) hz
  have hzRd : -z ∈ upperSector α Rd :=
    upperSector_antitone le_rfl (le_max_right R₁ Rd) hz
  have hτρ : τ ∈ upperParameterDisk τ₀ ρ := by rw [hρeq]; exact hτ
  have hlow' := hlow τ hτρ i hi z hzR₁
  have hεle : ‖modularPhi M i.1 i.2 z τ /
      modularReflectionFactor M i.1 i.2 z τ - 1‖ ≤
      C * Real.exp (-rate M τ₀ α * ‖z‖) := by
    have hle : ‖modularPhi M i.1 i.2 z τ /
        modularReflectionFactor M i.1 i.2 z τ - 1‖ ≤ lowerError M i z τ := by
      unfold lowerError
      exact le_add_of_nonneg_right (norm_nonneg _)
    exact le_trans hle (by simpa [hkeq] using hlow')
  have ht := htail τ hτ.1 i hi z (Or.inr hzRd)
  have hne : modularPhi M i.1 i.2 z τ ≠ 0 :=
    (modularPhi_ne_zero_iff M hM i.1 i.2 z τ ht.2.2.1 ht.1).2 ht.2.1
  have hA : modularReflectionFactor M i.1 i.2 z τ ≠ 0 := by
    unfold modularReflectionFactor
    exact mul_ne_zero
      (mul_ne_zero (zpow_ne_zero _ (etaMultiplier_ne_zero M hM))
        (zpow_ne_zero _ (by norm_num)))
      (e_ne_zero _)
  refine ⟨modularPhi M i.1 i.2 z τ /
    modularReflectionFactor M i.1 i.2 z τ - 1, hεle, ?_, ?_⟩
  · have h1e : 1 + (modularPhi M i.1 i.2 z τ /
        modularReflectionFactor M i.1 i.2 z τ - 1) =
        modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ := by ring
    rw [h1e]
    exact div_ne_zero hne hA
  · have h1e : 1 + (modularPhi M i.1 i.2 z τ /
        modularReflectionFactor M i.1 i.2 z τ - 1) =
        modularPhi M i.1 i.2 z τ / modularReflectionFactor M i.1 i.2 z τ := by ring
    rw [h1e]
    have hAdef : modularReflectionFactor M i.1 i.2 z τ =
        (etaMultiplier M) ^ (-2 : ℤ) * (-1 : ℂ) ^ (i.1 + i.2) *
          e (modularReflectionPolynomial M i.1 i.2 z τ) := rfl
    rw [← hAdef]
    field_simp [hA]

/--
Uniform limits with an ε-dependent R that still precedes every τ; [RW26, p. 6, p. 7, Prop. 1--2,
Lemma 1].
-/
theorem upper_half_uniform_limits (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ τ ∈ upperParameterDisk τ₀ (parameterRadius M τ₀ α), ∀ i ∈ F,
        (∀ z ∈ upperSector α R, upperError M i z τ < ε) ∧
        (∀ z : ℂ, -z ∈ upperSector α R → lowerError M i z τ < ε) := by
  intro ε hε
  obtain ⟨ρ, C, k, R₀, hρ, hC, hk, hR₀, hρeq, hkeq, hunif⟩ :=
    upper_half_uniform_asymptotics M hM F τ₀ α hT hα hα'
  have hlin : Tendsto (fun R : ℝ => k * R) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hk tendsto_id
  have htend : Tendsto (fun R : ℝ => Real.exp (-(k * R))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have htend2 : Tendsto (fun R : ℝ => C * Real.exp (-k * R)) atTop (𝓝 0) := by
    have h := htend.const_mul C
    simpa [mul_zero] using h
  have hev : ∀ᶠ R : ℝ in atTop, C * Real.exp (-k * R) < ε :=
    htend2.eventually (eventually_lt_nhds hε)
  obtain ⟨R₂, hR₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max R₀ R₂, lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro τ hτ i hi
  have hτρ : τ ∈ upperParameterDisk τ₀ ρ := by rw [hρeq]; exact hτ
  have hu := (hunif τ hτρ).2 i hi
  have hbound : C * Real.exp (-k * max R₀ R₂) < ε :=
    hR₂ (max R₀ R₂) (le_max_right _ _)
  have hexp_le : ∀ z : ℂ, max R₀ R₂ ≤ ‖z‖ →
      Real.exp (-k * ‖z‖) ≤ Real.exp (-k * max R₀ R₂) := by
    intro z hz
    apply Real.exp_le_exp.mpr
    nlinarith
  constructor
  · intro z hz
    have hz₀ : z ∈ upperSector α R₀ :=
      upperSector_antitone le_rfl (le_max_left _ _) hz
    have hb := (hu.1 z hz₀).2
    have hCle : C * Real.exp (-k * ‖z‖) ≤ C * Real.exp (-k * max R₀ R₂) :=
      mul_le_mul_of_nonneg_left (hexp_le z hz.1) hC.le
    exact lt_of_le_of_lt (le_trans hb hCle) hbound
  · intro z hz
    have hz₀ : -z ∈ upperSector α R₀ :=
      upperSector_antitone le_rfl (le_max_left _ _) hz
    have hb := (hu.2 z hz₀).2
    have hzn : max R₀ R₂ ≤ ‖z‖ := by simpa [norm_neg] using hz.1
    have hCle : C * Real.exp (-k * ‖z‖) ≤ C * Real.exp (-k * max R₀ R₂) :=
      mul_le_mul_of_nonneg_left (hexp_le z hzn) hC.le
    exact lt_of_le_of_lt (le_trans hb hCle) hbound

end SICLean.L4.ModularSector

#check SICLean.L4.modularPhi_reflection_germ
#check SICLean.L4.modularPhi_reflection_normalized
#check SICLean.L4.modularPhi_joint_unit_neighborhood
#print SICLean.L4.modularReflectionPolynomial
#print SICLean.L4.modularReflectionFactor
#print SICLean.L4.ModularSector.lowerError
