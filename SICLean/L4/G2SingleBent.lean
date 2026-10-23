import SICLean.L4.G2ResidueLedger
import SICLean.L4.G2SingleBentAux

set_option autoImplicit false

/-!
# The common bent chain for the single raw kernel

The geometric, analytic and almost-everywhere obligations are proved below.

This file gives the single-function contour calculation. [RW26, p. 13].

Only geometric/arithmetic data and literal integrals are defined here.
The lower ray is traversed towards its finite endpoint. Its common-X
parameter has Jacobian (β-i)/c; the G1 unit-speed parameter is different.
The already proved rawG_period/rawG_difference_germ and the integer
divmod of Telescoping are reused; no lower vertical-tail assertion is made.
-/

noncomputable section

open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2.SingleBent

open G2SingleBentAux

/-- The first half of the existing representative window, with no v. -/
def Window (M : SL(2, ℤ)) (u : ℤ × ℤ) : Prop :=
  0 < sIndex M u ∧ sIndex M u ≤ specialValueOrder M

def angle (β : ℝ) : ℝ := Real.arctan β

/-- C_m-jΔ, in the z coordinate; its corner is crossing-i. -/
def crossing (M : SL(2, ℤ)) (δ : ℝ) (m j : ℤ) : ℝ :=
  (-δ - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ)

def displacement (M : SL(2, ℤ)) (δ : ℝ) (j : ℤ) : ℝ :=
  (δ + (j : ℝ) * length M) / (M 1 0 : ℝ)

/-- The actual common-X ray after pulling back X-εm-jL by division by c. -/
def lowerPoint (M : SL(2, ℤ)) (δ β : ℝ) (m j : ℤ) (R : ℝ) : ℂ :=
  (-(δ : ℂ) - (M 1 0 : ℂ) * Complex.I + (R : ℂ) * ((β : ℂ) - Complex.I) -
    (epsilon M : ℂ) * (m : ℂ) - (j : ℂ) * (length M : ℂ)) / (M 1 0 : ℂ)

def lowerJacobian (M : SL(2, ℤ)) (β : ℝ) : ℂ :=
  ((β : ℂ) - Complex.I) / (M 1 0 : ℂ)

def lowerScale (M : SL(2, ℤ)) (β : ℝ) : ℝ :=
  Real.sqrt (1 + β ^ 2) / (M 1 0 : ℝ)

/-- Literal G1 integral, with its negated outward lower ray. -/
def integral (M : SL(2, ℤ)) (δ β : ℝ) (m j : ℤ) (f : ℂ → ℂ) : ℂ :=
  g1BentIntegral f (crossing M δ m j) (angle β)

def differenceKernel (M : SL(2, ℤ)) (u : ℤ × ℤ) (m : ℤ) (z : ℂ) : ℂ :=
  rawG M u m z - rawG M u (m + 1 - M 0 0) (z + (translate M : ℂ))

/-- Horizontal connector from the left chain to the right chain at the top. -/
def upperConnector (M : SL(2, ℤ)) (u : ℤ × ℤ) (δ : ℝ) (m j : ℤ) (T : ℝ) : ℂ :=
  horizontalIntegral (rawG M u m)
    (crossing M δ m (j + 1)) (crossing M δ m j) T

/-- Same oriented connector at the bent bottom, at the same common R. -/
def lowerConnector (M : SL(2, ℤ)) (u : ℤ × ℤ) (δ β : ℝ)
    (m j : ℤ) (R : ℝ) : ℂ :=
  ∫ t : ℝ in 0..shiftLength M,
    rawG M u m (lowerPoint M δ β m (j + 1) R + (t : ℂ))

/--
Literal n=h=0, ell=u₁+1 specialization; [RW26, p. 7, p. 13, (22)].
-/
theorem singleKernel_eq_g1 (M : SL(2, ℤ)) (u : ℤ × ℤ) (m : ℤ) (z : ℂ) :
    singleKernel M u m z =
      g1SingleKernel M (repellingTau M) (argument M u) 0 0 (u.1 + 1) m z := by
  rw [singleKernel, kernelK_eq_g1, g1SingleKernel, mul_comm]

/--
[RW26, p. 13].
The positive square root normalizes the direction; no phase is selected.
-/
theorem angle_direction (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    0 < angle β ∧ angle β < Real.pi / 4 ∧
      g1LowerDirection (angle β) =
        ((β : ℂ) - Complex.I) / (Real.sqrt (1 + β ^ 2) : ℂ) := by
  refine ⟨Real.arctan_pos.mpr hβ.1,
    (Real.arctan_strictMono hβ.2).trans_eq Real.arctan_one, ?_⟩
  unfold g1LowerDirection angle
  rw [mul_comm Complex.I, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show -Real.pi / 2 + Real.arctan β = Real.arctan β - Real.pi / 2 by ring,
    Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two,
    Real.sin_arctan, Real.cos_arctan]
  push_cast
  ring

/--
The G1 displacement is (δ+jL)/c; [RW26, p. 7, p. 13, (22)] (G1 application).
-/
theorem crossing_eq_g1 (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (hδ : 0 < δ) (m j : ℤ) (hj : 0 ≤ j) :
    0 < displacement M δ j ∧
      crossing M δ m j =
        g1BentCrossing M (repellingTau M) (displacement M δ j) 0 m := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hj' : 0 ≤ (j : ℝ) := by exact_mod_cast hj
  constructor
  · exact div_pos (add_pos_of_pos_of_nonneg hδ
      (mul_nonneg hj' (length_pos M hM).le)) hc
  · simp only [crossing, g1BentCrossing, displacement, Int.cast_zero, zero_sub,
      epsilon]
    ring

/--
Reparameterization r=R√(1+β²)/c, not r=R; [RW26, p. 13].
-/
theorem lowerPoint_eq_g1 (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ β : ℝ) (hβ : 0 < β ∧ β < 1) (m j : ℤ) (R : ℝ) :
    lowerPoint M δ β m j R =
      g1BentLowerPoint (crossing M δ m j) (angle β) (R * lowerScale M β) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.1.ne'
  have hs : (Real.sqrt (1 + β ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 1 + β ^ 2)).ne'
  rw [g1BentLowerPoint, (angle_direction β hβ).2.2]
  dsimp only [lowerPoint, crossing, lowerScale]
  push_cast
  field_simp
  ring

/--
The actual real-parameter derivative, including division by c; [RW26, p. 7, (22)] is the target
integral convention.
-/
theorem lowerPoint_hasDerivAt (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ β : ℝ) (m j : ℤ) (R : ℝ) :
    HasDerivAt (lowerPoint M δ β m j) (lowerJacobian M β) R ∧
      0 < lowerScale M β := by
  constructor
  · simpa [lowerPoint, lowerJacobian] using!
      (((((Complex.ofRealCLM.hasDerivAt (x := R)).mul_const
        ((β : ℂ) - Complex.I)).const_add
        (-(δ : ℂ) - (M 1 0 : ℂ) * Complex.I)).sub_const
        ((epsilon M : ℂ) * (m : ℂ))).sub_const
        ((j : ℂ) * (length M : ℂ))).div_const (M 1 0 : ℂ)
  · apply div_pos (Real.sqrt_pos.mpr (by positivity))
    exact_mod_cast hM.1

/--
Original and final numerator families stay to the right, retaining m; [RW26, p. 6, p. 13].
-/
theorem numerator_poles_right (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (hδ : 0 < δ) (m j : ℤ) (hj : 0 ≤ j) :
    ∀ X ∈ originalRightComponent M m ∪ rightComponent M m,
      crossing M δ m j < (X - epsilon M * (m : ℝ)) / (M 1 0 : ℝ) := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hj' : 0 ≤ (j : ℝ) := by exact_mod_cast hj
  intro X hX
  have hx : 0 ≤ X := by
    rcases hX with ⟨K, J, _, _, rfl⟩ | ⟨K, J, _, rfl⟩ <;>
      exact add_nonneg (mul_nonneg (epsilon_pos M hM).le (Nat.cast_nonneg K))
        (Nat.cast_nonneg J)
  unfold crossing
  apply (div_lt_div_iff_of_pos_right hc).2
  have := mul_nonneg hj' (length_pos M hM).le
  linarith

/--
Actual point regularity on both pieces, including the real crossing.
δ<scale avoids the comb; [RW26, p. 6, p. 13].
This conclusion is not inferred merely by evaluating a punctured identity.
-/
theorem rawG_analytic_on_paths (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (δ β : ℝ) (hδ : 0 < δ ∧ δ < scale M)
    (hβ : 0 < β ∧ β < 1) (m : ℤ) (j : Fin ((M 1 0).toNat + 1)) :
    (∀ R : ℝ, 0 ≤ R → AnalyticAt ℂ (rawG M u m) (lowerPoint M δ β m (j : ℤ) R)) ∧
    (∀ t : ℝ, -1 ≤ t →
      AnalyticAt ℂ (rawG M u m) (g1VerticalPoint (crossing M δ m (j : ℤ)) t)) := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  constructor
  · intro R hR
    apply rawG_analytic_nonreal M hM
    change (bentPoint M δ β m (j : ℤ) R).im ≠ 0
    rw [bentPoint_im M hM]
    have := div_nonneg hR hc.le
    linarith
  · intro t _
    by_cases ht : t = 0
    · subst t
      simp only [g1VerticalPoint, Complex.ofReal_zero, zero_mul, add_zero]
      apply rawG_analytic_crossing M hM u δ hδ m (j : ℤ)
        (Int.natCast_nonneg _) (crossing M δ m (j : ℤ))
      dsimp only [crossing]
      field_simp
      ring
    · apply rawG_analytic_nonreal M hM
      simpa [g1VerticalPoint] using ht

/--
Fixed-parameter upper bound, uniform over the finite m,j families; [RW26, p. 7, p. 13, Lemma 1].
Reuses named fixed-τ estimates, never an extra G1 field.
-/
theorem rawG_upper_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ : ℝ) (hδ : 0 < δ ∧ δ < scale M) :
    0 < rawUpperRate M u ∧ ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧
      ∀ (m : Fin (M 1 0).toNat) (j : Fin ((M 1 0).toNat + 1)) (t : ℝ), T₀ ≤ t →
        ‖rawG M u (m : ℤ) (g1VerticalPoint (crossing M δ (m : ℤ) (j : ℤ)) t)‖ ≤
          C * Real.exp (-2 * Real.pi * rawUpperRate M u * t) := by
  have hr : 0 < rawUpperRate M u := by
    rw [(raw_rate_formulas M hM u u).1]
    exact div_pos (by exact_mod_cast hu.1) (length_pos M hM)
  refine ⟨hr, ?_⟩
  let ι := Fin (M 1 0).toNat × Fin ((M 1 0).toNat + 1)
  have hb (i : ι) : ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t →
      ‖rawG M u (i.1 : ℤ) (g1VerticalPoint (crossing M δ (i.1 : ℤ) (i.2 : ℤ)) t)‖ ≤
        C * Real.exp (-2 * Real.pi * rawUpperRate M u * t) := by
    obtain ⟨C, T, hC, hT, hb⟩ := rawG_upper_tail_bound M hM u (i.1 : ℤ)
      |crossing M δ (i.1 : ℤ) (i.2 : ℤ)| (abs_nonneg _)
    refine ⟨C, T, hC, hT, fun t ht => ?_⟩
    simpa [g1VerticalPoint] using hb
      (g1VerticalPoint (crossing M δ (i.1 : ℤ) (i.2 : ℤ)) t) (by simp [g1VerticalPoint])
      (by simpa [g1VerticalPoint] using ht)
  choose C T hC hT hb using hb
  obtain ⟨C₀, hC₀⟩ := (Set.finite_range C).bddAbove
  obtain ⟨T₀, hT₀⟩ := (Set.finite_range T).bddAbove
  refine ⟨max 1 C₀, max 1 T₀, lt_max_of_lt_left zero_lt_one,
    lt_max_of_lt_left zero_lt_one, ?_⟩
  intro m j t ht
  calc
    _ ≤ C (m, j) * Real.exp (-2 * Real.pi * rawUpperRate M u * t) :=
      hb (m, j) t ((hT₀ ⟨(m, j), rfl⟩).trans ((le_max_right _ _).trans ht))
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((hC₀ ⟨(m, j), rfl⟩).trans (le_max_right _ _)) (Real.exp_pos _).le

/--
The lower tail is Gaussian on the bent ray; [RW26, p. 6, p. 13].
The explicit leading coefficient is 2πβ/(cε); C₁ absorbs the linear term.
-/
theorem rawG_lower_gaussian_bound (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1) :
    ∃ C C₁ R₀ : ℝ, 0 < C ∧ 0 < C₁ ∧ 0 < R₀ ∧
      ∀ (m : Fin (M 1 0).toNat) (j : Fin ((M 1 0).toNat + 1)) (R : ℝ), R₀ ≤ R →
        ‖rawG M u (m : ℤ) (lowerPoint M δ β (m : ℤ) (j : ℤ) R)‖ ≤
          C * Real.exp (-(2 * Real.pi * β / ((M 1 0 : ℝ) * epsilon M)) * R ^ 2 + C₁ * R) := by
  let Fm : Finset ℤ := Finset.univ.image (fun m : Fin (M 1 0).toNat => (m : ℤ))
  obtain ⟨B, hB⟩ := (Set.finite_range (fun i :
      Fin (M 1 0).toNat × Fin ((M 1 0).toNat + 1) =>
        |crossing M δ (i.1 : ℤ) (i.2 : ℤ)|)).bddAbove
  obtain ⟨C, C₁, R₀, hC, hC₁, hR₀, hb⟩ :=
    rawG_affine_lower_gaussian M hM u Fm (max 0 B) β (le_max_left _ _) hβ
  refine ⟨C, C₁, R₀, hC, hC₁, hR₀, ?_⟩
  intro m j R hR
  apply hb (m : ℤ) (Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩)
    (crossing M δ (m : ℤ) (j : ℤ))
    ((hB ⟨(m, j), rfl⟩).trans (le_max_right _ _)) R hR
    (lowerPoint M δ β (m : ℤ) (j : ℤ) R)
  · change (bentPoint M δ β (m : ℤ) (j : ℤ) R).re = _
    rw [bentPoint_re]
    dsimp only [crossing]
    ring
  · exact bentPoint_im M hM δ β (m : ℤ) (j : ℤ) R

/--
Absolute convergence on the actual G1 bent contour; [RW26, p. 7, p. 13, (22)]. No lower vertical
tail is used.
-/
theorem rawG_bent_integrable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1)
    (m : ℤ) (j : Fin ((M 1 0).toNat + 1)) :
    G1BentIntegrable (rawG M u m) (crossing M δ m (j : ℤ)) (angle β) := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hs : 0 < lowerScale M β := (lowerPoint_hasDerivAt M hM δ β m 0 0).2
  have ha : 0 < 2 * Real.pi * β / ((M 1 0 : ℝ) * epsilon M) := by
    exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hβ.1)
      (mul_pos hc (epsilon_pos M hM))
  have hd : ‖g1LowerDirection (angle β)‖ = 1 := by
    simp [g1LowerDirection, Complex.norm_exp, Complex.mul_re]
  have hregular := rawG_analytic_on_paths M hM u δ β hδ hβ m j
  have hrescale (r : ℝ) :
      g1BentLowerPoint (crossing M δ m (j : ℤ)) (angle β) r =
        lowerPoint M δ β m (j : ℤ) (r / lowerScale M β) := by
    rw [lowerPoint_eq_g1 M hM δ β hβ]
    congr 1
    field_simp
  have hlcont : ContinuousOn
      (g1BentLowerPullback (rawG M u m) (crossing M δ m (j : ℤ)) (angle β)) (Ici 0) := by
    intro r hr
    have hp := hregular.1 (r / lowerScale M β) (div_nonneg hr hs.le)
    rw [← hrescale] at hp
    have hp' := hp.continuousAt.comp
      (f := fun t : ℝ => g1BentLowerPoint (crossing M δ m (j : ℤ)) (angle β) t)
      (by unfold g1BentLowerPoint; fun_prop)
    exact (hp'.mul continuousAt_const).continuousWithinAt
  have hvcont : ContinuousOn
      (g1VerticalPullback (rawG M u m) (crossing M δ m (j : ℤ))) (Ici (-1)) := by
    intro t ht
    have hp := (hregular.2 t ht).continuousAt.comp
      (f := fun s : ℝ => g1VerticalPoint (crossing M δ m (j : ℤ)) s)
      (by unfold g1VerticalPoint; fun_prop)
    exact (hp.mul continuousAt_const).continuousWithinAt
  have htail (f : ℝ → ℂ) (a : ℝ) (hf : ContinuousOn f (Ici a))
      (C κ T₀ : ℝ) (hκ : 0 < κ)
      (hb : ∀ t : ℝ, T₀ ≤ t → ‖f t‖ ≤ C * Real.exp (-κ * t)) :
      IntegrableOn f (Ici a) := by
    let T := max a T₀
    have hmid : IntegrableOn f (Icc a T) :=
      (hf.mono (fun _ ht => ht.1)).integrableOn_compact isCompact_Icc
    have hright : IntegrableOn f (Ioi T) := by
      apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hκ) T).const_mul C).mono'
        ((hf.mono (fun t ht => (le_max_left a T₀).trans ht.le)).aestronglyMeasurable
          measurableSet_Ioi)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb t ((le_max_right a T₀).trans ht.le)
    have hcover : Icc a T ∪ Ioi T = Ici a := by
      ext t
      constructor
      · rintro (⟨ha, _⟩ | ht)
        · exact ha
        · exact (le_max_left a T₀).trans ht.le
      · intro ht
        by_cases h : t ≤ T
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr (lt_of_not_ge h)
    rw [← hcover]
    exact hmid.union hright
  constructor
  · obtain ⟨C, C₁, R₀, hC, hC₁, hR₀, hb⟩ :=
      rawG_affine_lower_gaussian M hM u {m}
        |crossing M δ m (j : ℤ)| β (abs_nonneg _) hβ
    let a := 2 * Real.pi * β / ((M 1 0 : ℝ) * epsilon M)
    let T := max R₀ ((C₁ + lowerScale M β) / a)
    apply htail _ 0 hlcont C 1 (T * lowerScale M β) zero_lt_one
    intro r hr
    have hR : T ≤ r / lowerScale M β := (le_div_iff₀ hs).mpr hr
    have hR₀' : R₀ ≤ r / lowerScale M β := (le_max_left _ _).trans hR
    have hRpos : 0 ≤ r / lowerScale M β := hR₀.le.trans hR₀'
    have hbig : C₁ + lowerScale M β ≤ a * (r / lowerScale M β) := by
      simpa only [a, mul_comm] using
        (div_le_iff₀ ha).mp ((le_max_right _ _).trans hR)
    have hexp : -a * (r / lowerScale M β) ^ 2 + C₁ * (r / lowerScale M β) ≤ -r := by
      have hh := mul_le_mul_of_nonneg_right hbig hRpos
      have he : (r / lowerScale M β) * lowerScale M β = r := div_mul_cancel₀ _ hs.ne'
      nlinarith
    have hh := hb m (by simp) (crossing M δ m (j : ℤ)) (le_refl _)
      (r / lowerScale M β) hR₀' (lowerPoint M δ β m (j : ℤ) (r / lowerScale M β))
      (by change (bentPoint _ _ _ _ _ _).re = _; rw [bentPoint_re]; dsimp [crossing]; ring)
      (bentPoint_im M hM δ β m (j : ℤ) (r / lowerScale M β))
    rw [g1BentLowerPullback, hrescale, norm_mul, hd, mul_one]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_one_mul] using hexp)) hC.le)
  · obtain ⟨C, T, hC, hT, hb⟩ := rawG_upper_tail_bound M hM u m
      |crossing M δ m (j : ℤ)| (abs_nonneg _)
    have hr : 0 < rawUpperRate M u := by
      rw [(raw_rate_formulas M hM u u).1]
      exact div_pos (by exact_mod_cast hu.1) (length_pos M hM)
    apply htail _ (-1) hvcont C (2 * Real.pi * rawUpperRate M u) T (by positivity)
    intro t ht
    simpa [g1VerticalPullback, g1VerticalPoint, norm_mul, mul_assoc] using
      hb (g1VerticalPoint (crossing M δ m (j : ℤ)) t)
        (by simp [g1VerticalPoint]) (by simpa [g1VerticalPoint] using ht)

/--
Both finite closing segments vanish, with their literal directions; [RW26, p. 13].
-/
theorem closing_segments_tendsto_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1)
    (m j : Fin (M 1 0).toNat) :
    Tendsto (upperConnector M u δ (m : ℤ) (j : ℤ)) atTop (𝓝 0) ∧
      Tendsto (lowerConnector M u δ β (m : ℤ) (j : ℤ)) atTop (𝓝 0) := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hr : 0 < rawUpperRate M u := by
    rw [(raw_rate_formulas M hM u u).1]
    exact div_pos (by exact_mod_cast hu.1) (length_pos M hM)
  have hl : 0 < shiftLength M := div_pos (length_pos M hM) hc
  have ha : 0 < 2 * Real.pi * β / ((M 1 0 : ℝ) * epsilon M) := by
    exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hβ.1)
      (mul_pos hc (epsilon_pos M hM))
  constructor
  · let lo := crossing M δ (m : ℤ) ((j : ℤ) + 1)
    let hi := crossing M δ (m : ℤ) (j : ℤ)
    let B := max |lo| |hi|
    have hB : 0 ≤ B := (abs_nonneg lo).trans (le_max_left _ _)
    obtain ⟨C, T₀, hC, hT₀, hb⟩ := rawG_upper_tail_bound M hM u (m : ℤ) B hB
    have hlim : Tendsto (fun T : ℝ =>
        C * Real.exp (-2 * Real.pi * rawUpperRate M u * T) * |hi - lo|)
        atTop (𝓝 0) := by
      have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.const_mul_atTop (by positivity : 0 < 2 * Real.pi * rawUpperRate M u)
          tendsto_id)
      simpa only [Function.comp_apply, id_eq, neg_mul, mul_assoc, mul_zero, zero_mul] using
        (ht.const_mul C).mul_const |hi - lo|
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop T₀] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hxB : |x| ≤ B := by
      have hlo := abs_le.mp (le_max_left |lo| |hi|)
      have hhi := abs_le.mp (le_max_right |lo| |hi|)
      exact abs_le.mpr ⟨(le_min hlo.1 hhi.1).trans hx.1.le,
        hx.2.trans (max_le hlo.2 hhi.2)⟩
    simpa [horizontalPullback] using hb ((x : ℂ) + (T : ℂ) * Complex.I)
      (by simpa using hxB) (by simpa using hT)
  · let x₀ := crossing M δ (m : ℤ) ((j : ℤ) + 1)
    let B := |x₀| + |shiftLength M|
    obtain ⟨C, C₁, R₀, hC, hC₁, hR₀, hb⟩ := rawG_affine_lower_gaussian
      M hM u {(m : ℤ)} B β (by positivity) hβ
    let a := 2 * Real.pi * β / ((M 1 0 : ℝ) * epsilon M)
    have hlim : Tendsto (fun R : ℝ =>
        C * Real.exp (-a * R ^ 2 + C₁ * R) * |shiftLength M - 0|) atTop (𝓝 0) := by
      have hexp : Tendsto (fun R : ℝ => Real.exp (-a * R ^ 2 + C₁ * R))
          atTop (𝓝 0) := by
        apply squeeze_zero' (Eventually.of_forall (fun R => (Real.exp_pos _).le)) _
          Real.tendsto_exp_neg_atTop_nhds_zero
        filter_upwards [eventually_ge_atTop (max 0 ((C₁ + 1) / a))] with R hR
        apply Real.exp_le_exp.mpr
        have hR₀' : 0 ≤ R := (le_max_left _ _).trans hR
        have hbig : C₁ + 1 ≤ a * R := by
          simpa only [a, mul_comm] using (div_le_iff₀ ha).mp ((le_max_right _ _).trans hR)
        nlinarith [mul_le_mul_of_nonneg_right hbig hR₀']
      simpa only [mul_zero, zero_mul] using
        (hexp.const_mul C).mul_const |shiftLength M - 0|
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop R₀] with R hR
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : t ∈ Ioc 0 (shiftLength M) := by
      simpa only [uIoc_of_le hl.le] using ht
    have hx : |x₀ + t| ≤ B := by
      calc
        |x₀ + t| ≤ |x₀| + |t| := abs_add_le _ _
        _ ≤ |x₀| + |shiftLength M| := by
          rw [abs_of_pos ht'.1, abs_of_pos hl]
          linarith [ht'.2]
    apply hb (m : ℤ) (by simp) (x₀ + t) hx R hR
      (lowerPoint M δ β (m : ℤ) ((j : ℤ) + 1) R + (t : ℂ))
    · change (bentPoint M δ β (m : ℤ) ((j : ℤ) + 1) R + (t : ℂ)).re = _
      rw [Complex.add_re, Complex.ofReal_re, bentPoint_re]
      dsimp only [x₀, crossing]
      ring
    · change (bentPoint M δ β (m : ℤ) ((j : ℤ) + 1) R + (t : ℂ)).im = _
      rw [Complex.add_im, Complex.ofReal_im, add_zero, bentPoint_im M hM]

/--
Germ-to-integral bridge on the two actual parameter domains. Reuses
rawG_difference_germ, not an unrestricted point identity at comb poles; [RW26, p. 13].
-/
theorem difference_pullbacks_ae (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m : ℤ) (x β : ℝ) (hβ : 0 < β ∧ β < 1) :
    g1BentLowerPullback (differenceKernel M u m) x (angle β) =ᵐ[volume.restrict (Ici 0)]
      g1BentLowerPullback (singleKernel M u m) x (angle β) ∧
    g1VerticalPullback (differenceKernel M u m) x =ᵐ[volume.restrict (Ici (-1))]
      g1VerticalPullback (singleKernel M u m) x := by
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    have hs : 0 < Real.sqrt (1 + β ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hz : (g1BentLowerPoint x (angle β) r).im ≠ 0 := by
      rw [g1BentLowerPoint, (angle_direction β hβ).2.2]
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, Complex.div_ofReal_im,
        zero_mul, add_zero, zero_sub]
      have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ r from hr)
        (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1 : ℝ) ≤ 0) hs.le)
      linarith
    simp only [g1BentLowerPullback, differenceKernel,
      rawG_difference_nonreal M hM u m _ hz]
  · have hne : ∀ᵐ t : ℝ ∂(volume.restrict (Ici (-1))), t ≠ 0 := by
      apply ae_restrict_of_ae
      rw [ae_iff]
      simp
    filter_upwards [hne] with t ht
    have hz : (g1VerticalPoint x t).im ≠ 0 := by simpa [g1VerticalPoint] using ht
    simp only [g1VerticalPullback, differenceKernel,
      rawG_difference_nonreal M hM u m _ hz]

#check @upperRepresentative_window
#check @Telescoping.reindexing_divmod
#check @rawG_period
#check @rawG_difference_germ
#print crossing
#print lowerPoint
#print integral
#check @lowerPoint_hasDerivAt
#check @difference_pullbacks_ae

end SICLean.L4.G2.SingleBent
