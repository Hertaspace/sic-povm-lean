import SICLean.L4.G1RatioTailBounds
import SICLean.L4.ModularClusterLedger

set_option autoImplicit false

/-!
# Finite circle and directed-rectangle accounts

These elementary interfaces keep all comparisons punctured at the listed centers. They allow
arbitrary finite real supports, including centers outside the integration region. No theorem from
`G1FiniteChainLedger` is imported.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1FiniteChainLedgerAux

def closedBox (B R : ℝ) : Set ℂ :=
  FinitePrincipalParts.closedRectangle (g1VerticalPoint (-B) (-R)) (g1VerticalPoint B R)

def principalParts (P : Finset ℝ) (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (z : ℂ) : ℂ :=
  FinitePrincipalParts.finitePrincipalPart P (fun x => (x : ℂ)) N A z

def baselineJump (x₀ x₁ a : ℝ) : ℤ :=
  (if a < x₁ then 1 else 0) - (if a < x₀ then 1 else 0)

theorem principalPart_analyticAt (p : ℂ) (N : ℕ) (a : ℕ → ℂ) {w : ℂ}
    (hw : w ≠ p) : AnalyticAt ℂ (FinitePrincipalParts.principalPart p N a) w := by
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

theorem principalPart_continuousOn (p : ℂ) (N : ℕ) (a : ℕ → ℂ)
    {s : Set ℂ} (hs : ∀ w ∈ s, w ≠ p) :
    ContinuousOn (FinitePrincipalParts.principalPart p N a) s := by
  apply continuousOn_finsetSum
  intro j hj
  exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
    (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (hs w hw)))

theorem circle_integral_inverse_power (c p : ℂ) (r : ℝ) (k : ℕ)
    (hr : 0 < r) (hsafe : dist p c ≠ r) :
    (∮ w in C(c, r), 1 / (w - p) ^ (k + 1)) =
      if k = 0 ∧ dist p c < r then 2 * (Real.pi : ℂ) * I else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [zero_add, pow_one, one_div, true_and]
    by_cases hp : dist p c < r
    · rw [if_pos hp]
      exact circleIntegral.integral_sub_inv_of_mem_ball hp
    · rw [if_neg hp]
      have hfar : r < dist p c := lt_of_le_of_ne (le_of_not_gt hp) hsafe.symm
      apply DiffContOnCl.circleIntegral_eq_zero hr.le
      apply DifferentiableOn.diffContOnCl
      intro w hw
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.inv
      · exact differentiableAt_id.sub_const p
      · apply sub_ne_zero.mpr
        intro he
        subst w
        exact (not_le_of_gt hfar) (Metric.closure_ball_subset_closedBall hw)
  · rw [if_neg (by simp [hk])]
    have hn : -(↑(k + 1) : ℤ) ≠ -1 := by omega
    simpa only [zpow_neg, zpow_natCast, one_div] using
      circleIntegral.integral_sub_zpow_of_ne hn c p r

theorem circle_integral_principalPart (c p : ℂ) (r : ℝ) (N : ℕ) (a : ℕ → ℂ)
    (hr : 0 < r) (hsafe : dist p c ≠ r) :
    (∮ w in C(c, r), FinitePrincipalParts.principalPart p N a w) =
      2 * (Real.pi : ℂ) * I *
        (if dist p c < r then FinitePrincipalParts.residueCoefficient N a else 0) := by
  unfold FinitePrincipalParts.principalPart
  rw [circleIntegral.integral_fun_sum]
  · have hb (j : ℕ) :
        (∮ w in C(c, r), a j / (w - p) ^ (j + 1)) =
          a j * (if j = 0 ∧ dist p c < r then 2 * (Real.pi : ℂ) * I else 0) := by
      have he : (fun w : ℂ => a j / (w - p) ^ (j + 1)) =
          (fun w : ℂ => a j * (1 / (w - p) ^ (j + 1))) := by
        ext w
        simp [div_eq_mul_inv]
      rw [he, circleIntegral.integral_const_mul, circle_integral_inverse_power c p r j hr hsafe]
    simp_rw [hb]
    by_cases hp : dist p c < r
    · cases N with
      | zero => simp [FinitePrincipalParts.residueCoefficient]
      | succ n =>
        rw [Finset.sum_eq_single 0]
        · simp [hp, FinitePrincipalParts.residueCoefficient, mul_comm]
        · intro b hb hb0
          simp [hb0]
        · simp
    · simp [hp]
  · intro j hj
    apply ContinuousOn.circleIntegrable hr.le
    exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
      (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (by
        intro he
        subst w
        exact hsafe hw)))

/-- A finite circle account, with no restriction on the number or location of the poles away from
its boundary. -/
theorem circle_finite_ledger (f g : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (B R r ρ : ℝ) (hρ : 0 < ρ)
    (hinside : Metric.closedBall (r : ℂ) ρ ⊆ closedBox B R)
    (hsafe : ∀ x ∈ P, |x - r| ≠ ρ)
    (hg : AnalyticOnNhd ℂ g (closedBox B R))
    (hfg : ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      f z = principalParts P N A z + g z) :
    FinitePrincipalParts.circleCCW (r : ℂ) ρ f =
      2 * (Real.pi : ℂ) * I *
        ∑ x ∈ P, if |x - r| < ρ then
          FinitePrincipalParts.residueCoefficient (N x) (A x) else 0 := by
  have hdist (x : ℝ) : dist (x : ℂ) (r : ℂ) = |x - r| := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hne (w : ℂ) (hw : w ∈ Metric.sphere (r : ℂ) ρ) (x : ℝ) (hx : x ∈ P) :
      w ≠ (x : ℂ) := by
    intro he
    subst w
    have hw' : dist (x : ℂ) (r : ℂ) = ρ := hw
    exact hsafe x hx (by rwa [hdist] at hw')
  have hP : CircleIntegrable (principalParts P N A) (r : ℂ) ρ := by
    apply ContinuousOn.circleIntegrable hρ.le
    apply continuousOn_finsetSum
    intro x hx
    exact principalPart_continuousOn _ _ _ (fun w hw => hne w hw x hx)
  have hgd : AnalyticOnNhd ℂ g (Metric.closedBall (r : ℂ) ρ) := hg.mono hinside
  have hgi : CircleIntegrable g (r : ℂ) ρ :=
    (hgd.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hρ.le
  have hgz : (∮ w in C((r : ℂ), ρ), g w) = 0 := by
    apply DiffContOnCl.circleIntegral_eq_zero hρ.le
    apply DifferentiableOn.diffContOnCl
    exact hgd.differentiableOn.mono Metric.closure_ball_subset_closedBall
  rw [FinitePrincipalParts.circleCCW_eq_circleIntegral _ _ _ hρ]
  calc
    _ = ∮ w in C((r : ℂ), ρ), principalParts P N A w + g w := by
      apply circleIntegral.integral_congr hρ.le
      intro w hw
      apply hfg w (hinside (Metric.sphere_subset_closedBall hw))
      rintro ⟨x, hx, he⟩
      exact hne w hw x hx he.symm
    _ = ∮ w in C((r : ℂ), ρ), principalParts P N A w := by
      rw [circleIntegral.integral_add hP hgi, hgz, add_zero]
    _ = _ := by
      unfold principalParts FinitePrincipalParts.finitePrincipalPart
      rw [circleIntegral.integral_fun_sum]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        simpa only [hdist] using circle_integral_principalPart (r : ℂ) (x : ℂ) ρ
          (N x) (A x) hρ (by simpa only [hdist] using hsafe x hx)
      · intro x hx
        exact (principalPart_continuousOn _ _ _
          (fun w hw => hne w hw x hx)).circleIntegrable hρ.le

open FinitePrincipalParts

def rectangleBoundary (lo hi : ℂ) : Set ℂ :=
  closedRectangle lo hi \ openRectangle lo hi

theorem horizontal_mem_boundary (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) (x y : ℝ) (hx : x ∈ [[lo.re, hi.re]])
    (hy : y = lo.im ∨ y = hi.im) :
    (x : ℂ) + (y : ℂ) * I ∈ rectangleBoundary lo hi := by
  have hx' : lo.re ≤ x ∧ x ≤ hi.re := by simpa [uIcc_of_le hre] using hx
  rcases hy with rfl | rfl <;>
    simp_all [rectangleBoundary, closedRectangle, openRectangle]

theorem vertical_mem_boundary (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) (x y : ℝ) (hy : y ∈ [[lo.im, hi.im]])
    (hx : x = lo.re ∨ x = hi.re) :
    (x : ℂ) + (y : ℂ) * I ∈ rectangleBoundary lo hi := by
  have hy' : lo.im ≤ y ∧ y ≤ hi.im := by simpa [uIcc_of_le him] using hy
  rcases hx with rfl | rfl <;>
    simp_all [rectangleBoundary, closedRectangle, openRectangle]

theorem horizontal_intervalIntegrable (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f : ℂ → ℂ} (hf : ContinuousOn f (rectangleBoundary lo hi))
    (y : ℝ) (hy : y = lo.im ∨ y = hi.im) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume lo.re hi.re :=
  (hf.comp (by fun_prop) (fun x hx => horizontal_mem_boundary lo hi hre him x y hx hy)).intervalIntegrable

theorem vertical_intervalIntegrable (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f : ℂ → ℂ} (hf : ContinuousOn f (rectangleBoundary lo hi))
    (x : ℝ) (hx : x = lo.re ∨ x = hi.re) :
    IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume lo.im hi.im :=
  (hf.comp (by fun_prop) (fun y hy => vertical_mem_boundary lo hi hre him x y hy hx)).intervalIntegrable

theorem rectangleCCW_congr (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f g : ℂ → ℂ} (he : EqOn f g (rectangleBoundary lo hi)) :
    rectangleCCW lo hi f = rectangleCCW lo hi g := by
  have hh (y : ℝ) (hy : y = lo.im ∨ y = hi.im) :
      (∫ x : ℝ in lo.re..hi.re, f ((x : ℂ) + (y : ℂ) * I)) =
        ∫ x : ℝ in lo.re..hi.re, g ((x : ℂ) + (y : ℂ) * I) :=
    intervalIntegral.integral_congr (fun x hx => he (horizontal_mem_boundary lo hi hre him x y hx hy))
  have hv (x : ℝ) (hx : x = lo.re ∨ x = hi.re) :
      (∫ y : ℝ in lo.im..hi.im, f ((x : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ in lo.im..hi.im, g ((x : ℂ) + (y : ℂ) * I) :=
    intervalIntegral.integral_congr (fun y hy => he (vertical_mem_boundary lo hi hre him x y hy hx))
  simp only [rectangleCCW, hh lo.im (Or.inl rfl), hh hi.im (Or.inr rfl),
    hv lo.re (Or.inl rfl), hv hi.re (Or.inr rfl)]

theorem rectangleCCW_sub (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f g : ℂ → ℂ}
    (hf : ContinuousOn f (rectangleBoundary lo hi)) (hg : ContinuousOn g (rectangleBoundary lo hi)) :
    rectangleCCW lo hi (fun w => f w - g w) = rectangleCCW lo hi f - rectangleCCW lo hi g := by
  unfold rectangleCCW
  rw [intervalIntegral.integral_sub (horizontal_intervalIntegrable lo hi hre him hf _ (Or.inl rfl))
      (horizontal_intervalIntegrable lo hi hre him hg _ (Or.inl rfl)),
    intervalIntegral.integral_sub (horizontal_intervalIntegrable lo hi hre him hf _ (Or.inr rfl))
      (horizontal_intervalIntegrable lo hi hre him hg _ (Or.inr rfl)),
    intervalIntegral.integral_sub (vertical_intervalIntegrable lo hi hre him hf _ (Or.inl rfl))
      (vertical_intervalIntegrable lo hi hre him hg _ (Or.inl rfl)),
    intervalIntegral.integral_sub (vertical_intervalIntegrable lo hi hre him hf _ (Or.inr rfl))
      (vertical_intervalIntegrable lo hi hre him hg _ (Or.inr rfl))]
  ring

theorem rectangleCCW_fun_sum {ι : Type*} (s : Finset ι) (lo hi : ℂ)
    (hre : lo.re ≤ hi.re) (him : lo.im ≤ hi.im) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (rectangleBoundary lo hi)) :
    rectangleCCW lo hi (fun w => ∑ i ∈ s, f i w) = ∑ i ∈ s, rectangleCCW lo hi (f i) := by
  unfold rectangleCCW
  rw [intervalIntegral.integral_finsetSum (fun i his =>
      horizontal_intervalIntegrable lo hi hre him (hf i his) _ (Or.inl rfl)),
    intervalIntegral.integral_finsetSum (fun i his =>
      horizontal_intervalIntegrable lo hi hre him (hf i his) _ (Or.inr rfl)),
    intervalIntegral.integral_finsetSum (fun i his =>
      vertical_intervalIntegrable lo hi hre him (hf i his) _ (Or.inl rfl)),
    intervalIntegral.integral_finsetSum (fun i his =>
      vertical_intervalIntegrable lo hi hre him (hf i his) _ (Or.inr rfl))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem rectangleCCW_const_mul (lo hi : ℂ) (c : ℂ) (f : ℂ → ℂ) :
    rectangleCCW lo hi (fun w => c * f w) = c * rectangleCCW lo hi f := by
  simp only [rectangleCCW, intervalIntegral.integral_const_mul]
  ring

theorem rectangleCCW_eq_zero (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedRectangle lo hi)) : rectangleCCW lo hi f = 0 := by
  have hm : ([[lo.re, hi.re]] ×ℂ [[lo.im, hi.im]]) = closedRectangle lo hi := by
    ext w
    simp [Complex.mem_reProdIm, uIcc_of_le hre, uIcc_of_le him, closedRectangle, and_assoc]
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f lo hi (hm ▸ hf)
  simp only [smul_eq_mul] at h
  unfold rectangleCCW
  linear_combination h


theorem rectangleCCW_add (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f g : ℂ → ℂ}
    (hf : ContinuousOn f (rectangleBoundary lo hi))
    (hg : ContinuousOn g (rectangleBoundary lo hi)) :
    rectangleCCW lo hi (fun w => f w + g w) = rectangleCCW lo hi f + rectangleCCW lo hi g := by
  unfold rectangleCCW
  rw [intervalIntegral.integral_add (horizontal_intervalIntegrable lo hi hre him hf _ (Or.inl rfl))
      (horizontal_intervalIntegrable lo hi hre him hg _ (Or.inl rfl)),
    intervalIntegral.integral_add (horizontal_intervalIntegrable lo hi hre him hf _ (Or.inr rfl))
      (horizontal_intervalIntegrable lo hi hre him hg _ (Or.inr rfl)),
    intervalIntegral.integral_add (vertical_intervalIntegrable lo hi hre him hf _ (Or.inl rfl))
      (vertical_intervalIntegrable lo hi hre him hg _ (Or.inl rfl)),
    intervalIntegral.integral_add (vertical_intervalIntegrable lo hi hre him hf _ (Or.inr rfl))
      (vertical_intervalIntegrable lo hi hre him hg _ (Or.inr rfl))]
  ring

/-- A single finite principal part inside a rectangle. The singleton use of the existing
finite-principal-parts API avoids any simple-pole assumption. -/
theorem rectangleCCW_principalPart (lo hi p : ℂ) (N : ℕ) (a : ℕ → ℂ)
    (hp : p ∈ openRectangle lo hi) :
    rectangleCCW lo hi (FinitePrincipalParts.principalPart p N a) =
      2 * (Real.pi : ℂ) * I * residueCoefficient N a := by
  have hU : IsOpen (openRectangle lo hi) := by
    exact (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_lt continuous_re continuous_const).inter
        ((isOpen_lt continuous_const continuous_im).inter
          (isOpen_lt continuous_im continuous_const)))
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU p hp
  have hr : 0 < ε / 2 := half_pos hε
  have hball : Metric.closedBall p (ε / 2) ⊆ openRectangle lo hi :=
    (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hεU
  have hf : AnalyticOnNhd ℂ (FinitePrincipalParts.principalPart p N a)
      (closedRectangle lo hi \ ((fun _ : Unit => p) '' (({()} : Finset Unit) : Set Unit))) := by
    intro w hw
    apply principalPart_analyticAt
    intro he
    apply hw.2
    exact ⟨(), by simp, he.symm⟩
  have h := FinitePrincipalParts.rectangle_finite_principal_parts ({()} : Finset Unit)
    (FinitePrincipalParts.principalPart p N a) lo hi (fun _ => p) (fun _ => ε / 2)
    (fun _ => N) (fun _ => a) (fun _ _ => 0)
    (hp.1.trans hp.2.1) (hp.2.2.1.trans hp.2.2.2)
    (by intro i hi; exact hr) (by intro i hi; exact hball)
    (by intro i hi j hj hij; exact (hij (Subsingleton.elim _ _)).elim) hf
    (by intro i hi w hw; exact analyticAt_const)
    (by intro i hi w hw hwp; simp)
  simpa using h.2.2

theorem rectangle_finite_ledger_of_lt (f g : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (B R x₀ x₁ : ℝ)
    (hR : 0 < R) (hx₀ : |x₀| < B) (hx₁ : |x₁| < B) (horder : x₀ < x₁)
    (hsafe₀ : x₀ ∉ P) (hsafe₁ : x₁ ∉ P)
    (hg : AnalyticOnNhd ℂ g (closedBox B R))
    (hfg : ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      f z = principalParts P N A z + g z) :
    rectangleCCW (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) f =
      2 * (Real.pi : ℂ) * I * ∑ x ∈ P,
        if x₀ < x ∧ x < x₁ then residueCoefficient (N x) (A x) else 0 := by
  let lo := g1VerticalPoint x₀ (-R)
  let hi := g1VerticalPoint x₁ R
  have hre : lo.re < hi.re := by simpa [lo, hi, g1VerticalPoint] using horder
  have him : lo.im < hi.im := by simp [lo, hi, g1VerticalPoint]; linarith
  have hbox : closedRectangle lo hi ⊆ closedBox B R := by
    intro w hw
    have hb₀ := (abs_lt.mp hx₀).1
    have hb₁ := (abs_lt.mp hx₁).2
    simp only [closedRectangle, lo, hi, g1VerticalPoint, add_re, ofReal_re,
      mul_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_self, add_zero,
      add_im, mul_im, mul_one, zero_add, Set.mem_setOf_eq] at hw
    simp only [closedBox, closedRectangle, g1VerticalPoint, add_re, ofReal_re,
      mul_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_self, add_zero,
      add_im, mul_im, mul_one, zero_add, Set.mem_setOf_eq]
    exact ⟨hb₀.le.trans hw.1, hw.2.1.trans hb₁.le, hw.2.2⟩
  have hne (x : ℝ) (hx : x ∈ P) (w : ℂ) (hw : w ∈ rectangleBoundary lo hi) :
      w ≠ (x : ℂ) := by
    intro he
    subst w
    have hclosed : x₀ ≤ x ∧ x ≤ x₁ := by
      have := hw.1
      simpa [closedRectangle, lo, hi, g1VerticalPoint, hR.le] using this
    have hzero : x₀ < x := lt_of_le_of_ne hclosed.1 (by
      intro he
      apply hsafe₀
      simpa [he] using hx)
    have hone : x < x₁ := lt_of_le_of_ne hclosed.2 (by
      intro he
      apply hsafe₁
      simpa [he] using hx)
    apply hw.2
    simpa [openRectangle, lo, hi, g1VerticalPoint] using
      (show x₀ < x ∧ x < x₁ ∧ -R < 0 ∧ 0 < R from ⟨hzero, hone, by linarith, hR⟩)
  have hPc : ContinuousOn (principalParts P N A) (rectangleBoundary lo hi) := by
    apply continuousOn_finsetSum
    intro x hx
    exact principalPart_continuousOn _ _ _ (fun w hw => hne x hx w hw)
  have hgc : ContinuousOn g (rectangleBoundary lo hi) :=
    (hg.mono hbox).continuousOn.mono (fun w hw => hw.1)
  have hgz : rectangleCCW lo hi g = 0 :=
    rectangleCCW_eq_zero lo hi hre.le him.le (hg.mono hbox).differentiableOn
  have hterm (x : ℝ) (hx : x ∈ P) :
      rectangleCCW lo hi (FinitePrincipalParts.principalPart (x : ℂ) (N x) (A x)) =
        2 * (Real.pi : ℂ) * I *
          (if x₀ < x ∧ x < x₁ then residueCoefficient (N x) (A x) else 0) := by
    by_cases hxinside : x₀ < x ∧ x < x₁
    · rw [if_pos hxinside]
      apply rectangleCCW_principalPart
      simpa [openRectangle, lo, hi, g1VerticalPoint] using
        (show x₀ < x ∧ x < x₁ ∧ -R < 0 ∧ 0 < R from
          ⟨hxinside.1, hxinside.2, by linarith, hR⟩)
    · rw [if_neg hxinside, mul_zero]
      apply rectangleCCW_eq_zero lo hi hre.le him.le
      intro w hw
      apply AnalyticAt.differentiableWithinAt
      apply principalPart_analyticAt
      intro he
      subst w
      have hclosed : x₀ ≤ x ∧ x ≤ x₁ := by
        simpa [closedRectangle, lo, hi, g1VerticalPoint, hR.le] using hw
      apply hxinside
      constructor
      · exact lt_of_le_of_ne hclosed.1 (by
          intro he
          apply hsafe₀
          simpa [he] using hx)
      · exact lt_of_le_of_ne hclosed.2 (by
          intro he
          apply hsafe₁
          simpa [he] using hx)
  change rectangleCCW lo hi f = _
  calc
    _ = rectangleCCW lo hi (fun w => principalParts P N A w + g w) := by
      apply rectangleCCW_congr lo hi hre.le him.le
      intro w hw
      apply hfg w (hbox hw.1)
      rintro ⟨x, hx, he⟩
      exact hne x hx w hw he.symm
    _ = rectangleCCW lo hi (principalParts P N A) := by
      rw [rectangleCCW_add lo hi hre.le him.le hPc hgc, hgz, add_zero]
    _ = _ := by
      unfold principalParts finitePrincipalPart
      rw [rectangleCCW_fun_sum P lo hi hre.le him.le]
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hterm
      · intro x hx
        exact principalPart_continuousOn _ _ _ (fun w hw => hne x hx w hw)

theorem rectangleCCW_swap_baselines (f : ℂ → ℂ) (x₀ x₁ R : ℝ) :
    rectangleCCW (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) f =
      -rectangleCCW (g1VerticalPoint x₁ (-R)) (g1VerticalPoint x₀ R) f := by
  simp only [rectangleCCW, g1VerticalPoint, add_re, ofReal_re, mul_re, I_re,
    mul_zero, ofReal_im, I_im, zero_mul, sub_self, add_zero, add_im, mul_im,
    mul_one, zero_add]
  rw [intervalIntegral.integral_symm x₀ x₁, intervalIntegral.integral_symm x₀ x₁]
  ring

theorem baselineJump_ascending (x₀ x₁ x : ℝ) (horder : x₀ < x₁) (hx : x ≠ x₀) :
    baselineJump x₀ x₁ x = if x₀ < x ∧ x < x₁ then 1 else 0 := by
  unfold baselineJump
  by_cases hleft : x < x₀
  · simp [hleft, hleft.trans horder, not_lt_of_gt hleft]
  · have hstrict : x₀ < x := lt_of_le_of_ne (le_of_not_gt hleft) hx.symm
    simp [hleft, hstrict]

/-- Directed rectangle account for either ordering of the baselines, including equal baselines. All
integral comparisons exclude the finite support. -/
theorem rectangle_finite_ledger (f g : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (B R x₀ x₁ : ℝ)
    (hR : 0 < R) (hx₀ : |x₀| < B) (hx₁ : |x₁| < B)
    (hsafe₀ : x₀ ∉ P) (hsafe₁ : x₁ ∉ P)
    (hg : AnalyticOnNhd ℂ g (closedBox B R))
    (hfg : ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      f z = principalParts P N A z + g z) :
    rectangleCCW (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) f =
      2 * (Real.pi : ℂ) * I * ∑ x ∈ P,
        (baselineJump x₀ x₁ x : ℂ) * residueCoefficient (N x) (A x) := by
  have hasc (a b : ℝ) (ha : |a| < B) (hb : |b| < B) (hab : a < b)
      (hsafea : a ∉ P) (hsafeb : b ∉ P) :
      rectangleCCW (g1VerticalPoint a (-R)) (g1VerticalPoint b R) f =
        2 * (Real.pi : ℂ) * I * ∑ x ∈ P,
          (baselineJump a b x : ℂ) * residueCoefficient (N x) (A x) := by
    rw [rectangle_finite_ledger_of_lt f g P N A B R a b hR ha hb hab hsafea hsafeb hg hfg]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [baselineJump_ascending a b x hab (by
      intro he
      apply hsafea
      simpa [he] using hx)]
    split_ifs <;> simp
  rcases lt_trichotomy x₀ x₁ with hord | heq | hord
  · exact hasc x₀ x₁ hx₀ hx₁ hord hsafe₀ hsafe₁
  · subst x₁
    simp [rectangleCCW, g1VerticalPoint, baselineJump]
  · rw [rectangleCCW_swap_baselines,
      hasc x₁ x₀ hx₁ hx₀ hord hsafe₁ hsafe₀, ← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have hswap : baselineJump x₀ x₁ x = -baselineJump x₁ x₀ x := by
      unfold baselineJump
      ring
    rw [hswap, Int.cast_neg, neg_mul]

/-! The actual ratio kernel: real candidate centers and analytic removal of all finitely many
principal parts. -/

def candidatePoles (M : SL(2, ℤ)) (τ y : ℝ) (n p m : ℤ) : Set ℝ :=
  g1NumeratorPoles M τ n m ∪ g1InversePoles M τ y n p m

def orderBudget (M : SL(2, ℤ)) (τ w y : ℝ) (n h ell p m : ℤ) (x : ℝ) : ℕ :=
  ModularCluster.poleBudget M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)
    (x : ℂ) (τ : ℂ)

theorem branch_real_mem (M : SL(2, ℤ)) (τ w y : ℝ) (n h ell p m : ℤ)
    (b : ModularCluster.Label)
    (hb : b ∈ ModularCluster.labels M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)) :
    ∃ x ∈ candidatePoles M τ y n p m,
      ModularCluster.branchPoint M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)
        (τ : ℂ) b = (x : ℂ) := by
  rcases b with ⟨b, K, J⟩
  cases b with
  | false =>
    have hb' : (K, J) ∈ modularPhiZeroLabels M (m + p) n := by
      simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
    let x : ℝ := ((n : ℝ) - 1 - ((m : ℝ) + (p : ℝ)) * g1T M τ -
      (K : ℝ) * g1T M τ - (J : ℝ)) / (M 1 0 : ℝ) - y
    have he : (x : ℂ) = modularPhiZeroPoint M (m + p) n (τ : ℂ) K J - (y : ℂ) := by
      dsimp [x, modularPhiZeroPoint, etaDenom, g1T]
      push_cast
      rfl
    refine ⟨x, Or.inr ⟨K, J, hb', he⟩, ?_⟩
    simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using he.symm
  | true =>
    have hb' : (K, J) ∈ modularPhiPoleLabels M (m + 1) n := by
      simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
    let x : ℝ := ((n : ℝ) - (((m : ℝ) + 1) - 1) * g1T M τ +
      (K : ℝ) * g1T M τ + (J : ℝ)) / (M 1 0 : ℝ)
    have he : (x : ℂ) = modularPhiPolePoint M (m + 1) n (τ : ℂ) K J := by
      dsimp [x, modularPhiPolePoint, etaDenom, g1T]
      push_cast
      rfl
    refine ⟨x, Or.inl ⟨K, J, hb', he⟩, ?_⟩
    simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using he.symm

theorem candidate_has_label (M : SL(2, ℤ)) (τ w y x : ℝ) (n h ell p m : ℤ)
    (hx : x ∈ candidatePoles M τ y n p m) :
    ∃ b ∈ ModularCluster.labels M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m),
      ModularCluster.branchPoint M (G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m)
        (τ : ℂ) b = (x : ℂ) := by
  rcases hx with ⟨K, J, hlabel, he⟩ | ⟨K, J, hlabel, he⟩
  · refine ⟨(true, K, J), ?_, ?_⟩
    · simpa [ModularCluster.labels, G1Pinch.ratioData] using hlabel
    · simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using he.symm
  · refine ⟨(false, K, J), ?_, ?_⟩
    · simpa [ModularCluster.labels, G1Pinch.ratioData] using hlabel
    · simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using he.symm

theorem finite_regularized_remainder {ι : Type*} (P : Finset ι)
    (p : ι → ℂ) (hp : Function.Injective p) (f : ℂ → ℂ) (S : Set ℂ)
    (N : ι → ℕ) (A : ι → ℕ → ℂ) (g : ι → ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (S \ p '' (P : Set ι)))
    (hg : ∀ i ∈ P, AnalyticAt ℂ (g i) (p i))
    (hfg : ∀ i ∈ P, f =ᶠ[𝓝[≠] (p i)]
      (fun z => FinitePrincipalParts.principalPart (p i) (N i) (A i) z + g i z)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H S ∧
      ∀ z ∈ S, z ∉ p '' (P : Set ι) →
        f z = FinitePrincipalParts.finitePrincipalPart P p N A z + H z := by
  let t : Set ℂ := p '' (P : Set ι)
  let q : ℂ → ℂ := fun z => f z - FinitePrincipalParts.finitePrincipalPart P p N A z
  let H : ℂ → ℂ := fun z => if z ∈ t then limUnder (𝓝[≠] z) q else q z
  have htclosed : IsClosed t := (P.finite_toSet.image p).isClosed
  have hHoff (z : ℂ) (hz : z ∉ t) : H z = q z := by simp [H, hz]
  have hqana (z : ℂ) (hz : z ∈ S \ t) : AnalyticAt ℂ q z := by
    apply (hf z hz).sub
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact principalPart_analyticAt (p i) (N i) (A i)
      (fun he => hz.2 ⟨i, hi, he.symm⟩)
  have hHcenter (i : ι) (hi : i ∈ P) : AnalyticAt ℂ H (p i) := by
    let L : ℂ → ℂ := fun z => g i z -
      ∑ j ∈ P.erase i, FinitePrincipalParts.principalPart (p j) (N j) (A j) z
    have hLana : AnalyticAt ℂ L (p i) := by
      apply (hg i hi).sub
      apply Finset.analyticAt_fun_sum
      intro j hj
      exact principalPart_analyticAt (p j) (N j) (A j)
        (fun he => (Finset.mem_erase.mp hj).1 (hp he).symm)
    have hqL : q =ᶠ[𝓝[≠] (p i)] L := by
      filter_upwards [hfg i hi] with z hz
      dsimp only [q, L, FinitePrincipalParts.finitePrincipalPart]
      rw [hz, ← Finset.sum_erase_add P
        (fun j => FinitePrincipalParts.principalPart (p j) (N j) (A j) z) hi]
      ring
    have hlim : Tendsto q (𝓝[≠] (p i)) (𝓝 (L (p i))) :=
      (hLana.continuousAt.tendsto.mono_left inf_le_left).congr' hqL.symm
    have hvalue : H (p i) = L (p i) := by
      dsimp only [H]
      rw [if_pos (show p i ∈ t from ⟨i, hi, rfl⟩)]
      exact hlim.limUnder_eq
    let u : Set ℂ := p '' (P.erase i : Set ι)
    have hclosed : IsClosed u := ((P.erase i).finite_toSet.image p).isClosed
    have hnot : p i ∉ u := by
      rintro ⟨j, hj, he⟩
      exact (Finset.mem_erase.mp hj).1 (hp he)
    have hqL' : ∀ᶠ z in 𝓝 (p i), z ≠ p i → q z = L z :=
      eventually_nhdsWithin_iff.mp hqL
    apply hLana.congr
    filter_upwards [hclosed.isOpen_compl.mem_nhds hnot, hqL'] with z hz hqz
    by_cases he : z = p i
    · simpa only [he] using hvalue.symm
    · have hzt : z ∉ t := by
        rintro ⟨j, hj, hjz⟩
        by_cases hji : j = i
        · exact he (hji ▸ hjz.symm)
        · exact hz ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, hjz⟩
      rw [hHoff z hzt, hqz he]
  refine ⟨H, ?_, ?_⟩
  · intro z hz
    by_cases hzt : z ∈ t
    · rcases hzt with ⟨i, hi, rfl⟩
      exact hHcenter i hi
    · apply (hqana z ⟨hz, hzt⟩).congr
      filter_upwards [htclosed.isOpen_compl.mem_nhds hzt] with w hw
      exact (hHoff w hw).symm
  · intro z hz hzt
    rw [hHoff z hzt]
    dsimp only [q]
    ring

theorem exists_finite_principalParts (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y B R : ℝ) (n h ell p m : ℤ) (hT : 0 < g1T M τ)
    (hB : 0 < B) (hR : 0 < R) (P : Finset ℝ)
    (hP : (P : Set ℝ) = candidatePoles M τ y n p m ∩ Icc (-B) B) :
    ∃ (A : ℝ → ℕ → ℂ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g (closedBox B R) ∧
        ∀ z ∈ closedBox B R, z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
          g1RatioKernel M τ w y n h ell p m z =
            principalParts P (orderBudget M τ w y n h ell p m) A z + g z := by
  let k := G1Pinch.ratioData (w : ℂ) (y : ℂ) n h ell p m
  let f : ℂ → ℂ := fun z => ModularCluster.kernel M k z (τ : ℂ)
  have hτ : (τ : ℂ) ∈ modularPhiDomain M := real_mem_modularPhiDomain M τ hT
  obtain ⟨δ, C, hδ, hδdom, hcenters, hradii, hdisj, hiso, hcapture⟩ :=
    ModularCluster.exists_fixed_circles M hM k (τ : ℂ) hτ B hB.le
  have hτδ : (τ : ℂ) ∈ Metric.closedBall (τ : ℂ) δ := Metric.mem_closedBall_self hδ.le
  have hlocal : ∀ x : ℝ, ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), x ∈ P →
      AnalyticAt ℂ g (x : ℂ) ∧
      f =ᶠ[𝓝[≠] (x : ℂ)] (fun z => FinitePrincipalParts.principalPart
        (x : ℂ) (orderBudget M τ w y n h ell p m x) A z + g z) := by
    intro x
    by_cases hx : x ∈ P
    · have hxP : x ∈ candidatePoles M τ y n p m ∩ Icc (-B) B := by
        rw [← hP]
        exact hx
      have hxC : (x : ℂ) ∈ C.centers := by
        change (x : ℂ) ∈ (C.centers : Set ℂ)
        rw [hcenters]
        refine ⟨?_, ?_⟩
        · simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr hxP.2
        · exact candidate_has_label M τ w y x n h ell p m hxP.1
      have hxiso : ∀ b ∈ ModularCluster.labels M k,
          dist (ModularCluster.branchPoint M k (τ : ℂ) b) (x : ℂ) ≤ C.radius (x : ℂ) →
          ModularCluster.branchPoint M k (τ : ℂ) b = (x : ℂ) := by
        intro b hb hdist
        by_contra hne
        exact (not_lt_of_ge hdist) ((hiso (x : ℂ) hxC b hb (τ : ℂ) hτδ).2 hne)
      obtain ⟨A, g, hg, hfg⟩ := ModularCluster.exists_local_principalPart
        M hM k (τ : ℂ) (x : ℂ) hτ (C.radius (x : ℂ)) (hradii (x : ℂ) hxC).1 hxiso
      refine ⟨A, g, fun _ => ⟨?_, ?_⟩⟩
      · exact hg (x : ℂ) (Metric.mem_closedBall_self (hradii (x : ℂ) hxC).1.le)
      · apply eventually_nhdsWithin_iff.mpr
        filter_upwards [Metric.closedBall_mem_nhds (x : ℂ) (hradii (x : ℂ) hxC).1]
          with z hz hne
        exact hfg z hz hne
    · exact ⟨fun _ => 0, fun _ => 0, fun hx' => (hx hx').elim⟩
  choose A g hAg using hlocal
  have hf : AnalyticOnNhd ℂ f
      (closedBox B R \ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ)) := by
    intro z hz
    have hreg : (z, (τ : ℂ)) ∈ ModularCluster.regularDomain M k := by
      apply (ModularCluster.regularDomain_iff_no_labels M hM k z (τ : ℂ)).mpr
      refine ⟨hτ, ?_⟩
      intro b hb he
      obtain ⟨x, hx, hbx⟩ := branch_real_mem M τ w y n h ell p m b hb
      have hzx : z = (x : ℂ) := he.trans hbx
      have hxB : x ∈ Icc (-B) B := by
        have hz' : -B ≤ z.re ∧ z.re ≤ B ∧ -R ≤ z.im ∧ z.im ≤ R := by
          simpa only [closedBox, FinitePrincipalParts.closedRectangle, g1VerticalPoint,
            Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
            Complex.add_im, Complex.mul_im, mul_one, zero_add, mem_ofPred_eq] using hz.1
        rw [hzx] at hz'
        exact ⟨hz'.1, hz'.2.1⟩
      apply hz.2
      refine ⟨x, ?_, hzx.symm⟩
      rw [hP]
      exact ⟨hx, hxB⟩
    exact (ModularCluster.kernel_joint_analytic M hM k (z, (τ : ℂ)) hreg).curry_left
  obtain ⟨H, hH, hfH⟩ := finite_regularized_remainder P (fun x : ℝ => (x : ℂ))
    Complex.ofReal_injective f (closedBox B R) (orderBudget M τ w y n h ell p m) A g
    hf (fun x hx => (hAg x hx).1) (fun x hx => (hAg x hx).2)
  refine ⟨A, H, hH, ?_⟩
  intro z hz hn
  rw [G1Pinch.g1RatioKernel_eq_kernel]
  exact hfH z hz hn

end SICLean.L4.G1FiniteChainLedgerAux
