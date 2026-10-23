import SICLean.L4.FaddeevContour
import Mathlib.Analysis.Complex.CauchyIntegral
import SICLean.L4.FinitePrincipalPartsRectangleKernel

set_option autoImplicit false

/-!
# Auxiliary proofs for finite principal parts

The elementary definitions below are literal counterparts of the public definitions in
`FinitePrincipalParts`. Keeping
them here avoids an import cycle: the public theorems reduce to these fully proved results by
definitional equality. All analytic input and orientation conventions are the same as there.

Higher inverse powers have explicit primitives. The finite rectangle proof subtracts the finite
negative Laurent polynomials and fills the finitely many removable values using their local analytic
remainders. The remaining rectangle integral is zero by Cauchy-Goursat; only simple coefficients
contribute.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Interval BigOperators Topology

namespace SICLean.L4.FinitePrincipalPartsAux

/-- Literal negative Laurent polynomial, with order at most `N`. -/
def principalPart (p : ℂ) (N : ℕ) (a : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, a j / (w - p) ^ (j + 1)

/-- The coefficient actually present at exponent `-1`. -/
def residueCoefficient (N : ℕ) (a : ℕ → ℂ) : ℂ := if N = 0 then 0 else a 0

/-- A finite sum, with each center's order specified independently. -/
def finitePrincipalPart {ι : Type*} (s : Finset ι) (p : ι → ℂ)
    (N : ι → ℕ) (a : ι → ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ i ∈ s, principalPart (p i) (N i) (a i) w

/-- Full positively oriented circle: `θ` increases from `0` to `2π`. -/
def circleCCW (p : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ θ : ℝ in 0..(2 * Real.pi),
    f (circleMap p r θ) * (Complex.I * (circleMap p r θ - p))

/-- The same circle as a clockwise boundary of a hole. -/
def circleCW (p : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ θ : ℝ in (2 * Real.pi)..0,
    f (circleMap p r θ) * (Complex.I * (circleMap p r θ - p))

/-- Upper indentation from `p-r` to `p+r`, hence clockwise. -/
def upperArcCW (p : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ θ : ℝ in Real.pi..0,
    f (circleMap p r θ) * (Complex.I * (circleMap p r θ - p))

def closedRectangle (lo hi : ℂ) : Set ℂ :=
  {w | lo.re ≤ w.re ∧ w.re ≤ hi.re ∧ lo.im ≤ w.im ∧ w.im ≤ hi.im}

def openRectangle (lo hi : ℂ) : Set ℂ :=
  {w | lo.re < w.re ∧ w.re < hi.re ∧ lo.im < w.im ∧ w.im < hi.im}

/-- Bottom rightwards, right upwards, top leftwards, left downwards. -/
def rectangleCCW (lo hi : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in lo.re..hi.re, f ((x : ℂ) + (lo.im : ℂ) * Complex.I)) +
    Complex.I * (∫ y : ℝ in lo.im..hi.im,
      f ((hi.re : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ x : ℝ in lo.re..hi.re, f ((x : ℂ) + (hi.im : ℂ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in lo.im..hi.im,
      f ((lo.re : ℂ) + (y : ℂ) * Complex.I))

/-- Implementation bridge to Mathlib `circleIntegral`, whose radius is `|r|`. -/
theorem circleCCW_eq_circleIntegral (p : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (hr : 0 < r) : circleCCW p r f = ∮ w in C(p, r), f w := by
  simp only [circleCCW, circleIntegral, deriv_circleMap, circleMap_sub_center,
    smul_eq_mul, mul_comm]

/-- `intervalIntegral.integral_symm`: the sign of a hole correction. -/
theorem circleCW_eq_neg (p : ℂ) (r : ℝ) (f : ℂ → ℂ) :
    circleCW p r f = -circleCCW p r f := by
  unfold circleCW circleCCW
  exact intervalIntegral.integral_symm 0 (2 * Real.pi)

/-- Project finite principal-part calculation. Only the simple term survives. Mathlib:
`circleIntegral.integral_sub_zpow_of_ne` and `circleIntegral.integral_sub_inv_of_mem_ball`. -/
theorem circleCCW_inverse_power (p : ℂ) (r : ℝ) (k : ℕ) (hr : 0 < r) :
    circleCCW p r (fun w => 1 / (w - p) ^ (k + 1)) =
      if k = 0 then 2 * (Real.pi : ℂ) * Complex.I else 0 := by
  rw [circleCCW_eq_circleIntegral p r _ hr]
  by_cases hk : k = 0
  · simp [hk, circleIntegral.integral_sub_center_inv p hr.ne']
  · rw [if_neg hk]
    have hn : -(↑(k + 1) : ℤ) ≠ -1 := by omega
    simpa only [zpow_neg, zpow_natCast, one_div] using
      circleIntegral.integral_sub_zpow_of_ne hn p p r

private theorem principalPart_continuousOn (p : ℂ) (N : ℕ) (a : ℕ → ℂ)
    {t : Set ℂ} (ht : ∀ w ∈ t, w ≠ p) : ContinuousOn (principalPart p N a) t := by
  apply continuousOn_finsetSum
  intro j hj
  exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
    (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (ht w hw)))

private theorem principalPart_circleIntegrable (p : ℂ) (r : ℝ) (N : ℕ) (a : ℕ → ℂ)
    (hr : 0 < r) : CircleIntegrable (principalPart p N a) p r := by
  apply (principalPart_continuousOn p N a ?_).circleIntegrable hr.le
  intro w hw he
  subst w
  exact hr.ne' (by simpa using hw : (0 : ℝ) = r).symm

/-- Finite upper-arc calculation, retaining the possibly divergent high-order terms. For `k=0` the
correction is `-πi` [RW26, p. 5]. -/
theorem upperArcCW_inverse_power (p : ℂ) (r : ℝ) (k : ℕ) (hr : 0 < r) :
    upperArcCW p r (fun w => 1 / (w - p) ^ (k + 1)) =
      if k = 0 then -(Real.pi : ℂ) * Complex.I
      else ((-1 : ℂ) ^ k - 1) / ((k : ℂ) * (r : ℂ) ^ k) := by
  have hn (θ : ℝ) : circleMap p r θ - p ≠ 0 :=
    sub_ne_zero.mpr (circleMap_ne_center hr.ne')
  cases k with
  | zero =>
    have he (θ : ℝ) :
        1 / (circleMap p r θ - p) ^ (0 + 1) * (I * (circleMap p r θ - p)) = I := by
      simp only [zero_add, pow_one]
      field_simp [hn θ]
      exact div_self (hn θ)
    simp only [upperArcCW, he, ↓reduceIte]
    simp [intervalIntegral.integral_const, real_smul]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    let F : ℝ → ℂ := fun θ => ((circleMap p r θ - p) ^ (n + 1))⁻¹ / (-(n + 1 : ℂ))
    have hk : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hd (θ : ℝ) : HasDerivAt F
        (1 / (circleMap p r θ - p) ^ (n + 1 + 1) *
          (I * (circleMap p r θ - p))) θ := by
      have hu : HasDerivAt (fun θ => circleMap p r θ - p)
          ((circleMap p r θ - p) * I) θ := by
        simpa using (hasDerivAt_circleMap p r θ).sub_const p
      convert! ((hu.pow (n + 1)).inv (pow_ne_zero _ (hn θ))).div_const (-(n + 1 : ℂ)) using 1
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.pow_apply, pow_succ]
      field_simp [hn θ, pow_ne_zero n (hn θ), hk]
    have hi : IntervalIntegrable (fun θ : ℝ =>
        1 / (circleMap p r θ - p) ^ (n + 1 + 1) *
          (I * (circleMap p r θ - p))) volume Real.pi 0 := by
      apply Continuous.intervalIntegrable
      exact (continuous_const.div ((continuous_circleMap p r).sub continuous_const |>.pow _)
        (fun θ => pow_ne_zero _ (hn θ))).mul
          (continuous_const.mul ((continuous_circleMap p r).sub continuous_const))
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ) hi
    change (∫ θ : ℝ in Real.pi..0,
      1 / (circleMap p r θ - p) ^ (n + 1 + 1) * (I * (circleMap p r θ - p))) = _
    rw [he]
    dsimp [F]
    have h0 : circleMap p r 0 - p = (r : ℂ) := by simp [circleMap]
    have hpi : circleMap p r Real.pi - p = -(r : ℂ) := by
      simp [circleMap, Complex.exp_pi_mul_I]
    rw [h0, hpi, neg_pow]
    have hinv : ((-1 : ℂ) ^ (n + 1))⁻¹ = (-1 : ℂ) ^ (n + 1) := by
      rw [← inv_pow]
      norm_num
    rw [mul_inv_rev, hinv]
    simp only [Nat.cast_succ]
    field_simp [pow_ne_zero (n + 1) (Complex.ofReal_ne_zero.mpr hr.ne'), hk]
    ring

/-- Linearity plus the preceding basis integrals. -/
theorem circleCCW_principalPart (p : ℂ) (r : ℝ) (N : ℕ) (a : ℕ → ℂ)
    (hr : 0 < r) :
    circleCCW p r (principalPart p N a) =
      2 * (Real.pi : ℂ) * Complex.I * residueCoefficient N a := by
  rw [circleCCW_eq_circleIntegral p r _ hr]
  unfold principalPart
  rw [circleIntegral.integral_fun_sum]
  · have hb (j : ℕ) :
        (∮ w in C(p, r), a j / (w - p) ^ (j + 1)) =
          a j * (if j = 0 then 2 * (Real.pi : ℂ) * I else 0) := by
      have heq : (fun w : ℂ => a j / (w - p) ^ (j + 1)) =
          (fun w : ℂ => a j • (1 / (w - p) ^ (j + 1))) := by
        ext w
        simp [smul_eq_mul, div_eq_mul_inv]
      rw [heq, circleIntegral.integral_smul, ← circleCCW_eq_circleIntegral p r _ hr,
        circleCCW_inverse_power p r j hr, smul_eq_mul]
    simp_rw [hb]
    cases N with
    | zero => simp [residueCoefficient]
    | succ n =>
      rw [Finset.sum_eq_single 0]
      · simp [residueCoefficient, mul_comm]
      · intro b hb hb0
        simp [hb0]
      · simp
  · intro j hj
    apply ContinuousOn.circleIntegrable hr.le
    exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
      (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (by
        intro he
        subst w
        exact hr.ne' (by simpa using hw : (0 : ℝ) = r).symm)))

/-- Local expansion version, including orders zero and greater than one. The center value of `f` is
irrelevant to the circle integral. -/
theorem circleCCW_of_local_principalPart (f g : ℂ → ℂ) (p : ℂ) (r : ℝ)
    (N : ℕ) (a : ℕ → ℂ) (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall p r))
    (hfg : ∀ w ∈ Metric.closedBall p r, w ≠ p →
      f w = principalPart p N a w + g w) :
    circleCCW p r f = 2 * (Real.pi : ℂ) * Complex.I * residueCoefficient N a := by
  rw [circleCCW_eq_circleIntegral p r _ hr]
  have hgp : CircleIntegrable g p r :=
    (hg.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hr.le
  have hgz : (∮ w in C(p, r), g w) = 0 := by
    apply DiffContOnCl.circleIntegral_eq_zero hr.le
    apply DifferentiableOn.diffContOnCl
    exact hg.differentiableOn.mono Metric.closure_ball_subset_closedBall
  calc
    _ = ∮ w in C(p, r), principalPart p N a w + g w := by
      apply circleIntegral.integral_congr hr.le
      intro w hw
      apply hfg w (Metric.sphere_subset_closedBall hw)
      intro he
      subst w
      exact hr.ne' (by simpa using hw : (0 : ℝ) = r).symm
    _ = (∮ w in C(p, r), principalPart p N a w) + ∮ w in C(p, r), g w :=
      circleIntegral.integral_add (principalPart_circleIntegrable p r N a hr) hgp
    _ = _ := by
      rw [hgz, add_zero, ← circleCCW_eq_circleIntegral p r _ hr,
        circleCCW_principalPart p r N a hr]

/-- Finite local integral account. Disjointness is explicit, so these are separate holes. [RW26]. -/
theorem finite_circle_ledger {ι : Type*} (s : Finset ι) (f : ℂ → ℂ)
    (p : ι → ℂ) (r : ι → ℝ) (N : ι → ℕ) (a : ι → ℕ → ℂ)
    (g : ι → ℂ → ℂ) (hr : ∀ i ∈ s, 0 < r i)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Metric.closedBall (p i) (r i)) (Metric.closedBall (p j) (r j)))
    (hg : ∀ i ∈ s, AnalyticOnNhd ℂ (g i) (Metric.closedBall (p i) (r i)))
    (hfg : ∀ i ∈ s, ∀ w ∈ Metric.closedBall (p i) (r i), w ≠ p i →
      f w = principalPart (p i) (N i) (a i) w + g i w) :
    (∑ i ∈ s, circleCCW (p i) (r i) f) =
      2 * (Real.pi : ℂ) * Complex.I * ∑ i ∈ s, residueCoefficient (N i) (a i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact circleCCW_of_local_principalPart f (g i) (p i) (r i) (N i) (a i)
    (hr i hi) (hg i hi) (hfg i hi)

private def rectangleBoundary (lo hi : ℂ) : Set ℂ :=
  closedRectangle lo hi \ openRectangle lo hi

private theorem horizontal_mem_boundary (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) (x y : ℝ) (hx : x ∈ [[lo.re, hi.re]])
    (hy : y = lo.im ∨ y = hi.im) :
    (x : ℂ) + (y : ℂ) * I ∈ rectangleBoundary lo hi := by
  have hx' : lo.re ≤ x ∧ x ≤ hi.re := by simpa [uIcc_of_le hre] using hx
  rcases hy with rfl | rfl <;>
    simp_all [rectangleBoundary, closedRectangle, openRectangle]

private theorem vertical_mem_boundary (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) (x y : ℝ) (hy : y ∈ [[lo.im, hi.im]])
    (hx : x = lo.re ∨ x = hi.re) :
    (x : ℂ) + (y : ℂ) * I ∈ rectangleBoundary lo hi := by
  have hy' : lo.im ≤ y ∧ y ≤ hi.im := by simpa [uIcc_of_le him] using hy
  rcases hx with rfl | rfl <;>
    simp_all [rectangleBoundary, closedRectangle, openRectangle]

private theorem horizontal_intervalIntegrable (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f : ℂ → ℂ} (hf : ContinuousOn f (rectangleBoundary lo hi))
    (y : ℝ) (hy : y = lo.im ∨ y = hi.im) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume lo.re hi.re :=
  (hf.comp (by fun_prop) (fun x hx => horizontal_mem_boundary lo hi hre him x y hx hy)).intervalIntegrable

private theorem vertical_intervalIntegrable (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f : ℂ → ℂ} (hf : ContinuousOn f (rectangleBoundary lo hi))
    (x : ℝ) (hx : x = lo.re ∨ x = hi.re) :
    IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume lo.im hi.im :=
  (hf.comp (by fun_prop) (fun y hy => vertical_mem_boundary lo hi hre him x y hy hx)).intervalIntegrable

private theorem rectangleCCW_congr (lo hi : ℂ) (hre : lo.re ≤ hi.re)
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

private theorem rectangleCCW_sub (lo hi : ℂ) (hre : lo.re ≤ hi.re)
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

private theorem rectangleCCW_fun_sum {ι : Type*} (s : Finset ι) (lo hi : ℂ)
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

private theorem rectangleCCW_const_mul (lo hi : ℂ) (c : ℂ) (f : ℂ → ℂ) :
    rectangleCCW lo hi (fun w => c * f w) = c * rectangleCCW lo hi f := by
  simp only [rectangleCCW, intervalIntegral.integral_const_mul]
  ring

private theorem rectangleCCW_eq_zero (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedRectangle lo hi)) : rectangleCCW lo hi f = 0 := by
  have hm : ([[lo.re, hi.re]] ×ℂ [[lo.im, hi.im]]) = closedRectangle lo hi := by
    ext w
    simp [Complex.mem_reProdIm, uIcc_of_le hre, uIcc_of_le him, closedRectangle, and_assoc]
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f lo hi (hm ▸ hf)
  simp only [smul_eq_mul] at h
  unfold rectangleCCW
  linear_combination h

private theorem principalPart_analyticAt (p : ℂ) (N : ℕ) (a : ℕ → ℂ) {w : ℂ}
    (hw : w ≠ p) : AnalyticAt ℂ (principalPart p N a) w := by
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

private theorem rectangleCCW_primitive (lo hi : ℂ) (hre : lo.re ≤ hi.re)
    (him : lo.im ≤ hi.im) (F f : ℂ → ℂ)
    (hd : ∀ w ∈ rectangleBoundary lo hi, HasDerivAt F (f w) w)
    (hc : ContinuousOn f (rectangleBoundary lo hi)) : rectangleCCW lo hi f = 0 := by
  have hh (y : ℝ) (hy : y = lo.im ∨ y = hi.im) :
      (∫ x : ℝ in lo.re..hi.re, f ((x : ℂ) + (y : ℂ) * I)) =
        F ((hi.re : ℂ) + (y : ℂ) * I) - F ((lo.re : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F ((x : ℂ) + (y : ℂ) * I)) _
      (horizontal_intervalIntegrable lo hi hre him hc y hy)
    intro x hx
    have hu : HasDerivAt (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) 1 x := by
      simpa using Complex.ofRealCLM.hasDerivAt.add_const ((y : ℂ) * I)
    simpa [Function.comp_def, smul_eq_mul] using
      (hd _ (horizontal_mem_boundary lo hi hre him x y hx hy)).scomp x hu
  have hv (x : ℝ) (hx : x = lo.re ∨ x = hi.re) :
      I * (∫ y : ℝ in lo.im..hi.im, f ((x : ℂ) + (y : ℂ) * I)) =
        F ((x : ℂ) + (hi.im : ℂ) * I) - F ((x : ℂ) + (lo.im : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => F ((x : ℂ) + (y : ℂ) * I)) _
      ((vertical_intervalIntegrable lo hi hre him hc x hx).const_mul I)
    intro y hy
    have hu : HasDerivAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (x : ℂ)
    simpa [Function.comp_def, smul_eq_mul] using
      (hd _ (vertical_mem_boundary lo hi hre him x y hy hx)).scomp y hu
  unfold rectangleCCW
  rw [hh lo.im (Or.inl rfl), hh hi.im (Or.inr rfl), hv lo.re (Or.inl rfl), hv hi.re (Or.inr rfl)]
  ring

private theorem inversePower_primitive (p : ℂ) (n : ℕ) {w : ℂ} (hw : w ≠ p) :
    HasDerivAt (fun z : ℂ => ((z - p) ^ (n + 1))⁻¹ / (-(n + 1 : ℂ)))
      (1 / (w - p) ^ (n + 1 + 1)) w := by
  have hn := sub_ne_zero.mpr hw
  have hk : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  convert! ((((hasDerivAt_id w).sub_const p).pow (n + 1)).inv
    (pow_ne_zero _ hn)).div_const (-(n + 1 : ℂ)) using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.pow_apply, id_eq, mul_one, pow_succ]
  field_simp [hn, pow_ne_zero n hn, hk]

private theorem boundary_ne_center (lo hi p : ℂ) (hp : p ∈ openRectangle lo hi)
    {w : ℂ} (hw : w ∈ rectangleBoundary lo hi) : w ≠ p := by
  intro he
  exact hw.2 (he ▸ hp)

private theorem rectangleCCW_higher_inverse_power (lo hi p : ℂ) (n : ℕ)
    (hp : p ∈ openRectangle lo hi) :
    rectangleCCW lo hi (fun w => 1 / (w - p) ^ (n + 1 + 1)) = 0 := by
  have hre : lo.re ≤ hi.re := le_of_lt (hp.1.trans hp.2.1)
  have him : lo.im ≤ hi.im := le_of_lt (hp.2.2.1.trans hp.2.2.2)
  apply rectangleCCW_primitive lo hi hre him
    (fun z : ℂ => ((z - p) ^ (n + 1))⁻¹ / (-(n + 1 : ℂ)))
  · intro w hw
    exact inversePower_primitive p n (boundary_ne_center lo hi p hp hw)
  · exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
      (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (boundary_ne_center lo hi p hp hw)))

private theorem rectangleCCW_inverse_power (lo hi p : ℂ) (k : ℕ)
    (hp : p ∈ openRectangle lo hi) :
    rectangleCCW lo hi (fun w => 1 / (w - p) ^ (k + 1)) =
      if k = 0 then 2 * (Real.pi : ℂ) * I else 0 := by
  cases k with
  | zero =>
    simpa [rectangleCCW, pow_one, one_div] using
      FinitePrincipalPartsRectangleKernel.integral_boundary_rect_inv lo hi p hp
  | succ n => exact rectangleCCW_higher_inverse_power lo hi p n hp

private theorem rectangleCCW_principalPart (lo hi p : ℂ) (N : ℕ) (a : ℕ → ℂ)
    (hp : p ∈ openRectangle lo hi) :
    rectangleCCW lo hi (principalPart p N a) =
      2 * (Real.pi : ℂ) * I * residueCoefficient N a := by
  have hre : lo.re ≤ hi.re := le_of_lt (hp.1.trans hp.2.1)
  have him : lo.im ≤ hi.im := le_of_lt (hp.2.2.1.trans hp.2.2.2)
  unfold principalPart
  rw [rectangleCCW_fun_sum (Finset.range N) lo hi hre him]
  · have hb (j : ℕ) :
        rectangleCCW lo hi (fun w => a j / (w - p) ^ (j + 1)) =
          a j * (if j = 0 then 2 * (Real.pi : ℂ) * I else 0) := by
      have heq : (fun w : ℂ => a j / (w - p) ^ (j + 1)) =
          (fun w : ℂ => a j * (1 / (w - p) ^ (j + 1))) := by
        ext w
        simp [div_eq_mul_inv]
      rw [heq, rectangleCCW_const_mul, rectangleCCW_inverse_power lo hi p j hp]
    simp_rw [hb]
    cases N with
    | zero => simp [residueCoefficient]
    | succ n =>
      rw [Finset.sum_eq_single 0]
      · simp [residueCoefficient, mul_comm]
      · intro b hb hb0
        simp [hb0]
      · simp
  · intro j hj
    exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
      (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (boundary_ne_center lo hi p hp hw)))

private theorem exists_regularized_remainder {ι : Type*} (s : Finset ι)
    (f : ℂ → ℂ) (lo hi : ℂ) (p : ι → ℂ) (r : ι → ℝ)
    (N : ι → ℕ) (a : ι → ℕ → ℂ) (g : ι → ℂ → ℂ)
    (hr : ∀ i ∈ s, 0 < r i)
    (hinside : ∀ i ∈ s, Metric.closedBall (p i) (r i) ⊆ openRectangle lo hi)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Metric.closedBall (p i) (r i)) (Metric.closedBall (p j) (r j)))
    (hf : AnalyticOnNhd ℂ f (closedRectangle lo hi \ (p '' (s : Set ι))))
    (hg : ∀ i ∈ s, AnalyticOnNhd ℂ (g i) (Metric.closedBall (p i) (r i)))
    (hfg : ∀ i ∈ s, ∀ w ∈ Metric.closedBall (p i) (r i), w ≠ p i →
      f w = principalPart (p i) (N i) (a i) w + g i w) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (closedRectangle lo hi) ∧
      EqOn H (fun w => f w - finitePrincipalPart s p N a w) (rectangleBoundary lo hi) := by
  classical
  let t : Set ℂ := p '' (s : Set ι)
  let q : ℂ → ℂ := fun w => f w - finitePrincipalPart s p N a w
  let H : ℂ → ℂ := fun w => if w ∈ t then limUnder (𝓝[≠] w) q else q w
  have htclosed : IsClosed t := (s.finite_toSet.image p).isClosed
  have hc (i : ι) (his : i ∈ s) : p i ∈ Metric.closedBall (p i) (r i) :=
    Metric.mem_closedBall_self (hr i his).le
  have hnoother (i : ι) (his : i ∈ s) (w : ℂ)
      (hw : w ∈ Metric.closedBall (p i) (r i)) (j : ι) (hjs : j ∈ s)
      (he : w = p j) : j = i := by
    by_contra hji
    exact Set.disjoint_left.mp (hdisj i his j hjs (Ne.symm hji)) hw (he ▸ hc j hjs)
  have hsep (i : ι) (his : i ∈ s) (j : ι) (hjs : j ∈ s) (hji : j ≠ i) :
      p i ≠ p j := by
    intro he
    exact hji (hnoother i his (p i) (hc i his) j hjs he)
  have hHoff (w : ℂ) (hw : w ∉ t) : H w = q w := by simp [H, hw]
  have hqana (w : ℂ) (hw : w ∈ closedRectangle lo hi \ t) : AnalyticAt ℂ q w := by
    apply (hf w hw).sub
    apply Finset.analyticAt_fun_sum
    intro i his
    apply principalPart_analyticAt
    intro he
    exact hw.2 ⟨i, his, he.symm⟩
  have hHcenter (i : ι) (his : i ∈ s) : AnalyticAt ℂ H (p i) := by
    let L : ℂ → ℂ := fun w => g i w -
      ∑ j ∈ s.erase i, principalPart (p j) (N j) (a j) w
    have hLana : AnalyticAt ℂ L (p i) := by
      apply (hg i his (p i) (hc i his)).sub
      apply Finset.analyticAt_fun_sum
      intro j hjs
      exact principalPart_analyticAt (p j) (N j) (a j)
        (hsep i his j (Finset.mem_erase.mp hjs).2 (Finset.mem_erase.mp hjs).1)
    have hqLpoint (w : ℂ) (hw : w ∈ Metric.closedBall (p i) (r i)) (hne : w ≠ p i) :
        q w = L w := by
      dsimp only [q, L, finitePrincipalPart]
      rw [hfg i his w hw hne, ← Finset.sum_erase_add s
        (fun j => principalPart (p j) (N j) (a j) w) his]
      ring
    have hqL : q =ᶠ[𝓝[≠] (p i)] L := by
      apply eventually_nhdsWithin_iff.mpr
      filter_upwards [Metric.closedBall_mem_nhds (p i) (hr i his)] with w hw hne
      exact hqLpoint w hw hne
    have hlim : Tendsto q (𝓝[≠] (p i)) (𝓝 (L (p i))) :=
      (hLana.continuousAt.tendsto.mono_left inf_le_left).congr' hqL.symm
    have hvalue : H (p i) = L (p i) := by
      dsimp only [H]
      rw [if_pos (show p i ∈ t from ⟨i, his, rfl⟩)]
      exact hlim.limUnder_eq
    apply hLana.congr
    filter_upwards [Metric.closedBall_mem_nhds (p i) (hr i his)] with w hw
    by_cases he : w = p i
    · simpa only [he] using hvalue.symm
    · have hwt : w ∉ t := by
        rintro ⟨j, hjs, hjw⟩
        have hji := hnoother i his w hw j hjs hjw.symm
        exact he (hji ▸ hjw.symm)
      rw [hHoff w hwt, hqLpoint w hw he]
  refine ⟨H, ?_, ?_⟩
  · intro w hw
    by_cases hwt : w ∈ t
    · rcases hwt with ⟨i, his, rfl⟩
      exact (hHcenter i his).differentiableAt.differentiableWithinAt
    · apply ((hqana w ⟨hw, hwt⟩).congr ?_).differentiableAt.differentiableWithinAt
      filter_upwards [htclosed.isOpen_compl.mem_nhds hwt] with z hz
      exact (hHoff z hz).symm
  · intro w hw
    apply hHoff
    rintro ⟨i, his, hpi⟩
    exact hw.2 (hpi ▸ hinside i his (hc i his))

/-- Finite rectangular ledger with three directly usable conclusions: outer boundary = positive
small circles, outer + hole boundaries = 0, and the explicit sum of simple coefficients. No boundary
pole is allowed. [RW26, p. 5]. All analytic input is stated, rather than assuming the desired
ledger. -/
theorem rectangle_finite_principal_parts {ι : Type*} (s : Finset ι)
    (f : ℂ → ℂ) (lo hi : ℂ) (p : ι → ℂ) (r : ι → ℝ)
    (N : ι → ℕ) (a : ι → ℕ → ℂ) (g : ι → ℂ → ℂ)
    (hre : lo.re < hi.re) (him : lo.im < hi.im)
    (hr : ∀ i ∈ s, 0 < r i)
    (hinside : ∀ i ∈ s, Metric.closedBall (p i) (r i) ⊆ openRectangle lo hi)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Metric.closedBall (p i) (r i)) (Metric.closedBall (p j) (r j)))
    (hf : AnalyticOnNhd ℂ f (closedRectangle lo hi \ (p '' (s : Set ι))))
    (hg : ∀ i ∈ s, AnalyticOnNhd ℂ (g i) (Metric.closedBall (p i) (r i)))
    (hfg : ∀ i ∈ s, ∀ w ∈ Metric.closedBall (p i) (r i), w ≠ p i →
      f w = principalPart (p i) (N i) (a i) w + g i w) :
    rectangleCCW lo hi f = (∑ i ∈ s, circleCCW (p i) (r i) f) ∧
      rectangleCCW lo hi f + (∑ i ∈ s, circleCW (p i) (r i) f) = 0 ∧
      rectangleCCW lo hi f =
        2 * (Real.pi : ℂ) * Complex.I * ∑ i ∈ s, residueCoefficient (N i) (a i) := by
  classical
  have hp (i : ι) (his : i ∈ s) : p i ∈ openRectangle lo hi :=
    hinside i his (Metric.mem_closedBall_self (hr i his).le)
  have hboundary : rectangleBoundary lo hi ⊆
      closedRectangle lo hi \ (p '' (s : Set ι)) := by
    intro w hw
    refine ⟨hw.1, ?_⟩
    rintro ⟨i, his, he⟩
    exact hw.2 (he ▸ hp i his)
  have hPcont : ContinuousOn (finitePrincipalPart s p N a) (rectangleBoundary lo hi) := by
    apply continuousOn_finsetSum
    intro i his
    exact principalPart_continuousOn (p i) (N i) (a i)
      (fun w hw => boundary_ne_center lo hi (p i) (hp i his) hw)
  obtain ⟨H, hHd, hHe⟩ := exists_regularized_remainder s f lo hi p r N a g hr hinside hdisj hf hg hfg
  have hHrect : rectangleCCW lo hi H = 0 := rectangleCCW_eq_zero lo hi hre.le him.le hHd
  have hrectP : rectangleCCW lo hi f = rectangleCCW lo hi (finitePrincipalPart s p N a) := by
    have he := rectangleCCW_congr lo hi hre.le him.le hHe
    rw [rectangleCCW_sub lo hi hre.le him.le (hf.continuousOn.mono hboundary) hPcont] at he
    linear_combination -he + hHrect
  have hPrect : rectangleCCW lo hi (finitePrincipalPart s p N a) =
      2 * (Real.pi : ℂ) * I * ∑ i ∈ s, residueCoefficient (N i) (a i) := by
    change rectangleCCW lo hi (fun w => ∑ i ∈ s, principalPart (p i) (N i) (a i) w) = _
    rw [rectangleCCW_fun_sum s lo hi hre.le him.le]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i his
      exact rectangleCCW_principalPart lo hi (p i) (N i) (a i) (hp i his)
    · intro i his
      exact principalPart_continuousOn (p i) (N i) (a i)
        (fun w hw => boundary_ne_center lo hi (p i) (hp i his) hw)
  have hcircles := finite_circle_ledger s f p r N a g hr hdisj hg hfg
  have houter : rectangleCCW lo hi f = ∑ i ∈ s, circleCCW (p i) (r i) f :=
    (hrectP.trans hPrect).trans hcircles.symm
  refine ⟨houter, ?_, hrectP.trans hPrect⟩
  simp_rw [circleCW_eq_neg, Finset.sum_neg_distrib]
  rw [houter, add_neg_cancel]

end SICLean.L4.FinitePrincipalPartsAux
