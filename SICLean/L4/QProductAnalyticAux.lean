import SICLean.L4.QProductCircleAux

set_option autoImplicit false

/-!
# Joint analyticity of the q product

The product is first lifted to continuous functions on a fixed unit circle.
The locally uniform limit theorem then gives analyticity in the base parameter
with values in that Banach algebra.  The Cauchy formula recovers the other
parameter through the analytic inverse of a unit in the same algebra.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators

namespace SICLean.QProductAnalyticAux

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

/-- The product with its first argument ranging over a compact space. -/
def liftedProduct (X : C(K, ℂ)) (q : ℂ) : C(K, ℂ) :=
  ∏' j : ℕ, (1 - q ^ j • X)

lemma liftedProduct_multipliable (X : C(K, ℂ)) (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable (fun j : ℕ => (1 - q ^ j • X)) := by
  have hs : Summable (fun j : ℕ => ‖-(q ^ j • X)‖) := by
    simpa only [norm_neg, norm_smul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right ‖X‖
  simpa only [sub_eq_add_neg] using
    (multipliable_one_add_of_summable (f := fun j : ℕ => -(q ^ j • X)) hs)

lemma liftedProduct_apply (X : C(K, ℂ)) (q : ℂ) (hq : ‖q‖ < 1) (w : K) :
    liftedProduct X q w = ∏' j : ℕ, (1 - X w * q ^ j) := by
  rw [liftedProduct, ← ContinuousMap.tprod_apply (liftedProduct_multipliable X q hq)]
  simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply,
    ContinuousMap.smul_apply, smul_eq_mul, mul_comm]

lemma liftedProduct_analyticAt (X : C(K, ℂ)) (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (liftedProduct X) q := by
  obtain ⟨r, hqr, hr⟩ := exists_between hq
  have hr0 : 0 ≤ r := (norm_nonneg q).trans hqr.le
  have hu : Summable (fun j : ℕ => r ^ j * ‖X‖) :=
    (summable_geometric_of_lt_one hr0 hr).mul_right ‖X‖
  have hloc := hu.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun j (q : ℂ) => -(q ^ j • X))
    (K := {q : ℂ | ‖q‖ < r}) (isOpen_lt continuous_norm continuous_const)
    (Eventually.of_forall fun j q hq => by
      simp only [norm_neg, norm_smul, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hq.le j) (norm_nonneg _))
    (fun j => by fun_prop)
  have hd : DifferentiableOn ℂ (liftedProduct X) {q : ℂ | ‖q‖ < r} := by
    convert
      hloc.differentiableOn (Eventually.of_forall fun n => by fun_prop)
        (isOpen_lt continuous_norm continuous_const) using 1
    all_goals rfl
  exact hd.analyticAt ((isOpen_lt continuous_norm continuous_const).mem_nhds hqr)

def unitOfNoZeros (X : C(K, ℂ)) (hX : ∀ w, X w ≠ 0) : C(K, ℂ)ˣ where
  val := X
  inv := ⟨fun w => (X w)⁻¹, X.continuous.inv₀ hX⟩
  val_inv := by ext w; simp [hX w]
  inv_val := by ext w; simp [hX w]

omit [CompactSpace K] [Nonempty K] in
lemma inverse_apply (X : C(K, ℂ)) (hX : ∀ w, X w ≠ 0) (w : K) :
    Ring.inverse X w = (X w)⁻¹ := by
  change Ring.inverse (unitOfNoZeros X hX : C(K, ℂ)) w = _
  rw [Ring.inverse_unit]
  rfl

omit [Nonempty K] in
lemma kernelProduct_analyticAt (X : C(K, ℂ)) (p : ℂ × ℂ)
    (hX : ∀ w, X w - p.1 ≠ 0)
    {F : ℂ → C(K, ℂ)} (hF : AnalyticAt ℂ F p.2) :
    AnalyticAt ℂ (fun z : ℂ × ℂ =>
      Ring.inverse (X - ContinuousMap.const K z.1) * F z.2) p := by
  have hconst : AnalyticAt ℂ (fun z : ℂ × ℂ => ContinuousMap.const K z.1) p := by
    exact ((ContinuousLinearMap.const ℂ K).analyticAt p.1).comp analyticAt_fst
  have hsub : AnalyticAt ℂ (fun z : ℂ × ℂ => X - ContinuousMap.const K z.1) p :=
    analyticAt_const.sub hconst
  have hInv : AnalyticAt ℂ (Ring.inverse : C(K, ℂ) → C(K, ℂ))
      (X - ContinuousMap.const K p.1) :=
    analyticAt_inverse (𝕜 := ℂ) (unitOfNoZeros (X - ContinuousMap.const K p.1) hX)
  have hkernel : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      Ring.inverse (X - ContinuousMap.const K z.1)) p :=
    hInv.comp_of_eq hsub rfl
  exact hkernel.mul (hF.comp analyticAt_snd)

lemma differentiable_tprod_one_sub (q : ℂ) (hq : ‖q‖ < 1) :
    Differentiable ℂ (fun x : ℂ => ∏' j : ℕ, (1 - x * q ^ j)) := by
  intro x
  let R := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu : Summable (fun j : ℕ => R * ‖q‖ ^ j) :=
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left R
  have hloc := hu.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun j (z : ℂ) => -z * q ^ j)
    (K := {z : ℂ | ‖z‖ < R}) (isOpen_lt continuous_norm continuous_const)
    (Eventually.of_forall fun j z hz => by
      simp only [norm_mul, norm_neg, norm_pow]
      exact mul_le_mul_of_nonneg_right hz.le (pow_nonneg (norm_nonneg q) j))
    (fun j => by fun_prop)
  have hd : DifferentiableOn ℂ (fun x : ℂ => ∏' j : ℕ, (1 - x * q ^ j))
      {z : ℂ | ‖z‖ < R} := by
    simpa only [sub_eq_add_neg, neg_mul] using
      hloc.differentiableOn (Eventually.of_forall fun n => by fun_prop)
        (isOpen_lt continuous_norm continuous_const)
  exact hd.differentiableAt ((isOpen_lt continuous_norm continuous_const).mem_nhds
    (by dsimp [R]; linarith))

lemma sphere_sub_ne_zero (c x : ℂ) (hx : x ∈ Metric.ball c 1)
    (w : Metric.sphere c 1) : (w : ℂ) - x ≠ 0 := by
  intro h
  have hw : dist (w : ℂ) c = 1 := w.property
  have hx' : dist x c < 1 := hx
  rw [sub_eq_zero.mp h] at hw
  linarith

/-- Genuine joint analyticity, including the base value zero. -/
theorem analyticAt_tprod_one_sub (p : ℂ × ℂ) (hq : ‖p.2‖ < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => ∏' j : ℕ, (1 - z.1 * z.2 ^ j)) p := by
  let K := Metric.sphere p.1 1
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_sphere p.1 1)
  let : Nonempty K := Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr (by norm_num))
  let X : C(K, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  let H (z : ℂ × ℂ) := QProductCircleAux.normalizedCircleIntegralCLM p.1
    (Ring.inverse (X - ContinuousMap.const K z.1) * liftedProduct X z.2)
  have hH : AnalyticAt ℂ H p := by
    exact ((QProductCircleAux.normalizedCircleIntegralCLM p.1).analyticAt _).comp_of_eq
      (kernelProduct_analyticAt X p
        (fun w => sphere_sub_ne_zero p.1 p.1 (Metric.mem_ball_self (by norm_num)) w)
        (liftedProduct_analyticAt X p.2 hq)) rfl
  apply hH.congr
  have hqevent : ∀ᶠ z : ℂ × ℂ in 𝓝 p, ‖z.2‖ < 1 :=
    (isOpen_lt continuous_snd.norm continuous_const).mem_nhds hq
  have hxevent : ∀ᶠ z : ℂ × ℂ in 𝓝 p, z.1 ∈ Metric.ball p.1 1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds p.1 (by norm_num))
  filter_upwards [hqevent, hxevent] with z hzq hzx
  have hnonzero : ∀ w : K, (X - ContinuousMap.const K z.1) w ≠ 0 :=
    fun w => sphere_sub_ne_zero p.1 z.1 hzx w
  rw [show H z = QProductCircleAux.normalizedCircleIntegralCLM p.1
    (Ring.inverse (X - ContinuousMap.const K z.1) * liftedProduct X z.2) from rfl,
    QProductCircleAux.normalizedCircleIntegralCLM_eq_of_restrict p.1 _
      (fun w : ℂ => (w - z.1)⁻¹ • ∏' j : ℕ, (1 - w * z.2 ^ j)) (by
        intro w
        rw [ContinuousMap.mul_apply, inverse_apply _ hnonzero,
          liftedProduct_apply _ _ hzq]
        rfl)]
  exact (differentiable_tprod_one_sub z.2 hzq).differentiableOn.diffContOnCl
    |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzx

end SICLean.QProductAnalyticAux
