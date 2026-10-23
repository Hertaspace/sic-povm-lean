import SICLean.L4.ModularClusterRegularity
import SICLean.L4.FinitePrincipalParts
import SICLean.L4.ModularClusterIntegralsAux

set_option autoImplicit false

/-!
# Common pullback majorants and circle limits

Real-boundary limit theorems. [RW26, p. 6] limits are formalized here.
The fixed CCW parametrization is exactly `circleCCW`, including its
Jacobian. All bounds are on the whole cluster circle; none is an estimate
on an individual simple-pole residue. Full complex neighborhoods imply
both one-sided limits, with no irrationality restriction.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators MatrixGroups Interval Classical

namespace SICLean.L4.ModularCluster

/-- Literal pullback including dz/dθ, with positive orientation. -/
def circleKernel (M : SL(2, ℤ)) (k : KernelData) (a : ℂ) (r : ℝ)
    (τ : ℂ) (θ : ℝ) : ℂ :=
  kernel M k (circleMap a r θ) τ * (Complex.I * (circleMap a r θ - a))

/-- Actual circle integral of the existing Φ kernel. -/
def circleContribution (M : SL(2, ℤ)) (k : KernelData)
    (a : ℂ) (r : ℝ) (τ : ℂ) : ℂ :=
  FinitePrincipalParts.circleCCW a r (fun z => kernel M k z τ)

/--
Exact parametrization, including the Jacobian. [RW26, p. 6].
-/
theorem circleContribution_eq_integral (M : SL(2, ℤ)) (k : KernelData)
    (a : ℂ) (r : ℝ) (τ : ℂ) :
    circleContribution M k a r τ =
      ∫ θ : ℝ in 0..(2 * Real.pi), circleKernel M k a r τ θ := by
  rfl

/--
Arc-length factor is r for positive radii; [RW26, p. 6] sets; circle convention.
-/
theorem norm_circleKernel (M : SL(2, ℤ)) (k : KernelData)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (τ : ℂ) (θ : ℝ) :
    ‖circleKernel M k a r τ θ‖ = r * ‖kernel M k (circleMap a r θ) τ‖ := by
  have hsub : circleMap a r θ - a = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [circleMap_sub_center, circleMap_zero]
  rw [circleKernel, norm_mul]
  have h2 : ‖Complex.I * (circleMap a r θ - a)‖ = r := by
    rw [hsub, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_I, one_mul]
  rw [h2, mul_comm]

/--
Joint continuity on fixed compact angle/parameter rectangles; [RW26, p. 6] divisor sets.
-/
theorem continuousOn_circleKernel (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ a : ℂ) (ρ r : ℝ) (hr : 0 < r)
    (hsafe : ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ z ∈ Metric.sphere a r,
      (z, τ) ∈ regularDomain M k) :
    ContinuousOn (fun q : ℂ × ℝ => circleKernel M k a r q.1 q.2)
      (Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi)) := by
  have hk : ContinuousOn (fun q : ℂ × ℂ => kernel M k q.1 q.2) (regularDomain M k) :=
    (kernel_joint_analytic M hM k).continuousOn
  have hmap : Continuous (fun q : ℂ × ℝ => (circleMap a r q.2, q.1)) :=
    ((continuous_circleMap a r).comp continuous_snd).prodMk continuous_fst
  have hmt : MapsTo (fun q : ℂ × ℝ => (circleMap a r q.2, q.1))
      (Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi)) (regularDomain M k) := by
    intro q hq
    exact hsafe q.1 hq.1 (circleMap a r q.2) (circleMap_mem_sphere a (le_of_lt hr) q.2)
  have hcomp := hk.comp hmap.continuousOn hmt
  have hcomp' : ContinuousOn (fun q : ℂ × ℝ => kernel M k (circleMap a r q.2) q.1)
      (Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi)) := by
    refine hcomp.congr ?_
    intro q _
    rfl
  have hfac : Continuous (fun q : ℂ × ℝ => Complex.I * (circleMap a r q.2 - a)) :=
    continuous_const.mul (((continuous_circleMap a r).comp continuous_snd).sub continuous_const)
  have hprod := hcomp'.mul hfac.continuousOn
  refine hprod.congr ?_
  intro q _
  rfl

/--
A single explicit constant function is an integrable majorant on the
finite angle interval, simultaneously for all circles and parameters.
[RW26, p. 6]. The majorant is stated on a full ball.
-/
theorem exists_uniform_circle_majorant (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M) (C : Circles)
    (hr : ∀ a ∈ C.centers, 0 < C.radius a)
    (hsafe : ∀ z ∈ boundaries C, (z, τ₀) ∈ regularDomain M k) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧ Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      IntervalIntegrable (fun _ : ℝ => B) volume 0 (2 * Real.pi) ∧
      ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ a ∈ C.centers,
        (∀ z ∈ Metric.sphere a (C.radius a), (z, τ) ∈ regularDomain M k) ∧
        ∀ θ ∈ Icc 0 (2 * Real.pi), ‖circleKernel M k a (C.radius a) τ θ‖ ≤ B := by
  obtain ⟨ρ, B₀, hρ, hB₀, hball, hbound⟩ :=
    exists_uniform_boundary_bound M hM k τ₀ hτ₀ C hsafe
  have hterm : ∀ x ∈ C.centers, 0 ≤ C.radius x * B₀ := fun x hx =>
    mul_nonneg (le_of_lt (hr x hx)) (le_of_lt hB₀)
  have hsum : 0 ≤ ∑ x ∈ C.centers, C.radius x * B₀ :=
    Finset.sum_nonneg hterm
  refine ⟨ρ, 1 + ∑ x ∈ C.centers, C.radius x * B₀, hρ, by linarith, hball,
    intervalIntegrable_const, ?_⟩
  intro τ hτ a ha
  have hreg : ∀ z ∈ Metric.sphere a (C.radius a), (z, τ) ∈ regularDomain M k :=
    fun z hz => (hbound τ hτ z ⟨a, ha, hz⟩).1
  refine ⟨hreg, ?_⟩
  intro θ hθ
  have hz : circleMap a (C.radius a) θ ∈ Metric.sphere a (C.radius a) :=
    circleMap_mem_sphere a (le_of_lt (hr a ha)) θ
  have hkern : ‖kernel M k (circleMap a (C.radius a) θ) τ‖ ≤ B₀ :=
    (hbound τ hτ _ ⟨a, ha, hz⟩).2
  rw [norm_circleKernel M k a (C.radius a) (hr a ha) τ θ]
  have hle : C.radius a * B₀ ≤ ∑ x ∈ C.centers, C.radius x * B₀ :=
    Finset.single_le_sum hterm ha
  have hmul : C.radius a * ‖kernel M k (circleMap a (C.radius a) θ) τ‖ ≤
      C.radius a * B₀ :=
    mul_le_mul_of_nonneg_left hkern (le_of_lt (hr a ha))
  linarith

/--
Ordinary interval integrability; center point values are irrelevant; [RW26, p. 6] sets.
-/
theorem intervalIntegrable_circleKernel (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (r : ℝ) (hr : 0 < r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ) ∈ regularDomain M k) :
    IntervalIntegrable (circleKernel M k a r τ) volume 0 (2 * Real.pi) := by
  have hker := continuousOn_circleKernel M hM k τ a 0 r hr (by
    intro τ' hτ' z hz
    have hτ'' : τ' = τ := by simpa using hτ'
    subst hτ''
    exact hsafe z hz)
  have hmap : ContinuousOn (fun θ : ℝ => (τ, θ)) (Icc 0 (2 * Real.pi)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmt : MapsTo (fun θ : ℝ => (τ, θ)) (Icc 0 (2 * Real.pi))
      (Metric.closedBall τ (0 : ℝ) ×ˢ Icc 0 (2 * Real.pi)) := by
    intro θ hθ
    exact ⟨by simp, hθ⟩
  have hcomp := hker.comp hmap hmt
  have hcont : ContinuousOn (fun θ : ℝ => circleKernel M k a r τ θ) (Icc 0 (2 * Real.pi)) := by
    refine hcomp.congr ?_
    intro θ _
    rfl
  exact hcont.intervalIntegrable_of_Icc (by positivity)

/--
Pointwise pullback limit from the full complex parameter neighborhood; [RW26, p. 6] divisor sets.
-/
theorem circleKernel_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ a : ℂ) (r : ℝ) (hr : 0 < r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ₀) ∈ regularDomain M k) (θ : ℝ) :
    Tendsto (fun τ => circleKernel M k a r τ θ) (𝓝 τ₀)
      (𝓝 (circleKernel M k a r τ₀ θ)) := by
  have hmem : (circleMap a r θ, τ₀) ∈ regularDomain M k :=
    hsafe _ (circleMap_mem_sphere a (le_of_lt hr) θ)
  have hcont : ContinuousAt (fun q : ℂ × ℂ => kernel M k q.1 q.2)
      (circleMap a r θ, τ₀) :=
    (kernel_joint_analytic M hM k _ hmem).continuousAt
  have hmap : ContinuousAt (fun τ : ℂ => (circleMap a r θ, τ)) τ₀ :=
    continuousAt_const.prodMk continuousAt_id
  have hcomp := hcont.comp hmap
  have hmul : ContinuousAt
      (fun τ => kernel M k (circleMap a r θ) τ * (Complex.I * (circleMap a r θ - a))) τ₀ :=
    hcomp.mul continuousAt_const
  simpa [circleKernel] using hmul.tendsto

/--
Uniform limit on the entire finite collection of circle parametrizations. [RW26, p. 6].
-/
theorem uniform_circleKernel_limit (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (C : Circles)
    (hr : ∀ a ∈ C.centers, 0 < C.radius a)
    (hsafe : ∀ z ∈ boundaries C, (z, τ₀) ∈ regularDomain M k) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ τ : ℂ, dist τ τ₀ < δ → ∀ a ∈ C.centers, ∀ θ ∈ Icc 0 (2 * Real.pi),
        ‖circleKernel M k a (C.radius a) τ θ -
          circleKernel M k a (C.radius a) τ₀ θ‖ < ε := by
  intro ε hε
  by_cases hne : C.centers.Nonempty
  · have hne' : C.centers.Nonempty := hne
    obtain ⟨a₀, ha₀⟩ := hne'
    have hτ₀ : τ₀ ∈ modularPhiDomain M :=
      (hsafe _ ⟨a₀, ha₀, circleMap_mem_sphere a₀ (le_of_lt (hr a₀ ha₀)) 0⟩).1
    obtain ⟨ρ, hρ, -, hsafeρ⟩ :=
      exists_regular_boundary_tube M hM k τ₀ hτ₀ C hsafe
    have hscomp : IsCompact (Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi)) :=
      (isCompact_closedBall τ₀ ρ).prod isCompact_Icc
    have hδ : ∀ a ∈ C.centers, ∃ d : ℝ, 0 < d ∧
        ∀ x ∈ Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi),
          ∀ y ∈ Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi),
            dist x y < d →
              dist (circleKernel M k a (C.radius a) x.1 x.2)
                (circleKernel M k a (C.radius a) y.1 y.2) < ε := by
      intro a ha
      have hcont : ContinuousOn
          (fun q : ℂ × ℝ => circleKernel M k a (C.radius a) q.1 q.2)
          (Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi)) :=
        continuousOn_circleKernel M hM k τ₀ a ρ (C.radius a) (hr a ha) (by
          intro τ hτ z hz
          exact hsafeρ τ hτ z ⟨a, ha, hz⟩)
      have huni := hscomp.uniformContinuousOn_of_continuous hcont
      rw [Metric.uniformContinuousOn_iff] at huni
      exact huni ε hε
    let D : ℂ → ℝ := fun a => if ha : a ∈ C.centers then Classical.choose (hδ a ha) else 1
    have hDpos : ∀ a ∈ C.centers, 0 < D a := by
      intro a ha
      simp only [D, dif_pos ha]
      exact (Classical.choose_spec (hδ a ha)).1
    have hDprop : ∀ a ∈ C.centers,
        ∀ x ∈ Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi),
          ∀ y ∈ Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi),
            dist x y < D a →
              dist (circleKernel M k a (C.radius a) x.1 x.2)
                (circleKernel M k a (C.radius a) y.1 y.2) < ε := by
      intro a ha
      simp only [D, dif_pos ha]
      exact (Classical.choose_spec (hδ a ha)).2
    have hinfpos : 0 < C.centers.inf' hne D := by
      rw [Finset.lt_inf'_iff]
      exact fun a ha => hDpos a ha
    refine ⟨min ρ (C.centers.inf' hne D), lt_min hρ hinfpos, ?_⟩
    intro τ hτ a ha θ hθ
    have hτball : τ ∈ Metric.closedBall τ₀ ρ := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (hτ.trans_le (min_le_left ρ _))
    have hx : (τ, θ) ∈ Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi) :=
      ⟨hτball, hθ⟩
    have hy : (τ₀, θ) ∈ Metric.closedBall τ₀ ρ ×ˢ Icc 0 (2 * Real.pi) :=
      ⟨by rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hρ, hθ⟩
    have hlt : dist (τ, θ) (τ₀, θ) < D a := by
      rw [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)]
      exact hτ.trans_le (le_trans (min_le_right ρ _) (Finset.inf'_le D ha))
    have := hDprop a ha (τ, θ) hx (τ₀, θ) hy hlt
    simpa [dist_eq_norm] using this
  · refine ⟨1, one_pos, ?_⟩
    intro τ _ a ha θ _
    exact absurd ⟨a, ha⟩ hne

/--
Ordinary parameter continuity of the entire circle contribution; [RW26, p. 6] sets.
-/
theorem continuousAt_circleContribution (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ a : ℂ) (r : ℝ) (hr : 0 < r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ₀) ∈ regularDomain M k) :
    ContinuousAt (circleContribution M k a r) τ₀ := by
  have hτ₀ : τ₀ ∈ modularPhiDomain M :=
    (hsafe _ (circleMap_mem_sphere a (le_of_lt hr) 0)).1
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hsafeC : ∀ z ∈ boundaries (⟨{a}, fun _ => r⟩ : Circles),
      (z, τ₀) ∈ regularDomain M k := by
    intro z hz
    rcases hz with ⟨a', ha', hz'⟩
    simp only [Finset.mem_singleton] at ha'
    subst ha'
    exact hsafe z hz'
  have hradius : ∀ x ∈ (⟨{a}, fun _ => r⟩ : Circles).centers,
      0 < (⟨{a}, fun _ => r⟩ : Circles).radius x := by
    intro x _
    simpa using hr
  obtain ⟨ρ, B, hρ, hB, hball, hIntB, hmaj⟩ :=
    exists_uniform_circle_majorant M hM k τ₀ hτ₀ ⟨{a}, fun _ => r⟩ hradius hsafeC
  set ε' : ℝ := ε / (2 * Real.pi + 2) with hε'def
  have hε' : 0 < ε' := by
    rw [hε'def]
    exact div_pos hε (by positivity)
  have hε'bound : ε' * (2 * Real.pi) < ε := by
    rw [hε'def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi + 2)]
    nlinarith [Real.pi_pos, hε]
  obtain ⟨δ₀, hδ₀, hδ₀prop⟩ :=
    uniform_circleKernel_limit M hM k τ₀ ⟨{a}, fun _ => r⟩ hradius hsafeC ε' hε'
  refine ⟨min δ₀ ρ, lt_min hδ₀ hρ, ?_⟩
  intro y hy
  have hyball : y ∈ Metric.closedBall τ₀ ρ := by
    rw [Metric.mem_closedBall]
    exact le_of_lt (hy.trans_le (min_le_right δ₀ ρ))
  have hregy : ∀ z ∈ Metric.sphere a r, (z, y) ∈ regularDomain M k :=
    fun z hz => (hmaj y hyball a (by simp)).1 z hz
  have hIy := intervalIntegrable_circleKernel M hM k y a r hr hregy
  have hI0 := intervalIntegrable_circleKernel M hM k τ₀ a r hr hsafe
  have hdiff : ∀ θ ∈ Ι 0 (2 * Real.pi),
      ‖circleKernel M k a r y θ - circleKernel M k a r τ₀ θ‖ ≤ ε' := by
    intro θ hθ
    rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at hθ
    exact le_of_lt (hδ₀prop y (hy.trans_le (min_le_left δ₀ ρ)) a (by simp) θ
      (Ioc_subset_Icc_self hθ))
  calc dist (circleContribution M k a r y) (circleContribution M k a r τ₀)
      = ‖circleContribution M k a r y - circleContribution M k a r τ₀‖ :=
        dist_eq_norm _ _
    _ = ‖∫ θ in 0..(2 * Real.pi),
          (circleKernel M k a r y θ - circleKernel M k a r τ₀ θ)‖ := by
        rw [circleContribution_eq_integral, circleContribution_eq_integral,
          intervalIntegral.integral_sub hIy hI0]
    _ ≤ ε' * |2 * Real.pi - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hdiff
    _ = ε' * (2 * Real.pi) := by rw [sub_zero, abs_of_pos (by positivity)]
    _ < ε := hε'bound

/--
Direct full-neighborhood limit interface; [RW26, p. 6] sets.
-/
theorem circleContribution_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ a : ℂ) (r : ℝ) (hr : 0 < r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ₀) ∈ regularDomain M k) :
    Tendsto (circleContribution M k a r) (𝓝 τ₀)
      (𝓝 (circleContribution M k a r τ₀)) :=
  (continuousAt_circleContribution M hM k τ₀ a r hr hsafe).tendsto

/--
Upper-side real boundary, including rational τ₀ and multiple poles; [RW26, p. 6] sets.
-/
theorem circleContribution_tendsto_upper (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, (τ₀ : ℂ)) ∈ regularDomain M k) :
    Tendsto (circleContribution M k a r) (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (circleContribution M k a r (τ₀ : ℂ))) :=
  (circleContribution_tendsto M hM k (τ₀ : ℂ) a r hr hsafe).mono_left
    nhdsWithin_le_nhds

/--
The lower-side version uses the same parametrization and the divisor sets of [RW26, p. 6]. No lower
q-product sum is used.
-/
theorem circleContribution_tendsto_lower (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, (τ₀ : ℂ)) ∈ regularDomain M k) :
    Tendsto (circleContribution M k a r) (𝓝[{τ : ℂ | τ.im < 0}] (τ₀ : ℂ))
      (𝓝 (circleContribution M k a r (τ₀ : ℂ))) :=
  (circleContribution_tendsto M hM k (τ₀ : ℂ) a r hr hsafe).mono_left
    nhdsWithin_le_nhds

/--
Useful concrete bound for finite circle corrections; [RW26, p. 6] sets. This does not estimate split
residues.
-/
theorem norm_circleContribution_le (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (r B : ℝ) (hr : 0 < r) (hB : 0 ≤ B)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ) ∈ regularDomain M k)
    (hbound : ∀ z ∈ Metric.sphere a r, ‖kernel M k z τ‖ ≤ B) :
    ‖circleContribution M k a r τ‖ ≤ 2 * Real.pi * r * B := by
  rw [circleContribution_eq_integral]
  have h : ∀ θ ∈ Ι 0 (2 * Real.pi),
      ‖circleKernel M k a r τ θ‖ ≤ r * B := by
    intro θ _
    rw [norm_circleKernel M k a r hr τ θ]
    exact mul_le_mul_of_nonneg_left
      (hbound _ (circleMap_mem_sphere a (le_of_lt hr) θ)) (le_of_lt hr)
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const h
  calc ‖∫ θ in 0..(2 * Real.pi), circleKernel M k a r τ θ‖
      ≤ (r * B) * |2 * Real.pi - 0| := hmain
    _ = 2 * Real.pi * r * B := by
        rw [sub_zero, abs_of_pos (by positivity)]
        ring

/--
Joint analytic circle contribution for the local removable-value
argument, with the circle fixed while τ, w, and y vary.
The joint-chart input extends the fixed-w, y statement. [RW26, p. 6].
This does not assert analyticity of a raw
ratio at a removable center inside the circle.
-/
theorem analyticAt_circleContribution_parameters (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ a : ℂ) (r : ℝ) (hr : 0 < r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ₀) ∈ regularDomain M k) :
    AnalyticAt ℂ
      (fun q : ℂ × ℂ × ℂ =>
        circleContribution M (withParameters k q.2.1 q.2.2) a r q.1)
      (τ₀, k.w, k.y) := by
  have hτ₀ : τ₀ ∈ modularPhiDomain M :=
    (hsafe _ (circleMap_mem_sphere a hr.le 0)).1
  let C : Circles := ⟨{a}, fun _ => r⟩
  obtain ⟨ρ, B, hρ, hB, hball, hbound⟩ :=
    finite_family_uniform_boundary_bound_parameters M hM {k} τ₀ hτ₀ (fun _ => C) (by
      intro k' hk' z hz
      have hk : k' = k := Finset.mem_singleton.mp hk'
      subst k'
      rcases hz with ⟨a', ha', hz'⟩
      have ha : a' = a := Finset.mem_singleton.mp ha'
      subst a'
      exact hsafe z hz')
  let p : ℂ × ℂ × ℂ := (τ₀, k.w, k.y)
  let F : (ℂ × ℂ × ℂ) × ℂ → ℂ := fun u =>
    kernel M (withParameters k u.1.2.1 u.1.2.2) u.2 u.1.1 *
      (Complex.I * (u.2 - a))
  have hF : ∀ q ∈ Metric.closedBall p ρ, ∀ θ ∈ Icc 0 (2 * Real.pi),
      AnalyticAt ℂ F (q, circleMap a r θ) := by
    intro q hq θ hθ
    have hq' : q.1 ∈ Metric.closedBall τ₀ ρ ∧
        q.2.1 ∈ Metric.closedBall k.w ρ ∧ q.2.2 ∈ Metric.closedBall k.y ρ := by
      simpa only [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, p] using hq
    have hz : circleMap a r θ ∈ boundaries C :=
      ⟨a, by simp [C], circleMap_mem_sphere a hr.le θ⟩
    have hreg := (hbound k (by simp) q.1 hq'.1 q.2.1 hq'.2.1 q.2.2 hq'.2.2 _ hz).1
    dsimp only [F]
    apply AnalyticAt.mul
    · apply ModularClusterIntegralsAux.analyticAt_kernel M hM k
      · exact analyticAt_snd
      · exact analyticAt_fst.comp (f := fun u : (ℂ × ℂ × ℂ) × ℂ => u.1) analyticAt_fst
      · exact analyticAt_fst.comp (f := fun u : (ℂ × ℂ × ℂ) × ℂ => u.1.2)
          (analyticAt_snd.comp (f := fun u : (ℂ × ℂ × ℂ) × ℂ => u.1) analyticAt_fst)
      · exact analyticAt_snd.comp (f := fun u : (ℂ × ℂ × ℂ) × ℂ => u.1.2)
          (analyticAt_snd.comp (f := fun u : (ℂ × ℂ × ℂ) × ℂ => u.1) analyticAt_fst)
      · exact hreg
    · exact analyticAt_const.mul (analyticAt_snd.sub analyticAt_const)
  have hd := ModularClusterIntegralsAux.differentiableOn_integral_pullback
    (continuous_circleMap a r) (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hF
  change AnalyticAt ℂ (fun q => ∫ θ in 0..(2 * Real.pi), F (q, circleMap a r θ)) p
  exact ModularClusterIntegralsAux.analyticAt_of_differentiableOn_closedBall_three
    (hd.mono (Metric.closedBall_subset_ball (show ρ / 2 < ρ by linarith))) (by positivity)

#check IntervalIntegrable
#check circleMap
#check hasDerivAt_circleMap
#check FinitePrincipalParts.circleCCW
#check FinitePrincipalParts.circleCCW_eq_circleIntegral
#check MeasureTheory.integrableOn_const
#print circleKernel
#print circleContribution

end SICLean.L4.ModularCluster
