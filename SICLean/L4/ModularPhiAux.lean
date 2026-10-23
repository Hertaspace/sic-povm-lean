import SICLean.L4.FaddeevProduct
import SICLean.L4.EtaMultiplier

set_option autoImplicit false

/-!
# Elementary auxiliaries for the positive-c modular Φ

Nothing here mentions `modularPhi`; this file only collects square-root,
exponential-phase, filter and analytic-product facts used in
`ModularPhi.lean`. No definition or statement of `ModularPhi.lean` is changed.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators

namespace SICLean.L4

/-! ## Principal square root on the slit plane -/

lemma sqrt_re_pos_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt z).re := by
  have hz' : 0 < (‖z‖ + z.re) / 2 := by
    rcases Complex.mem_slitPlane_iff.mp hz with h | h
    · have := norm_nonneg z; linarith
    · have h2 : z.re ^ 2 < ‖z‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        nlinarith [sq_pos_of_ne_zero h]
      have h3 : -‖z‖ < z.re := by nlinarith [norm_nonneg z]
      have := norm_nonneg z; linarith
  have hre : (Complex.sqrt z).re = Real.sqrt ((‖z‖ + z.re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]
    simp only [Complex.add_re, Complex.ofReal_re]
    split_ifs <;> simp
  rw [hre]
  exact Real.sqrt_pos.2 hz'

lemma sqrt_ne_zero_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.sqrt z ≠ 0 := by
  intro h
  have hz0 : z = 0 := by
    have := EtaMultiplierAux.sqrt_mul_self z
    rw [h] at this
    simpa using this.symm
  exact Complex.zero_notMem_slitPlane (hz0 ▸ hz)

lemma sqrt_re_pos_of_admissible {z : ℂ} (hz : AdmissibleB z) :
    0 < (Complex.sqrt z).re :=
  sqrt_re_pos_of_mem_slitPlane (Or.inl hz)

lemma sqrt_ne_zero_of_admissible {z : ℂ} (hz : AdmissibleB z) :
    Complex.sqrt z ≠ 0 :=
  sqrt_ne_zero_of_mem_slitPlane (Or.inl hz)

/-! ## The phase `e` -/

lemma e_add' (z w : ℂ) : e (z + w) = e z * e w := by
  simp only [e, mul_add, Complex.exp_add]

lemma e_neg' (z : ℂ) : e (-z) = (e z)⁻¹ := by
  simp only [e, mul_neg, Complex.exp_neg]

lemma e_intCast (k : ℤ) : e (k : ℂ) = 1 := by
  have h : (k : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp
  simp only [e]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) =
    (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma e_natCast (n : ℕ) : e (n : ℂ) = 1 := by
  simpa using e_intCast (n : ℤ)

lemma e_nat_mul (x : ℂ) (n : ℕ) : e x ^ n = e ((n : ℂ) * x) := by
  simp only [e]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma e_int_mul (x : ℂ) (k : ℤ) : e x ^ k = e ((k : ℂ) * x) := by
  induction k using Int.induction_on with
  | zero => simp [e]
  | succ n ih =>
    rw [zpow_add_one₀ (e_ne_zero x), ih, ← e_add']
    congr 1
    push_cast
    ring
  | pred n ih =>
    rw [zpow_sub_one₀ (e_ne_zero x), ih, ← e_neg', ← e_add']
    congr 1
    push_cast
    ring

lemma e_eq_one_iff_int {x : ℂ} (h : e x = 1) : ∃ k : ℤ, x = k := by
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * x) = 1 := h
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨n, hn⟩ := hexp
  refine ⟨n, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have h' : (Real.pi : ℂ) = 0 := by
      have := congrArg (fun z => z / (2 * Complex.I)) h0
      simpa using this
    exact Real.pi_ne_zero (by exact_mod_cast h')
  exact mul_left_cancel₀ hpi (by simpa [mul_assoc, mul_comm, mul_left_comm] using hn)

/-! ## A frequent-nonvanishing transfer through a nonconstant affine map -/

/-- If `f` is nonzero arbitrarily close to `a` and `w ↦ α w + β` is a
nonconstant affine map with `α z₀ + β = a`, then `f (α w + β)` is nonzero
arbitrarily close to `z₀`. This is the elementary replacement for intersecting
several `Frequently` filters by hand. -/
lemma frequently_ne_zero_comp_affine {f : ℂ → ℂ} {a z₀ α β : ℂ} (hα : α ≠ 0)
    (h : ∃ᶠ y : ℂ in 𝓝 a, f y ≠ 0) (ha : α * z₀ + β = a) :
    ∃ᶠ w : ℂ in 𝓝 z₀, f (α * w + β) ≠ 0 := by
  have hinv : Tendsto (fun y : ℂ => (y - β) / α) (𝓝 a) (𝓝 z₀) := by
    have hc : Tendsto (fun y : ℂ => (y - β) / α) (𝓝 a) (𝓝 ((a - β) / α)) := by
      apply ContinuousAt.tendsto
      fun_prop
    have hv : (a - β) / α = z₀ := by
      rw [← ha]
      field_simp
      ring
    rwa [hv] at hc
  by_contra hzero
  rw [Filter.not_frequently] at hzero
  have hcontra : ∀ᶠ y : ℂ in 𝓝 a, f y = 0 := by
    filter_upwards [hinv.eventually hzero] with y hy
    have hy' : α * ((y - β) / α) + β = y := by
      field_simp
      ring
    rw [hy'] at hy
    simpa using hy
  exact (Filter.not_eventually.mpr h) hcontra

/-- A nonzero analytic germ is not locally identically zero. -/
lemma meromorphicOrderAt_ne_top_of_analytic_frequently_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (h : ∃ᶠ w : ℂ in 𝓝 z, f w ≠ 0) :
    meromorphicOrderAt f z ≠ ⊤ := by
  rw [hf.meromorphicOrderAt_eq]
  intro htop
  rw [ENat.map_eq_top_iff] at htop
  rw [analyticOrderAt_eq_top] at htop
  exact (Filter.not_eventually.mpr h) htop

/-- The explicit continuation charts obey the cross-multiplied identity at
every common center, including poles. The proof uses the chart germ equality
plus the fact that each fixed denominator vanishes at most on a discrete set,
so the analytic difference vanishes on a punctured neighborhood. -/
lemma continuationNumerator_mul_denominator_comm (b z : ℂ) (k l : ℤ)
    (hb : AdmissibleB b)
    (hk : InStrip b (shiftedArgument b z k)) (hl : InStrip b (shiftedArgument b z l)) :
    continuationNumerator b z k * continuationDenominator b z l =
      continuationNumerator b z l * continuationDenominator b z k := by
  set G : ℂ → ℂ := fun w => continuationNumerator b w k * continuationDenominator b w l -
    continuationNumerator b w l * continuationDenominator b w k with hG
  have hGan : AnalyticAt ℂ G z := by
    have h1 : AnalyticAt ℂ (fun w => continuationNumerator b w k *
        continuationDenominator b w l) z :=
      (analyticAt_continuationNumerator b z k hb hk).mul
        (analyticAt_continuationDenominator b z l)
    have h2 : AnalyticAt ℂ (fun w => continuationNumerator b w l *
        continuationDenominator b w k) z :=
      (analyticAt_continuationNumerator b z l hb hl).mul
        (analyticAt_continuationDenominator b z k)
    refine (h1.sub h2).congr ?_
    filter_upwards with w
    simp [G, Pi.sub_apply]
  have hntk : meromorphicOrderAt (fun w => continuationDenominator b w k) z ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_analytic_frequently_ne_zero
      (analyticAt_continuationDenominator b z k)
      (continuationDenominator_frequently_ne_zero b z k hb hk)
  have hntl : meromorphicOrderAt (fun w => continuationDenominator b w l) z ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_analytic_frequently_ne_zero
      (analyticAt_continuationDenominator b z l)
      (continuationDenominator_frequently_ne_zero b z l hb hl)
  have hevk : ∀ᶠ w : ℂ in 𝓝[≠] z, continuationDenominator b w k ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (analyticAt_continuationDenominator b z k).meromorphicAt).mp hntk
  have hevl : ∀ᶠ w : ℂ in 𝓝[≠] z, continuationDenominator b w l ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (analyticAt_continuationDenominator b z l).meromorphicAt).mp hntl
  have hzero : G =ᶠ[𝓝[≠] z] 0 := by
    filter_upwards [hevk, hevl, phiChart_overlap b z k l hb hk hl] with w hwk hwl heq
    have heq' : continuationNumerator b w k / continuationDenominator b w k =
        continuationNumerator b w l / continuationDenominator b w l := heq
    simp only [G]
    rw [div_eq_div_iff hwk hwl] at heq'
    rw [heq', sub_self]
    simp
  have ht : Tendsto G (𝓝[≠] z) (𝓝 (G z)) :=
    hGan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht0 : Tendsto G (𝓝[≠] z) (𝓝 0) :=
    Tendsto.congr' hzero.symm tendsto_const_nhds
  have hGz : G z = 0 := tendsto_nhds_unique ht ht0
  simpa [G, sub_eq_zero] using hGz

end SICLean.L4

namespace SICLean.L4

/-! ## Openness helpers -/

/-- If `f` is continuous at every point of `f ⁻¹' t` and `t` is open, then
`f ⁻¹' t` is open. This avoids asking for global continuity of `sqrt`. -/
lemma isOpen_preimage_of_continuousAt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {t : Set Y} (ht : IsOpen t)
    (h : ∀ x ∈ f ⁻¹' t, ContinuousAt f x) : IsOpen (f ⁻¹' t) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact (h x hx).preimage_mem_nhds (ht.mem_nhds hx)

/-- Joint openness of the strip condition with a variable admissible base. -/
lemma isOpen_inStrip_joint (k : ℤ) :
    IsOpen {q : ℂ × ℂ | InStrip q.1 (shiftedArgument q.1 q.2 k)} := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hq' : |(shiftedArgument q.1 q.2 k).im| < stripWidth q.1 := hq
  have hb : q.1 ≠ 0 := by
    intro h0
    rw [h0] at hq'
    simp [stripWidth] at hq'
    linarith [abs_nonneg (shiftedArgument (0 : ℂ) q.2 k).im]
  have hcontf : ContinuousAt (fun q : ℂ × ℂ => |(shiftedArgument q.1 q.2 k).im|) q := by
    unfold shiftedArgument
    fun_prop
  have hcontg : ContinuousAt (fun q : ℂ × ℂ => stripWidth q.1) q := by
    have h1 : ContinuousAt (fun q : ℂ × ℂ => q.1) q := continuousAt_fst
    have hi : ContinuousAt (fun b : ℂ => b⁻¹) q.1 := continuousAt_inv₀ hb
    have h2 : ContinuousAt (fun q : ℂ × ℂ => (q.1).re) q :=
      Complex.continuous_re.continuousAt.comp h1
    have h3 : ContinuousAt (fun q : ℂ × ℂ => (q.1)⁻¹) q := hi.comp h1
    have h4 : ContinuousAt (fun q : ℂ × ℂ => ((q.1)⁻¹).re) q :=
      Complex.continuous_re.continuousAt.comp h3
    have h5 : ContinuousAt (fun q : ℂ × ℂ => ((q.1).re + ((q.1)⁻¹).re) / 2) q :=
      (h2.add h4).div_const 2
    have heq : (fun q : ℂ × ℂ => stripWidth q.1) =
        fun q : ℂ × ℂ => ((q.1).re + ((q.1)⁻¹).re) / 2 := by
      funext q
      rfl
    rw [heq]
    exact h5
  have hmem : |(shiftedArgument q.1 q.2 k).im| - stripWidth q.1 ∈ Set.Iio (0 : ℝ) := by
    simp only [Set.mem_Iio]
    linarith
  have hlt := (hcontf.sub hcontg).preimage_mem_nhds (isOpen_Iio.mem_nhds hmem)
  rw [show {q : ℂ × ℂ | InStrip q.1 (shiftedArgument q.1 q.2 k)} =
      (fun q : ℂ × ℂ => |(shiftedArgument q.1 q.2 k).im| - stripWidth q.1) ⁻¹' Set.Iio 0 from by
    ext q
    simp [InStrip, sub_neg]]
  exact hlt


/-- Analyticity of a continuation denominator composed with a complex affine
map, with no hypothesis on the affine map. -/
lemma analyticAt_continuationDenominator_affine (b : ℂ) (k : ℤ) (α β z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => continuationDenominator b (α * w + β) k) z := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => α * w + β) z := by fun_prop
  have := (analyticAt_continuationDenominator b (α * z + β) k).comp (x := z) hlin
  simpa [Function.comp_def] using this

/-- Nondegeneracy of the above order for a nonconstant affine map. -/
lemma meromorphicOrderAt_continuationDenominator_affine_ne_top (b : ℂ) (hb : AdmissibleB b)
    (k : ℤ) (α β z : ℂ) (hα : α ≠ 0)
    (hz : InStrip b (shiftedArgument b (α * z + β) k)) :
    meromorphicOrderAt (fun w : ℂ => continuationDenominator b (α * w + β) k) z ≠ ⊤ := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => α * w + β) z := by fun_prop
  have hderiv : deriv (fun w : ℂ => α * w + β) z = α := by
    simpa using ((hasDerivAt_id z).const_mul α).add_const β
  have hderivne : deriv (fun w : ℂ => α * w + β) z ≠ 0 := by
    rw [hderiv]
    exact hα
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := fun x : ℂ => continuationDenominator b x k) hlin hderivne
  change meromorphicOrderAt ((fun x : ℂ => continuationDenominator b x k) ∘
    (fun w : ℂ => α * w + β)) z ≠ ⊤
  rw [hcomp]
  exact meromorphicOrderAt_ne_top_of_analytic_frequently_ne_zero
    (analyticAt_continuationDenominator b (α * z + β) k)
    (continuationDenominator_frequently_ne_zero b (α * z + β) k hb hz)


/-- Pointwise joint analyticity of `phiExtended` on its explicit regular
locus, read off the already proved local quotient. -/
lemma analyticAt_phiExtended_joint {p : ℂ × ℂ} (hp : p ∈ phiRegularDomain) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => phiExtended q.1 q.2) p := by
  obtain ⟨k, U, hU, hmem, hsub, hnum, hden, hfreq, heq⟩ :=
    phiExtended_joint_local_quotient p hp.1
  have hD : continuationDenominator p.1 p.2 k ≠ 0 :=
    (continuationDenominator_ne_zero_iff _ _ _ hp.1 (hsub _ hmem).2).mpr hp.2
  have hcont : ContinuousAt (fun q : ℂ × ℂ => continuationDenominator q.1 q.2 k) p :=
    (analyticAt_continuationDenominator_joint p k).continuousAt
  have hne : ∀ᶠ q : ℂ × ℂ in 𝓝 p, continuationDenominator q.1 q.2 k ≠ 0 :=
    hcont.eventually_ne hD
  have hq : AnalyticAt ℂ (fun q : ℂ × ℂ => continuationNumerator q.1 q.2 k /
      continuationDenominator q.1 q.2 k) p :=
    (analyticAt_continuationNumerator_joint p k (hsub p hmem).1 (hsub p hmem).2).div
      (analyticAt_continuationDenominator_joint p k) hD
  refine hq.congr ?_
  filter_upwards [hU.mem_nhds hmem, hne] with q hqU hqD
  exact (heq q hqU hqD).symm

end SICLean.L4
