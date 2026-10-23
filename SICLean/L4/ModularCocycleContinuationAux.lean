import SICLean.L4.ModularPhi
import SICLean.L4.ModularCocycleUpperAux
import SICLean.L4.ModularCocycleMatrixAux

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped Topology MatrixGroups UpperHalfPlane

namespace SICLean.L4.ModularCocycleContinuationAux

/-- Compatibility of analytic quotient charts transfers local vanishing.
The frequent nonvanishing hypothesis is local density of the denominator,
so specified values on its zero set play no role. -/
theorem quotient_zero_transfer {ι : Type*} (U : ι → Set (ℂ × ℂ))
    (A D : ι → (ℂ × ℂ) → ℂ)
    (hU : ∀ i, IsOpen (U i))
    (hA : ∀ i, AnalyticOnNhd ℂ (A i) (U i))
    (hD : ∀ i p, p ∈ U i → ∃ᶠ q in 𝓝 p, D i q ≠ 0)
    (hcompat : ∀ i j p, p ∈ U i → p ∈ U j →
      A i p * D j p = A j p * D i p)
    (i j : ι) (p : ℂ × ℂ) (hi : p ∈ U i) (hj : p ∈ U j)
    (hz : A i =ᶠ[𝓝 p] 0) : A j =ᶠ[𝓝 p] 0 := by
  have hev : ∀ᶠ q in 𝓝 p, q ∈ U i ∧ q ∈ U j ∧ A i q = 0 := by
    filter_upwards [(hU i).mem_nhds hi, (hU j).mem_nhds hj, hz] with q hqi hqj hqz
    exact ⟨hqi, hqj, hqz⟩
  have hloc := eventually_eventually_nhds.mpr hev
  filter_upwards [hev, hloc] with q hq hqloc
  have hfreq : ∃ᶠ r in 𝓝 q, A j r = 0 := by
    apply ((hD i q hq.1).and_eventually hqloc).mono
    rintro r ⟨hrD, hri, hrj, hrz⟩
    have hc := hcompat i j r hri hrj
    rw [hrz, zero_mul] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_right hrD
  exact tendsto_nhds_unique_of_frequently_eq (hA j q hq.2.1).continuousAt
    tendsto_const_nhds hfreq

/-- Identity principle for an atlas of concrete analytic quotients.
Compatible cross products, rather than any choice of pole values, are
continued through the connected joint domain. -/
theorem quotient_atlas_identity {ι : Type*} (Ω : Set (ℂ × ℂ))
    (U : ι → Set (ℂ × ℂ)) (A D : ι → (ℂ × ℂ) → ℂ)
    (hΩ : IsPreconnected Ω)
    (hU : ∀ i, IsOpen (U i))
    (hsub : ∀ i, U i ⊆ Ω)
    (hcover : ∀ p ∈ Ω, ∃ i, p ∈ U i)
    (hA : ∀ i, AnalyticOnNhd ℂ (A i) (U i))
    (hD : ∀ i p, p ∈ U i → ∃ᶠ q in 𝓝 p, D i q ≠ 0)
    (hcompat : ∀ i j p, p ∈ U i → p ∈ U j →
      A i p * D j p = A j p * D i p)
    (i₀ : ι) (p₀ : ℂ × ℂ) (hp₀ : p₀ ∈ U i₀)
    (hzero : A i₀ =ᶠ[𝓝 p₀] 0) :
    ∀ i p, p ∈ U i → A i p = 0 := by
  let Z : Set (ℂ × ℂ) := {p | ∃ i, p ∈ U i ∧ A i =ᶠ[𝓝 p] 0}
  have hZopen : IsOpen Z := by
    apply isOpen_iff_mem_nhds.mpr
    rintro p ⟨i, hpi, hpz⟩
    filter_upwards [(hU i).mem_nhds hpi,
      eventually_eventually_nhds.mpr hpz] with q hqi hqz
    exact ⟨i, hqi, hqz⟩
  have hclosure : closure Z ∩ Ω ⊆ Z := by
    rintro p ⟨hpcl, hpΩ⟩
    obtain ⟨i, hpi⟩ := hcover p hpΩ
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU i) p hpi
    obtain ⟨q, hqZ, hqdist⟩ := Metric.mem_closure_iff.mp hpcl ε hε
    have hqball : q ∈ Metric.ball p ε := by
      simpa only [Metric.mem_ball, dist_comm] using hqdist
    have hqi : q ∈ U i := hball hqball
    obtain ⟨j, hqj, hqzero⟩ := hqZ
    have hqzero' := quotient_zero_transfer U A D hU hA hD hcompat j i q hqj hqi hqzero
    have hEq : Set.EqOn (A i) 0 (Metric.ball p ε) :=
      (hA i |>.mono hball).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        (convex_ball p ε).isPreconnected hqball hqzero'
    refine ⟨i, hpi, ?_⟩
    filter_upwards [Metric.ball_mem_nhds p hε] with r hr
    exact hEq hr
  have hΩZ : Ω ⊆ Z := hΩ.subset_of_closure_inter_subset hZopen
    ⟨p₀, hsub i₀ hp₀, i₀, hp₀, hzero⟩ hclosure
  intro i p hpi
  obtain ⟨j, hpj, hpzero⟩ := hΩZ (hsub i hpi)
  exact (quotient_zero_transfer U A D hU hA hD hcompat j i p hpj hpi hpzero).eq_of_nhds

theorem analytic_eventually_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hne : ∃ᶠ w in 𝓝 z, f w ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  exact hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun hz => hne (hz.mono (fun w hw h => h hw)))

theorem tendsto_div_const_nhdsNE (z c : ℂ) (hc : c ≠ 0) :
    Tendsto (fun w : ℂ => w / c) (𝓝[≠] z) (𝓝[≠] (z / c)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuousAt_id.div_const c).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun heq => hw ((div_left_inj' hc).mp heq)

theorem pullback_analyticAt (M : SL(2, ℤ)) (p : ℂ × ℂ)
    (hp : etaDenom M p.2 ≠ 0) :
    AnalyticAt ℂ (fun q : ℂ × ℂ =>
      (q.1 / etaDenom M q.2, etaMobius M q.2)) p := by
  have hd : AnalyticAt ℂ (fun q : ℂ × ℂ => etaDenom M q.2) p := by
    unfold etaDenom
    exact (analyticAt_const.mul analyticAt_snd).add analyticAt_const
  apply AnalyticAt.prod
  · exact analyticAt_fst.div hd hp
  · unfold etaMobius
    exact ((analyticAt_const.mul analyticAt_snd).add analyticAt_const).div hd hp

/-- Polynomial bookkeeping for the difference of three compatible quotient charts. -/
theorem cocycle_numerator_overlap (a a' b b' c c' x x' y y' z z' : ℂ)
    (ha : a * x' = a' * x) (hb : b * y' = b' * y) (hc : c * z' = c' * z) :
    (a * y * z - b * c * x) * (x' * y' * z') =
      (a' * y' * z' - b' * c' * x') * (x * y * z) := by
  linear_combination y * z * y' * z' * ha - c * x * x' * z' * hb -
    b' * x * x' * y * hc

/-- Cross-multiplied cocycles propagate over a connected domain covered by
joint analytic charts.  The denominator hypothesis concerns one-dimensional
slices and proves the density needed by the joint identity principle. -/
theorem cocycle_atlas_identity {ι : Type*} (Ω : Set (ℂ × ℂ))
    (U : ι → Set (ℂ × ℂ))
    (a b c x y z : ι → (ℂ × ℂ) → ℂ)
    (hΩ : IsPreconnected Ω) (hU : ∀ i, IsOpen (U i))
    (hsub : ∀ i, U i ⊆ Ω) (hcover : ∀ p ∈ Ω, ∃ i, p ∈ U i)
    (ha : ∀ i, AnalyticOnNhd ℂ (a i) (U i))
    (hb : ∀ i, AnalyticOnNhd ℂ (b i) (U i))
    (hc : ∀ i, AnalyticOnNhd ℂ (c i) (U i))
    (hx : ∀ i, AnalyticOnNhd ℂ (x i) (U i))
    (hy : ∀ i, AnalyticOnNhd ℂ (y i) (U i))
    (hz : ∀ i, AnalyticOnNhd ℂ (z i) (U i))
    (hne : ∀ i p, p ∈ U i → ∀ᶠ w in 𝓝[≠] p.1,
      x i (w, p.2) ≠ 0 ∧ y i (w, p.2) ≠ 0 ∧ z i (w, p.2) ≠ 0)
    (hcompat : ∀ i j p, p ∈ U i → p ∈ U j →
      a i p * x j p = a j p * x i p ∧
      b i p * y j p = b j p * y i p ∧
      c i p * z j p = c j p * z i p)
    (i₀ : ι) (p₀ : ℂ × ℂ) (hp₀ : p₀ ∈ U i₀)
    (hzero : (fun p => a i₀ p * y i₀ p * z i₀ p - b i₀ p * c i₀ p * x i₀ p)
      =ᶠ[𝓝 p₀] 0) :
    ∀ i p, p ∈ U i → a i p * y i p * z i p = b i p * c i p * x i p := by
  let A := fun i p => a i p * y i p * z i p - b i p * c i p * x i p
  let D := fun i p => x i p * y i p * z i p
  have hA : ∀ i, AnalyticOnNhd ℂ (A i) (U i) := fun i =>
    ((ha i).mul (hy i) |>.mul (hz i)).sub ((hb i).mul (hc i) |>.mul (hx i))
  have hD : ∀ i p, p ∈ U i → ∃ᶠ q in 𝓝 p, D i q ≠ 0 := by
    intro i p hp
    have hslice : ∃ᶠ w in 𝓝[≠] p.1, D i (w, p.2) ≠ 0 :=
      ((hne i p hp).mono (fun w hw => mul_ne_zero (mul_ne_zero hw.1 hw.2.1) hw.2.2)).frequently
    exact (continuousAt_id.prodMk continuousAt_const).tendsto.frequently
      (hslice.filter_mono nhdsWithin_le_nhds)
  have hcomp : ∀ i j p, p ∈ U i → p ∈ U j → A i p * D j p = A j p * D i p := by
    intro i j p hi hj
    obtain ⟨h₁, h₂, h₃⟩ := hcompat i j p hi hj
    exact cocycle_numerator_overlap _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
  intro i p hp
  exact sub_eq_zero.mp (quotient_atlas_identity Ω U A D hΩ hU hsub hcover hA hD hcomp
    i₀ p₀ hp₀ hzero i p hp)

/-- A quotient identity of punctured one-variable germs gives the
cross-product value at its center for continuous chart numerators. -/
theorem cross_mul_of_quotient_germ (a b c x y z : ℂ → ℂ) (w₀ : ℂ)
    (ha : ContinuousAt a w₀) (hb : ContinuousAt b w₀) (hc : ContinuousAt c w₀)
    (hx : ContinuousAt x w₀) (hy : ContinuousAt y w₀) (hz : ContinuousAt z w₀)
    (hne : ∀ᶠ w in 𝓝[≠] w₀, x w ≠ 0 ∧ y w ≠ 0 ∧ z w ≠ 0)
    (heq : (fun w => a w / x w) =ᶠ[𝓝[≠] w₀]
      (fun w => (b w / y w) * (c w / z w))) :
    a w₀ * y w₀ * z w₀ = b w₀ * c w₀ * x w₀ := by
  have hev : (fun w => a w * y w * z w) =ᶠ[𝓝[≠] w₀]
      (fun w => b w * c w * x w) := by
    filter_upwards [hne, heq] with w hw heqw
    have ht : a w / x w = (b w * c w) / (y w * z w) := by
      simpa only [mul_div_mul_comm] using heqw
    simpa only [mul_assoc] using
      (div_eq_div_iff hw.1 (mul_ne_zero hw.2.1 hw.2.2)).mp ht
  exact tendsto_nhds_unique_of_eventuallyEq
    ((ha.mul hy).mul hz |>.tendsto.mono_left nhdsWithin_le_nhds)
    ((hb.mul hc).mul hx |>.tendsto.mono_left nhdsWithin_le_nhds) hev


/-- Concrete finite translation expression used by the continuation helper.
These formulas are definitionally the wrappers in `ModularCocycle`; they
are repeated here to keep the helper independent of that theorem file. -/
def modularPhiTranslation (m n : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammerInt ((e τ) ^ m * e z) (e τ) (n - m)

def modularPhiTranslationNumerator (m n : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammerIntNumerator ((e τ) ^ m * e z) (e τ) (n - m)

def modularPhiTranslationDenominator (m n : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammerIntDenominator ((e τ) ^ m * e z) (e τ) (n - m)

def ModularPhiSupported (M : SL(2, ℤ)) : Prop :=
  0 < M 1 0 ∨ ∃ k : ℤ, M = ModularGroup.T ^ k

def modularPhiConstructed (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℂ :=
  if 0 < M 1 0 then modularPhi M m n z τ
  else modularPhiTranslation m n z τ

def modularPhiConstructedNumerator (M : SL(2, ℤ)) (m n : ℤ)
    (κ : ℕ → ℤ) (z τ : ℂ) : ℂ :=
  if 0 < M 1 0 then modularPhiChartNumerator M m n κ z τ
  else modularPhiTranslationNumerator m n z τ

def modularPhiConstructedDenominator (M : SL(2, ℤ)) (m n : ℤ)
    (κ : ℕ → ℤ) (z τ : ℂ) : ℂ :=
  if 0 < M 1 0 then modularPhiChartDenominator M m n κ z τ
  else modularPhiTranslationDenominator m n z τ

def modularPhiConstructedChartDomain (M : SL(2, ℤ)) (m n : ℤ)
    (κ : ℕ → ℤ) : Set (ℂ × ℂ) :=
  if 0 < M 1 0 then modularPhiChartDomain M m n κ else Set.univ

def modularCocyclePullback (M : SL(2, ℤ)) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1 / etaDenom M p.2, etaMobius M p.2)

def modularCocycleDomain (M N : SL(2, ℤ)) : Set ℂ :=
  {τ | τ ∈ modularPhiDomain N ∧
    etaMobius N τ ∈ modularPhiDomain M ∧ τ ∈ modularPhiDomain (M * N)}

private theorem m36_constructed_chart_isOpen (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ) :
    IsOpen (modularPhiConstructedChartDomain M m n κ) := by
  unfold modularPhiConstructedChartDomain
  split_ifs
  · exact modularPhiChartDomain_isOpen M m n κ
  · exact isOpen_univ

private theorem m36_constructed_chart_analytic (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiConstructedNumerator M m n κ p.1 p.2)
      (modularPhiConstructedChartDomain M m n κ) ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiConstructedDenominator M m n κ p.1 p.2)
      (modularPhiConstructedChartDomain M m n κ) := by
  by_cases hM : 0 < M 1 0
  · simpa only [modularPhiConstructedNumerator, modularPhiConstructedDenominator,
      modularPhiConstructedChartDomain, if_pos hM] using modularPhiChart_analytic M hM m n κ
  · simpa only [modularPhiConstructedNumerator, modularPhiConstructedDenominator,
      modularPhiConstructedChartDomain, if_neg hM, modularPhiTranslationNumerator,
      modularPhiTranslationDenominator] using ModularCocycleUpperAux.finite_symbol_joint_analytic m (n - m)

private theorem m36_constructed_chart_cover (M : SL(2, ℤ)) (m n : ℤ) (p : ℂ × ℂ)
    (hp : p.2 ∈ modularPhiDomain M) :
    ∃ κ : ℕ → ℤ, p ∈ modularPhiConstructedChartDomain M m n κ := by
  by_cases hM : 0 < M 1 0
  · let κ := fun j => continuationIndex (modularPhiFactorPoint M m n j p.1 p.2).1
        (modularPhiFactorPoint M m n j p.1 p.2).2
    refine ⟨κ, ?_⟩
    simp only [modularPhiConstructedChartDomain, if_pos hM]
    refine ⟨hp, ?_⟩
    intro j hj
    exact shiftedArgument_inStrip _ _ (modularPhi_sqrt_admissible M p.2 hp).1
  · exact ⟨fun _ => 0, by simp [modularPhiConstructedChartDomain, hM]⟩

private theorem m36_constructed_eq_chart (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ)
    (p : ℂ × ℂ) (hp : p ∈ modularPhiConstructedChartDomain M m n κ) :
    modularPhiConstructed M m n p.1 p.2 =
      modularPhiConstructedNumerator M m n κ p.1 p.2 /
      modularPhiConstructedDenominator M m n κ p.1 p.2 := by
  by_cases hM : 0 < M 1 0
  · simp only [modularPhiConstructedChartDomain, if_pos hM] at hp
    simpa only [modularPhiConstructed, modularPhiConstructedNumerator,
      modularPhiConstructedDenominator, if_pos hM, modularPhiChart] using modularPhi_eq_chart M hM m n κ p hp
  · simp [modularPhiConstructed, modularPhiConstructedNumerator,
      modularPhiConstructedDenominator, hM, modularPhiTranslation,
      modularPhiTranslationNumerator, modularPhiTranslationDenominator, qPochhammerInt]

private theorem m36_constructed_chart_overlap (M : SL(2, ℤ)) (m n : ℤ) (κ κ' : ℕ → ℤ)
    (p : ℂ × ℂ) (hp : p ∈ modularPhiConstructedChartDomain M m n κ)
    (hp' : p ∈ modularPhiConstructedChartDomain M m n κ') :
    modularPhiConstructedNumerator M m n κ p.1 p.2 *
        modularPhiConstructedDenominator M m n κ' p.1 p.2 =
      modularPhiConstructedNumerator M m n κ' p.1 p.2 *
        modularPhiConstructedDenominator M m n κ p.1 p.2 := by
  by_cases hM : 0 < M 1 0
  · simp only [modularPhiConstructedChartDomain, if_pos hM] at hp hp'
    simpa only [modularPhiConstructedNumerator, modularPhiConstructedDenominator,
      if_pos hM] using modularPhiChart_overlap_cross_mul M hM m n κ κ' p hp hp'
  · simp only [modularPhiConstructedNumerator, modularPhiConstructedDenominator, if_neg hM]

private theorem m36_constructed_den_eventually (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ)
    (p : ℂ × ℂ) (hp : p ∈ modularPhiConstructedChartDomain M m n κ) :
    ∀ᶠ w in 𝓝[≠] p.1, modularPhiConstructedDenominator M m n κ w p.2 ≠ 0 := by
  by_cases hM : 0 < M 1 0
  · simp only [modularPhiConstructedChartDomain, if_pos hM] at hp
    have han : AnalyticAt ℂ (fun w => modularPhiChartDenominator M m n κ w p.2) p.1 := by
      have hjoint := (modularPhiChart_analytic M hM m n κ).2 p hp
      have hemb : AnalyticAt ℂ (fun w : ℂ => (w, p.2)) p.1 := analyticAt_id.prod analyticAt_const
      have hcomp := hjoint.comp (x := p.1) (f := fun w : ℂ => (w, p.2)) hemb
      simpa only [Function.comp_def] using hcomp
    simpa only [modularPhiConstructedDenominator, if_pos hM] using
      ModularCocycleContinuationAux.analytic_eventually_ne_zero han
        (modularPhiChartDenominator_frequently_ne_zero M hM m n κ p hp)
  · simpa only [modularPhiConstructedDenominator, if_neg hM,
      modularPhiTranslationDenominator] using
      ModularCocycleUpperAux.finite_denominator_eventually_ne_zero m (n - m) p.1 p.2

private theorem m36_cocycle_den_eventually (M N : SL(2, ℤ)) (m k n : ℤ)
    (κMN κM κN : ℕ → ℤ) (p : ℂ × ℂ)
    (hpN : p.2 ∈ modularPhiDomain N)
    (hpMN : p ∈ modularPhiConstructedChartDomain (M * N) m n κMN)
    (hpM : modularCocyclePullback N p ∈ modularPhiConstructedChartDomain M k n κM)
    (hpN' : p ∈ modularPhiConstructedChartDomain N m k κN) :
    ∀ᶠ w in 𝓝[≠] p.1,
      modularPhiConstructedDenominator (M * N) m n κMN w p.2 ≠ 0 ∧
      modularPhiConstructedDenominator M k n κM
        (w / etaDenom N p.2) (etaMobius N p.2) ≠ 0 ∧
      modularPhiConstructedDenominator N m k κN w p.2 ≠ 0 := by
  have hn := Complex.slitPlane_ne_zero hpN
  have ht := ModularCocycleContinuationAux.tendsto_div_const_nhdsNE p.1 (etaDenom N p.2) hn
  have hM := ht.eventually (m36_constructed_den_eventually M k n κM
    (modularCocyclePullback N p) hpM)
  filter_upwards [m36_constructed_den_eventually (M * N) m n κMN p hpMN,
    hM, m36_constructed_den_eventually N m k κN p hpN'] with w h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

private theorem m36_cocycle_cross_of_germ (M N : SL(2, ℤ)) (m k n : ℤ)
    (κMN κM κN : ℕ → ℤ) (p : ℂ × ℂ)
    (hpN : p.2 ∈ modularPhiDomain N)
    (hpMN : p ∈ modularPhiConstructedChartDomain (M * N) m n κMN)
    (hpM : modularCocyclePullback N p ∈ modularPhiConstructedChartDomain M k n κM)
    (hpN' : p ∈ modularPhiConstructedChartDomain N m k κN)
    (hg : (fun w => modularPhiConstructed (M * N) m n w p.2) =ᶠ[𝓝[≠] p.1]
      (fun w => modularPhiConstructed M k n (w / etaDenom N p.2) (etaMobius N p.2) *
        modularPhiConstructed N m k w p.2)) :
    modularPhiConstructedNumerator (M * N) m n κMN p.1 p.2 *
        modularPhiConstructedDenominator M k n κM
          (modularCocyclePullback N p).1 (modularCocyclePullback N p).2 *
        modularPhiConstructedDenominator N m k κN p.1 p.2 =
      modularPhiConstructedNumerator M k n κM
          (modularCocyclePullback N p).1 (modularCocyclePullback N p).2 *
        modularPhiConstructedNumerator N m k κN p.1 p.2 *
        modularPhiConstructedDenominator (M * N) m n κMN p.1 p.2 := by
  have ht : AnalyticAt ℂ (fun w : ℂ => (w, p.2)) p.1 := analyticAt_id.prod analyticAt_const
  have htM : AnalyticAt ℂ (fun w : ℂ => (w / etaDenom N p.2, etaMobius N p.2)) p.1 :=
    (analyticAt_id.div_const (c := etaDenom N p.2)).prod analyticAt_const
  have hev₁ : ∀ᶠ w in 𝓝[≠] p.1,
      (w, p.2) ∈ modularPhiConstructedChartDomain (M * N) m n κMN :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (ht.continuousAt.preimage_mem_nhds ((m36_constructed_chart_isOpen _ _ _ _).mem_nhds hpMN))
  have hev₂ : ∀ᶠ w in 𝓝[≠] p.1,
      (w / etaDenom N p.2, etaMobius N p.2) ∈ modularPhiConstructedChartDomain M k n κM :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (htM.continuousAt.preimage_mem_nhds ((m36_constructed_chart_isOpen _ _ _ _).mem_nhds hpM))
  have hev₃ : ∀ᶠ w in 𝓝[≠] p.1,
      (w, p.2) ∈ modularPhiConstructedChartDomain N m k κN :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (ht.continuousAt.preimage_mem_nhds ((m36_constructed_chart_isOpen _ _ _ _).mem_nhds hpN'))
  have heq := hg
  have hratio :
      (fun w => modularPhiConstructedNumerator (M * N) m n κMN w p.2 /
        modularPhiConstructedDenominator (M * N) m n κMN w p.2) =ᶠ[𝓝[≠] p.1]
      (fun w => (modularPhiConstructedNumerator M k n κM (w / etaDenom N p.2) (etaMobius N p.2) /
        modularPhiConstructedDenominator M k n κM (w / etaDenom N p.2) (etaMobius N p.2)) *
        (modularPhiConstructedNumerator N m k κN w p.2 /
        modularPhiConstructedDenominator N m k κN w p.2)) := by
    filter_upwards [heq, hev₁, hev₂, hev₃] with w hw h₁ h₂ h₃
    rw [m36_constructed_eq_chart _ _ _ _ (w, p.2) h₁,
      m36_constructed_eq_chart _ _ _ _ (w / etaDenom N p.2, etaMobius N p.2) h₂,
      m36_constructed_eq_chart _ _ _ _ (w, p.2) h₃] at hw
    exact hw
  apply ModularCocycleContinuationAux.cross_mul_of_quotient_germ
    (w₀ := p.1) (hne := m36_cocycle_den_eventually M N m k n κMN κM κN p hpN hpMN hpM hpN')
    (heq := hratio)
  · exact (((m36_constructed_chart_analytic _ _ _ _).1 p hpMN).comp (x := p.1) (f := fun w : ℂ => (w, p.2)) ht).continuousAt
  · exact (((m36_constructed_chart_analytic _ _ _ _).1 _ hpM).comp (x := p.1) (f := fun w : ℂ => (w / etaDenom N p.2, etaMobius N p.2)) htM).continuousAt
  · exact (((m36_constructed_chart_analytic _ _ _ _).1 p hpN').comp (x := p.1) (f := fun w : ℂ => (w, p.2)) ht).continuousAt
  · exact (((m36_constructed_chart_analytic _ _ _ _).2 p hpMN).comp (x := p.1) (f := fun w : ℂ => (w, p.2)) ht).continuousAt
  · exact (((m36_constructed_chart_analytic _ _ _ _).2 _ hpM).comp (x := p.1) (f := fun w : ℂ => (w / etaDenom N p.2, etaMobius N p.2)) htM).continuousAt
  · exact (((m36_constructed_chart_analytic _ _ _ _).2 p hpN').comp (x := p.1) (f := fun w : ℂ => (w, p.2)) ht).continuousAt

theorem real_chart_cross_mul (M N : SL(2, ℤ))
    (_hM : ModularPhiSupported M) (_hN : ModularPhiSupported N)
    (_hMN : ModularPhiSupported (M * N)) (m k n : ℤ) (τ₀ : ℝ)
    (hTN : 0 < (etaDenom N (τ₀ : ℂ)).re)
    (hTM : 0 < (etaDenom M (etaMobius N (τ₀ : ℂ))).re)
    (hupper : ∀ z τ : ℂ, 0 < τ.im →
      (fun w => modularPhiConstructed (M * N) m n w τ) =ᶠ[𝓝[≠] z]
        (fun w => modularPhiConstructed M k n
          (w / etaDenom N τ) (etaMobius N τ) * modularPhiConstructed N m k w τ)) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (τ₀ : ℂ) δ ⊆ modularCocycleDomain M N ∧
      ∀ (κMN κM κN : ℕ → ℤ) (p : ℂ × ℂ), p.2 ∈ Metric.ball (τ₀ : ℂ) δ →
        p ∈ modularPhiConstructedChartDomain (M * N) m n κMN →
        modularCocyclePullback N p ∈ modularPhiConstructedChartDomain M k n κM →
        p ∈ modularPhiConstructedChartDomain N m k κN →
        modularPhiConstructedNumerator (M * N) m n κMN p.1 p.2 *
            modularPhiConstructedDenominator M k n κM
              (modularCocyclePullback N p).1 (modularCocyclePullback N p).2 *
            modularPhiConstructedDenominator N m k κN p.1 p.2 =
          modularPhiConstructedNumerator M k n κM
              (modularCocyclePullback N p).1 (modularCocyclePullback N p).2 *
            modularPhiConstructedNumerator N m k κN p.1 p.2 *
            modularPhiConstructedDenominator (M * N) m n κMN p.1 p.2 := by
  obtain ⟨_, δ, hδ, hball⟩ := ModularCocycleMatrixAux.cocycle_real_neighborhood M N τ₀ hTN hTM
  refine ⟨δ, hδ, hball, ?_⟩
  let ι := (ℕ → ℤ) × (ℕ → ℤ) × (ℕ → ℤ)
  let Ω : Set (ℂ × ℂ) := Set.univ ×ˢ Metric.ball (τ₀ : ℂ) δ
  let U : ι → Set (ℂ × ℂ) := fun i => {p |
    p.2 ∈ Metric.ball (τ₀ : ℂ) δ ∧
    p ∈ modularPhiConstructedChartDomain (M * N) m n i.1 ∧
    modularCocyclePullback N p ∈ modularPhiConstructedChartDomain M k n i.2.1 ∧
    p ∈ modularPhiConstructedChartDomain N m k i.2.2}
  let a : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiConstructedNumerator (M * N) m n i.1 p.1 p.2
  let b : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiConstructedNumerator M k n i.2.1
      (modularCocyclePullback N p).1 (modularCocyclePullback N p).2
  let c : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiConstructedNumerator N m k i.2.2 p.1 p.2
  let x : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiConstructedDenominator (M * N) m n i.1 p.1 p.2
  let y : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiConstructedDenominator M k n i.2.1
      (modularCocyclePullback N p).1 (modularCocyclePullback N p).2
  let z : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiConstructedDenominator N m k i.2.2 p.1 p.2
  have hΩ : IsPreconnected Ω := isPreconnected_univ.prod (convex_ball _ _).isPreconnected
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hdom := hball hp.1
    have hpb : ContinuousAt (modularCocyclePullback N) p :=
      (ModularCocycleContinuationAux.pullback_analyticAt N p
        (Complex.slitPlane_ne_zero hdom.1)).continuousAt
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hp.1),
      (m36_constructed_chart_isOpen _ _ _ _).mem_nhds hp.2.1,
      hpb.preimage_mem_nhds ((m36_constructed_chart_isOpen _ _ _ _).mem_nhds hp.2.2.1),
      (m36_constructed_chart_isOpen _ _ _ _).mem_nhds hp.2.2.2] with q hq₀ hq₁ hq₂ hq₃
    exact ⟨hq₀, hq₁, hq₂, hq₃⟩
  have hsub : ∀ i, U i ⊆ Ω := fun _ _ hp => ⟨Set.mem_univ _, hp.1⟩
  have hcover : ∀ p ∈ Ω, ∃ i, p ∈ U i := by
    intro p hp
    have hdom := hball hp.2
    obtain ⟨κMN, hMN⟩ := m36_constructed_chart_cover (M * N) m n p hdom.2.2
    obtain ⟨κM, hM⟩ := m36_constructed_chart_cover M k n (modularCocyclePullback N p) hdom.2.1
    obtain ⟨κN, hN⟩ := m36_constructed_chart_cover N m k p hdom.1
    exact ⟨(κMN, κM, κN), hp.2, hMN, hM, hN⟩
  have ha : ∀ i, AnalyticOnNhd ℂ (a i) (U i) := fun i p hp =>
    (m36_constructed_chart_analytic _ _ _ _).1 p hp.2.1
  have hc : ∀ i, AnalyticOnNhd ℂ (c i) (U i) := fun i p hp =>
    (m36_constructed_chart_analytic _ _ _ _).1 p hp.2.2.2
  have hx : ∀ i, AnalyticOnNhd ℂ (x i) (U i) := fun i p hp =>
    (m36_constructed_chart_analytic _ _ _ _).2 p hp.2.1
  have hz : ∀ i, AnalyticOnNhd ℂ (z i) (U i) := fun i p hp =>
    (m36_constructed_chart_analytic _ _ _ _).2 p hp.2.2.2
  have hb : ∀ i, AnalyticOnNhd ℂ (b i) (U i) := by
    intro i p hp
    have hpb : AnalyticAt ℂ (modularCocyclePullback N) p :=
      ModularCocycleContinuationAux.pullback_analyticAt N p
        (Complex.slitPlane_ne_zero (hball hp.1).1)
    exact ((m36_constructed_chart_analytic _ _ _ _).1 _ hp.2.2.1).comp (x := p) hpb
  have hy : ∀ i, AnalyticOnNhd ℂ (y i) (U i) := by
    intro i p hp
    have hpb : AnalyticAt ℂ (modularCocyclePullback N) p :=
      ModularCocycleContinuationAux.pullback_analyticAt N p
        (Complex.slitPlane_ne_zero (hball hp.1).1)
    exact ((m36_constructed_chart_analytic _ _ _ _).2 _ hp.2.2.1).comp (x := p) hpb
  have hne : ∀ i p, p ∈ U i → ∀ᶠ w in 𝓝[≠] p.1,
      x i (w, p.2) ≠ 0 ∧ y i (w, p.2) ≠ 0 ∧ z i (w, p.2) ≠ 0 := by
    intro i p hp
    exact m36_cocycle_den_eventually M N m k n i.1 i.2.1 i.2.2 p
      (hball hp.1).1 hp.2.1 hp.2.2.1 hp.2.2.2
  have hcompat : ∀ i j p, p ∈ U i → p ∈ U j →
      a i p * x j p = a j p * x i p ∧
      b i p * y j p = b j p * y i p ∧
      c i p * z j p = c j p * z i p := by
    intro i j p hi hj
    exact ⟨m36_constructed_chart_overlap _ _ _ _ _ p hi.2.1 hj.2.1,
      m36_constructed_chart_overlap _ _ _ _ _ _ hi.2.2.1 hj.2.2.1,
      m36_constructed_chart_overlap _ _ _ _ _ p hi.2.2.2 hj.2.2.2⟩
  let τs : ℂ := (τ₀ : ℂ) + (δ / 2 : ℝ) * Complex.I
  have hτs : τs ∈ Metric.ball (τ₀ : ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [τs, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hδ), Complex.norm_I, mul_one]
    exact half_lt_self hδ
  have hτsim : 0 < τs.im := by
    simpa [τs] using half_pos hδ
  obtain ⟨i₀, hi₀⟩ := hcover (0, τs) ⟨Set.mem_univ _, hτs⟩
  have hseed : (fun p => a i₀ p * y i₀ p * z i₀ p - b i₀ p * c i₀ p * x i₀ p)
      =ᶠ[𝓝 (0, τs)] 0 := by
    have hu : IsOpen {p : ℂ × ℂ | 0 < p.2.im} :=
      isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd)
    filter_upwards [(hU i₀).mem_nhds hi₀, hu.mem_nhds hτsim] with p hp hpu
    exact sub_eq_zero.mpr (m36_cocycle_cross_of_germ M N m k n i₀.1 i₀.2.1 i₀.2.2 p
      (hball hp.1).1 hp.2.1 hp.2.2.1 hp.2.2.2
      (hupper p.1 p.2 hpu))
  have hId := ModularCocycleContinuationAux.cocycle_atlas_identity Ω U a b c x y z hΩ hU
    hsub hcover ha hb hc hx hy hz hne hcompat i₀ (0, τs) hi₀ hseed
  intro κMN κM κN p hpτ hpMN hpM hpN
  exact hId (κMN, κM, κN) p ⟨hpτ, hpMN, hpM, hpN⟩

theorem real_germ (M N : SL(2, ℤ))
    (hM : ModularPhiSupported M) (hN : ModularPhiSupported N)
    (hMN : ModularPhiSupported (M * N)) (m k n : ℤ) (τ₀ : ℝ)
    (hTN : 0 < (etaDenom N (τ₀ : ℂ)).re)
    (hTM : 0 < (etaDenom M (etaMobius N (τ₀ : ℂ))).re)
    (hupper : ∀ z τ : ℂ, 0 < τ.im →
      (fun w => modularPhiConstructed (M * N) m n w τ) =ᶠ[𝓝[≠] z]
        (fun w => modularPhiConstructed M k n
          (w / etaDenom N τ) (etaMobius N τ) * modularPhiConstructed N m k w τ)) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (τ₀ : ℂ) δ ⊆ modularCocycleDomain M N ∧
      ∀ τ ∈ Metric.ball (τ₀ : ℂ) δ, ∀ z : ℂ,
        (fun w => modularPhiConstructed (M * N) m n w τ) =ᶠ[𝓝[≠] z]
          (fun w => modularPhiConstructed M k n
              (w / etaDenom N τ) (etaMobius N τ) *
            modularPhiConstructed N m k w τ) := by
  obtain ⟨δ, hδ, hball, hcross⟩ := real_chart_cross_mul M N hM hN hMN m k n τ₀ hTN hTM hupper
  refine ⟨δ, hδ, hball, ?_⟩
  intro τ hτ z
  have hdom := hball hτ
  obtain ⟨κMN, hpMN⟩ := m36_constructed_chart_cover (M * N) m n (z, τ) hdom.2.2
  obtain ⟨κM, hpM⟩ := m36_constructed_chart_cover M k n
    (modularCocyclePullback N (z, τ)) hdom.2.1
  obtain ⟨κN, hpN⟩ := m36_constructed_chart_cover N m k (z, τ) hdom.1
  have ht : AnalyticAt ℂ (fun w : ℂ => (w, τ)) z := analyticAt_id.prod analyticAt_const
  have htM : AnalyticAt ℂ (fun w : ℂ => (w / etaDenom N τ, etaMobius N τ)) z :=
    (analyticAt_id.div_const (c := etaDenom N τ)).prod analyticAt_const
  have hev₁ : ∀ᶠ w in 𝓝[≠] z,
      (w, τ) ∈ modularPhiConstructedChartDomain (M * N) m n κMN :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (ht.continuousAt.preimage_mem_nhds ((m36_constructed_chart_isOpen _ _ _ _).mem_nhds hpMN))
  have hev₂ : ∀ᶠ w in 𝓝[≠] z,
      (w / etaDenom N τ, etaMobius N τ) ∈ modularPhiConstructedChartDomain M k n κM :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (htM.continuousAt.preimage_mem_nhds ((m36_constructed_chart_isOpen _ _ _ _).mem_nhds hpM))
  have hev₃ : ∀ᶠ w in 𝓝[≠] z,
      (w, τ) ∈ modularPhiConstructedChartDomain N m k κN :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (ht.continuousAt.preimage_mem_nhds ((m36_constructed_chart_isOpen _ _ _ _).mem_nhds hpN))
  have hden := m36_cocycle_den_eventually M N m k n κMN κM κN (z, τ) hdom.1 hpMN hpM hpN
  filter_upwards [hev₁, hev₂, hev₃, hden] with w h₁ h₂ h₃ hwden
  rw [m36_constructed_eq_chart _ _ _ _ (w, τ) h₁,
    m36_constructed_eq_chart _ _ _ _ (w / etaDenom N τ, etaMobius N τ) h₂,
    m36_constructed_eq_chart _ _ _ _ (w, τ) h₃, ← mul_div_mul_comm]
  apply (div_eq_div_iff hwden.1 (mul_ne_zero hwden.2.1 hwden.2.2)).mpr
  simpa only [modularCocyclePullback, mul_assoc] using hcross κMN κM κN (w, τ) hτ h₁ h₂ h₃


end SICLean.L4.ModularCocycleContinuationAux
