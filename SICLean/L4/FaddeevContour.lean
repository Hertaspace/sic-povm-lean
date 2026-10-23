import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Horizontal contour comparison

These lemmas pass from finite rectangular Cauchy identities to absolutely convergent horizontal
integrals. Vanishing side integrals include the fixed vertical length. The last lemma isolates the
separate finite identity needed for a clockwise semicircular indentation; it does not assume that
identity follows from a full-circle Cauchy theorem.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval

universe u v

namespace SICLean.L4.Contour

theorem exists_primitive_on_open_convex
    {s : Set ℂ} {f : ℂ → ℂ}
    (hs : Convex ℝ s) (ho : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ∃ F : ℂ → ℂ, ∀ w ∈ s, HasDerivAt F (f w) w := by
  obtain ⟨F, hF⟩ := hs.exists_forall_hasDerivWithinAt hf
  exact ⟨F, fun w hw => (hF w hw).hasDerivAt (ho.mem_nhds hw)⟩

theorem integral_of_primitive_along
    {F f : ℂ → ℂ} {γ γ' : ℝ → ℂ} {a b : ℝ}
    (hF : ∀ t ∈ [[a, b]], HasDerivAt F (f (γ t)) (γ t))
    (hγ : ∀ t ∈ [[a, b]], HasDerivAt γ (γ' t) t)
    (hint : IntervalIntegrable (fun t => f (γ t) * γ' t) volume a b) :
    (∫ t : ℝ in a..b, f (γ t) * γ' t) = F (γ b) - F (γ a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro t ht
  simpa [Function.comp_def, mul_comm] using (hF t ht).scomp t (hγ t ht)

theorem tendsto_intervalIntegral_of_continuousOn_compact
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {p : ι → ℝ} {F : ℝ → ℝ → ℂ} {δ a b : ℝ}
    (hδ : 0 ≤ δ)
    (hF : ContinuousOn F.uncurry (Icc 0 δ ×ˢ [[a, b]]))
    (hp : Tendsto p l (𝓝 0))
    (hpbound : ∀ᶠ i in l, p i ∈ Icc 0 δ) :
    Tendsto (fun i => ∫ t : ℝ in a..b, F (p i) t) l
      (𝓝 (∫ t : ℝ in a..b, F 0 t)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_uIcc).bddAbove_image hF.norm
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · filter_upwards [hpbound] with i hi
    have hc : ContinuousOn (F (p i)) [[a, b]] := by
      exact hF.comp (f := fun t : ℝ => (p i, t))
        (by fun_prop) (fun t ht => ⟨hi, ht⟩)
    exact hc.intervalIntegrable.def'.aestronglyMeasurable
  · filter_upwards [hpbound] with i hi
    exact ae_of_all _ (fun t ht => hM
      ⟨(p i, t), ⟨hi, uIoc_subset_uIcc ht⟩, rfl⟩)
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun t ht => by
      have hpoint : (0, t) ∈ Icc 0 δ ×ˢ [[a, b]] := ⟨⟨le_rfl, hδ⟩, uIoc_subset_uIcc ht⟩
      have hmap : Tendsto (fun i => (p i, t)) l
          (𝓝[Icc 0 δ ×ˢ [[a, b]]] (0, t)) := by
        apply tendsto_nhdsWithin_iff.mpr
        exact ⟨hp.prodMk_nhds tendsto_const_nhds,
          hpbound.mono (fun i hi => ⟨hi, uIoc_subset_uIcc ht⟩)⟩
      exact (hF (0, t) hpoint).tendsto.comp hmap)

/-- Compare the finite paths after moving the indentation strictly above the real axis. A primitive
exists on the open convex upper strip. -/
theorem indented_rect_identity_shifted
    {f : ℂ → ℂ} {H r h ε : ℝ} (R : ℝ)
    (hr : 0 ≤ r) (hrh : r ≤ h) (hε : 0 < ε) (hH : h + ε < H)
    (hf : DifferentiableOn ℂ f {w : ℂ | 0 < w.im ∧ w.im < H}) :
    (∫ x : ℝ in -R..-r, f ((x : ℂ) + (ε : ℂ) * I)) +
      (∫ θ : ℝ in Real.pi..0,
        f (circleMap 0 r θ + (ε : ℂ) * I) * (I * circleMap 0 r θ)) +
      (∫ x : ℝ in r..R, f ((x : ℂ) + (ε : ℂ) * I)) -
      (∫ x : ℝ in -R..R, f ((x : ℂ) + ((h + ε : ℝ) : ℂ) * I)) +
      I * (∫ y : ℝ in 0..h,
        f ((R : ℂ) + ((y + ε : ℝ) : ℂ) * I)) -
      I * (∫ y : ℝ in 0..h,
        f (((-R : ℝ) : ℂ) + ((y + ε : ℝ) : ℂ) * I)) = 0 := by
  let s : Set ℂ := {w : ℂ | 0 < w.im ∧ w.im < H}
  have hso : IsOpen s := isOpen_Ioo.preimage Complex.continuous_im
  have hsc : Convex ℝ s :=
    (convex_Ioo (𝕜 := ℝ) 0 H).linear_preimage Complex.imCLM.toLinearMap
  obtain ⟨F, hF⟩ := exists_primitive_on_open_convex hsc hso hf
  have hfc : ContinuousOn f s := hf.continuousOn
  have hp {a b : ℝ} {γ γ' : ℝ → ℂ}
      (hc : Continuous γ) (hc' : Continuous γ')
      (hm : MapsTo γ [[a,b]] s)
      (hd : ∀ t ∈ [[a,b]], HasDerivAt γ (γ' t) t) :
      (∫ t : ℝ in a..b, f (γ t) * γ' t) = F (γ b) - F (γ a) :=
    integral_of_primitive_along (fun t ht => hF (γ t) (hm ht)) hd
      (((hfc.comp hc.continuousOn hm).mul hc'.continuousOn).intervalIntegrable)
  have hlin (t : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    convert (Complex.ofRealCLM.hasDerivAt (x := t)) using 1 <;> rfl
  have hh (a b y : ℝ) (hy : 0 < y ∧ y < H) :
      (∫ x : ℝ in a..b, f ((x : ℂ) + (y : ℂ) * I)) =
        F ((b : ℂ) + (y : ℂ) * I) - F ((a : ℂ) + (y : ℂ) * I) := by
    simpa using hp (a := a) (b := b)
      (γ := fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (γ' := fun _ => 1)
      (by fun_prop) (by fun_prop) (fun x hx => by simpa [s] using hy)
      (fun x hx => (hlin x).add_const _)
  have hv (x : ℝ) :
      I * (∫ y : ℝ in 0..h, f ((x : ℂ) + ((y + ε : ℝ) : ℂ) * I)) =
        F ((x : ℂ) + ((h + ε : ℝ) : ℂ) * I) -
          F ((x : ℂ) + (ε : ℂ) * I) := by
    have hm : MapsTo (fun y : ℝ => (x : ℂ) + ((y + ε : ℝ) : ℂ) * I) [[0,h]] s := by
      intro y hy
      have hy' : 0 ≤ y ∧ y ≤ h := by
        simpa [uIcc_of_le (hr.trans hrh)] using hy
      simp only [s, mem_ofPred_eq, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
        I_re, mul_zero, add_zero, zero_add]
      constructor <;> linarith
    have hx := hp (a := 0) (b := h)
      (γ := fun y : ℝ => (x : ℂ) + ((y + ε : ℝ) : ℂ) * I) (γ' := fun _ => I)
      (by fun_prop) (by fun_prop) hm (fun y hy => by
        simpa [Complex.ofReal_add] using
          (((hlin y).add_const (ε : ℂ)).mul_const I).const_add (x : ℂ))
    simpa [intervalIntegral.integral_mul_const, mul_comm] using hx
  have ha :
      (∫ θ : ℝ in Real.pi..0,
        f (circleMap 0 r θ + (ε : ℂ) * I) * (I * circleMap 0 r θ)) =
      F ((r : ℂ) + (ε : ℂ) * I) -
        F (((-r : ℝ) : ℂ) + (ε : ℂ) * I) := by
    have hm : MapsTo (fun θ : ℝ => circleMap 0 r θ + (ε : ℂ) * I) [[Real.pi,0]] s := by
      intro θ hθ
      have hθ' : θ ∈ Icc 0 Real.pi := by simpa [uIcc_of_ge Real.pi_nonneg] using hθ
      have him : (circleMap 0 r θ).im = r * Real.sin θ := by
        simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_sin]
      have hsn := Real.sin_nonneg_of_mem_Icc hθ'
      have hsl := Real.sin_le_one θ
      have hm0 : 0 ≤ r * Real.sin θ := mul_nonneg hr hsn
      have hm1 : r * Real.sin θ ≤ r := by nlinarith
      simp only [s, mem_ofPred_eq, add_im, him, mul_im, ofReal_re, I_im, mul_one,
        ofReal_im, I_re, mul_zero]
      constructor <;> linarith
    have hx := hp (a := Real.pi) (b := 0)
      (γ := fun θ : ℝ => circleMap 0 r θ + (ε : ℂ) * I)
      (γ' := fun θ => circleMap 0 r θ * I)
      (by fun_prop) (by fun_prop) hm (fun θ hθ => (hasDerivAt_circleMap 0 r θ).add_const _)
    have hc0 : circleMap 0 r 0 = (r : ℂ) := by simp [circleMap]
    have hcp : circleMap 0 r Real.pi = -(r : ℂ) := by simp [circleMap]
    simpa only [hc0, hcp, Complex.ofReal_neg, mul_comm] using hx
  rw [hh (-R) (-r) ε ⟨hε, by linarith⟩, ha,
    hh r R ε ⟨hε, by linarith⟩, hh (-R) R (h+ε) ⟨by linarith, hH⟩,
    hv R, hv (-R)]
  push_cast
  ring

/-- A genuine finite clockwise upper indentation, obtained by taking the positive vertical
translation to zero on compact path pieces. -/
theorem indented_rect_identity
    {f : ℂ → ℂ} {H r h R : ℝ}
    (hr : 0 < r) (hrh : r ≤ h) (hR : r ≤ R)
    (hhH : h < H)
    (hf : DifferentiableOn ℂ f {w : ℂ | 0 < w.im ∧ w.im < H})
    (hfc : ContinuousOn f {w : ℂ | 0 ≤ w.im ∧ w.im < H ∧ w ≠ 0}) :
    (∫ x : ℝ in -R..-r, f (x : ℂ)) +
      (∫ θ : ℝ in Real.pi..0, f (circleMap 0 r θ) * (I * circleMap 0 r θ)) +
      (∫ x : ℝ in r..R, f (x : ℂ)) -
      (∫ x : ℝ in -R..R, f ((x : ℂ) + (h : ℂ) * I)) +
      I * (∫ y : ℝ in 0..h, f ((R : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in 0..h, f (((-R : ℝ) : ℂ) + (y : ℂ) * I)) = 0 := by
  let δ : ℝ := (H - h) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hH : h + δ < H := by dsimp [δ]; linarith
  let T : Set ℂ := {w : ℂ | 0 ≤ w.im ∧ w.im < H ∧ w ≠ 0}
  have hεbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Icc 0 δ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεδ
    exact ⟨hε.le, hεδ.le⟩
  have hlim {a b : ℝ} {J : ℝ → ℝ → ℂ}
      (hJ : ContinuousOn J.uncurry (Icc 0 δ ×ˢ [[a,b]])) :
      Tendsto (fun ε => ∫ t : ℝ in a..b, J ε t) (𝓝[>] 0)
        (𝓝 (∫ t : ℝ in a..b, J 0 t)) :=
    tendsto_intervalIntegral_of_continuousOn_compact hδ.le hJ
      nhdsWithin_le_nhds hεbound
  have hparam {a b : ℝ} {G : ℝ × ℝ → ℂ}
      (hGc : Continuous G) (hGt : MapsTo G (Icc 0 δ ×ˢ [[a,b]]) T) :
      ContinuousOn (f ∘ G) (Icc 0 δ ×ˢ [[a,b]]) :=
    hfc.comp hGc.continuousOn hGt
  have hreal {a b : ℝ} (hne : ∀ x ∈ [[a,b]], x ≠ 0) :
      ContinuousOn
        (fun p : ℝ × ℝ => f ((p.2 : ℂ) + (p.1 : ℂ) * I))
        (Icc 0 δ ×ˢ [[a,b]]) := by
    apply hparam (by fun_prop)
    intro p hp
    change 0 ≤ ((p.2 : ℂ) + (p.1 : ℂ) * I).im ∧
      ((p.2 : ℂ) + (p.1 : ℂ) * I).im < H ∧
      (p.2 : ℂ) + (p.1 : ℂ) * I ≠ 0
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add]
    refine ⟨hp.1.1, by linarith [hp.1.2], ?_⟩
    intro hz
    have hx : p.2 = 0 := by simpa using congrArg Complex.re hz
    exact hne p.2 hp.2 hx
  have hminus := hlim (a := -R) (b := -r)
    (J := fun ε x => f ((x : ℂ) + (ε : ℂ) * I))
    (hreal (a := -R) (b := -r) (fun x hx => by
    have hx' : -R ≤ x ∧ x ≤ -r := by
      simpa [uIcc_of_le (neg_le_neg hR)] using hx
    linarith))
  have hplus := hlim (a := r) (b := R)
    (J := fun ε x => f ((x : ℂ) + (ε : ℂ) * I))
    (hreal (a := r) (b := R) (fun x hx => by
    have hx' : r ≤ x ∧ x ≤ R := by simpa [uIcc_of_le hR] using hx
    linarith))
  have htopc : ContinuousOn
      (fun p : ℝ × ℝ => f ((p.2 : ℂ) + ((h + p.1 : ℝ) : ℂ) * I))
      (Icc 0 δ ×ˢ [[-R,R]]) := by
    apply hparam (by fun_prop)
    intro p hp
    change 0 ≤ ((p.2 : ℂ) + ((h + p.1 : ℝ) : ℂ) * I).im ∧
      ((p.2 : ℂ) + ((h + p.1 : ℝ) : ℂ) * I).im < H ∧
      (p.2 : ℂ) + ((h + p.1 : ℝ) : ℂ) * I ≠ 0
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add]
    refine ⟨by linarith [hp.1.1], by linarith [hp.1.2], ?_⟩
    intro hz
    have hi : h + p.1 = 0 := by simpa using congrArg Complex.im hz
    linarith [hp.1.1]
  have htop := hlim (a := -R) (b := R)
    (J := fun ε x => f ((x : ℂ) + ((h + ε : ℝ) : ℂ) * I)) htopc
  have hvertc (x : ℝ) (hx : x ≠ 0) : ContinuousOn
      (fun p : ℝ × ℝ => f ((x : ℂ) + ((p.2 + p.1 : ℝ) : ℂ) * I))
      (Icc 0 δ ×ˢ [[0,h]]) := by
    apply hparam (by fun_prop)
    intro p hp
    have hy : 0 ≤ p.2 ∧ p.2 ≤ h := by
      simpa [uIcc_of_le (hr.le.trans hrh)] using hp.2
    change 0 ≤ ((x : ℂ) + ((p.2 + p.1 : ℝ) : ℂ) * I).im ∧
      ((x : ℂ) + ((p.2 + p.1 : ℝ) : ℂ) * I).im < H ∧
      (x : ℂ) + ((p.2 + p.1 : ℝ) : ℂ) * I ≠ 0
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add]
    refine ⟨by linarith [hp.1.1], by linarith [hp.1.2], ?_⟩
    intro hz
    exact hx (by simpa using congrArg Complex.re hz)
  have hright := hlim (a := 0) (b := h)
    (J := fun ε y => f ((R : ℂ) + ((y + ε : ℝ) : ℂ) * I))
    (hvertc R (by linarith))
  have hleft := hlim (a := 0) (b := h)
    (J := fun ε y => f (((-R : ℝ) : ℂ) + ((y + ε : ℝ) : ℂ) * I))
    (hvertc (-R) (by linarith))
  have harcc : ContinuousOn
      (fun p : ℝ × ℝ =>
        f (circleMap 0 r p.2 + (p.1 : ℂ) * I) * (I * circleMap 0 r p.2))
      (Icc 0 δ ×ˢ [[Real.pi,0]]) := by
    apply ContinuousOn.mul
    · apply hparam (by fun_prop)
      intro p hp
      have hθ : p.2 ∈ Icc 0 Real.pi := by
        simpa [uIcc_of_ge Real.pi_nonneg] using hp.2
      have him : (circleMap 0 r p.2).im = r * Real.sin p.2 := by
        simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_sin]
      have hm0 := mul_nonneg hr.le (Real.sin_nonneg_of_mem_Icc hθ)
      have hm1 : r * Real.sin p.2 ≤ r := by nlinarith [Real.sin_le_one p.2]
      change 0 ≤ (circleMap 0 r p.2 + (p.1 : ℂ) * I).im ∧
        (circleMap 0 r p.2 + (p.1 : ℂ) * I).im < H ∧
        circleMap 0 r p.2 + (p.1 : ℂ) * I ≠ 0
      simp only [add_im, him, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
        I_re, mul_zero]
      refine ⟨by linarith [hp.1.1], by linarith [hp.1.2], ?_⟩
      intro hz
      have hi : r * Real.sin p.2 + p.1 = 0 := by
        simpa [him] using congrArg Complex.im hz
      have he : p.1 = 0 := by linarith [hp.1.1]
      have hc : circleMap 0 r p.2 = 0 := by simpa [he] using hz
      have hn := congrArg norm hc
      simp [norm_circleMap_zero, abs_of_pos hr, hr.ne'] at hn
    · fun_prop
  have harc := hlim (a := Real.pi) (b := 0)
    (J := fun ε θ => f (circleMap 0 r θ + (ε : ℂ) * I) * (I * circleMap 0 r θ))
    harcc
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ x : ℝ in -R..-r, f ((x : ℂ) + (ε : ℂ) * I)) +
        (∫ θ : ℝ in Real.pi..0,
          f (circleMap 0 r θ + (ε : ℂ) * I) * (I * circleMap 0 r θ)) +
        (∫ x : ℝ in r..R, f ((x : ℂ) + (ε : ℂ) * I)) -
        (∫ x : ℝ in -R..R, f ((x : ℂ) + ((h + ε : ℝ) : ℂ) * I)) +
        I * (∫ y : ℝ in 0..h,
          f ((R : ℂ) + ((y + ε : ℝ) : ℂ) * I)) -
        I * (∫ y : ℝ in 0..h,
          f (((-R : ℝ) : ℂ) + ((y + ε : ℝ) : ℂ) * I)) = 0 := by
    filter_upwards [self_mem_nhdsWithin, hεbound] with ε hε hεδ
    exact indented_rect_identity_shifted R hr.le hrh hε (by linarith [hεδ.2]) hf
  have hlimall := ((((hminus.add harc).add hplus).sub htop).add
    (hright.const_mul I)).sub (hleft.const_mul I)
  have hz := tendsto_nhds_unique hlimall
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] 0) (𝓝 0)).congr'
      (hevent.mono (fun _ he => he.symm)))
  simpa using hz

theorem horizontal_integral_eq_of_vanishing_sides
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (h₁ h₂ : ℝ)
    (hf : DifferentiableOn ℂ f {w : ℂ | w.im ∈ [[h₁, h₂]]})
    (h₁int : Integrable (fun x : ℝ => f ((x : ℂ) + (h₁ : ℂ) * I)))
    (h₂int : Integrable (fun x : ℝ => f ((x : ℂ) + (h₂ : ℂ) * I)))
    (hleft : Tendsto (fun x : ℝ => ∫ y : ℝ in h₁..h₂,
      f ((x : ℂ) + (y : ℂ) * I)) atBot (𝓝 0))
    (hright : Tendsto (fun x : ℝ => ∫ y : ℝ in h₁..h₂,
      f ((x : ℂ) + (y : ℂ) * I)) atTop (𝓝 0)) :
    (∫ x : ℝ, f ((x : ℂ) + (h₁ : ℂ) * I)) =
      ∫ x : ℝ, f ((x : ℂ) + (h₂ : ℂ) * I) := by
  have hrect (R : ℝ) :
      (∫ x : ℝ in -R..R, f ((x : ℂ) + (h₁ : ℂ) * I)) -
        (∫ x : ℝ in -R..R, f ((x : ℂ) + (h₂ : ℂ) * I)) +
        I • (∫ y : ℝ in h₁..h₂, f ((R : ℂ) + (y : ℂ) * I)) -
        I • (∫ y : ℝ in h₁..h₂, f (((-R : ℝ) : ℂ) + (y : ℂ) * I)) = 0 := by
    have hd : DifferentiableOn ℂ f
        ([[(((-R : ℝ) : ℂ) + (h₁ : ℂ) * I).re,
            ((R : ℂ) + (h₂ : ℂ) * I).re]] ×ℂ
          [[(((-R : ℝ) : ℂ) + (h₁ : ℂ) * I).im,
            ((R : ℂ) + (h₂ : ℂ) * I).im]]) := by
      apply hf.mono
      intro w hw
      simpa using hw.2
    simpa using Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      (((-R : ℝ) : ℂ) + (h₁ : ℂ) * I) ((R : ℂ) + (h₂ : ℂ) * I) hd
  have ht₁ := MeasureTheory.intervalIntegral_tendsto_integral h₁int
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have ht₂ := MeasureTheory.intervalIntegral_tendsto_integral h₂int
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hl := hleft.comp tendsto_neg_atTop_atBot
  have hlim := ((ht₁.sub ht₂).add (hright.const_smul I)).sub (hl.const_smul I)
  have heq :
      (∫ x : ℝ, f ((x : ℂ) + (h₁ : ℂ) * I)) -
        (∫ x : ℝ, f ((x : ℂ) + (h₂ : ℂ) * I)) = 0 := by
    simpa using tendsto_nhds_unique hlim
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : E)) atTop (𝓝 0)).congr
        (fun R => (hrect R).symm))
  exact sub_eq_zero.mp heq

theorem tendsto_intervalIntegral_zero_of_uniform_bound
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {l : Filter ι} {a b : ℝ}
    {g : ι → ℝ → E} {M : ι → ℝ}
    (hbound : ∀ᶠ i in l, ∀ y ∈ [[a, b]], ‖g i y‖ ≤ M i)
    (hM : Tendsto M l (𝓝 0)) :
    Tendsto (fun i => ∫ y : ℝ in a..b, g i y) l (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun i => M i * |b - a|)
  · filter_upwards [hbound] with i hi
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y hy => hi y (uIoc_subset_uIcc hy))
  · simpa using hM.mul_const |b - a|

theorem horizontal_eq_detour_of_finite_identity
    (f : ℂ → ℂ) (h r : ℝ) (A : ℂ)
    (hline : Integrable (fun x : ℝ => f ((x : ℂ) + (h : ℂ) * I)))
    (hminus : IntegrableOn (fun x : ℝ => f (x : ℂ)) (Iic (-r)))
    (hplus : IntegrableOn (fun x : ℝ => f (x : ℂ)) (Ici r))
    (hleft : Tendsto (fun x : ℝ => ∫ y : ℝ in 0..h,
      f ((x : ℂ) + (y : ℂ) * I)) atBot (𝓝 0))
    (hright : Tendsto (fun x : ℝ => ∫ y : ℝ in 0..h,
      f ((x : ℂ) + (y : ℂ) * I)) atTop (𝓝 0))
    (hfinite : ∀ᶠ R : ℝ in atTop,
      (∫ x : ℝ in -R..-r, f (x : ℂ)) + A +
        (∫ x : ℝ in r..R, f (x : ℂ)) -
        (∫ x : ℝ in -R..R, f ((x : ℂ) + (h : ℂ) * I)) +
        I * (∫ y : ℝ in 0..h, f ((R : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ in 0..h, f (((-R : ℝ) : ℂ) + (y : ℂ) * I)) = 0) :
    (∫ x : ℝ, f ((x : ℂ) + (h : ℂ) * I)) =
      (∫ x : ℝ in Iic (-r), f (x : ℂ)) + A +
        (∫ x : ℝ in Ici r, f (x : ℂ)) := by
  have hm := intervalIntegral_tendsto_integral_Iic (-r) hminus
    (tendsto_neg_atTop_atBot : Tendsto (fun R : ℝ => -R) atTop atBot)
  have hp := intervalIntegral_tendsto_integral_Ioi r (hplus.mono_set Ioi_subset_Ici_self)
    (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  rw [← integral_Ici_eq_integral_Ioi] at hp
  have htop := intervalIntegral_tendsto_integral hline tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hl := hleft.comp tendsto_neg_atTop_atBot
  have hlim := ((((hm.add_const A).add hp).sub htop).add (hright.const_mul I)).sub
    (hl.const_mul I)
  have hz := tendsto_nhds_unique hlim
    (Filter.Tendsto.congr' (hfinite.mono (fun _ h => h.symm))
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0)))
  simpa using (sub_eq_zero.mp (by simpa using hz)).symm

theorem horizontal_eq_detour
    {f : ℂ → ℂ} {H r h : ℝ}
    (hr : 0 < r) (hrh : r ≤ h) (hhH : h < H)
    (hf : DifferentiableOn ℂ f {w : ℂ | 0 < w.im ∧ w.im < H})
    (hfc : ContinuousOn f {w : ℂ | 0 ≤ w.im ∧ w.im < H ∧ w ≠ 0})
    (hline : Integrable (fun x : ℝ => f ((x : ℂ) + (h : ℂ) * I)))
    (hminus : IntegrableOn (fun x : ℝ => f (x : ℂ)) (Iic (-r)))
    (hplus : IntegrableOn (fun x : ℝ => f (x : ℂ)) (Ici r))
    (hleft : Tendsto (fun x : ℝ => ∫ y : ℝ in 0..h,
      f ((x : ℂ) + (y : ℂ) * I)) atBot (𝓝 0))
    (hright : Tendsto (fun x : ℝ => ∫ y : ℝ in 0..h,
      f ((x : ℂ) + (y : ℂ) * I)) atTop (𝓝 0)) :
    (∫ x : ℝ, f ((x : ℂ) + (h : ℂ) * I)) =
      (∫ x : ℝ in Iic (-r), f (x : ℂ)) +
        (∫ θ : ℝ in Real.pi..0, f (circleMap 0 r θ) * (I * circleMap 0 r θ)) +
        (∫ x : ℝ in Ici r, f (x : ℂ)) := by
  apply horizontal_eq_detour_of_finite_identity f h r _ hline hminus hplus hleft hright
  filter_upwards [eventually_ge_atTop r] with R hR
  exact indented_rect_identity hr hrh hR hhH hf hfc

/-- The inverse kernel on the upper half of a rectangle. The clockwise small semicircle contributes
`-π i`. -/
theorem inv_upper_rect_identity {R h : ℝ} (hR : 0 < R) (hh : 0 < h) :
    -(∫ x : ℝ in -R..R, ((x : ℂ) + (h : ℂ) * I)⁻¹) +
      I * (∫ y : ℝ in 0..h, ((R : ℂ) + (y : ℂ) * I)⁻¹) -
      I * (∫ y : ℝ in 0..h, (((-R : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) =
      (Real.pi : ℂ) * I := by
  let r : ℝ := min R h
  have hr : 0 < r := lt_min hR hh
  have hrR : r ≤ R := min_le_left _ _
  have hrh : r ≤ h := min_le_right _ _
  have hf : DifferentiableOn ℂ (fun w : ℂ => w⁻¹)
      {w : ℂ | 0 < w.im ∧ w.im < h+1} := by
    apply differentiableOn_id.inv
    intro w hw hz
    have : w.im = 0 := by simp [hz]
    linarith [hw.1]
  have hfc : ContinuousOn (fun w : ℂ => w⁻¹)
      {w : ℂ | 0 ≤ w.im ∧ w.im < h+1 ∧ w ≠ 0} :=
    continuousOn_id.inv₀ (fun w hw => hw.2.2)
  have he := indented_rect_identity (f := fun w : ℂ => w⁻¹)
    hr hrh hrR (show h < h+1 by linarith) hf hfc
  have harc :
      (∫ θ : ℝ in Real.pi..0, (circleMap 0 r θ)⁻¹ * (I * circleMap 0 r θ)) =
        -(Real.pi : ℂ) * I := by
    have hc (θ : ℝ) : (circleMap 0 r θ)⁻¹ * (I * circleMap 0 r θ) = I := by
      have hn : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
      field_simp
    simp_rw [hc]
    simp [intervalIntegral.integral_const, real_smul]
  have ht : (∫ x : ℝ in -R..-r, (x : ℂ)⁻¹) =
      -(∫ x : ℝ in r..R, (x : ℂ)⁻¹) := by
    have hn := intervalIntegral.integral_comp_neg (a := r) (b := R)
      (fun x : ℝ => (x : ℂ)⁻¹)
    simpa only [Complex.ofReal_neg, inv_neg, intervalIntegral.integral_neg] using hn.symm
  rw [harc, ht] at he
  linear_combination he

/-- Glue the two indented half rectangles. This is the finite small-circle correction used below for
a simple pole. -/
theorem integral_boundary_rect_inv
    {R A B : ℝ} (hR : 0 < R) (hA : 0 < A) (hB : 0 < B) :
    (∫ x : ℝ in -R..R, ((x : ℂ) + ((-A : ℝ) : ℂ) * I)⁻¹) -
      (∫ x : ℝ in -R..R, ((x : ℂ) + (B : ℂ) * I)⁻¹) +
      I * (∫ y : ℝ in -A..B, ((R : ℂ) + (y : ℂ) * I)⁻¹) -
      I * (∫ y : ℝ in -A..B, (((-R : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) =
      2 * (Real.pi : ℂ) * I := by
  have htop :
      (∫ x : ℝ in -R..R, ((x : ℂ) + ((-A : ℝ) : ℂ) * I)⁻¹) =
        -(∫ x : ℝ in -R..R, ((x : ℂ) + (A : ℂ) * I)⁻¹) := by
    have hn := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun x : ℝ => ((x : ℂ) + ((-A : ℝ) : ℂ) * I)⁻¹)
    have hpoint (x : ℝ) :
        (((-x : ℝ) : ℂ) + ((-A : ℝ) : ℂ) * I) = -((x : ℂ) + (A : ℂ) * I) := by
      push_cast
      ring
    simp_rw [hpoint, inv_neg] at hn
    simpa only [intervalIntegral.integral_neg, neg_neg] using hn.symm
  have hvneg (x : ℝ) :
      (∫ y : ℝ in -A..0, ((x : ℂ) + (y : ℂ) * I)⁻¹) =
        -(∫ y : ℝ in 0..A, (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) := by
    have hn := intervalIntegral.integral_comp_neg (a := 0) (b := A)
      (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I)⁻¹)
    have hpoint (y : ℝ) :
        (x : ℂ) + ((-y : ℝ) : ℂ) * I = -(((-x : ℝ) : ℂ) + (y : ℂ) * I) := by
      push_cast
      ring
    simp_rw [hpoint, inv_neg] at hn
    simpa only [intervalIntegral.integral_neg, neg_zero] using hn.symm
  have hvint (x : ℝ) (hx : x ≠ 0) (a b : ℝ) :
      IntervalIntegrable (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I)⁻¹) volume a b := by
    have hc : Continuous (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I)⁻¹) := by
      apply Continuous.inv₀ (by fun_prop)
      intro y hz
      exact hx (by simpa using congrArg Complex.re hz)
    exact hc.intervalIntegrable a b
  have hvr := intervalIntegral.integral_add_adjacent_intervals
    (hvint R hR.ne' (-A) 0) (hvint R hR.ne' 0 B)
  have hvl := intervalIntegral.integral_add_adjacent_intervals
    (hvint (-R) (neg_ne_zero.mpr hR.ne') (-A) 0)
    (hvint (-R) (neg_ne_zero.mpr hR.ne') 0 B)
  rw [htop, ← hvr, ← hvl, hvneg R, hvneg (-R)]
  simp only [neg_neg]
  have huA := inv_upper_rect_identity hR hA
  have huB := inv_upper_rect_identity hR hB
  linear_combination huA + huB

theorem integral_boundary_rect_simple_pole
    {R A B : ℝ} {f g : ℂ → ℂ} (c : ℂ)
    (hR : 0 < R) (hA : 0 < A) (hB : 0 < B)
    (hg : DifferentiableOn ℂ g ([[(-R),R]] ×ℂ [[(-A),B]]))
    (hfg : ∀ w ∈ ([[(-R),R]] ×ℂ [[(-A),B]]), w ≠ 0 → f w = c * w⁻¹ + g w) :
    (∫ x : ℝ in -R..R, f ((x : ℂ) + ((-A : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in -R..R, f ((x : ℂ) + (B : ℂ) * I)) +
      I * (∫ y : ℝ in -A..B, f ((R : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in -A..B, f (((-R : ℝ) : ℂ) + (y : ℂ) * I)) =
      2 * (Real.pi : ℂ) * I * c := by
  have hhm (y : ℝ) (hy : y ∈ [[-A,B]]) :
      MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * I)
        [[-R,R]] ([[-R,R]] ×ℂ [[-A,B]]) := by
    intro x hx
    simpa [Complex.mem_reProdIm] using And.intro hx hy
  have hvm (x : ℝ) (hx : x ∈ [[-R,R]]) :
      MapsTo (fun y : ℝ => (x : ℂ) + (y : ℂ) * I)
        [[-A,B]] ([[-R,R]] ×ℂ [[-A,B]]) := by
    intro y hy
    simpa [Complex.mem_reProdIm] using And.intro hx hy
  have hhne (y : ℝ) (hy : y ≠ 0) (x : ℝ) : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro hz
    exact hy (by simpa using congrArg Complex.im hz)
  have hvne (x : ℝ) (hx : x ≠ 0) (y : ℝ) : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro hz
    exact hx (by simpa using congrArg Complex.re hz)
  have hhg (y : ℝ) (hy : y ∈ [[-A,B]]) :
      IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) volume (-R) R :=
    (hg.continuousOn.comp (by fun_prop) (hhm y hy)).intervalIntegrable
  have hvg (x : ℝ) (hx : x ∈ [[-R,R]]) :
      IntervalIntegrable (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) volume (-A) B :=
    (hg.continuousOn.comp (by fun_prop) (hvm x hx)).intervalIntegrable
  have hhci (y : ℝ) (hy : y ≠ 0) :
      IntervalIntegrable (fun x : ℝ => c * ((x : ℂ) + (y : ℂ) * I)⁻¹) volume (-R) R := by
    have hc : Continuous (fun x : ℝ => c * ((x : ℂ) + (y : ℂ) * I)⁻¹) := by
      apply Continuous.mul continuous_const
      exact Continuous.inv₀ (by fun_prop) (hhne y hy)
    exact hc.intervalIntegrable (-R) R
  have hvci (x : ℝ) (hx : x ≠ 0) :
      IntervalIntegrable (fun y : ℝ => c * ((x : ℂ) + (y : ℂ) * I)⁻¹) volume (-A) B := by
    have hc : Continuous (fun y : ℝ => c * ((x : ℂ) + (y : ℂ) * I)⁻¹) := by
      apply Continuous.mul continuous_const
      exact Continuous.inv₀ (by fun_prop) (hvne x hx)
    exact hc.intervalIntegrable (-A) B
  have hhf (y : ℝ) (hy : y ∈ [[-A,B]]) (hyne : y ≠ 0) :
      (∫ x : ℝ in -R..R, f ((x : ℂ) + (y : ℂ) * I)) =
        c * (∫ x : ℝ in -R..R, ((x : ℂ) + (y : ℂ) * I)⁻¹) +
        (∫ x : ℝ in -R..R, g ((x : ℂ) + (y : ℂ) * I)) := by
    calc
      _ = ∫ x : ℝ in -R..R, c * ((x : ℂ) + (y : ℂ) * I)⁻¹ +
          g ((x : ℂ) + (y : ℂ) * I) :=
        intervalIntegral.integral_congr (fun x hx => hfg _ (hhm y hy hx) (hhne y hyne x))
      _ = _ := by
        rw [intervalIntegral.integral_add (hhci y hyne) (hhg y hy),
          intervalIntegral.integral_const_mul]
  have hvf (x : ℝ) (hx : x ∈ [[-R,R]]) (hxne : x ≠ 0) :
      (∫ y : ℝ in -A..B, f ((x : ℂ) + (y : ℂ) * I)) =
        c * (∫ y : ℝ in -A..B, ((x : ℂ) + (y : ℂ) * I)⁻¹) +
        (∫ y : ℝ in -A..B, g ((x : ℂ) + (y : ℂ) * I)) := by
    calc
      _ = ∫ y : ℝ in -A..B, c * ((x : ℂ) + (y : ℂ) * I)⁻¹ +
          g ((x : ℂ) + (y : ℂ) * I) :=
        intervalIntegral.integral_congr (fun y hy => hfg _ (hvm x hx hy) (hvne x hxne y))
      _ = _ := by
        rw [intervalIntegral.integral_add (hvci x hxne) (hvg x hx),
          intervalIntegral.integral_const_mul]
  have hgzero :
      (∫ x : ℝ in -R..R, g ((x : ℂ) + ((-A : ℝ) : ℂ) * I)) -
        (∫ x : ℝ in -R..R, g ((x : ℂ) + (B : ℂ) * I)) +
        I * (∫ y : ℝ in -A..B, g ((R : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ in -A..B, g (((-R : ℝ) : ℂ) + (y : ℂ) * I)) = 0 := by
    have hd : DifferentiableOn ℂ g
        ([[((((-R : ℝ) : ℂ) + ((-A : ℝ) : ℂ) * I).re),
            (((R : ℂ) + (B : ℂ) * I).re)]] ×ℂ
          [[((((-R : ℝ) : ℂ) + ((-A : ℝ) : ℂ) * I).im),
            (((R : ℂ) + (B : ℂ) * I).im)]]) := by simpa using hg
    simpa [smul_eq_mul] using Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
      (((-R : ℝ) : ℂ) + ((-A : ℝ) : ℂ) * I) ((R : ℂ) + (B : ℂ) * I) hd
  rw [hhf (-A) left_mem_uIcc (neg_ne_zero.mpr hA.ne'),
    hhf B right_mem_uIcc hB.ne', hvf R right_mem_uIcc hR.ne',
    hvf (-R) left_mem_uIcc (neg_ne_zero.mpr hR.ne')]
  have hi := integral_boundary_rect_inv hR hA hB
  linear_combination c * hi + hgzero

theorem integral_boundary_rect_simple_pole_of_strip
    {R A B lo hi : ℝ} {f g : ℂ → ℂ} (p c : ℂ)
    (hR : 0 < R) (hA : 0 < A) (hB : 0 < B)
    (hlo : lo < p.im - A) (hhi : p.im + B < hi)
    (hg : DifferentiableOn ℂ g {w : ℂ | lo < w.im ∧ w.im < hi})
    (hfg : ∀ w, lo < w.im → w.im < hi → w ≠ p → f w = c / (w - p) + g w) :
    (∫ x : ℝ in -R..R, f (p + ((x : ℂ) + ((-A : ℝ) : ℂ) * I))) -
      (∫ x : ℝ in -R..R, f (p + ((x : ℂ) + (B : ℂ) * I))) +
      I * (∫ y : ℝ in -A..B, f (p + ((R : ℂ) + (y : ℂ) * I))) -
      I * (∫ y : ℝ in -A..B, f (p + (((-R : ℝ) : ℂ) + (y : ℂ) * I))) =
      2 * (Real.pi : ℂ) * I * c := by
  have hm : MapsTo (fun w : ℂ => p + w) ([[-R,R]] ×ℂ [[-A,B]])
      {w : ℂ | lo < w.im ∧ w.im < hi} := by
    intro w hw
    have him : -A ≤ w.im ∧ w.im ≤ B := by
      simpa [uIcc_of_le (show -A ≤ B by linarith)] using hw.2
    change lo < (p + w).im ∧ (p + w).im < hi
    simp only [Complex.add_im]
    constructor <;> linarith
  have hgd : DifferentiableOn ℂ (fun w : ℂ => g (p + w)) ([[-R,R]] ×ℂ [[-A,B]]) :=
    hg.comp (by fun_prop) hm
  exact integral_boundary_rect_simple_pole (f := fun w => f (p+w))
    (g := fun w => g (p+w)) c hR hA hB hgd (by
      intro w hw hne
      have hpne : p+w ≠ p := by
        intro he
        exact hne (by simpa using he)
      simpa [div_eq_mul_inv] using hfg (p+w) (hm hw).1 (hm hw).2 hpne)

end SICLean.L4.Contour
