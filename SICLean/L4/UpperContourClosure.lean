import SICLean.L4.UpperContourSides
import SICLean.L4.UpperContourUpperArc
import SICLean.L4.UpperContourLowerArc
import SICLean.L4.UpperContourClosureAux

set_option autoImplicit false

/-!
# Finite clockwise residue ledger

Finite-contour and limit theorems. The parallelogram ledger is a new finite
bridge: the axis-aligned rectangle theorem cannot be applied by a complex
affine change of coordinates to the non-orthogonal basis (T,1).
All local principal parts are punctured comparisons. The center point
values are never inferred from a germ or a raw q-product quotient.

`sum_lines_eq_box_limit` is the main downstream entry after summing m.
`lineIntegral_eq_of_residueBox_limit` also supplies the per-m form when a
finite box sum limit has been computed. No q-binomial/Euler sum or G1
product identity is assumed here. The rotations and the residue computations motivate the q-germ
bridge.
[RW26, pp. 28--29, Appendix A.2]. No Jordan lemma is taken as an axiom.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContour

/--
Only an upper-plane q-product comparator. It does not prescribe
values at common product zeros, and is used through punctured germs.
-/
def qKernel (kind : Kind) (M : SL(2, ℤ)) (m n h ℓ p : ℤ)
    (x : UpperWindow.Parameters) (z : ℂ) : ℂ :=
  match kind with
  | .single => modularPhiQProduct M (m + 1) n z x.1 *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)
  | .ratio => (modularPhiQProduct M (m + 1) n z x.1 /
      modularPhiQProduct M (m + p) n (z + x.2.2) x.1) *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)

/--
Punctured-germ invariance, with no center point identification.
Finite-residue infrastructure; [RW26, p. 29].
[RW26, pp. 28--29].
-/
theorem simpleResidue_germ_congr (f g : ℂ → ℂ) (a : ℂ)
    (hfg : f =ᶠ[𝓝[≠] a] g) : simpleResidue f a = simpleResidue g a := by
  unfold simpleResidue Filter.limUnder
  exact congrArg Filter.lim (Filter.map_congr (hfg.mono fun z hz => by
    dsimp only
    rw [hz]))

/--
Regular germs have zero candidate residue. [RW26, p. 29].
[RW26, pp. 28--29].
-/
theorem simpleResidue_of_analytic (f : ℂ → ℂ) (a : ℂ) (hf : AnalyticAt ℂ f a) :
    simpleResidue f a = 0 := by
  apply Filter.Tendsto.limUnder_eq
  have hc : ContinuousAt (fun z : ℂ => (z - a) * f z) a := by
    fun_prop
  simpa only [sub_self, zero_mul] using hc.tendsto.mono_left
    (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)

/--
At-most-simple Laurent germ identifies both the limit and coefficient.
The raw value f(a) is irrelevant. [RW26, p. 29].
[RW26, pp. 28--29].
-/
theorem simpleResidue_of_principalPart (f g : ℂ → ℂ) (a A : ℂ)
    (hg : AnalyticAt ℂ g a)
    (hfg : f =ᶠ[𝓝[≠] a] (fun z => A / (z - a) + g z)) :
    Tendsto (fun z => (z - a) * f z) (𝓝[≠] a) (𝓝 A) ∧ simpleResidue f a = A := by
  have ht : Tendsto (fun z : ℂ => A + (z - a) * g z) (𝓝[≠] a) (𝓝 A) := by
    have hc : ContinuousAt (fun z : ℂ => A + (z - a) * g z) a := by
      fun_prop
    simpa only [sub_self, zero_mul, add_zero] using hc.tendsto.mono_left
      (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)
  have hlim : Tendsto (fun z => (z - a) * f z) (𝓝[≠] a) (𝓝 A) := by
    apply ht.congr'
    filter_upwards [hfg, self_mem_nhdsWithin] with z hz hza
    rw [hz]
    have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
    field_simp
  exact ⟨hlim, hlim.limUnder_eq⟩

/--
Every numerator label admits a local simple principal part, including
cancelled ratio poles (coefficient zero). This proves existence of the
candidate residue limit rather than assuming it; [RW26, p. 6, p. 29] (residue use).
[RW26, pp. 28--29].
-/
theorem kernel_simple_principalPart (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    let f := kernel kind M m n h ℓ p x
    let a := modularPhiPolePoint M (m + 1) n x.1 k.1 k.2
    (Tendsto (fun z => (z - a) * f z) (𝓝[≠] a) (𝓝 (simpleResidue f a))) ∧
      ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ AnalyticOnNhd ℂ g (Metric.closedBall a r) ∧
        ∀ z ∈ Metric.closedBall a r, z ≠ a → f z = simpleResidue f a / (z - a) + g z := by
  let f := UpperContour.kernel kind M m n h ℓ p x
  let a := modularPhiPolePoint M (m + 1) n x.1 k.1 k.2
  have hτ : x.1 ∈ modularPhiDomain M :=
    (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).1
  have hf : MeromorphicAt f a :=
    UpperContour.kernel_meromorphic kind M hc.1 m n h ℓ p x hτ a (Set.mem_univ _)
  obtain ⟨A, g, hg, hfg⟩ := UpperContourClosureAux.simple_principalPart_germ_of_order f a hf
    (UpperContourClosureAux.kernel_order_ge_neg_one kind M h ℓ p m n ψ σ ρ δ hc x hx k hk)
  obtain ⟨hlim, hres⟩ := UpperContour.simpleResidue_of_principalPart f g a A hg hfg
  have hnear : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ g z ∧
      (z ≠ a → f z = A / (z - a) + g z) := by
    exact hg.eventually_analyticAt.and (eventually_nhdsWithin_iff.mp hfg)
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  change Tendsto (fun z => (z - a) * f z) (𝓝[≠] a) (𝓝 (UpperContour.simpleResidue f a)) ∧ _
  rw [hres]
  exact ⟨hlim, r, g, hr, fun z hz => (hrs hz).1, fun z hz => (hrs hz).2⟩

/--
Finite analytic bridge for the actual tilted parallelogram. Input
consists of explicit local expansions and analyticity, never an assumed
residue theorem. All pole orders, including zero and higher orders, are
allowed in this general lemma. The clockwise coefficient is -2πi.
This extends `rectangle_finite_principal_parts` to this finite boundary.
[RW26, pp. 28--29].
-/
theorem parallelogram_finite_principal_parts (f : ℂ → ℂ) (v T : ℂ)
    (hT : 0 < T.im) (R : ℕ) (hR : 1 ≤ R) (P : Finset ℂ)
    (r : ℂ → ℝ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ)
    (hr : ∀ a ∈ P, 0 < r a)
    (hinside : ∀ a ∈ P, Metric.closedBall a (r a) ⊆ openBox v T (R : ℝ))
    (hdisj : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      Disjoint (Metric.closedBall a (r a)) (Metric.closedBall b (r b)))
    (hf : AnalyticOnNhd ℂ f (closedBox v T (R : ℝ) \ (P : Set ℂ)))
    (hg : ∀ a ∈ P, AnalyticOnNhd ℂ (g a) (Metric.closedBall a (r a)))
    (hfg : ∀ a ∈ P, ∀ z ∈ Metric.closedBall a (r a), z ≠ a →
      f z = FinitePrincipalParts.principalPart a (N a) (A a) z + g a z) :
    clockwiseBoundary f v T R = -2 * (Real.pi : ℂ) * Complex.I *
      ∑ a ∈ P, FinitePrincipalParts.residueCoefficient (N a) (A a) := by
  exact UpperContourClosureAux.parallelogram_finite_principal_parts
    f v T hT R hR P r N A g hr hinside hdisj hf hg hfg

/--
Finite R identity for either kernel; all four edges are still present.
No inverse-denominator poles enter, and no cancellation center is removed
from boxLabels. [RW26, pp. 28--29].
-/
theorem finite_clockwise_residue (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) (hR : 1 ≤ R) :
    clockwiseBoundary (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
      (etaDenom M x.1) R = -2 * (Real.pi : ℂ) * Complex.I *
        residueBox (kernel kind M m n h ℓ p x) M m n x.1 R := by
  classical
  let f := kernel kind M m n h ℓ p x
  let v := UpperWindow.base M m n δ x.1
  let T := etaDenom M x.1
  let P := boxCenters M m n x.1 R
  have hM : 0 < M 1 0 := hc.1
  have hτ : 0 < x.1.im := hx.1.1
  have hT : 0 < T.im := im_etaDenom_pos_of_im_pos M hM hτ
  have hδ : 0 < δ := hc.2.2.2.2.2.2.1
  have hχ : (M 1 0 : ℝ) * δ < 1 :=
    (UpperWindow.radius_margins M ψ σ ρ δ hc).2.2.2.2.2
  have hopen : IsOpen (openBox v T (R : ℝ)) := by
    have h₁ : Continuous (fun z : ℂ => (UpperWindow.coords T (z - v)).1) := by
      unfold UpperWindow.coords
      fun_prop
    have h₂ : Continuous (fun z : ℂ => (UpperWindow.coords T (z - v)).2) := by
      unfold UpperWindow.coords
      fun_prop
    exact (isOpen_lt continuous_const h₁).inter
      ((isOpen_lt h₁ continuous_const).inter
        ((isOpen_lt continuous_const h₂).inter (isOpen_lt h₂ continuous_const)))
  have hinside : ∀ a ∈ P, a ∈ openBox v T (R : ℝ) := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨⟨K, J⟩, hk, rfl⟩
    apply (pole_mem_openBox_iff M hM m n δ hδ hχ x.1 hτ R K J hR).mpr
    exact ⟨((mem_boxLabels M m n R K J).mp hk).1,
      ((mem_boxLabels M m n R K J).mp hk).2.1⟩
  have hlocal : ∀ a ∈ P, ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧
      AnalyticOnNhd ℂ g (Metric.closedBall a r) ∧
        ∀ z ∈ Metric.closedBall a r, z ≠ a →
          f z = simpleResidue f a / (z - a) + g z := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    exact (kernel_simple_principalPart kind M h ℓ p m n ψ σ ρ δ hc x hx k
      (Finset.mem_filter.mp hk).2).2
  choose! r₀ g hr₀ hg hfg using hlocal
  obtain ⟨d, hd, hsep⟩ :=
    (Set.pairwiseDisjoint_nhds (P : Set ℂ)).exists_mem_filter_basis P.finite_toSet
      (fun _ => Metric.nhds_basis_closedBall)
  have hsmall : ∀ a ∈ P, ∃ e : ℝ, 0 < e ∧
      Metric.closedBall a e ⊆ openBox v T (R : ℝ) ∩ Metric.ball a (r₀ a) := by
    intro a ha
    exact Metric.nhds_basis_closedBall.mem_iff.mp
      (inter_mem (hopen.mem_nhds (hinside a ha)) (Metric.ball_mem_nhds a (hr₀ a ha)))
  choose! e he heinside using hsmall
  let r : ℂ → ℝ := fun a => min (d a) (e a)
  have hr : ∀ a ∈ P, 0 < r a := by
    intro a ha
    exact lt_min (hd a) (he a ha)
  have hsub₁ (a : ℂ) : Metric.closedBall a (r a) ⊆ Metric.closedBall a (d a) :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hsub₂ (a : ℂ) : Metric.closedBall a (r a) ⊆ Metric.closedBall a (e a) :=
    Metric.closedBall_subset_closedBall (min_le_right _ _)
  have hinside' : ∀ a ∈ P, Metric.closedBall a (r a) ⊆ openBox v T (R : ℝ) := by
    intro a ha z hz
    exact (heinside a ha (hsub₂ a hz)).1
  have hdisj : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      Disjoint (Metric.closedBall a (r a)) (Metric.closedBall b (r b)) := by
    intro a ha b hb hab
    exact (hsep ha hb hab).mono (hsub₁ a) (hsub₁ b)
  have hsub₀ (a : ℂ) (ha : a ∈ P) :
      Metric.closedBall a (r a) ⊆ Metric.closedBall a (r₀ a) := by
    intro z hz
    exact Metric.ball_subset_closedBall (heinside a ha (hsub₂ a hz)).2
  have hg' : ∀ a ∈ P, AnalyticOnNhd ℂ (g a) (Metric.closedBall a (r a)) := by
    intro a ha
    exact (hg a ha).mono (hsub₀ a ha)
  have hfg' : ∀ a ∈ P, ∀ z ∈ Metric.closedBall a (r a), z ≠ a →
      f z = FinitePrincipalParts.principalPart a 1 (fun _ => simpleResidue f a) z + g a z := by
    intro a ha z hz hza
    simpa [FinitePrincipalParts.principalPart] using hfg a ha z (hsub₀ a ha hz) hza
  have hledger := parallelogram_finite_principal_parts f v T hT R hR P r
    (fun _ => 1) (fun a _ => simpleResidue f a) g hr hinside' hdisj
    (kernel_analytic_off_box kind M h ℓ p m n ψ σ ρ δ hc x hx R hR) hg' hfg'
  have hsum : (∑ a ∈ P, simpleResidue f a) = residueBox f M m n x.1 R := by
    dsimp only [P, boxCenters, residueBox]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact polePoint_injective M hM m n x.1 hτ hab
  simp only [FinitePrincipalParts.residueCoefficient, one_ne_zero, ↓reduceIte] at hledger
  rw [hsum] at hledger
  exact hledger

/--
Limit of the finite boxes along integer R, with no claim of absolute
double-sum convergence. [RW26, p. 29].
[RW26, pp. 28--29].
-/
theorem residueBox_tendsto (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (residueBox (kernel kind M m n h ℓ p x) M m n x.1) atTop
      (𝓝 (vIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (etaDenom M x.1) / (-2 * (Real.pi : ℂ) * Complex.I))) := by
  have hD : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (two_ne_zero' ℂ))
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  apply ((clockwiseBoundary_tendsto kind M h ℓ p m n ψ σ ρ δ hc x hx).div_const
    (-2 * (Real.pi : ℂ) * Complex.I)).congr'
  filter_upwards [eventually_ge_atTop 1] with R hR
  rw [finite_clockwise_residue kind M h ℓ p m n ψ σ ρ δ hc x hx R hR]
  exact mul_div_cancel_left₀ _ hD

set_option maxHeartbeats 800000 in
/--
Full upward tilted line is absolutely integrable, not only its tails. [RW26, pp. 28--29].
-/
theorem line_integrable (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Integrable (linePullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) ψ) := by
  have hp := upper_rotated_ray_integrable kind M h ℓ p m n ψ σ ρ δ hc x hx
  have hn := lower_rotated_ray_integrable kind M h ℓ p m n ψ σ ρ δ hc x hx
  have hrotp : UpperWindow.rotation (Real.pi / 2 + ψ) =
      Complex.I * UpperWindow.rotation ψ := by
    unfold UpperWindow.rotation
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    congr 1
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_div]
  have hrotn : UpperWindow.rotation (-Real.pi / 2 + ψ) =
      -(Complex.I * UpperWindow.rotation ψ) := by
    unfold UpperWindow.rotation
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    have he : Complex.exp (Complex.I * ((-Real.pi / 2 : ℝ) : ℂ)) = -Complex.I := by
      rw [mul_comm, Complex.exp_mul_I]
      simp [Complex.ofReal_div, neg_div]
    rw [he, neg_mul]
  have hright : IntegrableOn (linePullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) ψ) (Ioi 0) := by
    change IntegrableOn (rayPullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (Complex.I * UpperWindow.rotation ψ)) (Ioi 0)
    rw [hrotp] at hp
    exact hp
  have hn0 : IntegrableOn (rayPullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (UpperWindow.rotation (-Real.pi / 2 + ψ)))
      (Ioi (-(0 : ℝ))) := by
    simpa only [neg_zero] using hn
  have hn' : IntegrableOn (fun t : ℝ =>
      rayPullback (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (UpperWindow.rotation (-Real.pi / 2 + ψ)) (-t)) (Iio 0) := by
    exact hn0.comp_neg_Iio
  have hleft : IntegrableOn (linePullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) ψ) (Iic 0) := by
    apply (integrableOn_Iic_iff_integrableOn_Iio (f := _) (b := (0 : ℝ))).mpr
    have hnneg := hn'.neg
    change IntegrableOn (fun t : ℝ =>
      -(kernel kind M m n h ℓ p x (UpperWindow.base M m n δ x.1 +
        ((-t : ℝ) : ℂ) * UpperWindow.rotation (-Real.pi / 2 + ψ)) *
          UpperWindow.rotation (-Real.pi / 2 + ψ))) (Iio 0) at hnneg
    change IntegrableOn (fun t : ℝ => kernel kind M m n h ℓ p x
      (UpperWindow.base M m n δ x.1 + (t : ℂ) * (Complex.I * UpperWindow.rotation ψ)) *
        (Complex.I * UpperWindow.rotation ψ)) (Iio 0)
    simpa only [hrotn, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg] using hnneg
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hleft, hright⟩

/--
Both end rotations assembled with the incoming minus sign. [RW26, pp. 28--29].
-/
theorem lineIntegral_eq_vIntegral (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    lineIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) ψ =
      vIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) (etaDenom M x.1) := by
  have hline := line_integrable kind M h ℓ p m n ψ σ ρ δ hc x hx
  have hrotp : UpperWindow.rotation (Real.pi / 2 + ψ) =
      Complex.I * UpperWindow.rotation ψ := by
    unfold UpperWindow.rotation
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    congr 1
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_div]
  have hrotn : UpperWindow.rotation (-Real.pi / 2 + ψ) =
      -(Complex.I * UpperWindow.rotation ψ) := by
    unfold UpperWindow.rotation
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    have he : Complex.exp (Complex.I * ((-Real.pi / 2 : ℝ) : ℂ)) = -Complex.I := by
      rw [mul_comm, Complex.exp_mul_I]
      simp [Complex.ofReal_div, neg_div]
    rw [he, neg_mul]
  have hleft : (∫ t : ℝ in Iic 0,
      linePullback (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) ψ t) =
      -rayIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (UpperWindow.rotation (-Real.pi / 2 + ψ)) := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    unfold rayIntegral
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [linePullback, rayPullback, hrotn, Complex.ofReal_neg, mul_neg, neg_neg]
    congr 2
    ring
  unfold lineIntegral vIntegral
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hline.integrableOn hline.integrableOn, hleft]
  rw [lower_ray_rotation kind M h ℓ p m n ψ σ ρ δ hc x hx,
    upper_ray_rotation kind M h ℓ p m n ψ σ ρ δ hc x hx]
  simp only [rayIntegral, rayPullback, linePullback, hrotp]

/--
Direct per-m export: tilted integral is the -2πi finite-box limit. [RW26, pp. 28--29].
-/
theorem lineIntegral_eq_box_limit (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => -2 * (Real.pi : ℂ) * Complex.I *
      residueBox (kernel kind M m n h ℓ p x) M m n x.1 R) atTop
      (𝓝 (lineIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) ψ)) := by
  rw [lineIntegral_eq_vIntegral kind M h ℓ p m n ψ σ ρ δ hc x hx]
  apply (clockwiseBoundary_tendsto kind M h ℓ p m n ψ σ ρ δ hc x hx).congr'
  filter_upwards [eventually_ge_atTop 1] with R hR
  exact finite_clockwise_residue kind M h ℓ p m n ψ σ ρ δ hc x hx R hR

/--
Finite residue-class sum. There is exactly the displayed sum
over m, with no extra c factor. [RW26, p. 29].
[RW26, pp. 28--29].
-/
theorem sum_lines_eq_box_limit (kind : Kind) (M : SL(2, ℤ)) (h ℓ p n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => -2 * (Real.pi : ℂ) * Complex.I *
      ∑ m ∈ Finset.range (M 1 0).toNat,
        residueBox (kernel kind M (m : ℤ) n h ℓ p x) M (m : ℤ) n x.1 R) atTop
      (𝓝 (∑ m ∈ Finset.range (M 1 0).toNat,
        lineIntegral (kernel kind M (m : ℤ) n h ℓ p x)
          (UpperWindow.base M (m : ℤ) n δ x.1) ψ)) := by
  simpa only [Finset.mul_sum] using tendsto_finsetSum (Finset.range (M 1 0).toNat)
    (fun m _ => lineIntegral_eq_box_limit kind M h ℓ p (m : ℤ) n ψ σ ρ δ hc x hx)

/--
Actual Φ compared with the raw q quotient only as a punctured germ. [RW26, p. 29].
[RW26, pp. 28--29].
-/
theorem kernel_eq_qKernel_germ (kind : Kind) (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n h ℓ p : ℤ) (x : UpperWindow.Parameters) (hτ : 0 < x.1.im) (z : ℂ) :
    kernel kind M m n h ℓ p x =ᶠ[𝓝[≠] z] qKernel kind M m n h ℓ p x := by
  have hnum := modularPhi_eq_qProduct_germ M hM (m + 1) n z x.1 hτ
  cases kind with
  | single =>
      filter_upwards [hnum] with w hw
      simp only [kernel, qKernel, UpperWindow.singleKernel]
      rw [hw]
  | ratio =>
      have hshift : Tendsto (fun w : ℂ => w + x.2.2)
          (𝓝[≠] z) (𝓝[≠] (z + x.2.2)) := by
        simp only [Tendsto, Filter.map_add_right_nhdsNE, le_refl]
      have hden := hshift.eventually
        (modularPhi_eq_qProduct_germ M hM (m + p) n (z + x.2.2) x.1 hτ)
      filter_upwards [hnum, hden] with w hn hd
      simp only [kernel, qKernel, UpperWindow.ratioKernel]
      rw [hn, hd]

/--
Residues of the q quotient may be calculated without assigning its
common-zero center values to Φ. [RW26, p. 29].
[RW26, pp. 28--29].
-/
theorem residueBox_eq_qKernel (kind : Kind) (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n h ℓ p : ℤ) (x : UpperWindow.Parameters) (hτ : 0 < x.1.im) (R : ℕ) :
    residueBox (kernel kind M m n h ℓ p x) M m n x.1 R =
      residueBox (qKernel kind M m n h ℓ p x) M m n x.1 R := by
  unfold residueBox
  apply Finset.sum_congr rfl
  intro k hk
  exact simpleResidue_germ_congr _ _ _
    (kernel_eq_qKernel_germ kind M hM m n h ℓ p x hτ _)

/--
Every admissible nonnegative pair eventually enters these integer
boxes. This is exhaustion, not an interchange of infinite sums; [RW26, p. 29].
[RW26, pp. 28--29].
-/
theorem boxLabels_exhaust (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (k : ℕ × ℕ) (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    ∀ᶠ R : ℕ in atTop, k ∈ boxLabels M m n R := by
  have hc : 1 ≤ (M 1 0).toNat := by omega
  filter_upwards [eventually_ge_atTop (max k.1 k.2 + 1)] with R hR
  have hRc : R ≤ (M 1 0).toNat * R := by
    simpa only [one_mul] using Nat.mul_le_mul_right R hc
  have h₁ := le_max_left k.1 k.2
  have h₂ := le_max_right k.1 k.2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hk⟩
  · exact Finset.mem_range.mpr (by omega)
  · exact Finset.mem_range.mpr (by omega)

/--
Final per-m identity after its independently justified q summation.
The only new input is the computed finite-box sum limit S. [RW26, pp. 28--29].
-/
theorem lineIntegral_eq_of_residueBox_limit (kind : Kind) (M : SL(2, ℤ))
    (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ)
    (x : UpperWindow.Parameters) (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ)
    (S : ℂ) (hS : Tendsto (residueBox (kernel kind M m n h ℓ p x) M m n x.1) atTop (𝓝 S)) :
    lineIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) ψ =
      -2 * (Real.pi : ℂ) * Complex.I * S := by
  exact tendsto_nhds_unique (lineIntegral_eq_box_limit kind M h ℓ p m n ψ σ ρ δ hc x hx)
    (tendsto_const_nhds.mul hS)

#print qKernel
#check FinitePrincipalParts.rectangle_finite_principal_parts
#check parallelogram_finite_principal_parts
#check finite_clockwise_residue
#check lineIntegral_eq_box_limit
#check sum_lines_eq_box_limit
#check lineIntegral_eq_of_residueBox_limit

end SICLean.L4.UpperContour
