import SICLean.L4.G1ContinuationCircles
import SICLean.L4.G1BilateralGeometry
import SICLean.L4.G1BilateralRatioTailsAux
import SICLean.L4.G1BilateralSingleTailsAux

set_option autoImplicit false

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1ContinuationEndRotationAux

lemma rotation_re (θ : ℝ) : (UpperWindow.rotation θ).re = Real.cos θ := by
  simp [UpperWindow.rotation, Complex.exp_re, Complex.mul_re, Complex.mul_im]

lemma rotation_im (θ : ℝ) : (UpperWindow.rotation θ).im = Real.sin θ := by
  simp [UpperWindow.rotation, Complex.exp_im, Complex.mul_re, Complex.mul_im]

lemma continuous_rotation : Continuous UpperWindow.rotation := by
  unfold UpperWindow.rotation
  fun_prop

lemma rotation_quarter (θ : ℝ) :
    UpperWindow.rotation (Real.pi / 2 + θ) = Complex.I * UpperWindow.rotation θ := by
  apply Complex.ext
  · simp [rotation_re, rotation_im, Real.cos_add]
  · simp [rotation_re, rotation_im, Real.sin_add]

lemma rotation_pi (θ : ℝ) :
    UpperWindow.rotation (θ + Real.pi) = -UpperWindow.rotation θ := by
  apply Complex.ext
  · simp [rotation_re, rotation_im, Real.cos_add]
  · simp [rotation_re, rotation_im, Real.sin_add]

lemma upper_rotated_im (z : ℂ) (θ : ℝ) :
    (z * UpperWindow.rotation θ).im =
      (z * UpperWindow.rotation (θ - Real.pi / 2)).re := by
  simp [Complex.mul_im, Complex.mul_re, rotation_re, rotation_im, Real.cos_sub, Real.sin_sub]
  <;> ring

lemma lower_rotated_im (z : ℂ) (θ : ℝ) :
    (z * UpperWindow.rotation θ).im =
      -(z * UpperWindow.rotation (θ + Real.pi / 2)).re := by
  simp [Complex.mul_im, Complex.mul_re, rotation_re, rotation_im, Real.cos_add, Real.sin_add]
  <;> ring

def components (M : SL(2, ℤ)) : Finset ℤ :=
  Finset.univ.image (fun m : Fin (M 1 0).toNat => (m : ℤ))

lemma component_mem (M : SL(2, ℤ)) (m : Fin (M 1 0).toNat) : (m : ℤ) ∈ components M :=
  Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩

lemma index_left (M : SL(2, ℤ)) (n p : ℤ) (m : Fin (M 1 0).toNat) :
    ((m : ℤ) + 1, n) ∈ G1BilateralGeometry.indexFamily (components M) n p :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(m : ℤ), component_mem M m, rfl⟩)

lemma index_right (M : SL(2, ℤ)) (n p : ℤ) (m : Fin (M 1 0).toNat) :
    ((m : ℤ) + p, n) ∈ G1BilateralGeometry.indexFamily (components M) n p :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(m : ℤ), component_mem M m, rfl⟩)

lemma real_denom (M : SL(2, ℤ)) (τ : ℝ) :
    etaDenom M (τ : ℂ) = (g1T M τ : ℂ) := by
  simp [etaDenom, g1T, Complex.ofReal_intCast]

/-- The compact angle set is shrunk jointly with the parameters. -/
lemma open_uniform_margin {E : Type*} [TopologicalSpace E]
    (F : E → ℝ → ℝ) (u : E) (J : Set ℝ) (hJ : IsCompact J)
    (hc : ∀ θ ∈ J, ContinuousAt (fun q : E × ℝ => F q.1 q.2) (u, θ))
    (hp : ∀ θ ∈ J, 0 < F u θ) :
    ∃ (U : Set E) (κ : ℝ), IsOpen U ∧ u ∈ U ∧ 0 < κ ∧
      ∀ v ∈ U, ∀ θ ∈ J, κ ≤ F v θ := by
  obtain ⟨a, ha, hm⟩ := hJ.exists_forall_le'
    (fun θ hθ => ((hc θ hθ).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt) hp
  have hn : ∀ᶠ v in 𝓝 u, ∀ θ ∈ J, a / 2 < F v θ := by
    apply hJ.eventually_forall_of_forall_eventually
    intro θ hθ
    have hm' : a ≤ F u θ := hm θ hθ
    exact (hc θ hθ).eventually (lt_mem_nhds (by dsimp; linarith))
  obtain ⟨U, hU, hUo, hu⟩ := mem_nhds_iff.mp hn
  exact ⟨U, a / 2, hUo, hu, half_pos ha,
    fun v hv θ hθ => (hU hv θ hθ).le⟩

lemma positive_rotated_coordinates (T : ℂ) (ψ a b θ : ℝ)
    (hTr : 0 < T.re) (hTi : 0 ≤ T.im) (hψ : ψ < Real.pi / 4)
    (ha : 0 < a) (hb : 0 < b) (hθ : θ ∈ Icc 0 ψ) :
    0 < (((a : ℂ) + (b : ℂ) / T) * UpperWindow.rotation θ).re := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [Real.pi_pos, hθ.2])
  have hT : T ≠ 0 := by intro ht; simpa [ht] using hTr
  have hdiv : 0 < (UpperWindow.rotation θ / T).re := by
    rw [Complex.div_re, rotation_re, rotation_im, ← add_div]
    exact div_pos (add_pos_of_pos_of_nonneg (mul_pos hcos hTr)
      (mul_nonneg hsin hTi)) (Complex.normSq_pos.mpr hT)
  have heq : (((a : ℂ) + (b : ℂ) / T) * UpperWindow.rotation θ).re =
      a * Real.cos θ + b * (UpperWindow.rotation θ / T).re := by
    rw [add_mul, show (b : ℂ) / T * UpperWindow.rotation θ =
      (b : ℂ) * (UpperWindow.rotation θ / T) by ring]
    simp [Complex.mul_re, rotation_re]
  rw [heq]
  exact add_pos (mul_pos ha hcos) (mul_pos hb hdiv)

lemma seed_rotated_positive (M : SL(2, ℤ)) (h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) (θ : ℝ)
    (hθ : θ ∈ Icc 0 ψ) :
    0 < (G1RatioTail.complexS M x.1 x.2.1 h ell /
      etaDenom M x.1 * UpperWindow.rotation θ).re ∧
    0 < -(G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p /
      etaDenom M x.1 * UpperWindow.rotation θ).re := by
  obtain ⟨_, hTi, hTr, hT, _⟩ :=
    UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have hi := UpperWindow.coordinate_inequalities M h ell p ψ σ ρ δ hc x hx
  let S := UpperWindow.coords (etaDenom M x.1) (UpperWindow.s M h ell x.1 x.2.1)
  let H := UpperWindow.coords (etaDenom M x.1) (UpperWindow.height M p x.1 x.2.2)
  have hs := UpperWindow.coords_reconstruct (etaDenom M x.1)
    (UpperWindow.s M h ell x.1 x.2.1) hTi.ne'
  have hh := UpperWindow.coords_reconstruct (etaDenom M x.1)
    (UpperWindow.height M p x.1 x.2.2) hTi.ne'
  have hu : G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1 =
      (S.1 : ℂ) + (S.2 : ℂ) / etaDenom M x.1 := by
    change UpperWindow.s M h ell x.1 x.2.1 / etaDenom M x.1 = _
    rw [← hs]
    dsimp [S]
    field_simp
  have hl : -(G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p /
      etaDenom M x.1) =
      ((1 - S.1 - H.1 : ℝ) : ℂ) +
        ((1 - S.2 - H.2 : ℝ) : ℂ) / etaDenom M x.1 := by
    have he : G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p =
        UpperWindow.s M h ell x.1 x.2.1 +
          UpperWindow.height M p x.1 x.2.2 - (etaDenom M x.1 + 1) := by
      unfold G1RatioTail.complexL G1RatioTail.complexS UpperWindow.s UpperWindow.height
      ring
    rw [he, ← hs, ← hh]
    change -(((S.1 : ℂ) * etaDenom M x.1 + (S.2 : ℂ) +
      ((H.1 : ℂ) * etaDenom M x.1 + (H.2 : ℂ)) - (etaDenom M x.1 + 1)) /
      etaDenom M x.1) = _
    push_cast
    field_simp
    <;> ring
  constructor
  · rw [hu]
    exact positive_rotated_coordinates _ ψ S.1 S.2 θ hTr hTi.le hc.2.2.1
      hi.1 hi.2.1 hθ
  · rw [← Complex.neg_re, ← neg_mul, hl]
    exact positive_rotated_coordinates _ ψ _ _ θ hTr hTi.le hc.2.2.1
      (by linarith [hi.2.2.2.2.1]) (by linarith [hi.2.2.2.2.2]) hθ

lemma qPochhammer_small_error (η b : ℝ) (hη : 0 < η) (hb : b < 1) :
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧ ∀ u q : ℂ,
      ‖u‖ ≤ 1 / 4 → η ≤ ‖q‖ → ‖q‖ ≤ b →
      ‖qPochhammer u q‖ ≤ B ∧ ‖(qPochhammer u q)⁻¹‖ ≤ B ∧
      ‖qPochhammer u q - 1‖ ≤ L * ‖u‖ := by
  obtain ⟨B, hB, hbound⟩ := UpperContourUpperArcAux.wedge_q_bound η (3 / 4) b
    hη (by norm_num) hb
  refine ⟨B, 16 * B / 3, hB, by positivity, ?_⟩
  intro u q hu hqη hqb
  have hq : 0 < ‖q‖ ∧ ‖q‖ < 1 := ⟨hη.trans_le hqη, hqb.trans_lt hb⟩
  have ha (v : ℂ) : AnalyticAt ℂ (fun v : ℂ => qPochhammer v q) v :=
    (analyticOnNhd_qPochhammer_joint (v, q) hq).comp (x := v)
      (f := fun v : ℂ => (v, q))
      (analyticAt_id.prod analyticAt_const)
  have hfd (v : ℂ) (hv : v ∈ Metric.closedBall (0 : ℂ) (1 / 4 : ℝ)) :
      ‖fderiv ℂ (fun v : ℂ => qPochhammer v q) v‖ ≤ 16 * B / 3 := by
    have hmem : v ∈ Metric.ball (0 : ℂ) (3 / 8 : ℝ) := by
      simp only [Metric.mem_closedBall, dist_zero_right] at hv
      simpa only [Metric.mem_ball, dist_zero_right] using (show ‖v‖ < 3 / 8 by linarith)
    have h := joint_norm_fderiv_le_of_ball_bound (f := fun v : ℂ => qPochhammer v q)
      (p := 0) (r := 3 / 8) (B := B) (by norm_num) hmem
      (fun v _ => (ha v).differentiableAt.differentiableWithinAt) (by
        intro v hv
        have hv' : ‖v‖ ≤ 3 / 4 := by
          simp only [Metric.mem_ball, dist_zero_right] at hv
          linarith
        exact (hbound v q hv' hqη hqb).1)
    convert h using 1 <;> ring
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (s := Metric.closedBall (0 : ℂ) (1 / 4 : ℝ))
    (f := fun v : ℂ => qPochhammer v q) (C := 16 * B / 3) (x := 0) (y := u)
    (fun v _ => (ha v).differentiableAt) hfd (convex_closedBall (0 : ℂ) (1 / 4 : ℝ))
    (by simp) (by simpa using hu)
  obtain ⟨h₁, h₂⟩ := hbound u q (by linarith) hqη hqb
  exact ⟨h₁, h₂, by simpa only [qPochhammer_zero, sub_zero] using he⟩

lemma phase_zpow (τ z : ℂ) (r : ℤ) : (e τ) ^ r * e z = e ((r : ℂ) * τ + z) := by
  simp only [e]
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  ring

/-- Small original q arguments exclude both actual divisor families. -/
lemma upper_unit_of_arguments (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) (hTi : 0 < (etaDenom M τ).im)
    (hu : ‖(e τ) ^ r * e z‖ < 1)
    (hv : ‖(e (etaMobius M τ)) ^ n * e (z / etaDenom M τ)‖ < 1) :
    (z, τ) ∈ modularPhiNonvanishingDomain M r n := by
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hc0 : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hT : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hτ
  have hns : 0 < Complex.normSq (etaDenom M τ) := Complex.normSq_pos.mpr hT
  have hpos (a : ℂ) (ha : ‖e a‖ < 1) : 0 < a.im := by
    rw [G1BilateralRatioTailsAux.norm_e, Real.exp_lt_one_iff] at ha
    nlinarith [Real.pi_pos]
  have hu' := hpos _ (phase_zpow τ z r ▸ hu)
  have hv' := hpos _ (phase_zpow (etaMobius M τ) (z / etaDenom M τ) n ▸ hv)
  apply UpperWindow.nonvanishingDomain_of_avoids M r n z τ hτ
  · intro K J heq
    have he : (n : ℂ) * etaMobius M τ + modularPhiPolePoint M r n τ K J / etaDenom M τ =
        ((n : ℂ) * (M 0 0 : ℂ) + (K : ℂ) - (r : ℂ) + 1) / (M 1 0 : ℂ) +
          (J : ℂ) / ((M 1 0 : ℂ) * etaDenom M τ) := by
      have hm := UpperWindow.mobius_denominator_relation M τ hT
      have hm' : etaMobius M τ = ((M 0 0 : ℂ) - 1 / etaDenom M τ) /
          (M 1 0 : ℂ) := (eq_div_iff hc0).mpr (by simpa [mul_comm] using hm)
      rw [hm']
      unfold modularPhiPolePoint
      field_simp [hT, hc0]
      <;> ring
    have hi : ((n : ℂ) * etaMobius M τ + modularPhiPolePoint M r n τ K J /
        etaDenom M τ).im ≤ 0 := by
      rw [he]
      simp only [Complex.add_im, Complex.div_im, Complex.add_re, Complex.add_im,
        Complex.sub_im, Complex.sub_re, Complex.mul_re, Complex.mul_im,
        Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.natCast_im,
        Complex.one_im, Complex.one_re, mul_zero, zero_mul, add_zero, zero_add,
        sub_zero, zero_sub, zero_div]
      exact neg_nonpos.mpr (div_nonneg
        (mul_nonneg (Nat.cast_nonneg J) (mul_nonneg hc.le hTi.le)) (Complex.normSq_nonneg _))
    rw [heq] at hv'
    linarith
  · intro K J heq
    have he : (r : ℂ) * τ + modularPhiZeroPoint M r n τ K J =
        ((n : ℂ) - 1 - (r : ℂ) * (M 1 1 : ℂ) - (J : ℂ)) / (M 1 0 : ℂ) -
          (K : ℂ) * etaDenom M τ / (M 1 0 : ℂ) := by
      unfold modularPhiZeroPoint etaDenom
      field_simp
      ring
    have hi : ((r : ℂ) * τ + modularPhiZeroPoint M r n τ K J).im ≤ 0 := by
      rw [he, Complex.sub_im]
      simp only [Complex.div_im, Complex.sub_im, Complex.mul_im, Complex.mul_re,
        Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.natCast_im,
        Complex.one_im, Complex.one_re, mul_zero, zero_mul, zero_sub, sub_zero,
        zero_add, add_zero, zero_div]
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg K) hTi.le) hc.le) (Complex.normSq_nonneg _))
    rw [heq] at hu'
    linarith

/-- A compact family of upward rays, allowing a moving origin and parameter. The two strict
directional inequalities are kept on the whole compact set. -/
lemma upper_ray_estimates {E : Type*} [TopologicalSpace E]
    (M : SL(2, ℤ)) (hM : 0 < M 1 0) (K : Set E) (hK : IsCompact K)
    (τ a d : E → ℂ) (hτc : ContinuousOn τ K) (hac : ContinuousOn a K)
    (hdc : ContinuousOn d K)
    (hτ : ∀ x ∈ K, τ x ∈ modularPhiDomain M ∧ 0 < (τ x).im ∧ 0 < (etaDenom M (τ x)).im)
    (hd : ∀ x ∈ K, 0 < (d x).im ∧ 0 < (d x / etaDenom M (τ x)).im)
    (F : Finset (ℤ × ℤ)) :
    ∃ C k R₀ : ℝ, 0 < C ∧ 0 < k ∧ 0 < R₀ ∧
      ∀ x ∈ K, ∀ i ∈ F, ∀ R ≥ R₀,
        let z := a x + (R : ℂ) * d x
        (z, τ x) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ModularSector.upperError M i z (τ x) ≤ C * Real.exp (-k * R) ∧
        ‖modularPhi M i.1 i.2 z (τ x)‖ ≤ C ∧
        ‖(modularPhi M i.1 i.2 z (τ x))⁻¹‖ ≤ C := by
  have hTc : ContinuousOn (fun x => etaDenom M (τ x)) K :=
    (UpperWindow.CompactAux.continuous_etaDenom M).comp_continuousOn hτc
  have hT (x : E) (hx : x ∈ K) : etaDenom M (τ x) ≠ 0 :=
    etaDenom_ne_zero_of_mem M (hτ x hx).1
  have hηc : ContinuousOn (fun x => etaMobius M (τ x)) K := by
    unfold etaMobius
    exact ((continuousOn_const.mul hτc).add continuousOn_const).div hTc hT
  have hec : Continuous e := UpperWindow.CompactAux.continuous_e
  have hq (x : E) (hx : x ∈ K) :
      0 < ‖e (τ x)‖ ∧ ‖e (τ x)‖ < 1 ∧
      0 < ‖e (etaMobius M (τ x))‖ ∧ ‖e (etaMobius M (τ x))‖ < 1 := by
    have hu := (hτ x hx).2.1
    have hη : 0 < (etaMobius M (τ x)).im := by
      rw [← coe_smul_eq_etaMobius M (⟨τ x, hu⟩ : UpperHalfPlane)]
      exact (M • (⟨τ x, hu⟩ : UpperHalfPlane)).im_pos
    exact ⟨norm_pos_iff.mpr (e_ne_zero _), norm_e_lt_one ⟨τ x, hu⟩,
      norm_pos_iff.mpr (e_ne_zero _), norm_e_lt_one ⟨_, hη⟩⟩
  obtain ⟨η, hη, hηb⟩ := hK.exists_forall_le'
    ((hec.comp_continuousOn hτc).norm.inf (hec.comp_continuousOn hηc).norm)
    (fun x hx => lt_min (hq x hx).1 (hq x hx).2.2.1)
  obtain ⟨b, hb0, hb1, hbb⟩ := UpperWindow.CompactAux.strict_upper_bound hK
    ((hec.comp_continuousOn hτc).norm.sup (hec.comp_continuousOn hηc).norm)
    (fun x hx => max_lt (hq x hx).2.1 (hq x hx).2.2.2)
  obtain ⟨μ, hμ, hμb⟩ := hK.exists_forall_le'
    ((continuous_im.comp_continuousOn hdc).inf
      (continuous_im.comp_continuousOn (hdc.div hTc hT)))
      (fun x hx => lt_min_iff.mpr (hd x hx))
  let k := 2 * Real.pi * μ
  have hk : 0 < k := by dsimp [k]; positivity
  let f : (ℤ × ℤ) → E → ℂ := fun i x =>
    ((e (τ x)) ^ i.1 * e (a x)) +
      Complex.I * ((e (etaMobius M (τ x))) ^ i.2 * e (a x / etaDenom M (τ x)))
  -- Bound the arguments separately, using a finite doubled index family.
  let ff : Bool × (ℤ × ℤ) → E → ℂ := fun j x =>
    if j.1 then (e (τ x)) ^ j.2.1 * e (a x)
    else (e (etaMobius M (τ x))) ^ j.2.2 * e (a x / etaDenom M (τ x))
  obtain ⟨B, hB, hBb⟩ := G1BilateralRatioTailsAux.finite_compact_bound
    (Finset.univ.product F) K hK ff (by
      rintro ⟨b, i⟩ hi
      cases b <;> dsimp only [ff] <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact ((hec.comp_continuousOn hηc).zpow₀ _ (fun x _ => Or.inl (e_ne_zero _))).mul
          (hec.comp_continuousOn (hac.div hTc hT))
      · exact ((hec.comp_continuousOn hτc).zpow₀ _ (fun x _ => Or.inl (e_ne_zero _))).mul
          (hec.comp_continuousOn hac))
  have hargs (x : E) (hx : x ∈ K) (i : ℤ × ℤ) (hi : i ∈ F)
      (R : ℝ) (hR : 0 ≤ R) :
      ‖(e (τ x)) ^ i.1 * e (a x + (R : ℂ) * d x)‖ ≤ B * Real.exp (-k * R) ∧
      ‖(e (etaMobius M (τ x))) ^ i.2 *
        e ((a x + (R : ℂ) * d x) / etaDenom M (τ x))‖ ≤ B * Real.exp (-k * R) := by
    have hu := (le_min_iff.mp (hμb x hx)).1
    have hv := (le_min_iff.mp (hμb x hx)).2
    have hcalc (U v : ℂ) (hU : ‖U‖ ≤ B) (hv : μ ≤ v.im) :
        ‖U * e ((R : ℂ) * v)‖ ≤ B * Real.exp (-k * R) := by
      rw [norm_mul, G1BilateralRatioTailsAux.norm_e]
      have hexp : -2 * Real.pi * ((R : ℂ) * v).im ≤ -k * R := by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        dsimp [k]
        nlinarith [mul_le_mul_of_nonneg_right hv hR, Real.pi_pos]
      exact mul_le_mul hU (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le hB.le
    constructor
    · rw [G1BilateralRatioTailsAux.e_add, ← mul_assoc]
      exact hcalc _ _ (hBb (true, i) (by simp [hi]) x hx) hu
    · rw [add_div, mul_div_assoc, G1BilateralRatioTailsAux.e_add, ← mul_assoc]
      exact hcalc _ _ (hBb (false, i) (by simp [hi]) x hx) hv
  have hexp : Tendsto (fun R : ℝ => B * Real.exp (-k * R)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 k hk).const_mul B
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (hexp.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  obtain ⟨D, L, hD, hL, hqerr⟩ := qPochhammer_small_error η b hη hb1
  let C := max (4 * L * B * D) (D * D)
  refine ⟨C, k, max 1 R₁, lt_of_lt_of_le (by positivity : 0 < D * D)
    (le_max_right _ _), hk, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx i hi R hR
  have hR0 : 0 ≤ R := (show (0 : ℝ) ≤ max 1 R₁ by positivity).trans hR
  let z := a x + (R : ℂ) * d x
  let u := (e (τ x)) ^ i.1 * e z
  let v := (e (etaMobius M (τ x))) ^ i.2 * e (z / etaDenom M (τ x))
  have harg := hargs x hx i hi R hR0
  have hsmall : B * Real.exp (-k * R) < 1 / 4 :=
    hR₁ R ((le_max_right _ _).trans hR)
  have hu : ‖u‖ < 1 := lt_of_le_of_lt harg.1 (by linarith)
  have hv : ‖v‖ < 1 := lt_of_le_of_lt harg.2 (by linarith)
  obtain ⟨hqη, hQη⟩ := le_min_iff.mp (hηb x hx)
  obtain ⟨hqb, hQb⟩ := max_le_iff.mp (hbb x hx)
  obtain ⟨hp, hpi, hpe⟩ := hqerr u (e (τ x)) (harg.1.trans hsmall.le) hqη hqb
  obtain ⟨hq', hqi, hqe⟩ := hqerr v (e (etaMobius M (τ x)))
    (harg.2.trans hsmall.le) hQη hQb
  have hpn : qPochhammer u (e (τ x)) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one _ _ hu (hq x hx).1 (hq x hx).2.1
  have hqn : qPochhammer v (e (etaMobius M (τ x))) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one _ _ hv (hq x hx).2.2.1 (hq x hx).2.2.2
  have hphi : modularPhi M i.1 i.2 z (τ x) =
      qPochhammer u (e (τ x)) / qPochhammer v (e (etaMobius M (τ x))) := by
    exact modularPhi_eq_qProduct M hM i.1 i.2 z (τ x) (hτ x hx).2.1 hqn
  have herr (P Q : ℂ) (hQ : Q ≠ 0) (hQi : ‖Q⁻¹‖ ≤ D)
      (hP : ‖P - 1‖ ≤ L * ‖u‖) (hQ' : ‖Q - 1‖ ≤ L * ‖v‖) :
      ‖P / Q - 1‖ ≤ (2 * L * B * D) * Real.exp (-k * R) := by
    rw [div_sub_one hQ, norm_div, div_eq_mul_inv, ← norm_inv]
    have hsub : ‖P - Q‖ ≤ 2 * L * B * Real.exp (-k * R) := by
      calc
        ‖P - Q‖ ≤ ‖P - 1‖ + ‖Q - 1‖ := by
          simpa only [norm_sub_rev (1 : ℂ) Q] using norm_sub_le_norm_sub_add_norm_sub P 1 Q
        _ ≤ L * ‖u‖ + L * ‖v‖ := add_le_add hP hQ'
        _ ≤ L * (B * Real.exp (-k * R)) + L * (B * Real.exp (-k * R)) := by
          gcongr
          · exact harg.1
          · exact harg.2
        _ = _ := by ring
    exact (mul_le_mul hsub hQi (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have he₁ := herr _ _ hqn hqi hpe hqe
  have he₂ : ‖(qPochhammer u (e (τ x)) /
      qPochhammer v (e (etaMobius M (τ x))))⁻¹ - 1‖ ≤
      (2 * L * B * D) * Real.exp (-k * R) := by
    rw [inv_div]
    rw [div_sub_one hpn, norm_div, div_eq_mul_inv, ← norm_inv]
    have hs : ‖qPochhammer v (e (etaMobius M (τ x))) - qPochhammer u (e (τ x))‖ =
        ‖qPochhammer u (e (τ x)) - qPochhammer v (e (etaMobius M (τ x)))‖ := norm_sub_rev _ _
    rw [hs]
    have hh : ‖qPochhammer u (e (τ x)) - qPochhammer v (e (etaMobius M (τ x)))‖ ≤
        2 * L * B * Real.exp (-k * R) := by
      calc
        _ ≤ ‖qPochhammer u (e (τ x)) - 1‖ +
            ‖qPochhammer v (e (etaMobius M (τ x))) - 1‖ := by
          simpa only [norm_sub_rev (1 : ℂ) (qPochhammer v (e (etaMobius M (τ x))))] using
            norm_sub_le_norm_sub_add_norm_sub (qPochhammer u (e (τ x))) 1
              (qPochhammer v (e (etaMobius M (τ x))))
        _ ≤ L * ‖u‖ + L * ‖v‖ := add_le_add hpe hqe
        _ ≤ L * (B * Real.exp (-k * R)) + L * (B * Real.exp (-k * R)) := by
          gcongr
          · exact harg.1
          · exact harg.2
        _ = _ := by ring
    exact (mul_le_mul hh hpi (norm_nonneg _) (by positivity)).trans_eq (by ring)
  refine ⟨upper_unit_of_arguments M hM i.1 i.2 z (τ x) (hτ x hx).1
      (hτ x hx).2.2 hu hv, ?_, ?_, ?_⟩
  · unfold ModularSector.upperError
    rw [hphi]
    calc
      _ ≤ (4 * L * B * D) * Real.exp (-k * R) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · rw [hphi, div_eq_mul_inv, norm_mul]
    exact (mul_le_mul hp hqi (norm_nonneg _) hD.le).trans (le_max_right _ _)
  · rw [hphi, inv_div, div_eq_mul_inv, norm_mul]
    exact (mul_le_mul hq' hpi (norm_nonneg _) hD.le).trans (le_max_right _ _)

lemma upper_arc_estimates (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (ψ A : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (K : Set ℂ) (hK : IsCompact K) (hτ : K ⊆ UpperWindow.tauRegion M ψ)
    (F : Finset (ℤ × ℤ)) :
    ∃ C k R₀ : ℝ, 0 < C ∧ 0 < k ∧ 0 < R₀ ∧
      ∀ τ ∈ K, ∀ i ∈ F, ∀ a ∈ Metric.closedBall (0 : ℂ) A, ∀ R ≥ R₀,
        ∀ θ ∈ Icc (Real.pi / 2) (Real.pi / 2 + ψ),
        let z := a + (R : ℂ) * UpperWindow.rotation θ
        (z, τ) ∈ modularPhiNonvanishingDomain M i.1 i.2 ∧
        ModularSector.upperError M i z τ ≤ C * Real.exp (-k * R) ∧
        ‖modularPhi M i.1 i.2 z τ‖ ≤ C ∧ ‖(modularPhi M i.1 i.2 z τ)⁻¹‖ ≤ C := by
  let P : Set (ℂ × ℂ × ℝ) := K ×ˢ Metric.closedBall (0 : ℂ) A ×ˢ
    Icc (Real.pi / 2) (Real.pi / 2 + ψ)
  have hP : IsCompact P := hK.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  obtain ⟨C, k, R₀, hC, hk, hR₀, hb⟩ := upper_ray_estimates M hM P hP
    (fun q => q.1) (fun q => q.2.1) (fun q => UpperWindow.rotation q.2.2)
    continuous_fst.continuousOn (continuous_fst.comp continuous_snd).continuousOn
    (continuous_rotation.comp (continuous_snd.comp continuous_snd)).continuousOn
    (by
      intro q hq
      have ht := UpperWindow.tauRegion_properties M hM ψ hψ' q.1 (hτ hq.1)
      exact ⟨ht.1, (hτ hq.1).1, ht.2.1⟩)
    (by
      intro q hq
      have harg := (hτ hq.1).2
      have hT := (UpperWindow.tauRegion_properties M hM ψ hψ' q.1 (hτ hq.1)).2.2.2.1
      constructor
      · rw [rotation_im]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hq.2.2.1])
          (by linarith [Real.pi_pos, hq.2.2.2])
      · rw [UpperContourLowerArcAux.rotation_div_im _ _ hT]
        exact div_pos (Real.sin_pos_of_pos_of_lt_pi
          (by linarith [Real.pi_pos, hq.2.2.1])
          (by linarith [Real.pi_pos, hq.2.2.2])) (norm_pos_iff.mpr hT)) F
  exact ⟨C, k, R₀, hC, hk, hR₀,
    fun τ hτ i hi a ha R hR θ hθ => hb (τ, a, θ) ⟨hτ, ha, hθ⟩ i hi R hR⟩

lemma reflected_unit (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ)
    (hz : (-z, τ) ∈ modularPhiNonvanishingDomain M (1 - r) (1 - n)) :
    (z, τ) ∈ modularPhiNonvanishingDomain M r n := by
  have hm := ModularSector.divisor_multiplicity_reflection M r n z τ
  exact ⟨hz.1, hm.1.trans hz.2.2, hm.2.trans hz.2.1⟩

lemma point_reflection (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ) (z τ : ℂ)
    (hz : (z, τ) ∈ modularPhiNonvanishingDomain M r n)
    (hmz : (-z, τ) ∈ modularPhiNonvanishingDomain M (1 - r) (1 - n)) :
    modularPhi M r n z τ = modularReflectionFactor M r n z τ /
      modularPhi M (1 - r) (1 - n) (-z) τ := by
  apply UpperContourLowerArcAux.modularPhi_reflection_div M hM r n z τ hz.1
  · exact ((modularPhi_joint_analytic_no_poles M hM r n (z, τ) ⟨hz.1, hz.2.1⟩).comp
      (f := fun z : ℂ => (z, τ)) (analyticAt_id.prod analyticAt_const)).continuousAt
  · exact ((modularPhi_joint_analytic_no_poles M hM (1 - r) (1 - n) (-z, τ)
      ⟨hmz.1, hmz.2.1⟩).comp (f := fun z : ℂ => (-z, τ))
        (analyticAt_id.neg.prod analyticAt_const)).continuousAt

lemma lower_ratio_normalized (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n h ell p m : ℤ)
    (τ w y z : ℂ)
    (hz : (-z, τ) ∈ modularPhiNonvanishingDomain M (1 - (m + 1)) (1 - n))
    (hzy : (-(z + y), τ) ∈ modularPhiNonvanishingDomain M (1 - (m + p)) (1 - n)) :
    UpperWindow.ratioKernel M m n h ell p τ w y z /
      (modularReflectionFactor M (m + 1) n z τ /
        modularReflectionFactor M (m + p) n (z + y) τ *
          e (g1Exponent M τ w z n h ell m)) =
      modularPhi M (1 - (m + p)) (1 - n) (-(z + y)) τ /
        modularPhi M (1 - (m + 1)) (1 - n) (-z) τ := by
  have ha := point_reflection M hM (m + 1) n z τ (reflected_unit M _ _ _ _ hz) hz
  have hb := point_reflection M hM (m + p) n (z + y) τ (reflected_unit M _ _ _ _ hzy) hzy
  have hA := (ModularSector.reflectionFactor_joint_unit M hM (m + 1) n z τ hz.1).2
  have hB := (ModularSector.reflectionFactor_joint_unit M hM (m + p) n (z + y) τ hz.1).2
  have ha0 := (modularPhi_ne_zero_iff M hM _ _ _ _ hz.1 hz.2.1).mpr hz.2.2
  have hb0 := (modularPhi_ne_zero_iff M hM _ _ _ _ hzy.1 hzy.2.1).mpr hzy.2.2
  unfold UpperWindow.ratioKernel UpperWindow.phase
  change (modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ) *
    e (g1Exponent M τ w z n h ell m) / _ = _
  rw [ha, hb]
  field_simp [hA, hB, ha0, hb0, e_ne_zero]

lemma lower_factor_affine (M : SL(2, ℤ)) (hM : 0 < M 1 0) (n h ell p m : ℤ)
    (τ w y z : ℂ) (hT : etaDenom M τ ≠ 0) :
    modularReflectionFactor M (m + 1) n z τ /
        modularReflectionFactor M (m + p) n (z + y) τ *
          e (g1Exponent M τ w z n h ell m) =
      ((-1 : ℂ) ^ (1 - p) * e (modularReflectionPolynomial M (m + 1) n 0 τ -
        modularReflectionPolynomial M (m + p) n y τ + g1Exponent M τ w 0 n h ell m)) *
          e (G1RatioTail.complexL M τ w y h ell p / etaDenom M τ * z) := by
  rw [UpperContourLowerArcAux.reflection_factor_ratio M hM m p n z y τ]
  have hphase := G1BilateralRatioTailsAux.lower_phase_affine M τ w y z n h ell p m hT
  have heq : g1Exponent M τ w z n h ell m + modularReflectionPolynomial M (m + 1) n z τ -
      modularReflectionPolynomial M (m + p) n (z + y) τ =
      (modularReflectionPolynomial M (m + 1) n 0 τ -
        modularReflectionPolynomial M (m + p) n y τ + g1Exponent M τ w 0 n h ell m) +
        G1RatioTail.complexL M τ w y h ell p / etaDenom M τ * z := by
    linear_combination hphase
  rw [heq, G1BilateralRatioTailsAux.e_add]
  ring

def lowerLinearAt (M : SL(2, ℤ)) (τ w z₀ : ℂ) (ψ : ℝ) (n h ell m : ℤ) : ℂ :=
  (-((M 1 0 : ℂ) * z₀ / etaDenom M τ) - (m : ℂ) - 1 / 2 +
    (2 * (n : ℂ) - 1) / (2 * etaDenom M τ) +
    G1RatioTail.complexS M τ w h ell / etaDenom M τ) * g1LowerDirection ψ

def lowerConstantAt (M : SL(2, ℤ)) (τ w z₀ : ℂ) (n h ell m : ℤ) : ℂ :=
  modularReflectionPolynomial M (m + 1) n z₀ τ + g1Exponent M τ w z₀ n h ell m

lemma single_phase_quad (M : SL(2, ℤ)) (τ w z₀ : ℂ) (ψ R : ℝ) (n h ell m : ℤ)
    (hT : etaDenom M τ ≠ 0) :
    modularReflectionPolynomial M (m + 1) n (z₀ + (R : ℂ) * g1LowerDirection ψ) τ +
      g1Exponent M τ w (z₀ + (R : ℂ) * g1LowerDirection ψ) n h ell m =
      (-((M 1 0 : ℂ) / (2 * etaDenom M τ)) * g1LowerDirection ψ ^ 2) * (R : ℂ) ^ 2 +
        lowerLinearAt M τ w z₀ ψ n h ell m * (R : ℂ) + lowerConstantAt M τ w z₀ n h ell m := by
  unfold lowerLinearAt lowerConstantAt modularReflectionPolynomial g1Exponent G1RatioTail.complexS
  push_cast
  field_simp
  <;> ring

lemma reflected_lower_direction (ψ : ℝ) :
    -g1LowerDirection ψ = UpperWindow.rotation (Real.pi / 2 + ψ) := by
  change -UpperWindow.rotation (-Real.pi / 2 + ψ) = _
  rw [show Real.pi / 2 + ψ = (-Real.pi / 2 + ψ) + Real.pi by ring, rotation_pi]

/-- The seed separates in both Cartesian coordinates, not just along the tilt. -/
lemma seed_pole_quadrants (M : SL(2, ℤ)) (h ell p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) (K J : ℕ) :
    let v := UpperWindow.base M m n δ x.1
    v.re < (modularPhiPolePoint M (m + 1) n x.1 K J).re ∧
    v.im < (modularPhiPolePoint M (m + 1) n x.1 K J).im ∧
    (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2).re < v.re ∧
    (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2).im < v.im := by
  have ht := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have hs := UpperWindow.pole_coordinate_signs M h ell p m n ψ σ ρ δ hc x hx K J
  dsimp only at hs
  have hp := UpperWindow.coords_reconstruct (etaDenom M x.1)
    (modularPhiPolePoint M (m + 1) n x.1 K J - UpperWindow.base M m n δ x.1) ht.2.1.ne'
  have hz := UpperWindow.coords_reconstruct (etaDenom M x.1)
    (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2 -
      UpperWindow.base M m n δ x.1) ht.2.1.ne'
  have hpr := congrArg Complex.re hp
  have hpi := congrArg Complex.im hp
  have hzr := congrArg Complex.re hz
  have hzi := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, Complex.sub_re] at hpr hzr
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.sub_im, Complex.ofReal_im] at hpi hzi
  dsimp only
  simp only [Complex.sub_re, Complex.sub_im]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_pos hs.1 ht.2.2.1, hs.2.1]
  · nlinarith [mul_pos hs.1 ht.2.1]
  · nlinarith [mul_neg_of_neg_of_pos hs.2.2.1 ht.2.2.1, hs.2.2.2]
  · nlinarith [mul_neg_of_neg_of_pos hs.2.2.1 ht.2.1]

def seedCrossing (v : ℂ) (ψ : ℝ) : ℝ :=
  v.re - max 0 (-v.im - 1) * Real.tan ψ

lemma bentClear_of_quadrant (M : SL(2, ℤ)) (τ v : ℂ) (n m : ℤ) (ψ : ℝ)
    (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (hp : ∀ K J : ℕ, v.re < (modularPhiPolePoint M (m + 1) n τ K J).re ∧
      v.im < (modularPhiPolePoint M (m + 1) n τ K J).im) :
    G1Continuation.BentClear M τ n m (seedCrossing v ψ) ψ := by
  have htan : 0 ≤ Real.tan ψ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hψ.le
    (by linarith [Real.pi_pos])
  rintro ⟨K, J⟩ hk
  dsimp only
  obtain ⟨hr, hi⟩ := hp K J
  by_cases hz : -((modularPhiPolePoint M (m + 1) n τ K J).im) - 1 ≤ 0
  · rw [max_eq_left hz]
    dsimp [seedCrossing]
    nlinarith [mul_nonneg (le_max_left (0 : ℝ) (-v.im - 1)) htan]
  · have hv : 0 ≤ -v.im - 1 := by linarith
    rw [max_eq_right (le_of_not_ge hz)]
    dsimp [seedCrossing]
    rw [max_eq_right hv]
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.le) htan]

def seedChain (v : ℂ) : G1Continuation.CircleExtension :=
  G1Continuation.ofChain ⟨v.re, ∅, fun _ => 0⟩

lemma seedChain_separates (M : SL(2, ℤ)) (h ell p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) :
    G1Continuation.SeparatesExtension (seedChain (UpperWindow.base M m n δ x.1))
      M x.1 x.2.2 n p m := by
  refine ⟨by simp [seedChain, G1Continuation.ofChain], by simp [seedChain, G1Continuation.ofChain], ?_⟩
  rintro ⟨b, K, J⟩ hb
  have hq := seed_pole_quadrants M h ell p m n ψ σ ρ δ hc x hx K J
  cases b
  · have hl : (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2).re <
        (UpperWindow.base M m n δ x.1).re := hq.2.2.1
    simp only [Complex.sub_re] at hl
    simp [seedChain, G1Continuation.ofChain, G1Continuation.extensionAvoids,
      G1Continuation.extensionAssignment, G1FixedSeparation.leftAssignmentAt,
      G1FixedSeparation.circleWindingAt, ModularCluster.branchPoint, G1Pinch.ratioData, ne_of_lt hl, hl]
  · have hr : (UpperWindow.base M m n δ x.1).re <
        (modularPhiPolePoint M (m + 1) n x.1 K J).re := hq.1
    simp [seedChain, G1Continuation.ofChain, G1Continuation.extensionAvoids,
      G1Continuation.extensionAssignment, G1FixedSeparation.leftAssignmentAt,
      G1FixedSeparation.circleWindingAt, ModularCluster.branchPoint, G1Pinch.ratioData, ne_of_gt hr, not_lt_of_ge hr.le]

end SICLean.L4.G1ContinuationEndRotationAux
