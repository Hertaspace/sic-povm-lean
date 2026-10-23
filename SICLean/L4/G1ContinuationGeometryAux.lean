import Mathlib
import SICLean.L4.UpperIntegralIdentities
import SICLean.L4.G1ChainTransfer

set_option autoImplicit false

/-!
# Auxiliary geometry for the strict G1 continuation windows

The Baire argument chooses one intermediate vertex whose two real lines avoid every member of the
countable family of forbidden complex values. It gives literal straight segments, rather than only a
continuous path. The other helpers give explicit collision arithmetic, initial coordinate
inequalities, and openness after deleting locally finite closed graphs.
-/

noncomputable section
open Complex Set Filter
open scoped MatrixGroups Topology

namespace SICLean.L4.G1ContinuationGeometryAux

theorem complex_line_avoids_of_im_div_ne_zero {x m a : ℂ}
    (hx : x ≠ a) (hm : ((m - x) / (a - x)).im ≠ 0) (t : ℝ) :
    (1 - (t : ℂ)) * x + (t : ℂ) * m ≠ a := by
  intro h
  have ha : a - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have he : (t : ℂ) * ((m - x) / (a - x)) = 1 := by
    apply mul_right_cancel₀ ha
    rw [mul_assoc, div_mul_cancel₀ _ ha, one_mul]
    linear_combination h
  have hi := congrArg Complex.im he
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.one_im] at hi
  have ht : t = 0 := (mul_eq_zero.mp hi).resolve_right hm
  exact hx (by simpa [ht] using h)

theorem isOpen_complex_nonlinear_set (x a : ℂ) :
    IsOpen {v : ℂ × ℂ | ((v.2 - x) / (a - x)).im ≠ 0} := by
  exact isOpen_ne.preimage (Complex.continuous_im.comp
    ((continuous_snd.sub continuous_const).div_const _))

theorem dense_complex_nonlinear_set (x a : ℂ) (ha : x ≠ a) :
    Dense {v : ℂ × ℂ | ((v.2 - x) / (a - x)).im ≠ 0} := by
  have hmul : IsOpenMap (fun z : ℂ => z * (a - x)⁻¹) :=
    (Homeomorph.mulRight₀ ((a - x)⁻¹)
      (inv_ne_zero (sub_ne_zero.mpr (Ne.symm ha)))).isOpenMap
  have hsub : IsOpenMap (fun z : ℂ => z - x) := (Homeomorph.subRight x).isOpenMap
  have ho : IsOpenMap (fun v : ℂ × ℂ => ((v.2 - x) / (a - x)).im) := by
    simpa only [Function.comp_def, div_eq_mul_inv] using
      Complex.isOpenMap_im.comp (hmul.comp (hsub.comp isOpenMap_snd))
  exact (dense_compl_singleton (0 : ℝ)).preimage ho

theorem exists_two_segment_avoiding_countable
    {ι : Type*} [Countable ι] (a : ι → ℂ)
    {U : Set (ℂ × ℂ)} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {x y : ℂ × ℂ} (hxU : x ∈ U) (hyU : y ∈ U)
    (hx : ∀ i, x.2 ≠ a i) (hy : ∀ i, y.2 ≠ a i) :
    ∃ m : ℂ × ℂ, m ∈ U ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (1 - (t : ℂ)) • x + (t : ℂ) • m ∈ U ∧
        ∀ i, ((1 - (t : ℂ)) • x + (t : ℂ) • m).2 ≠ a i) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (1 - (t : ℂ)) • m + (t : ℂ) • y ∈ U ∧
        ∀ i, ((1 - (t : ℂ)) • m + (t : ℂ) • y).2 ≠ a i) := by
  let F : ι → Set (ℂ × ℂ) := fun i =>
    {v | ((v.2 - x.2) / (a i - x.2)).im ≠ 0} ∩
    {v | ((v.2 - y.2) / (a i - y.2)).im ≠ 0}
  have hFo : ∀ i, IsOpen (F i) := fun i =>
    (isOpen_complex_nonlinear_set x.2 (a i)).inter
      (isOpen_complex_nonlinear_set y.2 (a i))
  have hFd : ∀ i, Dense (F i) := fun i =>
    (dense_complex_nonlinear_set x.2 (a i) (hx i)).inter_of_isOpen_right
      (dense_complex_nonlinear_set y.2 (a i) (hy i))
      (isOpen_complex_nonlinear_set y.2 (a i))
  obtain ⟨m, hmU, hmF⟩ :=
    (dense_iInter_of_isOpen hFo hFd).inter_open_nonempty U hUo ⟨x, hxU⟩
  have hm (i : ι) := (mem_iInter.mp hmF i : m ∈ F i)
  refine ⟨m, hmU, ?_, ?_⟩
  · intro t ht
    constructor
    · have hc := hUc hxU hmU (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
      change (((1 - t : ℝ) : ℂ) • x + (t : ℂ) • m) ∈ U at hc
      simpa only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one] using hc
    · intro i
      exact complex_line_avoids_of_im_div_ne_zero (hx i) (hm i).1 t
  · intro t ht
    constructor
    · have hc := hUc hmU hyU (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
      change (((1 - t : ℝ) : ℂ) • m + (t : ℂ) • y) ∈ U at hc
      simpa only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one] using hc
    · intro i
      have hav := complex_line_avoids_of_im_div_ne_zero (hy i) (hm i).2 (1 - t)
      convert hav using 1
      simp [sub_sub_cancel, mul_comm, add_comm]

lemma crossSeparated_iff_no_collision (M : SL(2, ℤ)) (τ w y : ℂ)
    (n h ell p m : ℤ) :
    ModularCluster.crossSeparated M (G1Pinch.ratioData w y n h ell p m) τ ↔
      ∀ K J K' J' : ℕ,
        (K, J) ∈ modularPhiPoleLabels M (m + 1) n →
        (K', J') ∈ modularPhiZeroLabels M (m + p) n →
        modularPhiPolePoint M (m + 1) n τ K J ≠
          modularPhiZeroPoint M (m + p) n τ K' J' - y := by
  constructor
  · intro hs K J K' J' hP hZ heq
    have hclasses := hs (true, K, J)
      (by simpa [ModularCluster.labels, G1Pinch.ratioData] using hP) (false, K', J')
      (by simpa [ModularCluster.labels, G1Pinch.ratioData] using hZ)
      (by simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using heq)
    cases hclasses
  · intro hn b hb b' hb' heq
    rcases b with ⟨bt, K, J⟩
    rcases b' with ⟨bt', K', J'⟩
    cases bt <;> cases bt'
    · rfl
    · exfalso
      apply hn K' J' K J
      · simpa [ModularCluster.labels, G1Pinch.ratioData] using hb'
      · simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
      · simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using heq.symm
    · exfalso
      apply hn K J K' J'
      · simpa [ModularCluster.labels, G1Pinch.ratioData] using hb
      · simpa [ModularCluster.labels, G1Pinch.ratioData] using hb'
      · simpa [ModularCluster.branchPoint, G1Pinch.ratioData] using heq
    · rfl

lemma collision_iff (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ y : ℂ) (n p m : ℤ) (K J K' J' : ℕ) :
    modularPhiPolePoint M (m + 1) n τ K J =
        modularPhiZeroPoint M (m + p) n τ K' J' - y ↔
      y = -(((p : ℂ) + ((K + K' : ℕ) : ℂ)) * etaDenom M τ +
        1 + ((J + J' : ℕ) : ℂ)) / (M 1 0 : ℂ) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  unfold modularPhiPolePoint modularPhiZeroPoint
  push_cast
  constructor <;> intro heq <;> field_simp [hc] at heq ⊢ <;>
    linear_combination heq

lemma sum_label (M : SL(2, ℤ)) (n p m : ℤ) (K J K' J' : ℕ)
    (hP : (K, J) ∈ modularPhiPoleLabels M (m + 1) n)
    (hZ : (K', J') ∈ modularPhiZeroLabels M (m + p) n) :
    Int.ModEq (M 1 0) (((J + J' : ℕ) : ℤ) + M 1 1 * ((K + K' : ℕ) : ℤ))
      (-1 - M 1 1 * p) := by
  change Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ))
    (M 1 1 * (m + 1 - 1) - n) at hP
  change Int.ModEq (M 1 0) ((J' : ℤ) + M 1 1 * (K' : ℤ))
    (n - 1 - M 1 1 * (m + p)) at hZ
  push_cast
  convert hP.add hZ using 1 <;> ring


lemma div_re_coords (T z : ℂ) (hT : T.im ≠ 0) :
    (z / T).re = (UpperWindow.coords T z).1 +
      (UpperWindow.coords T z).2 * T⁻¹.re := by
  have hne : T ≠ 0 := by
    intro heq
    exact hT (by simp [heq])
  calc
    (z / T).re =
        (((UpperWindow.coords T z).1 * T + ((UpperWindow.coords T z).2 : ℂ)) / T).re := by
      rw [UpperWindow.coords_reconstruct T z hT]
    _ = (((UpperWindow.coords T z).1 : ℂ) +
        ((UpperWindow.coords T z).2 : ℂ) * T⁻¹).re := by
      congr 1
      field_simp [hne]
    _ = _ := by simp

lemma seed_strict (M : SL(2, ℤ)) (h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ)
    (x : UpperWindow.Parameters) (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) :
    (0 < (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1).re ∧
      (G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p / etaDenom M x.1).re < 0) := by
  have ht := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have him : (etaDenom M x.1).im ≠ 0 := ht.2.1.ne'
  have hinv : 0 < (etaDenom M x.1)⁻¹.re := by
    rw [Complex.inv_re]
    exact div_pos ht.2.2.1 (Complex.normSq_pos.mpr ht.2.2.2.1)
  have hi := UpperWindow.coordinate_inequalities M h ell p ψ σ ρ δ hc x hx
  let S := UpperWindow.coords (etaDenom M x.1) (UpperWindow.s M h ell x.1 x.2.1)
  let H := UpperWindow.coords (etaDenom M x.1) (UpperWindow.height M p x.1 x.2.2)
  have hS : UpperWindow.s M h ell x.1 x.2.1 =
      (S.1 : ℂ) * etaDenom M x.1 + (S.2 : ℂ) :=
    (UpperWindow.coords_reconstruct _ _ him).symm
  have hH : UpperWindow.height M p x.1 x.2.2 =
      (H.1 : ℂ) * etaDenom M x.1 + (H.2 : ℂ) :=
    (UpperWindow.coords_reconstruct _ _ him).symm
  have hnum : G1RatioTail.complexL M x.1 x.2.1 x.2.2 h ell p =
      ((S.1 + H.1 - 1 : ℝ) : ℂ) * etaDenom M x.1 +
        ((S.2 + H.2 - 1 : ℝ) : ℂ) := by
    calc
      _ = UpperWindow.s M h ell x.1 x.2.1 + UpperWindow.height M p x.1 x.2.2 -
          (etaDenom M x.1 + 1) := by
        unfold G1RatioTail.complexL G1RatioTail.complexS UpperWindow.s UpperWindow.height
        ring
      _ = _ := by rw [hS, hH]; push_cast; ring
  change 0 < (G1RatioTail.complexS M x.1 x.2.1 h ell / etaDenom M x.1).re ∧ _
  constructor
  · change 0 < (UpperWindow.s M h ell x.1 x.2.1 / etaDenom M x.1).re
    rw [div_re_coords _ _ him]
    exact add_pos hi.1 (mul_pos hi.2.1 hinv)
  · rw [hnum]
    have hdiv :
        (((((S.1 + H.1 - 1 : ℝ) : ℂ) * etaDenom M x.1 +
          ((S.2 + H.2 - 1 : ℝ) : ℂ)) / etaDenom M x.1)).re =
        S.1 + H.1 - 1 + (S.2 + H.2 - 1) * (etaDenom M x.1)⁻¹.re := by
      rw [div_re_coords _ _ him, UpperWindow.coords_real_combination _ him]
    rw [hdiv]
    exact add_neg (by linarith [hi.2.2.2.2.1])
      (mul_neg_of_neg_of_pos (by linarith [hi.2.2.2.2.2]) hinv)

theorem isOpen_delete_of_compact_finite {X ι : Type*} [MetricSpace X] [ProperSpace X]
    (D : Set X) (hD : IsOpen D) (A : ι → Set X) (hA : ∀ i, IsClosed (A i))
    (hfin : ∀ K : Set X, IsCompact K → K ⊆ D →
      {i | ∃ x ∈ K, x ∈ A i}.Finite) :
    IsOpen {x | x ∈ D ∧ ∀ i, x ∉ A i} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨r, hr, hrD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx.1)
  let K : Set X := Metric.closedBall x (r / 2)
  have hKD : K ⊆ D := by
    intro y hy
    apply hrD
    exact (Metric.mem_closedBall.mp hy).trans_lt (by linarith)
  let F : Set ι := {i | ∃ y ∈ K, y ∈ A i}
  have hF : F.Finite := hfin K (isCompact_closedBall _ _) hKD
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i ∈ F, y ∉ A i := by
    apply (Filter.eventually_all_finite hF).mpr
    intro i hi
    exact (hA i).isOpen_compl.mem_nhds (hx.2 i)
  filter_upwards [Metric.ball_mem_nhds x (by linarith : 0 < r / 2), havoid] with y hy hay
  have hyK : y ∈ K := Metric.ball_subset_closedBall hy
  refine ⟨hKD hyK, ?_⟩
  intro i hi
  exact hay i ⟨y, hyK, hi⟩ hi

end SICLean.L4.G1ContinuationGeometryAux
