import SICLean.L4.UpperWindowDivisor

set_option autoImplicit false

/-! Compact extrema, finite-family bounds, compact template graphs, and
exponential shift estimates for the initial upper-plane window. The
compactness helpers also apply to the empty compact set. -/

noncomputable section
open Complex Set
open scoped Topology MatrixGroups

namespace SICLean.L4.UpperWindow.CompactAux

lemma positive_minimum {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K)
    (hp : ∀ x ∈ K, 0 < f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ f x :=
  hK.exists_forall_le' hf hp

lemma strict_upper_bound {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K)
    (hp : ∀ x ∈ K, f x < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ K, f x ≤ r := by
  obtain ⟨ε, hε, hb⟩ := positive_minimum hK (continuousOn_const.sub hf)
    (fun x hx => sub_pos.mpr (hp x hx))
  refine ⟨max (1 / 2) (1 - ε), by positivity, max_lt (by norm_num) (by linarith), ?_⟩
  intro x hx
  have hb' : ε ≤ 1 - f x := hb x hx
  exact (by linarith : f x ≤ 1 - ε).trans (le_max_right _ _)

lemma positive_bound {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, f x ≤ R := by
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn hf).bddAbove
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  exact fun x hx => (hR (mem_image_of_mem _ hx)).trans (le_max_right _ _)

@[fun_prop] lemma continuous_etaDenom (M : SL(2, ℤ)) : Continuous (etaDenom M) := by
  unfold etaDenom
  fun_prop

@[fun_prop] lemma continuous_e : Continuous e := by
  unfold e
  fun_prop

@[fun_prop] lemma continuousAt_e (z : ℂ) : ContinuousAt e z :=
  continuous_e.continuousAt

@[fun_prop] lemma continuousAt_etaDenom (M : SL(2, ℤ)) (τ : ℂ) :
    ContinuousAt (etaDenom M) τ := (continuous_etaDenom M).continuousAt

@[fun_prop] lemma continuousAt_etaMobius (M : SL(2, ℤ)) (τ : ℂ)
    (hT : etaDenom M τ ≠ 0) : ContinuousAt (etaMobius M) τ := by
  unfold etaMobius
  fun_prop (disch := assumption)

@[fun_prop] lemma continuous_rotation : Continuous rotation := by
  unfold rotation
  fun_prop

lemma tau_facts (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) {x : Parameters}
    (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    x.1 ∈ modularPhiDomain M ∧ 0 < (etaDenom M x.1).im ∧
      0 < (etaDenom M x.1).re ∧ etaDenom M x.1 ≠ 0 ∧
      0 < ‖e x.1‖ ∧ ‖e x.1‖ < 1 ∧
      0 < ‖e (etaMobius M x.1)‖ ∧ ‖e (etaMobius M x.1)‖ < 1 :=
  tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1

@[fun_prop] lemma continuous_aArg (m : ℤ) :
    Continuous (fun q : ℂ × ℂ => aArg m q.1 q.2) := by
  unfold aArg
  fun_prop (disch := simp [e_ne_zero])

@[fun_prop] lemma continuous_bArg (m p : ℤ) :
    Continuous (fun q : ℂ × ℂ × ℂ => bArg m p q.1 q.2.1 q.2.2) := by
  unfold bArg
  fun_prop (disch := simp [e_ne_zero])

@[fun_prop] lemma continuousAt_dArg (M : SL(2, ℤ)) (n : ℤ) (τ z : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    ContinuousAt (fun q : ℂ × ℂ => dArg M n q.1 q.2) (τ, z) := by
  unfold dArg
  fun_prop (disch := simp [e_ne_zero])

@[fun_prop] lemma continuousAt_cArg (M : SL(2, ℤ)) (n : ℤ) (τ y z : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    ContinuousAt (fun q : ℂ × ℂ × ℂ => cArg M n q.1 q.2.1 q.2.2) (τ, y, z) := by
  unfold cArg
  fun_prop (disch := simp [e_ne_zero])

lemma aArg_ne_zero (m : ℤ) (τ z : ℂ) : aArg m τ z ≠ 0 := by
  unfold aArg
  exact mul_ne_zero (zpow_ne_zero _ (e_ne_zero _)) (e_ne_zero _)

lemma bArg_ne_zero (m p : ℤ) (τ y z : ℂ) : bArg m p τ y z ≠ 0 := by
  unfold bArg
  exact mul_ne_zero (zpow_ne_zero _ (e_ne_zero _)) (e_ne_zero _)

lemma dArg_ne_zero (M : SL(2, ℤ)) (n : ℤ) (τ z : ℂ) : dArg M n τ z ≠ 0 := by
  unfold dArg
  exact mul_ne_zero (zpow_ne_zero _ (e_ne_zero _)) (e_ne_zero _)

lemma cArg_ne_zero (M : SL(2, ℤ)) (n : ℤ) (τ y z : ℂ) : cArg M n τ y z ≠ 0 := by
  unfold cArg
  exact mul_ne_zero (zpow_ne_zero _ (e_ne_zero _)) (e_ne_zero _)

lemma finite_strict_upper_bound {ι X : Type*} [TopologicalSpace X]
    (F : Finset ι) {K : Set X} (hK : IsCompact K) {f : ι → X → ℝ}
    (hf : ∀ i ∈ F, ContinuousOn (f i) K) (hp : ∀ i ∈ F, ∀ x ∈ K, f i x < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i ∈ F, ∀ x ∈ K, f i x ≤ r := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨r, hr, hr1, hri⟩ := strict_upper_bound hK (hf i (by simp)) (hp i (by simp))
    obtain ⟨s, hs, hs1, hsF⟩ := ih
      (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hp j (Finset.mem_insert_of_mem hj))
    refine ⟨max r s, lt_of_lt_of_le hr (le_max_left _ _), max_lt hr1 hs1, ?_⟩
    intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (hri x hx).trans (le_max_left _ _)
    · exact (hsF j hj x hx).trans (le_max_right _ _)

@[fun_prop] lemma continuous_base (M : SL(2, ℤ)) (m n : ℤ) (δ : ℝ) :
    Continuous (base M m n δ) := by
  unfold base
  fun_prop

@[fun_prop] lemma continuousAt_base (M : SL(2, ℤ)) (m n : ℤ) (δ : ℝ) (τ : ℂ) :
    ContinuousAt (base M m n δ) τ := (continuous_base M m n δ).continuousAt

/-- The eight arguments are kept in the same order as the fixed compact theorem. -/
def vertexArguments (M : SL(2, ℤ)) (m n p : ℤ) (δ : ℝ) (x : Parameters) : Fin 8 → ℂ :=
  let z := base M m n δ x.1
  ![aArg m x.1 z, bArg m p x.1 x.2.2 z, dArg M n x.1 z,
    cArg M n x.1 x.2.2 z, e x.1 / aArg m x.1 z,
    e (etaMobius M x.1) / dArg M n x.1 z,
    e x.1 / bArg m p x.1 x.2.2 z,
    e (etaMobius M x.1) / cArg M n x.1 x.2.2 z]

lemma vertexArguments_continuousAt (M : SL(2, ℤ)) (m n p : ℤ) (δ : ℝ)
    (x : Parameters) (hT : etaDenom M x.1 ≠ 0) (i : Fin 8) :
    ContinuousAt (fun x => vertexArguments M m n p δ x i) x := by
  fin_cases i <;> dsimp [vertexArguments]
  all_goals
    fun_prop (disch := first
      | assumption
      | exact aArg_ne_zero _ _ _
      | exact bArg_ne_zero _ _ _ _ _
      | exact dArg_ne_zero _ _ _ _
      | exact cArg_ne_zero _ _ _ _ _
      | simp [e_ne_zero])

lemma vertexArguments_lt_one (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ)
    (i : Fin 8) : ‖vertexArguments M m n p δ x i‖ < 1 := by
  have ht := tau_facts M h ℓ p ψ σ ρ δ hc hx
  obtain ⟨hS₁, hS₂, hH₁, hH₂, hsum₁, hsum₂⟩ :=
    coordinate_inequalities M h ℓ p ψ σ ρ δ hc x hx
  obtain ⟨_, _, _, _, hχ, hχ1⟩ := radius_margins M ψ σ ρ δ hc
  obtain ⟨ha, hb, hd, he⟩ := vertex_moduli M h ℓ p m n ψ σ ρ δ hc x hx
  obtain ⟨hra, hrd, hrb, hrc⟩ := reflected_vertex_moduli M h ℓ p m n ψ σ ρ δ hc x hx
  fin_cases i <;> dsimp [vertexArguments]
  all_goals simp only [ha, hb, hd, he, hra, hrd, hrb, hrc]
  all_goals apply Real.rpow_lt_one (norm_nonneg _)
  all_goals first | exact ht.2.2.2.2.2.1 | exact ht.2.2.2.2.2.2.2 | linarith

lemma compact_template_set (M : SL(2, ℤ)) (m n : ℤ) (δ : ℝ)
    (K : Set Parameters) (hK : IsCompact K) :
    IsCompact {q : Parameters × ℂ | q.1 ∈ K ∧ q.2 ∈ templates M m n δ q.1.1} := by
  let f₁ : Parameters × ℝ → Parameters × ℂ :=
    fun q => (q.1, base M m n δ q.1.1 + (q.2 : ℂ))
  let f₂ : Parameters × ℝ → Parameters × ℂ :=
    fun q => (q.1, base M m n δ q.1.1 + (q.2 : ℂ) * etaDenom M q.1.1)
  have hf₁ : Continuous f₁ := by
    dsimp [f₁, base, etaDenom]
    fun_prop
  have hf₂ : Continuous f₂ := by
    dsimp [f₂, base, etaDenom]
    fun_prop
  let S : Set (Parameters × ℂ) := f₁ '' (K ×ˢ Icc 0 1) ∪ f₂ '' (K ×ˢ Icc 0 1)
  have hS : IsCompact S :=
    ((hK.prod isCompact_Icc).image hf₁).union ((hK.prod isCompact_Icc).image hf₂)
  have heq : S = {q : Parameters × ℂ | q.1 ∈ K ∧ q.2 ∈ templates M m n δ q.1.1} := by
    ext q
    constructor
    · intro hq
      rcases hq with hq | hq
      · rcases hq with ⟨⟨x, t⟩, ⟨hx, ht⟩, heq⟩
        cases heq
        exact ⟨hx, Or.inl ⟨t, ht, rfl⟩⟩
      · rcases hq with ⟨⟨x, t⟩, ⟨hx, ht⟩, heq⟩
        cases heq
        exact ⟨hx, Or.inr ⟨t, ht, rfl⟩⟩
    · rintro ⟨hx, hz | hz⟩
      · rcases hz with ⟨t, ht, heq⟩
        exact Or.inl ⟨(q.1, t), ⟨hx, ht⟩, Prod.ext rfl heq⟩
      · rcases hz with ⟨t, ht, heq⟩
        exact Or.inr ⟨(q.1, t), ⟨hx, ht⟩, Prod.ext rfl heq⟩
  exact heq ▸ hS

lemma finite_rates {ι : Type*} (F : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ i a b, a ≤ b → P i a → P i b)
    (hb : ∀ i ∈ F, ∃ r : ℝ, 0 < r ∧ r < 1 ∧ P i r) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i ∈ F, P i r := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨r, hr, hr1, hri⟩ := hb i (by simp)
    obtain ⟨s, hs, hs1, hsF⟩ := ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    refine ⟨max r s, lt_of_lt_of_le hr (le_max_left _ _), max_lt hr1 hs1, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hmono _ _ _ (le_max_left _ _) hri
    · exact hmono _ _ _ (le_max_right _ _) (hsF _ hj)

lemma e_add (z u : ℂ) : e (z + u) = e z * e u := by
  simp only [e, mul_add, Complex.exp_add]

lemma e_neg (z : ℂ) : e (-z) = (e z)⁻¹ := by
  simp only [e, mul_neg, Complex.exp_neg]

lemma norm_e (z : ℂ) : ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  rw [e, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma norm_e_le_one {z : ℂ} (hz : 0 ≤ z.im) : ‖e z‖ ≤ 1 := by
  rw [norm_e, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos]

lemma arguments_add (M : SL(2, ℤ)) (m n p : ℤ) (τ y z u : ℂ) :
    aArg m τ (z + u) = aArg m τ z * e u ∧
      bArg m p τ y (z + u) = bArg m p τ y z * e u ∧
      dArg M n τ (z + u) = dArg M n τ z * e (u / etaDenom M τ) ∧
      cArg M n τ y (z + u) = cArg M n τ y z * e (u / etaDenom M τ) := by
  simp only [aArg, bArg, dArg, cArg, add_div, add_right_comm z u y, e_add]
  constructor <;> [ring; skip]
  constructor <;> [ring; skip]
  constructor <;> ring

lemma norm_mul_e_le {a u : ℂ} (hu : 0 ≤ u.im) : ‖a * e u‖ ≤ ‖a‖ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_e_le_one hu) (norm_nonneg _)).trans_eq (mul_one _)

lemma norm_div_mul_e_le {q a u : ℂ} (hu : 0 ≤ (-u).im) :
    ‖q / (a * e u)‖ ≤ ‖q / a‖ := by
  have he : q / (a * e u) = (q / a) * e (-u) := by
    rw [e_neg]
    ring
  rw [he]
  exact norm_mul_e_le hu

lemma upper_arguments_le_vertex (M : SL(2, ℤ)) (m n p : ℤ) (τ y z : ℂ)
    (ψ r θ : ℝ) (hr : 0 ≤ r)
    (hT : 0 < (etaDenom M τ).arg) (hTψ : (etaDenom M τ).arg < ψ)
    (hψ : ψ < Real.pi / 4)
    (hθ : θ ∈ Icc (etaDenom M τ).arg (Real.pi / 2 + ψ)) :
    ‖aArg m τ (z + (r : ℂ) * rotation θ)‖ ≤ ‖aArg m τ z‖ ∧
      ‖bArg m p τ y (z + (r : ℂ) * rotation θ)‖ ≤ ‖bArg m p τ y z‖ ∧
      ‖dArg M n τ (z + (r : ℂ) * rotation θ)‖ ≤ ‖dArg M n τ z‖ ∧
      ‖cArg M n τ y (z + (r : ℂ) * rotation θ)‖ ≤ ‖cArg M n τ y z‖ := by
  obtain ⟨hi, hiT⟩ := upper_direction_im_nonneg (etaDenom M τ) ψ θ hT hTψ hψ hθ
  have hu : 0 ≤ ((r : ℂ) * rotation θ).im := by simpa using mul_nonneg hr hi
  have huT : 0 ≤ (((r : ℂ) * rotation θ) / etaDenom M τ).im := by
    rw [mul_div_assoc]
    simpa using mul_nonneg hr hiT
  obtain ⟨ha, hb, hd, he⟩ := arguments_add M m n p τ y z ((r : ℂ) * rotation θ)
  rw [ha, hb, hd, he]
  exact ⟨norm_mul_e_le hu, norm_mul_e_le hu, norm_mul_e_le huT, norm_mul_e_le huT⟩

lemma lower_arguments_le_vertex (M : SL(2, ℤ)) (m n p : ℤ) (τ y z : ℂ)
    (ψ r θ : ℝ) (hr : 0 ≤ r)
    (hT : 0 < (etaDenom M τ).arg) (hTψ : (etaDenom M τ).arg < ψ)
    (hψ : ψ < Real.pi / 4) (hθ : θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    ‖e τ / aArg m τ (z + (r : ℂ) * rotation θ)‖ ≤ ‖e τ / aArg m τ z‖ ∧
      ‖e (etaMobius M τ) / dArg M n τ (z + (r : ℂ) * rotation θ)‖ ≤
        ‖e (etaMobius M τ) / dArg M n τ z‖ ∧
      ‖e τ / bArg m p τ y (z + (r : ℂ) * rotation θ)‖ ≤ ‖e τ / bArg m p τ y z‖ ∧
      ‖e (etaMobius M τ) / cArg M n τ y (z + (r : ℂ) * rotation θ)‖ ≤
        ‖e (etaMobius M τ) / cArg M n τ y z‖ := by
  obtain ⟨hi, hiT⟩ := lower_direction_im_nonneg (etaDenom M τ) ψ θ hT hTψ hψ hθ
  have hu : 0 ≤ (-((r : ℂ) * rotation θ)).im := by
    simpa [← mul_neg] using mul_nonneg hr hi
  have huT : 0 ≤ (-(((r : ℂ) * rotation θ) / etaDenom M τ)).im := by
    rw [mul_div_assoc]
    simpa [← neg_div, ← mul_neg] using mul_nonneg hr hiT.le
  obtain ⟨ha, hb, hd, he⟩ := arguments_add M m n p τ y z ((r : ℂ) * rotation θ)
  rw [ha, hb, hd, he]
  exact ⟨norm_div_mul_e_le hu, norm_div_mul_e_le huT,
    norm_div_mul_e_le hu, norm_div_mul_e_le huT⟩

end SICLean.L4.UpperWindow.CompactAux
