import SICLean.L4.UpperContourBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContourSidesAux
open UpperContour

lemma integral_units {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (R : ℕ)
    (hg : ContinuousOn g (Icc 0 (R : ℝ))) :
    (∫ t : ℝ in 0..(R : ℝ), g t) =
      ∑ k ∈ Finset.range R, ∫ u : ℝ in 0..1, g ((k : ℝ) + u) := by
  have hi : ∀ k < R, IntervalIntegrable g volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable
    apply hg.mono
    rw [uIcc_of_le (by exact_mod_cast Nat.le_succ k)]
    intro t ht
    exact ⟨(by positivity : (0 : ℝ) ≤ k).trans ht.1,
      ht.2.trans (by exact_mod_cast Nat.succ_le_of_lt hk)⟩
  calc
    _ = ∑ k ∈ Finset.range R, ∫ t : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g t := by
      simpa using (intervalIntegral.sum_integral_adjacent_intervals hi).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa [Nat.cast_add, add_comm] using
        (intervalIntegral.integral_comp_add_left g (k : ℝ) (a := 0) (b := 1)).symm

lemma norm_integral_units_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (b : ℕ → ℝ) (R : ℕ)
    (hg : ContinuousOn g (Icc 0 (R : ℝ)))
    (hb : ∀ k < R, ∀ u ∈ Icc (0 : ℝ) 1, ‖g ((k : ℝ) + u)‖ ≤ b k) :
    ‖∫ t : ℝ in 0..(R : ℝ), g t‖ ≤ ∑ k ∈ Finset.range R, b k := by
  rw [integral_units g R hg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hbound : ∀ u ∈ Ι (0 : ℝ) 1, ‖g ((k : ℝ) + u)‖ ≤ b k := by
    intro u hu
    rw [uIoc_of_le zero_le_one] at hu
    exact hb k (Finset.mem_range.mp hk) u ⟨hu.1.le, hu.2⟩
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

lemma geometric_sum_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (R : ℕ) :
    (∑ k ∈ Finset.range R, r ^ k) ≤ 1 / (1 - r) := by
  have hs := summable_geometric_of_lt_one hr hr1
  simpa [tsum_geometric_of_lt_one hr hr1, one_div] using
    hs.sum_le_tsum (Finset.range R) (fun k _ => pow_nonneg hr k)

lemma kernel_continuousAt (kind : Kind) (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ℓ p m n : ℤ) (x : UpperWindow.Parameters) (z : ℂ)
    (hz : (z, x.1) ∈ modularPhiNonvanishingDomain M (m + 1) n ∧
      (z + x.2.2, x.1) ∈ modularPhiNonvanishingDomain M (m + p) n) :
    ContinuousAt (UpperContour.kernel kind M m n h ℓ p x) z := by
  have hn : ContinuousAt (fun u : ℂ => modularPhi M (m + 1) n u x.1) z :=
    (modularPhi_joint_analytic_no_poles M hM (m + 1) n
      (z, x.1) ⟨hz.1.1, hz.1.2.1⟩).continuousAt.comp (f := fun u : ℂ => (u, x.1))
        (show ContinuousAt (fun u : ℂ => (u, x.1)) z by fun_prop)
  have hd : ContinuousAt (fun u : ℂ => modularPhi M (m + p) n (u + x.2.2) x.1) z :=
    (modularPhi_joint_analytic_no_poles M hM (m + p) n
      (z + x.2.2, x.1) ⟨hz.2.1, hz.2.2.1⟩).continuousAt.comp
        (f := fun u : ℂ => (u + x.2.2, x.1))
        (show ContinuousAt (fun u : ℂ => (u + x.2.2, x.1)) z by fun_prop)
  have hdn : modularPhi M (m + p) n (z + x.2.2) x.1 ≠ 0 :=
    (modularPhi_ne_zero_iff M hM (m + p) n _ _ hz.2.1 hz.2.2.1).mpr hz.2.2.2
  have he : ContinuousAt (fun z => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)) z := by
    unfold UpperWindow.phase e
    fun_prop
  cases kind
  · exact hn.mul he
  · exact (hn.div hd hdn).mul he

lemma boundary_continuous (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) :
    ContinuousOn (UpperContour.kernel kind M m n h ℓ p x)
      (boxBoundary (UpperWindow.base M m n δ x.1) (etaDenom M x.1) (R : ℝ)) := by
  intro z hz
  exact (kernel_continuousAt kind M hc.1 h ℓ p m n x z
    (boundary_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx R z hz)).continuousWithinAt

lemma side_continuous (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) :
    let f := UpperContour.kernel kind M m n h ℓ p x
    let v := UpperWindow.base M m n δ x.1
    let T := etaDenom M x.1
    ContinuousOn (fun t : ℝ => f (v + (t : ℂ))) (Icc 0 (R : ℝ)) ∧
    ContinuousOn (rayPullback f v T) (Icc 0 (R : ℝ)) ∧
    ContinuousOn (fun t : ℝ => f (v + (R : ℂ) * T + (t : ℂ))) (Icc 0 (R : ℝ)) ∧
    ContinuousOn (fun t : ℝ => f (v + (R : ℂ) + (t : ℂ) * T) * T)
      (Icc 0 (R : ℝ)) := by
  dsimp only
  have hT := (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).2.1.ne'
  have hf := boundary_continuous kind M h ℓ p m n ψ σ ρ δ hc x hx R
  rw [boundary_eq_four_edges _ _ hT R] at hf
  have h1 := hf.mono (Set.subset_union_of_subset_left
    (Set.subset_union_of_subset_left Set.subset_union_left _ ) _)
  have h2 := hf.mono (Set.subset_union_of_subset_left
    (Set.subset_union_of_subset_left Set.subset_union_right _ ) _)
  have h3 := hf.mono (Set.subset_union_of_subset_left Set.subset_union_right _)
  have h4 := hf.mono Set.subset_union_right
  refine ⟨h1.comp (by fun_prop) (fun t ht => mem_image_of_mem _ ht), ?_,
    h3.comp (by fun_prop) (fun t ht => mem_image_of_mem _ ht), ?_⟩
  · exact (h2.comp (by fun_prop) (fun t ht => mem_image_of_mem _ ht)).mul_const _
  · exact (h4.comp (by fun_prop) (fun t ht => mem_image_of_mem _ ht)).mul_const _

lemma ray_continuous (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ContinuousOn (rayPullback (UpperContour.kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) 1) (Ici 0) ∧
    ContinuousOn (rayPullback (UpperContour.kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (etaDenom M x.1)) (Ici 0) := by
  have hT := (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).2.1.ne'
  constructor <;> intro t ht <;> obtain ⟨R, hR⟩ := exists_nat_ge t
  · have hz : UpperWindow.base M m n δ x.1 + (t : ℂ) ∈
        boxBoundary (UpperWindow.base M m n δ x.1) (etaDenom M x.1) (R : ℝ) := by
      rw [boundary_eq_four_edges _ _ hT R]
      exact Or.inl (Or.inl (Or.inl ⟨t, ⟨ht, hR⟩, rfl⟩))
    have hcont := kernel_continuousAt kind M hc.1 h ℓ p m n x _
      (boundary_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx R _ hz)
    change ContinuousWithinAt (fun u : ℝ => UpperContour.kernel kind M m n h ℓ p x
      (UpperWindow.base M m n δ x.1 + (u : ℂ) * 1) * 1) (Ici 0) t
    simp only [mul_one]
    exact (hcont.comp (f := fun u : ℝ => UpperWindow.base M m n δ x.1 + (u : ℂ))
      (by fun_prop)).continuousWithinAt
  · have hz : UpperWindow.base M m n δ x.1 + (t : ℂ) * etaDenom M x.1 ∈
        boxBoundary (UpperWindow.base M m n δ x.1) (etaDenom M x.1) (R : ℝ) := by
      rw [boundary_eq_four_edges _ _ hT R]
      exact Or.inl (Or.inl (Or.inr ⟨t, ⟨ht, hR⟩, rfl⟩))
    have hcont := kernel_continuousAt kind M hc.1 h ℓ p m n x _
      (boundary_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx R _ hz)
    exact ((hcont.comp (f := fun u : ℝ =>
      UpperWindow.base M m n δ x.1 + (u : ℂ) * etaDenom M x.1)
      (by fun_prop)).mul_const _).continuousWithinAt

lemma integral_norm_unit_bound (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 0))
    (b : ℕ → ℝ) (hbound : ∀ (k : ℕ) (t : ℝ),
      t ∈ Icc (k : ℝ) ((k : ℝ) + 1) → ‖g t‖ ≤ b k) (k : ℕ) :
    (∫ t in (k : ℝ)..((k : ℝ) + 1), ‖g t‖) ≤ b k := by
  have hi : IntervalIntegrable g volume (k : ℝ) ((k : ℝ) + 1) :=
    (hg.mono (fun t ht => (Nat.cast_nonneg k).trans ht.1)).intervalIntegrable_of_Icc
      (by linarith)
  calc
    _ ≤ ∫ t in (k : ℝ)..((k : ℝ) + 1), b k :=
      intervalIntegral.integral_mono_on (by linarith) hi.norm
        intervalIntegrable_const (fun t ht => hbound k t ht)
    _ = b k := by simp

lemma integral_norm_finite_bound (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 0))
    (b : ℕ → ℝ) (hbound : ∀ (k : ℕ) (t : ℝ),
      t ∈ Icc (k : ℝ) ((k : ℝ) + 1) → ‖g t‖ ≤ b k) (R n : ℕ) :
    (∫ t in (R : ℝ)..((R + n : ℕ) : ℝ), ‖g t‖) ≤
      ∑ k ∈ Finset.range n, b (R + k) := by
  calc
    _ = ∑ k ∈ Finset.range n,
        ∫ t in ((R + k : ℕ) : ℝ)..(((R + k : ℕ) : ℝ) + 1), ‖g t‖ := by
      symm
      simpa only [Nat.cast_add, Nat.cast_one, add_zero, add_assoc] using
        intervalIntegral.sum_integral_adjacent_intervals
          (a := fun k : ℕ => ((R + k : ℕ) : ℝ)) (n := n)
          (fun k hk => ((hg.mono (fun t ht =>
            (Nat.cast_nonneg (R + k)).trans ht.1)).intervalIntegrable_of_Icc
              (μ := volume) (by exact_mod_cast Nat.le_add_right (R + k) 1)).norm)
    _ ≤ _ := Finset.sum_le_sum (fun k hk =>
      integral_norm_unit_bound g hg b hbound (R + k))

lemma integrable_ray_of_unit_bounds (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 0))
    (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k)
    (hbound : ∀ (k : ℕ) (t : ℝ),
      t ∈ Icc (k : ℝ) ((k : ℝ) + 1) → ‖g t‖ ≤ b k) :
    IntegrableOn g (Ioi 0) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (∑' k, b k) 0
    (fun n : ℕ => ((hg.mono (fun t ht => ht.1)).intervalIntegrable_of_Icc
      (Nat.cast_nonneg n)).1) tendsto_natCast_atTop_atTop
    (Eventually.of_forall (fun n => ?_))
  calc
    _ ≤ ∑ k ∈ Finset.range n, b k := by
      simpa using integral_norm_finite_bound g hg b hbound 0 n
    _ ≤ _ := hb.sum_le_tsum _ (fun k hk => hb0 k)

lemma ray_tail_bound (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 0))
    (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k)
    (hbound : ∀ (k : ℕ) (t : ℝ),
      t ∈ Icc (k : ℝ) ((k : ℝ) + 1) → ‖g t‖ ≤ b k) (R : ℕ) :
    ‖(∫ t in (0 : ℝ)..(R : ℝ), g t) - ∫ t in Ioi 0, g t‖ ≤
      ∑' k : ℕ, b (R + k) := by
  have hgI := integrable_ray_of_unit_bounds g hg b hb hb0 hbound
  have hgR : IntegrableOn g (Ioi (R : ℝ)) :=
    hgI.mono_set (Ioi_subset_Ioi (Nat.cast_nonneg R))
  have hbR : Summable (fun k : ℕ => b (R + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff R).2 hb
  have hlim : Tendsto (fun n : ℕ => ∫ t in (R : ℝ)..((R + n : ℕ) : ℝ), ‖g t‖)
      atTop (𝓝 (∫ t in Ioi (R : ℝ), ‖g t‖)) := by
    apply intervalIntegral_tendsto_integral_Ioi (R : ℝ) hgR.norm
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat R) using 1
    funext n
    simp only [Function.comp_apply, Nat.add_comm]
  have htail : (∫ t in Ioi (R : ℝ), ‖g t‖) ≤ ∑' k : ℕ, b (R + k) := by
    apply le_of_tendsto' hlim
    intro n
    exact (integral_norm_finite_bound g hg b hbound R n).trans
      (hbR.sum_le_tsum _ (fun k hk => hb0 (R + k)))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hgI hgR
  have hdiff : (∫ t in (0 : ℝ)..(R : ℝ), g t) - ∫ t in Ioi 0, g t =
      -(∫ t in Ioi (R : ℝ), g t) := by
    rw [← hsplit]
    abel
  rw [hdiff, norm_neg]
  exact (norm_integral_le_integral_norm _).trans htail

theorem phi_index_covariance (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n q : ℤ) (τ z : ℂ) :
    modularPhi M (m + M 1 0 * q) n (z - (q : ℂ) * etaDenom M τ) τ =
      modularPhi M m n z τ := by
  have hs := modularPhi_shift_integer M hM (m + M 1 0 * q) n
    (-(M 1 0 * q)) (-(M 1 1 * q)) z τ
  have hz : z + ((-(M 1 0 * q) : ℤ) : ℂ) * τ + ((-(M 1 1 * q) : ℤ) : ℂ) =
      z - (q : ℂ) * etaDenom M τ := by
    push_cast
    unfold etaDenom
    ring
  rw [hz] at hs
  convert hs using 1 <;> congr 1 <;> ring

theorem phase_index_covariance (M : SL(2, ℤ)) (m n h ℓ q : ℤ) (τ w z : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    UpperWindow.phase M (m + M 1 0 * q) n h ℓ τ w (z - (q : ℂ) * etaDenom M τ) =
      UpperWindow.phase M m n h ℓ τ w z + ((-((ℓ * M 1 1 + h) * q) : ℤ) : ℂ) := by
  unfold UpperWindow.phase
  push_cast
  field_simp
  unfold etaDenom
  ring

theorem base_index_covariance (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n q : ℤ) (δ : ℝ) (τ : ℂ) :
    UpperWindow.base M (m + M 1 0 * q) n δ τ =
      UpperWindow.base M m n δ τ - (q : ℂ) * etaDenom M τ := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  unfold UpperWindow.base
  push_cast
  field_simp
  ring

theorem kernel_index_covariance (kind : Kind) (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n h ℓ p q : ℤ) (x : UpperWindow.Parameters) (hT : etaDenom M x.1 ≠ 0) (z : ℂ) :
    UpperContour.kernel kind M (m + M 1 0 * q) n h ℓ p x
        (z - (q : ℂ) * etaDenom M x.1) = UpperContour.kernel kind M m n h ℓ p x z := by
  have hnum : modularPhi M (m + M 1 0 * q + 1) n
      (z - (q : ℂ) * etaDenom M x.1) x.1 = modularPhi M (m + 1) n z x.1 := by
    convert phi_index_covariance M hM (m + 1) n q x.1 z using 1 <;> congr 1 <;> ring
  have hden : modularPhi M (m + M 1 0 * q + p) n
      (z - (q : ℂ) * etaDenom M x.1 + x.2.2) x.1 =
      modularPhi M (m + p) n (z + x.2.2) x.1 := by
    convert phi_index_covariance M hM (m + p) n q x.1 (z + x.2.2)
      using 1 <;> congr 1 <;> ring
  have hp : e (UpperWindow.phase M (m + M 1 0 * q) n h ℓ x.1 x.2.1
      (z - (q : ℂ) * etaDenom M x.1)) = e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z) := by
    rw [phase_index_covariance M m n h ℓ q x.1 x.2.1 z hT, e_add', e_intCast, mul_one]
  cases kind <;> simp only [UpperContour.kernel, UpperWindow.singleKernel,
    UpperWindow.ratioKernel, hnum, hden, hp]

theorem kernel_base_index_covariance (kind : Kind) (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n h ℓ p q : ℤ) (δ : ℝ) (x : UpperWindow.Parameters) (hT : etaDenom M x.1 ≠ 0)
    (u : ℂ) :
    UpperContour.kernel kind M (m + M 1 0 * q) n h ℓ p x
        (UpperWindow.base M (m + M 1 0 * q) n δ x.1 + u) =
      UpperContour.kernel kind M m n h ℓ p x (UpperWindow.base M m n δ x.1 + u) := by
  rw [base_index_covariance M hM]
  convert kernel_index_covariance kind M hM m n h ℓ p q x hT
    (UpperWindow.base M m n δ x.1 + u) using 1 <;> congr 1 <;> ring

theorem template_index_covariance (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n q : ℤ)
    (δ : ℝ) (τ z : ℂ) (hz : z ∈ UpperWindow.templates M (m + M 1 0 * q) n δ τ) :
    z + (q : ℂ) * etaDenom M τ ∈ UpperWindow.templates M m n δ τ := by
  rcases hz with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · left
    refine ⟨u, hu, ?_⟩
    rw [base_index_covariance M hM]
    ring
  · right
    refine ⟨u, hu, ?_⟩
    rw [base_index_covariance M hM]
    ring

theorem template_bound_integer_extension (kind : Kind) (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ℓ p : ℤ) (δ : ℝ) (x : UpperWindow.Parameters) (hT : etaDenom M x.1 ≠ 0)
    (H : ℕ → ℕ → ℝ)
    (hb : ∀ r ∈ Finset.range (M 1 0).toNat,
      ∀ z ∈ UpperWindow.templates M (r : ℤ) n δ x.1, ∀ j k : ℕ,
      ‖UpperContour.kernel kind M (r : ℤ) n h ℓ p x (UpperContour.translate M x.1 z j k)‖ ≤ H j k)
    (m : ℤ) (z : ℂ) (hz : z ∈ UpperWindow.templates M m n δ x.1) (j k : ℕ) :
    ‖UpperContour.kernel kind M m n h ℓ p x (UpperContour.translate M x.1 z j k)‖ ≤ H j k := by
  let r : ℕ := (m % M 1 0).toNat
  let q : ℤ := m / M 1 0
  have hr0 : 0 ≤ m % M 1 0 := Int.emod_nonneg _ (ne_of_gt hM)
  have hr : (r : ℤ) = m % M 1 0 := Int.toNat_of_nonneg hr0
  have hrange : r ∈ Finset.range (M 1 0).toNat := by
    rw [Finset.mem_range]
    exact (Int.toNat_lt_toNat hM).2 (Int.emod_lt_of_pos m hM)
  have hm : m = (r : ℤ) + M 1 0 * q := by
    rw [hr]
    exact (Int.emod_add_mul_ediv m (M 1 0)).symm
  have hzb : z + (q : ℂ) * etaDenom M x.1 ∈ UpperWindow.templates M (r : ℤ) n δ x.1 := by
    apply template_index_covariance M hM (r : ℤ) n q δ x.1 z
    rwa [← hm]
  have heq : UpperContour.kernel kind M m n h ℓ p x (UpperContour.translate M x.1 z j k) =
      UpperContour.kernel kind M (r : ℤ) n h ℓ p x
        (UpperContour.translate M x.1 (z + (q : ℂ) * etaDenom M x.1) j k) := by
    rw [hm]
    convert kernel_index_covariance kind M hM (r : ℤ) n h ℓ p q x hT
      (UpperContour.translate M x.1 (z + (q : ℂ) * etaDenom M x.1) j k) using 1 <;>
      congr 1 <;> unfold UpperContour.translate <;> ring
  rw [heq]
  exact hb r hrange _ hzb j k

theorem fixed_template_bounds_integer (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ M₀ D : ℝ, 0 < M₀ ∧ 0 < D ∧
      ∀ m : ℤ, ∀ z ∈ UpperWindow.templates M m n δ x.1, ∀ j k : ℕ,
        ‖UpperContour.kernel .ratio M m n h ℓ p x (UpperContour.translate M x.1 z j k)‖ ≤
          M₀ * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
            (‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat) ^ k ∧
        ‖UpperContour.kernel .single M m n h ℓ p x (UpperContour.translate M x.1 z j k)‖ ≤
          M₀ * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
            quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k := by
  rcases fixed_template_bounds M h ℓ p n ψ σ ρ δ hc x hx with ⟨M₀, D, hM₀, hD, hb⟩
  have hT := ModularCocycleUpperAux.etaDenom_ne_zero_upper M hx.1.1
  refine ⟨M₀, D, hM₀, hD, ?_⟩
  intro m z hz j k
  constructor
  · exact template_bound_integer_extension .ratio M hc.1 n h ℓ p δ x hT _
      (fun r hr u hu a b => (hb r hr u hu a b).1) m z hz j k
  · exact template_bound_integer_extension .single M hc.1 n h ℓ p δ x hT _
      (fun r hr u hu a b => (hb r hr u hu a b).2) m z hz j k

lemma kernel_unit_bounds (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (δ : ℝ) (x : UpperWindow.Parameters) (C r L : ℝ) (w : ℕ → ℝ)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hw : ∀ k, 0 ≤ w k) (hL : ‖etaDenom M x.1‖ ≤ L)
    (hb : ∀ z ∈ UpperWindow.templates M m n δ x.1, ∀ j k : ℕ,
      ‖UpperContour.kernel kind M m n h ℓ p x (UpperContour.translate M x.1 z j k)‖ ≤
        C * r ^ j * w k) :
    (∀ (k : ℕ) (t : ℝ), t ∈ Icc (k : ℝ) ((k : ℝ) + 1) →
      ‖rayPullback (UpperContour.kernel kind M m n h ℓ p x)
        (UpperWindow.base M m n δ x.1) 1 t‖ ≤ C * w k) ∧
    (∀ (j : ℕ) (t : ℝ), t ∈ Icc (j : ℝ) ((j : ℝ) + 1) →
      ‖rayPullback (UpperContour.kernel kind M m n h ℓ p x)
        (UpperWindow.base M m n δ x.1) (etaDenom M x.1) t‖ ≤ L * C * w 0 * r ^ j) := by
  constructor
  · intro k t ht
    have hu : t - (k : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hb0 := hb (UpperWindow.base M m n δ x.1 + ((t - (k : ℝ) : ℝ) : ℂ))
      (Or.inl ⟨t - k, hu, rfl⟩) 0 k
    have heq : UpperContour.translate M x.1
        (UpperWindow.base M m n δ x.1 + ((t - (k : ℝ) : ℝ) : ℂ)) 0 k =
        UpperWindow.base M m n δ x.1 + (t : ℂ) := by
      simp only [UpperContour.translate, Nat.cast_zero, zero_mul, add_zero,
        Complex.ofReal_sub, Complex.ofReal_natCast]
      ring
    simpa only [heq, pow_zero, mul_one, rayPullback] using hb0
  · intro j t ht
    have hu : t - (j : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hb0 := hb (UpperWindow.base M m n δ x.1 +
        ((t - (j : ℝ) : ℝ) : ℂ) * etaDenom M x.1) (Or.inr ⟨t - j, hu, rfl⟩) j 0
    have heq : UpperContour.translate M x.1
        (UpperWindow.base M m n δ x.1 + ((t - (j : ℝ) : ℝ) : ℂ) * etaDenom M x.1) j 0 =
        UpperWindow.base M m n δ x.1 + (t : ℂ) * etaDenom M x.1 := by
      simp only [UpperContour.translate, Nat.cast_zero, add_zero,
        Complex.ofReal_sub, Complex.ofReal_natCast]
      ring
    rw [heq] at hb0
    rw [rayPullback, norm_mul]
    calc
      _ ≤ (C * r ^ j * w 0) * ‖etaDenom M x.1‖ :=
        mul_le_mul_of_nonneg_right hb0 (norm_nonneg _)
      _ ≤ (C * r ^ j * w 0) * L :=
        mul_le_mul_of_nonneg_left hL (mul_nonneg (mul_nonneg hC (pow_nonneg hr j)) (hw 0))
      _ = _ := by ring

/-- A summable grid majorant gives both absolute ray integrals and four
separate quantitative errors. Its constants can be chosen before parameters. -/
lemma four_side_estimates (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (C r L : ℝ) (w : ℕ → ℝ)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1) (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (hL : ‖etaDenom M x.1‖ ≤ L)
    (hb : ∀ z ∈ UpperWindow.templates M m n δ x.1, ∀ j k : ℕ,
      ‖UpperContour.kernel kind M m n h ℓ p x (UpperContour.translate M x.1 z j k)‖ ≤
        C * r ^ j * w k) :
    let f := UpperContour.kernel kind M m n h ℓ p x
    let v := UpperWindow.base M m n δ x.1
    let T := etaDenom M x.1
    IntegrableOn (rayPullback f v 1) (Ioi 0) ∧
    IntegrableOn (rayPullback f v T) (Ioi 0) ∧
    ∀ R : ℕ,
      ‖firstSide f v R + rayIntegral f v 1‖ ≤ (∑' k : ℕ, C * w (R + k)) ∧
      ‖secondSide f v T R - rayIntegral f v T‖ ≤
        (∑' j : ℕ, L * C * w 0 * r ^ (R + j)) ∧
      ‖thirdSide f v T R‖ ≤ C * r ^ R * (∑' k : ℕ, w k) ∧
      ‖fourthSide f v T R‖ ≤ L * C / (1 - r) * w R := by
  dsimp only
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  obtain ⟨hb1, hb2⟩ := kernel_unit_bounds kind M h ℓ p m n δ x C r L w hC hr hw hL hb
  obtain ⟨hg1, hg2⟩ := ray_continuous kind M h ℓ p m n ψ σ ρ δ hc x hx
  have hs1 : Summable (fun k => C * w k) := hws.mul_left C
  have hs2 : Summable (fun j => L * C * w 0 * r ^ j) :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hn1 : ∀ k, 0 ≤ C * w k := fun k => mul_nonneg hC (hw k)
  have hn2 : ∀ j, 0 ≤ L * C * w 0 * r ^ j := fun j =>
    mul_nonneg (mul_nonneg (mul_nonneg hL0 hC) (hw 0)) (pow_nonneg hr j)
  refine ⟨integrable_ray_of_unit_bounds _ hg1 _ hs1 hn1 hb1,
    integrable_ray_of_unit_bounds _ hg2 _ hs2 hn2 hb2, ?_⟩
  intro R
  have hn := ray_tail_bound _ hg1 _ hs1 hn1 hb1 R
  have hfirst : ‖firstSide (UpperContour.kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) R +
      rayIntegral (UpperContour.kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) 1‖ ≤
      ∑' k : ℕ, C * w (R + k) := by
    rw [firstSide, intervalIntegral.integral_symm]
    convert hn using 1
    rw [← norm_neg]
    congr 1
    simp only [rayPullback, mul_one, rayIntegral]
    abel
  refine ⟨hfirst, ray_tail_bound _ hg2 _ hs2 hn2 hb2 R, ?_, ?_⟩
  · have hi := norm_integral_units_le
      (fun t : ℝ => UpperContour.kernel kind M m n h ℓ p x
        (UpperWindow.base M m n δ x.1 + (R : ℂ) * etaDenom M x.1 + (t : ℂ)))
      (fun k => C * r ^ R * w k) R
      (side_continuous kind M h ℓ p m n ψ σ ρ δ hc x hx R).2.2.1
    have hb' : ∀ k < R, ∀ u ∈ Icc (0 : ℝ) 1,
        ‖UpperContour.kernel kind M m n h ℓ p x (UpperWindow.base M m n δ x.1 +
          (R : ℂ) * etaDenom M x.1 + (((k : ℝ) + u : ℝ) : ℂ))‖ ≤ C * r ^ R * w k := by
      intro k hk u hu
      convert hb (UpperWindow.base M m n δ x.1 + (u : ℂ))
        (Or.inl ⟨u, hu, rfl⟩) R k using 1 <;> congr 1 <;>
        simp only [UpperContour.translate, Complex.ofReal_add, Complex.ofReal_natCast] <;> ring
    have hfin : ‖thirdSide (UpperContour.kernel kind M m n h ℓ p x)
        (UpperWindow.base M m n δ x.1) (etaDenom M x.1) R‖ ≤
        C * r ^ R * ∑ k ∈ Finset.range R, w k := by
      simpa only [thirdSide, Finset.mul_sum] using hi hb'
    exact hfin.trans (mul_le_mul_of_nonneg_left
      (hws.sum_le_tsum _ (fun k _ => hw k)) (mul_nonneg hC (pow_nonneg hr R)))
  · rw [fourthSide, intervalIntegral.integral_symm, norm_neg]
    have hi := norm_integral_units_le
      (fun t : ℝ => UpperContour.kernel kind M m n h ℓ p x
        (UpperWindow.base M m n δ x.1 + (R : ℂ) + (t : ℂ) * etaDenom M x.1) * etaDenom M x.1)
      (fun j => L * C * w R * r ^ j) R
      (side_continuous kind M h ℓ p m n ψ σ ρ δ hc x hx R).2.2.2
    have hb' : ∀ j < R, ∀ u ∈ Icc (0 : ℝ) 1,
        ‖UpperContour.kernel kind M m n h ℓ p x (UpperWindow.base M m n δ x.1 + (R : ℂ) +
          (((j : ℝ) + u : ℝ) : ℂ) * etaDenom M x.1) * etaDenom M x.1‖ ≤
          L * C * w R * r ^ j := by
      intro j hj u hu
      have hb0 := hb (UpperWindow.base M m n δ x.1 + (u : ℂ) * etaDenom M x.1)
        (Or.inr ⟨u, hu, rfl⟩) j R
      have heq : UpperWindow.base M m n δ x.1 + (R : ℂ) +
          (((j : ℝ) + u : ℝ) : ℂ) * etaDenom M x.1 =
          UpperContour.translate M x.1 (UpperWindow.base M m n δ x.1 +
            (u : ℂ) * etaDenom M x.1) j R := by
        simp only [UpperContour.translate, Complex.ofReal_add, Complex.ofReal_natCast]
        ring
      rw [norm_mul, heq]
      calc
        _ ≤ (C * r ^ j * w R) * ‖etaDenom M x.1‖ :=
          mul_le_mul_of_nonneg_right hb0 (norm_nonneg _)
        _ ≤ (C * r ^ j * w R) * L :=
          mul_le_mul_of_nonneg_left hL (mul_nonneg (mul_nonneg hC (pow_nonneg hr j)) (hw R))
        _ = _ := by ring
    calc
      _ ≤ L * C * w R * ∑ j ∈ Finset.range R, r ^ j := by
        simpa only [Finset.mul_sum] using hi hb'
      _ ≤ L * C * w R * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geometric_sum_le r hr hr1 R)
          (mul_nonneg (mul_nonneg hL0 hC) (hw R))
      _ = _ := by ring

lemma fixed_grid_majorant (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C r : ℝ, ∃ w : ℕ → ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      (∀ k, 0 ≤ w k) ∧ Summable w ∧
      ∀ (kind : Kind) (m : ℤ), ∀ z ∈ UpperWindow.templates M m n δ x.1, ∀ j k : ℕ,
        ‖UpperContour.kernel kind M m n h ℓ p x (UpperContour.translate M x.1 z j k)‖ ≤
          C * r ^ j * w k := by
  obtain ⟨C, D, hC, hD, hb⟩ := fixed_template_bounds_integer M h ℓ p n ψ σ ρ δ hc x hx
  let c := (M 1 0).toNat
  let rA := ‖UpperWindow.A ℓ x.1 x.2.1‖ ^ c
  let rB := ‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ c
  have hcpos : 0 < c := by dsimp [c]; have := hc.1; omega
  obtain ⟨hA0, hA1, hB0, hB1⟩ := UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx
  have hrA0 : 0 ≤ rA := pow_nonneg (norm_nonneg _) _
  have hrA1 : rA < 1 := pow_lt_one₀ hA0.le hA1 hcpos.ne'
  have hrB0 : 0 ≤ rB := pow_nonneg (norm_nonneg _) _
  have hrB1 : rB < 1 := pow_lt_one₀ hB0.le hB1 hcpos.ne'
  have hq := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have hqs := quadratic_summable c hcpos D ‖e (etaMobius M x.1)‖ hD
    hq.2.2.2.2.2.2.1 hq.2.2.2.2.2.2.2
  have hqn : ∀ k, 0 ≤ quadraticWeight c D ‖e (etaMobius M x.1)‖ k := by
    intro k
    unfold quadraticWeight
    positivity
  refine ⟨C, rA, fun k => rB ^ k + quadraticWeight c D ‖e (etaMobius M x.1)‖ k,
    hC.le, hrA0, hrA1, (fun k => add_nonneg (pow_nonneg hrB0 k) (hqn k)),
    (summable_geometric_of_lt_one hrB0 hrB1).add hqs, ?_⟩
  intro kind m z hz j k
  cases kind
  · exact (hb m z hz j k).2.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (pow_nonneg hrB0 k)) (mul_nonneg hC.le (pow_nonneg hrA0 j)))
  · exact (hb m z hz j k).1.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (hqn k)) (mul_nonneg hC.le (pow_nonneg hrA0 j)))

lemma four_envelopes_tendsto (C r L : ℝ) (w : ℕ → ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hws : Summable w) :
    Tendsto (fun R : ℕ => ∑' k : ℕ, C * w (R + k)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℕ => ∑' j : ℕ, L * C * w 0 * r ^ (R + j)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℕ => C * r ^ R * (∑' k : ℕ, w k)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℕ => L * C / (1 - r) * w R) atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_comm] using tendsto_sum_nat_add (fun k => C * w k)
  · simpa only [Nat.add_comm] using tendsto_sum_nat_add (fun j => L * C * w 0 * r ^ j)
  · simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1)).mul
      (tendsto_const_nhds (x := ∑' k : ℕ, w k))
  · simpa using (tendsto_const_nhds (x := L * C / (1 - r))).mul hws.tendsto_atTop_zero

end SICLean.L4.UpperContourSidesAux
