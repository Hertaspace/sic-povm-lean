import SICLean.L4.UpperContourBounds
import SICLean.L4.UpperContourUpperArcAux

set_option autoImplicit false

/-!
# Outgoing upper-ray rotation at arbitrary real radii

The actual integral includes dz/dθ=i r exp(iθ).
The q-product bounds cover the full closed wedge, and Green's formula
gives the finite rotation before the real-radius limit is taken.
The finite rotation uses the upper circular connecting arc. [RW26, pp. 28--29].
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContour

open SICLean.L4.UpperContourUpperArcAux

def upperArcIntegral (f : ℂ → ℂ) (v T : ℂ) (ψ r : ℝ) : ℂ :=
  arcIntegral f v r T.arg (Real.pi / 2 + ψ)

/--
Real differentiation includes the full radius; [RW26, pp. 28--29].
-/
theorem arcPoint_hasDerivAt (v : ℂ) (r θ : ℝ) :
    HasDerivAt (arcPoint v r) (Complex.I * (r : ℂ) * UpperWindow.rotation θ) θ := by
  change HasDerivAt (fun θ : ℝ => v + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    (Complex.I * (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) θ
  have hrot := ((Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul Complex.I).cexp
  simpa [arcPoint, UpperWindow.rotation, mul_comm, mul_left_comm, mul_assoc] using
    (hrot.const_mul (r : ℂ)).const_add v

/--
Arc-length factor for a nonnegative real radius; [RW26, pp. 28--29].
-/
theorem norm_arcPullback (f : ℂ → ℂ) (v : ℂ) (r θ : ℝ) (hr : 0 ≤ r) :
    ‖arcPullback f v r θ‖ = r * ‖f (arcPoint v r θ)‖ := by
  simp [arcPullback, UpperWindow.rotation, Complex.norm_exp, abs_of_nonneg hr, mul_comm]

/--
Original Φ factors and their inverses are bounded on the entire
upper wedge, including its endpoints and radius zero; [RW26, pp. 28--29]. Constants precede every
varying parameter.
-/
theorem compact_upper_phi_bounds (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ r : ℝ, 0 ≤ r → ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      let z := arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ
      ‖modularPhi M ((m : ℤ) + 1) n z x.1‖ ≤ C ∧
        ‖(modularPhi M ((m : ℤ) + 1) n z x.1)⁻¹‖ ≤ C ∧
        ‖modularPhi M ((m : ℤ) + p) n (z + x.2.2) x.1‖ ≤ C ∧
        ‖(modularPhi M ((m : ℤ) + p) n (z + x.2.2) x.1)⁻¹‖ ≤ C := by
  exact wedge_compact_upper_phi_bounds M h ℓ p n ψ σ ρ δ hc K hK hKU

/--
Linear upper decay from s/T, for both existing kernels; [RW26, pp. 28--29].
-/
theorem compact_upper_kernel_bound (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat, ∀ kind : Kind, ∀ r : ℝ, 0 ≤ r →
      ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      ‖kernel kind M (m : ℤ) n h ℓ p x
        (arcPoint (UpperWindow.base M (m : ℤ) n δ x.1) r θ)‖ ≤
        C * Real.exp (-2 * Real.pi * lam * r) := by
  exact wedge_compact_upper_kernel_bound M h ℓ p n ψ σ ρ δ hc K hK hKU

/--
Pointwise pulled-back majorant, including the radius; [RW26, pp. 28--29].
-/
theorem compact_upper_arc_pullback_bound (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat, ∀ kind : Kind, ∀ r : ℝ, 0 ≤ r →
      ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      ‖arcPullback (kernel kind M (m : ℤ) n h ℓ p x)
        (UpperWindow.base M (m : ℤ) n δ x.1) r θ‖ ≤
        C * r * Real.exp (-2 * Real.pi * lam * r) := by
  obtain ⟨C, lam, hC, hlam, hbound⟩ :=
    compact_upper_kernel_bound M h ℓ p n ψ σ ρ δ hc K hK hKU
  refine ⟨C, lam, hC, hlam, ?_⟩
  intro x hx m hm kind r hr θ hθ
  rw [norm_arcPullback _ _ _ _ hr]
  calc
    _ ≤ r * (C * Real.exp (-2 * Real.pi * lam * r)) :=
      mul_le_mul_of_nonneg_left (hbound x hx m hm kind r hr θ hθ) hr
    _ = _ := by ring

/--
Actual finite arc integral exists; [RW26, pp. 28--29].
-/
theorem upperArc_intervalIntegrable (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r : ℝ) (hr : 0 ≤ r) :
    IntervalIntegrable (arcPullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) r) volume (etaDenom M x.1).arg (Real.pi / 2 + ψ) := by
  have hab : (etaDenom M x.1).arg ≤ Real.pi / 2 + ψ := by
    linarith [hx.1.2.2, Real.pi_pos]
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro θ hθ
  have hf := (kernel_sector_differentiable kind M h ℓ p m n ψ σ ρ δ
    hc x hx r θ hr (Or.inl hθ)).continuousAt
  have hp := (arcPoint_hasDerivAt (UpperWindow.base M m n δ x.1) r θ).continuousAt
  have hrot : ContinuousAt UpperWindow.rotation θ := by
    unfold UpperWindow.rotation
    fun_prop
  exact ((hf.comp hp).mul ((continuousAt_const.mul continuousAt_const).mul hrot)).continuousWithinAt

/--
Quantitative O(r exp(-kr)) with the actual angular length retained; [RW26, pp. 28--29].
-/
theorem compact_upperArc_bound (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ ∀ x ∈ K,
      ∀ m ∈ Finset.range (M 1 0).toNat, ∀ kind : Kind, ∀ r : ℝ, 0 ≤ r →
      ‖upperArcIntegral (kernel kind M (m : ℤ) n h ℓ p x)
        (UpperWindow.base M (m : ℤ) n δ x.1) (etaDenom M x.1) ψ r‖ ≤
        (Real.pi / 2 + ψ - (etaDenom M x.1).arg) * C * r *
          Real.exp (-2 * Real.pi * lam * r) := by
  obtain ⟨C, lam, hC, hlam, hbound⟩ :=
    compact_upper_arc_pullback_bound M h ℓ p n ψ σ ρ δ hc K hK hKU
  refine ⟨C, lam, hC, hlam, ?_⟩
  intro x hx m hm kind r hr
  have hab : (etaDenom M x.1).arg ≤ Real.pi / 2 + ψ := by
    have harg := (hKU hx).1.2.2
    linarith [Real.pi_pos]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (etaDenom M x.1).arg) (b := Real.pi / 2 + ψ)
    (f := arcPullback (kernel kind M (m : ℤ) n h ℓ p x)
      (UpperWindow.base M (m : ℤ) n δ x.1) r)
    (C := C * r * Real.exp (-2 * Real.pi * lam * r))
    (fun θ hθ => hbound x hx m hm kind r hr θ (by
      rw [uIoc_of_le hab] at hθ
      exact ⟨hθ.1.le, hθ.2⟩))
  simpa only [upperArcIntegral, arcIntegral, abs_of_nonneg (sub_nonneg.mpr hab),
    mul_assoc, mul_left_comm, mul_comm] using hb

/--
Radius runs through ℝ atTop, not just integers; [RW26, pp. 28--29].
-/
theorem upperArc_tendsto_zero (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (upperArcIntegral (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (etaDenom M x.1) ψ) atTop (𝓝 0) := by
  obtain ⟨C, lam, hC, hlam, hbound⟩ :=
    wedge_fixed_m_upper_kernel_bound M h ℓ p m n ψ σ ρ δ hc {x}
      isCompact_singleton (by simpa only [singleton_subset_iff] using hx)
  apply arcIntegral_tendsto_zero_of_exp_bound _ _ _ _ C (2 * Real.pi * lam)
    (by linarith [hx.1.2.2, Real.pi_pos]) (by positivity)
  intro r hr θ hθ
  simpa only [neg_mul] using hbound x (mem_singleton x) kind r hr θ hθ

/--
One real cutoff for all parameters, classes and kernels; [RW26, pp. 28--29].
-/
theorem compact_upperArc_limit (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
      ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat, ∀ kind : Kind,
      ‖upperArcIntegral (kernel kind M (m : ℤ) n h ℓ p x)
        (UpperWindow.base M (m : ℤ) n δ x.1) (etaDenom M x.1) ψ r‖ < ε := by
  obtain ⟨C, lam, hC, hlam, hbound⟩ :=
    compact_upperArc_bound M h ℓ p n ψ σ ρ δ hc K hK hKU
  have hexp : Tendsto (fun r : ℝ => r * Real.exp (-2 * Real.pi * lam * r))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one, neg_mul, mul_assoc] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 * Real.pi * lam)
        (by positivity)
  have hlim : Tendsto (fun r : ℝ => (Real.pi / 2 + ψ) * C * r *
      Real.exp (-2 * Real.pi * lam * r)) atTop (𝓝 0) := by
    convert hexp.const_mul ((Real.pi / 2 + ψ) * C) using 1 <;> simp [mul_assoc]
  intro ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hr x hx m hm kind
  have hr0 : 0 ≤ r := le_trans (by positivity : (0 : ℝ) ≤ max 1 R) hr
  refine lt_of_le_of_lt (hbound x hx m hm kind r hr0) ?_
  calc
    (Real.pi / 2 + ψ - (etaDenom M x.1).arg) * C * r *
        Real.exp (-2 * Real.pi * lam * r) ≤
        (Real.pi / 2 + ψ) * C * r * Real.exp (-2 * Real.pi * lam * r) := by
      have harg : 0 < (etaDenom M x.1).arg := (hKU hx).1.2.1
      gcongr
      linarith
    _ < ε := hR r (le_trans (le_max_right _ _) hr)

/--
Exact finite wedge ledger: outgoing old ray + CCW arc - new ray =0.
No poles are crossed; [RW26, pp. 28--29].
-/
theorem finite_upper_rotation (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (r : ℝ) (hr : 0 ≤ r) :
    let f := kernel kind M m n h ℓ p x
    let v := UpperWindow.base M m n δ x.1
    rayFinite f v (UpperWindow.rotation (etaDenom M x.1).arg) r +
      upperArcIntegral f v (etaDenom M x.1) ψ r -
      rayFinite f v (UpperWindow.rotation (Real.pi / 2 + ψ)) r = 0 := by
  exact SICLean.L4.UpperContourUpperArcAux.finite_upper_rotation
    kind M h ℓ p m n ψ σ ρ δ hc x hx r hr

/--
Reparametrize a ray by a positive real scale. This accounts for the
fact that the second rectangle edge has physical radius R‖T‖; [RW26, pp. 28--29].
-/
theorem ray_positive_rescale (f : ℂ → ℂ) (v d : ℂ) (a : ℝ) (ha : 0 < a)
    (hf : IntegrableOn (rayPullback f v d) (Ioi 0)) :
    IntegrableOn (rayPullback f v ((a : ℂ) * d)) (Ioi 0) ∧
      rayIntegral f v ((a : ℂ) * d) = rayIntegral f v d := by
  have hscale : rayPullback f v ((a : ℂ) * d) =
      fun t : ℝ => a • rayPullback f v d (a * t) := by
    funext t
    simp only [rayPullback, Complex.ofReal_mul, Complex.real_smul,
      mul_assoc, mul_comm, mul_left_comm]
  constructor
  · have hcomp : IntegrableOn
        (fun t : ℝ => rayPullback f v d (a * t)) (Ioi 0) := by
      apply (integrableOn_Ioi_comp_mul_left_iff
        (rayPullback f v d) 0 ha).mpr
      simpa only [mul_zero] using hf
    rw [hscale]
    exact hcomp.smul a
  · simp only [rayIntegral, hscale]
    rw [integral_smul]
    simpa only [mul_zero] using
      integral_comp_mul_left_Ioi' (rayPullback f v d) 0 ha

/--
New upper ray is absolutely integrable; [RW26, pp. 28--29].
-/
theorem upper_rotated_ray_integrable (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    IntegrableOn (rayPullback (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (UpperWindow.rotation (Real.pi / 2 + ψ))) (Ioi 0) := by
  obtain ⟨C, lam, hC, hlam, hbound⟩ :=
    wedge_fixed_m_upper_kernel_bound M h ℓ p m n ψ σ ρ δ hc {x}
      isCompact_singleton (by simpa only [singleton_subset_iff] using hx)
  have hθ : Real.pi / 2 + ψ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ) :=
    ⟨by linarith [hx.1.2.2, Real.pi_pos], le_rfl⟩
  apply ray_integrable_of_exp_bound _ _ _ C (2 * Real.pi * lam) (by positivity)
  · intro t ht
    exact (kernel_sector_differentiable kind M h ℓ p m n ψ σ ρ δ
      hc x hx t _ ht (Or.inl hθ)).continuousAt
  · intro t ht
    simpa only [arcPoint, neg_mul] using
      hbound x (mem_singleton x) kind t ht _ hθ

/--
T-ray rotates to i exp(iψ) with its orientation preserved; [RW26, pp. 28--29].
-/
theorem upper_ray_rotation (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    rayIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (etaDenom M x.1) =
      rayIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
        (UpperWindow.rotation (Real.pi / 2 + ψ)) := by
  let f := kernel kind M m n h ℓ p x
  let v := UpperWindow.base M m n δ x.1
  let T := etaDenom M x.1
  obtain ⟨C, lam, hC, hlam, hbound⟩ :=
    wedge_fixed_m_upper_kernel_bound M h ℓ p m n ψ σ ρ δ hc {x}
      isCompact_singleton (by simpa only [singleton_subset_iff] using hx)
  have ha : T.arg ∈ Icc T.arg (Real.pi / 2 + ψ) :=
    ⟨le_rfl, by dsimp [T]; linarith [hx.1.2.2, Real.pi_pos]⟩
  have hold : IntegrableOn (rayPullback f v (UpperWindow.rotation T.arg)) (Ioi 0) := by
    apply ray_integrable_of_exp_bound _ _ _ C (2 * Real.pi * lam) (by positivity)
    · intro t ht
      exact (kernel_sector_differentiable kind M h ℓ p m n ψ σ ρ δ
        hc x hx t _ ht (Or.inl ha)).continuousAt
    · intro t ht
      simpa only [arcPoint, neg_mul] using
        hbound x (mem_singleton x) kind t ht _ ha
  have hnew := upper_rotated_ray_integrable kind M h ℓ p m n ψ σ ρ δ hc x hx
  have hlim := ((rayFinite_tendsto f v _ hold).add
    (upperArc_tendsto_zero kind M h ℓ p m n ψ σ ρ δ hc x hx)).sub
      (rayFinite_tendsto f v _ hnew)
  have hzero : Tendsto (fun r : ℝ => rayFinite f v (UpperWindow.rotation T.arg) r +
      upperArcIntegral f v T ψ r - rayFinite f v (UpperWindow.rotation (Real.pi / 2 + ψ)) r)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact (finite_upper_rotation kind M h ℓ p m n ψ σ ρ δ hc x hx r hr).symm
  have heq : rayIntegral f v (UpperWindow.rotation T.arg) =
      rayIntegral f v (UpperWindow.rotation (Real.pi / 2 + ψ)) := by
    have h := tendsto_nhds_unique hlim hzero
    simpa only [add_zero, sub_eq_zero] using h
  have hTne : T ≠ 0 :=
    (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).2.2.2.1
  have hscale := ray_positive_rescale f v (UpperWindow.rotation T.arg) ‖T‖
    (norm_pos_iff.mpr hTne) hold
  have hT : (‖T‖ : ℂ) * UpperWindow.rotation T.arg = T := by
    simpa only [UpperWindow.rotation, mul_comm Complex.I] using Complex.norm_mul_exp_arg_mul_I T
  rw [hT] at hscale
  exact hscale.2.trans heq

#print upperArcIntegral
#check arcPoint_hasDerivAt
#check compact_upperArc_bound
#check finite_upper_rotation
#check upper_ray_rotation

end SICLean.L4.UpperContour
