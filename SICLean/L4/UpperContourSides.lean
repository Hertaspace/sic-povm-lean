import SICLean.L4.UpperContourBounds
import SICLean.L4.UpperContourSidesAux

set_option autoImplicit false

/-!
# Each of the four finite edge integrals and its own limit

The remote bounds retain the finite
geometric sums, the discrete Gaussian sum, and the T-edge Jacobian ‖T‖.
Quantitative estimates take the already-proved template bounds explicitly;
the convergence exports require only the original window inputs. [RW26, pp. 28--29].
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContour
open UpperContourSidesAux

/--
Four genuinely finite integrable pullbacks, before any limit; [RW26, pp. 28--29].
-/
theorem sides_intervalIntegrable (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) :
    let f := kernel kind M m n h ℓ p x
    let v := UpperWindow.base M m n δ x.1
    let T := etaDenom M x.1
    IntervalIntegrable (fun t : ℝ => f (v + (t : ℂ))) volume (R : ℝ) 0 ∧
      IntervalIntegrable (rayPullback f v T) volume 0 (R : ℝ) ∧
      IntervalIntegrable (fun t : ℝ => f (v + (R : ℂ) * T + (t : ℂ))) volume 0 (R : ℝ) ∧
      IntervalIntegrable (fun t : ℝ => f (v + (R : ℂ) + (t : ℂ) * T) * T) volume (R : ℝ) 0 := by
  have hs := side_continuous kind M h ℓ p m n ψ σ ρ δ hc x hx R
  dsimp only at hs ⊢
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  exact ⟨(hs.1.intervalIntegrable_of_Icc hR).symm,
    hs.2.1.intervalIntegrable_of_Icc hR,
    hs.2.2.1.intervalIntegrable_of_Icc hR,
    (hs.2.2.2.intervalIntegrable_of_Icc hR).symm⟩

/--
Absolute integrability of both rays of V, for each kernel separately; [RW26, pp. 28--29].
-/
theorem v_rays_integrable (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    let f := kernel kind M m n h ℓ p x
    let v := UpperWindow.base M m n δ x.1
    IntegrableOn (rayPullback f v 1) (Ioi 0) ∧
      IntegrableOn (rayPullback f v (etaDenom M x.1)) (Ioi 0) := by
  obtain ⟨C, r, w, hC, hr, hr1, hw, hws, hb⟩ :=
    fixed_grid_majorant M h ℓ p n ψ σ ρ δ hc x hx
  have he := four_side_estimates kind M h ℓ p m n ψ σ ρ δ hc x hx
    C r ‖etaDenom M x.1‖ w hC hr hr1 hw hws le_rfl (hb kind m)
  exact ⟨he.1, he.2.1⟩

/--
Incoming real edge has a minus sign. Integer R tends to infinity; [RW26, pp. 28--29].
-/
theorem firstSide_tendsto (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => firstSide (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) R) atTop
      (𝓝 (-rayIntegral (kernel kind M m n h ℓ p x) (UpperWindow.base M m n δ x.1) 1)) := by
  have hi := (v_rays_integrable kind M h ℓ p m n ψ σ ρ δ hc x hx).1
  have ht := (intervalIntegral_tendsto_integral_Ioi 0 hi
    (tendsto_natCast_atTop_atTop (R := ℝ))).neg
  convert ht using 1
  · funext R
    simp only [firstSide, rayPullback, mul_one]
    exact intervalIntegral.integral_symm _ _
  · rfl

/--
Outgoing T edge, including its Jacobian; [RW26, pp. 28--29].
-/
theorem secondSide_tendsto (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => secondSide (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (etaDenom M x.1) R) atTop
      (𝓝 (rayIntegral (kernel kind M m n h ℓ p x)
        (UpperWindow.base M m n δ x.1) (etaDenom M x.1))) := by
  exact intervalIntegral_tendsto_integral_Ioi 0
    (v_rays_integrable kind M h ℓ p m n ψ σ ρ δ hc x hx).2
    tendsto_natCast_atTop_atTop

/--
Exact unit-template decomposition, not an estimate on kernel values; [RW26, pp. 28--29].
-/
theorem firstSide_unit_decomposition (f : ℂ → ℂ) (v : ℂ) (R : ℕ)
    (hf : ContinuousOn f ((fun t : ℝ => v + (t : ℂ)) '' Icc 0 (R : ℝ))) :
    firstSide f v R = -(∑ k ∈ Finset.range R,
      ∫ u : ℝ in 0..1, f (v + (k : ℂ) + (u : ℂ))) := by
  have hg : ContinuousOn (fun t : ℝ => f (v + (t : ℂ))) (Icc 0 (R : ℝ)) :=
    hf.comp (by fun_prop) (fun t ht => mem_image_of_mem _ ht)
  rw [firstSide, intervalIntegral.integral_symm]
  simpa [Complex.ofReal_add, add_assoc] using
    congrArg Neg.neg (integral_units (fun t : ℝ => f (v + (t : ℂ))) R hg)

/--
Exact T-template decomposition including T; [RW26, pp. 28--29].
-/
theorem secondSide_unit_decomposition (f : ℂ → ℂ) (v T : ℂ) (R : ℕ)
    (hf : ContinuousOn f ((fun t : ℝ => v + (t : ℂ) * T) '' Icc 0 (R : ℝ))) :
    secondSide f v T R = ∑ j ∈ Finset.range R,
      ∫ u : ℝ in 0..1, f (v + ((j : ℂ) + (u : ℂ)) * T) * T := by
  have hg : ContinuousOn (fun t : ℝ => f (v + (t : ℂ) * T) * T) (Icc 0 (R : ℝ)) :=
    (hf.comp (by fun_prop) (fun t ht => mem_image_of_mem _ ht)).mul_const T
  simpa [secondSide, Complex.ofReal_add] using
    integral_units (fun t : ℝ => f (v + (t : ℂ) * T) * T) R hg

/--
Third edge: retain the finite geometric sum and its closed bound; [RW26, pp. 28--29].
-/
theorem thirdSide_ratio_bound (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (M₀ rA rB : ℝ)
    (hM₀ : 0 < M₀) (hA : 0 < rA ∧ rA < 1) (hB : 0 < rB ∧ rB < 1)
    (hb : ∀ z ∈ UpperWindow.templates M m n δ x.1, ∀ j k : ℕ,
      ‖kernel .ratio M m n h ℓ p x (translate M x.1 z j k)‖ ≤ M₀ * rA ^ j * rB ^ k)
    (R : ℕ) :
    ‖thirdSide (kernel .ratio M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
      (etaDenom M x.1) R‖ ≤ M₀ * rA ^ R * (∑ k ∈ Finset.range R, rB ^ k) ∧
      M₀ * rA ^ R * (∑ k ∈ Finset.range R, rB ^ k) ≤ M₀ * rA ^ R / (1 - rB) := by
  constructor
  · have hi := norm_integral_units_le
      (fun t : ℝ => kernel .ratio M m n h ℓ p x
        (UpperWindow.base M m n δ x.1 + (R : ℂ) * etaDenom M x.1 + (t : ℂ)))
      (fun k => M₀ * rA ^ R * rB ^ k) R
      (side_continuous .ratio M h ℓ p m n ψ σ ρ δ hc x hx R).2.2.1
    have hb' : ∀ k < R, ∀ u ∈ Icc (0 : ℝ) 1,
        ‖kernel .ratio M m n h ℓ p x (UpperWindow.base M m n δ x.1 +
          (R : ℂ) * etaDenom M x.1 + (((k : ℝ) + u : ℝ) : ℂ))‖ ≤
          M₀ * rA ^ R * rB ^ k := by
      intro k hk u hu
      convert hb (UpperWindow.base M m n δ x.1 + (u : ℂ))
        (Or.inl ⟨u, hu, rfl⟩) R k using 1 <;> congr 1 <;>
        simp only [translate, Complex.ofReal_add, Complex.ofReal_natCast] <;> ring
    simpa [thirdSide, Finset.mul_sum] using hi hb'
  · simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (geometric_sum_le rB hB.1.le hB.2 R)
        (mul_nonneg hM₀.le (pow_nonneg hA.1.le R))

/--
Fourth edge: ‖T‖ must not be dropped; [RW26, pp. 28--29].
-/
theorem fourthSide_ratio_bound (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (M₀ rA rB : ℝ)
    (hM₀ : 0 < M₀) (hA : 0 < rA ∧ rA < 1) (hB : 0 < rB ∧ rB < 1)
    (hb : ∀ z ∈ UpperWindow.templates M m n δ x.1, ∀ j k : ℕ,
      ‖kernel .ratio M m n h ℓ p x (translate M x.1 z j k)‖ ≤ M₀ * rA ^ j * rB ^ k)
    (R : ℕ) :
    ‖fourthSide (kernel .ratio M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
      (etaDenom M x.1) R‖ ≤
      ‖etaDenom M x.1‖ * M₀ * rB ^ R * (∑ j ∈ Finset.range R, rA ^ j) ∧
      ‖etaDenom M x.1‖ * M₀ * rB ^ R * (∑ j ∈ Finset.range R, rA ^ j) ≤
        ‖etaDenom M x.1‖ * M₀ * rB ^ R / (1 - rA) := by
  constructor
  · rw [fourthSide, intervalIntegral.integral_symm, norm_neg]
    have hi := norm_integral_units_le
      (fun t : ℝ => kernel .ratio M m n h ℓ p x
        (UpperWindow.base M m n δ x.1 + (R : ℂ) + (t : ℂ) * etaDenom M x.1) *
          etaDenom M x.1)
      (fun j => ‖etaDenom M x.1‖ * M₀ * rB ^ R * rA ^ j) R
      (side_continuous .ratio M h ℓ p m n ψ σ ρ δ hc x hx R).2.2.2
    have hb' : ∀ j < R, ∀ u ∈ Icc (0 : ℝ) 1,
        ‖kernel .ratio M m n h ℓ p x (UpperWindow.base M m n δ x.1 + (R : ℂ) +
          (((j : ℝ) + u : ℝ) : ℂ) * etaDenom M x.1) * etaDenom M x.1‖ ≤
          ‖etaDenom M x.1‖ * M₀ * rB ^ R * rA ^ j := by
      intro j hj u hu
      have hb0 := hb (UpperWindow.base M m n δ x.1 + (u : ℂ) * etaDenom M x.1)
        (Or.inr ⟨u, hu, rfl⟩) j R
      have heq : UpperWindow.base M m n δ x.1 + (R : ℂ) +
          (((j : ℝ) + u : ℝ) : ℂ) * etaDenom M x.1 =
          translate M x.1 (UpperWindow.base M m n δ x.1 +
            (u : ℂ) * etaDenom M x.1) j R := by
        simp only [translate, Complex.ofReal_add, Complex.ofReal_natCast]
        ring
      rw [norm_mul, heq]
      nlinarith [mul_le_mul_of_nonneg_right hb0 (norm_nonneg (etaDenom M x.1))]
    simpa [Finset.mul_sum] using hi hb'
  · simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (geometric_sum_le rA hA.1.le hA.2 R)
        (mul_nonneg (mul_nonneg (norm_nonneg _) hM₀.le) (pow_nonneg hB.1.le R))

/--
Third single edge: actual |Q| and its entire summable quadratic series; [RW26, pp. 28--29].
-/
theorem thirdSide_single_bound (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (M₀ D rA : ℝ)
    (hM₀ : 0 < M₀) (hD : 0 < D) (hA : 0 < rA ∧ rA < 1)
    (hb : ∀ z ∈ UpperWindow.templates M m n δ x.1, ∀ j k : ℕ,
      ‖kernel .single M m n h ℓ p x (translate M x.1 z j k)‖ ≤
        M₀ * rA ^ j * quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k)
    (R : ℕ) :
    ‖thirdSide (kernel .single M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
      (etaDenom M x.1) R‖ ≤ M₀ * rA ^ R *
        (∑ k ∈ Finset.range R, quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k) ∧
      M₀ * rA ^ R *
        (∑ k ∈ Finset.range R, quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k) ≤
      M₀ * rA ^ R * (∑' k : ℕ, quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k) := by
  constructor
  · have hi := norm_integral_units_le
      (fun t : ℝ => kernel .single M m n h ℓ p x
        (UpperWindow.base M m n δ x.1 + (R : ℂ) * etaDenom M x.1 + (t : ℂ)))
      (fun k => M₀ * rA ^ R * quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k) R
      (side_continuous .single M h ℓ p m n ψ σ ρ δ hc x hx R).2.2.1
    have hb' : ∀ k < R, ∀ u ∈ Icc (0 : ℝ) 1,
        ‖kernel .single M m n h ℓ p x (UpperWindow.base M m n δ x.1 +
          (R : ℂ) * etaDenom M x.1 + (((k : ℝ) + u : ℝ) : ℂ))‖ ≤
          M₀ * rA ^ R * quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k := by
      intro k hk u hu
      convert hb (UpperWindow.base M m n δ x.1 + (u : ℂ))
        (Or.inl ⟨u, hu, rfl⟩) R k using 1 <;> congr 1 <;>
        simp only [translate, Complex.ofReal_add, Complex.ofReal_natCast] <;> ring
    simpa [thirdSide, Finset.mul_sum] using hi hb'
  · have hq := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
    have hcpos : 0 < (M 1 0).toNat := by have := hc.1; omega
    have hs := quadratic_summable (M 1 0).toNat hcpos D
      ‖e (etaMobius M x.1)‖ hD hq.2.2.2.2.2.2.1 hq.2.2.2.2.2.2.2
    exact mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum (Finset.range R) (fun k _ => by
        unfold quadraticWeight
        positivity)) (mul_nonneg hM₀.le (pow_nonneg hA.1.le R))

/--
Fourth single edge: the finite j sum followed by its geometric bound; [RW26, pp. 28--29].
-/
theorem fourthSide_single_bound (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (M₀ D rA : ℝ)
    (hM₀ : 0 < M₀) (hD : 0 < D) (hA : 0 < rA ∧ rA < 1)
    (hb : ∀ z ∈ UpperWindow.templates M m n δ x.1, ∀ j k : ℕ,
      ‖kernel .single M m n h ℓ p x (translate M x.1 z j k)‖ ≤
        M₀ * rA ^ j * quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k)
    (R : ℕ) :
    ‖fourthSide (kernel .single M m n h ℓ p x) (UpperWindow.base M m n δ x.1)
      (etaDenom M x.1) R‖ ≤ ‖etaDenom M x.1‖ * M₀ *
        (∑ j ∈ Finset.range R, rA ^ j) *
          quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ R ∧
      ‖etaDenom M x.1‖ * M₀ * (∑ j ∈ Finset.range R, rA ^ j) *
          quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ R ≤
        ‖etaDenom M x.1‖ * M₀ / (1 - rA) *
          quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ R := by
  constructor
  · rw [fourthSide, intervalIntegral.integral_symm, norm_neg]
    have hi := norm_integral_units_le
      (fun t : ℝ => kernel .single M m n h ℓ p x
        (UpperWindow.base M m n δ x.1 + (R : ℂ) + (t : ℂ) * etaDenom M x.1) *
          etaDenom M x.1)
      (fun j => ‖etaDenom M x.1‖ * M₀ *
        quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ R * rA ^ j) R
      (side_continuous .single M h ℓ p m n ψ σ ρ δ hc x hx R).2.2.2
    have hb' : ∀ j < R, ∀ u ∈ Icc (0 : ℝ) 1,
        ‖kernel .single M m n h ℓ p x (UpperWindow.base M m n δ x.1 + (R : ℂ) +
          (((j : ℝ) + u : ℝ) : ℂ) * etaDenom M x.1) * etaDenom M x.1‖ ≤
          ‖etaDenom M x.1‖ * M₀ *
            quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ R * rA ^ j := by
      intro j hj u hu
      have hb0 := hb (UpperWindow.base M m n δ x.1 + (u : ℂ) * etaDenom M x.1)
        (Or.inr ⟨u, hu, rfl⟩) j R
      have heq : UpperWindow.base M m n δ x.1 + (R : ℂ) +
          (((j : ℝ) + u : ℝ) : ℂ) * etaDenom M x.1 =
          translate M x.1 (UpperWindow.base M m n δ x.1 +
            (u : ℂ) * etaDenom M x.1) j R := by
        simp only [translate, Complex.ofReal_add, Complex.ofReal_natCast]
        ring
      rw [norm_mul, heq]
      nlinarith [mul_le_mul_of_nonneg_right hb0 (norm_nonneg (etaDenom M x.1))]
    have heq : (∑ j ∈ Finset.range R, ‖etaDenom M x.1‖ * M₀ *
        quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ R * rA ^ j) =
        ‖etaDenom M x.1‖ * M₀ * (∑ j ∈ Finset.range R, rA ^ j) *
          quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ R := by
      rw [← Finset.mul_sum]
      ring
    exact (hi hb').trans_eq heq
  · have hsum := mul_le_mul_of_nonneg_left (geometric_sum_le rA hA.1.le hA.2 R)
      (mul_nonneg (norm_nonneg (etaDenom M x.1)) hM₀.le)
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hsum
      (show 0 ≤ quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ R by
        unfold quadraticWeight
        positivity)

/--
Third finite integral tends to zero for each kind; [RW26, pp. 28--29].
-/
theorem thirdSide_tendsto_zero (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => thirdSide (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (etaDenom M x.1) R) atTop (𝓝 0) := by
  obtain ⟨C, r, w, hC, hr, hr1, hw, hws, hb⟩ :=
    fixed_grid_majorant M h ℓ p n ψ σ ρ δ hc x hx
  have he := four_side_estimates kind M h ℓ p m n ψ σ ρ δ hc x hx
    C r ‖etaDenom M x.1‖ w hC hr hr1 hw hws le_rfl (hb kind m)
  exact squeeze_zero_norm (fun R => (he.2.2 R).2.2.1)
    (four_envelopes_tendsto C r ‖etaDenom M x.1‖ w hr hr1 hws).2.2.1

/--
Fourth finite integral tends to zero, independently of the third; [RW26, pp. 28--29].
-/
theorem fourthSide_tendsto_zero (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => fourthSide (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (etaDenom M x.1) R) atTop (𝓝 0) := by
  obtain ⟨C, r, w, hC, hr, hr1, hw, hws, hb⟩ :=
    fixed_grid_majorant M h ℓ p n ψ σ ρ δ hc x hx
  have he := four_side_estimates kind M h ℓ p m n ψ σ ρ δ hc x hx
    C r ‖etaDenom M x.1‖ w hC hr hr1 hw hws le_rfl (hb kind m)
  exact squeeze_zero_norm (fun R => (he.2.2 R).2.2.2)
    (four_envelopes_tendsto C r ‖etaDenom M x.1‖ w hr hr1 hws).2.2.2

/--
Sum only after the four separate limits; [RW26, pp. 28--29].
-/
theorem clockwiseBoundary_tendsto (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => clockwiseBoundary (kernel kind M m n h ℓ p x)
      (UpperWindow.base M m n δ x.1) (etaDenom M x.1) R) atTop
      (𝓝 (vIntegral (kernel kind M m n h ℓ p x)
        (UpperWindow.base M m n δ x.1) (etaDenom M x.1))) := by
  simpa [clockwiseBoundary, vIntegral] using
    (((firstSide_tendsto kind M h ℓ p m n ψ σ ρ δ hc x hx).add
      (secondSide_tendsto kind M h ℓ p m n ψ σ ρ δ hc x hx)).add
      (thirdSide_tendsto_zero kind M h ℓ p m n ψ σ ρ δ hc x hx)).add
      (fourthSide_tendsto_zero kind M h ℓ p m n ψ σ ρ δ hc x hx)

/--
Uniformity over the same compact set, all finite residue classes and
both kernels, with one cutoff before x,m,kind; [RW26, pp. 28--29].
-/
theorem compact_four_side_limits (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ R : ℕ, N ≤ R →
      ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat, ∀ kind : Kind,
      let f := kernel kind M (m : ℤ) n h ℓ p x
      let v := UpperWindow.base M (m : ℤ) n δ x.1
      let T := etaDenom M x.1
      ‖firstSide f v R + rayIntegral f v 1‖ < ε ∧
        ‖secondSide f v T R - rayIntegral f v T‖ < ε ∧
        ‖thirdSide f v T R‖ < ε ∧ ‖fourthSide f v T R‖ < ε := by
  obtain ⟨C, D, rA, rB, hC, hD, hA0, hA1, hB0, hB1, hb⟩ :=
    compact_template_bounds M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨Q, a, hQ0, hQ1, ha, hqs, hqb⟩ :=
    compact_quadratic_domination M h ℓ p ψ σ ρ δ hc K hK hKU D hD
  obtain ⟨η, L, q, hη, hL, hq, hq1, hp⟩ :=
    UpperWindow.compact_parameter_bounds M h ℓ p ψ σ ρ δ hc K hK hKU
  let w : ℕ → ℝ := fun k => rB ^ k + quadraticWeight (M 1 0).toNat D Q k
  have hqn : ∀ k, 0 ≤ quadraticWeight (M 1 0).toNat D Q k := by
    intro k
    unfold quadraticWeight
    positivity
  have hwn : ∀ k, 0 ≤ w k := fun k => add_nonneg (pow_nonneg hB0.le k) (hqn k)
  have hws : Summable w := (summable_geometric_of_lt_one hB0.le hB1).add hqs
  have hbound : ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat, ∀ kind : Kind,
      ∀ z ∈ UpperWindow.templates M (m : ℤ) n δ x.1, ∀ j k : ℕ,
      ‖kernel kind M (m : ℤ) n h ℓ p x (translate M x.1 z j k)‖ ≤ C * rA ^ j * w k := by
    intro x hx m hm kind z hz j k
    have hcoef : 0 ≤ C * rA ^ j := mul_nonneg hC.le (pow_nonneg hA0.le j)
    cases kind
    · exact (hb x hx m hm z hz j k).2.trans (mul_le_mul_of_nonneg_left
        (((hqb x hx).2 k).trans (le_add_of_nonneg_left (pow_nonneg hB0.le k))) hcoef)
    · exact (hb x hx m hm z hz j k).1.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (hqn k)) hcoef)
  obtain ⟨ht1, ht2, ht3, ht4⟩ := four_envelopes_tendsto C rA L w hA0.le hA1 hws
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((ht1.eventually (gt_mem_nhds hε)).and
      ((ht2.eventually (gt_mem_nhds hε)).and
        ((ht3.eventually (gt_mem_nhds hε)).and (ht4.eventually (gt_mem_nhds hε)))))
  refine ⟨N, ?_⟩
  intro R hR x hx m hm kind
  have hcap : ‖etaDenom M x.1‖ ≤ L := by
    rcases hp x hx with ⟨_, _, _, _, _, hcap, _⟩
    exact hcap
  have he := four_side_estimates kind M h ℓ p (m : ℤ) n ψ σ ρ δ hc x (hKU hx)
    C rA L w hC.le hA0.le hA1 hwn hws hcap (hbound x hx m hm kind)
  obtain ⟨h1, h2, h3, h4⟩ := he.2.2 R
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hN R hR
  exact ⟨h1.trans_lt hl1, h2.trans_lt hl2, h3.trans_lt hl3, h4.trans_lt hl4⟩

#check sides_intervalIntegrable
#check thirdSide_single_bound
#check fourthSide_ratio_bound
#check firstSide_tendsto
#check fourthSide_tendsto_zero
#check compact_four_side_limits

end SICLean.L4.UpperContour
