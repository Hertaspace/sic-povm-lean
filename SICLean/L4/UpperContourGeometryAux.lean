import SICLean.L4.UpperWindowCompact

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped Topology MatrixGroups

namespace SICLean.L4.UpperContourGeometryAux

/-- A positive shift smaller than one grid spacing selects the same integer box,
whether the outer endpoint is included or excluded. -/
theorem shifted_index_bounds (c : ℤ) (hc : 0 < c) (δ : ℝ)
    (hδ : 0 < δ) (hχ : (c : ℝ) * δ < 1) (R K : ℕ) :
    (δ + (K : ℝ) / (c : ℝ) < (R : ℝ) ↔ K < c.toNat * R) ∧
      (δ + (K : ℝ) / (c : ℝ) ≤ (R : ℝ) ↔ K < c.toNat * R) := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hcast : (c.toNat : ℝ) = (c : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hc.le
  have hmul : (δ + (K : ℝ) / (c : ℝ)) * (c : ℝ) =
      (c : ℝ) * δ + (K : ℝ) := by field_simp
  have hforward : δ + (K : ℝ) / (c : ℝ) ≤ (R : ℝ) → K < c.toNat * R := by
    intro h
    have h' := mul_le_mul_of_nonneg_right h hcR.le
    rw [hmul] at h'
    have hlt : (K : ℝ) < (c.toNat * R : ℕ) := by
      push_cast
      rw [hcast]
      nlinarith
    exact_mod_cast hlt
  have hbackward : K < c.toNat * R → δ + (K : ℝ) / (c : ℝ) < (R : ℝ) := by
    intro h
    have h' : ((K + 1 : ℕ) : ℝ) ≤ (c.toNat * R : ℕ) := by exact_mod_cast h
    push_cast at h'
    rw [hcast] at h'
    apply (mul_lt_mul_iff_of_pos_right hcR).mp
    rw [hmul]
    nlinarith
  exact ⟨⟨fun h => hforward h.le, hbackward⟩,
    ⟨hforward, fun h => (hbackward h).le⟩⟩

/-- Subdivide a nonnegative real edge into one template and integer translates. -/
theorem real_grid_divisor_free (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (t : ℝ) (ht : 0 ≤ t)
    (j : ℕ) :
    (UpperWindow.base M m n δ x.1 + (j : ℂ) * etaDenom M x.1 + (t : ℂ), x.1) ∈
        modularPhiNonvanishingDomain M (m + 1) n ∧
      (UpperWindow.base M m n δ x.1 + (j : ℂ) * etaDenom M x.1 + (t : ℂ) + x.2.2,
        x.1) ∈ modularPhiNonvanishingDomain M (m + p) n := by
  have hu : t - (⌊t⌋₊ : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨Nat.zero_le_self_sub_floor ht, (Nat.self_sub_floor_lt_one t).le⟩
  have hz : UpperWindow.base M m n δ x.1 + ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) ∈
      UpperWindow.templates M m n δ x.1 :=
    Or.inl ⟨_, hu, rfl⟩
  convert UpperWindow.grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx _ hz j ⌊t⌋₊
    using 1 <;> push_cast <;> ring_nf

/-- The analogous subdivision for an edge parallel to T, retaining its base. -/
theorem denom_grid_divisor_free (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (t : ℝ) (ht : 0 ≤ t)
    (k : ℕ) :
    (UpperWindow.base M m n δ x.1 + (k : ℂ) + (t : ℂ) * etaDenom M x.1, x.1) ∈
        modularPhiNonvanishingDomain M (m + 1) n ∧
      (UpperWindow.base M m n δ x.1 + (k : ℂ) + (t : ℂ) * etaDenom M x.1 + x.2.2,
        x.1) ∈ modularPhiNonvanishingDomain M (m + p) n := by
  have hu : t - (⌊t⌋₊ : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨Nat.zero_le_self_sub_floor ht, (Nat.self_sub_floor_lt_one t).le⟩
  have hz : UpperWindow.base M m n δ x.1 +
      ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * etaDenom M x.1 ∈
      UpperWindow.templates M m n δ x.1 :=
    Or.inr ⟨_, hu, rfl⟩
  convert UpperWindow.grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx _ hz ⌊t⌋₊ k
    using 1 <;> push_cast <;> ring_nf

/-- The specified reciprocal is analytic off zeros, including at Φ poles.
Its value there is justified by the actual chart equality and total division. -/
theorem reciprocal_analyticAt (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (p : ℂ × ℂ) (hτ : p.2 ∈ modularPhiDomain M)
    (hz : modularPhiZeroMultiplicity M m n p.1 p.2 = 0) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => (modularPhi M m n q.1 q.2)⁻¹) p := by
  let κ : ℕ → ℤ := fun j =>
    continuationIndex (modularPhiFactorPoint M m n j p.1 p.2).1
      (modularPhiFactorPoint M m n j p.1 p.2).2
  have hb := (modularPhi_sqrt_admissible M p.2 hτ).1
  have hp : p ∈ modularPhiChartDomain M m n κ := by
    refine ⟨hτ, fun j _ => ?_⟩
    exact shiftedArgument_inStrip _ _ hb
  have hzfac : ∀ j ∈ Finset.range (M 1 0).toNat,
      phiZeroMultiplicity (modularPhiFactorPoint M m n j p.1 p.2).1
        (modularPhiFactorPoint M m n j p.1 p.2).2 = 0 := by
    apply Finset.sum_eq_zero_iff.mp
    rw [← (modularPhi_multiplicity_pullback M hM m n p.1 p.2 hτ).2]
    exact hz
  have hN : modularPhiChartNumerator M m n κ p.1 p.2 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact (continuationNumerator_ne_zero_iff _ _ _ hb (hp.2 j hj)).mpr (hzfac j hj)
  have hAn := modularPhiChart_analytic M hM m n κ
  have hquot : AnalyticAt ℂ
      (fun q : ℂ × ℂ => modularPhiChartDenominator M m n κ q.1 q.2 /
        modularPhiChartNumerator M m n κ q.1 q.2) p :=
    (hAn.2 p hp).div (hAn.1 p hp) hN
  apply hquot.congr
  filter_upwards [(modularPhiChartDomain_isOpen M m n κ).mem_nhds hp] with q hq
  rw [modularPhi_eq_chart M hM m n κ q hq, modularPhiChart, inv_div]

end SICLean.L4.UpperContourGeometryAux
