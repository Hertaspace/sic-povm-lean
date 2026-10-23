import SICLean.L4.G1ContinuationBoundary

set_option autoImplicit false

/-!
# Joint lower comparison filter for the real ratio boundary

The spectral coordinates move in a dense good fiber after choosing a nearby lower-half-plane
parameter in the actual open Φ domain. This proves joint nontriviality even when the target lies on
an entire fixed-spectral divisor.
-/

noncomputable section
open Classical Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L4.G1RealRatioBoundaryAux

open G1Continuation

theorem ratio_lower_joint_neBot (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w y : ℝ) (h ell p : ℤ) (hT : 0 < g1T M τ₀) :
    NeBot (𝓝[{x : Parameters | x ∈ ratioGood M h ell p ∧ x.1.im < 0}]
      ((τ₀ : ℂ), (w : ℂ), (y : ℂ))) := by
  rw [nhdsWithin_neBot]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hdom : modularPhiDomain M ∈ 𝓝 (τ₀ : ℂ) :=
    (modularPhiDomain_isOpen M).mem_nhds (real_mem_modularPhiDomain M τ₀ hT)
  obtain ⟨δ, hδ, hδdom⟩ := Metric.mem_nhds_iff.mp hdom
  let r : ℝ := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hrδ : r < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  let τ : ℂ := (τ₀ : ℂ) - (r : ℂ) * Complex.I
  have hdist : dist τ (τ₀ : ℂ) = r := by
    rw [dist_eq_norm]
    have heq : τ - (τ₀ : ℂ) = -((r : ℂ) * Complex.I) := by dsimp [τ]; ring
    rw [heq, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  have hτ : τ ∈ modularPhiDomain M := hδdom (by simpa [Metric.mem_ball, hdist] using hrδ)
  have hτlower : τ.im < 0 := by simpa [τ] using neg_lt_zero.mpr hr
  obtain ⟨v, hv, hvball⟩ :=
    ((ratio_good_open_dense_fibers M hM h ell p).2 τ hτ).exists_mem_open
      (Metric.isOpen_ball : IsOpen (Metric.ball ((w : ℂ), (y : ℂ)) ε))
      ⟨((w : ℂ), (y : ℂ)), Metric.mem_ball_self hε⟩
  refine ⟨(τ, v), hεU ?_, hv, hτlower⟩
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨hdist ▸ hrε, hvball⟩

end SICLean.L4.G1RealRatioBoundaryAux
