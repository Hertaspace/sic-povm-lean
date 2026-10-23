import SICLean.L4.G1ContinuationBoundary

set_option autoImplicit false

/-!
# Kernel comparison and nontriviality of the lower joint comparison filter

The spectral parameter is allowed to move. Every product neighborhood contains a lower-half-plane
parameter in the modular domain, followed by a point of its dense spectral unit locus.
-/

noncomputable section
open Classical Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L4.G1RealSingleBoundaryAux

open G1Continuation

theorem single_kernel_eq (M : SL(2, ℤ)) (τ w : ℂ) (n h ell m : ℤ) :
    UpperWindow.singleKernel M m n h ell τ w =
      G1BilateralGeometry.singleKernel M τ w n h ell m := by
  funext z
  simp [UpperWindow.singleKernel, UpperWindow.phase, G1BilateralGeometry.singleKernel,
    G1BilateralGeometry.singleData, ModularCluster.kernel, ModularCluster.phase]

theorem lower_good_nhdsWithin_neBot (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ w : ℝ) (h ell : ℤ) (hT : 0 < g1T M τ₀) :
    NeBot (𝓝[{u : ℂ × ℂ | u ∈ singleGood M h ell ∧ u.1.im < 0}]
      ((τ₀ : ℂ), (w : ℂ))) := by
  apply nhdsWithin_neBot.mpr
  intro S hS
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hS
  have hdomain : modularPhiDomain M ∈ 𝓝 (τ₀ : ℂ) :=
    (modularPhiDomain_isOpen M).mem_nhds (real_mem_modularPhiDomain M τ₀ hT)
  have hclosure : (τ₀ : ℂ) ∈ closure {τ : ℂ | τ.im < 0} := by
    simp
  obtain ⟨τ, hτ, hτlower⟩ :=
    mem_closure_iff_nhds.mp hclosure (U ∩ modularPhiDomain M) (inter_mem hU hdomain)
  obtain ⟨z, hzgood, hzV⟩ :=
    ((single_good_open_dense_fibers M hM h ell).2 τ hτ.2).inter_nhds_nonempty hV
  exact ⟨(τ, z), hUV ⟨hτ.1, hzV⟩, hzgood, hτlower⟩

end SICLean.L4.G1RealSingleBoundaryAux
