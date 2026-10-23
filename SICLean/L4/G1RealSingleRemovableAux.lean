import SICLean.L4.G1ContinuationBoundary
import Mathlib.Analysis.Complex.ReImTopology

set_option autoImplicit false

/-! Joint unit-chart continuity and the dense off-real comparison used by SR02. -/

noncomputable section

open Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L4.G1RealSingleRemovableAux

/-- Continuity is joint in τ and w, and comes from the actual Φ unit chart. -/
theorem single_raw_continuousAt (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ell : ℤ) (u : ℂ × ℂ) (hu : u ∈ G1Continuation.singleGood M h ell) :
    ContinuousAt (G1Continuation.singleRaw M h ell) u := by
  obtain ⟨U, _hU, huU, _hsub, hA, hne⟩ :=
    modularPhi_joint_unit_neighborhood M hM ell (1 - h) (u.2, u.1) hu
  have hΦ : ContinuousAt (fun v : ℂ × ℂ => modularPhi M ell (1 - h) v.2 v.1) u :=
    (hA (u.2, u.1) huU).continuousAt.comp (f := fun v : ℂ × ℂ => (v.2, v.1))
      (continuous_snd.prodMk continuous_fst).continuousAt
  exact hΦ.inv₀ (hne (u.2, u.1) huU)

/-- The off-real set is dense jointly; no good fixed-spectral τ fiber is asserted. -/
theorem offReal_dense : Dense {u : ℂ × ℂ | u.1.im ≠ 0} := by
  exact (dense_compl_singleton (0 : ℝ)).preimage
    (Complex.isOpenMap_im.comp isOpenMap_fst)

/-- A joint off-real germ identifies the values of two continuous functions. -/
theorem eq_of_offReal_germ {f g : ℂ × ℂ → ℂ} {u : ℂ × ℂ}
    (hf : ContinuousAt f u) (hg : ContinuousAt g u)
    (heq : f =ᶠ[𝓝[{v : ℂ × ℂ | v.1.im ≠ 0}] u] g) : f u = g u := by
  have : NeBot (𝓝[{v : ℂ × ℂ | v.1.im ≠ 0}] u) :=
    mem_closure_iff_nhdsWithin_neBot.mp (offReal_dense u)
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)

end SICLean.L4.G1RealSingleRemovableAux
