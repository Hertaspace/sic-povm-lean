import SICLean.L4.G1RealRatioBoundary

set_option autoImplicit false

/-!
# Joint unit-chart and real-slice bridges for the ratio removable value

The displayed quotient is continuous only at common unit points. Its joint continuity below comes
from the actual two-variable Φ unit neighborhoods. An ordinary open comparison neighborhood then
lets an off-real identity pass to its real-τ slice by moving τ through positive imaginary heights.
-/

noncomputable section
open Classical Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L4.G1RealRatioRemovableAux

open G1Continuation

/-- Joint continuity of all three affine Φ factors, on their common unit locus. -/
theorem ratioRaw_continuousAt (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ell p : ℤ) (x : Parameters) (hx : x ∈ ratioGood M h ell p) :
    ContinuousAt (ratioRaw M h ell p) x := by
  obtain ⟨UA, _, hxA, _, hA, _⟩ :=
    modularPhi_joint_unit_neighborhood M hM (p + ell) (-h) (x.2.1 + x.2.2, x.1) hx.1
  obtain ⟨UB, _, hxB, _, hB, hBne⟩ :=
    modularPhi_joint_unit_neighborhood M hM p 0 (x.2.2, x.1) hx.2.1
  obtain ⟨UC, _, hxC, _, hC, hCne⟩ :=
    modularPhi_joint_unit_neighborhood M hM ell (1 - h) (x.2.1, x.1) hx.2.2
  have ha : ContinuousAt
      (fun v : Parameters => modularPhi M (p + ell) (-h) (v.2.1 + v.2.2) v.1) x :=
    (hA _ hxA).continuousAt.comp (f := fun v : Parameters => (v.2.1 + v.2.2, v.1))
      ((continuousAt_snd.fst.add continuousAt_snd.snd).prodMk continuousAt_fst)
  have hb : ContinuousAt
      (fun v : Parameters => modularPhi M p 0 v.2.2 v.1) x :=
    (hB _ hxB).continuousAt.comp (f := fun v : Parameters => (v.2.2, v.1))
      (continuousAt_snd.snd.prodMk continuousAt_fst)
  have hc : ContinuousAt
      (fun v : Parameters => modularPhi M ell (1 - h) v.2.1 v.1) x :=
    (hC _ hxC).continuousAt.comp (f := fun v : Parameters => (v.2.1, v.1))
      (continuousAt_snd.fst.prodMk continuousAt_fst)
  have hden : ContinuousAt (fun v : Parameters =>
      modularPhi M p 0 v.2.2 v.1 * modularPhi M ell (1 - h) v.2.1 v.1) x :=
    hb.mul hc
  have hden_ne : modularPhi M p 0 x.2.2 x.1 *
      modularPhi M ell (1 - h) x.2.1 x.1 ≠ 0 :=
    mul_ne_zero (hBne (x.2.2, x.1) hxB) (hCne (x.2.1, x.1) hxC)
  change ContinuousAt
    (fun v : Parameters => modularPhi M (p + ell) (-h) (v.2.1 + v.2.2) v.1 /
      (modularPhi M p 0 v.2.2 v.1 * modularPhi M ell (1 - h) v.2.1 v.1)) x
  exact ContinuousAt.div
    (f := fun v : Parameters => modularPhi M (p + ell) (-h) (v.2.1 + v.2.2) v.1)
    (g := fun v : Parameters => modularPhi M p 0 v.2.2 v.1 *
      modularPhi M ell (1 - h) v.2.1 v.1) ha hden hden_ne

/-- Continuity at a real-τ comparison point fills in the real slice. Both functions are evaluated at
the comparison point, which may differ from the original center of the open comparison neighborhood.
-/
theorem eq_of_off_real (f g : Parameters → ℂ) (U : Set Parameters)
    (hU : IsOpen U) (x : Parameters) (hx : x ∈ U) (hxim : x.1.im = 0)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (heq : ∀ z ∈ U, z.1.im ≠ 0 → f z = g z) :
    f x = g x := by
  let γ : ℝ → Parameters := fun t => (x.1 + (t : ℂ) * Complex.I, x.2)
  have hγ : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hc : ContinuousAt γ 0 := by
      dsimp [γ]
      fun_prop
    simpa [γ] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique_of_eventuallyEq (hf.tendsto.comp hγ) (hg.tendsto.comp hγ)
  filter_upwards [hγ.eventually (hU.mem_nhds hx), self_mem_nhdsWithin] with t ht htpos
  apply heq _ ht
  simpa [γ, hxim] using ne_of_gt htpos

end SICLean.L4.G1RealRatioRemovableAux
