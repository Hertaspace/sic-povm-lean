import SICLean.L4.ModularPhi

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4.ModularCocycleAux

/-- A punctured germ determines the value of its continuous representatives. -/
theorem eq_of_germ {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (hfg : f =ᶠ[𝓝[≠] z] g) : f z = g z :=
  ((hf.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg).mp hfg).eq_of_nhds

/-- Division by a nonzero constant preserves a punctured neighborhood. -/
theorem tendsto_div_const_nhdsNE (a z : ℂ) (ha : a ≠ 0) :
    Tendsto (fun w : ℂ => w / a) (𝓝[≠] z) (𝓝[≠] (z / a)) := by
  apply ContinuousWithinAt.tendsto_nhdsWithin
    (show ContinuousAt (fun w : ℂ => w / a) z by fun_prop).continuousWithinAt
  intro w hw h
  exact hw ((div_left_inj' ha).mp h)

/-- The slit plane is star convex about its positive real point `1`. -/
theorem slitPlane_isPreconnected : IsPreconnected Complex.slitPlane := by
  have hstar : StarConvex ℝ (1 : ℂ) Complex.slitPlane := by
    intro y hy a b ha hb hab
    rcases Complex.mem_slitPlane_iff.mp hy with hy | hy
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl
        ((convex_halfSpace_re_gt 0) (by norm_num) hy ha hb hab))
    · by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simp [hb0, ha1]
      · apply Complex.mem_slitPlane_iff.mpr
        right
        simpa using mul_ne_zero hb0 hy
  exact (hstar.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected

/-- An invertible affine change of the slit plane gives the modular domain. -/
theorem modularPhiDomain_isPreconnected (M : SL(2, ℤ)) (hM : M 1 0 ≠ 0) :
    IsPreconnected (modularPhiDomain M) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM
  let g : ℂ → ℂ := fun T => (T - (M 1 1 : ℂ)) / (M 1 0 : ℂ)
  have hcont : Continuous g := by dsimp [g]; fun_prop
  have himage : g '' Complex.slitPlane = modularPhiDomain M := by
    ext τ
    constructor
    · rintro ⟨T, hT, rfl⟩
      change etaDenom M (g T) ∈ Complex.slitPlane
      have hcomp : etaDenom M (g T) = T := by
        dsimp [g, etaDenom]
        field_simp
        ring
      rwa [hcomp]
    · intro hτ
      refine ⟨etaDenom M τ, hτ, ?_⟩
      dsimp [g, etaDenom]
      field_simp
      ring
  rw [← himage]
  exact slitPlane_isPreconnected.image g hcont.continuousOn

/-- Analytic functions on the modular slit domain are determined above
the real axis. This applies to explicit finite exponential phases. -/
theorem eqOn_domain_of_upper (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (modularPhiDomain M))
    (hg : AnalyticOnNhd ℂ g (modularPhiDomain M))
    (hupper : ∀ τ : ℂ, 0 < τ.im → f τ = g τ) :
    EqOn f g (modularPhiDomain M) := by
  have hI : (Complex.I : ℂ) ∈ modularPhiDomain M :=
    upper_mem_modularPhiDomain M hM UpperHalfPlane.I
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    (modularPhiDomain_isPreconnected M hM.ne') hI
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    (show (0 : ℝ) < Complex.I.im by norm_num)] with τ hτ
  exact hupper τ hτ

end SICLean.L4.ModularCocycleAux
