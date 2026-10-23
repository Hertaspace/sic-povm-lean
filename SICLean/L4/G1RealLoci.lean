import SICLean.L4.G1ContinuationBoundary

set_option autoImplicit false

/-!
# Fixed-real-τ good loci and analytic/filter bridges

Fixed-real-τ topology and analytic bridge theorems. The loci are exactly those of
G1RealInterface: the entire zero/pole divisor of every displayed Φ factor is excluded. All target
spectral coordinates remain complex, including at divisor points; no fixed-w,y τ-slice nontriviality
is asserted.

The topology and fixed-τ filter statements below are the finite/nonzero comparison and the
removable-value step. [RW26, p. 6, p. 7, (22), (23), p. 29]. The fixed-τ topology is formalized
here.

The only import is the prior continuation boundary block. In particular, this file uses no G2 result
and proves no integral identity or removable-value assertion. Joint-to-slice bridges use the same
raw functions and loci as Boundary B01 and Strict S01/S02.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L4.G1RealLoci

/-- The positive real automorphy factor puts τ in the actual Φ parameter domain. This supplies the
domain input for the auxiliary fixed-τ topology. Background: [RW26, p. 6, p. 7, (22), (23)]. -/
theorem real_tau_mem_modularPhiDomain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (hT : 0 < g1T M τ₀) :
    (τ₀ : ℂ) ∈ modularPhiDomain M := by
  exact real_mem_modularPhiDomain M τ₀ hT

/-- Openness of the contract's single fixed-τ unit locus, by slicing the joint actual-divisor
complement (Strict S01, Boundary B01). This is an auxiliary topology step. [RW26, p. 6, p. 7,
(22), p. 29]. -/
theorem single_rhs_locus_isOpen (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell : ℤ) :
    IsOpen (g1SingleRHSLocus M τ₀ h ell) := by
  exact (modularPhiDivisor_domains_isOpen M hM ell (1 - h)).2.preimage
    (continuous_id.prodMk continuous_const)

/-- Openness of the three-factor fixed-τ unit locus, excluding every actual zero/pole divisor
(Strict S02, Boundary B01). Background: [RW26, p. 6, p. 7, (23), p. 29]. -/
theorem ratio_rhs_locus_isOpen (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell p : ℤ) :
    IsOpen (g1RatioRHSLocus M τ₀ h ell p) := by
  exact ((modularPhiDivisor_domains_isOpen M hM (p + ell) (-h)).2.preimage
    ((continuous_fst.add continuous_snd).prodMk continuous_const)).inter
      (((modularPhiDivisor_domains_isOpen M hM p 0).2.preimage
        (continuous_snd.prodMk continuous_const)).inter
          ((modularPhiDivisor_domains_isOpen M hM ell (1 - h)).2.preimage
            (continuous_fst.prodMk continuous_const)))

/-- Dense single spectral slice at positive real T, inherited from Strict S01 rather than assumed.
Background: [RW26, p. 6, p. 7, (22), p. 29]. Density concerns complex w and the full divisor
complement. -/
theorem single_rhs_locus_dense (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell : ℤ) (hT : 0 < g1T M τ₀) :
    Dense (g1SingleRHSLocus M τ₀ h ell) := by
  exact (G1Continuation.single_good_open_dense_fibers M hM h ell).2
    (τ₀ : ℂ) (real_tau_mem_modularPhiDomain M hM τ₀ hT)

/-- Dense common three-factor spectral slice, inherited from Strict S02. Background: [RW26, p. 6, p.
7, (23), p. 29]. The affine w+y factor is excluded together with the w and y factors. -/
theorem ratio_rhs_locus_dense (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell p : ℤ) (hT : 0 < g1T M τ₀) :
    Dense (g1RatioRHSLocus M τ₀ h ell p) := by
  exact (G1Continuation.ratio_good_open_dense_fibers M hM h ell p).2
    (τ₀ : ℂ) (real_tau_mem_modularPhiDomain M hM τ₀ hT)

/-- Nontriviality at every complex spectral target, including divisor points, obtained from the
fixed-τ density theorem. This is the auxiliary filter step in the removable-value reading.
Background: [RW26, p. 7, (22), p. 29]. No τ-slice nontriviality is claimed. -/
theorem single_rhs_locus_nhdsWithin_neBot (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell : ℤ) (hT : 0 < g1T M τ₀) (w : ℂ) :
    NeBot (𝓝[g1SingleRHSLocus M τ₀ h ell] w) := by
  exact mem_closure_iff_nhdsWithin_neBot.mp (single_rhs_locus_dense M hM τ₀ h ell hT w)

/-- Nontriviality at every complex pair target, including intersecting spectral divisors, from the
dense common fixed-τ locus. Background: [RW26, p. 7, (23), p. 29]. The locus removes entire divisor
sets, not only the center of ℂ². -/
theorem ratio_rhs_locus_nhdsWithin_neBot (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell p : ℤ) (hT : 0 < g1T M τ₀) (v : ℂ × ℂ) :
    NeBot (𝓝[g1RatioRHSLocus M τ₀ h ell p] v) := by
  exact mem_closure_iff_nhdsWithin_neBot.mp (ratio_rhs_locus_dense M hM τ₀ h ell p hT v)

/-- Analyticity of the literal single raw RHS on the contract's fixed-τ unit locus, using the actual
joint Φ unit charts and analytic inversion. Background: [RW26, p. 6, p. 7, (22), p. 29]. -/
theorem single_raw_analyticOnNhd (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell : ℤ) :
    AnalyticOnNhd ℂ (g1SingleRawRHS M τ₀ h ell)
      (g1SingleRHSLocus M τ₀ h ell) := by
  intro w hw
  obtain ⟨U, _hU, hwU, _hsub, hA, hne⟩ :=
    modularPhi_joint_unit_neighborhood M hM ell (1 - h) (w, (τ₀ : ℂ)) hw
  exact ((hA _ hwU).comp (f := fun z : ℂ => (z, (τ₀ : ℂ)))
    (analyticAt_id.prod analyticAt_const)).inv (hne _ hwU)

/-- Analyticity of the literal three-factor raw quotient on the contract's fixed-τ common unit
locus, including the affine w+y pullback. Background: [RW26, p. 6, p. 7, (23), p. 29]. -/
theorem ratio_raw_analyticOnNhd (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell p : ℤ) :
    AnalyticOnNhd ℂ (g1RatioRawRHS M τ₀ h ell p)
      (g1RatioRHSLocus M τ₀ h ell p) := by
  intro v hv
  have hnum : AnalyticAt ℂ
      (fun z : ℂ × ℂ => modularPhi M (p + ell) (-h) (z.1 + z.2) (τ₀ : ℂ)) v :=
    (modularPhi_joint_analytic_no_poles M hM (p + ell) (-h)
      (v.1 + v.2, (τ₀ : ℂ)) ⟨hv.1.1, hv.1.2.1⟩).comp
        (f := fun z : ℂ × ℂ => (z.1 + z.2, (τ₀ : ℂ)))
        ((analyticAt_fst.add analyticAt_snd).prod analyticAt_const)
  have hdenB : AnalyticAt ℂ
      (fun z : ℂ × ℂ => modularPhi M p 0 z.2 (τ₀ : ℂ)) v :=
    (modularPhi_joint_analytic_no_poles M hM p 0
      (v.2, (τ₀ : ℂ)) ⟨hv.2.1.1, hv.2.1.2.1⟩).comp
        (f := fun z : ℂ × ℂ => (z.2, (τ₀ : ℂ)))
        (analyticAt_snd.prod analyticAt_const)
  have hdenC : AnalyticAt ℂ
      (fun z : ℂ × ℂ => modularPhi M ell (1 - h) z.1 (τ₀ : ℂ)) v :=
    (modularPhi_joint_analytic_no_poles M hM ell (1 - h)
      (v.1, (τ₀ : ℂ)) ⟨hv.2.2.1, hv.2.2.2.1⟩).comp
        (f := fun z : ℂ × ℂ => (z.1, (τ₀ : ℂ)))
        (analyticAt_fst.prod analyticAt_const)
  have hB : modularPhi M p 0 v.2 (τ₀ : ℂ) ≠ 0 :=
    (modularPhi_ne_zero_iff M hM p 0 v.2 (τ₀ : ℂ) hv.2.1.1 hv.2.1.2.1).mpr hv.2.1.2.2
  have hC : modularPhi M ell (1 - h) v.1 (τ₀ : ℂ) ≠ 0 :=
    (modularPhi_ne_zero_iff M hM ell (1 - h) v.1 (τ₀ : ℂ) hv.2.2.1 hv.2.2.2.1).mpr hv.2.2.2.2
  exact hnum.div (hdenB.mul hdenC) (mul_ne_zero hB hC)

/-- At a good complex single target the raw RHS has its ordinary, unpunctured neighborhood limit.
Background: [RW26, p. 7, (22), p. 29]. It does not assign a raw total-division value at a pole. -/
theorem single_raw_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell : ℤ) (w : ℂ)
    (hw : w ∈ g1SingleRHSLocus M τ₀ h ell) :
    Tendsto (g1SingleRawRHS M τ₀ h ell) (𝓝 w)
      (𝓝 (g1SingleRawRHS M τ₀ h ell w)) := by
  exact (single_raw_analyticOnNhd M hM τ₀ h ell w hw).continuousAt

/-- At a good complex pair target the raw quotient has its ordinary, unpunctured neighborhood limit.
Background: [RW26, p. 7, (23), p. 29]. No apparent-singularity value is inferred from total
division. -/
theorem ratio_raw_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ : ℝ) (h ell p : ℤ) (v : ℂ × ℂ)
    (hv : v ∈ g1RatioRHSLocus M τ₀ h ell p) :
    Tendsto (g1RatioRawRHS M τ₀ h ell p) (𝓝 v)
      (𝓝 (g1RatioRawRHS M τ₀ h ell p v)) := by
  exact (ratio_raw_analyticOnNhd M hM τ₀ h ell p v hv).continuousAt

/-- Fixed-τ insertion maps the contract's single spectral-locus filter to the joint singleGood
filter at any complex target. Boundary B01 identifies the loci. Background: [RW26, p. 7, (22), p.
29]. The target may lie on the Φ divisor. -/
theorem single_slice_tendsto_good (M : SL(2, ℤ)) (τ₀ : ℝ) (h ell : ℤ)
    (w : ℂ) :
    Tendsto (fun z : ℂ => ((τ₀ : ℂ), z))
      (𝓝[g1SingleRHSLocus M τ₀ h ell] w)
      (𝓝[G1Continuation.singleGood M h ell] ((τ₀ : ℂ), w)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_const.prodMk continuous_id).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun _ hz => hz

/-- Fixed-τ insertion maps the contract's common pair-locus filter to the joint ratioGood filter at
any complex pair target. Boundary B01 identifies the loci. Background: [RW26, p. 7, (23), p. 29]. No
fixed-w,y τ-filter nontriviality is asserted. -/
theorem ratio_slice_tendsto_good (M : SL(2, ℤ)) (τ₀ : ℝ) (h ell p : ℤ)
    (v : ℂ × ℂ) :
    Tendsto (fun z : ℂ × ℂ => ((τ₀ : ℂ), z))
      (𝓝[g1RatioRHSLocus M τ₀ h ell p] v)
      (𝓝[G1Continuation.ratioGood M h ell p] ((τ₀ : ℂ), v)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_const.prodMk continuous_id).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun _ hz => hz

#check @single_rhs_locus_nhdsWithin_neBot
#check @ratio_rhs_locus_nhdsWithin_neBot
#check @single_slice_tendsto_good
#check @ratio_slice_tendsto_good
#check @G1Continuation.single_good_open_dense_fibers
#check @G1Continuation.ratio_good_open_dense_fibers
#print g1SingleRHSLocus
#print g1RatioRHSLocus

end SICLean.L4.G1RealLoci
