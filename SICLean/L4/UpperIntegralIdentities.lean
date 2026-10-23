import SICLean.L4.UpperSingleResidues
import SICLean.L4.UpperRatioResidues
import SICLean.L4.UpperIntegralIdentitiesAux

set_option autoImplicit false

/-!
# Both upper-plane integral identities

The proofs use the upstream contour and residue interfaces. All integrals use the
existing actual Φ and the upward tilted line. The single window
below forgets y and p by literal coordinates; it is not defined by an
integral identity or by an existential analytic-continuation property.

Exports include absolute integrability, point-value identities on the
initial open sets, joint ordinary-neighborhood equalities, and cleared
product identities. The q-product prefactor stays T(q;q)∞/(Q;Q)∞.
No theorem here asserts G1RealConclusion.
[RW26, p. 28, p. 29, (55), (56), (58), Appendix A.2]. The contour integrals, including an
independent single-function argument, are formalized here.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperIntegralIdentities
open UpperResidueParameters

/-- Explicit (τ,w) seed box; no y or integer p in the single conclusion. -/
def singleDomain (M : SL(2, ℤ)) (h ℓ : ℤ) (ψ σ ρ δ : ℝ) : Set (ℂ × ℂ) :=
  {u | u.1 ∈ UpperWindow.tauRegion M ψ ∧
    |(UpperWindow.coords (etaDenom M u.1) (UpperWindow.s M h ℓ u.1 u.2)).1 - σ| <
      UpperWindow.radius M σ ρ δ ∧
    |(UpperWindow.coords (etaDenom M u.1) (UpperWindow.s M h ℓ u.1 u.2)).2 - σ| <
      UpperWindow.radius M σ ρ δ}

def singleLineSum (M : SL(2, ℤ)) (n h ℓ : ℤ) (ψ δ : ℝ) (u : ℂ × ℂ) : ℂ :=
  ∑ m ∈ Finset.range (M 1 0).toNat,
    UpperContour.lineIntegral (UpperWindow.singleKernel M (m : ℤ) n h ℓ u.1 u.2)
      (UpperWindow.base M (m : ℤ) n δ u.1) ψ

def ratioLineSum (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ δ : ℝ)
    (x : UpperWindow.Parameters) : ℂ :=
  ∑ m ∈ Finset.range (M 1 0).toNat,
    UpperContour.lineIntegral (UpperWindow.ratioKernel M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2)
      (UpperWindow.base M (m : ℤ) n δ x.1) ψ

/--
[RW26, p. 28]. Nonemptiness is an output.
-/
theorem initial_domains_open_nonempty (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) :
    IsOpen (singleDomain M h ℓ ψ σ ρ δ) ∧ (singleDomain M h ℓ ψ σ ρ δ).Nonempty ∧
      IsOpen (UpperWindow.domain M h ℓ p ψ σ ρ δ) ∧
      (UpperWindow.domain M h ℓ p ψ σ ρ δ).Nonempty := by
  have hsopen : IsOpen (singleDomain M h ℓ ψ σ ρ δ) := by
    have heq : singleDomain M h ℓ ψ σ ρ δ =
        (fun u : ℂ × ℂ => (u.1, u.2, UpperWindow.centerY M 0 ρ u.1)) ⁻¹'
          UpperWindow.domain M h ℓ 0 ψ σ ρ δ := by
      ext u
      exact (UpperIntegralIdentitiesAux.center_lift_mem_iff M h ℓ 0 ψ σ ρ δ hc u).symm
    rw [heq]
    apply (UpperWindow.domain_isOpen M h ℓ 0 ψ σ ρ δ hc).preimage
    unfold UpperWindow.centerY etaDenom
    fun_prop
  obtain ⟨τ, hτ⟩ := UpperIntegralIdentitiesAux.tauRegion_nonempty M ψ hc.1 hc.2.1 hc.2.2.1
  have hx := UpperWindow.center_mem_domain M h ℓ p ψ σ ρ δ hc τ hτ
  refine ⟨hsopen, ?_, UpperWindow.domain_isOpen M h ℓ p ψ σ ρ δ hc, ?_⟩
  · exact ⟨(τ, UpperWindow.centerW M h ℓ σ τ), hx.1, hx.2.1, hx.2.2.1⟩
  · exact ⟨(τ, UpperWindow.centerW M h ℓ σ τ, UpperWindow.centerY M p ρ τ), hx⟩

/--
[RW26, p. 28]. A single point is lifted with p=0.
-/
theorem singleDomain_lift (M : SL(2, ℤ)) (h ℓ : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (u : ℂ × ℂ)
    (hu : u ∈ singleDomain M h ℓ ψ σ ρ δ) :
    (u.1, u.2, UpperWindow.centerY M 0 ρ u.1) ∈
      UpperWindow.domain M h ℓ 0 ψ σ ρ δ := by
  exact (UpperIntegralIdentitiesAux.center_lift_mem_iff M h ℓ 0 ψ σ ρ δ hc u).mpr hu

/--
[RW26, p. 28, p. 29, (55), (56)].
Compare two independently justified integer box limits.
-/
theorem singleLineSum_eq_product (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    singleLineSum M n h ℓ ψ δ (x.1, x.2.1) = singleProduct M h ℓ x := by
  exact tendsto_nhds_unique
    (UpperContour.sum_lines_eq_box_limit .single M h ℓ p n ψ σ ρ δ hc x hx)
    (UpperSingleResidues.integer_box_limit M n h ℓ p ψ σ ρ δ hc x hx)

/--
[RW26, p. 28, p. 29, (58)].
The finite m partition supplies coefficient one, never c.
-/
theorem ratioLineSum_eq_product (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ratioLineSum M n h ℓ p ψ δ x = ratioProduct M h ℓ p x := by
  exact tendsto_nhds_unique
    (UpperContour.sum_lines_eq_box_limit .ratio M h ℓ p n ψ σ ρ δ hc x hx)
    (UpperRatioResidues.integer_box_limit M n h ℓ p ψ σ ρ δ hc x hx)

/--
The single-function case, by the residue method of [RW26, p. 28, p. 29, (55), (56)].
Actual Φ point values, all on their unit domains.
-/
theorem upper_single (M : SL(2, ℤ)) (n h ℓ : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (u : ℂ × ℂ)
    (hu : u ∈ singleDomain M h ℓ ψ σ ρ δ) :
    (∀ m ∈ Finset.range (M 1 0).toNat,
      Integrable (UpperContour.linePullback
        (UpperWindow.singleKernel M (m : ℤ) n h ℓ u.1 u.2)
        (UpperWindow.base M (m : ℤ) n δ u.1) ψ)) ∧
      singleLineSum M n h ℓ ψ δ u =
        prefactor M u.1 * (modularPhi M ℓ (1 - h) u.2 u.1)⁻¹ := by
  let x : UpperWindow.Parameters := (u.1, u.2, UpperWindow.centerY M 0 ρ u.1)
  have hx : x ∈ UpperWindow.domain M h ℓ 0 ψ σ ρ δ :=
    singleDomain_lift M h ℓ ψ σ ρ δ hc u hu
  constructor
  · intro m hm
    exact UpperContour.line_integrable .single M h ℓ 0 (m : ℤ) n ψ σ ρ δ hc x hx
  · calc
      singleLineSum M n h ℓ ψ δ u = singleProduct M h ℓ x := by
        simpa only [x] using singleLineSum_eq_product M n h ℓ 0 ψ σ ρ δ hc x hx
      _ = _ := singleProduct_eq_modularPhi M h ℓ 0 ψ σ ρ δ hc x hx

/--
[RW26, p. 29]. No removable-point convention
is used: the initial box makes all three Φ values units.
-/
theorem upper_ratio (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    (∀ m ∈ Finset.range (M 1 0).toNat,
      Integrable (UpperContour.linePullback
        (UpperWindow.ratioKernel M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2)
        (UpperWindow.base M (m : ℤ) n δ x.1) ψ)) ∧
      ratioLineSum M n h ℓ p ψ δ x = prefactor M x.1 *
        (modularPhi M (p + ℓ) (-h) (x.2.1 + x.2.2) x.1 /
          (modularPhi M p 0 x.2.2 x.1 * modularPhi M ℓ (1 - h) x.2.1 x.1)) := by
  constructor
  · intro m hm
    exact UpperContour.line_integrable .ratio M h ℓ p (m : ℤ) n ψ σ ρ δ hc x hx
  · exact (ratioLineSum_eq_product M n h ℓ p ψ σ ρ δ hc x hx).trans
      (ratioProduct_eq_modularPhi M h ℓ p ψ σ ρ δ hc x hx)

/--
[RW26, p. 29] (product identification). Joint analyticity follows
from the proved initial identities and analytic zero-free products.
The chain-transport holomorphy is proved separately, in the `G1Continuation` files.
-/
theorem integral_sums_analytic (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) :
    AnalyticOnNhd ℂ (singleLineSum M n h ℓ ψ δ) (singleDomain M h ℓ ψ σ ρ δ) ∧
      AnalyticOnNhd ℂ (ratioLineSum M n h ℓ p ψ δ) (UpperWindow.domain M h ℓ p ψ σ ρ δ) := by
  obtain ⟨hsopen, _, hropen, _⟩ := initial_domains_open_nonempty M h ℓ p ψ σ ρ δ hc
  constructor
  · intro u hu
    let f : (ℂ × ℂ) → UpperWindow.Parameters :=
      fun v => (v.1, v.2, UpperWindow.centerY M 0 ρ v.1)
    have hfu : f u ∈ UpperWindow.domain M h ℓ 0 ψ σ ρ δ :=
      singleDomain_lift M h ℓ ψ σ ρ δ hc u hu
    have hp := ((products_analytic M h ℓ 0 ψ σ ρ δ hc).1 (f u) hfu).comp
      (UpperIntegralIdentitiesAux.center_lift_analytic M 0 ρ u)
    apply hp.congr
    filter_upwards [hsopen.mem_nhds hu] with v hv
    exact (singleLineSum_eq_product M n h ℓ 0 ψ σ ρ δ hc (f v)
      (singleDomain_lift M h ℓ ψ σ ρ δ hc v hv)).symm
  · exact (products_analytic M h ℓ p ψ σ ρ δ hc).2.congr hropen
      (fun x hx => (ratioLineSum_eq_product M n h ℓ p ψ σ ρ δ hc x hx).symm)

/--
[RW26, p. 28, (55), (56)]. Cleared initial identity for subsequent chart comparisons.
-/
theorem single_cleared (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    qPochhammer (e (etaMobius M x.1)) (e (etaMobius M x.1)) *
      qPochhammer (UpperWindow.A ℓ x.1 x.2.1) (e x.1) *
      singleLineSum M n h ℓ ψ δ (x.1, x.2.1) =
        etaDenom M x.1 * qPochhammer (e x.1) (e x.1) *
          qPochhammer (e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1)
            (e (etaMobius M x.1)) := by
  rw [singleLineSum_eq_product M n h ℓ p ψ σ ρ δ hc x hx]
  obtain ⟨hq, hQ, ha, ht, hA, hB, haA, hQC⟩ :=
    infinite_products_ne_zero M h ℓ p ψ σ ρ δ hc x hx
  dsimp only [singleProduct, prefactor]
  field_simp [hQ, hA]

/--
[RW26, p. 29]. This is a finite equality with all denominators cleared, on the initial
domain. Its continuation is proved in the `G1Continuation` files.
-/
theorem ratio_cleared (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    qPochhammer (e (etaMobius M x.1)) (e (etaMobius M x.1)) *
      qPochhammer (a p x) (e x.1) * qPochhammer (UpperWindow.A ℓ x.1 x.2.1) (e x.1) *
      qPochhammer (UpperWindow.B M h x.1 x.2.1 x.2.2) (e (etaMobius M x.1)) *
      ratioLineSum M n h ℓ p ψ δ x =
        etaDenom M x.1 * qPochhammer (e x.1) (e x.1) *
          qPochhammer (t M x) (e (etaMobius M x.1)) *
          qPochhammer (a p x * UpperWindow.A ℓ x.1 x.2.1) (e x.1) *
          qPochhammer (e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1)
            (e (etaMobius M x.1)) := by
  rw [ratioLineSum_eq_product M n h ℓ p ψ σ ρ δ hc x hx]
  obtain ⟨hq, hQ, ha, ht, hA, hB, haA, hQC⟩ :=
    infinite_products_ne_zero M h ℓ p ψ σ ρ δ hc x hx
  dsimp only [ratioProduct, prefactor]
  field_simp [hQ, ha, hA, hB]

/--
[RW26, p. 29]. Joint ordinary-neighborhood
equality; this is stronger than a fixed-τ punctured residue germ.
-/
theorem single_seed_neighborhood (M : SL(2, ℤ)) (n h ℓ : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (u : ℂ × ℂ)
    (hu : u ∈ singleDomain M h ℓ ψ σ ρ δ) :
    singleLineSum M n h ℓ ψ δ =ᶠ[𝓝 u]
      (fun v : ℂ × ℂ => prefactor M v.1 * (modularPhi M ℓ (1 - h) v.2 v.1)⁻¹) := by
  have hU := (initial_domains_open_nonempty M h ℓ 0 ψ σ ρ δ hc).1
  filter_upwards [hU.mem_nhds hu] with v hv
  exact (upper_single M n h ℓ ψ σ ρ δ hc v hv).2

/--
[RW26, p. 29]. A joint ordinary neighborhood of (τ,w,y), with all
denominators still nonzero. No multivariate puncture is used to hide a divisor.
-/
theorem ratio_seed_neighborhood (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ratioLineSum M n h ℓ p ψ δ =ᶠ[𝓝 x]
      (fun z : UpperWindow.Parameters => prefactor M z.1 *
        (modularPhi M (p + ℓ) (-h) (z.2.1 + z.2.2) z.1 /
          (modularPhi M p 0 z.2.2 z.1 * modularPhi M ℓ (1 - h) z.2.1 z.1))) := by
  have hU := UpperWindow.domain_isOpen M h ℓ p ψ σ ρ δ hc
  filter_upwards [hU.mem_nhds hx] with z hz
  exact (upper_ratio M n h ℓ p ψ σ ρ δ hc z hz).2

/--
[RW26, p. 28].
Direct fixed-τ seeds: use upper_single / upper_ratio on these sets.
-/
theorem initial_fibers (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (τ : ℂ)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) :
    (∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧
      ∀ w ∈ U, (τ, w) ∈ singleDomain M h ℓ ψ σ ρ δ) ∧
      (∃ V : Set (ℂ × ℂ), IsOpen V ∧ V.Nonempty ∧
        ∀ v ∈ V, (τ, v.1, v.2) ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) := by
  constructor
  · refine ⟨{w : ℂ | (τ, w) ∈ singleDomain M h ℓ ψ σ ρ δ}, ?_, ?_, ?_⟩
    · exact ((initial_domains_open_nonempty M h ℓ p ψ σ ρ δ hc).1).preimage
        (by fun_prop)
    · have hx := UpperWindow.center_mem_domain M h ℓ p ψ σ ρ δ hc τ hτ
      exact ⟨UpperWindow.centerW M h ℓ σ τ, hx.1, hx.2.1, hx.2.2.1⟩
    · intro w hw
      exact hw
  · obtain ⟨hVopen, hVne⟩ := UpperWindow.fiber_open_nonempty M h ℓ p ψ σ ρ δ hc τ hτ
    exact ⟨{v : ℂ × ℂ | (τ, v) ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ},
      hVopen, hVne, fun v hv => hv⟩

#print singleDomain
#print singleLineSum
#print ratioLineSum
#check UpperContour.sum_lines_eq_box_limit
#check UpperSingleResidues.integer_box_limit
#check UpperRatioResidues.integer_box_limit
#check upper_single
#check upper_ratio
#check single_seed_neighborhood
#check ratio_seed_neighborhood

end SICLean.L4.UpperIntegralIdentities
