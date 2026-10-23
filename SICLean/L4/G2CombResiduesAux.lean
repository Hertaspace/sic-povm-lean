import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import SICLean.L4.ModularPhiAux

set_option autoImplicit false

/-!
Auxiliaries for the component-labelled comb residues. Exponential identities use the existing `e`.
The local quotient expansion factors a simple zero through its analytic divided difference, then
separates the constant term of the analytic unit quotient. No residue or contour identity is
assumed.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace SICLean.L4.G2CombResiduesAux

lemma e_sub (z w : ℂ) : e (z - w) = e z / e w := by
  simp only [e, mul_sub, Complex.exp_sub]

lemma e_eq_iff_int_sub (z w : ℂ) :
    e z = e w ↔ ∃ k : ℤ, z - w = (k : ℂ) := by
  constructor
  · intro h
    apply e_eq_one_iff_int
    rw [e_sub, h, div_self (e_ne_zero w)]
  · rintro ⟨k, hk⟩
    have h : e (z - w) = 1 := by rw [hk, e_intCast]
    rw [e_sub] at h
    exact (div_eq_one_iff_eq (e_ne_zero w)).mp h

lemma e_hasDerivAt (z : ℂ) :
    HasDerivAt e (2 * (Real.pi : ℂ) * Complex.I * e z) z := by
  change HasDerivAt
    (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w))
    (2 * (Real.pi : ℂ) * Complex.I *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)) z
  apply HasDerivAt.congr_deriv
    (((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp)
  simp only [id_eq, mul_one]
  ring

/-- The divided difference of an analytic function is analytic at its center. -/
theorem analyticAt_dslope {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (dslope f p) p := by
  rcases hf with ⟨q, hq⟩
  exact ⟨q.fslope, hq.has_fpower_series_dslope_fslope⟩

/-- The residue limit for a quotient at a simple zero of its denominator. -/
theorem tendsto_mul_div_at_simple_zero {a b : ℂ → ℂ} {p d : ℂ}
    (ha : AnalyticAt ℂ a p) (hb : AnalyticAt ℂ b p) (hb0 : b p = 0)
    (hbd : HasDerivAt b d p) (hd : d ≠ 0) :
    Tendsto (fun z => (z - p) * (a z / b z)) (𝓝[≠] p) (𝓝 (a p / d)) := by
  have hbs : AnalyticAt ℂ (dslope b p) p := analyticAt_dslope hb
  have hbsp : dslope b p p = d := by
    rw [dslope_same, hbd.deriv]
  have hbsp0 : dslope b p p ≠ 0 := by
    rwa [hbsp]
  let q : ℂ → ℂ := fun z => a z / dslope b p z
  have hq : AnalyticAt ℂ q p := ha.div hbs hbsp0
  have ht : Tendsto q (𝓝[≠] p) (𝓝 (a p / d)) := by
    simpa only [q, hbsp] using hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzp : z ≠ p := hz
  have hbz : b z = (z - p) * dslope b p z := by
    simpa only [smul_eq_mul, hb0, sub_zero] using (sub_smul_dslope b p z).symm
  dsimp only [q]
  rw [hbz]
  field_simp [sub_ne_zero.mpr hzp]

/-- A quotient with a simple denominator zero has an analytic remainder after subtracting its
first-order principal part, on a positive closed ball. -/
theorem exists_analytic_remainder {a b : ℂ → ℂ} {p d : ℂ}
    (ha : AnalyticAt ℂ a p) (hb : AnalyticAt ℂ b p) (hb0 : b p = 0)
    (hbd : HasDerivAt b d p) (hd : d ≠ 0) :
    ∃ R : ℝ, ∃ g : ℂ → ℂ, 0 < R ∧
      AnalyticOnNhd ℂ g (Metric.closedBall p R) ∧
      ∀ z ∈ Metric.closedBall p R, z ≠ p →
        a z / b z = (a p / d) / (z - p) + g z := by
  have hbs : AnalyticAt ℂ (dslope b p) p := analyticAt_dslope hb
  have hbsp : dslope b p p = d := by
    rw [dslope_same, hbd.deriv]
  have hbsp0 : dslope b p p ≠ 0 := by
    rwa [hbsp]
  let q : ℂ → ℂ := fun z => a z / dslope b p z
  have hq : AnalyticAt ℂ q p := ha.div hbs hbsp0
  have hqp : q p = a p / d := by
    simp only [q, hbsp]
  have hgs : AnalyticAt ℂ (dslope q p) p := analyticAt_dslope hq
  have hnear : ∀ᶠ z in 𝓝 p,
      AnalyticAt ℂ (dslope q p) z ∧ dslope b p z ≠ 0 :=
    hgs.eventually_analyticAt.and (hbs.continuousAt.eventually_ne hbsp0)
  obtain ⟨R, hR, hBall⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp hnear
  refine ⟨R, dslope q p, hR, fun z hz => (hBall hz).1, ?_⟩
  intro z hz hzp
  have hbsz : dslope b p z ≠ 0 := (hBall hz).2
  have hsub : z - p ≠ 0 := sub_ne_zero.mpr hzp
  have hbz : b z = (z - p) * dslope b p z := by
    simpa only [smul_eq_mul, hb0, sub_zero] using (sub_smul_dslope b p z).symm
  calc
    a z / b z = q z / (z - p) := by
      rw [hbz]
      dsimp only [q]
      field_simp
    _ = (a p / d) / (z - p) + dslope q p z := by
      rw [dslope_of_ne q hzp, slope_def_field, hqp]
      ring

end SICLean.L4.G2CombResiduesAux
