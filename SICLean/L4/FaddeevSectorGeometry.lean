import SICLean.L4.Faddeev
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

/-!
Compact angular geometry. [RW26, pp. 4--5] supplies the underlying φ integral. Parameter-uniform
estimates are formalized here. The structures contain only explicit input inequalities and
compactness.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4.Sector

def rotation (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

def opening (β κ : ℝ) : ℝ := Real.pi / 2 - β - κ

def rotatedRe (b : ℂ) (θ : ℝ) : ℝ := (b * rotation θ).re

def rotatedInvRe (b : ℂ) (θ : ℝ) : ℝ := (b⁻¹ * rotation θ).re

/-- No decay, regularity, contour comparison or integral identity is assumed. -/
structure Family (K : Set ℂ) (β κ : ℝ) : Prop where
  compact : IsCompact K
  admissible : ∀ b ∈ K, AdmissibleB b
  arg_le : ∀ b ∈ K, |b.arg| ≤ β
  beta_nonneg : 0 ≤ β
  kappa_pos : 0 < κ
  angle_lt : β + κ < Real.pi / 2

/-- A quantitative lower bound, later supplied by `exists_uniform_margin`. -/
def UniformMargin (K : Set ℂ) (Θ lam : ℝ) : Prop :=
  0 < lam ∧ ∀ b ∈ K, ∀ θ ∈ Icc (-Θ) Θ,
    lam ≤ rotatedRe b θ ∧ lam ≤ rotatedInvRe b θ

def SafeHeight (lam v : ℝ) : Prop := 0 < v ∧ v < Real.pi * lam / 2

/-- The real part of `b * rotation θ` in polar form. -/
private lemma rotatedRe_eq_norm_mul_cos (b : ℂ) (θ : ℝ) :
    rotatedRe b θ = ‖b‖ * Real.cos (b.arg + θ) := by
  have h1 : b * rotation θ =
      (‖b‖ : ℂ) * Complex.exp (((b.arg + θ : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [rotation, ← Complex.norm_mul_exp_arg_mul_I b]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  calc rotatedRe b θ
      = ((‖b‖ : ℂ) * Complex.exp (((b.arg + θ : ℝ) : ℂ) * Complex.I)).re := by
        rw [rotatedRe, h1]
    _ = ‖b‖ * Real.cos (b.arg + θ) := by
        rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Inversion negates the argument when the real part is positive. -/
private lemma arg_inv_eq_neg {b : ℂ} (hb : 0 < b.re) : (b⁻¹).arg = -b.arg := by
  rw [Complex.arg_inv]
  have hne : b.arg ≠ Real.pi := by
    intro h
    have hneg : b.re < 0 := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  simp [hne]

theorem opening_pos {K : Set ℂ} {β κ : ℝ} (hK : Family K β κ) :
    0 < opening β κ := by
  have hlt := hK.angle_lt
  have hpi := Real.pi_pos
  unfold opening
  linarith

theorem opening_lt_half_pi {K : Set ℂ} {β κ : ℝ} (hK : Family K β κ) :
    opening β κ < Real.pi / 2 := by
  have hβ := hK.beta_nonneg
  have hκ := hK.kappa_pos
  unfold opening
  linarith

theorem rotation_ne_zero (θ : ℝ) : rotation θ ≠ 0 := by
  unfold rotation
  exact Complex.exp_ne_zero _

theorem norm_rotation (θ : ℝ) : ‖rotation θ‖ = 1 := by
  unfold rotation
  rw [mul_comm Complex.I (θ : ℂ)]
  exact Complex.norm_exp_ofReal_mul_I θ

theorem rotation_neg (θ : ℝ) : rotation (-θ) = (rotation θ)⁻¹ := by
  unfold rotation
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem rotatedRe_inv (b : ℂ) (θ : ℝ) :
    rotatedRe b⁻¹ θ = rotatedInvRe b θ := by
  rfl

theorem rotatedRe_pos_of_arg (b : ℂ) (θ : ℝ) (hb : AdmissibleB b)
    (hθ : |b.arg| + |θ| < Real.pi / 2) : 0 < rotatedRe b θ := by
  have hbne : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp [AdmissibleB] at hb
  rw [rotatedRe_eq_norm_mul_cos]
  apply mul_pos (norm_pos_iff.mpr hbne)
  apply Real.cos_pos_of_mem_Ioo
  apply abs_lt.mp
  calc |b.arg + θ| ≤ |b.arg| + |θ| := abs_add_le _ _
    _ < Real.pi / 2 := hθ

theorem rotatedInvRe_pos_of_arg (b : ℂ) (θ : ℝ) (hb : AdmissibleB b)
    (hθ : |b.arg| + |θ| < Real.pi / 2) : 0 < rotatedInvRe b θ := by
  have hbne : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp [AdmissibleB] at hb
  have hinvne : b⁻¹ ≠ 0 := inv_ne_zero hbne
  have harg : (b⁻¹).arg = -b.arg := arg_inv_eq_neg hb
  have hbound : |(b⁻¹).arg| + |θ| < Real.pi / 2 := by
    rw [harg, abs_neg]
    exact hθ
  have h := rotatedRe_eq_norm_mul_cos b⁻¹ θ
  rw [rotatedRe_inv] at h
  rw [h]
  apply mul_pos (norm_pos_iff.mpr hinvne)
  apply Real.cos_pos_of_mem_Ioo
  apply abs_lt.mp
  calc |(b⁻¹).arg + θ| ≤ |(b⁻¹).arg| + |θ| := abs_add_le _ _
    _ < Real.pi / 2 := hbound

/-- Same lam for b, b⁻¹ and the entire closed, symmetric angle interval. -/
theorem exists_uniform_margin {K : Set ℂ} {β κ : ℝ} (hK : Family K β κ) :
    ∃ lam : ℝ, UniformMargin K (opening β κ) lam := by
  set Θ := opening β κ with hΘdef
  have hΘpos : 0 < Θ := by
    rw [hΘdef]
    exact opening_pos hK
  set T : Set (ℂ × ℝ) := K ×ˢ Icc (-Θ) Θ with hT
  set f : ℂ × ℝ → ℝ := fun p => min (rotatedRe p.1 p.2) (rotatedInvRe p.1 p.2)
    with hf
  have hTcompact : IsCompact T := by
    rw [hT]
    exact hK.compact.prod isCompact_Icc
  have hne : ∀ p ∈ T, p.1 ≠ 0 := by
    intro p hp
    rw [hT] at hp
    exact fun h => by
      have hadm := hK.admissible p.1 hp.1
      rw [h] at hadm
      simp [AdmissibleB] at hadm
  have hexp : ContinuousOn (fun p : ℂ × ℝ => Complex.exp (Complex.I * (p.2 : ℂ))) T := by
    apply Continuous.continuousOn
    continuity
  have hfst : ContinuousOn (fun p : ℂ × ℝ => p.1) T := continuous_fst.continuousOn
  have hcontRe : ContinuousOn (fun p : ℂ × ℝ => rotatedRe p.1 p.2) T := by
    have hmul : ContinuousOn (fun p : ℂ × ℝ => p.1 * rotation p.2) T := by
      apply hfst.mul
      unfold rotation
      exact hexp
    exact Complex.continuous_re.comp_continuousOn hmul
  have hcontInv : ContinuousOn (fun p : ℂ × ℝ => rotatedInvRe p.1 p.2) T := by
    have hmul : ContinuousOn (fun p : ℂ × ℝ => p.1⁻¹ * rotation p.2) T := by
      apply (hfst.inv₀ hne).mul
      unfold rotation
      exact hexp
    exact Complex.continuous_re.comp_continuousOn hmul
  have hfcont : ContinuousOn f T := by
    rw [hf]
    have hpair : ContinuousOn (fun p : ℂ × ℝ => (rotatedRe p.1 p.2, rotatedInvRe p.1 p.2)) T :=
      hcontRe.prodMk hcontInv
    exact (continuous_fst.min continuous_snd).comp_continuousOn hpair
  have hpos : ∀ p ∈ T, (0 : ℝ) < f p := by
    intro p hp
    rw [hT] at hp
    obtain ⟨hbK, hθIcc⟩ := hp
    have hadm : AdmissibleB p.1 := hK.admissible p.1 hbK
    have hargle : |p.1.arg| ≤ β := hK.arg_le p.1 hbK
    have hθabs : |p.2| ≤ Θ := abs_le.mpr ⟨hθIcc.1, hθIcc.2⟩
    have hangle : |p.1.arg| + |p.2| < Real.pi / 2 := by
      have hsum : β + Θ = Real.pi / 2 - κ := by
        rw [hΘdef]
        unfold opening
        ring
      linarith [hK.kappa_pos]
    rw [hf]
    simp only
    exact lt_min (rotatedRe_pos_of_arg p.1 p.2 hadm hangle)
      (rotatedInvRe_pos_of_arg p.1 p.2 hadm hangle)
  obtain ⟨lam, hlam0, hle⟩ := hTcompact.exists_forall_le' hfcont hpos
  refine ⟨lam, hlam0, ?_⟩
  intro b hb θ hθ
  have hp : (b, θ) ∈ T := by
    rw [hT]
    exact ⟨hb, hθ⟩
  exact ⟨le_trans (hle (b, θ) hp) (min_le_left _ _),
    le_trans (hle (b, θ) hp) (min_le_right _ _)⟩

theorem uniform_margin_neg_angle {K : Set ℂ} {Θ lam : ℝ}
    (hlam : UniformMargin K Θ lam) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) :
    lam ≤ rotatedRe b (-θ) ∧ lam ≤ rotatedInvRe b (-θ) := by
  have hneg : -θ ∈ Icc (-Θ) Θ := by
    obtain ⟨h1, h2⟩ := hθ
    exact ⟨by linarith, by linarith⟩
  exact hlam.2 b hb (-θ) hneg

theorem exists_safe_height {lam : ℝ} (hlam : 0 < lam) :
    ∃ v : ℝ, SafeHeight lam v := by
  refine ⟨Real.pi * lam / 4, ?_⟩
  unfold SafeHeight
  constructor
  · positivity
  · have h : 0 < Real.pi * lam := mul_pos Real.pi_pos hlam
    nlinarith

theorem safe_height_admissible {K : Set ℂ} {Θ lam v : ℝ}
    (hΘ : 0 ≤ Θ) (hlam : UniformMargin K Θ lam) (hv : SafeHeight lam v)
    {b : ℂ} (hb : b ∈ K) : AdmissibleHeight b v := by
  have h0 : (0 : ℝ) ∈ Icc (-Θ) Θ := ⟨by linarith, hΘ⟩
  obtain ⟨hre, hinv⟩ := hlam.2 b hb 0 h0
  have hre' : lam ≤ b.re := by
    simpa [rotatedRe, rotation] using hre
  have hinv' : lam ≤ (b⁻¹).re := by
    simpa [rotatedInvRe, rotation] using hinv
  have hmin : lam ≤ min b.re (b⁻¹).re := le_min hre' hinv'
  have hminpos : 0 < min b.re (b⁻¹).re := lt_of_lt_of_le hlam.1 hmin
  refine ⟨hv.1, ?_⟩
  unfold poleHeight
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hbig : Real.pi * lam / 2 < Real.pi * min b.re (b⁻¹).re := by
    nlinarith
  linarith [hv.2]

end SICLean.L4.Sector
