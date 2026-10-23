import SICLean.L4.ModularPhi
import SICLean.L4.FaddeevSectorDecay

set_option autoImplicit false

/-!
The concrete constants below work on a full closed parameter disk. The
upper-half-disk exports are stated before the bilateral exports in later files.
No regularity, estimate, or existence assertion is part of a definition.
[RW26, p. 6, p. 7, (19), Prop. 2(i), Lemma 1]. Explicit constants and full-disk geometry are
formalized here.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.ModularSector

def realDenom (M : SL(2, ℤ)) (τ₀ : ℝ) : ℝ :=
  (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)

def parameterRadius (M : SL(2, ℤ)) (τ₀ α : ℝ) : ℝ :=
  realDenom M τ₀ * Real.sin (α / 4) / (4 * (M 1 0 : ℝ))

def sqrtLower (M : SL(2, ℤ)) (τ₀ : ℝ) : ℝ :=
  Real.sqrt (realDenom M τ₀ / 2)

def sqrtUpper (M : SL(2, ℤ)) (τ₀ : ℝ) : ℝ :=
  Real.sqrt (2 * realDenom M τ₀)

def margin (M : SL(2, ℤ)) (τ₀ α : ℝ) : ℝ :=
  min (sqrtLower M τ₀) (1 / sqrtUpper M τ₀) * Real.sin (α / 2)

def height (M : SL(2, ℤ)) (τ₀ α : ℝ) : ℝ :=
  Real.pi * margin M τ₀ α / 4

/-- The φ rate 2v and the lower bound |x|≥|z|/(2B) give k=v/B. -/
def rate (M : SL(2, ℤ)) (τ₀ α : ℝ) : ℝ :=
  height M τ₀ α / sqrtUpper M τ₀

def parameterDisk (τ₀ ρ : ℝ) : Set ℂ := Metric.closedBall (τ₀ : ℂ) ρ

def upperParameterDisk (τ₀ ρ : ℝ) : Set ℂ :=
  parameterDisk τ₀ ρ ∩ {τ | 0 ≤ τ.im}

def sqrtParameters (M : SL(2, ℤ)) (τ₀ ρ : ℝ) : Set ℂ :=
  (fun τ => Complex.sqrt (etaDenom M τ)) '' parameterDisk τ₀ ρ

def upperSector (α R : ℝ) : Set ℂ :=
  {z | R ≤ ‖z‖ ∧ α ≤ z.arg ∧ z.arg ≤ Real.pi - α}

/-- Exactly the constant term of the existing affine factor argument. -/
def factorOffset (M : SL(2, ℤ)) (r n : ℤ) (j : ℕ) (τ : ℂ) : ℂ :=
  (modularPhiFactorPoint M r n j 0 τ).2

def factorRadius (M : SL(2, ℤ)) (τ₀ α A : ℝ) : ℝ :=
  max (2 * sqrtUpper M τ₀)
    (2 * sqrtUpper M τ₀ * A / Real.sin (α / 4))

/--
Nonzero arguments, including the boundary rays; [RW26, p. 7, Lemma 1].
-/
theorem upperSector_ne_zero (α R : ℝ) (hR : 0 < R) {z : ℂ}
    (hz : z ∈ upperSector α R) : z ≠ 0 := by
  intro h
  rw [h] at hz
  simp only [upperSector, Set.mem_ofPred_eq, norm_zero] at hz
  linarith [hz.1]

/--
Shrinking the angle interval or enlarging R only restricts the set; [RW26, p. 7, Lemma 1].
-/
theorem upperSector_antitone {α α' R R' : ℝ} (hα : α ≤ α') (hR : R ≤ R') :
    upperSector α' R' ⊆ upperSector α R := by
  intro z hz
  simp only [upperSector, Set.mem_ofPred_eq] at hz ⊢
  exact ⟨hR.trans hz.1, hα.trans hz.2.1, hz.2.2.trans (by linarith)⟩

/--
Quantitative choice for the shrinking; [RW26, p. 6, (19)].
-/
theorem parameterRadius_pos (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) : 0 < parameterRadius M τ₀ α := by
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hsin : 0 < Real.sin (α / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  unfold parameterRadius
  positivity

/--
Every parameter, on either side, stays on the same principal branch. [RW26, p. 6, (19)].
-/
theorem parameterDisk_denom_control (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) {τ : ℂ}
    (hτ : τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α)) :
    realDenom M τ₀ / 2 ≤ (etaDenom M τ).re ∧
      ‖etaDenom M τ‖ ≤ 2 * realDenom M τ₀ ∧
      |(etaDenom M τ).arg| ≤ α / 4 ∧ τ ∈ modularPhiDomain M := by
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hsin_pos : 0 < Real.sin (α / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin_le_one : Real.sin (α / 4) ≤ 1 := Real.sin_le_one _
  have hρpos : 0 < parameterRadius M τ₀ α := parameterRadius_pos M hM τ₀ α hT hα hα'
  have hcru : (M 1 0 : ℝ) * parameterRadius M τ₀ α =
      realDenom M τ₀ * Real.sin (α / 4) / 4 := by
    rw [parameterRadius]
    field_simp
  have hdist : ‖τ - (τ₀ : ℂ)‖ ≤ parameterRadius M τ₀ α := by
    have h := hτ
    rw [parameterDisk, Metric.mem_closedBall, dist_eq_norm] at h
    exact h
  have hre_eq : (etaDenom M τ).re = (M 1 0 : ℝ) * τ.re + (M 1 1 : ℝ) := by
    simp [etaDenom]
  have him_eq : (etaDenom M τ).im = (M 1 0 : ℝ) * τ.im := by
    simp [etaDenom]
  have hsplit_re : (M 1 0 : ℝ) * τ.re + (M 1 1 : ℝ) =
      realDenom M τ₀ + (M 1 0 : ℝ) * (τ.re - τ₀) := by
    simp only [realDenom]
    ring
  have hre_lower : realDenom M τ₀ / 2 ≤ (etaDenom M τ).re := by
    have hb : -(parameterRadius M τ₀ α) ≤ τ.re - τ₀ ∧
        τ.re - τ₀ ≤ parameterRadius M τ₀ α := by
      have h := abs_le.1 ((Complex.abs_re_le_norm (τ - (τ₀ : ℂ))).trans hdist)
      simpa using h
    rw [hre_eq, hsplit_re]
    nlinarith [hcru, hsin_le_one, hT, hb.1, hb.2, hc.le]
  have hnorm_upper : ‖etaDenom M τ‖ ≤ 2 * realDenom M τ₀ := by
    have hsplit : etaDenom M τ =
        ((M 1 0 : ℝ) : ℂ) * (τ - (τ₀ : ℂ)) + ((realDenom M τ₀ : ℝ) : ℂ) := by
      simp only [etaDenom, realDenom]
      push_cast
      ring
    rw [hsplit]
    have h1 : ‖((M 1 0 : ℝ) : ℂ) * (τ - (τ₀ : ℂ))‖ =
        (M 1 0 : ℝ) * ‖τ - (τ₀ : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.le]
    have h2 : ‖((M 1 0 : ℝ) : ℂ) * (τ - (τ₀ : ℂ))‖ ≤
        (M 1 0 : ℝ) * parameterRadius M τ₀ α := by
      rw [h1]; exact mul_le_mul_of_nonneg_left hdist hc.le
    have h3 : ‖((realDenom M τ₀ : ℝ) : ℂ)‖ = realDenom M τ₀ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    calc ‖((M 1 0 : ℝ) : ℂ) * (τ - (τ₀ : ℂ)) + ((realDenom M τ₀ : ℝ) : ℂ)‖
        ≤ ‖((M 1 0 : ℝ) : ℂ) * (τ - (τ₀ : ℂ))‖ + ‖((realDenom M τ₀ : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ (M 1 0 : ℝ) * parameterRadius M τ₀ α + realDenom M τ₀ := by rw [h3]; linarith
      _ = realDenom M τ₀ * Real.sin (α / 4) / 4 + realDenom M τ₀ := by rw [hcru]
      _ ≤ 2 * realDenom M τ₀ := by nlinarith [hsin_le_one, hT]
  have hw_re : 0 < (etaDenom M τ).re := by linarith
  have hnorm_lower : realDenom M τ₀ / 2 ≤ ‖etaDenom M τ‖ :=
    hre_lower.trans (Complex.re_le_norm _)
  have him_bound : |(etaDenom M τ).im| ≤ (M 1 0 : ℝ) * parameterRadius M τ₀ α := by
    have him_diff : |τ.im| ≤ parameterRadius M τ₀ α := by
      have h := Complex.abs_im_le_norm (τ - (τ₀ : ℂ))
      simpa using h.trans hdist
    rw [him_eq, abs_mul, abs_of_nonneg hc.le]
    exact mul_le_mul_of_nonneg_left him_diff hc.le
  have hsin_bound : |Real.sin (etaDenom M τ).arg| ≤ Real.sin (α / 4) := by
    have hsin_eq : |Real.sin (etaDenom M τ).arg| =
        |(etaDenom M τ).im| / ‖etaDenom M τ‖ := by
      rw [Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg _)]
    rw [hsin_eq]
    have hkey : |(etaDenom M τ).im| / ‖etaDenom M τ‖ ≤
        ((M 1 0 : ℝ) * parameterRadius M τ₀ α) / (realDenom M τ₀ / 2) := by
      exact div_le_div₀ (le_of_lt (mul_pos hc hρpos)) him_bound (by linarith) hnorm_lower
    refine hkey.trans ?_
    rw [hcru]
    have hcalc : realDenom M τ₀ * Real.sin (α / 4) / 4 / (realDenom M τ₀ / 2) =
        Real.sin (α / 4) / 2 := by
      field_simp
      ring
    rw [hcalc]
    linarith [hsin_pos]
  have hw_arg_lt : |(etaDenom M τ).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw_re)
  have harg : |(etaDenom M τ).arg| ≤ α / 4 := by
    have hsabs := Real.abs_sin_eq_sin_abs_of_abs_le_pi
      (x := (etaDenom M τ).arg) (Complex.abs_arg_le_pi _)
    rw [hsabs] at hsin_bound
    have hmem1 : |(etaDenom M τ).arg| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [abs_nonneg (etaDenom M τ).arg, hw_arg_lt], le_of_lt hw_arg_lt⟩
    have hmem2 : α / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, by linarith [Real.pi_pos]⟩
    exact (Real.strictMonoOn_sin.le_iff_le hmem1 hmem2).1 hsin_bound
  refine ⟨hre_lower, hnorm_upper, harg, ?_⟩
  simp only [modularPhiDomain, Set.mem_ofPred_eq, Complex.mem_slitPlane_iff]
  exact Or.inl hw_re

/--
Compact image, rather than an assumed compact family of sqrt values; [RW26, p. 6, (19)]
-/
theorem sqrtParameters_isCompact (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    IsCompact (sqrtParameters M τ₀ (parameterRadius M τ₀ α)) := by
  have hmaps : Set.MapsTo (fun τ : ℂ => etaDenom M τ)
      (parameterDisk τ₀ (parameterRadius M τ₀ α)) Complex.slitPlane := by
    intro τ hτ
    have h := (parameterDisk_denom_control M hM τ₀ α hT hα hα' hτ).2.2.2
    simpa only [modularPhiDomain, Set.mem_ofPred_eq] using h
  have hden : ContinuousOn (fun τ : ℂ => etaDenom M τ)
      (parameterDisk τ₀ (parameterRadius M τ₀ α)) := by
    unfold etaDenom
    fun_prop
  have hcont : ContinuousOn (fun τ : ℂ => Complex.sqrt (etaDenom M τ))
      (parameterDisk τ₀ (parameterRadius M τ₀ α)) :=
    Complex.continuousOn_sqrt.comp hden hmaps
  exact IsCompact.image_of_continuousOn (isCompact_closedBall _ _) hcont

/--
Uniform lower/upper moduli and half the T angle for the principal sqrt; [RW26, p. 6, (19)]
-/
theorem sqrtParameters_bounds (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) {b : ℂ}
    (hb : b ∈ sqrtParameters M τ₀ (parameterRadius M τ₀ α)) :
    AdmissibleB b ∧ sqrtLower M τ₀ ≤ ‖b‖ ∧ ‖b‖ ≤ sqrtUpper M τ₀ ∧
      |b.arg| ≤ α / 8 := by
  rw [sqrtParameters] at hb
  obtain ⟨τ, hτ, rfl⟩ := hb
  obtain ⟨hre, hnorm, harg, hdom⟩ := parameterDisk_denom_control M hM τ₀ α hT hα hα' hτ
  have hwslit : etaDenom M τ ∈ Complex.slitPlane := by
    simpa only [modularPhiDomain, Set.mem_ofPred_eq] using hdom
  have hwne : etaDenom M τ ≠ 0 := fun h => Complex.zero_notMem_slitPlane (h ▸ hwslit)
  have hNpos : 0 < ‖etaDenom M τ‖ := norm_pos_iff.2 hwne
  have hadm : AdmissibleB (Complex.sqrt (etaDenom M τ)) :=
    sqrt_re_pos_of_mem_slitPlane hwslit
  have hnorm_sqrt : ‖Complex.sqrt (etaDenom M τ)‖ = Real.sqrt ‖etaDenom M τ‖ := by
    have h2 : ‖Complex.sqrt (etaDenom M τ)‖ ^ 2 = ‖etaDenom M τ‖ := by
      rw [sq, ← norm_mul, EtaMultiplierAux.sqrt_mul_self]
    calc ‖Complex.sqrt (etaDenom M τ)‖
        = Real.sqrt (‖Complex.sqrt (etaDenom M τ)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ‖etaDenom M τ‖ := by rw [h2]
  have hre_sqrt : (Complex.sqrt (etaDenom M τ)).re =
      Real.sqrt ((‖etaDenom M τ‖ + (etaDenom M τ).re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]
    simp only [Complex.add_re, Complex.ofReal_re]
    split_ifs <;> simp
  have hmod : sqrtLower M τ₀ ≤ ‖Complex.sqrt (etaDenom M τ)‖ := by
    rw [hnorm_sqrt, sqrtLower]
    exact Real.sqrt_le_sqrt (hre.trans (Complex.re_le_norm _))
  have hmod' : ‖Complex.sqrt (etaDenom M τ)‖ ≤ sqrtUpper M τ₀ := by
    rw [hnorm_sqrt, sqrtUpper]
    exact Real.sqrt_le_sqrt hnorm
  have hargb : |(Complex.sqrt (etaDenom M τ)).arg| ≤ α / 8 := by
    have hb0 : Complex.sqrt (etaDenom M τ) ≠ 0 :=
      sqrt_ne_zero_of_mem_slitPlane hwslit
    have hcos_b : Real.cos (Complex.sqrt (etaDenom M τ)).arg =
        Real.sqrt ((1 + Real.cos (etaDenom M τ).arg) / 2) := by
      rw [Complex.cos_arg hb0, hre_sqrt, hnorm_sqrt]
      have hwre : (etaDenom M τ).re = ‖etaDenom M τ‖ * Real.cos (etaDenom M τ).arg :=
        (Complex.norm_mul_cos_arg _).symm
      rw [hwre]
      have hfac : (‖etaDenom M τ‖ + ‖etaDenom M τ‖ * Real.cos (etaDenom M τ).arg) / 2 =
          ‖etaDenom M τ‖ * ((1 + Real.cos (etaDenom M τ).arg) / 2) := by ring
      rw [hfac, Real.sqrt_mul hNpos.le]
      field_simp
    have hcos_half : Real.cos (Complex.sqrt (etaDenom M τ)).arg =
        Real.cos ((etaDenom M τ).arg / 2) := by
      rw [hcos_b, Real.cos_half (Complex.arg_mem_Ioc _).1.le (Complex.arg_mem_Ioc _).2]
    have hcos_abs : Real.cos |(Complex.sqrt (etaDenom M τ)).arg| =
        Real.cos |(etaDenom M τ).arg / 2| := by
      rw [Real.cos_abs, Real.cos_abs, hcos_half]
    have hmem1 : |(Complex.sqrt (etaDenom M τ)).arg| ∈ Set.Icc 0 Real.pi :=
      ⟨abs_nonneg _, Complex.abs_arg_le_pi _⟩
    have hmem2 : |(etaDenom M τ).arg / 2| ∈ Set.Icc 0 Real.pi :=
      ⟨abs_nonneg _, by
        rw [abs_div]
        have := Complex.abs_arg_le_pi (etaDenom M τ)
        norm_num
        linarith [Real.pi_pos]⟩
    have heq : |(Complex.sqrt (etaDenom M τ)).arg| = |(etaDenom M τ).arg / 2| :=
      Real.injOn_cos hmem1 hmem2 hcos_abs
    rw [heq, abs_div]
    have h3 : |(2 : ℝ)| = 2 := by norm_num
    rw [h3]
    linarith
  exact ⟨hadm, hmod, hmod', hargb⟩

/--
The actual input, without adding any analytic property to Family; [RW26, p. 6, p. 7, (19), Lemma 1]
is directional only.
-/
theorem sqrtParameters_family (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    Sector.Family (sqrtParameters M τ₀ (parameterRadius M τ₀ α)) (α / 8) (α / 2) := by
  have hb := fun b (hb : b ∈ sqrtParameters M τ₀ (parameterRadius M τ₀ α)) =>
    sqrtParameters_bounds M hM τ₀ α hT hα hα' hb
  exact
    { compact := sqrtParameters_isCompact M hM τ₀ α hT hα hα'
      admissible := fun b hbm => (hb b hbm).1
      arg_le := fun b hbm => (hb b hbm).2.2.2
      beta_nonneg := by linarith
      kappa_pos := by linarith
      angle_lt := by linarith }

/--
Explicit positive lower margin, including nonempty real centers. The margin is formalized here.
[RW26, p. 7, Lemma 1].
-/
theorem margin_pos (M : SL(2, ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) : 0 < margin M τ₀ α := by
  have hlow : 0 < sqrtLower M τ₀ := by
    rw [sqrtLower]
    exact Real.sqrt_pos.2 (by linarith)
  have hup : 0 < sqrtUpper M τ₀ := by
    rw [sqrtUpper]
    exact Real.sqrt_pos.2 (by linarith)
  have hsin : 0 < Real.sin (α / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  unfold margin
  exact mul_pos (lt_min hlow (by positivity)) hsin

/--
UniformMargin for both b and b⁻¹, on the whole rotation interval; [RW26, p. 6, (19)] supplies the
factors.
-/
theorem margin_uniform (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    Sector.UniformMargin (sqrtParameters M τ₀ (parameterRadius M τ₀ α))
      (Sector.opening (α / 8) (α / 2)) (margin M τ₀ α) := by
  have hm : 0 < margin M τ₀ α := margin_pos M τ₀ α hT hα hα'
  have hsin : 0 < Real.sin (α / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin_nonneg : 0 ≤ Real.sin (α / 2) := hsin.le
  have hlow : 0 < sqrtLower M τ₀ := by
    rw [sqrtLower]; exact Real.sqrt_pos.2 (by linarith)
  have hup : 0 < sqrtUpper M τ₀ := by
    rw [sqrtUpper]; exact Real.sqrt_pos.2 (by linarith)
  refine ⟨hm, ?_⟩
  intro b hb θ hθ
  obtain ⟨hadm, hmod, hmod', harg⟩ := sqrtParameters_bounds M hM τ₀ α hT hα hα' hb
  have hbpos : 0 < ‖b‖ := by
    have hre : 0 < b.re := hadm
    exact norm_pos_iff.2 (by intro h0; rw [h0] at hre; simp at hre)
  have habsθ : |θ| ≤ Sector.opening (α / 8) (α / 2) := abs_le.2 hθ
  rw [Sector.opening] at habsθ
  have hsize : |b.arg + θ| ≤ Real.pi / 2 - α / 2 := by
    have h1 := abs_add_le b.arg θ
    linarith
  have hy : Real.pi / 2 - α / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hcos : Real.sin (α / 2) ≤ Real.cos (b.arg + θ) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (b.arg + θ)) hy hsize
    rwa [Real.cos_pi_div_two_sub, Real.cos_abs] at h
  have rot_re : ∀ c : ℂ, (c * Sector.rotation θ).re = ‖c‖ * Real.cos (c.arg + θ) := by
    intro c
    have hrot : Sector.rotation θ = Complex.exp ((θ : ℂ) * Complex.I) := by
      unfold Sector.rotation
      rw [mul_comm]
    have hc : c = (‖c‖ : ℂ) * Complex.exp (c.arg * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I c).symm
    have hmul : c * Sector.rotation θ =
        (‖c‖ : ℂ) * Complex.exp (((c.arg + θ : ℝ) : ℂ) * Complex.I) := by
      rw [hrot]
      conv_lhs => rw [hc]
      rw [mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    rw [hmul, Complex.mul_re, Complex.exp_ofReal_mul_I_re (c.arg + θ)]
    simp
  have hmargin_le : margin M τ₀ α ≤ sqrtLower M τ₀ * Real.sin (α / 2) := by
    unfold margin
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hsin_nonneg
  have hmargin_inv : margin M τ₀ α ≤ (1 / sqrtUpper M τ₀) * Real.sin (α / 2) := by
    unfold margin
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hsin_nonneg
  constructor
  · unfold Sector.rotatedRe
    rw [rot_re b]
    calc margin M τ₀ α ≤ sqrtLower M τ₀ * Real.sin (α / 2) := hmargin_le
      _ ≤ ‖b‖ * Real.cos (b.arg + θ) :=
          mul_le_mul hmod hcos hsin_nonneg (norm_nonneg b)
  · unfold Sector.rotatedInvRe
    rw [rot_re b⁻¹]
    have harg_inv : (b⁻¹).arg = -b.arg := by
      rw [Complex.arg_inv]
      have hne : b.arg ≠ Real.pi := by
        intro h
        rw [h, abs_of_pos Real.pi_pos] at harg
        linarith
      simp [hne]
    have hsize_inv : |(b⁻¹).arg + θ| ≤ Real.pi / 2 - α / 2 := by
      rw [harg_inv]
      have h1 : |(-b.arg) + θ| ≤ |b.arg| + |θ| := by
        simpa [abs_neg] using abs_add_le (-b.arg) θ
      linarith
    have hcos_inv : Real.sin (α / 2) ≤ Real.cos ((b⁻¹).arg + θ) := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hy hsize_inv
      rwa [Real.cos_pi_div_two_sub, Real.cos_abs] at h
    have hnorm_inv : (1 : ℝ) / sqrtUpper M τ₀ ≤ ‖b⁻¹‖ := by
      rw [norm_inv, inv_eq_one_div]
      exact one_div_le_one_div_of_le hbpos hmod'
    calc margin M τ₀ α ≤ (1 / sqrtUpper M τ₀) * Real.sin (α / 2) := hmargin_inv
      _ ≤ ‖b⁻¹‖ * Real.cos ((b⁻¹).arg + θ) :=
          mul_le_mul hnorm_inv hcos_inv hsin_nonneg (norm_nonneg _)

/--
One admissible height and one positive rate, fixed before τ,z,r,n; [RW26, p. 7, Lemma 1].
-/
theorem height_safe_rate_pos (M : SL(2, ℤ)) (τ₀ α : ℝ)
    (hT : 0 < realDenom M τ₀) (hα : 0 < α) (hα' : α < Real.pi / 2) :
    Sector.SafeHeight (margin M τ₀ α) (height M τ₀ α) ∧ 0 < rate M τ₀ α := by
  have hm : 0 < margin M τ₀ α := margin_pos M τ₀ α hT hα hα'
  have hup : 0 < sqrtUpper M τ₀ := by
    rw [sqrtUpper]
    exact Real.sqrt_pos.2 (by linarith)
  constructor
  · unfold Sector.SafeHeight height
    constructor
    · positivity
    · nlinarith [Real.pi_pos]
  · unfold rate height
    positivity

/--
Literal affine decomposition; no q quotient or germ evaluation; [RW26, p. 6, (19)].
-/
theorem factorPoint_split (M : SL(2, ℤ)) (r n : ℤ) (j : ℕ) (z τ : ℂ) :
    (modularPhiFactorPoint M r n j z τ).2 =
      Complex.I * z / Complex.sqrt (etaDenom M τ) + factorOffset M r n j τ := by
  by_cases h : Complex.sqrt (etaDenom M τ) = 0
  · simp [factorOffset, modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput, h]
  · simp only [factorOffset, modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput]
    field_simp
    ring

/--
A single offset bound for the finite family and all disk parameters;
works for an empty family too; [RW26, p. 6, (19)].
-/
theorem factorOffset_uniform_bound (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (F : Finset (ℤ × ℤ)) (τ₀ α : ℝ) (hT : 0 < realDenom M τ₀)
    (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      ∀ i ∈ F, ∀ j ∈ Finset.range (M 1 0).toNat,
        ‖factorOffset M i.1 i.2 j τ‖ ≤ A := by
  classical
  have hc0 : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hmaps : Set.MapsTo (fun τ : ℂ => etaDenom M τ)
      (parameterDisk τ₀ (parameterRadius M τ₀ α)) Complex.slitPlane := by
    intro τ hτ
    have h := (parameterDisk_denom_control M hM τ₀ α hT hα hα' hτ).2.2.2
    simpa only [modularPhiDomain, Set.mem_ofPred_eq] using h
  have hden : ContinuousOn (fun τ : ℂ => etaDenom M τ)
      (parameterDisk τ₀ (parameterRadius M τ₀ α)) := by
    unfold etaDenom
    fun_prop
  have hsqrt : ContinuousOn (fun τ : ℂ => Complex.sqrt (etaDenom M τ))
      (parameterDisk τ₀ (parameterRadius M τ₀ α)) :=
    Complex.continuousOn_sqrt.comp hden hmaps
  have hne : ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
      Complex.sqrt (etaDenom M τ) ≠ 0 :=
    fun τ hτ => sqrt_ne_zero_of_mem_slitPlane (hmaps hτ)
  have hsingle : ∀ (i : ℤ × ℤ) (j : ℕ), ∃ C : ℝ,
      ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
        ‖factorOffset M i.1 i.2 j τ‖ ≤ C := by
    intro i j
    have hformula : (fun τ : ℂ => factorOffset M i.1 i.2 j τ) =
        fun τ : ℂ => Complex.I *
            ((((i.1 : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M i.1 i.2 j : ℂ))) /
              Complex.sqrt (etaDenom M τ)
          - Complex.I * Complex.sqrt (etaDenom M τ) / 2
          + Complex.I / (2 * Complex.sqrt (etaDenom M τ)) := by
      funext τ
      simp [factorOffset, modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput]
    simp only [hformula]
    apply IsCompact.exists_bound_of_continuousOn (isCompact_closedBall _ _)
    have hnum : ContinuousOn
        (fun τ : ℂ => Complex.I *
          ((((i.1 : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M i.1 i.2 j : ℂ))))
        (parameterDisk τ₀ (parameterRadius M τ₀ α)) := by
      fun_prop
    have h1 : ContinuousOn
        (fun τ : ℂ => Complex.I *
          ((((i.1 : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M i.1 i.2 j : ℂ))) /
            Complex.sqrt (etaDenom M τ))
        (parameterDisk τ₀ (parameterRadius M τ₀ α)) :=
      hnum.div hsqrt hne
    have h2 : ContinuousOn
        (fun τ : ℂ => Complex.I * Complex.sqrt (etaDenom M τ) / 2)
        (parameterDisk τ₀ (parameterRadius M τ₀ α)) :=
      hsqrt.const_mul Complex.I |>.div continuousOn_const (fun _ _ => two_ne_zero)
    have h3 : ContinuousOn
        (fun τ : ℂ => Complex.I / (2 * Complex.sqrt (etaDenom M τ)))
        (parameterDisk τ₀ (parameterRadius M τ₀ α)) :=
      continuousOn_const.div (hsqrt.const_mul 2)
        (fun τ hτ => mul_ne_zero two_ne_zero (hne τ hτ))
    exact h1.sub h2 |>.add h3
  obtain ⟨Cf, hCf1, hCf⟩ : ∃ Cf : ℝ, 1 ≤ Cf ∧
      ∀ i ∈ F, ∀ j ∈ Finset.range (M 1 0).toNat,
        ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
          ‖factorOffset M i.1 i.2 j τ‖ ≤ Cf := by
    induction F using Finset.induction_on with
    | empty => exact ⟨1, le_rfl, by simp⟩
    | insert a s ha ih =>
      obtain ⟨A, hA1, hA⟩ := ih
      have hb : ∃ B : ℝ, ∀ j ∈ Finset.range (M 1 0).toNat,
          ∀ τ ∈ parameterDisk τ₀ (parameterRadius M τ₀ α),
            ‖factorOffset M a.1 a.2 j τ‖ ≤ B := by
        induction (Finset.range (M 1 0).toNat) using Finset.induction_on with
        | empty => exact ⟨0, by simp⟩
        | insert b t hbt iht =>
          obtain ⟨B, hB⟩ := iht
          obtain ⟨B', hB'⟩ := hsingle a b
          refine ⟨max B B', ?_⟩
          intro j hj τ hτ
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact (hB' τ hτ).trans (le_max_right _ _)
          · exact (hB j hj τ hτ).trans (le_max_left _ _)
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, le_trans hA1 (le_max_left _ _), ?_⟩
      intro i hi j hj τ hτ
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact (hB j hj τ hτ).trans (le_max_right _ _)
      · exact (hA i hi j hj τ hτ).trans (le_max_left _ _)
  exact ⟨max 1 Cf, le_max_left _ _,
    fun τ hτ i hi j hj => (hCf i hi j hj τ hτ).trans (le_max_right _ _)⟩

end SICLean.L4.ModularSector

#check SICLean.L4.modularPhiFactorPoint_z_slope
#check SICLean.L4.modularPhi_sqrt_admissible
#check SICLean.L4.Sector.phiExtended_sector_decay_with_margin
#print SICLean.L4.modularPhiFactorPoint
#print SICLean.L4.ModularSector.rate
