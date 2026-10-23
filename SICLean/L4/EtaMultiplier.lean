import SICLean.L4.QProduct
import SICLean.L4.EtaMultiplierAux

set_option autoImplicit false

/-!
# The η function, its common multiplier, and real phases

The separately developed q-product statements are
imported as dependencies.

[RW26, p. 3].

We reuse `ModularForm.eta: ℂ → ℂ`, its nonvanishing/holomorphy,
`ModularForm.eta_comp_eq_csqrt_I_inv`, and the weight-12 cusp form `CuspForm.discriminant`. We do
not redevelop the S transformation. The minimal route is Δ=η^24, its SL₂ transformation, the
principal square root, continuity of the actual quotient on the connected upper half-plane, and its
finite 24th-root image. No full multiplier cocycle or Dedekind sum is required.

`etaMultiplier M` is the actual quotient at `i`, not a chosen constant with postulated properties.
Matrices are bare `SL(2, ℤ)`; positive lower-left entries occur as explicit theorem hypotheses.
Translations are stated separately. The phase extends to a complex neighborhood of every real point
with `c*τ₀+d>0`. Only that η-free phase has a two-sided limit. The original q quotient is used and
limited from the upper half-plane only.

The last six statements are the scalar/matrix part, not a definition or proof of the Φ or
pseudolattice distribution relation. In particular `etaKappa = μ_I^2 / μ_J` is retained, with exact
`etaKappa^24=1`.
-/

noncomputable section

open Set Filter
open scoped MatrixGroups UpperHalfPlane Topology

namespace SICLean.L4

/-- RW's `e(x)`. In particular `e(τ/24)` is not a principal `q^(1/24)`. -/
def e (x : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * x)

/-- The automorphy factor, as an actual complex affine function. -/
def etaDenom (M : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (M 1 0 : ℂ) * z + (M 1 1 : ℂ)

/-- Raw complex Möbius function; total division is used outside its valid domain. It is compared
with the actual action on `ℍ` below. -/
def etaMobius (M : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((M 0 0 : ℂ) * z + (M 0 1 : ℂ)) / etaDenom M z

/-- The actual η quotient, with the principal complex square root. -/
def etaRatio (M : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  ModularForm.eta ((M • τ : ℍ) : ℂ) /
    (Complex.sqrt (etaDenom M τ) * ModularForm.eta τ)

/-- The same quotient at `i`; constancy and order are separate theorems. -/
def etaMultiplier (M : SL(2, ℤ)) : ℂ := etaRatio M UpperHalfPlane.I

/-- η-free expression. This formula, rather than the q products or η itself, is continued to the
real boundary. -/
def etaPhase (M : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (etaMultiplier M)⁻¹ * Complex.sqrt (etaDenom M z) *
    e ((etaMobius M z - z) / 24)

/-- Explicit slit-plane preimage. Real points with positive denominator are interior points, not
boundary points of this complex domain. -/
def etaPhaseDomain (M : SL(2, ℤ)) : Set ℂ :=
  {z : ℂ | etaDenom M z ∈ Complex.slitPlane}

/-- The later pseudolattice bridge must instantiate these same actual multipliers. -/
def etaKappa (MI MJ : SL(2, ℤ)) : ℂ :=
  etaMultiplier MI ^ 2 / etaMultiplier MJ

/-- Bridge to the Mathlib action `UpperHalfPlane.SLAction`; no second action is introduced. Cf.
[RW26, p. 3]. -/
theorem coe_smul_eq_etaMobius (M : SL(2, ℤ)) (τ : ℍ) :
    ((M • τ : ℍ) : ℂ) = etaMobius M τ := by
  simpa [etaMobius, etaDenom] using UpperHalfPlane.coe_specialLinearGroup_apply M τ

/-- Mathlib `Complex.exp_ne_zero`, in the normalization used here. -/
theorem e_ne_zero (z : ℂ) : e z ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- Mathlib `UpperHalfPlane.norm_exp_two_pi_I_lt_one`; together with `e_ne_zero`, this supplies
`0 < ‖q‖ < 1`. -/
theorem norm_e_lt_one (τ : ℍ) : ‖e τ‖ < 1 := by
  exact UpperHalfPlane.norm_exp_two_pi_I_lt_one τ

/-- Positive-c domain check: the denominator has positive imaginary part. -/
theorem etaDenom_im_pos (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ) :
    0 < (etaDenom M τ).im := by
  simpa [etaDenom] using mul_pos (show (0 : ℝ) < (M 1 0 : ℝ) by exact_mod_cast hM) τ.im_pos

/-- Same domain check, in the form required by Mathlib's principal sqrt. -/
theorem etaDenom_mem_slitPlane (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ) :
    etaDenom M τ ∈ Complex.slitPlane := by
  exact Or.inr (ne_of_gt (etaDenom_im_pos M hM τ))

/-- Explicit denominator nonvanishing for the η quotient. -/
theorem etaDenom_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ) :
    etaDenom M τ ≠ 0 := by
  intro h
  have hi := etaDenom_im_pos M hM τ
  simp [h] at hi

/-- Exact comparison with Mathlib `eta`, `eta_q_eq_pow` and `Function.Periodic.qParam`. It is an
equality of the total definitions, even outside `ℍ`. -/
theorem eta_eq_e_mul_qPochhammer (z : ℂ) :
    ModularForm.eta z = e (z / 24) * qPochhammer (e z) (e z) := by
  exact EtaMultiplierAux.eta_eq_exp_mul_qPochhammer z

/-- Integer T phase from the actual product. The periodic q factors are equal term by term, so no
upper-plane hypothesis is needed. -/
theorem eta_add_int (z : ℂ) (k : ℤ) :
    ModularForm.eta (z + (k : ℂ)) =
      e ((k : ℂ) / 24) * ModularForm.eta z := by
  have he : e (z + (k : ℂ)) = e z := by
    unfold e
    rw [mul_add, Complex.exp_add]
    have hk : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
      simpa only [mul_comm] using Complex.exp_int_mul_two_pi_mul_I k
    rw [hk, mul_one]
  rw [eta_eq_e_mul_qPochhammer, eta_eq_e_mul_qPochhammer, he]
  unfold e
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Translations have lower-left entry zero and are treated separately. -/
theorem etaRatio_T_zpow (k : ℤ) (τ : ℍ) :
    etaRatio (ModularGroup.T ^ k) τ = e ((k : ℂ) / 24) := by
  have hd : etaDenom (ModularGroup.T ^ k) τ = 1 := by
    simp [etaDenom, ModularGroup.coe_T_zpow]
  have ha : (((ModularGroup.T ^ k) • τ : ℍ) : ℂ) = (τ : ℂ) + (k : ℂ) := by
    rw [UpperHalfPlane.modular_T_zpow_smul]
    simp [UpperHalfPlane.coe_vadd, add_comm]
  rw [etaRatio, hd, Complex.sqrt_one, one_mul, ha, eta_add_int]
  exact mul_div_cancel_right₀ _ (ModularForm.eta_ne_zero τ.2)

/-- Same actual quotient, specialized at `i`. -/
theorem etaMultiplier_T_zpow (k : ℤ) :
    etaMultiplier (ModularGroup.T ^ k) = e ((k : ℂ) / 24) := by
  exact etaRatio_T_zpow k UpperHalfPlane.I

/-- Exact order for the separate translation case, including negative k. -/
theorem etaMultiplier_T_zpow_pow_twentyFour (k : ℤ) :
    etaMultiplier (ModularGroup.T ^ k) ^ 24 = 1 := by
  rw [etaMultiplier_T_zpow, e, ← Complex.exp_nat_mul]
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  congr 1
  ring

/-- Calibration wrapper for the Mathlib S transformation `ModularForm.eta_comp_eq_csqrt_I_inv`; not
a new proof of that transformation. -/
theorem etaMultiplier_S : etaMultiplier ModularGroup.S = e (-1 / 8) := by
  have hd : etaDenom ModularGroup.S (UpperHalfPlane.I : ℂ) = Complex.I := by
    simp [etaDenom, ModularGroup.S]
  have hs := ModularForm.eta_comp_eq_csqrt_I_inv UpperHalfPlane.I.2
  have hη : ModularForm.eta (-1 / (UpperHalfPlane.I : ℂ)) =
      (Complex.sqrt Complex.I)⁻¹ *
        (Complex.sqrt (UpperHalfPlane.I : ℂ) * ModularForm.eta UpperHalfPlane.I) := hs
  have hm : (((ModularGroup.S • UpperHalfPlane.I : ℍ)) : ℂ) =
      -1 / (UpperHalfPlane.I : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [ModularGroup.S]
  have hsq : Complex.sqrt Complex.I ≠ 0 := by
    simp [Complex.sqrt]
  rw [etaMultiplier, etaRatio, hd, hm, hη]
  simp only [UpperHalfPlane.coe_I]
  rw [mul_div_cancel_right₀ _ (mul_ne_zero hsq
    (ModularForm.eta_ne_zero (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp)))]
  rw [sqrt_eq_exp Complex.I_ne_zero, ← Complex.exp_neg]
  unfold e
  congr 1
  rw [Complex.log_I]
  ring

/-- Principal square root power needed in the minimal Δ route. Mathlib's source-local
`csqrt_pow_24_eq` is not an exported API; the exported raw material is `Complex.cpow_nat_inv_pow`
(the sqrt is the complex half-power). -/
theorem eta_sqrt_pow_twentyFour (z : ℂ) : Complex.sqrt z ^ 24 = z ^ 12 := by
  rw [show 24 = 2 * 12 from rfl, pow_mul]
  simp [Complex.sqrt]

/-- `ModularForm.discriminant = eta^24` and the SL₂ transformation of `CuspForm.discriminant`. This
holds for every SL matrix, before restricting c. -/
theorem eta_pow_twentyFour_smul (M : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.eta ((M • τ : ℍ) : ℂ) ^ 24 =
      etaDenom M τ ^ 12 * ModularForm.eta τ ^ 24 := by
  have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ M) (by exact ⟨M, rfl⟩) τ
  dsimp [Matrix.SpecialLinearGroup.mapGL, algebraMap_int_eq] at h
  change ModularForm.discriminant _ = _ * ModularForm.discriminant τ at h
  simpa [CuspForm.coe_discriminant, ModularForm.discriminant,
    UpperHalfPlane.denom, etaDenom, Matrix.SpecialLinearGroup.mapGL_coe_matrix] using h

/-- Δ and the sqrt power put the actual quotient in the finite root set. -/
theorem etaRatio_pow_twentyFour (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ) :
    etaRatio M τ ^ 24 = 1 := by
  rw [etaRatio, div_pow, mul_pow, eta_sqrt_pow_twentyFour,
    eta_pow_twentyFour_smul]
  exact div_self (mul_ne_zero (pow_ne_zero _ (etaDenom_ne_zero M hM τ))
    (pow_ne_zero _ (ModularForm.eta_ne_zero τ.2)))

/-- Nonzero quotient, from Mathlib `eta_ne_zero` and the denominator check. -/
theorem etaRatio_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ) :
    etaRatio M τ ≠ 0 := by
  apply div_ne_zero (ModularForm.eta_ne_zero (M • τ).2)
  apply mul_ne_zero _ (ModularForm.eta_ne_zero τ.2)
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (etaDenom_ne_zero M hM τ))

/-- Continuity on the connected upper half-plane, using Mathlib η holomorphy and principal sqrt on
the slit plane. -/
theorem continuous_etaRatio (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    Continuous (etaRatio M) := by
  have hη : Continuous (fun τ : ℍ => ModularForm.eta (τ : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro τ
    exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.2).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt
  have hact : Continuous (fun τ : ℍ => (M • τ : ℍ)) := by
    change Continuous (fun τ : ℍ =>
      (Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) M) • τ : ℍ))
    exact continuous_const_smul _
  have hd : Continuous (fun τ : ℍ => etaDenom M τ) := by
    exact (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
  have hs : Continuous (fun τ : ℍ => Complex.sqrt (etaDenom M τ)) := by
    apply continuous_iff_continuousAt.mpr
    intro τ
    exact ContinuousAt.comp (f := fun τ : ℍ => etaDenom M τ)
      (Complex.differentiableAt_sqrt (etaDenom_mem_slitPlane M hM τ)).continuousAt hd.continuousAt
  exact (hη.comp hact).div (hs.mul hη) (fun τ =>
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (etaDenom_ne_zero M hM τ)))
      (ModularForm.eta_ne_zero τ.2))

/-- Connectedness plus the finite 24th-root image gives a common value. This is a conclusion about
the concrete quotient, not a definition of μ. -/
theorem etaRatio_eq_etaMultiplier (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ) :
    etaRatio M τ = etaMultiplier M := by
  have hfinite : Set.Finite {z : ℂ | z ^ 24 = 1} := by
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using
      Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 24)
        (1 : ℂ))
  exact isPreconnected_univ.constant_of_mapsTo hfinite.isDiscrete
    (continuous_etaRatio M hM).continuousOn
    (fun τ _ => etaRatio_pow_twentyFour M hM τ) (by trivial) (by trivial)


theorem etaMultiplier_pow_twentyFour (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    etaMultiplier M ^ 24 = 1 := by
  exact etaRatio_pow_twentyFour M hM UpperHalfPlane.I

/-- Common nonzero scalar for the later Fourier input. -/
theorem etaMultiplier_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    etaMultiplier M ≠ 0 := by
  exact etaRatio_ne_zero M hM UpperHalfPlane.I

/-- Algebraicity of μ from its exact power, not of all special E values. Mathlib
`IsIntegral.isAlgebraic` suffices. -/
theorem etaMultiplier_isAlgebraic (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    IsAlgebraic ℚ (etaMultiplier M) := by
  apply IsIntegral.isAlgebraic
  apply IsIntegral.of_pow (n := 24) (by norm_num)
  rw [etaMultiplier_pow_twentyFour M hM]
  exact isIntegral_one

/-- The required transformation, using the same actual μ as every later formula. -/
theorem eta_smul_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ) :
    ModularForm.eta ((M • τ : ℍ) : ℂ) =
      etaMultiplier M * Complex.sqrt (etaDenom M τ) * ModularForm.eta τ := by
  have hs : Complex.sqrt (etaDenom M τ) ≠ 0 := by
    simpa [Complex.sqrt] using etaDenom_ne_zero M hM τ
  have h := (div_eq_iff (mul_ne_zero hs (ModularForm.eta_ne_zero τ.2))).mp
    (etaRatio_eq_etaMultiplier M hM τ)
  simpa only [mul_assoc] using h


theorem qPochhammer_eta_prefactor_mul (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ) :
    etaDenom M τ * qPochhammer (e τ) (e τ) =
      etaPhase M τ * qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) := by
  have htrans := eta_smul_eq M hM τ
  simp only [coe_smul_eq_etaMobius, eta_eq_e_mul_qPochhammer] at htrans
  have he : e ((etaMobius M τ - (τ : ℂ)) / 24) =
      e (etaMobius M τ / 24) / e ((τ : ℂ) / 24) := by
    rw [sub_div]
    exact EtaMultiplierAux.exp_phase_sub _ _
  unfold etaPhase
  rw [he]
  calc
    etaDenom M τ * qPochhammer (e τ) (e τ) =
        (Complex.sqrt (etaDenom M τ) * Complex.sqrt (etaDenom M τ)) *
          qPochhammer (e τ) (e τ) := by rw [EtaMultiplierAux.sqrt_mul_self]
    _ = (etaMultiplier M)⁻¹ * Complex.sqrt (etaDenom M τ) *
        (etaMultiplier M * Complex.sqrt (etaDenom M τ) *
          (e ((τ : ℂ) / 24) * qPochhammer (e τ) (e τ))) /
            e ((τ : ℂ) / 24) := by
      field_simp [etaMultiplier_ne_zero M hM, e_ne_zero]
    _ = (etaMultiplier M)⁻¹ * Complex.sqrt (etaDenom M τ) *
        (e (etaMobius M τ / 24) *
          qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))) /
            e ((τ : ℂ) / 24) := by rw [← htrans]
    _ = _ := by ring

/-- Same with the transformed product's nonzero condition explicit. It follows independently from
`norm_e_lt_one` and `qPochhammer_q_ne_zero`. -/
theorem qPochhammer_eta_prefactor (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℍ)
    (hd : qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) ≠ 0) :
    etaDenom M τ *
      (qPochhammer (e τ) (e τ) /
        qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))) = etaPhase M τ := by
  rw [← mul_div_assoc, div_eq_iff hd]
  exact qPochhammer_eta_prefactor_mul M hM τ

/-- Topological domain obligation; no boundary η. -/
theorem etaPhaseDomain_isOpen (M : SL(2, ℤ)) : IsOpen (etaPhaseDomain M) := by
  exact Complex.isOpen_slitPlane.preimage (by unfold etaDenom; fun_prop)

/-- Positive real automorphy factors lie in the interior complex domain. -/
theorem real_mem_etaPhaseDomain (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT₀ : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) :
    (τ₀ : ℂ) ∈ etaPhaseDomain M := by
  change etaDenom M (τ₀ : ℂ) ∈ Complex.slitPlane
  apply Complex.mem_slitPlane_iff.mpr
  left
  simpa [etaDenom] using hT₀

/-- η-free holomorphy on the actual slit domain; includes both sides of a real point with positive
denominator. -/
theorem etaPhase_analyticOnNhd (M : SL(2, ℤ)) :
    AnalyticOnNhd ℂ (etaPhase M) (etaPhaseDomain M) := by
  have hden : AnalyticOnNhd ℂ (etaDenom M) Set.univ := by
    intro z _
    unfold etaDenom
    fun_prop
  have hsqrt : AnalyticOnNhd ℂ Complex.sqrt Complex.slitPlane :=
    Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane
  intro z hz
  have hd : AnalyticAt ℂ (etaDenom M) z := hden z (Set.mem_univ _)
  have hs : AnalyticAt ℂ (fun z => Complex.sqrt (etaDenom M z)) z :=
    (hsqrt (etaDenom M z) hz).comp hd
  have hm : AnalyticAt ℂ (etaMobius M) z := by
    apply AnalyticAt.div
    · fun_prop
    · exact hd
    · exact Complex.slitPlane_ne_zero hz
  unfold etaPhase e
  fun_prop

/-- Full complex-neighborhood limit of the η-free expression, with the phase retained away from a
fixed point. -/
theorem etaPhase_tendsto_real (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT₀ : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) :
    Tendsto (etaPhase M) (𝓝 (τ₀ : ℂ))
      (𝓝 ((etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) *
        e ((etaMobius M (τ₀ : ℂ) - (τ₀ : ℂ)) / 24))) := by
  have hc := (etaPhase_analyticOnNhd M (τ₀ : ℂ)
    (real_mem_etaPhaseDomain M τ₀ hT₀)).continuousAt
  have hs : Complex.sqrt (etaDenom M (τ₀ : ℂ)) =
      (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) :=
    EtaMultiplierAux.sqrt_affine_real (M 1 0) (M 1 1) τ₀ hT₀
  simpa only [etaPhase, hs] using hc.tendsto

/-- Actual η-free center value at a real fixed point. -/
theorem etaPhase_real_fixedPoint (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT₀ : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ)) :
    etaPhase M (τ₀ : ℂ) = (etaMultiplier M)⁻¹ *
      (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) := by
  have hs : Complex.sqrt (etaDenom M (τ₀ : ℂ)) =
      (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) :=
    EtaMultiplierAux.sqrt_affine_real (M 1 0) (M 1 1) τ₀ hT₀
  simp [etaPhase, hfix, hs, e]

/-- Same fixed-point limit; the fixed-point hypothesis is indispensable. -/
theorem etaPhase_tendsto_real_fixedPoint (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT₀ : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ)) :
    Tendsto (etaPhase M) (𝓝 (τ₀ : ℂ))
      (𝓝 ((etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ))) := by
  have he0 : e 0 = 1 := EtaMultiplierAux.exp_phase_zero
  simpa only [hfix, sub_self, zero_div, he0, mul_one] using
    etaPhase_tendsto_real M τ₀ hT₀

/-- The original q quotient is limited only from `ℍ`. We first eliminate η using the preceding
identity. No value/limit of η at τ₀ is assumed. -/
theorem qPochhammer_eta_prefactor_tendsto_real
    (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ₀ : ℝ)
    (hT₀ : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) :
    Tendsto
      (fun z : ℂ => etaDenom M z *
        (qPochhammer (e z) (e z) /
          qPochhammer (e (etaMobius M z)) (e (etaMobius M z))))
      (𝓝[UpperHalfPlane.upperHalfPlaneSet] (τ₀ : ℂ))
      (𝓝 ((etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) *
        e ((etaMobius M (τ₀ : ℂ) - (τ₀ : ℂ)) / 24))) := by
  apply (etaPhase_tendsto_real M τ₀ hT₀).mono_left
      nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  let τ : ℍ := ⟨z, hz⟩
  have hd : qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) ≠ 0 := by
    rw [← coe_smul_eq_etaMobius]
    exact qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _))
      (norm_e_lt_one (M • τ))
  exact (qPochhammer_eta_prefactor M hM τ hd).symm

/-- Both fixed-point automorphy factors are positive, A is positive-c or a translation, and the
conjugate has positive c. Cancel η in `ℍ` before taking limits of the sqrt factors. -/
theorem etaMultiplier_conjugate (M A : SL(2, ℤ)) (τ₀ : ℝ)
    (hM : 0 < M 1 0)
    (hA : 0 < A 1 0 ∨ ∃ k : ℤ, A = ModularGroup.T ^ k)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hTM : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hTA : 0 < (A 1 0 : ℝ) * τ₀ + (A 1 1 : ℝ))
    (hconj : 0 < (A * M * A⁻¹) 1 0) :
    etaMultiplier (A * M * A⁻¹) = etaMultiplier M := by
  have hdenom_mul (P Q : SL(2, ℤ)) (z : ℂ) (hQ : etaDenom Q z ≠ 0) :
      etaDenom (P * Q) z = etaDenom P (etaMobius Q z) * etaDenom Q z := by
    simp only [etaDenom, etaMobius, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul]
    unfold etaDenom at hQ
    field_simp [hQ]
    ring
  have hsmulA (τ : ℍ) : ModularForm.eta ((A • τ : ℍ) : ℂ) =
      etaMultiplier A * Complex.sqrt (etaDenom A τ) * ModularForm.eta τ := by
    rcases hA with hA | ⟨k, rfl⟩
    · exact eta_smul_eq A hA τ
    · rw [etaMultiplier_T_zpow]
      have hd : etaDenom (ModularGroup.T ^ k) τ = 1 := by
        simp [etaDenom, ModularGroup.coe_T_zpow]
      rw [hd, Complex.sqrt_one, mul_one]
      rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd, add_comm]
      exact eta_add_int τ k
  have hμA : etaMultiplier A ≠ 0 := by
    rcases hA with hA | ⟨k, rfl⟩
    · exact etaMultiplier_ne_zero A hA
    · rw [etaMultiplier_T_zpow]
      exact e_ne_zero _
  -- Cancel eta in the upper half-plane before extending any expression.
  have hcancel (τ : ℍ) :
      etaMultiplier (A * M * A⁻¹) *
          Complex.sqrt (etaDenom (A * M * A⁻¹) (etaMobius A τ)) *
          Complex.sqrt (etaDenom A τ) =
        etaMultiplier M * Complex.sqrt (etaDenom A (etaMobius M τ)) *
          Complex.sqrt (etaDenom M τ) := by
    have h1 := eta_smul_eq (A * M * A⁻¹) hconj (A • τ)
    have h2 := hsmulA (M • τ)
    have h3 := hsmulA τ
    have h4 := eta_smul_eq M hM τ
    have heq : (A * M * A⁻¹) • (A • τ) = A • (M • τ) := by
      simp only [mul_smul, inv_smul_smul]
    rw [heq, h2, h3, h4] at h1
    simp only [coe_smul_eq_etaMobius] at h1
    have hη := ModularForm.eta_ne_zero τ.im_pos
    apply mul_right_cancel₀ (mul_ne_zero hμA hη)
    calc
      _ = etaMultiplier (A * M * A⁻¹) *
        Complex.sqrt (etaDenom (A * M * A⁻¹) (etaMobius A τ)) *
        (etaMultiplier A * Complex.sqrt (etaDenom A τ) * ModularForm.eta τ) := by ring
      _ = _ := h1.symm
      _ = _ := by ring
  have hdenom_real (P : SL(2, ℤ)) :
      etaDenom P (τ₀ : ℂ) = (((P 1 0 : ℝ) * τ₀ + (P 1 1 : ℝ)) : ℂ) := by
    simp [etaDenom]
  have hDM : etaDenom M (τ₀ : ℂ) ≠ 0 := by
    rw [hdenom_real]
    exact_mod_cast ne_of_gt hTM
  have hDA : etaDenom A (τ₀ : ℂ) ≠ 0 := by
    rw [hdenom_real]
    exact_mod_cast ne_of_gt hTA
  have hDM_re : 0 < (etaDenom M (τ₀ : ℂ)).re := by
    simpa [etaDenom] using hTM
  have hDA_re : 0 < (etaDenom A (τ₀ : ℂ)).re := by
    simpa [etaDenom] using hTA
  have hCden : etaDenom (A * M * A⁻¹) (etaMobius A (τ₀ : ℂ)) =
      etaDenom M (τ₀ : ℂ) := by
    have hmat : A * M * A⁻¹ * A = A * M := by group
    have heq := congrArg (fun N => etaDenom N (τ₀ : ℂ)) hmat
    rw [hdenom_mul _ A _ hDA, hdenom_mul A M _ hDM, hfix] at heq
    apply mul_right_cancel₀ hDA
    simpa only [mul_comm (etaDenom A (τ₀ : ℂ)) (etaDenom M (τ₀ : ℂ))] using heq
  have hcdenom (P : SL(2, ℤ)) : Continuous (etaDenom P) := by
    unfold etaDenom
    fun_prop
  have hcmobius (P : SL(2, ℤ)) (hz : etaDenom P (τ₀ : ℂ) ≠ 0) :
      ContinuousAt (etaMobius P) (τ₀ : ℂ) := by
    unfold etaMobius
    exact (continuous_const.mul continuous_id |>.add continuous_const).continuousAt.div
      (hcdenom P).continuousAt hz
  have hsM : ContinuousAt (fun z => Complex.sqrt (etaDenom M z)) (τ₀ : ℂ) :=
    (Complex.continuousAt_sqrt (Or.inl hDM_re.le)).comp (hcdenom M).continuousAt
  have hsA : ContinuousAt (fun z => Complex.sqrt (etaDenom A z)) (τ₀ : ℂ) :=
    (Complex.continuousAt_sqrt (Or.inl hDA_re.le)).comp (hcdenom A).continuousAt
  have hsCA : ContinuousAt
      (fun z => Complex.sqrt (etaDenom (A * M * A⁻¹) (etaMobius A z))) (τ₀ : ℂ) := by
    apply (Complex.continuousAt_sqrt (Or.inl (by rw [hCden]; exact hDM_re.le))).comp
    exact (hcdenom (A * M * A⁻¹)).continuousAt.comp (hcmobius A hDA)
  have hsAM : ContinuousAt
      (fun z => Complex.sqrt (etaDenom A (etaMobius M z))) (τ₀ : ℂ) := by
    apply (Complex.continuousAt_sqrt (Or.inl (by rw [hfix]; exact hDA_re.le))).comp
    exact (hcdenom A).continuousAt.comp (hcmobius M hDM)
  -- This boundary step applies only to the continuous eta-free factors.
  have hboundary (F G : ℂ → ℂ)
      (hF : ContinuousAt F (τ₀ : ℂ)) (hG : ContinuousAt G (τ₀ : ℂ))
      (hEq : ∀ z : ℍ, F z = G z) : F (τ₀ : ℂ) = G (τ₀ : ℂ) := by
    let z : ℝ → ℂ := fun y => (τ₀ : ℂ) + (y : ℂ) * Complex.I
    have hz : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 (τ₀ : ℂ)) := by
      have hc : ContinuousAt z 0 := by dsimp [z]; fun_prop
      simpa only [z, Complex.ofReal_zero, zero_mul, add_zero] using
        hc.tendsto.mono_left nhdsWithin_le_nhds
    have heq : (fun y => F (z y)) =ᶠ[𝓝[>] (0 : ℝ)] (fun y => G (z y)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hzy : 0 < (z y).im := by simpa [z] using hy
      exact hEq ⟨z y, hzy⟩
    have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl _)
    exact tendsto_nhds_unique (hF.tendsto.comp hz) ((hG.tendsto.comp hz).congr' heq.symm)
  have heq := hboundary
    (fun z => etaMultiplier (A * M * A⁻¹) *
      Complex.sqrt (etaDenom (A * M * A⁻¹) (etaMobius A z)) *
      Complex.sqrt (etaDenom A z))
    (fun z => etaMultiplier M * Complex.sqrt (etaDenom A (etaMobius M z)) *
      Complex.sqrt (etaDenom M z))
    ((continuousAt_const.mul hsCA).mul hsA)
    ((continuousAt_const.mul hsAM).mul hsM) hcancel
  rw [hCden, hfix] at heq
  have hsM0 : Complex.sqrt (etaDenom M (τ₀ : ℂ)) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hDM)
  have hsA0 : Complex.sqrt (etaDenom A (τ₀ : ℂ)) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hDA)
  apply mul_right_cancel₀ (mul_ne_zero hsM0 hsA0)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using heq

/-- No norm approximation. -/
theorem etaKappa_pow_twentyFour (MI MJ : SL(2, ℤ))
    (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0) : etaKappa MI MJ ^ 24 = 1 := by
  rw [etaKappa, div_pow, ← pow_mul, Nat.mul_comm 2 24, pow_mul,
    etaMultiplier_pow_twentyFour MI hI, etaMultiplier_pow_twentyFour MJ hJ]
  norm_num

/-- Same exact quotient is nonzero, so division in the distribution is legal. -/
theorem etaKappa_ne_zero (MI MJ : SL(2, ℤ))
    (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0) : etaKappa MI MJ ≠ 0 := by
  exact div_ne_zero (pow_ne_zero 2 (etaMultiplier_ne_zero MI hI))
    (etaMultiplier_ne_zero MJ hJ)

/-- Algebraicity of κ alone. Its exact 24th power also supplies the input to the
`SICLean.L3.ValuationSupport.value_pow_eq_one`; no valuation is computed from the complex norm or
numerical phase. -/
theorem etaKappa_isAlgebraic (MI MJ : SL(2, ℤ))
    (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0) :
    IsAlgebraic ℚ (etaKappa MI MJ) := by
  apply IsAlgebraic.of_pow (show 0 < (24 : ℕ) by norm_num)
  rw [etaKappa_pow_twentyFour MI MJ hI hJ]
  exact isAlgebraic_one

/-- Positive c's are explicit. The same sqrt occurs at τ for MI and 2τ for MJ. All η denominators
are nonzero in `ℍ`. -/
theorem eta_doubling_quotient (MI MJ : SL(2, ℤ))
    (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hdouble : MJ 0 0 = MI 0 0 ∧ MJ 0 1 = 2 * MI 0 1 ∧
      2 * MJ 1 0 = MI 1 0 ∧ MJ 1 1 = MI 1 1) (τ : ℍ) :
    ModularForm.eta (2 * (τ : ℂ)) * ModularForm.eta (etaMobius MI τ) /
      (ModularForm.eta τ * ModularForm.eta (2 * etaMobius MI τ)) =
      etaMultiplier MI / etaMultiplier MJ := by
  let τ₂ : ℍ :=
    ⟨2 * (τ : ℂ), by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) τ.im_pos⟩
  have hcoe : (τ₂ : ℂ) = 2 * (τ : ℂ) := rfl
  have hden : etaDenom MJ τ₂ = etaDenom MI τ := by
    rcases hdouble with ⟨ha, hb, hc, hd⟩
    have hc' : (2 : ℂ) * (MJ 1 0 : ℂ) = (MI 1 0 : ℂ) := by exact_mod_cast hc
    simp only [etaDenom, hcoe, hd]
    rw [← hc']
    ring
  have hmob : etaMobius MJ τ₂ = 2 * etaMobius MI τ := by
    rcases hdouble with ⟨ha, hb, hc, hd⟩
    have hb' : (MJ 0 1 : ℂ) = 2 * (MI 0 1 : ℂ) := by exact_mod_cast hb
    unfold etaMobius
    rw [hden]
    simp only [hcoe, ha, hb']
    ring
  have hηI := eta_smul_eq MI hI τ
  rw [coe_smul_eq_etaMobius] at hηI
  have hηJ := eta_smul_eq MJ hJ τ₂
  rw [coe_smul_eq_etaMobius, hmob,
    hden, hcoe] at hηJ
  have hητ : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.im_pos
  have hη2τ : ModularForm.eta (2 * (τ : ℂ)) ≠ 0 :=
    ModularForm.eta_ne_zero τ₂.im_pos
  have hs : Complex.sqrt (etaDenom MI τ) ≠ 0 :=
    fun h => (pow_ne_zero 12 (etaDenom_ne_zero MI hI τ)) (by
      simpa [h] using (eta_sqrt_pow_twentyFour (etaDenom MI τ)).symm)
  have hμJ := etaMultiplier_ne_zero MJ hJ
  rw [hηI, hηJ]
  field_simp

/-- The q product version of the preceding identity, before division. This retains the nontrivial μ
ratio needed at
x=0,h; it does not state a Φ identity. -/
theorem qPochhammer_doubling_mul_eq_phase (MI MJ : SL(2, ℤ))
    (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hdouble : MJ 0 0 = MI 0 0 ∧ MJ 0 1 = 2 * MI 0 1 ∧
      2 * MJ 1 0 = MI 1 0 ∧ MJ 1 1 = MI 1 1) (τ : ℍ) :
    qPochhammer (-1) (e τ) =
      e ((etaMobius MI τ - (τ : ℂ)) / 24) *
        (etaMultiplier MI / etaMultiplier MJ) *
        qPochhammer (-1) (e (etaMobius MI τ)) := by
  have hη := eta_doubling_quotient MI MJ hI hJ hdouble τ
  have hητ : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.im_pos
  have hηT : ModularForm.eta (etaMobius MI τ) ≠ 0 := by
    rw [← coe_smul_eq_etaMobius]
    exact ModularForm.eta_ne_zero (MI • τ).im_pos
  have hη2T : ModularForm.eta (2 * etaMobius MI τ) ≠ 0 := by
    rw [← coe_smul_eq_etaMobius]
    apply ModularForm.eta_ne_zero
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) (MI • τ).im_pos
  have heτ := e_ne_zero ((τ : ℂ) / 24)
  have heT := e_ne_zero (etaMobius MI τ / 24)
  have hq (z : ℍ) : qPochhammer (-1) (e z) =
      2 * (ModularForm.eta (2 * (z : ℂ)) / ModularForm.eta z) / e ((z : ℂ) / 24) :=
    EtaMultiplierAux.qPochhammer_neg_one_eq_eta_double z
  have he_sub (z w : ℂ) : e (z - w) = e z / e w :=
    EtaMultiplierAux.exp_phase_sub z w
  have hqT := hq (MI • τ)
  rw [coe_smul_eq_etaMobius] at hqT
  rw [hq τ, hqT,
    show (etaMobius MI τ - (τ : ℂ)) / 24 =
      etaMobius MI τ / 24 - (τ : ℂ) / 24 by ring, he_sub]
  rw [← hη]
  field_simp

/-- The quotient version of the same identity, with its nonzero product explicit. At a real fixed
point the η-free phase
tends to 1, retaining μ_I/μ_J. -/
theorem qPochhammer_doubling_ratio_eq_phase (MI MJ : SL(2, ℤ))
    (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hdouble : MJ 0 0 = MI 0 0 ∧ MJ 0 1 = 2 * MI 0 1 ∧
      2 * MJ 1 0 = MI 1 0 ∧ MJ 1 1 = MI 1 1) (τ : ℍ)
    (hd : qPochhammer (-1) (e (etaMobius MI τ)) ≠ 0) :
    qPochhammer (-1) (e τ) / qPochhammer (-1) (e (etaMobius MI τ)) =
      e ((etaMobius MI τ - (τ : ℂ)) / 24) *
        (etaMultiplier MI / etaMultiplier MJ) := by
  rw [qPochhammer_doubling_mul_eq_phase MI MJ hI hJ hdouble τ]
  exact mul_div_cancel_right₀ _ hd

end SICLean.L4

-- Actual types in Mathlib. The Δ bridge must use the mapGL range,
-- not an assumed definitional equality with a differently written group.
#check ModularForm.eta
#print ModularForm.eta
#check ModularForm.eta_q_eq_pow
#check Function.Periodic.qParam
#check ModularForm.eta_ne_zero
#check ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
#check ModularForm.eta_comp_eq_csqrt_I_inv
#print ModularForm.discriminant
#check CuspForm.discriminant
#check SlashInvariantForm.slash_action_eqn''
#check Complex.cpow_nat_inv_pow
#check UpperHalfPlane.norm_exp_two_pi_I_lt_one
#check SICLean.L4.etaRatio_eq_etaMultiplier
#print SICLean.L4.etaMultiplier
#print SICLean.L4.etaKappa
#check SICLean.L4.etaPhase_tendsto_real
#check SICLean.L4.etaMultiplier_conjugate
