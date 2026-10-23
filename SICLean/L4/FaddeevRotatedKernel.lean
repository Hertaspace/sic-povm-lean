import SICLean.L4.FaddeevSectorGeometry

set_option autoImplicit false

/-!
The pole calculation. Both integer signs and both sinh pole families are retained. The Jacobian is
explicit before cancellation, so no new φ is defined here.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace SICLean.L4.Sector

def rotatedPoint (θ v t : ℝ) : ℂ := rotation θ * linePoint v t

def rotatedDenominator (b : ℂ) (θ v t : ℝ) : ℂ :=
  4 * Complex.sinh (b * rotatedPoint θ v t) *
    Complex.sinh (b⁻¹ * rotatedPoint θ v t) * linePoint v t

def amplitude (b : ℂ) (θ v t : ℝ) : ℂ := (rotatedDenominator b θ v t)⁻¹

/-- Pullback including du/dt. Its canceled form is a theorem below. -/
def rotatedKernel (b x : ℂ) (θ v t : ℝ) : ℂ :=
  kernel b x (rotatedPoint θ v t) * rotation θ

def firstKernelPole (b : ℂ) (k : ℤ) : ℂ :=
  Complex.I * (Real.pi : ℂ) * (k : ℂ) / b

def secondKernelPole (b : ℂ) (k : ℤ) : ℂ :=
  Complex.I * (Real.pi : ℂ) * (k : ℂ) * b

theorem rotatedPoint_ne_zero (θ v t : ℝ) (hv : 0 < v) :
    rotatedPoint θ v t ≠ 0 := by
  unfold rotatedPoint
  refine mul_ne_zero (rotation_ne_zero θ) ?_
  intro h
  have him := congrArg Complex.im h
  simp [linePoint] at him
  linarith

theorem norm_rotatedPoint (θ v t : ℝ) :
    ‖rotatedPoint θ v t‖ = ‖linePoint v t‖ := by
  unfold rotatedPoint
  rw [norm_mul, norm_rotation, one_mul]

theorem firstKernelPole_rotated_im (b : ℂ) (θ : ℝ) (k : ℤ) :
    (rotation (-θ) * firstKernelPole b k).im =
      Real.pi * (k : ℝ) * rotatedInvRe b (-θ) := by
  unfold firstKernelPole rotatedInvRe
  rw [div_eq_mul_inv]
  rw [show rotation (-θ) * (Complex.I * (Real.pi : ℂ) * (k : ℂ) * b⁻¹)
      = Complex.I * (rotation (-θ) * ((Real.pi : ℂ) * (k : ℂ) * b⁻¹)) by ring]
  rw [mul_comm Complex.I, Complex.mul_I_im]
  have hre : ((Real.pi : ℂ) * (k : ℂ) * b⁻¹ * rotation (-θ)).re =
      Real.pi * (k : ℝ) * (b⁻¹ * rotation (-θ)).re := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [show rotation (-θ) * ((Real.pi : ℂ) * (k : ℂ) * b⁻¹)
      = (Real.pi : ℂ) * (k : ℂ) * b⁻¹ * rotation (-θ) by ring]
  exact hre

theorem secondKernelPole_rotated_im (b : ℂ) (θ : ℝ) (k : ℤ) :
    (rotation (-θ) * secondKernelPole b k).im =
      Real.pi * (k : ℝ) * rotatedRe b (-θ) := by
  unfold secondKernelPole rotatedRe
  rw [show rotation (-θ) * (Complex.I * (Real.pi : ℂ) * (k : ℂ) * b)
      = Complex.I * (rotation (-θ) * ((Real.pi : ℂ) * (k : ℂ) * b)) by ring]
  rw [mul_comm Complex.I, Complex.mul_I_im]
  have hre : ((Real.pi : ℂ) * (k : ℂ) * b * rotation (-θ)).re =
      Real.pi * (k : ℝ) * (b * rotation (-θ)).re := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [show rotation (-θ) * ((Real.pi : ℂ) * (k : ℂ) * b)
      = (Real.pi : ℂ) * (k : ℂ) * b * rotation (-θ) by ring]
  exact hre

theorem firstKernelPole_positive_height {K : Set ℂ} {Θ lam : ℝ}
    (hlam : UniformMargin K Θ lam) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) (k : ℤ) (hk : 1 ≤ k) :
    Real.pi * lam ≤ (rotation (-θ) * firstKernelPole b k).im := by
  rw [firstKernelPole_rotated_im]
  have hθ' : -θ ∈ Icc (-Θ) Θ := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hR : lam ≤ rotatedInvRe b (-θ) := (hlam.2 b hb (-θ) hθ').2
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
  have hp : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h1 : Real.pi * lam ≤ Real.pi * (k : ℝ) * lam := by
    have := mul_le_mul_of_nonneg_left hk' (mul_nonneg hp hlam.1.le)
    linarith
  have h2 : Real.pi * (k : ℝ) * lam ≤ Real.pi * (k : ℝ) * rotatedInvRe b (-θ) :=
    mul_le_mul_of_nonneg_left hR (mul_nonneg hp hk0)
  linarith

theorem secondKernelPole_positive_height {K : Set ℂ} {Θ lam : ℝ}
    (hlam : UniformMargin K Θ lam) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) (k : ℤ) (hk : 1 ≤ k) :
    Real.pi * lam ≤ (rotation (-θ) * secondKernelPole b k).im := by
  rw [secondKernelPole_rotated_im]
  have hθ' : -θ ∈ Icc (-Θ) Θ := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hR : lam ≤ rotatedRe b (-θ) := (hlam.2 b hb (-θ) hθ').1
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
  have hp : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h1 : Real.pi * lam ≤ Real.pi * (k : ℝ) * lam := by
    have := mul_le_mul_of_nonneg_left hk' (mul_nonneg hp hlam.1.le)
    linarith
  have h2 : Real.pi * (k : ℝ) * lam ≤ Real.pi * (k : ℝ) * rotatedRe b (-θ) :=
    mul_le_mul_of_nonneg_left hR (mul_nonneg hp hk0)
  linarith

theorem firstKernelPole_negative_height {K : Set ℂ} {Θ lam : ℝ}
    (hlam : UniformMargin K Θ lam) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) (k : ℤ) (hk : k ≤ -1) :
    (rotation (-θ) * firstKernelPole b k).im ≤ -(Real.pi * lam) := by
  rw [firstKernelPole_rotated_im]
  have hθ' : -θ ∈ Icc (-Θ) Θ := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hR : lam ≤ rotatedInvRe b (-θ) := (hlam.2 b hb (-θ) hθ').2
  have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≤ 0 := by linarith
  have hp : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h1 : Real.pi * (k : ℝ) * rotatedInvRe b (-θ) ≤ Real.pi * (k : ℝ) * lam :=
    mul_le_mul_of_nonpos_left hR (mul_nonpos_of_nonneg_of_nonpos hp hk0)
  have h2 : Real.pi * (k : ℝ) * lam ≤ -(Real.pi * lam) := by
    have hp' : (0 : ℝ) ≤ Real.pi * lam := mul_nonneg hp hlam.1.le
    calc Real.pi * (k : ℝ) * lam = (Real.pi * lam) * (k : ℝ) := by ring
      _ ≤ (Real.pi * lam) * (-1) := mul_le_mul_of_nonneg_left hk' hp'
      _ = -(Real.pi * lam) := by ring
  linarith

theorem secondKernelPole_negative_height {K : Set ℂ} {Θ lam : ℝ}
    (hlam : UniformMargin K Θ lam) {b : ℂ} (hb : b ∈ K)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) (k : ℤ) (hk : k ≤ -1) :
    (rotation (-θ) * secondKernelPole b k).im ≤ -(Real.pi * lam) := by
  rw [secondKernelPole_rotated_im]
  have hθ' : -θ ∈ Icc (-Θ) Θ := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hR : lam ≤ rotatedRe b (-θ) := (hlam.2 b hb (-θ) hθ').1
  have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≤ 0 := by linarith
  have hp : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h1 : Real.pi * (k : ℝ) * rotatedRe b (-θ) ≤ Real.pi * (k : ℝ) * lam :=
    mul_le_mul_of_nonpos_left hR (mul_nonpos_of_nonneg_of_nonpos hp hk0)
  have h2 : Real.pi * (k : ℝ) * lam ≤ -(Real.pi * lam) := by
    have hp' : (0 : ℝ) ≤ Real.pi * lam := mul_nonneg hp hlam.1.le
    calc Real.pi * (k : ℝ) * lam = (Real.pi * lam) * (k : ℝ) := by ring
      _ ≤ (Real.pi * lam) * (-1) := mul_le_mul_of_nonneg_left hk' hp'
      _ = -(Real.pi * lam) := by ring
  linarith

theorem rotated_sinh_ne_zero {K : Set ℂ} {Θ lam v : ℝ}
    (hlam : UniformMargin K Θ lam) (hv : SafeHeight lam v)
    {b : ℂ} (hb : b ∈ K) (hb0 : b ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) (t : ℝ) :
    Complex.sinh (b * rotatedPoint θ v t) ≠ 0 ∧
      Complex.sinh (b⁻¹ * rotatedPoint θ v t) ≠ 0 := by
  have hθ' : -θ ∈ Icc (-Θ) Θ := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hR1 : lam ≤ (b⁻¹ * rotation (-θ)).re := (hlam.2 b hb (-θ) hθ').2
  have hR2 : lam ≤ (b * rotation (-θ)).re := (hlam.2 b hb (-θ) hθ').1
  have hinv1 : (b * rotation θ)⁻¹ = b⁻¹ * rotation (-θ) := by
    rw [mul_inv_rev, ← rotation_neg]
    exact mul_comm (rotation (-θ)) b⁻¹
  have hinv2 : (b⁻¹ * rotation θ)⁻¹ = b * rotation (-θ) := by
    rw [mul_inv_rev, ← rotation_neg, inv_inv]
    exact mul_comm (rotation (-θ)) b
  constructor
  · have hc : b * rotation θ ≠ 0 := mul_ne_zero hb0 (rotation_ne_zero θ)
    have hci : 0 < ((b * rotation θ)⁻¹).re := by
      rw [hinv1]; exact lt_of_lt_of_le hlam.1 hR1
    have hhp : v < Real.pi * ((b * rotation θ)⁻¹).re := by
      rw [hinv1]
      have hhalf : Real.pi * lam / 2 < Real.pi * lam := by
        linarith [mul_pos Real.pi_pos hlam.1]
      have hmono : Real.pi * lam ≤ Real.pi * (b⁻¹ * rotation (-θ)).re :=
        mul_le_mul_of_nonneg_left hR1 Real.pi_pos.le
      linarith [hv.2]
    have hsin := sinh_line_ne_zero (b * rotation θ) v t hc hci hv.1 hhp
    simpa only [rotatedPoint, mul_assoc] using hsin
  · have hc : b⁻¹ * rotation θ ≠ 0 :=
      mul_ne_zero (inv_ne_zero hb0) (rotation_ne_zero θ)
    have hci : 0 < ((b⁻¹ * rotation θ)⁻¹).re := by
      rw [hinv2]; exact lt_of_lt_of_le hlam.1 hR2
    have hhp : v < Real.pi * ((b⁻¹ * rotation θ)⁻¹).re := by
      rw [hinv2]
      have hhalf : Real.pi * lam / 2 < Real.pi * lam := by
        linarith [mul_pos Real.pi_pos hlam.1]
      have hmono : Real.pi * lam ≤ Real.pi * (b * rotation (-θ)).re :=
        mul_le_mul_of_nonneg_left hR2 Real.pi_pos.le
      linarith [hv.2]
    have hsin := sinh_line_ne_zero (b⁻¹ * rotation θ) v t hc hci hv.1 hhp
    simpa only [rotatedPoint, mul_assoc] using hsin

theorem rotatedDenominator_ne_zero {K : Set ℂ} {Θ lam v : ℝ}
    (hlam : UniformMargin K Θ lam) (hv : SafeHeight lam v)
    {b : ℂ} (hb : b ∈ K) (hb0 : b ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc (-Θ) Θ) (t : ℝ) :
    rotatedDenominator b θ v t ≠ 0 := by
  have hs := rotated_sinh_ne_zero hlam hv hb hb0 hθ t
  have hw : linePoint v t ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [linePoint] at him
    linarith [hv.1]
  unfold rotatedDenominator
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs.1) hs.2) hw

/-- du cancels the rotation in u; the last factor is t+iv, not u. -/
theorem rotatedKernel_eq (b x : ℂ) (θ v t : ℝ) :
    rotatedKernel b x θ v t =
      Complex.exp (-2 * Complex.I * x * rotatedPoint θ v t) * amplitude b θ v t := by
  unfold rotatedKernel kernel amplitude rotatedDenominator rotatedPoint
  have hR : rotation θ ≠ 0 := rotation_ne_zero θ
  set D : ℂ := 4 * Complex.sinh (b * (rotation θ * linePoint v t)) *
      Complex.sinh (b⁻¹ * (rotation θ * linePoint v t)) * linePoint v t with hD
  have hden : 4 * Complex.sinh (b * (rotation θ * linePoint v t)) *
      Complex.sinh (b⁻¹ * (rotation θ * linePoint v t)) * (rotation θ * linePoint v t)
      = rotation θ * D := by rw [hD]; ring
  rw [hden]
  rcases eq_or_ne D 0 with hD0 | hD0
  · rw [hD0]; simp
  · field_simp [hR, hD0]

theorem continuousOn_amplitude {K : Set ℂ} {Θ lam v : ℝ}
    (hK : ∀ b ∈ K, b ≠ 0) (hlam : UniformMargin K Θ lam) (hv : SafeHeight lam v) :
    ContinuousOn (fun p : (ℂ × ℝ) × ℝ => amplitude p.1.1 p.1.2 v p.2)
      ((K ×ˢ Icc (-Θ) Θ) ×ˢ (Set.univ : Set ℝ)) := by
  intro p hp
  have hb : p.1.1 ∈ K := hp.1.1
  have hθ : p.1.2 ∈ Icc (-Θ) Θ := hp.1.2
  have hne := rotatedDenominator_ne_zero hlam hv hb (hK p.1.1 hb) hθ p.2
  have hsin : Continuous (fun z : ℂ => Complex.sinh z) := by
    unfold Complex.sinh; fun_prop
  have hrot : Continuous rotation := by
    unfold rotation; fun_prop
  have hline : ContinuousAt (fun p : (ℂ × ℝ) × ℝ => linePoint v p.2) p := by
    unfold linePoint; fun_prop
  have hrotp : ContinuousAt (fun p : (ℂ × ℝ) × ℝ => rotation p.1.2) p :=
    hrot.continuousAt.comp (by fun_prop)
  have hbp : ContinuousAt (fun p : (ℂ × ℝ) × ℝ => p.1.1) p := by fun_prop
  have hbip : ContinuousAt (fun p : (ℂ × ℝ) × ℝ => p.1.1⁻¹) p :=
    hbp.inv₀ (hK p.1.1 hb)
  have harg1 : ContinuousAt (fun p : (ℂ × ℝ) × ℝ =>
      p.1.1 * (rotation p.1.2 * linePoint v p.2)) p :=
    hbp.mul (hrotp.mul hline)
  have harg2 : ContinuousAt (fun p : (ℂ × ℝ) × ℝ =>
      p.1.1⁻¹ * (rotation p.1.2 * linePoint v p.2)) p :=
    hbip.mul (hrotp.mul hline)
  have hsin1 : ContinuousAt (fun p : (ℂ × ℝ) × ℝ =>
      Complex.sinh (p.1.1 * (rotation p.1.2 * linePoint v p.2))) p :=
    hsin.continuousAt.comp harg1
  have hsin2 : ContinuousAt (fun p : (ℂ × ℝ) × ℝ =>
      Complex.sinh (p.1.1⁻¹ * (rotation p.1.2 * linePoint v p.2))) p :=
    hsin.continuousAt.comp harg2
  have hden : ContinuousAt (fun p : (ℂ × ℝ) × ℝ =>
      rotatedDenominator p.1.1 p.1.2 v p.2) p := by
    unfold rotatedDenominator
    exact ((continuousAt_const.mul hsin1).mul hsin2).mul hline
  exact (hden.inv₀ hne).continuousWithinAt

end SICLean.L4.Sector
