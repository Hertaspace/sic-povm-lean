import SICLean.L4.M75Gaussian
import SICLean.L4.G2SpecialValueBridge

set_option autoImplicit false

/-!
# (5) and the explicit full (7) imply Q3

The sole new analytic hypothesis is MatrixPentagon:
the attracting side of attracting_pentagon_iff_repelling, including
the origin term -N F⁺(0) at (0,0). Its definition below is the full equation,
not Fourier (6), Prop. 8, a Q3 assumption, or an arbitrary-function contract.
All values are existing actual point values. No germ is evaluated here.
The existing modularPhi / phiExtended / etaMultiplier and their branch
choices are unchanged. No premise u+u≠0 occurs anywhere. The full identity (7) uses (36) at (2u,-u).
[RW26, p. 3, p. 22, (5), (7), Theorem 10].
Identity (7) is used for every parameter, including the origin term. [RW26, (7)].
-/

noncomputable section

open scoped Classical BigOperators MatrixGroups
open SICLean.L4.G2.SpecialValueBridge

namespace SICLean.L3.M75.Doubling

/-- Explicit input (7), literally the left side of the existing bridge iff.
No assertion that it holds is built into this definition. -/
def MatrixPentagon (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) : Prop :=
  ∀ u v : L4.SpecialValueGroup M,
    normalizedValueSum M hM (fun x => L4.specialValuePairing M hM x u *
      (L4.specialValuePlus M hM x / L4.specialValueMinus M hM (x + v))) =
    L4.specialValuePlus M hM (u + v) /
      (L4.specialValueMinus M hM u * L4.specialValueMinus M hM v) -
        (if u = 0 ∧ v = 0 then
          (L4.specialValueOrder M : ℂ) * L4.specialValuePlus M hM 0 else 0)

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)

/--
Reflection at -z, including zero. F-minus is not replaced by E at zero; [RW26, p. 3, (5), footnote
2].
-/
theorem minus_inv (z : L4.SpecialValueGroup M) :
    (L4.specialValueMinus M hM z)⁻¹ =
      L4.specialValueGaussian M hM z * L4.specialValuePlus M hM (-z) := by
  have h := L4.specialValue_mixed_reflection M hM (-z)
  rw [neg_neg, M74.gaussian_neg] at h
  apply inv_eq_of_mul_eq_one_left
  rw [mul_assoc, h, mul_inv_cancel₀ (Gaussian.gaussian_ne_zero M hM z)]

/--
Off-zero two-E reflection, with its actual inverse normalization; [RW26, p. 3, (5), footnote 2].
-/
theorem plus_neg (u : L4.SpecialValueGroup M) (hu : u ≠ 0) :
    L4.specialValuePlus M hM (-u) =
      (L4.specialValueGaussian M hM u)⁻¹ * (L4.specialValuePlus M hM u)⁻¹ := by
  have h := minus_inv M hM u
  rw [← L4.specialValue_agree_off_zero M hM u hu] at h
  calc
    L4.specialValuePlus M hM (-u) =
        (L4.specialValueGaussian M hM u)⁻¹ *
          (L4.specialValueGaussian M hM u * L4.specialValuePlus M hM (-u)) := by
      rw [inv_mul_cancel_left₀ (Gaussian.gaussian_ne_zero M hM u)]
    _ = _ := by rw [← h]

/--
(u,-2u) is off the double origin even when 2u=0; the full identity (7); [RW26, p. 3, (7)].
-/
theorem doubling_correction_zero (u : L4.SpecialValueGroup M) (hu : u ≠ 0) :
    (if u = 0 ∧ -(u + u) = 0 then
      (L4.specialValueOrder M : ℂ) * L4.specialValuePlus M hM 0 else 0) = 0 := by
  simp only [hu, false_and, if_false]

/--
Reflect the denominator before the reindexing, including t=2u; [RW26, p. 3, (5), (7)]
(substitution).
-/
theorem ratio_summand (u t : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM t u *
        (L4.specialValuePlus M hM t / L4.specialValueMinus M hM (t - (u + u))) =
      L4.specialValuePairing M hM t u * L4.specialValueGaussian M hM (t - (u + u)) *
        L4.specialValuePlus M hM t * L4.specialValuePlus M hM (u + u - t) := by
  rw [div_eq_mul_inv, minus_inv]
  have ht : -(t - (u + u)) = u + u - t := by abel
  rw [ht]
  ring

/--
Exact t=u+s summand; in particular s=±u is retained; [RW26, p. 3, (3), (5)] (finite algebra).
-/
theorem shifted_summand (u s : L4.SpecialValueGroup M) :
    L4.specialValuePairing M hM (u + s) u *
        (L4.specialValuePlus M hM (u + s) /
          L4.specialValueMinus M hM (u + s - (u + u))) =
      L4.specialValueGaussian M hM u ^ 3 *
        (L4.specialValueGaussian M hM s * L4.specialValuePlus M hM (u + s) *
          L4.specialValuePlus M hM (u - s)) := by
  rw [ratio_summand]
  have hleft : u + s - (u + u) = s - u := by abel
  have hright : u + u - (u + s) = u - s := by abel
  rw [hleft, hright, mul_assoc _ _ (L4.specialValuePlus M hM (u - s)),
    ← mul_assoc, Gaussian.doubling_phase]
  ring

/--
Translation bijection t=u+s in the same actual finite group; [RW26, p. 3, (7)] (reindexing, no
analytic premise).
-/
theorem doubling_sum_reindex (u : L4.SpecialValueGroup M) :
    normalizedValueSum M hM (fun t => L4.specialValuePairing M hM t u *
      (L4.specialValuePlus M hM t / L4.specialValueMinus M hM (t - (u + u)))) =
      L4.specialValueGaussian M hM u ^ 3 *
        normalizedValueSum M hM (fun s => L4.specialValueGaussian M hM s *
          L4.specialValuePlus M hM (u + s) * L4.specialValuePlus M hM (u - s)) := by
  let : Fintype (L4.SpecialValueGroup M) :=
    @Fintype.ofFinite _ (L4.specialValueGroup_finite M hM)
  unfold normalizedValueSum
  rw [← Equiv.sum_comp (Equiv.addLeft u)]
  simp only [Equiv.coe_addLeft, shifted_summand]
  rw [← Finset.mul_sum]
  ring

/--
The only use of (7) is its explicit (u,-2u) instance; [RW26, p. 3, (7)] origin term.
-/
theorem pentagon_doubling_input (h7 : MatrixPentagon M hM)
    (u : L4.SpecialValueGroup M) (hu : u ≠ 0) :
    normalizedValueSum M hM (fun t => L4.specialValuePairing M hM t u *
      (L4.specialValuePlus M hM t / L4.specialValueMinus M hM (t - (u + u)))) =
      L4.specialValuePlus M hM (-u) /
        (L4.specialValueMinus M hM u * L4.specialValueMinus M hM (-(u + u))) := by
  have h := h7 u (-(u + u))
  rw [doubling_correction_zero M hM u hu, sub_zero] at h
  have hu' : u + -(u + u) = -u := by abel
  simpa only [← sub_eq_add_neg, hu'] using h

/--
The RHS before off-zero reflection: χ(u)·χ(2u)=χ(u)^5.
The second minus denominator may be the zero branch; [RW26, p. 3, (3), (5)].
-/
theorem doubling_rhs_gaussian (u : L4.SpecialValueGroup M) (hu : u ≠ 0) :
    L4.specialValuePlus M hM (-u) /
        (L4.specialValueMinus M hM u * L4.specialValueMinus M hM (-(u + u))) =
      L4.specialValueGaussian M hM u ^ 5 * L4.specialValuePlus M hM (-u) ^ 2 *
        L4.specialValuePlus M hM (u + u) := by
  rw [div_eq_mul_inv, mul_inv_rev, minus_inv, minus_inv, neg_neg,
    M74.gaussian_neg, Gaussian.gaussian_double]
  ring

/--
Cancellation uses only E(u)≠0 and u≠0, never 2u≠0; [RW26, p. 3, (5)].
-/
theorem doubling_rhs_reflection (u : L4.SpecialValueGroup M) (hu : u ≠ 0) :
    L4.specialValuePlus M hM (-u) /
        (L4.specialValueMinus M hM u * L4.specialValueMinus M hM (-(u + u))) =
      L4.specialValueGaussian M hM u ^ 3 *
        L4.specialValuePlus M hM (u + u) / L4.specialValuePlus M hM u ^ 2 := by
  rw [doubling_rhs_gaussian M hM u hu, plus_neg M hM u hu]
  field_simp [Gaussian.gaussian_ne_zero M hM u, L4.specialValuePlus_ne_zero M hM u]

/--
Normalized Q3, obtained from (5) and (7), for every nonzero u.
[RW26, p. 22, (36), Theorem 10].
-/
theorem doubling_normalized (h7 : MatrixPentagon M hM)
    (u : L4.SpecialValueGroup M) (hu : u ≠ 0) :
    L4.specialValuePlus M hM (u + u) = L4.specialValuePlus M hM u ^ 2 *
      normalizedValueSum M hM (fun s => L4.specialValueGaussian M hM s *
        L4.specialValuePlus M hM (u + s) * L4.specialValuePlus M hM (u - s)) := by
  have h := pentagon_doubling_input M hM h7 u hu
  rw [doubling_sum_reindex, doubling_rhs_reflection M hM u hu] at h
  have h' := mul_left_cancel₀ (pow_ne_zero 3 (Gaussian.gaussian_ne_zero M hM u))
    (show L4.specialValueGaussian M hM u ^ 3 *
        normalizedValueSum M hM (fun s => L4.specialValueGaussian M hM s *
          L4.specialValuePlus M hM (u + s) * L4.specialValuePlus M hM (u - s)) =
      L4.specialValueGaussian M hM u ^ 3 *
        (L4.specialValuePlus M hM (u + u) / L4.specialValuePlus M hM u ^ 2) by
      simpa only [mul_div_assoc] using h)
  have hE : L4.specialValuePlus M hM u ^ 2 ≠ 0 :=
    pow_ne_zero 2 (L4.specialValuePlus_ne_zero M hM u)
  calc
    L4.specialValuePlus M hM (u + u) =
        (L4.specialValuePlus M hM (u + u) / L4.specialValuePlus M hM u ^ 2) *
          L4.specialValuePlus M hM u ^ 2 := (div_mul_cancel₀ _ hE).symm
    _ = _ := by rw [← h']; ring

/--
Literal unnormalized Q3. The letI is the existing finite quotient's
Fintype choice, not a finiteness hypothesis or a different finite group; [RW26, p. 22, Theorem 10].
-/
theorem doubling (h7 : MatrixPentagon M hM)
    (u : L4.SpecialValueGroup M) (hu : u ≠ 0) :
    letI : Fintype (L4.SpecialValueGroup M) :=
      @Fintype.ofFinite _ (L4.specialValueGroup_finite M hM)
    (Real.sqrt (L4.specialValueOrder M : ℝ) : ℂ) * L4.specialValuePlus M hM (u + u) =
      L4.specialValuePlus M hM u ^ 2 * ∑ s : L4.SpecialValueGroup M,
        L4.specialValueGaussian M hM s * L4.specialValuePlus M hM (u + s) *
          L4.specialValuePlus M hM (u - s) := by
  let : Fintype (L4.SpecialValueGroup M) :=
    @Fintype.ofFinite _ (L4.specialValueGroup_finite M hM)
  have hsqrt : (Real.sqrt (L4.specialValueOrder M : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast L4.specialValueOrder_pos M hM
  have h := doubling_normalized M hM h7 u hu
  unfold normalizedValueSum at h
  dsimp only at h ⊢
  rw [h]
  field_simp

/--
Explicit nonzero order-two specialization, with E(0)=sqrt(epsilon); [RW26, p. 3, (4)] even-order
discussion, [RW26, p. 23].
-/
theorem doubling_orderTwo (h7 : MatrixPentagon M hM)
    (u : L4.SpecialValueGroup M) (hu : u ≠ 0) (h2u : u + u = 0) :
    letI : Fintype (L4.SpecialValueGroup M) :=
      @Fintype.ofFinite _ (L4.specialValueGroup_finite M hM)
    (Real.sqrt (L4.specialValueOrder M : ℝ) : ℂ) *
        (Real.sqrt (L4.specialValueEpsilon M) : ℂ) =
      L4.specialValuePlus M hM u ^ 2 * ∑ s : L4.SpecialValueGroup M,
        L4.specialValueGaussian M hM s * L4.specialValuePlus M hM (u + s) *
          L4.specialValuePlus M hM (u - s) := by
  simpa only [h2u, L4.specialValuePlus_zero] using doubling M hM h7 u hu

#print MatrixPentagon
#check @attracting_pentagon_iff_repelling
#check @L4.specialValue_mixed_reflection
#check @minus_inv
#check @doubling
#check @doubling_orderTwo

end SICLean.L3.M75.Doubling
