import SICLean.L5.ConjugationContinuation
import SICLean.L5.ConjugationPhase
import SICLean.L4.ModularCocycle

set_option autoImplicit false

/-!
# Finite-product Φ conjugation

Sources: [RW26, p. 5; Prop. 2(i), (19), p. 6; Prop. 1, p. 6; Prop. 7, p. 14].

The parameters are real τ and positive T = cτ+d. The fixed-point form is
stated separately. Finite factor reordering is j ↦ c-1-j, and the Euclidean
floor gives k' = d-1-k. This step has no extra parity factor. Point values
are reached after continuity at both centers. A common zero or pole is not
cancelled by multiplying raw total values.

Index reversal uses the floor arithmetic. Conjugation is taken from the
continued S-factor germ and combined across the finite product. The
reflection exponential excludes zero germs, and continuity then evaluates
the product at the center.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L5.ConjugationModular

open SICLean.L4

/-- Index reversal for the finite product. [RW26, (19), p. 6]. -/
def reflectedIndex (M : SL(2, ℤ)) (j : ℕ) : ℕ := (M 1 0).toNat - 1 - j

/-- Same sources: index reversal stays in the literal finite product. -/
theorem reflectedIndex_lt (M : SL(2, ℤ)) (hM : 0 < M 1 0) (j : ℕ)
    (hj : j < (M 1 0).toNat) : reflectedIndex M j < (M 1 0).toNat := by
  unfold reflectedIndex
  omega

/-- Same sources: reversal is an involution on the product range. -/
theorem reflectedIndex_involutive (M : SL(2, ℤ)) (hM : 0 < M 1 0) (j : ℕ)
    (hj : j < (M 1 0).toNat) : reflectedIndex M (reflectedIndex M j) = j := by
  unfold reflectedIndex
  omega

/-- Same sources: the floor identity for arbitrary integer m,n, including
negative values. Reuses the existing reflection-index arithmetic. -/
theorem modularPhiIndex_reflect (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) (hj : j < (M 1 0).toNat) :
    modularPhiIndex M (1 - m) (1 - n) (reflectedIndex M j) =
      M 1 1 - 1 - modularPhiIndex M m n j := by
  exact ModularCocycleReflectionAux.reflection_index M hM m n j
    (Finset.mem_range.mpr hj)

/-- After reversing the product range, the S-input reflects as T-1-conj ζ.
[RW26, p. 5; (19), p. 6]. -/
theorem modularPhiFactorInput_reflect (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) (hj : j < (M 1 0).toNat) (z : ℂ) (τ : ℝ) :
    modularPhiFactorInput M (1 - m) (1 - n) (reflectedIndex M j)
        (-((starRingEnd ℂ) z)) (τ : ℂ) =
      etaDenom M (τ : ℂ) - 1 -
        (starRingEnd ℂ) (modularPhiFactorInput M m n j z (τ : ℂ)) := by
  have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.le
  have hjZ : (reflectedIndex M j : ℤ) = M 1 0 - 1 - (j : ℤ) := by
    unfold reflectedIndex
    omega
  have hjC : (reflectedIndex M j : ℂ) = (M 1 0 : ℂ) - 1 - (j : ℂ) := by
    exact_mod_cast hjZ
  simp only [modularPhiFactorInput, modularPhiIndex_reflect M hM m n j hj,
    hjC, etaDenom, map_add, map_mul, map_intCast, map_natCast, Complex.conj_ofReal]
  push_cast
  ring

/-- The positive square root of the real automorphy factor. [RW26, p. 5]. -/
theorem modularPhiFactorPoint_parameter_real (M : SL(2, ℤ)) (m n : ℤ)
    (j : ℕ) (z : ℂ) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) :
    (modularPhiFactorPoint M m n j z (τ : ℂ)).1 =
      (Real.sqrt ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) : ℂ) := by
  exact ConjugationPhase.sqrt_etaDenom_real M τ hT

/-- Conjugation of the φ-argument. The real positive root is the slit-plane root.
Same sources. -/
theorem modularPhiFactorPoint_argument_reflect (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) (hj : j < (M 1 0).toNat) (z : ℂ) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) :
    (modularPhiFactorPoint M (1 - m) (1 - n) (reflectedIndex M j)
        (-((starRingEnd ℂ) z)) (τ : ℂ)).2 =
      (starRingEnd ℂ) (modularPhiFactorPoint M m n j z (τ : ℂ)).2 := by
  have hden : etaDenom M (τ : ℂ) =
      (((M 1 0 : ℝ) * τ + (M 1 1 : ℝ) : ℝ) : ℂ) := by
    simp [etaDenom]
  change modularPhiSArgument _ _ = (starRingEnd ℂ) (modularPhiSArgument _ _)
  rw [modularPhiFactorInput_reflect M hM m n j hj z τ, hden]
  exact (ConjugationContinuation.modularPhiSArgument_conj _ hT _).symm

/-- Each factor, as a punctured z-germ. [RW26, p. 5; (19), p. 6]. -/
theorem modularPhiFactor_conj_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) (hj : j < (M 1 0).toNat) (z : ℂ) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) :
    (fun w : ℂ => (starRingEnd ℂ)
      (modularPhiS (modularPhiFactorInput M m n j w (τ : ℂ))
        (etaDenom M (τ : ℂ)))) =ᶠ[𝓝[≠] z]
    (fun w => (modularPhiS
      (modularPhiFactorInput M (1 - m) (1 - n) (reflectedIndex M j)
        (-((starRingEnd ℂ) w)) (τ : ℂ)) (etaDenom M (τ : ℂ)))⁻¹) := by
  have hden : etaDenom M (τ : ℂ) =
      (((M 1 0 : ℝ) * τ + (M 1 1 : ℝ) : ℝ) : ℂ) := by
    simp [etaDenom]
  have ht : Tendsto (fun w => modularPhiFactorInput M m n j w (τ : ℂ))
      (𝓝[≠] z) (𝓝[≠] (modularPhiFactorInput M m n j z (τ : ℂ))) := by
    have hcont : ContinuousAt (fun w => modularPhiFactorInput M m n j w (τ : ℂ)) z := by
      unfold modularPhiFactorInput
      fun_prop
    apply hcont.continuousWithinAt.tendsto_nhdsWithin
    intro w hw heq
    apply hw
    change w = z
    change modularPhiFactorInput M m n j w (τ : ℂ) =
      modularPhiFactorInput M m n j z (τ : ℂ) at heq
    exact add_right_cancel (add_right_cancel heq)
  have hg := ConjugationContinuation.modularPhiS_conj_germ _ hT
    (modularPhiFactorInput M m n j z (τ : ℂ))
  simp only [← hden] at hg
  filter_upwards [ht.eventually hg] with w hw
  simpa only [modularPhiFactorInput_reflect M hM m n j hj w τ] using hw

/-- The finite product, for a general matrix. [RW26, p. 5; Prop. 2(i), (19), p. 6].
This germ statement does not evaluate the center. -/
theorem modularPhi_conj_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z : ℂ) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) :
    (fun w : ℂ => (starRingEnd ℂ) (modularPhi M m n w (τ : ℂ))) =ᶠ[𝓝[≠] z]
      (fun w => (modularPhi M (1 - m) (1 - n)
        (-((starRingEnd ℂ) w)) (τ : ℂ))⁻¹) := by
  classical
  have hall : ∀ᶠ w : ℂ in 𝓝[≠] z,
      ∀ j ∈ Finset.range (M 1 0).toNat,
      (starRingEnd ℂ) (modularPhiS (modularPhiFactorInput M m n j w (τ : ℂ))
        (etaDenom M (τ : ℂ))) =
      (modularPhiS
        (modularPhiFactorInput M (1 - m) (1 - n) (reflectedIndex M j)
          (-((starRingEnd ℂ) w)) (τ : ℂ)) (etaDenom M (τ : ℂ)))⁻¹ := by
    apply (Finset.range (M 1 0).toNat).finite_toSet.eventually_all.mpr
    intro j hj
    exact modularPhiFactor_conj_germ M hM m n j (Finset.mem_range.mp hj) z τ hT
  filter_upwards [hall] with w hw
  change (starRingEnd ℂ) (∏ j ∈ Finset.range (M 1 0).toNat,
    modularPhiS (modularPhiFactorInput M m n j w (τ : ℂ)) (etaDenom M (τ : ℂ))) = _
  rw [map_prod]
  trans ∏ j ∈ Finset.range (M 1 0).toNat,
    (modularPhiS
      (modularPhiFactorInput M (1 - m) (1 - n) (reflectedIndex M j)
        (-((starRingEnd ℂ) w)) (τ : ℂ)) (etaDenom M (τ : ℂ)))⁻¹
  · exact Finset.prod_congr rfl hw
  rw [Finset.prod_inv_distrib]
  exact congrArg (Inv.inv : ℂ → ℂ) (Finset.prod_range_reflect
    (fun j => modularPhiS (modularPhiFactorInput M (1 - m) (1 - n) j
      (-((starRingEnd ℂ) w)) (τ : ℂ)) (etaDenom M (τ : ℂ))) (M 1 0).toNat)

/-- Same sources, after both centers are continuous.
The product equaling 1 is the nonvanishing statement. -/
theorem modularPhi_conj_mul (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z : ℂ) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (hL : ContinuousAt (fun w => modularPhi M m n w (τ : ℂ)) z)
    (hR : ContinuousAt (fun w => modularPhi M (1 - m) (1 - n) w (τ : ℂ))
      (-((starRingEnd ℂ) z))) :
    (starRingEnd ℂ) (modularPhi M m n z (τ : ℂ)) *
      modularPhi M (1 - m) (1 - n) (-((starRingEnd ℂ) z)) (τ : ℂ) = 1 := by
  have hτ := real_mem_modularPhiDomain M τ hT
  have hg : (fun w : ℂ => (starRingEnd ℂ) (modularPhi M m n w (τ : ℂ)) *
      modularPhi M (1 - m) (1 - n) (-((starRingEnd ℂ) w)) (τ : ℂ))
      =ᶠ[𝓝[≠] z] (fun _ => (1 : ℂ)) := by
    filter_upwards [modularPhi_conj_germ M hM m n z τ hT,
      ModularCocycleReflectionAux.reflection_exponential_germ M hM m n z (τ : ℂ) hτ]
      with w hc hr
    have hn : modularPhi M m n w (τ : ℂ) ≠ 0 := by
      intro hn
      rw [hn, zero_mul] at hr
      exact Complex.exp_ne_zero _ hr.symm
    have hn' : modularPhi M (1 - m) (1 - n)
        (-((starRingEnd ℂ) w)) (τ : ℂ) ≠ 0 := by
      intro hn'
      rw [hn', inv_zero] at hc
      exact hn ((map_eq_zero (starRingEnd ℂ)).mp hc)
    rw [hc, inv_mul_cancel₀ hn']
  have hcL : ContinuousAt (fun w => (starRingEnd ℂ) (modularPhi M m n w (τ : ℂ))) z :=
    Complex.continuous_conj.continuousAt.comp hL
  have hcR : ContinuousAt (fun w => modularPhi M (1 - m) (1 - n)
      (-((starRingEnd ℂ) w)) (τ : ℂ)) z :=
    hR.comp (f := fun w : ℂ => -((starRingEnd ℂ) w))
      (Complex.continuous_conj.continuousAt.neg)
  exact ModularCocycleAux.eq_of_germ (hcL.mul hcR) continuousAt_const hg

/-- Same sources, point-value reciprocal form with center regularity
supplied by the caller. No individual-factor regularity is demanded. -/
theorem modularPhi_conj (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z : ℂ) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (hL : ContinuousAt (fun w => modularPhi M m n w (τ : ℂ)) z)
    (hR : ContinuousAt (fun w => modularPhi M (1 - m) (1 - n) w (τ : ℂ))
      (-((starRingEnd ℂ) z))) :
    (starRingEnd ℂ) (modularPhi M m n z (τ : ℂ)) =
      (modularPhi M (1 - m) (1 - n) (-((starRingEnd ℂ) z)) (τ : ℂ))⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (modularPhi_conj_mul M hM m n z τ hT hL hR)

/-- The same identity with the multiplier included. [RW26, p. 3; Prop. 7, p. 14]. -/
theorem modularPhi_normalized_conj (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z : ℂ) (τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (hL : ContinuousAt (fun w => modularPhi M m n w (τ : ℂ)) z)
    (hR : ContinuousAt (fun w => modularPhi M (1 - m) (1 - n) w (τ : ℂ))
      (-((starRingEnd ℂ) z))) :
    (starRingEnd ℂ) (etaMultiplier M * modularPhi M m n z (τ : ℂ)) =
      (etaMultiplier M *
        modularPhi M (1 - m) (1 - n) (-((starRingEnd ℂ) z)) (τ : ℂ))⁻¹ := by
  rw [map_mul, ConjugationPhase.etaMultiplier_conj M hM,
    modularPhi_conj M hM m n z τ hT hL hR, mul_inv]

/-- Fixed-point form with real argument, specialized from the real-τ theorem.
[RW26, Prop. 7, p. 14]. -/
theorem modularPhi_normalized_conj_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ : ℂ) = (τ : ℂ))
    (hL : ContinuousAt (fun w => modularPhi M m n w (τ : ℂ)) (z : ℂ))
    (hR : ContinuousAt (fun w => modularPhi M (1 - m) (1 - n) w (τ : ℂ)) (-z : ℂ)) :
    (starRingEnd ℂ) (etaMultiplier M * modularPhi M m n (z : ℂ) (τ : ℂ)) =
      (etaMultiplier M * modularPhi M (1 - m) (1 - n) (-z : ℂ) (τ : ℂ))⁻¹ := by
  simpa only [Complex.conj_ofReal] using
    modularPhi_normalized_conj M hM m n (z : ℂ) τ hT hL (by
      simpa only [Complex.conj_ofReal] using hR)

/-- The phase given by the reflection polynomial. [RW26, Prop. 1, p. 6].
At the actual special point this sign is the Gaussian q. -/
theorem modularPhi_normalized_conj_phase (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ))
    (hL : ContinuousAt (fun w => modularPhi M m n w (τ : ℂ)) (z : ℂ))
    (hR : ContinuousAt (fun w => modularPhi M (1 - m) (1 - n) w (τ : ℂ)) (-z : ℂ)) :
    (starRingEnd ℂ) (etaMultiplier M * modularPhi M m n (z : ℂ) (τ : ℂ)) =
      (-1 : ℂ) ^ (m + n) * e (-modularReflectionPolynomial M m n (z : ℂ) (τ : ℂ)) *
        (etaMultiplier M * modularPhi M m n (z : ℂ) (τ : ℂ)) := by
  have hc := modularPhi_normalized_conj M hM m n (z : ℂ) τ hT hL (by
    simpa only [Complex.conj_ofReal] using hR)
  simp only [Complex.conj_ofReal] at hc
  have hr := modularPhi_reflection_normalized M hM m n (z : ℂ) (τ : ℂ)
    (real_mem_modularPhiDomain M τ hT) hL (hR.comp continuousAt_id.neg)
  have hn : etaMultiplier M * modularPhi M (1 - m) (1 - n) (-z : ℂ) (τ : ℂ) ≠ 0 := by
    intro hn
    rw [hn, mul_zero] at hr
    exact (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (e_ne_zero _)) hr.symm
  have hs : (-1 : ℂ) ^ (m + n) * (-1 : ℂ) ^ (m + n) = 1 := by
    rw [← mul_zpow]
    norm_num
  have he : e (-modularReflectionPolynomial M m n (z : ℂ) (τ : ℂ)) *
      e (modularReflectionPolynomial M m n (z : ℂ) (τ : ℂ)) = 1 := by
    rw [e_neg', inv_mul_cancel₀ (e_ne_zero _)]
  rw [hc]
  apply mul_right_cancel₀ hn
  rw [inv_mul_cancel₀ hn, mul_assoc, hr]
  calc
    1 = ((-1 : ℂ) ^ (m + n) * (-1 : ℂ) ^ (m + n)) *
        (e (-modularReflectionPolynomial M m n (z : ℂ) (τ : ℂ)) *
          e (modularReflectionPolynomial M m n (z : ℂ) (τ : ℂ))) := by rw [hs, he, one_mul]
    _ = _ := by ring

#print reflectedIndex
#print SICLean.L4.modularPhi
#check SICLean.L4.ModularCocycleReflectionAux.reflection_index
#check SICLean.L4.modularPhi_reflection_normalized
#check SICLean.L4.modularPhi_iterate_fixedPoint
#check modularPhi_normalized_conj_fixedPoint

end SICLean.L5.ConjugationModular
