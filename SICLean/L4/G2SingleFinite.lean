import SICLean.L4.G2SingleBent
import SICLean.L4.G2SingleFiniteAux

set_option autoImplicit false

/-!
# Single-function telescoping, c-fold counting, and Fourier (6)

The file follows `G2SingleBent`.
Fourier (6) is formalized here. [RW26, p. 3, (6), p. 13].
The explicit divmod permutation and the true quotient's c-fold strip count are reused.
No cyclic-group assumption,
new special-value function, independently chosen μ, or Fourier inversion.
-/

noncomputable section

open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2.SingleFinite

open SingleBent CombResidues StripCounting SpecialValueBridge

/-- Right upward bent chain minus left upward bent chain, for all m. -/
def rawIntegral (M : SL(2, ℤ)) (u : ℤ × ℤ) (δ β : ℝ) : ℂ :=
  ∑ m : Fin (M 1 0).toNat,
    (SingleBent.integral M δ β (m : ℤ) 0 (rawG M u (m : ℤ)) -
      SingleBent.integral M δ β (m : ℤ) (M 1 0) (rawG M u (m : ℤ)))

/-- Literal candidate 2πi residue of rawG; only one Φ factor. -/
def singleRho (M : SL(2, ℤ)) (u : ℤ × ℤ) (m k : ℤ) : ℂ :=
  (scale M : ℂ) * specialValuePairingLift M (m, k) u * phiNumerator M m k

/--
Same exact translations, now of the bent-chain crossing; [RW26, p. 12, p. 13].
-/
theorem crossing_translates (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (δ : ℝ) (m j : ℤ) :
    crossing M δ (m + M 1 0) j = crossing M δ m j - epsilon M ∧
      crossing M δ (m + 1 - M 0 0) (j + 1) = crossing M δ m j + translate M := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  constructor
  · simpa only [mul_one, Int.cast_one, neg_one_mul, sub_eq_add_neg] using
      G2SingleFiniteAux.crossing_integer_period M hM δ m j 1
  · have ht := fixedPoint_translate M hM
    change (M 1 0 : ℝ) * translate M = (M 0 0 : ℝ) * epsilon M - 1 at ht
    simp only [crossing]
    push_cast
    apply (div_eq_iff hc).2
    simp only [add_mul, div_mul_cancel₀ _ hc]
    dsimp [length]
    nlinarith [ht]

/--
All signed quotients k are allowed. Reuses rawG_period and the
already fixed integer reindexing; [RW26, p. 13]. Translation has derivative 1, with the same angle.
-/
theorem integral_integer_period (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (δ β : ℝ) (m j k : ℤ) :
    SingleBent.integral M δ β (m + M 1 0 * k) j (rawG M u (m + M 1 0 * k)) =
      SingleBent.integral M δ β m j (rawG M u m) := by
  unfold SingleBent.integral
  rw [G2SingleFiniteAux.crossing_integer_period M hM,
    G2SingleFiniteAux.bent_integral_translate]
  congr 1
  funext z
  simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_intCast,
    neg_mul, ← sub_eq_add_neg] using
      (Telescoping.raw_integer_period M hM u 0 m k z).2

/--
The same finite divmod permutation and two translations,
applied to actual bent integrals; [RW26, p. 13]. This is not a contour homotopy.
-/
theorem reindexed_negative_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1)
    (j : Fin (M 1 0).toNat) :
    (∑ m : Fin (M 1 0).toNat,
      SingleBent.integral M δ β (m : ℤ) ((j : ℤ) + 1) (rawG M u (m : ℤ))) =
    ∑ m : Fin (M 1 0).toNat,
      SingleBent.integral M δ β (m : ℤ) (j : ℤ)
        (fun z => rawG M u ((m : ℤ) + 1 - M 0 0) (z + (translate M : ℂ))) := by
  have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg (le_of_lt hM.1)
  have hrange (r : Fin (M 1 0).toNat) : (r : ℤ) ∈ Ico 0 (M 1 0) := by
    have h := r.isLt
    constructor <;> omega
  let idx : Fin (M 1 0).toNat → Fin (M 1 0).toNat := fun r =>
    ⟨(Telescoping.newIndex M (r : ℤ)).toNat, by
      have h := Telescoping.reindexing_divmod M hM (r : ℤ)
      omega⟩
  have hidx (r : Fin (M 1 0).toNat) :
      (idx r : ℤ) = Telescoping.newIndex M (r : ℤ) := by
    exact Int.toNat_of_nonneg (Telescoping.reindexing_divmod M hM (r : ℤ)).1
  have hbij : Function.Bijective idx := by
    constructor
    · intro r s hrs
      have h := (Telescoping.reindexing_bijOn M hM).2.1 (hrange r) (hrange s)
        (by rw [← hidx r, ← hidx s, hrs])
      exact Fin.ext (by exact_mod_cast h)
    · intro m
      obtain ⟨r, hr, he⟩ := (Telescoping.reindexing_bijOn M hM).2.2 (hrange m)
      have hr0 : 0 ≤ r := hr.1
      have hrlt : r < M 1 0 := hr.2
      let r' : Fin (M 1 0).toNat := ⟨r.toNat, by omega⟩
      refine ⟨r', ?_⟩
      apply Fin.ext
      have hr' : (r' : ℤ) = r := Int.toNat_of_nonneg hr.1
      have h : (idx r' : ℤ) = (m : ℤ) := by rw [hidx, hr', he]
      exact_mod_cast h
  apply Fintype.sum_bijective idx hbij
  intro r
  have hr := (Telescoping.reindexing_divmod M hM (r : ℤ)).2.2
  calc
    _ = SingleBent.integral M δ β
        (Telescoping.newIndex M (r : ℤ) + 1 - M 0 0) ((j : ℤ) + 1)
        (rawG M u (Telescoping.newIndex M (r : ℤ) + 1 - M 0 0)) := by
      simpa only [← hr] using integral_integer_period M hM u δ β
        (Telescoping.newIndex M (r : ℤ) + 1 - M 0 0) ((j : ℤ) + 1)
        (Telescoping.integerQuotient M (r : ℤ))
    _ = _ := by
      simp only [SingleBent.integral, hidx]
      rw [(crossing_translates M hM δ (Telescoping.newIndex M (r : ℤ)) (j : ℤ)).2,
        G2SingleFiniteAux.bent_integral_translate]

/--
Exact finite telescope, after absolute convergence has been supplied; [RW26, p. 13].
-/
theorem exact_telescope (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1) :
    rawIntegral M u δ β =
      ∑ j : Fin (M 1 0).toNat, ∑ m : Fin (M 1 0).toNat,
        SingleBent.integral M δ β (m : ℤ) (j : ℤ) (SingleBent.differenceKernel M u (m : ℤ)) := by
  have hfinite : rawIntegral M u δ β =
      ∑ j : Fin (M 1 0).toNat, ∑ m : Fin (M 1 0).toNat,
        (SingleBent.integral M δ β (m : ℤ) (j : ℤ) (rawG M u (m : ℤ)) -
          SingleBent.integral M δ β (m : ℤ) ((j : ℤ) + 1) (rawG M u (m : ℤ))) := by
    unfold rawIntegral
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    let f : ℕ → ℂ := fun j =>
      SingleBent.integral M δ β (m : ℤ) (j : ℤ) (rawG M u (m : ℤ))
    have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg (le_of_lt hM.1)
    have hs := Fin.sum_univ_eq_sum_range (fun j => f j - f (j + 1)) (M 1 0).toNat
    rw [Finset.sum_range_sub'] at hs
    simpa only [f, Nat.cast_add, Nat.cast_one, Nat.cast_zero, hc] using hs.symm
  rw [hfinite]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_sub_distrib, reindexed_negative_sum M hM u hu δ β hδ hβ j,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hj0 : (j : ℕ) < (M 1 0).toNat + 1 := by omega
  have hj1 : (j : ℕ) + 1 < (M 1 0).toNat + 1 := by omega
  have hf := rawG_bent_integrable M hM u hu δ β hδ hβ (m : ℤ)
    (⟨(j : ℕ), hj0⟩ : Fin ((M 1 0).toNat + 1))
  have hg := rawG_bent_integrable M hM u hu δ β hδ hβ ((m : ℤ) + 1 - M 0 0)
    (⟨(j : ℕ) + 1, hj1⟩ : Fin ((M 1 0).toNat + 1))
  have hg' : G1BentIntegrable (rawG M u ((m : ℤ) + 1 - M 0 0))
      (crossing M δ (m : ℤ) (j : ℤ) + translate M) (angle β) := by
    simpa only [Nat.cast_add, Nat.cast_one,
      (crossing_translates M hM δ (m : ℤ) (j : ℤ)).2] using hg
  have htrans := (G2SingleFiniteAux.bent_integrable_translate_iff _ _ _ _).1 hg'
  exact (G2SingleFiniteAux.bent_integral_sub _ _ _ _ hf htrans).symm

/--
The single-function difference has no (1-t) factor. The existing
punctured identity is used through the a.e. pullback bridge; [RW26, p. 13].
-/
theorem telescope_to_single (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1) :
    rawIntegral M u δ β =
      ∑ j : Fin (M 1 0).toNat, ∑ m : Fin (M 1 0).toNat,
        SingleBent.integral M δ β (m : ℤ) (j : ℤ) (singleKernel M u (m : ℤ)) := by
  rw [exact_telescope M hM u hu δ β hδ hβ]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro m hm
  apply G2SingleFiniteAux.bent_integral_congr_ae
  · exact (SingleBent.difference_pullbacks_ae M hM u (m : ℤ)
      (crossing M δ (m : ℤ) (j : ℤ)) β hβ).1
  · exact (SingleBent.difference_pullbacks_ae M hM u (m : ℤ)
      (crossing M δ (m : ℤ) (j : ℤ)) β hβ).2

/--
The actual removable G1 center, including the true zero class.
Reuses g1_single_rhs_value and the balanced exponent, not a
total 0/0 or an off-center germ; [RW26, p. 7, p. 12, p. 13, (22)].
-/
theorem single_rhs_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) :
    G1SingleRemovable M (repellingTau M) (argument M u) 0 (u.1 + 1) ∧
      g1SingleRHS M (repellingTau M) (argument M u) 0 (u.1 + 1) =
        etaMultiplier M / repellingMinus M hM (specialValueMk M u) := by
  have hwin : RepresentativeWindow M u (deepRepresentative M 0) :=
    ⟨hu.1, hu.2, (deepRepresentative_window M hM 0).1,
      (deepRepresentative_window M hM 0).2⟩
  have hid : etaMultiplier M *
      modularPhi M (u.1 + 1) 1 (argument M u : ℂ) (repellingTau M : ℂ) =
      repellingMinus M hM (specialValueMk M u) :=
    Evaluation.upper_minus_identification M hM u (deepRepresentative M 0) hwin
  refine ⟨(g1_single_rhs_value M hM u).1, ?_⟩
  rw [(g1_single_rhs_value M hM u).2, ← hid]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, etaMultiplier_ne_zero M hM.1]

/--
One G1 single-function call for each j, summed over all m. The μ in
the prefactor cancels the same μ in the actual center identification; [RW26, p. 7, p. 13, (22)].
-/
theorem single_integral_each_j (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1)
    (j : Fin (M 1 0).toNat) :
    (∀ m : Fin (M 1 0).toNat,
      G1BentIntegrable (singleKernel M u (m : ℤ))
        (crossing M δ (m : ℤ) (j : ℤ)) (angle β)) ∧
    (∑ m : Fin (M 1 0).toNat,
      SingleBent.integral M δ β (m : ℤ) (j : ℤ) (singleKernel M u (m : ℤ))) =
      (Real.sqrt (epsilon M) : ℂ) / repellingMinus M hM (specialValueMk M u) := by
  have hs : 0 < g1S M (repellingTau M) (argument M u) 0 (u.1 + 1) := by
    rw [(coefficient_formulas M hM u 0).1]
    exact add_pos (epsilon_pos M hM)
      (mul_pos (scale_identities M hM).1 (by exact_mod_cast hu.1))
  have hj : 0 ≤ (j : ℤ) := Int.natCast_nonneg _
  have hc := crossing_eq_g1 M hM δ hδ.1 0 (j : ℤ) hj
  have ha := angle_direction β hβ
  have hcall := (hG1 M (repellingTau M) hM.1 (epsilon_pos M hM)).1
    0 0 (u.1 + 1) (argument M u) (displacement M δ (j : ℤ)) (angle β)
    hs hc.1 ha.1 ha.2.1
  have hk (m : ℤ) : singleKernel M u m =
      g1SingleKernel M (repellingTau M) (argument M u) 0 0 (u.1 + 1) m :=
    funext (singleKernel_eq_g1 M u m)
  have hx (m : ℤ) := (crossing_eq_g1 M hM δ hδ.1 m (j : ℤ) hj).2
  refine ⟨fun m => ?_, ?_⟩
  · rw [hk, hx]
    exact hcall.2.1 m.val (Finset.mem_range.mpr m.isLt)
  · simp only [SingleBent.integral]
    simp_rw [hk, hx]
    rw [Fin.sum_univ_eq_sum_range (fun m : ℕ =>
      g1BentIntegral
        (g1SingleKernel M (repellingTau M) (argument M u) 0 0 (u.1 + 1) (m : ℤ))
        (g1BentCrossing M (repellingTau M) (displacement M δ (j : ℤ)) 0 (m : ℤ))
        (angle β)), hcall.2.2, g1_fixed_prefactor M hM,
      (single_rhs_value M hM u hu).2]
    field_simp [etaMultiplier_ne_zero M hM.1]

/--
The first value of the concrete raw integral, from G1 only; [RW26, p. 13].
-/
theorem rawIntegral_value (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1) :
    rawIntegral M u δ β = (M 1 0 : ℂ) * (Real.sqrt (epsilon M) : ℂ) /
      repellingMinus M hM (specialValueMk M u) := by
  rw [telescope_to_single M hM u hu δ β hδ hβ]
  simp_rw [(single_integral_each_j hG1 M hM u hu δ β hδ hβ _).2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg (le_of_lt hM.1)
  have hc' : ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by exact_mod_cast hc
  rw [hc']
  ring

/--
Positive local coefficient of rawG at a labelled comb root. This is
a punctured Laurent expansion, independent of the total value at the pole.
Reuses comb derivative and actual Φ center regularity; [RW26, p. 12].
-/
theorem single_comb_principalPart (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m k : ℤ) :
    ∃ (R : ℝ) (g : ℂ → ℂ), 0 < R ∧
      AnalyticOnNhd ℂ g (Metric.closedBall (root M m k) R) ∧
      ∀ z ∈ Metric.closedBall (root M m k) R, z ≠ root M m k →
        rawG M u m z =
          (singleRho M u m k / (2 * (Real.pi : ℂ) * Complex.I)) / (z - root M m k) + g z := by
  let p := root M m k
  let N : ℂ → ℂ := fun z => kernelK M u m z * modularPhi M m 0 z (repellingTau M : ℂ)
  let D : ℂ → ℂ := fun z => combV M z - combU M m z
  let d : ℂ := 2 * (Real.pi : ℂ) * Complex.I *
    ((length M : ℂ) / (epsilon M : ℂ)) * combV M p
  have hK : AnalyticAt ℂ (kernelK M u m) p := by
    unfold kernelK e
    fun_prop
  have hphi : AnalyticAt ℂ (fun z => modularPhi M m 0 z (repellingTau M : ℂ)) p :=
    (phi_units_at_root M hM (0, 0) m k).1.comp
      (f := fun z : ℂ => (z, (repellingTau M : ℂ))) (x := p)
      (analyticAt_id.prod analyticAt_const)
  have hN : AnalyticAt ℂ N p := hK.mul hphi
  have hD : AnalyticAt ℂ D p := by
    dsimp [D, combV, combU, e]
    fun_prop
  have hD0 : D p = 0 := by
    have hs : (scale M : ℂ) ≠ 0 := by exact_mod_cast (scale_identities M hM).1.ne'
    apply (comb_zeros M hM m p).mpr
    refine ⟨k, rfl, ?_⟩
    intro k' hk'
    apply Int.cast_injective (α := ℂ)
    dsimp [p, root] at hk'
    have heq := (mul_left_cancel₀ hs hk').symm
    linear_combination heq
  have hd : HasDerivAt D d p := (comb_hasDerivAt M hM m k).1
  have hd0 : d ≠ 0 := (comb_hasDerivAt M hM m k).2
  have he : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
  have hl : (length M : ℂ) ≠ 0 := by exact_mod_cast (length_pos M hM).ne'
  have hv : combV M p ≠ 0 := by
    intro h
    apply hd0
    dsimp [d]
    rw [h, mul_zero]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcoeff : N p / d = singleRho M u m k / (2 * (Real.pi : ℂ) * Complex.I) := by
    dsimp [N, d, singleRho]
    rw [← kernel_character M hM u m k]
    simp only [scale, Complex.ofReal_div, phiNumerator]
    dsimp [p]
    field_simp [he, hl, hv, hπ, Complex.I_ne_zero]
    <;> ring
  obtain ⟨R, g, hR, hg, hfg⟩ := G2SingleFiniteAux.simple_pole_expansion N D p d hN hD hD0 hd hd0
  refine ⟨R, g, hR, hg, ?_⟩
  intro z hz hzp
  rw [← hcoeff, ← hfg z hz hzp]
  dsimp [rawG, N, D]
  ring

/--
The existing c-fold count on the true quotient; every numerator zero
occurrence uses A. No circles or inverse-denominator branch are present; [RW26, p. 12, p. 13].
-/
theorem single_comb_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    (∑ x ∈ stripFinset M, singleRho M u x.1 x.2) =
      (M 1 0 : ℂ) * (scale M : ℂ) * (etaMultiplier M)⁻¹ *
        groupSum M hM (fun x => specialValuePairing M hM x (specialValueMk M u) * repellingPlus M hM x) := by
  have hμ : etaMultiplier M ≠ 0 := etaMultiplier_ne_zero M hM.1
  have hwin := representativeWindow_construct M hM 0 0
  have hphi (x : ℤ × ℤ) (hx : x ∈ stripFinset M) :
      phiNumerator M x.1 x.2 =
        (etaMultiplier M)⁻¹ * repellingPlus M hM (specialValueMk M x) := by
    rw [(repellingValues_mk M hM x).1,
      ← (ResidueLedger.strip_phi_plus_values M hM _ _ hwin x hx).1,
      ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
  calc
    _ = (scale M : ℂ) * (etaMultiplier M)⁻¹ *
        ∑ x ∈ stripFinset M,
          specialValuePairing M hM (specialValueMk M x) (specialValueMk M u) *
            repellingPlus M hM (specialValueMk M x) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [singleRho, hphi x hx, specialValuePairing_mk]
      ring
    _ = _ := by
      rw [strip_sum M hM
        (fun x => specialValuePairing M hM x (specialValueMk M u) * repellingPlus M hM x)]
      ring

/--
The second raw-integral value: positive boundary, no original Φ poles,
and both closing segments vanish. The comb sum is a conclusion; [RW26, p. 13].
-/
theorem single_residue_account (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : Window M u) (δ β : ℝ)
    (hδ : 0 < δ ∧ δ < scale M) (hβ : 0 < β ∧ β < 1) :
    rawIntegral M u δ β = ∑ x ∈ stripFinset M, singleRho M u x.1 x.2 := by
  have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.1.le
  have hπ : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hrect (m : Fin (M 1 0).toNat) (T : ℝ) (hT : 0 < T) :
      FinitePrincipalParts.rectangleCCW
        (g1VerticalPoint (crossing M δ (m : ℤ) (M 1 0)) (-1))
        (g1VerticalPoint (crossing M δ (m : ℤ) 0) T) (rawG M u (m : ℤ)) =
          ∑ k ∈ G2SingleFiniteAux.componentKs M (m : ℤ), singleRho M u (m : ℤ) k := by
    rw [G2SingleFiniteAux.rawG_upper_rectangle M hM u δ hδ m T hT
      (fun k => singleRho M u (m : ℤ) k / (2 * (Real.pi : ℂ) * I))
      (fun k => single_comb_principalPart M hM u (m : ℤ) k), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_div_cancel₀ _ hπ
  have hcomponent (m : Fin (M 1 0).toNat) :
      SingleBent.integral M δ β (m : ℤ) 0 (rawG M u (m : ℤ)) -
        SingleBent.integral M δ β (m : ℤ) (M 1 0) (rawG M u (m : ℤ)) =
          ∑ k ∈ G2SingleFiniteAux.componentKs M (m : ℤ), singleRho M u (m : ℤ) k := by
    have hright := G2SingleFiniteAux.rawG_truncated_bent_tendsto M hM u hu δ β hδ hβ
      (m : ℤ) (0 : Fin ((M 1 0).toNat + 1))
    have hleft := G2SingleFiniteAux.rawG_truncated_bent_tendsto M hM u hu δ β hδ hβ
      (m : ℤ) (Fin.last (M 1 0).toNat)
    simp only [Fin.val_zero, Nat.cast_zero] at hright
    simp only [Fin.val_last, hc] at hleft
    have hlim := hright.sub hleft
    have hclosing := G2SingleFiniteAux.full_closing_segments_tendsto_zero M hM u hu δ β hδ hβ m
    have hother := (tendsto_const_nhds
      (x := ∑ k ∈ G2SingleFiniteAux.componentKs M (m : ℤ), singleRho M u (m : ℤ) k)).add
        hclosing.1 |>.sub hclosing.2
    simp only [add_zero, sub_zero] at hother
    apply tendsto_nhds_unique hlim
    apply hother.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hfinite := G2SingleFiniteAux.common_finite_bent_boundary M hM
      (rawG M u (m : ℤ)) δ β (m : ℤ) T hT
      (fun z hz => G2SingleFiniteAux.rawG_analytic_nonreal M hM u (m : ℤ) z (by linarith))
    rw [hrect m T hT] at hfinite
    exact hfinite.symm
  unfold rawIntegral
  calc
    _ = ∑ m : Fin (M 1 0).toNat,
        ∑ k ∈ G2SingleFiniteAux.componentKs M (m : ℤ), singleRho M u (m : ℤ) k :=
      Finset.sum_congr rfl (fun m _ => hcomponent m)
    _ = _ := G2SingleFiniteAux.component_sum M hM (fun x => singleRho M u x.1 x.2)

/--
Fourier (6), including u=0, for the existing auxiliary actual values.
The constant is the fixed etaMultiplier M, quantified before all u.
The proof uses L/√ε=√N and upperRepresentative_window to remove the window; [RW26, p. 3, p. 13,
(6)].
-/
theorem repelling_fourier (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ∀ u : SpecialValueGroup M,
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u * repellingPlus M hM x) =
        etaMultiplier M / repellingMinus M hM u := by
  intro u
  refine Quotient.inductionOn u fun x => ?_
  let w := upperRepresentative M x
  have hw : Window M w := upperRepresentative_window M hM x
  have hclass : specialValueMk M w = specialValueMk M x := upperRepresentative_class M x
  let δ := scale M / 2
  have hδ : 0 < δ ∧ δ < scale M := by
    dsimp [δ]
    have hscale := (scale_identities M hM).1
    constructor <;> linarith
  have hβ : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by norm_num
  have hi := (rawIntegral_value hG1 M hM w hw δ (1 / 2) hδ hβ).symm.trans
    ((single_residue_account M hM w hw δ (1 / 2) hδ hβ).trans
      (single_comb_sum M hM w))
  rw [hclass] at hi
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  have hμ : etaMultiplier M ≠ 0 := etaMultiplier_ne_zero M hM.1
  have he : (Real.sqrt (epsilon M) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (epsilon_pos M hM))
  have hn : (Real.sqrt (specialValueOrder M : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr
      (show (0 : ℝ) < specialValueOrder M from by exact_mod_cast specialValueOrder_pos M hM))
  have hscale : (scale M : ℂ) * (Real.sqrt (specialValueOrder M : ℝ) : ℂ) =
      (Real.sqrt (epsilon M) : ℂ) := by
    have hlen := normalized_length M hM
    have hesq := Real.sq_sqrt (le_of_lt (epsilon_pos M hM))
    have hl : length M ≠ 0 := ne_of_gt (length_pos M hM)
    have heR : Real.sqrt (epsilon M) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (epsilon_pos M hM))
    have hs : scale M * Real.sqrt (specialValueOrder M : ℝ) = Real.sqrt (epsilon M) := by
      rw [← hlen]
      dsimp [scale]
      field_simp
      nlinarith [hesq]
    exact_mod_cast hs
  change (Real.sqrt (specialValueOrder M : ℝ) : ℂ)⁻¹ *
    groupSum M hM (fun y => specialValuePairing M hM y (specialValueMk M x) * repellingPlus M hM y) =
      etaMultiplier M / repellingMinus M hM (specialValueMk M x)
  rw [← hscale] at hi
  have hs : (scale M : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (scale_identities M hM).1
  field_simp at hi ⊢
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hi.symm

#check @Telescoping.integerQuotient
#check @Telescoping.reindexing_bijOn
#check @StripCounting.strip_fiber_card
#check @g1_single_rhs_value
#check @normalized_length
#print rawIntegral
#print singleRho
#check @repelling_fourier

end SICLean.L4.G2.SingleFinite
