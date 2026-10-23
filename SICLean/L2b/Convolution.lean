import SICLean.L2b.Gaussian

set_option autoImplicit false

/-!
# [RW26, (40)] and the bridge to the L2a input

Only the three E-dependent statements of [RW26] are inputs.
All properties of the concrete group and Gaussian are conclusions in earlier files.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2b

variable (M : ℕ) [Fact (4 ≤ M)]

private theorem cast_dimension_ne_zero : (M : ℂ) ≠ 0 := by
  exact_mod_cast (NeZero.ne M)

private theorem cast_cofactor_ne_zero : (cofactor M : ℂ) ≠ 0 := by
  exact_mod_cast (NeZero.ne (cofactor M))

private theorem convolutionScalar_sq :
    L2a.convolutionScalar M ^ 2 = (cofactor M : ℂ) := by
  have hM : 4 ≤ M := Fact.out
  have hM' : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M : ℝ) - 3 by linarith)
  unfold L2a.convolutionScalar
  rw [← Complex.ofReal_pow, hs]
  simp only [cofactor, Nat.cast_sub (show 3 ≤ M by omega), Nat.cast_ofNat,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_ofNat]

private theorem convolutionScalar_ne_zero : L2a.convolutionScalar M ≠ 0 := by
  intro hc
  have hs := convolutionScalar_sq M
  rw [hc, zero_pow (by decide : 2 ≠ 0)] at hs
  exact cast_cofactor_ne_zero M hs.symm

/-- E restricted along the explicit homomorphism ι; no relabeling of H. -/
def restrict (E : G M → ℂ) : L2a.Values M := E ∘ iota M

/-- Input A, with no group-structure hypotheses.
Sources: [RW26, (31)], [RW26, (38)], and the zero convention in [RW26, (37)] for γ=α³. -/
structure FQDInput (E : G M → ℂ) : Prop where
  pentagon : IsFiniteQuantumDilogarithm (gaussian M) E
  epsilon_invariant : ∀ g : G M, E g = E (epsilonAut M g)
  origin : E 0 = L2a.sqrtEpsilon M ^ 3

def convolutionKernel (E : G M → ℂ) (h : L2a.Index M) (g : G M) : ℂ :=
  E g * gaussian M g * E (iota M h - g)

def subgroupConvolution (E : G M → ℂ) (h : L2a.Index M) : ℂ :=
  (∑ k : L2a.Index M, convolutionKernel M E h (iota M k) *
    metricPairing (gaussian M) (witnessW M h) (iota M k)) / (M : ℂ)

def shiftedW (h : L2a.Index M) (j : Fin (cofactor M)) : G M :=
  witnessW M h + j.val • annihilatorGenerator M

def averagedFullConvolution (E : G M → ℂ) (h : L2a.Index M) : ℂ :=
  (∑ j : Fin (cofactor M), ∑ g : G M,
    convolutionKernel M E h g * metricPairing (gaussian M) (shiftedW M h j) g) /
      ((M : ℂ) * (cofactor M : ℂ))

private theorem pairing_shiftedW_iota (h k : L2a.Index M) (j : Fin (cofactor M)) :
    metricPairing (gaussian M) (shiftedW M h j) (iota M k) =
      metricPairing (gaussian M) (witnessW M h) (iota M k) := by
  have hm : j.val • annihilatorGenerator M ∈
      AddSubgroup.zmultiples (annihilatorGenerator M) := by
    exact AddSubgroup.nsmul_mem _
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩) j.val
  change j.val • annihilatorGenerator M ∈
    (AddSubgroup.zmultiples (annihilatorGenerator M) : Set (G M)) at hm
  rw [← orthogonal_iota M] at hm
  have hp := hm k
  rw [shiftedW, (concrete_isMetricGaussian M).add_left, hp, mul_one]

private theorem sum_index_eq_fin (f : L2a.Index M → ℂ) :
    (∑ k : L2a.Index M, f k) =
      ∑ i : Fin M, ∑ j : Fin M, f ((i.val : ZMod M), (j.val : ZMod M)) := by
  let e : Fin M ≃ ZMod M :=
    { toFun := fun i => (i.val : ZMod M)
      invFun := fun k => ⟨k.val, ZMod.val_lt k⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact ZMod.val_cast_of_lt i.isLt
      right_inv := ZMod.natCast_zmod_val }
  calc
    _ = ∑ p : Fin M × Fin M, f (e p.1, e p.2) :=
      (Fintype.sum_equiv (e.prodCongr e) _ f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

theorem subgroupConvolution_eq_L2a (E : G M → ℂ) (h : L2a.Index M) :
    subgroupConvolution M E h =
      L2a.convolution M (restrict M E) h.1.val h.2.val := by
  unfold subgroupConvolution L2a.convolution
  rw [sum_index_eq_fin, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hi : ((i.val : ZMod M).val : ℤ) = (i.val : ℤ) := by
    rw [ZMod.val_cast_of_lt i.isLt]
  have hj : ((j.val : ZMod M).val : ℤ) = (j.val : ℤ) := by
    rw [ZMod.val_cast_of_lt j.isLt]
  have hsub : iota M
      (((h.1.val : ℤ) - i.val : ℤ), ((h.2.val : ℤ) - j.val : ℤ)) =
      iota M h - iota M ((i.val : ZMod M), (j.val : ZMod M)) := by
    have hp : ((((h.1.val : ℤ) - i.val : ℤ) : ZMod M),
        (((h.2.val : ℤ) - j.val : ℤ) : ZMod M)) =
        h - ((i.val : ZMod M), (j.val : ZMod M)) := by
      simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
      rfl
    rw [hp, map_sub]
  simp only [convolutionKernel, gaussian_iota, pairing_witnessW,
    L2a.gaussian, L2a.valueAt, restrict, Function.comp_apply, hi, hj,
    Int.cast_natCast]
  rw [hsub]
  ring

/-- First equality in (40), valid also at h=0. -/
theorem average_over_annihilator (E : G M → ℂ) (h : L2a.Index M) :
    subgroupConvolution M E h =
      (∑ j : Fin (cofactor M), ∑ k : L2a.Index M,
        convolutionKernel M E h (iota M k) *
          metricPairing (gaussian M) (shiftedW M h j) (iota M k)) /
            ((M : ℂ) * (cofactor M : ℂ)) := by
  simp_rw [pairing_shiftedW_iota]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold subgroupConvolution
  field_simp [cast_dimension_ne_zero M, cast_cofactor_ne_zero M]

/-- Second equality in (40), by the character filter for H. -/
theorem average_extend_to_G (E : G M → ℂ) (h : L2a.Index M) :
    subgroupConvolution M E h = averagedFullConvolution M E h := by
  have hs : (∑ j : Fin (cofactor M), ∑ g : G M,
      convolutionKernel M E h g * metricPairing (gaussian M) (shiftedW M h j) g) =
      (cofactor M : ℂ) * ∑ k : L2a.Index M,
        convolutionKernel M E h (iota M k) *
          metricPairing (gaussian M) (witnessW M h) (iota M k) := by
    calc
      _ = ∑ j : Fin (cofactor M), ∑ g : G M,
          (convolutionKernel M E h g * metricPairing (gaussian M) (witnessW M h) g) *
            metricPairing (gaussian M) (j.val • annihilatorGenerator M) g := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro g _
        rw [shiftedW, (concrete_isMetricGaussian M).add_left]
        ring
      _ = _ := sum_character_filter M _
  unfold subgroupConvolution averagedFullConvolution
  rw [hs]
  field_simp [cast_dimension_ne_zero M, cast_cofactor_ne_zero M]

/-- Apply [RW26, (36)], including the value at (0,0). -/
theorem average_pentagon36 {E : G M → ℂ}
    (hE : IsFiniteQuantumDilogarithm (gaussian M) E) (h : L2a.Index M) :
    averagedFullConvolution M E h =
      (∑ j : Fin (cofactor M),
        (E (iota M h) * E (shiftedW M h j) *
            gaussian M (iota M h + shiftedW M h j) *
            E (-(iota M h + shiftedW M h j)) -
          (groupOrder M : ℂ) * E 0 *
            (if iota M h = 0 ∧ shiftedW M h j = 0 then 1 else 0))) /
        L2a.convolutionScalar M := by
  let R : Fin (cofactor M) → ℂ := fun j =>
    E (iota M h) * E (shiftedW M h j) *
        gaussian M (iota M h + shiftedW M h j) *
        E (-(iota M h + shiftedW M h j)) -
      (groupOrder M : ℂ) * E 0 *
        (if iota M h = 0 ∧ shiftedW M h j = 0 then 1 else 0)
  have hp (j : Fin (cofactor M)) :
      (∑ g : G M, convolutionKernel M E h g *
        metricPairing (gaussian M) (shiftedW M h j) g) = R j * sqrtCard (G M) := by
    apply (div_eq_iff (sqrtCard_ne_zero (A := G M))).mp
    calc
      _ = normalizedSum (fun g : G M => E g * gaussian M g * E (iota M h - g) *
          metricPairing (gaussian M) g (shiftedW M h j)) := by
        unfold normalizedSum convolutionKernel
        congr 1
        apply Finset.sum_congr rfl
        intro g _
        rw [metric_pairing_symmetric (gaussian M) (shiftedW M h j) g]
      _ = R j := by
        rw [fqd_pentagon36 (concrete_isMetricGaussian M) (card_G_gt_four M) hE]
        dsimp only [R]
        rw [card_G M, show -iota M h - shiftedW M h j =
          -(iota M h + shiftedW M h j) by abel]
        ac_rfl
  change (∑ j : Fin (cofactor M), ∑ g : G M,
      convolutionKernel M E h g * metricPairing (gaussian M) (shiftedW M h j) g) /
      ((M : ℂ) * (cofactor M : ℂ)) = (∑ j : Fin (cofactor M), R j) /
        L2a.convolutionScalar M
  simp_rw [hp]
  rw [← Finset.sum_mul, sqrtCard_G M, ← convolutionScalar_sq M]
  field_simp [cast_dimension_ne_zero M, convolutionScalar_ne_zero M]

/-- The last equality of [RW26, (40)] is the case h≠0. -/
theorem equation40_nonzero {E : G M → ℂ}
    (hE : IsFiniteQuantumDilogarithm (gaussian M) E)
    (h : L2a.Index M) (hh : h ≠ 0) :
    subgroupConvolution M E h =
      (∑ j : Fin (cofactor M), E (iota M h) * E (shiftedW M h j) *
        gaussian M (iota M h + shiftedW M h j) *
        E (-(iota M h + shiftedW M h j))) / L2a.convolutionScalar M := by
  have hv : iota M h ≠ 0 := by
    intro hv
    apply hh
    apply iota_injective M
    simpa only [map_zero] using hv
  rw [average_extend_to_G, average_pentagon36 M hE]
  simp only [hv, false_and, if_false, mul_zero, sub_zero]

theorem epsilonAut_shiftedW (h : L2a.Index M) (j : Fin (cofactor M)) :
    epsilonAut M (shiftedW M h j) = iota M h + shiftedW M h j := by
  simp only [shiftedW, map_add, map_nsmul, witnessW_epsilon,
    epsilonAut_fixes_annihilatorGenerator]
  abel

/-- Both factors are nonzero in the application of [RW26, Thm. 5(ii)]. -/
theorem shiftedW_ne_zero (h : L2a.Index M) (hh : h ≠ 0) (j : Fin (cofactor M)) :
    shiftedW M h j ≠ 0 ∧ iota M h + shiftedW M h j ≠ 0 := by
  have hv : iota M h ≠ 0 := by
    intro hv
    apply hh
    apply iota_injective M
    simpa only [map_zero] using hv
  have hy : shiftedW M h j ≠ 0 := by
    intro hy
    have he := epsilonAut_shiftedW M h j
    rw [hy, map_zero, add_zero] at he
    exact hv he.symm
  refine ⟨hy, ?_⟩
  intro hz
  apply hy
  apply (epsilonAut M).injective
  rw [epsilonAut_shiftedW, hz, map_zero]

theorem equation40_term {E : G M → ℂ} (hE : FQDInput M E)
    (h : L2a.Index M) (hh : h ≠ 0) (j : Fin (cofactor M)) :
    E (iota M h) * E (shiftedW M h j) * gaussian M (iota M h + shiftedW M h j) *
      E (-(iota M h + shiftedW M h j)) = E (iota M h) := by
  have hz := (shiftedW_ne_zero M h hh j).2
  have hi := hE.epsilon_invariant (shiftedW M h j)
  rw [epsilonAut_shiftedW] at hi
  have hr := fqd_reflection (concrete_isMetricGaussian M) (card_G_gt_four M)
    hE.pentagon (iota M h + shiftedW M h j) hz
  rw [hi]
  calc
    _ = E (iota M h) *
        ((E (iota M h + shiftedW M h j) * E (-(iota M h + shiftedW M h j))) *
          gaussian M (iota M h + shiftedW M h j)) := by ring
    _ = E (iota M h) := by
      rw [hr, inv_mul_cancel₀ (gaussian_ne_zero M _), mul_one]

theorem subgroupConvolution_nonzero {E : G M → ℂ} (hE : FQDInput M E)
    (h : L2a.Index M) (hh : h ≠ 0) :
    subgroupConvolution M E h = L2a.convolutionScalar M * E (iota M h) := by
  rw [equation40_nonzero M hE.pentagon h hh]
  simp_rw [equation40_term M hE h hh]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← convolutionScalar_sq M]
  field_simp [convolutionScalar_ne_zero M]

/-- The value at zero. It follows from the origin quadratic; reflection is used only off zero. -/
theorem subgroupConvolution_zero {E : G M → ℂ}
    (hE : IsFiniteQuantumDilogarithm (gaussian M) E) :
    subgroupConvolution M E 0 = (E 0 ^ 2 + (M : ℂ) ^ 2 - 1) / (M : ℂ) ∧
    subgroupConvolution M E 0 = L2a.convolutionScalar M * E 0 + (M : ℂ) := by
  have hW : witnessW M (0 : L2a.Index M) = 0 := by
    simp [witnessW, coordinate]
  have hp (k : L2a.Index M) :
      metricPairing (gaussian M) (witnessW M 0) (iota M k) = 1 := by
    rw [hW]
    simp [metricPairing, gaussian_zero, gaussian_ne_zero]
  have ht (k : L2a.Index M) :
      convolutionKernel M E 0 (iota M k) *
          metricPairing (gaussian M) (witnessW M 0) (iota M k) =
        (if k = 0 then E 0 ^ 2 - 1 else 0) + 1 := by
    rw [hp, mul_one]
    by_cases hk : k = 0
    · subst k
      simp [convolutionKernel, gaussian_zero, pow_two]
    · have hv : iota M k ≠ 0 := by
        intro hv
        apply hk
        apply iota_injective M
        simpa only [map_zero] using hv
      have hr := fqd_reflection_all (concrete_isMetricGaussian M) (card_G_gt_four M)
        hE (iota M k)
      simp only [hv, if_false, mul_zero, add_zero] at hr
      simp only [convolutionKernel, map_zero, zero_sub, if_neg hk, zero_add]
      calc
        _ = E (iota M k) * E (-iota M k) * gaussian M (iota M k) := by ring
        _ = 1 := hr
  have hc : (Fintype.card (L2a.Index M) : ℂ) = (M : ℂ) ^ 2 := by
    simp [L2a.Index, Fintype.card_prod, pow_two]
  have hz : subgroupConvolution M E 0 =
      (E 0 ^ 2 + (M : ℂ) ^ 2 - 1) / (M : ℂ) := by
    unfold subgroupConvolution
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hc]
    ring
  refine ⟨hz, ?_⟩
  rw [hz, fqd_origin_quadratic (concrete_isMetricGaussian M) (card_G_gt_four M) hE,
    sqrtCard_G M]
  field_simp [cast_dimension_ne_zero M]
  ring

theorem restrict_origin {E : G M → ℂ} (hE : FQDInput M E) :
    restrict M E 0 = L2a.sqrtEpsilon M ^ 3 := by
  simpa only [restrict, Function.comp_apply, map_zero] using hE.origin

theorem restrict_reflection {E : G M → ℂ} (hE : FQDInput M E)
    (h : L2a.Index M) (hh : h ≠ 0) :
    restrict M E h * restrict M E (-h) = (L2a.gaussian M h)⁻¹ := by
  have hv : iota M h ≠ 0 := by
    intro hv
    apply hh
    apply iota_injective M
    simpa only [map_zero] using hv
  have hr := fqd_reflection (concrete_isMetricGaussian M) (card_G_gt_four M)
    hE.pentagon (iota M h) hv
  simpa only [restrict, Function.comp_apply, map_neg, gaussian_iota] using hr

theorem restrict_convolution {E : G M → ℂ} (hE : FQDInput M E) (h : L2a.Index M) :
    L2a.convolution M (restrict M E) h.1.val h.2.val =
      L2a.convolutionScalar M * restrict M E h + if h = 0 then (M : ℂ) else 0 := by
  rw [← subgroupConvolution_eq_L2a]
  by_cases hh : h = 0
  · subst h
    simpa [restrict] using
      (subgroupConvolution_zero M hE.pentagon).2
  · simpa only [restrict, Function.comp_apply, if_neg hh, add_zero] using
      subgroupConvolution_nonzero M hE h hh

end SICLean.L2b
