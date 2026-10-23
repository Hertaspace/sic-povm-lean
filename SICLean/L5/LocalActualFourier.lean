import SICLean.L5.LocalLemmaOne
import SICLean.L5.FiniteAlgebraicTransport
import SICLean.L5.LocalActualFourierAux

set_option autoImplicit false

/-!
# Concrete special-value calls to the local Lemma 1

All functions and coefficients here are the existing fixed-Qbar lifts from
`FiniteAlgebraicTransport`, the lifts already constructed. The square root is its
existing lift of the positive real `sqrtOrder`. The complex functions remain
`modularPhi`, `phiExtended`, `etaMultiplier`; no germ, point value, square-root branch,
or multiplier is redefined. [RW-rec, §4, §7, p. 7, p. 12] are the local sources. Finite
identities: [RW26, p. 3, p. 15, p. 16, p. 18, (3)--(7), (36)].
-/

noncomputable section

open scoped BigOperators MatrixGroups

namespace SICLean.L5.LocalActualFourier

open L4 LocalFourierSetup FiniteCosetMoments
open LocalActualFourierAux

variable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)

/-- Transport of the existing pairing laws, [RW-rec]; [RW26, p. 3, (3)]. -/
theorem actual_isBicharacter : IsBicharacter (FiniteAlgebraicTransport.pairing M hM) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply L3.M75.Gaussian.pairing_ne_zero M hM x y
    rw [← FiniteAlgebraicTransport.embed_pairing M hM x y, hxy, map_zero]
  · intro x x' y
    apply (show Function.Injective Galois.embed from Galois.embed.injective)
    simpa only [map_mul, FiniteAlgebraicTransport.embed_pairing] using
      L3.M75.Gaussian.pairing_add_left M hM x x' y
  · intro x y y'
    apply (show Function.Injective Galois.embed from Galois.embed.injective)
    simpa only [map_mul, FiniteAlgebraicTransport.embed_pairing] using
      L3.M75.Gaussian.pairing_add_right M hM x y y'

/-- Transport of the existing nondegenerate pairing; [RW-rec]; [RW26, p. 15]. -/
theorem actual_nondegenerate : Nondegenerate (FiniteAlgebraicTransport.pairing M hM) := by
  constructor
  · intro x hx
    by_contra hzero
    obtain ⟨y, hy⟩ := G2.DegenerateParameters.pairing_separates_right M hM x hzero
    apply hy
    rw [L3.M75.Gaussian.pairing_symmetric]
    simpa only [FiniteAlgebraicTransport.embed_pairing, map_one] using
      congrArg Galois.embed (hx y)
  · intro y hy
    by_contra hzero
    obtain ⟨x, hx⟩ := G2.DegenerateParameters.pairing_separates_right M hM y hzero
    apply hx
    simpa only [FiniteAlgebraicTransport.embed_pairing, map_one] using
      congrArg Galois.embed (hy x)

/-- The same positive-branch root normalizes the actual group cardinality. [RW-rec]; [RW26, p. 15].
-/
theorem actual_normalization_sq :
    letI : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
    letI : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
    (FiniteAlgebraicTransport.sqrtOrder M hM) ^ 2 =
      (Fintype.card (SpecialValueGroup M) : Galois.Qbar) := by
  let : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  let : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  have hcard : Fintype.card (SpecialValueGroup M) = (specialValueOrder M).toNat := by
    rw [← Nat.card_eq_fintype_card, specialValueGroup_card M hM]
  apply (show Function.Injective Galois.embed from Galois.embed.injective)
  simp only [map_pow, FiniteAlgebraicTransport.embed_sqrtOrder, map_natCast, hcard]
  rw [FiniteFourier.sqrtOrder, G2DegenerateParametersAux.sqrt_order_sq M hM]
  exact_mod_cast (Int.toNat_of_nonneg (specialValueOrder_pos M hM).le).symm

/-- Definitional finite-sum bridge to the general local transform. [RW-rec]; [RW26, p. 15]. -/
theorem generic_fourier_eq (f : SpecialValueGroup M → Galois.Qbar) (y : SpecialValueGroup M) :
    letI : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
    letI : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
    fourier (FiniteAlgebraicTransport.pairing M hM) (FiniteAlgebraicTransport.sqrtOrder M hM) f y =
      FiniteAlgebraicTransport.fourier M hM f y := by
  rfl

/-- Literal quotient compatibility; [RW-rec] derivation; [RW26, p. 18, (36)] is the finite input. -/
theorem generic_ratio_eq (h t : SpecialValueGroup M) :
    LocalLemmaOne.translationRatio (FiniteAlgebraicTransport.value M hM) h t =
      FiniteAlgebraicTransport.ratio M hM h t := by
  rfl

/-- [RW-rec]: all finite coefficients except sqrt(N) are valuation units; sqrt(N) is integral. This
assumes no unit property of E. -/
theorem actual_coefficient_values (v : AddValuation Galois.Qbar (WithTop ℝ))
    (x y : SpecialValueGroup M) :
    v (FiniteAlgebraicTransport.gaussian M hM x) = 0 ∧
      v (FiniteAlgebraicTransport.pairing M hM x y) = 0 ∧
      v (FiniteAlgebraicTransport.multiplier M hM) = 0 ∧
      0 ≤ v (FiniteAlgebraicTransport.sqrtOrder M hM) := by
  let : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  let : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  have hN : 0 < (specialValueOrder M).toNat := by
    have := specialValueOrder_pos M hM
    omega
  have hg (t : SpecialValueGroup M) : v (FiniteAlgebraicTransport.gaussian M hM t) = 0 := by
    apply L3.ValuationSupport.value_pow_eq_one v (n := 2 * (specialValueOrder M).toNat)
      (Nat.ne_of_gt (mul_pos (by norm_num) hN))
    apply (show Function.Injective Galois.embed from Galois.embed.injective)
    simpa only [map_pow, FiniteAlgebraicTransport.embed_gaussian, map_one] using
      L3.M74.gaussian_order M hM t
  have hpolar : FiniteAlgebraicTransport.gaussian M hM (x + y) =
      FiniteAlgebraicTransport.gaussian M hM x * FiniteAlgebraicTransport.gaussian M hM y *
        FiniteAlgebraicTransport.pairing M hM x y := by
    apply (show Function.Injective Galois.embed from Galois.embed.injective)
    simpa only [map_mul, FiniteAlgebraicTransport.embed_gaussian,
      FiniteAlgebraicTransport.embed_pairing] using
      L3.M75.Gaussian.gaussian_add M hM x y
  have hB : v (FiniteAlgebraicTransport.pairing M hM x y) = 0 := by
    simpa only [v.map_mul, hg, zero_add] using (congrArg v hpolar).symm
  refine ⟨hg x, hB, ?_, ?_⟩
  · apply L3.ValuationSupport.value_pow_eq_one v (by decide : (24 : ℕ) ≠ 0)
    apply (show Function.Injective Galois.embed from Galois.embed.injective)
    simpa only [map_pow, FiniteAlgebraicTransport.embed_multiplier, map_one] using
      etaMultiplier_pow_twentyFour M hM.1
  · apply L3.ValuationSupport.nonneg_of_square v
    rw [actual_normalization_sq M hM]
    exact L3.ValuationSupport.natCast_nonneg v _

/-- [RW-rec, (5)]: integrality transfers to the transform of E. Calls
`FiniteAlgebraicTransport.actual_fourier`; [RW26, p. 3, (6)]. -/
theorem actual_fourier_integral (v : AddValuation Galois.Qbar (WithTop ℝ))
    (hf : Integral v (FiniteAlgebraicTransport.value M hM)) :
    Integral v (FiniteAlgebraicTransport.fourier M hM (FiniteAlgebraicTransport.value M hM)) := by
  intro y
  obtain ⟨hg, _, hm, _⟩ := actual_coefficient_values M hM v y y
  rw [FiniteAlgebraicTransport.actual_fourier, v.map_mul, v.map_mul, hm, hg,
    zero_add, zero_add]
  exact hf y

/-- [RW-rec]: the final term is the constant one. The proof uses the already proved
`actual_inverse_fourier`;
same [RW26] finite source as the preceding theorem. -/
theorem actual_inverse_fourier_integral (v : AddValuation Galois.Qbar (WithTop ℝ))
    (hf : Integral v (FiniteAlgebraicTransport.value M hM)) :
    Integral v (FiniteAlgebraicTransport.fourier M hM
      (fun t => (FiniteAlgebraicTransport.value M hM t)⁻¹)) := by
  intro y
  obtain ⟨_, _, hm, _⟩ := actual_coefficient_values M hM v y y
  rw [FiniteAlgebraicTransport.actual_inverse_fourier]
  apply value_sub_nonneg v ?_ (by simp)
  exact value_mul_nonneg v (value_inv_nonneg_of_zero v hm) (hf y)

/-- [RW-rec]: an actual translation quotient is unit-valued when E is, with nonvanishing from [RW26,
p. 3, (5)]. -/
theorem actual_ratio_unitValued (v : AddValuation Galois.Qbar (WithTop ℝ))
    (hu : UnitValued v (FiniteAlgebraicTransport.value M hM)) (h : SpecialValueGroup M) :
    UnitValued v (FiniteAlgebraicTransport.ratio M hM h) := by
  intro t
  rw [FiniteAlgebraicTransport.ratio, v.map_div, hu (t + h), hu t]
  simp

/-- [RW-rec]: both required Fourier transforms are integral, by the existing `ratio_fourier` and
`ratio_inverse_fourier`. [RW26, p. 18, (36)] supplies their finite input. -/
theorem actual_ratio_fouriers_integral (v : AddValuation Galois.Qbar (WithTop ℝ))
    (hu : UnitValued v (FiniteAlgebraicTransport.value M hM)) (h : SpecialValueGroup M) :
    Integral v (FiniteAlgebraicTransport.fourier M hM (FiniteAlgebraicTransport.ratio M hM h)) ∧
      Integral v (FiniteAlgebraicTransport.fourier M hM
        (fun t => (FiniteAlgebraicTransport.ratio M hM h t)⁻¹)) := by
  have hR := actual_ratio_unitValued M hM v hu h
  constructor
  · intro t
    obtain ⟨hg, _, _, hsqrt⟩ := actual_coefficient_values M hM v h t
    rw [FiniteAlgebraicTransport.ratio_fourier]
    apply value_add_nonneg v
    · exact value_mul_nonneg v (by rw [hu])
        (value_sub_nonneg v (value_inv_nonneg_of_zero v (hR t)) (by simp))
    · exact value_mul_nonneg v
        (value_mul_nonneg v hsqrt (value_inv_nonneg_of_zero v hg))
        (delta_nonneg v M (t + h))
  · intro t
    obtain ⟨hg, hB, _, hsqrt⟩ := actual_coefficient_values M hM v h t
    rw [FiniteAlgebraicTransport.ratio_inverse_fourier]
    apply value_sub_nonneg v
    · apply value_add_nonneg v
      · rw [div_eq_mul_inv]
        exact value_mul_nonneg v (by rw [hR]) (value_inv_nonneg_of_zero v (hu h))
      · exact value_mul_nonneg v hsqrt (delta_nonneg v M t)
    · rw [div_eq_mul_inv]
      exact value_mul_nonneg v
        (value_mul_nonneg v (value_inv_nonneg_of_zero v hg) (by rw [hB]))
        (value_inv_nonneg_of_zero v (hu h))

/-- [RW-rec]: scaled-integrality statement needed before Theorem 5 proves that E is a unit. The four
explicit hypotheses are exactly the valuations checked in Theorem 4; no global E-integrality or
E-unit hypothesis occurs. Finite inputs: [RW26, p. 18, (36)]. -/
theorem actual_scaled_ratio_fouriers_integral (v : AddValuation Galois.Qbar (WithTop ℝ))
    (z : Galois.Qbar) (h : SpecialValueGroup M)
    (hz : 0 ≤ v z) (hzE : 0 ≤ v (z * FiniteAlgebraicTransport.value M hM h))
    (hR : Integral v (fun t => z * FiniteAlgebraicTransport.ratio M hM h t))
    (hiR : Integral v (fun t =>
      z * FiniteAlgebraicTransport.value M hM h / FiniteAlgebraicTransport.ratio M hM h t)) :
    Integral v (FiniteAlgebraicTransport.fourier M hM
      (fun t => z * FiniteAlgebraicTransport.ratio M hM h t)) ∧
      Integral v (FiniteAlgebraicTransport.fourier M hM (fun t =>
        z * FiniteAlgebraicTransport.value M hM h / FiniteAlgebraicTransport.ratio M hM h t)) := by
  have hcoeff := actual_coefficient_values M hM v h h
  have hg : 0 ≤ v (FiniteAlgebraicTransport.gaussian M hM h)⁻¹ :=
    value_inv_nonneg_of_zero v hcoeff.1
  have hsqrt : 0 ≤ v (FiniteAlgebraicTransport.sqrtOrder M hM) := hcoeff.2.2.2
  have hcancel (a : Galois.Qbar) :
      (z * FiniteAlgebraicTransport.value M hM h) *
        (a / FiniteAlgebraicTransport.value M hM h) = z * a := by
    calc
      _ = z * a * (FiniteAlgebraicTransport.value M hM h /
        FiniteAlgebraicTransport.value M hM h) := by ring
      _ = z * a := by
        rw [div_self (FiniteAlgebraicTransport.value_ne_zero M hM h), mul_one]
  constructor
  · intro t
    have heq :
        FiniteAlgebraicTransport.fourier M hM
          (fun u => z * FiniteAlgebraicTransport.ratio M hM h u) t =
        z * FiniteAlgebraicTransport.value M hM h /
            FiniteAlgebraicTransport.ratio M hM h t -
          z * FiniteAlgebraicTransport.value M hM h +
          z * FiniteAlgebraicTransport.sqrtOrder M hM *
            (FiniteAlgebraicTransport.gaussian M hM h)⁻¹ *
            FiniteAlgebraicTransport.delta M (t + h) := by
      rw [fourier_const_mul, FiniteAlgebraicTransport.ratio_fourier]
      ring
    rw [heq]
    exact value_add_nonneg v (value_sub_nonneg v (hiR t) hzE)
      (value_mul_nonneg v (value_mul_nonneg v (value_mul_nonneg v hz hsqrt) hg)
        (delta_nonneg v M (t + h)))
  · intro t
    have hlinear :
        FiniteAlgebraicTransport.fourier M hM
          (fun u => z * FiniteAlgebraicTransport.value M hM h /
            FiniteAlgebraicTransport.ratio M hM h u) t =
        (z * FiniteAlgebraicTransport.value M hM h) *
          FiniteAlgebraicTransport.fourier M hM
            (fun u => (FiniteAlgebraicTransport.ratio M hM h u)⁻¹) t := by
      simpa only [div_eq_mul_inv] using
        fourier_const_mul M hM (z * FiniteAlgebraicTransport.value M hM h)
          (fun u => (FiniteAlgebraicTransport.ratio M hM h u)⁻¹) t
    have heq :
        FiniteAlgebraicTransport.fourier M hM
          (fun u => z * FiniteAlgebraicTransport.value M hM h /
            FiniteAlgebraicTransport.ratio M hM h u) t =
        z * FiniteAlgebraicTransport.ratio M hM h (-t) +
          (z * FiniteAlgebraicTransport.value M hM h) *
            FiniteAlgebraicTransport.sqrtOrder M hM *
            FiniteAlgebraicTransport.delta M t -
          z * (FiniteAlgebraicTransport.gaussian M hM h)⁻¹ *
            FiniteAlgebraicTransport.pairing M hM h t := by
      rw [hlinear, FiniteAlgebraicTransport.ratio_inverse_fourier,
        mul_sub, mul_add, hcancel, hcancel]
      ring
    rw [heq]
    have hB : 0 ≤ v (FiniteAlgebraicTransport.pairing M hM h t) := by
      rw [(actual_coefficient_values M hM v h t).2.1]
    exact value_sub_nonneg v
      (value_add_nonneg v (hR (-t))
        (value_mul_nonneg v (value_mul_nonneg v hzE hsqrt) (delta_nonneg v M t)))
      (value_mul_nonneg v (value_mul_nonneg v hz hg) hB)

/-- [RW-rec]: the first concrete Theorem 7 call, on E. The only unit input is Theorem 5's
conclusion. Its finite inputs are the identities cited with the statements below. -/
theorem actual_lemma1_iii {p s : ℕ} [Fact p.Prime]
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hodd : p ≠ 2) (hs : 1 ≤ s) {C : Type*} [AddCommGroup C] [Fintype C]
    (hC : Nat.Coprime p (Fintype.card C))
    (e : (Point p s 2 × C) ≃+ SpecialValueGroup M)
    (hu : UnitValued v (FiniteAlgebraicTransport.value M hM)) (x : SpecialValueGroup M)
    (a : AffineCoordinates p 2)
    (A D : ZMod p → Residue v)
    (hfactor : ∀ u, planeRestriction e v (FiniteAlgebraicTransport.value M hM) x a u =
      A u.1 * D u.2) :
    (∃ c : Residue v, c ≠ 0 ∧ ∀ t, A t = c) ∨
      (∃ c : Residue v, c ≠ 0 ∧ ∀ t, D t = c) := by
  let : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  let : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  have hf : Integral v (FiniteAlgebraicTransport.value M hM) :=
    fun t => le_of_eq (hu t).symm
  apply LocalLemmaOne.lemma1_iii_factors v hp hodd hs hC
    (FiniteAlgebraicTransport.pairing M hM) (actual_isBicharacter M hM)
    (actual_nondegenerate M hM) (FiniteAlgebraicTransport.sqrtOrder M hM)
    (actual_normalization_sq M hM) (FiniteAlgebraicTransport.value M hM)
    ?_ e hu ?_ x a A D hfactor
  · intro y
    rw [generic_fourier_eq]
    exact actual_fourier_integral M hM v hf y
  · intro y
    rw [generic_fourier_eq]
    exact actual_inverse_fourier_integral M hM v hf y

/-- [RW-rec]: the second concrete Theorem 7 call, on R_h. This does not infer a uniform direction
across cosets; the remaining contradiction and global choice belong to the uniform-direction
argument. -/
theorem actual_ratio_lemma1_iii {p s : ℕ} [Fact p.Prime]
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hodd : p ≠ 2) (hs : 1 ≤ s) {C : Type*} [AddCommGroup C] [Fintype C]
    (hC : Nat.Coprime p (Fintype.card C))
    (e : (Point p s 2 × C) ≃+ SpecialValueGroup M)
    (hu : UnitValued v (FiniteAlgebraicTransport.value M hM)) (h x : SpecialValueGroup M)
    (a : AffineCoordinates p 2)
    (A D : ZMod p → Residue v)
    (hfactor : ∀ u, planeRestriction e v (FiniteAlgebraicTransport.ratio M hM h) x a u =
      A u.1 * D u.2) :
    (∃ c : Residue v, c ≠ 0 ∧ ∀ t, A t = c) ∨
      (∃ c : Residue v, c ≠ 0 ∧ ∀ t, D t = c) := by
  let : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  let : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  obtain ⟨hF, hFi⟩ := actual_ratio_fouriers_integral M hM v hu h
  apply LocalLemmaOne.lemma1_iii_factors v hp hodd hs hC
    (FiniteAlgebraicTransport.pairing M hM) (actual_isBicharacter M hM)
    (actual_nondegenerate M hM) (FiniteAlgebraicTransport.sqrtOrder M hM)
    (actual_normalization_sq M hM) (FiniteAlgebraicTransport.ratio M hM h)
    ?_ e (actual_ratio_unitValued M hM v hu h) ?_ x a A D hfactor
  · intro y
    rw [generic_fourier_eq]
    exact hF y
  · intro y
    rw [generic_fourier_eq]
    exact hFi y

#check @generic_fourier_eq
#check @actual_scaled_ratio_fouriers_integral
#check @actual_lemma1_iii
#check @actual_ratio_lemma1_iii

end SICLean.L5.LocalActualFourier
