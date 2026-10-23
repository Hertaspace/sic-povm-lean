import SICLean.L2r.Inputs

set_option autoImplicit false

/-!
# Character projection and the twisted convolution

F⁺ = E and F⁻ = `minusValues E`, derived from [RW26, (31)] through [RW26, (36)].
H is the large d-torsion subgroup, corresponding to `H_gamma^perp`, while
`smallSubgroup` corresponds to `H_gamma`.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2r

theorem restrict_origin (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) :
    restrict d r E 0 = originValue d r := by
  simpa only [restrict, Function.comp_apply, map_zero] using hE.origin

theorem restrict_reflection (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) (p : Index d) (hp : p ≠ 0) :
    restrict d r E p * restrict d r E (-p) = (torsionGaussian d r p)⁻¹ := by
  have hi : iota d r p ≠ 0 := by
    intro hi
    apply hp
    apply iota_injective d r
    simpa only [map_zero] using hi
  simpa only [restrict, Function.comp_apply, map_neg, gaussian_iota] using
    L2b.fqd_reflection (concrete_isMetricGaussian d r) (card_G_gt_four d r)
      hE.pentagon (iota d r p) hi

theorem restrict_ne_zero (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) (p : Index d) :
    restrict d r E p ≠ 0 := by
  exact L2b.fqd_everywhere_ne_zero (concrete_isMetricGaussian d r) hE.pentagon
    (iota d r p)

/-- The unsimplified projection equation keeps F⁺ and F⁻ distinct at zero.
v=-ιp, Y-TY=v. Every five-term instance has v≠0. -/
theorem projected_ratio_pentagon (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) (p : Index d) (hp : p ≠ 0) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ j : Fin (cofactor d r),
      E (j.val • annihilatorGenerator d r - witnessY d r p) /
        minusValues E (j.val • annihilatorGenerator d r - witnessY d r p - iota d r p)) /
        (Real.sqrt (cofactor d r) : ℂ) =
      (∑ q : Index d,
        L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
          E (iota d r q - iota d r p) / minusValues E (iota d r q)) /
        ((d : ℂ) * minusValues E (-iota d r p)) := by
  classical
  haveI : NeZero d := admissibleDimensionNeZero d r
  have hmetric := concrete_isMetricGaussian d r
  have hi : iota d r p ≠ 0 := by
    intro hi
    apply hp
    apply iota_injective d r
    simpa only [map_zero] using hi
  let f : G d r → ℂ := fun x => E x / minusValues E (x - iota d r p)
  let S : ℂ := ∑ j : Fin (cofactor d r),
    f (j.val • annihilatorGenerator d r - witnessY d r p)
  let R : ℂ := ∑ q : Index d,
    L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
      E (iota d r q - iota d r p) / minusValues E (iota d r q)
  have henumerate (F : G d r → ℂ) :
      (∑ g : G d r, if g ∈ smallSubgroup d r then F g else 0) =
        ∑ j : Fin (cofactor d r), F (j.val • annihilatorGenerator d r) := by
    let e : Fin (cofactor d r) ≃ smallSubgroup d r :=
      (finCongr (annihilatorGenerator_order d r).symm).trans
        (finEquivZMultiples (isOfFinAddOrder_of_finite (annihilatorGenerator d r)))
    have he (j : Fin (cofactor d r)) : (e j).val = j.val • annihilatorGenerator d r := rfl
    rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    change (∑ g : smallSubgroup d r, F g) = _
    exact (Fintype.sum_equiv e _ _ (fun j => congrArg F (he j).symm)).symm
  have hshift :
      (∑ x : G d r, if x + witnessY d r p ∈ smallSubgroup d r then f x else 0) =
        ∑ g : G d r, if g ∈ smallSubgroup d r then f (g - witnessY d r p) else 0 := by
    apply Fintype.sum_equiv (Equiv.addRight (witnessY d r p))
    intro x
    simp
  have hleft :
      (∑ q : Index d,
        L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
          L2b.normalizedSum (fun x : G d r =>
            L2b.metricPairing (gaussian d r) x (iota d r q) * f x)) =
        (d : ℂ) ^ 2 * S / L2b.sqrtCard (G d r) := by
    calc
      _ = (∑ q : Index d, ∑ x : G d r,
          f x * L2b.metricPairing (gaussian d r)
            (x + witnessY d r p) (iota d r q)) / L2b.sqrtCard (G d r) := by
        simp only [L2b.normalizedSum, Finset.sum_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro x _
        rw [hmetric.add_left]
        ring
      _ = (∑ x : G d r, f x *
          (if x + witnessY d r p ∈ smallSubgroup d r then (d : ℂ) ^ 2 else 0)) /
            L2b.sqrtCard (G d r) := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, torsion_character_sum]
      _ = (d : ℂ) ^ 2 *
          (∑ x : G d r, if x + witnessY d r p ∈ smallSubgroup d r then f x else 0) /
            L2b.sqrtCard (G d r) := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> ring
      _ = _ := by rw [hshift, henumerate]
  have hpent (q : Index d) :
      L2b.normalizedSum (fun x : G d r =>
        L2b.metricPairing (gaussian d r) x (iota d r q) * f x) =
      E (iota d r q - iota d r p) / minusValues E (iota d r q) /
        minusValues E (-iota d r p) := by
    have hn : ¬ (iota d r q = 0 ∧ -iota d r p = 0) :=
      fun h => (neg_ne_zero.mpr hi) h.2
    simpa only [f, sub_eq_add_neg, mul_div_assoc, div_div] using
      fqd_ratio_pentagon hmetric (card_G_gt_four d r) hE.pentagon
        (iota d r q) (-iota d r p) hn
  have hproject : (d : ℂ) ^ 2 * S / L2b.sqrtCard (G d r) =
      R / minusValues E (-iota d r p) := by
    rw [← hleft]
    simp_rw [hpent]
    dsimp only [R]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hs : (Real.sqrt (cofactor d r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (cofactor d r)))).ne'
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have he := minusValues_ne_zero hmetric hE.pentagon (-iota d r p)
  rw [sqrtCard_G] at hproject
  change S / (Real.sqrt (cofactor d r) : ℂ) =
    R / ((d : ℂ) * minusValues E (-iota d r p))
  apply (div_eq_div_iff hs (mul_ne_zero hd he)).mpr
  have hcross := (div_eq_div_iff (mul_ne_zero hd hs) he).mp hproject
  apply mul_left_cancel₀ hd
  linear_combination hcross

/-- Invariance can be used only after the two shifted arguments are nonzero. -/
theorem projected_ratio_left (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) (p : Index d) (hp : p ≠ 0)
    (j : Fin (cofactor d r)) :
    E (j.val • annihilatorGenerator d r - witnessY d r p) /
      minusValues E (j.val • annihilatorGenerator d r - witnessY d r p - iota d r p) = 1 :=
  by
  have hj : j.val • annihilatorGenerator d r ∈ smallSubgroup d r :=
    AddSubgroup.nsmul_mem _
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩) j.val
  obtain ⟨h0, h1⟩ := shifted_witness_ne_zero d r p hp _ hj
  have ht : epsilonAut d r (j.val • annihilatorGenerator d r - witnessY d r p) =
      j.val • annihilatorGenerator d r - witnessY d r p - iota d r p := by
    rw [map_sub, smallSubgroup_fixed d r _ hj]
    have hw := witnessY_epsilon d r p
    rw [sub_eq_iff_eq_add] at hw
    rw [hw]
    abel
  have hi := hE.epsilon_invariant
    (j.val • annihilatorGenerator d r - witnessY d r p)
  rw [ht] at hi
  rw [minusValues, if_neg h1, ← hi]
  exact div_self (L2b.fqd_everywhere_ne_zero (concrete_isMetricGaussian d r)
    hE.pentagon _)

/-- Replacing F⁻(0)=A⁻¹ with F⁺(0)=A removes exactly d√a E(v).
The denominator at the zero summand is E(0), not E(v). -/
theorem replace_origin_term (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) (p : Index d) (hp : p ≠ 0) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ q : Index d,
      L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
        E (iota d r q - iota d r p) / E (iota d r q)) =
      (∑ q : Index d,
        L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
          E (iota d r q - iota d r p) / minusValues E (iota d r q)) -
        (originValue d r - (originValue d r)⁻¹) * E (-iota d r p) := by
  haveI : NeZero d := admissibleDimensionNeZero d r
  have ht (q : Index d) :
      L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
          E (iota d r q - iota d r p) / E (iota d r q) =
        L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
            E (iota d r q - iota d r p) / minusValues E (iota d r q) -
          (if q = 0 then
            (originValue d r - (originValue d r)⁻¹) * E (-iota d r p) else 0) := by
    by_cases hq : q = 0
    · subst q
      simp only [map_zero, zero_sub, L2b.aux_pairing_zero_right
        (concrete_isMetricGaussian d r), one_mul, minusValues,
        hE.origin, ite_true, div_inv_eq_mul]
      ring
    · have hi : iota d r q ≠ 0 := by
        intro hi
        apply hq
        apply iota_injective d r
        simpa only [map_zero] using hi
      simp only [minusValues, if_neg hi, if_neg hq, sub_zero]
  simp_rw [ht]
  rw [Finset.sum_sub_distrib]
  simp

theorem ratio_sum_nonzero (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) (p : Index d) (hp : p ≠ 0) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ q : Index d,
      L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
        E (iota d r q - iota d r p) / E (iota d r q)) = 0 := by
  haveI : NeZero d := admissibleDimensionNeZero d r
  have hi : iota d r p ≠ 0 := by
    intro hi
    apply hp
    apply iota_injective d r
    simpa only [map_zero] using hi
  have hs : (Real.sqrt (cofactor d r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (cofactor d r)))).ne'
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have he : E (-iota d r p) ≠ 0 :=
    L2b.fqd_everywhere_ne_zero (concrete_isMetricGaussian d r) hE.pentagon _
  have hs2 : (Real.sqrt (cofactor d r) : ℂ) ^ 2 = (cofactor d r : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hproj := projected_ratio_pentagon d r hE p hp
  simp_rw [projected_ratio_left d r hE p hp] at hproj
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, minusValues, if_neg (neg_ne_zero.mpr hi)] at hproj
  have hsum :
      (∑ q : Index d,
        L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
          E (iota d r q - iota d r p) / minusValues E (iota d r q)) =
        (d : ℂ) * (Real.sqrt (cofactor d r) : ℂ) * E (-iota d r p) := by
    apply mul_right_cancel₀ hs
    rw [show (d : ℂ) * (Real.sqrt (cofactor d r) : ℂ) * E (-iota d r p) *
        (Real.sqrt (cofactor d r) : ℂ) =
        (cofactor d r : ℂ) * ((d : ℂ) * E (-iota d r p)) by
      rw [← hs2]
      ring]
    exact ((div_eq_div_iff hs (mul_ne_zero hd he)).mp hproj).symm
  rw [replace_origin_term d r hE p hp, hsum,
    (normalizer_identities (Fact.out : Admissible d r)).1]
  ring

theorem restrict_twisted_ratio (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) (p : Index d) :
    twistedRatio d r (restrict d r E) p = if p = 0 then (d : ℂ) ^ 2 else 0 := by
  haveI : NeZero d := admissibleDimensionNeZero d r
  have hl (q : Index d) : label d (lift q - lift p) = q - p := by
    ext <;> simp [label, lift]
  have hr : twistedRatio d r (restrict d r E) p =
      ∑ q : Index d,
        L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) *
          E (iota d r q - iota d r p) / E (iota d r q) := by
    unfold twistedRatio valueAt restrict
    apply Finset.sum_congr rfl
    intro q _
    simp only [Function.comp_apply, hl, map_sub, pairing_witnessY]
  rw [hr]
  by_cases hp : p = 0
  · subst p
    have hw : witnessY d r (0 : Index d) = 0 := by simp [witnessY, coordinate]
    simp only [map_zero, sub_zero, hw,
      L2b.aux_pairing_zero_left (concrete_isMetricGaussian d r), one_mul,
      div_self (L2b.fqd_everywhere_ne_zero (concrete_isMetricGaussian d r)
        hE.pentagon _)]
    simp [Index, pow_two]
  · rw [if_neg hp]
    exact ratio_sum_nonzero d r hE p hp

theorem rwConvolutionInput_of_FQD_rank (d r : ℕ) [Fact (Admissible d r)]
    {E : G d r → ℂ} (hE : FQDInput d r E) :
    RWConvolutionInput d r (restrict d r E) := by
  exact ⟨restrict_origin d r hE, restrict_reflection d r hE,
    restrict_twisted_ratio d r hE⟩

end SICLean.L2r
