import SICLean.L4.ModularDistribution
import SICLean.L5.DistributionHermiteAux

set_option autoImplicit false

/-!
# [RW-rec, Lemma 10]: n by m Hermite grouping of modular Φ

[RW-rec, Appendix A, pp. 18--19, Lem. 10]. The product identities use
[RW26, p. 2, (1)], [RW26, p. 6, (19)], and [RW26, p. 14, Prop. 9].

Both A_i and B_ij are ceilings, expressed by minus Euclidean division.
Germs delete one point in the complex z variable. Joint comparisons are
analytic-chart cross products. A point-value theorem has explicit
holomorphic-center hypotheses, including centers where numerators vanish.
The slit-plane square root is `Complex.sqrt` inside `modularPhi`.
-/

noncomputable section
open SICLean.L4
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L5.DistributionHermite

def hermiteMatrix (n m : ℕ) (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(n : ℤ), k; 0, (m : ℤ)]

def hermiteTau (n m : ℕ) (k : ℤ) (τ : ℂ) : ℂ :=
  ((n : ℂ) * τ + (k : ℂ)) / (m : ℂ)

def hermiteArgument (m i j : ℕ) (z τ : ℂ) : ℂ :=
  (z + (i : ℂ) * τ + (j : ℂ)) / (m : ℂ)

def hermiteNumIndex (n : ℕ) (u : ℤ) (i : ℕ) : ℤ := -(((i : ℤ) - u) / (n : ℤ))

def hermiteDenIndex (MJ : SL(2, ℤ)) (n i j : ℕ) : ℤ :=
  -((MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ)) / (n : ℤ))

def hermiteResidue (MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (ij : ℤ × ℤ) : ℤ × ℤ :=
  let a := MJ 1 1 * ij.1 - MJ 1 0 * ij.2
  let b := -MJ 0 1 * ij.1 + MJ 0 0 * ij.2
  let t := -(a / (n : ℤ))
  (a + (n : ℤ) * t, (b + k * t) % (m : ℤ))

def hermiteProduct (MI MJ : SL(2, ℤ)) (n m : ℕ) (k u : ℤ) (z τ : ℂ) : ℂ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m,
    modularPhi MI (hermiteNumIndex n u i) (hermiteDenIndex MJ n i j)
      (hermiteArgument m i j z τ) (hermiteTau n m k τ)

/-- [RW-rec, p. 18, Lem. 10]; [RW26, p. 14, Prop. 9]. -/
theorem hermite_indices_eq_ceil (MJ : SL(2, ℤ)) (n : ℕ) (hn : 0 < n)
    (u : ℤ) (i j : ℕ) :
    hermiteNumIndex n u i = ⌈((u : ℚ) - (i : ℚ)) / (n : ℚ)⌉ ∧
      hermiteDenIndex MJ n i j =
        ⌈(-(MJ 1 1 : ℚ) * (i : ℚ) + (MJ 1 0 : ℚ) * (j : ℚ)) / (n : ℚ)⌉ := by
  exact DistributionHermiteAux.hermite_indices_eq_ceil MJ n hn u i j

/-- [RW-rec, pp. 18--19, Lem. 10]; [RW26, p. 14, Prop. 9].
The first inverse residue lies in the half-open interval. -/
theorem hermite_den_residue_bounds (MJ : SL(2, ℤ)) (n : ℕ) (hn : 0 < n) (i j : ℕ) :
    0 ≤ MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ) + (n : ℤ) * hermiteDenIndex MJ n i j ∧
      MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ) +
        (n : ℤ) * hermiteDenIndex MJ n i j < (n : ℤ) := by
  exact DistributionHermiteAux.hermite_den_residue_bounds MJ n hn i j

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6].
The ceiling indices match along an inverse-ε orbit, by the integer
coordinate equation. -/
theorem hermite_orbit_index_match (MJ : SL(2, ℤ)) (n : ℕ) (hn : 0 < n)
    (u h : ℤ) (i j i' : ℕ)
    (hstep : u + MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ) = (i' : ℤ) + (n : ℤ) * h) :
    hermiteNumIndex n u i' = hermiteDenIndex MJ n i j + h := by
  exact DistributionHermiteAux.hermite_orbit_index_match MJ n hn u h i j i' hstep

/-- [RW-rec, Appendix A, p. 18]; [RW26, p. 14].
Both products use the same automorphy factor. -/
theorem hermite_automorphy (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (τ : ℂ)
    (hn : 0 < n) (hm : 0 < m)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ))
    (hden : etaDenom MJ τ ≠ 0) :
    etaDenom MI (hermiteTau n m k τ) = etaDenom MJ τ ∧
      etaMobius MI (hermiteTau n m k τ) = hermiteTau n m k (etaMobius MJ τ) := by
  exact DistributionHermiteAux.hermite_automorphy MI MJ n m k τ hn hm hH hden

/-- [RW-rec, Appendix A, pp. 18--19]; [RW26, p. 2, (1)].
The common slit domain of the germ. -/
theorem hermite_domain (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (τ : ℂ)
    (hn : 0 < n) (hm : 0 < m)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) :
    hermiteTau n m k τ ∈ modularPhiDomain MI ↔ τ ∈ modularPhiDomain MJ := by
  exact DistributionHermiteAux.hermite_domain MI MJ n m k τ hn hm hH

/-- [RW-rec, pp. 18--19, Lem. 10]; [RW26, p. 14, Prop. 9].
The inverse action on J/I is a permutation. -/
theorem hermite_inverse_residues_bijOn (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ)
    (hn : 0 < n) (hm : 0 < m)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) :
    Set.BijOn (hermiteResidue MJ n m k)
      ((Set.Ico 0 (n : ℤ)) ×ˢ (Set.Ico 0 (m : ℤ)))
      ((Set.Ico 0 (n : ℤ)) ×ˢ (Set.Ico 0 (m : ℤ))) := by
  exact DistributionHermiteAux.hermite_inverse_residues_bijOn MI MJ n m k hn hm hH

/-- [RW-rec, Appendix A, p. 18]; [RW26, p. 14, Prop. 9].
[RW26, p. 28, (57)] is a logarithmic series, distinct from this finite product. -/
theorem hermite_roots_product (m : ℕ) (hm : 0 < m) (X : ℂ) :
    ∏ j ∈ Finset.range m, (1 - e ((j : ℂ) / (m : ℂ)) * X) = 1 - X ^ m := by
  exact DistributionHermiteAux.hermite_roots_product m hm X

/-- The same product. The convergent q-product is the case ‖q‖ < 1. -/
theorem hermite_qPochhammer_roots (m : ℕ) (hm : 0 < m) (X q : ℂ)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ∏ j ∈ Finset.range m, qPochhammer (e ((j : ℂ) / (m : ℂ)) * X) q =
      qPochhammer (X ^ m) (q ^ m) := by
  exact DistributionHermiteAux.hermite_qPochhammer_roots m hm X q hq0 hq1

/-- [RW-rec, Appendix A, p. 18]; [RW26, p. 2, (1)]; [RW26, p. 14, Prop. 9].
Numerators are grouped before dividing, so common zeros are allowed. -/
theorem hermite_q_numerators (n m : ℕ) (k u : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (hτ : 0 < τ.im) :
    (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m,
      modularPhiQNumerator (hermiteNumIndex n u i)
        (hermiteArgument m i j z τ) (hermiteTau n m k τ)) =
      modularPhiQNumerator u z τ := by
  exact DistributionHermiteAux.hermite_q_numerators n m k u z τ hn hm hτ

/-- [RW-rec, pp. 18--19, Lem. 10]; [RW26, p. 2, (1)]; [RW26, p. 14, Prop. 9].
The denominator indices use the inverse Hermite permutation. -/
theorem hermite_q_denominators (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) (hτ : 0 < τ.im) :
    (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m,
      modularPhiQDenominator MI (hermiteDenIndex MJ n i j)
        (hermiteArgument m i j z τ) (hermiteTau n m k τ)) =
      modularPhiQDenominator MJ 0 z τ := by
  exact DistributionHermiteAux.denominator_product MI MJ n m k z τ hn hm hI hJ hH hτ

/-- [RW-rec, pp. 18--19, Lem. 10]; [RW26, p. 2, (1)]; [RW26, p. 6].
A germ in the single variable z. -/
theorem hermitePhi_upper_germ (MI MJ : SL(2, ℤ)) (n m : ℕ) (k u : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) (hτ : 0 < τ.im) :
    (fun w => modularPhi MJ u 0 w τ) =ᶠ[𝓝[≠] z]
      (fun w => hermiteProduct MI MJ n m k u w τ) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hτI : 0 < (hermiteTau n m k τ).im := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    simpa [hermiteTau, Complex.div_natCast_im] using div_pos (mul_pos hnR hτ) hmR
  have hfac : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range m,
      (fun w => modularPhi MI (hermiteNumIndex n u i) (hermiteDenIndex MJ n i j)
        (hermiteArgument m i j w τ) (hermiteTau n m k τ)) =ᶠ[𝓝[≠] z]
      (fun w => modularPhiQProduct MI (hermiteNumIndex n u i) (hermiteDenIndex MJ n i j)
        (hermiteArgument m i j w τ) (hermiteTau n m k τ)) := by
    intro i hi j hj
    have ht : Tendsto (fun w => hermiteArgument m i j w τ) (𝓝[≠] z)
        (𝓝[≠] (hermiteArgument m i j z τ)) := by
      simpa [hermiteArgument, div_eq_mul_inv, add_mul, mul_add,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using
        ModularDistributionAux.tendsto_affine_nhdsNE ((m : ℂ)⁻¹)
          (((i : ℂ) * τ + (j : ℂ)) / (m : ℂ)) z (inv_ne_zero hmC)
    exact (modularPhi_eq_qProduct_germ MI hI (hermiteNumIndex n u i)
      (hermiteDenIndex MJ n i j) (hermiteArgument m i j z τ)
      (hermiteTau n m k τ) hτI).comp_tendsto ht
  have hall := (Finset.eventually_all _).mpr fun i hi =>
    (Finset.eventually_all _).mpr fun j hj => hfac i hi j hj
  filter_upwards [modularPhi_eq_qProduct_germ MJ hJ u 0 z τ hτ, hall] with w hw hwi
  have hp : hermiteProduct MI MJ n m k u w τ =
      ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m,
        modularPhiQProduct MI (hermiteNumIndex n u i) (hermiteDenIndex MJ n i j)
          (hermiteArgument m i j w τ) (hermiteTau n m k τ) := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    exact hwi i hi j hj
  rw [hw, hp]
  simp_rw [modularPhiQProduct, Finset.prod_div_distrib]
  rw [hermite_q_numerators n m k u w τ hn hm hτ,
    hermite_q_denominators MI MJ n m k w τ hn hm hI hJ hH hτ]

/-- [RW-rec, pp. 18--19, Lem. 10]; [RW26, p. 6].
Joint-chart form, including zeros of chart denominators.
This is an equality of chart numerators and denominators, not an equality
on a punctured two-variable neighborhood. -/
theorem hermitePhi_chart_cross_mul (MI MJ : SL(2, ℤ)) (n m : ℕ) (k u : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ))
    (κJ : ℕ → ℤ) (κI : ℕ → ℕ → ℕ → ℤ)
    (hchartJ : (z, τ) ∈ modularPhiChartDomain MJ u 0 κJ)
    (hchartI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range m,
      (hermiteArgument m i j z τ, hermiteTau n m k τ) ∈
        modularPhiChartDomain MI (hermiteNumIndex n u i) (hermiteDenIndex MJ n i j) (κI i j)) :
    modularPhiChartNumerator MJ u 0 κJ z τ *
        (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m,
          modularPhiChartDenominator MI (hermiteNumIndex n u i) (hermiteDenIndex MJ n i j)
            (κI i j) (hermiteArgument m i j z τ) (hermiteTau n m k τ)) =
      modularPhiChartDenominator MJ u 0 κJ z τ *
        (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m,
          modularPhiChartNumerator MI (hermiteNumIndex n u i) (hermiteDenIndex MJ n i j)
            (κI i j) (hermiteArgument m i j z τ) (hermiteTau n m k τ)) := by
  let r : Fin n × Fin m → ℤ := fun t => hermiteNumIndex n u t.1
  let s : Fin n × Fin m → ℤ := fun t => hermiteDenIndex MJ n t.1 t.2
  let T : ℂ → ℂ := hermiteTau n m k
  let Z : Fin n × Fin m → ℂ → ℂ → ℂ := fun t => hermiteArgument m t.1 t.2
  have hmap : ∀ t p, AnalyticAt ℂ (fun q : ℂ × ℂ => (Z t q.1 q.2, T q.2)) p := by
    intro t p
    dsimp only [Z, T, hermiteArgument, hermiteTau]
    exact (((analyticAt_fst.add (analyticAt_const.mul analyticAt_snd)).add
      analyticAt_const).div_const (c := (m : ℂ))).prod
        (((analyticAt_const.mul analyticAt_snd).add analyticAt_const).div_const (c := (m : ℂ)))
  have hslice : ∀ t z τ, Tendsto (fun w => Z t w τ) (𝓝[≠] z) (𝓝[≠] (Z t z τ)) := by
    intro t z τ
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    apply ContinuousWithinAt.tendsto_nhdsWithin
      (show ContinuousAt (fun w => Z t w τ) z by dsimp only [Z, hermiteArgument]; fun_prop).continuousWithinAt
    intro w hw heq
    apply hw
    dsimp only [Z, hermiteArgument] at heq
    exact add_right_cancel (add_right_cancel ((div_left_inj' hm0).mp heq))
  have hupper : ∀ z τ : ℂ, 0 < τ.im →
      (fun w => modularPhi MJ u 0 w τ) =ᶠ[𝓝[≠] z]
        (fun w => ∏ t, modularPhi MI (r t) (s t) (Z t w τ) (T τ)) := by
    intro z τ hτ
    simpa only [r, s, Z, T, hermiteProduct, Fintype.prod_prod_type, ← Fin.prod_univ_eq_prod_range] using
      hermitePhi_upper_germ MI MJ n m k u z τ hn hm hI hJ hH hτ
  have hc := DistributionHermiteAux.product_chart_cross_mul_of_upper MJ MI hJ hI u 0 r s T Z
    hmap hslice (hermite_domain MI MJ n m k · hn hm hH) hupper κJ
    (fun t => κI t.1 t.2) z τ hchartJ
    (fun t => hchartI t.1 (Finset.mem_range.mpr t.1.isLt) t.2 (Finset.mem_range.mpr t.2.isLt))
  simpa only [r, s, Z, T, Fintype.prod_prod_type, ← Fin.prod_univ_eq_prod_range] using hc

/-- [RW-rec, pp. 18--19, Lem. 10]; [RW26, p. 2, (1)]; [RW26, p. 6].
The germ on the common slit domain, by continuation along compatible
analytic charts. -/
theorem hermitePhi_germ (MI MJ : SL(2, ℤ)) (n m : ℕ) (k u : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ))
    (hτ : τ ∈ modularPhiDomain MJ) :
    (fun w => modularPhi MJ u 0 w τ) =ᶠ[𝓝[≠] z]
      (fun w => hermiteProduct MI MJ n m k u w τ) := by
  let r : Fin n × Fin m → ℤ := fun t => hermiteNumIndex n u t.1
  let s : Fin n × Fin m → ℤ := fun t => hermiteDenIndex MJ n t.1 t.2
  let T : ℂ → ℂ := hermiteTau n m k
  let Z : Fin n × Fin m → ℂ → ℂ → ℂ := fun t => hermiteArgument m t.1 t.2
  have hmap : ∀ t p, AnalyticAt ℂ (fun q : ℂ × ℂ => (Z t q.1 q.2, T q.2)) p := by
    intro t p
    dsimp only [Z, T, hermiteArgument, hermiteTau]
    exact (((analyticAt_fst.add (analyticAt_const.mul analyticAt_snd)).add
      analyticAt_const).div_const (c := (m : ℂ))).prod
        (((analyticAt_const.mul analyticAt_snd).add analyticAt_const).div_const (c := (m : ℂ)))
  have hslice : ∀ t z τ, Tendsto (fun w => Z t w τ) (𝓝[≠] z) (𝓝[≠] (Z t z τ)) := by
    intro t z τ
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    apply ContinuousWithinAt.tendsto_nhdsWithin
      (show ContinuousAt (fun w => Z t w τ) z by dsimp only [Z, hermiteArgument]; fun_prop).continuousWithinAt
    intro w hw heq
    apply hw
    dsimp only [Z, hermiteArgument] at heq
    exact add_right_cancel (add_right_cancel ((div_left_inj' hm0).mp heq))
  have hupper : ∀ z τ : ℂ, 0 < τ.im →
      (fun w => modularPhi MJ u 0 w τ) =ᶠ[𝓝[≠] z]
        (fun w => ∏ t, modularPhi MI (r t) (s t) (Z t w τ) (T τ)) := by
    intro z τ hτ
    simpa only [r, s, Z, T, hermiteProduct, Fintype.prod_prod_type, ← Fin.prod_univ_eq_prod_range] using
      hermitePhi_upper_germ MI MJ n m k u z τ hn hm hI hJ hH hτ
  have hg := DistributionHermiteAux.product_germ_of_upper MJ MI hJ hI u 0 r s T Z
    hmap hslice (hermite_domain MI MJ n m k · hn hm hH) hupper z τ hτ
  simpa only [r, s, Z, T, hermiteProduct, Fintype.prod_prod_type, ← Fin.prod_univ_eq_prod_range] using hg

/-- [RW-rec, Appendix A, p. 18]; [RW26, p. 6].
Point equality uses regularity at the centers. -/
theorem hermitePhi_value (MI MJ : SL(2, ℤ)) (n m : ℕ) (k u : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ))
    (hcenterJ : (z, τ) ∈ modularPhiHolomorphicDomain MJ u 0)
    (hcenterI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range m,
      (hermiteArgument m i j z τ, hermiteTau n m k τ) ∈
        modularPhiHolomorphicDomain MI (hermiteNumIndex n u i) (hermiteDenIndex MJ n i j)) :
    modularPhi MJ u 0 z τ = hermiteProduct MI MJ n m k u z τ := by
  have hemb : AnalyticAt ℂ (fun w : ℂ => (w, τ)) z := analyticAt_id.prod analyticAt_const
  have hcJ : ContinuousAt (fun w => modularPhi MJ u 0 w τ) z :=
    (((modularPhi_joint_analytic_no_poles MJ hJ u 0) (z, τ) hcenterJ).comp
      (x := z) (f := fun w : ℂ => (w, τ)) hemb).continuousAt
  have hprod : AnalyticAt ℂ (fun w => hermiteProduct MI MJ n m k u w τ) z := by
    unfold hermiteProduct
    apply Finset.analyticAt_fun_prod
    intro i hi
    apply Finset.analyticAt_fun_prod
    intro j hj
    have harg : AnalyticAt ℂ (fun w : ℂ =>
        (hermiteArgument m i j w τ, hermiteTau n m k τ)) z := by
      dsimp only [hermiteArgument, hermiteTau]
      fun_prop
    exact ((modularPhi_joint_analytic_no_poles MI hI (hermiteNumIndex n u i)
      (hermiteDenIndex MJ n i j)) _ (hcenterI i hi j hj)).comp
        (x := z) (f := fun w : ℂ => (hermiteArgument m i j w τ, hermiteTau n m k τ)) harg
  exact ModularCocycleAux.eq_of_germ (z := z)
    (f := fun w => modularPhi MJ u 0 w τ) (g := fun w => hermiteProduct MI MJ n m k u w τ)
    hcJ hprod.continuousAt
    (hermitePhi_germ MI MJ n m k u z τ hn hm hI hJ hH hcenterJ.1)

/-- [RW-rec, Lem. 10] at (n, m, k) = (1, 2, 0); [RW26, p. 14, Prop. 9].
The doubling germ. -/
theorem hermitePhi_double (M : SL(2, ℤ)) (hM : 0 < M 1 0) (hc : 2 ∣ M 1 0)
    (u : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi (modularDouble M hc) u 0 (2 * w) (2 * τ)) =ᶠ[𝓝[≠] z]
      (fun w => modularPhi M u 0 w τ * modularPhi M u (M 1 0 / 2) (w + 1 / 2) τ) := by
  simpa only [zero_add] using (modularDistribution_germ M hM hc u 0 z τ hτ).symm

#print hermiteNumIndex
#print hermiteDenIndex
#print hermiteResidue
#print hermiteProduct
#check @modularPhi
#check @phiExtended
#check @modularPhi_joint_local_quotient
#check hermitePhi_germ

end SICLean.L5.DistributionHermite
