import SICLean.L5.OddPrimeValues
import SICLean.L5.LocalActualFourier
import SICLean.L5.OddPrimeCyclicAux
import Mathlib.GroupTheory.Torsion

set_option autoImplicit false

/-!
# [RW-rec, Thm. 4] before any global unit theorem

Sources: [RW-rec, p. 7] (the theorem starts after the two Fourier identities on pp.
6--7). Finite inputs include [RW26, p. 3, p. 18, (5)--(7), (36)]. Each use below
identifies its [RW-rec] proof location. Proof plan: realize a positive maximum
oscillation on a G[p]-coset, choose the explicit scaling element from two extremal
ratios, apply LocalLemmaOne.lemma1_i_adjacent_units to obtain a doubled oscillation,
then use lemma1_ii_cyclicProduct_one. There is no hypothesis of global integrality,
unit-valued E, good reduction, or unramifiedness. The finite maximum argument precedes
every assertion of unit-valuedness.
-/

noncomputable section
open scoped Classical BigOperators MatrixGroups

namespace SICLean.L5.OddPrimeCyclic

open L3 OddPrimeValues LocalFourierSetup

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- A finite real maximum written as a concrete set supremum, not as a chosen quantity assumed to
satisfy the maximum property. -/
def cosetDiameter {G : Type*} [AddCommGroup G] (p : ℕ) (w : G → ℝ) : ℝ :=
  sSup {d : ℝ | ∃ x y : G, p • (x - y) = 0 ∧ d = w x - w y}

/-- Difference of existing ordinary real valuations; [RW-rec]. -/
def ratioWeight (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (h t : PseudolatticeGroup P I) : ℝ :=
  weight P I v (t + h) - weight P I v t

/-- [RW-rec] explicit algebraic scaling: compare the valuations of R(a)^-1 and R(b)/E(h). No
divisible value group is assumed. -/
def scalingElement (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (h a b : PseudolatticeGroup P I) : Galois.Qbar :=
  if -(ratioWeight P I v h a) ≥ ratioWeight P I v h b - weight P I v h then
    (LocalLemmaOne.translationRatio (lift P I) h a)⁻¹
  else LocalLemmaOne.translationRatio (lift P I) h b / lift P I h

/-- Presentation transport, [RW-rec, Def. 1, p. 3]; [RW26, p. 2, (2)]. The same actual values, not
an extra finite-system solution, are transported to a matrix interface. -/
theorem exists_matrix_presentation (P : PeriodData K) (I : StablePseudolattice P) :
    ∃ M : SL(2, ℤ), ∃ hM : L4.SpecialValueAdmissible M,
      ∃ e : PseudolatticeGroup P I ≃+ L4.SpecialValueGroup M,
        ∀ x, lift P I x = FiniteAlgebraicTransport.value M hM (e x) := by
  let B := M72.chosenBasis P I
  have hB : PseudolatticePresentation P I B := M72.chosenBasis_spec P I
  let e := (M72.rowToK P I B hB).symm
  refine ⟨B.matrix, (M72.basis_parameters B hB.1).1, e, ?_⟩
  intro x
  apply Galois.embed.injective
  change Galois.embed (lift P I x) = Galois.embed
    (FiniteAlgebraicTransport.value B.matrix (M72.basis_parameters B hB.1).1 (e x))
  rw [embed_lift, FiniteAlgebraicTransport.embed_value]
  simpa only [e, AddEquiv.apply_symm_apply] using
    M72.value_rowToK P I B hB (e x)

/-- [RW-rec, Lemma 1, p. 5]: the equal-exponent d=1 decomposition needed to call the existing local
lemma is a conclusion. -/
theorem cyclic_primary_decomposition {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (hc : IsAddCyclic (AddCommGroup.primaryComponent G p))
    (hn : Nontrivial (AddCommGroup.primaryComponent G p)) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ C : AddSubgroup G,
      Nat.Coprime p (Nat.card C) ∧
      Nonempty ((FiniteCosetMoments.Point p s 1 × C) ≃+ G) := by
  exact OddPrimeCyclicAux.primary_decomposition p hc hn

/-- [RW-rec] finite oscillation includes the zero difference. Only finite real arithmetic, with no
analogue asserted in [RW26]. -/
theorem cosetDiameter_nonneg {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) (w : G → ℝ) : 0 ≤ cosetDiameter p w := by
  simpa only [sub_self, cosetDiameter] using
    (OddPrimeCyclicAux.diameter_attained p w).2 0 0 (by simp)

/-- [RW-rec] both attainment and the global bound on every coset. -/
theorem cosetDiameter_attained {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) (w : G → ℝ) :
    (∃ x y : G, p • (x - y) = 0 ∧ cosetDiameter p w = w x - w y) ∧
      ∀ x y : G, p • (x - y) = 0 → w x - w y ≤ cosetDiameter p w := by
  exact OddPrimeCyclicAux.diameter_attained p w

/-- [RW-rec]: choosing the displacement from a maximizing pair produces a nonzero p-torsion step
whose maximal ratio valuation is D. -/
theorem extreme_step (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (p : ℕ)
    (hD : 0 < cosetDiameter p (weight P I v)) :
    ∃ h a b : PseudolatticeGroup P I, h ≠ 0 ∧ p • h = 0 ∧
      ratioWeight P I v h b = cosetDiameter p (weight P I v) ∧
      (∀ t, ratioWeight P I v h a ≤ ratioWeight P I v h t) ∧
      (∀ t, ratioWeight P I v h t ≤ ratioWeight P I v h b) := by
  letI := (pseudolatticeGroup_finite_card P I).1
  obtain ⟨⟨x, y, hxy, hDxy⟩, hbound⟩ := cosetDiameter_attained p (weight P I v)
  let h := x - y
  have hne : h ≠ 0 := by
    intro hz
    have : x = y := sub_eq_zero.mp hz
    simp [this] at hDxy
    linarith
  obtain ⟨a, _, ha⟩ := Set.exists_min_image Set.univ
    (ratioWeight P I v h) (Set.finite_univ) Set.univ_nonempty
  refine ⟨h, a, y, hne, hxy, ?_, fun t => ha t (Set.mem_univ t), ?_⟩
  · simpa [ratioWeight, h] using hDxy.symm
  · intro t
    rw [show ratioWeight P I v h y = cosetDiameter p (weight P I v) by
      simpa [ratioWeight, h] using hDxy.symm]
    exact hbound (t + h) t (by simpa using hxy)

/-- [RW-rec]: w(-h)=-w(h) bounds twice the absolute shift value. The reflection input is [RW26, p.
3, (5)] finite identities. -/
theorem shift_value_bound (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (p : ℕ)
    (h : PseudolatticeGroup P I) (hh : p • h = 0) :
    2 * |weight P I v h| ≤ cosetDiameter p (weight P I v) := by
  letI := (pseudolatticeGroup_finite_card P I).1
  have hbound := (cosetDiameter_attained p (weight P I v)).2
  have hpair : p • (h - -h) = 0 := by simp [nsmul_sub, nsmul_add, hh]
  have hpair' : p • (-h - h) = 0 := by simp [nsmul_sub, nsmul_add, hh]
  have hpos := hbound h (-h) hpair
  have hneg := hbound (-h) h hpair'
  rw [weight_neg] at hpos hneg
  rcases le_total 0 (weight P I v h) with hw | hw
  · rw [abs_of_nonneg hw]
    linarith
  · rw [abs_of_nonpos hw]
    linarith

/-- [RW-rec]: all scaling inequalities and a unit value are outputs, not inputs of a local model.
The two alternatives are used separately and give the finite identities above. -/
theorem scaled_functions_integral (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (p : ℕ)
    (h a b : PseudolatticeGroup P I)
    (hD : 0 < cosetDiameter p (weight P I v)) (hh : p • h = 0)
    (hb : ratioWeight P I v h b = cosetDiameter p (weight P I v))
    (hmin : ∀ t, ratioWeight P I v h a ≤ ratioWeight P I v h t)
    (hmax : ∀ t, ratioWeight P I v h t ≤ ratioWeight P I v h b) :
    let z := scalingElement P I v h a b
    let R := LocalLemmaOne.translationRatio (lift P I) h
    z ≠ 0 ∧ 0 < v z ∧
      (cosetDiameter p (weight P I v) : WithTop ℝ) ≤ v (z * lift P I h) ∧
      Integral v (fun t => z * R t) ∧
      Integral v (fun t => z * lift P I h / R t) ∧
      ((∃ t, v (z * R t) = 0) ∨ (∃ t, v (z * lift P I h / R t) = 0)) := by
  dsimp only
  let A := ratioWeight P I v h a
  let B := ratioWeight P I v h b
  let W := weight P I v h
  let Z := max (-A) (B - W)
  let z := scalingElement P I v h a b
  have hR (t) : v (LocalLemmaOne.translationRatio (lift P I) h t) =
      (ratioWeight P I v h t : WithTop ℝ) := ratio_valuation P I v h t
  have hz : z ≠ 0 := by
    dsimp [z, scalingElement]
    split_ifs
    · exact inv_ne_zero (div_ne_zero (lift_ne_zero P I _) (lift_ne_zero P I _))
    · exact div_ne_zero (div_ne_zero (lift_ne_zero P I _) (lift_ne_zero P I _))
        (lift_ne_zero P I _)
  have hvz : v z = (Z : WithTop ℝ) := by
    change v (if -A ≥ B - W then
      (LocalLemmaOne.translationRatio (lift P I) h a)⁻¹
      else LocalLemmaOne.translationRatio (lift P I) h b / lift P I h) = (Z : WithTop ℝ)
    by_cases hc : -A ≥ B - W
    · rw [if_pos hc, show Z = -A from max_eq_left hc]
      exact OddPrimeCyclicAux.map_inv_coe v (hR a)
    · rw [if_neg hc, show Z = B - W from max_eq_right (le_of_not_ge hc)]
      exact OddPrimeCyclicAux.map_div_coe v (hR b) (coe_weight P I v h).symm
  have hZE : v (z * lift P I h) = ((Z + W : ℝ) : WithTop ℝ) :=
    OddPrimeCyclicAux.map_mul_coe v hvz (coe_weight P I v h).symm
  have hscaled (t) : v (z * LocalLemmaOne.translationRatio (lift P I) h t) =
      ((Z + ratioWeight P I v h t : ℝ) : WithTop ℝ) :=
    OddPrimeCyclicAux.map_mul_coe v hvz (hR t)
  have hiscaled (t) : v (z * lift P I h /
      LocalLemmaOne.translationRatio (lift P I) h t) =
      ((Z + W - ratioWeight P I v h t : ℝ) : WithTop ℝ) :=
    OddPrimeCyclicAux.map_div_coe v hZE (hR t)
  have hZA : -A ≤ Z := le_max_left _ _
  have hZB : B - W ≤ Z := le_max_right _ _
  have hW := shift_value_bound P I v p h hh
  have habs : W ≤ |W| := le_abs_self W
  have hB : B = cosetDiameter p (weight P I v) := hb
  have hZpos : 0 < Z := by dsimp [W] at habs; linarith
  refine ⟨hz, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvz]
    exact WithTop.coe_lt_coe.mpr hZpos
  · rw [hZE]
    exact WithTop.coe_le_coe.mpr (by linarith)
  · intro t
    rw [hscaled]
    apply WithTop.coe_le_coe.mpr
    have := hmin t
    change A ≤ _ at this
    linarith
  · intro t
    rw [hiscaled]
    apply WithTop.coe_le_coe.mpr
    have := hmax t
    change _ ≤ B at this
    linarith
  · by_cases hc : -A ≥ B - W
    · left
      refine ⟨a, ?_⟩
      rw [hscaled]
      simp only [Z, max_eq_left hc, A, neg_add_cancel, WithTop.coe_zero]
    · right
      refine ⟨b, ?_⟩
      rw [hiscaled]
      have heq : Z + W - ratioWeight P I v h b = 0 := by
        rw [show Z = B - W from max_eq_right (le_of_not_ge hc)]
        change B - W + W - B = 0
        ring
      rw [heq, WithTop.coe_zero]

/-- [RW-rec, (15)]. Transport of LocalActualFourier.actual_scaled_ratio_fouriers_integral through
any actual matrix presentation. [RW26, p. 18, (36)]; no unscaled integrality assumption. -/
theorem scaled_fourier_pair (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (z : Galois.Qbar)
    (h : PseudolatticeGroup P I) (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (e : PseudolatticeGroup P I ≃+ L4.SpecialValueGroup M)
    (he : ∀ x, lift P I x = FiniteAlgebraicTransport.value M hM (e x))
    (hz : 0 ≤ v z) (hzE : 0 ≤ v (z * lift P I h))
    (hR : Integral v (fun t => z * LocalLemmaOne.translationRatio (lift P I) h t))
    (hiR : Integral v (fun t =>
      z * lift P I h / LocalLemmaOne.translationRatio (lift P I) h t)) :
    Integral v (FiniteAlgebraicTransport.fourier M hM
      (fun t => z * FiniteAlgebraicTransport.ratio M hM (e h) t)) ∧
    Integral v (FiniteAlgebraicTransport.fourier M hM
      (fun t => z * FiniteAlgebraicTransport.value M hM (e h) /
        FiniteAlgebraicTransport.ratio M hM (e h) t)) := by
  have hratio (t) : LocalLemmaOne.translationRatio (lift P I) h t =
      FiniteAlgebraicTransport.ratio M hM (e h) (e t) := by
    simp only [LocalLemmaOne.translationRatio, FiniteAlgebraicTransport.ratio, he, map_add]
  apply LocalActualFourier.actual_scaled_ratio_fouriers_integral M hM v z (e h) hz
    (by simpa only [he] using hzE)
  · intro t
    simpa only [hratio, e.apply_symm_apply] using hR (e.symm t)
  · intro t
    simpa only [hratio, he, e.apply_symm_apply] using hiR (e.symm t)

/-- [RW-rec, Thm. 4]: the strict-majority/adjacent-point contradiction proves constancy before
asserting any E-unit property. Uses LocalLemmaOne(i), not an extra moment hypothesis. -/
theorem weight_constant_on_p_cosets (P : PeriodData K) (I : StablePseudolattice P)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hc : IsAddCyclic (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (hn : Nontrivial (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (t h : PseudolatticeGroup P I) (hh : p • h = 0) :
    weight P I v (t + h) = weight P I v t := by
  letI := (pseudolatticeGroup_finite_card P I).1
  letI := Fintype.ofFinite (PseudolatticeGroup P I)
  obtain ⟨s, hs, C, hC, ⟨dec⟩⟩ := cyclic_primary_decomposition p hc hn
  letI := Fintype.ofFinite C
  have hC' : Nat.Coprime p (Fintype.card C) := by simpa only [Nat.card_eq_fintype_card] using hC
  obtain ⟨M, hM, e, he⟩ := exists_matrix_presentation P I
  letI := L4.specialValueGroup_finite M hM
  letI := Fintype.ofFinite (L4.SpecialValueGroup M)
  let B := fun x y => FiniteAlgebraicTransport.pairing M hM (e x) (e y)
  let r := FiniteAlgebraicTransport.sqrtOrder M hM
  have hB : IsBicharacter B := OddPrimeCyclicAux.bicharacter_comp e _
    (LocalActualFourier.actual_isBicharacter M hM)
  have hnd : Nondegenerate B := OddPrimeCyclicAux.nondegenerate_comp e _
    (LocalActualFourier.actual_nondegenerate M hM)
  have hr : r ^ 2 = (Fintype.card (PseudolatticeGroup P I) : Galois.Qbar) := by
    rw [Fintype.card_congr e.toEquiv]
    exact LocalActualFourier.actual_normalization_sq M hM
  have hratio (h t) : LocalLemmaOne.translationRatio (lift P I) h t =
      FiniteAlgebraicTransport.ratio M hM (e h) (e t) := by
    simp only [LocalLemmaOne.translationRatio, FiniteAlgebraicTransport.ratio, he, map_add]
  have hDn : ¬ 0 < cosetDiameter p (weight P I v) := by
    intro hD
    obtain ⟨k, a, b, hk, hpk, hb, hmin, hmax⟩ := extreme_step P I v p hD
    let z := scalingElement P I v k a b
    let R := LocalLemmaOne.translationRatio (lift P I) k
    obtain ⟨hz, hzpos, hzD, hR, hiR, hu⟩ :=
      scaled_functions_integral P I v p k a b hD hpk hb hmin hmax
    obtain ⟨hFR, hFiR⟩ := scaled_fourier_pair P I v z k M hM e he
      hzpos.le ((WithTop.coe_le_coe.mpr hD.le).trans hzD) hR hiR
    have hFR' : Integral v (LocalFourierSetup.fourier B r (fun t => z * R t)) :=
      OddPrimeCyclicAux.actual_fourier_transfer M hM e v _ _
        (fun t => by simp only [R, hratio]) hFR
    have hFiR' : Integral v (LocalFourierSetup.fourier B r
        (fun t => z * lift P I k / R t)) :=
      OddPrimeCyclicAux.actual_fourier_transfer M hM e v _ _
        (fun t => by simp only [R, hratio, he]) hFiR
    let Z := ValuationSupport.realValue v z
    have hZ : v z = (Z : WithTop ℝ) := (ValuationSupport.coe_realValue v hz).symm
    have hZE : v (z * lift P I k) = ((Z + weight P I v k : ℝ) : WithTop ℝ) :=
      OddPrimeCyclicAux.map_mul_coe v hZ (coe_weight P I v k).symm
    have hval (x) : v (z * R x) =
        ((Z + ratioWeight P I v k x : ℝ) : WithTop ℝ) :=
      OddPrimeCyclicAux.map_mul_coe v hZ (ratio_valuation P I v k x)
    have hival (x) : v (z * lift P I k / R x) =
        ((Z + weight P I v k - ratioWeight P I v k x : ℝ) : WithTop ℝ) :=
      OddPrimeCyclicAux.map_div_coe v hZE (ratio_valuation P I v k x)
    have hDbound := (cosetDiameter_attained p (weight P I v)).2
    have hZDbound : cosetDiameter p (weight P I v) ≤ Z + weight P I v k := by
      rw [hZE] at hzD
      exact WithTop.coe_le_coe.mp hzD
    by_cases hiunit : ∃ x, v (z * lift P I k / R x) = 0
    · obtain ⟨y, hy⟩ := hiunit
      have hDZE : Z + weight P I v k = cosetDiameter p (weight P I v) := by
        rw [hival] at hy
        have hy' : Z + weight P I v k - ratioWeight P I v k y = 0 :=
          WithTop.coe_eq_coe.mp hy
        have := hmax y
        linarith
      obtain ⟨u, _, hu, huh⟩ := LocalLemmaOne.lemma1_i_adjacent_units v hp hodd hs hC'
        B hB hnd r hr _ hiR hFiR' dec y y k (by simp) hy hk hpk
      rw [hival] at hu huh
      have hu' : Z + weight P I v k - ratioWeight P I v k u = 0 :=
        WithTop.coe_eq_coe.mp hu
      have huh' : Z + weight P I v k - ratioWeight P I v k (u + k) = 0 :=
        WithTop.coe_eq_coe.mp huh
      have hbound := hDbound (u + k + k) u (by simp [nsmul_sub, nsmul_add, hpk])
      dsimp [ratioWeight] at hu' huh'
      linarith
    · obtain ⟨y, hy⟩ := hu.resolve_right hiunit
      have hgap : 0 < Z + weight P I v k - cosetDiameter p (weight P I v) := by
        have hge := hiR b
        rw [hival, hb] at hge
        have hge' : 0 ≤ Z + weight P I v k - cosetDiameter p (weight P I v) :=
          WithTop.coe_le_coe.mp hge
        apply lt_of_le_of_ne hge'
        intro hz0
        apply hiunit
        refine ⟨b, ?_⟩
        rw [hival, hb, ← hz0, WithTop.coe_zero]
      have hw := shift_value_bound P I v p k hpk
      have hw' := le_abs_self (weight P I v k)
      obtain ⟨u, _, hu, huh⟩ := LocalLemmaOne.lemma1_i_adjacent_units v hp hodd hs hC'
        B hB hnd r hr _ hR hFR' dec y y k (by simp) hy hk hpk
      rw [hval] at hu huh
      have hu' : Z + ratioWeight P I v k u = 0 := WithTop.coe_eq_coe.mp hu
      have huh' : Z + ratioWeight P I v k (u + k) = 0 := WithTop.coe_eq_coe.mp huh
      have hbound := hDbound u (u + k + k) (by simp [nsmul_sub, nsmul_add, hpk])
      dsimp [ratioWeight] at hu' huh'
      linarith
  have hDle := le_of_not_gt hDn
  have hbound := (cosetDiameter_attained p (weight P I v)).2
  have h₁ := hbound (t + h) t (by simpa using hh)
  have h₂ := hbound t (t + h) (by simp [nsmul_sub, nsmul_add, hh])
  linarith

/-- [RW-rec, Thm. 4]: every order-p ratio is a local unit. No assumption that E itself is
unit-valued. -/
theorem translation_unit (P : PeriodData K) (I : StablePseudolattice P)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hc : IsAddCyclic (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (hn : Nontrivial (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (h t : PseudolatticeGroup P I) (hh : addOrderOf h = p) :
    v (LocalLemmaOne.translationRatio (lift P I) h t) = 0 := by
  have hph : p • h = 0 := by simpa only [hh] using addOrderOf_nsmul_eq_zero h
  rw [LocalLemmaOne.translationRatio, ratio_valuation,
    weight_constant_on_p_cosets P I p hodd v hp hc hn t h hph, sub_self, WithTop.coe_zero]

/-- [RW-rec, Thm. 4]: Lemma1(ii) and the actual telescoping p-cycle product give residue one. Unit
equality is repeated so the totalized reduction map cannot conceal a nonintegral input. -/
theorem translation_reduce_one (P : PeriodData K) (I : StablePseudolattice P)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hc : IsAddCyclic (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (hn : Nontrivial (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (h t : PseudolatticeGroup P I) (hh : addOrderOf h = p) :
    v (LocalLemmaOne.translationRatio (lift P I) h t) = 0 ∧
      reduce v (LocalLemmaOne.translationRatio (lift P I) h t) = 1 := by
  letI := (pseudolatticeGroup_finite_card P I).1
  letI := Fintype.ofFinite (PseudolatticeGroup P I)
  obtain ⟨s, hs, C, hC, ⟨dec⟩⟩ := cyclic_primary_decomposition p hc hn
  letI := Fintype.ofFinite C
  have hC' : Nat.Coprime p (Fintype.card C) := by simpa only [Nat.card_eq_fintype_card] using hC
  obtain ⟨M, hM, e, he⟩ := exists_matrix_presentation P I
  letI := L4.specialValueGroup_finite M hM
  letI := Fintype.ofFinite (L4.SpecialValueGroup M)
  let B := fun x y => FiniteAlgebraicTransport.pairing M hM (e x) (e y)
  let r := FiniteAlgebraicTransport.sqrtOrder M hM
  let R := LocalLemmaOne.translationRatio (lift P I) h
  have hB : IsBicharacter B := OddPrimeCyclicAux.bicharacter_comp e _
    (LocalActualFourier.actual_isBicharacter M hM)
  have hnd : Nondegenerate B := OddPrimeCyclicAux.nondegenerate_comp e _
    (LocalActualFourier.actual_nondegenerate M hM)
  have hr : r ^ 2 = (Fintype.card (PseudolatticeGroup P I) : Galois.Qbar) := by
    rw [Fintype.card_congr e.toEquiv]
    exact LocalActualFourier.actual_normalization_sq M hM
  have hratio (x) : R x = FiniteAlgebraicTransport.ratio M hM (e h) (e x) := by
    simp only [R, LocalLemmaOne.translationRatio, FiniteAlgebraicTransport.ratio, he, map_add]
  have hu : UnitValued v R := fun x => translation_unit P I p hodd v hp hc hn h x hh
  have hph : p • h = 0 := by simpa only [hh] using addOrderOf_nsmul_eq_zero h
  have hw := weight_constant_on_p_cosets P I p hodd v hp hc hn 0 h hph
  simp only [zero_add] at hw
  have hE : v (lift P I h) = 0 := by
    rw [← coe_weight, hw, coe_weight, zero_value_valuation]
  have hR : Integral v (fun x => (1 : Galois.Qbar) * R x) := by
    intro x
    simp only [one_mul, hu x, le_refl]
  have hiR : Integral v (fun x => (1 : Galois.Qbar) * lift P I h / R x) := by
    intro x
    simp [hE, hu x]
  obtain ⟨hFR, hFiR⟩ := scaled_fourier_pair P I v 1 h M hM e he (by simp)
    (by simp [hE]) hR hiR
  have hFR' : Integral v (LocalFourierSetup.fourier B r R) :=
    OddPrimeCyclicAux.actual_fourier_transfer M hM e v _ _
      (fun x => by simp only [one_mul, hratio]) hFR
  have hFiR' : Integral v (LocalFourierSetup.fourier B r (fun x => lift P I h / R x)) :=
    OddPrimeCyclicAux.actual_fourier_transfer M hM e v _ _
      (fun x => by simp only [one_mul, hratio, he]) hFiR
  refine ⟨hu t, ?_⟩
  exact LocalLemmaOne.lemma1_ii_cyclicProduct_one v hp hodd hs hC' B hB hnd r hr
    R hFR' dec hu (OddPrimeCyclicAux.integral_fourier_inv_of_div v B r _ R hE hFiR')
    t h hph (OddPrimeCyclicAux.translationRatio_product (lift P I) (lift_ne_zero P I) h t p hph)

/-- [RW-rec, Thm. 4]: includes h=0 using the already known e-unit. -/
theorem torsion_value_unit (P : PeriodData K) (I : StablePseudolattice P)
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hc : IsAddCyclic (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (hn : Nontrivial (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (h : PseudolatticeGroup P I) (hh : p • h = 0) : v (lift P I h) = 0 := by
  have hw := weight_constant_on_p_cosets P I p hodd v hp hc hn 0 h hh
  simp only [zero_add] at hw
  rw [← coe_weight, hw, coe_weight, zero_value_valuation]

#check @LocalLemmaOne.lemma1_i_adjacent_units
#check @LocalLemmaOne.lemma1_ii_cyclicProduct_one
#check @LocalActualFourier.actual_scaled_ratio_fouriers_integral
#check @FiniteTranslationRatio.ratio_cyclic_product
#check @AddCommGroup.primaryComponent
#check @translation_reduce_one
#print cosetDiameter
#print scalingElement

end SICLean.L5.OddPrimeCyclic
