import SICLean.L5.LocalCosetDegree
import SICLean.L5.LocalLemmaOneAux

set_option autoImplicit false

/-!
# [RW-rec, Lemma 1(i)--(iii)]

Downstream statements from [RW-rec, p. 5]; the argument is on pp. 5--6. Theorem 4
(p. 7) consumes (i)/(ii) on scaled translation quotients. Theorem 5 (p. 9)
consumes Theorem 4, not an extra version of Lemma 1. Theorem 7 (p. 12) consumes (iii)
first on E and then on its translation quotient. It needs the same theorem on one
selected coset, with arbitrary affine coordinates, in both calls. Every theorem requires
the full equal-exponent primary decomposition `G ≃ (Z/p^s)^d × C`, `p ∤ |C|`, `s ≥ 1`,
and odd prime p. No theorem here claims the uniform choice across all cosets of Theorem
7.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalLemmaOne

open LocalFourierSetup FiniteCosetMoments

variable {p s : ℕ} [Fact p.Prime]
variable {L G C : Type*} [Field L] [CharZero L]
variable [AddCommGroup G] [Fintype G] [AddCommGroup C] [Fintype C]
variable (v : AddValuation L (WithTop ℝ)) (hp : v (p : L) = 1)
variable (hodd : p ≠ 2) (hs : 1 ≤ s) (hC : Nat.Coprime p (Fintype.card C))
variable (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B)
variable (r : L) (hr : r ^ 2 = (Fintype.card G : L))
variable (f : G → L) (hf : Integral v f) (hF : Integral v (fourier B r f))

include hp hodd hs hC hB hnd hr hf hF

/-- [RW-rec, Lemma 1(i)]; interpolation/root count. This is a strict majority, not merely half the
points. -/
theorem lemma1_i_line (e : (Point p s 1 × C) ≃+ G) (x : G)
    (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) :
    (∀ t, lineRestriction e v f x a t = 0) ∨
      p < 2 * Nat.card {t : ZMod p // lineRestriction e v f x a t ≠ 0} := by
  let : CharP (Residue v) p := residue_charP v hp
  rcases FiniteInterpolation.eq_zero_or_support_large_of_lowMoments p (Residue v)
    (lineRestriction e v f x a)
    (LocalCosetDegree.line_lowMoments v hp hodd hs hC B hB hnd r hr f hf hF e x a)
      with hz | hlarge
  · exact Or.inl (fun t => congrFun hz t)
  · exact Or.inr hlarge

/-- [RW-rec, Lemma 1(i)] in the actual `G[p]`-coset. -/
theorem lemma1_i_coset (e : (Point p s 1 × C) ≃+ G) (x : G) :
    (∀ y, p • (y - x) = 0 → reduce v (f y) = 0) ∨
      p < 2 * Nat.card {y : G // p • (y - x) = 0 ∧ reduce v (f y) ≠ 0} := by
  classical
  let a := AffineEquiv.refl (ZMod p) (Fin 1 → ZMod p)
  let E := LocalLemmaOneAux.lineChartEquiv hs hC e x a
  rcases lemma1_i_line v hp hodd hs hC B hB hnd r hr f hf hF e x a with hz | hlarge
  · left
    intro y hy
    obtain ⟨t, ht⟩ := E.surjective ⟨y, hy⟩
    have hvalue : cosetChart e x a (fun _ => t) = y := congrArg Subtype.val ht
    simpa only [lineRestriction, hvalue] using hz t
  · right
    let k : {t : ZMod p // lineRestriction e v f x a t ≠ 0} →
        {y : G // p • (y - x) = 0 ∧ reduce v (f y) ≠ 0} :=
      fun t => ⟨(E t.val).val, (E t.val).property, t.property⟩
    have hk : Function.Injective k := by
      intro t u htu
      apply Subtype.ext
      apply E.injective
      apply Subtype.ext
      change (k t).val = (k u).val
      exact congrArg Subtype.val htu
    have hcard := Nat.card_le_card_of_injective k hk
    omega

/-- [RW-rec]: a specified unit value rules out the zero alternative. -/
theorem lemma1_i_support_at_unit (e : (Point p s 1 × C) ≃+ G) (x y : G)
    (hy : p • (y - x) = 0) (hunit : v (f y) = 0) :
    p < 2 * Nat.card {t : G // p • (t - x) = 0 ∧ v (f t) = 0} := by
  classical
  rcases lemma1_i_coset v hp hodd hs hC B hB hnd r hr f hf hF e x with hz | hlarge
  · exact False.elim (((reduce_ne_zero_iff v (f y) (hf y)).2 hunit) (hz y hy))
  · have hcard : Nat.card {t : G // p • (t - x) = 0 ∧ reduce v (f t) ≠ 0} =
        Nat.card {t : G // p • (t - x) = 0 ∧ v (f t) = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun t : G =>
        and_congr_right (fun _ => reduce_ne_zero_iff v (f t) (hf t))))
    rwa [hcard] at hlarge

/-- [RW-rec]: a strict majority contains neighboring unit values for every nonzero p-torsion step.
This is the counting statement for Theorem 4. -/
theorem lemma1_i_adjacent_units (e : (Point p s 1 × C) ≃+ G)
    (x y h : G) (hy : p • (y - x) = 0) (hunit : v (f y) = 0)
    (hh : h ≠ 0) (hph : p • h = 0) :
    ∃ t : G, p • (t - x) = 0 ∧ v (f t) = 0 ∧ v (f (t + h)) = 0 := by
  exact LocalLemmaOneAux.exists_adjacent_of_strict_majority p x h
    (fun t => v (f t) = 0) hph
    (by simpa only [pow_one] using
      LocalFourierRestriction.card_pTorsion_coset hs hC e x)
    (lemma1_i_support_at_unit v hp hodd hs hC B hB hnd r hr f hf hF e x y hy hunit)

omit hf in
/-- [RW-rec, Lemma 1(ii)]; proof: nonzero constant residue. -/
theorem lemma1_ii_line (e : (Point p s 1 × C) ≃+ G) (hu : UnitValued v f)
    (hFi : Integral v (fourier B r (fun t => (f t)⁻¹))) (x : G)
    (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) :
    ∃ c : Residue v, c ≠ 0 ∧ ∀ t, lineRestriction e v f x a t = c := by
  let : CharP (Residue v) p := residue_charP v hp
  have hf' := integral_of_unitValued v f hu
  exact FiniteInterpolation.eq_const_of_lowMoments_and_reciprocal p (Residue v)
    (lineRestriction e v f x a)
    (fun t => (reduce_ne_zero_iff v _ (hf' _)).2 (hu _))
    (LocalCosetDegree.line_lowMoments v hp hodd hs hC B hB hnd r hr f hf' hF e x a)
    (LocalCosetDegree.line_inverse_lowMoments v hp hodd hs hC B hB hnd r hr f e hu hFi x a)

omit hf in
/-- [RW-rec, Lemma 1(ii)] without a coordinate choice. -/
theorem lemma1_ii_coset (e : (Point p s 1 × C) ≃+ G) (hu : UnitValued v f)
    (hFi : Integral v (fourier B r (fun t => (f t)⁻¹))) (x : G) :
    ∃ c : Residue v, c ≠ 0 ∧ ∀ y, p • (y - x) = 0 → reduce v (f y) = c := by
  let a := AffineEquiv.refl (ZMod p) (Fin 1 → ZMod p)
  let E := LocalLemmaOneAux.lineChartEquiv hs hC e x a
  obtain ⟨c, hc, hconstant⟩ := lemma1_ii_line v hp hodd hs hC B hB hnd r hr f hF e hu hFi x a
  refine ⟨c, hc, ?_⟩
  intro y hy
  obtain ⟨t, ht⟩ := E.surjective ⟨y, hy⟩
  have hvalue : cosetChart e x a (fun _ => t) = y := congrArg Subtype.val ht
  simpa only [lineRestriction, hvalue] using hconstant t

omit hf in
/-- [RW-rec]: pointwise congruence along every p-torsion translation. -/
theorem lemma1_ii_translation (e : (Point p s 1 × C) ≃+ G) (hu : UnitValued v f)
    (hFi : Integral v (fourier B r (fun t => (f t)⁻¹))) (x h : G) (hh : p • h = 0) :
    reduce v (f (x + h)) = reduce v (f x) := by
  obtain ⟨c, _, hc⟩ := lemma1_ii_coset v hp hodd hs hC B hB hnd r hr f hF e hu hFi x
  exact (hc (x + h) (by simpa using hh)).trans (hc x (by simp)).symm

omit hf in
/-- [RW-rec]: constant residue plus the actual cyclic product forces residue one; telescoping the
translation quotient is already proved. -/
theorem lemma1_ii_cyclicProduct_one (e : (Point p s 1 × C) ≃+ G)
    (hu : UnitValued v f) (hFi : Integral v (fourier B r (fun t => (f t)⁻¹)))
    (x h : G) (hh : p • h = 0)
    (hprod : (∏ j : Fin p, f (x + j.val • h)) = 1) : reduce v (f x) = 1 := by
  classical
  let : CharP (Residue v) p := residue_charP v hp
  have hf' := integral_of_unitValued v f hu
  let g : Fin p → integers v := fun j => ⟨f (x + j.val • h), hf' _⟩
  have hgprod : (∏ j : Fin p, g j) = 1 := by
    apply Subtype.ext
    change (integers v).subtype (∏ j : Fin p, g j) = 1
    rw [map_prod]
    exact hprod
  have hresprod : (∏ j : Fin p, reduce v (f (x + j.val • h))) = 1 := by
    calc
      _ = ∏ j : Fin p, IsLocalRing.residue (integers v) (g j) := by
        apply Finset.prod_congr rfl
        intro j _
        exact reduce_eq_residue v _ (hf' _)
      _ = IsLocalRing.residue (integers v) (∏ j : Fin p, g j) := (map_prod _ _ _).symm
      _ = 1 := by rw [hgprod, map_one]
  have hconstant (j : Fin p) : reduce v (f (x + j.val • h)) = reduce v (f x) := by
    apply lemma1_ii_translation v hp hodd hs hC B hB hnd r hr f hF e hu hFi
    rw [smul_comm p j.val h, hh, smul_zero]
  have hpower : reduce v (f x) ^ p = 1 := by
    simpa only [hconstant, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hresprod
  apply frobenius_inj (Residue v) p
  change reduce v (f x) ^ p = (1 : Residue v) ^ p
  simpa only [one_pow] using hpower

omit hf in
/-- [RW-rec, Lemma 1(iii)]. The factors and their factorization concern only this selected coset. -/
theorem lemma1_iii_factors (e : (Point p s 2 × C) ≃+ G) (hu : UnitValued v f)
    (hFi : Integral v (fourier B r (fun t => (f t)⁻¹))) (x : G)
    (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p))
    (A D : ZMod p → Residue v)
    (hfactor : ∀ u, planeRestriction e v f x a u = A u.1 * D u.2) :
    (∃ c : Residue v, c ≠ 0 ∧ ∀ t, A t = c) ∨
      (∃ c : Residue v, c ≠ 0 ∧ ∀ t, D t = c) := by
  let : CharP (Residue v) p := residue_charP v hp
  have hf' := integral_of_unitValued v f hu
  exact FiniteInterpolation.one_factor_constant_of_factorization p (Residue v)
    (planeRestriction e v f x a) A D hfactor
    (fun u => (reduce_ne_zero_iff v _ (hf' _)).2 (hu _))
    (LocalCosetDegree.plane_lowMoments v hp hodd hs hC B hB hnd r hr f hf' hF e x a)
    (LocalCosetDegree.plane_inverse_lowMoments v hp hodd hs hC B hB hnd r hr f e hu hFi x a)

omit hf in
/-- [RW-rec]: the first Theorem 7 call leaves at least one coordinate direction invariant on this
coset. The choice here may still depend on the coset. -/
theorem lemma1_iii_coordinate_invariance (e : (Point p s 2 × C) ≃+ G)
    (hu : UnitValued v f) (hFi : Integral v (fourier B r (fun t => (f t)⁻¹)))
    (x : G) (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p))
    (A D : ZMod p → Residue v)
    (hfactor : ∀ u, planeRestriction e v f x a u = A u.1 * D u.2) :
    (∀ u w t : ZMod p,
      planeRestriction e v f x a (u + t, w) = planeRestriction e v f x a (u, w)) ∨
      (∀ u w t : ZMod p,
        planeRestriction e v f x a (u, w + t) = planeRestriction e v f x a (u, w)) := by
  rcases lemma1_iii_factors v hp hodd hs hC B hB hnd r hr f hF e hu hFi x a A D hfactor
    with ⟨c, _, hc⟩ | ⟨c, _, hc⟩
  · left
    intro u w t
    simp only [hfactor, hc]
  · right
    intro u w t
    simp only [hfactor, hc]

omit hf in
/-- [RW-rec]: the contradiction statement for the second Theorem 7 call. -/
theorem lemma1_iii_no_two_nonconstant (e : (Point p s 2 × C) ≃+ G)
    (hu : UnitValued v f) (hFi : Integral v (fourier B r (fun t => (f t)⁻¹)))
    (x : G) (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p))
    (A D : ZMod p → Residue v)
    (hfactor : ∀ u, planeRestriction e v f x a u = A u.1 * D u.2)
    (hA : ∃ u w, A u ≠ A w) (hD : ∃ u w, D u ≠ D w) : False := by
  rcases lemma1_iii_factors v hp hodd hs hC B hB hnd r hr f hF e hu hFi x a A D hfactor
    with ⟨c, _, hc⟩ | ⟨c, _, hc⟩
  · obtain ⟨u, w, huw⟩ := hA
    exact huw ((hc u).trans (hc w).symm)
  · obtain ⟨u, w, huw⟩ := hD
    exact huw ((hc u).trans (hc w).symm)

/-- Literal quotient, compatible with `FiniteTranslationRatio.ratio` and
`FiniteAlgebraicTransport.ratio`; [RW-rec]. -/
def translationRatio (E : G → L) (h t : G) : L := E (t + h) / E t

omit hf hF in
/-- [RW-rec]: both scaled functions in Theorem 4 have this call shape. Choose `(z,E)` or
`(z*E(h),fun t => E(t)⁻¹)` as appropriate. -/
theorem lemma1_i_scaled_ratio (e : (Point p s 1 × C) ≃+ G)
    (E : G → L) (z : L) (h : G)
    (hscaled : Integral v (fun t => z * translationRatio E h t))
    (hFscaled : Integral v (fourier B r (fun t => z * translationRatio E h t))) (x : G) :
    (∀ y, p • (y - x) = 0 → reduce v (z * translationRatio E h y) = 0) ∨
      p < 2 * Nat.card {y : G //
        p • (y - x) = 0 ∧ reduce v (z * translationRatio E h y) ≠ 0} := by
  exact lemma1_i_coset v hp hodd hs hC B hB hnd r hr
    (fun t => z * translationRatio E h t) hscaled hFscaled e x

omit hf hF in
/-- [RW-rec]: apply (iii) to the same actual quotient once its two Fourier-integrality hypotheses
have been supplied by the finite identities. -/
theorem lemma1_iii_translationRatio (e : (Point p s 2 × C) ≃+ G)
    (E : G → L) (h : G) (hE : UnitValued v E)
    (hR : Integral v (fourier B r (translationRatio E h)))
    (hRi : Integral v (fourier B r (fun t => (translationRatio E h t)⁻¹)))
    (x : G) (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p))
    (A D : ZMod p → Residue v)
    (hfactor : ∀ u, planeRestriction e v (translationRatio E h) x a u = A u.1 * D u.2) :
    (∃ c : Residue v, c ≠ 0 ∧ ∀ t, A t = c) ∨
      (∃ c : Residue v, c ≠ 0 ∧ ∀ t, D t = c) := by
  have hunit : UnitValued v (translationRatio E h) := by
    intro t
    simp only [translationRatio, div_eq_mul_inv, v.map_mul, v.map_inv,
      hE (t + h), hE t, neg_zero, add_zero]
  exact lemma1_iii_factors v hp hodd hs hC B hB hnd r hr
    (translationRatio E h) hR e hunit hRi x a A D hfactor

#check @lemma1_i_coset
#check @lemma1_ii_translation
#check @lemma1_iii_factors
#check @lemma1_iii_translationRatio

end SICLean.L5.LocalLemmaOne
