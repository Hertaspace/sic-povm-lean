import SICLean.L5.LocalFourierRestriction
import SICLean.L5.LocalCyclotomicValuation
import SICLean.L5.LocalFourierMomentsAux

set_option autoImplicit false

/-!
# From local Fourier integrality to the existing finite moment interface

[RW-rec, Lemma 1, p. 5, p. 6, (13), (14)]. This is the valuation bridge, into
`FiniteQBinomial` or `FiniteCosetMoments`. `globalBinomialVanishing` is the exact input
already consumed by `FiniteMomentConsequences`; no new polynomial-moment axiom is
assumed.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalFourierMoments

open LocalFourierSetup LocalFourierRestriction LocalCyclotomicValuation
open FiniteQBinomial FiniteCosetMoments FiniteMomentConsequences

variable {p s d : ℕ} [Fact p.Prime]
variable {L G C : Type*} [Field L] [CharZero L]
variable [AddCommGroup G] [Fintype G] [AddCommGroup C] [Fintype C]

/-- [RW-rec]: the literal q-binomial weighted sum. -/
def qMoment (z : L) (g : Point p s d → L) (j : Fin d → ℕ) : L :=
  ∑ x, g x * ∏ i, qBinomial z (x i).val (j i)

/-- [RW-rec]: the product multiplying the weighted sum. -/
def qDenominator (z : L) (j : Fin d → ℕ) : L :=
  ∏ i, finitePochhammer z z (j i)

variable (hs : 1 ≤ s) (hC : Nat.Coprime p (Fintype.card C))
variable (e : (Point p s d × C) ≃+ G) (B : G → G → L)
variable (hB : IsBicharacter B) (hnd : Nondegenerate B)
variable (r : L) (hr : r ^ 2 = (Fintype.card G : L))
variable (v : AddValuation L (WithTop ℝ)) (hp : v (p : L) = 1)
variable (f : G → L) (hF : Integral v (fourier B r f))

include hs hC hB hnd hr hp hF

/-- [RW-rec]: every positive standard-kernel sum has valuation at least ds/2. The
frequency-coordinate equivalence is separate from the value coordinates. -/
theorem standard_kernel_sum_value_ge (z : L) (hz : IsPrimitiveRoot z (p ^ s))
    (T : Point p s d ≃+ Point p s d)
    (hT : ∀ x y, primaryPairing e B x (T y) = z ^ (∑ i, (x i).val * (y i).val))
    (c : C) (a : Fin d → ℕ) :
    (((((d * s : ℕ) : ℝ) / 2) : ℝ) : WithTop ℝ) ≤
      v (∑ x : Point p s d, primarySlice e f c x * z ^ (∑ i, a i * (x i).val)) := by
  classical
  let y : Point p s d := fun i => (a i : ZMod (p ^ s))
  have hsum : rawFourier (primaryPairing e B) (primarySlice e f c) (-(T y)) =
      ∑ x : Point p s d, primarySlice e f c x * z ^ (∑ i, a i * (x i).val) := by
    unfold rawFourier
    simp only [neg_neg, hT]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    exact (LocalFourierMomentsAux.pow_dot_natCast z hz.pow_eq_one x a).symm
  rw [← hsum]
  exact raw_primarySlice_value_ge hs hC e B hB hnd r hr v hp f hF c (-(T y))

/-- [RW-rec]: invoke the existing `qBinomial_weighted_sum` and bound its RHS. -/
theorem scaled_qMoment_value_ge (z : L) (hz : IsPrimitiveRoot z (p ^ s))
    (T : Point p s d ≃+ Point p s d)
    (hT : ∀ x y, primaryPairing e B x (T y) = z ^ (∑ i, (x i).val * (y i).val))
    (c : C) (j : Fin d → ℕ) (hj : ∀ i, j i < p ^ s) :
    (((((d * s : ℕ) : ℝ) / 2) : ℝ) : WithTop ℝ) ≤
      v (qDenominator z j * qMoment z (primarySlice e f c) j) := by
  classical
  unfold qDenominator qMoment
  rw [qBinomial_weighted_sum z (hz.ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))]
  apply v.map_le_sum
  intro a _
  rw [v.map_mul]
  have hc := LocalFourierMomentsAux.value_prod_nonneg v Finset.univ
    (fun i => finitePochhammerCoeff z⁻¹ (j i) (a i).val)
    (fun i _ => finitePochhammerCoeff_value_nonneg v
      (primitive_value_zero v hs hz) (j i) (a i).val)
  have hk := standard_kernel_sum_value_ge hs hC e B hB hnd r hr v hp f hF
    z hz T hT c (fun i => (a i).val)
  simpa only [zero_add] using add_le_add hc hk

/-- [RW-rec, (13)]: division by the nonzero Pochhammer factors. -/
theorem qMoment_value_ge (z : L) (hz : IsPrimitiveRoot z (p ^ s))
    (T : Point p s d ≃+ Point p s d)
    (hT : ∀ x y, primaryPairing e B x (T y) = z ^ (∑ i, (x i).val * (y i).val))
    (c : C) (j : Fin d → ℕ) (hj : ∀ i, j i < p ^ s) :
    (((((d * s : ℕ) : ℝ) / 2 - ∑ i, pochhammerValue v z (j i)) : ℝ) : WithTop ℝ) ≤
      v (qMoment z (primarySlice e f c) j) := by
  have hden : v (qDenominator z j) =
      ((∑ i, pochhammerValue v z (j i) : ℝ) : WithTop ℝ) :=
    LocalFourierMomentsAux.value_prod_eq_sum v Finset.univ
      (fun i => finitePochhammer z z (j i)) (fun i => pochhammerValue v z (j i))
      (fun i _ => value_finitePochhammer v hs hz (hj i))
  have hscaled := scaled_qMoment_value_ge hs hC e B hB hnd r hr v hp f hF
    z hz T hT c j hj
  rw [v.map_mul, hden] at hscaled
  apply (WithTop.add_le_add_iff_left (x :=
    ((∑ i, pochhammerValue v z (j i) : ℝ) : WithTop ℝ)) WithTop.coe_ne_top).mp
  simpa only [← WithTop.coe_add, add_sub_cancel] using hscaled

/-- [RW-rec]: the low-total-degree q-moment lies in the maximal ideal. -/
theorem qMoment_value_pos (hodd : p ≠ 2) (hd : d = 1 ∨ d = 2)
    (z : L) (hz : IsPrimitiveRoot z (p ^ s))
    (T : Point p s d ≃+ Point p s d)
    (hT : ∀ x y, primaryPairing e B x (T y) = z ^ (∑ i, (x i).val * (y i).val))
    (c : C) (j : Fin d → ℕ) (hj : ∀ i, j i < p ^ s)
    (hdeg : 2 * totalDegree j < d * (p ^ s - 1)) :
    0 < v (qMoment z (primarySlice e f c) j) := by
  have hlow := low_multiIndex_value_lt v hp hodd hs hz hd j hj hdeg
  have hpos : (0 : WithTop ℝ) <
      ((((d * s : ℕ) : ℝ) / 2 - ∑ i, pochhammerValue v z (j i) : ℝ) : WithTop ℝ) := by
    exact_mod_cast sub_pos.mpr hlow
  exact hpos.trans_le (qMoment_value_ge hs hC e B hB hnd r hr v hp f hF
    z hz T hT c j hj)

omit hC hB hnd hr hF in
/-- [RW-rec]: reduce the existing integral q-binomial polynomials termwise. No global moment
hypothesis is assumed by `reduction`. -/
theorem reduce_qMoment (hf : Integral v f) (z : L)
    (hz : IsPrimitiveRoot z (p ^ s)) (c : C) (j : Fin d → ℕ) :
    reduce v (qMoment z (primarySlice e f c) j) =
      globalBinomialMoment (reduction v (primarySlice e f c)) j := by
  classical
  have hz0 : 0 ≤ v z := (primitive_value_zero v hs hz).ge
  have hq (x : Point p s d) (i : Fin d) :
      0 ≤ v (qBinomial z (x i).val (j i)) :=
    qBinomial_value_nonneg v hz0 _ _
  have hw (x : Point p s d) : 0 ≤ v (∏ i, qBinomial z (x i).val (j i)) :=
    LocalFourierMomentsAux.value_prod_nonneg v Finset.univ _ (fun i _ => hq x i)
  unfold qMoment globalBinomialMoment
  rw [LocalFourierMomentsAux.reduce_sum v Finset.univ _ (fun x _ => by
    rw [v.map_mul]
    exact add_nonneg (hf _) (hw x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [reduce_mul v (primarySlice e f c x) _ (hf (e (x, c))) (hw x),
    LocalFourierMomentsAux.reduce_prod v Finset.univ _ (fun i _ => hq x i)]
  simp only [qBinomial_reduce v hp hs hz, binomialWeight, reduction]

/-- [RW-rec]: bounded low binomial moments vanish. -/
theorem globalBinomialMoment_zero_bounded (hodd : p ≠ 2) (hd : d = 1 ∨ d = 2)
    (hf : Integral v f) (c : C) (j : Fin d → ℕ) (hj : ∀ i, j i < p ^ s)
    (hdeg : 2 * totalDegree j < d * (p ^ s - 1)) :
    globalBinomialMoment (reduction v (primarySlice e f c)) j = 0 := by
  obtain ⟨z, hz, T, hT⟩ := exists_standard_primary_kernel hs hd hC e B hB hnd
  rw [← reduce_qMoment hs e v hp f hf z hz c j]
  have hpos := qMoment_value_pos hs hC e B hB hnd r hr v hp f hF
    hodd hd z hz T hT c j hj hdeg
  exact (reduce_eq_zero_iff v _ hpos.le).mpr hpos

/-- [RW-rec]: the precise already existing finite interface, including unbounded indices (a binomial
coefficient then vanishes identically). -/
theorem globalBinomialVanishing (hodd : p ≠ 2) (hd : d = 1 ∨ d = 2)
    (hf : Integral v f) (c : C) :
    GlobalLowBinomialVanishing (reduction v (primarySlice e f c)) := by
  classical
  intro j hdeg
  by_cases hj : ∀ i, j i < p ^ s
  · exact globalBinomialMoment_zero_bounded hs hC e B hB hnd r hr v hp f hF
      hodd hd hf c j hj hdeg
  · push Not at hj
    obtain ⟨i, hi⟩ := hj
    exact LocalFourierMomentsAux.globalBinomialMoment_eq_zero_of_large_index
      _ j i hi

/-- [RW-rec]: use arbitrary centers in G, not only chosen lower-digit representatives. Fourier
translation supplies the input. -/
theorem translated_globalBinomialVanishing (hodd : p ≠ 2) (hd : d = 1 ∨ d = 2)
    (hf : Integral v f) (x : G) :
    GlobalLowBinomialVanishing (fun h : Point p s d => reduce v (f (x + e (h, 0)))) := by
  have hshift := integral_fourier_translate B hB r v f hF x
  have hglobal := globalBinomialVanishing hs hC e B hB hnd r hr v hp
    (fun t => f (x + t)) hshift hodd hd (fun t => hf (x + t)) (0 : C)
  exact hglobal

omit hF in
/-- [RW-rec]: the same bridge for the pointwise inverse. This is the inverse-transform hypothesis of
Lemma 1(ii)/(iii), not a Fourier inversion operation. -/
theorem inverse_globalBinomialVanishing (hodd : p ≠ 2) (hd : d = 1 ∨ d = 2)
    (hu : UnitValued v f) (hFi : Integral v (fourier B r (fun x => (f x)⁻¹))) (c : C) :
    GlobalLowBinomialVanishing (fun h : Point p s d =>
      (reduce v (primarySlice e f c h))⁻¹) := by
  have hui := unitValued_inverse v f hu
  have hglobal := globalBinomialVanishing hs hC e B hB hnd r hr v hp
    (fun x => (f x)⁻¹) hFi hodd hd (integral_of_unitValued v _ hui) c
  have hred : reduction v (primarySlice e (fun x => (f x)⁻¹) c) =
      (fun h => (reduce v (primarySlice e f c h))⁻¹) := by
    funext h
    exact reduce_inv v _ (hu (e (h, c)))
  rw [hred] at hglobal
  exact hglobal

/-- [RW-rec, (14)]: invoke the existing Pascal/Lucas/polynomial theorem on this selected small
coset. Its proof calls that finite theorem. -/
theorem primary_coset_polynomial_moment (hodd : p ≠ 2) (hd : d = 1 ∨ d = 2)
    (hf : Integral v f) (c : C) (b : CosetBase p s d)
    (P : MvPolynomial (Fin d) (Residue v))
    (hP : 2 * P.totalDegree < d * (p - 1)) :
    ∑ u : CosetCoordinate p d,
      reduce v (primarySlice e f c (cosetPoint b u)) *
        MvPolynomial.eval (fun i => ((u i).val : Residue v)) P = 0 := by
  let : CharP (Residue v) p := residue_charP v hp
  exact coset_polynomial_moment_eq_zero hs hd (reduction v (primarySlice e f c))
    (globalBinomialVanishing hs hC e B hB hnd r hr v hp f hF hodd hd hf c) b P hP

#check @globalBinomialVanishing
#check @FiniteCosetMoments.coset_polynomial_moment_eq_zero
#check @FiniteMomentConsequences.line_lowMoments_of_global

end SICLean.L5.LocalFourierMoments
