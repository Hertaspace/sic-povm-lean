import SICLean.L5.LocalFourierMoments
import SICLean.L5.LocalCosetDegreeAux

set_option autoImplicit false

/-!
# Arbitrary affine coset coordinates and polynomial degree bounds

[RW-rec, p. 6] especially affine invariance. The local-to-finite bridge uses
`FiniteCosetMoments` and `FiniteInterpolation` for all Pascal, interpolation and
root-count facts. The residue field is unrestricted. The displayed `CharP` instance is
supplied by `LocalFourierSetup.residue_charP v hp`, not an additional number-theoretic
conjecture.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalCosetDegree

open LocalFourierSetup FiniteCosetMoments FiniteInterpolation

variable {p s : ℕ} [Fact p.Prime]
variable {L G C : Type*} [Field L] [CharZero L]
variable [AddCommGroup G] [Fintype G] [AddCommGroup C] [Fintype C]
variable (v : AddValuation L (WithTop ℝ)) [CharP (Residue v) p]
variable (hp : v (p : L) = 1) (hodd : p ≠ 2) (hs : 1 ≤ s)
variable (hC : Nat.Coprime p (Fintype.card C))
variable (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B)
variable (r : L) (hr : r ^ 2 = (Fintype.card G : L))
variable (f : G → L) (hf : Integral v f) (hF : Integral v (fourier B r f))

include hp hodd hs hC hB hnd hr hf hF

/-- [RW-rec, (14)]: the moment bound in any affine prime-field chart. The translation in the affine
map need not vanish. -/
theorem chart_polynomial_moment {d : ℕ} (hd : d = 1 ∨ d = 2)
    (e : (Point p s d × C) ≃+ G) (x : G)
    (a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p))
    (P : MvPolynomial (Fin d) (Residue v)) (hP : 2 * P.totalDegree < d * (p - 1)) :
    ∑ u : Fin d → ZMod p,
      reduce v (f (cosetChart e x a u)) *
        MvPolynomial.eval (fun i => primeField p (Residue v) (u i)) P = 0 := by
  exact LocalCosetDegreeAux.affine_polynomial_moment hs hd
    (fun h => reduce v (f (x + e (h, 0))))
    (LocalFourierMoments.translated_globalBinomialVanishing hs hC e B hB hnd r hr
      v hp f hF hodd hd hf x) a P hP

/-- [RW-rec, (14)]: explicit monomial version with the strict total-degree cutoff. -/
theorem chart_monomial_moment {d : ℕ} (hd : d = 1 ∨ d = 2)
    (e : (Point p s d × C) ≃+ G) (x : G)
    (a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p))
    (j : Fin d → ℕ) (hj : 2 * totalDegree j < d * (p - 1)) :
    ∑ u : Fin d → ZMod p,
      reduce v (f (cosetChart e x a u)) *
        ∏ i, (primeField p (Residue v) (u i)) ^ j i = 0 := by
  classical
  let P : MvPolynomial (Fin d) (Residue v) := ∏ i, MvPolynomial.X i ^ j i
  have hdegree : P.totalDegree ≤ totalDegree j := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simp)
  have hm := chart_polynomial_moment v hp hodd hs hC B hB hnd r hr f hf hF
    hd e x a P (by omega)
  simpa only [P, MvPolynomial.eval_prod, map_pow, MvPolynomial.eval_X] using hm

omit hf hF in
/-- [RW-rec]: inverse moments in the same chosen chart. -/
theorem chart_inverse_polynomial_moment {d : ℕ} (hd : d = 1 ∨ d = 2)
    (e : (Point p s d × C) ≃+ G) (hu : UnitValued v f)
    (hFi : Integral v (fourier B r (fun t => (f t)⁻¹))) (x : G)
    (a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p))
    (P : MvPolynomial (Fin d) (Residue v)) (hP : 2 * P.totalDegree < d * (p - 1)) :
    ∑ u : Fin d → ZMod p,
      (reduce v (f (cosetChart e x a u)))⁻¹ *
        MvPolynomial.eval (fun i => primeField p (Residue v) (u i)) P = 0 := by
  have hm := chart_polynomial_moment v hp hodd hs hC B hB hnd r hr
    (fun t => (f t)⁻¹)
    (integral_of_unitValued v _ (unitValued_inverse v f hu)) hFi hd e x a P hP
  have hinv (t : G) := reduce_inv v (f t) (hu t)
  simpa only [hinv] using hm

/-- [RW-rec]: the exact rank-one predicate already used by interpolation. -/
theorem line_lowMoments (e : (Point p s 1 × C) ≃+ G) (x : G)
    (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) :
    HasVanishingLowMoments p (Residue v) (lineRestriction e v f x a) := by
  intro j hj
  have hm := chart_monomial_moment v hp hodd hs hC B hB hnd r hr f hf hF
    (Or.inl rfl) e x a (fun _ => j)
    (by simpa only [totalDegree, Fin.sum_univ_one, one_mul] using hj)
  have heq : (∑ u : Fin 1 → ZMod p,
      reduce v (f (cosetChart e x a u)) *
        ∏ i, primeField p (Residue v) (u i) ^ j) =
      moment p (Residue v) (lineRestriction e v f x a) j := by
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod p))
    intro u
    have hu : (fun _ : Fin 1 => u 0) = u := by ext i; congr 1; exact Subsingleton.elim _ _
    simp only [Fin.prod_univ_one, lineRestriction, Equiv.funUnique_apply,
      show (default : Fin 1) = 0 from Subsingleton.elim _ _, hu, mul_comm]
  exact heq.symm.trans hm

omit hf hF in
/-- [RW-rec]: the reciprocal rank-one predicate, not inverse Fourier. -/
theorem line_inverse_lowMoments (e : (Point p s 1 × C) ≃+ G)
    (hu : UnitValued v f) (hFi : Integral v (fourier B r (fun t => (f t)⁻¹)))
    (x : G) (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) :
    HasVanishingLowMoments p (Residue v) (fun t => (lineRestriction e v f x a t)⁻¹) := by
  have hm := line_lowMoments v hp hodd hs hC B hB hnd r hr (fun t => (f t)⁻¹)
    (integral_of_unitValued v _ (unitValued_inverse v f hu)) hFi e x a
  have hinv : lineRestriction e v (fun t => (f t)⁻¹) x a =
      (fun t => (lineRestriction e v f x a t)⁻¹) := by
    funext t
    exact reduce_inv v _ (hu _)
  rwa [hinv] at hm

/-- [RW-rec]: apply the existing degree bound to this local coset. -/
theorem line_interpolant_degree (e : (Point p s 1 × C) ≃+ G) (x : G)
    (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) :
    (interpolant p (Residue v) (lineRestriction e v f x a)).natDegree ≤ (p - 1) / 2 := by
  exact natDegree_interpolant_le_half_of_lowMoments p (Residue v) _
    (line_lowMoments v hp hodd hs hC B hB hnd r hr f hf hF e x a)

omit hf hF in
/-- [RW-rec]: the same bound for the reciprocal interpolant. -/
theorem line_inverse_interpolant_degree (e : (Point p s 1 × C) ≃+ G)
    (hu : UnitValued v f) (hFi : Integral v (fourier B r (fun t => (f t)⁻¹)))
    (x : G) (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) :
    (interpolant p (Residue v) (fun t => (lineRestriction e v f x a t)⁻¹)).natDegree ≤
      (p - 1) / 2 := by
  exact natDegree_interpolant_le_half_of_lowMoments p (Residue v) _
    (line_inverse_lowMoments v hp hodd hs hC B hB hnd r hr f e hu hFi x a)

/-- [RW-rec]: the existing plane-moment predicate in this chart. -/
theorem plane_lowMoments (e : (Point p s 2 × C) ≃+ G) (x : G)
    (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p)) :
    HasVanishingPlaneMoments p (Residue v) (planeRestriction e v f x a) := by
  intro j k hjk
  have hm := chart_monomial_moment v hp hodd hs hC B hB hnd r hr f hf hF
    (Or.inr rfl) e x a ![j, k]
    (by simpa only [totalDegree, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] using (Nat.mul_lt_mul_left (by decide : 0 < 2)).mpr hjk)
  have heq : (∑ u : Fin 2 → ZMod p,
      reduce v (f (cosetChart e x a u)) *
        ∏ i, primeField p (Residue v) (u i) ^ (![j, k] i)) =
      planeMoment p (Residue v) (planeRestriction e v f x a) j k := by
    apply Fintype.sum_equiv (finTwoArrowEquiv (ZMod p))
    intro u
    have hu : ![u 0, u 1] = u :=
      (finTwoArrowEquiv (ZMod p)).symm_apply_apply u
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    change reduce v (f (cosetChart e x a u)) *
        (primeField p (Residue v) (u 0) ^ j * primeField p (Residue v) (u 1) ^ k) =
      primeField p (Residue v) (u 0) ^ j * primeField p (Residue v) (u 1) ^ k *
        reduce v (f (cosetChart e x a ![u 0, u 1]))
    rw [hu, mul_comm]
  exact heq.symm.trans hm

omit hf hF in
/-- [RW-rec]: reciprocal plane moments, needed for the second degree inequality. -/
theorem plane_inverse_lowMoments (e : (Point p s 2 × C) ≃+ G)
    (hu : UnitValued v f) (hFi : Integral v (fourier B r (fun t => (f t)⁻¹)))
    (x : G) (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p)) :
    HasVanishingPlaneMoments p (Residue v) (fun u => (planeRestriction e v f x a u)⁻¹) := by
  have hm := plane_lowMoments v hp hodd hs hC B hB hnd r hr (fun t => (f t)⁻¹)
    (integral_of_unitValued v _ (unitValued_inverse v f hu)) hFi e x a
  have hinv : planeRestriction e v (fun t => (f t)⁻¹) x a =
      (fun u => (planeRestriction e v f x a u)⁻¹) := by
    funext u
    exact reduce_inv v _ (hu _)
  rwa [hinv] at hm

omit hf in
/-- [RW-rec]: factorization is required only on this selected coset. -/
theorem plane_factor_degrees (e : (Point p s 2 × C) ≃+ G) (hu : UnitValued v f)
    (x : G) (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p))
    (A D : ZMod p → Residue v)
    (hfactor : ∀ u, planeRestriction e v f x a u = A u.1 * D u.2) :
    (interpolant p (Residue v) A).natDegree +
      (interpolant p (Residue v) D).natDegree ≤ p - 1 := by
  have hnonzero (u : ZMod p × ZMod p) : planeRestriction e v f x a u ≠ 0 :=
    (reduce_ne_zero_iff v _ (integral_of_unitValued v f hu _)).mpr (hu _)
  have hA : A ≠ 0 := by
    intro hzero
    apply hnonzero (0, 0)
    rw [hfactor, hzero]
    exact zero_mul _
  have hD : D ≠ 0 := by
    intro hzero
    apply hnonzero (0, 0)
    rw [hfactor, hzero]
    exact mul_zero _
  apply natDegree_add_le_of_separable_lowMoments p (Residue v) A D hA hD
  have hm := plane_lowMoments v hp hodd hs hC B hB hnd r hr f
    (integral_of_unitValued v f hu) hF e x a
  have hsep : planeRestriction e v f x a = separableFunction p (Residue v) A D :=
    funext hfactor
  rwa [hsep] at hm

omit hf hF in
/-- [RW-rec]: second inequality for the actual reciprocal factors. -/
theorem plane_inverse_factor_degrees (e : (Point p s 2 × C) ≃+ G)
    (hu : UnitValued v f) (hFi : Integral v (fourier B r (fun t => (f t)⁻¹)))
    (x : G) (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p))
    (A D : ZMod p → Residue v)
    (hfactor : ∀ u, planeRestriction e v f x a u = A u.1 * D u.2) :
    (interpolant p (Residue v) (fun t => (A t)⁻¹)).natDegree +
      (interpolant p (Residue v) (fun t => (D t)⁻¹)).natDegree ≤ p - 1 := by
  have hm := plane_factor_degrees v hp hodd hs hC B hB hnd r hr
    (fun t => (f t)⁻¹) hFi e (unitValued_inverse v f hu) x a
    (fun t => (A t)⁻¹) (fun t => (D t)⁻¹)
  apply hm
  intro u
  change reduce v (f (cosetChart e x a ![u.1, u.2]))⁻¹ = _
  rw [reduce_inv v _ (hu _)]
  change (planeRestriction e v f x a u)⁻¹ = _
  rw [hfactor, mul_inv]

#check @chart_polynomial_moment
#check @plane_factor_degrees
#check @FiniteInterpolation.one_factor_constant_of_factorization

end SICLean.L5.LocalCosetDegree
