import SICLean.L5.LocalFourierSetup

set_option autoImplicit false

/-!
# Coordinate transport for `LocalCosetDegree`

The finite affine-substitution theorem is applied to the inverse chart. This keeps the
translation part of an arbitrary affine equivalence and allows coefficients in any
characteristic `p` residue field.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalCosetDegreeAux

open LocalFourierSetup FiniteCosetMoments FiniteMomentConsequences FiniteInterpolation

variable {p s d : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p]

/-- The coordinate formula for an affine map, after embedding the prime field. -/
theorem primeField_affine_apply
    (a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p))
    (u : Fin d → ZMod p) (i : Fin d) :
    primeField p k (a u i) =
      (∑ j, primeField p k (a.linear (Pi.single j 1) i) * primeField p k (u j)) +
        primeField p k (a 0 i) := by
  have ha : a u = a.linear u + a 0 := by
    simpa only [vadd_eq_add, add_zero] using a.map_vadd 0 u
  have hlinear : a.linear u i = ∑ j, u j * a.linear (Pi.single j 1) i := by
    conv_lhs => rw [pi_eq_sum_univ' u]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [ha]
  simp only [Pi.add_apply, map_add, hlinear, map_sum, map_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- [RW-rec, (14)] in arbitrary affine prime-field coordinates, using the existing finite
Pascal/Lucas and affine-polynomial moment theorem. -/
theorem affine_polynomial_moment (hs : 1 ≤ s) (hd : d = 1 ∨ d = 2)
    (g : Point p s d → k) (hglobal : GlobalLowBinomialVanishing g)
    (a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p))
    (P : MvPolynomial (Fin d) k) (hP : 2 * P.totalDegree < d * (p - 1)) :
    ∑ u : Fin d → ZMod p,
      g (topDigit p s d (a u)) *
        MvPolynomial.eval (fun i => primeField p k (u i)) P = 0 := by
  classical
  let b : CosetBase p s d := fun _ => ⟨0, pow_pos (Fact.out : p.Prime).pos _⟩
  let A : Matrix (Fin d) (Fin d) k :=
    fun i j => primeField p k (a.symm.linear (Pi.single j 1) i)
  let c : Fin d → k := fun i => primeField p k (a.symm 0 i)
  let E : CosetCoordinate p d ≃ (Fin d → ZMod p) :=
    (coordinateEquiv p d).trans a.toEquiv.symm
  have hpoint (u : CosetCoordinate p d) :
      cosetPoint b u = topDigit p s d (a (E u)) := by
    change cosetPoint b u = topDigit p s d (a (a.symm (coordinateEquiv p d u)))
    rw [a.apply_symm_apply]
    ext i
    simpa only [primeCosetPoint, Equiv.symm_apply_apply, b, zero_add, topDigit] using
      primeCosetPoint_apply b (coordinateEquiv p d u) i
  have hcoordinates (u : CosetCoordinate p d) :
      A.mulVec (fun i => ((u i).val : k)) + c =
        (fun i => primeField p k (E u i)) := by
    ext i
    change (∑ j, primeField p k (a.symm.linear (Pi.single j 1) i) * ((u j).val : k)) +
      primeField p k (a.symm 0 i) =
        primeField p k (a.symm (coordinateEquiv p d u) i)
    rw [primeField_affine_apply a.symm (coordinateEquiv p d u) i]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show coordinateEquiv p d u j = finPrimeEquiv p (u j) from rfl,
      primeField_finPrimeEquiv]
  have hm := coset_affine_polynomial_moment_eq_zero hs hd g hglobal b A c P hP
  calc
    _ = ∑ u : CosetCoordinate p d,
        g (cosetPoint b u) * MvPolynomial.eval (A.mulVec (fun i => ((u i).val : k)) + c) P := by
      symm
      apply Fintype.sum_equiv E
      intro u
      rw [hpoint, hcoordinates]
    _ = 0 := hm

end SICLean.L5.LocalCosetDegreeAux
