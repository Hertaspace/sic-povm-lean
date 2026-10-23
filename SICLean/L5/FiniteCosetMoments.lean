import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Extension.Linear
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import SICLean.L5.FiniteCosetMomentsAux

/-!
# Partial Lucas and low moments on `H[p]`-cosets

Finite algebra from [RW-rec, Lemma 1], through equation (14). The group is
explicitly `(ZMod (p ^ s))^d`; its `p`-torsion, rather than the whole group,
supplies the small cosets. All characteristic-`p` statements allow any
coefficient field `k` of characteristic `p`, including proper extensions of `ZMod p`.

Every degree hypothesis uses the strict integer inequality `2 * degree < bound`.
The restriction `d = 1 ∨ d = 2` transfers the global cutoff to every choice of
lower digits. No valuation or special value occurs here.
-/

set_option autoImplicit false

noncomputable section

namespace SICLean.L5.FiniteCosetMoments

open scoped BigOperators

/-- The equal-exponent `p`-primary group used in [RW-rec, Lemma 1]. -/
abbrev Point (p s d : ℕ) := Fin d → ZMod (p ^ s)

/-- Lower digits label the `H[p]`-cosets; see [RW-rec, Lemma 1]. -/
abbrev CosetBase (p s d : ℕ) := Fin d → Fin (p ^ (s - 1))

/-- Upper digits give coordinates on a small coset; see [RW-rec, Lemma 1]. -/
abbrev CosetCoordinate (p d : ℕ) := Fin d → Fin p

/-- The actual subgroup `H[p]`, defined as the kernel of multiplication by `p`. -/
def pTorsion (p s d : ℕ) : AddSubgroup (Point p s d) :=
  (nsmulAddMonoidHom p : Point p s d →+ Point p s d).ker

/-- The representative of the coset with lower digits `b`. -/
def cosetBasePoint {p s d : ℕ} (b : CosetBase p s d) : Point p s d :=
  fun i => ((b i).val : ZMod (p ^ s))

/-- The coordinate formula `xᵢ = bᵢ + p^(s-1) uᵢ` of [RW-rec, Lemma 1]. -/
def cosetPoint {p s d : ℕ} (b : CosetBase p s d)
    (u : CosetCoordinate p d) : Point p s d :=
  fun i => (((b i).val + p ^ (s - 1) * (u i).val : ℕ) : ZMod (p ^ s))

/-- Split a binomial exponent as `jᵢ = cᵢ + p^(s-1) rᵢ`. -/
def splitExponent {p s d : ℕ} (c : CosetBase p s d)
    (r : CosetCoordinate p d) : Fin d → ℕ :=
  fun i => (c i).val + p ^ (s - 1) * (r i).val

/-- Total degree of a multi-index, with no bounded-exponent convention. -/
def totalDegree {d : ℕ} (j : Fin d → ℕ) : ℕ := ∑ i, j i

/-- The Pascal matrix has row `c`, column `b`, and entry `choose b c`. -/
def pascalMatrix (k : Type*) [CommRing k] (m : ℕ) : Matrix (Fin m) (Fin m) k :=
  fun c b => (Nat.choose b.val c.val : k)

/-- The concrete `d`-fold Pascal tensor on function indices. -/
def tensorPascalMatrix (k : Type*) [CommRing k] (d m : ℕ) :
    Matrix (Fin d → Fin m) (Fin d → Fin m) k :=
  fun c b => ∏ i, pascalMatrix k m (c i) (b i)

/-- Product binomial weight on natural representatives. -/
def binomialWeight (k : Type*) [CommRing k] {d : ℕ}
    (x j : Fin d → ℕ) : k :=
  ∏ i, (Nat.choose (x i) (j i) : k)

/-- Product monomial weight evaluated in the coefficient field. -/
def monomialWeight (k : Type*) [CommRing k] {d : ℕ}
    (x : Fin d → k) (j : Fin d → ℕ) : k :=
  ∏ i, x i ^ j i

/-- The global moment in [RW-rec, Lemma 1], using canonical `ZMod` representatives. -/
def globalBinomialMoment {p s d : ℕ} [Fact p.Prime] {k : Type*} [CommRing k]
    (f : Point p s d → k) (j : Fin d → ℕ) : k :=
  ∑ x, f x * binomialWeight k (fun i => (x i).val) j

/-- The inner binomial moment in [RW-rec, Lemma 1]. -/
def cosetBinomialMoment {p s d : ℕ} {k : Type*} [CommRing k]
    (f : Point p s d → k) (b : CosetBase p s d) (r : CosetCoordinate p d) : k :=
  ∑ u, f (cosetPoint b u) *
    binomialWeight k (fun i => (u i).val) (fun i => (r i).val)

/-- The monomial moment in [RW-rec, (14)]. -/
def cosetMonomialMoment {p s d : ℕ} {k : Type*} [CommRing k]
    (f : Point p s d → k) (b : CosetBase p s d) (j : Fin d → ℕ) : k :=
  ∑ u, f (cosetPoint b u) * monomialWeight k (fun i => ((u i).val : k)) j

/-- [RW-rec, Lemma 1]: partial Lucas in any coefficient field of characteristic `p`.
The bounds on both lower digits and both upper digits are explicit. -/
theorem partialLucas {p s : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p]
    (hs : 1 ≤ s) {b c u r : ℕ}
    (hb : b < p ^ (s - 1)) (hc : c < p ^ (s - 1)) (hu : u < p) (hr : r < p) :
    (Nat.choose (b + p ^ (s - 1) * u) (c + p ^ (s - 1) * r) : k) =
      (Nat.choose b c : k) * (Nat.choose u r : k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have step (n m : ℕ) :
      (Nat.choose n m : k) = (Nat.choose (n % p) (m % p) : k) *
        (Nat.choose (n / p) (m / p) : k) := by
    simpa only [Nat.cast_mul] using
      CharP.natCast_eq_natCast' k p
        (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := m) (p := p))
  have split : ∀ (a b c u r : ℕ), b < p ^ a → c < p ^ a →
      (Nat.choose (b + p ^ a * u) (c + p ^ a * r) : k) =
        (Nat.choose b c : k) * (Nat.choose u r : k) := by
    intro a
    induction a with
    | zero =>
        intro b c u r hb hc
        have hb0 : b = 0 := by simpa using hb
        have hc0 : c = 0 := by simpa using hc
        simp [hb0, hc0]
    | succ a ih =>
        intro b c u r hb hc
        have hb' : b / p < p ^ a := by
          apply (Nat.div_lt_iff_lt_mul hp).mpr
          simpa only [Nat.pow_succ] using hb
        have hc' : c / p < p ^ a := by
          apply (Nat.div_lt_iff_lt_mul hp).mpr
          simpa only [Nat.pow_succ] using hc
        rw [step]
        simp only [Nat.pow_succ', Nat.mul_assoc, Nat.add_mul_mod_self_left,
          Nat.add_mul_div_left _ _ hp]
        rw [ih (b / p) (c / p) u r hb' hc', ← mul_assoc, ← step b c]
  exact split (s - 1) b c u r hb hc

/-- Helper for [RW-rec, Lemma 1]: every finite Pascal matrix has determinant one. -/
theorem pascalMatrix_det_one (k : Type*) [CommRing k] (m : ℕ) :
    (pascalMatrix k m).det = 1 := by
  have htri : (pascalMatrix k m).IsUpperTriangular := by
    intro c b hbc
    change (Nat.choose b.val c.val : k) = 0
    rw [Nat.choose_eq_zero_of_lt (show b.val < c.val from hbc), Nat.cast_zero]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [pascalMatrix]

/-- [RW-rec, Lemma 1]: the concrete Pascal tensor has determinant one over any ring. -/
theorem tensorPascalMatrix_det_one (k : Type*) [CommRing k] (d m : ℕ) :
    (tensorPascalMatrix k d m).det = 1 := by
  classical
  let ι := LinearExtension (Fin d → Fin m)
  let e : ι ≃ (Fin d → Fin m) := Equiv.refl _
  let : Fintype ι := Fintype.ofEquiv _ e.symm
  let M := (tensorPascalMatrix k d m).submatrix e e
  have htri : M.IsUpperTriangular := by
    intro c b hbc
    by_cases hcb : ∀ i, e c i ≤ e b i
    · have hle : toLinearExtension (e c) ≤ toLinearExtension (e b) :=
        toLinearExtension.monotone hcb
      exact (not_le_of_gt hbc hle).elim
    · obtain ⟨i, hi⟩ := not_forall.mp hcb
      have hval : (e b i).val < (e c i).val := Fin.lt_def.mp (lt_of_not_ge hi)
      change (∏ i, pascalMatrix k m (e c i) (e b i)) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [pascalMatrix, Nat.choose_eq_zero_of_lt hval, Nat.cast_zero]
  rw [← Matrix.det_submatrix_equiv_self e]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [M, tensorPascalMatrix, pascalMatrix, Matrix.submatrix]

/-- [RW-rec, Lemma 1]: the Pascal tensor is a unit in the square matrix ring. -/
theorem tensorPascalMatrix_isUnit (k : Type*) [CommRing k] (d m : ℕ) :
    IsUnit (tensorPascalMatrix k d m) := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [tensorPascalMatrix_det_one]
  exact isUnit_one

/-- Helper for [RW-rec, Lemma 1]: Pascal tensor multiplication is injective. -/
theorem tensorPascalMatrix_mulVec_injective (k : Type*) [CommRing k] (d m : ℕ) :
    Function.Injective (tensorPascalMatrix k d m).mulVec := by
  classical
  exact Matrix.mulVec_injective_of_isUnit (tensorPascalMatrix_isUnit k d m)

/-- [RW-rec, Lemma 1]: the lower and upper digits give unique global coordinates. -/
theorem cosetPoint_bijective {p s d : ℕ} [Fact p.Prime] (hs : 1 ≤ s) :
    Function.Bijective (fun bu : CosetBase p s d × CosetCoordinate p d =>
      cosetPoint bu.1 bu.2) := by
  let q := p ^ (s - 1)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < q := pow_pos hp _
  have hpow : q * p = p ^ s := by
    dsimp [q]
    rw [← pow_succ, Nat.sub_add_cancel hs]
  have hbound : ∀ (b : CosetBase p s d) (u : CosetCoordinate p d) (i : Fin d),
      (b i).val + q * (u i).val < p ^ s := by
    intro b u i
    calc
      (b i).val + q * (u i).val < q + q * (u i).val :=
        Nat.add_lt_add_right (b i).isLt _
      _ = q * ((u i).val + 1) := by ring
      _ ≤ q * p := Nat.mul_le_mul_left _ (u i).isLt
      _ = p ^ s := hpow
  constructor
  · rintro ⟨b, u⟩ ⟨c, v⟩ h
    have hn : ∀ i, (b i).val + q * (u i).val =
        (c i).val + q * (v i).val := by
      intro i
      have hi := congrArg ZMod.val (congrFun h i)
      change (((b i).val + q * (u i).val : ℕ) : ZMod (p ^ s)).val =
        (((c i).val + q * (v i).val : ℕ) : ZMod (p ^ s)).val at hi
      rwa [ZMod.val_natCast_of_lt (hbound b u i),
        ZMod.val_natCast_of_lt (hbound c v i)] at hi
    have hb : b = c := by
      funext i
      apply Fin.ext
      have hi := congrArg (fun n => n % q) (hn i)
      simpa only [Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (show (b i).val < q from (b i).isLt),
        Nat.mod_eq_of_lt (show (c i).val < q from (c i).isLt)] using hi
    have hu : u = v := by
      funext i
      apply Fin.ext
      have hi := hn i
      rw [hb] at hi
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel hi)
    exact Prod.ext hb hu
  · intro x
    let b : CosetBase p s d := fun i => ⟨(x i).val % q, Nat.mod_lt _ hq⟩
    let u : CosetCoordinate p d := fun i =>
      ⟨(x i).val / q, (Nat.div_lt_iff_lt_mul hq).mpr (by
        rw [Nat.mul_comm, hpow]
        exact (x i).val_lt)⟩
    refine ⟨(b, u), ?_⟩
    funext i
    change (((x i).val % q + q * ((x i).val / q) : ℕ) : ZMod (p ^ s)) = x i
    rw [Nat.mod_add_div, ZMod.natCast_zmod_val]

/-- [RW-rec, Lemma 1]: for fixed lower digits, the coordinate image is exactly one
coset of the concrete `p`-torsion subgroup, not a coset of the whole group. -/
theorem cosetPoint_range_eq_pTorsion_coset {p s d : ℕ} [Fact p.Prime]
    (hs : 1 ≤ s) (b : CosetBase p s d) :
    Set.range (cosetPoint b) = {x | x - cosetBasePoint b ∈ pTorsion p s d} := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow : p * p ^ (s - 1) = p ^ s := by
    rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel hs]
  have hzero : (p : ZMod (p ^ s)) * ((p ^ (s - 1) : ℕ) : ZMod (p ^ s)) = 0 := by
    rw [← Nat.cast_mul, hpow, ZMod.natCast_self]
  have hcoordinate : ∀ (c : CosetBase p s d) (u : CosetCoordinate p d),
      p • cosetPoint c u = p • cosetBasePoint c := by
    intro c u
    funext i
    simp only [Pi.smul_apply, cosetPoint, cosetBasePoint, Nat.cast_add,
      Nat.cast_mul, nsmul_eq_mul]
    rw [mul_add, ← mul_assoc, hzero, zero_mul, add_zero]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    change p • (cosetPoint b u - cosetBasePoint b) = 0
    rw [smul_sub, hcoordinate, sub_self]
  · intro hx
    obtain ⟨⟨c, u⟩, rfl⟩ := (cosetPoint_bijective hs).surjective x
    change p • (cosetPoint c u - cosetBasePoint b) = 0 at hx
    rw [smul_sub, hcoordinate, sub_eq_zero] at hx
    have hcb : c = b := by
      funext i
      apply Fin.ext
      have hi := congrFun hx i
      change p • ((c i).val : ZMod (p ^ s)) =
        p • ((b i).val : ZMod (p ^ s)) at hi
      simp only [nsmul_eq_mul, ← Nat.cast_mul] at hi
      have hc : p * (c i).val < p ^ s := by
        rw [← hpow]
        exact Nat.mul_lt_mul_of_pos_left (c i).isLt hp
      have hb : p * (b i).val < p ^ s := by
        rw [← hpow]
        exact Nat.mul_lt_mul_of_pos_left (b i).isLt hp
      have hn := congrArg ZMod.val hi
      rw [ZMod.val_natCast_of_lt hc, ZMod.val_natCast_of_lt hb] at hn
      exact Nat.eq_of_mul_eq_mul_left hp hn
    exact ⟨u, by rw [hcb]⟩

/-- [RW-rec, Lemma 1]: in rank one or two, every lower-digit choice stays strictly
below the global degree cutoff when the upper digits satisfy the small cutoff. -/
theorem splitExponent_degree_lt {p s d : ℕ} [Fact p.Prime]
    (hs : 1 ≤ s) (hd : d = 1 ∨ d = 2)
    (c : CosetBase p s d) (r : CosetCoordinate p d)
    (hr : 2 * totalDegree (fun i => (r i).val) < d * (p - 1)) :
    2 * totalDegree (splitExponent c r) < d * (p ^ s - 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < p ^ (s - 1) := pow_pos hp _
  have hpow : p ^ s = p ^ (s - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have hsub : p ^ (s - 1) * p - 1 + 1 = p ^ (s - 1) * p :=
    Nat.sub_add_cancel (Nat.mul_pos hq hp)
  rcases hd with rfl | rfl
  · have hc := (c 0).isLt
    simp only [totalDegree, Fin.sum_univ_one, one_mul] at hr ⊢
    simp only [splitExponent]
    rw [hpow]
    have hupper := Nat.mul_le_mul_left (p ^ (s - 1))
      (show 2 * (r 0).val + 2 ≤ p by omega)
    nlinarith
  · have hc0 := (c 0).isLt
    have hc1 := (c 1).isLt
    simp [totalDegree, Fin.sum_univ_two] at hr ⊢
    simp only [splitExponent]
    rw [hpow]
    have hupper := Nat.mul_le_mul_left (p ^ (s - 1))
      (show (r 0).val + (r 1).val + 2 ≤ p by omega)
    nlinarith

/-- [RW-rec, Lemma 1]: partial Lucas rewrites a global split-index moment as
Pascal tensor multiplication of the small-coset binomial moments. -/
theorem globalBinomialMoment_split {p s d : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p] (hs : 1 ≤ s)
    (f : Point p s d → k) (c : CosetBase p s d) (r : CosetCoordinate p d) :
    globalBinomialMoment f (splitExponent c r) =
      (tensorPascalMatrix k d (p ^ (s - 1))).mulVec
        (fun b => cosetBinomialMoment f b r) c := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow : p ^ s = p ^ (s - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have hval (b : CosetBase p s d) (u : CosetCoordinate p d) (i : Fin d) :
      (cosetPoint b u i).val = (b i).val + p ^ (s - 1) * (u i).val := by
    apply ZMod.val_natCast_of_lt
    rw [hpow]
    have hb := (b i).isLt
    have hu := (u i).isLt
    have hupper := Nat.mul_le_mul_left (p ^ (s - 1)) (show (u i).val + 1 ≤ p by omega)
    nlinarith
  unfold globalBinomialMoment
  rw [← (cosetPoint_bijective (p := p) (s := s) (d := d) hs).sum_comp
    (fun x => f x * binomialWeight k (fun i => (x i).val) (splitExponent c r))]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mulVec, dotProduct, cosetBinomialMoment, tensorPascalMatrix,
    pascalMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro u _
  simp only [binomialWeight, splitExponent, hval]
  simp_rw [partialLucas hs (b _).isLt (c _).isLt (u _).isLt (r _).isLt]
  rw [Finset.prod_mul_distrib]
  ring

/-- [RW-rec, Lemma 1]: global low binomial vanishing separates into binomial
vanishing on each individual `H[p]`-coset. -/
theorem cosetBinomialMoment_eq_zero {p s d : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    (hs : 1 ≤ s) (hd : d = 1 ∨ d = 2) (f : Point p s d → k)
    (hglobal : ∀ j : Fin d → ℕ,
      2 * totalDegree j < d * (p ^ s - 1) → globalBinomialMoment f j = 0)
    (b : CosetBase p s d) (r : CosetCoordinate p d)
    (hr : 2 * totalDegree (fun i => (r i).val) < d * (p - 1)) :
    cosetBinomialMoment f b r = 0 := by
  have hvec : (tensorPascalMatrix k d (p ^ (s - 1))).mulVec
      (fun b => cosetBinomialMoment f b r) =
      (tensorPascalMatrix k d (p ^ (s - 1))).mulVec 0 := by
    funext c
    rw [Matrix.mulVec_zero, Pi.zero_apply, ← globalBinomialMoment_split hs]
    exact hglobal _ (splitExponent_degree_lt hs hd c r hr)
  have hzero := tensorPascalMatrix_mulVec_injective k d (p ^ (s - 1)) hvec
  exact congrFun hzero b

/-- [RW-rec, Lemma 1]: the triangular binomial-to-monomial change of basis
preserves any strict total-degree cutoff below the coordinatewise `p` bounds. -/
theorem monomial_moment_eq_zero_of_binomial {p d : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    (g : CosetCoordinate p d → k) (B : ℕ)
    (hbinomial : ∀ r : CosetCoordinate p d,
      2 * totalDegree (fun i => (r i).val) < B →
        ∑ u, g u * binomialWeight k (fun i => (u i).val) (fun i => (r i).val) = 0)
    (j : Fin d → ℕ) (hj : ∀ i, j i < p) (hdegree : 2 * totalDegree j < B) :
    ∑ u, g u * monomialWeight k (fun i => ((u i).val : k)) j = 0 := by
  classical
  unfold monomialWeight
  refine SICLean.L5.FiniteCosetMomentsAux.monomial_moment_of_binomial_box
    (fun u i => (u i).val) g j ?_
  intro r hr
  let rb : CosetCoordinate p d := fun i => ⟨r i, lt_of_le_of_lt (hr i) (hj i)⟩
  have hrdegree : 2 * totalDegree (fun i => (rb i).val) < B := by
    apply lt_of_le_of_lt _ hdegree
    exact Nat.mul_le_mul_left 2 (Finset.sum_le_sum (fun i _ => hr i))
  simpa only [rb, binomialWeight] using hbinomial rb hrdegree

/-- [RW-rec, (14)]: the finite-algebra statement from global low
binomial vanishing to every low monomial moment on every small coset. -/
theorem cosetMonomialMoment_eq_zero {p s d : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    (hs : 1 ≤ s) (hd : d = 1 ∨ d = 2) (f : Point p s d → k)
    (hglobal : ∀ j : Fin d → ℕ,
      2 * totalDegree j < d * (p ^ s - 1) → globalBinomialMoment f j = 0)
    (b : CosetBase p s d) (j : Fin d → ℕ)
    (hj : 2 * totalDegree j < d * (p - 1)) :
    cosetMonomialMoment f b j = 0 := by
  classical
  have hbound (i : Fin d) : j i < p := by
    have hle : j i ≤ totalDegree j := Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hp := (Fact.out : p.Prime).pos
    rcases hd with rfl | rfl
    · simp only [one_mul] at hj
      omega
    · omega
  exact monomial_moment_eq_zero_of_binomial (fun u => f (cosetPoint b u))
    (d * (p - 1)) (fun r hr => cosetBinomialMoment_eq_zero hs hd f hglobal b r hr)
    j hbound hj

/-- [RW-rec, Lemma 1]: linearity gives vanishing against every polynomial over
the full coefficient field `k` below the strict small-coset degree cutoff. -/
theorem coset_polynomial_moment_eq_zero {p s d : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    (hs : 1 ≤ s) (hd : d = 1 ∨ d = 2) (f : Point p s d → k)
    (hglobal : ∀ j : Fin d → ℕ,
      2 * totalDegree j < d * (p ^ s - 1) → globalBinomialMoment f j = 0)
    (b : CosetBase p s d) (P : MvPolynomial (Fin d) k)
    (hP : 2 * P.totalDegree < d * (p - 1)) :
    ∑ u : CosetCoordinate p d,
      f (cosetPoint b u) * MvPolynomial.eval (fun i => ((u i).val : k)) P = 0 := by
  classical
  simp_rw [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hmdegree : totalDegree (fun i => m i) ≤ P.totalDegree := by
    change (∑ i, m i) ≤ P.totalDegree
    rw [← Finsupp.sum_fintype m (fun _ e => e) (fun _ => rfl)]
    exact MvPolynomial.le_totalDegree hm
  have hmoment := cosetMonomialMoment_eq_zero hs hd f hglobal b (fun i => m i)
    (show 2 * totalDegree (fun i => m i) < d * (p - 1) by omega)
  calc
    (∑ u : CosetCoordinate p d, f (cosetPoint b u) *
        (P.coeff m * ∏ i, ((u i).val : k) ^ m i)) =
        P.coeff m * cosetMonomialMoment f b (fun i => m i) := by
      simp only [cosetMonomialMoment, monomialWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = 0 := by rw [hmoment, mul_zero]

/-- [RW-rec, Lemma 1]: affine substitution preserves the degree cutoff. This
stronger form permits every matrix over `k`; affine bijections are a special case. -/
theorem coset_affine_polynomial_moment_eq_zero {p s d : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    (hs : 1 ≤ s) (hd : d = 1 ∨ d = 2) (f : Point p s d → k)
    (hglobal : ∀ j : Fin d → ℕ,
      2 * totalDegree j < d * (p ^ s - 1) → globalBinomialMoment f j = 0)
    (b : CosetBase p s d) (A : Matrix (Fin d) (Fin d) k) (v : Fin d → k)
    (P : MvPolynomial (Fin d) k) (hP : 2 * P.totalDegree < d * (p - 1)) :
    ∑ u : CosetCoordinate p d,
      f (cosetPoint b u) *
        MvPolynomial.eval (A.mulVec (fun i => ((u i).val : k)) + v) P = 0 := by
  classical
  let q : Fin d → MvPolynomial (Fin d) k := fun i =>
    (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) + MvPolynomial.C (v i)
  let Q : MvPolynomial (Fin d) k := MvPolynomial.eval₂Hom MvPolynomial.C q P
  have hq (i : Fin d) : (q i).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro j _
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · simp
  have hQ : Q.totalDegree ≤ P.totalDegree := by
    change (MvPolynomial.eval₂ MvPolynomial.C q P).totalDegree ≤ P.totalDegree
    rw [MvPolynomial.eval₂_eq']
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc
      (∑ i, (q i ^ m i).totalDegree) ≤ ∑ i, m i := by
        apply Finset.sum_le_sum
        intro i _
        exact (MvPolynomial.totalDegree_pow _ _).trans
          (by simpa using Nat.mul_le_mul_left (m i) (hq i))
      _ ≤ P.totalDegree := by
        rw [← Finsupp.sum_fintype m (fun _ e => e) (fun _ => rfl)]
        exact MvPolynomial.le_totalDegree hm
  have heval (x : Fin d → k) :
      MvPolynomial.eval x Q = MvPolynomial.eval (A.mulVec x + v) P := by
    change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C q P) = _
    rw [← MvPolynomial.eval_assoc]
    apply congrArg (fun y : Fin d → k => MvPolynomial.eval y P)
    funext i
    simp [q, Matrix.mulVec, dotProduct]
  have hQcut : 2 * Q.totalDegree < d * (p - 1) := by omega
  have hmoment := coset_polynomial_moment_eq_zero hs hd f hglobal b Q hQcut
  simpa only [heval] using hmoment

end SICLean.L5.FiniteCosetMoments
