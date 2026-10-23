import SICLean.L4.ModularPhi
import SICLean.L4.ModularDivisorAuxA

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The actual Φ divisor and fixed-point lattice values

The file treats both label bijections, the affine pullback,
divisor-index finiteness, divisor disjointness, the multiplicity pullback,
the exact order, simplicity for nonreal parameters, the no-pole/regular
domain identity, joint analyticity off poles, the nonzero criterion, the
pole value convention, the common-zero center, the Möbius lattice relation,
and fixed-point irrationality, together with exact branch formulas,
multiplicities, and common-zero factorization. The explicit definitions
use the same `modularPhi`, `phiExtended`, principal square root and actual
`etaMultiplier`. No analytic or meromorphic property is a field
or a defining condition.

[RW26, p. 6]
(divisor and (19)); [RW26, p. 12, Lemma 2, Theorem 2].
Multiplicities are recorded with the divisor. [RW26, p. 6, Lemma 2].

The branch families retain labels. `Nat.card` is used together with the
separate finiteness theorem. Nonreal parameters give simple branches;
rational positive real parameters can merge branches, and their orders add.
The slit-plane domain excludes collisions between a pole and a zero.
Regular loci below are specified only by explicit index counts.

Germ conventions: orders and q-quotient comparisons use fixed-τ punctured
complex germs. We never identify two-variable meromorphic functions by
deleting only the center of ℂ²: their polar curves would remain. Joint
statements are analytic neighborhoods, explicit local factorizations, or
cross products. Pointwise assertions concern the specified finite
product, whose value at a pole is 0 by total division. A removable raw
q-quotient need not have that raw quotient's center value.

The elementary common-zero factor is explicitly regularized, separately
from the raw quotient. Its moving coordinate is ζ=z-kτ-l, not z-z₀.
Actual lattice center values are theorems about `modularPhi`, not a new
definition of Φ. Their hypotheses keep c>0, trace>2, a real fixed point,
positive automorphy factor and equality of the two lattice exponents.
Both attracting and repelling fixed points are covered.

Downstream files use joint unit neighborhoods, lattice centers and
ordinary joint limits. The proof uses compact parameter finiteness, exact orders
(including merged branches), and separation from the actual divisor.
No neighborhood avoiding the whole dense real pseudolattice is asserted.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane Classical

namespace SICLean.L4

/-! ## Concrete divisor labels and branches -/

/-- Admissible labels (K,J) of the poles, including repeated locations. -/
def modularPhiPoleLabels (M : SL(2, ℤ)) (m n : ℤ) : Set (ℕ × ℕ) :=
  {p | Int.ModEq (M 1 0) ((p.2 : ℤ) + M 1 1 * (p.1 : ℤ))
    (M 1 1 * (m - 1) - n)}

/-- Admissible labels (K,J) of the zeros, including repeated locations. -/
def modularPhiZeroLabels (M : SL(2, ℤ)) (m n : ℤ) : Set (ℕ × ℕ) :=
  {p | Int.ModEq (M 1 0) ((p.2 : ℤ) + M 1 1 * (p.1 : ℤ))
    (n - 1 - M 1 1 * m)}

/-- The pole with label (K,J): the same affine branch for real and complex τ. -/
def modularPhiPolePoint (M : SL(2, ℤ)) (m n : ℤ) (τ : ℂ) (K J : ℕ) : ℂ :=
  ((n : ℂ) - ((m : ℂ) - 1) * etaDenom M τ +
    (K : ℂ) * etaDenom M τ + (J : ℂ)) / (M 1 0 : ℂ)

/-- The zero with label (K,J): the same affine branch for real and complex τ. -/
def modularPhiZeroPoint (M : SL(2, ℤ)) (m n : ℤ) (τ : ℂ) (K J : ℕ) : ℂ :=
  ((n : ℂ) - 1 - (m : ℂ) * etaDenom M τ -
    (K : ℂ) * etaDenom M τ - (J : ℂ)) / (M 1 0 : ℂ)

def modularPhiPoleIndices (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : Set (ℕ × ℕ) :=
  {p | p ∈ modularPhiPoleLabels M m n ∧ z = modularPhiPolePoint M m n τ p.1 p.2}

def modularPhiZeroIndices (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : Set (ℕ × ℕ) :=
  {p | p ∈ modularPhiZeroLabels M m n ∧ z = modularPhiZeroPoint M m n τ p.1 p.2}

/-- Meaningful after `modularPhiDivisor_indices_finite`. It counts labels, not locations. -/
def modularPhiPoleMultiplicity (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℕ :=
  Nat.card (modularPhiPoleIndices M m n z τ)

def modularPhiZeroMultiplicity (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℕ :=
  Nat.card (modularPhiZeroIndices M m n z τ)

/-- Mathlib sign: zeros positive and poles negative. -/
def modularPhiDivisorOrder (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℤ :=
  (modularPhiZeroMultiplicity M m n z τ : ℤ) -
    (modularPhiPoleMultiplicity M m n z τ : ℤ)

/-- Explicit reindexing of the j-th φ pole (u,v). Only j<c is used. -/
def modularPhiPoleFactorLabel (M : SL(2, ℤ)) (m n : ℤ) (j u v : ℕ) : ℕ × ℕ :=
  ((M 1 0).toNat * u + ((M 1 0).toNat - 1 - j),
    (M 1 0).toNat * v + (modularPhiResidue M m n j).toNat)

/-- Explicit reindexing of the j-th φ zero (u,v). Only j<c is used. -/
def modularPhiZeroFactorLabel (M : SL(2, ℤ)) (m n : ℤ) (j u v : ℕ) : ℕ × ℕ :=
  ((M 1 0).toNat * u + j,
    (M 1 0).toNat * v + ((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat))

/-- Explicit no-pole locus. Zeros are included. -/
def modularPhiHolomorphicDomain (M : SL(2, ℤ)) (m n : ℤ) : Set (ℂ × ℂ) :=
  {p | p.2 ∈ modularPhiDomain M ∧ modularPhiPoleMultiplicity M m n p.1 p.2 = 0}

/-- Explicit complement of both divisor families, with no regularity assumed. -/
def modularPhiNonvanishingDomain (M : SL(2, ℤ)) (m n : ℤ) : Set (ℂ × ℂ) :=
  {p | p.2 ∈ modularPhiDomain M ∧ modularPhiPoleMultiplicity M m n p.1 p.2 = 0 ∧
    modularPhiZeroMultiplicity M m n p.1 p.2 = 0}

/-- This can be dense for real irrational τ; it is not the actual divisor. -/
def modularPhiPseudoLattice (τ : ℂ) : Set ℂ :=
  {z | ∃ k l : ℤ, z = (k : ℂ) * τ + (l : ℂ)}

/-! # A concrete common-zero factor for Φ -/

/--
Explicit removable representative.
The raw total quotient has value 0 at ζ=0; this function assigns T there.
Analyticity and agreement with the actual Φ are separate theorems below.
-/
def modularPhiCommonZeroFactor (ζ T : ℂ) : ℂ :=
  if ζ = 0 then T else (1 - e ζ) / (1 - e (ζ / T))

/--
q tail with its unique zero term removed when r≤0. The omitted term
has index -r. Defined by finite products and the same `qPochhammer`.
For r≥1 no term is removed. No claim is made for real-τ q products.
-/
def modularPhiLatticeQTail (r : ℤ) (ζ q : ℂ) : ℂ :=
  if 1 ≤ r then qPochhammer (q ^ r * e ζ) q
  else qPochhammerNat (q ^ r * e ζ) q (-r).toNat * qPochhammer (q * e ζ) q

/-- The remaining q quotient after removal of the possible common zero.
Its local nonvanishing is proved only in the upper-half-plane theorem. -/
def modularPhiLatticeQRegularPart (M : SL(2, ℤ)) (r : ℤ) (ζ τ : ℂ) : ℂ :=
  modularPhiLatticeQTail r ζ (e τ) /
    modularPhiLatticeQTail r (ζ / etaDenom M τ) (e (etaMobius M τ))

/-- Explicit upper-half-plane lattice evaluator. This is not Φ's
definition, nor a q-product prescription at a real parameter. -/
def modularPhiLatticeQValue (M : SL(2, ℤ)) (r : ℤ) (τ : ℂ) : ℂ :=
  (if 1 ≤ r then 1 else etaDenom M τ) * modularPhiLatticeQRegularPart M r 0 τ

/-! ## Helper lemmas (arithmetic reindexing and affine pullback) -/

section DivisorHelpers

lemma divisorC_pos (M : SL(2, ℤ)) (hM : 0 < M 1 0) : 0 < (M 1 0).toNat := by
  omega

lemma divisorC_cast (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    (((M 1 0).toNat : ℕ) : ℤ) = M 1 0 :=
  Int.toNat_of_nonneg hM.le

lemma residue_nonneg (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (j : ℕ) :
    0 ≤ modularPhiResidue M m n j :=
  (modularPhiResidue_permutation M hM m n).1 j |>.1

lemma residue_lt (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (j : ℕ) :
    modularPhiResidue M m n j < M 1 0 :=
  (modularPhiResidue_permutation M hM m n).1 j |>.2

lemma residue_cast_toNat_int (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (j : ℕ) :
    ((modularPhiResidue M m n j).toNat : ℤ) = modularPhiResidue M m n j :=
  Int.toNat_of_nonneg (residue_nonneg M hM m n j)

lemma residue_cast_toNat (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (j : ℕ) :
    ((modularPhiResidue M m n j).toNat : ℂ) = (modularPhiResidue M m n j : ℂ) := by
  rw [show ((modularPhiResidue M m n j).toNat : ℂ) =
    (((modularPhiResidue M m n j).toNat : ℤ) : ℂ) by push_cast; ring]
  rw [residue_cast_toNat_int M hM m n j]

lemma residue_toNat_lt (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (j : ℕ) :
    (modularPhiResidue M m n j).toNat < (M 1 0).toNat := by
  have h := residue_lt M hM m n j
  omega

lemma residue_key (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) :
    M 1 1 * (m + (j : ℤ)) - n =
      M 1 0 * modularPhiIndex M m n j + modularPhiResidue M m n j := by
  unfold modularPhiResidue
  ring

lemma residue_key_complex (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) :
    (M 1 1 : ℂ) * ((m : ℂ) + (j : ℂ)) - (n : ℂ) =
      (M 1 0 : ℂ) * (modularPhiIndex M m n j : ℂ) +
        (modularPhiResidue M m n j : ℂ) := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (residue_key M m n j)
  push_cast at h
  exact h

lemma cast_c_sub_one_sub (M : SL(2, ℤ)) (hM : 0 < M 1 0) {j : ℕ}
    (hj : j < (M 1 0).toNat) :
    (((M 1 0).toNat - 1 - j : ℕ) : ℂ) =
      ((M 1 0).toNat : ℂ) - 1 - (j : ℂ) := by
  have hc : 1 ≤ (M 1 0).toNat := divisorC_pos M hM
  have hj1 : j ≤ (M 1 0).toNat - 1 := by omega
  rw [Nat.cast_sub hj1, Nat.cast_sub hc]
  push_cast
  ring

lemma residue_complement (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (j : ℕ) :
    ((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat) +
        (modularPhiResidue M m n j).toNat = (M 1 0).toNat - 1 := by
  have h := residue_toNat_lt M hM m n j
  omega

lemma residue_complement_cast (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (j : ℕ) :
    (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℂ) +
        ((modularPhiResidue M m n j).toNat : ℂ) = ((M 1 0).toNat : ℂ) - 1 := by
  have hc : 1 ≤ (M 1 0).toNat := divisorC_pos M hM
  have h' := congrArg (fun z : ℕ => (z : ℂ)) (residue_complement M hM m n j)
  push_cast at h'
  rw [Nat.cast_sub hc] at h'
  simpa using h'

lemma cast_c_sub_one_sub_residue (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (j : ℕ) :
    (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℂ) =
      ((M 1 0).toNat : ℂ) - 1 - (modularPhiResidue M m n j : ℂ) := by
  have hc : 1 ≤ (M 1 0).toNat := divisorC_pos M hM
  have hr : (modularPhiResidue M m n j).toNat ≤ (M 1 0).toNat - 1 := by
    have := residue_toNat_lt M hM m n j; omega
  rw [Nat.cast_sub hr, Nat.cast_sub hc, residue_cast_toNat M hM m n j]
  push_cast
  ring

/-! ### Affine algebra at the level of complex numbers -/

lemma pole_point_algebra (cC dC T τ : ℂ) (hc : cC ≠ 0) (hT : T = cC * τ + dC)
    (mC nC : ℂ) (u v j : ℕ) (idx res : ℂ)
    (hkey : dC * (mC + (j : ℂ)) - nC = cC * idx + res) :
    (nC - (mC - 1) * T + (((u : ℂ) * cC + (cC - 1 - (j : ℂ))) * T +
      ((v : ℂ) * cC + res))) / cC + (mC + (j : ℂ)) * τ + idx =
      ((u : ℂ) + 1) * T + (v : ℂ) := by
  rw [show (nC - (mC - 1) * T + (((u : ℂ) * cC + (cC - 1 - (j : ℂ))) * T +
      ((v : ℂ) * cC + res))) / cC =
      ((u : ℂ) + 1) * T + (v : ℂ) - ((mC + (j : ℂ)) * τ + idx) from ?_]
  · ring
  rw [div_eq_iff hc]
  rw [hT] at ⊢
  linear_combination -hkey

lemma zero_point_algebra (cC dC T τ : ℂ) (hc : cC ≠ 0) (hT : T = cC * τ + dC)
    (mC nC : ℂ) (u v j : ℕ) (idx res comp : ℂ)
    (hkey : dC * (mC + (j : ℂ)) - nC = cC * idx + res)
    (hcomp : comp + res = cC - 1) :
    (nC - 1 - mC * T - ((u : ℂ) * cC + (j : ℂ)) * T -
      ((v : ℂ) * cC + comp)) / cC + (mC + (j : ℂ)) * τ + idx =
      -((u : ℂ) * T + (v : ℂ) + 1) := by
  rw [show (nC - 1 - mC * T - ((u : ℂ) * cC + (j : ℂ)) * T -
      ((v : ℂ) * cC + comp)) / cC =
      -((u : ℂ) * T + (v : ℂ) + 1) - ((mC + (j : ℂ)) * τ + idx) from ?_]
  · ring
  rw [div_eq_iff hc]
  rw [hT] at ⊢
  linear_combination -hkey - hcomp

lemma pole_input_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (τ : ℂ)
    (j u v : ℕ) (hj : j < (M 1 0).toNat) :
    modularPhiPolePoint M m n τ
        ((M 1 0).toNat * u + ((M 1 0).toNat - 1 - j))
        ((M 1 0).toNat * v + (modularPhiResidue M m n j).toNat) +
      ((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ) =
      ((u : ℂ) + 1) * etaDenom M τ + (v : ℂ) := by
  have hcC : ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast divisorC_cast M hM
  have hcne : (M 1 0 : ℂ) ≠ 0 := by
    have h : (M 1 0 : ℤ) ≠ 0 := hM.ne'
    exact_mod_cast h
  simp only [modularPhiPolePoint]
  push_cast
  rw [cast_c_sub_one_sub M hM hj, residue_cast_toNat M hM m n j, hcC]
  simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm] using
    (pole_point_algebra (cC := (M 1 0 : ℂ)) (dC := (M 1 1 : ℂ))
      (T := etaDenom M τ) (τ := τ) hcne rfl (u := u) (v := v) (j := j)
      (mC := (m : ℂ)) (nC := (n : ℂ))
      (idx := (modularPhiIndex M m n j : ℂ)) (res := (modularPhiResidue M m n j : ℂ))
      (residue_key_complex M m n j))

lemma zero_input_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (τ : ℂ)
    (j u v : ℕ) (hj : j < (M 1 0).toNat) :
    modularPhiZeroPoint M m n τ
        ((M 1 0).toNat * u + j)
        ((M 1 0).toNat * v +
          ((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat)) +
      ((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ) =
      -((u : ℂ) * etaDenom M τ + (v : ℂ) + 1) := by
  have hcC : ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast divisorC_cast M hM
  have hcne : (M 1 0 : ℂ) ≠ 0 := by
    have h : (M 1 0 : ℤ) ≠ 0 := hM.ne'
    exact_mod_cast h
  have hcompC : (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℂ) +
      (modularPhiResidue M m n j : ℂ) = (M 1 0 : ℂ) - 1 := by
    have h := residue_complement_cast M hM m n j
    rw [residue_cast_toNat M hM m n j, hcC] at h
    exact h
  simp only [modularPhiZeroPoint]
  push_cast
  rw [hcC]
  simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm] using
    (zero_point_algebra (cC := (M 1 0 : ℂ)) (dC := (M 1 1 : ℂ))
      (T := etaDenom M τ) (τ := τ) hcne rfl (u := u) (v := v) (j := j)
      (mC := (m : ℂ)) (nC := (n : ℂ))
      (idx := (modularPhiIndex M m n j : ℂ)) (res := (modularPhiResidue M m n j : ℂ))
      (comp := (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℂ))
      (residue_key_complex M m n j) hcompC)

lemma sArgument_eq_phiPolePoint (T : ℂ) (hT : T ≠ 0) (u v : ℕ) :
    modularPhiSArgument T (((u : ℂ) + 1) * T + (v : ℂ)) =
      phiPolePoint (Complex.sqrt T) u v := by
  set b := Complex.sqrt T with hbdef
  have hb2 : b * b = T := by rw [hbdef]; exact EtaMultiplierAux.sqrt_mul_self T
  have hbne : b ≠ 0 := by
    intro h; rw [h] at hb2; simp at hb2; exact hT hb2.symm
  simp only [modularPhiSArgument]
  rw [← hbdef, ← hb2]
  unfold phiPolePoint
  field_simp
  ring

lemma sArgument_eq_phiZeroPoint (T : ℂ) (hT : T ≠ 0) (u v : ℕ) :
    modularPhiSArgument T (-((u : ℂ) * T + (v : ℂ) + 1)) =
      phiZeroPoint (Complex.sqrt T) u v := by
  set b := Complex.sqrt T with hbdef
  have hb2 : b * b = T := by rw [hbdef]; exact EtaMultiplierAux.sqrt_mul_self T
  have hbne : b ≠ 0 := by
    intro h; rw [h] at hb2; simp at hb2; exact hT hb2.symm
  simp only [modularPhiSArgument]
  rw [← hbdef, ← hb2]
  unfold phiZeroPoint phiPolePoint
  field_simp
  ring

theorem modularPhi_factor_divisor_pullback_aux (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (j u v : ℕ) (hj : j < (M 1 0).toNat) :
    let p := modularPhiPoleFactorLabel M m n j u v
    let q := modularPhiZeroFactorLabel M m n j u v
    (modularPhiFactorPoint M m n j (modularPhiPolePoint M m n τ p.1 p.2) τ).2 =
        phiPolePoint (Complex.sqrt (etaDenom M τ)) u v ∧
      (modularPhiFactorPoint M m n j (modularPhiZeroPoint M m n τ q.1 q.2) τ).2 =
        phiZeroPoint (Complex.sqrt (etaDenom M τ)) u v := by
  dsimp only
  have hT : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hτ
  constructor
  · show modularPhiSArgument (etaDenom M τ)
        (modularPhiFactorInput M m n j
          (modularPhiPolePoint M m n τ
            ((M 1 0).toNat * u + ((M 1 0).toNat - 1 - j))
            ((M 1 0).toNat * v + (modularPhiResidue M m n j).toNat)) τ) =
      phiPolePoint (Complex.sqrt (etaDenom M τ)) u v
    rw [show modularPhiFactorInput M m n j
          (modularPhiPolePoint M m n τ
            ((M 1 0).toNat * u + ((M 1 0).toNat - 1 - j))
            ((M 1 0).toNat * v + (modularPhiResidue M m n j).toNat)) τ =
        ((u : ℂ) + 1) * etaDenom M τ + (v : ℂ) from by
      simpa only [modularPhiFactorInput] using pole_input_eq M hM m n τ j u v hj]
    exact sArgument_eq_phiPolePoint _ hT u v
  · show modularPhiSArgument (etaDenom M τ)
        (modularPhiFactorInput M m n j
          (modularPhiZeroPoint M m n τ
            ((M 1 0).toNat * u + j)
            ((M 1 0).toNat * v +
              ((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat))) τ) =
      phiZeroPoint (Complex.sqrt (etaDenom M τ)) u v
    rw [show modularPhiFactorInput M m n j
          (modularPhiZeroPoint M m n τ
            ((M 1 0).toNat * u + j)
            ((M 1 0).toNat * v +
              ((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat))) τ =
        -((u : ℂ) * etaDenom M τ + (v : ℂ) + 1) from by
      simpa only [modularPhiFactorInput] using zero_input_eq M hM m n τ j u v hj]
    exact sArgument_eq_phiZeroPoint _ hT u v

theorem modularPhiCommonZeroFactor_zero_aux (T : ℂ) :
    modularPhiCommonZeroFactor 0 T = T := by
  simp [modularPhiCommonZeroFactor]

lemma mobius_algebra (a b c d τ k l : ℂ) (hden : c*τ+d ≠ 0)
    (hdet : a*d - b*c = 1) :
    (k*τ+l)/(c*τ+d) = (d*k - c*l)*((a*τ+b)/(c*τ+d)) + (a*l - b*k) := by
  have hnum : (d*k - c*l)*(a*τ+b) + (a*l-b*k)*(c*τ+d) = k*τ+l := by
    linear_combination (k*τ+l) * hdet
  rw [← hnum]
  field_simp

theorem modularPhi_lattice_mobius_aux (M : SL(2, ℤ)) (k l : ℤ) (τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M) :
    ((k : ℂ) * τ + (l : ℂ)) / etaDenom M τ =
      ((M 1 1 * k - M 1 0 * l : ℤ) : ℂ) * etaMobius M τ +
        ((M 0 0 * l - M 0 1 * k : ℤ) : ℂ) := by
  have hT : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hτ
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by
    exact_mod_cast det_coe_int M
  rw [etaMobius]
  rw [show etaDenom M τ = (M 1 0 : ℂ) * τ + (M 1 1 : ℂ) from rfl]
  push_cast
  exact mobius_algebra _ _ _ _ _ _ _ hT hdet


lemma pole_label_mem (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (u v j : ℕ) (hj : j < (M 1 0).toNat) :
    modularPhiPoleFactorLabel M m n j u v ∈ modularPhiPoleLabels M m n := by
  simp only [modularPhiPoleLabels, modularPhiPoleFactorLabel, Set.mem_setOf_eq]
  rw [Int.modEq_iff_dvd]
  refine ⟨modularPhiIndex M m n j - (v : ℤ) - M 1 1 * (u : ℤ) - M 1 1, ?_⟩
  have hc : 1 ≤ (M 1 0).toNat := divisorC_pos M hM
  have hj1 : j ≤ (M 1 0).toNat - 1 := by omega
  have hkj : (((M 1 0).toNat - 1 - j : ℕ) : ℤ) =
      ((M 1 0).toNat : ℤ) - 1 - (j : ℤ) := by
    rw [Nat.cast_sub hj1, Nat.cast_sub hc]; push_cast; ring
  have hres : ((modularPhiResidue M m n j).toNat : ℤ) = modularPhiResidue M m n j :=
    residue_cast_toNat_int M hM m n j
  push_cast
  rw [hkj, hres, divisorC_cast M hM]
  simp only [modularPhiResidue, modularPhiIndex]
  ring

lemma pole_label_mem_res (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (u j : ℕ) (hj : j < (M 1 0).toNat) :
    Int.ModEq (M 1 0)
      ((modularPhiResidue M m n j).toNat + M 1 1 *
        ((((M 1 0).toNat * u + ((M 1 0).toNat - 1 - j) : ℕ)) : ℤ))
      (M 1 1 * (m - 1) - n) := by
  rw [Int.modEq_iff_dvd]
  refine ⟨modularPhiIndex M m n j - M 1 1 * (u : ℤ) - M 1 1, ?_⟩
  have hc : 1 ≤ (M 1 0).toNat := divisorC_pos M hM
  have hj1 : j ≤ (M 1 0).toNat - 1 := by omega
  have hkj : (((M 1 0).toNat - 1 - j : ℕ) : ℤ) =
      ((M 1 0).toNat : ℤ) - 1 - (j : ℤ) := by
    rw [Nat.cast_sub hj1, Nat.cast_sub hc]; push_cast; ring
  have hres : ((modularPhiResidue M m n j).toNat : ℤ) = modularPhiResidue M m n j :=
    residue_cast_toNat_int M hM m n j
  push_cast
  rw [hkj, hres, divisorC_cast M hM]
  simp only [modularPhiResidue, modularPhiIndex]
  ring

lemma modEq_cancel_right (c x y z : ℤ) (h : Int.ModEq c (x + z) (y + z)) :
    Int.ModEq c x y := by
  rw [Int.modEq_iff_dvd] at h ⊢
  rwa [show y - x = (y + z) - (x + z) by ring]

lemma pole_label_inj (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) :
    Set.InjOn (fun p : ℕ × ℕ × ℕ => modularPhiPoleFactorLabel M m n p.1 p.2.1 p.2.2)
      {p | p.1 < (M 1 0).toNat} := by
  rintro ⟨j, u, v⟩ hj ⟨j', u', v'⟩ hj' heq
  simp only [Set.mem_ofPred_eq] at hj hj'
  have hc : 0 < (M 1 0).toNat := divisorC_pos M hM
  have hkj : (((M 1 0).toNat - 1 - j : ℕ) : ℤ) =
      ((M 1 0).toNat : ℤ) - 1 - (j : ℤ) := by omega
  have hkj' : (((M 1 0).toNat - 1 - j' : ℕ) : ℤ) =
      ((M 1 0).toNat : ℤ) - 1 - (j' : ℤ) := by omega
  have h1n := congrArg Prod.fst heq
  have h2n := congrArg Prod.snd heq
  simp only [modularPhiPoleFactorLabel] at h1n h2n
  have h1 : ((M 1 0).toNat : ℤ) * (u : ℤ) + (((M 1 0).toNat : ℤ) - 1 - (j : ℤ)) =
      ((M 1 0).toNat : ℤ) * (u' : ℤ) + (((M 1 0).toNat : ℤ) - 1 - (j' : ℤ)) := by
    have h := congrArg (fun z : ℕ => (z : ℤ)) h1n
    push_cast at h
    rwa [hkj, hkj'] at h
  have hdvd : ((M 1 0).toNat : ℤ) ∣ ((j : ℤ) - j') := by
    refine ⟨(u : ℤ) - u', by linear_combination -h1⟩
  have hlt : |((j : ℤ) - j')| < ((M 1 0).toNat : ℤ) := by
    rw [abs_lt]; constructor <;> omega
  have hjj : ((j : ℤ) - j') = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  have hjeq : j = j' := by omega
  subst hjeq
  have hueq : u = u' := by
    have h : (M 1 0).toNat * u = (M 1 0).toNat * u' := by omega
    exact Nat.eq_of_mul_eq_mul_left hc h
  have hveq : v = v' := by
    have h : (M 1 0).toNat * v = (M 1 0).toNat * v' := by
      exact Nat.add_right_cancel h2n
    exact Nat.eq_of_mul_eq_mul_left hc h
  subst hueq; subst hveq; rfl

lemma pole_label_surj (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) :
    Set.SurjOn (fun p : ℕ × ℕ × ℕ => modularPhiPoleFactorLabel M m n p.1 p.2.1 p.2.2)
      {p | p.1 < (M 1 0).toNat} (modularPhiPoleLabels M m n) := by
  rintro ⟨K, J⟩ hy
  simp only [modularPhiPoleLabels, Set.mem_setOf_eq] at hy
  set c : ℕ := (M 1 0).toNat with hcdef
  have hc : 0 < c := divisorC_pos M hM
  have hcZ : (c : ℤ) = M 1 0 := divisorC_cast M hM
  set a : ℕ := K % c with hadef
  have ha_lt : a < c := Nat.mod_lt _ hc
  set j : ℕ := c - 1 - a with hjdef
  have hj_lt : j < c := by omega
  set u : ℕ := K / c with hudef
  have hK : K = c * u + a := by
    have h := Nat.div_add_mod K c
    rw [hudef, hadef]
    exact h.symm
  have hja : c - 1 - j = a := by omega
  have hK' : K = c * u + (c - 1 - j) := by rw [hja]; exact hK
  have hmem : Int.ModEq (M 1 0)
      ((modularPhiResidue M m n j).toNat + M 1 1 *
        (((c * u + (c - 1 - j) : ℕ)) : ℤ)) (M 1 1 * (m - 1) - n) := by
    have := pole_label_mem_res M hM m n u j (by simpa [hcdef] using hj_lt)
    simpa [hcdef] using this
  have hyK : Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (((c * u + (c - 1 - j) : ℕ)) : ℤ))
      (M 1 1 * (m - 1) - n) := by
    have h := hy
    rw [hK'] at h
    exact h
  have hcancel : Int.ModEq (M 1 0) (J : ℤ) ((modularPhiResidue M m n j).toNat : ℤ) := by
    have h := hyK.trans hmem.symm
    exact modEq_cancel_right (M 1 0) (J : ℤ) ((modularPhiResidue M m n j).toNat : ℤ)
      (M 1 1 * (((c * u + (c - 1 - j) : ℕ)) : ℤ)) h
  have hres_lt : ((modularPhiResidue M m n j).toNat : ℤ) < (c : ℤ) := by
    exact_mod_cast residue_toNat_lt M hM m n j
  have hres_nn : (0:ℤ) ≤ ((modularPhiResidue M m n j).toNat : ℤ) := by positivity
  have hcancel' : Int.ModEq (c : ℤ) (J : ℤ) ((modularPhiResidue M m n j).toNat : ℤ) := by
    rw [hcZ]; exact hcancel
  have heq : (J : ℤ) % (c : ℤ) = ((modularPhiResidue M m n j).toNat : ℤ) := by
    have h := hcancel'.eq
    rwa [Int.emod_eq_of_lt hres_nn hres_lt] at h
  have hJmod : J % c = (modularPhiResidue M m n j).toNat := by
    have h1 : ((J % c : ℕ) : ℤ) = ((J : ℤ) % (c : ℤ)) := Int.natCast_emod J c
    have h2 : ((J % c : ℕ) : ℤ) = ((modularPhiResidue M m n j).toNat : ℤ) := by rw [h1, heq]
    exact_mod_cast h2
  refine ⟨(j, u, J / c), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]; simpa [hcdef] using hj_lt
  · simp only [modularPhiPoleFactorLabel]
    apply Prod.ext
    · show c * u + (c - 1 - j) = K
      rw [hK']
    · show c * (J / c) + (modularPhiResidue M m n j).toNat = J
      rw [← hJmod]
      exact Nat.div_add_mod J c

lemma zero_label_mem (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (u v j : ℕ) (hj : j < (M 1 0).toNat) :
    modularPhiZeroFactorLabel M m n j u v ∈ modularPhiZeroLabels M m n := by
  simp only [modularPhiZeroLabels, modularPhiZeroFactorLabel, Set.mem_ofPred_eq]
  rw [Int.modEq_iff_dvd]
  refine ⟨-(modularPhiIndex M m n j) - (v : ℤ) - 1 - M 1 1 * (u : ℤ), ?_⟩
  have hc : 1 ≤ (M 1 0).toNat := divisorC_pos M hM
  have hr : (modularPhiResidue M m n j).toNat ≤ (M 1 0).toNat - 1 := by
    have := residue_toNat_lt M hM m n j; omega
  have hcomp : (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℤ) =
      ((M 1 0).toNat : ℤ) - 1 - ((modularPhiResidue M m n j).toNat : ℤ) := by omega
  have hres : ((modularPhiResidue M m n j).toNat : ℤ) = modularPhiResidue M m n j :=
    residue_cast_toNat_int M hM m n j
  push_cast
  rw [hcomp, hres, divisorC_cast M hM]
  simp only [modularPhiResidue, modularPhiIndex]
  ring

lemma zero_label_mem_res (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (u j : ℕ) (hj : j < (M 1 0).toNat) :
    Int.ModEq (M 1 0)
      ((((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ)) + M 1 1 *
        ((((M 1 0).toNat * u + j : ℕ)) : ℤ))
      (n - 1 - M 1 1 * m) := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-(modularPhiIndex M m n j) - M 1 1 * (u : ℤ) - 1, ?_⟩
  have hc : 1 ≤ (M 1 0).toNat := divisorC_pos M hM
  have hr : (modularPhiResidue M m n j).toNat ≤ (M 1 0).toNat - 1 := by
    have := residue_toNat_lt M hM m n j; omega
  have hcomp : (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℤ) =
      ((M 1 0).toNat : ℤ) - 1 - ((modularPhiResidue M m n j).toNat : ℤ) := by omega
  have hres : ((modularPhiResidue M m n j).toNat : ℤ) = modularPhiResidue M m n j :=
    residue_cast_toNat_int M hM m n j
  push_cast
  rw [hcomp, hres, divisorC_cast M hM]
  simp only [modularPhiResidue, modularPhiIndex]
  ring

lemma zero_label_inj (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) :
    Set.InjOn (fun p : ℕ × ℕ × ℕ => modularPhiZeroFactorLabel M m n p.1 p.2.1 p.2.2)
      {p | p.1 < (M 1 0).toNat} := by
  rintro ⟨j, u, v⟩ hj ⟨j', u', v'⟩ hj' heq
  simp only [Set.mem_ofPred_eq] at hj hj'
  have hc : 0 < (M 1 0).toNat := divisorC_pos M hM
  have h1n := congrArg Prod.fst heq
  have h2n := congrArg Prod.snd heq
  simp only [modularPhiZeroFactorLabel] at h1n h2n
  have h1 : ((M 1 0).toNat : ℤ) * (u : ℤ) + (j : ℤ) =
      ((M 1 0).toNat : ℤ) * (u' : ℤ) + (j' : ℤ) := by
    have h := congrArg (fun z : ℕ => (z : ℤ)) h1n
    push_cast at h
    exact h
  have hdvd : ((M 1 0).toNat : ℤ) ∣ ((j : ℤ) - j') := by
    refine ⟨(u' : ℤ) - u, by linear_combination h1⟩
  have hlt : |((j : ℤ) - j')| < ((M 1 0).toNat : ℤ) := by
    rw [abs_lt]; constructor <;> omega
  have hjj : ((j : ℤ) - j') = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  have hjeq : j = j' := by omega
  subst hjeq
  have hueq : u = u' := by
    have h : (M 1 0).toNat * u = (M 1 0).toNat * u' := by omega
    exact Nat.eq_of_mul_eq_mul_left hc h
  have hveq : v = v' := by
    have h : (M 1 0).toNat * v = (M 1 0).toNat * v' := by
      exact Nat.add_right_cancel h2n
    exact Nat.eq_of_mul_eq_mul_left hc h
  subst hueq; subst hveq; rfl

lemma zero_label_surj (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) :
    Set.SurjOn (fun p : ℕ × ℕ × ℕ => modularPhiZeroFactorLabel M m n p.1 p.2.1 p.2.2)
      {p | p.1 < (M 1 0).toNat} (modularPhiZeroLabels M m n) := by
  rintro ⟨K, J⟩ hy
  simp only [modularPhiZeroLabels, Set.mem_ofPred_eq] at hy
  set c : ℕ := (M 1 0).toNat with hcdef
  have hc : 0 < c := divisorC_pos M hM
  have hcZ : (c : ℤ) = M 1 0 := divisorC_cast M hM
  set a : ℕ := K % c with hadef
  have ha_lt : a < c := Nat.mod_lt _ hc
  set j : ℕ := a with hjdef
  have hj_lt : j < c := by omega
  set u : ℕ := K / c with hudef
  have hK : K = c * u + j := by
    show K = c * (K / c) + K % c
    exact (Nat.div_add_mod K c).symm
  have hmem : Int.ModEq (M 1 0)
      ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) + M 1 1 *
        (((c * u + j : ℕ)) : ℤ)) (n - 1 - M 1 1 * m) := by
    have := zero_label_mem_res M hM m n u j (by simpa [hcdef] using hj_lt)
    simpa [hcdef] using this
  have hyK : Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (((c * u + j : ℕ)) : ℤ))
      (n - 1 - M 1 1 * m) := by
    have h := hy
    rw [show (K : ℤ) = ((c * u + j : ℕ) : ℤ) from by rw [hK]] at h
    exact h
  have hcancel : Int.ModEq (M 1 0) (J : ℤ)
      (((c - 1 - (modularPhiResidue M m n j).toNat : ℕ)) : ℤ) := by
    have h := hyK.trans hmem.symm
    exact modEq_cancel_right (M 1 0) (J : ℤ)
      (((c - 1 - (modularPhiResidue M m n j).toNat : ℕ)) : ℤ)
      (M 1 1 * (((c * u + j : ℕ)) : ℤ)) h
  have hres_nn : (0:ℤ) ≤ (((c - 1 - (modularPhiResidue M m n j).toNat : ℕ)) : ℤ) := by positivity
  have hres_lt : (((c - 1 - (modularPhiResidue M m n j).toNat : ℕ)) : ℤ) < (c : ℤ) := by
    have h := residue_toNat_lt M hM m n j
    have : (c - 1 - (modularPhiResidue M m n j).toNat) < c := by omega
    exact_mod_cast this
  have hcancel' : Int.ModEq (c : ℤ) (J : ℤ)
      (((c - 1 - (modularPhiResidue M m n j).toNat : ℕ)) : ℤ) := by
    rw [hcZ]; exact hcancel
  have heq : (J : ℤ) % (c : ℤ) =
      (((c - 1 - (modularPhiResidue M m n j).toNat : ℕ)) : ℤ) := by
    have h := hcancel'.eq
    rwa [Int.emod_eq_of_lt hres_nn hres_lt] at h
  have hJmod : J % c = (c - 1 - (modularPhiResidue M m n j).toNat) := by
    have h1 : ((J % c : ℕ) : ℤ) = ((J : ℤ) % (c : ℤ)) := Int.natCast_emod J c
    have h2 : ((J % c : ℕ) : ℤ) =
        (((c - 1 - (modularPhiResidue M m n j).toNat : ℕ)) : ℤ) := by rw [h1, heq]
    exact_mod_cast h2
  refine ⟨(j, u, J / c), ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq]; simpa [hcdef] using hj_lt
  · simp only [modularPhiZeroFactorLabel]
    apply Prod.ext
    · show c * u + j = K
      rw [hK]
    · show c * (J / c) + (c - 1 - (modularPhiResidue M m n j).toNat) = J
      rw [← hJmod]
      exact Nat.div_add_mod J c



lemma fiber_finite (T : ℂ) (hT : T ∈ Complex.slitPlane) (C : ℂ) :
    {p : ℕ × ℕ | (p.1 : ℂ) * T + (p.2 : ℂ) = C}.Finite := by
  by_cases him : T.im = 0
  · have hpos : 0 < T.re := by
      rcases Complex.mem_slitPlane_iff.mp hT with h | h
      · exact h
      · exact absurd him h
    have hsub : {p : ℕ × ℕ | (p.1 : ℂ) * T + (p.2 : ℂ) = C} ⊆
        {K : ℕ | K ≤ ⌊C.re / T.re⌋.toNat} ×ˢ
          {J : ℕ | J ≤ ⌊C.re⌋.toNat} := by
      rintro ⟨K, J⟩ hp
      have hre : (K : ℝ) * T.re + (J : ℝ) = C.re := by
        have h := congrArg Complex.re hp
        simpa using h
      have hKle : (K : ℝ) ≤ C.re / T.re := by
        rw [le_div_iff₀ hpos]
        nlinarith [(Nat.cast_nonneg J : (0:ℝ) ≤ (J:ℝ))]
      have hKleZ : (K : ℤ) ≤ ⌊(C.re / T.re : ℝ)⌋ := Int.le_floor.mpr hKle
      have hJle : (J : ℝ) ≤ C.re := by
        nlinarith [mul_nonneg (Nat.cast_nonneg K : (0:ℝ) ≤ (K:ℝ)) hpos.le]
      have hJleZ : (J : ℤ) ≤ ⌊(C.re : ℝ)⌋ := Int.le_floor.mpr hJle
      have hKb : K ≤ ⌊(C.re / T.re : ℝ)⌋.toNat := by
        have hnn : (0:ℤ) ≤ ⌊(C.re / T.re : ℝ)⌋ := le_trans (Int.natCast_nonneg K) hKleZ
        have h2 : (K : ℤ) ≤ (⌊(C.re / T.re : ℝ)⌋).toNat := by
          rw [Int.toNat_of_nonneg hnn]; exact hKleZ
        exact_mod_cast h2
      have hJb : J ≤ ⌊(C.re : ℝ)⌋.toNat := by
        have hnn : (0:ℤ) ≤ ⌊(C.re : ℝ)⌋ := le_trans (Int.natCast_nonneg J) hJleZ
        have h2 : (J : ℤ) ≤ (⌊(C.re : ℝ)⌋).toNat := by
          rw [Int.toNat_of_nonneg hnn]; exact hJleZ
        exact_mod_cast h2
      exact ⟨hKb, hJb⟩
    apply (Set.finite_le_nat ⌊C.re / T.re⌋.toNat |>.prod (Set.finite_le_nat ⌊C.re⌋.toNat)).subset
    intro p hp
    exact hsub hp
  · have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 : ℂ) * T + (p.2 : ℂ)) := by
      rintro ⟨K, J⟩ ⟨K', J'⟩ h
      have h' : ((K : ℂ) - (K' : ℂ)) * T = (J' : ℂ) - (J : ℂ) := by
        linear_combination h
      have himEq : (((K : ℂ) - (K' : ℂ)) * T).im = 0 := by rw [h']; simp
      have h2 : ((K : ℝ) - (K' : ℝ)) * T.im = 0 := by
        simpa [Complex.mul_im] using himEq
      have hKre : (K : ℝ) - K' = 0 := by
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact h3
        · exact absurd h3 him
      have hKre' : (K : ℝ) = (K' : ℝ) := by linarith
      have hK : K = K' := by exact_mod_cast hKre'
      subst hK
      have hJ : (J : ℂ) = (J' : ℂ) := add_left_cancel h
      exact Prod.ext rfl (by exact_mod_cast hJ)
    have hsub : {p : ℕ × ℕ | (p.1 : ℂ) * T + (p.2 : ℂ) = C}.Subsingleton := by
      intro p hp q hq
      exact hinj (hp.trans hq.symm)
    exact hsub.finite



lemma not_nat_mul_slitPlane_neg (T : ℂ) (hT : T ∈ Complex.slitPlane)
    (k j : ℕ) (hk : 0 < k) : (k : ℂ) * T ≠ -(j : ℂ) := by
  intro h
  by_cases him : T.im = 0
  · have hpos : 0 < T.re := by
      rcases Complex.mem_slitPlane_iff.mp hT with h1 | h1
      · exact h1
      · exact absurd him h1
    have h2 : (k : ℝ) * T.re = -(j : ℝ) := by
      have := congrArg Complex.re h
      simpa using this
    nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ)), (Nat.cast_pos.mpr hk : (0:ℝ) < (k:ℝ))]
  · have h2 : (k : ℝ) * T.im = 0 := by
      have := congrArg Complex.im h
      simpa using this
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    exact him (by
      rcases mul_eq_zero.mp h2 with h1 | h1
      · exact absurd h1 hk0
      · exact h1)

lemma arg_injective (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) (τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M) (z z' : ℂ)
    (h : (modularPhiFactorPoint M m n j z τ).2 =
      (modularPhiFactorPoint M m n j z' τ).2) : z = z' := by
  have hbne : Complex.sqrt (etaDenom M τ) ≠ 0 := sqrt_ne_zero_of_mem_slitPlane hτ
  have harg : ∀ w : ℂ, (modularPhiFactorPoint M m n j w τ).2 =
      (Complex.I / Complex.sqrt (etaDenom M τ)) * w +
        (modularPhiSArgument (etaDenom M τ)
          (((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ))) := by
    intro w
    simp only [modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput]
    field_simp
    ring
  rw [harg z, harg z'] at h
  exact mul_left_cancel₀ (div_ne_zero Complex.I_ne_zero hbne) (add_right_cancel h)

lemma pole_decomp_K (M : SL(2, ℤ)) (hM : 0 < M 1 0) (K : ℕ) :
    ((M 1 0).toNat - 1 - (K % (M 1 0).toNat)) < (M 1 0).toNat ∧
      K = (M 1 0).toNat * (K / (M 1 0).toNat) +
        ((M 1 0).toNat - 1 - ((M 1 0).toNat - 1 - (K % (M 1 0).toNat))) := by
  have hc : 0 < (M 1 0).toNat := divisorC_pos M hM
  have ha : K % (M 1 0).toNat < (M 1 0).toNat := Nat.mod_lt _ hc
  have hja : (M 1 0).toNat - 1 - ((M 1 0).toNat - 1 - (K % (M 1 0).toNat))
      = K % (M 1 0).toNat := by omega
  refine ⟨by omega, ?_⟩
  rw [hja]
  exact (Nat.div_add_mod K (M 1 0).toNat).symm

lemma pole_residue_mod (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (K J : ℕ)
    (h : Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ)) (M 1 1 * (m - 1) - n)) :
    J % (M 1 0).toNat =
      (modularPhiResidue M m n ((M 1 0).toNat - 1 - (K % (M 1 0).toNat))).toNat := by
  set c : ℕ := (M 1 0).toNat with hcdef
  set j : ℕ := c - 1 - (K % c) with hjdef
  have hc : 0 < c := divisorC_pos M hM
  have hcZ : (c : ℤ) = M 1 0 := divisorC_cast M hM
  have ha : K % c < c := Nat.mod_lt _ hc
  have hja : c - 1 - j = K % c := by
    rw [hjdef]; omega
  have hK : K = c * (K / c) + (c - 1 - j) := by
    rw [hja]
    exact (Nat.div_add_mod K c).symm
  have hmem : Int.ModEq (M 1 0)
      ((modularPhiResidue M m n j).toNat + M 1 1 *
        (((c * (K / c) + (c - 1 - j) : ℕ)) : ℤ)) (M 1 1 * (m - 1) - n) := by
    have hj_lt : j < c := by rw [hjdef]; omega
    have := pole_label_mem_res M hM m n (K / c) j hj_lt
    simpa [hcdef] using this
  have hyK : Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (((c * (K / c) + (c - 1 - j) : ℕ)) : ℤ))
      (M 1 1 * (m - 1) - n) := by
    have hh := h
    have hKZ : (K : ℤ) = ((c * (K / c) + (c - 1 - j) : ℕ) : ℤ) := by exact_mod_cast hK
    rw [hKZ] at hh
    exact hh
  have hcancel : Int.ModEq (M 1 0) (J : ℤ) ((modularPhiResidue M m n j).toNat : ℤ) := by
    have hh := hyK.trans hmem.symm
    exact modEq_cancel_right (M 1 0) (J : ℤ) ((modularPhiResidue M m n j).toNat : ℤ)
      (M 1 1 * (((c * (K / c) + (c - 1 - j) : ℕ)) : ℤ)) hh
  have hres_lt : ((modularPhiResidue M m n j).toNat : ℤ) < (c : ℤ) := by
    exact_mod_cast residue_toNat_lt M hM m n j
  have hres_nn : (0:ℤ) ≤ ((modularPhiResidue M m n j).toNat : ℤ) := by positivity
  have hcancel' : Int.ModEq (c : ℤ) (J : ℤ) ((modularPhiResidue M m n j).toNat : ℤ) := by
    rw [hcZ]; exact hcancel
  have heq : (J : ℤ) % (c : ℤ) = ((modularPhiResidue M m n j).toNat : ℤ) := by
    have hh := hcancel'.eq
    rwa [Int.emod_eq_of_lt hres_nn hres_lt] at hh
  have h1 : ((J % c : ℕ) : ℤ) = ((J : ℤ) % (c : ℤ)) := Int.natCast_emod J c
  have h2 : ((J % c : ℕ) : ℤ) = ((modularPhiResidue M m n j).toNat : ℤ) := by rw [h1, heq]
  simpa [hcdef, hjdef] using (Nat.cast_injective h2)



lemma pole_label_decompose (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (K J : ℕ)
    (hlab : (K, J) ∈ modularPhiPoleLabels M m n) :
    ((M 1 0).toNat - 1 - (K % (M 1 0).toNat)) < (M 1 0).toNat ∧
      K = (M 1 0).toNat * (K / (M 1 0).toNat) +
        ((M 1 0).toNat - 1 - ((M 1 0).toNat - 1 - (K % (M 1 0).toNat))) ∧
      J = (M 1 0).toNat * (J / (M 1 0).toNat) +
        (modularPhiResidue M m n ((M 1 0).toNat - 1 - (K % (M 1 0).toNat))).toNat := by
  simp only [modularPhiPoleLabels, Set.mem_ofPred_eq] at hlab
  refine ⟨(pole_decomp_K M hM K).1, (pole_decomp_K M hM K).2, ?_⟩
  have hmod := pole_residue_mod M hM m n K J hlab
  rw [← hmod]
  exact (Nat.div_add_mod J (M 1 0).toNat).symm

lemma pole_multiplicity_eq_sum (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    modularPhiPoleMultiplicity M m n z τ =
      ∑ j ∈ Finset.range (M 1 0).toNat,
        phiPoleMultiplicity (modularPhiFactorPoint M m n j z τ).1
          (modularPhiFactorPoint M m n j z τ).2 := by
  classical
  set c : ℕ := (M 1 0).toNat with hcdef
  have hc : 0 < c := divisorC_pos M hM
  set b : ℂ := Complex.sqrt (etaDenom M τ) with hbdef
  let S : Set (ℕ × ℕ × ℕ) :=
    {q | q.1 < c ∧ (modularPhiFactorPoint M m n q.1 z τ).2 = phiPolePoint b q.2.1 q.2.2}
  let G : ↥S → ↥(modularPhiPoleIndices M m n z τ) := fun q =>
    ⟨modularPhiPoleFactorLabel M m n q.1.1 q.1.2.1 q.1.2.2, by
      refine ⟨pole_label_mem M hM m n q.1.2.1 q.1.2.2 q.1.1 q.2.1, ?_⟩
      have hp := (modularPhi_factor_divisor_pullback_aux M hM m n τ hτ
        q.1.1 q.1.2.1 q.1.2.2 q.2.1).1
      have hinj := arg_injective M m n q.1.1 τ hτ
        (modularPhiPolePoint M m n τ
          (modularPhiPoleFactorLabel M m n q.1.1 q.1.2.1 q.1.2.2).1
          (modularPhiPoleFactorLabel M m n q.1.1 q.1.2.1 q.1.2.2).2) z
      exact (hinj (hp.trans q.2.2.symm)).symm⟩
  have hGinj : Function.Injective G := by
    intro q q' h
    apply Subtype.ext
    apply pole_label_inj M hM m n q.2.1 q'.2.1
    exact congrArg (fun x : ↥(modularPhiPoleIndices M m n z τ) => x.1) h
  have hGsurj : Function.Surjective G := by
    intro p
    obtain ⟨hlab, hz⟩ := p.2
    obtain ⟨hj, hK, hJ⟩ := pole_label_decompose M hM m n p.1.1 p.1.2 hlab
    set j : ℕ := c - 1 - (p.1.1 % c) with hjdef
    set u : ℕ := p.1.1 / c with hudef
    set v : ℕ := p.1.2 / c with hvdef
    have hja : c - 1 - j = p.1.1 % c := by
      rw [hjdef]
      exact Nat.sub_sub_self (by have := Nat.mod_lt p.1.1 hc; omega)
    have hK' : p.1.1 = c * u + (c - 1 - j) := by
      have h2 : c - 1 - (c - 1 - p.1.1 % c) = p.1.1 % c := by
        exact Nat.sub_sub_self (by have := Nat.mod_lt p.1.1 hc; omega)
      rw [hudef, hja, ← h2]
      exact hK
    have hJ' : p.1.2 = c * v + (modularPhiResidue M m n j).toNat := by
      rw [hvdef]
      exact hJ
    have hp_eq : p.1 = modularPhiPoleFactorLabel M m n j u v := by
      apply Prod.ext
      · exact hK'
      · exact hJ'
    refine ⟨⟨(j, u, v), ⟨?_, ?_⟩⟩, ?_⟩
    · show j < c
      rw [hjdef]; exact hj
    · have hj' : j < c := by rw [hjdef]; exact hj
      have hpull := (modularPhi_factor_divisor_pullback_aux M hM m n τ hτ j u v hj').1
      rw [hp_eq] at hz
      rw [← hz] at hpull
      simpa using hpull
    · apply Subtype.ext
      exact hp_eq.symm
  have hcardI : Nat.card (modularPhiPoleIndices M m n z τ) = Nat.card S := by
    symm
    exact Nat.card_eq_of_bijective G ⟨hGinj, hGsurj⟩
  rw [show modularPhiPoleMultiplicity M m n z τ =
    Nat.card (modularPhiPoleIndices M m n z τ) from rfl, hcardI]
  have hcardS : Nat.card S = Nat.card (Σ j : Fin c,
      ↥(phiPoleIndices b (modularPhiFactorPoint M m n j z τ).2)) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun q => ⟨⟨q.1.1, q.2.1⟩, ⟨(q.1.2.1, q.1.2.2), ?_⟩⟩
        invFun := fun s => ⟨(s.1.1, (s.2.1.1, s.2.1.2)), ⟨s.1.2, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · simpa only [phiPoleIndices, Set.mem_ofPred_eq] using q.2.2
    · simpa only [phiPoleIndices, Set.mem_ofPred_eq] using s.2.2
    · rintro ⟨⟨j, u, v⟩, hj, harg⟩
      rfl
    · rintro ⟨⟨j, hj⟩, ⟨⟨u, v⟩, huv⟩⟩
      rfl
  rw [hcardS]
  have : ∀ j : Fin c, Finite ↥(phiPoleIndices b (modularPhiFactorPoint M m n j z τ).2) :=
    fun j => phiPoleIndices_finite b _ (by rw [hbdef]; exact sqrt_re_pos_of_mem_slitPlane hτ)
  rw [Nat.card_sigma]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => Nat.card ↥(phiPoleIndices b (modularPhiFactorPoint M m n j z τ).2)) c]
  apply Finset.sum_congr rfl
  intro j hj
  rfl



lemma zero_label_residue_mod (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (K J : ℕ)
    (h : Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ)) (n - 1 - M 1 1 * m)) :
    J % (M 1 0).toNat =
      ((M 1 0).toNat - 1 -
        (modularPhiResidue M m n (K % (M 1 0).toNat)).toNat) := by
  set c : ℕ := (M 1 0).toNat with hcdef
  set j : ℕ := K % c with hjdef
  have hc : 0 < c := divisorC_pos M hM
  have hcZ : (c : ℤ) = M 1 0 := divisorC_cast M hM
  have hK : K = c * (K / c) + j := by
    rw [hjdef]
    exact (Nat.div_add_mod K c).symm
  have hmem : Int.ModEq (M 1 0)
      ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) + M 1 1 *
        (((c * (K / c) + j : ℕ)) : ℤ)) (n - 1 - M 1 1 * m) := by
    have := zero_label_mem_res M hM m n (K / c) j (by rw [hjdef]; exact Nat.mod_lt _ hc)
    simpa [hcdef] using this
  have hyK : Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (((c * (K / c) + j : ℕ)) : ℤ))
      (n - 1 - M 1 1 * m) := by
    have hh := h
    have hKZ : (K : ℤ) = ((c * (K / c) + j : ℕ) : ℤ) := by exact_mod_cast hK
    rwa [hKZ] at hh
  have hcancel : Int.ModEq (M 1 0) (J : ℤ)
      ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) : ℤ) := by
    have hh := hyK.trans hmem.symm
    exact modEq_cancel_right (M 1 0) (J : ℤ)
      ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) : ℤ)
      (M 1 1 * (((c * (K / c) + j : ℕ)) : ℤ)) hh
  have hres_lt : ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) : ℤ) < (c : ℤ) := by
    have := residue_toNat_lt M hM m n j
    have hlt : c - 1 - (modularPhiResidue M m n j).toNat < c := by omega
    exact_mod_cast hlt
  have hres_nn : (0:ℤ) ≤ ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) : ℤ) := by positivity
  have hcancel' : Int.ModEq (c : ℤ) (J : ℤ)
      ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) : ℤ) := by
    rw [hcZ]; exact hcancel
  have heq : (J : ℤ) % (c : ℤ) =
      ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) : ℤ) := by
    have hh := hcancel'.eq
    rwa [Int.emod_eq_of_lt hres_nn hres_lt] at hh
  have h1 : ((J % c : ℕ) : ℤ) = ((J : ℤ) % (c : ℤ)) := Int.natCast_emod J c
  have h2 : ((J % c : ℕ) : ℤ) =
      ((((c - 1 - (modularPhiResidue M m n j).toNat : ℕ))) : ℤ) := by rw [h1, heq]
  simpa [hcdef, hjdef] using (Nat.cast_injective h2)

lemma zero_label_decompose (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (K J : ℕ)
    (hlab : (K, J) ∈ modularPhiZeroLabels M m n) :
    (K % (M 1 0).toNat) < (M 1 0).toNat ∧
      K = (M 1 0).toNat * (K / (M 1 0).toNat) + (K % (M 1 0).toNat) ∧
      J = (M 1 0).toNat * (J / (M 1 0).toNat) +
        ((M 1 0).toNat - 1 -
          (modularPhiResidue M m n (K % (M 1 0).toNat)).toNat) := by
  simp only [modularPhiZeroLabels, Set.mem_ofPred_eq] at hlab
  refine ⟨Nat.mod_lt _ (divisorC_pos M hM), ?_, ?_⟩
  · exact (Nat.div_add_mod K (M 1 0).toNat).symm
  · have hmod := zero_label_residue_mod M hM m n K J hlab
    rw [← hmod]
    exact (Nat.div_add_mod J (M 1 0).toNat).symm



lemma zero_multiplicity_eq_sum (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    modularPhiZeroMultiplicity M m n z τ =
      ∑ j ∈ Finset.range (M 1 0).toNat,
        phiZeroMultiplicity (modularPhiFactorPoint M m n j z τ).1
          (modularPhiFactorPoint M m n j z τ).2 := by
  classical
  set c : ℕ := (M 1 0).toNat with hcdef
  have hc : 0 < c := divisorC_pos M hM
  set b : ℂ := Complex.sqrt (etaDenom M τ) with hbdef
  let S : Set (ℕ × ℕ × ℕ) :=
    {q | q.1 < c ∧ (modularPhiFactorPoint M m n q.1 z τ).2 = phiZeroPoint b q.2.1 q.2.2}
  let G : ↥S → ↥(modularPhiZeroIndices M m n z τ) := fun q =>
    ⟨modularPhiZeroFactorLabel M m n q.1.1 q.1.2.1 q.1.2.2, by
      refine ⟨zero_label_mem M hM m n q.1.2.1 q.1.2.2 q.1.1 q.2.1, ?_⟩
      have hp := (modularPhi_factor_divisor_pullback_aux M hM m n τ hτ
        q.1.1 q.1.2.1 q.1.2.2 q.2.1).2
      have hinj := arg_injective M m n q.1.1 τ hτ
        (modularPhiZeroPoint M m n τ
          (modularPhiZeroFactorLabel M m n q.1.1 q.1.2.1 q.1.2.2).1
          (modularPhiZeroFactorLabel M m n q.1.1 q.1.2.1 q.1.2.2).2) z
      exact (hinj (hp.trans q.2.2.symm)).symm⟩
  have hGinj : Function.Injective G := by
    intro q q' h
    apply Subtype.ext
    apply zero_label_inj M hM m n q.2.1 q'.2.1
    exact congrArg (fun x : ↥(modularPhiZeroIndices M m n z τ) => x.1) h
  have hGsurj : Function.Surjective G := by
    intro p
    obtain ⟨hlab, hz⟩ := p.2
    obtain ⟨hj, hK, hJ⟩ := zero_label_decompose M hM m n p.1.1 p.1.2 hlab
    set j : ℕ := p.1.1 % c with hjdef
    set u : ℕ := p.1.1 / c with hudef
    set v : ℕ := p.1.2 / c with hvdef
    have hK' : p.1.1 = c * u + j := by
      rw [hudef, hjdef]
      exact hK
    have hJ' : p.1.2 = c * v + (c - 1 - (modularPhiResidue M m n j).toNat) := by
      rw [hvdef, hjdef]
      exact hJ
    have hp_eq : p.1 = modularPhiZeroFactorLabel M m n j u v := by
      apply Prod.ext
      · exact hK'
      · exact hJ'
    refine ⟨⟨(j, u, v), ⟨?_, ?_⟩⟩, ?_⟩
    · show j < c
      rw [hjdef]; exact hj
    · have hj' : j < c := by rw [hjdef]; exact hj
      have hpull := (modularPhi_factor_divisor_pullback_aux M hM m n τ hτ j u v hj').2
      rw [hp_eq] at hz
      rw [← hz] at hpull
      simpa using hpull
    · apply Subtype.ext
      exact hp_eq.symm
  have hcardI : Nat.card (modularPhiZeroIndices M m n z τ) = Nat.card S := by
    symm
    exact Nat.card_eq_of_bijective G ⟨hGinj, hGsurj⟩
  rw [show modularPhiZeroMultiplicity M m n z τ =
    Nat.card (modularPhiZeroIndices M m n z τ) from rfl, hcardI]
  have hcardS : Nat.card S = Nat.card (Σ j : Fin c,
      ↥(phiZeroIndices b (modularPhiFactorPoint M m n j z τ).2)) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun q => ⟨⟨q.1.1, q.2.1⟩, ⟨(q.1.2.1, q.1.2.2), ?_⟩⟩
        invFun := fun s => ⟨(s.1.1, (s.2.1.1, s.2.1.2)), ⟨s.1.2, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · simpa only [phiZeroIndices, Set.mem_ofPred_eq] using q.2.2
    · simpa only [phiZeroIndices, Set.mem_ofPred_eq] using s.2.2
    · rintro ⟨⟨j, u, v⟩, hj, harg⟩
      rfl
    · rintro ⟨⟨j, hj⟩, ⟨⟨u, v⟩, huv⟩⟩
      rfl
  rw [hcardS]
  have : ∀ j : Fin c, Finite ↥(phiZeroIndices b (modularPhiFactorPoint M m n j z τ).2) :=
    fun j => phiZeroIndices_finite b _ (by rw [hbdef]; exact sqrt_re_pos_of_mem_slitPlane hτ)
  rw [Nat.card_sigma]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => Nat.card ↥(phiZeroIndices b (modularPhiFactorPoint M m n j z τ).2)) c]
  apply Finset.sum_congr rfl
  intro j hj
  rfl



lemma polePoint_inj_of_im_ne (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (τ : ℂ)
    (him : (etaDenom M τ).im ≠ 0) (K J K' J' : ℕ)
    (h : modularPhiPolePoint M m n τ K J = modularPhiPolePoint M m n τ K' J') :
    K = K' ∧ J = J' := by
  have hcne : (M 1 0 : ℂ) ≠ 0 := by
    have hh : (M 1 0 : ℤ) ≠ 0 := hM.ne'
    exact_mod_cast hh
  have h3 : (K : ℂ) * etaDenom M τ + (J : ℂ) = (K' : ℂ) * etaDenom M τ + (J' : ℂ) := by
    have hh := congrArg (fun w => (M 1 0 : ℂ) * w) h
    simp only [modularPhiPolePoint] at hh
    rw [mul_div_cancel₀ _ hcne, mul_div_cancel₀ _ hcne] at hh
    linear_combination hh
  have himEq : (((K : ℂ) - (K' : ℂ)) * etaDenom M τ).im = 0 := by
    have h4 : ((K : ℂ) - (K' : ℂ)) * etaDenom M τ = (J' : ℂ) - (J : ℂ) := by
      linear_combination h3
    rw [h4]; simp
  have h2r : ((K : ℝ) - (K' : ℝ)) * (etaDenom M τ).im = 0 := by
    simpa [Complex.mul_im] using himEq
  have hK : K = K' := by
    have hz : (K : ℝ) - (K' : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2r with h1 | h1
      · exact h1
      · exact absurd h1 him
    have hz' : (K : ℝ) = (K' : ℝ) := by linarith
    exact_mod_cast hz'
  have hJ : J = J' := by
    have h4 : (J : ℂ) = (J' : ℂ) := by
      rw [hK] at h3
      exact add_left_cancel h3
    exact_mod_cast h4
  exact ⟨hK, hJ⟩


lemma zeroPoint_inj_of_im_ne (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) (τ : ℂ)
    (him : (etaDenom M τ).im ≠ 0) (K J K' J' : ℕ)
    (h : modularPhiZeroPoint M m n τ K J = modularPhiZeroPoint M m n τ K' J') :
    K = K' ∧ J = J' := by
  have hcne : (M 1 0 : ℂ) ≠ 0 := by
    have hh : (M 1 0 : ℤ) ≠ 0 := hM.ne'
    exact_mod_cast hh
  have h3 : (K : ℂ) * etaDenom M τ + (J : ℂ) = (K' : ℂ) * etaDenom M τ + (J' : ℂ) := by
    have hh := congrArg (fun w => (M 1 0 : ℂ) * w) h
    simp only [modularPhiZeroPoint] at hh
    rw [mul_div_cancel₀ _ hcne, mul_div_cancel₀ _ hcne] at hh
    linear_combination -hh
  have himEq : (((K : ℂ) - (K' : ℂ)) * etaDenom M τ).im = 0 := by
    have h4 : ((K : ℂ) - (K' : ℂ)) * etaDenom M τ = (J' : ℂ) - (J : ℂ) := by
      linear_combination h3
    rw [h4]; simp
  have h2r : ((K : ℝ) - (K' : ℝ)) * (etaDenom M τ).im = 0 := by
    simpa [Complex.mul_im] using himEq
  have hK : K = K' := by
    have hz : (K : ℝ) - (K' : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2r with h1 | h1
      · exact h1
      · exact absurd h1 him
    have hz' : (K : ℝ) = (K' : ℝ) := by linarith
    exact_mod_cast hz'
  have hJ : J = J' := by
    have h4 : (J : ℂ) = (J' : ℂ) := by
      rw [hK] at h3
      exact add_left_cancel h3
    exact_mod_cast h4
  exact ⟨hK, hJ⟩

end DivisorHelpers

/-! ## Pullback, multiplicity and uniform local finiteness -/

/--
[RW26, p. 6, (19)].
This is a bijection of labels even when different labels have equal values.
-/
theorem modularPhiPoleFactorLabel_bijOn (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) :
    Set.BijOn (fun p : ℕ × ℕ × ℕ => modularPhiPoleFactorLabel M m n p.1 p.2.1 p.2.2)
      {p | p.1 < (M 1 0).toNat} (modularPhiPoleLabels M m n) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, u, v⟩ hj
    exact pole_label_mem M hM m n u v j hj
  · exact pole_label_inj M hM m n
  · exact pole_label_surj M hM m n

/-- [RW26, p. 6, (19)]. -/
theorem modularPhiZeroFactorLabel_bijOn (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) :
    Set.BijOn (fun p : ℕ × ℕ × ℕ => modularPhiZeroFactorLabel M m n p.1 p.2.1 p.2.2)
      {p | p.1 < (M 1 0).toNat} (modularPhiZeroLabels M m n) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, u, v⟩ hj
    exact zero_label_mem M hM m n u v j hj
  · exact zero_label_inj M hM m n
  · exact zero_label_surj M hM m n

/--
Exact pullback to the same φ pole/zero points, including the
nonzero affine z slope. [RW26, p. 6, (19)].
-/
theorem modularPhi_factor_divisor_pullback (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (j u v : ℕ) (hj : j < (M 1 0).toNat) :
    let p := modularPhiPoleFactorLabel M m n j u v
    let q := modularPhiZeroFactorLabel M m n j u v
    (modularPhiFactorPoint M m n j (modularPhiPolePoint M m n τ p.1 p.2) τ).2 =
        phiPolePoint (Complex.sqrt (etaDenom M τ)) u v ∧
      (modularPhiFactorPoint M m n j (modularPhiZeroPoint M m n τ q.1 q.2) τ).2 =
        phiZeroPoint (Complex.sqrt (etaDenom M τ)) u v :=
  modularPhi_factor_divisor_pullback_aux M hM m n τ hτ j u v hj

/--
Independent finiteness of the labeled pole and zero index sets, before using `Nat.card`. [RW26, p.
6].
-/
theorem modularPhiDivisor_indices_finite (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (modularPhiPoleIndices M m n z τ).Finite ∧
      (modularPhiZeroIndices M m n z τ).Finite := by
  have hT : etaDenom M τ ∈ Complex.slitPlane := hτ
  have hcne : (M 1 0 : ℂ) ≠ 0 := by
    have h : (M 1 0 : ℤ) ≠ 0 := hM.ne'
    exact_mod_cast h
  constructor
  · refine (fiber_finite (etaDenom M τ) hT
      ((M 1 0 : ℂ) * z - (n : ℂ) + ((m : ℂ) - 1) * etaDenom M τ)).subset ?_
    rintro ⟨K, J⟩ hmem
    simp only [modularPhiPoleIndices, modularPhiPolePoint, Set.mem_ofPred_eq] at hmem
    obtain ⟨-, hz⟩ := hmem
    simp only [Set.mem_ofPred_eq]
    have h := congrArg (fun w => (M 1 0 : ℂ) * w) hz
    rw [mul_div_cancel₀ _ hcne] at h
    linear_combination -h
  · refine (fiber_finite (etaDenom M τ) hT
      ((n : ℂ) - 1 - (m : ℂ) * etaDenom M τ - (M 1 0 : ℂ) * z)).subset ?_
    rintro ⟨K, J⟩ hmem
    simp only [modularPhiZeroIndices, modularPhiZeroPoint, Set.mem_ofPred_eq] at hmem
    obtain ⟨-, hz⟩ := hmem
    simp only [Set.mem_ofPred_eq]
    have h := congrArg (fun w => (M 1 0 : ℂ) * w) hz
    rw [mul_div_cancel₀ _ hcne] at h
    linear_combination h

/--
Parameter-uniform local finiteness, retaining labels of both signs.
[RW26, p. 6].
The open parameter ball stays inside the square-root domain. The formulation covers the admissible
parameters, using uniform finiteness and the finite pullback.
-/
theorem modularPhiDivisor_uniform_local_finiteness (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M) (R : ℝ) (hR : 0 ≤ R) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ τ : ℂ, dist τ τ₀ < ρ → τ ∈ modularPhiDomain M) ∧
      {p : ℕ × ℕ | p ∈ modularPhiPoleLabels M m n ∧
        ∃ τ : ℂ, dist τ τ₀ < ρ ∧ ‖modularPhiPolePoint M m n τ p.1 p.2‖ ≤ R}.Finite ∧
      {p : ℕ × ℕ | p ∈ modularPhiZeroLabels M m n ∧
        ∃ τ : ℂ, dist τ τ₀ < ρ ∧ ‖modularPhiZeroPoint M m n τ p.1 p.2‖ ≤ R}.Finite := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨ρ, hρ, hdom, hpole, hzero⟩ :=
    SICLean.L4.ModularDivisorAuxA.affine_divisors_uniform
      (modularPhiDomain M) (modularPhiDomain_isOpen M) (etaDenom M)
      (fun τ => (n : ℂ) - ((m : ℂ) - 1) * etaDenom M τ)
      (fun τ => (n : ℂ) - 1 - (m : ℂ) * etaDenom M τ)
      (M 1 0 : ℂ) τ₀ hc hτ₀
      (by unfold etaDenom; fun_prop)
      (by unfold etaDenom; fun_prop)
      (by unfold etaDenom; fun_prop) hτ₀ R
  refine ⟨ρ, hρ, hdom, hpole.subset ?_, hzero.subset ?_⟩
  · intro p hp
    exact hp.2
  · intro p hp
    exact hp.2

/--
Compact parameter version for the finite pole clusters.
[RW26, p. 6].
The arbitrary compact-C form is a corollary of the preceding
all-Dγ local theorem, formalized here.
This does not give tail decay or no pinch.
-/
theorem modularPhiDivisor_compact_finiteness (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (C : Set ℂ) (hC : IsCompact C) (hCD : C ⊆ modularPhiDomain M)
    (R : ℝ) (hR : 0 ≤ R) :
    {p : ℕ × ℕ | p ∈ modularPhiPoleLabels M m n ∧
      ∃ τ ∈ C, ‖modularPhiPolePoint M m n τ p.1 p.2‖ ≤ R}.Finite ∧
      {p : ℕ × ℕ | p ∈ modularPhiZeroLabels M m n ∧
        ∃ τ ∈ C, ‖modularPhiZeroPoint M m n τ p.1 p.2‖ ≤ R}.Finite := by
  classical
  have hlocal := fun τ : C =>
    modularPhiDivisor_uniform_local_finiteness M hM m n τ (hCD τ.property) R hR
  choose ρ hρ hdom hpole hzero using hlocal
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover
    (fun τ : C => Metric.ball (τ : ℂ) (ρ τ)) (fun _ => Metric.isOpen_ball) (by
      intro τ hτ
      exact mem_iUnion.mpr ⟨⟨τ, hτ⟩, Metric.mem_ball_self (hρ ⟨τ, hτ⟩)⟩)
  constructor
  · refine (s.finite_toSet.biUnion (fun τ _ => hpole τ)).subset ?_
    rintro p ⟨hlabel, τ, hτ, hbound⟩
    obtain ⟨v, hv, hτv⟩ := mem_iUnion₂.mp (hs hτ)
    exact mem_iUnion₂.mpr ⟨v, hv, hlabel, τ, hτv, hbound⟩
  · refine (s.finite_toSet.biUnion (fun τ _ => hzero τ)).subset ?_
    rintro p ⟨hlabel, τ, hτ, hbound⟩
    obtain ⟨v, hv, hτv⟩ := mem_iUnion₂.mp (hs hτ)
    exact mem_iUnion₂.mpr ⟨v, hv, hlabel, τ, hτv, hbound⟩

/--
No pole-zero cancellation on Dγ: equality would force T to be a
negative real number. [RW26, p. 6].
This concerns images of labeled families, not the dense pseudolattice.
-/
theorem modularPhiDivisor_disjoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    Disjoint ((fun p : ℕ × ℕ => modularPhiPolePoint M m n τ p.1 p.2) ''
      modularPhiPoleLabels M m n)
      ((fun p : ℕ × ℕ => modularPhiZeroPoint M m n τ p.1 p.2) ''
        modularPhiZeroLabels M m n) := by
  rw [Set.disjoint_left]
  rintro z ⟨⟨K, J⟩, -, hzp⟩ ⟨⟨K', J'⟩, -, hzq⟩
  have hcne : (M 1 0 : ℂ) ≠ 0 := by
    have h : (M 1 0 : ℤ) ≠ 0 := hM.ne'
    exact_mod_cast h
  have h := hzp.trans hzq.symm
  have h2 : ((n : ℂ) - ((m : ℂ) - 1) * etaDenom M τ + (K : ℂ) * etaDenom M τ + (J : ℂ)) =
      ((n : ℂ) - 1 - (m : ℂ) * etaDenom M τ - (K' : ℂ) * etaDenom M τ - (J' : ℂ)) := by
    have hh := congrArg (fun w => (M 1 0 : ℂ) * w) h
    simp only [modularPhiPolePoint, modularPhiZeroPoint] at hh
    simpa only [mul_div_cancel₀ _ hcne] using hh
  have h3 : (((1 + K + K' : ℕ)) : ℂ) * etaDenom M τ = -(((J + J' + 1 : ℕ)) : ℂ) := by
    push_cast
    linear_combination h2
  exact not_nat_mul_slitPlane_neg (etaDenom M τ) hτ (1 + K + K') (J + J' + 1) (by omega) h3

/--
Multiplicities are sums of the already proved φ multiplicities.
[RW26, p. 6, (19)].
Repeated rational-parameter branches
are counted with full multiplicity, not by a Finset of locations.
-/
theorem modularPhi_multiplicity_pullback (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    modularPhiPoleMultiplicity M m n z τ =
        ∑ j ∈ Finset.range (M 1 0).toNat,
          phiPoleMultiplicity (modularPhiFactorPoint M m n j z τ).1
            (modularPhiFactorPoint M m n j z τ).2 ∧
      modularPhiZeroMultiplicity M m n z τ =
        ∑ j ∈ Finset.range (M 1 0).toNat,
          phiZeroMultiplicity (modularPhiFactorPoint M m n j z τ).1
            (modularPhiFactorPoint M m n j z τ).2 :=
  ⟨pole_multiplicity_eq_sum M hM m n z τ hτ,
    zero_multiplicity_eq_sum M hM m n z τ hτ⟩

/--
Exact order of the actual Φ. Independent meromorphy is already
`modularPhi_meromorphic`; no inference from Mathlib's default order.
[RW26, p. 6], with multiplicities added.
-/
theorem modularPhi_order (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    meromorphicOrderAt (fun w => modularPhi M m n w τ) z =
      (modularPhiDivisorOrder M m n z τ : WithTop ℤ) := by
  classical
  set b : ℂ := Complex.sqrt (etaDenom M τ) with hbdef
  have hb : AdmissibleB b := by
    rw [hbdef]; exact (modularPhi_sqrt_admissible M τ hτ).1
  have hbne : b ≠ 0 := by rw [hbdef]; exact sqrt_ne_zero_of_mem_slitPlane hτ
  set c : ℕ := (M 1 0).toNat with hcdef
  have hargfun : ∀ j : ℕ, (fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2) =
      fun w => (Complex.I / b) * w +
        (modularPhiSArgument (etaDenom M τ)
          (((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ))) := by
    intro j
    funext w
    simp only [modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput, hbdef]
    field_simp
    ring
  have harg_an : ∀ j : ℕ, AnalyticAt ℂ
      (fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2) z := by
    intro j
    rw [hargfun j]; fun_prop
  have hmer : ∀ j ∈ Finset.range c, MeromorphicAt
      (fun w : ℂ => phiExtended b (modularPhiFactorPoint M m n j w τ).2) z := by
    intro j hj
    exact (MeromorphicAt.comp_analyticAt
      (f := phiExtended b) (g := fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2)
      (x := z) (phiExtended_meromorphic b hb _ (Set.mem_univ _)) (harg_an j))
  have hcomp : ∀ j : ℕ, meromorphicOrderAt
      (fun w : ℂ => phiExtended b (modularPhiFactorPoint M m n j w τ).2) z =
      meromorphicOrderAt (phiExtended b) (modularPhiFactorPoint M m n j z τ).2 := by
    intro j
    have hderiv : deriv (fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2) z ≠ 0 := by
      rw [hargfun j]
      have hd : deriv (fun w : ℂ => (Complex.I / b) * w +
          (modularPhiSArgument (etaDenom M τ)
            (((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ)))) z =
          Complex.I / b := by simp
      rw [hd]
      exact div_ne_zero Complex.I_ne_zero hbne
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := phiExtended b) (g := fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2)
      (harg_an j) hderiv
  have hfun : (fun w : ℂ => modularPhi M m n w τ) =
      fun w => ∏ j ∈ Finset.range c,
        phiExtended b (modularPhiFactorPoint M m n j w τ).2 := by
    funext w; rfl
  rw [hfun, meromorphicOrderAt_fun_prod hmer]
  simp_rw [hcomp]
  have hord : ∀ j : ℕ, meromorphicOrderAt (phiExtended b)
      (modularPhiFactorPoint M m n j z τ).2 =
      ((phiDivisorOrder b (modularPhiFactorPoint M m n j z τ).2 : ℤ) : WithTop ℤ) := by
    intro j
    rw [phiExtended_order b _ hb]
  simp_rw [hord]
  rw [← WithTop.coe_sum]
  have hpull := modularPhi_multiplicity_pullback M hM m n z τ hτ
  have hsum : (∑ j ∈ Finset.range c,
      phiDivisorOrder b (modularPhiFactorPoint M m n j z τ).2) =
      modularPhiDivisorOrder M m n z τ := by
    simp only [phiDivisorOrder]
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ j ∈ Finset.range c,
        (phiZeroMultiplicity b (modularPhiFactorPoint M m n j z τ).2 : ℤ)) =
        (modularPhiZeroMultiplicity M m n z τ : ℤ) := by
      rw [← Nat.cast_sum, hpull.2]
      rfl
    have h2 : (∑ j ∈ Finset.range c,
        (phiPoleMultiplicity b (modularPhiFactorPoint M m n j z τ).2 : ℤ)) =
        (modularPhiPoleMultiplicity M m n z τ : ℤ) := by
      rw [← Nat.cast_sum, hpull.1]
      rfl
    rw [h1, h2]
    rfl
  rw [hsum]

/--
Nonreal parameters have simple branches. [RW26, p. 6].
-/
theorem modularPhiDivisor_simple_of_im_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (hτ : τ ∈ modularPhiDomain M) (hi : τ.im ≠ 0) :
    (∀ p ∈ modularPhiPoleLabels M m n,
      modularPhiPoleMultiplicity M m n (modularPhiPolePoint M m n τ p.1 p.2) τ = 1) ∧
      (∀ p ∈ modularPhiZeroLabels M m n,
        modularPhiZeroMultiplicity M m n (modularPhiZeroPoint M m n τ p.1 p.2) τ = 1) := by
  have himT : (etaDenom M τ).im ≠ 0 := by
    have h1 : (etaDenom M τ).im = ((M 1 0 : ℤ) : ℝ) * τ.im := by
      simp [etaDenom, Complex.mul_im]
    rw [h1]
    have hcpos : (0:ℝ) < ((M 1 0 : ℤ) : ℝ) := by exact_mod_cast hM
    exact mul_ne_zero hcpos.ne' hi
  constructor
  · intro p hp
    have hset : modularPhiPoleIndices M m n
        (modularPhiPolePoint M m n τ p.1 p.2) τ = {p} := by
      ext q
      simp only [modularPhiPoleIndices, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, hq⟩
        obtain ⟨h1, h2⟩ := polePoint_inj_of_im_ne M hM m n τ himT p.1 p.2 q.1 q.2 hq
        exact Prod.ext h1.symm h2.symm
      · rintro rfl
        exact ⟨hp, rfl⟩
    show modularPhiPoleMultiplicity M m n
      (modularPhiPolePoint M m n τ p.1 p.2) τ = 1
    simp only [modularPhiPoleMultiplicity]
    rw [hset]
    exact Nat.card_unique
  · intro p hp
    have hset : modularPhiZeroIndices M m n
        (modularPhiZeroPoint M m n τ p.1 p.2) τ = {p} := by
      ext q
      simp only [modularPhiZeroIndices, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, hq⟩
        obtain ⟨h1, h2⟩ := zeroPoint_inj_of_im_ne M hM m n τ himT p.1 p.2 q.1 q.2 hq
        exact Prod.ext h1.symm h2.symm
      · rintro rfl
        exact ⟨hp, rfl⟩
    show modularPhiZeroMultiplicity M m n
      (modularPhiZeroPoint M m n τ p.1 p.2) τ = 1
    simp only [modularPhiZeroMultiplicity]
    rw [hset]
    exact Nat.card_unique

/--
Rational-parameter calibration, pulled back from `phiDivisor_at_one`.
[RW26, p. 5, p. 6, (9), (19)] S, τ=1, K+J=s all coincide.
-/
theorem modularPhiDivisor_at_S_one (s : ℕ) :
    modularPhiPoleMultiplicity ModularGroup.S 0 0 ((s : ℂ) + 1) 1 = s + 1 ∧
      modularPhiZeroMultiplicity ModularGroup.S 0 0 (-((s : ℂ) + 1)) 1 = s + 1 := by
  have hM : 0 < ModularGroup.S 1 0 := by norm_num [ModularGroup.coe_S]
  have hτ : (1 : ℂ) ∈ modularPhiDomain ModularGroup.S := by
    norm_num [modularPhiDomain, etaDenom, ModularGroup.coe_S,
      Complex.mem_slitPlane_iff]
  have hp := (modularPhi_multiplicity_pullback ModularGroup.S hM 0 0
    ((s : ℂ) + 1) 1 hτ).1
  have hz := (modularPhi_multiplicity_pullback ModularGroup.S hM 0 0
    (-((s : ℂ) + 1)) 1 hτ).2
  norm_num [ModularGroup.coe_S, modularPhiFactorPoint, etaDenom,
    modularPhiFactorInput, modularPhiIndex, modularPhiSArgument] at hp hz
  constructor
  · rw [hp]
    convert (phiDivisor_at_one s).1 using 2 <;> ring
  · calc
      _ = phiZeroMultiplicity 1 (-Complex.I * ((s : ℂ) + 1)) := by
        convert hz using 2 <;> ring
      _ = s + 1 := (phiDivisor_at_one s).2

/-! ## Joint regularity and specified point values -/

/--
The explicit no-pole locus equals the sufficient factorwise locus, now because the divisor pullback
has been counted exactly.
[RW26, p. 6, (19)].
-/
theorem modularPhiHolomorphicDomain_eq_regularDomain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) :
    modularPhiHolomorphicDomain M m n = modularPhiRegularDomain M m n := by
  ext p
  simp only [modularPhiHolomorphicDomain, modularPhiRegularDomain, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hdom, hzero⟩
    refine ⟨hdom, fun j hj => ?_⟩
    have hpull := modularPhi_multiplicity_pullback M hM m n p.1 p.2 hdom
    have hsum : (∑ j ∈ Finset.range (M 1 0).toNat,
        phiPoleMultiplicity (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2) = 0 := by
      rw [← hpull.1]; exact hzero
    exact (Finset.sum_eq_zero_iff.mp hsum) j hj
  · rintro ⟨hdom, hall⟩
    refine ⟨hdom, ?_⟩
    have hpull := modularPhi_multiplicity_pullback M hM m n p.1 p.2 hdom
    rw [hpull.1]
    exact Finset.sum_eq_zero_iff.mpr hall

/--
Openness follows from uniform local finiteness, not fixed-τ
discreteness. [RW26, p. 6].
-/
theorem modularPhiDivisor_domains_isOpen (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) :
    IsOpen (modularPhiHolomorphicDomain M m n) ∧
      IsOpen (modularPhiNonvanishingDomain M m n) := by
  have hreg : IsOpen (modularPhiRegularDomain M m n) := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hdom : ∀ᶠ q : ℂ × ℂ in 𝓝 p, q.2 ∈ modularPhiDomain M :=
      ((modularPhiDomain_isOpen M).preimage continuous_snd).mem_nhds hp.1
    have hfac : ∀ᶠ q : ℂ × ℂ in 𝓝 p,
        ∀ j ∈ Finset.range (M 1 0).toNat,
          modularPhiFactorPoint M m n j q.1 q.2 ∈ phiRegularDomain := by
      apply (Finset.eventually_all _).mpr
      intro j hj
      exact (((modularPhiFactorPoint_analytic M m n j) p hp.1).continuousAt)
        (isOpen_phiRegularDomain.mem_nhds
          ⟨(modularPhi_sqrt_admissible M p.2 hp.1).1, hp.2 j hj⟩)
    filter_upwards [hdom, hfac] with q hq hqfac
    exact ⟨hq, fun j hj => (hqfac j hj).2⟩
  have hhol : IsOpen (modularPhiHolomorphicDomain M m n) := by
    rw [modularPhiHolomorphicDomain_eq_regularDomain M hM m n]
    exact hreg
  refine ⟨hhol, ?_⟩
  have hunit (p : ℂ × ℂ) (hp : p ∈ modularPhiHolomorphicDomain M m n) :
      modularPhi M m n p.1 p.2 ≠ 0 ↔
        modularPhiZeroMultiplicity M m n p.1 p.2 = 0 := by
    have hpull := modularPhi_multiplicity_pullback M hM m n p.1 p.2 hp.1
    have hpfac : ∀ j ∈ Finset.range (M 1 0).toNat,
        phiPoleMultiplicity (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 = 0 := by
      apply Finset.sum_eq_zero_iff.mp
      rw [← hpull.1]
      exact hp.2
    rw [modularPhi, Finset.prod_ne_zero_iff, hpull.2, Finset.sum_eq_zero_iff]
    exact forall₂_congr fun j hj => phiExtended_ne_zero_iff _ _
      (modularPhi_sqrt_admissible M p.2 hp.1).1 (hpfac j hj)
  have heq : modularPhiNonvanishingDomain M m n =
      modularPhiHolomorphicDomain M m n ∩
        (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2) ⁻¹' ({0}ᶜ : Set ℂ) := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨hp.1, hp.2.1⟩, (hunit p ⟨hp.1, hp.2.1⟩).mpr hp.2.2⟩
    · rintro ⟨hp, hne⟩
      exact ⟨hp.1, hp.2, (hunit p hp).mp hne⟩
  rw [heq, modularPhiHolomorphicDomain_eq_regularDomain M hM m n]
  exact ((modularPhi_joint_analytic_regular M hM m n).continuousOn).isOpen_inter_preimage
    hreg isClosed_singleton.isOpen_compl

/--
Joint analyticity of the specified representative on the full no-pole
locus, including zeros. [RW26, p. 6].
Uses the actual charts; a nonnegative germ order alone is insufficient.
-/
theorem modularPhi_joint_analytic_no_poles (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2)
      (modularPhiHolomorphicDomain M m n) := by
  rw [modularPhiHolomorphicDomain_eq_regularDomain M hM m n]
  exact modularPhi_joint_analytic_regular M hM m n

/--
Exact pointwise nonzero criterion off poles; at poles the specified
representative is separately 0. [RW26, p. 6].
-/
theorem modularPhi_ne_zero_iff (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hp : modularPhiPoleMultiplicity M m n z τ = 0) :
    modularPhi M m n z τ ≠ 0 ↔ modularPhiZeroMultiplicity M m n z τ = 0 := by
  classical
  have hpull := modularPhi_multiplicity_pullback M hM m n z τ hτ
  have hb : AdmissibleB (Complex.sqrt (etaDenom M τ)) :=
    (modularPhi_sqrt_admissible M τ hτ).1
  have hpole : ∀ j ∈ Finset.range (M 1 0).toNat,
      phiPoleMultiplicity (modularPhiFactorPoint M m n j z τ).1
        (modularPhiFactorPoint M m n j z τ).2 = 0 := by
    apply Finset.sum_eq_zero_iff.mp
    rw [← hpull.1]; exact hp
  have hfun : modularPhi M m n z τ = ∏ j ∈ Finset.range (M 1 0).toNat,
      phiExtended (modularPhiFactorPoint M m n j z τ).1
        (modularPhiFactorPoint M m n j z τ).2 := rfl
  rw [hfun, Finset.prod_ne_zero_iff, hpull.2, Finset.sum_eq_zero_iff]
  constructor
  · intro hall j hj
    exact (phiExtended_ne_zero_iff _ _ hb (hpole j hj)).mp (hall j hj)
  · intro hall j hj
    exact (phiExtended_ne_zero_iff _ _ hb (hpole j hj)).mpr (hall j hj)

/--
Total-division convention, not a removable value.
`phiExtended_pole_value`, [RW26, p. 6, (19)] divisor disjointness.
-/
theorem modularPhi_pole_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hp : modularPhiPoleMultiplicity M m n z τ ≠ 0) :
    modularPhi M m n z τ = 0 := by
  classical
  have hpull := modularPhi_multiplicity_pullback M hM m n z τ hτ
  have hsum : (∑ j ∈ Finset.range (M 1 0).toNat,
      phiPoleMultiplicity (modularPhiFactorPoint M m n j z τ).1
        (modularPhiFactorPoint M m n j z τ).2) ≠ 0 := by
    rw [← hpull.1]; exact hp
  obtain ⟨j, hj, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  rw [modularPhi, Finset.prod_eq_zero_iff]
  refine ⟨j, hj, ?_⟩
  exact phiExtended_pole_value _ _ (modularPhi_sqrt_admissible M τ hτ).1 hjne

/--
A callable two-complex-variable unit neighborhood. Only the actual divisor is avoided, even at real
irrational τ.
[RW26, p. 6].
-/
theorem modularPhi_joint_unit_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (p : ℂ × ℂ) (hp : p ∈ modularPhiNonvanishingDomain M m n) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ p ∈ U ∧
      U ⊆ modularPhiNonvanishingDomain M m n ∧
      AnalyticOnNhd ℂ (fun q : ℂ × ℂ => modularPhi M m n q.1 q.2) U ∧
      (∀ q ∈ U, modularPhi M m n q.1 q.2 ≠ 0) := by
  refine ⟨modularPhiNonvanishingDomain M m n,
    (modularPhiDivisor_domains_isOpen M hM m n).2, hp, Subset.rfl, ?_, ?_⟩
  · exact (modularPhi_joint_analytic_no_poles M hM m n).mono
      (fun _ hq => ⟨hq.1, hq.2.1⟩)
  · intro q hq
    exact (modularPhi_ne_zero_iff M hM m n q.1 q.2 hq.1 hq.2.1).mpr hq.2.2

lemma m37b_polePoint_mem_pseudolattice (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (K J : ℕ) (h : (K, J) ∈ modularPhiPoleLabels M m n) :
    modularPhiPolePoint M m n τ K J ∈ modularPhiPseudoLattice τ := by
  obtain ⟨q, hq⟩ := Int.ModEq.dvd h
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨(K : ℤ) - m + 1, -q, ?_⟩
  apply (div_eq_iff hc).mpr
  have hqC := congrArg (fun x : ℤ => (x : ℂ)) hq
  push_cast at hqC ⊢
  unfold etaDenom
  linear_combination -hqC

lemma m37b_zeroPoint_mem_pseudolattice (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (K J : ℕ) (h : (K, J) ∈ modularPhiZeroLabels M m n) :
    modularPhiZeroPoint M m n τ K J ∈ modularPhiPseudoLattice τ := by
  obtain ⟨q, hq⟩ := Int.ModEq.dvd h
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨-m - K, q, ?_⟩
  apply (div_eq_iff hc).mpr
  have hqC := congrArg (fun x : ℤ => (x : ℂ)) hq
  push_cast at hqC ⊢
  unfold etaDenom
  linear_combination hqC

/--
Pointwise divisor exclusion at a real nonlattice point. This does not
need a neighborhood avoiding the pseudolattice.
[RW26, p. 6].
-/
theorem modularPhi_real_off_lattice (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ₀ : ℝ) (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (z : ℂ) (hz : z ∉ modularPhiPseudoLattice (τ₀ : ℂ)) :
    (z, (τ₀ : ℂ)) ∈ modularPhiNonvanishingDomain M m n := by
  refine ⟨real_mem_modularPhiDomain M τ₀ hT, ?_, ?_⟩
  · have hempty : modularPhiPoleIndices M m n z (τ₀ : ℂ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨K, J⟩ ⟨hlabel, hz'⟩
      apply hz
      rw [hz']
      exact m37b_polePoint_mem_pseudolattice M hM m n _ K J hlabel
    simp [modularPhiPoleMultiplicity, hempty]
  · have hempty : modularPhiZeroIndices M m n z (τ₀ : ℂ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨K, J⟩ ⟨hlabel, hz'⟩
      apply hz
      rw [hz']
      exact m37b_zeroPoint_mem_pseudolattice M hM m n _ K J hlabel
    simp [modularPhiZeroMultiplicity, hempty]

lemma m37b_irrational_relation (τ : ℝ) (hτ : Irrational τ) (a b : ℤ)
    (h : (a : ℂ) * (τ : ℂ) + (b : ℂ) = 0) : a = 0 ∧ b = 0 := by
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re] at hr
  have ha : a = 0 := by
    by_contra ha
    have hia := (hτ.intCast_mul ha).add_intCast b
    rw [hr] at hia
    exact hia (by exact ⟨0, by simp⟩)
  refine ⟨ha, ?_⟩
  simp [ha] at hr
  exact_mod_cast hr

lemma m37b_pole_index_iff (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k l : ℤ) (τ : ℝ) (hτ : Irrational τ) (K J : ℕ) :
    (K, J) ∈ modularPhiPoleIndices M m n ((k : ℂ) * (τ : ℂ) + (l : ℂ)) τ ↔
      (K : ℤ) = k + m - 1 ∧ (J : ℤ) = -(M 1 1 * k - M 1 0 * l + n) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  constructor
  · rintro ⟨_, hz⟩
    have heq := (eq_div_iff hc).mp hz
    have hrel : ((M 1 0 * (k - (K : ℤ) + m - 1) : ℤ) : ℂ) * (τ : ℂ) +
        ((M 1 0 * l - n + (m - 1) * M 1 1 - (K : ℤ) * M 1 1 - J : ℤ) : ℂ) = 0 := by
      push_cast
      dsimp [modularPhiPolePoint, etaDenom] at heq
      linear_combination heq
    obtain ⟨hA, hB⟩ := m37b_irrational_relation τ hτ _ _ hrel
    have hK : (K : ℤ) = k + m - 1 := by
      have : k - (K : ℤ) + m - 1 = 0 := (mul_eq_zero.mp hA).resolve_left hM.ne'
      omega
    refine ⟨hK, ?_⟩
    rw [hK] at hB
    linear_combination -hB
  · rintro ⟨hK, hJ⟩
    refine ⟨?_, ?_⟩
    · apply Int.modEq_iff_dvd.mpr
      refine ⟨-l, ?_⟩
      change M 1 1 * (m - 1) - n - ((J : ℤ) + M 1 1 * (K : ℤ)) = _
      rw [hK, hJ]
      ring
    · apply (eq_div_iff hc).mpr
      have hKC : (K : ℂ) = (k : ℂ) + (m : ℂ) - 1 := by exact_mod_cast hK
      have hJC : (J : ℂ) = -((M 1 1 : ℂ) * (k : ℂ) - (M 1 0 : ℂ) * (l : ℂ) + (n : ℂ)) := by
        exact_mod_cast hJ
      dsimp [modularPhiPolePoint, etaDenom]
      rw [hKC, hJC]
      ring

lemma m37b_zero_index_iff (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k l : ℤ) (τ : ℝ) (hτ : Irrational τ) (K J : ℕ) :
    (K, J) ∈ modularPhiZeroIndices M m n ((k : ℂ) * (τ : ℂ) + (l : ℂ)) τ ↔
      (K : ℤ) = -k - m ∧ (J : ℤ) = M 1 1 * k - M 1 0 * l + n - 1 := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  constructor
  · rintro ⟨_, hz⟩
    have heq := (eq_div_iff hc).mp hz
    have hrel : ((M 1 0 * (k + m + (K : ℤ)) : ℤ) : ℂ) * (τ : ℂ) +
        ((M 1 0 * l - n + 1 + m * M 1 1 + (K : ℤ) * M 1 1 + J : ℤ) : ℂ) = 0 := by
      push_cast
      dsimp [modularPhiZeroPoint, etaDenom] at heq
      linear_combination heq
    obtain ⟨hA, hB⟩ := m37b_irrational_relation τ hτ _ _ hrel
    have hK : (K : ℤ) = -k - m := by
      have : k + m + (K : ℤ) = 0 := (mul_eq_zero.mp hA).resolve_left hM.ne'
      omega
    refine ⟨hK, ?_⟩
    rw [hK] at hB
    linear_combination hB
  · rintro ⟨hK, hJ⟩
    refine ⟨?_, ?_⟩
    · apply Int.modEq_iff_dvd.mpr
      refine ⟨l, ?_⟩
      change n - 1 - M 1 1 * m - ((J : ℤ) + M 1 1 * (K : ℤ)) = _
      rw [hK, hJ]
      ring
    · apply (eq_div_iff hc).mpr
      have hKC : (K : ℂ) = -(k : ℂ) - (m : ℂ) := by exact_mod_cast hK
      have hJC : (J : ℂ) = (M 1 1 : ℂ) * (k : ℂ) - (M 1 0 : ℂ) * (l : ℂ) + (n : ℂ) - 1 := by
        exact_mod_cast hJ
      dsimp [modularPhiZeroPoint, etaDenom]
      rw [hKC, hJC]
      ring
lemma m37b_card_nonneg_pair (a b : ℤ) :
    Nat.card {p : ℕ × ℕ | (p.1 : ℤ) = a ∧ (p.2 : ℤ) = b} =
      if 0 ≤ a ∧ 0 ≤ b then 1 else 0 := by
  by_cases hab : 0 ≤ a ∧ 0 ≤ b
  · rw [if_pos hab]
    apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · refine ⟨?_⟩
      intro x y
      apply Subtype.ext
      apply Prod.ext
      · exact_mod_cast x.property.1.trans y.property.1.symm
      · exact_mod_cast x.property.2.trans y.property.2.symm
    · exact ⟨⟨(a.toNat, b.toNat), Int.toNat_of_nonneg hab.1, Int.toNat_of_nonneg hab.2⟩⟩
  · rw [if_neg hab]
    have hempty : {p : ℕ × ℕ | (p.1 : ℤ) = a ∧ (p.2 : ℤ) = b} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨K, J⟩ ⟨hK, hJ⟩
      apply hab
      constructor <;> omega
    rw [hempty]
    simp

/--
Exact [RW26] sign criterion when the lattice representation is unique.
Irrationality is essential here; rational parameters use full counts.
[RW26, p. 6]. This is not a lattice value theorem.
-/
theorem modularPhi_real_lattice_multiplicity (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ₀ : ℝ) (hτ₀ : Irrational τ₀)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) (k l : ℤ) :
    modularPhiPoleMultiplicity M m n ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ)) (τ₀ : ℂ) =
        (if M 1 1 * k - M 1 0 * l + n ≤ 0 ∧ 0 < k + m then 1 else 0) ∧
      modularPhiZeroMultiplicity M m n ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ)) (τ₀ : ℂ) =
        (if k + m ≤ 0 ∧ 0 < M 1 1 * k - M 1 0 * l + n then 1 else 0) := by
  have hp : modularPhiPoleIndices M m n ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ)) τ₀ =
      {p : ℕ × ℕ | (p.1 : ℤ) = k + m - 1 ∧
        (p.2 : ℤ) = -(M 1 1 * k - M 1 0 * l + n)} := by
    ext ⟨K, J⟩
    exact m37b_pole_index_iff M hM m n k l τ₀ hτ₀ K J
  have hz : modularPhiZeroIndices M m n ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ)) τ₀ =
      {p : ℕ × ℕ | (p.1 : ℤ) = -k - m ∧
        (p.2 : ℤ) = M 1 1 * k - M 1 0 * l + n - 1} := by
    ext ⟨K, J⟩
    exact m37b_zero_index_iff M hM m n k l τ₀ hτ₀ K J
  constructor
  · rw [modularPhiPoleMultiplicity, hp, m37b_card_nonneg_pair]
    have hsign : (0 ≤ k + m - 1 ∧ 0 ≤ -(M 1 1 * k - M 1 0 * l + n)) ↔
        (M 1 1 * k - M 1 0 * l + n ≤ 0 ∧ 0 < k + m) := by omega
    simp only [hsign]
  · rw [modularPhiZeroMultiplicity, hz, m37b_card_nonneg_pair]
    have hsign : (0 ≤ -k - m ∧ 0 ≤ M 1 1 * k - M 1 0 * l + n - 1) ↔
        (k + m ≤ 0 ∧ 0 < M 1 1 * k - M 1 0 * l + n) := by omega
    simp only [hsign]

/-! ## Common-zero cancellation in two variables -/

/--
Center of the explicit regularization, not the raw quotient.
[RW26, p. 12].
-/
theorem modularPhiCommonZeroFactor_zero (T : ℂ) : modularPhiCommonZeroFactor 0 T = T :=
  modularPhiCommonZeroFactor_zero_aux T

noncomputable def m37b_expSlope (z : ℂ) : ℂ := dslope e 0 z

lemma m37b_expSlope_mul (z : ℂ) : z * m37b_expSlope z = e z - 1 := by
  simpa [m37b_expSlope, e] using sub_smul_dslope e 0 z

lemma m37b_expSlope_zero : m37b_expSlope 0 = 2 * (Real.pi : ℂ) * Complex.I := by
  dsimp [m37b_expSlope]
  rw [dslope_same]
  have hd := (((hasDerivAt_id (0 : ℂ)).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)).cexp).deriv
  change deriv (fun x : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * x)) 0 = _
  simpa using hd

lemma m37b_expSlope_zero_ne : m37b_expSlope 0 ≠ 0 := by
  rw [m37b_expSlope_zero]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
    Complex.I_ne_zero

lemma m37b_expSlope_analytic_zero : AnalyticAt ℂ m37b_expSlope 0 := by
  have he : AnalyticAt ℂ e 0 := by unfold e; fun_prop
  rcases he with ⟨p, hp⟩
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

lemma m37b_commonZeroFactor_eq (ζ T : ℂ) (hT : T ≠ 0)
    (hG : m37b_expSlope (ζ / T) ≠ 0) :
    (if ζ = 0 then T else (1 - e ζ) / (1 - e (ζ / T))) =
      T * m37b_expSlope ζ / m37b_expSlope (ζ / T) := by
  by_cases hζ : ζ = 0
  · simp [hζ, m37b_expSlope_zero_ne]
  · rw [if_neg hζ]
    have hnum := m37b_expSlope_mul ζ
    have hden := m37b_expSlope_mul (ζ / T)
    have hdenne : 1 - e (ζ / T) ≠ 0 := by
      intro h
      have hh : (ζ / T) * m37b_expSlope (ζ / T) = 0 := by
        rw [hden]
        linear_combination -h
      exact (mul_ne_zero (div_ne_zero hζ hT) hG) hh
    apply (div_eq_iff hdenne).mpr
    rw [← neg_sub (e ζ) 1, ← neg_sub (e (ζ / T)) 1, ← hnum, ← hden]
    field_simp


lemma m37b_commonZeroFactor_identity (ζ T : ℂ) (hT : T ≠ 0)
    (hG : m37b_expSlope (ζ / T) ≠ 0) :
    (T * m37b_expSlope ζ / m37b_expSlope (ζ / T)) * (1 - e (ζ / T)) =
      1 - e ζ := by
  have hnum := m37b_expSlope_mul ζ
  have hden := m37b_expSlope_mul (ζ / T)
  rw [← neg_sub (e ζ) 1, ← neg_sub (e (ζ / T)) 1, ← hnum, ← hden]
  field_simp

/--
Genuine joint analytic/nonzero neighborhood of (0,T₀), and a
denominator-cleared identity valid also on ζ=0. The conclusion is not
`AnalyticAt` for the raw total quotient. [RW26, p. 12] is the explicit factorization.
-/
theorem modularPhiCommonZeroFactor_joint (T₀ : ℂ) (hT₀ : T₀ ≠ 0) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ (0, T₀) ∈ U ∧ U ⊆ {p | p.2 ≠ 0} ∧
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiCommonZeroFactor p.1 p.2) U ∧
      (∀ p ∈ U, modularPhiCommonZeroFactor p.1 p.2 ≠ 0 ∧
        modularPhiCommonZeroFactor p.1 p.2 * (1 - e (p.1 / p.2)) = 1 - e p.1) := by
  unfold modularPhiCommonZeroFactor
  let R : ℂ × ℂ → ℂ := fun p => p.2 * m37b_expSlope p.1 / m37b_expSlope (p.1 / p.2)
  have hG : AnalyticAt ℂ m37b_expSlope (0 : ℂ) := m37b_expSlope_analytic_zero
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ => m37b_expSlope p.1) (0, T₀) :=
    hG.comp (f := fun p : ℂ × ℂ => p.1) (x := (0, T₀)) analyticAt_fst
  have hB : AnalyticAt ℂ (fun p : ℂ × ℂ => m37b_expSlope (p.1 / p.2)) (0, T₀) := by
    have hf : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 / p.2) (0, T₀) :=
      analyticAt_fst.div analyticAt_snd hT₀
    have hg0 : AnalyticAt ℂ m37b_expSlope ((0 : ℂ) / T₀) := by simpa using hG
    exact hg0.comp (f := fun p : ℂ × ℂ => p.1 / p.2) (x := (0, T₀)) hf
  have hBne : m37b_expSlope ((0 : ℂ) / T₀) ≠ 0 := by
    simpa using m37b_expSlope_zero_ne
  have hR : AnalyticAt ℂ R (0, T₀) := (analyticAt_snd.mul hA).div hB hBne
  have hRzero : R (0, T₀) = T₀ := by simp [R, m37b_expSlope_zero_ne]
  have hev : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, T₀),
      p.2 ≠ 0 ∧ m37b_expSlope (p.1 / p.2) ≠ 0 ∧ R p ≠ 0 ∧ AnalyticAt ℂ R p := by
    filter_upwards [continuous_snd.continuousAt.eventually_ne hT₀,
      hB.continuousAt.eventually_ne hBne,
      hR.continuousAt.eventually_ne (hRzero ▸ hT₀), hR.eventually_analyticAt]
      with p hp hbp hrp hap
    exact ⟨hp, hbp, hrp, hap⟩
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.mp hev
  refine ⟨U, hUopen, hUmem, fun p hp => (hUsub hp).1, ?_, ?_⟩
  · apply AnalyticOnNhd.congr hUopen (fun p hp => (hUsub hp).2.2.2)
    intro p hp
    exact (m37b_commonZeroFactor_eq p.1 p.2 (hUsub hp).1 (hUsub hp).2.1).symm
  · intro p hp
    rw [m37b_commonZeroFactor_eq p.1 p.2 (hUsub hp).1 (hUsub hp).2.1]
    exact ⟨(hUsub hp).2.2.1,
      m37b_commonZeroFactor_identity p.1 p.2 (hUsub hp).1 (hUsub hp).2.1⟩

/--
[RW26, p. 6, p. 12, Lemma 2]. This holds for every admissible complex τ:
k′=dk-cl and l′=al-bk. It explains the moving common-zero curve.
-/
theorem modularPhi_lattice_mobius (M : SL(2, ℤ)) (k l : ℤ) (τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M) :
    ((k : ℂ) * τ + (l : ℂ)) / etaDenom M τ =
      ((M 1 1 * k - M 1 0 * l : ℤ) : ℂ) * etaMobius M τ +
        ((M 0 0 * l - M 0 1 * k : ℤ) : ℂ) :=
  modularPhi_lattice_mobius_aux M k l τ hτ

lemma m37c_qTail_analytic (r : ℤ) (p : ℂ × ℂ)
    (hq0 : 0 < ‖p.2‖) (hq1 : ‖p.2‖ < 1) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhiLatticeQTail r p.1 p.2) p := by
  have he : AnalyticAt ℂ (fun p : ℂ × ℂ => e p.1) p := by
    unfold e
    exact (analyticAt_const.mul analyticAt_fst).cexp
  have hx (s : ℤ) : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2 ^ s * e p.1) p :=
    (analyticAt_snd.zpow (norm_pos_iff.mp hq0)).mul he
  have hP (s : ℤ) : AnalyticAt ℂ
      (fun p : ℂ × ℂ => qPochhammer (p.2 ^ s * e p.1) p.2) p := by
    exact (analyticOnNhd_qPochhammer_joint (p.2 ^ s * e p.1, p.2)
      ⟨hq0, hq1⟩).comp (x := p) ((hx s).prod analyticAt_snd)
  unfold modularPhiLatticeQTail
  split_ifs
  · exact hP r
  · apply AnalyticAt.mul
    · unfold qPochhammerNat
      apply Finset.analyticAt_fun_prod
      intro j hj
      exact analyticAt_const.sub ((hx r).mul (analyticAt_snd.pow j))
    · simpa only [zpow_one] using hP 1

lemma m37c_qTail_ne_zero (r : ℤ) (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    modularPhiLatticeQTail r 0 q ≠ 0 := by
  have hq : q ≠ 0 := norm_pos_iff.mp hq0
  have he0 : e 0 = 1 := by simp [e]
  unfold modularPhiLatticeQTail
  split_ifs with hr
  · rw [he0, mul_one]
    exact qPochhammer_ne_zero_of_norm_lt_one _ q
      (by rw [norm_zpow]; exact zpow_lt_one₀ hq0 hq1 (by omega)) hq0 hq1
  · rw [he0, mul_one, mul_one]
    apply mul_ne_zero _ (qPochhammer_q_ne_zero q hq0 hq1)
    rw [qPochhammerNat, Finset.prod_ne_zero_iff]
    intro j hj
    apply sub_ne_zero.mpr
    intro h
    have hpow : q ^ (r + (j : ℤ)) = 1 := by
      rw [zpow_add₀ hq, zpow_natCast]
      exact h.symm
    have hneg : r + (j : ℤ) < 0 := by
      have := Finset.mem_range.mp hj
      omega
    have hnorm := congrArg norm hpow
    rw [norm_zpow, norm_one] at hnorm
    have := one_lt_zpow_of_neg₀ hq0 hq1 hneg
    linarith

lemma m37c_upper_mobius (M : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    0 < (etaMobius M τ).im := by
  rw [← coe_smul_eq_etaMobius M (⟨τ, hτ⟩ : ℍ)]
  exact (M • (⟨τ, hτ⟩ : ℍ)).im_pos

lemma m37c_regularPart_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r : ℤ) (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ => modularPhiLatticeQRegularPart M r p.1 p.2) (0, τ) ∧
      modularPhiLatticeQRegularPart M r 0 τ ≠ 0 := by
  have hq0 : 0 < ‖e τ‖ := norm_pos_iff.mpr (e_ne_zero τ)
  have hq1 : ‖e τ‖ < 1 := norm_e_lt_one ⟨τ, hτ⟩
  have hQ0 : 0 < ‖e (etaMobius M τ)‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hQ1 : ‖e (etaMobius M τ)‖ < 1 :=
    norm_e_lt_one ⟨_, m37c_upper_mobius M τ hτ⟩
  have hD : etaDenom M τ ≠ 0 :=
    etaDenom_ne_zero_of_mem M (mem_modularPhiDomain_of_im_pos M hM hτ)
  have hd : AnalyticAt ℂ (fun p : ℂ × ℂ => etaDenom M p.2) (0, τ) := by
    exact (analyticAt_const.mul analyticAt_snd).add analyticAt_const
  have hm : AnalyticAt ℂ (fun p : ℂ × ℂ => etaMobius M p.2) (0, τ) := by
    exact ((analyticAt_const.mul analyticAt_snd).add analyticAt_const).div hd hD
  have he : AnalyticAt ℂ (fun p : ℂ × ℂ => e p.2) (0, τ) := by
    unfold e
    exact (analyticAt_const.mul analyticAt_snd).cexp
  have hE : AnalyticAt ℂ (fun p : ℂ × ℂ => e (etaMobius M p.2)) (0, τ) := by
    unfold e
    exact (analyticAt_const.mul hm).cexp
  have hn := (m37c_qTail_analytic r (0, e τ) hq0 hq1).comp (x := (0, τ))
    (analyticAt_fst.prod he)
  have hden := (m37c_qTail_analytic r (0 / etaDenom M τ, e (etaMobius M τ))
    hQ0 hQ1).comp (x := (0, τ)) ((analyticAt_fst.div hd hD).prod hE)
  have hn0 := m37c_qTail_ne_zero r (e τ) hq0 hq1
  have hd0 := m37c_qTail_ne_zero r (e (etaMobius M τ)) hQ0 hQ1
  constructor
  · exact hn.div hden (by simpa only [zero_div] using hd0)
  · exact div_ne_zero hn0 (by simpa only [zero_div] using hd0)

lemma m37c_regularPart_moving_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r k l : ℤ) (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhiLatticeQRegularPart M r
      (p.1 - (k : ℂ) * p.2 - (l : ℂ)) p.2) ((k : ℂ) * τ + (l : ℂ), τ) := by
  apply (m37c_regularPart_analytic M hM r τ hτ).1.comp_of_eq
    (((analyticAt_fst.sub (analyticAt_const.mul analyticAt_snd)).sub
      analyticAt_const).prod analyticAt_snd)
  exact Prod.ext (by dsimp; ring) rfl

lemma m37c_repair_moving_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r k l : ℤ) (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticAt ℂ (fun p : ℂ × ℂ =>
      (if 1 ≤ r then 1 else modularPhiCommonZeroFactor
        (p.1 - (k : ℂ) * p.2 - (l : ℂ)) (etaDenom M p.2)) *
      modularPhiLatticeQRegularPart M r
        (p.1 - (k : ℂ) * p.2 - (l : ℂ)) p.2) ((k : ℂ) * τ + (l : ℂ), τ) := by
  have hF := m37c_regularPart_moving_analytic M hM r k l τ hτ
  by_cases hr : 1 ≤ r
  · simpa only [if_pos hr, one_mul] using hF
  · simp only [if_neg hr]
    have hD : etaDenom M τ ≠ 0 :=
      etaDenom_ne_zero_of_mem M (mem_modularPhiDomain_of_im_pos M hM hτ)
    obtain ⟨V, _, hV, _, hVan, _⟩ := modularPhiCommonZeroFactor_joint _ hD
    have hd : AnalyticAt ℂ (fun p : ℂ × ℂ => etaDenom M p.2)
        ((k : ℂ) * τ + (l : ℂ), τ) :=
      (analyticAt_const.mul analyticAt_snd).add analyticAt_const
    have hcoord : AnalyticAt ℂ (fun p : ℂ × ℂ =>
        (p.1 - (k : ℂ) * p.2 - (l : ℂ), etaDenom M p.2))
        ((k : ℂ) * τ + (l : ℂ), τ) :=
      (((analyticAt_fst.sub (analyticAt_const.mul analyticAt_snd)).sub
        analyticAt_const).prod hd)
    have hC := (hVan _ hV).comp_of_eq hcoord (Prod.ext (by dsimp; ring) rfl)
    exact hC.mul hF

lemma m37c_qTail_factor (r : ℤ) (ζ q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    qPochhammer (q ^ r * e ζ) q =
      (if 1 ≤ r then 1 else 1 - e ζ) * modularPhiLatticeQTail r ζ q := by
  by_cases hr : 1 ≤ r
  · simp [modularPhiLatticeQTail, hr]
  · have hq : q ≠ 0 := norm_ne_zero_iff.mp hq0.ne'
    have hr0 : r ≤ 0 := by omega
    have hnat : ((-r).toNat : ℤ) = -r := Int.toNat_of_nonneg (by omega)
    have hpow : q ^ r * q ^ (-r).toNat = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hq, hnat]
      simp
    have hshift := qPochhammer_shift_nat (q ^ r * e ζ) q (-r).toNat hq0 hq1
    have harg : q ^ r * e ζ * q ^ (-r).toNat = e ζ := by
      calc
        q ^ r * e ζ * q ^ (-r).toNat = (q ^ r * q ^ (-r).toNat) * e ζ := by ring
        _ = e ζ := by rw [hpow, one_mul]
    rw [harg] at hshift
    have hfirst := qPochhammer_shift_nat (e ζ) q 1 hq0 hq1
    simp only [qPochhammerNat, Finset.prod_range_one, pow_zero, mul_one, pow_one] at hfirst
    rw [hshift, hfirst]
    simp only [modularPhiLatticeQTail, hr, if_false]
    ring

lemma m37c_exp_lattice_shift (q τ ζ : ℂ) (hq : q = e τ) (k l : ℤ) :
    e (ζ + ((k : ℂ) * τ + (l : ℂ))) = e ζ * q ^ k := by
  rw [e_add', e_add', e_intCast, mul_one, ← e_int_mul, ← hq]

lemma m37c_qNumerator_lattice (m k l : ℤ) (z τ : ℂ) :
    modularPhiQNumerator m z τ =
      qPochhammer ((e τ) ^ (k + m) * e (z - (k : ℂ) * τ - (l : ℂ))) (e τ) := by
  unfold modularPhiQNumerator
  congr 1
  have hz : z = (z - (k : ℂ) * τ - (l : ℂ)) + ((k : ℂ) * τ + (l : ℂ)) := by ring
  conv_lhs => rw [hz]
  rw [m37c_exp_lattice_shift (e τ) τ _ rfl k l, zpow_add₀ (e_ne_zero τ)]
  ring

lemma m37c_qDenominator_lattice (M : SL(2, ℤ)) (n k l : ℤ)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    modularPhiQDenominator M n z τ =
      qPochhammer ((e (etaMobius M τ)) ^ (M 1 1 * k - M 1 0 * l + n) *
        e ((z - (k : ℂ) * τ - (l : ℂ)) / etaDenom M τ)) (e (etaMobius M τ)) := by
  unfold modularPhiQDenominator
  congr 1
  have hz : z / etaDenom M τ =
      (z - (k : ℂ) * τ - (l : ℂ)) / etaDenom M τ +
        (((k : ℂ) * τ + (l : ℂ)) / etaDenom M τ) := by ring
  rw [hz, modularPhi_lattice_mobius M k l τ hτ,
    m37c_exp_lattice_shift (e (etaMobius M τ)) (etaMobius M τ) _ rfl]
  rw [zpow_add₀ (e_ne_zero _)]
  ring

lemma m37c_qProduct_eq_repair_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n)
    (z τ : ℂ) (hτ : 0 < τ.im) :
    (fun w => modularPhiQProduct M m n w τ) =ᶠ[𝓝[≠] z]
      (fun w => (if 1 ≤ k + m then 1 else modularPhiCommonZeroFactor
        (w - (k : ℂ) * τ - (l : ℂ)) (etaDenom M τ)) *
          modularPhiLatticeQRegularPart M (k + m)
            (w - (k : ℂ) * τ - (l : ℂ)) τ) := by
  have hdom : τ ∈ modularPhiDomain M := mem_modularPhiDomain_of_im_pos M hM hτ
  have hηim : 0 < (etaMobius M τ).im := m37c_upper_mobius M τ hτ
  have hev : ∀ᶠ w : ℂ in 𝓝[≠] z, w ≠ (k : ℂ) * τ + (l : ℂ) := by
    by_cases hz : z = (k : ℂ) * τ + (l : ℂ)
    · subst z
      exact self_mem_nhdsWithin
    · have hopen : IsOpen {w : ℂ | w ≠ (k : ℂ) * τ + (l : ℂ)} := isOpen_ne
      have he : ∀ᶠ w : ℂ in 𝓝 z, w ≠ (k : ℂ) * τ + (l : ℂ) := hopen.mem_nhds hz
      exact he.filter_mono nhdsWithin_le_nhds
  filter_upwards [hev] with w hw
  unfold modularPhiQProduct
  rw [m37c_qNumerator_lattice m k l w τ,
    m37c_qDenominator_lattice M n k l w τ hdom, ← hbalance]
  rw [m37c_qTail_factor _ _ _ (norm_pos_iff.mpr (e_ne_zero τ)) (norm_e_lt_one ⟨τ, hτ⟩),
    m37c_qTail_factor _ _ _ (norm_pos_iff.mpr (e_ne_zero _)) (norm_e_lt_one ⟨_, hηim⟩)]
  by_cases hr : 1 ≤ k + m
  · simp [hr, modularPhiLatticeQRegularPart]
  · have hζ : w - (k : ℂ) * τ - (l : ℂ) ≠ 0 := by
      intro hh
      apply hw
      linear_combination hh
    simp only [hr, if_false, modularPhiCommonZeroFactor, hζ, modularPhiLatticeQRegularPart]
    exact (div_mul_div_comm _ _ _ _).symm

lemma m37c_no_poles_of_nonneg_order (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (ho : 0 ≤ meromorphicOrderAt (fun w => modularPhi M m n w τ) z) :
    modularPhiPoleMultiplicity M m n z τ = 0 := by
  by_contra hp
  have hpne : (modularPhiPoleIndices M m n z τ).Nonempty := by
    by_contra hh
    have he : modularPhiPoleIndices M m n z τ = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
    exact hp (by simp [modularPhiPoleMultiplicity, he])
  obtain ⟨p, hpLabel, hpEq⟩ := hpne
  have hzi : modularPhiZeroIndices M m n z τ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hdis := modularPhiDivisor_disjoint M hM m n τ hτ
    exact Set.disjoint_left.mp hdis
      ⟨p, hpLabel, hpEq.symm⟩ ⟨q, hq.1, hq.2.symm⟩
  have hz : modularPhiZeroMultiplicity M m n z τ = 0 := by
    simp [modularPhiZeroMultiplicity, hzi]
  rw [modularPhi_order M hM m n z τ hτ, modularPhiDivisorOrder, hz] at ho
  have hcast : (0 : ℤ) ≤ -(modularPhiPoleMultiplicity M m n z τ : ℤ) := by
    simp only [Nat.cast_zero, zero_sub] at ho
    exact_mod_cast ho
  omega

lemma m37c_eq_of_analytic_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g z)
    (heq : (fun w => modularPhi M m n w τ) =ᶠ[𝓝[≠] z] g) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2) (z, τ) ∧
      modularPhi M m n z τ = g z := by
  have ho : 0 ≤ meromorphicOrderAt (fun w => modularPhi M m n w τ) z := by
    rw [meromorphicOrderAt_congr heq]
    exact hg.meromorphicOrderAt_nonneg
  have hp := m37c_no_poles_of_nonneg_order M hM m n z τ hτ ho
  have hreg : (z, τ) ∈ modularPhiRegularDomain M m n := by
    refine ⟨hτ, ?_⟩
    apply Finset.sum_eq_zero_iff.mp
    rw [← (modularPhi_multiplicity_pullback M hM m n z τ hτ).1]
    exact hp
  have hjoint : AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2) (z, τ) :=
    modularPhi_joint_analytic_regular M hM m n (z, τ) hreg
  refine ⟨hjoint, ?_⟩
  have hemb : AnalyticAt ℂ (fun w : ℂ => (w, τ)) z := by fun_prop
  have hs : AnalyticAt ℂ (fun w => modularPhi M m n w τ) z := by
    have hh := hjoint.comp (x := z) hemb
    simpa only [Function.comp_def] using hh
  exact (hs.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hg.continuousAt).mp heq |>.eq_of_nhds

/--
Explicit upper-half-plane local cancellation, including the center
on the whole moving curve z=kτ+l. For r≤0 this uses the separately
regularized factor with center T; for r≥1 there is no zero term.
[RW26, p. 2, p. 12, (1)].
This is pointwise equality of the specified Φ on a joint neighborhood,
stronger than a fixed-τ punctured-germ assertion.
-/
theorem modularPhi_lattice_upper_local_factorization (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n)
    (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ ((k : ℂ) * τ + (l : ℂ), τ) ∈ U ∧
      U ⊆ {p | 0 < p.2.im} ∧
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiLatticeQRegularPart M (k + m)
        (p.1 - (k : ℂ) * p.2 - (l : ℂ)) p.2) U ∧
      (∀ p ∈ U, modularPhiLatticeQRegularPart M (k + m)
        (p.1 - (k : ℂ) * p.2 - (l : ℂ)) p.2 ≠ 0) ∧
      (∀ p ∈ U, modularPhi M m n p.1 p.2 =
        (if 1 ≤ k + m then 1 else modularPhiCommonZeroFactor
          (p.1 - (k : ℂ) * p.2 - (l : ℂ)) (etaDenom M p.2)) *
          modularPhiLatticeQRegularPart M (k + m)
            (p.1 - (k : ℂ) * p.2 - (l : ℂ)) p.2) := by
  let p₀ : ℂ × ℂ := ((k : ℂ) * τ + (l : ℂ), τ)
  let F : ℂ × ℂ → ℂ := fun p => modularPhiLatticeQRegularPart M (k + m)
    (p.1 - (k : ℂ) * p.2 - (l : ℂ)) p.2
  let H : ℂ × ℂ → ℂ := fun p =>
    (if 1 ≤ k + m then 1 else modularPhiCommonZeroFactor
      (p.1 - (k : ℂ) * p.2 - (l : ℂ)) (etaDenom M p.2)) * F p
  have hF : AnalyticAt ℂ F p₀ := m37c_regularPart_moving_analytic M hM (k + m) k l τ hτ
  have hH : AnalyticAt ℂ H p₀ := m37c_repair_moving_analytic M hM (k + m) k l τ hτ
  have hFne : F p₀ ≠ 0 := by
    change modularPhiLatticeQRegularPart M (k + m)
      ((k : ℂ) * τ + (l : ℂ) - (k : ℂ) * τ - (l : ℂ)) τ ≠ 0
    rw [show (k : ℂ) * τ + (l : ℂ) - (k : ℂ) * τ - (l : ℂ) = 0 by ring]
    exact (m37c_regularPart_analytic M hM (k + m) τ hτ).2
  have hopen : IsOpen {p : ℂ × ℂ | 0 < p.2.im} :=
    isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd)
  have hevent : {p : ℂ × ℂ | 0 < p.2.im ∧ AnalyticAt ℂ F p ∧
      F p ≠ 0 ∧ AnalyticAt ℂ H p} ∈ 𝓝 p₀ := by
    filter_upwards [hopen.mem_nhds hτ, hF.eventually_analyticAt,
      hF.continuousAt.eventually_ne hFne, hH.eventually_analyticAt] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨U, hU, hUopen, hp₀⟩ := mem_nhds_iff.mp hevent
  refine ⟨U, hUopen, hp₀, fun p hp => (hU hp).1,
    fun p hp => (hU hp).2.1, fun p hp => (hU hp).2.2.1, ?_⟩
  intro p hp
  have hupper : 0 < p.2.im := (hU hp).1
  have hHa : AnalyticAt ℂ H p := (hU hp).2.2.2
  have hemb : AnalyticAt ℂ (fun w : ℂ => (w, p.2)) p.1 := by fun_prop
  have hg : AnalyticAt ℂ (fun w : ℂ => H (w, p.2)) p.1 := by
    have hh := hHa.comp (x := p.1) hemb
    simpa only [Function.comp_def] using hh
  have heq := (modularPhi_eq_qProduct_germ M hM m n p.1 p.2 hupper).trans
    (m37c_qProduct_eq_repair_germ M hM m n k l hbalance p.1 p.2 hupper)
  exact (m37c_eq_of_analytic_germ M hM m n p.1 p.2
    (mem_modularPhiDomain_of_im_pos M hM hupper) (fun w => H (w, p.2)) hg heq).2

/--
Upper-half-plane center value after cancellation, for both exponent
ranges. It never substitutes z=kτ+l into a raw 0/0.
[RW26, p. 2, p. 12, (1)].
-/
theorem modularPhi_lattice_upper_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n)
    (τ : ℂ) (hτ : 0 < τ.im) :
    modularPhi M m n ((k : ℂ) * τ + (l : ℂ)) τ =
      modularPhiLatticeQValue M (k + m) τ := by
  obtain ⟨U, _, hc, _, _, _, hvalue⟩ :=
    modularPhi_lattice_upper_local_factorization M hM m n k l hbalance τ hτ
  have hz : (k : ℂ) * τ + (l : ℂ) - (k : ℂ) * τ - (l : ℂ) = 0 := by ring
  simpa only [modularPhiLatticeQValue, hz, modularPhiCommonZeroFactor_zero] using
    hvalue _ hc

/-! ## Real hyperbolic fixed points: joint regularity and actual centers -/

/--
Elementary hyperbolic arithmetic required for the lattice sign test
and the finite q factors. [RW26, p. 12].
The positive-trace form is used in (trace=N+2, N>0).
-/
theorem modularPhi_real_fixedPoint_irrational (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ)) : Irrational τ₀ := by
  rintro ⟨q, hq⟩
  have hden : etaDenom M (τ₀ : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [etaDenom] at hre
    linarith
  have hmul : (M 0 0 : ℂ) * (τ₀ : ℂ) + (M 0 1 : ℂ) =
      (τ₀ : ℂ) * ((M 1 0 : ℂ) * (τ₀ : ℂ) + (M 1 1 : ℂ)) := by
    have h := hfix
    rw [etaMobius] at h
    exact (div_eq_iff hden).mp h
  have hquad : (M 1 0 : ℝ) * τ₀ ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * τ₀ - (M 0 1 : ℝ) = 0 := by
    have h := congrArg Complex.re hmul
    simp only [← Complex.ofReal_intCast, Complex.add_re, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_zero] at h
    linear_combination -h
  -- determinant
  have hdet : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    exact_mod_cast det_coe_int M
  -- substitute q
  have hq' : (↑q : ℝ) = τ₀ := hq
  have hquad_q : (M 1 0 : ℝ) * (q:ℝ) ^ 2 + ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * (q:ℝ) - (M 0 1 : ℝ) = 0 := by
    rw [hq']; exact hquad
  -- s squared
  set s : ℚ := 2 * (M 1 0 : ℚ) * q + ((M 1 1 : ℚ) - (M 0 0 : ℚ)) with hs
  have hsq : (s:ℝ) ^ 2 = (M 0 0 : ℝ) ^ 2 + 2 * (M 0 0 : ℝ) * (M 1 1 : ℝ) +
      (M 1 1 : ℝ) ^ 2 - 4 := by
    rw [hs]; push_cast
    linear_combination 4 * (M 1 0 : ℝ) * hquad_q - 4 * hdet
  -- integer t
  set t : ℕ := (M 0 0 + M 1 1).toNat with ht
  have htZ : (t : ℤ) = M 0 0 + M 1 1 := Int.toNat_of_nonneg (by omega)
  have ht3 : 3 ≤ t := by omega
  have htR : ((t:ℝ)) = (M 0 0 : ℝ) + (M 1 1 : ℝ) := by
    have := congrArg (fun z : ℤ => (z:ℝ)) htZ
    push_cast at this
    linarith
  have hD : (s:ℝ) ^ 2 = ((t ^ 2 - 4 : ℕ) : ℝ) := by
    rw [hsq, Nat.cast_sub (by nlinarith : 4 ≤ t ^ 2), Nat.cast_pow]
    push_cast
    rw [htR]; ring
  have hnsq : ¬ IsSquare (t ^ 2 - 4) := by
    rintro ⟨k, hk⟩
    have hkZ : (k : ℤ) ^ 2 = (t : ℤ) ^ 2 - 4 := by
      have h1 : ((k * k : ℕ) : ℤ) = ((t ^ 2 - 4 : ℕ) : ℤ) := by rw [← hk]
      rw [Nat.cast_sub (by nlinarith : 4 ≤ t ^ 2), Nat.cast_pow] at h1
      push_cast at h1
      simpa [pow_two] using h1
    have ht3Z : (3:ℤ) ≤ (t:ℤ) := by omega
    have h1 : ((t : ℤ) - 1) ^ 2 < (k : ℤ) ^ 2 := by
      rw [hkZ]
      have hexp : ((t : ℤ) - 1) ^ 2 = (t:ℤ)^2 - 2*(t:ℤ) + 1 := by ring
      rw [hexp]; nlinarith [ht3Z]
    have h2 : (k : ℤ) ^ 2 < (t : ℤ) ^ 2 := by
      rw [hkZ]; nlinarith
    have hk0 : (0:ℤ) ≤ (k : ℤ) := by positivity
    have ht1 : (0:ℤ) ≤ (t : ℤ) - 1 := by omega
    have ht0 : (0:ℤ) ≤ (t : ℤ) := by omega
    have hklo : (t : ℤ) - 1 < (k : ℤ) := by nlinarith
    have hkhi : (k : ℤ) < (t : ℤ) := by nlinarith
    omega
  have hirr : Irrational (Real.sqrt ((t ^ 2 - 4 : ℕ) : ℝ)) :=
    irrational_sqrt_natCast_iff.mpr hnsq
  have habs : Real.sqrt ((t ^ 2 - 4 : ℕ) : ℝ) = |(s:ℝ)| := by
    rw [← hD, ← sq_abs]
    exact Real.sqrt_sq (abs_nonneg _)
  apply hirr
  refine ⟨|s|, ?_⟩
  rw [habs]
  push_cast
  rfl

/--
Equal common lattice exponents exclude both actual divisor families.
[RW26, p. 6, p. 12].
Kept in fixed-point form for callers; no rational-real generalization.
-/
theorem modularPhi_fixedPoint_lattice_divisor_free (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (m n : ℤ) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n) :
    ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ), (τ₀ : ℂ)) ∈
      modularPhiNonvanishingDomain M m n := by
  have hirr := modularPhi_real_fixedPoint_irrational M hM htrace τ₀ hT hfix
  obtain ⟨hp, hz⟩ := modularPhi_real_lattice_multiplicity M hM m n τ₀ hirr hT k l
  refine ⟨real_mem_modularPhiDomain M τ₀ hT, ?_, ?_⟩
  · rw [hp, if_neg (by omega)]
  · rw [hz, if_neg (by omega)]

/--
Joint removability/nonvanishing for the actual finite product,
including its center, and for all approaches in ℂ².
[RW26, p. 12].
Neither only a fixed-τ germ nor an η boundary value is assumed.
-/
theorem modularPhi_fixedPoint_lattice_joint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (m n : ℤ) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧
      ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ), (τ₀ : ℂ)) ∈ U ∧
      U ⊆ modularPhiNonvanishingDomain M m n ∧
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2) U ∧
      (∀ p ∈ U, modularPhi M m n p.1 p.2 ≠ 0) := by
  exact modularPhi_joint_unit_neighborhood M hM m n _
    (modularPhi_fixedPoint_lattice_divisor_free M hM htrace m n τ₀ hT hfix k l hbalance)

def m37c_qCorrection (r : ℤ) (q : ℂ) : ℂ :=
  if 1 ≤ r then (qPochhammerNat q q (r - 1).toNat)⁻¹
  else qPochhammerNat (q ^ r) q (-r).toNat

lemma m37c_qpow_ne_one (t : ℝ) (ht : Irrational t) (k : ℤ) (hk : k ≠ 0) :
    (e (t : ℂ)) ^ k ≠ 1 := by
  intro h
  rw [e_int_mul] at h
  obtain ⟨l, hl⟩ := e_eq_one_iff_int h
  have hlr : (k : ℝ) * t = (l : ℝ) := by
    simpa using congrArg Complex.re hl
  exact (ht.intCast_mul hk).ne_int l hlr

lemma m37c_finite_ne_zero (t : ℝ) (ht : Irrational t) (r : ℤ) (n : ℕ)
    (hn : ∀ j < n, r + (j : ℤ) ≠ 0) :
    qPochhammerNat ((e (t : ℂ)) ^ r) (e (t : ℂ)) n ≠ 0 := by
  unfold qPochhammerNat
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hjzero
  apply m37c_qpow_ne_one t ht (r + (j : ℤ)) (hn j (Finset.mem_range.mp hj))
  rw [zpow_add₀ (e_ne_zero _), zpow_natCast]
  exact hjzero.symm

lemma m37c_qCorrection_ne_zero (t : ℝ) (ht : Irrational t) (r : ℤ) :
    m37c_qCorrection r (e (t : ℂ)) ≠ 0 := by
  unfold m37c_qCorrection
  split_ifs with hr
  · apply inv_ne_zero
    simpa only [zpow_one] using
      m37c_finite_ne_zero t ht 1 (r - 1).toNat (by intro j hj; omega)
  · apply m37c_finite_ne_zero t ht r (-r).toNat
    intro j hj
    omega

lemma m37c_finite_continuousAt (r : ℤ) (n : ℕ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0) :
    ContinuousAt (fun q : ℂ => qPochhammerNat (q ^ r) q n) q₀ := by
  unfold qPochhammerNat
  apply tendsto_finsetProd
  intro j hj
  exact continuousAt_const.sub
    ((continuousAt_id.zpow₀ r (Or.inl hq₀)).mul (continuousAt_id.pow j))

lemma m37c_qCorrection_continuousAt (t : ℝ) (ht : Irrational t) (r : ℤ) :
    ContinuousAt (m37c_qCorrection r) (e (t : ℂ)) := by
  unfold m37c_qCorrection
  split_ifs with hr
  · apply ContinuousAt.inv₀
    · simpa only [zpow_one] using
        m37c_finite_continuousAt 1 (r - 1).toNat (e (t : ℂ)) (e_ne_zero _)
    · simpa only [zpow_one] using
        m37c_finite_ne_zero t ht 1 (r - 1).toNat (by intro j hj; omega)
  · exact m37c_finite_continuousAt r (-r).toNat _ (e_ne_zero _)

lemma m37c_qTail_zero (r : ℤ) (q : ℂ) (hq₀ : 0 < ‖q‖) (hq₁ : ‖q‖ < 1) :
    modularPhiLatticeQTail r 0 q = m37c_qCorrection r q * qPochhammer q q := by
  have he₀ : e 0 = 1 := by simp [e]
  unfold modularPhiLatticeQTail m37c_qCorrection
  simp only [he₀, mul_one]
  split_ifs with hr
  · have hq : q ≠ 0 := norm_pos_iff.mp hq₀
    have hN : ((r - 1).toNat : ℤ) = r - 1 := Int.toNat_of_nonneg (by omega)
    have hp : q * q ^ (r - 1).toNat = q ^ r := by
      calc
        q * q ^ (r - 1).toNat = q ^ (1 : ℤ) * q ^ ((r - 1).toNat : ℤ) := by simp
        _ = q ^ ((1 : ℤ) + ((r - 1).toNat : ℤ)) := (zpow_add₀ hq _ _).symm
        _ = q ^ r := by congr 1; omega
    have hs := qPochhammer_shift_nat q q (r - 1).toNat hq₀ hq₁
    rw [hp] at hs
    rw [hs]
    simp only [← mul_assoc, inv_mul_cancel₀
      (qPochhammerNat_q_ne_zero q (r - 1).toNat hq₀ hq₁), one_mul]
  · rfl

lemma m37c_qValue_upper (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r : ℤ) (z : ℂ) (hz : 0 < z.im) :
    modularPhiLatticeQValue M r z =
      (if 1 ≤ r then etaPhase M z / etaDenom M z else etaPhase M z) *
        (m37c_qCorrection r (e z) / m37c_qCorrection r (e (etaMobius M z))) := by
  let τ : ℍ := ⟨z, hz⟩
  have hq₁ : ‖e z‖ < 1 := norm_e_lt_one τ
  have hQ₁ : ‖e (etaMobius M z)‖ < 1 := by
    change ‖e (etaMobius M τ)‖ < 1
    rw [← coe_smul_eq_etaMobius]
    exact norm_e_lt_one (M • τ)
  have hQ : qPochhammer (e (etaMobius M z)) (e (etaMobius M z)) ≠ 0 :=
    qPochhammer_q_ne_zero _ (norm_pos_iff.mpr (e_ne_zero _)) hQ₁
  have hpref : etaDenom M z *
      (qPochhammer (e z) (e z) /
        qPochhammer (e (etaMobius M z)) (e (etaMobius M z))) = etaPhase M z :=
    qPochhammer_eta_prefactor M hM τ hQ
  have hratio : qPochhammer (e z) (e z) /
      qPochhammer (e (etaMobius M z)) (e (etaMobius M z)) =
      etaPhase M z / etaDenom M z := by
    apply (eq_div_iff (etaDenom_ne_zero M hM τ)).mpr
    simpa only [mul_comm] using hpref
  unfold modularPhiLatticeQValue modularPhiLatticeQRegularPart
  simp only [zero_div]
  rw [m37c_qTail_zero r (e z) (norm_pos_iff.mpr (e_ne_zero _)) hq₁,
    m37c_qTail_zero r (e (etaMobius M z))
      (norm_pos_iff.mpr (e_ne_zero _)) hQ₁,
    mul_div_mul_comm]
  split_ifs with hr
  · rw [one_mul, hratio]
    ring
  · calc
      etaDenom M z *
          (m37c_qCorrection r (e z) / m37c_qCorrection r (e (etaMobius M z)) *
            (qPochhammer (e z) (e z) /
              qPochhammer (e (etaMobius M z)) (e (etaMobius M z)))) =
          (etaDenom M z *
            (qPochhammer (e z) (e z) /
              qPochhammer (e (etaMobius M z)) (e (etaMobius M z)))) *
            (m37c_qCorrection r (e z) / m37c_qCorrection r (e (etaMobius M z))) := by
          ring
      _ = _ := by rw [hpref]

lemma m37c_qValue_tendsto_aux (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r : ℤ) (τ₀ : ℝ) (hτ₀ : Irrational τ₀)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ)) :
    Tendsto (modularPhiLatticeQValue M r)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (if 1 ≤ r then
        (etaMultiplier M)⁻¹ /
          (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ)
      else (etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ))) := by
  have hD : etaDenom M (τ₀ : ℂ) =
      (((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ) : ℝ) : ℂ) := by
    simp [etaDenom]
  have hD₀ : etaDenom M (τ₀ : ℂ) ≠ 0 := by
    rw [hD]
    exact_mod_cast ne_of_gt hT
  have hden : Continuous (etaDenom M) := by unfold etaDenom; fun_prop
  have he : Continuous e := by unfold e; fun_prop
  have hmob : ContinuousAt (etaMobius M) (τ₀ : ℂ) := by
    unfold etaMobius
    exact (by fun_prop : ContinuousAt
      (fun z : ℂ => (M 0 0 : ℂ) * z + (M 0 1 : ℂ)) (τ₀ : ℂ)).div
        hden.continuousAt hD₀
  have hmoblim : Tendsto (etaMobius M) (𝓝 (τ₀ : ℂ)) (𝓝 (τ₀ : ℂ)) := by
    simpa only [hfix] using hmob.tendsto
  have hC := m37c_qCorrection_continuousAt τ₀ hτ₀ r
  have hC₀ := m37c_qCorrection_ne_zero τ₀ hτ₀ r
  have hC₁ : Tendsto (fun z : ℂ => m37c_qCorrection r (e z))
      (𝓝 (τ₀ : ℂ)) (𝓝 (m37c_qCorrection r (e (τ₀ : ℂ)))) :=
    hC.tendsto.comp he.continuousAt.tendsto
  have hC₂ : Tendsto (fun z : ℂ => m37c_qCorrection r (e (etaMobius M z)))
      (𝓝 (τ₀ : ℂ)) (𝓝 (m37c_qCorrection r (e (τ₀ : ℂ)))) :=
    hC₁.comp hmoblim
  have hClim : Tendsto
      (fun z : ℂ => m37c_qCorrection r (e z) /
        m37c_qCorrection r (e (etaMobius M z)))
      (𝓝 (τ₀ : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa only [Pi.div_def, div_self hC₀] using hC₁.div hC₂ hC₀
  have hphase := etaPhase_tendsto_real_fixedPoint M τ₀ hT hfix
  have hpref : Tendsto
      (fun z : ℂ => if 1 ≤ r then etaPhase M z / etaDenom M z else etaPhase M z)
      (𝓝 (τ₀ : ℂ))
      (𝓝 (if 1 ≤ r then
        (etaMultiplier M)⁻¹ /
          (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ)
      else (etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ))) := by
    split_ifs with hr
    · have hs₀ : (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
      have hs : (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) ^ 2 =
          etaDenom M (τ₀ : ℂ) := by
        rw [hD]
        exact_mod_cast Real.sq_sqrt hT.le
      have hv :
          ((etaMultiplier M)⁻¹ *
            (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ)) /
              etaDenom M (τ₀ : ℂ) =
          (etaMultiplier M)⁻¹ /
            (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) := by
        rw [← hs]
        field_simp
      simpa only [Pi.div_def, hv] using
        hphase.div hden.continuousAt.tendsto hD₀
    · exact hphase
  have hlim := hpref.mul hClim
  simp only [mul_one] at hlim
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (m37c_qValue_upper M hM r z hz).symm

/--
η-free upper approach to a real fixed point. No real η limit is
asserted; use `etaPhase_real_fixedPoint` and finite nonzero q factors.
[RW26, p. 12].
-/
theorem modularPhiLatticeQValue_tendsto_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (r : ℤ) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ)) :
    Tendsto (modularPhiLatticeQValue M r)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (if 1 ≤ r then
        (etaMultiplier M)⁻¹ /
          (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ)
      else (etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ))) := by
  exact m37c_qValue_tendsto_aux M hM r τ₀
    (modularPhi_real_fixedPoint_irrational M hM htrace τ₀ hT hfix) hT hfix

lemma m37c_real_upper_neBot (τ₀ : ℝ) :
    NeBot (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(τ₀ : ℂ) + (ε / 2 : ℝ) * Complex.I, ?_, ?_⟩
  · simpa using half_pos hε
  · simpa [dist_eq_norm, Complex.norm_mul, abs_of_pos hε] using half_lt_self hε

/--
The specified Φ center, with r=k+m=k′+n. This is not an assignment
by definition and not a conclusion from punctured equality alone.
[RW26, p. 12]. Both real fixed points are covered.
The statement keeps the stated hypotheses on τ.
-/
theorem modularPhi_fixedPoint_lattice_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (m n : ℤ) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n) :
    modularPhi M m n ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ)) (τ₀ : ℂ) =
      if 1 ≤ k + m then
        (etaMultiplier M)⁻¹ /
          (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ)
      else (etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) := by
  obtain ⟨U, _, hp, _, hanalytic, _⟩ :=
    modularPhi_fixedPoint_lattice_joint M hM htrace m n τ₀ hT hfix k l hbalance
  have hcurve : ContinuousAt
      (fun τ : ℂ => ((k : ℂ) * τ + (l : ℂ), τ)) (τ₀ : ℂ) := by fun_prop
  have hcenter := (hanalytic _ hp).continuousAt.tendsto.comp hcurve.tendsto
  haveI := m37c_real_upper_neBot τ₀
  refine tendsto_nhds_unique_of_eventuallyEq
    (hcenter.mono_left nhdsWithin_le_nhds)
    (modularPhiLatticeQValue_tendsto_fixedPoint M hM htrace (k + m) τ₀ hT hfix) ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact modularPhi_lattice_upper_value M hM m n k l hbalance τ hτ

/--
The r≥1 specialization. [RW26, p. 12].
-/
theorem modularPhi_fixedPoint_lattice_value_of_pos (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (m n : ℤ) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n)
    (hr : 1 ≤ k + m) :
    modularPhi M m n ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ)) (τ₀ : ℂ) =
      (etaMultiplier M)⁻¹ /
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) := by
  simpa only [if_pos hr] using
    modularPhi_fixedPoint_lattice_value M hM htrace m n τ₀ hT hfix k l hbalance

/--
r≤0 specialization, after common-zero cancellation.
[RW26, p. 12].
-/
theorem modularPhi_fixedPoint_lattice_value_of_nonpos (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (m n : ℤ) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n)
    (hr : k + m ≤ 0) :
    modularPhi M m n ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ)) (τ₀ : ℂ) =
      (etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) := by
  simpa only [if_neg (show ¬ 1 ≤ k + m by omega)] using
    modularPhi_fixedPoint_lattice_value M hM htrace m n τ₀ hT hfix k l hbalance

/--
Ordinary two-variable limit to the specified center, with no deleted
divisor or special approach curve. Local regularity supplies a full
neighborhood. [RW26, p. 12].
-/
theorem modularPhi_fixedPoint_lattice_tendsto (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (m n : ℤ) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ))
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (k l : ℤ) (hbalance : k + m = M 1 1 * k - M 1 0 * l + n) :
    Tendsto (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2)
      (𝓝 ((k : ℂ) * (τ₀ : ℂ) + (l : ℂ), (τ₀ : ℂ)))
      (𝓝 (if 1 ≤ k + m then
        (etaMultiplier M)⁻¹ /
          (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ)
      else (etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ))) := by
  obtain ⟨U, _, hp, _, hanalytic, _⟩ :=
    modularPhi_fixedPoint_lattice_joint M hM htrace m n τ₀ hT hfix k l hbalance
  have hlimit := (hanalytic _ hp).continuousAt.tendsto
  rw [modularPhi_fixedPoint_lattice_value M hM htrace m n τ₀ hT hfix k l hbalance]
    at hlimit
  exact hlimit

/-! Pinned type checks, not proof obligations or new axioms. -/
#check Int.ModEq
#check Set.BijOn
#check Nat.card
#check meromorphicOrderAt
#check modularPhi_meromorphic
#check modularPhi_joint_local_quotient
#check modularPhi_joint_analytic_regular
#check phiExtended_order
#check phiExtended_pole_value
#check etaPhase_real_fixedPoint
#print modularPhiPoleLabels
#print modularPhiPolePoint
#print modularPhiPoleMultiplicity
#print modularPhiCommonZeroFactor
#print modularPhiLatticeQTail
#check modularPhi_order
#check modularPhi_fixedPoint_lattice_value

end SICLean.L4
