import SICLean.L5.PrimeFiniteModel
import SICLean.L5.PrimeUnits

set_option autoImplicit false

/-!
# Reduction of actual algebraic complex values

The reductions use the existing `Galois.algebraicLift` and `embed_algebraicLift` from
AlgebraicClosure.lean. [RW-rec, Prop. 4, p. 14]; local use
[RW-rec, Thm. 7--8, pp. 12--13]. [RW26, Thm. 1, p. 3], pp. 2--3 definition (2), and pp.
22--23. Here z ranges over the already defined point values, e.g. M72.value, together with
q, B, etaMultiplier, e and Fourier coefficients via finite sum index types when needed.
Nothing here evaluates a punctured germ or redefines
modularPhi/phiExtended/etaMultiplier or the square-root branch. Algebraicity is explicit
input; local unit properties of E are conclusions established separately, not hypotheses
of the finite-field choice.
-/

noncomputable section

namespace SICLean.L5.FinitePlace

open scoped Classical

variable {ι : Type*} [Fintype ι]

/-- Exactly the algebraic preimages of the supplied actual complex point values. -/
def familyGenerators (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) : Finset Galois.Qbar :=
  Finset.univ.image (fun i => Galois.algebraicLift (z i) (hz i))

/-- A common finite field for the entire indexed family. -/
abbrev FamilyField (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) :=
  generatedField (familyGenerators z hz)

/-- Every actual preimage is among the explicit generators. -/
theorem familyLift_mem (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) (i : ι) :
    Galois.algebraicLift (z i) (hz i) ∈ familyGenerators z hz := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- A point value in its concrete common number field. -/
def familyElement (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) (i : ι) : FamilyField z hz :=
  fieldElement (familyGenerators z hz) (Galois.algebraicLift (z i) (hz i)) (familyLift_mem z hz i)

/-- This is the same complex value under the fixed embedding. -/
theorem familyElement_embed (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) (i : ι) :
    Galois.embed (familyElement z hz i : Galois.Qbar) = z i := by
  exact Galois.embed_algebraicLift (z i) (hz i)

/-- Actual nonvanishing can be transported without changing the chosen algebraic preimage. -/
theorem familyElement_ne_zero_iff (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) (i : ι) :
    familyElement z hz i ≠ 0 ↔ z i ≠ 0 := by
  rw [← familyElement_embed z hz i]
  exact (map_ne_zero (Galois.embed.comp (FamilyField z hz).val)).symm

/-- Exact products of point values transport to the same finite field. -/
theorem familyElement_mul (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) (i j k : ι)
    (h : z i * z j = z k) : familyElement z hz i * familyElement z hz j = familyElement z hz k := by
  apply (FamilyField z hz).val.injective
  apply Galois.embed.injective
  change Galois.embed ((familyElement z hz i : Galois.Qbar) *
    (familyElement z hz j : Galois.Qbar)) = Galois.embed (familyElement z hz k : Galois.Qbar)
  rw [map_mul, familyElement_embed, familyElement_embed, familyElement_embed]
  exact h

/-- Exact ratios transport before any reduction is performed. -/
theorem familyElement_div (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) (i j k : ι)
    (h : z i / z j = z k) : familyElement z hz i / familyElement z hz j = familyElement z hz k := by
  apply (FamilyField z hz).val.injective
  apply Galois.embed.injective
  change Galois.embed ((familyElement z hz i : Galois.Qbar) /
    (familyElement z hz j : Galois.Qbar)) = Galois.embed (familyElement z hz k : Galois.Qbar)
  rw [map_div₀, familyElement_embed, familyElement_embed, familyElement_embed]
  exact h

/-- Period powers and root relations can be transported without a new branch choice. -/
theorem familyElement_pow (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) (i j : ι) (n : ℕ)
    (h : z i ^ n = z j) : familyElement z hz i ^ n = familyElement z hz j := by
  apply (FamilyField z hz).val.injective
  apply Galois.embed.injective
  change Galois.embed ((familyElement z hz i : Galois.Qbar) ^ n) =
    Galois.embed (familyElement z hz j : Galois.Qbar)
  rw [map_pow, familyElement_embed, familyElement_embed]
  exact h

/-- A known complex root relation gives local unit evidence for its preimage. -/
theorem familyRoot_unitAt (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i))
    (P : Prime (FamilyField z hz)) (i : ι) (n : ℕ) (hn : n ≠ 0) (h : z i ^ n = 1) :
    UnitAt P (familyElement z hz i) := by
  apply root_unitAt P hn
  apply (FamilyField z hz).val.injective
  apply Galois.embed.injective
  change Galois.embed ((familyElement z hz i : Galois.Qbar) ^ n) = Galois.embed 1
  rw [map_pow, map_one, familyElement_embed]
  exact h

/-- Its actual reduction is nonzero, with no prime-to-n restriction. -/
theorem familyRoot_red_ne_zero (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i))
    (P : Prime (FamilyField z hz)) (i : ι) (n : ℕ) (hn : n ≠ 0) (h : z i ^ n = 1)
    (hi : IntegralAt P (familyElement z hz i)) : red P (familyElement z hz i) hi ≠ 0 := by
  exact (red_ne_zero_iff P (familyElement z hz i) hi).mpr
    (familyRoot_unitAt z hz P i n hn h)

/-- One reduction function, one field and one prime for all labels. -/
def reducedFamily (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i))
    (P : Prime (FamilyField z hz)) (hi : ∀ i, IntegralAt P (familyElement z hz i)) : ι → Residue P :=
  fun i => red P (familyElement z hz i) (hi i)

/-- Equality of reductions is literally the required mod-P congruence of actual lifts. -/
theorem reducedFamily_eq_iff (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i))
    (P : Prime (FamilyField z hz)) (hi : ∀ i, IntegralAt P (familyElement z hz i)) (i j : ι) :
    reducedFamily z hz P hi i = reducedFamily z hz P hi j ↔
      Congruent P (familyElement z hz i) (familyElement z hz j) := by
  exact red_eq_iff P (familyElement z hz i) (familyElement z hz j) (hi i) (hi j)

/-- Directly usable for U=E/e and R_h, once proves the denominator a unit. -/
theorem reducedFamily_ratio (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i))
    (P : Prime (FamilyField z hz)) (hi : ∀ i, IntegralAt P (familyElement z hz i))
    (i j k : ι) (hj : UnitAt P (familyElement z hz j)) (h : z i / z j = z k) :
    reducedFamily z hz P hi k = reducedFamily z hz P hi i / reducedFamily z hz P hi j := by
  have hdiv := red_div P (hi i) hj
  simpa only [familyElement_div z hz i j k h, reducedFamily] using hdiv

/-- Selecting a place once for the family gives the requested characteristic. -/
theorem family_chosenPrime_char (z : ι → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i))
    (p : ℕ) (hp : p.Prime) : residueChar (chosenPrime (FamilyField z hz) p hp) = p := by
  exact chosenPrime_char (FamilyField z hz) p hp

end SICLean.L5.FinitePlace

#check @SICLean.Galois.embed_algebraicLift
#check @SICLean.L5.FinitePlace.familyElement_embed
#check @SICLean.L5.FinitePlace.reducedFamily_ratio
#print SICLean.L5.FinitePlace.familyGenerators
#print SICLean.L5.FinitePlace.reducedFamily
