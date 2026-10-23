import SICLean.L5.ActualPseudolattice
import SICLean.L5.ActualValueBridgeAux

set_option autoImplicit false

/-!
# Intrinsic Gaussian, actual point values, and fixed Qbar lifts

Coordinates are taken in the oriented basis (tau, 1). The Gaussian is the
sum in [RW-rec, (2)]. Its agreement with the matrix Gaussian is a theorem.
Actual values use `M72.value`, `modularPhi`, `phiExtended`, and `etaMultiplier`.
A punctured germ is kept off its center, and the origin is prescribed.

Sources: [RW26, p. 2, (2); p. 3, (3)--(4), footnote 2; Lemma 2, p. 12; (37), p. 20];
[RW-rec, Def. 1, (2), Prop. 1].
-/

noncomputable section
open scoped Classical MatrixGroups

namespace SICLean.L5.ActualValues

open ActualField ActualLattice

/-- The two coefficients of x in the actual basis (tau,1), via both embeddings. -/
def coordinates (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM) : ℝ × ℝ :=
  ((sigma₁ M hM x - sigma₂ M hM x) /
      (L4.specialValueTau M - conjugateTau M),
    (L4.specialValueTau M * sigma₂ M hM x - conjugateTau M * sigma₁ M hM x) /
      (L4.specialValueTau M - conjugateTau M))

def omega (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x y : baseField M hM) : ℝ :=
  (coordinates M hM x).1 * (coordinates M hM y).2 -
    (coordinates M hM x).2 * (coordinates M hM y).1

def latticeSign (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM) : ℂ :=
  if x ∈ L3.pseudolatticeScale (2 : baseField M hM) (lattice M hM) then 1 else -1

def gaussianAt (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM) : ℂ :=
  latticeSign M hM ((epsilon M hM - 1) * x) *
    L4.e ((omega M hM x (epsilon M hM * x) / 2 : ℝ) : ℂ)

def gaussian (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : ActualLattice.Group M hM) : ℂ :=
  gaussianAt M hM (L3.pseudolatticeRepresentative (periodData M hM) (stableLattice M hM) g)

/-- Coordinates of the oriented basis (tau, 1). [RW26, p. 3, (3)]; [RW-rec, (2)]. -/
theorem coordinates_basis (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    coordinates M hM (tau M hM) = (1, 0) ∧
      coordinates M hM 1 = (0, 1) := by
  constructor
  · change ActualValueBridgeAux.coord M hM (tau M hM) = (1, 0)
    simpa only [Rat.cast_one, Rat.cast_zero, one_mul, add_zero] using
      ActualValueBridgeAux.coord_rat M hM 1 0
  · change ActualValueBridgeAux.coord M hM 1 = (0, 1)
    simpa only [Rat.cast_one, Rat.cast_zero, zero_mul, zero_add] using
      ActualValueBridgeAux.coord_rat M hM 0 1

/-- The Gaussian is unchanged by lattice periods.
[RW26, p. 3, (3)]; [RW-rec, (2)]. -/
theorem gaussianAt_periodic (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x t : baseField M hM)
    (hx : x ∈ L3.pseudolatticePeriodPoints (periodData M hM) (stableLattice M hM))
    (ht : t ∈ lattice M hM) : gaussianAt M hM (x + t) = gaussianAt M hM x := by
  exact ActualValueBridgeAux.qAt_periodic M hM x t hx ht

/-- Termwise agreement of [RW-rec, (2)] and [RW26, (3), p. 3], including the
parity sign and the denominator 2N. -/
theorem gaussian_label (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) :
    gaussian M hM (labelEquiv M hM g) = L4.specialValueGaussian M hM g := by
  exact ActualValueBridgeAux.qAt_representative_label M hM g

/-- The origin has Gaussian 1. [RW26, p. 3, (3)]; [RW-rec, (2)]. -/
theorem gaussian_zero (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    gaussian M hM 0 = 1 := by
  simpa only [map_zero] using
    (gaussian_label M hM 0).trans (L3.M74.gaussian_zero M hM)

def value (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    ActualLattice.Group M hM → ℂ :=
  L3.M72.value (periodData M hM) (stableLattice M hM)

def minusValue (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    ActualLattice.Group M hM → ℂ :=
  L3.M72.minusValue (periodData M hM) (stableLattice M hM)

/-- Point values agree on every label, including zero.
[RW26, p. 2, (2); p. 3, (4)]; [RW-rec, Def. 1]. -/
theorem value_label (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) :
    value M hM (labelEquiv M hM g) = L4.specialValuePlus M hM g := by
  exact (L3.M72.matrixToK_values (periodData M hM) M hM (order_nat M hM).2 g).1

/-- The same identification for the inverse origin.
[RW26, p. 3, footnote 2]; [RW-rec, Def. 1]. -/
theorem minusValue_label (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) :
    minusValue M hM (labelEquiv M hM g) = L4.specialValueMinus M hM g := by
  exact (L3.M72.matrixToK_values (periodData M hM) M hM (order_nat M hM).2 g).2

/-- The value at zero is the positive square root of epsilon.
[RW26, p. 3, (4), footnote 2]; [RW-rec, Def. 1]. -/
theorem value_zero (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    value M hM 0 = (Real.sqrt (L4.specialValueEpsilon M) : ℂ) := by
  simpa only [map_zero, L4.specialValuePlus_zero] using value_label M hM 0

/-- Off zero, the value is mu*Phi. [RW26, p. 2, (2); (37), p. 20]; [RW-rec, Def. 1]. -/
theorem value_nonzero_formula (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ L4.specialValueLattice M) :
    value M hM (labelEquiv M hM (L4.specialValueMk M u)) =
      L4.etaMultiplier M * L4.modularPhi M u.1 0
        (L4.specialValueArgument M u) (L4.specialValueTau M : ℂ) := by
  rw [value_label, L4.specialValuePlus_mk]
  exact if_neg hu

/-- Algebraicity of the matrix point values, using G1, before Prop. 7.
[RW26, Thm. 1, p. 3]; [RW-rec, Prop. 1]. -/
theorem matrixValue_isAlgebraic (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) : IsAlgebraic ℚ (L4.specialValuePlus M hM g) := by
  exact (L3.M78.Transport.chosenFamily_specialValues_isAlgebraic (periodData M hM)
    (FinalAssembly.familyPentagon_of_G1 L4.g1RealConclusion
      (L3.chosenPseudolatticeFamily (periodData M hM)))
    M hM (order_nat M hM).2 g).1

/-- Algebraicity of the same values. Same sources as `matrixValue_isAlgebraic`. -/
theorem value_isAlgebraic (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : ActualLattice.Group M hM) : IsAlgebraic ℚ (value M hM g) := by
  obtain ⟨x, rfl⟩ := (labelEquiv M hM).surjective g
  rw [value_label]
  exact matrixValue_isAlgebraic M hM x

def valueLift (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : ActualLattice.Group M hM) : Galois.Qbar :=
  Galois.algebraicLift (value M hM g) (value_isAlgebraic M hM g)

def matrixLift (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) : Galois.Qbar :=
  Galois.algebraicLift (L4.specialValuePlus M hM g) (matrixValue_isAlgebraic M hM g)

/-- The fixed embedding recovers the value. [RW26, p. 2, (2)]. -/
theorem embed_valueLift (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : ActualLattice.Group M hM) : Galois.embed (valueLift M hM g) = value M hM g := by
  exact Galois.embed_algebraicLift _ _

/-- Matrix point-value recovery under the same embed. Same sources as above. -/
theorem embed_matrixLift (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) :
    Galois.embed (matrixLift M hM g) = L4.specialValuePlus M hM g := by
  exact Galois.embed_algebraicLift _ _

/-- Equality in Qbar, so every automorphism sees the same value. [RW26, p. 2, (2)]. -/
theorem valueLift_label (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) :
    valueLift M hM (labelEquiv M hM g) = matrixLift M hM g := by
  apply Galois.embed.injective
  change Galois.embed (valueLift M hM (labelEquiv M hM g)) = Galois.embed (matrixLift M hM g)
  rw [embed_valueLift, embed_matrixLift, value_label]

/-- Every algebraic preimage equals the canonical lift.
[RW-rec, Prop. 7]; [RW26, Thm. 1, p. 3]. -/
theorem lift_unique (z : ℂ) (hz : IsAlgebraic ℚ z) (a : Galois.Qbar)
    (ha : Galois.embed a = z) : a = Galois.algebraicLift z hz := by
  apply Galois.embed.injective
  change Galois.embed a = Galois.embed (Galois.algebraicLift z hz)
  rw [ha, Galois.embed_algebraicLift]

/-- The lifted values are nonzero, including at the origin.
[RW26, p. 6; Lemma 2, p. 12]; [RW-rec, Def. 1]. -/
theorem valueLift_ne_zero (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : ActualLattice.Group M hM) : valueLift M hM g ≠ 0 := by
  intro h
  have hz := congrArg Galois.embed h
  rw [embed_valueLift, map_zero] at hz
  exact L3.M72.value_ne_zero (periodData M hM) (stableLattice M hM) g hz

#check @Galois.algebraicLift
#check @L3.M78.Transport.chosenFamily_specialValues_isAlgebraic
#print gaussianAt
#print value
#print matrixLift

end SICLean.L5.ActualValues
