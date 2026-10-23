import SICLean.L4.DistributionBasisValues
import SICLean.L2c.Coordinates
import SICLean.L2rc.Coordinates
import SICLean.L4.DistributionCoordinatesAux

set_option autoImplicit false

/-!
# Coordinate/positive-homothety bridge

This file is independent of the order-two proofs. It is needed because a finite family closes only
modulo positive homothety: J=ρ I_j, not literally J=I_j. Each embedding has its own positive scale.
A genuine totally positive K-element specializes these two scales. No finiteness of all real-scaled
presentations is asserted.

[RW26, p. 2, (2), p. 14, Prop. 9]. The row-quotient identifications are the explicit L2c/L2rc
coordinates, not additional analytic inputs.
-/

noncomputable section

open Set
open scoped MatrixGroups

namespace SICLean.L4

def distributionHomothety (ρ : ℝ × ℝ) : (ℝ × ℝ) →+ (ℝ × ℝ) :=
  (AddMonoidHom.mulLeft ρ.1).prodMap (AddMonoidHom.mulLeft ρ.2)

def distributionScale (B : DistributionBasis) (ρ : ℝ × ℝ) : DistributionBasis :=
  { matrix := B.matrix
    tau := B.tau
    scale := ρ.1 * B.scale
    scaleConj := ρ.2 * B.scaleConj }

/-- The actual finite-family projection x↦ρ⁻¹x modulo the chosen target. It is a specified set map;
descent is a separate theorem. -/
def distributionScaledProject (B C : DistributionBasis) (ρ : ℝ × ℝ)
    (hP : distributionPeriodPoints B ≤ (distributionPeriodPoints C).comap
      (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)))
    (g : DistributionGroup B) : DistributionGroup C :=
  distributionMk C
    (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) (distributionRepresentative B g))
    (hP (Quotient.out g).property)

/-- Generic row quotient, using the existing L2r integer-row convention. -/
abbrev DistributionRowGroup (B : DistributionBasis) :=
  (ℤ × ℤ) ⧸ L2r.rowLattice ((B.matrix : Matrix (Fin 2) (Fin 2) ℤ) - 1)

/-- Solve (D_ε⁻¹-1)x=u₁β₁+u₂β₂ in both embeddings. -/
def distributionRowPoint (B : DistributionBasis) (u : ℤ × ℤ) : ℝ × ℝ :=
  (((u.1 : ℝ) * (distributionBetaOne B).1 +
      (u.2 : ℝ) * (distributionBetaTwo B).1) / ((distributionPeriod B)⁻¹ - 1),
    ((u.1 : ℝ) * (distributionBetaOne B).2 +
      (u.2 : ℝ) * (distributionBetaTwo B).2) / (distributionPeriod B - 1))

@[simp] lemma distributionScale_matrix (B : DistributionBasis) (ρ : ℝ × ℝ) :
    (distributionScale B ρ).matrix = B.matrix := rfl

@[simp] lemma distributionScale_tau (B : DistributionBasis) (ρ : ℝ × ℝ) :
    (distributionScale B ρ).tau = B.tau := rfl

@[simp] lemma distributionScale_scale (B : DistributionBasis) (ρ : ℝ × ℝ) :
    (distributionScale B ρ).scale = ρ.1 * B.scale := rfl

@[simp] lemma distributionScale_scaleConj (B : DistributionBasis) (ρ : ℝ × ℝ) :
    (distributionScale B ρ).scaleConj = ρ.2 * B.scaleConj := rfl

lemma distributionScale_period (B : DistributionBasis) (ρ : ℝ × ℝ) :
    distributionPeriod (distributionScale B ρ) = distributionPeriod B := rfl

lemma distributionScale_betaOne (B : DistributionBasis) (ρ : ℝ × ℝ) :
    distributionBetaOne (distributionScale B ρ) =
      distributionHomothety ρ (distributionBetaOne B) := by
  ext
  · simp [distributionBetaOne, distributionScale, distributionHomothety]
    ring
  · show ρ.2 * B.scaleConj * distributionConjugateTau B =
      ρ.2 * (B.scaleConj * distributionConjugateTau B)
    ring

lemma distributionScale_conjugateTau (B : DistributionBasis) (ρ : ℝ × ℝ) :
    distributionConjugateTau (distributionScale B ρ) = distributionConjugateTau B := rfl

lemma distributionScale_betaTwo (B : DistributionBasis) (ρ : ℝ × ℝ) :
    distributionBetaTwo (distributionScale B ρ) =
      distributionHomothety ρ (distributionBetaTwo B) := by
  ext
  · simp [distributionBetaTwo, distributionScale, distributionHomothety]
  · simp [distributionBetaTwo, distributionScale, distributionHomothety]

lemma distributionHomothety_injective (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2) :
    Function.Injective (distributionHomothety ρ) := by
  intro x y h
  have h1 : ρ.1 * x.1 = ρ.1 * y.1 := by
    simpa [distributionHomothety] using congrArg Prod.fst h
  have h2 : ρ.2 * x.2 = ρ.2 * y.2 := by
    simpa [distributionHomothety] using congrArg Prod.snd h
  ext
  · exact mul_left_cancel₀ (ne_of_gt hρ.1) h1
  · exact mul_left_cancel₀ (ne_of_gt hρ.2) h2

lemma distributionHomothety_surjective (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2) :
    Function.Surjective (distributionHomothety ρ) := by
  intro y
  refine ⟨(y.1 / ρ.1, y.2 / ρ.2), ?_⟩
  have h1 : ρ.1 * (y.1 / ρ.1) = y.1 := by
    field_simp [ne_of_gt hρ.1]
  have h2 : ρ.2 * (y.2 / ρ.2) = y.2 := by
    field_simp [ne_of_gt hρ.2]
  ext
  · simpa [distributionHomothety] using h1
  · simpa [distributionHomothety] using h2

lemma distributionHomothety_bijective (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2) :
    Function.Bijective (distributionHomothety ρ) :=
  ⟨distributionHomothety_injective ρ hρ, distributionHomothety_surjective ρ hρ⟩

lemma distributionScale_periodDifference (B : DistributionBasis) (ρ : ℝ × ℝ) :
    distributionPeriodDifference (distributionScale B ρ) =
      distributionPeriodDifference B := rfl

lemma distributionHomothety_periodDifference_comm (B : DistributionBasis) (ρ : ℝ × ℝ) :
    ∀ x, distributionPeriodDifference B (distributionHomothety ρ x) =
      distributionHomothety ρ (distributionPeriodDifference B x) := by
  intro x
  ext <;> simp [distributionPeriodDifference, distributionHomothety] <;> ring

lemma distributionComap_map_of_commute {f g : (ℝ × ℝ) →+ (ℝ × ℝ)}
    (hcomm : ∀ x, f (g x) = g (f x)) (hg : Function.Bijective g)
    (P : AddSubgroup (ℝ × ℝ)) :
    (P.map g).comap f = (P.comap f).map g := by
  ext x
  constructor
  · intro hx
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_map] at hx
    obtain ⟨p, hp, hgp⟩ := hx
    obtain ⟨q, rfl⟩ := hg.2 x
    refine AddSubgroup.mem_map.mpr ⟨q, ?_, rfl⟩
    rw [AddSubgroup.mem_comap]
    have hgf : g (f q) = g p := by
      rw [← hcomm q, ← hgp]
    have hfq : f q = p := hg.1 hgf
    rw [hfq]
    exact hp
  · intro hx
    rw [AddSubgroup.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_map]
    exact ⟨f q, hq, (hcomm q).symm⟩

/-- Positive scaling preserves admissibility and determines the unit, while scaling the actual
lattice. [RW26, p. 2, (2)]. -/
theorem distributionScale_valid (B : DistributionBasis) (hB : B.Valid)
    (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2) :
    (distributionScale B ρ).Valid ∧
      distributionPeriod (distributionScale B ρ) = distributionPeriod B ∧
      distributionLattice (distributionScale B ρ) =
        (distributionLattice B).map (distributionHomothety ρ) := by
  refine ⟨?_, distributionScale_period B ρ, ?_⟩
  · simp only [DistributionBasis.Valid, distributionScale, distributionPeriod]
    exact ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1,
      mul_pos hρ.1 hB.2.2.2.2.1, mul_pos hρ.2 hB.2.2.2.2.2⟩
  · rw [distributionLattice, distributionLattice,
      distributionScale_betaOne, distributionScale_betaTwo, AddSubgroup.map_sup]
    simp

/-- The actual period-point groups scale as well. [RW26, p. 2, (2)]. -/
theorem distributionScale_periodPoints (B : DistributionBasis) (hB : B.Valid)
    (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2) :
    distributionPeriodPoints (distributionScale B ρ) =
      (distributionPeriodPoints B).map (distributionHomothety ρ) := by
  have hL := (distributionScale_valid B hB ρ hρ).2.2
  rw [distributionPeriodPoints, distributionPeriodPoints,
    distributionScale_periodDifference, hL]
  exact distributionComap_map_of_commute
    (distributionHomothety_periodDifference_comm B ρ)
    (distributionHomothety_bijective ρ hρ) (distributionLattice B)

/-- All floor-coordinate inputs are preserved, including points outside I. [RW26, p. 2, (2)]
background. -/
theorem distributionScale_coordinates (B : DistributionBasis) (ρ : ℝ × ℝ)
    (hρ : 0 < ρ.1 ∧ 0 < ρ.2) (x : ℝ × ℝ) :
    distributionCoordinates (distributionScale B ρ) (distributionHomothety ρ x) =
      distributionCoordinates B x := by
  have h1 : (ρ.1 * x.1) / (ρ.1 * B.scale) = x.1 / B.scale :=
    mul_div_mul_left x.1 B.scale (ne_of_gt hρ.1)
  have h2 : (ρ.2 * x.2) / (ρ.2 * B.scaleConj) = x.2 / B.scaleConj :=
    mul_div_mul_left x.2 B.scaleConj (ne_of_gt hρ.2)
  funext i
  fin_cases i
  · simp only [distributionCoordinates, distributionHomothety]
    rw [distributionScale_conjugateTau]
    simp [distributionScale, h1, h2]
  · simp only [distributionCoordinates, distributionHomothety]
    rw [distributionScale_conjugateTau]
    simp [distributionScale, h1, h2]

lemma distributionHomothety_mem_scale_lattice_iff (B : DistributionBasis) (hB : B.Valid)
    (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2) (x : ℝ × ℝ) :
    distributionHomothety ρ x ∈ distributionLattice (distributionScale B ρ) ↔
      x ∈ distributionLattice B := by
  rw [(distributionScale_valid B hB ρ hρ).2.2, AddSubgroup.mem_map]
  constructor
  · rintro ⟨p, hp, hpx⟩
    have hpx' : p = x := distributionHomothety_injective ρ hρ hpx
    rwa [hpx'] at hp
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The same Φ and μ give homothety invariance, including the zero branch. [RW26, p. 2, (2)]. -/
theorem distributionBasisValue_scale (B : DistributionBasis) (hB : B.Valid)
    (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionBasisValue (distributionScale B ρ) (distributionHomothety ρ x) =
      distributionBasisValue B x := by
  by_cases hxI : x ∈ distributionLattice B
  · have hHI : distributionHomothety ρ x ∈
        distributionLattice (distributionScale B ρ) :=
      (distributionHomothety_mem_scale_lattice_iff B hB ρ hρ x).2 hxI
    rw [distributionBasisValue_on_lattice _ _ hHI,
      distributionBasisValue_on_lattice _ _ hxI, distributionScale_period]
  · have hHI : distributionHomothety ρ x ∉
        distributionLattice (distributionScale B ρ) := fun h =>
      hxI ((distributionHomothety_mem_scale_lattice_iff B hB ρ hρ x).1 h)
    rw [distributionBasisValue_off_lattice _ _ hHI,
      distributionBasisValue_off_lattice _ _ hxI]
    have hcoord : distributionIntegerCoordinates (distributionScale B ρ)
        (distributionPeriodDifference (distributionScale B ρ) (distributionHomothety ρ x)) =
        distributionIntegerCoordinates B (distributionPeriodDifference B x) := by
      funext i
      have hD : distributionPeriodDifference (distributionScale B ρ)
          (distributionHomothety ρ x) =
          distributionHomothety ρ (distributionPeriodDifference B x) := by
        rw [distributionScale_periodDifference]
        exact distributionHomothety_periodDifference_comm B ρ x
      rw [hD]
      simp only [distributionIntegerCoordinates]
      rw [distributionScale_coordinates B ρ hρ]
    have harg : ((distributionHomothety ρ x).1 /
        (distributionScale B ρ).scale : ℝ) = x.1 / B.scale := by
      simp only [distributionHomothety, distributionScale]
      exact mul_div_mul_left x.1 B.scale (ne_of_gt hρ.1)
    simp only [distributionScale_matrix, distributionScale_tau]
    rw [show distributionIntegerCoordinates (distributionScale B ρ)
        (distributionPeriodDifference (distributionScale B ρ) (distributionHomothety ρ x)) 0 =
        distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 from
      congrFun hcoord 0, harg]

lemma distributionHomothety_inv_mem_lattice (B C : DistributionBasis) (hC : C.Valid)
    (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2)
    (hI : distributionLattice B ≤ distributionLattice (distributionScale C ρ))
    {v : ℝ × ℝ} (hv : v ∈ distributionLattice B) :
    distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) v ∈ distributionLattice C := by
  have hp : distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) v ∈
      (distributionLattice (distributionScale C ρ)).map
        (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)) :=
    AddSubgroup.mem_map.mpr ⟨v, hI hv, rfl⟩
  have hid : (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)).comp
      (distributionHomothety ρ) = AddMonoidHom.id (ℝ × ℝ) := by
    ext y
    · simp [distributionHomothety]
      field_simp [ne_of_gt hρ.1]
    · simp [distributionHomothety]
      field_simp [ne_of_gt hρ.2]
  rw [(distributionScale_valid C hC ρ hρ).2.2, AddSubgroup.map_map, hid] at hp
  simpa using hp

/-- Callable inclusion for the finite-family inverse-homothety projection. [RW26, p. 14, Prop. 9].
-/
theorem distributionScaled_periodPoints_mono (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2)
    (hε : distributionPeriod C = distributionPeriod B)
    (hI : distributionLattice B ≤ distributionLattice (distributionScale C ρ)) :
    distributionPeriodPoints B ≤ (distributionPeriodPoints C).comap
      (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)) := by
  intro x hx
  have hxI : distributionPeriodDifference B x ∈ distributionLattice B := by
    simpa [distributionPeriodPoints] using hx
  have hDcomm : distributionPeriodDifference B
      (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) x) =
      distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) (distributionPeriodDifference B x) :=
    distributionHomothety_periodDifference_comm B (ρ.1⁻¹, ρ.2⁻¹) x
  have hmem : distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)
      (distributionPeriodDifference B x) ∈ distributionLattice C := by
    have hp : distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)
        (distributionPeriodDifference B x) ∈
        (distributionLattice (distributionScale C ρ)).map
          (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)) :=
      AddSubgroup.mem_map.mpr ⟨_, hI hxI, rfl⟩
    have hid : (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)).comp
        (distributionHomothety ρ) = AddMonoidHom.id (ℝ × ℝ) := by
      ext y
      · simp [distributionHomothety]
        field_simp [ne_of_gt hρ.1]
      · simp [distributionHomothety]
        field_simp [ne_of_gt hρ.2]
    rw [(distributionScale_valid C hC ρ hρ).2.2, AddSubgroup.map_map, hid] at hp
    simpa using hp
  have hDC : distributionPeriodDifference C = distributionPeriodDifference B := by
    simp only [distributionPeriodDifference, hε]
  rw [distributionPeriodPoints]
  rw [hDC]
  change distributionPeriodDifference B
    (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) x) ∈ distributionLattice C
  rw [hDcomm]
  exact hmem

/-- Descent of x↦ρ⁻¹x for arbitrary representatives. [RW26, p. 14, Prop. 9]. -/
theorem distributionScaledProject_mk (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) (ρ : ℝ × ℝ) (hρ : 0 < ρ.1 ∧ 0 < ρ.2)
    (hP : distributionPeriodPoints B ≤ (distributionPeriodPoints C).comap
      (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)))
    (hI : distributionLattice B ≤ distributionLattice (distributionScale C ρ))
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionScaledProject B C ρ hP (distributionMk B x hx) =
      distributionMk C (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) x) (hP hx) := by
  have hy : distributionRepresentative B (distributionMk B x hx) - x ∈
      distributionLattice B := distributionRepresentative_mk B hB x hx
  have hy' : distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)
      (distributionRepresentative B (distributionMk B x hx) - x) ∈
      distributionLattice C :=
    distributionHomothety_inv_mem_lattice B C hC ρ hρ hI hy
  show distributionMk C (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹)
      (distributionRepresentative B (distributionMk B x hx))) _ =
    distributionMk C (distributionHomothety (ρ.1⁻¹, ρ.2⁻¹) x) (hP hx)
  refine (distributionMk_eq_iff C hC _ _ _ _).mpr ?_
  rw [← map_sub]
  exact hy'

lemma distributionRowPoint_periodDifference (B : DistributionBasis) (hB : B.Valid)
    (u : ℤ × ℤ) :
    distributionPeriodDifference B (distributionRowPoint B u) =
      (u.1 : ℝ) • distributionBetaOne B + (u.2 : ℝ) • distributionBetaTwo B := by
  ext
  · simp [distributionRowPoint, distributionPeriodDifference, distributionBetaOne,
      distributionBetaTwo]
    field_simp [distributionPeriod_inv_sub_one_ne_zero B hB]
  · simp [distributionRowPoint, distributionPeriodDifference, distributionBetaOne,
      distributionBetaTwo]
    field_simp [distributionPeriod_sub_one_ne_zero B hB]

/-- The row-point formula is an actual period point. [RW26, p. 2, (2)]. -/
theorem distributionRowPoint_mem (B : DistributionBasis) (hB : B.Valid) (u : ℤ × ℤ) :
    distributionRowPoint B u ∈ distributionPeriodPoints B := by
  rw [distributionPeriodPoints, AddSubgroup.mem_comap,
    distributionRowPoint_periodDifference B hB u, distributionLattice_mem_iff]
  refine ⟨![u.1, u.2], ?_⟩
  simpa [Int.cast_smul_eq_zsmul ℝ]

/-- Additivity of the explicit point formula. [RW26, p. 2, (2)]. -/
theorem distributionRowPoint_add (B : DistributionBasis) (u v : ℤ × ℤ) :
    distributionRowPoint B (u + v) = distributionRowPoint B u + distributionRowPoint B v := by
  ext <;>
    simp only [distributionRowPoint, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
      Prod.add_def] <;>
    push_cast <;>
    rw [add_div] <;>
    ring

/-- Row-lattice equality, with the correct ε⁻¹-1 versus γ-1 convention. [RW26, p. 2, (2)]. -/
theorem distributionRowPoint_lattice_iff (B : DistributionBasis) (hB : B.Valid)
    (u : ℤ × ℤ) :
    distributionRowPoint B u ∈ distributionLattice B ↔
      u ∈ L2r.rowLattice ((B.matrix : Matrix (Fin 2) (Fin 2) ℤ) - 1) := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ :=
      (distributionLattice_mem_iff_coordinates B hB (distributionRowPoint B u)).1 hx
    have hr : distributionRowPoint B u =
        (z.1 : ℝ) • distributionBetaOne B + (z.2 : ℝ) • distributionBetaTwo B := by
      rw [distributionCoordinates_reconstruct B hB (distributionRowPoint B u), hz]
      simp
    have hDz : distributionPeriodDifference B (distributionRowPoint B u) =
        (z.1 * ((B.matrix 1 1 : ℝ) - 1) - z.2 * (B.matrix 1 0 : ℝ)) •
            distributionBetaOne B +
          (z.1 * (-(B.matrix 0 1 : ℝ)) + z.2 * ((B.matrix 0 0 : ℝ) - 1)) •
            distributionBetaTwo B := by
      rw [hr]
      exact distributionPeriodDifference_combination B hB (z.1 : ℝ) (z.2 : ℝ)
    have hcu := distributionBetaCoefficients_unique B hB
      (z.1 * ((B.matrix 1 1 : ℝ) - 1) - z.2 * (B.matrix 1 0 : ℝ))
      (z.1 * (-(B.matrix 0 1 : ℝ)) + z.2 * ((B.matrix 0 0 : ℝ) - 1))
      (u.1 : ℝ) (u.2 : ℝ)
      (by rw [← hDz, distributionRowPoint_periodDifference B hB u])
    have hu1 : u.1 = z.1 * (B.matrix 1 1 - 1) - z.2 * (B.matrix 1 0) := by
      have h := hcu.1.symm
      push_cast at h
      exact_mod_cast h
    have hu2 : u.2 = -z.1 * (B.matrix 0 1) + z.2 * (B.matrix 0 0 - 1) := by
      have h := hcu.2.symm
      push_cast at h
      have h' : u.2 = z.1 * (-(B.matrix 0 1)) + z.2 * (B.matrix 0 0 - 1) := by
        exact_mod_cast h
      simpa using h'
    rw [L2r.rowLattice, AddMonoidHom.mem_range]
    refine ⟨(-(u.1 + z.1), -(u.2 + z.2)), ?_⟩
    show L2r.rowAction ((B.matrix : Matrix (Fin 2) (Fin 2) ℤ) - 1)
      (-(u.1 + z.1), -(u.2 + z.2)) = u
    simpa [L2r.rowAction, Matrix.sub_apply] using
      rowAction_int_forward (B.matrix 0 0) (B.matrix 0 1) (B.matrix 1 0) (B.matrix 1 1)
        z.1 z.2 u.1 u.2 (det_coe_int B.matrix) hu1 hu2
  · intro hu
    rw [L2r.rowLattice, AddMonoidHom.mem_range] at hu
    obtain ⟨z, hz⟩ := hu
    change L2r.rowAction ((B.matrix : Matrix (Fin 2) (Fin 2) ℤ) - 1) z = u at hz
    have hz1 : u.1 = z.1 * (B.matrix 0 0 - 1) + z.2 * (B.matrix 1 0) := by
      have h := congrArg Prod.fst hz
      simpa [L2r.rowAction, Matrix.sub_apply] using h.symm
    have hz2 : u.2 = z.1 * (B.matrix 0 1) + z.2 * (B.matrix 1 1 - 1) := by
      have h := congrArg Prod.snd hz
      simpa [L2r.rowAction, Matrix.sub_apply] using h.symm
    have hcu := rowAction_int_backward (B.matrix 0 0) (B.matrix 0 1) (B.matrix 1 0)
      (B.matrix 1 1) z.1 z.2 u.1 u.2 (det_coe_int B.matrix) hz1 hz2
    have hr : distributionRowPoint B u =
        (-(u.1 + z.1) : ℝ) • distributionBetaOne B +
          (-(u.2 + z.2) : ℝ) • distributionBetaTwo B := by
      apply distributionPeriodDifference_injective B hB
      rw [distributionRowPoint_periodDifference B hB u,
        distributionPeriodDifference_combination B hB (-(u.1 + z.1) : ℝ) (-(u.2 + z.2) : ℝ)]
      rw [show (-(u.1 + z.1) * ((B.matrix 1 1 : ℝ) - 1) -
            (-(u.2 + z.2)) * (B.matrix 1 0 : ℝ)) = (u.1 : ℝ) from by
          exact_mod_cast hcu.1,
        show (-(u.1 + z.1) * (-(B.matrix 0 1 : ℝ)) +
            (-(u.2 + z.2)) * ((B.matrix 0 0 : ℝ) - 1)) = (u.2 : ℝ) from by
          exact_mod_cast hcu.2]
    exact (distributionLattice_mem_iff_coordinates B hB (distributionRowPoint B u)).2
      ⟨(-(u.1 + z.1), -(u.2 + z.2)), by
        rw [hr, distributionCoordinates_real_combination B hB]
        simp⟩

/-- The coordinate equivalence is a theorem, not an input law. Its pointwise clause determines the
actual correspondence used downstream. [RW26, p. 2, (2)]. -/
theorem distributionRowGroup_equiv (B : DistributionBasis) (hB : B.Valid) :
    ∃ e : DistributionRowGroup B ≃+ DistributionGroup B, ∀ u : ℤ × ℤ,
      e (QuotientAddGroup.mk u) = distributionMk B (distributionRowPoint B u)
        (distributionRowPoint_mem B hB u) := by
  let L := L2r.rowLattice ((B.matrix : Matrix (Fin 2) (Fin 2) ℤ) - 1)
  let φ : (ℤ × ℤ) →+ DistributionGroup B :=
    { toFun := fun u => distributionMk B (distributionRowPoint B u)
        (distributionRowPoint_mem B hB u)
      map_zero' := by
        have h0 : (⟨distributionRowPoint B 0, distributionRowPoint_mem B hB 0⟩ :
            distributionPeriodPoints B) = 0 := by
          apply Subtype.ext
          simp [distributionRowPoint]
        show distributionMk B (distributionRowPoint B 0)
          (distributionRowPoint_mem B hB 0) = 0
        rw [distributionMk, h0]
        exact map_zero (QuotientAddGroup.mk'
          ((distributionLattice B).addSubgroupOf (distributionPeriodPoints B)))
      map_add' := by
        intro u v
        have h1 : (⟨distributionRowPoint B (u + v),
            distributionRowPoint_mem B hB (u + v)⟩ : distributionPeriodPoints B) =
            (⟨distributionRowPoint B u, distributionRowPoint_mem B hB u⟩ :
              distributionPeriodPoints B) +
            (⟨distributionRowPoint B v, distributionRowPoint_mem B hB v⟩ :
              distributionPeriodPoints B) := by
          apply Subtype.ext
          simp [distributionRowPoint_add]
        show distributionMk B (distributionRowPoint B (u + v))
            (distributionRowPoint_mem B hB (u + v)) =
          distributionMk B (distributionRowPoint B u) (distributionRowPoint_mem B hB u) +
            distributionMk B (distributionRowPoint B v) (distributionRowPoint_mem B hB v)
        rw [distributionMk, distributionMk, distributionMk, h1]
        exact map_add (QuotientAddGroup.mk'
          ((distributionLattice B).addSubgroupOf (distributionPeriodPoints B))) _ _ }
  have hker : L ≤ φ.ker := by
    intro u hu
    rw [AddMonoidHom.mem_ker]
    have hmem : (⟨distributionRowPoint B u, distributionRowPoint_mem B hB u⟩ :
        distributionPeriodPoints B) ∈
        (distributionLattice B).addSubgroupOf (distributionPeriodPoints B) := by
      rw [AddSubgroup.mem_addSubgroupOf]
      exact (distributionRowPoint_lattice_iff B hB u).2 hu
    have hzero : (0 : DistributionGroup B) =
        QuotientAddGroup.mk (0 : distributionPeriodPoints B) :=
      (map_zero (QuotientAddGroup.mk'
        ((distributionLattice B).addSubgroupOf (distributionPeriodPoints B)))).symm
    show distributionMk B (distributionRowPoint B u)
      (distributionRowPoint_mem B hB u) = 0
    rw [distributionMk, hzero, QuotientAddGroup.eq]
    simpa using hmem
  let ψ : DistributionRowGroup B →+ DistributionGroup B :=
    QuotientAddGroup.lift L φ hker
  have hψ : ∀ u : ℤ × ℤ, ψ (QuotientAddGroup.mk u) =
      distributionMk B (distributionRowPoint B u) (distributionRowPoint_mem B hB u) := by
    intro u
    rw [QuotientAddGroup.lift_mk]
    rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hψ u] at hx
    have hu : u ∈ L := by
      rw [← (distributionRowPoint_lattice_iff B hB u)]
      have hzero : (0 : DistributionGroup B) =
          QuotientAddGroup.mk (0 : distributionPeriodPoints B) :=
        (map_zero (QuotientAddGroup.mk'
          ((distributionLattice B).addSubgroupOf (distributionPeriodPoints B)))).symm
      have hmem : (⟨distributionRowPoint B u, distributionRowPoint_mem B hB u⟩ :
          distributionPeriodPoints B) ∈
          (distributionLattice B).addSubgroupOf (distributionPeriodPoints B) := by
        rw [distributionMk, hzero, QuotientAddGroup.eq] at hx
        simpa using hx
      rwa [AddSubgroup.mem_addSubgroupOf] at hmem
    rw [show (0 : DistributionRowGroup B) = QuotientAddGroup.mk (0 : ℤ × ℤ) from
      (map_zero (QuotientAddGroup.mk' L)).symm, QuotientAddGroup.eq]
    simpa using hu
  have hsurj : Function.Surjective ψ := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective g
    obtain ⟨w, hw⟩ := (distributionLattice_mem_iff B
      (distributionPeriodDifference B (x : ℝ × ℝ))).1
      (by simpa [distributionPeriodPoints] using x.property)
    refine ⟨QuotientAddGroup.mk (w 0, w 1), ?_⟩
    rw [hψ]
    show distributionMk B (distributionRowPoint B (w 0, w 1))
      (distributionRowPoint_mem B hB (w 0, w 1)) = QuotientAddGroup.mk x
    have hrv : distributionRowPoint B (w 0, w 1) = (x : ℝ × ℝ) := by
      apply distributionPeriodDifference_injective B hB
      rw [distributionRowPoint_periodDifference B hB (w 0, w 1), hw]
      simp [Int.cast_smul_eq_zsmul ℝ]
    have hx_eq : (⟨distributionRowPoint B (w 0, w 1),
        distributionRowPoint_mem B hB (w 0, w 1)⟩ : distributionPeriodPoints B) = x := by
      apply Subtype.ext
      exact hrv
    rw [distributionMk, hx_eq]
  exact ⟨AddEquiv.ofBijective ψ ⟨hinj, hsurj⟩, hψ⟩

/-- The Fin-2 parameter is explicit; ℤ×ℤ is not definitionally Fin 2→ℤ. [RW26, p. 2, (2)]. -/
theorem distributionRowPoint_specialArgument (B : DistributionBasis) (hB : B.Valid)
    (u : ℤ × ℤ) :
    (((distributionRowPoint B u).1 / B.scale : ℝ) : ℂ) =
      modularPhiSpecialArgument B.matrix ![u.1, u.2] (B.tau : ℂ) := by
  have hreal : (distributionRowPoint B u).1 / B.scale =
      ((u.1 : ℝ) * B.tau + (u.2 : ℝ)) / ((distributionPeriod B)⁻¹ - 1) := by
    simp only [distributionRowPoint, distributionBetaOne, distributionBetaTwo]
    rw [show (u.1 : ℝ) * (B.scale * B.tau) + (u.2 : ℝ) * B.scale =
        B.scale * ((u.1 : ℝ) * B.tau + (u.2 : ℝ)) from by ring]
    rw [div_div, mul_comm B.scale ((u.1 : ℝ) * B.tau + (u.2 : ℝ))]
    exact mul_div_mul_right _ _ (ne_of_gt hB.2.2.2.2.1)
  rw [hreal]
  simp only [modularPhiSpecialArgument, etaDenom, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  rw [show (B.matrix 1 0 : ℂ) * (B.tau : ℂ) + (B.matrix 1 1 : ℂ) =
      ((distributionPeriod B : ℝ) : ℂ) from by
    simp only [distributionPeriod]; push_cast; ring]
  rw [Complex.ofReal_div]
  push_cast
  ring

/-- Actual nonzero-class formula, with no Fourier or pentagon premise. [RW26, p. 2, (2)]. -/
theorem distributionRowPoint_value (B : DistributionBasis) (hB : B.Valid)
    (u : ℤ × ℤ)
    (hu : u ∉ L2r.rowLattice ((B.matrix : Matrix (Fin 2) (Fin 2) ℤ) - 1)) :
    distributionBasisValue B (distributionRowPoint B u) =
      etaMultiplier B.matrix * modularPhi B.matrix u.1 0
        (modularPhiSpecialArgument B.matrix ![u.1, u.2] (B.tau : ℂ)) (B.tau : ℂ) := by
  have hxI : distributionRowPoint B u ∉ distributionLattice B := fun h =>
    hu ((distributionRowPoint_lattice_iff B hB u).1 h)
  have hcoord : distributionIntegerCoordinates B
      (distributionPeriodDifference B (distributionRowPoint B u)) 0 = u.1 := by
    simp only [distributionIntegerCoordinates]
    rw [distributionRowPoint_periodDifference B hB u,
      distributionCoordinates_real_combination B hB]
    simp
  rw [distributionBasisValue_off_lattice B (distributionRowPoint B u) hxI,
    hcoord, distributionRowPoint_specialArgument B hB u]

/-- Existing original-family group, with its label fixed on every integer row.
It uses `L2c.lattice_eq_row_range`. Background: [RW26, p. 2, (2), p. 14, Prop. 8]. -/
theorem distributionL2c_equiv (M : ℕ) [Fact (4 ≤ M)]
    (B : DistributionBasis) (hB : B.Valid)
    (hM : (B.matrix : Matrix (Fin 2) (Fin 2) ℤ) = L2b.gamma M) :
    ∃ e : L2c.RWGroup M ≃+ DistributionGroup B, ∀ u : ℤ × ℤ,
      e (L2c.mk M u) = distributionMk B (distributionRowPoint B u)
        (distributionRowPoint_mem B hB u) := by
  obtain ⟨e₀, he₀⟩ := distributionRowGroup_equiv B hB
  have hmap : L2c.rowLatticeMap M = L2r.rowActionHom (L2b.gamma M - 1) := by
    ext u : 1
    change L2c.rowGamma M u - u = L2r.rowAction (L2b.gamma M - 1) u
    ext <;> simp [L2c.rowGamma, L2r.rowAction, Matrix.sub_apply] <;> ring
  have hlat : L2c.lattice M =
      L2r.rowLattice ((B.matrix : Matrix (Fin 2) (Fin 2) ℤ) - 1) := by
    rw [L2c.lattice_eq_row_range, hmap, L2r.rowLattice, hM]
    rfl
  let e₁ : L2c.RWGroup M ≃+ DistributionRowGroup B :=
    QuotientAddGroup.quotientAddEquivOfEq hlat
  refine ⟨e₁.trans e₀, ?_⟩
  intro u
  have hmk : e₁ (L2c.mk M u) = QuotientAddGroup.mk u := by
    rw [show L2c.mk M u = QuotientAddGroup.mk u from rfl,
      QuotientAddGroup.quotientAddEquivOfEq_mk]
  rw [AddEquiv.trans_apply, hmk, he₀]

/-- Existing high-rank row group, preserving its existing Gaussian labels, from
`SICLean.L2rc.Coordinates`.
Background: [RW26, p. 2, (2), p. 14, Prop. 8]. -/
theorem distributionL2rc_equiv (d r : ℕ) [Fact (L2r.Admissible d r)]
    (B : DistributionBasis) (hB : B.Valid)
    (hM : (B.matrix : Matrix (Fin 2) (Fin 2) ℤ) = L2r.gamma d r) :
    ∃ e : L2rc.RWGroup d r ≃+ DistributionGroup B, ∀ u : ℤ × ℤ,
      e (L2rc.mk d r u) = distributionMk B (distributionRowPoint B u)
        (distributionRowPoint_mem B hB u) := by
  obtain ⟨e₀, he₀⟩ := distributionRowGroup_equiv B hB
  have hlat : L2r.rowLattice (L2r.gamma d r - 1) =
      L2r.rowLattice ((B.matrix : Matrix (Fin 2) (Fin 2) ℤ) - 1) := by
    rw [hM]
  let e₁ : L2rc.RWGroup d r ≃+ DistributionRowGroup B :=
    QuotientAddGroup.quotientAddEquivOfEq hlat
  refine ⟨e₁.trans e₀, ?_⟩
  intro u
  have hmk : e₁ (L2rc.mk d r u) = QuotientAddGroup.mk u := by
    rw [show L2rc.mk d r u = QuotientAddGroup.mk u from rfl,
      QuotientAddGroup.quotientAddEquivOfEq_mk]
  rw [AddEquiv.trans_apply, hmk, he₀]

#print distributionScaledProject
#print distributionRowPoint
#check L2c.lattice_eq_row_range
#check L2rc.lattice_eq_row_range
#check distributionL2c_equiv
#check distributionL2rc_equiv

end SICLean.L4
