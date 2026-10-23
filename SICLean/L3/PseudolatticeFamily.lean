import SICLean.L3.PseudolatticeFiniteness
import SICLean.L3.PseudolatticePresentation
import SICLean.L3.PseudolatticeFamilyAux
import SICLean.L4.DistributionContract

set_option autoImplicit false

/-!
# A finite family of stable pseudolattices

`FinitePseudolatticeFamily` is constructed from `PeriodData`. The target and
scaling factor come from the arithmetic overlattice and the finite cover.
Q4 below is the distribution identity on every label.

Neither Q3, a complete `IsSolution`, nor algebraicity of `E` is asserted here.
-/

noncomputable section

open Set

namespace SICLean.L3

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Finite representatives covering all arithmetic lattices up to
totally positive elements of K. No literal closure under extension. -/
structure FinitePseudolatticeFamily (P : PeriodData K) where
  size : ℕ
  representative : Fin size → StablePseudolattice P
  covers : ∀ I : StablePseudolattice P, ∃ (i : Fin size) (lam : K),
    TotallyPositive P lam ∧ I.val = pseudolatticeScale lam (representative i).val

variable {P : PeriodData K}

/-- The cover is a conclusion, not a premise. -/
theorem finitePseudolatticeFamily_exists (P : PeriodData K) :
    Nonempty (FinitePseudolatticeFamily P) := by
  obtain ⟨n, _, reps, hcovers⟩ := finiteRepresentatives P
  exact ⟨⟨n, reps, hcovers⟩⟩

/-- Nonemptiness follows from the stable lattice Z[epsilon]. -/
theorem finitePseudolatticeFamily_size_pos (F : FinitePseudolatticeFamily P) :
    0 < F.size := by
  obtain ⟨i, _⟩ := F.covers (Classical.choice (stablePseudolattice_nonempty P))
  exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt

def chosenPseudolatticeFamily (P : PeriodData K) : FinitePseudolatticeFamily P :=
  Classical.choice (finitePseudolatticeFamily_exists P)

def pseudolatticeFamilyBasis (F : FinitePseudolatticeFamily P) (i : Fin F.size) :
    L4.DistributionBasis :=
  Classical.choose (exists_pseudolatticePresentation P (F.representative i))

/-- This pins every B_i to an actual K-lattice. -/
theorem pseudolatticeFamilyBasis_spec (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) :
    PseudolatticePresentation P (F.representative i) (pseudolatticeFamilyBasis F i) := by
  exact Classical.choose_spec (exists_pseudolatticePresentation P (F.representative i))

abbrev PseudolatticeFamilyGroup (F : FinitePseudolatticeFamily P) (i : Fin F.size) :=
  L4.DistributionGroup (pseudolatticeFamilyBasis F i)

/-- The new target's group is again N-element, not G_i/<h>. -/
theorem pseudolatticeFamilyGroup_finite_card (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) :
    Finite (PseudolatticeFamilyGroup F i) ∧
      Nat.card (PseudolatticeFamilyGroup F i) = P.N := by
  let e := pseudolatticeGroupEquiv P (F.representative i)
    (pseudolatticeFamilyBasis F i) (pseudolatticeFamilyBasis_spec F i)
  obtain ⟨hfinite, hcard⟩ := pseudolatticeGroup_finite_card P (F.representative i)
  let _ := hfinite
  exact ⟨Finite.of_equiv _ e.toEquiv, (Nat.card_congr e.toEquiv).symm.trans hcard⟩

noncomputable instance pseudolatticeFamilyGroupFintype
    (F : FinitePseudolatticeFamily P) (i : Fin F.size) :
    Fintype (PseudolatticeFamilyGroup F i) :=
  @Fintype.ofFinite _ (pseudolatticeFamilyGroup_finite_card F i).1

def pseudolatticeFamilyLabel (F : FinitePseudolatticeFamily P) (i : Fin F.size) :
    PseudolatticeFamilyGroup F i ≃+ L4.DistributionGroup (pseudolatticeFamilyBasis F i) :=
  AddEquiv.refl _

/-- The overlattice is J = λ I_j with λ ≫ 0.
Every nonzero 2-torsion label is included. Existence is not assumed. -/
theorem pseudolatticeFamily_target_exists (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    ∃ (j : Fin F.size) (lam : K), TotallyPositive P lam ∧
      L4.distributionLattice
          (L4.distributionScale (pseudolatticeFamilyBasis F j) (pseudolatticeScales P lam)) =
        L4.distributionOverlattice (pseudolatticeFamilyBasis F i) h.val := by
  let I := F.representative i
  let B := pseudolatticeFamilyBasis F i
  have hB : PseudolatticePresentation P I B := pseudolatticeFamilyBasis_spec F i
  let e := pseudolatticeGroupEquiv P I B hB
  let g := e.symm h.val
  have hg : g ≠ 0 ∧ g + g = 0 := by
    constructor
    · intro hz
      apply h.property.1
      calc
        h.val = e g := (e.apply_symm_apply h.val).symm
        _ = 0 := by rw [hz, map_zero]
    · apply e.injective
      simpa only [map_add, map_zero, g, AddEquiv.apply_symm_apply] using h.property.2
  let J := stablePseudolatticeOverlattice P I g hg
  obtain ⟨j, lam, hlam, hJ⟩ := F.covers J
  refine ⟨j, lam, hlam, ?_⟩
  calc
    L4.distributionLattice
        (L4.distributionScale (pseudolatticeFamilyBasis F j) (pseudolatticeScales P lam)) =
        (L4.distributionLattice (pseudolatticeFamilyBasis F j)).map
          (L4.distributionHomothety (pseudolatticeScales P lam)) :=
      (L4.distributionScale_valid _ (pseudolatticeFamilyBasis_spec F j).1
        (pseudolatticeScales P lam) hlam).2.2
    _ = pseudolatticeEmbeddingImage P (pseudolatticeScale lam (F.representative j).val) := by
      rw [(pseudolatticeFamilyBasis_spec F j).2.2, pseudolatticeEmbeddingImage_scale]
    _ = pseudolatticeEmbeddingImage P J.val := by rw [hJ]
    _ = L4.distributionOverlattice B h.val := by
      change pseudolatticeEmbeddingImage P (pseudolatticeOverlattice P I g) = _
      simpa only [g, e, AddEquiv.apply_symm_apply] using
        pseudolatticePresentation_overlattice P I B hB g

def pseudolatticeFamilyTarget (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) : Fin F.size :=
  Classical.choose (pseudolatticeFamily_target_exists F i h)

def pseudolatticeFamilyFactor (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) : K :=
  Classical.choose (Classical.choose_spec (pseudolatticeFamily_target_exists F i h))

def pseudolatticeFamilyScale (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) : ℝ × ℝ :=
  pseudolatticeScales P (pseudolatticeFamilyFactor F i h)

/-- The normalization is a totally positive element of K, not two unrelated real scalars. -/
theorem pseudolatticeFamilyFactor_positive (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    TotallyPositive P (pseudolatticeFamilyFactor F i h) := by
  exact (Classical.choose_spec
    (Classical.choose_spec (pseudolatticeFamily_target_exists F i h))).1

/-- This is `DistributionContract.hρ`. -/
theorem pseudolatticeFamilyScale_positive (F : FinitePseudolatticeFamily P) :
    ∀ i h, 0 < (pseudolatticeFamilyScale F i h).1 ∧
      0 < (pseudolatticeFamilyScale F i h).2 := by
  intro i h
  exact pseudolatticeFamilyFactor_positive F i h

/-- All representatives have the same ε, not only the same trace.
This is `DistributionContract.hε`. -/
theorem pseudolatticeFamilyTarget_period (F : FinitePseudolatticeFamily P) :
    ∀ i h, L4.distributionPeriod (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h)) =
      L4.distributionPeriod (pseudolatticeFamilyBasis F i) := by
  intro i h
  exact (pseudolatticeFamilyBasis_spec F (pseudolatticeFamilyTarget F i h)).2.1.trans
    (pseudolatticeFamilyBasis_spec F i).2.1.symm

/-- This is `DistributionContract.hJ`, in its required orientation. -/
theorem pseudolatticeFamilyTarget_lattice (F : FinitePseudolatticeFamily P) :
    ∀ i h, L4.distributionLattice
        (L4.distributionScale (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h))
          (pseudolatticeFamilyScale F i h)) =
      L4.distributionOverlattice (pseudolatticeFamilyBasis F i) h.val := by
  intro i h
  exact (Classical.choose_spec
    (Classical.choose_spec (pseudolatticeFamily_target_exists F i h))).2

/-- This is `DistributionContract.hP`, from hJ and the common period.
The normalization map is λ⁻¹. -/
theorem pseudolatticeFamilyTarget_periodPoints (F : FinitePseudolatticeFamily P) :
    ∀ i h, L4.distributionPeriodPoints (pseudolatticeFamilyBasis F i) ≤
      (L4.distributionPeriodPoints
        (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h))).comap
        (L4.distributionHomothety
          ((pseudolatticeFamilyScale F i h).1⁻¹, (pseudolatticeFamilyScale F i h).2⁻¹)) := by
  intro i h
  apply L4.distributionScaled_periodPoints_mono _ _ (pseudolatticeFamilyBasis_spec F i).1
    (pseudolatticeFamilyBasis_spec F (pseudolatticeFamilyTarget F i h)).1
    _ (pseudolatticeFamilyScale_positive F i h) (pseudolatticeFamilyTarget_period F i h)
  rw [pseudolatticeFamilyTarget_lattice F i h]
  exact le_sup_left

/-- The set map required by `FiniteSystem.project`, transported by identity
labels on the distribution groups. -/
def pseudolatticeFamilyProject (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i)
    (x : PseudolatticeFamilyGroup F i) :
    PseudolatticeFamilyGroup F (pseudolatticeFamilyTarget F i h) :=
  L4.distributionFamilyProject (pseudolatticeFamilyBasis F) (pseudolatticeFamilyLabel F)
    (pseudolatticeFamilyTarget F) (pseudolatticeFamilyScale F)
    (pseudolatticeFamilyTarget_periodPoints F) i h x

def pseudolatticeFamilyPoint (F : FinitePseudolatticeFamily P) :
    Coordinate (Fin F.size) (PseudolatticeFamilyGroup F) → ℂ :=
  L4.distributionFamilyPoint (pseudolatticeFamilyBasis F) (pseudolatticeFamilyLabel F)

/--
The representative formula determines the inverse
homothety direction without requiring a surjective projection.
-/
theorem pseudolatticeFamilyProject_mk (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i)
    (x : ℝ × ℝ) (hx : x ∈ L4.distributionPeriodPoints (pseudolatticeFamilyBasis F i)) :
    pseudolatticeFamilyProject F i h
        (L4.distributionMk (pseudolatticeFamilyBasis F i) x hx) =
      L4.distributionMk (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h))
        (L4.distributionHomothety
          ((pseudolatticeFamilyScale F i h).1⁻¹, (pseudolatticeFamilyScale F i h).2⁻¹) x)
        (pseudolatticeFamilyTarget_periodPoints F i h hx) := by
  change L4.distributionScaledProject _ _ _ (pseudolatticeFamilyTarget_periodPoints F i h)
    (L4.distributionMk _ x hx) = _
  apply L4.distributionScaledProject_mk _ _ (pseudolatticeFamilyBasis_spec F i).1
    (pseudolatticeFamilyBasis_spec F (pseudolatticeFamilyTarget F i h)).1
    _ (pseudolatticeFamilyScale_positive F i h)
  rw [pseudolatticeFamilyTarget_lattice F i h]
  exact le_sup_left

/-- The kernel is {0, h}. Both source and target have N elements;
the target is not defined as the source modulo this kernel. -/
theorem pseudolatticeFamilyProject_kernel (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i)
    (x : PseudolatticeFamilyGroup F i) :
    pseudolatticeFamilyProject F i h x = 0 ↔ x = 0 ∨ x = h.val := by
  exact PseudolatticeFamilyAux.distributionScaledProject_kernel _ _
    (pseudolatticeFamilyBasis_spec F i).1
    (pseudolatticeFamilyBasis_spec F (pseudolatticeFamilyTarget F i h)).1
    _ (pseudolatticeFamilyScale_positive F i h) h.val h.property
    (pseudolatticeFamilyTarget_periodPoints F i h)
    (pseudolatticeFamilyTarget_lattice F i h) x

/-- The family form of Q4, with its geometric premises. This is not Q3. -/
theorem pseudolatticeFamily_q4 (F : FinitePseudolatticeFamily P) :
    ∀ i (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i)
      (x : PseudolatticeFamilyGroup F i),
      pseudolatticeFamilyPoint F ⟨i, x⟩ * pseudolatticeFamilyPoint F ⟨i, x + h.val⟩ =
        L4.distributionFamilyKappa (pseudolatticeFamilyBasis F) (pseudolatticeFamilyTarget F) i h *
          pseudolatticeFamilyPoint F
            ⟨pseudolatticeFamilyTarget F i h, pseudolatticeFamilyProject F i h x⟩ := by
  exact L4.distributionFamily_q4 (pseudolatticeFamilyBasis F)
    (fun i => (pseudolatticeFamilyBasis_spec F i).1) (pseudolatticeFamilyLabel F)
    (pseudolatticeFamilyTarget F) (pseudolatticeFamilyScale F)
    (pseudolatticeFamilyScale_positive F) (pseudolatticeFamilyTarget_period F)
    (pseudolatticeFamilyTarget_lattice F) (pseudolatticeFamilyTarget_periodPoints F)

/--
The cover applies to any presentation of an arithmetic lattice.
No assertion quantifies over all real-scaled Valid presentations.
-/
theorem pseudolatticeFamily_covers_presentation (F : FinitePseudolatticeFamily P)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) :
    ∃ (i : Fin F.size) (lam : K), TotallyPositive P lam ∧
      L4.distributionLattice B = L4.distributionLattice
        (L4.distributionScale (pseudolatticeFamilyBasis F i) (pseudolatticeScales P lam)) := by
  obtain ⟨i, lam, hlam, hI⟩ := F.covers I
  refine ⟨i, lam, hlam, ?_⟩
  rw [(L4.distributionScale_valid _ (pseudolatticeFamilyBasis_spec F i).1
      (pseudolatticeScales P lam) hlam).2.2,
    (pseudolatticeFamilyBasis_spec F i).2.2, ← pseudolatticeEmbeddingImage_scale,
    hB.2.2, hI]

#check @L4.distributionFamily_q4
#check @L4.distributionFamily_isSolution_of_remaining_equations
#check @FiniteSystem
#print pseudolatticeFamilyProject
#print pseudolatticeFamily_q4

end SICLean.L3
