import SICLean.L4.G2RepresentativeWindow
import SICLean.L4.G2PoleSeparationAux

set_option autoImplicit false

/-!
Component-labelled pole families and separation. The terminal inclusions keep the original K≥1 /
J≥1. [RW26, pp. 12--13]. No cyclicity or S mod N zero test is assumed.
-/

noncomputable section
open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2

open SICLean.L4.G2PoleSeparationAux

def rightLabels (M : SL(2, ℤ)) (m : ℤ) : Set (ℕ × ℕ) :=
  {q | Int.ModEq (M 1 0) (M 1 1 * (q.1 : ℤ) + (q.2 : ℤ)) (M 1 1 * m)}

def leftLabels (M : SL(2, ℤ)) (v : ℤ × ℤ) (m : ℤ) : Set (ℕ × ℕ) :=
  {q | Int.ModEq (M 1 0) (M 1 1 * (q.1 : ℤ) + (q.2 : ℤ))
    (-M 1 1 * (m + v.1))}

def rightPoint (M : SL(2, ℤ)) (K J : ℕ) : ℝ :=
  epsilon M * (K : ℝ) + (J : ℝ)

def leftPoint (M : SL(2, ℤ)) (v : ℤ × ℤ) (K J : ℕ) : ℝ :=
  -inverseOffset M v - epsilon M * (K : ℝ) - (J : ℝ)

def rightComponent (M : SL(2, ℤ)) (m : ℤ) : Set ℝ :=
  {x | ∃ K J : ℕ, (K, J) ∈ rightLabels M m ∧ x = rightPoint M K J}

def leftComponent (M : SL(2, ℤ)) (v : ℤ × ℤ) (m : ℤ) : Set ℝ :=
  {x | ∃ K J : ℕ, (K, J) ∈ leftLabels M v m ∧ x = leftPoint M v K J}

def originalRightComponent (M : SL(2, ℤ)) (m : ℤ) : Set ℝ :=
  {x | ∃ K J : ℕ, 1 ≤ K ∧ (K, J) ∈ rightLabels M m ∧ x = rightPoint M K J}

def originalLeftComponent (M : SL(2, ℤ)) (v : ℤ × ℤ) (m : ℤ) : Set ℝ :=
  {x | ∃ K J : ℕ, 1 ≤ J ∧ (K, J) ∈ leftLabels M v m ∧ x = leftPoint M v K J}

def rightCoordinates (M : SL(2, ℤ)) : Set ℝ :=
  {x | ∃ K J : ℕ, x = rightPoint M K J}

def leftCoordinates (M : SL(2, ℤ)) (v : ℤ × ℤ) : Set ℝ :=
  {x | ∃ K J : ℕ, x = leftPoint M v K J}

def originalRightCoordinates (M : SL(2, ℤ)) : Set ℝ :=
  {x | ∃ K J : ℕ, 1 ≤ K ∧ x = rightPoint M K J}

def originalLeftCoordinates (M : SL(2, ℤ)) (v : ℤ × ℤ) : Set ℝ :=
  {x | ∃ K J : ℕ, 1 ≤ J ∧ x = leftPoint M v K J}

def translateSet (S : Set ℝ) (t : ℝ) : Set ℝ := (fun x => x + t) '' S

def commonRight (M : SL(2, ℤ)) : Set ℝ :=
  (⋃ j : Fin (M 1 0).toNat, translateSet (rightCoordinates M) ((j : ℝ) * length M)) ∪
    translateSet (originalRightCoordinates M) ((M 1 0 : ℝ) * length M)

def commonLeft (M : SL(2, ℤ)) (v : ℤ × ℤ) : Set ℝ :=
  (⋃ j : Fin (M 1 0).toNat, translateSet (leftCoordinates M v) ((j : ℝ) * length M)) ∪
    translateSet (originalLeftCoordinates M v) ((M 1 0 : ℝ) * length M)

theorem right_component_unique (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (K J : ℕ) :
    ∃! m : Fin (M 1 0).toNat, (K, J) ∈ rightLabels M (m : ℤ) := by
  exact G2PoleSeparationAux.existsUnique_linear_residue M hM.1
    (M 1 1 * (K : ℤ) + (J : ℤ))

theorem left_component_unique (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (K J : ℕ) :
    ∃! m : Fin (M 1 0).toNat, (K, J) ∈ leftLabels M v (m : ℤ) := by
  let z : ℤ := M 1 1 * (K : ℤ) + (J : ℤ)
  have hlabel : ∀ m : Fin (M 1 0).toNat,
      (K, J) ∈ leftLabels M v (m : ℤ) ↔
        Int.ModEq (M 1 0) (-z - M 1 1 * v.1) (M 1 1 * (m : ℤ)) := by
    intro m
    change Int.ModEq (M 1 0) z (-M 1 1 * ((m : ℤ) + v.1)) ↔ _
    constructor <;> intro h
    · convert h.neg.sub_right (M 1 1 * v.1) using 1
      ring
    · convert h.neg.sub_right (M 1 1 * v.1) using 1 <;> ring
  obtain ⟨m, hm, huniq⟩ :=
    G2PoleSeparationAux.existsUnique_linear_residue M hM.1 (-z - M 1 1 * v.1)
  exact ⟨m, (hlabel m).mpr hm, fun n hn => huniq n ((hlabel n).mp hn)⟩

/-- Exact affine coordinate, using the existing labelled divisor definitions. -/
theorem right_component_divisor (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m : ℤ) (x : ℝ) :
    x ∈ rightComponent M m ↔
      (x - epsilon M * (m : ℝ)) / (M 1 0 : ℝ) ∈
        g1NumeratorPoles M (repellingTau M) 0 m := by
  constructor
  · rintro ⟨K, J, hl, hx⟩
    exact ⟨K, J, (right_label_iff M m K J).1 hl,
      (right_point_affine_iff M hM m x K J).2 hx⟩
  · rintro ⟨K, J, hl, hx⟩
    exact ⟨K, J, (right_label_iff M m K J).2 hl,
      (right_point_affine_iff M hM m x K J).1 hx⟩

/-- The G1 ratio has denominator index n=0 after p,y translation. Its zero set is precisely that of
Φ_{m+v₁,1}(z+y). -/
theorem left_component_divisor (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : ℤ) (x : ℝ) :
    x ∈ leftComponent M v m ↔
      (x - epsilon M * (m : ℝ)) / (M 1 0 : ℝ) ∈
        g1InversePoles M (repellingTau M) (translatedY M v) 0 (v.1 - M 0 0) m := by
  constructor
  · rintro ⟨K, J, hl, hx⟩
    exact ⟨K, J, (left_label_iff M v m K J).1 hl,
      (left_point_affine_iff M hM v m x K J).2 hx⟩
  · rintro ⟨K, J, hl, hx⟩
    exact ⟨K, J, (left_label_iff M v m K J).2 hl,
      (left_point_affine_iff M hM v m x K J).1 hx⟩

theorem terminal_right_subset (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    translateSet (originalRightCoordinates M) ((M 1 0 : ℝ) * length M) ⊆
      translateSet (rightCoordinates M) (((M 1 0 : ℝ) - 1) * length M) := by
  rintro x ⟨y, ⟨K, J, hK, rfl⟩, rfl⟩
  refine ⟨rightPoint M (K - 1) (J + 1), ⟨K - 1, J + 1, rfl⟩, ?_⟩
  dsimp [rightPoint, length]
  rw [Nat.cast_sub hK]
  push_cast
  ring

theorem terminal_left_subset (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) :
    translateSet (originalLeftCoordinates M v) ((M 1 0 : ℝ) * length M) ⊆
      translateSet (leftCoordinates M v) (((M 1 0 : ℝ) - 1) * length M) := by
  rintro x ⟨y, ⟨K, J, hJ, rfl⟩, rfl⟩
  refine ⟨leftPoint M v (K + 1) (J - 1), ⟨K + 1, J - 1, rfl⟩, ?_⟩
  dsimp [leftPoint, length]
  rw [Nat.cast_sub hJ]
  push_cast
  ring

theorem collision_integer_identity (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (k : ℤ) (U V : ℕ)
    (hcollision : inverseOffset M v = (k : ℝ) * length M -
      epsilon M * (U : ℝ) - (V : ℝ)) :
    (U : ℝ) + (V : ℝ) + epsilon M *
      ((sIndex M v - k * specialValueOrder M -
        (specialValueOrder M + 1) * (U : ℤ) - (V : ℤ) : ℤ) : ℝ) = 0 := by
  exact G2PoleSeparationAux.collision_identity M hM v k U V hcollision

theorem common_sets_disjoint (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    Disjoint (commonRight M) (commonLeft M v) := by
  have hR : commonRight M =
      ⋃ j : Fin (M 1 0).toNat,
        translateSet (rightCoordinates M) ((j : ℝ) * length M) :=
    G2PoleSeparationAux.terminal_union_eq_int (M 1 0) hM.1
      (rightCoordinates M) (originalRightCoordinates M) (length M)
      (terminal_right_subset M hM)
  have hL : commonLeft M v =
      ⋃ j : Fin (M 1 0).toNat,
        translateSet (leftCoordinates M v) ((j : ℝ) * length M) :=
    G2PoleSeparationAux.terminal_union_eq_int (M 1 0) hM.1
      (leftCoordinates M v) (originalLeftCoordinates M v) (length M)
      (terminal_left_subset M hM v)
  apply Set.disjoint_left.2
  intro x hxR hxL
  rw [hR] at hxR
  rw [hL] at hxL
  obtain ⟨i, y, ⟨K, J, rfl⟩, hy⟩ := mem_iUnion.1 hxR
  obtain ⟨j, z, ⟨K', J', rfl⟩, hz⟩ := mem_iUnion.1 hxL
  have hi : (i : ℤ) < M 1 0 := by have := i.isLt; omega
  have hj : 0 ≤ (j : ℤ) := Int.natCast_nonneg _
  apply G2PoleSeparationAux.no_collision M hM u v hwin
    ((j : ℤ) - (i : ℤ)) (by omega) (K + K') (J + J')
  dsimp [rightPoint] at hy
  dsimp [leftPoint] at hz
  push_cast
  linarith

theorem commonRight_nonnegative (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    commonRight M ⊆ Ici 0 := by
  have hR : commonRight M =
      ⋃ j : Fin (M 1 0).toNat,
        translateSet (rightCoordinates M) ((j : ℝ) * length M) :=
    G2PoleSeparationAux.terminal_union_eq_int (M 1 0) hM.1
      (rightCoordinates M) (originalRightCoordinates M) (length M)
      (terminal_right_subset M hM)
  intro x hx
  rw [hR] at hx
  obtain ⟨j, y, ⟨K, J, rfl⟩, rfl⟩ := mem_iUnion.1 hx
  exact add_nonneg
    (add_nonneg (mul_nonneg (epsilon_pos M hM).le (Nat.cast_nonneg K))
      (Nat.cast_nonneg J))
    (mul_nonneg (Nat.cast_nonneg j.val) (length_pos M hM).le)

theorem commonLeft_boundedAbove (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) :
    BddAbove (commonLeft M v) := by
  have hL : commonLeft M v =
      ⋃ j : Fin (M 1 0).toNat,
        translateSet (leftCoordinates M v) ((j : ℝ) * length M) :=
    G2PoleSeparationAux.terminal_union_eq_int (M 1 0) hM.1
      (leftCoordinates M v) (originalLeftCoordinates M v) (length M)
      (terminal_left_subset M hM v)
  refine ⟨-inverseOffset M v + (M 1 0 : ℝ) * length M, ?_⟩
  intro x hx
  rw [hL] at hx
  obtain ⟨j, y, ⟨K, J, rfl⟩, rfl⟩ := mem_iUnion.1 hx
  have hj : (j : ℝ) ≤ (M 1 0 : ℝ) := by
    have hj' : (j : ℤ) ≤ M 1 0 := by have := j.isLt; omega
    exact_mod_cast hj'
  have hshift := mul_le_mul_of_nonneg_right hj (length_pos M hM).le
  dsimp [leftPoint]
  nlinarith [mul_nonneg (epsilon_pos M hM).le (Nat.cast_nonneg (α := ℝ) K),
    Nat.cast_nonneg (α := ℝ) J]

theorem common_coordinates_locally_finite (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (lo hi : ℝ) :
    ((commonRight M ∪ commonLeft M v) ∩ Icc lo hi).Finite := by
  have hR : commonRight M =
      ⋃ j : Fin (M 1 0).toNat,
        translateSet (rightCoordinates M) ((j : ℝ) * length M) :=
    G2PoleSeparationAux.terminal_union_eq_int (M 1 0) hM.1
      (rightCoordinates M) (originalRightCoordinates M) (length M)
      (terminal_right_subset M hM)
  have hL : commonLeft M v =
      ⋃ j : Fin (M 1 0).toNat,
        translateSet (leftCoordinates M v) ((j : ℝ) * length M) :=
    G2PoleSeparationAux.terminal_union_eq_int (M 1 0) hM.1
      (leftCoordinates M v) (originalLeftCoordinates M v) (length M)
      (terminal_left_subset M hM v)
  rw [hR, hL, union_inter_distrib_right, iUnion_inter, iUnion_inter]
  apply Set.Finite.union
  · apply Set.finite_iUnion
    intro j
    apply (G2PoleSeparationAux.right_grid_locally_finite
      (epsilon M) (epsilon_pos M hM) ((j : ℝ) * length M) lo hi).subset
    rintro x ⟨⟨y, ⟨K, J, rfl⟩, rfl⟩, hx⟩
    exact ⟨⟨K, J, rfl⟩, hx⟩
  · apply Set.finite_iUnion
    intro j
    apply (G2PoleSeparationAux.left_grid_locally_finite
      (epsilon M) (epsilon_pos M hM)
      (-inverseOffset M v + (j : ℝ) * length M) lo hi).subset
    rintro x ⟨⟨y, ⟨K, J, rfl⟩, rfl⟩, hx⟩
    refine ⟨⟨K, J, ?_⟩, hx⟩
    dsimp [leftPoint]
    ring

theorem translated_noPinch (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    g1NoPinch M (repellingTau M) (translatedY M v) (v.1 - M 0 0) := by
  intro K J _ h
  change translatedY M v =
    -((((v.1 - M 0 0 : ℤ) : ℝ) + (K : ℝ)) * epsilon M + 1 + (J : ℝ)) /
      (M 1 0 : ℝ) at h
  have hmul := (eq_div_iff (c_ne_zero M hM)).1 h
  have hy := translatedY_mul_c M hM v
  apply G2PoleSeparationAux.no_collision M hM u v hwin 0
    (by have := hM.1; omega) K J
  push_cast at hmul
  simp only [Int.cast_zero, zero_mul, zero_sub]
  nlinarith

#print rightLabels
#print leftLabels
#check left_component_divisor
#check translated_noPinch

end SICLean.L4.G2
