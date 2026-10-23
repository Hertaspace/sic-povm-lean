import SICLean.L4.G2PoleSeparation

set_option autoImplicit false

/-! Auxiliary finite-set and affine geometry for the common contour chain. All declarations belong
to this file's dedicated namespace. -/

noncomputable section
open Classical Set
open scoped BigOperators MatrixGroups

namespace SICLean.L4.G2ContourChainAux

open G2

theorem c_pos (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1

theorem c_nat_pos (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < (M 1 0).toNat := by
  have := hM.1
  omega

theorem length_eq_scale_mul (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    length M = scale M * (specialValueOrder M : ℝ) := by
  have hN : (specialValueOrder M : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast specialValueOrder_pos M hM)
  rw [(scale_identities M hM).2, div_mul_cancel₀ _ hN]

theorem finite_scaled_integers (s : ℝ) (hs : 0 < s) (lo hi : ℝ) :
    ({x : ℝ | ∃ k : ℤ, x = s * k} ∩ Icc lo hi).Finite := by
  apply ((Set.finite_Icc (⌈lo / s⌉ : ℤ) ⌊hi / s⌋).image
    (fun k : ℤ => s * (k : ℝ))).subset
  rintro x ⟨⟨k, rfl⟩, hx⟩
  refine ⟨k, ⟨?_, ?_⟩, rfl⟩
  · apply Int.ceil_le.mpr
    exact (div_le_iff₀ hs).mpr (by nlinarith [hx.1])
  · apply Int.le_floor.mpr
    exact (le_div_iff₀ hs).mpr (by nlinarith [hx.2])

theorem shifted_comb_scaled (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m k j : ℤ) :
    scale M * (((1 - M 1 1) * m + M 1 0 * k : ℤ) : ℝ) + (j : ℝ) * length M =
      scale M * (((1 - M 1 1) * m + M 1 0 * k + j * specialValueOrder M : ℤ) : ℝ) := by
  rw [length_eq_scale_mul M hM]
  push_cast
  ring

theorem neg_gap_not_scaled (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) (hδs : δ < s) :
    -δ ∉ {x : ℝ | ∃ k : ℤ, x = s * k} := by
  rintro ⟨k, hk⟩
  by_cases hnonneg : 0 ≤ k
  · have hkr : 0 ≤ (k : ℝ) := by exact_mod_cast hnonneg
    nlinarith
  · have hkle : k ≤ -1 := by omega
    have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hkle
    nlinarith

theorem finite_distance_gap (S : Set ℝ) (hS : S.Finite) (r : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ S, x ≠ r → η < |x - r| := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨η, hη, hgap⟩ := ih
    by_cases har : a = r
    · refine ⟨η, hη, ?_⟩
      intro x hx hxr
      rcases hx with rfl | hx
      · exact (hxr har).elim
      · exact hgap x hx hxr
    · refine ⟨min η (|a - r| / 2), lt_min hη (half_pos (abs_pos.mpr (sub_ne_zero.mpr har))), ?_⟩
      intro x hx hxr
      rcases hx with rfl | hx
      · exact lt_of_le_of_lt (min_le_right _ _) (by
          have := abs_pos.mpr (sub_ne_zero.mpr har)
          linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (hgap x hx hxr)

/-- Local finiteness gives a strict positive distance from all other coordinates. -/
theorem locally_finite_distance_gap (S : Set ℝ)
    (hS : ∀ lo hi : ℝ, (S ∩ Icc lo hi).Finite) (r : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ S, x ≠ r → η < |x - r| := by
  obtain ⟨η, hη, hgap⟩ := finite_distance_gap _ (hS (r - 1) (r + 1)) r
  refine ⟨min η (1 / 2), lt_min hη (by norm_num), ?_⟩
  intro x hx hxr
  by_cases hnear : x ∈ Icc (r - 1) (r + 1)
  · exact lt_of_le_of_lt (min_le_left _ _) (hgap x ⟨hx, hnear⟩ hxr)
  · have habs : 1 < |x - r| := by
      simp only [mem_Icc, not_and_or, not_le] at hnear
      rcases hnear with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

theorem right_translate_mem (M : SL(2, ℤ)) (j : Fin (M 1 0).toNat)
    {x : ℝ} (hx : x ∈ rightCoordinates M) :
    x + (j : ℝ) * length M ∈ commonRight M := by
  exact Or.inl (mem_iUnion.mpr ⟨j, ⟨x, hx, rfl⟩⟩)

theorem left_translate_mem (M : SL(2, ℤ)) (v : ℤ × ℤ)
    (j : Fin (M 1 0).toNat) {x : ℝ} (hx : x ∈ leftCoordinates M v) :
    x + (j : ℝ) * length M ∈ commonLeft M v := by
  exact Or.inl (mem_iUnion.mpr ⟨j, ⟨x, hx, rfl⟩⟩)

theorem right_mem (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    {x : ℝ} (hx : x ∈ rightCoordinates M) : x ∈ commonRight M := by
  simpa using right_translate_mem M ⟨0, c_nat_pos M hM⟩ hx

theorem left_mem (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) {x : ℝ} (hx : x ∈ leftCoordinates M v) :
    x ∈ commonLeft M v := by
  simpa using left_translate_mem M v ⟨0, c_nat_pos M hM⟩ hx

theorem zero_mem_right (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (0 : ℝ) ∈ commonRight M := by
  exact right_mem M hM ⟨0, 0, by simp [rightPoint]⟩

theorem winding_zero (D : G1VerticalChain) (x : ℝ)
    (hx : ∀ r ∈ D.centers, D.radius r < |x - r|) :
    g1CircleWinding D x = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  simp only [if_neg (not_lt.mpr (le_of_lt (hx r hr)))]

theorem winding_one (D : G1VerticalChain) (x : ℝ) (hx : x ∈ D.centers)
    (hpos : 0 < D.radius x)
    (hgap : ∀ r ∈ D.centers, x ≠ r → D.radius r < |x - r|) :
    g1CircleWinding D x = 1 := by
  unfold g1CircleWinding
  rw [Finset.sum_eq_single x]
  · simp [hpos]
  · intro r hr hrx
    exact if_neg (not_lt.mpr (le_of_lt (hgap r hr (Ne.symm hrx))))
  · exact fun h => (h hx).elim

/-- A positive affine pullback, with the two shifts kept separate to match the fixed component-chain
definition literally. -/
def affineChain (D : G1VerticalChain) (c a b : ℝ) : G1VerticalChain where
  crossing := (D.crossing - a - b) / c
  centers := D.centers.image (fun r => (r - a - b) / c)
  radius := fun r => D.radius (c * r + a + b) / c

theorem affine_cancel (c a b r : ℝ) (hc : c ≠ 0) :
    c * ((r - a - b) / c) + a + b = r := by
  field_simp
  ring

theorem affine_cancel' (c a b x : ℝ) (hc : c ≠ 0) :
    (c * x + a + b - a - b) / c = x := by
  field_simp
  ring

theorem affine_injective (c a b : ℝ) (hc : c ≠ 0) :
    Function.Injective (fun r : ℝ => (r - a - b) / c) := by
  intro x y h
  have := congrArg (fun r : ℝ => c * r + a + b) h
  simpa only [affine_cancel c a b _ hc] using this

theorem affine_radius (D : G1VerticalChain) (c a b r : ℝ) (hc : c ≠ 0) :
    (affineChain D c a b).radius ((r - a - b) / c) = D.radius r / c := by
  simp only [affineChain, affine_cancel c a b r hc]

theorem affine_distance (c a b x r : ℝ) (hc : 0 < c) :
    |x - (r - a - b) / c| = |c * x + a + b - r| / c := by
  have heq : x - (r - a - b) / c = (c * x + a + b - r) / c := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hc]

theorem affine_winding (D : G1VerticalChain) (c a b x : ℝ) (hc : 0 < c) :
    g1CircleWinding (affineChain D c a b) x = g1CircleWinding D (c * x + a + b) := by
  unfold g1CircleWinding
  change (∑ r ∈ D.centers.image (fun r => (r - a - b) / c),
    if |x - r| < (affineChain D c a b).radius r then (1 : ℤ) else 0) = _
  rw [Finset.sum_image (fun _ _ _ _ h => affine_injective c a b (ne_of_gt hc) h)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [affine_radius D c a b r (ne_of_gt hc), affine_distance c a b x r hc]
  simp only [div_lt_div_iff_of_pos_right hc]

theorem affine_assignment (D : G1VerticalChain) (c a b x : ℝ) (hc : 0 < c) :
    g1LeftAssignment (affineChain D c a b) x = g1LeftAssignment D (c * x + a + b) := by
  unfold g1LeftAssignment
  rw [affine_winding D c a b x hc]
  have hiff : x < (D.crossing - a - b) / c ↔ c * x + a + b < D.crossing := by
    rw [lt_div_iff₀ hc]
    constructor <;> intro h <;> nlinarith
  simp only [affineChain, hiff]

theorem affine_separates (D : G1VerticalChain) (P Z : Set ℝ) (c a b : ℝ)
    (hc : 0 < c)
    (hpos : ∀ r ∈ D.centers, 0 < D.radius r)
    (hboundary : ∀ x ∈ P ∪ Z, c * x + a + b ≠ D.crossing ∧
      ∀ r ∈ D.centers, |c * x + a + b - r| ≠ D.radius r)
    (hP : ∀ x ∈ P, g1LeftAssignment D (c * x + a + b) = 0)
    (hZ : ∀ x ∈ Z, g1LeftAssignment D (c * x + a + b) = 1) :
    G1Separates (affineChain D c a b) P Z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    rw [affine_radius D c a b s (ne_of_gt hc)]
    exact div_pos (hpos s hs) hc
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro heq
      apply (hboundary x hx).1
      rw [heq]
      exact affine_cancel c a b D.crossing (ne_of_gt hc)
    · intro r hr heq
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      rw [affine_radius D c a b s (ne_of_gt hc), affine_distance c a b x s hc] at heq
      exact (hboundary x hx).2 s hs ((div_left_inj' (ne_of_gt hc)).mp heq)
  · intro x hx
    rw [affine_assignment D c a b x hc]
    exact hP x hx
  · intro x hx
    rw [affine_assignment D c a b x hc]
    exact hZ x hx

end SICLean.L4.G2ContourChainAux
