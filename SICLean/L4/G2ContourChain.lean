import SICLean.L4.G2ContourChainAux

set_option autoImplicit false

/-!
One concrete finite-circle chain and every translate. [RW26, pp. 12--13]. No integral evaluation or
residue theorem is assumed. Coincident comb coordinates are
intentionally enclosed.
-/

noncomputable section
open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2

open G2ContourChainAux

def combCoordinate (M : SL(2, ℤ)) (m k : ℤ) : ℝ :=
  scale M * (((1 - M 1 1) * m + M 1 0 * k : ℤ) : ℝ)

/-- Relevant pole coordinates, including all translated combs, retaining the component index m in
its definition. This set is used only for choosing small radii; the later residue ledger keeps (m,k)
rather than this union. -/
def guardSet (M : SL(2, ℤ)) (v : ℤ × ℤ) : Set ℝ :=
  commonRight M ∪ commonLeft M v ∪
    {x | ∃ (m : Fin (M 1 0).toNat) (k : ℤ) (j : Fin ((M 1 0).toNat + 1)),
      x = combCoordinate M (m : ℤ) k + (j : ℝ) * length M}

/-- A construction specification consisting only of explicit geometry. The centers are exactly the
distinct positive common-left coordinates. No list of poles or comb roots is removed when
coordinates coincide. -/
def CommonChain (M : SL(2, ℤ)) (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) : Prop :=
  0 < δ ∧ δ < scale M ∧ δ < length M ∧ D.crossing = -δ ∧
    (∀ x ∈ commonLeft M v, x ∉ Icc (-δ) 0) ∧
    (D.centers : Set ℝ) = commonLeft M v ∩ Ioi 0 ∧
    (∀ r ∈ D.centers, 0 < D.radius r ∧ D.crossing < r - D.radius r ∧
      ∀ x ∈ guardSet M v, x ≠ r → D.radius r < |x - r|)

/-- Exact affine pullback of the common chain: (D-εm-jL)/c. For j=0 this is D_m, for general j it is
D_m-jΔ, Δ=L/c. -/
def componentChain (M : SL(2, ℤ)) (D : G1VerticalChain) (m j : ℤ) : G1VerticalChain where
  crossing := (D.crossing - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ)
  centers := D.centers.image
    (fun r => (r - epsilon M * (m : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ))
  radius := fun r => D.radius
    ((M 1 0 : ℝ) * r + epsilon M * (m : ℝ) + (j : ℝ) * length M) / (M 1 0 : ℝ)

theorem guardSet_locally_finite (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (lo hi : ℝ) :
    (guardSet M v ∩ Icc lo hi).Finite := by
  have hL := length_eq_scale_mul M hM
  have hpoles := common_coordinates_locally_finite M hM v lo hi
  have hlattice := finite_scaled_integers (scale M) (scale_identities M hM).1 lo hi
  apply (hpoles.union hlattice).subset
  rintro x ⟨hx, hbounds⟩
  rcases hx with hx | hx
  · exact Or.inl ⟨hx, hbounds⟩
  · right
    refine ⟨?_, hbounds⟩
    obtain ⟨m, k, j, rfl⟩ := hx
    refine ⟨(1 - M 1 1) * (m : ℤ) + M 1 0 * k + (j : ℤ) * specialValueOrder M, ?_⟩
    simp only [combCoordinate, hL]
    push_cast
    ring

theorem positive_left_finite (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) :
    (commonLeft M v ∩ Ioi 0).Finite := by
  obtain ⟨b, hb⟩ := commonLeft_boundedAbove M hM v
  apply (common_coordinates_locally_finite M hM v 0 b).subset
  intro x hx
  exact ⟨Or.inr hx.1, le_of_lt hx.2, hb hx.1⟩

theorem exists_commonChain (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    ∃ (δ : ℝ) (D : G1VerticalChain), CommonChain M v δ D := by
  have hloc := guardSet_locally_finite M hM v
  obtain ⟨η, hη, hgap⟩ := locally_finite_distance_gap _ hloc 0
  have hz : (0 : ℝ) ∉ commonLeft M v := by
    intro hz
    exact Set.disjoint_left.mp (common_sets_disjoint M hM u v hwin)
      (zero_mem_right M hM) hz
  have hs := (scale_identities M hM).1
  have hL := length_pos M hM
  let δ := min (scale M) (min (length M) η) / 2
  have hδ : 0 < δ := half_pos (lt_min hs (lt_min hL hη))
  have hδs : δ < scale M := by
    have := min_le_left (scale M) (min (length M) η)
    dsimp [δ]
    linarith
  have hδL : δ < length M := by
    have := (min_le_right (scale M) (min (length M) η)).trans
      (min_le_left (length M) η)
    dsimp [δ]
    linarith
  have hδη : δ < η := by
    have := (min_le_right (scale M) (min (length M) η)).trans
      (min_le_right (length M) η)
    dsimp [δ]
    linarith
  let ρ := fun r : ℝ => (locally_finite_distance_gap _ hloc r).choose
  have hρ (r : ℝ) : 0 < ρ r ∧
      ∀ x ∈ guardSet M v, x ≠ r → ρ r < |x - r| :=
    (locally_finite_distance_gap _ hloc r).choose_spec
  let centers := (positive_left_finite M hM v).toFinset
  let D : G1VerticalChain :=
    ⟨-δ, centers, fun r => min (ρ r) ((r + δ) / 2)⟩
  refine ⟨δ, D, hδ, hδs, hδL, rfl, ?_, ?_, ?_⟩
  · intro x hx hnear
    have hdist := hgap x (Or.inl (Or.inr hx)) (by
      intro h
      exact hz (h ▸ hx))
    rw [sub_zero, abs_of_nonpos hnear.2] at hdist
    linarith [hnear.1]
  · exact Set.Finite.coe_toFinset _
  · intro r hr
    have hr' : r ∈ commonLeft M v ∩ Ioi 0 := by simpa [D, centers] using hr
    have hpositive : 0 < r + δ := add_pos hr'.2 hδ
    refine ⟨lt_min (hρ r).1 (half_pos hpositive), ?_, ?_⟩
    · change -δ < r - min (ρ r) ((r + δ) / 2)
      have := min_le_right (ρ r) ((r + δ) / 2)
      linarith
    · intro x hx hxr
      exact lt_of_le_of_lt (min_le_left _ _) ((hρ r).2 x hx hxr)

theorem commonChain_boundary_avoids (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    D.crossing ∉ guardSet M v ∧
      ∀ r ∈ D.centers, ∀ x ∈ guardSet M v, |x - r| ≠ D.radius r := by
  rcases hD with ⟨hδ, hδs, hδL, hcross, hleft, hcent, hradii⟩
  constructor
  · rw [hcross]
    intro hx
    rcases hx with (hx | hx) | hx
    · have := commonRight_nonnegative M hM hx
      change 0 ≤ -δ at this
      linarith
    · exact hleft (-δ) hx ⟨le_rfl, by linarith⟩
    · apply neg_gap_not_scaled (scale M) δ (scale_identities M hM).1 hδ hδs
      obtain ⟨m, k, j, hx⟩ := hx
      refine ⟨(1 - M 1 1) * (m : ℤ) + M 1 0 * k + (j : ℤ) * specialValueOrder M, ?_⟩
      exact hx.trans (shifted_comb_scaled M hM (m : ℤ) k (j : ℤ))
  · intro r hr x hx
    by_cases hxr : x = r
    · subst x
      simpa using (ne_of_lt (hradii r hr).1)
    · exact ne_of_gt ((hradii r hr).2.2 x hx hxr)

theorem commonChain_right_assignment (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    ∀ x ∈ commonRight M, g1LeftAssignment D x = 0 := by
  rcases hD with ⟨hδ, hδs, hδL, hcross, hleft, hcent, hradii⟩
  intro x hx
  have hxnonneg := commonRight_nonnegative M hM hx
  have hxbase : ¬x < D.crossing := by
    rw [hcross]
    change 0 ≤ x at hxnonneg
    linarith
  have hw : g1CircleWinding D x = 0 := by
    apply winding_zero
    intro r hr
    have hrleft : r ∈ commonLeft M v := (hcent ▸ hr : r ∈ commonLeft M v ∩ Ioi 0).1
    apply (hradii r hr).2.2 x (Or.inl (Or.inl hx))
    intro hxr
    exact Set.disjoint_left.mp (common_sets_disjoint M hM u v hwin) hx (hxr ▸ hrleft)
  simp only [g1LeftAssignment, if_neg hxbase, hw, add_zero]

theorem commonChain_left_assignment (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    ∀ x ∈ commonLeft M v, g1LeftAssignment D x = 1 := by
  rcases hD with ⟨hδ, hδs, hδL, hcross, hleft, hcent, hradii⟩
  intro x hx
  by_cases hxbase : x < D.crossing
  · have hw : g1CircleWinding D x = 0 := by
      apply winding_zero
      intro r hr
      have hrpos : 0 < r := (hcent ▸ hr : r ∈ commonLeft M v ∩ Ioi 0).2
      apply (hradii r hr).2.2 x (Or.inl (Or.inr hx))
      rw [hcross] at hxbase
      linarith
    simp only [g1LeftAssignment, if_pos hxbase, hw, add_zero]
  · have hxpos : 0 < x := by
      by_contra h
      apply hleft x hx
      exact ⟨by simpa only [hcross] using le_of_not_gt hxbase, le_of_not_gt h⟩
    have hxcenter : x ∈ D.centers := by rw [← Finset.mem_coe, hcent]; exact ⟨hx, hxpos⟩
    have hw : g1CircleWinding D x = 1 :=
      winding_one D x hxcenter (hradii x hxcenter).1
        (fun r hr hxr => (hradii r hr).2.2 x (Or.inl (Or.inr hx)) hxr)
    simp only [g1LeftAssignment, if_neg hxbase, hw, zero_add]

/-- Parametrization equality; the real parameter rescales by positive c. -/
theorem componentChain_verticalPoint (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j : ℤ) (t : ℝ) :
    g1VerticalPoint (componentChain M D m j).crossing t =
      (g1VerticalPoint D.crossing ((M 1 0 : ℝ) * t) -
        (epsilon M : ℂ) * (m : ℂ) - (j : ℂ) * (length M : ℂ)) / (M 1 0 : ℂ) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (c_pos M hM))
  simp only [g1VerticalPoint, componentChain]
  push_cast
  field_simp
  <;> ring

theorem componentChain_circlePoint (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j : ℤ) (r θ : ℝ) :
    circleMap (((r - epsilon M * (m : ℝ) - (j : ℝ) * length M) /
        (M 1 0 : ℝ) : ℝ) : ℂ) (D.radius r / (M 1 0 : ℝ)) θ =
      (circleMap (r : ℂ) (D.radius r) θ -
        (epsilon M : ℂ) * (m : ℂ) - (j : ℂ) * (length M : ℂ)) / (M 1 0 : ℂ) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (c_pos M hM))
  simp only [circleMap]
  push_cast
  field_simp
  <;> ring

/-- Every intermediate translate, every component, with exact G1 p',y'. This is pure divisor
geometry; G1RealConclusion is not assumed here. -/
theorem componentChain_g1_separates (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : ℤ) (j : Fin (M 1 0).toNat) :
    G1Separates (componentChain M D m (j : ℤ))
      (g1NumeratorPoles M (repellingTau M) 0 m)
      (g1InversePoles M (repellingTau M) (translatedY M v) 0 (v.1 - M 0 0) m) := by
  have hc := c_pos M hM
  have hcoord (x : ℝ) :
      ((M 1 0 : ℝ) * x + epsilon M * (m : ℝ) - epsilon M * (m : ℝ)) /
        (M 1 0 : ℝ) = x := by
    field_simp
    <;> ring
  have hright (x : ℝ) (hx : x ∈ g1NumeratorPoles M (repellingTau M) 0 m) :
      (M 1 0 : ℝ) * x + epsilon M * (m : ℝ) + (j : ℝ) * length M ∈ commonRight M := by
    apply right_translate_mem M j
    have hcomp := (right_component_divisor M hM m
      ((M 1 0 : ℝ) * x + epsilon M * (m : ℝ))).mpr (by
        simpa only [hcoord x] using hx)
    obtain ⟨K, J, hlabel, hx⟩ := hcomp
    exact ⟨K, J, hx⟩
  have hleft (x : ℝ) (hx : x ∈ g1InversePoles M (repellingTau M)
      (translatedY M v) 0 (v.1 - M 0 0) m) :
      (M 1 0 : ℝ) * x + epsilon M * (m : ℝ) + (j : ℝ) * length M ∈ commonLeft M v := by
    apply left_translate_mem M v j
    have hcomp := (left_component_divisor M hM v m
      ((M 1 0 : ℝ) * x + epsilon M * (m : ℝ))).mpr (by
        simpa only [hcoord x] using hx)
    obtain ⟨K, J, hlabel, hx⟩ := hcomp
    exact ⟨K, J, hx⟩
  change G1Separates
    (affineChain D (M 1 0 : ℝ) (epsilon M * (m : ℝ)) ((j : ℝ) * length M)) _ _
  apply affine_separates D _ _ _ _ _ hc
  · intro r hr
    exact (hD.2.2.2.2.2.2 r hr).1
  · intro x hx
    have hguard : (M 1 0 : ℝ) * x + epsilon M * (m : ℝ) + (j : ℝ) * length M ∈
        guardSet M v := by
      rcases hx with hx | hx
      · exact Or.inl (Or.inl (hright x hx))
      · exact Or.inl (Or.inr (hleft x hx))
    have hb := commonChain_boundary_avoids M hM v δ D hD
    exact ⟨fun heq => hb.1 (heq ▸ hguard), fun r hr => hb.2 r hr _ hguard⟩
  · intro x hx
    exact commonChain_right_assignment M hM u v hwin δ D hD _ (hright x hx)
  · intro x hx
    exact commonChain_left_assignment M hM v δ D hD _ (hleft x hx)

theorem original_numerator_winding_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) (m : ℤ) :
    ∀ x ∈ originalRightComponent M m,
      g1LeftAssignment D x = 0 ∧
        g1LeftAssignment D (x + (M 1 0 : ℝ) * length M) = 0 := by
  intro x hx
  obtain ⟨K, J, hK, hlabel, hx⟩ := hx
  have hbase : x ∈ commonRight M := right_mem M hM ⟨K, J, hx⟩
  have hterminal : x + (M 1 0 : ℝ) * length M ∈ commonRight M :=
    Or.inr ⟨x, ⟨K, J, hK, hx⟩, rfl⟩
  exact ⟨commonChain_right_assignment M hM u v hwin δ D hD x hbase,
    commonChain_right_assignment M hM u v hwin δ D hD _ hterminal⟩

theorem original_inverse_winding_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) (m : ℤ) :
    ∀ x ∈ originalLeftComponent M v m,
      g1LeftAssignment D x = 1 ∧
        g1LeftAssignment D (x + (M 1 0 : ℝ) * length M) = 1 := by
  intro x hx
  obtain ⟨K, J, hJ, hlabel, hx⟩ := hx
  have hbase : x ∈ commonLeft M v := left_mem M hM v ⟨K, J, hx⟩
  have hterminal : x + (M 1 0 : ℝ) * length M ∈ commonLeft M v :=
    Or.inr ⟨x, ⟨K, J, hJ, hx⟩, rfl⟩
  exact ⟨commonChain_left_assignment M hM v δ D hD x hbase,
    commonChain_left_assignment M hM v δ D hD _ hterminal⟩

/-- Includes j=0, the inverse-denominator endpoint. Component-labelled residues at coincident
coordinates are retained for the later ledger. -/
theorem inverse_endpoint_enclosed (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    -inverseOffset M v + (j : ℝ) * length M ∈ D.centers ∧
      g1CircleWinding D (-inverseOffset M v + (j : ℝ) * length M) = 1 := by
  let x := -inverseOffset M v + (j : ℝ) * length M
  have hxleft : x ∈ commonLeft M v := by
    apply left_translate_mem M v j
    exact ⟨0, 0, by simp [leftPoint]⟩
  have hxpos : 0 < x := by
    have hY := (strict_window_bounds M hM u v hwin).2.2.1
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    have hL := length_pos M hM
    dsimp [x]
    nlinarith
  have hxcenter : x ∈ D.centers := by
    rw [← Finset.mem_coe, hD.2.2.2.2.2.1]
    exact ⟨hxleft, hxpos⟩
  refine ⟨hxcenter, winding_one D x hxcenter (hD.2.2.2.2.2.2 x hxcenter).1 ?_⟩
  intro r hr hxr
  exact (hD.2.2.2.2.2.2 r hr).2.2 x (Or.inl (Or.inr hxleft)) hxr

#print CommonChain
#print componentChain
#check componentChain_g1_separates
#check inverse_endpoint_enclosed

end SICLean.L4.G2
