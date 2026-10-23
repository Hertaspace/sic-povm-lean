import SICLean.L4.G2CombResidues
import SICLean.L4.G2StripCounting
import SICLean.L4.G2ComponentJumpsAux

set_option autoImplicit false

/-!
Finite, component-labelled circle changes. Componentwise jump and finite-sum theorems.
[RW26]. This file gives the jump calculation. `circleLabels` is a finite
enumeration by coordinates and component m; equal coordinates in different components are never
merged as residues.
-/

noncomputable section
open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2.ComponentJumps

open CombResidues SICLean.L4.G2ComponentJumpsAux

/-- Candidate integer k at a real coordinate, subsequently checked for exact equality in
circleLabels. Floor is not a zero-class criterion. -/
def coordinateK (M : SL(2, ℤ)) (m : ℤ) (X : ℝ) : ℤ :=
  ⌊(X / scale M - (((1 - M 1 1) * m : ℤ) : ℝ)) / (M 1 0 : ℝ)⌋

/-- Finite enumeration of comb roots at circle centers. The filter discards floor candidates which
are not exact comb roots. -/
def circleLabels (M : SL(2, ℤ)) (D : G1VerticalChain) : Finset (ℤ × ℤ) :=
  ((Finset.univ : Finset (Fin (M 1 0).toNat)).biUnion fun m =>
    D.centers.image (fun X => ((m : ℤ), coordinateK M (m : ℤ) X))).filter
      (fun x => combCoordinate M x.1 x.2 ∈ D.centers)

/-- The two terms carry the same component m. X-cL₂ is k-N. -/
def bracket (M : SL(2, ℤ)) (u v : ℤ × ℤ) (m k : ℤ) : ℂ :=
  rho M u v m k - rho M u v m (k - specialValueOrder M)

/-- h(X)[ρ_m(X)-ρ_m(X-cL₂)], literally with the existing circle winding. -/
def circleTerm (M : SL(2, ℤ)) (u v : ℤ × ℤ) (D : G1VerticalChain)
    (m k : ℤ) : ℂ :=
  (g1CircleWinding D (combCoordinate M m k) : ℂ) * bracket M u v m k

/-- Unique component at X=jL₂ with true zero numerator class. -/
def numeratorJumpLabel (M : SL(2, ℤ)) (j : Fin (M 1 0).toNat) : ℤ × ℤ :=
  let m := ((M 0 0 - 1) * (j : ℤ)) % M 1 0
  (m, (specialValueOrder M * (j : ℤ) - (1 - M 1 1) * m) / M 1 0)

/-- Unique component at X=-Y+jL₂ with true zero denominator class. -/
def denominatorJumpLabel (M : SL(2, ℤ)) (v : ℤ × ℤ)
    (j : Fin (M 1 0).toNat) : ℤ × ℤ :=
  let m := ((M 0 0 - 1) * (j : ℤ) - v.1) % M 1 0
  (m, (specialValueOrder M * (j : ℤ) - sIndex M v - (1 - M 1 1) * m) / M 1 0)

/-- The finite set is exactly the nonzero-winding comb labels. This uses the guard-set radius
condition, not a new analytic chain assumption. [RW26, p. 13]. -/
theorem circleLabels_spec (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m k : ℤ) :
    (m, k) ∈ circleLabels M D ↔
      0 ≤ m ∧ m < M 1 0 ∧ g1CircleWinding D (combCoordinate M m k) ≠ 0 := by
  have hK : coordinateK M m (combCoordinate M m k) = k := by
    have hs : scale M ≠ 0 := (scale_identities M hM).1.ne'
    have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hM.1.ne'
    have he : (combCoordinate M m k / scale M -
        (((1 - M 1 1) * m : ℤ) : ℝ)) / (M 1 0 : ℝ) = (k : ℝ) := by
      dsimp [combCoordinate]
      push_cast
      field_simp
      ring
    simp only [coordinateK, he, Int.floor_intCast]
  have hguard (hm : 0 ≤ m) (hmc : m < M 1 0) :
      combCoordinate M m k ∈ guardSet M v := by
    refine Or.inr ⟨⟨m.toNat, by omega⟩, k, ⟨0, by omega⟩, ?_⟩
    simp only [Nat.cast_zero, zero_mul, add_zero,
      Int.toNat_of_nonneg hm]
  constructor
  · intro hx
    obtain ⟨hlabels, hcenter⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hlabels
    obtain ⟨X, _, hi⟩ := Finset.mem_image.mp hi
    have hm : 0 ≤ m := by
      have he : (i : ℤ) = m := congrArg Prod.fst hi
      omega
    have hmc : m < M 1 0 := by
      have hi' := i.isLt
      have he : (i : ℤ) = m := congrArg Prod.fst hi
      omega
    exact ⟨hm, hmc, (winding_iff_center M hM v δ D hD _ (hguard hm hmc)).mpr hcenter⟩
  · rintro ⟨hm, hmc, hw⟩
    have hc := (winding_iff_center M hM v δ D hD _ (hguard hm hmc)).mp hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨⟨m.toNat, by omega⟩, Finset.mem_univ _, ?_⟩, hc⟩
    apply Finset.mem_image.mpr
    refine ⟨combCoordinate M m k, hc, ?_⟩
    simp only [Int.toNat_of_nonneg hm, hK]

/-- Both tests are tests in the real quotient group. [RW26, Lemma 2, p. 12]. -/
theorem nonexceptional_bracket_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ) (hx : specialValueMk M (m, k) ≠ 0)
    (hxv : specialValueMk M ((m, k) + v) ≠ 0) :
    bracket M u v m k = 0 := by
  exact sub_eq_zero.mpr (rho_shift_eq M hM u v m k
    (fun h => hx h.1) (fun h => hxv h.1))

/-- Full support of a possible branch change, before multiplying by h. The two lists are explicit
labelled roots, not congruence classes of S. [RW26, p. 13]. -/
theorem bracket_support (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hv : specialValueMk M v ≠ 0) (m k : ℤ)
    (hm : 0 ≤ m) (hmc : m < M 1 0) (hb : bracket M u v m k ≠ 0) :
    (∃ j : Fin (M 1 0).toNat, (m, k) = numeratorJumpLabel M j) ∨
      ∃ j : Fin (M 1 0).toNat, (m, k) = denominatorJumpLabel M v j := by
  by_contra h
  apply hb
  apply sub_eq_zero.mpr
  apply rho_shift_eq M hM u v m k
  · rintro ⟨hx, hs, hsc⟩
    obtain ⟨j, hj⟩ := jump_index M hM (m, k) hx hs hsc
    apply h
    left
    refine ⟨j, ?_⟩
    have he := (label_unique M hM 0 (j : ℤ) m k hm hmc).mp
      (by simpa [sIndex] using And.intro hx hj)
    simpa [numeratorJumpLabel, sIndex] using he
  · rintro ⟨hx, hs, hsc⟩
    obtain ⟨j, hj⟩ := jump_index M hM ((m, k) + v) hx hs hsc
    apply h
    right
    exact ⟨j, (label_unique M hM v (j : ℤ) m k hm hmc).mp
      ⟨hx, by simpa only [sIndex_add] using hj⟩⟩

/-- Exact full-class uniqueness at X=jL₂. [RW26, p. 12]. -/
theorem numerator_jump_unique (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (j : Fin (M 1 0).toNat) (m k : ℤ) (hm : 0 ≤ m) (hmc : m < M 1 0) :
    (specialValueMk M (m, k) = 0 ∧
      combCoordinate M m k = (j : ℝ) * length M) ↔
        (m, k) = numeratorJumpLabel M j := by
  have hc := coordinate_eq_iff M hM (m, k) 0 (j : ℤ)
  simp only [inverseOffset, sIndex, Prod.fst_zero, Prod.snd_zero, mul_zero,
    add_zero, Int.cast_zero, neg_zero, zero_add, Int.cast_natCast] at hc
  rw [hc]
  simpa only [numeratorJumpLabel, sIndex, Prod.fst_zero, Prod.snd_zero, mul_zero,
    add_zero, sub_zero] using label_unique M hM 0 (j : ℤ) m k hm hmc

/-- Exact full-class uniqueness at X=-Y+jL₂, including j=0. [RW26, p. 13]. -/
theorem denominator_jump_unique (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (j : Fin (M 1 0).toNat) (m k : ℤ)
    (hm : 0 ≤ m) (hmc : m < M 1 0) :
    (specialValueMk M ((m, k) + v) = 0 ∧
      combCoordinate M m k = -inverseOffset M v + (j : ℝ) * length M) ↔
        (m, k) = denominatorJumpLabel M v j := by
  rw [show (j : ℝ) = ((j : ℤ) : ℝ) by simp,
    coordinate_eq_iff M hM (m, k) v (j : ℤ)]
  exact label_unique M hM v (j : ℤ) m k hm hmc

/-- These c numerator coordinates lie in the common right set, so no numerator A branch is changed.
[RW26, p. 13]. -/
theorem numerator_winding_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    g1CircleWinding D ((j : ℝ) * length M) = 0 := by
  have hx : (j : ℝ) * length M ∈ commonRight M := by
    simpa only [zero_add] using G2ContourChainAux.right_translate_mem M j
      (x := 0) ⟨0, 0, by simp [rightPoint]⟩
  have he := commonChain_right_assignment M hM u v hwin δ D hD _ hx
  have hge : ¬ (j : ℝ) * length M < D.crossing := by
    rw [hD.2.2.2.1]
    nlinarith [Nat.cast_nonneg (α := ℝ) j.val, length_pos M hM, hD.1]
  simpa only [g1LeftAssignment, if_neg hge, zero_add] using he

/-- Component-labelled version: the possible numerator jump contributes zero individually. [RW26, p.
13]. -/
theorem numerator_circleTerm_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    circleTerm M u v D (numeratorJumpLabel M j).1 (numeratorJumpLabel M j).2 = 0 := by
  have hs := label_spec M hM 0 (j : ℤ)
  have hm : 0 ≤ (numeratorJumpLabel M j).1 := by
    simpa only [numeratorJumpLabel, Prod.fst_zero, sub_zero] using hs.1
  have hmc : (numeratorJumpLabel M j).1 < M 1 0 := by
    simpa only [numeratorJumpLabel, Prod.fst_zero, sub_zero] using hs.2.1
  have he := (numerator_jump_unique M hM j _ _ hm hmc).mpr rfl
  change specialValueMk M (numeratorJumpLabel M j) = 0 ∧
    combCoordinate M (numeratorJumpLabel M j).1 (numeratorJumpLabel M j).2 =
      (j : ℝ) * length M at he
  unfold circleTerm
  rw [he.2, numerator_winding_zero M hM u v hwin δ D hD j]
  simp

/-- Actual denominator center values on the two sides of the jump. Neither value is obtained by
substituting into a punctured quotient. [RW26, p. 12] supplies the lattice-value input. -/
theorem denominator_phi_branches (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (j : Fin (M 1 0).toNat) :
    phiDenominator M v (denominatorJumpLabel M v j).1 (denominatorJumpLabel M v j).2 =
        (etaMultiplier M)⁻¹ * (Real.sqrt (epsilon M) : ℂ) ∧
      phiDenominator M v (denominatorJumpLabel M v j).1
          ((denominatorJumpLabel M v j).2 - specialValueOrder M) =
        (etaMultiplier M)⁻¹ / (Real.sqrt (epsilon M) : ℂ) := by
  let x := denominatorJumpLabel M v j
  have hs : 0 ≤ x.1 ∧ x.1 < M 1 0 ∧ specialValueMk M (x + v) = 0 ∧
      sIndex M x + sIndex M v = specialValueOrder M * (j : ℤ) := label_spec M hM v (j : ℤ)
  have hj0 : ¬ (j : ℤ) < 0 := by omega
  have hjc : (j : ℤ) - M 1 0 < 0 := by have := j.isLt; omega
  have hz : specialValueMk M ((x.1, x.2 - specialValueOrder M) + v) = 0 := by
    rw [map_add, (StripCounting.subtract_vertical_period M hM x.1 x.2).2.1, ← map_add]
    exact hs.2.2.1
  have hsz : sIndex M ((x.1, x.2 - specialValueOrder M) + v) =
      specialValueOrder M * ((j : ℤ) - M 1 0) := by
    rw [sIndex_add, sIndex_shift]
    linear_combination hs.2.2.2
  constructor
  · rw [phiDenominator_eq M hM,
      phi_zero_index M hM (x + v) hs.2.2.1 (j : ℤ)
        (by simpa only [sIndex_add] using hs.2.2.2), if_neg hj0]
  · rw [phiDenominator_eq M hM,
      phi_zero_index M hM _ hz _ hsz, if_pos hjc]

/-- Every denominator endpoint has h=1, not only j>0. [RW26, p. 13]. -/
theorem denominator_winding_one (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    g1CircleWinding D (-inverseOffset M v + (j : ℝ) * length M) = 1 := by
  exact (inverse_endpoint_enclosed M hM u v hwin δ D hD j).2

/-- One denominator occurrence changes division by A into division by A⁻¹. The value is independent
of j because its true class is -v. [RW26, (3), p. 3, p. 13]. -/
theorem denominator_circleTerm_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    circleTerm M u v D (denominatorJumpLabel M v j).1 (denominatorJumpLabel M v j).2 =
      (scale M : ℂ) * specialValuePairingLift M (-v) u *
        SpecialValueBridge.repellingPlusLift M (-v) *
        ((Real.sqrt (epsilon M) : ℂ)⁻¹ - (Real.sqrt (epsilon M) : ℂ)) := by
  let x := denominatorJumpLabel M v j
  have hs : 0 ≤ x.1 ∧ x.1 < M 1 0 ∧ specialValueMk M (x + v) = 0 ∧
      sIndex M x + sIndex M v = specialValueOrder M * (j : ℤ) := label_spec M hM v (j : ℤ)
  have hcoord := ((denominator_jump_unique M hM v j x.1 x.2 hs.1 hs.2.1).mpr rfl).2
  have hclass : specialValueMk M x = specialValueMk M (-v) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left (by simpa only [map_add] using hs.2.2.1)
  have hx : specialValueMk M x ≠ 0 := by
    rw [hclass, map_neg]
    exact neg_ne_zero.mpr hv
  have hnum : phiNumerator M x.1 x.2 =
      (etaMultiplier M)⁻¹ * SpecialValueBridge.repellingPlusLift M (-v) := by
    rw [phiNumerator, root_eq_argument M hM, phi_nonzero M hM x hx,
      plusLift_eq M hM x (-v) hclass]
  have hnum' := phiNumerator_shift_eq M hM x.1 x.2 (fun h => hx h.1)
  have hpair := pairing_eq M hM x (-v) u hclass
  have hpair' := pairing_eq M hM (x.1, x.2 - specialValueOrder M) x u
    (StripCounting.subtract_vertical_period M hM x.1 x.2).2.1
  obtain ⟨hd, hd'⟩ := denominator_phi_branches M hM v j
  change circleTerm M u v D x.1 x.2 = _
  simp only [circleTerm, hcoord, denominator_winding_one M hM u v hwin δ D hD j,
    Int.cast_one, one_mul, bracket, rho]
  rw [← hnum', hnum, hpair, hpair', hpair, hd, hd']
  have ht : (Real.sqrt (epsilon M) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (epsilon_pos M hM)).ne'
  field_simp [etaMultiplier_ne_zero M hM.1]

/-- Equal real coordinates in other components have zero bracket, separately. This prevents an S≡0
false zero-class inference in a noncyclic G. [RW26, p. 12, p. 13]. -/
theorem other_components_bracket_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (j : Fin (M 1 0).toNat) (m k : ℤ) (hm : 0 ≤ m) (hmc : m < M 1 0) :
    (combCoordinate M m k = (j : ℝ) * length M →
        m ≠ (numeratorJumpLabel M j).1 → bracket M u v m k = 0) ∧
      (combCoordinate M m k = -inverseOffset M v + (j : ℝ) * length M →
        m ≠ (denominatorJumpLabel M v j).1 → bracket M u v m k = 0) := by
  have hn := specialValueOrder_pos M hM
  have hj0 : 0 ≤ (j : ℤ) := Int.natCast_nonneg _
  have hjc : (j : ℤ) ≤ M 1 0 - 1 := by have := j.isLt; omega
  constructor
  · intro hcoord hmne
    have hs : sIndex M (m, k) = specialValueOrder M * (j : ℤ) := by
      have he := coordinate_eq_iff M hM (m, k) 0 (j : ℤ)
      simp only [inverseOffset, sIndex, Prod.fst_zero, Prod.snd_zero,
        mul_zero, add_zero, Int.cast_zero, neg_zero, zero_add, Int.cast_natCast] at he
      exact he.mp hcoord
    have hx : specialValueMk M (m, k) ≠ 0 := by
      intro hz
      have he := (numerator_jump_unique M hM j m k hm hmc).mp ⟨hz, hcoord⟩
      exact hmne (congrArg Prod.fst he)
    have hneg : sIndex M ((m, k) + v) < 0 := by
      rw [sIndex_add, hs]
      nlinarith [hwin.2.2.2]
    exact sub_eq_zero.mpr (rho_shift_eq M hM u v m k
      (fun h => hx h.1) (fun h => (not_le_of_gt hneg) h.2.1))
  · intro hcoord hmne
    have hs : sIndex M (m, k) + sIndex M v = specialValueOrder M * (j : ℤ) := by
      apply (coordinate_eq_iff M hM (m, k) v (j : ℤ)).mp
      simpa only [Int.cast_natCast] using hcoord
    have hxv : specialValueMk M ((m, k) + v) ≠ 0 := by
      intro hz
      have he := (denominator_jump_unique M hM v j m k hm hmc).mp ⟨hz, hcoord⟩
      exact hmne (congrArg Prod.fst he)
    apply sub_eq_zero.mpr
    apply rho_shift_eq M hM u v m k
    · rintro ⟨hx, hs0, hsc⟩
      obtain ⟨i, hi⟩ := jump_index M hM (m, k) hx hs0 hsc
      have hic : (i : ℤ) ≤ M 1 0 - 1 := by have := i.isLt; omega
      nlinarith [hwin.2.2.2]
    · exact fun h => hxv h.1

/-- All nonzero circle corrections occur at the explicitly listed denominator labels. Numerator
labels are already zero after h. [RW26, p. 13]. -/
theorem circleTerm_support (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) (m k : ℤ)
    (hm : 0 ≤ m) (hmc : m < M 1 0) (ht : circleTerm M u v D m k ≠ 0) :
    ∃ j : Fin (M 1 0).toNat, (m, k) = denominatorJumpLabel M v j := by
  have hb : bracket M u v m k ≠ 0 := by
    intro h
    exact ht (by simp [circleTerm, h])
  rcases bracket_support M hM u v hv m k hm hmc hb with ⟨j, hj⟩ | ⟨j, hj⟩
  · have he := numerator_circleTerm_zero M hM u v hwin δ D hD j
    rw [← hj] at he
    exact (ht he).elim
  · exact ⟨j, hj⟩

/-- j=0 is present and its contribution is nonzero. The explicit j₀ parameter avoids manufacturing a
Fin inhabitant by a proof in a definition. [RW26, p. 13]. -/
theorem inverse_endpoint_nonzero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j₀ : Fin (M 1 0).toNat) (hj₀ : (j₀ : ℕ) = 0) :
    denominatorJumpLabel M v j₀ ∈ circleLabels M D ∧
      combCoordinate M (denominatorJumpLabel M v j₀).1 (denominatorJumpLabel M v j₀).2 =
        -inverseOffset M v ∧
      circleTerm M u v D (denominatorJumpLabel M v j₀).1
        (denominatorJumpLabel M v j₀).2 ≠ 0 := by
  let x := denominatorJumpLabel M v j₀
  have hs : 0 ≤ x.1 ∧ x.1 < M 1 0 ∧ specialValueMk M (x + v) = 0 ∧
      sIndex M x + sIndex M v = specialValueOrder M * (j₀ : ℤ) := label_spec M hM v (j₀ : ℤ)
  have hcoord := ((denominator_jump_unique M hM v j₀ x.1 x.2 hs.1 hs.2.1).mpr rfl).2
  have hmem : x ∈ circleLabels M D := by
    apply (circleLabels_spec M hM v δ D hD x.1 x.2).mpr
    exact ⟨hs.1, hs.2.1, by rw [hcoord, denominator_winding_one M hM u v hwin δ D hD j₀]; norm_num⟩
  refine ⟨hmem, ?_, ?_⟩
  · simpa only [hj₀, Nat.cast_zero, zero_mul, add_zero] using hcoord
  · rw [denominator_circleTerm_value M hM u v hwin hv δ D hD j₀]
    have hscale : (scale M : ℂ) ≠ 0 := by exact_mod_cast (scale_identities M hM).1.ne'
    have hpair : specialValuePairingLift M (-v) u ≠ 0 := e_ne_zero _
    have hplus : SpecialValueBridge.repellingPlusLift M (-v) ≠ 0 := by
      rw [← (SpecialValueBridge.repellingValues_mk M hM (-v)).1]
      exact (SpecialValueBridge.repellingValues_ne_zero M hM _).1
    have ht := Real.sqrt_pos.mpr (epsilon_pos M hM)
    have hdiff : (Real.sqrt (epsilon M) : ℂ)⁻¹ - (Real.sqrt (epsilon M) : ℂ) ≠ 0 := by
      intro he
      have heR : (Real.sqrt (epsilon M))⁻¹ - Real.sqrt (epsilon M) = 0 := by exact_mod_cast he
      have he' := congrArg (fun z : ℝ => z * Real.sqrt (epsilon M)) heR
      rw [sub_mul, inv_mul_cancel₀ ht.ne', zero_mul] at he'
      nlinarith [Real.sq_sqrt (epsilon_pos M hM).le, epsilon_lt_one M hM]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscale hpair) hplus) hdiff

/-- After the componentwise exclusions, precisely c copies of the same denominator correction
remain. [RW26, p. 13]. -/
theorem circle_correction_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    (∑ x ∈ circleLabels M D, circleTerm M u v D x.1 x.2) =
      (M 1 0 : ℂ) * (scale M : ℂ) * specialValuePairingLift M (-v) u *
        SpecialValueBridge.repellingPlusLift M (-v) *
        ((Real.sqrt (epsilon M) : ℂ)⁻¹ - (Real.sqrt (epsilon M) : ℂ)) := by
  let q := denominatorJumpLabel M v
  let f := fun x : ℤ × ℤ => circleTerm M u v D x.1 x.2
  have hq (j : Fin (M 1 0).toNat) :
      0 ≤ (q j).1 ∧ (q j).1 < M 1 0 ∧ specialValueMk M (q j + v) = 0 ∧
        sIndex M (q j) + sIndex M v = specialValueOrder M * (j : ℤ) :=
    label_spec M hM v (j : ℤ)
  have hqmem (j : Fin (M 1 0).toNat) : q j ∈ circleLabels M D := by
    have hc : combCoordinate M (q j).1 (q j).2 =
        -inverseOffset M v + (j : ℝ) * length M :=
      ((denominator_jump_unique M hM v j _ _ (hq j).1 (hq j).2.1).mpr rfl).2
    apply (circleLabels_spec M hM v δ D hD _ _).mpr
    refine ⟨(hq j).1, (hq j).2.1, ?_⟩
    change g1CircleWinding D (combCoordinate M (q j).1 (q j).2) ≠ 0
    rw [hc, denominator_winding_one M hM u v hwin δ D hD j]
    norm_num
  have hinj : Function.Injective q := by
    intro i j hij
    have hi := (hq i).2.2.2
    rw [hij] at hi
    have he : (i : ℤ) = (j : ℤ) :=
      mul_left_cancel₀ (specialValueOrder_pos M hM).ne' (hi.symm.trans (hq j).2.2.2)
    apply Fin.ext
    exact_mod_cast he
  have hsub : Finset.univ.image q ⊆ circleLabels M D := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hqmem j
  have hsum : (∑ x ∈ circleLabels M D, f x) = ∑ x ∈ Finset.univ.image q, f x := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hxq
    by_contra hfx
    have hrange := (circleLabels_spec M hM v δ D hD x.1 x.2).mp hx
    obtain ⟨j, hj⟩ := circleTerm_support M hM u v hwin hv δ D hD x.1 x.2
      hrange.1 hrange.2.1 hfx
    exact hxq (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩)
  change (∑ x ∈ circleLabels M D, f x) = _
  rw [hsum, Finset.sum_image (fun i _ j _ hij => hinj hij)]
  change (∑ j : Fin (M 1 0).toNat,
    circleTerm M u v D (denominatorJumpLabel M v j).1 (denominatorJumpLabel M v j).2) = _
  simp only [denominator_circleTerm_value M hM u v hwin hv δ D hD,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast (Int.toNat_of_nonneg hM.1.le)
  rw [hc]
  ring

/-- Deleting just the labelled j=0 term changes the comb ledger. This is not a claim that deleting a
geometric circle affects no original Φ poles. [RW26, p. 13]. -/
theorem omit_endpoint_changes_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j₀ : Fin (M 1 0).toNat) (hj₀ : (j₀ : ℕ) = 0) :
    (∑ x ∈ (circleLabels M D).erase (denominatorJumpLabel M v j₀),
        circleTerm M u v D x.1 x.2) ≠
      ∑ x ∈ circleLabels M D, circleTerm M u v D x.1 x.2 := by
  obtain ⟨hmem, _, hne⟩ := inverse_endpoint_nonzero M hM u v hwin hv δ D hD j₀ hj₀
  have hs := Finset.sum_erase_add (circleLabels M D)
    (fun x => circleTerm M u v D x.1 x.2) hmem
  intro h
  rw [h] at hs
  exact hne (add_left_cancel (hs.trans (add_zero _).symm))

#print denominatorJumpLabel
#print circleLabels
#print circleTerm
#check @denominator_phi_branches
#check @other_components_bracket_zero
#check @inverse_endpoint_nonzero

end SICLean.L4.G2.ComponentJumps
