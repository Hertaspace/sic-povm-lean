import SICLean.L4.G2ComponentJumps
import SICLean.L4.G2ResidueLedgerAux

set_option autoImplicit false

/-!
The complete residue ledger and the call interface.
The fixed fifteen-statement interface, with proofs.
Component and endpoint contributions are included. [RW26, p. 13].

The first obligations below cancel every original Φ-pole's net winding.
Only then is the full rawIntegral identified with the comb baseline plus
the comb circle correction. Neither summand alone is asserted to be the
full straight-strip integral or the full circle-integral difference.
Local principal parts and analyticity are conclusions for the actual
kernel, not hypotheses smuggled into CommonChain or ledger definitions.
-/

noncomputable section
open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2.ResidueLedger

open CombResidues ComponentJumps StripCounting

/-- Right up minus left up: assignment(X)-assignment(X+cL₂). -/
def originalNetWinding (M : SL(2, ℤ)) (D : G1VerticalChain) (X : ℝ) : ℤ :=
  g1LeftAssignment D X - g1LeftAssignment D (X + (M 1 0 : ℝ) * length M)

/-- Candidate coordinates of the actual raw kernel, not of the final
ratio kernel. The original families retain K≥1 and J≥1. -/
def poleCoordinates (M : SL(2, ℤ)) (v : ℤ × ℤ) (m : ℤ) : Set ℝ :=
  originalRightComponent M m ∪ originalLeftComponent M v m ∪
    {X | ∃ k : ℤ, X = combCoordinate M m k}

/-- Only the comb contribution of the straight strip. -/
def combBaseline (M : SL(2, ℤ)) (u v : ℤ × ℤ) : ℂ :=
  ∑ x ∈ stripFinset M, rho M u v x.1 x.2

/-- Only the comb contribution of the circles after the left-circle
reindexing. The full integral identity is a theorem below. -/
def combCircleCorrection (M : SL(2, ℤ)) (u v : ℤ × ℤ) (D : G1VerticalChain) : ℂ :=
  ∑ x ∈ circleLabels M D, circleTerm M u v D x.1 x.2

def lowerCircleLabels (M : SL(2, ℤ)) (D : G1VerticalChain) : Finset (ℤ × ℤ) :=
  (circleLabels M D).image (fun x => (x.1, x.2 - specialValueOrder M))

/-- Return a label in a fixed component to its unique k residue in the
straight strip. This does not attempt to choose a cyclic coordinate on G. -/
def baselineLabel (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℤ × ℤ :=
  (x.1, firstK M x.1 + (x.2 - firstK M x.1) % specialValueOrder M)

/-- Quotient-level baseline summand, with the actual repelling F⁺. -/
def baselineSummand (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v x : SpecialValueGroup M) : ℂ :=
  specialValuePairing M hM x u * SpecialValueBridge.repellingPlus M hM x /
    SpecialValueBridge.repellingPlus M hM (x + v)

/--
Quotient-level summand, ready for finite Fourier/pentagon
work. Neither function nor pairing is selected to satisfy a sum identity.
-/
def ratioSummand (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v x : SpecialValueGroup M) : ℂ :=
  specialValuePairing M hM x u * SpecialValueBridge.repellingPlus M hM x /
    SpecialValueBridge.repellingMinus M hM (x + v)

/--
Original numerator poles have net winding 0 before computing any
comb sum; [RW26, p. 13].
-/
theorem original_numerator_net_winding_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) (m : ℤ) :
    ∀ X ∈ originalRightComponent M m, originalNetWinding M D X = 0 := by
  intro X hX
  obtain ⟨h₀, h₁⟩ := original_numerator_winding_zero M hM u v hwin δ D hD m X hX
  simp only [originalNetWinding, h₀, h₁, sub_self]

/--
Original inverse-Φ poles may contribute to the straight strip or
circles separately, but their total winding is 1-1=0; [RW26, p. 13].
-/
theorem original_inverse_net_winding_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) (m : ℤ) :
    ∀ X ∈ originalLeftComponent M v m, originalNetWinding M D X = 0 := by
  intro X hX
  obtain ⟨h₀, h₁⟩ := original_inverse_winding_zero M hM v δ D hD m X hX
  simp only [originalNetWinding, h₀, h₁, sub_self]

/--
The actual raw kernel supplies local principal parts at original
candidate poles (possibly removable, hence n=0 is allowed). No simple
Φ-pole assumption is made; [RW26, p. 6, p. 13] finite principal-parts API.
-/
theorem original_local_principalParts (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (X : ℝ)
    (hX : X ∈ originalRightComponent M m ∪ originalLeftComponent M v m) :
    ∃ (R : ℝ) (n : ℕ) (A : ℕ → ℂ) (g : ℂ → ℂ), 0 < R ∧
      AnalyticOnNhd ℂ g (Metric.closedBall (affinePoint M m 0 (X : ℂ)) R) ∧
      ∀ z ∈ Metric.closedBall (affinePoint M m 0 (X : ℂ)) R,
        z ≠ affinePoint M m 0 (X : ℂ) →
          rawF M u v m z =
            FinitePrincipalParts.principalPart (affinePoint M m 0 (X : ℂ)) n A z + g z := by
  exact G2ResidueLedgerAux.original_local_principalParts M hM u v m X

/--
There are no unlisted poles. This is analyticity of the existing
point-valued rawF at each point outside its explicit candidate set; [RW26, p. 6, p. 13].
-/
theorem rawF_analytic_off_poles (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (z : ℂ)
    (hz : z ∉ (fun X : ℝ => affinePoint M m 0 (X : ℂ)) '' poleCoordinates M v m) :
    AnalyticAt ℂ (rawF M u v m) z := by
  apply G2ResidueLedgerAux.rawF_analytic_off_poles M hM u v m z
  simpa only [poleCoordinates] using hz

/--
Both actual Φ centers on every straight-strip label are the plus
branch, including both exceptional zero classes; [RW26, p. 12, p. 13].
-/
theorem strip_phi_plus_values (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (x : ℤ × ℤ) (hx : x ∈ stripFinset M) :
    etaMultiplier M * phiNumerator M x.1 x.2 = SpecialValueBridge.repellingPlusLift M x ∧
      etaMultiplier M * phiDenominator M v x.1 x.2 =
        SpecialValueBridge.repellingPlusLift M (x + v) := by
  have hplus (y : ℤ × ℤ) (hy : sIndex M y < 0) :
      etaMultiplier M * modularPhi M y.1 0 (argument M y : ℂ) (repellingTau M : ℂ) =
        SpecialValueBridge.repellingPlusLift M y := by
    by_cases hy₀ : specialValueMk M y = 0
    · have hlat : y ∈ specialValueLattice M := (QuotientAddGroup.eq_zero_iff y).mp hy₀
      have he : 1 ≤ Evaluation.commonExponent M y 0 := by
        have hh := Evaluation.commonExponent_cast M hM y hy₀ 0
        have hN : 0 < (specialValueOrder M : ℝ) := by
          exact_mod_cast specialValueOrder_pos M hM
        have hneg : (sIndex M y : ℝ) / (specialValueOrder M : ℝ) < 0 :=
          div_neg_of_neg_of_pos (by exact_mod_cast hy) hN
        have hpos : (0 : ℝ) < (Evaluation.commonExponent M y 0 : ℝ) := by
          rw [hh]
          simpa only [Int.cast_zero, zero_sub] using neg_pos.mpr hneg
        have : 0 < Evaluation.commonExponent M y 0 := by exact_mod_cast hpos
        omega
      have hval := Evaluation.zero_class_phi_value M hM y hy₀ 0
      simp only [add_zero, if_pos he] at hval
      rw [hval, SpecialValueBridge.repellingPlusLift, if_pos hlat]
      field_simp [etaMultiplier_ne_zero M hM.1]
    · have hlat : y ∉ specialValueLattice M := fun hy =>
        hy₀ ((QuotientAddGroup.eq_zero_iff y).mpr hy)
      simp only [SpecialValueBridge.repellingPlusLift, if_neg hlat,
        RepellingPointValues.repellingRaw]
  have hS : sIndex M x < 0 := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (canonicalRepresentative_sIndex_bounds M hM i).2
  have hvS : sIndex M v < 0 := by
    have hc : 0 ≤ M 1 0 - 1 := by have := hM.1; omega
    have hprod := mul_nonneg hc (specialValueOrder_pos M hM).le
    have := hwin.2.2.2
    omega
  have hSv : sIndex M (x + v) < 0 := by
    have hadd : sIndex M (x + v) = sIndex M x + sIndex M v := by
      simp [sIndex, mul_add]
      ring
    rw [hadd]
    omega
  constructor
  · simpa only [phiNumerator, root_eq_argument M hM, Prod.eta] using hplus x hS
  · have harg : (argument M (x + v) : ℂ) =
        (argument M x : ℂ) + (argument M v : ℂ) := by
      rw [Evaluation.argument_add, Complex.ofReal_add]
    simpa only [phiDenominator, root_eq_argument M hM, Prod.eta, harg, Prod.fst_add] using
      hplus (x + v) hSv

/--
All c numerator-zero occurrences retain A. This is the full true
quotient equality, not the scalar congruence S≡0; [RW26, p. 12, p. 13].
-/
theorem numerator_A_occurrences (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    ((stripFinset M).filter (fun x => specialValueMk M x = 0)).card = (M 1 0).toNat ∧
      ∀ x ∈ stripFinset M, specialValueMk M x = 0 →
        etaMultiplier M * phiNumerator M x.1 x.2 = (Real.sqrt (epsilon M) : ℂ)⁻¹ := by
  refine ⟨(zero_class_counts M hM 0).1, ?_⟩
  intro x hx hx₀
  have hwin := representativeWindow_construct M hM (0 : ℤ × ℤ) (0 : ℤ × ℤ)
  have hval := (strip_phi_plus_values M hM _ _ hwin x hx).1
  rw [← (SpecialValueBridge.repellingValues_mk M hM x).1, hx₀,
    (SpecialValueBridge.repellingValues_zero M hM).1] at hval
  exact hval

/--
Before the circle correction all c denominator-zero occurrences
divide by A; [RW26, p. 12, p. 13].
-/
theorem denominator_baseline_A_occurrences (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    ((stripFinset M).filter (fun x => specialValueMk M (x + v) = 0)).card =
        (M 1 0).toNat ∧
      ∀ x ∈ stripFinset M, specialValueMk M (x + v) = 0 →
        etaMultiplier M * phiDenominator M v x.1 x.2 = (Real.sqrt (epsilon M) : ℂ)⁻¹ := by
  refine ⟨?_, ?_⟩
  · simpa only [map_add] using (zero_class_counts M hM (specialValueMk M v)).2
  · intro x hx hxv₀
    have hval := (strip_phi_plus_values M hM u v hwin x hx).2
    rw [← (SpecialValueBridge.repellingValues_mk M hM (x + v)).1, hxv₀,
      (SpecialValueBridge.repellingValues_zero M hM).1] at hval
    exact hval

/--
The c denominator jumps return bijectively to the c exceptional
baseline occurrences. Thus every occurrence is included, including j=0;
neither a component nor a true group class is replaced by S mod N; [RW26, p. 12, p. 13].
-/
theorem denominator_jump_baseline_bijection (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (v : ℤ × ℤ) :
    Function.Injective (denominatorJumpLabel M v) ∧
      Set.BijOn (baselineLabel M) (Set.range (denominatorJumpLabel M v))
        {x | x ∈ stripFinset M ∧ specialValueMk M (x + v) = 0} := by
  have hN := specialValueOrder_pos M hM
  have hc := hM.1
  have hlabel (j : Fin (M 1 0).toNat) :
      0 ≤ (denominatorJumpLabel M v j).1 ∧
      (denominatorJumpLabel M v j).1 < M 1 0 ∧
      specialValueMk M (denominatorJumpLabel M v j + v) = 0 ∧
      sIndex M (denominatorJumpLabel M v j) + sIndex M v = specialValueOrder M * (j : ℤ) := by
    have hm : 0 ≤ (denominatorJumpLabel M v j).1 := Int.emod_nonneg _ (ne_of_gt hc)
    have hmc : (denominatorJumpLabel M v j).1 < M 1 0 := Int.emod_lt_of_pos _ hc
    obtain ⟨hclass, hcoord⟩ :=
      (denominator_jump_unique M hM v j _ _ hm hmc).mpr (Prod.eta _)
    refine ⟨hm, hmc, hclass, ?_⟩
    change scale M * (sIndex M (denominatorJumpLabel M v j) : ℝ) =
      -(scale M * (sIndex M v : ℝ)) + (j : ℝ) * length M at hcoord
    rw [G2ContourChainAux.length_eq_scale_mul M hM] at hcoord
    have hreal : (sIndex M (denominatorJumpLabel M v j) : ℝ) + (sIndex M v : ℝ) =
        (specialValueOrder M : ℝ) * (j : ℝ) := by
      apply mul_left_cancel₀ (ne_of_gt (scale_identities M hM).1)
      linear_combination hcoord
    exact_mod_cast hreal
  have hbaseclass (x : ℤ × ℤ) : specialValueMk M (baselineLabel M x) = specialValueMk M x := by
    have hperiod : specialValueMk M (0, specialValueOrder M) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (vertical_period_mem M).2
    have heq : baselineLabel M x =
        x + (-((x.2 - firstK M x.1) / specialValueOrder M)) • (0, specialValueOrder M) := by
      apply Prod.ext
      · simp [baselineLabel]
      · have hdiv := Int.emod_add_mul_ediv (x.2 - firstK M x.1) (specialValueOrder M)
        change firstK M x.1 + (x.2 - firstK M x.1) % specialValueOrder M =
          x.2 + (-((x.2 - firstK M x.1) / specialValueOrder M)) • specialValueOrder M
        rw [zsmul_eq_mul]
        simp only [Int.cast_id, neg_mul]
        nlinarith
    rw [heq, map_add, map_zsmul, hperiod, smul_zero, add_zero]
  have hbasemem (x : ℤ × ℤ) (hm : 0 ≤ x.1) (hmc : x.1 < M 1 0) :
      baselineLabel M x ∈ stripFinset M := by
    let r := (x.2 - firstK M x.1) % specialValueOrder M
    have hr : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hN)
    have hrN : r < specialValueOrder M := Int.emod_lt_of_pos _ hN
    have hmnat : x.1.toNat < (M 1 0).toNat := by omega
    have hrnat : r.toNat < (specialValueOrder M).toNat := by omega
    refine Finset.mem_image.mpr ⟨(⟨x.1.toNat, hmnat⟩, ⟨r.toNat, hrnat⟩), Finset.mem_univ _, ?_⟩
    simp only [canonicalRepresentative, Int.toNat_of_nonneg hm, Int.toNat_of_nonneg hr]
    rfl
  let F : Fin (M 1 0).toNat → ℤ × ℤ := fun j => baselineLabel M (denominatorJumpLabel M v j)
  have hFinj : Function.Injective F := by
    intro i j hij
    have hm := congrArg Prod.fst hij
    change (denominatorJumpLabel M v i).1 = (denominatorJumpLabel M v j).1 at hm
    have hk := congrArg Prod.snd hij
    change firstK M (denominatorJumpLabel M v i).1 +
        ((denominatorJumpLabel M v i).2 - firstK M (denominatorJumpLabel M v i).1) % specialValueOrder M =
      firstK M (denominatorJumpLabel M v j).1 +
        ((denominatorJumpLabel M v j).2 - firstK M (denominatorJumpLabel M v j).1) % specialValueOrder M at hk
    rw [hm] at hk
    have hrem := add_left_cancel hk
    let q := ((denominatorJumpLabel M v j).2 - firstK M (denominatorJumpLabel M v j).1) / specialValueOrder M -
      ((denominatorJumpLabel M v i).2 - firstK M (denominatorJumpLabel M v j).1) / specialValueOrder M
    have hkk : (denominatorJumpLabel M v j).2 - (denominatorJumpLabel M v i).2 = specialValueOrder M * q := by
      have hi := Int.emod_add_mul_ediv
        ((denominatorJumpLabel M v i).2 - firstK M (denominatorJumpLabel M v j).1) (specialValueOrder M)
      have hj := Int.emod_add_mul_ediv
        ((denominatorJumpLabel M v j).2 - firstK M (denominatorJumpLabel M v j).1) (specialValueOrder M)
      dsimp [q]
      rw [hrem] at hi
      nlinarith
    have hi := (hlabel i).2.2.2
    have hj := (hlabel j).2.2.2
    simp only [sIndex] at hi hj
    rw [hm] at hi
    have hmul : specialValueOrder M * ((j : ℤ) - (i : ℤ)) =
        specialValueOrder M * (M 1 0 * q) := by
      linear_combination -hj + hi + M 1 0 * hkk
    have hji := mul_left_cancel₀ (ne_of_gt hN) hmul
    exact G2PoleSeparationAux.fin_int_modEq_eq hc i j
      (Int.modEq_iff_dvd.mpr ⟨q, hji⟩)
  let T := (stripFinset M).filter (fun x => specialValueMk M (x + v) = 0)
  have hFmem (j : Fin (M 1 0).toNat) : F j ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨hbasemem _ (hlabel j).1 (hlabel j).2.1, ?_⟩
    rw [map_add, hbaseclass, ← map_add]
    exact (hlabel j).2.2.1
  have himage : Finset.univ.image F = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact hFmem j
    · rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_fin]
      have hcount := (zero_class_counts M hM (specialValueMk M v)).2
      simpa only [T, map_add] using le_of_eq hcount
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hFinj (congrArg (baselineLabel M) hij)
  · rintro x ⟨j, rfl⟩
    exact Finset.mem_filter.mp (hFmem j)
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hij
    exact congrArg (denominatorJumpLabel M v) (hFinj hij)
  · intro x hx
    have hxt : x ∈ T := Finset.mem_filter.mpr hx
    rw [← himage] at hxt
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hxt
    exact ⟨denominatorJumpLabel M v j, ⟨j, rfl⟩, hj⟩

/--
Comb baseline only, not the whole straight-strip integral; [RW26, p. 12, p. 13].
-/
theorem comb_baseline_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    combBaseline M u v = (M 1 0 : ℂ) * (scale M : ℂ) *
      groupSum M hM (baselineSummand M hM (specialValueMk M u) (specialValueMk M v)) := by
  have hterm (x : ℤ × ℤ) (hx : x ∈ stripFinset M) :
      rho M u v x.1 x.2 = (scale M : ℂ) *
        baselineSummand M hM (specialValueMk M u) (specialValueMk M v) (specialValueMk M x) := by
    obtain ⟨hn, hd⟩ := strip_phi_plus_values M hM u v hwin x hx
    unfold baselineSummand
    rw [← map_add, specialValuePairing_mk,
      (SpecialValueBridge.repellingValues_mk M hM x).1,
      (SpecialValueBridge.repellingValues_mk M hM (x + v)).1, ← hn, ← hd]
    unfold rho
    field_simp [etaMultiplier_ne_zero M hM.1]
  unfold combBaseline
  calc
    (∑ x ∈ stripFinset M, rho M u v x.1 x.2) = (scale M : ℂ) *
        ∑ x ∈ stripFinset M,
          baselineSummand M hM (specialValueMk M u) (specialValueMk M v) (specialValueMk M x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hterm
    _ = _ := by rw [strip_sum M hM]; ring

/--
Reindex just the comb parts of the two circle sums. Original Φ-pole
circle residues have not been set to zero individually; [RW26, p. 13].
-/
theorem comb_circle_reindexing (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (D : G1VerticalChain) :
    (∑ x ∈ circleLabels M D,
        (g1CircleWinding D (combCoordinate M x.1 x.2) : ℂ) * rho M u v x.1 x.2) -
      (∑ x ∈ lowerCircleLabels M D,
        (g1CircleWinding D (combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M) : ℂ) *
          rho M u v x.1 x.2) = combCircleCorrection M u v D := by
  have hinj : Function.Injective (fun x : ℤ × ℤ => (x.1, x.2 - specialValueOrder M)) := by
    intro x y h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext h₁ (by dsimp at h₂; omega)
  rw [lowerCircleLabels, Finset.sum_image (fun x _ y _ h => hinj h)]
  unfold combCircleCorrection circleTerm bracket
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(root_shift M hM x.1 x.2).2]
  simp only [sub_add_cancel]
  ring

/--
The full raw integral. Finite principal parts, positive orientation,
horizontal closure, and both zero original windings precede this
step. No residue/integral equation is an input; [RW26, p. 13].
-/
theorem rawIntegral_comb_account (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    Telescoping.rawIntegral M u v D = combBaseline M u v + combCircleCorrection M u v D := by
  let T := stripFinset M ∪ circleLabels M D ∪ lowerCircleLabels M D
  let W := fun x : ℤ × ℤ =>
    ((g1LeftAssignment D (combCoordinate M x.1 x.2) -
      g1LeftAssignment D (combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M) : ℤ) : ℂ)
  have hrange (x : ℤ × ℤ) (hx : x ∈ T) : 0 ≤ x.1 ∧ x.1 < M 1 0 := by
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact ⟨((mem_stripFinset_iff M hM δ hD.1 hD.2.1 x).mp hx).1,
          ((mem_stripFinset_iff M hM δ hD.1 hD.2.1 x).mp hx).2.1⟩
      · exact ((circleLabels_spec M hM v δ D hD x.1 x.2).mp hx).imp_right And.left
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact ((circleLabels_spec M hM v δ D hD y.1 y.2).mp hy).imp_right And.left
  have hweights (x : ℤ × ℤ) (hx : x ∈ T) :
      W x = (if x ∈ stripFinset M then (1 : ℂ) else 0) +
        (g1CircleWinding D (combCoordinate M x.1 x.2) : ℂ) -
        (g1CircleWinding D (combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M) : ℂ) := by
    have hm := hrange x hx
    have hmnat : x.1.toNat < (M 1 0).toNat := by omega
    have hterminal : combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M ≠ -δ := by
      intro heq
      apply (commonChain_boundary_avoids M hM v δ D hD).1
      right
      refine ⟨⟨x.1.toNat, hmnat⟩, x.2, ⟨(M 1 0).toNat, by omega⟩, ?_⟩
      have hcReal : ((M 1 0).toNat : ℝ) = (M 1 0 : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hM.1.le
      simpa only [Int.toNat_of_nonneg hm.1, hcReal, hD.2.2.2.1] using heq.symm
    have hwidth : 0 < (M 1 0 : ℝ) * length M :=
      mul_pos (by exact_mod_cast hM.1) (length_pos M hM)
    have hbase : ((if combCoordinate M x.1 x.2 < -δ then 1 else 0) -
        (if combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M < -δ then 1 else 0) : ℤ) =
        if x ∈ stripFinset M then 1 else 0 := by
      by_cases hright : combCoordinate M x.1 x.2 < -δ
      · by_cases hleft : combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M < -δ
        · have hnot : x ∉ stripFinset M := by
            intro hmem
            have := ((mem_stripFinset_iff M hM δ hD.1 hD.2.1 x).mp hmem).2.2.1
            linarith
          simp only [if_pos hright, if_pos hleft, if_neg hnot, sub_self]
        · have hmem : x ∈ stripFinset M := by
            apply (mem_stripFinset_iff M hM δ hD.1 hD.2.1 x).mpr
            refine ⟨hm.1, hm.2, ?_, hright⟩
            have := lt_of_le_of_ne (le_of_not_gt hleft) hterminal.symm
            linarith
          simp only [if_pos hright, if_neg hleft, if_pos hmem, sub_zero]
      · have hleft : ¬combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M < -δ := by
          linarith
        have hnot : x ∉ stripFinset M := fun hmem =>
          hright ((mem_stripFinset_iff M hM δ hD.1 hD.2.1 x).mp hmem).2.2.2
        simp only [if_neg hright, if_neg hleft, if_neg hnot, sub_self]
    have hcbase := congrArg (fun n : ℤ => (n : ℂ)) hbase
    dsimp [W]
    simp only [g1LeftAssignment, hD.2.2.2.1, Int.cast_sub, Int.cast_add]
    push_cast at hcbase ⊢
    linear_combination hcbase
  have hcircles : circleLabels M D ⊆ T := fun _ hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hlower : lowerCircleLabels M D ⊆ T := fun _ hx => Finset.mem_union_right _ hx
  have hstrip : stripFinset M ⊆ T := fun _ hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hup : (∑ x ∈ T, (g1CircleWinding D (combCoordinate M x.1 x.2) : ℂ) * rho M u v x.1 x.2) =
      ∑ x ∈ circleLabels M D,
        (g1CircleWinding D (combCoordinate M x.1 x.2) : ℂ) * rho M u v x.1 x.2 := by
    symm
    apply Finset.sum_subset hcircles
    intro x hx hnot
    have hw : g1CircleWinding D (combCoordinate M x.1 x.2) = 0 := by
      by_contra hw
      exact hnot ((circleLabels_spec M hM v δ D hD x.1 x.2).mpr ⟨(hrange x hx).1, (hrange x hx).2, hw⟩)
    simp only [hw, Int.cast_zero, zero_mul]
  have hdown : (∑ x ∈ T,
        (g1CircleWinding D (combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M) : ℂ) * rho M u v x.1 x.2) =
      ∑ x ∈ lowerCircleLabels M D,
        (g1CircleWinding D (combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M) : ℂ) * rho M u v x.1 x.2 := by
    symm
    apply Finset.sum_subset hlower
    intro x hx hnot
    have hw : g1CircleWinding D (combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M) = 0 := by
      by_contra hw
      have hshift : combCoordinate M x.1 (x.2 + specialValueOrder M) =
          combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M := by
        have h := (root_shift M hM x.1 (x.2 + specialValueOrder M)).2
        simp only [add_sub_cancel_right] at h
        linarith
      apply hnot
      apply Finset.mem_image.mpr
      refine ⟨(x.1, x.2 + specialValueOrder M), ?_, ?_⟩
      · exact (circleLabels_spec M hM v δ D hD _ _).mpr
          ⟨(hrange x hx).1, (hrange x hx).2, by simpa only [hshift] using hw⟩
      · simp only [add_sub_cancel_right, Prod.eta]
    simp only [hw, Int.cast_zero, zero_mul]
  have hbaseSum : (∑ x ∈ T, if x ∈ stripFinset M then rho M u v x.1 x.2 else 0) =
      combBaseline M u v := by
    calc
      _ = ∑ x ∈ stripFinset M, if x ∈ stripFinset M then rho M u v x.1 x.2 else 0 := by
        symm
        apply Finset.sum_subset hstrip
        intro x _ hnot
        simp only [if_neg hnot]
      _ = combBaseline M u v := by
        unfold combBaseline
        apply Finset.sum_congr rfl
        intro x hx
        rw [if_pos hx]
  have hweighted : (∑ x ∈ T, W x * rho M u v x.1 x.2) =
      combBaseline M u v + combCircleCorrection M u v D := by
    calc
      (∑ x ∈ T, W x * rho M u v x.1 x.2) =
          (∑ x ∈ T, if x ∈ stripFinset M then rho M u v x.1 x.2 else 0) +
          (∑ x ∈ T, (g1CircleWinding D (combCoordinate M x.1 x.2) : ℂ) * rho M u v x.1 x.2) -
          (∑ x ∈ T, (g1CircleWinding D (combCoordinate M x.1 x.2 + (M 1 0 : ℝ) * length M) : ℂ) * rho M u v x.1 x.2) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        rw [hweights x hx, sub_mul, add_mul]
        by_cases hxs : x ∈ stripFinset M <;> simp only [hxs, if_true, if_false, one_mul, zero_mul]
      _ = combBaseline M u v + combCircleCorrection M u v D := by
        rw [hup, hdown, hbaseSum]
        linear_combination comb_circle_reindexing M hM u v D
  have hcomponents :
      (∑ m : Fin (M 1 0).toNat,
        ∑ x ∈ T.filter (fun x => x.1 = (m : ℤ)), W x * rho M u v x.1 x.2) =
      ∑ x ∈ T, W x * rho M u v x.1 x.2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    have hm := hrange x hx
    have hmnat : x.1.toNat < (M 1 0).toNat := by omega
    let m₀ : Fin (M 1 0).toNat := ⟨x.1.toNat, hmnat⟩
    have hm₀ : (m₀ : ℤ) = x.1 := Int.toNat_of_nonneg hm.1
    calc
      _ = if x.1 = (m₀ : ℤ) then W x * rho M u v x.1 x.2 else 0 := by
        apply Finset.sum_eq_single_of_mem m₀ (Finset.mem_univ _)
        intro m _ hmne
        apply if_neg
        intro hcast
        apply hmne
        apply Fin.ext
        exact_mod_cast hcast.symm.trans hm₀.symm
      _ = _ := if_pos hm₀.symm
  have haccount : Telescoping.rawIntegral M u v D =
      ∑ m : Fin (M 1 0).toNat,
        ∑ x ∈ T.filter (fun x => x.1 = (m : ℤ)), W x * rho M u v x.1 x.2 := by
    unfold Telescoping.rawIntegral
    apply Finset.sum_congr rfl
    intro m _
    let D₀ := componentChain M D (m : ℤ) (M 1 0)
    let D₁ := componentChain M D (m : ℤ) 0
    let Q := T.filter (fun x => x.1 = (m : ℤ))
    let R := fun x : ℤ × ℤ => G2ResidueLedgerAux.realPoint M (m : ℤ) (combCoordinate M x.1 x.2)
    let Bounds : Finset ℝ :=
      ({|D₀.crossing|, |D₁.crossing|} : Finset ℝ) ∪
        D₀.centers.image (fun r => |r| + D₀.radius r) ∪
        D₁.centers.image (fun r => |r| + D₁.radius r) ∪ T.image (fun x => |R x|)
    obtain ⟨b, hb⟩ := Bounds.bddAbove
    let B := b + 1
    have hbnd (r : ℝ) (hr : r ∈ Bounds) : r < B :=
      lt_of_le_of_lt (hb hr) (lt_add_one b)
    have hB₀ : |D₀.crossing| < B := hbnd _ (by simp [Bounds])
    have hB₁ : |D₁.crossing| < B := hbnd _ (by simp [Bounds])
    have hcB₀ (r : ℝ) (hr : r ∈ D₀.centers) : |r| + D₀.radius r < B := by
      apply hbnd
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)))
    have hcB₁ (r : ℝ) (hr : r ∈ D₁.centers) : |r| + D₁.radius r < B := by
      apply hbnd
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr))
    have hBR (x : ℤ × ℤ) (hx : x ∈ T) : |R x| < B :=
      hbnd _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
    let P := (G2ResidueLedgerAux.realCandidates_bounded_finite M hM v m B).toFinset
    have hP : (P : Set ℝ) = G2ResidueLedgerAux.realCandidates M v (m : ℤ) ∩ Icc (-B) B :=
      Set.Finite.coe_toFinset _
    obtain ⟨N, A, g, hg⟩ := G2ResidueLedgerAux.rawF_germ_data M hM u v (m : ℤ)
    let F := fun p : ℝ =>
      ((g1LeftAssignment D₁ p - g1LeftAssignment D₀ p : ℤ) : ℂ) *
        (2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient (N p) (A p))
    have hledger : g1ChainIntegral D₁ (rawF M u v (m : ℤ)) -
        g1ChainIntegral D₀ (rawF M u v (m : ℤ)) = ∑ p ∈ P, F p := by
      have hPC (p : ℝ) (hp : p ∈ P) : p ∈ G2ResidueLedgerAux.realCandidates M v (m : ℤ) := by
        have hp' : p ∈ (P : Set ℝ) := hp
        rw [hP] at hp'
        exact hp'.1
      have hs₀ := G2ResidueLedgerAux.component_boundary_safe' M hM v δ D hD m (M 1 0) (Or.inr rfl)
      have hs₁ := G2ResidueLedgerAux.component_boundary_safe' M hM v δ D hD m 0 (Or.inl rfl)
      have hh := horizontal_closures_vanish M hM u v hwin (m : ℤ) D₀.crossing D₁.crossing
      apply G2ResidueLedgerAux.chain_real_germs (rawF M u v (m : ℤ)) P N A g B D₀ D₁
        (G2ResidueLedgerAux.component_crossing_lt M hM D (m : ℤ)) hB₀ hB₁
        (fun r hr => ⟨G2ResidueLedgerAux.component_radius_pos M hM v δ D hD (m : ℤ) (M 1 0) r hr,
          hcB₀ r hr⟩)
        (fun r hr => ⟨G2ResidueLedgerAux.component_radius_pos M hM v δ D hD (m : ℤ) 0 r hr,
          hcB₁ r hr⟩)
        ⟨fun hp => hs₀.1 (hPC _ hp), fun p hp => hs₀.2 p (hPC p hp)⟩
        ⟨fun hp => hs₁.1 (hPC _ hp), fun p hp => hs₁.2 p (hPC p hp)⟩
        (G2ResidueLedgerAux.rawF_analytic_on_bounded M hM u v (m : ℤ) B P hP)
        (fun p _ => hg p) _ _ hh.1 hh.2.1
      · have hi := (rawF_chain_integrable M hM u v hwin δ D hD (m : ℤ)
          (⟨(M 1 0).toNat, Nat.lt_succ_self _⟩ : Fin ((M 1 0).toNat + 1))).1
        simpa only [D₀, Int.toNat_of_nonneg hM.1.le] using hi
      · exact (rawF_chain_integrable M hM u v hwin δ D hD (m : ℤ)
          (⟨0, Nat.zero_lt_succ _⟩ : Fin ((M 1 0).toNat + 1))).1
    let C := Q.image R
    have hCP : C ⊆ P := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      have hx' := Finset.mem_filter.mp hx
      change R x ∈ (P : Set ℝ)
      rw [hP]
      refine ⟨⟨combCoordinate M x.1 x.2, Or.inr ⟨x.2, ?_⟩, rfl⟩,
        abs_le.mp (hBR x hx'.1).le⟩
      rw [hx'.2]
    have hRinj : ∀ x ∈ Q, ∀ y ∈ Q, R x = R y → x = y := by
      intro x hx y hy hxy
      have hxm := (Finset.mem_filter.mp hx).2
      have hym := (Finset.mem_filter.mp hy).2
      apply Prod.ext (hxm.trans hym.symm)
      have hcoord := G2ResidueLedgerAux.realPoint_injective M hM (m : ℤ) hxy
      rw [hxm, hym] at hcoord
      unfold combCoordinate at hcoord
      have hreal := mul_left_cancel₀ (ne_of_gt (scale_identities M hM).1) hcoord
      have hint : (1 - M 1 1) * (m : ℤ) + M 1 0 * x.2 =
          (1 - M 1 1) * (m : ℤ) + M 1 0 * y.2 := by exact_mod_cast hreal
      exact mul_left_cancel₀ (ne_of_gt hM.1) (add_left_cancel hint)
    have hterm (x : ℤ × ℤ) (hx : x ∈ Q) : F (R x) = W x * rho M u v x.1 x.2 := by
      have hxm := (Finset.mem_filter.mp hx).2
      have hroot : (R x : ℂ) = root M (m : ℤ) x.2 := by
        dsimp [R]
        rw [hxm]
        exact G2ResidueLedgerAux.realPoint_root M hM (m : ℤ) x.2
      have hcoef := G2ResidueLedgerAux.rawF_comb_coefficient_of_real M hM u v (m : ℤ) x.2 (R x)
        hroot (N (R x)) (A (R x)) (g (R x)) (hg (R x)).1 (hg (R x)).2
      dsimp [F, D₀, D₁, R]
      rw [hcoef]
      simp only [G2ResidueLedgerAux.component_assignment M hM, Int.cast_zero, zero_mul, add_zero]
      simp only [W, hxm]
    have hzero (p : ℝ) (hp : p ∈ P) (hnot : p ∉ C) : F p = 0 := by
      have hp' : p ∈ G2ResidueLedgerAux.realCandidates M v (m : ℤ) ∩ Icc (-B) B := by
        rw [← hP]
        exact hp
      obtain ⟨X, hX, rfl⟩ := hp'.1
      rcases hX with (hX | hX) | ⟨k, rfl⟩
      · have hw := original_numerator_net_winding_zero M hM u v hwin δ D hD (m : ℤ) X hX
        dsimp [F, D₀, D₁]
        simp only [G2ResidueLedgerAux.component_assignment M hM, Int.cast_zero, zero_mul, add_zero]
        rw [show g1LeftAssignment D X -
          g1LeftAssignment D (X + (M 1 0 : ℝ) * length M) = 0 from hw]
        simp only [Int.cast_zero, zero_mul]
      · have hw := original_inverse_net_winding_zero M hM v δ D hD (m : ℤ) X hX
        dsimp [F, D₀, D₁]
        simp only [G2ResidueLedgerAux.component_assignment M hM, Int.cast_zero, zero_mul, add_zero]
        rw [show g1LeftAssignment D X -
          g1LeftAssignment D (X + (M 1 0 : ℝ) * length M) = 0 from hw]
        simp only [Int.cast_zero, zero_mul]
      · have hnT : ((m : ℤ), k) ∉ T := by
          intro hx
          exact hnot (Finset.mem_image.mpr ⟨((m : ℤ), k), Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩)
        have hm : 0 ≤ (m : ℤ) := by omega
        have hmc : (m : ℤ) < M 1 0 := by have := m.isLt; omega
        have hw := G2ResidueLedgerAux.comb_assignment_support M hM v δ D hD (m : ℤ) k hm hmc hnT
        dsimp [F, D₀, D₁]
        simp only [G2ResidueLedgerAux.component_assignment M hM, Int.cast_zero, zero_mul, add_zero]
        rw [hw]
        simp only [Int.cast_zero, zero_mul]
    calc
      _ = ∑ p ∈ P, F p := hledger
      _ = ∑ p ∈ C, F p := by symm; exact Finset.sum_subset hCP hzero
      _ = ∑ x ∈ Q, F (R x) := Finset.sum_image hRinj
      _ = _ := Finset.sum_congr rfl hterm
  exact haccount.trans (hcomponents.trans hweighted)

/--
The c exceptional denominators all change A to A⁻¹, while the
numerator c copies remain A; [RW26, p. 13] each component.
-/
theorem corrected_comb_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    combBaseline M u v + combCircleCorrection M u v D =
      (M 1 0 : ℂ) * (scale M : ℂ) *
        groupSum M hM (ratioSummand M hM (specialValueMk M u) (specialValueMk M v)) := by
  let U := specialValueMk M u
  let V := specialValueMk M v
  let C := specialValuePairing M hM (-V) U * SpecialValueBridge.repellingPlus M hM (-V) *
    ((Real.sqrt (epsilon M) : ℂ)⁻¹ - (Real.sqrt (epsilon M) : ℂ))
  have hpoint (x : SpecialValueGroup M) :
      ratioSummand M hM U V x = baselineSummand M hM U V x + if x = -V then C else 0 := by
    by_cases hx : x = -V
    · subst x
      simp only [ratioSummand, baselineSummand, neg_add_cancel,
        (SpecialValueBridge.repellingValues_zero M hM).1,
        (SpecialValueBridge.repellingValues_zero M hM).2, ite_true, C,
        div_eq_mul_inv, inv_inv]
      ring
    · have hxV : x + V ≠ 0 := by simpa only [eq_neg_iff_add_eq_zero] using hx
      rw [ratioSummand, baselineSummand,
        SpecialValueBridge.repellingValues_agree_off_zero M hM (x + V) hxV, if_neg hx, add_zero]
  have hsum : groupSum M hM (ratioSummand M hM U V) =
      groupSum M hM (baselineSummand M hM U V) + C := by
    let : Fintype (SpecialValueGroup M) := specialGroupFintype M hM
    unfold groupSum
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hC : specialValuePairingLift M (-v) u * SpecialValueBridge.repellingPlusLift M (-v) *
      ((Real.sqrt (epsilon M) : ℂ)⁻¹ - (Real.sqrt (epsilon M) : ℂ)) = C := by
    dsimp [C, U, V]
    rw [← map_neg, specialValuePairing_mk, (SpecialValueBridge.repellingValues_mk M hM (-v)).1]
  rw [comb_baseline_sum M hM u v hwin]
  unfold combCircleCorrection
  rw [circle_correction_sum M hM u v hwin hv δ D hD]
  change (M 1 0 : ℂ) * (scale M : ℂ) * groupSum M hM (baselineSummand M hM U V) +
    (M 1 0 : ℂ) * (scale M : ℂ) * specialValuePairingLift M (-v) u *
      SpecialValueBridge.repellingPlusLift M (-v) *
        ((Real.sqrt (epsilon M) : ℂ)⁻¹ - (Real.sqrt (epsilon M) : ℂ)) =
    (M 1 0 : ℂ) * (scale M : ℂ) * groupSum M hM (ratioSummand M hM U V)
  rw [hsum]
  linear_combination (M 1 0 : ℂ) * (scale M : ℂ) * hC

/--
Main output: actual integral equals the group sum.
No G1 hypothesis is needed for the residue side; [RW26, p. 13].
-/
theorem residue_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    Telescoping.rawIntegral M u v D = (M 1 0 : ℂ) * (scale M : ℂ) *
      groupSum M hM (ratioSummand M hM (specialValueMk M u) (specialValueMk M v)) := by
  rw [rawIntegral_comb_account M hM u v hwin hv δ D hD]
  exact corrected_comb_sum M hM u v hwin hv δ D hD

/--
The exact normalization needed: L₂/√ε=√N, with the same
existing quotient functions as SpecialValueBridge.normalizedValueSum; [RW26, p. 13].
-/
theorem normalized_residue_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    Telescoping.rawIntegral M u v D /
        ((M 1 0 : ℂ) * (Real.sqrt (epsilon M) : ℂ)) =
      SpecialValueBridge.normalizedValueSum M hM
        (ratioSummand M hM (specialValueMk M u) (specialValueMk M v)) := by
  rw [residue_value M hM u v hwin hv δ D hD]
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hM.1)
  have hε : (Real.sqrt (epsilon M) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (epsilon_pos M hM)))
  have hnorm : (scale M : ℂ) / (Real.sqrt (epsilon M) : ℂ) =
      (Real.sqrt (specialValueOrder M : ℝ) : ℂ)⁻¹ := by
    have hsq := Real.sq_sqrt (show 0 ≤ (specialValueOrder M : ℝ) by
      exact_mod_cast (specialValueOrder_pos M hM).le)
    have hr : scale M / Real.sqrt (epsilon M) =
        (Real.sqrt (specialValueOrder M : ℝ))⁻¹ := by
      rw [(scale_identities M hM).2, div_right_comm, normalized_length M hM, ← hsq]
      simp [pow_two]
    exact_mod_cast hr
  change (M 1 0 : ℂ) * (scale M : ℂ) * groupSum M hM _ /
    ((M 1 0 : ℂ) * (Real.sqrt (epsilon M) : ℂ)) =
      (Real.sqrt (specialValueOrder M : ℝ) : ℂ)⁻¹ * groupSum M hM _
  rw [← hnorm]
  field_simp

/--
Compare the two derived integral values and drop the representative windows.
This is the nonzero-v interface. The v=0 case, Fourier, and the origin term remain outside this
statement.
Only the named G1 contract is an analytic integral hypothesis. [RW26, p. 3, p. 13, (7)].
-/
theorem finite_ratio_sum_nonzero (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : SpecialValueGroup M) (hv : v ≠ 0) :
    SpecialValueBridge.normalizedValueSum M hM (ratioSummand M hM u v) =
      SpecialValueBridge.repellingPlus M hM (u + v) /
        (SpecialValueBridge.repellingMinus M hM u * SpecialValueBridge.repellingMinus M hM v) := by
  obtain ⟨u₀, rfl⟩ := QuotientAddGroup.mk'_surjective (specialValueLattice M) u
  obtain ⟨v₀, rfl⟩ := QuotientAddGroup.mk'_surjective (specialValueLattice M) v
  change specialValueMk M v₀ ≠ 0 at hv
  let u' := upperRepresentative M u₀
  let v' := deepRepresentative M v₀
  have hu' : specialValueMk M u' = specialValueMk M u₀ := upperRepresentative_class M u₀
  have hv' : specialValueMk M v' = specialValueMk M v₀ := deepRepresentative_class M v₀
  have hwin := representativeWindow_construct M hM u₀ v₀
  have hv'₀ : specialValueMk M v' ≠ 0 := by simpa only [hv'] using hv
  obtain ⟨δ, D, hD⟩ := exists_commonChain M hM u' v' hwin
  have hnorm := normalized_residue_value M hM u' v' hwin hv'₀ δ D hD
  have hvalue := Evaluation.rawIntegral_value hG1 M hM u' v' hwin hv'₀ δ D hD
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hM.1)
  have hε : (Real.sqrt (epsilon M) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (epsilon_pos M hM)))
  rw [hvalue, mul_div_cancel_left₀ _ (mul_ne_zero hc hε)] at hnorm
  rw [(evaluation_lifts_eq_bridge M (u' + v')).1,
    (evaluation_lifts_eq_bridge M u').2, (evaluation_lifts_eq_bridge M v').2] at hnorm
  rw [← (SpecialValueBridge.repellingValues_mk M hM (u' + v')).1,
    ← (SpecialValueBridge.repellingValues_mk M hM u').2,
    ← (SpecialValueBridge.repellingValues_mk M hM v').2,
    map_add, hu', hv'] at hnorm
  exact hnorm.symm

#print originalNetWinding
#print combBaseline
#print baselineLabel
#print ratioSummand
#check @original_inverse_net_winding_zero
#check @denominator_jump_baseline_bijection
#check @residue_value
#check @finite_ratio_sum_nonzero

end SICLean.L4.G2.ResidueLedger
