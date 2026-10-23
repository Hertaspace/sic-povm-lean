import SICLean.L4.G2ComponentJumps
import SICLean.L4.ModularClusterLedgerAux

set_option autoImplicit false

/-!
Analytic infrastructure for the actual G2 residue account. The raw kernel
supplies its own meromorphy, local principal parts and off-divisor regularity.
The generic chain account follows from finite rectangles and finite circle
sums, then from ordinary integrable-line limits and horizontal closure.
The final helpers identify its coefficients and support with the comb data.
G1 contributes concrete chain definitions only, with no G1 theorem invoked.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2ResidueLedgerAux

open G2 G2.CombResidues G2.ComponentJumps G2.StripCounting

def candidates (M : SL(2, ℤ)) (v : ℤ × ℤ) (m : ℤ) : Set ℝ :=
  originalRightComponent M m ∪ originalLeftComponent M v m ∪
    {X | ∃ k : ℤ, X = combCoordinate M m k}

def realPoint (M : SL(2, ℤ)) (m : ℤ) (X : ℝ) : ℝ :=
  (X - epsilon M * (m : ℝ)) / (M 1 0 : ℝ)

def realCandidates (M : SL(2, ℤ)) (v : ℤ × ℤ) (m : ℤ) : Set ℝ :=
  realPoint M m '' candidates M v m

lemma affinePoint_realPoint (M : SL(2, ℤ)) (m : ℤ) (X : ℝ) :
    affinePoint M m 0 (X : ℂ) = (realPoint M m X : ℂ) := by
  simp [affinePoint, realPoint]

lemma realPoint_cancel (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m : ℤ) (X : ℝ) :
    (M 1 0 : ℝ) * realPoint M m X + epsilon M * (m : ℝ) = X := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  unfold realPoint
  field_simp
  ring

lemma realPoint_injective (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m : ℤ) :
    Function.Injective (realPoint M m) := by
  intro X Y h
  have hX := realPoint_cancel M hM m X
  have hY := realPoint_cancel M hM m Y
  rw [h] at hX
  linarith

lemma realPoint_root (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m k : ℤ) :
    (realPoint M m (combCoordinate M m k) : ℂ) = root M m k := by
  rw [← affinePoint_realPoint, ← root_coordinate M hM m k]
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  simp [affinePoint, hc]

lemma combCoordinate_injective (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m : ℤ) :
    Function.Injective (combCoordinate M m) := by
  intro k l hkl
  unfold combCoordinate at hkl
  have hr := mul_left_cancel₀ (ne_of_gt (scale_identities M hM).1) hkl
  have hi : (1 - M 1 1) * m + M 1 0 * k = (1 - M 1 1) * m + M 1 0 * l := by
    exact_mod_cast hr
  exact mul_left_cancel₀ (ne_of_gt hM.1) (add_left_cancel hi)

lemma candidates_guard (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : Fin (M 1 0).toNat) (X : ℝ) (hX : X ∈ candidates M v (m : ℤ)) :
    X ∈ guardSet M v ∧ X + (M 1 0 : ℝ) * length M ∈ guardSet M v := by
  rcases hX with (hX | hX) | hX
  · obtain ⟨K, J, hK, hlabel, hx⟩ := hX
    exact ⟨Or.inl (Or.inl (G2ContourChainAux.right_mem M hM ⟨K, J, hx⟩)),
      Or.inl (Or.inl (Or.inr ⟨X, ⟨K, J, hK, hx⟩, rfl⟩))⟩
  · obtain ⟨K, J, hJ, hlabel, hx⟩ := hX
    exact ⟨Or.inl (Or.inr (G2ContourChainAux.left_mem M hM v ⟨K, J, hx⟩)),
      Or.inl (Or.inr (Or.inr ⟨X, ⟨K, J, hJ, hx⟩, rfl⟩))⟩
  · obtain ⟨k, rfl⟩ := hX
    constructor
    · exact Or.inr ⟨m, k, ⟨0, Nat.zero_lt_succ _⟩, by simp⟩
    · refine Or.inr ⟨m, k, ⟨(M 1 0).toNat, Nat.lt_succ_self _⟩, ?_⟩
      have hcNat : ((M 1 0).toNat : ℝ) = (M 1 0 : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hM.1.le
      change combCoordinate M (m : ℤ) k + (M 1 0 : ℝ) * length M =
        combCoordinate M (m : ℤ) k + ((M 1 0).toNat : ℝ) * length M
      rw [hcNat]

lemma realCandidates_bounded_finite (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : Fin (M 1 0).toNat) (B : ℝ) :
    (realCandidates M v (m : ℤ) ∩ Icc (-B) B).Finite := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  let lo := (M 1 0 : ℝ) * (-B) + epsilon M * ((m : ℤ) : ℝ)
  let hi := (M 1 0 : ℝ) * B + epsilon M * ((m : ℤ) : ℝ)
  have hs : (candidates M v (m : ℤ) ∩ Icc lo hi).Finite :=
    (guardSet_locally_finite M hM v lo hi).subset (fun X hX =>
      ⟨(candidates_guard M hM v m X hX.1).1, hX.2⟩)
  apply (hs.image (realPoint M (m : ℤ))).subset
  rintro p ⟨⟨X, hX, rfl⟩, hp₀, hp₁⟩
  refine ⟨X, ⟨hX, ?_⟩, rfl⟩
  have hcancel := realPoint_cancel M hM (m : ℤ) X
  have hl := mul_le_mul_of_nonneg_left hp₀ hc.le
  have hh := mul_le_mul_of_nonneg_left hp₁ hc.le
  constructor
  · dsimp only [lo]
    rw [← hcancel]
    exact add_le_add hl le_rfl
  · dsimp only [hi]
    rw [← hcancel]
    exact add_le_add hh le_rfl

theorem rawF_meromorphic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (z : ℂ) : MeromorphicAt (rawF M u v m) z := by
  have hτ : (repellingTau M : ℂ) ∈ modularPhiDomain M :=
    real_mem_modularPhiDomain M _ (epsilon_pos M hM)
  have hK : AnalyticAt ℂ (kernelK M u m) z := by
    unfold kernelK e
    fun_prop
  have hcomb : AnalyticAt ℂ (fun w => combV M w - combU M m w) z := by
    unfold combV combU e
    fun_prop
  have hnum := modularPhi_meromorphic M hM.1 m 0 _ hτ z (mem_univ z)
  have hden : MeromorphicAt
      (fun w => modularPhi M (m + v.1) 0 (w + (argument M v : ℂ))
        (repellingTau M : ℂ)) z :=
    (modularPhi_meromorphic M hM.1 (m + v.1) 0 _ hτ
      (z + (argument M v : ℂ)) (mem_univ _)).comp_analyticAt
        (g := fun w => w + (argument M v : ℂ)) (by fun_prop)
  exact (hK.meromorphicAt.div hcomb.meromorphicAt).mul (hnum.div hden)

/-- A meromorphic function has an actual finite Laurent principal part on
some closed disk. Its assigned value at the center is irrelevant. -/
theorem meromorphic_local_principalParts (f : ℂ → ℂ) (a : ℂ)
    (hf : MeromorphicAt f a) :
    ∃ (R : ℝ) (n : ℕ) (A : ℕ → ℂ) (g : ℂ → ℂ), 0 < R ∧
      AnalyticOnNhd ℂ g (Metric.closedBall a R) ∧
      ∀ z ∈ Metric.closedBall a R, z ≠ a →
        f z = FinitePrincipalParts.principalPart a n A z + g z := by
  obtain ⟨n, hn⟩ := hf
  have hreg : AnalyticAt ℂ (fun z => (z - a) ^ n * f z) a := by
    simpa only [smul_eq_mul] using hn
  obtain ⟨A, g, hg, _, hEq⟩ :=
    ModularCluster.LedgerAux.analytic_quotient_principalPart
      (fun z => (z - a) ^ n * f z) a n hreg
  obtain ⟨R, hR, hgR⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hg.eventually_analyticAt
  refine ⟨R, n, A, g, hR, fun z hz => hgR hz, ?_⟩
  intro z _ hza
  simpa only [mul_div_cancel_left₀ (f z) (pow_ne_zero n (sub_ne_zero.mpr hza))] using hEq z hza

theorem original_local_principalParts (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (X : ℝ) :
    ∃ (R : ℝ) (n : ℕ) (A : ℕ → ℂ) (g : ℂ → ℂ), 0 < R ∧
      AnalyticOnNhd ℂ g (Metric.closedBall (affinePoint M m 0 (X : ℂ)) R) ∧
      ∀ z ∈ Metric.closedBall (affinePoint M m 0 (X : ℂ)) R,
        z ≠ affinePoint M m 0 (X : ℂ) →
          rawF M u v m z =
            FinitePrincipalParts.principalPart (affinePoint M m 0 (X : ℂ)) n A z + g z := by
  exact meromorphic_local_principalParts _ _ (rawF_meromorphic M hM u v m _)

lemma pole_original_coordinate (M : SL(2, ℤ)) (m : ℤ) (K J : ℕ)
    (hKJ : (K, J) ∈ modularPhiPoleLabels M m 0) :
    rightPoint M (K + 1) J ∈ originalRightComponent M m ∧
      affinePoint M m 0 (rightPoint M (K + 1) J : ℂ) =
        modularPhiPolePoint M m 0 (repellingTau M : ℂ) K J := by
  constructor
  · refine ⟨K + 1, J, by omega, ?_, rfl⟩
    change Int.ModEq (M 1 0) (M 1 1 * ((K + 1 : ℕ) : ℤ) + (J : ℤ))
      (M 1 1 * m)
    change Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ))
      (M 1 1 * (m - 1) - 0) at hKJ
    convert hKJ.add_right (M 1 1) using 1 <;> push_cast <;> ring
  · simp [affinePoint, rightPoint, modularPhiPolePoint,
      G2PoleSeparationAux.repelling_etaDenom]
    ring

lemma zero_original_coordinate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : ℤ) (K J : ℕ)
    (hKJ : (K, J) ∈ modularPhiZeroLabels M (m + v.1) 0) :
    leftPoint M v K (J + 1) ∈ originalLeftComponent M v m ∧
      affinePoint M m 0 (leftPoint M v K (J + 1) : ℂ) =
        modularPhiZeroPoint M (m + v.1) 0 (repellingTau M : ℂ) K J -
          (argument M v : ℂ) := by
  constructor
  · refine ⟨K, J + 1, by omega, ?_, rfl⟩
    change Int.ModEq (M 1 0) (M 1 1 * (K : ℤ) + ((J + 1 : ℕ) : ℤ))
      (-M 1 1 * (m + v.1))
    change Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ))
      (0 - 1 - M 1 1 * (m + v.1)) at hKJ
    convert hKJ.add_right 1 using 1 <;> push_cast <;> ring
  · have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
    have hoff : (inverseOffset M v : ℂ) =
        (M 1 0 : ℂ) * (argument M v : ℂ) + (epsilon M : ℂ) * (v.1 : ℂ) := by
      exact_mod_cast (coefficient_formulas M hM v v).2.symm
    simp only [affinePoint, leftPoint, modularPhiZeroPoint,
      G2PoleSeparationAux.repelling_etaDenom, Int.cast_add, Complex.ofReal_sub,
      Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_natCast,
      Nat.cast_add, Nat.cast_one, Int.cast_zero, zero_mul, sub_zero,
      Complex.ofReal_add, Complex.ofReal_one]
    rw [hoff]
    field_simp
    ring

theorem rawF_analytic_off_poles (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (z : ℂ)
    (hz : z ∉ (fun X : ℝ => affinePoint M m 0 (X : ℂ)) ''
      (originalRightComponent M m ∪ originalLeftComponent M v m ∪
        {X | ∃ k : ℤ, X = combCoordinate M m k})) :
    AnalyticAt ℂ (rawF M u v m) z := by
  have hτ : (repellingTau M : ℂ) ∈ modularPhiDomain M :=
    real_mem_modularPhiDomain M _ (epsilon_pos M hM)
  have hp : modularPhiPoleIndices M m 0 z (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨hKJ, hpoint⟩
    obtain ⟨hcoord, heq⟩ := pole_original_coordinate M m K J hKJ
    exact hz ⟨rightPoint M (K + 1) J, Or.inl (Or.inl hcoord), heq.trans hpoint.symm⟩
  have hq : modularPhiZeroIndices M (m + v.1) 0
      (z + (argument M v : ℂ)) (repellingTau M : ℂ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨K, J⟩ ⟨hKJ, hpoint⟩
    obtain ⟨hcoord, heq⟩ := zero_original_coordinate M hM v m K J hKJ
    have heqz : affinePoint M m 0 (leftPoint M v K (J + 1) : ℂ) = z := by
      rw [heq, ← hpoint]
      ring
    exact hz ⟨leftPoint M v K (J + 1), Or.inl (Or.inr hcoord), heqz⟩
  have hnum : AnalyticAt ℂ (fun w => modularPhi M m 0 w (repellingTau M : ℂ)) z :=
    (modularPhi_joint_analytic_no_poles M hM.1 m 0 (z, (repellingTau M : ℂ))
      ⟨hτ, by simp [modularPhiPoleMultiplicity, hp]⟩).comp
        (f := fun w : ℂ => (w, (repellingTau M : ℂ))) (by fun_prop)
  have hden : AnalyticAt ℂ
      (fun w => (modularPhi M (m + v.1) 0 (w + (argument M v : ℂ))
        (repellingTau M : ℂ))⁻¹) z :=
    (ModularCluster.inversePhi_joint_analytic M hM.1 (m + v.1) 0
      (z + (argument M v : ℂ), (repellingTau M : ℂ))
      ⟨hτ, by simp [modularPhiZeroMultiplicity, hq]⟩).comp
        (f := fun w : ℂ => (w + (argument M v : ℂ), (repellingTau M : ℂ)))
          (by fun_prop)
  have hcomb : combV M z - combU M m z ≠ 0 := by
    intro hh
    obtain ⟨k, hk, _⟩ := (comb_zeros M hM m z).mp hh
    have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
    have heq : affinePoint M m 0 (combCoordinate M m k : ℂ) = root M m k := by
      rw [← root_coordinate M hM m k]
      simp [affinePoint, hc]
    exact hz ⟨combCoordinate M m k, Or.inr ⟨k, rfl⟩, heq.trans hk.symm⟩
  have hK : AnalyticAt ℂ (kernelK M u m) z := by
    unfold kernelK e
    fun_prop
  have hC : AnalyticAt ℂ (fun w => combV M w - combU M m w) z := by
    unfold combV combU e
    fun_prop
  change AnalyticAt ℂ (fun w => kernelK M u m w / (combV M w - combU M m w) *
    (modularPhi M m 0 w (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 0 (w + (argument M v : ℂ)) (repellingTau M : ℂ))) z
  exact (hK.div hC hcomb).fun_mul (hnum.fun_mul hden)

theorem rawF_analytic_off_realCandidates (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (z : ℂ)
    (hz : z ∉ (fun p : ℝ => (p : ℂ)) '' realCandidates M v m) :
    AnalyticAt ℂ (rawF M u v m) z := by
  apply rawF_analytic_off_poles M hM u v m z
  rintro ⟨X, hX, heq⟩
  exact hz ⟨realPoint M m X, ⟨X, hX, rfl⟩, (affinePoint_realPoint M m X).symm.trans heq⟩

theorem rawF_analytic_on_bounded (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (B : ℝ) (P : Finset ℝ)
    (hP : (P : Set ℝ) = realCandidates M v m ∩ Icc (-B) B)
    (z : ℂ) (hzB : |z.re| ≤ B)
    (hz : z ∉ (fun p : ℝ => (p : ℂ)) '' (P : Set ℝ)) :
    AnalyticAt ℂ (rawF M u v m) z := by
  apply rawF_analytic_off_realCandidates M hM u v m z
  rintro ⟨p, hp, hpz⟩
  apply hz
  refine ⟨p, ?_, hpz⟩
  rw [hP]
  refine ⟨hp, ?_⟩
  have hpb : |p| ≤ B := by simpa [← hpz] using hzB
  exact abs_le.mp hpb

lemma component_assignment (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j : ℤ) (X : ℝ) :
    g1LeftAssignment (componentChain M D m j) (realPoint M m X) =
      g1LeftAssignment D (X + (j : ℝ) * length M) := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  change g1LeftAssignment
    (G2ContourChainAux.affineChain D (M 1 0 : ℝ) (epsilon M * (m : ℝ))
      ((j : ℝ) * length M)) (realPoint M m X) = _
  rw [G2ContourChainAux.affine_assignment _ _ _ _ _ hc, realPoint_cancel M hM]

lemma component_radius_pos (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m j : ℤ) :
    ∀ r ∈ (componentChain M D m j).centers, 0 < (componentChain M D m j).radius r := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  change 0 < (G2ContourChainAux.affineChain D (M 1 0 : ℝ) (epsilon M * (m : ℝ))
      ((j : ℝ) * length M)).radius _
  rw [G2ContourChainAux.affine_radius _ _ _ _ _ (ne_of_gt hc)]
  exact div_pos (hD.2.2.2.2.2.2 s hs).1 hc

lemma component_crossing_lt (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m : ℤ) :
    (componentChain M D m (M 1 0)).crossing < (componentChain M D m 0).crossing := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  simp only [componentChain, Int.cast_zero, zero_mul, sub_zero]
  apply (div_lt_div_iff_of_pos_right hc).mpr
  have := mul_pos hc (length_pos M hM)
  linarith

lemma component_boundary_safe (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : Fin (M 1 0).toNat) (j : ℤ) (hj : j = 0 ∨ j = M 1 0) :
    ∀ p ∈ realCandidates M v (m : ℤ),
      p ≠ (componentChain M D (m : ℤ) j).crossing ∧
        ∀ r ∈ (componentChain M D (m : ℤ) j).centers,
          |p - r| ≠ (componentChain M D (m : ℤ) j).radius r := by
  rintro p ⟨X, hX, rfl⟩
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have hguard : X + (j : ℝ) * length M ∈ guardSet M v := by
    rcases hj with rfl | rfl
    · simpa using (candidates_guard M hM v m X hX).1
    · exact (candidates_guard M hM v m X hX).2
  have hboundary := commonChain_boundary_avoids M hM v δ D hD
  constructor
  · intro heq
    have hcancel := G2ContourChainAux.affine_cancel
      (M 1 0 : ℝ) (epsilon M * ((m : ℤ) : ℝ)) ((j : ℝ) * length M) D.crossing (ne_of_gt hc)
    have hcoord : X + (j : ℝ) * length M = D.crossing := by
      rw [← realPoint_cancel M hM (m : ℤ) X, heq]
      exact hcancel
    exact hboundary.1 (hcoord ▸ hguard)
  · intro r hr heq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    change |realPoint M (m : ℤ) X -
        (s - epsilon M * ((m : ℤ) : ℝ) - (j : ℝ) * length M) / (M 1 0 : ℝ)| =
      (G2ContourChainAux.affineChain D (M 1 0 : ℝ) (epsilon M * ((m : ℤ) : ℝ))
        ((j : ℝ) * length M)).radius _ at heq
    rw [G2ContourChainAux.affine_radius _ _ _ _ _ (ne_of_gt hc),
      G2ContourChainAux.affine_distance _ _ _ _ _ hc,
      realPoint_cancel M hM, div_left_inj' (ne_of_gt hc)] at heq
    exact hboundary.2 s hs _ hguard heq

lemma component_boundary_safe' (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m : Fin (M 1 0).toNat) (j : ℤ) (hj : j = 0 ∨ j = M 1 0) :
    (componentChain M D (m : ℤ) j).crossing ∉ realCandidates M v (m : ℤ) ∧
      ∀ p ∈ realCandidates M v (m : ℤ),
        ∀ r ∈ (componentChain M D (m : ℤ) j).centers,
          |p - r| ≠ (componentChain M D (m : ℤ) j).radius r := by
  have hs := component_boundary_safe M hM v δ D hD m j hj
  exact ⟨fun hp => (hs _ hp).1 rfl, fun p hp => (hs p hp).2⟩

theorem rectangle_prescribed_germs (f : ℂ → ℂ) (P : Finset ℂ)
    (lo hi : ℂ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ)
    (hre : lo.re < hi.re) (him : lo.im < hi.im)
    (hinside : ∀ p ∈ P, p ∈ FinitePrincipalParts.openRectangle lo hi)
    (hf : AnalyticOnNhd ℂ f (FinitePrincipalParts.closedRectangle lo hi \ (P : Set ℂ)))
    (hg : ∀ p ∈ P, AnalyticAt ℂ (g p) p ∧
      f =ᶠ[𝓝[≠] p] fun z => FinitePrincipalParts.principalPart p (N p) (A p) z + g p z) :
    FinitePrincipalParts.rectangleCCW lo hi f =
      2 * (Real.pi : ℂ) * I *
        ∑ p ∈ P, FinitePrincipalParts.residueCoefficient (N p) (A p) := by
  have hopen : IsOpen (FinitePrincipalParts.openRectangle lo hi) := by
    unfold FinitePrincipalParts.openRectangle
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hsmall (p : ℂ) (hp : p ∈ P) :
      ∃ r : ℝ, 0 < r ∧
        Metric.closedBall p r ⊆ FinitePrincipalParts.openRectangle lo hi ∧
        (∀ q ∈ P, q ≠ p → 3 * r < dist q p) ∧
        AnalyticOnNhd ℂ (g p) (Metric.closedBall p r) ∧
        ∀ z ∈ Metric.closedBall p r, z ≠ p →
          f z = FinitePrincipalParts.principalPart p (N p) (A p) z + g p z := by
    have hU : FinitePrincipalParts.openRectangle lo hi \ ((P.erase p : Finset ℂ) : Set ℂ)
        ∈ 𝓝 p :=
      inter_mem (hopen.mem_nhds (hinside p hp))
        ((P.erase p).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp))
    have hEq := eventually_nhdsWithin_iff.mp (hg p hp).2
    obtain ⟨s, hs, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (inter_mem hU (inter_mem (hg p hp).1.eventually_analyticAt hEq))
    refine ⟨s / 4, by positivity, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact (hsub (Metric.closedBall_subset_closedBall (by linarith) hz)).1.1
    · intro q hq hqp
      have hdist : s < dist q p := by
        by_contra hh
        have hqm := hsub (Metric.mem_closedBall.mpr (le_of_not_gt hh))
        exact hqm.1.2 (Finset.mem_erase.mpr ⟨hqp, hq⟩)
      linarith
    · intro z hz
      exact (hsub (Metric.closedBall_subset_closedBall (by linarith) hz)).2.1
    · intro z hz hzp
      exact (hsub (Metric.closedBall_subset_closedBall (by linarith) hz)).2.2 hzp
  choose r hr hrect hsep hana heq using hsmall
  let radius : ℂ → ℝ := fun p => if hp : p ∈ P then r p hp else 1
  have hrad (p : ℂ) (hp : p ∈ P) : radius p = r p hp := dif_pos hp
  have hdisj (p : ℂ) (hp : p ∈ P) (q : ℂ) (hq : q ∈ P) (hpq : p ≠ q) :
      Disjoint (Metric.closedBall p (radius p)) (Metric.closedBall q (radius q)) := by
    apply Metric.closedBall_disjoint_closedBall
    rw [hrad p hp, hrad q hq]
    have h₁ := hsep p hp q hq hpq.symm
    have h₂ := hsep q hq p hp hpq
    rw [dist_comm q p] at h₁
    have := hr p hp
    have := hr q hq
    linarith
  have hledger := FinitePrincipalParts.rectangle_finite_principal_parts P f lo hi id radius N A g
    hre him (fun p hp => by simpa [hrad p hp] using hr p hp)
    (fun p hp => by simpa [hrad p hp] using hrect p hp)
    hdisj (by simpa only [Set.image_id] using hf)
    (fun p hp => by simpa [hrad p hp] using hana p hp)
    (fun p hp => by simpa [hrad p hp] using heq p hp)
  exact hledger.2.2

lemma rectangle_real_germs (f : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (g : ℝ → ℂ → ℂ)
    (B x₀ x₁ R : ℝ) (hx : x₀ < x₁) (hR : 0 < R)
    (hB₀ : |x₀| < B) (hB₁ : |x₁| < B)
    (hs₀ : x₀ ∉ P) (hs₁ : x₁ ∉ P)
    (hf : ∀ z : ℂ, |z.re| ≤ B → z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      AnalyticAt ℂ f z)
    (hg : ∀ p ∈ P, AnalyticAt ℂ (g p) (p : ℂ) ∧
      f =ᶠ[𝓝[≠] (p : ℂ)] fun z =>
        FinitePrincipalParts.principalPart (p : ℂ) (N p) (A p) z + g p z) :
    FinitePrincipalParts.rectangleCCW (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) f =
      ∑ p ∈ P, if x₀ < p ∧ p < x₁ then
        2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient (N p) (A p) else 0 := by
  let Q : Finset ℝ := P.filter (fun p => x₀ < p ∧ p < x₁)
  let Qz : Finset ℂ := Q.image (fun p : ℝ => (p : ℂ))
  have hinside : ∀ p ∈ Qz, p ∈
      FinitePrincipalParts.openRectangle (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hq' := (Finset.mem_filter.mp hq).2
    simpa [FinitePrincipalParts.openRectangle, g1VerticalPoint] using
      (show x₀ < q ∧ q < x₁ ∧ 0 < R from ⟨hq'.1, hq'.2, hR⟩)
  have hana : AnalyticOnNhd ℂ f
      (FinitePrincipalParts.closedRectangle (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) \
        (Qz : Set ℂ)) := by
    intro z hz
    have hzx : x₀ ≤ z.re ∧ z.re ≤ x₁ := by
      simpa [FinitePrincipalParts.closedRectangle, g1VerticalPoint] using
        And.intro hz.1.1 hz.1.2.1
    apply hf z (abs_le.mpr ⟨by linarith [(abs_lt.mp hB₀).1], by linarith [(abs_lt.mp hB₁).2]⟩)
    rintro ⟨p, hp, hpz⟩
    have hzp : z.re = p := by rw [← hpz]; simp
    have hp₀ : x₀ < p := lt_of_le_of_ne (hzp ▸ hzx.1) (by intro he; exact hs₀ (he ▸ hp))
    have hp₁ : p < x₁ := lt_of_le_of_ne (hzp ▸ hzx.2) (by intro he; exact hs₁ (he ▸ hp))
    exact hz.2 (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hp₀, hp₁⟩, hpz⟩)
  have hgg : ∀ p ∈ Qz, AnalyticAt ℂ (g p.re) p ∧
      f =ᶠ[𝓝[≠] p] fun z =>
        FinitePrincipalParts.principalPart p (N p.re) (A p.re) z + g p.re z := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    simpa using hg q (Finset.mem_filter.mp hq).1
  have hledger := rectangle_prescribed_germs f Qz
    (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R)
    (fun p => N p.re) (fun p => A p.re) (fun p => g p.re)
    (by simpa [g1VerticalPoint] using hx) (by simpa [g1VerticalPoint] using (show -R < R by linarith))
    hinside hana hgg
  rw [hledger]
  dsimp only [Qz]
  rw [Finset.sum_image (by intro p hp q hq he; exact Complex.ofReal_injective he)]
  simp only [Complex.ofReal_re, Finset.mul_sum]
  simp only [Q, Finset.sum_filter]

lemma circle_real_germs (f : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (g : ℝ → ℂ → ℂ)
    (B r ρ : ℝ) (hρ : 0 < ρ) (hB : |r| + ρ < B)
    (hs : ∀ p ∈ P, |p - r| ≠ ρ)
    (hf : ∀ z : ℂ, |z.re| ≤ B → z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      AnalyticAt ℂ f z)
    (hg : ∀ p ∈ P, AnalyticAt ℂ (g p) (p : ℂ) ∧
      f =ᶠ[𝓝[≠] (p : ℂ)] fun z =>
        FinitePrincipalParts.principalPart (p : ℂ) (N p) (A p) z + g p z) :
    FinitePrincipalParts.circleCCW (r : ℂ) ρ f =
      ∑ p ∈ P, if |p - r| < ρ then
        2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient (N p) (A p) else 0 := by
  let Q : Finset ℝ := P.filter (fun p => |p - r| < ρ)
  let Qz : Finset ℂ := Q.image (fun p : ℝ => (p : ℂ))
  have hdist (p : ℝ) : dist (p : ℂ) (r : ℂ) = |p - r| := by
    simpa only [Real.dist_eq] using Complex.isometry_ofReal.dist_eq p r
  have hinside : ∀ p ∈ Qz, dist p (r : ℂ) < ρ := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [hdist]
    exact (Finset.mem_filter.mp hq).2
  have hana : AnalyticOnNhd ℂ f (Metric.closedBall (r : ℂ) ρ \ (Qz : Set ℂ)) := by
    intro z hz
    have hbd : |z.re| ≤ B := by
      have hzre : |z.re - r| ≤ dist z (r : ℂ) := by
        simpa [dist_eq_norm] using Complex.abs_re_le_norm (z - (r : ℂ))
      have hadd : |z.re| ≤ |z.re - r| + |r| := by
        simpa only [sub_add_cancel] using abs_add_le (z.re - r) r
      linarith [Metric.mem_closedBall.mp hz.1]
    apply hf z hbd
    rintro ⟨p, hp, hpz⟩
    have hpρ : |p - r| < ρ := lt_of_le_of_ne
      (by simpa only [← hpz, Metric.mem_closedBall, hdist] using hz.1) (hs p hp)
    exact hz.2 (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpρ⟩, hpz⟩)
  have hgg : ∀ p ∈ Qz, AnalyticAt ℂ (g p.re) p ∧
      f =ᶠ[𝓝[≠] p] fun z =>
        FinitePrincipalParts.principalPart p (N p.re) (A p.re) z + g p.re z := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    simpa using hg q (Finset.mem_filter.mp hq).1
  have hledger := ModularCluster.LedgerAux.circle_finite_prescribed_germs f (r : ℂ) ρ Qz
    (fun p => N p.re) (fun p => A p.re) (fun p => g p.re)
    hρ hinside hana hgg
  rw [hledger]
  dsimp only [Qz]
  rw [Finset.sum_image (by intro p hp q hq he; exact Complex.ofReal_injective he)]
  simp only [Complex.ofReal_re, Finset.mul_sum]
  simp only [Q, Finset.sum_filter]

lemma circle_family_real_germs (f : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (g : ℝ → ℂ → ℂ)
    (B : ℝ) (D : G1VerticalChain)
    (hB : ∀ r ∈ D.centers, 0 < D.radius r ∧ |r| + D.radius r < B)
    (hs : ∀ p ∈ P, ∀ r ∈ D.centers, |p - r| ≠ D.radius r)
    (hf : ∀ z : ℂ, |z.re| ≤ B → z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      AnalyticAt ℂ f z)
    (hg : ∀ p ∈ P, AnalyticAt ℂ (g p) (p : ℂ) ∧
      f =ᶠ[𝓝[≠] (p : ℂ)] fun z =>
        FinitePrincipalParts.principalPart (p : ℂ) (N p) (A p) z + g p z) :
    (∑ r ∈ D.centers, FinitePrincipalParts.circleCCW (r : ℂ) (D.radius r) f) =
      ∑ p ∈ P, (g1CircleWinding D p : ℂ) *
        (2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient (N p) (A p)) := by
  calc
    _ = ∑ r ∈ D.centers, ∑ p ∈ P, if |p - r| < D.radius r then
        2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient (N p) (A p) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact circle_real_germs f P N A g B r (D.radius r) (hB r hr).1 (hB r hr).2
        (fun p hp => hs p hp r hr) hf hg
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [g1CircleWinding, Int.cast_sum, Int.cast_ite, Int.cast_one,
        Int.cast_zero, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs <;> simp

lemma vertical_real_germs (f : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (g : ℝ → ℂ → ℂ)
    (B x₀ x₁ : ℝ) (hx : x₀ < x₁)
    (hB₀ : |x₀| < B) (hB₁ : |x₁| < B)
    (hs₀ : x₀ ∉ P) (hs₁ : x₁ ∉ P)
    (hf : ∀ z : ℂ, |z.re| ≤ B → z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      AnalyticAt ℂ f z)
    (hg : ∀ p ∈ P, AnalyticAt ℂ (g p) (p : ℂ) ∧
      f =ᶠ[𝓝[≠] (p : ℂ)] fun z =>
        FinitePrincipalParts.principalPart (p : ℂ) (N p) (A p) z + g p z)
    (hi₀ : Integrable (g1VerticalPullback f x₀))
    (hi₁ : Integrable (g1VerticalPullback f x₁))
    (hhUpper : Tendsto (fun T => horizontalIntegral f x₀ x₁ T) atTop (𝓝 0))
    (hhLower : Tendsto (fun T => horizontalIntegral f x₀ x₁ (-T)) atTop (𝓝 0)) :
    (∫ t : ℝ, g1VerticalPullback f x₁ t) - (∫ t : ℝ, g1VerticalPullback f x₀ t) =
      ∑ p ∈ P, if x₀ < p ∧ p < x₁ then
        2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient (N p) (A p) else 0 := by
  let F : ℝ → ℂ := fun R =>
    (∫ t : ℝ in -R..R, g1VerticalPullback f x₁ t) -
      (∫ t : ℝ in -R..R, g1VerticalPullback f x₀ t) +
        (horizontalIntegral f x₀ x₁ (-R) - horizontalIntegral f x₀ x₁ R)
  have hlim : Tendsto F atTop (𝓝
      ((∫ t : ℝ, g1VerticalPullback f x₁ t) - (∫ t : ℝ, g1VerticalPullback f x₀ t))) := by
    convert ((intervalIntegral_tendsto_integral hi₁ tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hi₀ tendsto_neg_atTop_atBot tendsto_id)).add
        (hhLower.sub hhUpper) using 1 <;> simp [F]
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have heq := rectangle_real_germs f P N A g B x₀ x₁ R hx hR hB₀ hB₁ hs₀ hs₁ hf hg
  rw [upward_rectangle_orientation] at heq
  simpa only [F, sub_eq_add_neg, add_assoc] using heq.symm

/-- Finite candidate ledger for two upward lines with finite CCW circles.
All analytic and convergence premises concern the actual function. -/
theorem chain_real_germs (f : ℂ → ℂ) (P : Finset ℝ)
    (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (g : ℝ → ℂ → ℂ)
    (B : ℝ) (D₀ D₁ : G1VerticalChain) (hx : D₀.crossing < D₁.crossing)
    (hB₀ : |D₀.crossing| < B) (hB₁ : |D₁.crossing| < B)
    (hc₀ : ∀ r ∈ D₀.centers, 0 < D₀.radius r ∧ |r| + D₀.radius r < B)
    (hc₁ : ∀ r ∈ D₁.centers, 0 < D₁.radius r ∧ |r| + D₁.radius r < B)
    (hs₀ : D₀.crossing ∉ P ∧ ∀ p ∈ P, ∀ r ∈ D₀.centers, |p - r| ≠ D₀.radius r)
    (hs₁ : D₁.crossing ∉ P ∧ ∀ p ∈ P, ∀ r ∈ D₁.centers, |p - r| ≠ D₁.radius r)
    (hf : ∀ z : ℂ, |z.re| ≤ B → z ∉ (fun x : ℝ => (x : ℂ)) '' (P : Set ℝ) →
      AnalyticAt ℂ f z)
    (hg : ∀ p ∈ P, AnalyticAt ℂ (g p) (p : ℂ) ∧
      f =ᶠ[𝓝[≠] (p : ℂ)] fun z =>
        FinitePrincipalParts.principalPart (p : ℂ) (N p) (A p) z + g p z)
    (hi₀ : Integrable (g1VerticalPullback f D₀.crossing))
    (hi₁ : Integrable (g1VerticalPullback f D₁.crossing))
    (hhUpper : Tendsto (fun T => horizontalIntegral f D₀.crossing D₁.crossing T) atTop (𝓝 0))
    (hhLower : Tendsto (fun T => horizontalIntegral f D₀.crossing D₁.crossing (-T)) atTop (𝓝 0)) :
    g1ChainIntegral D₁ f - g1ChainIntegral D₀ f =
      ∑ p ∈ P, ((g1LeftAssignment D₁ p - g1LeftAssignment D₀ p : ℤ) : ℂ) *
        (2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient (N p) (A p)) := by
  have hv := vertical_real_germs f P N A g B D₀.crossing D₁.crossing hx hB₀ hB₁
    hs₀.1 hs₁.1 hf hg hi₀ hi₁ hhUpper hhLower
  have h₀ := circle_family_real_germs f P N A g B D₀ hc₀ hs₀.2 hf hg
  have h₁ := circle_family_real_germs f P N A g B D₁ hc₁ hs₁.2 hf hg
  have hchain : g1ChainIntegral D₁ f - g1ChainIntegral D₀ f =
      ((∫ t : ℝ, g1VerticalPullback f D₁.crossing t) -
        (∫ t : ℝ, g1VerticalPullback f D₀.crossing t)) +
          (∑ r ∈ D₁.centers, FinitePrincipalParts.circleCCW (r : ℂ) (D₁.radius r) f) -
          (∑ r ∈ D₀.centers, FinitePrincipalParts.circleCCW (r : ℂ) (D₀.radius r) f) := by
    unfold g1ChainIntegral g1CirclePullback FinitePrincipalParts.circleCCW
    ring
  rw [hchain, hv, h₀, h₁, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp₀ : p ≠ D₀.crossing := by intro he; exact hs₀.1 (he ▸ hp)
  have hp₁ : p ≠ D₁.crossing := by intro he; exact hs₁.1 (he ▸ hp)
  simp only [g1LeftAssignment, Int.cast_sub, Int.cast_add, Int.cast_ite,
    Int.cast_one, Int.cast_zero]
  by_cases h₀ : p < D₀.crossing
  · have h₁ : p < D₁.crossing := h₀.trans hx
    have hh : ¬ D₀.crossing < p := by linarith
    simp only [h₀, h₁, hh, if_true, if_false, and_true]
    ring
  · by_cases h₁ : p < D₁.crossing
    · have hh : D₀.crossing < p ∧ p < D₁.crossing :=
        ⟨lt_of_le_of_ne (le_of_not_gt h₀) hp₀.symm, h₁⟩
      simp only [h₀, h₁, hh.1, if_true, if_false, true_and]
      ring
    · simp only [h₀, h₁, if_false, and_false]
      ring

theorem rawF_germ_data (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) :
    ∃ (N : ℝ → ℕ) (A : ℝ → ℕ → ℂ) (g : ℝ → ℂ → ℂ),
      ∀ p : ℝ, AnalyticAt ℂ (g p) (p : ℂ) ∧
        rawF M u v m =ᶠ[𝓝[≠] (p : ℂ)] fun z =>
          FinitePrincipalParts.principalPart (p : ℂ) (N p) (A p) z + g p z := by
  choose R N A g hR hana heq using fun p : ℝ =>
    meromorphic_local_principalParts (rawF M u v m) (p : ℂ)
      (rawF_meromorphic M hM u v m (p : ℂ))
  refine ⟨N, A, g, fun p => ⟨hana p _ (Metric.mem_closedBall_self (hR p).le), ?_⟩⟩
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [Metric.closedBall_mem_nhds (p : ℂ) (hR p)] with z hz hzp
  exact heq p z hz hzp

/-- Any Laurent principal part of the actual kernel has the already
computed comb residue. The total value at the center is never used. -/
theorem rawF_comb_coefficient (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ) (N : ℕ) (A : ℕ → ℂ) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g (root M m k))
    (heq : rawF M u v m =ᶠ[𝓝[≠] (root M m k)] fun z =>
      FinitePrincipalParts.principalPart (root M m k) N A z + g z) :
    2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient N A = rho M u v m k := by
  have hEq := eventually_nhdsWithin_iff.mp heq
  obtain ⟨s, hs, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hg.eventually_analyticAt hEq)
  obtain ⟨R, hR, hcircle⟩ := local_circle_value M hM u v m k
  let r : ℝ := min s R / 2
  have hr : 0 < r := half_pos (lt_min hs hR)
  have hrs : r ≤ s := by dsimp [r]; linarith [min_le_left s R]
  have hrR : r < R := by dsimp [r]; linarith [min_le_right s R]
  have hlocal := FinitePrincipalParts.circleCCW_of_local_principalPart
    (rawF M u v m) g (root M m k) r N A hr
    (fun z hz => (hsub (Metric.closedBall_subset_closedBall hrs hz)).1)
    (fun z hz hzp => (hsub (Metric.closedBall_subset_closedBall hrs hz)).2 hzp)
  exact hlocal.symm.trans (hcircle r hr hrR)

theorem rawF_comb_coefficient_of_real (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ) (p : ℝ) (hp : (p : ℂ) = root M m k)
    (N : ℕ) (A : ℕ → ℂ) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g (p : ℂ))
    (heq : rawF M u v m =ᶠ[𝓝[≠] (p : ℂ)] fun z =>
      FinitePrincipalParts.principalPart (p : ℂ) N A z + g z) :
    2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient N A = rho M u v m k := by
  apply rawF_comb_coefficient M hM u v m k N A g
  · simpa only [hp] using hg
  · simpa only [hp] using heq

theorem comb_assignment_support (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (m k : ℤ) (hm : 0 ≤ m) (hmc : m < M 1 0)
    (hnot : (m, k) ∉ stripFinset M ∪ circleLabels M D ∪
      (circleLabels M D).image (fun x => (x.1, x.2 - specialValueOrder M))) :
    g1LeftAssignment D (combCoordinate M m k) -
      g1LeftAssignment D (combCoordinate M m k + (M 1 0 : ℝ) * length M) = 0 := by
  have hnstrip : (m, k) ∉ stripFinset M := fun h =>
    hnot (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hncircle : (m, k) ∉ circleLabels M D := fun h =>
    hnot (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hnlow : (m, k) ∉ (circleLabels M D).image (fun x => (x.1, x.2 - specialValueOrder M)) := fun h =>
    hnot (Finset.mem_union_right _ h)
  have hw₀ : g1CircleWinding D (combCoordinate M m k) = 0 := by
    by_contra hw
    exact hncircle ((circleLabels_spec M hM v δ D hD m k).mpr ⟨hm, hmc, hw⟩)
  have hshift : combCoordinate M m (k + specialValueOrder M) =
      combCoordinate M m k + (M 1 0 : ℝ) * length M := by
    have h := (root_shift M hM m (k + specialValueOrder M)).2
    simp only [add_sub_cancel_right] at h
    linarith
  have hw₁ : g1CircleWinding D (combCoordinate M m k + (M 1 0 : ℝ) * length M) = 0 := by
    by_contra hw
    apply hnlow
    apply Finset.mem_image.mpr
    refine ⟨(m, k + specialValueOrder M), ?_, by simp⟩
    apply (circleLabels_spec M hM v δ D hD m (k + specialValueOrder M)).mpr
    exact ⟨hm, hmc, by simpa only [hshift] using hw⟩
  have hmnat : m.toNat < (M 1 0).toNat := by omega
  have hterminal : combCoordinate M m k + (M 1 0 : ℝ) * length M ≠ -δ := by
    intro heq
    apply (commonChain_boundary_avoids M hM v δ D hD).1
    right
    refine ⟨⟨m.toNat, hmnat⟩, k, ⟨(M 1 0).toNat, by omega⟩, ?_⟩
    have hcReal : ((M 1 0).toNat : ℝ) = (M 1 0 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hM.1.le
    simpa only [Int.toNat_of_nonneg hm, hcReal, hD.2.2.2.1] using heq.symm
  have hwidth : 0 < (M 1 0 : ℝ) * length M :=
    mul_pos (by exact_mod_cast hM.1) (length_pos M hM)
  simp only [g1LeftAssignment, hD.2.2.2.1, hw₀, hw₁, add_zero]
  by_cases hright : combCoordinate M m k < -δ
  · have hleft : combCoordinate M m k + (M 1 0 : ℝ) * length M < -δ := by
      by_contra hnleft
      apply hnstrip
      apply (mem_stripFinset_iff M hM δ hD.1 hD.2.1 (m, k)).mpr
      refine ⟨hm, hmc, ?_, hright⟩
      have := lt_of_le_of_ne (le_of_not_gt hnleft) hterminal.symm
      linarith
    simp only [if_pos hright, if_pos hleft, sub_self]
  · have hleft : ¬combCoordinate M m k + (M 1 0 : ℝ) * length M < -δ := by
      linarith
    simp only [if_neg hright, if_neg hleft, sub_self]


end SICLean.L4.G2ResidueLedgerAux
