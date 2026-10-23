import SICLean.L4.DistributionLattice
import SICLean.L4.ModularCocycle

set_option autoImplicit false

/-!
# Auxiliary proofs for the actual distribution values

The coordinate and basis lemmas are elementary bridges. Regularity and the pointwise
shift/cancellation identities are supplied by the upstream Φ modules.

`rebaseData` spells out the raw change of basis without importing the downstream value definitions.
Its fields contain no analytic properties.
-/

noncomputable section

open Set
open scoped MatrixGroups Classical

namespace SICLean.L4.DistributionBasisValuesAux

theorem coefficients_unique (B : DistributionBasis) (hB : B.Valid)
    (u v : Fin 2 → ℝ)
    (h : u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B =
      v 0 • distributionBetaOne B + v 1 • distributionBetaTwo B) : u = v := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [distributionBetaOne, distributionBetaTwo, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h₁ h₂
  have hs := hB.2.2.2.2.1
  have hs' := hB.2.2.2.2.2
  have ht := (distributionBasis_spectral B hB).2.1
  have hf : (u 0 - v 0) * (B.tau - distributionConjugateTau B) = 0 := by
    have h₁' : (u 0 - v 0) * B.tau + (u 1 - v 1) = 0 := by
      nlinarith [mul_pos hs hs]
    have h₂' : (u 0 - v 0) * distributionConjugateTau B + (u 1 - v 1) = 0 := by
      nlinarith [mul_pos hs' hs']
    nlinarith
  have hu : u 0 = v 0 := by
    rcases mul_eq_zero.mp hf with hf | hf
    · linarith
    · linarith
  have hv : u 1 = v 1 := by rw [hu] at h₁; nlinarith
  ext i
  fin_cases i <;> assumption

theorem coordinates_combination (B : DistributionBasis) (hB : B.Valid)
    (u : Fin 2 → ℝ) :
    distributionCoordinates B
      (u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B) = u := by
  exact coefficients_unique B hB _ _ (distributionCoordinates_reconstruct B hB _).symm

theorem integerCoordinates_combination (B : DistributionBasis) (hB : B.Valid)
    (u : Fin 2 → ℤ) :
    distributionIntegerCoordinates B
      (u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B) = u := by
  have hc := coordinates_combination B hB (fun i => (u i : ℝ))
  simp only [Int.cast_smul_eq_zsmul] at hc
  ext i
  simp only [distributionIntegerCoordinates, hc, Int.floor_intCast]

theorem coordinates_add (B : DistributionBasis) (x y : ℝ × ℝ) :
    distributionCoordinates B (x + y) =
      distributionCoordinates B x + distributionCoordinates B y := by
  ext i
  fin_cases i <;>
    simp [distributionCoordinates, add_div, sub_div] <;> ring

theorem integerCoordinates_add_on_lattice (B : DistributionBasis) (hB : B.Valid)
    (x y : ℝ × ℝ) (hx : x ∈ distributionLattice B) (hy : y ∈ distributionLattice B) :
    distributionIntegerCoordinates B (x + y) =
      distributionIntegerCoordinates B x + distributionIntegerCoordinates B y := by
  ext i
  have hx' := (distributionLattice_coordinates B hB x).1 hx i
  have hy' := (distributionLattice_coordinates B hB y).1 hy i
  change ⌊distributionCoordinates B (x + y) i⌋ = _
  rw [coordinates_add, Pi.add_apply, hx', hy', ← Int.cast_add, Int.floor_intCast]
  rfl

theorem nonlattice_continuous_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (t : ℝ) (hT : 0 < (M 1 0 : ℝ) * t + (M 1 1 : ℝ))
    (z : ℂ) (hz : z ∉ modularPhiPseudoLattice (t : ℂ)) :
    ContinuousAt (fun w => modularPhi M m n w (t : ℂ)) z ∧
      modularPhi M m n z (t : ℂ) ≠ 0 := by
  have hu := modularPhi_real_off_lattice M hM m n t hT z hz
  have ha := modularPhi_joint_analytic_no_poles M hM m n (z, (t : ℂ)) ⟨hu.1, hu.2.1⟩
  refine ⟨?_, (modularPhi_ne_zero_iff M hM m n z _ hu.1 hu.2.1).2 hu.2.2⟩
  exact ha.continuousAt.comp (f := fun w : ℂ => (w, (t : ℂ)))
    (show ContinuousAt (fun w : ℂ => (w, (t : ℂ))) z by fun_prop)

theorem nonlattice_phase_avoid (t : ℝ) (z : ℂ)
    (hz : z ∉ modularPhiPseudoLattice (t : ℂ)) (m : ℤ) :
    ∀ j : ℤ, 1 - e (t : ℂ) ^ (m + j) * e z ≠ 0 := by
  intro j hj
  have he : e (((m + j : ℤ) : ℂ) * (t : ℂ) + z) = 1 := by
    rw [e_add', ← e_int_mul]
    exact (sub_eq_zero.mp hj).symm
  obtain ⟨k, hk⟩ := e_eq_one_iff_int he
  apply hz
  refine ⟨-(m + j), k, ?_⟩
  push_cast at hk ⊢
  linear_combination hk

theorem periodPoint_argument (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    ((x.1 / B.scale : ℝ) : ℂ) / etaDenom B.matrix (B.tau : ℂ) =
      ((x.1 / B.scale : ℝ) : ℂ) +
        (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 : ℂ) *
          (B.tau : ℂ) +
        (distributionIntegerCoordinates B (distributionPeriodDifference B x) 1 : ℂ) := by
  have hf := congrArg Prod.fst (distributionPeriodPoints_expansion B hB x hx)
  change ((distributionPeriod B)⁻¹ - 1) * x.1 = _ at hf
  simp only [Prod.fst_add, distributionBetaOne, distributionBetaTwo,
    zsmul_eq_mul, Prod.fst_mul, Prod.fst_intCast] at hf
  have hs := hB.2.2.2.2.1.ne'
  have hε := (lt_trans zero_lt_one hB.2.2.2.1).ne'
  have hr : x.1 / B.scale / distributionPeriod B = x.1 / B.scale +
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 : ℝ) * B.tau +
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 1 : ℝ) := by
    field_simp [hs, hε] at hf ⊢
    nlinarith [hf]
  have hc := congrArg (fun t : ℝ => (t : ℂ)) hr
  simpa [distributionPeriod, etaDenom] using hc

theorem periodPoint_phase (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    e (B.tau : ℂ) ^ (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0) *
        e ((x.1 / B.scale : ℝ) : ℂ) =
      e (((x.1 / B.scale : ℝ) : ℂ) / etaDenom B.matrix (B.tau : ℂ)) := by
  rw [periodPoint_argument B hB x hx, e_add', e_add', e_intCast, mul_one, ← e_int_mul,
    mul_comm]

theorem periodDifference_combination (B : DistributionBasis) (hB : B.Valid)
    (k l : ℤ) :
    distributionPeriodDifference B (k • distributionBetaOne B + l • distributionBetaTwo B) =
      ((B.matrix 1 1 - 1) * k - B.matrix 1 0 * l) • distributionBetaOne B +
        (-B.matrix 0 1 * k + (B.matrix 0 0 - 1) * l) • distributionBetaTwo B := by
  rw [map_add, map_zsmul, map_zsmul,
    (distributionPeriodDifference_basis B hB).1,
    (distributionPeriodDifference_basis B hB).2]
  module

theorem integerCoordinates_translate (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) (k l : ℤ) :
    distributionIntegerCoordinates B
      (distributionPeriodDifference B (x + (k • distributionBetaOne B + l • distributionBetaTwo B))) 0 =
      distributionIntegerCoordinates B (distributionPeriodDifference B x) 0 +
        ((B.matrix 1 1 - 1) * k - B.matrix 1 0 * l) := by
  have hρ : k • distributionBetaOne B + l • distributionBetaTwo B ∈ distributionLattice B :=
    (distributionLattice_mem_iff B _).2 ⟨![k, l], rfl⟩
  have hDρ := distributionLattice_le_periodPoints B hB hρ
  rw [map_add, integerCoordinates_add_on_lattice B hB _ _ hx hDρ,
    periodDifference_combination B hB k l]
  have hc := integerCoordinates_combination B hB
    ![(B.matrix 1 1 - 1) * k - B.matrix 1 0 * l,
      -B.matrix 0 1 * k + (B.matrix 0 0 - 1) * l]
  simpa using congrFun (congrArg (fun f => distributionIntegerCoordinates B
    (distributionPeriodDifference B x) + f) hc) 0

theorem integerCoordinates_change (B C : DistributionBasis) (hB : B.Valid) (hC : C.Valid)
    (A : SL(2, ℤ))
    (h₁ : distributionBetaOne C =
      A 0 0 • distributionBetaOne B + A 0 1 • distributionBetaTwo B)
    (h₂ : distributionBetaTwo C =
      A 1 0 • distributionBetaOne B + A 1 1 • distributionBetaTwo B)
    (x : ℝ × ℝ) (hx : x ∈ distributionLattice B) :
    distributionIntegerCoordinates C x =
      ![A 1 1 * distributionIntegerCoordinates B x 0 -
          A 1 0 * distributionIntegerCoordinates B x 1,
        -A 0 1 * distributionIntegerCoordinates B x 0 +
          A 0 0 * distributionIntegerCoordinates B x 1] := by
  have hd := det_coe_int A
  have hb₁ : A 1 1 • distributionBetaOne C - A 0 1 • distributionBetaTwo C =
      distributionBetaOne B := by
    calc
      _ = (A 0 0 * A 1 1 - A 0 1 * A 1 0) • distributionBetaOne B := by
        rw [h₁, h₂]
        module
      _ = _ := by rw [hd, one_zsmul]
  have hb₂ : -A 1 0 • distributionBetaOne C + A 0 0 • distributionBetaTwo C =
      distributionBetaTwo B := by
    calc
      _ = (A 0 0 * A 1 1 - A 0 1 * A 1 0) • distributionBetaTwo B := by
        rw [h₁, h₂]
        module
      _ = _ := by rw [hd, one_zsmul]
  obtain ⟨u, hu⟩ := (distributionLattice_mem_iff B x).1 hx
  have huc : distributionIntegerCoordinates B x = u := by
    rw [hu, integerCoordinates_combination B hB]
  rw [huc]
  have hxc : x =
      (A 1 1 * u 0 - A 1 0 * u 1) • distributionBetaOne C +
        (-A 0 1 * u 0 + A 0 0 * u 1) • distributionBetaTwo C := by
    rw [hu, ← hb₁, ← hb₂]
    module
  rw [hxc]
  exact integerCoordinates_combination C hC
    ![A 1 1 * u 0 - A 1 0 * u 1, -A 0 1 * u 0 + A 0 0 * u 1]

theorem nonlattice_add_integer (t : ℂ) (z : ℂ)
    (hz : z ∉ modularPhiPseudoLattice t) (m n : ℤ) :
    z + (m : ℂ) * t + (n : ℂ) ∉ modularPhiPseudoLattice t := by
  rintro ⟨k, l, h⟩
  apply hz
  refine ⟨k - m, l - n, ?_⟩
  push_cast
  linear_combination h

theorem supported_of_nonneg (A : SL(2, ℤ)) (hc : 0 ≤ A 1 0)
    (t : ℝ) (hden : 0 < (A 1 0 : ℝ) * t + (A 1 1 : ℝ)) :
    ModularPhiSupported A := by
  rcases eq_or_lt_of_le hc with hz | hp
  · have hc0 : A 1 0 = 0 := hz.symm
    have hd := det_coe_int A
    rw [hc0, mul_zero, sub_zero] at hd
    have hdpos : 0 < A 1 1 := by exact_mod_cast (by simpa [hc0] using hden : (0 : ℝ) < A 1 1)
    have hd1 : A 1 1 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one (u := A 1 1) (v := A 0 0)
        (by simpa only [mul_comm] using hd) with h | h
      · exact h
      · omega
    have ha1 : A 0 0 = 1 := by simpa [hd1] using hd
    refine Or.inr ⟨A 0 1, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, hc0, ha1, hd1]
  · exact Or.inl hp

theorem constructed_zero_continuous_ne_zero (A : SL(2, ℤ))
    (t : ℝ) (hT : 0 < (A 1 0 : ℝ) * t + (A 1 1 : ℝ))
    (z : ℂ) (hz : z ∉ modularPhiPseudoLattice (t : ℂ)) :
    ContinuousAt (fun w => modularPhiConstructed A 0 0 w (t : ℂ)) z ∧
      modularPhiConstructed A 0 0 z (t : ℂ) ≠ 0 := by
  by_cases hc : 0 < A 1 0
  · simpa only [modularPhiConstructed, if_pos hc] using
      nonlattice_continuous_ne_zero A hc 0 0 t hT z hz
  · have hone (w : ℂ) : modularPhiConstructed A 0 0 w (t : ℂ) = 1 := by
      simp [modularPhiConstructed, hc, modularPhiTranslation, qPochhammerInt,
        qPochhammerIntNumerator, qPochhammerIntDenominator, qPochhammerNat]
    simp only [hone]
    exact ⟨continuousAt_const, one_ne_zero⟩

def realMobius (A : SL(2, ℤ)) (t : ℝ) : ℝ :=
  ((A 0 0 : ℝ) * t + (A 0 1 : ℝ)) /
    ((A 1 0 : ℝ) * t + (A 1 1 : ℝ))

def rebaseData (B : DistributionBasis) (A : SL(2, ℤ)) : DistributionBasis :=
  { matrix := A * B.matrix * A⁻¹
    tau := realMobius A B.tau
    scale := B.scale * ((A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ))
    scaleConj := B.scaleConj *
      ((A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ)) }

lemma realMobius_cast (A : SL(2, ℤ)) (t : ℝ) :
    etaMobius A (t : ℂ) = (realMobius A t : ℂ) := by
  simp [etaMobius, etaDenom, realMobius]

lemma trace_conjugate (M A : SL(2, ℤ)) :
    (A * M * A⁻¹) 0 0 + (A * M * A⁻¹) 1 1 = M 0 0 + M 1 1 := by
  have ht := Matrix.trace_mul_comm ((A * M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  change Matrix.trace ((↑(A * M * A⁻¹)) : Matrix (Fin 2) (Fin 2) ℤ) =
    Matrix.trace ((↑(A⁻¹ * (A * M))) : Matrix (Fin 2) (Fin 2) ℤ) at ht
  have hi : A⁻¹ * (A * M) = M := by group
  rw [hi] at ht
  simpa [Matrix.trace, Fin.sum_univ_two] using ht

lemma conjugateTau_fixed (B : DistributionBasis) (hB : B.Valid) :
    etaMobius B.matrix (distributionConjugateTau B : ℂ) =
      (distributionConjugateTau B : ℂ) := by
  obtain ⟨_, _, hs, ht⟩ := distributionBasis_spectral B hB
  have he : distributionPeriod B ≠ 0 := ne_of_gt (lt_trans zero_lt_one hB.2.2.2.1)
  have hc : (B.matrix 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hB.1
  have hd : (B.matrix 0 0 : ℝ) * B.matrix 1 1 -
      (B.matrix 0 1 : ℝ) * B.matrix 1 0 = 1 := by
    exact_mod_cast det_coe_int B.matrix
  have ha : (B.matrix 0 0 : ℝ) -
      (B.matrix 1 0 : ℝ) * distributionConjugateTau B = distributionPeriod B := by
    linarith
  have hn : ((B.matrix 0 0 : ℝ) -
      (B.matrix 1 0 : ℝ) * distributionConjugateTau B) *
      ((B.matrix 1 0 : ℝ) * distributionConjugateTau B +
        (B.matrix 1 1 : ℝ)) = 1 := by
    rw [ha, hs, mul_inv_cancel₀ he]
  have hf : (B.matrix 0 0 : ℝ) * distributionConjugateTau B +
      (B.matrix 0 1 : ℝ) =
      distributionConjugateTau B *
        ((B.matrix 1 0 : ℝ) * distributionConjugateTau B +
          (B.matrix 1 1 : ℝ)) := by
    apply (mul_left_cancel₀ hc)
    linear_combination hn - hd
  rw [realMobius_cast]
  apply congrArg Complex.ofReal
  exact (div_eq_iff (by rw [hs]; exact inv_ne_zero he)).mpr hf

theorem rebase_valid (B : DistributionBasis) (hB : B.Valid)
    (A : SL(2, ℤ))
    (hA₁ : 0 < (A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ))
    (hA₂ : 0 < (A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ))
    (hA₃ : 0 < (A * B.matrix * A⁻¹) 1 0) :
    (rebaseData B A).Valid ∧
      distributionPeriod (rebaseData B A) = distributionPeriod B ∧
      distributionConjugateTau (rebaseData B A) =
        realMobius A (distributionConjugateTau B) := by
  have he : distributionPeriod B ≠ 0 := ne_of_gt (lt_trans zero_lt_one hB.2.2.2.1)
  have hden : etaDenom B.matrix (B.tau : ℂ) ≠ 0 := by
    simpa [etaDenom, distributionPeriod] using Complex.ofReal_ne_zero.mpr he
  have hdenA : etaDenom A (B.tau : ℂ) ≠ 0 := by
    simpa [etaDenom] using Complex.ofReal_ne_zero.mpr (ne_of_gt hA₁)
  obtain ⟨hf, hp⟩ := ModularCocycleMatrixAux.conjugate_fixedPoint
    B.matrix A (B.tau : ℂ) hB.2.2.1 hden hdenA
  have hperiod : distributionPeriod (rebaseData B A) = distributionPeriod B := by
    have hr := congrArg Complex.re hp
    simpa [etaDenom, realMobius_cast, rebaseData, distributionPeriod] using hr
  have hnew : (rebaseData B A).Valid := by
    refine ⟨hA₃, ?_, ?_, ?_, ?_, ?_⟩
    · change 2 < (A * B.matrix * A⁻¹) 0 0 + (A * B.matrix * A⁻¹) 1 1
      rw [trace_conjugate]
      exact hB.2.1
    · simpa [rebaseData, realMobius_cast] using hf
    · rw [hperiod]
      exact hB.2.2.2.1
    · exact mul_pos hB.2.2.2.2.1 hA₁
    · exact mul_pos hB.2.2.2.2.2 hA₂
  refine ⟨hnew, hperiod, ?_⟩
  have hs := (distributionBasis_spectral B hB).2.2.1
  have hden' : etaDenom B.matrix (distributionConjugateTau B : ℂ) ≠ 0 := by
    have hr : (B.matrix 1 0 : ℝ) * distributionConjugateTau B +
        (B.matrix 1 1 : ℝ) ≠ 0 := by
      rw [hs]
      exact inv_ne_zero he
    simpa [etaDenom] using Complex.ofReal_ne_zero.mpr hr
  have hdenA' : etaDenom A (distributionConjugateTau B : ℂ) ≠ 0 := by
    simpa [etaDenom] using Complex.ofReal_ne_zero.mpr (ne_of_gt hA₂)
  have hp' := (ModularCocycleMatrixAux.conjugate_fixedPoint B.matrix A
    (distributionConjugateTau B : ℂ) (conjugateTau_fixed B hB) hden' hdenA').2
  have hr := congrArg Complex.re hp'
  have hr' : ((rebaseData B A).matrix 1 0 : ℝ) *
      realMobius A (distributionConjugateTau B) +
      ((rebaseData B A).matrix 1 1 : ℝ) = (distributionPeriod B)⁻¹ := by
    simpa [etaDenom, realMobius_cast, hs, rebaseData] using hr
  have hn := (distributionBasis_spectral (rebaseData B A) hnew).2.2.1
  rw [hperiod] at hn
  have hc : ((rebaseData B A).matrix 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hA₃
  apply mul_left_cancel₀ hc
  linarith

lemma rebase_beta (B : DistributionBasis) (hB : B.Valid)
    (A : SL(2, ℤ))
    (hA₁ : 0 < (A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ))
    (hA₂ : 0 < (A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ))
    (hA₃ : 0 < (A * B.matrix * A⁻¹) 1 0) :
    distributionBetaOne (rebaseData B A) =
        A 0 0 • distributionBetaOne B + A 0 1 • distributionBetaTwo B ∧
      distributionBetaTwo (rebaseData B A) =
        A 1 0 • distributionBetaOne B + A 1 1 • distributionBetaTwo B := by
  have hs := (rebase_valid B hB A hA₁ hA₂ hA₃).2.2
  have h₁ : (A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ) ≠ 0 := ne_of_gt hA₁
  have h₂ : (A 1 0 : ℝ) * distributionConjugateTau B +
      (A 1 1 : ℝ) ≠ 0 := ne_of_gt hA₂
  constructor
  · apply Prod.ext
    · simp only [distributionBetaOne, distributionBetaTwo, rebaseData,
        Prod.fst_add, Prod.smul_fst, realMobius]
      simp only [zsmul_eq_mul]
      field_simp [h₁, h₂]
    · simp only [distributionBetaOne, distributionBetaTwo, Prod.snd_add,
        Prod.smul_snd, hs]
      simp only [zsmul_eq_mul]
      dsimp only [rebaseData]
      rw [realMobius]
      field_simp [h₁, h₂]
  · apply Prod.ext
    · simp only [distributionBetaOne, distributionBetaTwo, rebaseData,
        Prod.fst_add, Prod.smul_fst]
      simp only [zsmul_eq_mul]
      ring
    · simp only [distributionBetaOne, distributionBetaTwo, rebaseData,
        Prod.snd_add, Prod.smul_snd]
      simp only [zsmul_eq_mul]
      ring

lemma integer_span_change (A : SL(2, ℤ)) (u v : ℝ × ℝ) :
    AddSubgroup.zmultiples (A 0 0 • u + A 0 1 • v) ⊔
        AddSubgroup.zmultiples (A 1 0 • u + A 1 1 • v) =
      AddSubgroup.zmultiples u ⊔ AddSubgroup.zmultiples v := by
  let L := AddSubgroup.zmultiples u ⊔ AddSubgroup.zmultiples v
  let L' := AddSubgroup.zmultiples (A 0 0 • u + A 0 1 • v) ⊔
    AddSubgroup.zmultiples (A 1 0 • u + A 1 1 • v)
  have hu : u ∈ L := (show AddSubgroup.zmultiples u ≤ L from le_sup_left)
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩)
  have hv : v ∈ L := (show AddSubgroup.zmultiples v ≤ L from le_sup_right)
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩)
  have hu' : A 0 0 • u + A 0 1 • v ∈ L' :=
    (show AddSubgroup.zmultiples (A 0 0 • u + A 0 1 • v) ≤ L' from le_sup_left)
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩)
  have hv' : A 1 0 • u + A 1 1 • v ∈ L' :=
    (show AddSubgroup.zmultiples (A 1 0 • u + A 1 1 • v) ≤ L' from le_sup_right)
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩)
  have hdet : A 1 1 * A 0 0 - A 0 1 * A 1 0 = 1 := by
    nlinarith [det_coe_int A]
  have hrecu : A 1 1 • (A 0 0 • u + A 0 1 • v) -
      A 0 1 • (A 1 0 • u + A 1 1 • v) = u := by
    calc
      _ = (A 1 1 * A 0 0 - A 0 1 * A 1 0) • u +
          (A 1 1 * A 0 1 - A 0 1 * A 1 1) • v := by
        simp only [smul_add, sub_smul, smul_smul]
        abel
      _ = u := by rw [hdet]; simp [mul_comm]
  have hrecv : A 0 0 • (A 1 0 • u + A 1 1 • v) -
      A 1 0 • (A 0 0 • u + A 0 1 • v) = v := by
    calc
      _ = (A 0 0 * A 1 0 - A 1 0 * A 0 0) • u +
          (A 0 0 * A 1 1 - A 1 0 * A 0 1) • v := by
        simp only [smul_add, sub_smul, smul_smul]
        abel
      _ = v := by
        rw [show A 0 0 * A 1 1 - A 1 0 * A 0 1 = 1 by nlinarith [det_coe_int A]]
        simp [mul_comm]
  apply le_antisymm
  · exact sup_le (AddSubgroup.zmultiples_le.mpr
        (L.add_mem (L.zsmul_mem hu _) (L.zsmul_mem hv _)))
      (AddSubgroup.zmultiples_le.mpr
        (L.add_mem (L.zsmul_mem hu _) (L.zsmul_mem hv _)))
  · apply sup_le
    · apply AddSubgroup.zmultiples_le.mpr
      simpa only [hrecu] using
        L'.sub_mem (L'.zsmul_mem hu' (A 1 1)) (L'.zsmul_mem hv' (A 0 1))
    · apply AddSubgroup.zmultiples_le.mpr
      simpa only [hrecv] using
        L'.sub_mem (L'.zsmul_mem hv' (A 0 0)) (L'.zsmul_mem hu' (A 1 0))

theorem rebase_lattice (B : DistributionBasis) (hB : B.Valid)
    (A : SL(2, ℤ))
    (hA₁ : 0 < (A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ))
    (hA₂ : 0 < (A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ))
    (hA₃ : 0 < (A * B.matrix * A⁻¹) 1 0) :
    distributionLattice (rebaseData B A) = distributionLattice B ∧
      distributionPeriodPoints (rebaseData B A) = distributionPeriodPoints B := by
  obtain ⟨hb₁, hb₂⟩ := rebase_beta B hB A hA₁ hA₂ hA₃
  have hI : distributionLattice (rebaseData B A) = distributionLattice B := by
    unfold distributionLattice
    rw [hb₁, hb₂]
    exact integer_span_change A (distributionBetaOne B) (distributionBetaTwo B)
  refine ⟨hI, ?_⟩
  have hp := (rebase_valid B hB A hA₁ hA₂ hA₃).2.1
  simp only [distributionPeriodPoints, distributionPeriodDifference, hI, hp]

theorem sc_zcoefficients_unique (B : DistributionBasis) (hB : B.Valid)
    (a b c d : ℤ)
    (h : a • distributionBetaOne B + b • distributionBetaTwo B =
      c • distributionBetaOne B + d • distributionBetaTwo B) : a = c ∧ b = d := by
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at hfst hsnd
  simp only [distributionBetaOne, distributionBetaTwo, zsmul_eq_mul] at hfst hsnd
  have hp : 0 < B.scale := hB.2.2.2.2.1
  have hq : 0 < B.scaleConj := hB.2.2.2.2.2
  have ht := (distributionBasis_spectral B hB).2.1
  have h1 : (a : ℝ) * B.tau + (b : ℝ) = (c : ℝ) * B.tau + (d : ℝ) := by
    apply mul_left_cancel₀ hp.ne'
    nlinarith only [hfst]
  have h2 : (a : ℝ) * distributionConjugateTau B + (b : ℝ) =
      (c : ℝ) * distributionConjugateTau B + (d : ℝ) := by
    apply mul_left_cancel₀ hq.ne'
    nlinarith only [hsnd]
  have ha : (a : ℝ) = (c : ℝ) := by
    apply (mul_left_injective₀ (sub_ne_zero.mpr (ne_of_gt ht)))
    nlinarith only [h1, h2]
  have hb : (b : ℝ) = (d : ℝ) := by rw [ha] at h1; linarith only [h1]
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

theorem sc_matrix_eq_of_rows (B : DistributionBasis) (hB : B.Valid)
    (P Q : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ∀ i, P i 0 • distributionBetaOne B + P i 1 • distributionBetaTwo B =
      Q i 0 • distributionBetaOne B + Q i 1 • distributionBetaTwo B) : P = Q := by
  ext i j
  have hi := sc_zcoefficients_unique B hB _ _ _ _ (h i)
  fin_cases j
  · exact hi.1
  · exact hi.2

theorem sc_basis_area_pos (B : DistributionBasis) (hB : B.Valid) :
    0 < (distributionBetaOne B).1 * (distributionBetaTwo B).2 -
      (distributionBetaOne B).2 * (distributionBetaTwo B).1 := by
  have hp := mul_pos (mul_pos hB.2.2.2.2.1 hB.2.2.2.2.2)
    (sub_pos.mpr (distributionBasis_spectral B hB).2.1)
  dsimp [distributionBetaOne, distributionBetaTwo]
  nlinarith only [hp]

theorem sc_same_lattice_SL_rows (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid)
    (hI : distributionLattice C = distributionLattice B) :
    ∃ A : SL(2, ℤ),
      distributionBetaOne C =
        A 0 0 • distributionBetaOne B + A 0 1 • distributionBetaTwo B ∧
      distributionBetaTwo C =
        A 1 0 • distributionBetaOne B + A 1 1 • distributionBetaTwo B := by
  have hone (D : DistributionBasis) :
      distributionBetaOne D ∈ distributionLattice D := by
    apply (distributionLattice_mem_iff D _).2
    exact ⟨![1, 0], by simp⟩
  have htwo (D : DistributionBasis) :
      distributionBetaTwo D ∈ distributionLattice D := by
    apply (distributionLattice_mem_iff D _).2
    exact ⟨![0, 1], by simp⟩
  obtain ⟨u, hu⟩ := (distributionLattice_mem_iff B _).1 (hI ▸ hone C)
  obtain ⟨v, hv⟩ := (distributionLattice_mem_iff B _).1 (hI ▸ htwo C)
  obtain ⟨r, hr⟩ := (distributionLattice_mem_iff C _).1 (hI.symm ▸ hone B)
  obtain ⟨s, hs⟩ := (distributionLattice_mem_iff C _).1 (hI.symm ▸ htwo B)
  let P : Matrix (Fin 2) (Fin 2) ℤ := ![u, v]
  let Q : Matrix (Fin 2) (Fin 2) ℤ := ![r, s]
  change distributionBetaOne C = P 0 0 • distributionBetaOne B +
    P 0 1 • distributionBetaTwo B at hu
  change distributionBetaTwo C = P 1 0 • distributionBetaOne B +
    P 1 1 • distributionBetaTwo B at hv
  change distributionBetaOne B = Q 0 0 • distributionBetaOne C +
    Q 0 1 • distributionBetaTwo C at hr
  change distributionBetaTwo B = Q 1 0 • distributionBetaOne C +
    Q 1 1 • distributionBetaTwo C at hs
  have hQP : Q * P = 1 := by
    apply sc_matrix_eq_of_rows B hB
    intro i
    fin_cases i
    · change (Q * P) 0 0 • distributionBetaOne B + (Q * P) 0 1 • distributionBetaTwo B =
        (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 • distributionBetaOne B +
        (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 • distributionBetaTwo B
      calc
        _ = Q 0 0 • (P 0 0 • distributionBetaOne B + P 0 1 • distributionBetaTwo B) +
            Q 0 1 • (P 1 0 • distributionBetaOne B + P 1 1 • distributionBetaTwo B) := by
          simp only [Matrix.mul_apply, Fin.sum_univ_two]
          module
        _ = Q 0 0 • distributionBetaOne C + Q 0 1 • distributionBetaTwo C := by
          rw [← hu, ← hv]
        _ = distributionBetaOne B := hr.symm
        _ = _ := by simp
    · change (Q * P) 1 0 • distributionBetaOne B + (Q * P) 1 1 • distributionBetaTwo B =
        (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 • distributionBetaOne B +
        (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 • distributionBetaTwo B
      calc
        _ = Q 1 0 • (P 0 0 • distributionBetaOne B + P 0 1 • distributionBetaTwo B) +
            Q 1 1 • (P 1 0 • distributionBetaOne B + P 1 1 • distributionBetaTwo B) := by
          simp only [Matrix.mul_apply, Fin.sum_univ_two]
          module
        _ = Q 1 0 • distributionBetaOne C + Q 1 1 • distributionBetaTwo C := by
          rw [← hu, ← hv]
        _ = distributionBetaTwo B := hs.symm
        _ = _ := by simp
  have hunit : P.det * Q.det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hQP, Matrix.det_one]
  have harea :
      (distributionBetaOne C).1 * (distributionBetaTwo C).2 -
          (distributionBetaOne C).2 * (distributionBetaTwo C).1 =
      (P.det : ℝ) * ((distributionBetaOne B).1 * (distributionBetaTwo B).2 -
          (distributionBetaOne B).2 * (distributionBetaTwo B).1) := by
    rw [hu, hv]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    simp only [zsmul_eq_mul, Matrix.det_fin_two, Int.cast_sub, Int.cast_mul]
    ring
  have hdetpos : 0 < (P.det : ℝ) := by
    exact (mul_pos_iff_of_pos_right (sc_basis_area_pos B hB)).1
      (harea ▸ sc_basis_area_pos C hC)
  have hdetposZ : 0 < P.det := by exact_mod_cast hdetpos
  have hdet : P.det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h
    · exact h
    · omega
  exact ⟨⟨P, hdet⟩, hu, hv⟩

def sc_inverseAction (B : DistributionBasis) : (ℝ × ℝ) →+ (ℝ × ℝ) :=
  distributionPeriodDifference B + AddMonoidHom.id (ℝ × ℝ)

theorem sc_inverseAction_eq (B C : DistributionBasis)
    (hε : distributionPeriod C = distributionPeriod B) :
    sc_inverseAction C = sc_inverseAction B := by
  simp [sc_inverseAction, distributionPeriodDifference, hε]

theorem sc_inverseAction_basis (B : DistributionBasis) (hB : B.Valid) :
    sc_inverseAction B (distributionBetaOne B) =
        (B.matrix⁻¹) 0 0 • distributionBetaOne B +
        (B.matrix⁻¹) 0 1 • distributionBetaTwo B ∧
      sc_inverseAction B (distributionBetaTwo B) =
        (B.matrix⁻¹) 1 0 • distributionBetaOne B +
        (B.matrix⁻¹) 1 1 • distributionBetaTwo B := by
  have h := distributionPeriodDifference_basis B hB
  simp only [sc_inverseAction, AddMonoidHom.add_apply, AddMonoidHom.id_apply]
  rw [h.1, h.2]
  simp only [Matrix.SpecialLinearGroup.SL2_inv_expl,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> module

theorem sc_change_conjugacy (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid)
    (hε : distributionPeriod C = distributionPeriod B)
    (A : SL(2, ℤ))
    (hu : distributionBetaOne C =
      A 0 0 • distributionBetaOne B + A 0 1 • distributionBetaTwo B)
    (hv : distributionBetaTwo C =
      A 1 0 • distributionBetaOne B + A 1 1 • distributionBetaTwo B) :
    C.matrix = A * B.matrix * A⁻¹ := by
  have hb := sc_inverseAction_basis B hB
  have hc := sc_inverseAction_basis C hC
  have hF := sc_inverseAction_eq B C hε
  have hrow (i : Fin 2) :
      (C.matrix⁻¹ * A) i 0 • distributionBetaOne B +
          (C.matrix⁻¹ * A) i 1 • distributionBetaTwo B =
      (A * B.matrix⁻¹) i 0 • distributionBetaOne B +
          (A * B.matrix⁻¹) i 1 • distributionBetaTwo B := by
    fin_cases i
    · change (C.matrix⁻¹ * A) 0 0 • distributionBetaOne B +
          (C.matrix⁻¹ * A) 0 1 • distributionBetaTwo B =
        (A * B.matrix⁻¹) 0 0 • distributionBetaOne B +
          (A * B.matrix⁻¹) 0 1 • distributionBetaTwo B
      calc
        _ = (C.matrix⁻¹) 0 0 • distributionBetaOne C +
            (C.matrix⁻¹) 0 1 • distributionBetaTwo C := by
          rw [hu, hv]
          simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
          module
        _ = sc_inverseAction C (distributionBetaOne C) := hc.1.symm
        _ = sc_inverseAction B
            (A 0 0 • distributionBetaOne B + A 0 1 • distributionBetaTwo B) := by
          rw [hF, hu]
        _ = _ := by
          rw [map_add, map_zsmul, map_zsmul, hb.1, hb.2]
          simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
          module
    · change (C.matrix⁻¹ * A) 1 0 • distributionBetaOne B +
          (C.matrix⁻¹ * A) 1 1 • distributionBetaTwo B =
        (A * B.matrix⁻¹) 1 0 • distributionBetaOne B +
          (A * B.matrix⁻¹) 1 1 • distributionBetaTwo B
      calc
        _ = (C.matrix⁻¹) 1 0 • distributionBetaOne C +
            (C.matrix⁻¹) 1 1 • distributionBetaTwo C := by
          rw [hu, hv]
          simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
          module
        _ = sc_inverseAction C (distributionBetaTwo C) := hc.2.symm
        _ = sc_inverseAction B
            (A 1 0 • distributionBetaOne B + A 1 1 • distributionBetaTwo B) := by
          rw [hF, hv]
        _ = _ := by
          rw [map_add, map_zsmul, map_zsmul, hb.1, hb.2]
          simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
          module
  have hinv : C.matrix⁻¹ * A = A * B.matrix⁻¹ := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h := sc_zcoefficients_unique B hB _ _ _ _ (hrow i)
    fin_cases j
    · exact h.1
    · exact h.2
  have heq : C.matrix⁻¹ = A * B.matrix⁻¹ * A⁻¹ :=
    (eq_mul_inv_iff_mul_eq).2 hinv
  calc
    C.matrix = (C.matrix⁻¹)⁻¹ := (inv_inv _).symm
    _ = (A * B.matrix⁻¹ * A⁻¹)⁻¹ := congrArg Inv.inv heq
    _ = A * B.matrix * A⁻¹ := by group

lemma inverse_mobius (A : SL(2, ℤ)) (t : ℝ)
    (ht : (A 1 0 : ℝ) * t + (A 1 1 : ℝ) ≠ 0) :
    realMobius A⁻¹ (realMobius A t) = t ∧
      ((A⁻¹ 1 0 : ℝ) * realMobius A t + (A⁻¹ 1 1 : ℝ)) =
        ((A 1 0 : ℝ) * t + (A 1 1 : ℝ))⁻¹ := by
  have hden : etaDenom A (t : ℂ) ≠ 0 := by
    simpa [etaDenom] using Complex.ofReal_ne_zero.mpr ht
  have hd := ModularCocycleMatrixAux.denom_mul A⁻¹ A (t : ℂ) hden
  have hr := congrArg Complex.re hd
  have hr' : (1 : ℝ) =
      ((A⁻¹ 1 0 : ℝ) * realMobius A t + (A⁻¹ 1 1 : ℝ)) *
        ((A 1 0 : ℝ) * t + (A 1 1 : ℝ)) := by
    simpa [etaDenom, realMobius_cast] using hr
  have hi : ((A⁻¹ 1 0 : ℝ) * realMobius A t + (A⁻¹ 1 1 : ℝ)) =
      ((A 1 0 : ℝ) * t + (A 1 1 : ℝ))⁻¹ := by
    apply mul_right_cancel₀ ht
    rw [inv_mul_cancel₀ ht]
    exact hr'.symm
  refine ⟨?_, hi⟩
  have hinv : etaDenom A⁻¹ (etaMobius A (t : ℂ)) ≠ 0 := by
    rw [realMobius_cast]
    have hn : ((A⁻¹ 1 0 : ℝ) * realMobius A t + (A⁻¹ 1 1 : ℝ)) ≠ 0 := by
      rw [hi]
      exact inv_ne_zero ht
    simpa [etaDenom] using Complex.ofReal_ne_zero.mpr hn
  have hf := (ModularCocycleMatrixAux.automorphy A⁻¹ A (t : ℂ) hden hinv).2.2
  have hone : etaMobius (1 : SL(2, ℤ)) (t : ℂ) = (t : ℂ) := by
    simp [etaMobius, etaDenom]
  rw [inv_mul_cancel, hone, realMobius_cast, realMobius_cast] at hf
  exact Complex.ofReal_injective hf.symm

theorem rebase_inverse (B : DistributionBasis) (hB : B.Valid)
    (A : SL(2, ℤ))
    (hA₁ : 0 < (A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ))
    (hA₂ : 0 < (A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ))
    (hA₃ : 0 < (A * B.matrix * A⁻¹) 1 0) :
    rebaseData (rebaseData B A) A⁻¹ = B ∧
      0 < (A⁻¹ 1 0 : ℝ) * (rebaseData B A).tau + (A⁻¹ 1 1 : ℝ) ∧
      0 < (A⁻¹ 1 0 : ℝ) * distributionConjugateTau (rebaseData B A) +
        (A⁻¹ 1 1 : ℝ) ∧
      0 < (A⁻¹ * (rebaseData B A).matrix * (A⁻¹)⁻¹) 1 0 := by
  obtain ⟨ht₁, hd₁⟩ := inverse_mobius A B.tau (ne_of_gt hA₁)
  obtain ⟨_, hd₂⟩ := inverse_mobius A (distributionConjugateTau B) (ne_of_gt hA₂)
  have hconj := (rebase_valid B hB A hA₁ hA₂ hA₃).2.2
  have hm : A⁻¹ * (rebaseData B A).matrix * (A⁻¹)⁻¹ = B.matrix := by
    dsimp only [rebaseData]
    group
  have h₁ : 0 < (A⁻¹ 1 0 : ℝ) * (rebaseData B A).tau + (A⁻¹ 1 1 : ℝ) := by
    change 0 < (A⁻¹ 1 0 : ℝ) * realMobius A B.tau + (A⁻¹ 1 1 : ℝ)
    rw [hd₁]
    exact inv_pos.mpr hA₁
  have h₂ : 0 < (A⁻¹ 1 0 : ℝ) * distributionConjugateTau (rebaseData B A) +
      (A⁻¹ 1 1 : ℝ) := by
    rw [hconj, hd₂]
    exact inv_pos.mpr hA₂
  refine ⟨?_, h₁, h₂, ?_⟩
  · have ht : (rebaseData (rebaseData B A) A⁻¹).tau = B.tau := ht₁
    have hs : (rebaseData (rebaseData B A) A⁻¹).scale = B.scale := by
      change B.scale * ((A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ)) *
        ((A⁻¹ 1 0 : ℝ) * realMobius A B.tau + (A⁻¹ 1 1 : ℝ)) = B.scale
      rw [hd₁, mul_assoc, mul_inv_cancel₀ (ne_of_gt hA₁), mul_one]
    have hs' : (rebaseData (rebaseData B A) A⁻¹).scaleConj = B.scaleConj := by
      change B.scaleConj * ((A 1 0 : ℝ) * distributionConjugateTau B +
          (A 1 1 : ℝ)) *
        ((A⁻¹ 1 0 : ℝ) * distributionConjugateTau (rebaseData B A) +
          (A⁻¹ 1 1 : ℝ)) = B.scaleConj
      rw [hconj, hd₂, mul_assoc, mul_inv_cancel₀ (ne_of_gt hA₂), mul_one]
    cases B
    change DistributionBasis.mk _ _ _ _ = DistributionBasis.mk _ _ _ _
    rw [DistributionBasis.mk.injEq]
    exact ⟨hm, ht, hs, hs'⟩
  · rw [hm]
    exact hB.1

end SICLean.L4.DistributionBasisValuesAux
