import SICLean.L4.DistributionBasisValuesAux

set_option autoImplicit false

/-!
# Actual E and independence of admissible basis

E uses the actual finite product, the actual eta quotient, and a separate √ε zero-class branch.
Floor coordinates and Quotient.out are concrete total prescriptions; periodicity and representative
independence are conclusions below.

[RW26, p. 2, (2), p. 3, (4), footnote 2, p. 6, (17)] are the matrix background. No assertion that E
is algebraic occurs here.
-/

noncomputable section

open Set
open scoped MatrixGroups Classical

namespace SICLean.L4

/-- Actual analytic value on a real-pair representative. Meaning is asserted for x∈P_B under
B.Valid. The index uses ε⁻¹-1, not ε-1. -/
def distributionBasisValue (B : DistributionBasis) (x : ℝ × ℝ) : ℂ :=
  if x ∈ distributionLattice B then (Real.sqrt (distributionPeriod B) : ℂ)
  else etaMultiplier B.matrix *
    modularPhi B.matrix
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0) 0
      ((x.1 / B.scale : ℝ) : ℂ) (B.tau : ℂ)

/-- A specified representative is used. Descent is not built into the definition. -/
def distributionValue (B : DistributionBasis) (g : DistributionGroup B) : ℂ :=
  distributionBasisValue B (distributionRepresentative B g)

/-- Real Möbius formula, used at both embeddings. -/
def distributionRealMobius (A : SL(2, ℤ)) (t : ℝ) : ℝ :=
  ((A 0 0 : ℝ) * t + (A 0 1 : ℝ)) /
    ((A 1 0 : ℝ) * t + (A 1 1 : ℝ))

/-- Actual change of integer basis. No invariance property is a field. -/
def distributionRebase (B : DistributionBasis) (A : SL(2, ℤ)) : DistributionBasis :=
  { matrix := A * B.matrix * A⁻¹
    tau := distributionRealMobius A B.tau
    scale := B.scale * ((A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ))
    scaleConj := B.scaleConj *
      ((A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ)) }

/-- Entry/embedding positivity only, not a Φ-support or invariance axiom. Negative c_A is allowed;
proofs exchange the bases and use A⁻¹. -/
def DistributionPositiveChange (B : DistributionBasis) (A : SL(2, ℤ)) : Prop :=
  0 < (A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ) ∧
    0 < (A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ) ∧
    0 < (A * B.matrix * A⁻¹) 1 0

/-- Explicit zero-class branch. [RW26, p. 3, (4), footnote 2]. -/
theorem distributionBasisValue_on_lattice (B : DistributionBasis) (x : ℝ × ℝ)
    (hx : x ∈ distributionLattice B) :
    distributionBasisValue B x = (Real.sqrt (distributionPeriod B) : ℂ) := by
  simp only [distributionBasisValue, if_pos hx]

/-- Nonzero-class branch with the precise integer coordinate. [RW26, p. 2, (2)]. -/
theorem distributionBasisValue_off_lattice (B : DistributionBasis) (x : ℝ × ℝ)
    (hx : x ∉ distributionLattice B) :
    distributionBasisValue B x = etaMultiplier B.matrix *
      modularPhi B.matrix
        (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0) 0
        ((x.1 / B.scale : ℝ) : ℂ) (B.tau : ℂ) := by
  simp only [distributionBasisValue, if_neg hx]

/-- Nonzero finite center, using actual divisor exclusion. [RW26, p. 6]. -/
theorem distributionBasisValue_ne_zero (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionBasisValue B x ≠ 0 := by
  by_cases hI : x ∈ distributionLattice B
  · rw [distributionBasisValue_on_lattice B x hI]
    exact_mod_cast (Real.sqrt_pos.2 (lt_trans zero_lt_one hB.2.2.2.1)).ne'
  · rw [distributionBasisValue_off_lattice B x hI]
    have hz : ((x.1 / B.scale : ℝ) : ℂ) ∉ modularPhiPseudoLattice (B.tau : ℂ) :=
      fun h => hI ((distributionPeriodPoints_first_lattice_iff B hB x hx).1 h)
    have hu := modularPhi_real_off_lattice B.matrix hB.1
      (distributionIntegerCoordinates B (distributionPeriodDifference B x) 0) 0
      B.tau (lt_trans zero_lt_one hB.2.2.2.1) _ hz
    exact mul_ne_zero (etaMultiplier_ne_zero B.matrix hB.1)
      ((modularPhi_ne_zero_iff B.matrix hB.1 _ _ _ _ hu.1 hu.2.1).2 hu.2.2)

/-- Every lattice translate, including zero-class representatives. [RW26, p. 6]. -/
theorem distributionBasisValue_periodic (B : DistributionBasis) (hB : B.Valid)
    (x ρ : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B)
    (hρ : ρ ∈ distributionLattice B) :
    distributionBasisValue B (x + ρ) = distributionBasisValue B x := by
  by_cases hI : x ∈ distributionLattice B
  · rw [distributionBasisValue_on_lattice B (x + ρ)
      ((distributionLattice B).add_mem hI hρ), distributionBasisValue_on_lattice B x hI]
  have hI' : x + ρ ∉ distributionLattice B := by
    intro h
    exact hI (by simpa using (distributionLattice B).sub_mem h hρ)
  rw [distributionBasisValue_off_lattice B (x + ρ) hI',
    distributionBasisValue_off_lattice B x hI]
  congr 1
  obtain ⟨u, rfl⟩ := (distributionLattice_mem_iff B ρ).1 hρ
  rw [DistributionBasisValuesAux.integerCoordinates_translate B hB x hx (u 0) (u 1)]
  have harg :
      (((x + (u 0 • distributionBetaOne B + u 1 • distributionBetaTwo B)).1 /
        B.scale : ℝ) : ℂ) = ((x.1 / B.scale : ℝ) : ℂ) +
        (u 0 : ℂ) * (B.tau : ℂ) + (u 1 : ℂ) := by
    simp only [distributionBetaOne, distributionBetaTwo, Prod.fst_add,
      zsmul_eq_mul, Prod.fst_mul, Prod.fst_intCast]
    push_cast
    field_simp [hB.2.2.2.2.1.ne']
    ring
  rw [harg, modularPhi_shift_integer B.matrix hB.1]
  set m := distributionIntegerCoordinates B (distributionPeriodDifference B x) 0
  have hz : ((x.1 / B.scale : ℝ) : ℂ) ∉ modularPhiPseudoLattice (B.tau : ℂ) :=
    fun h => hI ((distributionPeriodPoints_first_lattice_iff B hB x hx).1 h)
  have hT : 0 < (etaDenom B.matrix (B.tau : ℂ)).re := by
    simpa [etaDenom, distributionPeriod] using lt_trans zero_lt_one hB.2.2.2.1
  have hcont (p q : ℤ) := (DistributionBasisValuesAux.nonlattice_continuous_ne_zero
    B.matrix hB.1 p q B.tau (lt_trans zero_lt_one hB.2.2.2.1) _ hz).1
  have hphase := DistributionBasisValuesAux.periodPoint_phase B hB x hx
  have heq := modularPhi_diagonal_index_fixedPoint B.matrix hB.1 m 0
    (B.matrix 1 1 * u 0 - B.matrix 1 0 * u 1) _ B.tau hB.2.2.1 hT
    (by simpa using hphase) (DistributionBasisValuesAux.nonlattice_phase_avoid _ _ hz m)
    (hcont _ _) (hcont _ _)
  convert heq using 2 <;> ring

/-- Descent for any representative, not merely Quotient.out. [RW26, p. 2, (2)]. -/
theorem distributionValue_mk (B : DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionValue B (distributionMk B x hx) = distributionBasisValue B x := by
  unfold distributionValue
  have hρ := distributionRepresentative_mk B hB x hx
  simpa using distributionBasisValue_periodic B hB x
    (distributionRepresentative B (distributionMk B x hx) - x) hx hρ

/-- Genuine quotient zero. [RW26, p. 3, (4), footnote 2]. -/
theorem distributionValue_zero (B : DistributionBasis) (hB : B.Valid) :
    distributionValue B 0 = (Real.sqrt (distributionPeriod B) : ℂ) := by
  have hzero : distributionMk B 0 (distributionPeriodPoints B).zero_mem = 0 := rfl
  rw [← hzero, distributionValue_mk B hB]
  exact distributionBasisValue_on_lattice B 0 (distributionLattice B).zero_mem

/-- All quotient coordinates are nonzero as complex numbers. [RW26, p. 6]. -/
theorem distributionValue_ne_zero (B : DistributionBasis) (hB : B.Valid)
    (g : DistributionGroup B) : distributionValue B g ≠ 0 := by
  exact distributionBasisValue_ne_zero B hB _ (Quotient.out g).property

/-- Admissibility and spectral data survive an actual admissible rebase. [RW26, p. 6, (17)]. -/
theorem distributionRebase_valid (B : DistributionBasis) (hB : B.Valid)
    (A : SL(2, ℤ)) (hA : DistributionPositiveChange B A) :
    (distributionRebase B A).Valid ∧
      distributionPeriod (distributionRebase B A) = distributionPeriod B ∧
      distributionConjugateTau (distributionRebase B A) =
        distributionRealMobius A (distributionConjugateTau B) := by
  simpa only [distributionRebase, DistributionBasisValuesAux.rebaseData,
    distributionRealMobius, DistributionBasisValuesAux.realMobius] using
    DistributionBasisValuesAux.rebase_valid B hB A hA.1 hA.2.1 hA.2.2

/-- Both embeddings refer to the same lattice and period-point set. [RW26, p. 6, (17)]. -/
theorem distributionRebase_lattice (B : DistributionBasis) (hB : B.Valid)
    (A : SL(2, ℤ)) (hA : DistributionPositiveChange B A) :
    distributionLattice (distributionRebase B A) = distributionLattice B ∧
      distributionPeriodPoints (distributionRebase B A) = distributionPeriodPoints B := by
  simpa only [distributionRebase, DistributionBasisValuesAux.rebaseData,
    distributionRealMobius, DistributionBasisValuesAux.realMobius] using
    DistributionBasisValuesAux.rebase_lattice B hB A hA.1 hA.2.1 hA.2.2

/-- μ from the actual η quotient. The proof uses `etaMultiplier_conjugate`; if c_A<0, exchange
bases, rather
than constructing an unsupported Φ_A. [RW26, p. 3]. -/
theorem distributionRebase_multiplier (B : DistributionBasis) (hB : B.Valid)
    (A : SL(2, ℤ)) (hA : DistributionPositiveChange B A) :
    etaMultiplier (distributionRebase B A).matrix = etaMultiplier B.matrix := by
  by_cases hc : 0 ≤ A 1 0
  · exact etaMultiplier_conjugate B.matrix A B.tau hB.1
      (DistributionBasisValuesAux.supported_of_nonneg A hc B.tau hA.1)
      hB.2.2.1 (lt_trans zero_lt_one hB.2.2.2.1) hA.1 hA.2.2
  · have hrev : distributionRebase (distributionRebase B A) A⁻¹ = B ∧
        DistributionPositiveChange (distributionRebase B A) A⁻¹ := by
      simpa only [DistributionPositiveChange, distributionRebase,
        DistributionBasisValuesAux.rebaseData, distributionRealMobius,
        DistributionBasisValuesAux.realMobius] using
        DistributionBasisValuesAux.rebase_inverse B hB A hA.1 hA.2.1 hA.2.2
    have hC := (distributionRebase_valid B hB A hA).1
    have hci : 0 < (A⁻¹) 1 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using
        neg_pos.mpr (lt_of_not_ge hc)
    have hμ := etaMultiplier_conjugate (distributionRebase B A).matrix A⁻¹
      (distributionRebase B A).tau hC.1 (Or.inl hci) hC.2.2.1
      (lt_trans zero_lt_one hC.2.2.2.1) hrev.2.1 hrev.2.2.2
    have hm := congrArg DistributionBasis.matrix hrev.1
    exact ((congrArg etaMultiplier hm).symm.trans hμ).symm

/-- Full actual value, including lattice classes, after admissible rebase. [RW26, p. 6, (17)]. -/
theorem distributionRebase_value (B : DistributionBasis) (hB : B.Valid)
    (A : SL(2, ℤ)) (hA : DistributionPositiveChange B A)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionBasisValue (distributionRebase B A) x = distributionBasisValue B x := by
  have hsupported (D : DistributionBasis) (hD : D.Valid)
      (P : SL(2, ℤ)) (hP : DistributionPositiveChange D P)
      (hs : ModularPhiSupported P)
      (y : ℝ × ℝ) (hy : y ∈ distributionPeriodPoints D) :
      distributionBasisValue (distributionRebase D P) y = distributionBasisValue D y := by
    let C := distributionRebase D P
    obtain ⟨hC, hperiod, _⟩ := distributionRebase_valid D hD P hP
    obtain ⟨hI, hpoints⟩ := distributionRebase_lattice D hD P hP
    change C.Valid at hC
    change distributionPeriod C = distributionPeriod D at hperiod
    change distributionLattice C = distributionLattice D at hI
    change distributionPeriodPoints C = distributionPeriodPoints D at hpoints
    change distributionBasisValue C y = _
    by_cases hyI : y ∈ distributionLattice D
    · rw [distributionBasisValue_on_lattice C y (by simpa only [hI] using hyI),
        distributionBasisValue_on_lattice D y hyI, hperiod]
    have hyC : y ∉ distributionLattice C := by simpa only [hI] using hyI
    rw [distributionBasisValue_off_lattice C y hyC,
      distributionBasisValue_off_lattice D y hyI]
    have hβ :
        distributionBetaOne C = P 0 0 • distributionBetaOne D + P 0 1 • distributionBetaTwo D ∧
        distributionBetaTwo C = P 1 0 • distributionBetaOne D + P 1 1 • distributionBetaTwo D := by
      simpa only [C, distributionRebase, DistributionBasisValuesAux.rebaseData,
        distributionRealMobius, DistributionBasisValuesAux.realMobius] using
        DistributionBasisValuesAux.rebase_beta D hD P hP.1 hP.2.1 hP.2.2
    have hdiff : distributionPeriodDifference C = distributionPeriodDifference D := by
      simp only [distributionPeriodDifference, hperiod]
    have hi := DistributionBasisValuesAux.integerCoordinates_change D C hD hC P
      hβ.1 hβ.2 (distributionPeriodDifference D y) hy
    have hm : distributionIntegerCoordinates C (distributionPeriodDifference C y) 0 =
        P 1 1 * distributionIntegerCoordinates D (distributionPeriodDifference D y) 0 -
          P 1 0 * distributionIntegerCoordinates D (distributionPeriodDifference D y) 1 := by
      rw [hdiff]
      exact congrFun hi 0
    have hz : ((y.1 / D.scale : ℝ) : ℂ) ∉ modularPhiPseudoLattice (D.tau : ℂ) :=
      fun h => hyI ((distributionPeriodPoints_first_lattice_iff D hD y hy).1 h)
    have hyP : y ∈ distributionPeriodPoints C := by simpa only [hpoints] using hy
    have hzC : ((y.1 / C.scale : ℝ) : ℂ) ∉ modularPhiPseudoLattice (C.tau : ℂ) :=
      fun h => hyC ((distributionPeriodPoints_first_lattice_iff C hC y hyP).1 h)
    have harg : ((y.1 / C.scale : ℝ) : ℂ) =
        ((y.1 / D.scale : ℝ) : ℂ) / etaDenom P (D.tau : ℂ) := by
      simp [C, distributionRebase, etaDenom, div_mul_eq_div_div]
    have htau : (C.tau : ℂ) = etaMobius P (D.tau : ℂ) := by
      simp [C, distributionRebase, distributionRealMobius, etaMobius, etaDenom]
    have hmatrix : C.matrix = P * D.matrix * P⁻¹ := rfl
    have hMval := (DistributionBasisValuesAux.nonlattice_continuous_ne_zero
      D.matrix hD.1 (distributionIntegerCoordinates D (distributionPeriodDifference D y) 0)
      0 D.tau (lt_trans zero_lt_one hD.2.2.2.1) _ hz).1
    have hCval := (DistributionBasisValuesAux.nonlattice_continuous_ne_zero
      C.matrix hC.1
      (P 1 1 * distributionIntegerCoordinates D (distributionPeriodDifference D y) 0 -
        P 1 0 * distributionIntegerCoordinates D (distributionPeriodDifference D y) 1)
      0 C.tau (lt_trans zero_lt_one hC.2.2.2.1) _ hzC).1
    have hAval := DistributionBasisValuesAux.constructed_zero_continuous_ne_zero P
      D.tau hP.1 _ (DistributionBasisValuesAux.nonlattice_add_integer _ _ hz
        (distributionIntegerCoordinates D (distributionPeriodDifference D y) 0)
        (distributionIntegerCoordinates D (distributionPeriodDifference D y) 1))
    rw [hm, harg, htau]
    exact modularPhi_basis_change_fixedPoint D.matrix P hD.1 hs hP.2.2 _ _ _ D.tau
      hD.2.2.1 (by simpa [etaDenom, distributionPeriod] using lt_trans zero_lt_one hD.2.2.2.1)
      (by simpa [etaDenom] using hP.1)
      (DistributionBasisValuesAux.periodPoint_argument D hD y hy) hMval
      (by simpa only [harg, htau, hmatrix] using hCval) hAval.1 hAval.2
  by_cases hc : 0 ≤ A 1 0
  · exact hsupported B hB A hA
      (DistributionBasisValuesAux.supported_of_nonneg A hc B.tau hA.1) x hx
  · have hrev : distributionRebase (distributionRebase B A) A⁻¹ = B ∧
        DistributionPositiveChange (distributionRebase B A) A⁻¹ := by
      simpa only [DistributionPositiveChange, distributionRebase,
        DistributionBasisValuesAux.rebaseData, distributionRealMobius,
        DistributionBasisValuesAux.realMobius] using
        DistributionBasisValuesAux.rebase_inverse B hB A hA.1 hA.2.1 hA.2.2
    have hci : 0 < (A⁻¹) 1 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using
        neg_pos.mpr (lt_of_not_ge hc)
    have hxC : x ∈ distributionPeriodPoints (distributionRebase B A) := by
      simpa only [(distributionRebase_lattice B hB A hA).2] using hx
    have heq := hsupported (distributionRebase B A)
      (distributionRebase_valid B hB A hA).1 A⁻¹ hrev.2 (Or.inl hci) x hxC
    rw [hrev.1] at heq
    exact heq.symm

/-- Comparing arbitrary presentations is a theorem, not stored data. Both positive embeddings force
determinant +1. Same period is essential. [RW26, p. 6, (17)]. -/
theorem distributionBasis_same_lattice_change (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid)
    (hε : distributionPeriod C = distributionPeriod B)
    (hI : distributionLattice C = distributionLattice B) :
    ∃ A : SL(2, ℤ), DistributionPositiveChange B A ∧ C = distributionRebase B A := by
  obtain ⟨A, hu, hv⟩ :=
    DistributionBasisValuesAux.sc_same_lattice_SL_rows B C hB hC hI
  have hm := DistributionBasisValuesAux.sc_change_conjugacy B C hB hC hε A hu hv
  have hv1 := congrArg Prod.fst hv
  have hv2 := congrArg Prod.snd hv
  have hu1 := congrArg Prod.fst hu
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at hv1 hv2 hu1
  simp only [distributionBetaOne, distributionBetaTwo, zsmul_eq_mul] at hv1 hv2 hu1
  have hscale : C.scale = B.scale * ((A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ)) := by
    nlinarith only [hv1]
  have hscaleConj : C.scaleConj = B.scaleConj *
      ((A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ)) := by
    nlinarith only [hv2]
  have hp : 0 < (A 1 0 : ℝ) * B.tau + (A 1 1 : ℝ) :=
    (mul_pos_iff_of_pos_left hB.2.2.2.2.1).1 (hscale ▸ hC.2.2.2.2.1)
  have hq : 0 < (A 1 0 : ℝ) * distributionConjugateTau B + (A 1 1 : ℝ) :=
    (mul_pos_iff_of_pos_left hB.2.2.2.2.2).1 (hscaleConj ▸ hC.2.2.2.2.2)
  have htau : C.tau = distributionRealMobius A B.tau := by
    dsimp [distributionRealMobius]
    apply (eq_div_iff hp.ne').2
    apply mul_left_cancel₀ hB.2.2.2.2.1.ne'
    rw [hscale] at hu1
    nlinarith only [hu1]
  have heq : C = distributionRebase B A := by
    cases C
    simp only [distributionRebase, DistributionBasis.mk.injEq]
    exact ⟨hm, htau, hscale, hscaleConj⟩
  refine ⟨A, ⟨hp, hq, ?_⟩, heq⟩
  rw [← hm]
  exact hC.1

/-- Presentation-independent μ, with the period explicitly matched. [RW26, p. 3]. -/
theorem distributionBasis_same_lattice_multiplier (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid)
    (hε : distributionPeriod C = distributionPeriod B)
    (hI : distributionLattice C = distributionLattice B) :
    etaMultiplier C.matrix = etaMultiplier B.matrix := by
  obtain ⟨A, hA, rfl⟩ := distributionBasis_same_lattice_change B C hB hC hε hI
  exact distributionRebase_multiplier B hB A hA

/-- E depends only on the actual lattice, period and real-pair class. [RW26, p. 2, (2)]. -/
theorem distributionBasis_same_lattice_value (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid)
    (hε : distributionPeriod C = distributionPeriod B)
    (hI : distributionLattice C = distributionLattice B)
    (x : ℝ × ℝ) (hx : x ∈ distributionPeriodPoints B) :
    distributionBasisValue C x = distributionBasisValue B x := by
  obtain ⟨A, hA, rfl⟩ := distributionBasis_same_lattice_change B C hB hC hε hI
  exact distributionRebase_value B hB A hA x hx

#print distributionBasisValue
#print distributionRebase
#check modularPhi_basis_change_fixedPoint
#check etaMultiplier_conjugate
#check distributionBasis_same_lattice_value

end SICLean.L4
