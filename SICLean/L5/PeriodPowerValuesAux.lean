import SICLean.L5.PeriodPowerMatrix

set_option autoImplicit false

noncomputable section
open scoped MatrixGroups

namespace SICLean.L5.PeriodPowerValuesAux
open L3

lemma sqrt_power (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    Real.sqrt (t ^ r) = Real.sqrt t ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ', Real.sqrt_mul ht, ih, pow_succ']

def powerBasis (B : L4.DistributionBasis) (r : ℕ) : L4.DistributionBasis :=
  { B with matrix := B.matrix ^ r }

lemma powerBasis_period (B : L4.DistributionBasis) (hB : B.Valid)
    (r : ℕ) (hr : 0 < r) :
    L4.distributionPeriod (powerBasis B r) = L4.distributionPeriod B ^ r := by
  have hp := M72.basis_parameters B hB
  change ((B.matrix ^ r) 1 0 : ℝ) * B.tau + ((B.matrix ^ r) 1 1 : ℝ) = _
  rw [hp.2.1, ← L4.specialValueTau_pow B.matrix hp.1 r hr]
  exact (L4.specialValueEpsilon_pow B.matrix hp.1 r hr).trans
    (congrArg (fun t : ℝ => t ^ r) hp.2.2.symm)

lemma powerBasis_valid (B : L4.DistributionBasis) (hB : B.Valid)
    (r : ℕ) (hr : 0 < r) : (powerBasis B r).Valid := by
  have hp := M72.basis_parameters B hB
  have hA := L4.specialValue_pow_admissible B.matrix hp.1 r hr
  refine ⟨hA.1, hA.2, ?_, ?_, hB.2.2.2.2.1, hB.2.2.2.2.2⟩
  · change L4.etaMobius (B.matrix ^ r) (B.tau : ℂ) = (B.tau : ℂ)
    rw [hp.2.1, ← L4.specialValueTau_pow B.matrix hp.1 r hr]
    exact L4.specialValueTau_fixedPoint _ hA
  · rw [powerBasis_period B hB r hr]
    exact one_lt_pow₀ hB.2.2.2.1 (Nat.ne_of_gt hr)

lemma denom_ofReal (A : SL(2, ℤ)) (t : ℝ) :
    L4.etaDenom A (t : ℂ) = (((A 1 0 : ℝ) * t + (A 1 1 : ℝ) : ℝ) : ℂ) := by
  simp [L4.etaDenom]

lemma powerBasis_conjugateTau (B : L4.DistributionBasis) (hB : B.Valid)
    (r : ℕ) (hr : 0 < r) :
    L4.distributionConjugateTau (powerBasis B r) = L4.distributionConjugateTau B := by
  have hpos : 0 < (L4.distributionPeriod B)⁻¹ :=
    inv_pos.mpr (L4.dBasis_period_pos B hB)
  have hden : L4.etaDenom B.matrix (L4.distributionConjugateTau B : ℂ) =
      (((L4.distributionPeriod B)⁻¹ : ℝ) : ℂ) := by
    rw [denom_ofReal, L4.dBasis_conj_period B hB]
  have hquad := L4.dl_conj_quad B.matrix B.tau
    (ne_of_gt (L4.dBasis_c_pos B hB)) (L4.dBasis_quad B hB)
  change (B.matrix 1 0 : ℝ) * L4.distributionConjugateTau B ^ 2 +
    ((B.matrix 1 1 : ℝ) - (B.matrix 0 0 : ℝ)) *
      L4.distributionConjugateTau B - (B.matrix 0 1 : ℝ) = 0 at hquad
  have hfix : L4.etaMobius B.matrix (L4.distributionConjugateTau B : ℂ) =
      (L4.distributionConjugateTau B : ℂ) := by
    apply (div_eq_iff (show L4.etaDenom B.matrix
      (L4.distributionConjugateTau B : ℂ) ≠ 0 by
        rw [hden]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))).mpr
    rw [denom_ofReal]
    exact_mod_cast (show (B.matrix 0 0 : ℝ) * L4.distributionConjugateTau B +
        (B.matrix 0 1 : ℝ) = L4.distributionConjugateTau B *
          ((B.matrix 1 0 : ℝ) * L4.distributionConjugateTau B +
            (B.matrix 1 1 : ℝ)) by nlinarith [hquad])
  have hp := L4.ModularCocycleMatrixAux.pow_fixedPoint B.matrix
    (L4.distributionConjugateTau B) hfix (by simpa only [hden, Complex.ofReal_re] using hpos) r
  have hreal := congrArg Complex.re hp.2.1
  rw [denom_ofReal, hden, ← Complex.ofReal_pow] at hreal
  simp only [Complex.ofReal_re] at hreal
  have hnew := L4.dBasis_conj_period (powerBasis B r) (powerBasis_valid B hB r hr)
  rw [powerBasis_period B hB r hr, ← inv_pow] at hnew
  have hc : (((B.matrix ^ r) 1 0 : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (powerBasis_valid B hB r hr).1
  apply mul_left_cancel₀ hc
  change ((B.matrix ^ r) 1 0 : ℝ) * L4.distributionConjugateTau (powerBasis B r) +
    ((B.matrix ^ r) 1 1 : ℝ) = _ at hnew
  linarith

lemma powerBasis_lattice (B : L4.DistributionBasis) (hB : B.Valid)
    (r : ℕ) (hr : 0 < r) :
    L4.distributionLattice (powerBasis B r) = L4.distributionLattice B := by
  have hbeta : L4.distributionBetaOne (powerBasis B r) = L4.distributionBetaOne B := by
    simp only [L4.distributionBetaOne, powerBasis_conjugateTau B hB r hr]
    rfl
  simp only [L4.distributionLattice, hbeta]
  rfl

universe u
variable {K : Type u} [Field K] [NumberField K]

lemma rowPoint_argument (B : L4.DistributionBasis) (hB : B.Valid) (v : ℤ × ℤ) :
    (((L4.distributionRowPoint B v).1 / B.scale : ℝ) : ℂ) =
      L4.specialValueArgument B.matrix v := by
  rw [L4.distributionRowPoint_specialArgument B hB v]
  simp only [L4.specialValueArgument, (M72.basis_parameters B hB).2.1]

lemma rowPoint_exists (B : L4.DistributionBasis) (hB : B.Valid)
    (x : ℝ × ℝ) (hx : x ∈ L4.distributionPeriodPoints B) :
    ∃ v : ℤ × ℤ, L4.distributionRowPoint B v = x := by
  obtain ⟨w, hw⟩ := (L4.distributionLattice_mem_iff B
    (L4.distributionPeriodDifference B x)).mp hx
  refine ⟨(w 0, w 1), ?_⟩
  apply L4.distributionPeriodDifference_injective B hB
  rw [L4.distributionRowPoint_periodDifference B hB, hw]
  simp [Int.cast_smul_eq_zsmul ℝ]

/-- Equality of the first embedding suffices because each row point is an actual point of the same
arithmetic field. -/
lemma rowPoint_eq_embedding (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (v : ℤ × ℤ) (x : K)
    (hfirst : (L4.distributionRowPoint B v).1 = P.sigma₁ x) :
    L4.distributionRowPoint B v = pseudolatticeEmbedding P x := by
  have hmem := L4.distributionRowPoint_mem B hB.1 v
  rw [pseudolatticePresentation_periodPoints P I B hB] at hmem
  obtain ⟨y, _hy, hemb⟩ := hmem
  have hxy : y = x := P.sigma₁.injective (by
    have hy := congrArg Prod.fst hemb
    change P.sigma₁ y = (L4.distributionRowPoint B v).1 at hy
    exact hy.trans hfirst)
  simpa only [hxy] using hemb.symm

lemma basisValue_eq_specialValue (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (v : ℤ × ℤ) (x : K) (hemb : L4.distributionRowPoint B v = pseudolatticeEmbedding P x) :
    M72.basisValue P B x =
      L4.specialValuePlus B.matrix (M72.basis_parameters B hB.1).1
        (L4.specialValueMk B.matrix v) := by
  have h := M72.distributionPlus_eq_specialPlus B hB.1 (L4.specialValueMk B.matrix v)
  rw [M72.rowEquiv_mk, L4.distributionValue_mk B hB.1] at h
  change L4.distributionBasisValue B (pseudolatticeEmbedding P x) = _
  rwa [hemb] at h

lemma basisValue_power (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (r : ℕ) (hr : 0 < r)
    (hBr : PseudolatticePresentation (PeriodPower.powPeriod P r hr)
      (PeriodPower.powLattice P I r hr) (powerBasis B r))
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    M72.basisValue (PeriodPower.powPeriod P r hr) (powerBasis B r) x =
      M72.basisValue P B x ^ r := by
  obtain ⟨v, hv⟩ := rowPoint_exists B hB.1 (pseudolatticeEmbedding P x)
    (pseudolatticePresentation_point_mem P I B hB x hx)
  have harg := PeriodPowerMatrix.specialValueArgument_powerRow B.matrix
    (M72.basis_parameters B hB.1).1 r hr v
  change L4.specialValueArgument (powerBasis B r).matrix
    (PeriodPowerMatrix.powerRow B.matrix r v) = _ at harg
  rw [← rowPoint_argument (powerBasis B r) hBr.1, ← rowPoint_argument B hB.1, hv] at harg
  have hfirst : (L4.distributionRowPoint (powerBasis B r)
      (PeriodPowerMatrix.powerRow B.matrix r v)).1 = P.sigma₁ x := by
    have hreal := Complex.ofReal_injective harg
    change _ / B.scale = P.sigma₁ x / B.scale at hreal
    exact (div_left_inj' (ne_of_gt hB.1.2.2.2.2.1)).mp hreal
  have hrow := rowPoint_eq_embedding _ _ _ hBr _ x hfirst
  rw [basisValue_eq_specialValue _ _ _ hBr _ _ hrow,
    basisValue_eq_specialValue P I B hB v x hv]
  exact (PeriodPowerMatrix.inclusion_mk B.matrix
    (M72.basis_parameters B hB.1).1 r hr v ▸
      PeriodPowerMatrix.specialValuePlus_pow B.matrix
        (M72.basis_parameters B hB.1).1 r hr (L4.specialValueMk B.matrix v))

lemma basisValue_base_invariant (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (r : ℕ) (hr : 0 < r)
    (hBr : PseudolatticePresentation (PeriodPower.powPeriod P r hr)
      (PeriodPower.powLattice P I r hr) (powerBasis B r))
    (x : K)
    (hx : x ∈ pseudolatticePeriodPoints (PeriodPower.powPeriod P r hr)
      (PeriodPower.powLattice P I r hr)) :
    M72.basisValue (PeriodPower.powPeriod P r hr) (powerBasis B r) (P.epsilon * x) =
      M72.basisValue (PeriodPower.powPeriod P r hr) (powerBasis B r) x := by
  obtain ⟨v, hv⟩ := rowPoint_exists (powerBasis B r) hBr.1
    (pseudolatticeEmbedding (PeriodPower.powPeriod P r hr) x)
    (pseudolatticePresentation_point_mem _ _ _ hBr x hx)
  have harg := L4.specialValueArgument_base B.matrix
    (M72.basis_parameters B hB.1).1 r hr v
  change L4.specialValueArgument (powerBasis B r).matrix
    (L2r.rowAction (B.matrix : Matrix (Fin 2) (Fin 2) ℤ) v) =
      (L4.specialValueEpsilon B.matrix : ℂ) *
        L4.specialValueArgument (powerBasis B r).matrix v at harg
  rw [← rowPoint_argument (powerBasis B r) hBr.1,
    ← rowPoint_argument (powerBasis B r) hBr.1, hv,
    ← Complex.ofReal_mul] at harg
  have hfirst : (L4.distributionRowPoint (powerBasis B r)
      (L2r.rowAction (B.matrix : Matrix (Fin 2) (Fin 2) ℤ) v)).1 =
        P.sigma₁ (P.epsilon * x) := by
    apply (div_left_inj' (ne_of_gt hB.1.2.2.2.2.1)).mp
    have hreal := Complex.ofReal_injective harg
    change _ / B.scale = L4.specialValueEpsilon B.matrix * (P.sigma₁ x / B.scale) at hreal
    rw [hreal, map_mul, ← hB.2.1, (M72.basis_parameters B hB.1).2.2]
    ring
  have hrow := rowPoint_eq_embedding _ _ _ hBr _ (P.epsilon * x) hfirst
  rw [basisValue_eq_specialValue _ _ _ hBr _ _ hrow,
    basisValue_eq_specialValue _ _ _ hBr _ _ hv]
  have h := L4.specialValuePlus_base_invariant B.matrix
    (M72.basis_parameters B hB.1).1 r hr (L4.specialValueMk (B.matrix ^ r) v)
  rw [L4.specialValueUnitAction_mk] at h
  exact h.symm

end SICLean.L5.PeriodPowerValuesAux
