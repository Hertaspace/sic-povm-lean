import SICLean.L5.PeriodPowerMatrix
import SICLean.L5.PeriodPowerValuesAux

set_option autoImplicit false

/-!
# Actual arithmetic values for positive power periods

[RW-rec, Prop. 2(8)--(9)], p. 4, Appendix A pp. 19--20. [RW26, Prop. 8, p. 2, p. 3, p.
6, p. 14, (2), (4), (17)--(18), footnote 2]. No separate E/phi/mu is introduced:
basisValue/value/minusValue are the existing M72 definitions. The multiplier is the
etaMultiplier of the already chosen actual basis. Rechoosing a basis at each period is
handled by theorems, not by a definition enforcing compatibility.
-/

noncomputable section
open scoped MatrixGroups BigOperators Classical

namespace SICLean.L5.PeriodPower
open L3

universe u
variable {K : Type u} [Field K] [NumberField K]

def powBasis (B : L4.DistributionBasis) (r : ℕ) : L4.DistributionBasis :=
  { B with matrix := B.matrix ^ r }

def root (P : PeriodData K) : ℂ := (Real.sqrt (P.sigma₁ P.epsilon) : ℂ)

def multiplier (P : PeriodData K) (I : StablePseudolattice P) : ℂ :=
  L4.etaMultiplier (M72.chosenBasis P I).matrix

/-- [RW-rec, Def. 1, p. 3, p. 4, (8)]; [RW26, p. 3, (4)]. Zero classes use the positive real root.
-/
theorem root_power (P : PeriodData K) (r : ℕ) (hr : 0 < r) :
    root (powPeriod P r hr) = root P ^ r := by
  unfold root
  change (Real.sqrt (P.sigma₁ (P.epsilon ^ r)) : ℂ) = _
  rw [map_pow, PeriodPowerValuesAux.sqrt_power _
      (le_of_lt (lt_trans zero_lt_one P.epsilon_gt_one)),
    Complex.ofReal_pow]

/-- [RW-rec, p. 4, p. 20]; [RW26, p. 14]. Basis bridge: the original two embedding scales remain
positive. -/
theorem powBasis_valid (B : L4.DistributionBasis) (hB : B.Valid)
    (r : ℕ) (hr : 0 < r) : (powBasis B r).Valid := by
  exact PeriodPowerValuesAux.powerBasis_valid B hB r hr

/-- Both fixed points are unchanged. distributionConjugateTau depends on the matrix, so this is not
rfl. -/
theorem powBasis_lattice (B : L4.DistributionBasis) (hB : B.Valid)
    (r : ℕ) (hr : 0 < r) :
    L4.distributionLattice (powBasis B r) = L4.distributionLattice B := by
  exact PeriodPowerValuesAux.powerBasis_lattice B hB r hr

/-- [RW-rec, p. 4, (8)]; [RW26, Prop. 8, p. 14] automorphy factor. -/
theorem powBasis_period (B : L4.DistributionBasis) (hB : B.Valid)
    (r : ℕ) (hr : 0 < r) :
    L4.distributionPeriod (powBasis B r) = L4.distributionPeriod B ^ r := by
  exact PeriodPowerValuesAux.powerBasis_period B hB r hr

/-- [RW-rec, p. 3, p. 4]; [RW26, p. 2]. Same field, embeddings and lattice. -/
theorem powBasis_presentation (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (r : ℕ) (hr : 0 < r) :
    PseudolatticePresentation (powPeriod P r hr) (powLattice P I r hr) (powBasis B r) := by
  refine ⟨powBasis_valid B hB.1 r hr, ?_, ?_⟩
  · rw [powBasis_period B hB.1 r hr, hB.2.1]
    exact (map_pow P.sigma₁ P.epsilon r).symm
  · rw [powBasis_lattice B hB.1 r hr]
    exact hB.2.2

/-- [RW-rec, Def. 1, p. 3, p. 4, (8)]; [RW26, p. 3, (4)]. This real statement also covers r=0
without constructing PeriodData. -/
theorem sqrt_period_pow (P : PeriodData K) (r : ℕ) :
    Real.sqrt (P.sigma₁ (P.epsilon ^ r)) = Real.sqrt (P.sigma₁ P.epsilon) ^ r := by
  rw [map_pow]
  exact PeriodPowerValuesAux.sqrt_power _ (le_of_lt (lt_trans zero_lt_one P.epsilon_gt_one)) r

/-- [RW-rec, p. 4, (8)]; [RW26, Prop. 8, p. 6, p. 14, (18)]. Only old-period points are in this
assertion; the origin is included. -/
theorem basisValue_pow (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (r : ℕ) (hr : 0 < r) (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    M72.basisValue (powPeriod P r hr) (powBasis B r) x = M72.basisValue P B x ^ r := by
  exact PeriodPowerValuesAux.basisValue_power P I B hB r hr
    (powBasis_presentation P I B hB r hr) x hx

/-- [RW-rec, Def. 1, p. 4, p. 3, (8)]; [RW26, p. 3, (4)]. Explicit zero export for downstream
normalization. -/
theorem value_pow_zero (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) :
    M72.value (powPeriod P r hr) (powLattice P I r hr) 0 = M72.value P I 0 ^ r := by
  rw [M72.value_zero, M72.value_zero]
  change (Real.sqrt (P.sigma₁ (P.epsilon ^ r)) : ℂ) = _
  rw [sqrt_period_pow, Complex.ofReal_pow]

/-- [RW-rec, Prop. 2(8), p. 4]; [RW26, Prop. 8, p. 14]. Main period-power export on the canonical
embedding of the old group. -/
theorem value_pow (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) (g : PseudolatticeGroup P I) :
    M72.value (powPeriod P r hr) (powLattice P I r hr) (periodPowerInclusion P I r hr g) =
      M72.value P I g ^ r := by
  refine Quotient.inductionOn g ?_
  intro x
  change M72.value (powPeriod P r hr) (powLattice P I r hr)
    (periodPowerInclusion P I r hr (pseudolatticeMk P I x.val x.property)) =
      M72.value P I (pseudolatticeMk P I x.val x.property) ^ r
  rw [periodPowerInclusion_mk,
    M72.value_mk _ _ _ (powBasis_presentation P I (M72.chosenBasis P I)
      (M72.chosenBasis_spec P I) r hr),
    M72.value_mk P I _ (M72.chosenBasis_spec P I)]
  exact basisValue_pow P I _ (M72.chosenBasis_spec P I) r hr x.val x.property

/-- Same sources and [RW26, p. 3, footnote 2]; minus uses inverse positive root. -/
theorem minusValue_pow (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) (g : PseudolatticeGroup P I) :
    M72.minusValue (powPeriod P r hr) (powLattice P I r hr) (periodPowerInclusion P I r hr g) =
      M72.minusValue P I g ^ r := by
  by_cases hg : g = 0
  · subst g
    simp only [map_zero, M72.minusValue, ite_true]
    change (Real.sqrt (P.sigma₁ (P.epsilon ^ r)) : ℂ)⁻¹ = _
    rw [sqrt_period_pow, Complex.ofReal_pow, inv_pow]
  · have hpow : periodPowerInclusion P I r hr g ≠ 0 := by
      intro h
      exact hg (periodPowerInclusion_injective P I r hr (h.trans (map_zero _).symm))
    simp only [M72.minusValue, if_neg hg, if_neg hpow]
    exact value_pow P I r hr g

/-- [RW-rec, Prop. 2(9), p. 4]; [RW26, Prop. 8, p. 14]. The base unit acts on the whole
larger-period group. -/
theorem value_epsilon_invariant (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r)
    (g : PseudolatticeGroup (powPeriod P r hr) (powLattice P I r hr)) :
    M72.value (powPeriod P r hr) (powLattice P I r hr) (epsilonAction P I r hr g) =
      M72.value (powPeriod P r hr) (powLattice P I r hr) g := by
  refine Quotient.inductionOn g ?_
  intro x
  change M72.value (powPeriod P r hr) (powLattice P I r hr)
    (epsilonAction P I r hr
      (pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr) x.val x.property)) =
    M72.value (powPeriod P r hr) (powLattice P I r hr)
      (pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr) x.val x.property)
  rw [epsilonAction_mk,
    M72.value_mk _ _ _ (powBasis_presentation P I (M72.chosenBasis P I)
      (M72.chosenBasis_spec P I) r hr),
    M72.value_mk _ _ _ (powBasis_presentation P I (M72.chosenBasis P I)
      (M72.chosenBasis_spec P I) r hr)]
  exact PeriodPowerValuesAux.basisValue_base_invariant P I _ (M72.chosenBasis_spec P I)
    r hr (powBasis_presentation P I _ (M72.chosenBasis_spec P I) r hr) x.val x.property

/-- [RW-rec, Def. 1, p. 3]; [RW26, p. 3] multiplier convention. No arbitrary phase is chosen. -/
theorem multiplier_presentation (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B) :
    multiplier P I = L4.etaMultiplier B.matrix := by
  exact M72.presentation_multiplier P I B (M72.chosenBasis P I) hB (M72.chosenBasis_spec P I)

/-- [RW-rec, Appendix A, pp. 19--20]; [RW26, p. 6, (17)]. An actual eta-multiplier power, including
the positive sqrt branch. -/
theorem multiplier_pow (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) :
    multiplier (powPeriod P r hr) (powLattice P I r hr) = multiplier P I ^ r := by
  rw [multiplier_presentation _ _ _
    (powBasis_presentation P I (M72.chosenBasis P I) (M72.chosenBasis_spec P I) r hr)]
  exact PeriodPowerMatrix.etaMultiplier_pow _
    (M72.basis_parameters _ (M72.chosenBasis_spec P I).1).1 r hr

#print powBasis
#print root
#print multiplier
#check @L3.M72.value
#check @L4.phiExtended
#check @L4.etaMultiplier
#check value_pow
#check value_epsilon_invariant

end SICLean.L5.PeriodPower
