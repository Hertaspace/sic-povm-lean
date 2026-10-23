import SICLean.L5.ActualValueBridge

set_option autoImplicit false

/-!
# Original chain, with period t^3

Every object is specialized from the literal alpha^3 matrix. The base unit t
is the generator, and the period is t^3.
Sources: [RW26, p. 20, (37); p. 3, (2)--(4), footnote 2];
[RW-rec, Def. 1, (2), Prop. 7].
-/

noncomputable section
open scoped MatrixGroups

namespace SICLean.L5.ActualOriginal

/-- Independent algebraicity of the specified base unit. [RW26, p. 20]. -/
theorem unit_isAlgebraic (M : ℕ) [Fact (4 ≤ M)] :
    IsAlgebraic ℚ (L2a.epsilon M : ℂ) := by
  simpa only [(L4.rwL2c_parameters M).2.1] using
    ActualField.tau_isAlgebraic (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2

def unitLift (M : ℕ) [Fact (4 ≤ M)] : Galois.Qbar :=
  Galois.algebraicLift (L2a.epsilon M : ℂ) (unit_isAlgebraic M)

abbrev baseField (M : ℕ) [Fact (4 ≤ M)] : IntermediateField ℚ Galois.Qbar :=
  ActualField.baseField (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2

def periodData (M : ℕ) [Fact (4 ≤ M)] : L3.PeriodData (baseField M) :=
  ActualField.periodData (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2

def stableLattice (M : ℕ) [Fact (4 ≤ M)] : L3.StablePseudolattice (periodData M) :=
  ActualLattice.stableLattice (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2

def labelEquiv (M : ℕ) [Fact (4 ≤ M)] :
    L2c.RWGroup M ≃+ L3.PseudolatticeGroup (periodData M) (stableLattice M) :=
  (L4.rwL2cEquiv M).trans
    (ActualLattice.labelEquiv (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2)

def valueLift (M : ℕ) [Fact (4 ≤ M)] (g : L2c.RWGroup M) : Galois.Qbar :=
  ActualValues.valueLift (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 (labelEquiv M g)

/-- K is Q(t), hence Q(sqrt((M+1)(M-3))), in the fixed Qbar.
[RW26, p. 20]; [RW-rec]. The generator is identified by `L4.rwL2c_parameters`. -/
theorem baseField_eq_adjoin (M : ℕ) [Fact (4 ≤ M)] :
    baseField M = IntermediateField.adjoin ℚ ({unitLift M} : Set Galois.Qbar) := by
  unfold baseField ActualField.baseField ActualField.tauLift unitLift
  simp only [(L4.rwL2c_parameters M).2.1]

/-- The actual field has degree two, and the fixed embedding is real.
Same sources as `baseField_eq_adjoin`. -/
theorem baseField_isRealQuadratic (M : ℕ) [Fact (4 ≤ M)] :
    Galois.IsRealQuadratic (baseField M) := by
  exact ActualField.baseField_isRealQuadratic
    (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2

/-- Equality of the two generators in Qbar, before any automorphism.
[RW26, p. 20]. The identification is `L4.rwL2c_parameters`. -/
theorem tau_eq_unitLift (M : ℕ) [Fact (4 ≤ M)] :
    (ActualField.tau (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 : Galois.Qbar) =
      unitLift M := by
  change ActualField.tauLift (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 = unitLift M
  unfold ActualField.tauLift unitLift
  simp only [(L4.rwL2c_parameters M).2.1]

/-- The period is t^3 and its conjugate is t^(-3).
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem period_embeddings (M : ℕ) [Fact (4 ≤ M)] :
    (periodData M).sigma₁ (periodData M).epsilon = L2a.epsilon M ^ 3 ∧
      (periodData M).sigma₂ (periodData M).epsilon = (L2a.epsilon M ^ 3)⁻¹ ∧
      Galois.embed ((periodData M).epsilon : Galois.Qbar) =
        ((L2a.epsilon M ^ 3 : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · change ActualField.sigma₁ _ _ (ActualField.epsilon _ _) = _
    rw [ActualField.sigma₁_epsilon, (L4.rwL2c_parameters M).2.2]
  · change ActualField.sigma₂ _ _ (ActualField.epsilon _ _) = _
    rw [ActualField.sigma₂_epsilon, ActualField.sigma₁_epsilon,
      (L4.rwL2c_parameters M).2.2]
  · change Galois.embed (ActualField.epsilon _ _ : Galois.Qbar) = _
    rw [ActualField.embed_epsilon, (L4.rwL2c_parameters M).2.2]

/-- The order is the order of alpha^3. [RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem period_order (M : ℕ) [Fact (4 ≤ M)] :
    (periodData M).N = L2b.groupOrder M := by
  change (L4.specialValueOrder (L4.rwL2cPeriod M)).toNat = L2b.groupOrder M
  simp only [(L4.rwL2c_parameters M).1, Int.toNat_natCast]

/-- I = Z*t+Z inside this field K. [RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem lattice_eq_span (M : ℕ) [Fact (4 ≤ M)] :
    (stableLattice M).val = Submodule.span ℤ
      ({ActualField.tau (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2, 1} : Set (baseField M)) := by
  exact ActualLattice.lattice_eq_span (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2

/-- Row and Smith labels go to (m*t+n)/(t^(-3)-1)+I.
[RW26, p. 2, (2); Lemma 2, p. 12; p. 20]; [RW-rec, Def. 1]. -/
theorem labelEquiv_mk (M : ℕ) [Fact (4 ≤ M)] (u : ℤ × ℤ) :
    labelEquiv M (L2c.mk M u) =
      L3.pseudolatticeMk (periodData M) (stableLattice M)
        (ActualLattice.rowPoint (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 u)
        (ActualLattice.rowPoint_mem (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 u) := by
  change ActualLattice.labelEquiv (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2
    (L4.rwL2cEquiv M (L2c.mk M u)) = _
  rw [L4.rwL2cEquiv_mk]
  exact ActualLattice.labelEquiv_mk (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 u

/-- The class excluded by Prop. 7 is the zero class.
[RW26, p. 3, footnote 2]; [RW-rec, Prop. 7]. -/
theorem labelEquiv_zero_iff (M : ℕ) [Fact (4 ≤ M)] (g : L2c.RWGroup M) :
    labelEquiv M g = 0 ↔ g = 0 := by
  exact (labelEquiv M).map_eq_zero_iff

/-- The intrinsic Gaussian agrees with the L2c Gaussian on every class.
[RW26, p. 3, (3); p. 20]; [RW-rec, (2)]. -/
theorem gaussian (M : ℕ) [Fact (4 ≤ M)] (g : L2c.RWGroup M) :
    ActualValues.gaussian (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2 (labelEquiv M g) =
      L2c.gaussian M g := by
  change ActualValues.gaussian (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2
    (ActualLattice.labelEquiv (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2
      (L4.rwL2cEquiv M g)) = _
  rw [ActualValues.gaussian_label, L4.rwL2c_gaussian]

/-- Both branches, with their prescribed origins.
[RW26, p. 2, (2); p. 3, (4), footnote 2]; [RW-rec, Def. 1]. -/
theorem values (M : ℕ) [Fact (4 ≤ M)] (g : L2c.RWGroup M) :
    L3.M72.value (periodData M) (stableLattice M) (labelEquiv M g) = L4.rwL2cPlus M g ∧
      L3.M72.minusValue (periodData M) (stableLattice M) (labelEquiv M g) = L4.rwL2cMinus M g := by
  constructor
  · exact ActualValues.value_label (L4.rwL2cPeriod M)
      (L4.rwL2c_admissible M).2 (L4.rwL2cEquiv M g)
  · exact ActualValues.minusValue_label (L4.rwL2cPeriod M)
      (L4.rwL2c_admissible M).2 (L4.rwL2cEquiv M g)

/-- The fixed embedding sends the preimage to the original value.
Same sources as `values`. -/
theorem embed_valueLift (M : ℕ) [Fact (4 ≤ M)] (g : L2c.RWGroup M) :
    Galois.embed (valueLift M g) = L4.rwL2cPlus M g := by
  exact (ActualValues.embed_valueLift (L4.rwL2cPeriod M)
    (L4.rwL2c_admissible M).2 (labelEquiv M g)).trans (values M g).1

/-- Equality in Qbar used by the Prop. 7 specialization.
[RW26, p. 2, (2)]; [RW-rec, Prop. 7]. -/
theorem valueLift_eq_matrixLift (M : ℕ) [Fact (4 ≤ M)] (g : L2c.RWGroup M) :
    valueLift M g = ActualValues.matrixLift (L4.rwL2cPeriod M)
      (L4.rwL2c_admissible M).2 (L4.rwL2cEquiv M g) := by
  exact ActualValues.valueLift_label (L4.rwL2cPeriod M)
    (L4.rwL2c_admissible M).2 (L4.rwL2cEquiv M g)

#check @L4.rwL2c_parameters
#print baseField
#print periodData
#print labelEquiv

end SICLean.L5.ActualOriginal
