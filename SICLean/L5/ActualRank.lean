import SICLean.L5.ActualValueBridge

set_option autoImplicit false

/-!
# Rank-r chain, with the actual positive odd power

The matrix is beta^2*L. The period eta is a positive odd power of the base
unit, obtained in the statements below.
Sources: [RW26, p. 2, (2); p. 3, (3)--(4), footnote 2; (37), p. 20];
[RW-rec, Def. 1, (2), Prop. 7].
-/

noncomputable section
open scoped MatrixGroups

namespace SICLean.L5.ActualRank

/-- Algebraicity of the rank-r base unit, before Prop. 7. [RW26, p. 20]. -/
theorem unit_isAlgebraic (d r : ℕ) [Fact (L2r.Admissible d r)] :
    IsAlgebraic ℚ (L2r.unit d r : ℂ) := by
  rw [← (L4.rwL2rc_parameters d r).2.1]
  exact ActualField.tau_isAlgebraic (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2

def unitLift (d r : ℕ) [Fact (L2r.Admissible d r)] : Galois.Qbar :=
  Galois.algebraicLift (L2r.unit d r : ℂ) (unit_isAlgebraic d r)

abbrev baseField (d r : ℕ) [Fact (L2r.Admissible d r)] : IntermediateField ℚ Galois.Qbar :=
  ActualField.baseField (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2

def periodData (d r : ℕ) [Fact (L2r.Admissible d r)] : L3.PeriodData (baseField d r) :=
  ActualField.periodData (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2

def stableLattice (d r : ℕ) [Fact (L2r.Admissible d r)] :
    L3.StablePseudolattice (periodData d r) :=
  ActualLattice.stableLattice (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2

def labelEquiv (d r : ℕ) [Fact (L2r.Admissible d r)] :
    L2rc.RWGroup d r ≃+ L3.PseudolatticeGroup (periodData d r) (stableLattice d r) :=
  (L4.rwL2rcEquiv d r).trans
    (ActualLattice.labelEquiv (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2)

def valueLift (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2rc.RWGroup d r) : Galois.Qbar :=
  ActualValues.valueLift (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2
    (labelEquiv d r g)

/-- K = Q(t) in the fixed Qbar. [RW26, p. 20]; [RW-rec]. -/
theorem baseField_eq_adjoin (d r : ℕ) [Fact (L2r.Admissible d r)] :
    baseField d r = IntermediateField.adjoin ℚ ({unitLift d r} : Set Galois.Qbar) := by
  have ht : ActualField.tauLift (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 =
      unitLift d r := by
    apply Galois.embed.injective
    change Galois.embed (ActualField.tauLift (L4.rwL2rcPeriod d r)
      (L4.rwL2rc_admissible d r).2) = Galois.embed (unitLift d r)
    rw [ActualField.embed_tauLift, unitLift, Galois.embed_algebraicLift,
      (L4.rwL2rc_parameters d r).2.1]
  exact congrArg (fun t : Galois.Qbar =>
    IntermediateField.adjoin ℚ ({t} : Set Galois.Qbar)) ht

/-- The rank-r field has degree two, and the fixed embedding is real.
Same sources as `baseField_eq_adjoin`. -/
theorem baseField_isRealQuadratic (d r : ℕ) [Fact (L2r.Admissible d r)] :
    Galois.IsRealQuadratic (baseField d r) := by
  exact ActualField.baseField_isRealQuadratic
    (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2

/-- Equality in Qbar of the attracting generator and the base unit. [RW26, p. 20]. -/
theorem tau_eq_unitLift (d r : ℕ) [Fact (L2r.Admissible d r)] :
    (ActualField.tau (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 : Galois.Qbar) =
      unitLift d r := by
  change ActualField.tauLift (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 = _
  apply Galois.embed.injective
  change Galois.embed (ActualField.tauLift (L4.rwL2rcPeriod d r)
    (L4.rwL2rc_admissible d r).2) = Galois.embed (unitLift d r)
  rw [ActualField.embed_tauLift, unitLift, Galois.embed_algebraicLift,
    (L4.rwL2rc_parameters d r).2.1]

/-- The period eta and its positive odd exponent.
[RW26, p. 3, (4)]; [RW26, Prop. 8, p. 14]; [RW-rec, Def. 1].
The exponent is obtained in the statement. -/
theorem period_embeddings (d r : ℕ) [Fact (L2r.Admissible d r)] :
    (periodData d r).sigma₁ (periodData d r).epsilon = L2r.eta d r ∧
      (periodData d r).sigma₂ (periodData d r).epsilon = (L2r.eta d r)⁻¹ ∧
      Galois.embed ((periodData d r).epsilon : Galois.Qbar) = (L2r.eta d r : ℂ) ∧
      ∃ k : ℕ, 0 < k ∧ Odd k ∧ L2r.eta d r = L2r.unit d r ^ k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ActualField.sigma₁ _ _ (ActualField.epsilon _ _) = _
    rw [ActualField.sigma₁_epsilon, (L4.rwL2rc_parameters d r).2.2]
  · change ActualField.sigma₂ _ _ (ActualField.epsilon _ _) = _
    rw [ActualField.sigma₂_epsilon, ActualField.sigma₁_epsilon,
      (L4.rwL2rc_parameters d r).2.2]
  · change Galois.embed (ActualField.epsilon _ _ : Galois.Qbar) = _
    rw [ActualField.embed_epsilon, (L4.rwL2rc_parameters d r).2.2]
  · obtain ⟨k, hk, hodd, hpow⟩ := L4.rwL2rcPeriod_odd_power d r
    refine ⟨k, hk, hodd, ?_⟩
    rw [← (L4.rwL2rc_parameters d r).2.2, hpow,
      L4.specialValueEpsilon_pow _ (L4.rwL2rc_admissible d r).1 k hk]
    have ht : L4.specialValueTau (L4.rwL2rcBase d r) = L2r.unit d r := by
      unfold L4.specialValueTau L4.rwL2rcBase L2r.unit
      simp [L2r.alpha]
    have he : L4.specialValueEpsilon (L4.rwL2rcBase d r) = L2r.unit d r := by
      unfold L4.specialValueEpsilon
      rw [ht]
      norm_num [L4.rwL2rcBase, L2r.alpha]
    rw [he]

/-- The order of beta^2*L. [RW26, p. 3]; [RW-rec, Def. 1]. -/
theorem period_order (d r : ℕ) [Fact (L2r.Admissible d r)] :
    (periodData d r).N = L2r.groupOrder d r := by
  change (L4.specialValueOrder (L4.rwL2rcPeriod d r)).toNat = _
  rw [(L4.rwL2rc_parameters d r).1, Int.toNat_natCast]

/-- I = Z*t+Z in this field K. [RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem lattice_eq_span (d r : ℕ) [Fact (L2r.Admissible d r)] :
    (stableLattice d r).val = Submodule.span ℤ
      ({ActualField.tau (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2, 1} :
        Set (baseField d r)) := by
  exact ActualLattice.lattice_eq_span
    (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2

/-- Integer-row labels map to (m*t+n)/(eta^-1-1)+I.
[RW26, p. 2, (2); Lemma 2, p. 12]; [RW-rec, Def. 1]. -/
theorem labelEquiv_mk (d r : ℕ) [Fact (L2r.Admissible d r)] (u : ℤ × ℤ) :
    labelEquiv d r (L2rc.mk d r u) =
      L3.pseudolatticeMk (periodData d r) (stableLattice d r)
        (ActualLattice.rowPoint (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 u)
        (ActualLattice.rowPoint_mem (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 u) := by
  change ActualLattice.labelEquiv _ _ (L4.rwL2rcEquiv d r (L2rc.mk d r u)) = _
  rw [L4.rwL2rcEquiv_mk]
  exact ActualLattice.labelEquiv_mk
    (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 u

/-- The zero class is preserved in both directions.
[RW26, p. 3, footnote 2]; [RW-rec, Prop. 7]. -/
theorem labelEquiv_zero_iff (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2rc.RWGroup d r) :
    labelEquiv d r g = 0 ↔ g = 0 := by
  exact (labelEquiv d r).map_eq_zero_iff

/-- The intrinsic Gaussian agrees with the L2rc Gaussian on every class.
[RW26, p. 3, (3)]; [RW-rec, (2)]. -/
theorem gaussian (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2rc.RWGroup d r) :
    ActualValues.gaussian (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2 (labelEquiv d r g) =
      L2rc.gaussian d r g := by
  change ActualValues.gaussian _ _
    (ActualLattice.labelEquiv _ _ (L4.rwL2rcEquiv d r g)) = _
  rw [ActualValues.gaussian_label, L4.rwL2rc_gaussian]

/-- Both branches, including their values at zero.
[RW26, p. 2, (2); p. 3, (4), footnote 2]; [RW-rec, Def. 1]. -/
theorem values (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2rc.RWGroup d r) :
    L3.M72.value (periodData d r) (stableLattice d r) (labelEquiv d r g) =
        L4.rwL2rcPlus d r g ∧
      L3.M72.minusValue (periodData d r) (stableLattice d r) (labelEquiv d r g) =
        L4.rwL2rcMinus d r g := by
  exact ⟨ActualValues.value_label (L4.rwL2rcPeriod d r)
      (L4.rwL2rc_admissible d r).2 (L4.rwL2rcEquiv d r g),
    ActualValues.minusValue_label (L4.rwL2rcPeriod d r)
      (L4.rwL2rc_admissible d r).2 (L4.rwL2rcEquiv d r g)⟩

/-- The fixed embedding recovers the rank-r values. Same sources as `values`. -/
theorem embed_valueLift (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2rc.RWGroup d r) :
    Galois.embed (valueLift d r g) = L4.rwL2rcPlus d r g := by
  exact (ActualValues.embed_valueLift (L4.rwL2rcPeriod d r)
    (L4.rwL2rc_admissible d r).2 (labelEquiv d r g)).trans (values d r g).1

/-- Equality in Qbar used by the Prop. 7 specialization.
[RW26, p. 2, (2)]; [RW-rec, Prop. 7]. -/
theorem valueLift_eq_matrixLift (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2rc.RWGroup d r) :
    valueLift d r g = ActualValues.matrixLift (L4.rwL2rcPeriod d r)
      (L4.rwL2rc_admissible d r).2 (L4.rwL2rcEquiv d r g) := by
  exact ActualValues.valueLift_label (L4.rwL2rcPeriod d r)
    (L4.rwL2rc_admissible d r).2 (L4.rwL2rcEquiv d r g)

#check @L4.rwL2rc_parameters
#check @L4.rwL2rcPeriod_odd_power
#print baseField
#print periodData
#print labelEquiv

end SICLean.L5.ActualRank
