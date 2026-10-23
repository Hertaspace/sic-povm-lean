import SICLean.L5.ActualQuadraticField

set_option autoImplicit false

/-!
# The actual lattice and the row-label dictionary

The concrete matrix lattice and quotient equivalence are those of `M72`.
Their generator is identified with `ActualField.tau`.
The isomorphism is the explicit label map on representatives.

Sources: [RW26, pp. 2--3, (2)--(3); Lemma 2, p. 12; (37), p. 20];
[RW-rec, Def. 1]. The lattice, presentation, and label map are
`M72.matrixLattice`, `matrixStableLattice`, `matrixPresentation`, and `matrixToK`.
-/

noncomputable section
open scoped MatrixGroups

namespace SICLean.L5.ActualLattice

open ActualField

/-- Equality of the field elements themselves.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem matrixTauK_eq_tau (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    L3.M72.matrixTauK (periodData M hM) M = tau M hM := by
  have hc : (M 1 0 : baseField M hM) ≠ 0 := by
    exact_mod_cast ne_of_gt hM.1
  change ((M 1 0 : baseField M hM) * tau M hM + M 1 1 - M 1 1) /
    (M 1 0 : baseField M hM) = tau M hM
  rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hc]

def lattice (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    Submodule ℤ (baseField M hM) :=
  L3.M72.matrixLattice (periodData M hM) M

/-- The pseudolattice is Z*tau+Z. [RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem lattice_eq_span (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    lattice M hM = Submodule.span ℤ ({tau M hM, 1} : Set (baseField M hM)) := by
  unfold lattice L3.M72.matrixLattice
  rw [matrixTauK_eq_tau]

/-- The lattice has full rank two. [RW26, p. 20]; [RW-rec]. -/
theorem lattice_isLattice (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    Submodule.IsLattice ℚ (lattice M hM) := by
  exact L3.M72.matrixLattice_isLattice (periodData M hM) M hM (order_nat M hM).2

/-- Multiplication by the specified epsilon preserves I.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem lattice_periodStable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    L3.PeriodStable (periodData M hM) (lattice M hM) := by
  exact L3.M72.matrixLattice_periodStable (periodData M hM) M hM (order_nat M hM).2

def stableLattice (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    L3.StablePseudolattice (periodData M hM) :=
  L3.M72.matrixStableLattice (periodData M hM) M hM (order_nat M hM).2

abbrev Group (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :=
  L3.PseudolatticeGroup (periodData M hM) (stableLattice M hM)

/-- The basis (tau, 1), with both scales equal to 1.
[RW26, (37), p. 20]; [RW-rec, Def. 1]. -/
theorem presentation (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    L3.PseudolatticePresentation (periodData M hM) (stableLattice M hM)
      (L3.M72.matrixBasis M) := by
  exact L3.M72.matrixPresentation (periodData M hM) M hM (order_nat M hM).2

def rowPoint (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) : baseField M hM :=
  ((u.1 : baseField M hM) * tau M hM + (u.2 : baseField M hM)) /
    ((epsilon M hM)⁻¹ - 1)

/-- Membership for the dependent `mk` formula.
[RW26, p. 2, (2)]; [RW-rec, Def. 1]. -/
theorem rowPoint_mem (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) : rowPoint M hM u ∈
      L3.pseudolatticePeriodPoints (periodData M hM) (stableLattice M hM) := by
  obtain ⟨hx, _⟩ := L3.M72.matrixToK_mk (periodData M hM) M hM (order_nat M hM).2 u
  simp only [matrixTauK_eq_tau] at hx
  simpa only [rowPoint, stableLattice, periodData] using hx

/-- The analytic argument, including the inverse-period denominator.
[RW26, p. 2, (2); (37), p. 20]; [RW-rec, Def. 1]. -/
theorem embed_rowPoint (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    Galois.embed (rowPoint M hM u : Galois.Qbar) = L4.specialValueArgument M u := by
  rw [L4.SpecialValueDescentAux.argument_eq]
  let f : baseField M hM →+* ℂ :=
    Galois.embed.toRingHom.comp (baseField M hM).subtype
  change f (((u.1 : baseField M hM) * tau M hM + (u.2 : baseField M hM)) /
    ((epsilon M hM)⁻¹ - 1)) = _
  rw [map_div₀, map_add, map_mul, map_intCast, map_intCast, map_sub, map_inv₀, map_one]
  change ((u.1 : ℂ) * Galois.embed (tauLift M hM) + (u.2 : ℂ)) /
    ((Galois.embed (epsilon M hM : Galois.Qbar))⁻¹ - 1) = _
  rw [embed_tauLift, embed_epsilon]

/-- Both directions of the zero-class test.
[RW26, Lemma 2, p. 12]; [RW-rec, Def. 1]. -/
theorem rowPoint_mem_lattice_iff (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) (u : ℤ × ℤ) :
    rowPoint M hM u ∈ lattice M hM ↔ u ∈ L4.specialValueLattice M := by
  obtain ⟨_, hmk⟩ :=
    L3.M72.matrixToK_mk (periodData M hM) M hM (order_nat M hM).2 u
  simp only [matrixTauK_eq_tau] at hmk
  have hmk' : L3.M72.matrixToK (periodData M hM) M hM (order_nat M hM).2
    (L4.specialValueMk M u) =
      L3.pseudolatticeMk (periodData M hM) (stableLattice M hM)
        (rowPoint M hM u) (rowPoint_mem M hM u) := by
    simpa only [rowPoint, stableLattice, periodData] using hmk
  calc
    _ ↔ L3.pseudolatticeMk (periodData M hM) (stableLattice M hM)
        (rowPoint M hM u) (rowPoint_mem M hM u) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).symm
    _ ↔ L3.M72.matrixToK (periodData M hM) M hM (order_nat M hM).2
        (L4.specialValueMk M u) = 0 := by rw [hmk']; rfl
    _ ↔ L4.specialValueMk M u = 0 :=
      (L3.M72.matrixToK (periodData M hM) M hM (order_nat M hM).2).map_eq_zero_iff
    _ ↔ u ∈ L4.specialValueLattice M := QuotientAddGroup.eq_zero_iff _

def labelEquiv (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    L4.SpecialValueGroup M ≃+ Group M hM :=
  L3.M72.matrixToK (periodData M hM) M hM (order_nat M hM).2

/-- The formula on all representatives determines the isomorphism.
[RW26, p. 2, (2)]; [RW-rec, Def. 1]. -/
theorem labelEquiv_mk (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    labelEquiv M hM (L4.specialValueMk M u) =
      L3.pseudolatticeMk (periodData M hM) (stableLattice M hM)
        (rowPoint M hM u) (rowPoint_mem M hM u) := by
  obtain ⟨hx, hmk⟩ :=
    L3.M72.matrixToK_mk (periodData M hM) M hM (order_nat M hM).2 u
  simp only [matrixTauK_eq_tau] at hmk
  change L3.M72.matrixToK (periodData M hM) M hM (order_nat M hM).2
    (L4.specialValueMk M u) =
      L3.pseudolatticeMk (periodData M hM) (stableLattice M hM)
        (rowPoint M hM u) (rowPoint_mem M hM u)
  simpa only [rowPoint, stableLattice, periodData] using hmk

/-- The label map preserves the class excluded by Proposition 7.
[RW26, p. 3, footnote 2]; [RW-rec, Def. 1, Prop. 7]. -/
theorem labelEquiv_zero_iff (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) : labelEquiv M hM g = 0 ↔ g = 0 := by
  exact (labelEquiv M hM).map_eq_zero_iff

/-- The period-point condition (epsilon-1)*x ∈ I agrees with the inverse-period form.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem periodPoints_mem_iff (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM) :
    x ∈ L3.pseudolatticePeriodPoints (periodData M hM) (stableLattice M hM) ↔
      (epsilon M hM - 1) * x ∈ lattice M hM := by
  have he : epsilon M hM ≠ 0 := (periodData M hM).epsilon_ne_zero
  have hs : L3.pseudolatticeScale (epsilon M hM) (lattice M hM) = lattice M hM :=
    lattice_periodStable M hM
  have hi : L3.pseudolatticeScale (epsilon M hM)⁻¹ (lattice M hM) = lattice M hM := by
    calc
      _ = L3.pseudolatticeScale (epsilon M hM)⁻¹
          (L3.pseudolatticeScale (epsilon M hM) (lattice M hM)) :=
        congrArg (L3.pseudolatticeScale (epsilon M hM)⁻¹) hs.symm
      _ = _ := (L3.pseudolatticeScale_inv (epsilon M hM) he (lattice M hM)).1
  change ((epsilon M hM)⁻¹ - 1) * x ∈ lattice M hM ↔ _
  constructor
  · intro hx
    have hmul : epsilon M hM * (((epsilon M hM)⁻¹ - 1) * x) ∈ lattice M hM := by
      rw [← hs]
      exact (L3.pseudolatticeScale_mem_iff _ _ _).mpr ⟨_, hx, rfl⟩
    have hid : epsilon M hM * (((epsilon M hM)⁻¹ - 1) * x) =
        -((epsilon M hM - 1) * x) := by
      rw [← mul_assoc, mul_sub, mul_inv_cancel₀ he, mul_one]
      ring
    rw [hid] at hmul
    exact (lattice M hM).neg_mem_iff.mp hmul
  · intro hx
    have hmul : (epsilon M hM)⁻¹ * ((epsilon M hM - 1) * x) ∈ lattice M hM := by
      rw [← hi]
      exact (L3.pseudolatticeScale_mem_iff _ _ _).mpr ⟨_, hx, rfl⟩
    have hid : (epsilon M hM)⁻¹ * ((epsilon M hM - 1) * x) =
        -(((epsilon M hM)⁻¹ - 1) * x) := by
      rw [← mul_assoc, mul_sub, inv_mul_cancel₀ he, mul_one]
      ring
    rw [hid] at hmul
    exact (lattice M hM).neg_mem_iff.mp hmul

/-- Multiplication by epsilon on the oriented basis.
[RW26, p. 20]; [RW-rec, Def. 1]. -/
theorem epsilon_basis (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    epsilon M hM * tau M hM = (M 0 0 : baseField M hM) * tau M hM + M 0 1 ∧
      epsilon M hM = (M 1 0 : baseField M hM) * tau M hM + M 1 1 := by
  constructor
  · have h := L4.PseudolatticeMatrixValuesAux.epsilon_mul_tauK
      (periodData M hM) M hM (order_nat M hM).2
    change epsilon M hM * L3.M72.matrixTauK (periodData M hM) M =
      (M 0 0 : baseField M hM) * L3.M72.matrixTauK (periodData M hM) M + M 0 1 at h
    simpa only [matrixTauK_eq_tau] using h
  · rfl

#check @L3.M72.matrixToK
#check @L3.M72.matrixToK_mk
#print lattice
#print rowPoint
#print labelEquiv

end SICLean.L5.ActualLattice
