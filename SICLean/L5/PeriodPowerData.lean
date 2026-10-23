import SICLean.L4.PseudolatticeMatrixValues
import SICLean.L4.SpecialValueUnitAction
import SICLean.L5.PeriodPowerDataAux

set_option autoImplicit false

/-!
# Positive powers of the same arithmetic period

[RW-rec, Prop. 2, Def. 1, p. 4, p. 3]. [RW26, Prop. 8, pp. 2--3, p. 14, (2)--(4)]. The
trace recurrence constructs the powered period, while lattice stability gives the
representative-preserving inclusion and the base-unit action. The power changes epsilon
and N, preserving K, both real embeddings, and I. The sign-convention equivalence and
the period inclusion preserve the field representative x. Neither map multiplies its
label by -epsilon.
-/

noncomputable section
open scoped MatrixGroups BigOperators Classical

namespace SICLean.L5.PeriodPower
open L3

universe u
variable {K : Type u} [Field K] [NumberField K]

def periodTrace (N : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => (N : ℤ) + 2
  | n + 2 => ((N : ℤ) + 2) * periodTrace N (n + 1) - periodTrace N n

def periodOrder (P : PeriodData K) (r : ℕ) : ℕ :=
  (periodTrace P.N r - 2).toNat

/-- [RW-rec, p. 3, p. 4]. The trace recurrence, not an extra assumed integrality statement. [RW26,
p. 2]. -/
theorem periodTrace_spec (P : PeriodData K) (r : ℕ) :
    (periodTrace P.N r : K) = P.epsilon ^ r + (P.epsilon ^ r)⁻¹ := by
  have htrace : (P.N : K) + 2 = P.epsilon + P.epsilon⁻¹ := by
    apply (mul_right_injective₀ P.epsilon_ne_zero)
    field_simp [P.epsilon_ne_zero]
    linear_combination -P.epsilon_polynomial
  induction r using Nat.twoStepInduction with
  | zero => norm_num [periodTrace]
  | one => simpa [periodTrace] using htrace
  | more n ih₀ ih₁ =>
    rw [periodTrace, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast,
      Int.cast_ofNat, ih₀, ih₁, htrace]
    simp only [pow_succ, mul_inv_rev]
    field_simp [P.epsilon_ne_zero]
    ring

/-- Same sources: positivity and the quadratic equation needed to construct the power-period data.
The new N is Tr(epsilon^r)-2. -/
theorem powPeriod_spec (P : PeriodData K) (r : ℕ) (hr : 0 < r) :
    0 < periodOrder P r ∧
      (P.epsilon ^ r) ^ 2 - ((periodOrder P r : K) + 2) * P.epsilon ^ r + 1 = 0 ∧
      1 < P.sigma₁ (P.epsilon ^ r) ∧
      P.sigma₂ (P.epsilon ^ r) = (P.sigma₁ (P.epsilon ^ r))⁻¹ := by
  have hN : (0 : ℤ) < P.N := by exact_mod_cast P.N_pos
  have hgrow : ∀ n, 2 ≤ periodTrace P.N n ∧
      periodTrace P.N n < periodTrace P.N (n + 1) := by
    intro n
    induction n with
    | zero => simp only [periodTrace]; omega
    | succ n ih =>
      constructor
      · omega
      · change periodTrace P.N (n + 1) <
          ((P.N : ℤ) + 2) * periodTrace P.N (n + 1) - periodTrace P.N n
        nlinarith
  have hpos : 0 < periodTrace P.N r - 2 := by
    cases r with
    | zero => omega
    | succ n => have := hgrow n; omega
  have horder : (periodOrder P r : ℤ) = periodTrace P.N r - 2 :=
    Int.toNat_of_nonneg (le_of_lt hpos)
  have hcastOrder : (periodOrder P r : K) = ((periodTrace P.N r - 2 : ℤ) : K) := by
    exact_mod_cast horder
  have hcast : (periodOrder P r : K) + 2 =
      P.epsilon ^ r + (P.epsilon ^ r)⁻¹ := by
    rw [hcastOrder, Int.cast_sub, Int.cast_ofNat]
    simpa using periodTrace_spec P r
  refine ⟨by unfold periodOrder; omega, ?_, ?_, ?_⟩
  · rw [hcast]
    field_simp [P.epsilon_ne_zero]
    ring
  · rw [map_pow]
    exact one_lt_pow₀ P.epsilon_gt_one (Nat.ne_of_gt hr)
  · simp only [map_pow, P.epsilon_conj, inv_pow]

def powPeriod (P : PeriodData K) (r : ℕ) (hr : 0 < r) : PeriodData K where
  sigma₁ := P.sigma₁
  sigma₂ := P.sigma₂
  finrank_eq_two := P.finrank_eq_two
  epsilon := P.epsilon ^ r
  N := periodOrder P r
  N_pos := (powPeriod_spec P r hr).1
  epsilon_polynomial := (powPeriod_spec P r hr).2.1
  epsilon_gt_one := (powPeriod_spec P r hr).2.2.1
  epsilon_conj := (powPeriod_spec P r hr).2.2.2

/-- [RW-rec, p. 4], using epsilon I=I from p. 3. -/
theorem periodStable_pow (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) : PeriodStable (powPeriod P r hr) I.val := by
  exact PeriodPowerDataAux.epsilon_pow_scale P I r

def powLattice (P : PeriodData K) (I : StablePseudolattice P) (r : ℕ) (hr : 0 < r) :
    StablePseudolattice (powPeriod P r hr) :=
  ⟨I.val, I.property.1, periodStable_pow P I r hr⟩

def forwardPeriodPoints (P : PeriodData K) (I : StablePseudolattice P) : AddSubgroup K :=
  I.val.toAddSubgroup.comap (AddMonoidHom.mulLeft (P.epsilon - 1))

abbrev ForwardPeriodGroup (P : PeriodData K) (I : StablePseudolattice P) :=
  forwardPeriodPoints P I ⧸ I.val.toAddSubgroup.addSubgroupOf (forwardPeriodPoints P I)

/-- [RW-rec, Def. 1, p. 3]; [RW26, Lemma 2, p. 12]. Since epsilon^-1-1=-epsilon^-1(epsilon-1) and
epsilon I=I, the point subgroups are equal, with identity labels. -/
theorem periodPoints_eq_forward (P : PeriodData K) (I : StablePseudolattice P) :
    pseudolatticePeriodPoints P I = forwardPeriodPoints P I := by
  ext x
  change (P.epsilon⁻¹ - 1) * x ∈ I.val ↔ (P.epsilon - 1) * x ∈ I.val
  constructor
  · intro hx
    have h := I.val.neg_mem (PeriodPowerDataAux.epsilon_mul_mem P I hx)
    convert h using 1
    field_simp [P.epsilon_ne_zero]
    ring
  · intro hx
    have h := I.val.neg_mem (PeriodPowerDataAux.epsilon_inv_mul_mem P I hx)
    convert h using 1
    field_simp [P.epsilon_ne_zero]
    ring

namespace DataAux
/-- Equality transport, with the representative unchanged. -/
def subgroupQuotientCongr (I : AddSubgroup K) {H J : AddSubgroup K} (h : H = J) :
    (H ⧸ I.addSubgroupOf H) ≃+ (J ⧸ I.addSubgroupOf J) :=
  Eq.ndrec (motive := fun (J : AddSubgroup K) =>
    (H ⧸ I.addSubgroupOf H) ≃+ (J ⧸ I.addSubgroupOf J)) (AddEquiv.refl _) h
end DataAux

def conventionEquiv (P : PeriodData K) (I : StablePseudolattice P) :
    PseudolatticeGroup P I ≃+ ForwardPeriodGroup P I :=
  DataAux.subgroupQuotientCongr I.val.toAddSubgroup (periodPoints_eq_forward P I)

/-- Same sources as `periodPoints_eq_forward`: the requested explicit isomorphism sends x+I to x+I,
including x=0. -/
theorem conventionEquiv_mk (P : PeriodData K) (I : StablePseudolattice P)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    conventionEquiv P I (pseudolatticeMk P I x hx) =
      QuotientAddGroup.mk
        (⟨x, (periodPoints_eq_forward P I).le hx⟩ : forwardPeriodPoints P I) := by
  exact PeriodPowerDataAux.quotient_transport_mk _ _ _ (periodPoints_eq_forward P I) x hx

/-- [RW-rec, p. 4]; [RW26, Prop. 8, p. 14]. The old points lie in the new group, with unchanged K
representatives. -/
theorem periodPoints_le_pow (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) :
    pseudolatticePeriodPoints P I ≤
      pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr) := by
  intro x hx
  change (P.epsilon⁻¹ - 1) * x ∈ I.val at hx
  change ((P.epsilon ^ r)⁻¹ - 1) * x ∈ I.val
  rw [← inv_pow]
  exact PeriodPowerDataAux.pow_sub_one_mul_mem I.val P.epsilon⁻¹
    (fun _ hy => PeriodPowerDataAux.epsilon_inv_mul_mem P I hy) x hx r

/-- Quotient well-definedness for the preceding inclusion, same sources. -/
theorem periodPowerInclusion_rel (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) :
    I.val.toAddSubgroup.addSubgroupOf (pseudolatticePeriodPoints P I) ≤
      (I.val.toAddSubgroup.addSubgroupOf
        (pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr))).comap
          (AddSubgroup.inclusion (periodPoints_le_pow P I r hr)) := by
  intro x hx
  exact hx

def periodPowerInclusion (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) :
    PseudolatticeGroup P I →+ PseudolatticeGroup (powPeriod P r hr) (powLattice P I r hr) :=
  QuotientAddGroup.map _ _ (AddSubgroup.inclusion (periodPoints_le_pow P I r hr))
    (periodPowerInclusion_rel P I r hr)

/-- [RW-rec, p. 4]; [RW26, Prop. 8, p. 14]. -/
theorem periodPowerInclusion_mk (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    periodPowerInclusion P I r hr (pseudolatticeMk P I x hx) =
      pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr)
        x (periodPoints_le_pow P I r hr hx) := by
  rfl

/-- [RW-rec, p. 4]: this is an embedding, not merely a homomorphism. -/
theorem periodPowerInclusion_injective (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) : Function.Injective (periodPowerInclusion P I r hr) := by
  intro x y hxy
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    induction y using QuotientAddGroup.induction_on with
    | H y =>
      apply QuotientAddGroup.eq.mpr
      change (QuotientAddGroup.mk (AddSubgroup.inclusion (periodPoints_le_pow P I r hr) x) :
        PseudolatticeGroup (powPeriod P r hr) (powLattice P I r hr)) =
        QuotientAddGroup.mk (AddSubgroup.inclusion (periodPoints_le_pow P I r hr) y) at hxy
      have hmem := QuotientAddGroup.eq.mp hxy
      exact hmem

/-- [RW-rec, p. 4, (9)]; [RW26, Prop. 8, p. 14]. Multiplication by the base unit preserves all
points for the power period. -/
theorem epsilon_mem_powPoints (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr)) :
    P.epsilon * x ∈ pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr) := by
  change ((P.epsilon ^ r)⁻¹ - 1) * x ∈ I.val at hx
  change ((P.epsilon ^ r)⁻¹ - 1) * (P.epsilon * x) ∈ I.val
  simpa only [mul_left_comm] using PeriodPowerDataAux.epsilon_mul_mem P I hx

/-- The inverse multiplication used in the actual action, same sources. -/
theorem epsilon_inv_mem_powPoints (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr)) :
    P.epsilon⁻¹ * x ∈ pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr) := by
  change ((P.epsilon ^ r)⁻¹ - 1) * x ∈ I.val at hx
  change ((P.epsilon ^ r)⁻¹ - 1) * (P.epsilon⁻¹ * x) ∈ I.val
  simpa only [mul_left_comm] using PeriodPowerDataAux.epsilon_inv_mul_mem P I hx

/-- A concrete quotient action, not a choice of a map satisfying (9). -/
def epsilonAction (P : PeriodData K) (I : StablePseudolattice P) (r : ℕ) (hr : 0 < r) :
    PseudolatticeGroup (powPeriod P r hr) (powLattice P I r hr) ≃+
      PseudolatticeGroup (powPeriod P r hr) (powLattice P I r hr) where
  toFun := QuotientAddGroup.map _ _
    { toFun := fun x => ⟨P.epsilon * x.val, epsilon_mem_powPoints P I r hr x.val x.property⟩
      map_zero' := by
        apply Subtype.ext
        exact mul_zero _
      map_add' := by
        intro x y
        apply Subtype.ext
        exact mul_add _ _ _ } (by
          intro x hx
          change P.epsilon * x.val ∈ I.val
          exact PeriodPowerDataAux.epsilon_mul_mem P I hx)
  invFun := QuotientAddGroup.map _ _
    { toFun := fun x => ⟨P.epsilon⁻¹ * x.val, epsilon_inv_mem_powPoints P I r hr x.val x.property⟩
      map_zero' := by
        apply Subtype.ext
        exact mul_zero _
      map_add' := by
        intro x y
        apply Subtype.ext
        exact mul_add _ _ _ } (by
          intro x hx
          change P.epsilon⁻¹ * x.val ∈ I.val
          exact PeriodPowerDataAux.epsilon_inv_mul_mem P I hx)
  left_inv := by
    intro g
    refine QuotientAddGroup.induction_on g (fun x => ?_)
    change QuotientAddGroup.mk
      (⟨P.epsilon⁻¹ * (P.epsilon * x.val), _⟩ :
        pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr)) =
      QuotientAddGroup.mk x
    congr 1
    apply Subtype.ext
    simp [P.epsilon_ne_zero]
  right_inv := by
    intro g
    refine QuotientAddGroup.induction_on g (fun x => ?_)
    change QuotientAddGroup.mk
      (⟨P.epsilon * (P.epsilon⁻¹ * x.val), _⟩ :
        pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr)) =
      QuotientAddGroup.mk x
    congr 1
    apply Subtype.ext
    simp [P.epsilon_ne_zero]
  map_add' := by
    intro g h
    exact map_add _ g h

/-- [RW-rec, p. 4, (9)] label bridge; [RW26, Prop. 8, p. 14]. -/
theorem epsilonAction_mk (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr)) :
    epsilonAction P I r hr (pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr) x hx) =
      pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr)
        (P.epsilon * x) (epsilon_mem_powPoints P I r hr x hx) := by
  rfl

/-- [RW-rec, p. 4]: the action order divides r; equality of orders is not asserted. [RW26, p. 14].
-/
theorem epsilonAction_pow (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r)
    (g : PseudolatticeGroup (powPeriod P r hr) (powLattice P I r hr)) :
    (epsilonAction P I r hr)^[r] g = g := by
  refine QuotientAddGroup.induction_on g (fun x => ?_)
  have hmem (n : ℕ) : P.epsilon ^ n * x.val ∈
      pseudolatticePeriodPoints (powPeriod P r hr) (powLattice P I r hr) := by
    induction n with
    | zero => simpa only [pow_zero, one_mul] using x.property
    | succ n ih =>
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        epsilon_mem_powPoints P I r hr (P.epsilon ^ n * x.val) ih
  have hiter (n : ℕ) : (epsilonAction P I r hr)^[n]
      (pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr) x.val x.property) =
        pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr)
          (P.epsilon ^ n * x.val) (hmem n) := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, epsilonAction_mk]
      apply congrArg QuotientAddGroup.mk
      apply Subtype.ext
      simp only [pow_succ]
      ring
  change (epsilonAction P I r hr)^[r]
      (pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr) x.val x.property) =
    pseudolatticeMk (powPeriod P r hr) (powLattice P I r hr) x.val x.property
  rw [hiter]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change P.epsilon ^ r * x.val - x.val ∈ I.val
  have hx := (periodPoints_eq_forward (powPeriod P r hr) (powLattice P I r hr)).le x.property
  change (P.epsilon ^ r - 1) * x.val ∈ I.val at hx
  simpa only [sub_mul, one_mul] using hx

/-- [RW-rec, p. 4]: the embedded old group is fixed by the base unit. -/
theorem epsilonAction_inclusion (P : PeriodData K) (I : StablePseudolattice P)
    (r : ℕ) (hr : 0 < r) (g : PseudolatticeGroup P I) :
    epsilonAction P I r hr (periodPowerInclusion P I r hr g) =
      periodPowerInclusion P I r hr g := by
  refine QuotientAddGroup.induction_on g (fun x => ?_)
  change epsilonAction P I r hr
      (periodPowerInclusion P I r hr (pseudolatticeMk P I x.val x.property)) =
    periodPowerInclusion P I r hr (pseudolatticeMk P I x.val x.property)
  rw [periodPowerInclusion_mk, epsilonAction_mk]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change P.epsilon * x.val - x.val ∈ I.val
  have hx := (periodPoints_eq_forward P I).le x.property
  change (P.epsilon - 1) * x.val ∈ I.val at hx
  simpa only [sub_mul, one_mul] using hx

#check @L3.PeriodData
#print powPeriod
#print powLattice
#print conventionEquiv
#print periodPowerInclusion
#print epsilonAction

end SICLean.L5.PeriodPower
