import SICLean.L5.ActualPseudolattice
import SICLean.L5.RayArithmeticOrderAux
import Mathlib.GroupTheory.Exponent
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

set_option autoImplicit false

/-!
# The multiplier order and the level on the actual lattice

The field, period and lattice are the objects fixed above. In particular the order below
is computed from I, and c is its additive index in the maximal order. It is not the
possibly larger conductor of Z[epsilon]. Sources: [RW26, p. 20] (actual field/lattice
dictionary).
-/

noncomputable section
open scoped MatrixGroups NumberField

namespace SICLean.L5.RayArithmeticOrder

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)

local notation "K" => ActualField.baseField M hM
local notation "P" => ActualField.periodData M hM
local notation "I" => ActualLattice.stableLattice M hM

/-- Literal multiplier order (I:I) inside the actual K. -/
def multiplierOrder : Subring K where
  carrier := {a | ∀ x ∈ (I).val, a * x ∈ (I).val}
  zero_mem' := by
    intro x hx
    simpa only [zero_mul] using (I).val.zero_mem
  one_mem' := by
    intro x hx
    simpa only [one_mul] using hx
  add_mem' := by
    intro a b ha hb x hx
    simpa only [add_mul] using (I).val.add_mem (ha x hx) (hb x hx)
  neg_mem' := by
    intro a ha x hx
    simpa only [neg_mul] using (I).val.neg_mem (ha x hx)
  mul_mem' := by
    intro a b ha hb x hx
    simpa only [mul_assoc] using ha (b * x) (hb x hx)

/-- The same order viewed inside the maximal order, without assuming equality. -/
def integralOrder : Subring (𝓞 K) :=
  (multiplierOrder M hM).comap (algebraMap (𝓞 K) K)

/-- For quadratic orders the index is the conductor; this fact is proved below. -/
def conductor : ℕ := (integralOrder M hM).toAddSubgroup.index

/-- Raw arithmetic hypotheses; positivity is explicit since 4 divides 0. -/
def ValidLevel (m : ℕ) : Prop :=
  0 < m ∧ 4 ∣ m ∧ 2 * AddMonoid.exponent (ActualLattice.Group M hM) ∣ m

/-- Source: definition of (I:I), [RW-rec]. [RW26, p. 20]. -/
theorem mem_multiplierOrder (a : K) :
    a ∈ multiplierOrder M hM ↔ ∀ x ∈ (I).val, a * x ∈ (I).val := by
  rfl

/-- Source: full-lattice integrality bridge; [RW-rec]. No maximal-order stability of I is assumed.
[RW26, p. 20]. -/
theorem multiplierOrder_integral (a : K) (ha : a ∈ multiplierOrder M hM) :
    IsIntegral ℤ a := by
  have hne : (I).val ≠ ⊥ := by
    intro h
    have hs := (I).property.1.span_eq_top
    rw [h] at hs
    simp at hs
  exact isIntegral_of_smul_mem_submodule (I).val hne (I).property.1.fg a ha

/-- Source: the same order bridge, [RW-rec]. [RW26, p. 20]. -/
theorem mem_integralOrder (a : 𝓞 K) :
    a ∈ integralOrder M hM ↔ (a : K) ∈ multiplierOrder M hM := by
  rfl

/-- Source: quadratic-order finite index; [RW-rec]. [RW26, p. 20]. -/
theorem conductor_pos : 0 < conductor M hM := by
  let S := integralOrder M hM
  let N : Submodule ℤ (𝓞 K) := S.toAddSubgroup.toIntSubmodule
  let f := L3.pseudolatticeConductor P
  have hf : 0 < f := L3.pseudolatticeConductor_pos P
  have hmem (b : 𝓞 K) : (f : ℤ) • b ∈ N := by
    change ((f : ℤ) • b : 𝓞 K) ∈ S
    apply (mem_integralOrder M hM _).mpr
    intro x hx
    have hact := L3.periodStable_order_smul P I
      ((f : K) * (b : K)) x
      (L3.pseudolatticeConductor_mul_mem_epsilonOrder P b) hx
    simpa only [zsmul_eq_mul, NumberField.RingOfIntegers.coe_eq_algebraMap,
      map_mul, map_intCast, map_natCast, Int.cast_natCast] using hact
  let F : 𝓞 K →ₗ[ℤ] N :=
    (LinearMap.lsmul ℤ (𝓞 K) (f : ℤ)).codRestrict N hmem
  have hF : Function.Injective F := by
    intro b d hbd
    apply (LinearMap.lsmul_injective (M := 𝓞 K)
      (Int.natCast_ne_zero.mpr hf.ne'))
    exact congrArg Subtype.val hbd
  have hr : Module.finrank ℤ N = Module.finrank ℤ (𝓞 K) :=
    le_antisymm (Submodule.finrank_le N) (F.finrank_le_finrank_of_injective hF)
  have : Finite ((𝓞 K) ⧸ N) := Submodule.finiteQuotientOfFreeOfRankEq N hr
  have : Finite ((𝓞 K) ⧸ S.toAddSubgroup) := by
    change Finite ((𝓞 K) ⧸ N.toAddSubgroup)
    exact inferInstanceAs (Finite ((𝓞 K) ⧸ N))
  exact Nat.pos_of_ne_zero (AddSubgroup.index_ne_zero_of_finite
    (H := S.toAddSubgroup))

/-- Source: O=Z+c O_K, [RW-rec]; This is a theorem, not a property included in the definition of c.
[RW26, p. 20]. -/
theorem mem_multiplierOrder_iff (a : K) :
    a ∈ multiplierOrder M hM ↔
      ∃ z : ℤ, ∃ b : 𝓞 K, a = (z : K) + (conductor M hM : K) * (b : K) := by
  constructor
  · intro ha
    let aO : 𝓞 K := ⟨a, multiplierOrder_integral M hM a ha⟩
    have haO : aO ∈ integralOrder M hM := (mem_integralOrder M hM aO).mpr ha
    obtain ⟨z, b, heq⟩ :=
      (RayArithmeticOrderAux.mem_subring_iff_int_add_index_mul K
        (P).finrank_eq_two (integralOrder M hM) aO).mp haO
    refine ⟨z, b, ?_⟩
    have h := congrArg (algebraMap (𝓞 K) K) heq
    have haOcoe : (algebraMap (𝓞 K) K) aO = a := rfl
    rw [haOcoe] at h
    simpa only [conductor, map_add, map_mul, map_intCast, map_natCast,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap] using h
  · rintro ⟨z, b, rfl⟩
    have h : (z : 𝓞 K) + (conductor M hM : 𝓞 K) * b ∈ integralOrder M hM :=
      (RayArithmeticOrderAux.mem_subring_iff_int_add_index_mul K
        (P).finrank_eq_two (integralOrder M hM) _).mpr ⟨z, b, rfl⟩
    have h' := (mem_integralOrder M hM _).mp h
    simpa only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add,
      map_mul, map_intCast, map_natCast] using h'

/-- Source: conductor containment, [RW-rec]. [RW26, p. 20]. -/
theorem conductor_mul_mem (b : 𝓞 K) :
    (conductor M hM : K) * (b : K) ∈ multiplierOrder M hM := by
  have h : conductor M hM • b ∈ integralOrder M hM :=
    AddSubgroup.nsmul_index_mem (integralOrder M hM).toAddSubgroup b
  have h' := (mem_integralOrder M hM _).mp h
  simpa only [NumberField.RingOfIntegers.coe_eq_algebraMap, nsmul_eq_mul,
    map_mul, map_natCast] using h'

/-- Source: (I:I) and stability under epsilon, [RW-rec]; [RW26, p. 20]. -/
theorem epsilon_mem_multiplierOrder :
    (P).epsilon ∈ multiplierOrder M hM := by
  intro x hx
  rw [← (I).property.2]
  exact (L3.pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩

/-- Source: level convention, [RW-rec]. [RW26, p. 20]. -/
theorem exponent_dvd_level (m : ℕ) (hm : ValidLevel M hM m) :
    AddMonoid.exponent (ActualLattice.Group M hM) ∣ m := by
  exact dvd_trans (dvd_mul_left _ 2) hm.2.2

/-- Source: quotient exponent bridge, [RW-rec]; The point is in K, before taking its quotient class.
[RW26, p. 20]. -/
theorem level_mul_point_mem (m : ℕ) (hm : ValidLevel M hM m)
    (x : K) (hx : x ∈ L3.pseudolatticePeriodPoints P I) :
    (m : K) * x ∈ (I).val := by
  have hzero : m • L3.pseudolatticeMk P I x hx = 0 :=
    (AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mp
      (exponent_dvd_level M hM m hm)) _
  have hq : (QuotientAddGroup.mk
      (m • (⟨x, hx⟩ : L3.pseudolatticePeriodPoints P I)) :
      ActualLattice.Group M hM) = 0 := by
    simpa only [L3.pseudolatticeMk, QuotientAddGroup.mk_nsmul] using hzero
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hq
  change m • x ∈ (I).val at hmem
  simpa only [nsmul_eq_mul] using hmem

/-- Source: same bridge for the existing quotient representative, not an extra label convention.
[RW26, p. 20]. -/
theorem level_mul_representative_mem (m : ℕ) (hm : ValidLevel M hM m)
    (x : ActualLattice.Group M hM) :
    (m : K) * L3.pseudolatticeRepresentative P I x ∈ (I).val := by
  exact level_mul_point_mem M hM m hm _ (Quotient.out x).property

/-- Source: cm O_K subset m O, [RW-rec]; [RW26, p. 20]. -/
theorem cm_mul_eq_level_mul_order (m : ℕ) (b : 𝓞 K) :
    ∃ a : multiplierOrder M hM,
      ((conductor M hM * m : ℕ) : K) * (b : K) = (m : K) * (a : K) := by
  refine ⟨⟨(conductor M hM : K) * (b : K), conductor_mul_mem M hM b⟩, ?_⟩
  simp only [Nat.cast_mul]
  ring

/-- Source: integral generator plus cm congruence implies alpha in O, [RW-rec]; [RW26, p. 20]. -/
theorem one_add_cm_mem_order (m : ℕ) (b : 𝓞 K) :
    1 + ((conductor M hM * m : ℕ) : K) * (b : K) ∈
      multiplierOrder M hM := by
  obtain ⟨a, ha⟩ := cm_mul_eq_level_mul_order M hM m b
  rw [ha]
  simpa only [nsmul_eq_mul] using
    (multiplierOrder M hM).add_mem (multiplierOrder M hM).one_mem
      ((multiplierOrder M hM).nsmul_mem a.property m)

#check @AddMonoid.exponent
#print conductor
#print ValidLevel

end SICLean.L5.RayArithmeticOrder
