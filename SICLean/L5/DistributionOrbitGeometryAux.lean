import SICLean.L5.PeriodPowerData
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.GroupTheory.Perm.Basic

set_option autoImplicit false

/-! Auxiliary finite lattice quotients and fibres of the ambient quotient map. -/

noncomputable section

open scoped Classical

namespace SICLean.L5.DistributionOrbitGeometryAux

universe u

section AdditiveQuotients

variable {A : Type u} [AddCommGroup A]

/-- The projection induced by the identity on the ambient additive group. -/
def quotientProject (I J : AddSubgroup A) (hIJ : I ≤ J) :
    A ⧸ I →+ A ⧸ J :=
  QuotientAddGroup.map I J (AddMonoidHom.id A) hIJ

/-- A fibre of the ambient quotient map is a translate of the relative quotient. -/
def quotientFibreEquiv (I J : AddSubgroup A) (hIJ : I ≤ J) (y : A ⧸ J) :
    {x : A ⧸ I // quotientProject I J hIJ x = y} ≃ J ⧸ I.addSubgroupOf J := by
  let e := AddSubgroup.quotientEquivProdOfLE hIJ
  have hfst (x : A ⧸ I) : (e x).1 = quotientProject I J hIJ x := by
    refine Quotient.inductionOn' x fun a => ?_
    rfl
  refine
    { toFun := fun x => (e x.val).2
      invFun := fun z => ⟨e.symm (y, z), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [← hfst, e.apply_symm_apply]
  · intro x
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · exact (hfst x.val).trans x.property |>.symm
    · rfl
  · intro z
    exact congrArg Prod.snd (e.apply_symm_apply (y, z))

/-- The relative index counts every fibre, including the infinite case as `Nat.card = 0`. -/
theorem quotient_fibre_card (I J : AddSubgroup A) (hIJ : I ≤ J) (y : A ⧸ J) :
    Nat.card {x : A ⧸ I // quotientProject I J hIJ x = y} = I.relIndex J :=
  Nat.card_congr (quotientFibreEquiv I J hIJ y)

end AdditiveQuotients

variable {K : Type u} [Field K] [NumberField K]

/-- The quotient of two contained full integer lattices is finite. -/
theorem lattice_quotient_finite (I J : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (hJ : Submodule.IsLattice ℚ J) (hIJ : I ≤ J) :
    Finite (J ⧸ I.submoduleOf J) := by
  have : Submodule.IsLattice ℚ I := hI
  have : Submodule.IsLattice ℚ J := hJ
  apply Submodule.finiteQuotientOfFreeOfRankEq
  calc
    Module.finrank ℤ (I.submoduleOf J) = Module.finrank ℤ I :=
      (Submodule.submoduleOfEquivOfLe hIJ).finrank_eq
    _ = Module.finrank ℤ J := by
      unfold Module.finrank
      rw [Submodule.IsLattice.rank' ℚ I, Submodule.IsLattice.rank' ℚ J]

/-- A contained full integer lattice has positive relative index. -/
theorem lattice_relIndex_pos (I J : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (hJ : Submodule.IsLattice ℚ J) (hIJ : I ≤ J) :
    0 < I.toAddSubgroup.relIndex J.toAddSubgroup := by
  have : Finite (J.toAddSubgroup ⧸ I.toAddSubgroup.addSubgroupOf J.toAddSubgroup) :=
    lattice_quotient_finite I J hI hJ hIJ
  exact Nat.card_pos

/-- Each ambient quotient fibre is finite, and its cardinality is the lattice index. -/
theorem lattice_fibre_finite_card (I J : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (hJ : Submodule.IsLattice ℚ J) (hIJ : I ≤ J)
    (y : K ⧸ J.toAddSubgroup) :
    Finite {x : K ⧸ I.toAddSubgroup //
        quotientProject I.toAddSubgroup J.toAddSubgroup hIJ x = y} ∧
      Nat.card {x : K ⧸ I.toAddSubgroup //
        quotientProject I.toAddSubgroup J.toAddSubgroup hIJ x = y} =
          I.toAddSubgroup.relIndex J.toAddSubgroup := by
  have := lattice_quotient_finite I J hI hJ hIJ
  exact ⟨Finite.of_equiv (J ⧸ I.submoduleOf J)
      (quotientFibreEquiv I.toAddSubgroup J.toAddSubgroup hIJ y).symm,
    quotient_fibre_card I.toAddSubgroup J.toAddSubgroup hIJ y⟩

omit [NumberField K] in
/-- Iterating the actual quotient action multiplies a field representative by a power. -/
theorem quotient_mul_pow (I : AddSubgroup K) (epsilon : K)
    (f : Equiv.Perm (K ⧸ I))
    (hf : ∀ z : K, f (QuotientAddGroup.mk z) = QuotientAddGroup.mk (epsilon * z))
    (n : ℕ) (z : K) :
    (f ^ n) (QuotientAddGroup.mk z) = QuotientAddGroup.mk (epsilon ^ n * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, hf, pow_succ', mul_assoc]

/-- Stability makes multiplication by the specified period preserve lattice membership. -/
theorem epsilon_mul_mem_iff (P : L3.PeriodData K) (I : L3.StablePseudolattice P) (z : K) :
    P.epsilon * z ∈ I.val ↔ z ∈ I.val := by
  constructor
  · intro hz
    rw [← I.property.2] at hz
    obtain ⟨w, hw, he⟩ := (L3.pseudolatticeScale_mem_iff _ _ _).mp hz
    have hwz : w = z := mul_left_cancel₀ P.epsilon_ne_zero he
    exact hwz ▸ hw
  · intro hz
    rw [← I.property.2]
    exact (L3.pseudolatticeScale_mem_iff _ _ _).mpr ⟨z, hz, rfl⟩

/-- The two period-point conventions agree by an explicit unit multiplication. -/
theorem periodPoints_iff_mul_sub_mem (P : L3.PeriodData K) (I : L3.StablePseudolattice P)
    (z : K) : z ∈ L3.pseudolatticePeriodPoints P I ↔ (P.epsilon - 1) * z ∈ I.val := by
  change (P.epsilon⁻¹ - 1) * z ∈ I.val ↔ (P.epsilon - 1) * z ∈ I.val
  rw [← epsilon_mul_mem_iff P I]
  have he : P.epsilon * ((P.epsilon⁻¹ - 1) * z) = -((P.epsilon - 1) * z) := by
    rw [← mul_assoc, mul_sub, mul_inv_cancel₀ P.epsilon_ne_zero, mul_one]
    ring
  rw [he, I.val.neg_mem_iff]

/-- The return condition is membership in the actual group for the powered period. -/
theorem quotient_return_iff_pow_mem (P : L3.PeriodData K) (I : L3.StablePseudolattice P)
    (f : Equiv.Perm (K ⧸ I.val.toAddSubgroup))
    (hf : ∀ z : K, f (QuotientAddGroup.mk z) = QuotientAddGroup.mk (P.epsilon * z))
    (n : ℕ) (hn : 0 < n) (z : K) :
    (f ^ n) (QuotientAddGroup.mk z) = QuotientAddGroup.mk z ↔
      z ∈ L3.pseudolatticePeriodPoints (PeriodPower.powPeriod P n hn)
        (PeriodPower.powLattice P I n hn) := by
  rw [quotient_mul_pow _ _ f hf, QuotientAddGroup.eq_iff_sub_mem,
    periodPoints_iff_mul_sub_mem]
  change P.epsilon ^ n * z - z ∈ I.val ↔ (P.epsilon ^ n - 1) * z ∈ I.val
  rw [sub_mul, one_mul]

end SICLean.L5.DistributionOrbitGeometryAux
