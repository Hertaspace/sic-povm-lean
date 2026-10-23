import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Quadratic subrings and their additive index

In a quadratic number field, every subring of the ring of integers is `ℤ + c 𝓞 K`, where
`c` is its actual additive index. The proof constructs an additive quotient onto `ℤ`
whose kernel is the embedded copy of `ℤ`. No finite-index hypothesis is needed: index
zero also gives the integer subring.
-/

noncomputable section
open scoped NumberField
open Module NumberField

namespace SICLean.L5.RayArithmeticOrderAux

variable (K : Type*) [Field K] [NumberField K]

/-- The embedded integers form the kernel of a surjective additive map to `ℤ`. -/
theorem exists_int_quotient (hK : Module.finrank ℚ K = 2) :
    ∃ f : 𝓞 K →+ ℤ, Function.Surjective f ∧
      ∀ x : 𝓞 K, f x = 0 ↔ ∃ z : ℤ, x = (z : 𝓞 K) := by
  classical
  let b : Basis (Fin 2) ℤ (𝓞 K) :=
    (Module.finBasis ℤ (𝓞 K)).reindex (finCongr ((RingOfIntegers.rank K).trans hK))
  let u : ℤ := b.repr 1 0
  let v : ℤ := b.repr 1 1
  have huv : u • b 0 + v • b 1 = 1 := by
    simpa only [Fin.sum_univ_two] using b.sum_repr (1 : 𝓞 K)
  obtain ⟨u', hu'⟩ := Int.gcd_dvd_left u v
  obtain ⟨v', hv'⟩ := Int.gcd_dvd_right u v
  let g : ℕ := u.gcd v
  change u = (g : ℤ) * u' at hu'
  change v = (g : ℤ) * v' at hv'
  have hgunit : IsUnit ((u.gcd v : ℕ) : ℤ) := by
    apply isUnit_of_map_unit (algebraMap ℤ (𝓞 K))
    refine IsUnit.of_mul_eq_one (u' • b 0 + v' • b 1) ?_
    rw [map_natCast]
    change (g : 𝓞 K) * (u' • b 0 + v' • b 1) = 1
    calc
      _ = u • b 0 + v • b 1 := by
        simp only [zsmul_eq_mul]
        have huO : (u : 𝓞 K) = (g : 𝓞 K) * (u' : 𝓞 K) := by
          simpa only [Int.cast_mul, Int.cast_natCast] using
            congrArg (fun x : ℤ => (x : 𝓞 K)) hu'
        have hvO : (v : 𝓞 K) = (g : 𝓞 K) * (v' : 𝓞 K) := by
          simpa only [Int.cast_mul, Int.cast_natCast] using
            congrArg (fun x : ℤ => (x : 𝓞 K)) hv'
        rw [huO, hvO]
        ring
      _ = 1 := huv
  have hg : u.gcd v = 1 := by
    simpa only [Int.natAbs_natCast] using Int.isUnit_iff_natAbs_eq.mp hgunit
  let s : ℤ := u.gcdA v
  let t : ℤ := u.gcdB v
  have hbez : u * s + v * t = 1 := by
    simpa [s, t, hg] using (Int.gcd_eq_gcd_ab u v).symm
  let f : 𝓞 K →+ ℤ :=
    (-v) • (b.coord 0).toAddMonoidHom + u • (b.coord 1).toAddMonoidHom
  have hf (x : 𝓞 K) : f x = -v * b.repr x 0 + u * b.repr x 1 := by
    rfl
  have hf1 : f (1 : 𝓞 K) = 0 := by
    rw [hf]
    change -v * u + u * v = 0
    ring
  have hfsurj : Function.Surjective f := by
    have hw : f ((-t) • b 0 + s • b 1) = 1 := by
      rw [hf]
      simp only [map_add, map_smul, b.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.single_apply, Fin.zero_ne_one, one_ne_zero, ↓reduceIte,
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
      linear_combination hbez
    intro z
    refine ⟨z • ((-t) • b 0 + s • b 1), ?_⟩
    rw [map_zsmul, hw]
    simp
  refine ⟨f, hfsurj, ?_⟩
  intro x
  constructor
  · intro hx
    rw [hf] at hx
    refine ⟨s * b.repr x 0 + t * b.repr x 1, ?_⟩
    rw [show ((s * b.repr x 0 + t * b.repr x 1 : ℤ) : 𝓞 K) =
      (s * b.repr x 0 + t * b.repr x 1) • (1 : 𝓞 K) by simp]
    apply b.repr.injective
    ext i
    fin_cases i
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr x 0 = (s * b.repr x 0 + t * b.repr x 1) * u
      linear_combination -(b.repr x 0) * hbez - t * hx
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr x 1 = (s * b.repr x 0 + t * b.repr x 1) * v
      linear_combination -(b.repr x 1) * hbez + s * hx
  · rintro ⟨z, rfl⟩
    have hz : (z : 𝓞 K) = z • (1 : 𝓞 K) := by simp
    rw [hz, map_zsmul, hf1, smul_zero]

/-- A subring of a quadratic maximal order is `ℤ + c 𝓞 K`, with `c` the actual additive index. This
includes the index-zero integer subring. -/
theorem mem_subring_iff_int_add_index_mul (hK : Module.finrank ℚ K = 2)
    (S : Subring (𝓞 K)) (a : 𝓞 K) :
    a ∈ S ↔ ∃ z : ℤ, ∃ b : 𝓞 K,
      a = (z : 𝓞 K) + (S.toAddSubgroup.index : 𝓞 K) * b := by
  classical
  obtain ⟨f, hfsurj, hfker⟩ := exists_int_quotient K hK
  have hker : f.ker ≤ S.toAddSubgroup := by
    intro x hx
    obtain ⟨z, rfl⟩ := (hfker x).mp hx
    exact intCast_mem S z
  let H : AddSubgroup ℤ := S.toAddSubgroup.map f
  obtain ⟨n, hn⟩ : ∃ n : ℤ, AddSubgroup.zmultiples n = H :=
    H.isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
  have hc : S.toAddSubgroup.index = n.natAbs := by
    calc
      S.toAddSubgroup.index = H.index :=
        (S.toAddSubgroup.index_map_eq hfsurj hker).symm
      _ = (AddSubgroup.zmultiples n).index := congrArg AddSubgroup.index hn.symm
      _ = n.natAbs := Int.index_zmultiples n
  have hH : H = AddSubgroup.zmultiples (S.toAddSubgroup.index : ℤ) := by
    rw [hc, Int.zmultiples_natAbs]
    exact hn.symm
  constructor
  · intro ha
    have haf : f a ∈ AddSubgroup.zmultiples (S.toAddSubgroup.index : ℤ) := by
      rw [← hH]
      exact AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨k, hk⟩ := Int.mem_zmultiples_iff.mp haf
    obtain ⟨b, hb⟩ := hfsurj k
    have hmul : f ((S.toAddSubgroup.index : 𝓞 K) * b) =
        (S.toAddSubgroup.index : ℤ) * f b := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    have hdiff : f (a - (S.toAddSubgroup.index : 𝓞 K) * b) = 0 := by
      rw [map_sub, hmul, hb, ← hk, sub_self]
    obtain ⟨z, hz⟩ := (hfker _).mp hdiff
    exact ⟨z, b, sub_eq_iff_eq_add.mp hz⟩
  · rintro ⟨z, b, rfl⟩
    apply S.add_mem (intCast_mem S z)
    change (S.toAddSubgroup.index : 𝓞 K) * b ∈ S.toAddSubgroup
    simpa only [nsmul_eq_mul] using S.toAddSubgroup.nsmul_index_mem b

end SICLean.L5.RayArithmeticOrderAux
