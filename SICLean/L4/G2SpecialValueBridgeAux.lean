import SICLean.L4.G2RepellingPointValues

set_option autoImplicit false

noncomputable section

open scoped BigOperators MatrixGroups

namespace SICLean.L4.G2SpecialValueBridgeAux

open G2.ReflectionGeometry

/-- The explicit reflection preserves the actual zero class. -/
theorem rowReflection_mem_lattice_iff (M : SL(2, ℤ)) (x : ℤ × ℤ) :
    (x.1, -x.2) ∈ specialValueLattice (modularInverseReflection M) ↔
      x ∈ specialValueLattice M := by
  change rowReflection x ∈ specialValueLattice (modularInverseReflection M) ↔ _
  rw [← rowReflection_lattice M]
  exact AddSubgroup.mem_map_iff_mem rowReflection.injective

/-- Finite sums reindex along the concrete row-quotient equivalence. -/
theorem sum_reflection (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : SpecialValueGroup M → ℂ)
    (g : SpecialValueGroup (modularInverseReflection M) → ℂ)
    (h : ∀ x, f x = g (reflectionEquiv M x)) :
    letI : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
    letI : Fintype (SpecialValueGroup M) := Fintype.ofFinite _
    letI : Finite (SpecialValueGroup (modularInverseReflection M)) :=
      specialValueGroup_finite _ (reflection_admissible M hM)
    letI : Fintype (SpecialValueGroup (modularInverseReflection M)) := Fintype.ofFinite _
    ∑ x, f x = ∑ x, g x := by
  let : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  let : Fintype (SpecialValueGroup M) := Fintype.ofFinite _
  let : Finite (SpecialValueGroup (modularInverseReflection M)) :=
    specialValueGroup_finite _ (reflection_admissible M hM)
  let : Fintype (SpecialValueGroup (modularInverseReflection M)) := Fintype.ofFinite _
  exact Fintype.sum_equiv (reflectionEquiv M).toEquiv f g h

end SICLean.L4.G2SpecialValueBridgeAux
