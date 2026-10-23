import SICLean.L3.Pseudolattice
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

set_option autoImplicit false

/-! Auxiliary lattice facts for maximal-order saturation. -/

noncomputable section

open scoped nonZeroDivisors NumberField

namespace SICLean.L3

variable {K : Type*} [Field K] [NumberField K]

/-- A full integer lattice has nonzero span over the maximal order. -/
theorem pseudolattice_maximalSpan_ne_bot (I : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) :
    Submodule.span (𝓞 K) (I : Set K) ≠ ⊥ := by
  intro h
  have hi : I = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hm : x ∈ Submodule.span (𝓞 K) (I : Set K) := Submodule.subset_span hx
    rw [h] at hm
    change x = 0 at hm
    change x = 0
    exact hm
  have hs := hI.span_eq_top
  rw [hi] at hs
  simp at hs

end SICLean.L3
