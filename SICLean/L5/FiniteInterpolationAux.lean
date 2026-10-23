import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Prime-field power sums for finite interpolation

The exponent-zero case is separated because the sum is the characteristic,
whereas a positive multiple of the unit-group order has sum `-1`.
-/

set_option autoImplicit false

noncomputable section

namespace SICLean.L5.FiniteInterpolationAux

open Finset
open scoped BigOperators

/-- Power sums of the prime-field points, embedded into any coefficient field
of characteristic `p`. -/
theorem sum_primeField_pow (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [CharP k p] (n : ℕ) :
    (∑ t : ZMod p, ((ZMod.castHom (dvd_refl p) k) t) ^ n) =
      if n = 0 then 0 else if p - 1 ∣ n then -1 else 0 := by
  classical
  by_cases hn : n = 0
  · simp [hn, ZMod.card]
  · have hsum : (∑ t : ZMod p, t ^ n) =
        if p - 1 ∣ n then -1 else 0 := by
      let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
      have hφ : univ.map φ = univ \ {(0 : ZMod p)} := by
        ext x
        simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and,
          mem_sdiff, mem_singleton, φ] using! isUnit_iff_ne_zero
      calc
        (∑ t : ZMod p, t ^ n) = ∑ t ∈ univ \ {(0 : ZMod p)}, t ^ n := by
          rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ,
            sum_singleton, zero_pow hn, add_zero]
        _ = ∑ t : (ZMod p)ˣ, (t ^ n : ZMod p) := by
          simp [φ, ← hφ, univ.sum_map φ]
        _ = if p - 1 ∣ n then -1 else 0 := by
          simpa only [ZMod.card] using FiniteField.sum_pow_units (ZMod p) n
    rw [if_neg hn]
    have hmap := congrArg (ZMod.castHom (dvd_refl p) k) hsum
    simpa only [map_sum, map_pow, apply_ite, map_neg, map_one, map_zero] using hmap

end SICLean.L5.FiniteInterpolationAux
