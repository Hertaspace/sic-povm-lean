import SICLean.L3.PseudolatticeIdeal

set_option autoImplicit false

/-!
# Auxiliary lemmas for the finiteness of stable pseudolattice classes

These lemmas transport the `ℤ`-module structure of a fractional ideal to the
integer carrier used by the finiteness argument, and record the elementary
order properties of `pseudolatticeScale`.
-/

noncomputable section

open scoped nonZeroDivisors NumberField

namespace SICLean.L3

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The identity on underlying sets is `ℤ`-linear from a fractional ideal to its
integer carrier. Both sides are the same subtype of `K`, only the scalar
structures are recorded differently. -/
def fractionalIdealCarrierEquiv (a : FractionalIdeal (𝓞 K)⁰ K) :
    (a : Submodule (𝓞 K) K) ≃ₗ[ℤ] fractionalIdealCarrier a where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fractionalIdealCarrier_free (a : FractionalIdeal (𝓞 K)⁰ K) :
    Module.Free ℤ (fractionalIdealCarrier a) :=
  Module.Free.of_equiv' (inferInstance : Module.Free ℤ (a : Submodule (𝓞 K) K))
    (fractionalIdealCarrierEquiv a)

theorem fractionalIdealCarrier_finite (a : FractionalIdeal (𝓞 K)⁰ K) :
    Module.Finite ℤ (fractionalIdealCarrier a) :=
  Module.Finite.equiv (fractionalIdealCarrierEquiv a)

theorem pseudolatticeScale_mono (lam : K) {I J : Submodule ℤ K} (h : I ≤ J) :
    pseudolatticeScale lam I ≤ pseudolatticeScale lam J :=
  Submodule.map_mono h

theorem pseudolatticeScale_comm (a b : K) (I : Submodule ℤ K) :
    pseudolatticeScale a (pseudolatticeScale b I) =
      pseudolatticeScale b (pseudolatticeScale a I) := by
  rw [← pseudolatticeScale_mul, ← pseudolatticeScale_mul, mul_comm]

theorem pseudolatticeScale_inv_cancel (lam : K) (hlam : lam ≠ 0) (I : Submodule ℤ K) :
    pseudolatticeScale lam⁻¹ (pseudolatticeScale lam I) = I :=
  (pseudolatticeScale_inv lam hlam I).1

theorem pseudolatticeScale_mem_scale_iff (lam : K) (hlam : lam ≠ 0)
    (I : Submodule ℤ K) (x : K) :
    x ∈ pseudolatticeScale lam I ↔ lam⁻¹ * x ∈ I := by
  rw [pseudolatticeScale_mem_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [inv_mul_cancel_left₀ hlam]
  · intro hx
    exact ⟨lam⁻¹ * x, hx, mul_inv_cancel_left₀ hlam x⟩

end SICLean.L3
