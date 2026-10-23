import SICLean.L5.FrobeniusRestriction

set_option autoImplicit false

/-!
Integral-base transport for the rational Chebotarev bridge.
All algebras are the existing canonical integer-ring algebras.
-/

noncomputable section
open scoped NumberField

namespace SICLean.L5.DescentChebotarevAux

variable (F : IntermediateField ℚ Galois.Qbar)

/-- The map from the integers of `ℚ` factors through their equivalence with `ℤ`. -/
theorem algebraMap_integerBase (x : 𝓞 ℚ) :
    algebraMap (𝓞 ℚ) (𝓞 F) x = (Rat.ringOfIntegersEquiv x : 𝓞 F) := by
  apply NumberField.RingOfIntegers.coe_injective
  change algebraMap ℚ F (x : ℚ) = (Rat.ringOfIntegersEquiv x : F)
  have hx : (x : ℚ) = (Rat.ringOfIntegersEquiv x : ℚ) :=
    (Rat.ringOfIntegersEquiv_apply_coe x).symm
  rw [hx]
  exact map_intCast (algebraMap ℚ F) (Rat.ringOfIntegersEquiv x)

/-- Contraction through the two canonically isomorphic integral base rings. -/
theorem under_integerBase (Q : Ideal (𝓞 F)) :
    Q.under (𝓞 ℚ) = Ideal.comap Rat.ringOfIntegersEquiv (Q.under ℤ) := by
  ext x
  change algebraMap (𝓞 ℚ) (𝓞 F) x ∈ Q ↔
    algebraMap ℤ (𝓞 F) (Rat.ringOfIntegersEquiv x) ∈ Q
  rw [algebraMap_integerBase]
  rfl

/-- The base residue rings are isomorphic, so have the same cardinality. -/
theorem quotient_card_integerBase (Q : Ideal (𝓞 F)) :
    Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) = Nat.card (ℤ ⧸ Q.under ℤ) := by
  apply Nat.card_congr
  apply (Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv ?_).toEquiv
  rw [under_integerBase]
  exact (Ideal.map_comap_eq_self_of_equiv Rat.ringOfIntegersEquiv _).symm

/-- Changing the integral base from `𝓞 ℚ` to `ℤ` preserves nonramification. -/
theorem isUnramifiedAt_integerBase_iff (Q : Ideal (𝓞 F)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 ℚ) Q ↔ Algebra.IsUnramifiedAt ℤ Q := by
  have : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 ℚ)) (by
      intro x
      refine ⟨Rat.ringOfIntegersEquiv x, ?_⟩
      apply Rat.ringOfIntegersEquiv.injective
      simp)
  constructor
  · intro h
    let := h
    exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime Q)
  · intro h
    let := h
    exact Algebra.FormallyUnramified.of_restrictScalars ℤ (𝓞 ℚ)
      (Localization.AtPrime Q)

end SICLean.L5.DescentChebotarevAux
