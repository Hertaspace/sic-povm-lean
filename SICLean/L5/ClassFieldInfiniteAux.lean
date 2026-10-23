import SICLean.L5.ClassFieldConjugation
import SICLean.L5.ClassFieldSigns

set_option autoImplicit false

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory
open SICLean.L5.ClassFieldModulus SICLean.L5.ClassFieldTransport
open SICLean.L5.ClassFieldIdealAction SICLean.L5.ClassFieldConjugation

namespace SICLean.L5.ClassFieldInfiniteAux

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (n : ℕ)

theorem inducesNontrivial_iff (ρ : Galois.QbarAut) :
    Galois.InducesNontrivial (ActualField.baseField M hM) ρ ↔
      baseAction M hM ρ ≠ 1 := by
  constructor
  · rintro ⟨κ, hκ, hρκ⟩ h
    apply hκ
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    calc
      (κ x : Galois.Qbar) = ρ (x : Galois.Qbar) := (hρκ x).symm
      _ = (baseAction M hM ρ x : Galois.Qbar) := (baseAction_apply M hM ρ x).symm
      _ = (x : Galois.Qbar) := by rw [h]; rfl
  · intro h
    exact ⟨baseAction M hM ρ, h, fun x => (baseAction_apply M hM ρ x).symm⟩

theorem inducesNontrivial_inv (ρ : Galois.QbarAut)
    (hρ : Galois.InducesNontrivial (ActualField.baseField M hM) ρ) :
    Galois.InducesNontrivial (ActualField.baseField M hM) ρ⁻¹ := by
  obtain ⟨κ, hκ, hρκ⟩ := hρ
  refine ⟨κ⁻¹, ?_, ?_⟩
  · change κ ≠ 1 at hκ
    change κ⁻¹ ≠ 1
    exact inv_ne_one.mpr hκ
  · intro x
    apply ρ.injective
    simpa using (hρκ (κ⁻¹ x)).symm

theorem rayAction_eq_self_of_baseAction (ρ : Galois.QbarAut)
    (hρ : baseAction M hM ρ = 1) (a : RayGroup M hM n) :
    rayAction M hM n ρ a = a := by
  obtain ⟨b, rfl⟩ := idealClass_surjective M hM n a
  rw [rayAction_ideal]
  congr 1
  apply Subtype.ext
  change fractionalAction M hM ρ b.1 = b.1
  have hi : integerAction M hM ρ = RingEquiv.refl _ := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change baseAction M hM ρ (x : Base M hM) = (x : Base M hM)
    rw [hρ]
    rfl
  simp [fractionalAction, hi, FractionalIdeal.ringEquivOfRingEquiv_refl]
  rfl

theorem artin_restrict_injective :
    Function.Injective (fun a : RayGroup M hM n =>
      (ClassFieldTransport.artin M hM n a).restrictScalars ℚ) := by
  intro a b h
  apply (ClassFieldTransport.artinEquiv M hM n).injective
  exact AlgEquiv.restrictScalars_injective ℚ h

end SICLean.L5.ClassFieldInfiniteAux
