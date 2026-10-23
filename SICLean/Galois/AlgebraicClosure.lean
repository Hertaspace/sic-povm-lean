import Mathlib

set_option autoImplicit false

/-!
# A fixed copy of ℚbar in ℂ and extension of its automorphisms

`embed` is chosen once in this file.
The extension across the transcendental part of ℂ uses a transcendence basis,
not an application of `liftNormal` to the nonalgebraic extension ℂ/ℚ.
-/

noncomputable section

namespace SICLean.Galois

/-- The actual subfield of algebraic complex numbers. -/
abbrev Qbar := algebraicClosure ℚ ℂ

-- Priority avoids the generic `DivisionRing.toRatAlgebra` taking precedence
-- over the intermediate-field algebra when later files import this module.
instance (priority := 1100) qbarRatAlgebra : Algebra ℚ Qbar :=
  (algebraicClosure ℚ ℂ).algebra

instance qbarIsAlgClosure : IsAlgClosure ℚ Qbar :=
  algebraicClosure.isAlgClosure ℚ ℂ

instance qbarIsAlgClosed : IsAlgClosed Qbar := IsAlgClosure.isAlgClosed ℚ

abbrev QbarAut := Qbar ≃ₐ[ℚ] Qbar

/-- All norms in the reciprocity interface refer to this embedding. -/
def embed : Qbar →ₐ[ℚ] ℂ := (algebraicClosure ℚ ℂ).val

theorem exists_preimage_iff_isAlgebraic (z : ℂ) :
    (∃ a : Qbar, embed a = z) ↔ IsAlgebraic ℚ z := by
  constructor
  · rintro ⟨a, rfl⟩
    exact mem_algebraicClosure_iff.mp a.property
  · intro hz
    exact ⟨⟨z, mem_algebraicClosure_iff.mpr hz⟩, rfl⟩

/-- The canonical algebraic representative of the same complex value. -/
def algebraicLift (z : ℂ) (hz : IsAlgebraic ℚ z) : Qbar :=
  Classical.choose ((exists_preimage_iff_isAlgebraic z).mpr hz)

theorem embed_algebraicLift (z : ℂ) (hz : IsAlgebraic ℚ z) :
    embed (algebraicLift z hz) = z := by
  exact Classical.choose_spec ((exists_preimage_iff_isAlgebraic z).mpr hz)

def Extends (σ : QbarAut) (T : ℂ ≃ₐ[ℚ] ℂ) : Prop :=
  ∀ a : Qbar, T (embed a) = embed (σ a)

/-- Extend by fixing a transcendence basis and extending the coefficient
automorphism to the algebraic closure over the resulting polynomial ring.
No continuity or commutation with complex conjugation is asserted. -/
theorem exists_complex_extension (σ : QbarAut) :
    ∃ T : ℂ ≃ₐ[ℚ] ℂ, Extends σ T := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis Qbar ℂ
  let v : s → ℂ := Subtype.val
  let A := Algebra.adjoin Qbar (Set.range v)
  let e : A ≃+* A :=
    hs.1.aevalEquiv.symm.toRingEquiv.trans
      ((MvPolynomial.mapEquiv s σ.toRingEquiv).trans hs.1.aevalEquiv.toRingEquiv)
  let : IsAlgClosure A ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let T : ℂ ≃+* ℂ := IsAlgClosure.equivOfEquiv ℂ ℂ e
  refine ⟨T.toRatAlgEquiv, ?_⟩
  intro a
  have hmap : e (algebraMap Qbar A a) = algebraMap Qbar A (σ a) := by
    simpa [e, MvPolynomial.mapEquiv_apply] using hs.1.aevalEquiv.commutes (σ a)
  have h := IsAlgClosure.equivOfEquiv_algebraMap ℂ ℂ e (algebraMap Qbar A a)
  simpa [T, hmap, embed, ← IsScalarTower.algebraMap_apply Qbar A ℂ] using h

/-- The ring homomorphism used by the L2 inputs. -/
theorem exists_complex_ringHom_extension (σ : QbarAut) :
    ∃ τ : ℂ →+* ℂ, ∀ a : Qbar, τ (embed a) = embed (σ a) := by
  obtain ⟨T, hT⟩ := exists_complex_extension σ
  exact ⟨T.toRingHom, hT⟩

/-- The fixed-embedding convention also covers an abstract model of ℚbar.
The chosen equivalence is part of the interface, not a new embedding chosen
for each special value. -/
theorem exists_complex_extension_of_model
    (A : Type*) [Field A] [Algebra ℚ A] (e : A ≃ₐ[ℚ] Qbar)
    (σ : A ≃ₐ[ℚ] A) :
    ∃ T : ℂ ≃ₐ[ℚ] ℂ,
      ∀ a : A, T (embed (e a)) = embed (e (σ a)) := by
  obtain ⟨T, hT⟩ := exists_complex_extension (e.symm.trans (σ.trans e))
  refine ⟨T, ?_⟩
  intro a
  simpa [Extends] using hT (e a)

end SICLean.Galois

#synth Algebra ℚ SICLean.Galois.Qbar
#synth IsAlgClosure ℚ SICLean.Galois.Qbar
#synth IsAlgClosed SICLean.Galois.Qbar
#check @IsAlgClosed.isAlgClosure_of_transcendence_basis
#check @IsAlgClosure.equivOfEquiv
#check @IsAlgClosure.equivOfEquiv_algebraMap
#check @SICLean.Galois.exists_complex_extension
#print SICLean.Galois.exists_complex_extension
