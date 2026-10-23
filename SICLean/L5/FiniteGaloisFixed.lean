import SICLean.L5.FiniteGaloisEnvelope

set_option autoImplicit false

/-!
# Fixing every conjugate and descent to the base subfield

[RW-rec, Prop. 4, pp. 14--15]. Algebraicity of the values is [RW26, Thm. 1, p. 3].
Mathlib: `Normal/Closure.lean`, `Normal/Defs.lean`,
`Galois/Basic.lean`, `IsGalois.fixedField_fixingSubgroup`.

The all-conjugates hypothesis quantifies over `Gal(F/ℚ)`.
For an absolute automorphism the conclusion is the identity on `F`.
The final statements are the form used with a Chebotarev hypothesis.
-/

noncomputable section

open SICLean.Galois

namespace SICLean.L5.FiniteGaloisFixed

open FiniteGaloisEnvelope

/-- The same value, merely viewed in the actual finite envelope. -/
def valueInEnvelope (H : IntermediateField ℚ Qbar) (S : Finset Qbar)
    (u : S) : envelope H S :=
  ⟨u.1, subset_envelope H S u.2⟩

/-- Universal property of literal field adjunction. -/
theorem fixes_generatedField_iff (h : QbarAut) (S : Finset Qbar) :
    (∀ x ∈ generatedField S, h x = x) ↔ ∀ u ∈ S, h u = u := by
  simpa only [generatedField, AlgEquiv.smul_def, Finset.mem_coe] using
    (IntermediateField.forall_mem_adjoin_smul_eq_self_iff ℚ (S := (S : Set Qbar)) h)

/-- Universal property of the compositum. -/
theorem fixes_sup_iff (h : QbarAut) (E T : IntermediateField ℚ Qbar) :
    (∀ x ∈ E ⊔ T, h x = x) ↔
      (∀ x ∈ E, h x = x) ∧ (∀ x ∈ T, h x = x) := by
  rw [← IntermediateField.mem_fixingSubgroup_iff, IntermediateField.fixingSubgroup_sup,
    Subgroup.mem_inf, IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]

/-- Explicit conjugation direction for an image subfield. -/
theorem fixes_map_iff (h g : QbarAut) (E : IntermediateField ℚ Qbar) :
    (∀ x ∈ E.map (g : Qbar →ₐ[ℚ] Qbar), h x = x) ↔
      ∀ x ∈ E, (g⁻¹ * h * g) x = x := by
  constructor
  · intro hf x hx
    have hfix := hf (g x) ⟨x, hx, rfl⟩
    change g.symm (h (g x)) = x
    rw [hfix, g.symm_apply_apply]
  · intro hf y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change h (g x) = g x
    have hx' := congrArg g (hf x hx)
    simpa only [AlgEquiv.mul_apply, AlgEquiv.coe_inv, AlgEquiv.apply_symm_apply] using hx'

/-- Normality of H is essential for this consequence. -/
theorem conjugate_fixes_base (H : IntermediateField ℚ Qbar) [Normal ℚ H]
    (h : QbarAut) (hH : ∀ x ∈ H, h x = x) (g : QbarAut) :
    ∀ x ∈ H, (g⁻¹ * h * g) x = x := by
  apply (fixes_map_iff h g H).mp
  rwa [IntermediateField.normal_iff_forall_map_eq'.mp (inferInstance : Normal ℚ H) g]

/-- Mathlib `IntermediateField.normalClosure_def''` and the previous image-field identity. -/
theorem fixes_normalClosure_iff (h : QbarAut) (E : IntermediateField ℚ Qbar) :
    (∀ x ∈ IntermediateField.normalClosure ℚ E Qbar, h x = x) ↔
      ∀ g : QbarAut, ∀ x ∈ E, (g⁻¹ * h * g) x = x := by
  change IntermediateField.normalClosure ℚ E Qbar ≤
    FixedBy.intermediateField ℚ Qbar h ↔ _
  rw [IntermediateField.normalClosure_def'', iSup_le_iff]
  exact forall_congr' fun g => fixes_map_iff h g E

/-- The generated field contains every conjugate of the values. -/
theorem envelope_eq_sup_conjugates (H : IntermediateField ℚ Qbar) [Normal ℚ H]
    (S : Finset Qbar) :
    envelope H S = H ⊔ ⨆ g : QbarAut,
      (generatedField S).map (g : Qbar →ₐ[ℚ] Qbar) := by
  rw [envelope, IntermediateField.normalClosure_def'']
  simp_rw [IntermediateField.map_sup,
    IntermediateField.normal_iff_forall_map_eq'.mp (inferInstance : Normal ℚ H)]
  exact sup_iSup.symm

/-- Absolute-automorphism form of the generation argument. -/
theorem fixes_envelope_of_all_conjugates_fix_values
    (H : IntermediateField ℚ Qbar) [Normal ℚ H] (S : Finset Qbar)
    (h : QbarAut) (hH : ∀ x ∈ H, h x = x)
    (hS : ∀ g : QbarAut, ∀ u ∈ S, (g⁻¹ * h * g) u = u) :
    ∀ x ∈ envelope H S, h x = x := by
  apply (fixes_normalClosure_iff h (H ⊔ generatedField S)).mpr
  intro g
  exact (fixes_sup_iff (g⁻¹ * h * g) H (generatedField S)).mpr
    ⟨conjugate_fixes_base H h hH g,
      (fixes_generatedField_iff (g⁻¹ * h * g) S).mpr (hS g)⟩

/-- Same conclusion as an equality of finite-field automorphisms. -/
theorem restrictQbarAut_eq_one_of_all_conjugates_fix_values
    (H : IntermediateField ℚ Qbar) [Normal ℚ H] (S : Finset Qbar)
    (h : QbarAut) (hH : ∀ x ∈ H, h x = x)
    (hS : ∀ g : QbarAut, ∀ u ∈ S, (g⁻¹ * h * g) u = u) :
    restrictQbarAut H S h = 1 := by
  exact (restrictQbarAut_eq_one_iff H S h).mpr
    (fixes_envelope_of_all_conjugates_fix_values H S h hH hS)

/-- Finite-Galois form used after ranging over all primes above p. -/
theorem finite_aut_eq_one_of_all_conjugates_fix_values
    (H : IntermediateField ℚ Qbar) [NumberField H] [Normal ℚ H] (S : Finset Qbar)
    (h : envelope H S ≃ₐ[ℚ] envelope H S)
    (hH : ∀ x : envelope H S, (x : Qbar) ∈ H → h x = x)
    (hS : ∀ g : envelope H S ≃ₐ[ℚ] envelope H S, ∀ u : S,
      (g⁻¹ * h * g) (valueInEnvelope H S u) = valueInEnvelope H S u) :
    h = 1 := by
  obtain ⟨h', rfl⟩ := restrictQbarAut_surjective H S h
  apply restrictQbarAut_eq_one_of_all_conjugates_fix_values H S h'
  · intro x hx
    let x' : envelope H S := ⟨x, le_envelope H S hx⟩
    have hfix := congrArg (fun y : envelope H S => (y : Qbar)) (hH x' hx)
    simpa only [restrictQbarAut_apply] using hfix
  · intro g u hu
    have hfix := hS (restrictQbarAut H S g) ⟨u, hu⟩
    rw [← map_inv, ← map_mul, ← map_mul] at hfix
    have hval := congrArg (fun y : envelope H S => (y : Qbar)) hfix
    simpa only [restrictQbarAut_apply, valueInEnvelope] using hval

/-- Fixed-field theorem, without assuming the value lies in H. -/
theorem mem_base_of_all_fixers_fix
    (H : IntermediateField ℚ Qbar) [NumberField H] (S : Finset Qbar)
    (u : envelope H S)
    (hu : ∀ h : envelope H S ≃ₐ[ℚ] envelope H S,
      (∀ x : envelope H S, (x : Qbar) ∈ H → h x = x) → h u = u) :
    (u : Qbar) ∈ H := by
  let K : IntermediateField ℚ (envelope H S) := H.comap (envelope H S).val
  have huK : u ∈ K := by
    rw [← IsGalois.fixedField_fixingSubgroup K]
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    apply hu σ
    exact (IntermediateField.mem_fixingSubgroup_iff K σ).mp hσ
  exact huK

/-- Simultaneous descent, for a Chebotarev hypothesis. -/
theorem subset_base_of_all_fixers_fix
    (H : IntermediateField ℚ Qbar) [NumberField H] (S : Finset Qbar)
    (hS : ∀ h : envelope H S ≃ₐ[ℚ] envelope H S,
      (∀ x : envelope H S, (x : Qbar) ∈ H → h x = x) →
      ∀ u : S, h (valueInEnvelope H S u) = valueInEnvelope H S u) :
    (S : Set Qbar) ⊆ H := by
  intro u hu
  exact mem_base_of_all_fixers_fix H S (valueInEnvelope H S ⟨u, hu⟩)
    (fun h hH => hS h hH ⟨u, hu⟩)

/-- Equality of subfields requires H itself to be normal over ℚ. -/
theorem envelope_eq_base_of_all_fixers_fix
    (H : IntermediateField ℚ Qbar) [NumberField H] [Normal ℚ H] (S : Finset Qbar)
    (hS : ∀ h : envelope H S ≃ₐ[ℚ] envelope H S,
      (∀ x : envelope H S, (x : Qbar) ∈ H → h x = x) →
      ∀ u : S, h (valueInEnvelope H S u) = valueInEnvelope H S u) :
    envelope H S = H := by
  exact le_antisymm
    ((envelope_le_iff H H S).mpr ⟨le_rfl, subset_base_of_all_fixers_fix H S hS⟩)
    (le_envelope H S)

end SICLean.L5.FiniteGaloisFixed

#check @SICLean.L5.FiniteGaloisFixed.finite_aut_eq_one_of_all_conjugates_fix_values
#check @SICLean.L5.FiniteGaloisFixed.mem_base_of_all_fixers_fix
#print SICLean.L5.FiniteGaloisFixed.valueInEnvelope
