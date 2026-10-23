import SICLean.L4.G2ReflectionGeometry
import SICLean.L4.G2RepresentativeWindow

set_option autoImplicit false

/-!
# Auxiliaries for the repelling point-value bridge

These are cast identities, the balanced special argument, explicit row-lattice coordinates, and
restrictions of joint regularity. No new analytic function or multiplier is defined. All auxiliary
declarations stay in this file's namespace.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2RepellingPointValuesAux

open SICLean.L4.G2

lemma etaDenom_repelling (M : SL(2, ℤ)) :
    etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
  simp [etaDenom, epsilon, g1T]

lemma epsilon_complex_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (epsilon M : ℂ) ≠ 0 := by
  exact_mod_cast (epsilon_pos M hM).ne'

lemma epsilon_complex_ne_one (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (epsilon M : ℂ) ≠ 1 := by
  exact_mod_cast (epsilon_lt_one M hM).ne

lemma argument_complex (M : SL(2, ℤ)) (x : ℤ × ℤ) :
    (argument M x : ℂ) =
      ((x.1 : ℂ) * (repellingTau M : ℂ) + (x.2 : ℂ)) /
        ((epsilon M : ℂ)⁻¹ - 1) := by
  simp [argument]

lemma argument_balance (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    (argument M x : ℂ) / (epsilon M : ℂ) =
      (x.1 : ℂ) * (repellingTau M : ℂ) + (argument M x : ℂ) + (x.2 : ℂ) := by
  rw [argument_complex]
  have hε := epsilon_complex_ne_zero M hM
  have h1ε := sub_ne_zero.mpr (epsilon_complex_ne_one M hM).symm
  field_simp [hε, h1ε]
  ring

lemma lattice_coordinates (M : SL(2, ℤ)) (x : ℤ × ℤ)
    (hx : x ∈ specialValueLattice M) :
    ∃ p q : ℤ, x.1 = p * (M 0 0 - 1) + q * M 1 0 ∧
      x.2 = p * M 0 1 + q * (M 1 1 - 1) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := hx
  change L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) (p, q) = x at hpq
  refine ⟨p, q, ?_, ?_⟩
  · simpa [L2r.rowAction, Matrix.sub_apply] using (congrArg Prod.fst hpq).symm
  · simpa [L2r.rowAction, Matrix.sub_apply] using (congrArg Prod.snd hpq).symm

lemma reflected_not_mem (M : SL(2, ℤ)) (x : ℤ × ℤ)
    (hx : x ∉ specialValueLattice M) :
    (x.1, -x.2) ∉ specialValueLattice (modularInverseReflection M) := by
  intro hr
  rw [← ReflectionGeometry.rowReflection_lattice] at hr
  obtain ⟨y, hy, hye⟩ := hr
  change ReflectionGeometry.rowReflection y = ReflectionGeometry.rowReflection x at hye
  exact hx ((ReflectionGeometry.rowReflection.injective hye) ▸ hy)

lemma continuousAt_first {f : ℂ × ℂ → ℂ} {z τ : ℂ}
    (hf : AnalyticAt ℂ f (z, τ)) : ContinuousAt (fun w => f (w, τ)) z := by
  have hc : ContinuousAt (fun w : ℂ => (w, τ)) z := by fun_prop
  exact hf.continuousAt.comp_of_eq hc rfl

lemma fixed_numerator (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (M 0 0 : ℂ) * (repellingTau M : ℂ) + (M 0 1 : ℂ) =
      (repellingTau M : ℂ) * (epsilon M : ℂ) := by
  have hf := repellingTau_fixedPoint M hM
  change ((M 0 0 : ℂ) * (repellingTau M : ℂ) + (M 0 1 : ℂ)) /
    etaDenom M (repellingTau M : ℂ) = (repellingTau M : ℂ) at hf
  rw [etaDenom_repelling] at hf
  exact (div_eq_iff (epsilon_complex_ne_zero M hM)).mp hf

lemma row_argument (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (p q : ℤ)
    (hx1 : x.1 = p * (M 0 0 - 1) + q * M 1 0)
    (hx2 : x.2 = p * M 0 1 + q * (M 1 1 - 1)) :
    (argument M x : ℂ) =
      ((-p * M 0 0 - q * M 1 0 : ℤ) : ℂ) * (repellingTau M : ℂ) +
        ((-p * M 0 1 - q * M 1 1 : ℤ) : ℂ) := by
  have hε := epsilon_complex_ne_zero M hM
  have hε1 := epsilon_complex_ne_one M hM
  have hden : (epsilon M : ℂ)⁻¹ - 1 ≠ 0 := by
    simpa only [ne_eq, sub_eq_zero, inv_eq_one] using hε1
  have hf := fixed_numerator M hM
  have ht : (M 1 0 : ℂ) * (repellingTau M : ℂ) + (M 1 1 : ℂ) =
      (epsilon M : ℂ) := (etaDenom_repelling M)
  rw [argument_complex, div_eq_iff hden, hx1, hx2]
  push_cast
  field_simp [hε]
  linear_combination (p : ℂ) * hf + (q : ℂ) * ht

end SICLean.L4.G2RepellingPointValuesAux
