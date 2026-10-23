import SICLean.L4.UpperContourGeometry

set_option autoImplicit false

noncomputable section
open Complex Set Filter
open scoped Topology MatrixGroups

namespace SICLean.L4.UpperResidueParametersAux

open UpperWindow

/-- The two extra residue arguments, in the same `(T,1)` coordinates as the window. -/
theorem argument_norms (M : SL(2, ℤ)) (hM : 0 < M 1 0) (p : ℤ)
    (ψ : ℝ) (τ y : ℂ) (hτ : τ ∈ tauRegion M ψ) :
    ‖(e τ) ^ p * e y‖ = Real.rpow ‖e τ‖ (coords (etaDenom M τ) (height M p τ y)).1 ∧
      ‖e (y / etaDenom M τ)‖ = Real.rpow ‖e (etaMobius M τ)‖
        (1 - (coords (etaDenom M τ) (height M p τ y)).2) := by
  have hn := ABC_norms M hM 0 p p ψ τ y 0 hτ
  have hh : height M p τ y = s M 0 p τ y + 1 := by
    simp only [height, s, Int.cast_zero, add_zero]
    ring
  have h1 : coords (etaDenom M τ) (1 : ℂ) = (0, 1) := by simp [coords]
  rw [hh, coords_add, h1]
  constructor
  · simpa [A] using hn.1
  · simpa [C, e] using hn.2.1

/-- A nonzero actual Φ value excludes both actual divisor families. -/
theorem mem_unit_of_ne_zero (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) (hne : modularPhi M m n z τ ≠ 0) :
    (z, τ) ∈ modularPhiNonvanishingDomain M m n := by
  have hdom := mem_modularPhiDomain_of_im_pos M hM hτ
  have hp : modularPhiPoleMultiplicity M m n z τ = 0 := by
    by_contra hp
    exact hne (modularPhi_pole_value M hM m n z τ hdom hp)
  exact ⟨hdom, hp, (modularPhi_ne_zero_iff M hM m n z τ hdom hp).mp hne⟩

/-- The q quotient is a point value and a unit when both displayed products are units. -/
theorem phi_unit_of_q_products (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im)
    (hn : modularPhiQNumerator m z τ ≠ 0)
    (hd : modularPhiQDenominator M n z τ ≠ 0) :
    modularPhi M m n z τ = modularPhiQProduct M m n z τ ∧
      (z, τ) ∈ modularPhiNonvanishingDomain M m n ∧ modularPhi M m n z τ ≠ 0 := by
  have heq := modularPhi_eq_qProduct M hM m n z τ hτ hd
  have hne : modularPhi M m n z τ ≠ 0 := by
    rw [heq]
    exact div_ne_zero hn hd
  exact ⟨heq, mem_unit_of_ne_zero M hM m n z τ hτ hne, hne⟩

/-- The pole-label congruence makes the error in the residue phase an integer. -/
theorem phase_pole_integer (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n h ℓ : ℤ)
    (τ w : ℂ) (hτ : 0 < τ.im) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    ∃ r : ℤ, phase M m n h ℓ τ w
        (modularPhiPolePoint M (m + 1) n τ k.1 k.2) =
      (k.1 : ℂ) * ((ℓ : ℂ) * τ + w) +
        (k.2 : ℂ) * ((-h : ℤ) * etaMobius M τ + w / etaDenom M τ) + (r : ℂ) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hT := ModularCocycleUpperAux.etaDenom_ne_zero_upper M hτ
  have hk' : Int.ModEq (M 1 0) ((k.2 : ℤ) + M 1 1 * (k.1 : ℤ))
      (M 1 1 * m - n) := by simpa [modularPhiPoleLabels] using hk
  obtain ⟨r, hr⟩ := Int.modEq_iff_dvd.mp hk'.symm
  have hrC : (k.2 : ℂ) + (M 1 1 : ℂ) * (k.1 : ℂ) -
      ((M 1 1 : ℂ) * (m : ℂ) - (n : ℂ)) = (M 1 0 : ℂ) * (r : ℂ) := by
    exact_mod_cast hr
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by
    exact_mod_cast det_coe_int M
  let u : ℤ := M 0 0 * r - M 0 1 * ((k.1 : ℤ) - m)
  have hz : modularPhiPolePoint M (m + 1) n τ k.1 k.2 =
      ((k.1 : ℂ) - (m : ℂ)) * τ + (r : ℂ) := by
    unfold modularPhiPolePoint etaDenom
    push_cast
    apply (div_eq_iff hc).mpr
    linear_combination hrC
  have hm : modularPhiPolePoint M (m + 1) n τ k.1 k.2 / etaDenom M τ +
      (n : ℂ) * etaMobius M τ =
        -(k.2 : ℂ) * etaMobius M τ + (u : ℂ) := by
    rw [hz]
    unfold etaMobius
    field_simp [hT]
    dsimp [u, etaDenom]
    push_cast
    linear_combination ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) * hrC -
      (((k.1 : ℂ) - (m : ℂ)) * τ + (r : ℂ)) * hdet
  have hnum : (M 1 0 : ℂ) * modularPhiPolePoint M (m + 1) n τ k.1 k.2 -
      (n : ℂ) + etaDenom M τ * (m : ℂ) =
        (k.1 : ℂ) * etaDenom M τ + (k.2 : ℂ) := by
    unfold modularPhiPolePoint
    push_cast
    field_simp [hc]
    ring
  refine ⟨ℓ * r + h * u, ?_⟩
  unfold phase
  rw [hnum, hm, hz]
  push_cast
  field_simp [hT]
  ring

end SICLean.L4.UpperResidueParametersAux
