import SICLean.L4.G2ReflectionGeometry
import SICLean.L4.G2RepresentativeWindow
import SICLean.L4.G2RepellingPointValuesAux

set_option autoImplicit false

/-!
# Safe point values before inverse reflection

Eleven point-value specializations and inverse-reflection bridges. Notation follows
`G2ReflectionGeometry`. The existing germ and point-value interfaces, actual joint regularity and
lattice centers, and attracting values are reused. This file supplies their repelling
specializations and explicit continuity/cancellation obligations. It does not introduce another Φ,
φ, μ, square-root branch or q product.

`sIndex` is the existing concrete integer expression. Its congruence alone is not a test for the
zero class.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2.RepellingPointValues

open SICLean.L4.G2.ReflectionGeometry
open SICLean.L4.G2RepellingPointValuesAux

/-- The actual raw repelling expression. Its use as an F value is restricted to x∉Λ; its lattice
centers are not prescribed plus/minus zero values. [RW26, (2), p. 2]. -/
def repellingRaw (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℂ :=
  etaMultiplier M * modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ)

/-- [RW26, (2), p. 2]. The formula is valid on Λ as well. -/
theorem reflection_argument (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    specialValueArgument (modularInverseReflection M) (x.1, -x.2) =
      (argument M x : ℂ) / (epsilon M : ℂ) := by
  unfold specialValueArgument modularPhiSpecialArgument
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, reflection_tau M hM,
    Complex.ofReal_neg, Int.cast_neg]
  rw [(reflection_domains M hM).2.2.2, inv_inv, argument_complex]
  have hε := epsilon_complex_ne_zero M hM
  have h1ε := sub_ne_zero.mpr (epsilon_complex_ne_one M hM).symm
  have hε1 := sub_ne_zero.mpr (epsilon_complex_ne_one M hM)
  field_simp [hε, h1ε, hε1]
  ring

/-- Repelling specialization of the lattice test, with both directions. [RW26, Lemma 2, p. 12]. This
supplies the nonlattice input, without a dense-set avoidance claim. -/
theorem repellingArgument_mem_lattice_iff (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) :
    (argument M x : ℂ) ∈ modularPhiPseudoLattice (repellingTau M : ℂ) ↔
      x ∈ specialValueLattice M := by
  constructor
  · rintro ⟨k, l, hz⟩
    have hb := argument_balance M hM x
    have hm := modularPhi_lattice_mobius M k l (repellingTau M : ℂ)
      (reflection_domains M hM).1
    rw [repellingTau_fixedPoint M hM, etaDenom_repelling, ← hz] at hm
    have hrel : (((M 1 1 - 1) * k - M 1 0 * l - x.1 : ℤ) : ℂ) *
        (repellingTau M : ℂ) +
        (((M 0 0 - 1) * l - M 0 1 * k - x.2 : ℤ) : ℂ) = 0 := by
      rw [hz] at hb hm
      push_cast at hm ⊢
      linear_combination hb - hm
    have hr := m37b_irrational_relation (repellingTau M) (repellingTau_irrational M hM)
      _ _ hrel
    have hx1 : x.1 = (M 1 1 - 1) * k - M 1 0 * l := by omega
    have hx2 : x.2 = (M 0 0 - 1) * l - M 0 1 * k := by omega
    apply (specialValueLattice_mem_iff M hM x).mpr
    rw [L2r.rowAction, hx1, hx2]
    refine ⟨⟨-k, ?_⟩, ⟨-l, ?_⟩⟩
    · dsimp [specialValueOrder]
      linear_combination k * (det_coe_int M)
    · dsimp [specialValueOrder]
      linear_combination l * (det_coe_int M)
  · intro hx
    obtain ⟨p, q, hx1, hx2⟩ := lattice_coordinates M x hx
    exact ⟨-p * M 0 0 - q * M 1 0, -p * M 0 1 - q * M 1 1,
      row_argument M hM x p q hx1 hx2⟩

/-- [RW26, (16), p. 6]. Only a phase identity is asserted here, before index cancellation. -/
theorem repelling_phase (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    (e (repellingTau M : ℂ)) ^ x.1 * e (argument M x : ℂ) =
      e ((argument M x : ℂ) / (epsilon M : ℂ)) := by
  rw [e_int_mul, ← e_add', argument_balance M hM]
  simp only [e_add', e_intCast, mul_one]

/-- Every potentially cancelled factor is nonzero, only off Λ. [RW26, (16), p. 6, Lemma 2, p. 12].
-/
theorem repelling_index_factors_ne_zero (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) (hx : x ∉ specialValueLattice M)
    (j : ℤ) :
    1 - (e (repellingTau M : ℂ)) ^ (x.1 + j) * e (argument M x : ℂ) ≠ 0 := by
  intro hzero
  have he : e (((x.1 + j : ℤ) : ℂ) * (repellingTau M : ℂ) + (argument M x : ℂ)) = 1 := by
    rw [e_add', ← e_int_mul]
    exact (sub_eq_zero.mp hzero).symm
  obtain ⟨k, hk⟩ := e_eq_one_iff_int he
  apply hx
  apply (repellingArgument_mem_lattice_iff M hM x).mp
  refine ⟨-(x.1 + j), k, ?_⟩
  push_cast at hk ⊢
  linear_combination hk

/-- The specified finite-product representative has a genuine joint center. Apply
`modularPhi_real_off_lattice` and `modularPhi_joint_unit_neighborhood`. [RW26]. -/
theorem repellingPhi_joint_regular (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) (hx : x ∉ specialValueLattice M)
    (h : ℤ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M (x.1 + h) h p.1 p.2)
      ((argument M x : ℂ), (repellingTau M : ℂ)) ∧
      modularPhi M (x.1 + h) h (argument M x : ℂ) (repellingTau M : ℂ) ≠ 0 := by
  have hz : (argument M x : ℂ) ∉ modularPhiPseudoLattice (repellingTau M : ℂ) := by
    exact fun hz => hx ((repellingArgument_mem_lattice_iff M hM x).mp hz)
  have hp := modularPhi_real_off_lattice M hM.1 (x.1 + h) h (repellingTau M)
    (epsilon_pos M hM) (argument M x : ℂ) hz
  obtain ⟨U, _, hpU, _, ha, hn⟩ := modularPhi_joint_unit_neighborhood M hM.1
    (x.1 + h) h ((argument M x : ℂ), (repellingTau M : ℂ)) hp
  -- Specify the point before elaboration can unfold Φ to infer its projections.
  exact ⟨ha ((argument M x : ℂ), (repellingTau M : ℂ)) hpU,
    hn ((argument M x : ℂ), (repellingTau M : ℂ)) hpU⟩

/-- A point-value specialization of the existing diagonal-index theorem, after the nonzero factors
and both continuities above. No assertion on Λ. [RW26, (16), p. 6]. -/
theorem repellingPhi_diagonal_index (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) (hx : x ∉ specialValueLattice M)
    (h : ℤ) :
    modularPhi M (x.1 + h) h (argument M x : ℂ) (repellingTau M : ℂ) =
      modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ) := by
  have hp : 0 < (etaDenom M (repellingTau M : ℂ)).re := by
    simpa only [etaDenom_repelling, Complex.ofReal_re] using epsilon_pos M hM
  have hL := continuousAt_first (repellingPhi_joint_regular M hM x hx h).1
  have hR := continuousAt_first (repellingPhi_joint_regular M hM x hx 0).1
  have hd := modularPhi_diagonal_index_fixedPoint M hM.1 x.1 0 h
    (argument M x : ℂ) (repellingTau M) (repellingTau_fixedPoint M hM) hp
    (by simpa only [zpow_zero, one_mul, etaDenom_repelling] using repelling_phase M hM x)
    (repelling_index_factors_ne_zero M hM x hx)
    (by simpa only [zero_add] using hL)
    (by simpa only [add_zero] using hR)
  simpa only [zero_add] using hd

/-- The exact two continuity obligations in the existing point-value interface. The target is
composed with w↦w/ε, at the source center. [RW26, p. 6]. The proof uses repelling regularity and
target
regularity, not the germ alone. -/
theorem reflectionPhi_continuous (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) (hx : x ∉ specialValueLattice M) :
    ContinuousAt (fun w : ℂ => modularPhi (modularInverseReflection M) 1 (1 - x.1)
      (w / etaDenom M (repellingTau M : ℂ)) (-(repellingTau M : ℂ)))
      (argument M x : ℂ) ∧
    ContinuousAt (fun w : ℂ => modularPhi M x.1 0 w (repellingTau M : ℂ))
      (argument M x : ℂ) := by
  have hr := reflection_admissible M hM
  have hxR := reflected_not_mem M x hx
  have ht := (specialValuePhi_joint_regular (modularInverseReflection M) hr
    (x.1, -x.2) hxR (1 - x.1)).1
  have harg : specialValueArgument (modularInverseReflection M) (x.1, -x.2) =
      (argument M x : ℂ) / etaDenom M (repellingTau M : ℂ) := by
    rw [etaDenom_repelling, reflection_argument M hM]
  simp only [show x.1 + (1 - x.1) = 1 by omega, reflection_tau M hM, Complex.ofReal_neg,
    harg] at ht
  constructor
  · have hc : ContinuousAt (fun w : ℂ =>
        (w / etaDenom M (repellingTau M : ℂ), -(repellingTau M : ℂ)))
        (argument M x : ℂ) := by fun_prop
    exact ht.continuousAt.comp_of_eq
      (f := fun w : ℂ => (w / etaDenom M (repellingTau M : ℂ), -(repellingTau M : ℂ)))
      hc rfl
  · have hs := continuousAt_first (repellingPhi_joint_regular M hM x hx 0).1
    simpa only [add_zero] using hs

/-- First specialize the existing inverse-reflection point theorem. The target indices here remain
(1,1-x₁), before the safe common shift. [RW26, p. 6]. -/
theorem repellingPhi_inverse_reflection (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) (hx : x ∉ specialValueLattice M) :
    modularPhi (modularInverseReflection M) 1 (1 - x.1)
      (specialValueArgument (modularInverseReflection M) (x.1, -x.2))
      (specialValueTau (modularInverseReflection M) : ℂ) =
      modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ) := by
  have hc := reflectionPhi_continuous M hM x hx
  have hp : 0 < (etaDenom M (repellingTau M : ℂ)).re := by
    simpa only [etaDenom_repelling, Complex.ofReal_re] using epsilon_pos M hM
  have he := (modularPhi_inverse_reflection_fixedPoint M hM.1 x.1 0
    (argument M x : ℂ) (repellingTau M) (repellingTau_fixedPoint M hM) hp
    (by simpa only [sub_zero] using hc.1) hc.2).2.2
  simpa only [sub_zero, etaDenom_repelling, ← reflection_argument M hM,
    reflection_tau M hM, Complex.ofReal_neg] using he

/-- Then cancel the target common index 1-x₁ using regularity and factor avoidance, and reuse
`etaMultiplier_inverse_reflection` exactly. [RW26, (16), p. 6, μ]. No new or independently chosen μ
occurs in this equality. -/
theorem repellingRaw_reflection (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : x ∉ specialValueLattice M) :
    repellingRaw M x = specialValueRaw (modularInverseReflection M) (x.1, -x.2) := by
  have hr := reflection_admissible M hM
  have hxR := reflected_not_mem M x hx
  have hp : 0 < (etaDenom (modularInverseReflection M)
      (specialValueTau (modularInverseReflection M) : ℂ)).re := by
    rw [specialValue_etaDenom, Complex.ofReal_re]
    linarith [specialValueEpsilon_gt_one (modularInverseReflection M) hr]
  have hL := continuousAt_first (specialValuePhi_joint_regular (modularInverseReflection M)
    hr (x.1, -x.2) hxR (1 - x.1)).1
  have hR := continuousAt_first (specialValuePhi_joint_regular (modularInverseReflection M)
    hr (x.1, -x.2) hxR 0).1
  have hd := modularPhi_diagonal_index_fixedPoint (modularInverseReflection M) hr.1
    x.1 0 (1 - x.1) (specialValueArgument (modularInverseReflection M) (x.1, -x.2))
    (specialValueTau (modularInverseReflection M))
    (specialValueTau_fixedPoint (modularInverseReflection M) hr) hp
    (by simpa only [Prod.fst, zpow_zero, one_mul, specialValue_etaDenom] using
      specialValue_phase (modularInverseReflection M) hr (x.1, -x.2))
    (specialValue_index_factors_ne_zero (modularInverseReflection M) hr (x.1, -x.2) hxR)
    (by simpa only [Prod.fst, zero_add] using hL)
    (by simpa only [Prod.fst, add_zero] using hR)
  simp only [show x.1 + (1 - x.1) = 1 by omega, zero_add] at hd
  unfold repellingRaw specialValueRaw
  rw [etaMultiplier_inverse_reflection M hM.1, ← hd, repellingPhi_inverse_reflection M hM x hx]

/-- Only for the true zero class: expose k,l and the balanced common exponent r_h=h-S_x/N, using
integer division with exact divisibility. [RW26, Lemma 2, p. 12]. -/
theorem repelling_lattice_common_exponent (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) (hx : x ∈ specialValueLattice M)
    (h : ℤ) :
    specialValueOrder M ∣ sIndex M x ∧
      ∃ k l : ℤ,
        (argument M x : ℂ) = (k : ℂ) * (repellingTau M : ℂ) + (l : ℂ) ∧
        k + (x.1 + h) = M 1 1 * k - M 1 0 * l + h ∧
        k + (x.1 + h) = h - sIndex M x / specialValueOrder M := by
  obtain ⟨p, q, hx1, hx2⟩ := lattice_coordinates M x hx
  -- The first coordinate of the row-lattice witness is the exact quotient S_x/N.
  have hs : sIndex M x = specialValueOrder M * p := by
    dsimp [sIndex, specialValueOrder]
    rw [hx1, hx2]
    linear_combination -p * (det_coe_int M)
  have hdiv : sIndex M x / specialValueOrder M = p := by
    rw [hs, Int.mul_ediv_cancel_left _ (specialValueOrder_pos M hM).ne']
  refine ⟨⟨p, hs⟩, -p * M 0 0 - q * M 1 0, -p * M 0 1 - q * M 1 1,
    row_argument M hM x p q hx1 hx2, ?_, ?_⟩
  · rw [hx1]
    linear_combination p * (det_coe_int M)
  · rw [hx1, hdiv]
    ring

/-- Downstream zero-class evaluator, just the lattice-center theorem specialized using the preceding
exponent; it does not reprove that theorem. [RW26, p. 12]. Because this is the repelling branch, r≥1
gives μ⁻¹ A and r≤0 gives μ⁻¹ A⁻¹. The jump at r=0→1 is retained, not cancelled by a diagonal
identity. -/
theorem repelling_lattice_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : x ∈ specialValueLattice M) (h : ℤ) :
    modularPhi M (x.1 + h) h (argument M x : ℂ) (repellingTau M : ℂ) =
      if 1 ≤ h - sIndex M x / specialValueOrder M then
        (etaMultiplier M)⁻¹ / (Real.sqrt (epsilon M) : ℂ)
      else (etaMultiplier M)⁻¹ * (Real.sqrt (epsilon M) : ℂ) := by
  obtain ⟨_, k, l, harg, hbalance, hexponent⟩ :=
    repelling_lattice_common_exponent M hM x hx h
  rw [harg]
  simpa only [hexponent, epsilon, g1T] using modularPhi_fixedPoint_lattice_value M hM.1 hM.2
    (x.1 + h) h (repellingTau M) (epsilon_pos M hM) (repellingTau_fixedPoint M hM)
    k l hbalance

#check @modularPhi_real_off_lattice
#check @modularPhi_joint_unit_neighborhood
#check @modularPhi_diagonal_index_fixedPoint
#check @modularPhi_inverse_reflection_fixedPoint
#check @modularPhi_fixedPoint_lattice_joint
#check @modularPhi_fixedPoint_lattice_value
#print repellingRaw
#check reflectionPhi_continuous
#check repelling_lattice_value

end SICLean.L4.G2.RepellingPointValues
