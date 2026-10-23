import SICLean.L4.SpecialValueGeometry

set_option autoImplicit false

/-!
Elementary parameter algebra and descent helpers for the actual special values.
The analytic inputs are the fixed upstream divisor and diagonal-shift theorems.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.SpecialValueDescentAux

lemma epsilon_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (specialValueEpsilon M : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)))

lemma denominator_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (specialValueEpsilon M : ℂ)⁻¹ - 1 ≠ 0 := by
  have hε : (specialValueEpsilon M : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_gt (specialValueEpsilon_gt_one M hM))
  intro h
  exact hε (inv_eq_one.mp (sub_eq_zero.mp h))

lemma argument_eq (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    specialValueArgument M u =
      ((u.1 : ℂ) * (specialValueTau M : ℂ) + (u.2 : ℂ)) /
        ((specialValueEpsilon M : ℂ)⁻¹ - 1) := by
  simp only [specialValueArgument, modularPhiSpecialArgument,
    Matrix.cons_val_zero, Matrix.cons_val_one, specialValue_etaDenom]

lemma argument_add (M : SL(2, ℤ)) (u v : ℤ × ℤ) :
    specialValueArgument M (u + v) = specialValueArgument M u + specialValueArgument M v := by
  simp only [argument_eq, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

lemma argument_balance (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) :
    specialValueArgument M u / (specialValueEpsilon M : ℂ) =
      specialValueArgument M u + (u.1 : ℂ) * (specialValueTau M : ℂ) + (u.2 : ℂ) := by
  have h := (eq_div_iff (denominator_ne_zero M hM)).mp (argument_eq M u)
  calc
    specialValueArgument M u / (specialValueEpsilon M : ℂ) =
        specialValueArgument M u + specialValueArgument M u *
          ((specialValueEpsilon M : ℂ)⁻¹ - 1) := by ring
    _ = _ := by rw [h]; ring

lemma phase (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) :
    (e (specialValueTau M : ℂ)) ^ u.1 * e (specialValueArgument M u) =
      e (specialValueArgument M u / (specialValueEpsilon M : ℂ)) := by
  rw [e_int_mul, argument_balance M hM u, e_add', e_intCast, mul_one, e_add']
  exact mul_comm _ _

lemma index_factors_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) (j : ℤ) :
    1 - (e (specialValueTau M : ℂ)) ^ (u.1 + j) * e (specialValueArgument M u) ≠ 0 := by
  intro h
  have he : e (((u.1 + j : ℤ) : ℂ) * (specialValueTau M : ℂ) +
      specialValueArgument M u) = 1 := by
    rw [e_add', ← e_int_mul]
    exact (sub_eq_zero.mp h).symm
  obtain ⟨k, hk⟩ := e_eq_one_iff_int he
  apply hu
  apply (specialValueArgument_mem_lattice_iff M hM u).mp
  refine ⟨-(u.1 + j), k, ?_⟩
  push_cast at hk ⊢
  linear_combination hk

lemma joint_regular (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) (m n : ℤ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2)
      (specialValueArgument M u, (specialValueTau M : ℂ)) ∧
    modularPhi M m n (specialValueArgument M u) (specialValueTau M : ℂ) ≠ 0 := by
  have hε : 0 < (M 1 0 : ℝ) * specialValueTau M + (M 1 1 : ℝ) :=
    lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)
  have hz : specialValueArgument M u ∉ modularPhiPseudoLattice (specialValueTau M : ℂ) :=
    fun h => hu ((specialValueArgument_mem_lattice_iff M hM u).mp h)
  have hp := modularPhi_real_off_lattice M hM.1 m n (specialValueTau M) hε
    (specialValueArgument M u) hz
  refine ⟨modularPhi_joint_analytic_no_poles M hM.1 m n _ ⟨hp.1, hp.2.1⟩, ?_⟩
  exact (modularPhi_ne_zero_iff M hM.1 m n _ _ hp.1 hp.2.1).mpr hp.2.2

lemma continuous_phi (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) (m n : ℤ) :
    ContinuousAt (fun z => modularPhi M m n z (specialValueTau M : ℂ))
      (specialValueArgument M u) := by
  have ha := (joint_regular M hM u hu m n).1.continuousAt
  exact ha.comp (f := fun z : ℂ => (z, (specialValueTau M : ℂ))) (by fun_prop)

/--
A row in Λ gives a pseudolattice translation with matching shifted indices.
Using the forward row range avoids constructing Φ for the negative-c inverse.
-/
lemma lattice_shift (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (hv : v ∈ specialValueLattice M) :
    ∃ k l : ℤ, specialValueArgument M v = (k : ℂ) * (specialValueTau M : ℂ) + (l : ℂ) ∧
      v.1 + k = M 1 1 * k - M 1 0 * l := by
  change ∃ w, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w = v at hv
  obtain ⟨w, rfl⟩ := hv
  let p := L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w
  have hvp : L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w = p - w := by
    ext <;> simp [p, L2r.rowAction, Matrix.sub_apply] <;> ring
  have hrow : (p.1 : ℂ) * (specialValueTau M : ℂ) + (p.2 : ℂ) =
      (specialValueEpsilon M : ℂ) *
        ((w.1 : ℂ) * (specialValueTau M : ℂ) + (w.2 : ℂ)) := by
    have hr := ModularCocycleUnitAux.row_fixedPoint M ![w.1, w.2] (specialValueTau M : ℂ)
      (specialValueTau_fixedPoint M hM)
      (by rw [specialValue_etaDenom]; exact epsilon_ne_zero M hM)
    simpa [p, L2r.rowAction, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      specialValue_etaDenom] using hr
  have hi : M 1 1 * p.1 - M 1 0 * p.2 = w.1 := by
    simpa [p, L2r.rowAction, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using
      ModularCocycleUnitAux.row_second_index M ![w.1, w.2]
  refine ⟨-p.1, -p.2, ?_, ?_⟩
  · rw [hvp, argument_eq]
    simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Int.cast_neg]
    apply (div_eq_iff (denominator_ne_zero M hM)).mpr
    calc
      ((p.1 : ℂ) - (w.1 : ℂ)) * (specialValueTau M : ℂ) + ((p.2 : ℂ) - (w.2 : ℂ)) =
          ((p.1 : ℂ) * (specialValueTau M : ℂ) + (p.2 : ℂ)) -
            ((w.1 : ℂ) * (specialValueTau M : ℂ) + (w.2 : ℂ)) := by ring
      _ = (-(p.1 : ℂ) * (specialValueTau M : ℂ) + -(p.2 : ℂ)) *
          ((specialValueEpsilon M : ℂ)⁻¹ - 1) := by
        have hneg : -(p.1 : ℂ) * (specialValueTau M : ℂ) + -(p.2 : ℂ) =
            -((p.1 : ℂ) * (specialValueTau M : ℂ) + (p.2 : ℂ)) := by ring
        rw [hneg, hrow]
        field_simp [epsilon_ne_zero M hM]
        ring
  · rw [hvp]
    simp only [Prod.fst_sub]
    linear_combination hi

lemma phi_periodic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hu : u ∉ specialValueLattice M) (hv : v ∈ specialValueLattice M) :
    modularPhi M (u + v).1 0 (specialValueArgument M (u + v)) (specialValueTau M : ℂ) =
      modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ) := by
  obtain ⟨k, l, harg, hind⟩ := lattice_shift M hM v hv
  have hshift := modularPhi_shift_integer M hM.1 (u + v).1 0 k l
    (specialValueArgument M u) (specialValueTau M : ℂ)
  have harg' : specialValueArgument M (u + v) =
      specialValueArgument M u + (k : ℂ) * (specialValueTau M : ℂ) + (l : ℂ) := by
    rw [argument_add, harg]
    ring
  rw [harg', hshift]
  simp only [Prod.fst_add, zero_add]
  rw [add_assoc, hind]
  have hT : 0 < (etaDenom M (specialValueTau M : ℂ)).re := by
    rw [specialValue_etaDenom, Complex.ofReal_re]
    exact lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)
  have heq := modularPhi_diagonal_index_fixedPoint M hM.1 u.1 0
    (M 1 1 * k - M 1 0 * l) (specialValueArgument M u) (specialValueTau M)
    (specialValueTau_fixedPoint M hM) hT
    (by simpa only [zpow_zero, one_mul, specialValue_etaDenom] using phase M hM u)
    (index_factors_ne_zero M hM u hu)
    (continuous_phi M hM u hu (u.1 + (M 1 1 * k - M 1 0 * l))
      (0 + (M 1 1 * k - M 1 0 * l)))
    (continuous_phi M hM u hu u.1 0)
  simpa only [zero_add] using heq

/-- A separately prescribed lattice constant descends with the nonlattice raw value. -/
lemma piecewise_periodic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (C : ℂ) (u v : ℤ × ℤ) (hv : v ∈ specialValueLattice M) :
    (if u + v ∈ specialValueLattice M then C else etaMultiplier M *
      modularPhi M (u + v).1 0 (specialValueArgument M (u + v)) (specialValueTau M : ℂ)) =
    (if u ∈ specialValueLattice M then C else etaMultiplier M *
      modularPhi M u.1 0 (specialValueArgument M u) (specialValueTau M : ℂ)) := by
  have hmem : u + v ∈ specialValueLattice M ↔ u ∈ specialValueLattice M :=
    (specialValueLattice M).add_mem_cancel_right hv
  by_cases hu : u ∈ specialValueLattice M
  · simp only [if_pos hu, if_pos (hmem.mpr hu)]
  · simp only [if_neg hu, if_neg (mt hmem.mp hu)]
    rw [phi_periodic M hM u v hu hv]

end SICLean.L4.SpecialValueDescentAux
