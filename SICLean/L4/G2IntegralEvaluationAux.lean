import SICLean.L4.G2RepresentativeWindow

set_option autoImplicit false

/-!
Repelling-point coordinate and unit lemmas for integral evaluation. The lattice arguments use the
full row lattice, not an S-index congruence. Analyticity comes from the actual modularPhi
divisor-free domain.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2IntegralEvaluationAux
open G2

lemma mk_eq_zero_iff (M : SL(2, ℤ)) (x : ℤ × ℤ) :
    specialValueMk M x = 0 ↔ x ∈ specialValueLattice M := by
  change QuotientAddGroup.mk x = 0 ↔ _
  exact QuotientAddGroup.eq_zero_iff x

lemma etaDenom_eq (M : SL(2, ℤ)) :
    etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
  simp [etaDenom, G2.epsilon, g1T]

lemma epsilon_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (epsilon M : ℂ) ≠ 0 := by
  exact_mod_cast (epsilon_pos M hM).ne'

lemma sIndex_add (M : SL(2, ℤ)) (u v : ℤ × ℤ) :
    sIndex M (u + v) = sIndex M u + sIndex M v := by
  simp only [sIndex, Prod.fst_add, Prod.snd_add]
  ring

lemma argument_balance (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    (argument M x : ℂ) / (epsilon M : ℂ) =
      (x.1 : ℂ) * (repellingTau M : ℂ) + (x.2 : ℂ) + (argument M x : ℂ) := by
  rw [argument_eq_modular M hM]
  simp only [modularPhiSpecialArgument, Matrix.cons_val_zero, Matrix.cons_val_one,
    etaDenom_eq]
  have he := epsilon_ne_zero M hM
  have he1 : (epsilon M : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_lt (epsilon_lt_one M hM))
  field_simp
  ring

lemma off_lattice_argument (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x ≠ 0) :
    (argument M x : ℂ) ∉ modularPhiPseudoLattice (repellingTau M : ℂ) := by
  rintro ⟨k, l, hw⟩
  have hdom := real_mem_modularPhiDomain M (repellingTau M) (epsilon_pos M hM)
  have hmob := modularPhi_lattice_mobius M k l (repellingTau M : ℂ) hdom
  rw [repellingTau_fixedPoint M hM, etaDenom_eq, ← hw] at hmob
  have hbal := argument_balance M hM x
  rw [hmob, hw] at hbal
  have hrel : (((M 1 1 * k - M 1 0 * l) - (x.1 + k) : ℤ) : ℂ) *
      (repellingTau M : ℂ) +
      (((M 0 0 * l - M 0 1 * k) - (x.2 + l) : ℤ) : ℂ) = 0 := by
    push_cast at hbal ⊢
    linear_combination hbal
  obtain ⟨hc1, hc2⟩ := m37b_irrational_relation (repellingTau M)
    (repellingTau_irrational M hM) _ _ hrel
  have hx1 : x.1 = M 1 1 * k - M 1 0 * l - k := by omega
  have hx2 : x.2 = M 0 0 * l - M 0 1 * k - l := by omega
  apply hx
  apply (mk_eq_zero_iff M x).mpr
  change ∃ q : ℤ × ℤ, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) q = x
  refine ⟨(-M 1 1 * k + M 1 0 * l, M 0 1 * k - M 0 0 * l), ?_⟩
  have hdet := det_coe_int M
  ext
  · simp only [L2r.rowAction, Matrix.sub_apply]
    norm_num
    rw [hx1]
    linear_combination -k * hdet
  · simp only [L2r.rowAction, Matrix.sub_apply]
    norm_num
    rw [hx2]
    linear_combination -l * hdet

lemma nonzero_joint_regular (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x ≠ 0) (m n : ℤ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2)
      ((argument M x : ℂ), (repellingTau M : ℂ)) ∧
    modularPhi M m n (argument M x : ℂ) (repellingTau M : ℂ) ≠ 0 := by
  have hp : ((argument M x : ℂ), (repellingTau M : ℂ)) ∈
      modularPhiNonvanishingDomain M m n := modularPhi_real_off_lattice M hM.1 m n (repellingTau M)
    (epsilon_pos M hM) (argument M x : ℂ) (off_lattice_argument M hM x hx)
  exact ⟨modularPhi_joint_analytic_no_poles M hM.1 m n _ ⟨hp.1, hp.2.1⟩,
    (modularPhi_ne_zero_iff M hM.1 m n _ _ hp.1 hp.2.1).mpr hp.2.2⟩

lemma phase (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) :
    (e (repellingTau M : ℂ)) ^ x.1 * e (argument M x : ℂ) =
      e ((argument M x : ℂ) / etaDenom M (repellingTau M : ℂ)) := by
  rw [etaDenom_eq, argument_balance M hM, e_add', e_add', e_intCast, mul_one,
    e_int_mul]

lemma index_factors_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x ≠ 0) (j : ℤ) :
    1 - (e (repellingTau M : ℂ)) ^ (x.1 + j) * e (argument M x : ℂ) ≠ 0 := by
  intro h
  have he : e (((x.1 + j : ℤ) : ℂ) * (repellingTau M : ℂ) + (argument M x : ℂ)) = 1 := by
    rw [e_add', ← e_int_mul]
    exact (sub_eq_zero.mp h).symm
  obtain ⟨l, hl⟩ := e_eq_one_iff_int he
  apply off_lattice_argument M hM x hx
  refine ⟨-(x.1 + j), l, ?_⟩
  push_cast at hl ⊢
  linear_combination hl

lemma zero_coordinates (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x = 0) :
    ∃ k l : ℤ, (argument M x : ℂ) = (k : ℂ) * (repellingTau M : ℂ) + (l : ℂ) ∧
      k + x.1 = M 1 1 * k - M 1 0 * l ∧
      sIndex M x = -specialValueOrder M * (k + x.1) := by
  have hxmem := (mk_eq_zero_iff M x).mp hx
  change ∃ q : ℤ × ℤ, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) q = x at hxmem
  obtain ⟨q, rfl⟩ := hxmem
  let k : ℤ := -(q.1 * M 0 0 + q.2 * M 1 0)
  let l : ℤ := -(q.1 * M 0 1 + q.2 * M 1 1)
  have hdet := det_coe_int M
  have hx1 : (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) q).1 =
      q.1 * (M 0 0 - 1) + q.2 * M 1 0 := by simp [L2r.rowAction]
  have hx2 : (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) q).2 =
      q.1 * M 0 1 + q.2 * (M 1 1 - 1) := by simp [L2r.rowAction]
  refine ⟨k, l, ?_, ?_, ?_⟩
  · rw [argument_eq_modular M hM]
    have hrow := ModularCocycleUnitAux.row_fixedPoint M ![q.1, q.2]
      (repellingTau M : ℂ) (repellingTau_fixedPoint M hM)
      (by rw [etaDenom_eq]; exact epsilon_ne_zero M hM)
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hrow
    rw [etaDenom_eq] at hrow
    simp only [modularPhiSpecialArgument, Matrix.cons_val_zero,
      Matrix.cons_val_one, etaDenom_eq]
    rw [hx1, hx2]
    dsimp [k, l]
    push_cast at hrow ⊢
    have he := epsilon_ne_zero M hM
    have he1 : (epsilon M : ℂ) ≠ 1 := by
      exact_mod_cast (ne_of_lt (epsilon_lt_one M hM))
    apply (div_eq_iff (sub_ne_zero.mpr (inv_ne_one.mpr he1))).mpr
    field_simp
    linear_combination hrow
  · rw [hx1]
    dsimp [k, l]
    linear_combination q.1 * hdet
  · rw [sIndex, hx1, hx2]
    dsimp [k, specialValueOrder]
    linear_combination -q.1 * hdet

end SICLean.L4.G2IntegralEvaluationAux
