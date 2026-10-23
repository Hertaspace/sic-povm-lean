import SICLean.L4.G2ExactTelescoping

set_option autoImplicit false

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2G1SpecializationAux

open G2

lemma etaDenom_repelling (M : SL(2, ℤ)) :
    etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
  simp [etaDenom, epsilon, g1T]

lemma argument_add (M : SL(2, ℤ)) (u v : ℤ × ℤ) :
    argument M (u + v) = argument M u + argument M v := by
  simp only [argument, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

lemma translate_phi (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m n : ℤ) (z τ : ℂ) :
    modularPhi M m n (z + (M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) τ =
      modularPhi M (m + M 0 0) (n + 1) z τ := by
  have hn : n + M 1 1 * M 0 0 - M 1 0 * M 0 1 = n + 1 := by
    nlinarith [det_coe_int M]
  simpa only [hn] using
    modularPhi_shift_integer M hM.1 m n (M 0 0) (M 0 1) z τ

lemma domain_of_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hz : modularPhi M m n z τ ≠ 0) :
    (z, τ) ∈ modularPhiNonvanishingDomain M m n := by
  have hp : modularPhiPoleMultiplicity M m n z τ = 0 := by
    by_contra hp
    exact hz (modularPhi_pole_value M hM.1 m n z τ hτ hp)
  exact ⟨hτ, hp, (modularPhi_ne_zero_iff M hM.1 m n z τ hτ hp).mp hz⟩

lemma continuousAt_of_unit (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m n : ℤ) (p : ℂ × ℂ) (hp : p ∈ modularPhiNonvanishingDomain M m n) :
    ContinuousAt (fun q : ℂ × ℂ => modularPhi M m n q.1 q.2) p := by
  obtain ⟨U, _, hpU, _, hA, _⟩ := modularPhi_joint_unit_neighborhood M hM.1 m n p hp
  exact (hA p hpU).continuousAt

lemma ne_zero_of_unit (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m n : ℤ) (p : ℂ × ℂ) (hp : p ∈ modularPhiNonvanishingDomain M m n) :
    modularPhi M m n p.1 p.2 ≠ 0 :=
  (modularPhi_ne_zero_iff M hM.1 m n p.1 p.2 hp.1 hp.2.1).mpr hp.2.2

lemma argument_identity (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    argument M x = epsilon M *
      (argument M x + (x.1 : ℝ) * repellingTau M + (x.2 : ℝ)) := by
  have he := (epsilon_pos M hM).ne'
  have hd : (epsilon M)⁻¹ - 1 ≠ 0 := by
    intro h
    have hi : (epsilon M)⁻¹ = 1 := sub_eq_zero.mp h
    have := inv_eq_one.mp hi
    linarith [epsilon_lt_one M hM]
  dsimp [argument]
  field_simp [he, hd, (sub_pos.mpr (epsilon_lt_one M hM)).ne']
  ring

lemma lattice_relations (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (k l : ℤ)
    (hx : (argument M x : ℂ) = (k : ℂ) * (repellingTau M : ℂ) + (l : ℂ)) :
    k + x.1 = M 1 1 * k - M 1 0 * l ∧ specialValueMk M x = 0 := by
  have he : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
  have hf := repellingTau_fixedPoint M hM
  unfold etaMobius at hf
  rw [etaDenom_repelling] at hf
  have ht := (div_eq_iff he).mp hf
  have hw : (argument M x : ℂ) = (epsilon M : ℂ) *
      ((argument M x : ℂ) + (x.1 : ℂ) * (repellingTau M : ℂ) + (x.2 : ℂ)) := by
    exact_mod_cast argument_identity M hM x
  rw [hx] at hw
  have hlin :
      ((((k + x.1) * M 0 0 + (l + x.2) * M 1 0 - k : ℤ) : ℂ)) *
          (repellingTau M : ℂ) +
        (((k + x.1) * M 0 1 + (l + x.2) * M 1 1 - l : ℤ) : ℂ) = 0 := by
    push_cast
    have hd : (epsilon M : ℂ) =
        (M 1 0 : ℂ) * (repellingTau M : ℂ) + (M 1 1 : ℂ) := by
      simp [epsilon, g1T]
    linear_combination -hw + ((k : ℂ) + (x.1 : ℂ)) * ht
      - ((l : ℂ) + (x.2 : ℂ)) * hd
  obtain ⟨ha, hb⟩ := m37b_irrational_relation (repellingTau M)
    (repellingTau_irrational M hM) _ _ hlin
  refine ⟨?_, ?_⟩
  · linear_combination (M 1 1) * ha - (M 1 0) * hb - (k + x.1) * (det_coe_int M)
  · apply (QuotientAddGroup.eq_zero_iff x).mpr
    change x ∈ L2r.rowLattice ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
    change ∃ y : ℤ × ℤ, L2r.rowAction
      ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) y = x
    refine ⟨(-(k + x.1), -(l + x.2)), ?_⟩
    ext <;> simp [L2r.rowAction, Matrix.sub_apply]
    · linear_combination -ha
    · linear_combination -hb

lemma balanced_unit (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (h : ℤ) :
    ((argument M x : ℂ), (repellingTau M : ℂ)) ∈
      modularPhiNonvanishingDomain M (x.1 + h) h := by
  by_cases hx : (argument M x : ℂ) ∈ modularPhiPseudoLattice (repellingTau M : ℂ)
  · obtain ⟨k, l, hkl⟩ := hx
    rw [hkl]
    apply modularPhi_fixedPoint_lattice_divisor_free M hM.1 hM.2
      (x.1 + h) h (repellingTau M) (epsilon_pos M hM)
      (repellingTau_fixedPoint M hM) k l
    have := (lattice_relations M hM x k l hkl).1
    omega
  · exact modularPhi_real_off_lattice M hM.1 (x.1 + h) h (repellingTau M)
      (epsilon_pos M hM) (argument M x : ℂ) hx

lemma nonzero_class_unit (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x ≠ 0) (m n : ℤ) :
    ((argument M x : ℂ), (repellingTau M : ℂ)) ∈
      modularPhiNonvanishingDomain M m n := by
  apply modularPhi_real_off_lattice M hM.1 m n (repellingTau M)
    (epsilon_pos M hM)
  rintro ⟨k, l, hkl⟩
  exact hx (lattice_relations M hM x k l hkl).2

lemma translated_unit (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m : ℤ) (z : ℂ)
    (hz : (z, (repellingTau M : ℂ)) ∈ modularPhiNonvanishingDomain M m 1) :
    (z + (M 0 0 : ℂ) * (repellingTau M : ℂ) + (M 0 1 : ℂ),
      (repellingTau M : ℂ)) ∈ modularPhiNonvanishingDomain M (m - M 0 0) 0 := by
  apply domain_of_ne_zero M hM _ _ _ _ hz.1
  rw [translate_phi M hM]
  simpa only [sub_add_cancel, zero_add] using ne_zero_of_unit M hM m 1 _ hz

set_option maxHeartbeats 800000 in
lemma ratio_raw_continuousAt (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (τ : ℝ) (h ell p : ℤ) (q : ℂ × ℂ) (hq : q ∈ g1RatioRHSLocus M τ h ell p) :
    ContinuousAt (g1RatioRawRHS M τ h ell p) q := by
  have hn := continuousAt_of_unit M hM (p + ell) (-h) (q.1 + q.2, (τ : ℂ)) hq.1
  have hd := continuousAt_of_unit M hM p 0 (q.2, (τ : ℂ)) hq.2.1
  have he := continuousAt_of_unit M hM ell (1 - h) (q.1, (τ : ℂ)) hq.2.2
  have cn : ContinuousAt (fun v : ℂ × ℂ => (v.1 + v.2, (τ : ℂ))) q :=
    (continuousAt_fst.add continuousAt_snd).prodMk continuousAt_const
  have cd : ContinuousAt (fun v : ℂ × ℂ => (v.2, (τ : ℂ))) q :=
    continuousAt_snd.prodMk continuousAt_const
  have ce : ContinuousAt (fun v : ℂ × ℂ => (v.1, (τ : ℂ))) q :=
    continuousAt_fst.prodMk continuousAt_const
  unfold g1RatioRawRHS
  exact (ContinuousAt.comp (f := fun v : ℂ × ℂ => (v.1 + v.2, (τ : ℂ))) hn cn).div
    ((ContinuousAt.comp (f := fun v : ℂ × ℂ => (v.2, (τ : ℂ))) hd cd).mul
      (ContinuousAt.comp (f := fun v : ℂ × ℂ => (v.1, (τ : ℂ))) he ce))
    (mul_ne_zero (ne_zero_of_unit M hM p 0 (q.2, (τ : ℂ)) hq.2.1)
      (ne_zero_of_unit M hM ell (1 - h) (q.1, (τ : ℂ)) hq.2.2))

lemma single_raw_continuousAt (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (τ : ℝ) (h ell : ℤ) (w : ℂ) (hw : w ∈ g1SingleRHSLocus M τ h ell) :
    ContinuousAt (g1SingleRawRHS M τ h ell) w := by
  exact (ContinuousAt.comp (f := fun z : ℂ => (z, (τ : ℂ)))
    (continuousAt_of_unit M hM ell (1 - h) _ hw)
    (continuousAt_id.prodMk continuousAt_const)).inv₀
      (ne_zero_of_unit M hM ell (1 - h) _ hw)

end SICLean.L4.G2G1SpecializationAux
