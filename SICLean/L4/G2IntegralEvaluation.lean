import SICLean.L4.G2G1Specialization
import SICLean.L4.G2IntegralEvaluationAux

set_option autoImplicit false

/-!
Actual removable centers and the final integral value. [RW26, p. 12, Lemma 2, p. 13].

The existing specialValuePlus/Minus are attracting values. The concrete repelling lifts below are
the values before descent, with A=1/sqrt(ε). They do not replace those definitions or presume the
inverse-reflection bridge. That bridge and descent are outside this file. Neither F^- nor F^+ is
defined by the integral being evaluated.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2
namespace Evaluation

open G2IntegralEvaluationAux

/-- Exact integer r_h on the zero class; divisibility is a theorem below. For nonzero classes this
total integer formula has no lattice meaning. -/
def commonExponent (M : SL(2, ℤ)) (x : ℤ × ℤ) (h : ℤ) : ℤ :=
  h - sIndex M x / specialValueOrder M

/-- Actual repelling F^+ on representatives, with the separately prescribed zero-class value A. The
raw μΦ is used only outside Λ. -/
def repellingPlusLift (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℂ :=
  if x ∈ specialValueLattice M then (Real.sqrt (epsilon M) : ℂ)⁻¹
  else etaMultiplier M * modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ)

/-- Actual repelling F^-, whose zero-class value is A^-1=sqrt(ε). -/
def repellingMinusLift (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℂ :=
  if x ∈ specialValueLattice M then (Real.sqrt (epsilon M) : ℂ)
  else etaMultiplier M * modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ)

/-- [RW26, p. 13]. -/
theorem argument_add (M : SL(2, ℤ)) (u v : ℤ × ℤ) :
    argument M (u + v) = argument M u + argument M v := by
  simp only [argument, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

/-- Actual lattice coordinates and r_0=-S_x/N, not merely a test of S_x modulo N; [RW26, p. 12,
Lemma 2]. The premise is the full zero-class test. -/
theorem zero_class_lattice_coordinates (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x = 0) :
    ∃ k l : ℤ, (argument M x : ℂ) = (k : ℂ) * (repellingTau M : ℂ) + (l : ℂ) ∧
      k + x.1 = M 1 1 * k - M 1 0 * l ∧
      ((k + x.1 : ℤ) : ℝ) = -(sIndex M x : ℝ) / (specialValueOrder M : ℝ) := by
  obtain ⟨k, l, hw, hb, hs⟩ := zero_coordinates M hM x hx
  refine ⟨k, l, hw, hb, ?_⟩
  have hN : (specialValueOrder M : ℝ) ≠ 0 := by
    exact_mod_cast (specialValueOrder_pos M hM).ne'
  rw [hs]
  push_cast
  field_simp

/-- Only the forward divisibility consequence, never its converse; [RW26, p. 12]. -/
theorem zero_class_sIndex_dvd (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x = 0) :
    specialValueOrder M ∣ sIndex M x := by
  obtain ⟨k, l, _, _, hs⟩ := zero_coordinates M hM x hx
  exact ⟨-(k + x.1), by rw [hs]; ring⟩

/-- Explicit real/integer bridge for r_h=h-S_x/N on the zero class; [RW26, p. 12]. -/
theorem commonExponent_cast (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x = 0) (h : ℤ) :
    (commonExponent M x h : ℝ) =
      (h : ℝ) - (sIndex M x : ℝ) / (specialValueOrder M : ℝ) := by
  obtain ⟨q, hq⟩ := zero_class_sIndex_dvd M hM x hx
  have hN := (specialValueOrder_pos M hM).ne'
  simp only [commonExponent, hq, Int.mul_ediv_cancel_left _ hN, Int.cast_sub,
    Int.cast_mul]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast hN : (specialValueOrder M : ℝ) ≠ 0)]

/-- Specified Φ center after joint common-zero cancellation. The two branches are derived from
modularPhi_fixedPoint_lattice_value; [RW26, p. 12]. -/
theorem zero_class_phi_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x = 0) (h : ℤ) :
    modularPhi M (x.1 + h) h (argument M x : ℂ) (repellingTau M : ℂ) =
      if 1 ≤ commonExponent M x h then
        (etaMultiplier M)⁻¹ / (Real.sqrt (epsilon M) : ℂ)
      else (etaMultiplier M)⁻¹ * (Real.sqrt (epsilon M) : ℂ) := by
  obtain ⟨k, l, hw, hb, hs⟩ := zero_coordinates M hM x hx
  have hr : k + (x.1 + h) = commonExponent M x h := by
    unfold commonExponent
    rw [hs]
    have hN := (specialValueOrder_pos M hM).ne'
    have hdiv : -specialValueOrder M * (k + x.1) / specialValueOrder M = -(k + x.1) := by
      rw [neg_mul, Int.neg_ediv_of_dvd (dvd_mul_right _ _), Int.mul_ediv_cancel_left _ hN]
    rw [hdiv]
    ring
  rw [hw]
  have he : (M 1 0 : ℝ) * repellingTau M + (M 1 1 : ℝ) = epsilon M := rfl
  simpa only [hr, he] using modularPhi_fixedPoint_lattice_value M hM.1 hM.2
    (x.1 + h) h (repellingTau M) (epsilon_pos M hM) (repellingTau_fixedPoint M hM)
    k l (by linarith [hb])

/-- Nonzero-class diagonal shifts: center regularity and nonvanishing precede legitimate
cancellation. All functions are the existing Φ. [RW26, p. 6, (16), p. 12, Lemma 2]. -/
theorem nonzero_class_phi_shift (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x ≠ 0) (h : ℤ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M (x.1 + h) h p.1 p.2)
      ((argument M x : ℂ), (repellingTau M : ℂ)) ∧
    modularPhi M (x.1 + h) h (argument M x : ℂ) (repellingTau M : ℂ) ≠ 0 ∧
    modularPhi M (x.1 + h) h (argument M x : ℂ) (repellingTau M : ℂ) =
      modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ) := by
  have hL := nonzero_joint_regular M hM x hx (x.1 + h) h
  have hR := nonzero_joint_regular M hM x hx x.1 0
  refine ⟨hL.1, hL.2, ?_⟩
  have hc : ContinuousAt (fun w : ℂ => (w, (repellingTau M : ℂ))) (argument M x : ℂ) := by
    fun_prop
  simpa only [zero_add] using modularPhi_diagonal_index_fixedPoint M hM.1 x.1 0 h
    (argument M x : ℂ) (repellingTau M) (repellingTau_fixedPoint M hM)
    (by rw [etaDenom_eq]; exact epsilon_pos M hM)
    (by simpa using phase M hM x) (index_factors_ne_zero M hM x hx)
    (by simpa only [Function.comp_def, zero_add] using
      hL.1.continuousAt.comp (f := fun w : ℂ => (w, (repellingTau M : ℂ))) hc)
    (by simpa only [Function.comp_def] using
      hR.1.continuousAt.comp (f := fun w : ℂ => (w, (repellingTau M : ℂ))) hc)

/-- u=0 in the quotient, not necessarily the zero integer vector: S_u=N and r_1=0. [RW26, p. 13]. -/
theorem upper_zero_exponent (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (hu : specialValueMk M u = 0) :
    sIndex M u = specialValueOrder M ∧ commonExponent M u 1 = 0 := by
  have hN := specialValueOrder_pos M hM
  obtain ⟨k, hk⟩ := zero_class_sIndex_dvd M hM u hu
  have hkpos : 0 < k := by nlinarith [hwin.1]
  have hkle : k ≤ 1 := by nlinarith [hwin.2.1]
  have hkone : k = 1 := by omega
  have hs : sIndex M u = specialValueOrder M := by simpa [hkone] using hk
  refine ⟨hs, ?_⟩
  simp [commonExponent, hs, Int.ediv_self hN.ne']

/-- u+v=0 gives S_{u+v}≤0 and r_1≥1. The full quotient test is retained; no cyclicity or converse S
criterion is assumed. [RW26, p. 13]. -/
theorem sum_zero_exponent (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (huv : specialValueMk M (u + v) = 0) :
    sIndex M (u + v) ≤ 0 ∧ 1 ≤ commonExponent M (u + v) 1 := by
  have hN := specialValueOrder_pos M hM
  have hc : 1 ≤ M 1 0 := hM.1
  have hs : sIndex M (u + v) < specialValueOrder M := by
    rw [sIndex_add]
    nlinarith [hwin.2.1, hwin.2.2.2]
  obtain ⟨k, hk⟩ := zero_class_sIndex_dvd M hM (u + v) huv
  have hkneg : k ≤ 0 := by nlinarith
  have hsum : sIndex M (u + v) ≤ 0 := by nlinarith
  refine ⟨hsum, ?_⟩
  simp only [commonExponent, hk, Int.mul_ediv_cancel_left _ hN.ne']
  omega

/-- Includes u=0 via r_1=0, giving F^- rather than F^+; [RW26, p. 13]. -/
theorem upper_minus_identification (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    etaMultiplier M * modularPhi M (u.1 + 1) 1 (argument M u : ℂ) (repellingTau M : ℂ) =
      repellingMinusLift M u := by
  by_cases hu : specialValueMk M u = 0
  · have hm := (mk_eq_zero_iff M u).mp hu
    rw [zero_class_phi_value M hM u hu 1, (upper_zero_exponent M hM u v hwin hu).2]
    simp [repellingMinusLift, hm, etaMultiplier_ne_zero M hM.1]
  · rw [(nonzero_class_phi_shift M hM u hu 1).2.2]
    simp [repellingMinusLift, (mk_eq_zero_iff M u).not.mp hu]

/-- v is nonzero, so its diagonal shift uses no lattice branch change; [RW26, p. 12, p. 13]. -/
theorem nonzero_minus_identification (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (hv : specialValueMk M v ≠ 0) :
    etaMultiplier M * modularPhi M (v.1 + 1) 1 (argument M v : ℂ) (repellingTau M : ℂ) =
      repellingMinusLift M v := by
  rw [(nonzero_class_phi_shift M hM v hv 1).2.2]
  simp [repellingMinusLift, (mk_eq_zero_iff M v).not.mp hv]

/-- Includes u+v=0 via r_1≥1, giving F^+ rather than F^-; [RW26, p. 13]. -/
theorem sum_plus_identification (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    etaMultiplier M * modularPhi M (v.1 + (u.1 + 1)) 1
      ((argument M u : ℂ) + (argument M v : ℂ)) (repellingTau M : ℂ) =
        repellingPlusLift M (u + v) := by
  have hi : v.1 + (u.1 + 1) = (u + v).1 + 1 := by simp; ring
  rw [hi, ← Complex.ofReal_add, ← argument_add]
  by_cases huv : specialValueMk M (u + v) = 0
  · have hm := (mk_eq_zero_iff M (u + v)).mp huv
    rw [zero_class_phi_value M hM (u + v) huv 1,
      if_pos (sum_zero_exponent M hM u v hwin huv).2]
    simp [repellingPlusLift, hm, div_eq_mul_inv, etaMultiplier_ne_zero M hM.1]
  · rw [(nonzero_class_phi_shift M hM (u + v) huv 1).2.2]
    simp [repellingPlusLift, (mk_eq_zero_iff M (u + v)).not.mp huv]

/-- Actual repelling lifts are nonzero, by outside Λ and positive sqrt(ε) on Λ. [RW26, p. 12]. -/
theorem repelling_lifts_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    repellingPlusLift M x ≠ 0 ∧ repellingMinusLift M x ≠ 0 := by
  have hsqrt : (Real.sqrt (epsilon M) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (epsilon_pos M hM)).ne'
  by_cases hx : specialValueMk M x = 0
  · simp [repellingPlusLift, repellingMinusLift, (mk_eq_zero_iff M x).mp hx, hsqrt]
  · have hn := mul_ne_zero (etaMultiplier_ne_zero M hM.1)
      (nonzero_joint_regular M hM x hx x.1 0).2
    simpa [repellingPlusLift, repellingMinusLift, (mk_eq_zero_iff M x).not.mp hx] using
      And.intro hn hn

/-- One common μ, including the two exceptional zero-class outputs; [RW26, p. 13]. -/
theorem weighted_phi_identification (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0) :
    (etaMultiplier M)⁻¹ * weightedPhiRHS M u v =
      repellingPlusLift M (u + v) / (repellingMinusLift M u * repellingMinusLift M v) := by
  have hmu := etaMultiplier_ne_zero M hM.1
  have hu := (repelling_lifts_ne_zero M hM u).2
  have hv' := (repelling_lifts_ne_zero M hM v).2
  rw [← upper_minus_identification M hM u v hwin] at hu
  rw [← nonzero_minus_identification M hM v hv] at hv'
  have huPhi := (mul_ne_zero_iff.mp hu).2
  have hvPhi := (mul_ne_zero_iff.mp hv').2
  rw [← sum_plus_identification M hM u v hwin,
    ← upper_minus_identification M hM u v hwin,
    ← nonzero_minus_identification M hM v hv]
  unfold weightedPhiRHS
  field_simp [hmu, huPhi, hvPhi]

/-- First displayed equality, before identifying the actual F values. No sum identity/residue
formula is an input. [RW26, p. 13]. -/
theorem rawIntegral_phi_value (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    Telescoping.rawIntegral M u v D =
      (M 1 0 : ℂ) * (Real.sqrt (epsilon M) : ℂ) * (etaMultiplier M)⁻¹ *
        weightedPhiRHS M u v := by
  rw [Telescoping.telescope_to_ratio M hM u v hwin δ D hD, Finset.mul_sum]
  simp_rw [(weighted_integral_each_j hG1 M hM u v hwin hv δ D hD)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (le_of_lt hM.1)]
  ring

/-- Downstream / call form: exact integral of the concrete raw kernels. Only hG1 is an analytic
integral input. v=0 is deliberately later; [RW26, p. 13]. -/
theorem rawIntegral_value (hG1 : G1RealConclusion)
    (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) (hv : specialValueMk M v ≠ 0)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    Telescoping.rawIntegral M u v D =
      (M 1 0 : ℂ) * (Real.sqrt (epsilon M) : ℂ) *
        (repellingPlusLift M (u + v) / (repellingMinusLift M u * repellingMinusLift M v)) := by
  rw [rawIntegral_phi_value hG1 M hM u v hwin hv δ D hD,
    ← weighted_phi_identification M hM u v hwin hv]
  ring

#check @modularPhi_fixedPoint_lattice_value
#check @modularPhi_diagonal_index_fixedPoint
#print commonExponent
#print repellingPlusLift
#print repellingMinusLift
#check rawIntegral_value

end Evaluation
end SICLean.L4.G2
