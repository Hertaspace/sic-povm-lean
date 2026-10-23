import SICLean.L4.G2IntegralEvaluation
import SICLean.L4.G2SpecialValueBridge
import SICLean.L4.G2CombResiduesAux

set_option autoImplicit false

/-!
Component-labelled comb roots and the positive residue.
[RW26]. The principal-part statements are punctured identities; `rawF` is a total representative and
its value at a comb pole is not its Laurent residue. The actual finite-product `modularPhi`, its
removable centers, and the existing slit-plane branch / `etaMultiplier` are retained throughout.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2.CombResidues

open SICLean.L4.G2CombResiduesAux

/-- z_{m,k}=α(mτ+k), retaining both integer labels. -/
def root (M : SL(2, ℤ)) (m k : ℤ) : ℂ :=
  (scale M : ℂ) * ((m : ℂ) * (repellingTau M : ℂ) + (k : ℂ))

def phiNumerator (M : SL(2, ℤ)) (m k : ℤ) : ℂ :=
  modularPhi M m 0 (root M m k) (repellingTau M : ℂ)

def phiDenominator (M : SL(2, ℤ)) (v : ℤ × ℤ) (m k : ℤ) : ℂ :=
  modularPhi M (m + v.1) 0 (root M m k + (argument M v : ℂ))
    (repellingTau M : ℂ)

/-- The concrete coefficient 2πi Res f_m, with the positive α sign. Its identification as a residue
is a theorem, not part of the definition. -/
def rho (M : SL(2, ℤ)) (u v : ℤ × ℤ) (m k : ℤ) : ℂ :=
  (scale M : ℂ) * specialValuePairingLift M (m, k) u *
    phiNumerator M m k / phiDenominator M v m k

/-- The two already fixed concrete lift definitions agree. No new F or μ. [RW26, (2), p. 2, p. 13].
-/
theorem evaluation_lifts_eq_bridge (M : SL(2, ℤ)) (x : ℤ × ℤ) :
    Evaluation.repellingPlusLift M x = SpecialValueBridge.repellingPlusLift M x ∧
      Evaluation.repellingMinusLift M x = SpecialValueBridge.repellingMinusLift M x := by
  exact ⟨rfl, rfl⟩

/-- [RW26, p. 12]. -/
theorem root_eq_argument (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m k : ℤ) :
    root M m k = (argument M (m, k) : ℂ) := by
  have he : (epsilon M : ℂ) ≠ 0 := by
    exact_mod_cast (epsilon_pos M hM).ne'
  have hL : (1 : ℂ) - (epsilon M : ℂ) ≠ 0 := by
    exact_mod_cast (sub_pos.mpr (epsilon_lt_one M hM)).ne'
  simp only [root, scale, length, argument, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_inv]
  field_simp [he, hL]

/-- The coordinate X is an affine coordinate, not a quotient-class test. [RW26, p. 12, p. 13]. -/
theorem root_coordinate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m k : ℤ) :
    (M 1 0 : ℂ) * root M m k + (epsilon M : ℂ) * (m : ℂ) =
      (combCoordinate M m k : ℂ) := by
  rw [root_eq_argument M hM]
  exact_mod_cast argument_common_coordinate M hM (m, k)

/-- X-cL₂ is k-N in the same component; z itself changes by -L₂. [RW26, p. 13]. -/
theorem root_shift (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m k : ℤ) :
    root M m (k - specialValueOrder M) = root M m k - (length M : ℂ) ∧
      combCoordinate M m (k - specialValueOrder M) =
        combCoordinate M m k - (M 1 0 : ℝ) * length M := by
  have hL := G2ContourChainAux.length_eq_scale_mul M hM
  constructor
  · simp only [root, Int.cast_sub]
    rw [hL]
    push_cast
    ring
  · simp only [combCoordinate, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_one]
    rw [hL]
    ring

/-- The complete zero locus of the exponential comb, including uniqueness of k within one component.
[RW26, p. 12]. -/
theorem comb_zeros (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m : ℤ) (z : ℂ) :
    combV M z - combU M m z = 0 ↔ ∃! k : ℤ, z = root M m k := by
  have heps : (epsilon M : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (epsilon_pos M hM)
  have hlen : (length M : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (length_pos M hM)
  have hphase (k : ℤ) : root M m k / (epsilon M : ℂ) -
      ((m : ℂ) * (repellingTau M : ℂ) + root M m k) = (k : ℂ) := by
    simp only [root, scale, length, ofReal_div, ofReal_sub, ofReal_one]
    have heps' : (1 - (epsilon M : ℂ)) ≠ 0 := by
      simpa only [length, ofReal_sub, ofReal_one] using hlen
    field_simp
    ring
  constructor
  · intro hz
    have he : e (z / (epsilon M : ℂ)) =
        e ((m : ℂ) * (repellingTau M : ℂ) + z) := by
      simpa only [combV, combU, e_int_mul, e_add'] using sub_eq_zero.mp hz
    obtain ⟨k, hk⟩ := (e_eq_iff_int_sub _ _).mp he
    have hzroot : z = root M m k := by
      have hd : (1 / (epsilon M : ℂ) - 1) * (z - root M m k) = 0 := by
        linear_combination hk - hphase k
      have hcoef : 1 / (epsilon M : ℂ) - 1 ≠ 0 := by
        rw [sub_ne_zero]
        have hlt := epsilon_lt_one M hM
        intro hh
        have hh' : (1 : ℂ) = (epsilon M : ℂ) := by
          simpa only [one_mul] using (div_eq_iff heps).mp hh
        have heq : (1 : ℝ) = epsilon M := by exact_mod_cast hh'
        linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hcoef)
    refine ⟨k, hzroot, ?_⟩
    intro l hl
    have hr : root M m l = root M m k := hl.symm.trans hzroot
    have hc : (l : ℂ) = (k : ℂ) := by
      have hlphase := hphase l
      rw [hr] at hlphase
      exact hlphase.symm.trans (hphase k)
    exact_mod_cast hc
  · rintro ⟨k, rfl, _⟩
    apply sub_eq_zero.mpr
    simp only [combV, combU, e_int_mul, ← e_add']
    exact (e_eq_iff_int_sub _ _).mpr ⟨k, hphase k⟩

/-- Derivative 2πi(L₂/ε)e(z/ε), with a nonzero conclusion. [RW26, p. 13]. -/
theorem comb_hasDerivAt (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (m k : ℤ) :
    HasDerivAt (fun z => combV M z - combU M m z)
      (2 * (Real.pi : ℂ) * Complex.I * ((length M : ℂ) / (epsilon M : ℂ)) *
        combV M (root M m k)) (root M m k) ∧
      2 * (Real.pi : ℂ) * Complex.I * ((length M : ℂ) / (epsilon M : ℂ)) *
        combV M (root M m k) ≠ 0 := by
  have heps : (epsilon M : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (epsilon_pos M hM)
  have hlen : (length M : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (length_pos M hM)
  have hUV : combU M m (root M m k) = combV M (root M m k) := by
    apply Eq.symm
    apply sub_eq_zero.mp
    apply (comb_zeros M hM m (root M m k)).mpr
    refine ⟨k, rfl, ?_⟩
    intro l hl
    have hscale : (scale M : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (scale_identities M hM).1
    have hc : (l : ℂ) = (k : ℂ) := by
      apply add_left_cancel (a := (m : ℂ) * (repellingTau M : ℂ))
      exact mul_left_cancel₀ hscale hl.symm
    exact_mod_cast hc
  have hv : HasDerivAt (combV M)
      (2 * (Real.pi : ℂ) * Complex.I * combV M (root M m k) /
        (epsilon M : ℂ)) (root M m k) := by
    apply HasDerivAt.congr_deriv
      ((e_hasDerivAt (root M m k / (epsilon M : ℂ))).comp (root M m k)
        ((hasDerivAt_id (root M m k)).div_const (epsilon M : ℂ)))
    simp only [combV]
    ring
  have hu : HasDerivAt (combU M m)
      ((e (repellingTau M : ℂ)) ^ m *
        (2 * (Real.pi : ℂ) * Complex.I * e (root M m k))) (root M m k) := by
    exact (e_hasDerivAt (root M m k)).const_mul
      ((e (repellingTau M : ℂ)) ^ m)
  constructor
  · apply (hv.sub hu).congr_deriv
    rw [show (e (repellingTau M : ℂ)) ^ m *
        (2 * (Real.pi : ℂ) * Complex.I * e (root M m k)) =
      2 * (Real.pi : ℂ) * Complex.I * combU M m (root M m k) by
        unfold combU
        ring, hUV]
    simp only [length, ofReal_sub, ofReal_one]
    field_simp
  · apply mul_ne_zero
    · exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num)
          (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
        (div_ne_zero hlen heps)
    · exact e_ne_zero _

/-- Exact integer phase error, before exponentiation. The extra +1 in kernelK's ell=u₁+1 is
essential. [RW26, p. 12]. -/
theorem phase_integer_error (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m k : ℤ) :
    (((M 1 0 : ℂ) * root M m k + (epsilon M : ℂ) * (m : ℂ)) *
        (argument M u : ℂ)) / (epsilon M : ℂ) +
      ((u.1 + 1 : ℤ) : ℂ) * (root M m k + (m : ℂ) * (repellingTau M : ℂ)) -
      root M m k / (epsilon M : ℂ) -
      (specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (m, k) -
        (m, k)) u : ℂ) / (specialValueOrder M : ℂ) =
      ((-k - m * u.2 : ℤ) : ℂ) := by
  have he : (epsilon M : ℂ) ≠ 0 := by
    exact_mod_cast (epsilon_pos M hM).ne'
  have hN : (specialValueOrder M : ℂ) ≠ 0 := by
    exact_mod_cast (specialValueOrder_pos M hM).ne'
  have hs : (scale M : ℂ) = (length M : ℂ) / (specialValueOrder M : ℂ) := by
    exact_mod_cast (scale_identities M hM).2
  have hLs : (length M : ℂ) ^ 2 =
      (specialValueOrder M : ℂ) * (epsilon M : ℂ) := by
    exact_mod_cast length_sq M hM
  have hcoef : (scale M : ℂ) ^ 2 / (epsilon M : ℂ) =
      1 / (specialValueOrder M : ℂ) := by
    rw [hs]
    field_simp [he, hN]
    linear_combination hLs
  have hprod :
      (((M 1 0 : ℂ) * root M m k + (epsilon M : ℂ) * (m : ℂ)) *
        (argument M u : ℂ)) / (epsilon M : ℂ) =
      (((1 - M 1 1) * m + M 1 0 * k : ℤ) : ℂ) *
        ((u.1 : ℂ) * (repellingTau M : ℂ) + (u.2 : ℂ)) /
          (specialValueOrder M : ℂ) := by
    rw [root_coordinate M hM, ← root_eq_argument M hM u.1 u.2]
    simp only [combCoordinate, root, Complex.ofReal_mul, Complex.ofReal_intCast]
    calc
      _ = ((scale M : ℂ) ^ 2 / (epsilon M : ℂ)) *
          (((1 - M 1 1) * m + M 1 0 * k : ℤ) : ℂ) *
          ((u.1 : ℂ) * (repellingTau M : ℂ) + (u.2 : ℂ)) := by ring
      _ = _ := by rw [hcoef]; ring
  have hpair :
      (((M 1 0 : ℂ) * root M m k + (epsilon M : ℂ) * (m : ℂ)) *
        (argument M u : ℂ)) / (epsilon M : ℂ) +
      (u.1 : ℂ) * (root M m k + (m : ℂ) * (repellingTau M : ℂ)) +
      (m : ℂ) * (u.2 : ℂ) =
      (specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (m, k) -
        (m, k)) u : ℂ) / (specialValueOrder M : ℂ) := by
    rw [hprod]
    simp only [root, hs, specialValueOmega, L2r.rowAction, Prod.fst_sub, Prod.snd_sub]
    push_cast
    field_simp [hN]
    have hf := G2RepellingPointValuesAux.fixed_numerator M hM
    have ht : (M 1 0 : ℂ) * (repellingTau M : ℂ) + (M 1 1 : ℂ) =
        (epsilon M : ℂ) := G2RepellingPointValuesAux.etaDenom_repelling M
    simp only [length, specialValueOrder, Complex.ofReal_sub, Complex.ofReal_one,
      Int.cast_sub, Int.cast_add, Int.cast_ofNat]
    linear_combination
      (m : ℂ) * (u.1 : ℂ) * hf + (k : ℂ) * (u.1 : ℂ) * ht
  have hb := G2RepellingPointValuesAux.argument_balance M hM (m, k)
  rw [← root_eq_argument M hM m k] at hb
  push_cast
  linear_combination hpair - hb

/-- The character has the existing positive-sign pairing convention. [RW26, (3), p. 3, p. 12]. -/
theorem kernel_character (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (m k : ℤ) :
    kernelK M u m (root M m k) / combV M (root M m k) =
      specialValuePairingLift M (m, k) u := by
  unfold kernelK combV specialValuePairingLift
  rw [← e_sub]
  apply (e_eq_iff_int_sub _ _).mpr
  exact ⟨-k - m * u.2, phase_integer_error M hM u m k⟩

/-- Actual joint regularity and nonzero center values, also on Λ. [RW26, p. 12, Lemma 2], supplying
removable-center API. -/
theorem phi_units_at_root (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m k : ℤ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M m 0 p.1 p.2)
        (root M m k, (repellingTau M : ℂ)) ∧
      AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M (m + v.1) 0 p.1 p.2)
        (root M m k + (argument M v : ℂ), (repellingTau M : ℂ)) ∧
      phiNumerator M m k ≠ 0 ∧ phiDenominator M v m k ≠ 0 := by
  have units (x : ℤ × ℤ) :
      AnalyticAt ℂ (fun p : ℂ × ℂ => modularPhi M x.1 0 p.1 p.2)
        ((argument M x : ℂ), (repellingTau M : ℂ)) ∧
      modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ) ≠ 0 := by
    by_cases hx : x ∈ specialValueLattice M
    · obtain ⟨_, a, b, harg, hbalance, _⟩ :=
        RepellingPointValues.repelling_lattice_common_exponent M hM x hx 0
      obtain ⟨U, _, hp, _, ha, hn⟩ := modularPhi_fixedPoint_lattice_joint M hM.1 hM.2
        x.1 0 (repellingTau M) (epsilon_pos M hM) (repellingTau_fixedPoint M hM)
        a b (by simpa only [add_zero] using hbalance)
      rw [harg]
      exact ⟨ha ((a : ℂ) * (repellingTau M : ℂ) + (b : ℂ),
        (repellingTau M : ℂ)) hp,
        hn ((a : ℂ) * (repellingTau M : ℂ) + (b : ℂ), (repellingTau M : ℂ)) hp⟩
    · simpa only [add_zero] using
        RepellingPointValues.repellingPhi_joint_regular M hM x hx 0
  have hn := units (m, k)
  have hd := units ((m, k) + v)
  have harg : root M m k + (argument M v : ℂ) =
      (argument M ((m, k) + v) : ℂ) := by
    rw [root_eq_argument M hM, ← Complex.ofReal_add]
    congr 1
    simp only [argument, Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [root_eq_argument M hM] using hn.1
  · rw [harg]
    exact hd.1
  · simpa only [phiNumerator, root_eq_argument M hM] using hn.2
  · simpa only [phiDenominator, harg, Prod.fst_add, Prod.fst] using hd.2

/-- The raw quotient is analytic at this root before the comb factor is inserted. [RW26, p. 12, p.
13]. -/
theorem quotient_analytic_at_root (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m k : ℤ) :
    AnalyticAt ℂ (fun z => modularPhi M m 0 z (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 0 (z + (argument M v : ℂ)) (repellingTau M : ℂ))
      (root M m k) := by
  obtain ⟨hn, hd, _, hd0⟩ := phi_units_at_root M hM v m k
  have hemb : AnalyticAt ℂ (fun z : ℂ => (z, (repellingTau M : ℂ)))
      (root M m k) := analyticAt_id.prod analyticAt_const
  have hemb' : AnalyticAt ℂ
      (fun z : ℂ => (z + (argument M v : ℂ), (repellingTau M : ℂ)))
      (root M m k) := (analyticAt_id.add analyticAt_const).prod analyticAt_const
  exact (hn.comp (f := fun z : ℂ => (z, (repellingTau M : ℂ))) hemb).div
    (hd.comp (f := fun z : ℂ =>
      (z + (argument M v : ℂ), (repellingTau M : ℂ))) hemb') hd0

/-- Every labelled comb root is a genuine simple pole for this raw kernel. [RW26, p. 13]. -/
theorem rho_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ) : rho M u v m k ≠ 0 := by
  have hs : (scale M : ℂ) ≠ 0 := by
    exact_mod_cast (scale_identities M hM).1.ne'
  have hp := phi_units_at_root M hM v m k
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hs (e_ne_zero _)) hp.2.2.1) hp.2.2.2

/-- Punctured residue limit, independent of rawF's total value at its pole. [RW26, p. 13]. -/
theorem residue_limit (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ) :
    Tendsto (fun z => (z - root M m k) * rawF M u v m z)
      (𝓝[≠] (root M m k))
      (𝓝 (rho M u v m k / (2 * (Real.pi : ℂ) * Complex.I))) := by
  let p := root M m k
  let a : ℂ → ℂ := fun z => kernelK M u m z *
    (modularPhi M m 0 z (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 0 (z + (argument M v : ℂ)) (repellingTau M : ℂ))
  let b : ℂ → ℂ := fun z => combV M z - combU M m z
  let q : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let d : ℂ := q * ((length M : ℂ) / (epsilon M : ℂ)) * combV M p
  have ha : AnalyticAt ℂ a p := by
    have hK : AnalyticAt ℂ (kernelK M u m) p := by unfold kernelK e; fun_prop
    exact hK.mul (quotient_analytic_at_root M hM v m k)
  have hb : AnalyticAt ℂ b p := by unfold b combV combU e; fun_prop
  have hb0 : b p = 0 := by
    apply sub_eq_zero.mpr
    dsimp only [p, combV, combU]
    rw [root_eq_argument M hM]
    exact (RepellingPointValues.repelling_phase M hM (m, k)).symm
  have hd := comb_hasDerivAt M hM m k
  have hcoeff : a p / d = rho M u v m k / q := by
    have hq : q ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hL : (length M : ℂ) ≠ 0 := by exact_mod_cast (length_pos M hM).ne'
    have he : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
    have hv : combV M p ≠ 0 := e_ne_zero _
    have hphi := (phi_units_at_root M hM v m k).2.2.2
    change (kernelK M u m p * (phiNumerator M m k / phiDenominator M v m k)) /
      (q * ((length M : ℂ) / (epsilon M : ℂ)) * combV M p) = _
    unfold rho
    rw [← kernel_character M hM u m k]
    simp only [scale, Complex.ofReal_div]
    dsimp only [p] at hv ⊢
    field_simp [hq, hL, he, hv, hphi]
  have ht := G2CombResiduesAux.tendsto_mul_div_at_simple_zero ha hb hb0 hd.1 hd.2
  rw [hcoeff] at ht
  simpa only [a, b, p, rawF, div_mul_eq_mul_div] using ht

/-- A genuine local Laurent expansion with an analytic remainder. It is not inferred from a point
value, nor assumed in a ledger definition. [RW26, p. 13]. -/
theorem local_principalPart (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ) :
    ∃ (R : ℝ) (g : ℂ → ℂ), 0 < R ∧
      AnalyticOnNhd ℂ g (Metric.closedBall (root M m k) R) ∧
      ∀ z ∈ Metric.closedBall (root M m k) R, z ≠ root M m k →
        rawF M u v m z =
          (rho M u v m k / (2 * (Real.pi : ℂ) * Complex.I)) / (z - root M m k) + g z := by
  let p := root M m k
  let a : ℂ → ℂ := fun z => kernelK M u m z *
    (modularPhi M m 0 z (repellingTau M : ℂ) /
      modularPhi M (m + v.1) 0 (z + (argument M v : ℂ)) (repellingTau M : ℂ))
  let b : ℂ → ℂ := fun z => combV M z - combU M m z
  let q : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let d : ℂ := q * ((length M : ℂ) / (epsilon M : ℂ)) * combV M p
  have ha : AnalyticAt ℂ a p := by
    have hK : AnalyticAt ℂ (kernelK M u m) p := by unfold kernelK e; fun_prop
    exact hK.mul (quotient_analytic_at_root M hM v m k)
  have hb : AnalyticAt ℂ b p := by unfold b combV combU e; fun_prop
  have hb0 : b p = 0 := by
    apply sub_eq_zero.mpr
    dsimp only [p, combV, combU]
    rw [root_eq_argument M hM]
    exact (RepellingPointValues.repelling_phase M hM (m, k)).symm
  have hd := comb_hasDerivAt M hM m k
  have hcoeff : a p / d = rho M u v m k / q := by
    have hq : q ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hL : (length M : ℂ) ≠ 0 := by exact_mod_cast (length_pos M hM).ne'
    have he : (epsilon M : ℂ) ≠ 0 := by exact_mod_cast (epsilon_pos M hM).ne'
    have hv : combV M p ≠ 0 := e_ne_zero _
    have hphi := (phi_units_at_root M hM v m k).2.2.2
    change (kernelK M u m p * (phiNumerator M m k / phiDenominator M v m k)) /
      (q * ((length M : ℂ) / (epsilon M : ℂ)) * combV M p) = _
    unfold rho
    rw [← kernel_character M hM u m k]
    simp only [scale, Complex.ofReal_div]
    dsimp only [p] at hv ⊢
    field_simp [hq, hL, he, hv, hphi]
  obtain ⟨R, g, hR, hg, hfg⟩ :=
    G2CombResiduesAux.exists_analytic_remainder ha hb hb0 hd.1 hd.2
  refine ⟨R, g, hR, hg, ?_⟩
  intro z hz hne
  have hh := hfg z hz hne
  rw [hcoeff] at hh
  simpa only [a, b, rawF, div_mul_eq_mul_div] using hh

/-- Positive CCW circle value, for every sufficiently small radius. [RW26, p. 13]. -/
theorem local_circle_value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      FinitePrincipalParts.circleCCW (root M m k) r (rawF M u v m) = rho M u v m k := by
  obtain ⟨R, g, hR, hg, he⟩ := local_principalPart M hM u v m k
  refine ⟨R, hR, fun r hr hrR => ?_⟩
  have hsub : Metric.closedBall (root M m k) r ⊆ Metric.closedBall (root M m k) R :=
    Metric.closedBall_subset_closedBall hrR.le
  have h := FinitePrincipalParts.circleCCW_of_local_principalPart
    (rawF M u v m) g (root M m k) r 1
    (fun _ => rho M u v m k / (2 * (Real.pi : ℂ) * Complex.I)) hr
    (hg.mono hsub) (by
      intro z hz hne
      simpa only [FinitePrincipalParts.principalPart, Finset.range_one,
        Finset.sum_singleton, zero_add, pow_one] using he z (hsub hz) hne)
  have hq : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  simpa only [FinitePrincipalParts.residueCoefficient, Nat.one_ne_zero, if_false,
    mul_div_cancel₀ (rho M u v m k) hq] using h

/-- Right up minus left up is the positive boundary, with bottom minus top connectors. No assumption
about residues is hidden in this identity. [RW26, p. 13]. -/
theorem upward_rectangle_orientation (f : ℂ → ℂ) (x₀ x₁ R : ℝ) :
    FinitePrincipalParts.rectangleCCW (g1VerticalPoint x₀ (-R)) (g1VerticalPoint x₁ R) f =
      (∫ t : ℝ in -R..R, g1VerticalPullback f x₁ t) -
        (∫ t : ℝ in -R..R, g1VerticalPullback f x₀ t) +
        horizontalIntegral f x₀ x₁ (-R) - horizontalIntegral f x₀ x₁ R := by
  simp [FinitePrincipalParts.rectangleCCW, g1VerticalPoint, g1VerticalPullback,
    horizontalIntegral, horizontalPullback,
    mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

#print root
#print rho
#check @modularPhi_fixedPoint_lattice_value
#check @SpecialValueBridge.repellingValues_mk
#check @residue_limit
#check @upward_rectangle_orientation

end SICLean.L4.G2.CombResidues
