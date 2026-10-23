import SICLean.L4.SpecialValueUnitAction
import SICLean.L2rc.Inputs

set_option autoImplicit false

/-!
# Actual special values in the rank-r L2rc interface

The arithmetic specialization is the existing principal pair (d,r) from
L2r.Arithmetic: L=alpha d r, γ=beta²L, and γ=L^k for a proved positive
odd k. The base action is L. No recurrence index is chosen in a definition.

The period is packaged directly from the old γ, so its row quotient is
definitionally L2rc.RWGroup d r. Its equivalence below is the identity.
Fourier (6) and ratio (7) remain explicit hypotheses.
-/

noncomputable section

open scoped MatrixGroups

namespace SICLean.L4

/--
Determinant-one packaging of the fixed L2r base L. The generic
scope is [RW26, pp. 2--3].
-/
def rwL2rcBase (d r : ℕ) : SL(2, ℤ) :=
  ⟨L2r.alpha d r, by
  simp [L2r.alpha, Matrix.det_fin_two]⟩

/--
The existing γ=β²L, without a chosen odd exponent. [RW26, pp. 2--3].
-/
def rwL2rcPeriod (d r : ℕ) [Fact (L2r.Admissible d r)] : SL(2, ℤ) :=
  ⟨L2r.gamma d r, by
  exact (L2r.gamma_arithmetic (Fact.out : L2r.Admissible d r)).2.2.1⟩

/--
Both actual matrices meet the positive-c hyperbolic scope.
[RW26, p. 2]. This uses the already proved `L2rc.gamma_parameters`.
-/
theorem rwL2rc_admissible (d r : ℕ) [Fact (L2r.Admissible d r)] :
    SpecialValueAdmissible (rwL2rcBase d r) ∧
      SpecialValueAdmissible (rwL2rcPeriod d r) := by
  have h := Fact.out (p := L2r.Admissible d r)
  have hlev : 5 ≤ L2r.level d r := L2r.level_ge_five h
  have hgar := L2r.gamma_arithmetic h
  have hgap : 0 < L2r.gap d r := by
    simp only [L2r.gap]
    have := h.main_range
    omega
  have hd : 0 < (d : ℤ) := by
    have := h.main_range
    omega
  have hco : 0 < L2r.cofactor d r := by
    simp only [L2r.cofactor]
    omega
  have hell : (L2r.ell d r : ℤ) = (L2r.level d r : ℤ) - 2 := by
    simp only [L2r.ell]
    exact Nat.cast_sub (by omega)
  constructor
  · constructor
    · show (0 : ℤ) < L2r.alpha d r 1 0
      simp [L2r.alpha]
    · show (2 : ℤ) < L2r.alpha d r 0 0 + L2r.alpha d r 1 1
      simp [L2r.alpha]
      omega
  · constructor
    · show (0 : ℤ) < L2r.gamma d r 1 0
      rw [hgar.2.2.2.2]
      exact mul_pos hd hgap
    · show (2 : ℤ) < L2r.gamma d r 0 0 + L2r.gamma d r 1 1
      have ht := hgar.2.2.2.1
      simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] at ht
      rw [show L2r.gamma d r 0 0 + L2r.gamma d r 1 1 =
        (L2r.groupOrder d r : ℤ) + 2 by omega]
      have hgo : 0 < L2r.groupOrder d r := by
        simp only [L2r.groupOrder]
        have hdn : 0 < d := by
          have := h.main_range
          omega
        positivity
      have hgo' : (0 : ℤ) < (L2r.groupOrder d r : ℤ) := by exact_mod_cast hgo
      omega

/--
The attracting fixed point is the base unit u; γ's automorphy
factor is η. [RW26, p. 20, p. 3, (37), (4)].
-/
theorem rwL2rc_parameters (d r : ℕ) [Fact (L2r.Admissible d r)] :
    specialValueOrder (rwL2rcPeriod d r) = (L2r.groupOrder d r : ℤ) ∧
      specialValueTau (rwL2rcPeriod d r) = L2r.unit d r ∧
      specialValueEpsilon (rwL2rcPeriod d r) = L2r.eta d r := by
  have h := Fact.out (p := L2r.Admissible d r)
  have hN : specialValueOrder (rwL2rcPeriod d r) = (L2r.groupOrder d r : ℤ) := by
    have ht := (L2r.gamma_arithmetic h).2.2.2.1
    simp only [specialValueOrder, rwL2rcPeriod, Matrix.trace, Matrix.diag_apply,
      Fin.sum_univ_two] at ht ⊢
    omega
  have htau : specialValueTau (rwL2rcPeriod d r) = L2r.unit d r := by
    obtain ⟨m, hm1, hbeta, hgamma⟩ := L2rc.gamma_odd_power d r
    have hk : 0 < 2 * m + 1 := by omega
    have hpow : rwL2rcPeriod d r = rwL2rcBase d r ^ (2 * m + 1) := by
      apply Subtype.ext
      show L2r.gamma d r = L2r.alpha d r ^ (2 * m + 1)
      exact hgamma
    rw [hpow]
    rw [specialValueTau_pow (rwL2rcBase d r) (rwL2rc_admissible d r).1
      (2 * m + 1) hk]
    unfold specialValueTau L2r.unit rwL2rcBase
    simp [L2r.alpha]
  refine ⟨hN, htau, ?_⟩
  unfold specialValueEpsilon
  rw [htau]
  simpa [rwL2rcPeriod] using (L2r.eta_from_gamma h).symm

/--
A positive odd power is a conclusion of the principal-pair arithmetic,
not a hidden choice or a new input. It permits [RW26, p. 14, Prop. 8]
and the already proved `L2rc.gamma_odd_power`.
-/
theorem rwL2rcPeriod_odd_power (d r : ℕ) [Fact (L2r.Admissible d r)] :
    ∃ k : ℕ, 0 < k ∧ Odd k ∧ rwL2rcPeriod d r = rwL2rcBase d r ^ k := by
  obtain ⟨m, hm1, hbeta, hgamma⟩ := L2rc.gamma_odd_power d r
  refine ⟨2 * m + 1, by omega, ?_, ?_⟩
  · rw [Nat.odd_iff]
    omega
  · apply Subtype.ext
    show L2r.gamma d r = L2r.alpha d r ^ (2 * m + 1)
    exact hgamma

/--
The literal congruence lattice and the existing row quotient agree.
[RW26, p. 3, (3)].
The corresponding comparison is already proved in L2rc.Coordinates.
-/
theorem rwL2rc_lattice_eq (d r : ℕ) [Fact (L2r.Admissible d r)] :
    specialValueLattice (rwL2rcPeriod d r) = L2rc.lattice d r := by
  simpa [specialValueLattice, rwL2rcPeriod] using
    (L2rc.lattice_eq_row_range d r).symm

/--
The period wrapper preserves the old row-lattice quotient literally.
[RW26, p. 3, (3)].
-/
def rwL2rcEquiv (d r : ℕ) [Fact (L2r.Admissible d r)] :
    L2rc.RWGroup d r ≃+ SpecialValueGroup (rwL2rcPeriod d r) :=
  AddEquiv.refl (L2rc.RWGroup d r)

/--
Exact identity on every integer row lift. [RW26, p. 3, (3)].
-/
theorem rwL2rcEquiv_mk (d r : ℕ) [Fact (L2r.Admissible d r)] (u : ℤ × ℤ) :
    rwL2rcEquiv d r (L2rc.mk d r u) = specialValueMk (rwL2rcPeriod d r) u := by
  rfl

/--
Actual plus values on the fixed existing group. [RW26, pp. 2--3, (2), (4)].
-/
def rwL2rcPlus (d r : ℕ) [Fact (L2r.Admissible d r)] : L2rc.RWGroup d r → ℂ :=
  specialValuePlus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 ∘ rwL2rcEquiv d r

/--
Actual minus values with the separately prescribed inverse origin.
[RW26, pp. 2--3].
-/
def rwL2rcMinus (d r : ℕ) [Fact (L2r.Admissible d r)] : L2rc.RWGroup d r → ℂ :=
  specialValueMinus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 ∘ rwL2rcEquiv d r

/--
Exact [RW26, (3)] Gaussian, before the existing rwNumerator transport.
[RW26, p. 3].
The old Gaussian and its rank-r rectangular coordinates are unchanged.
-/
theorem rwL2rc_gaussian (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u : L2rc.RWGroup d r) :
    specialValueGaussian (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 (rwL2rcEquiv d r u) =
      L2rc.gaussian d r u := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  change specialValueGaussianLift (rwL2rcPeriod d r) a = L2rc.gaussianLift d r a
  have h := Fact.out (p := L2r.Admissible d r)
  have hN : specialValueOrder (rwL2rcPeriod d r) = (L2r.groupOrder d r : ℤ) := by
    have ht := (L2r.gamma_arithmetic h).2.2.2.1
    simp only [specialValueOrder, rwL2rcPeriod, Matrix.trace, Matrix.diag_apply,
      Fin.sum_univ_two] at ht ⊢
    omega
  unfold specialValueGaussianLift L2rc.gaussianLift
  rw [hN]
  have hrow : L2r.rowAction (rwL2rcPeriod d r : Matrix (Fin 2) (Fin 2) ℤ) a =
      L2rc.rowGamma d r a := rfl
  rw [hrow]
  congr 1
  simp only [e, L2a.e, specialValueOmega, L2rc.omega]
  congr 1
  push_cast
  ring

/--
Exact positive-sign pairing. [RW26, p. 3, (3)].
-/
theorem rwL2rc_pairing (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u v : L2rc.RWGroup d r) :
    specialValuePairing (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
        (rwL2rcEquiv d r u) (rwL2rcEquiv d r v) = L2rc.pairing d r u v := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  refine QuotientAddGroup.induction_on v ?_
  intro b
  change specialValuePairingLift (rwL2rcPeriod d r) a b = L2rc.pairingLift d r a b
  have h := Fact.out (p := L2r.Admissible d r)
  have hN : specialValueOrder (rwL2rcPeriod d r) = (L2r.groupOrder d r : ℤ) := by
    have ht := (L2r.gamma_arithmetic h).2.2.2.1
    simp only [specialValueOrder, rwL2rcPeriod, Matrix.trace, Matrix.diag_apply,
      Fin.sum_univ_two] at ht ⊢
    omega
  unfold specialValuePairingLift L2rc.pairingLift
  rw [hN]
  have hrow : L2r.rowAction (rwL2rcPeriod d r : Matrix (Fin 2) (Fin 2) ℤ) a =
      L2rc.rowGamma d r a := rfl
  rw [hrow]
  simp only [e, L2a.e, specialValueOmega, L2rc.omega]
  congr 1
  push_cast
  ring

/--
The fixed functions use precisely the actual lifts, including zero.
[RW26, p. 2, p. 12, (2), Lemma 2].
-/
theorem rwL2rcValues_mk (d r : ℕ) [Fact (L2r.Admissible d r)] (u : ℤ × ℤ) :
    rwL2rcPlus d r (L2rc.mk d r u) = specialValuePlusLift (rwL2rcPeriod d r) u ∧
      rwL2rcMinus d r (L2rc.mk d r u) = specialValueMinusLift (rwL2rcPeriod d r) u := by
  constructor
  · change specialValuePlus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
      (L2rc.mk d r u) = _
    exact specialValuePlus_mk (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 u
  · change specialValueMinus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
      (L2rc.mk d r u) = _
    exact specialValueMinus_mk (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 u

/--
Literal plus branch of Theorem 2 (4), retaining N=tr(γ)-2.
[RW26, p. 3].
-/
theorem rwL2rcPlus_zero (d r : ℕ) [Fact (L2r.Admissible d r)] :
    rwL2rcPlus d r 0 = L2rc.originPlus d r := by
  change specialValuePlus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 0 = _
  rw [specialValuePlus_origin_formula]
  have hN : specialValueOrder (rwL2rcPeriod d r) = (L2r.groupOrder d r : ℤ) := by
    have h := Fact.out (p := L2r.Admissible d r)
    have ht := (L2r.gamma_arithmetic h).2.2.2.1
    simp only [specialValueOrder, rwL2rcPeriod, Matrix.trace, Matrix.diag_apply,
      Fin.sum_univ_two] at ht ⊢
    omega
  unfold L2rc.originPlus
  rw [hN]
  push_cast
  rfl

/--
Literal minus branch of Theorem 2 (4), with positive outer root.
[RW26, p. 3].
-/
theorem rwL2rcMinus_zero (d r : ℕ) [Fact (L2r.Admissible d r)] :
    rwL2rcMinus d r 0 = L2rc.originMinus d r := by
  change specialValueMinus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 0 = _
  rw [specialValueMinus_origin_formula]
  have hN : specialValueOrder (rwL2rcPeriod d r) = (L2r.groupOrder d r : ℤ) := by
    have h := Fact.out (p := L2r.Admissible d r)
    have ht := (L2r.gamma_arithmetic h).2.2.2.1
    simp only [specialValueOrder, rwL2rcPeriod, Matrix.trace, Matrix.diag_apply,
      Fin.sum_univ_two] at ht ⊢
    omega
  unfold L2rc.originMinus
  rw [hN]
  push_cast
  rfl

/--
Both branches are nonzero at every class. [RW26, p. 6, p. 12, Lemma 2].
-/
theorem rwL2rc_values_ne_zero (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u : L2rc.RWGroup d r) :
    rwL2rcPlus d r u ≠ 0 ∧ rwL2rcMinus d r u ≠ 0 := by
  change specialValuePlus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
      (rwL2rcEquiv d r u) ≠ 0 ∧
    specialValueMinus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
      (rwL2rcEquiv d r u) ≠ 0
  exact ⟨specialValuePlus_ne_zero (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 _,
    specialValueMinus_ne_zero (rwL2rcPeriod d r) (rwL2rc_admissible d r).2 _⟩

/--
Literal footnote 2, [RW26, p. 3].
-/
theorem rwL2rc_agree_off_zero (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u : L2rc.RWGroup d r) (hu : u ≠ 0) :
    rwL2rcPlus d r u = rwL2rcMinus d r u := by
  change specialValuePlus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
      (rwL2rcEquiv d r u) =
    specialValueMinus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
      (rwL2rcEquiv d r u)
  exact specialValue_agree_off_zero (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
    (rwL2rcEquiv d r u) hu

/--
The exact existing mixed-reflection field, including zero.
[RW26, p. 3, p. 12, (5)].
-/
theorem rwL2rc_mixed_reflection (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u : L2rc.RWGroup d r) :
    rwL2rcPlus d r u * rwL2rcMinus d r (-u) = (L2rc.gaussian d r u)⁻¹ := by
  have h := specialValue_mixed_reflection (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
    (rwL2rcEquiv d r u)
  have hneg : rwL2rcEquiv d r (-u) = -(rwL2rcEquiv d r u) :=
    (rwL2rcEquiv d r).map_neg u
  change specialValuePlus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
      (rwL2rcEquiv d r u) *
    specialValueMinus (rwL2rcPeriod d r) (rwL2rc_admissible d r).2
      (rwL2rcEquiv d r (-u)) = _
  rw [hneg, h, rwL2rc_gaussian d r u]

/--
The base L action from Prop. 8, rather than γ's trivial action.
[RW26, p. 14].
-/
theorem rwL2rc_epsilon_invariant (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u : L2rc.RWGroup d r) :
    rwL2rcPlus d r u = rwL2rcPlus d r (L2rc.epsilonAction d r u) := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  change rwL2rcPlus d r (L2rc.mk d r a) =
    rwL2rcPlus d r (L2rc.epsilonAction d r (L2rc.mk d r a))
  rw [(rwL2rcValues_mk d r a).1, L2rc.epsilonAction_mk, (rwL2rcValues_mk d r _).1]
  obtain ⟨m, hm1, hbeta, hgamma⟩ := L2rc.gamma_odd_power d r
  have hk : 0 < 2 * m + 1 := by omega
  have hk2 : 2 ≤ 2 * m + 1 := by omega
  have hpow : rwL2rcPeriod d r = rwL2rcBase d r ^ (2 * m + 1) := by
    apply Subtype.ext
    show L2r.gamma d r = L2r.alpha d r ^ (2 * m + 1)
    exact hgamma
  have hA : SpecialValueAdmissible (rwL2rcBase d r) := (rwL2rc_admissible d r).1
  rw [hpow]
  unfold specialValuePlusLift
  simp only [L2rc.rowAlpha]
  have hmem := specialValue_base_mem_lattice_iff (rwL2rcBase d r) (2 * m + 1) a
  change L2r.rowAction (L2r.alpha d r) a ∈
      specialValueLattice (rwL2rcBase d r ^ (2 * m + 1)) ↔
    a ∈ specialValueLattice (rwL2rcBase d r ^ (2 * m + 1)) at hmem
  by_cases h : a ∈ specialValueLattice (rwL2rcBase d r ^ (2 * m + 1))
  · have hb : L2r.rowAction (L2r.alpha d r) a ∈
        specialValueLattice (rwL2rcBase d r ^ (2 * m + 1)) := hmem.mpr h
    simp [h, hb]
  · have hb : L2r.rowAction (L2r.alpha d r) a ∉
        specialValueLattice (rwL2rcBase d r ^ (2 * m + 1)) := fun hc => h (hmem.mp hc)
    simp [h, hb]
    exact (specialValueRaw_base_invariant (rwL2rcBase d r) hA (2 * m + 1) hk2 a h).symm

/--
Only Fourier (6) and ratio (7) remain as visible inputs.
[RW26, p. 3, p. 14, Theorem 2, Prop. 8, footnote 2]. No cardinality, coordinate or Gaussian
assumption is added.
-/
theorem rwL2rcAnalyticInput_of_sums (d r : ℕ) [Fact (L2r.Admissible d r)]
    (hfourier : ∃ μ : ℂ, μ ≠ 0 ∧ ∀ u : L2rc.RWGroup d r,
      L2rc.normalizedSum d r (fun x => L2rc.pairing d r x u * rwL2rcPlus d r x) =
        μ / rwL2rcMinus d r u)
    (hratio : ∀ u v : L2rc.RWGroup d r, (u, v) ≠ (0, 0) →
      L2rc.normalizedSum d r
        (fun x => L2rc.pairing d r x u *
          (rwL2rcPlus d r x / rwL2rcMinus d r (x + v))) =
            rwL2rcPlus d r (u + v) / (rwL2rcMinus d r u * rwL2rcMinus d r v)) :
    L2rc.RWAnalyticInput d r (rwL2rcPlus d r) (rwL2rcMinus d r) := by
  refine ⟨?_, ?_⟩
  · exact { origin_plus := rwL2rcPlus_zero d r
            origin_minus := rwL2rcMinus_zero d r
            mixed_reflection := rwL2rc_mixed_reflection d r
            fourier := hfourier
            ratio_sum := hratio
            agree_off_zero := rwL2rc_agree_off_zero d r }
  · exact rwL2rc_epsilon_invariant d r

#print rwL2rcBase
#print rwL2rcPeriod
#print rwL2rcEquiv
#print rwL2rcPlus
#print rwL2rcMinus
#check rwL2rcPeriod_odd_power
#check rwL2rcValues_mk
#check rwL2rc_mixed_reflection
#check rwL2rc_epsilon_invariant
#check rwL2rcAnalyticInput_of_sums

end SICLean.L4
