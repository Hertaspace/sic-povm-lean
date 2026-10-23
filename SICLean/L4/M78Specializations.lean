import SICLean.L4.M78Transport
import SICLean.L4.M78SpecializationsAux

set_option autoImplicit false

/-!
# Original alpha-cubed and rank-r actual values

The P.N equalities are arithmetic matching of
the fixed period, not Q3 or algebraicity assumptions. The existing
rwL2c_parameters / rwL2rc_parameters discharge the matrix-order equality
required by M72's already proved final transports. All other analytic
obligations here are precisely `FamilyPentagon F`. [RW26, pp. 2--3, p. 20, pp. 20--21, §4.4, (2),
(4), (37), footnote 2] (original alpha-cubed chain).
The rank-r values specialize `L2r.gamma_arithmetic`, `L2rc.gamma_parameters`, and
`SpecialValueL2rc`.
The two raw mu*Phi theorems are explicitly off-lattice point evaluations.
-/

noncomputable section

namespace SICLean.L3.M78.Specializations

universe u

variable {K : Type u} [Field K] [NumberField K] {P : PeriodData K}

/--
Original gamma=alpha^3, on the established [RW26] row quotient; [RW26, p. 20, §4.4, (37)]. Uses
M72.l2c_isAlgebraic_of_family after discharging hAlg.
-/
theorem l2c_values_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (M : ℕ) [Fact (4 ≤ M)]
    (hN : P.N = L2b.groupOrder M) (g : L2c.RWGroup M) :
    IsAlgebraic ℚ (L4.rwL2cPlus M g) ∧ IsAlgebraic ℚ (L4.rwL2cMinus M g) := by
  apply M72.l2c_isAlgebraic_of_family F (Point.familyPoint_isAlgebraic F h7) M _ g
  rw [(L4.rwL2c_parameters M).1, hN]

/--
The original chain's actual values in the already proved Smith coordinates.
No FQD, Fourier or extra five-term contract is needed for this transport; [RW26, pp. 20--21, §4.4]
(specialization).
-/
theorem l2c_smithValues_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (M : ℕ) [Fact (4 ≤ M)]
    (hN : P.N = L2b.groupOrder M) (g : L2b.G M) :
    IsAlgebraic ℚ (L2c.smithValues M (L4.rwL2cPlus M) g) ∧
      IsAlgebraic ℚ (L2c.smithValues M (L4.rwL2cMinus M) g) := by
  exact l2c_values_isAlgebraic F h7 M hN (L2c.fromSmith M g)

/--
Every integer row in the original chain, including the zero class; [RW26, p. 2, p. 20, (2), (37)].
-/
theorem l2c_rowValues_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (M : ℕ) [Fact (4 ≤ M)]
    (hN : P.N = L2b.groupOrder M) (v : ℤ × ℤ) :
    IsAlgebraic ℚ (L4.rwL2cPlus M (L2c.mk M v)) ∧
      IsAlgebraic ℚ (L4.rwL2cMinus M (L2c.mk M v)) := by
  exact l2c_values_isAlgebraic F h7 M hN (L2c.mk M v)

/--
Arithmetic normalization of both original zero branches, independently
of (7). The root is taken before inversion. [RW26, p. 3, (4)]. `rwL2c_parameters` identifies
epsilon^3.
-/
theorem l2c_originValues_isAlgebraic (M : ℕ) [Fact (4 ≤ M)] :
    IsAlgebraic ℚ (Real.sqrt (L2a.epsilon M ^ 3) : ℂ) ∧
      IsAlgebraic ℚ ((Real.sqrt (L2a.epsilon M ^ 3) : ℂ)⁻¹) := by
  have h := L4.M78SpecializationsAux.period_sqrt_isAlgebraic
    (L4.rwL2cPeriod M) (L4.rwL2c_admissible M).2
  rw [(L4.rwL2c_parameters M).2.2] at h
  exact ⟨h, h.inv⟩

/--
The original actual nonlattice mu*Phi, without replacing its eta multiplier
or square-root branch; [RW26, p. 2, p. 20, (2), (37)]. This is a point-value statement, not a germ.
-/
theorem l2c_phiValue_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (M : ℕ) [Fact (4 ≤ M)]
    (hN : P.N = L2b.groupOrder M) (v : ℤ × ℤ)
    (hv : v ∉ L4.specialValueLattice (L4.rwL2cPeriod M)) :
    IsAlgebraic ℚ (L4.etaMultiplier (L4.rwL2cPeriod M) *
      L4.modularPhi (L4.rwL2cPeriod M) v.1 0
        (L4.specialValueArgument (L4.rwL2cPeriod M) v)
        (L4.specialValueTau (L4.rwL2cPeriod M) : ℂ)) := by
  apply Transport.specialValueRaw_isAlgebraic F h7 (L4.rwL2cPeriod M)
    (L4.rwL2c_admissible M).2 _ v hv
  rw [(L4.rwL2c_parameters M).1, hN]

/--
Rank-r gamma=beta^2 L, on its established [RW26] quotient, without choosing
an odd exponent as new input. [RW26, p. 20, (37)].
The rank arithmetic is that of `L2r` and `L2rc`.
-/
theorem l2rc_values_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (d r : ℕ) [Fact (L2r.Admissible d r)]
    (hN : P.N = L2r.groupOrder d r) (g : L2rc.RWGroup d r) :
    IsAlgebraic ℚ (L4.rwL2rcPlus d r g) ∧ IsAlgebraic ℚ (L4.rwL2rcMinus d r g) := by
  apply M72.l2rc_isAlgebraic_of_family F (Point.familyPoint_isAlgebraic F h7) d r _ g
  rw [(L4.rwL2rc_parameters d r).1, hN]

/--
The rank-r chain's actual E and minus branch on the rectangular group.
Uses the existing rwIndexMap through concreteValues; no values are redefined; [RW26, p. 20, (37)].
-/
theorem l2rc_concreteValues_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (d r : ℕ) [Fact (L2r.Admissible d r)]
    (hN : P.N = L2r.groupOrder d r) (g : L2r.G d r) :
    IsAlgebraic ℚ (L2rc.concreteValues d r (L4.rwL2rcPlus d r) g) ∧
      IsAlgebraic ℚ (L2rc.concreteValues d r (L4.rwL2rcMinus d r) g) := by
  exact l2rc_values_isAlgebraic F h7 d r hN (L2r.rwIndexMap d r g)

/--
Every rank-r integer row, retaining the separate zero branches; [RW26, p. 2, p. 3, (2), footnote 2].
-/
theorem l2rc_rowValues_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (d r : ℕ) [Fact (L2r.Admissible d r)]
    (hN : P.N = L2r.groupOrder d r) (v : ℤ × ℤ) :
    IsAlgebraic ℚ (L4.rwL2rcPlus d r (L2rc.mk d r v)) ∧
      IsAlgebraic ℚ (L4.rwL2rcMinus d r (L2rc.mk d r v)) := by
  exact l2rc_values_isAlgebraic F h7 d r hN (L2rc.mk d r v)

/--
Arithmetic rank-r zero branches, independently of (7). Here `eta` is the
existing real period `L2r.eta`, not a new multiplier; [RW26, p. 3, (4)].
-/
theorem l2rc_originValues_isAlgebraic (d r : ℕ) [Fact (L2r.Admissible d r)] :
    IsAlgebraic ℚ (Real.sqrt (L2r.eta d r) : ℂ) ∧
      IsAlgebraic ℚ ((Real.sqrt (L2r.eta d r) : ℂ)⁻¹) := by
  have h := L4.M78SpecializationsAux.period_sqrt_isAlgebraic
    (L4.rwL2rcPeriod d r) (L4.rwL2rc_admissible d r).2
  rw [(L4.rwL2rc_parameters d r).2.2] at h
  exact ⟨h, h.inv⟩

/--
Actual nonlattice rank-r mu*Phi, with all definitions unchanged; [RW26, p. 2, p. 20, (2), (37)].
-/
theorem l2rc_phiValue_isAlgebraic (F : FinitePseudolatticeFamily P)
    (h7 : M75.Family.FamilyPentagon F) (d r : ℕ) [Fact (L2r.Admissible d r)]
    (hN : P.N = L2r.groupOrder d r) (v : ℤ × ℤ)
    (hv : v ∉ L4.specialValueLattice (L4.rwL2rcPeriod d r)) :
    IsAlgebraic ℚ (L4.etaMultiplier (L4.rwL2rcPeriod d r) *
      L4.modularPhi (L4.rwL2rcPeriod d r) v.1 0
        (L4.specialValueArgument (L4.rwL2rcPeriod d r) v)
        (L4.specialValueTau (L4.rwL2rcPeriod d r) : ℂ)) := by
  apply Transport.specialValueRaw_isAlgebraic F h7 (L4.rwL2rcPeriod d r)
    (L4.rwL2rc_admissible d r).2 _ v hv
  rw [(L4.rwL2rc_parameters d r).1, hN]

#check @L4.rwL2c_parameters
#check @L4.rwL2rc_parameters
#check @M72.l2c_isAlgebraic_of_family
#check @M72.l2rc_isAlgebraic_of_family
#check @l2c_values_isAlgebraic
#check @l2rc_values_isAlgebraic
#print L2c.smithValues
#print L2rc.concreteValues

end SICLean.L3.M78.Specializations
