import SICLean.Final.Assembly
import SICLean.L4.G1RealConclusion

set_option autoImplicit false

/-!
# The existence theorems without analytic hypotheses, assuming Proposition 7

`G1RealConclusion` discharges the analytic hypothesis of the final assembly.
The remaining hypothesis is [RW-rec, Prop. 7] for the actual values, in the form
`Prop7Actual`. It is proved in `SICLean.L5.ActualProp7`, which gives the final theorems
without hypotheses.

[RW26, Thm. 2], with footnote 2, and [RW26, Prop. 8], for the actual values of
the original chain, and the algebraicity of every actual special value, hold
with no further analytic hypothesis.
-/

noncomputable section

open OpenQuantumProblem23

namespace SICLean.FinalAssembly

/-- [RW26, Thm. 2], with footnote 2, and [RW26, Prop. 8], for the actual values
of the original chain. -/
theorem rwL2cAnalyticInput (M : ℕ) [Fact (4 ≤ M)] :
    L2c.RWAnalyticInput M (L4.rwL2cPlus M) (L4.rwL2cMinus M) :=
  L4.rwL2cAnalyticInput_of_G1 L4.g1RealConclusion M

/-- The same for the rank-r chain on the whole admissible range. -/
theorem rwL2rcAnalyticInput (d r : ℕ) [Fact (L2r.Admissible d r)] :
    L2rc.RWAnalyticInput d r (L4.rwL2rcPlus d r) (L4.rwL2rcMinus d r) :=
  L4.rwL2rcAnalyticInput_of_G1 L4.g1RealConclusion d r

/-- Every actual value of the original chain is algebraic. -/
theorem rwL2c_values_isAlgebraic (M : ℕ) [Fact (4 ≤ M)] (g : L2c.RWGroup M) :
    IsAlgebraic ℚ (L4.rwL2cPlus M g) ∧ IsAlgebraic ℚ (L4.rwL2cMinus M g) :=
  rwL2c_values_isAlgebraic_of_G1 L4.g1RealConclusion M g

/-- Every actual value of the rank-r chain is algebraic. -/
theorem rwL2rc_values_isAlgebraic (d r : ℕ) [Fact (L2r.Admissible d r)]
    (g : L2rc.RWGroup d r) :
    IsAlgebraic ℚ (L4.rwL2rcPlus d r g) ∧ IsAlgebraic ℚ (L4.rwL2rcMinus d r g) :=
  rwL2rc_values_isAlgebraic_of_G1 L4.g1RealConclusion d r g

/-- SIC-POVMs exist in every dimension, given Proposition 7 for the actual
values of the original chain. -/
theorem zaunerExistence_of_prop7
    (H7 : ∀ (M : ℕ) (hM : 4 ≤ M),
      letI : Fact (4 ≤ M) := ⟨hM⟩
      Prop7Actual (L4.rwL2cPlus M)) :
    ZaunerExistence :=
  zaunerExistence_of_G1_prop7 L4.g1RealConclusion H7

/-- Rank-r SICs exist in the whole admissible range, given Proposition 7 for
the actual values of the rank-r chain. -/
theorem hasRSIC_of_prop7
    (H7 : ∀ (d r : ℕ) (hr : 1 ≤ r) (hd : 2 * r + 1 < d)
      (hdiv : r * (d - r) ∣ d ^ 2 - 1),
      letI : Fact (L2r.Admissible d r) := ⟨⟨hr, hd, hdiv⟩⟩
      Prop7Actual (L4.rwL2rcPlus d r)) :
    ∀ (d r : ℕ), 1 ≤ r → 2 * r + 1 < d → r * (d - r) ∣ d ^ 2 - 1 →
      HasRSIC d r :=
  hasRSIC_of_G1_prop7 L4.g1RealConclusion H7

end SICLean.FinalAssembly
