import SICLean.L2b.Metric

set_option autoImplicit false

/-!
# The function form of a finite quantum dilogarithm

[RW26, Def. 4], [RW26, (31)], [RW26, Thm. 5(i)--(iii)], and [RW26, (36)].
The function definitions are separated so auxiliary proofs have no import cycle.
-/

noncomputable section

namespace SICLean.L2b

variable {A : Type*} [AddCommGroup A] [Fintype A]

local instance : DecidableEq A := Classical.decEq A

/-- The function relation [RW26, (31)], including every term of the sum. -/
def Pentagon (q E : A → ℂ) (C : ℂ) : Prop :=
  ∀ x y : A,
    metricPairing q x y * E x * E y =
      C + normalizedSum (fun z => E (y - z) * E z * q z * E (x - z))

/-- The E-dependent content of [RW26, Def. 4]. The ambient metric property and |A|>1
are supplied by the abstract theorem's context and proved for concrete G. -/
def IsFiniteQuantumDilogarithm (q E : A → ℂ) : Prop :=
  ∃ C : ℂ, C ≠ 0 ∧ Pentagon q E C

/-- The convolution kernel used in the proof, immediately before (33). -/
def pentagonKernel (q E : A → ℂ) (x z : A) : ℂ :=
  E (x - z) * E z * q z

/-- The scalar in [RW26, Thm. 5(iii)]. No root of unity or Gauss sum is assumed. -/
def fourierScalar (q E : A → ℂ) : ℂ := fourier q E 0 / E 0

end SICLean.L2b
