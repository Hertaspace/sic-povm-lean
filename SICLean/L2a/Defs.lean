import SICLean.Main

/-!
# The M-torsion form of [RW26, §4.4]

`Index M` labels `(i ε + j)/M`, and contains no model of the larger group G.
Values descend modulo M; Weyl phases retain integer lifts.
-/

noncomputable section

open Matrix

namespace SICLean.L2a

/-- H = (ℤ/M)². The first coordinate multiplies ε. -/
abbrev Index (M : ℕ) := ZMod M × ZMod M

/-- The M² values F(i,j) = F_γ((i ε + j)/M). -/
abbrev Values (M : ℕ) := Index M → ℂ

/-- Evaluate a residue-indexed value at an integer lift. -/
def valueAt {M : ℕ} (F : Values M) (i j : ℤ) : ℂ := F (i, j)

/-- The attracting unit of α, not the unit ε³ of γ = α³. -/
def epsilon (M : ℕ) : ℝ :=
  ((M : ℝ) - 1 + Real.sqrt (((M : ℝ) - 1) ^ 2 - 4)) / 2

/-- Positive √ε, embedded in ℂ. -/
def sqrtEpsilon (M : ℕ) : ℂ := (Real.sqrt (epsilon M) : ℂ)

/-- The projector denominator √ε + ε^(-1/2). -/
def denominator (M : ℕ) : ℂ := sqrtEpsilon M + (sqrtEpsilon M)⁻¹

/-- The coefficient √(M-3) in the identity of [RW26]. -/
def convolutionScalar (M : ℕ) : ℂ := (Real.sqrt ((M : ℝ) - 3) : ℂ)

/-- e_M(n) = exp(2πin/M), with integer exponent. -/
def e (M : ℕ) (n : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (M : ℂ))

/-- The quadratic form in the H-Gaussian. -/
def quadraticForm (i j : ℤ) : ℤ := i ^ 2 - i * j + j ^ 2

/-- Explicit Gaussian on integer lifts of H. -/
def gaussianLift (M : ℕ) (i j : ℤ) : ℂ := e M (quadraticForm i j)

/-- The same Gaussian as a function on H, using least nonnegative representatives. -/
def gaussian (M : ℕ) (h : Index M) : ℂ :=
  gaussianLift M h.1.val h.2.val

/-- The restricted pairing ⟨h;k⟩. It is allowed to be degenerate on H. -/
def pairing (M : ℕ) (h k : Index M) : ℂ :=
  gaussian M (h + k) / (gaussian M h * gaussian M k)

/-- The Weyl phase on integer lifts, not on H. -/
def theta (M : ℕ) (i j : ℤ) : ℂ :=
  (-1 : ℂ) ^ (i + j + i * j) *
    Complex.exp (Real.pi * Complex.I * (quadraticForm i j : ℂ) / (M : ℂ))

/-- The phase before converting q^i p^j to a displacement. -/
def heisenbergPhase (M : ℕ) (i j : ℤ) : ℂ :=
  (-1 : ℂ) ^ (i + j) *
    Complex.exp (Real.pi * Complex.I * ((i ^ 2 + j ^ 2 : ℤ) : ℂ) / (M : ℂ))

/-- Labels (i,j) in [RW26] give the WH displacement label (-j,i). -/
def toWH (i j : ℤ) : ℤ × ℤ := (-j, i)

/-- Inverse change of integer labels: (a,b) gives (b,-a). -/
def fromWH (p : ℤ × ℤ) : ℤ × ℤ := (p.2, -p.1)

/-- q^i f(y) = e_M(iy) f(y), so q = Z. -/
def qPower (M : ℕ) (i : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
  fun a b => if a = b then omega M ^ (i * (b : ℤ)) else 0

/-- p^j f(y) = f(y+j), so p = X⁻¹. -/
def pPower (M : ℕ) (j : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
  fun a b => if (b : ZMod M) = (a : ZMod M) + (j : ZMod M) then 1 else 0

/-- The left side of the expanded identity, with exactly M² summands. -/
def convolution (M : ℕ) (F : Values M) (r s : ℤ) : ℂ :=
  (M : ℂ)⁻¹ * ∑ i : Fin M, ∑ j : Fin M,
    valueAt F i j * valueAt F (r - i) (s - j) * gaussianLift M i j *
      e M (-(i : ℤ) * r + (j : ℤ) * (r - s))

/-- The operator P of [RW26, Thm. 7], after converting q^i p^j to a displacement. -/
def P (M : ℕ) (F : Values M) : Matrix (Fin M) (Fin M) ℂ :=
  (M : ℂ)⁻¹ • ∑ i : Fin M, ∑ j : Fin M,
    (theta M i j * valueAt F i j) • D M (toWH i j)

/-- Π̃ = (√ε I - P)/(√ε + ε^(-1/2)). -/
def ghostProjector (M : ℕ) (F : Values M) : Matrix (Fin M) (Fin M) ℂ :=
  (denominator M)⁻¹ • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F)

/-- Nonzero Weyl coefficient, on integer lifts. It need not be periodic modulo M. -/
def coefficient (M : ℕ) (F : Values M) (i j : ℤ) : ℂ :=
  -(theta M i j * valueAt F i j) / denominator M

end SICLean.L2a
