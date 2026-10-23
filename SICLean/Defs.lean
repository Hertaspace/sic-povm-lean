import SICLean.Statement

/-!
# Weyl–Heisenberg displacement operators and r-SICs

Conventions follow [AFK25, Def. 1.5]:
`X|j⟩ = |j+1⟩`, `Z|j⟩ = ω_d^j |j⟩` with `ω_d = exp(2πi/d)`, `ξ_d = -exp(πi/d)`, and
`D_p = ξ_d^{p₁p₂} X^{p₁} Z^{p₂}` for integer labels `p ∈ ℤ²`. With integer labels one has
`(D_p)ᴴ = D_{-p}` exactly, so no sign bookkeeping modulo `2d` is needed.

Nothing in this file is a hypothesis. The definitions enter the final theorem through
the input hypotheses in `SICLean.Inputs`.
-/

noncomputable section

open Matrix

namespace SICLean

/-- `ω_d = exp(2πi/d)`. -/
def omega (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

/-- `ξ_d = -exp(πi/d)` ([AFK25, Def. 1.5], called `τ` in much of the SIC literature). -/
def xi (d : ℕ) : ℂ := -Complex.exp (Real.pi * Complex.I / d)

/-- The displacement operator `D_p = ξ_d^{p₁p₂} X^{p₁} Z^{p₂}`, written entrywise:
`(D_p)_{i j} = ξ_d^{p₁p₂} ω_d^{p₂ j}` if `i ≡ j + p₁ (mod d)`, and `0` otherwise. -/
def D (d : ℕ) (p : ℤ × ℤ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    if (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
      xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((j : ℕ) : ℤ))
    else 0

/-- The overlaps `Tr(A D_pᴴ)` of a matrix `A` ([AFK25, Def. 1.9] when `A` is a fiducial). -/
def ov (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) : ℂ :=
  (A * (D d p)ᴴ).trace

/-- `p ∈ ℤ²` is the zero label modulo `d`. -/
def IsZeroLabel (d : ℕ) (p : ℤ × ℤ) : Prop :=
  (d : ℤ) ∣ p.1 ∧ (d : ℤ) ∣ p.2

instance (d : ℕ) : DecidablePred (IsZeroLabel d) :=
  fun p => inferInstanceAs (Decidable ((d : ℤ) ∣ p.1 ∧ (d : ℤ) ∣ p.2))

/-- The squared overlap modulus `r(d-r)/(d²-1)` of an r-SIC fiducial ([AFK25, Thm. 1.8]). -/
def rsicConst (d r : ℕ) : ℝ :=
  ((r : ℝ) * ((d : ℝ) - r)) / ((d : ℝ) ^ 2 - 1)

/-- [AFK25, Def. 1.2]: an r-SIC is a family of `d²` distinct rank-`r` Hermitian projectors
whose pairwise Hilbert–Schmidt inner products are all equal. -/
def IsRSIC (d r : ℕ) (P : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  Function.Injective P ∧
  (∀ j, (P j).IsHermitian ∧ P j * P j = P j ∧ (P j).rank = r) ∧
  ∃ α : ℂ, Pairwise fun j k => (P j * P k).trace = α

/-- There exists an r-SIC in dimension `d`. -/
def HasRSIC (d r : ℕ) : Prop :=
  ∃ P : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ, IsRSIC d r P

end SICLean
