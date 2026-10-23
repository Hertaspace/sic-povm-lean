/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# Challenge for `lake comparator`

The statements of Open Quantum Problem 23 from google-deepmind/formal-conjectures,
`FormalConjectures/OpenQuantumProblems/23.lean` at commit
90d18f666eb98adec4eee4d12f1d37e30b4eb204 (full file in `vendor/`). The definitions are copied
verbatim, and the twelve open theorems keep their names, statements and `sorry` proofs. The
`module` and `public` wrapper, the attributes (which come from `FormalConjecturesUtil`) and the
other declarations of that file are omitted, and `import Mathlib` replaces its imports. The
proofs are in `SICLean/Solution.lean`; see `comparator.json`.
-/

noncomputable section

namespace OpenQuantumProblem23

/-- A state vector in the $d$-dimensional complex Hilbert space $\mathbb{C}^d$. -/
abbrev StateVector (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Build a state vector from its coordinates in the computational basis. -/
abbrev mkStateVector {d : ℕ} (ψ : Fin d → ℂ) : StateVector d := WithLp.toLp 2 ψ

/-- Coercion from a state vector to its coordinate function. -/
instance {d : ℕ} : CoeFun (StateVector d) (fun _ => Fin d → ℂ) where
  coe ψ := ψ.ofLp

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {d : ℕ} (ψ : StateVector d) : Prop := ‖ψ‖ = 1

/-- The squared magnitude of the overlap between two state vectors. -/
def overlapSq {d : ℕ} (φ ψ : StateVector d) : ℝ :=
  Complex.normSq (∑ i : Fin d, star (φ i) * ψ i)

/-- A family has constant pairwise squared overlap $c$ if every two distinct members have squared overlap $c$. -/
def HasConstantOverlapSq {d N : ℕ} (c : ℝ) (Φ : Fin N → StateVector d) : Prop :=
  Pairwise fun i j => overlapSq (Φ i) (Φ j) = c

/-- The squared overlap value of a SIC family in dimension $d$. -/
def sicOverlapSq (d : ℕ) : ℝ := (d + 1 : ℝ)⁻¹

/-- A SIC family in dimension $d$ consists of $d^2$ normalized vectors in $\mathbb{C}^d$ with pairwise squared overlap $(d + 1)^{-1}$. -/
def IsSICFamily (d : ℕ) (Φ : Fin (d ^ 2) → StateVector d) : Prop :=
  (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq (sicOverlapSq d) Φ

/-- There exists a SIC-POVM in dimension $d$. -/
def HasSICPOVM (d : ℕ) : Prop :=
  ∃ Φ : Fin (d ^ 2) → StateVector d, IsSICFamily d Φ

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $56$. -/
theorem hasSICPOVM_56 : HasSICPOVM 56 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $58$. -/
theorem hasSICPOVM_58 : HasSICPOVM 58 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $59$. -/
theorem hasSICPOVM_59 : HasSICPOVM 59 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $60$. -/
theorem hasSICPOVM_60 : HasSICPOVM 60 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $64$. -/
theorem hasSICPOVM_64 : HasSICPOVM 64 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $68$. -/
theorem hasSICPOVM_68 : HasSICPOVM 68 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $69$. -/
theorem hasSICPOVM_69 : HasSICPOVM 69 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $70$. -/
theorem hasSICPOVM_70 : HasSICPOVM 70 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $71$. -/
theorem hasSICPOVM_71 : HasSICPOVM 71 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $72$. -/
theorem hasSICPOVM_72 : HasSICPOVM 72 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $75$. -/
theorem hasSICPOVM_75 : HasSICPOVM 75 := by sorry

/-- Do SIC-POVMs exist in every finite dimension? -/
theorem sicPOVMs :
    ∀ d : ℕ, 1 ≤ d → HasSICPOVM d := by
  sorry

end OpenQuantumProblem23
