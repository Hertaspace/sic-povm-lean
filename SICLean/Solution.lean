import SICLean.L5.ActualProp7

/-!
# Solution of Open Quantum Problem 23

The twelve statements of `Challenge.lean` (Open Quantum Problem 23 in
google-deepmind/formal-conjectures),
with the same names and statements, proved from `SICLean.FinalAssembly.zaunerExistence`.
-/

namespace OpenQuantumProblem23

/-- Do SIC-POVMs exist in every finite dimension? Yes. -/
theorem sicPOVMs :
    ∀ d : ℕ, 1 ≤ d → HasSICPOVM d :=
  SICLean.FinalAssembly.zaunerExistence

/-- Existence of a SIC-POVM in dimension $56$. -/
theorem hasSICPOVM_56 : HasSICPOVM 56 := sicPOVMs 56 (by norm_num)

/-- Existence of a SIC-POVM in dimension $58$. -/
theorem hasSICPOVM_58 : HasSICPOVM 58 := sicPOVMs 58 (by norm_num)

/-- Existence of a SIC-POVM in dimension $59$. -/
theorem hasSICPOVM_59 : HasSICPOVM 59 := sicPOVMs 59 (by norm_num)

/-- Existence of a SIC-POVM in dimension $60$. -/
theorem hasSICPOVM_60 : HasSICPOVM 60 := sicPOVMs 60 (by norm_num)

/-- Existence of a SIC-POVM in dimension $64$. -/
theorem hasSICPOVM_64 : HasSICPOVM 64 := sicPOVMs 64 (by norm_num)

/-- Existence of a SIC-POVM in dimension $68$. -/
theorem hasSICPOVM_68 : HasSICPOVM 68 := sicPOVMs 68 (by norm_num)

/-- Existence of a SIC-POVM in dimension $69$. -/
theorem hasSICPOVM_69 : HasSICPOVM 69 := sicPOVMs 69 (by norm_num)

/-- Existence of a SIC-POVM in dimension $70$. -/
theorem hasSICPOVM_70 : HasSICPOVM 70 := sicPOVMs 70 (by norm_num)

/-- Existence of a SIC-POVM in dimension $71$. -/
theorem hasSICPOVM_71 : HasSICPOVM 71 := sicPOVMs 71 (by norm_num)

/-- Existence of a SIC-POVM in dimension $72$. -/
theorem hasSICPOVM_72 : HasSICPOVM 72 := sicPOVMs 72 (by norm_num)

/-- Existence of a SIC-POVM in dimension $75$. -/
theorem hasSICPOVM_75 : HasSICPOVM 75 := sicPOVMs 75 (by norm_num)

end OpenQuantumProblem23
