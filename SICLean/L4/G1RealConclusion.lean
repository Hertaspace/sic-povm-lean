import SICLean.L4.G1RealSingleRemovable
import SICLean.L4.G1RealRatioRemovable

set_option autoImplicit false

/-!
# Assembly of the G1 real endpoint statement

This file adds no analytic lemma or definition. The statement uses the contract's M,τ,hM,hT, splits
the two clauses, and applies the two named contract_clause exports below with the arguments in their
displayed order. The ratio export already uses contract_chain_clauses for existence and arbitrary
representatives.

[RW26, p. 7, (22), (23), p. 29]. No G2 theorem is used.
-/

noncomputable section
open scoped MatrixGroups

namespace SICLean.L4

/-- Final assembly only: the original contract, including fixed-τ NeBot, limUnder limits, every bent
δ,ψ and every original separating chain. [RW26, p. 7, (22), (23)]. -/
theorem g1RealConclusion : G1RealConclusion := by
  intro M τ hM hT
  constructor
  · intro n h ell w δ ψ hs hδ hψ hψ'
    exact G1RealSingleRemovable.single_contract_clause M hM τ w δ ψ n h ell
      hT hs hδ hψ hψ'
  · intro n h ell p w y hs hL hpinch
    exact G1RealRatioRemovable.ratio_contract_clause M hM τ w y n h ell p
      hT hs hL hpinch

#check @G1RealSingleRemovable.single_contract_clause
#check @G1RealRatioRemovable.ratio_contract_clause
#check @G1ChainTransfer.contract_chain_clauses
#check @g1RealConclusion
#print G1RealConclusion

end SICLean.L4
