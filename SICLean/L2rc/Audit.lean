import SICLean.L2rc.Main

set_option autoImplicit false

/-!
# Signature checks for the rank-r form of [RW26, Thm. 2]
-/

#check @SICLean.L2rc.Generic.Theorem2Input
#check @SICLean.L2rc.Generic.isFiniteQuantumDilogarithm_of_theorem2
#check @SICLean.L2rc.Generic.l2c_theorem2Input
#check @SICLean.L2c.pentagon_of_transformed

#check @SICLean.L2rc.lattice_eq_row_range
#check @SICLean.L2rc.rwIndexEquiv
#check @SICLean.L2rc.gaussianLift_rwNumerator
#check @SICLean.L2rc.pairingLift_rwNumerator
#check @SICLean.L2rc.rowAlpha_rwNumerator
#check @SICLean.L2rc.concreteValues
#check @SICLean.L2rc.Theorem2Input
#check @SICLean.L2rc.RWAnalyticInput
#check @SICLean.L2rc.originPlus_eq_originValue
#check @SICLean.L2rc.concrete_theorem2Input
#check @SICLean.fqdInput_of_theorem2_rank
#check @SICLean.ghostGaloisInput_of_theorem2_rank
#check @SICLean.hasRSIC_of_theorem2

#print SICLean.L2rc.Generic.Theorem2Input
#print SICLean.L2rc.Theorem2Input
#print SICLean.L2rc.RWAnalyticInput
#print SICLean.fqdInput_of_theorem2_rank
#print SICLean.ghostGaloisInput_of_theorem2_rank
#print SICLean.hasRSIC_of_theorem2

#print axioms SICLean.L2rc.Generic.isFiniteQuantumDilogarithm_of_theorem2
#print axioms SICLean.fqdInput_of_theorem2_rank
#print axioms SICLean.hasRSIC_of_theorem2
