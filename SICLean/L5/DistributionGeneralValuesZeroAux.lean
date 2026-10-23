import SICLean.L5.DistributionGeneralValuesAux

set_option autoImplicit false

/-!
# The removable zero branch in the Hermite distribution product

A chart chooses the literal zero representative of the zero quotient
class. Uniqueness of the Hermite grid then forces the two grid indices
and both Phi indices to vanish. The singleton orbit is evaluated with
the removable value at the origin.
-/

noncomputable section

open scoped Classical BigOperators MatrixGroups Topology
open SICLean.L3 SICLean.L4

namespace SICLean.L5.DistributionGeneralValuesAux

open DistributionOrbitGeometry DistributionHermite DistributionOrbitCocycle

universe u
variable {K : Type u} [Field K] [NumberField K]

namespace HermiteData.Chart

variable {P : PeriodData K} {I J : StablePseudolattice P}
    {D : HermiteData P I J} {hIJ : I.val ≤ J.val} {x : PseudolatticeGroup P J}

lemma zero_of_gridLift_mem (C : D.Chart hIJ x) (ij : D.Grid)
    (hmem : D.gridLift C.z ij ∈ I.val) :
    C.z = 0 ∧ ij.1.val = 0 ∧ ij.2.val = 0 := by
  have hzJ : C.z ∈ J.val := by
    have h := J.val.sub_mem (hIJ hmem) (D.gridLift_sub_mem C.z ij)
    simpa only [sub_sub_cancel] using h
  have hx : x = 0 := by
    apply toAmbient_injective P J
    rw [← C.represents, toAmbient_mk, map_zero]
    have h : ambientMk J.val C.z = ambientMk J.val 0 :=
      (ambientMk_eq_iff _ _ _).mpr (by simpa only [sub_zero] using hzJ)
    simpa only [map_zero] using h
  have hz : C.z = 0 := C.zero hx
  let origin : D.Grid := (⟨0, D.hn⟩, ⟨0, D.hm⟩)
  have hij : ij = origin := by
    apply D.gridFibre_injective hIJ x C.z C.mem C.represents
    apply Subtype.ext
    apply (ambientMk_eq_iff I.val _ _).mpr
    simpa [HermiteData.gridLift, hz, origin] using hmem
  exact ⟨hz, congrArg (fun t : D.Grid => t.1.val) hij,
    congrArg (fun t : D.Grid => t.2.val) hij⟩

lemma gridLift_eq_zero_of_mem (C : D.Chart hIJ x) (ij : D.Grid)
    (hmem : D.gridLift C.z ij ∈ I.val) : D.gridLift C.z ij = 0 := by
  obtain ⟨hz, hi, hj⟩ := C.zero_of_gridLift_mem ij hmem
  simp [HermiteData.gridLift, hz, hi, hj]

lemma sourceIndex_eq_zero (C : D.Chart hIJ x) (hz : C.z = 0) :
    C.sourceIndex = 0 := by
  simp [sourceIndex, hz, distributionIntegerCoordinates, distributionCoordinates]

lemma indices_eq_zero_of_gridLift_mem (C : D.Chart hIJ x) (ij : D.Grid)
    (hmem : D.gridLift C.z ij ∈ I.val) :
    hermiteNumIndex D.n C.sourceIndex ij.1.val = 0 ∧
      hermiteDenIndex D.BJ.matrix D.n ij.1.val ij.2.val = 0 := by
  obtain ⟨hz, hi, hj⟩ := C.zero_of_gridLift_mem ij hmem
  simp [hermiteNumIndex, hermiteDenIndex, C.sourceIndex_eq_zero hz, hi, hj]

lemma point_initial_eq_zero (C : D.Chart hIJ x) (o : Orbit P I J hIJ x)
    (ho : (orbitRepresentative P I J hIJ x o).val = 0) : C.point o 0 = 0 := by
  apply C.gridLift_eq_zero_of_mem (C.grid o 0)
  have h := C.point_initial o
  rw [ho] at h
  simpa only [point, sub_zero] using (ambientMk_eq_iff I.val (C.point o 0) 0).mp h

lemma grid_initial_eq_zero (C : D.Chart hIJ x) (o : Orbit P I J hIJ x)
    (ho : (orbitRepresentative P I J hIJ x o).val = 0) :
    (C.grid o 0).1.val = 0 ∧ (C.grid o 0).2.val = 0 := by
  have hmem : D.gridLift C.z (C.grid o 0) ∈ I.val := by
    change C.point o 0 ∈ I.val
    rw [C.point_initial_eq_zero o ho]
    exact I.val.zero_mem
  exact (C.zero_of_gridLift_mem (C.grid o 0) hmem).2

lemma sourceIndex_eq_zero_of_zero_orbit (C : D.Chart hIJ x)
    (o : Orbit P I J hIJ x)
    (ho : (orbitRepresentative P I J hIJ x o).val = 0) : C.sourceIndex = 0 := by
  apply C.sourceIndex_eq_zero
  exact C.zero ((zero_orbit P I J hIJ x).mp ⟨o, ho⟩)

lemma initial_indices_eq_zero (C : D.Chart hIJ x) (o : Orbit P I J hIJ x)
    (ho : (orbitRepresentative P I J hIJ x o).val = 0) :
    C.A o 0 = 0 ∧ C.B o 0 = 0 := by
  have hij := C.grid_initial_eq_zero o ho
  simp [A, B, hermiteNumIndex, hermiteDenIndex,
    C.sourceIndex_eq_zero_of_zero_orbit o ho, hij.1, hij.2]

lemma weighted_product_eq_value_zero (C : D.Chart hIJ x)
    (o : Orbit P I J hIJ x)
    (ho : (orbitRepresentative P I J hIJ x o).val = 0)
    (hz : C.point o 0 ∈ pseudolatticePeriodPoints
      (PeriodPower.powPeriod P (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o))
      (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o))) :
    (∏ j ∈ Finset.range (orbitLength P I J hIJ x o),
      etaMultiplier D.BI.matrix * modularPhi D.BI.matrix
        (C.A o j) (C.B o j) (C.argument o j) (D.BI.tau : ℂ)) =
      M72.value _ _ (pseudolatticeMk _ _ (C.point o 0) hz) := by
  have hr : orbitLength P I J hIJ x o = 1 := zero_orbit_length P I J hIJ x o ho
  have hp : C.point o 0 = 0 := C.point_initial_eq_zero o ho
  have hAB := C.initial_indices_eq_zero o ho
  have ha : C.argument o 0 = 0 := by simp [argument, hp]
  have hmk : pseudolatticeMk
      (PeriodPower.powPeriod P (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o))
      (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o)) (C.point o 0) hz = 0 := by
    apply (toAmbient_injective _ _)
    rw [toAmbient_mk, hp, map_zero, map_zero]
  rw [hmk, M72.value_zero]
  simp only [hr, Finset.prod_range_one, hAB.1, hAB.2, ha]
  rw [modularPhi_zero_fixedPoint_value D.BI.matrix D.BI.tau D.hBI.1.1
    D.hBI.1.2.1 D.hBI.1.2.2.1 (basis_etaDenom_pos D.BI D.hBI.1)]
  rw [← mul_assoc, mul_inv_cancel₀ (etaMultiplier_ne_zero _ D.hBI.1.1), one_mul]
  change (Real.sqrt (distributionPeriod D.BI) : ℂ) =
    (Real.sqrt (P.sigma₁ (P.epsilon ^ 1)) : ℂ)
  rw [pow_one, D.hBI.2.1]

end HermiteData.Chart

end SICLean.L5.DistributionGeneralValuesAux
