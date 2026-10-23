import SICLean.L5.DistributionGeneralValuesZeroAux

set_option autoImplicit false

/-!
Assembly of the Hermite point identity and its inverse-epsilon orbit
products. Continuity at a grid point uses either divisor avoidance or
the unshifted removable origin, with those alternatives kept separate.
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

def gridPhi (C : D.Chart hIJ x) (ij : D.Grid) : ℂ :=
  modularPhi D.BI.matrix
    (hermiteNumIndex D.n C.sourceIndex ij.1.val)
    (hermiteDenIndex D.BJ.matrix D.n ij.1.val ij.2.val)
    ((P.sigma₁ (D.gridLift C.z ij) / D.BI.scale : ℝ) : ℂ) (D.BI.tau : ℂ)

def gridFactor (C : D.Chart hIJ x) (ij : D.Grid) : ℂ :=
  etaMultiplier D.BI.matrix * C.gridPhi ij

lemma source_continuous (C : D.Chart hIJ x) :
    ContinuousAt (fun w : ℂ => modularPhi D.BJ.matrix C.sourceIndex 0 w (D.BJ.tau : ℂ))
      ((P.sigma₁ C.z / D.BJ.scale : ℝ) : ℂ) := by
  apply fixedPoint_phi_continuous D.BJ D.hBJ.1
  by_cases hzJ : C.z ∈ J.val
  · have hx : x = 0 := by
      apply toAmbient_injective P J
      rw [← C.represents, toAmbient_mk, map_zero]
      simpa only [map_zero] using
        (ambientMk_eq_iff J.val C.z 0).mpr (by simpa only [sub_zero] using hzJ)
    have hz : C.z = 0 := C.zero hx
    exact Or.inr ⟨by simp [hz], C.sourceIndex_eq_zero hz, rfl⟩
  · exact Or.inl (fun hm => hzJ ((D.bJ.normalized_mem_iff D.hBJ C.z).mp hm))

lemma grid_continuous (C : D.Chart hIJ x) (ij : D.Grid) :
    ContinuousAt (fun w : ℂ => modularPhi D.BI.matrix
      (hermiteNumIndex D.n C.sourceIndex ij.1.val)
      (hermiteDenIndex D.BJ.matrix D.n ij.1.val ij.2.val)
      (hermiteArgument D.m ij.1.val ij.2.val w (D.BJ.tau : ℂ)) (D.BI.tau : ℂ))
      ((P.sigma₁ C.z / D.BJ.scale : ℝ) : ℂ) := by
  have hc : ContinuousAt (fun w : ℂ => modularPhi D.BI.matrix
      (hermiteNumIndex D.n C.sourceIndex ij.1.val)
      (hermiteDenIndex D.BJ.matrix D.n ij.1.val ij.2.val) w (D.BI.tau : ℂ))
      ((P.sigma₁ (D.gridLift C.z ij) / D.BI.scale : ℝ) : ℂ) := by
    apply fixedPoint_phi_continuous D.BI D.hBI.1
    by_cases hzI : D.gridLift C.z ij ∈ I.val
    · exact Or.inr ⟨by simp [C.gridLift_eq_zero_of_mem ij hzI],
        (C.indices_eq_zero_of_gridLift_mem ij hzI).1,
        (C.indices_eq_zero_of_gridLift_mem ij hzI).2⟩
    · exact Or.inl (fun hm => hzI
        ((D.bI.normalized_mem_iff D.hBI (D.gridLift C.z ij)).mp hm))
  rw [D.gridLift_argument] at hc
  exact hc.comp (f := fun w : ℂ =>
    hermiteArgument D.m ij.1.val ij.2.val w (D.BJ.tau : ℂ)) (show ContinuousAt
    (fun w : ℂ => hermiteArgument D.m ij.1.val ij.2.val w (D.BJ.tau : ℂ))
    ((P.sigma₁ C.z / D.BJ.scale : ℝ) : ℂ) by unfold hermiteArgument; fun_prop)

lemma hermite_value (C : D.Chart hIJ x) :
    modularPhi D.BJ.matrix C.sourceIndex 0
      ((P.sigma₁ C.z / D.BJ.scale : ℝ) : ℂ) (D.BJ.tau : ℂ) =
      ∏ ij : D.Grid, C.gridPhi ij := by
  have hh := hermitePhi_value_of_continuous D.BI.matrix D.BJ.matrix D.n D.m D.k
    C.sourceIndex ((P.sigma₁ C.z / D.BJ.scale : ℝ) : ℂ) (D.BJ.tau : ℂ)
    D.hn D.hm D.hBI.1.1 D.hBJ.1.1 D.matrix
    (show (D.BJ.tau : ℂ) ∈ modularPhiDomain D.BJ.matrix from
      Or.inl (basis_etaDenom_pos D.BJ D.hBJ.1)) C.source_continuous (by
        intro i hi j hj
        simpa only [← D.tau_complex] using C.grid_continuous (⟨i, Finset.mem_range.mp hi⟩,
          ⟨j, Finset.mem_range.mp hj⟩))
  refine hh.trans ?_
  simp only [hermiteProduct, Fintype.prod_prod_type, gridPhi, D.gridLift_argument,
    D.tau_complex]
  let f : ℕ → ℕ → ℂ := fun i j => modularPhi D.BI.matrix
    (hermiteNumIndex D.n C.sourceIndex i) (hermiteDenIndex D.BJ.matrix D.n i j)
    (hermiteArgument D.m i j ((P.sigma₁ C.z / D.BJ.scale : ℝ) : ℂ) (D.BJ.tau : ℂ))
    (hermiteTau D.n D.m D.k (D.BJ.tau : ℂ))
  change (∏ i ∈ Finset.range D.n, ∏ j ∈ Finset.range D.m, f i j) =
    ∏ i : Fin D.n, ∏ j : Fin D.m, f i.val j.val
  have hi (i : Fin D.n) : (∏ j : Fin D.m, f i.val j.val) =
      ∏ j ∈ Finset.range D.m, f i.val j :=
    Fin.prod_univ_eq_prod_range (f i.val) D.m
  simp_rw [hi]
  exact (Fin.prod_univ_eq_prod_range
    (fun i => ∏ j ∈ Finset.range D.m, f i j) D.n).symm


lemma weighted_grid_product (C : D.Chart hIJ x) :
    etaMultiplier D.BI.matrix ^ inclusionIndex I.val J.val * M72.value P J x =
      etaMultiplier D.BJ.matrix * ∏ ij : D.Grid, C.gridFactor ij := by
  rw [C.source_value, C.hermite_value]
  simp only [gridFactor, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, D.index]
  ring

lemma weighted_orbit_product (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) :
    (∏ j ∈ Finset.range (orbitLength P I J hIJ x o),
      etaMultiplier D.BI.matrix * modularPhi D.BI.matrix (C.A o j) (C.B o j)
        (C.argument o j) (D.BI.tau : ℂ)) =
      M72.value
        (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
        (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
          (orbitLength_pos P I J hIJ x o))
        (pseudolatticeMk _ _ (C.point o 0) (C.point_mem o)) := by
  by_cases ho : (orbitRepresentative P I J hIJ x o).val = 0
  · exact C.weighted_product_eq_value_zero o ho (C.point_mem o)
  · apply C.weighted_product_off_lattice o
    intro hm
    apply ho
    apply (C.point_initial o).symm.trans
    simpa only [map_zero] using
      (ambientMk_eq_iff I.val (C.point o 0) 0).mpr (by simpa only [sub_zero] using hm)

lemma grid_product_eq_orbit_product (C : D.Chart hIJ x) :
    (∏ ij : D.Grid, C.gridFactor ij) =
      ∏ o : Orbit P I J hIJ x,
        M72.value
          (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
          (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
            (orbitLength_pos P I J hIJ x o))
          (pseudolatticeMk _ _ (C.point o 0) (C.point_mem o)) := by
  let F : Fibre P I J hIJ x → ℂ := fun a => C.gridFactor (C.equiv.symm a)
  calc
    _ = ∏ a : Fibre P I J hIJ x, F a := by
      simpa only [F, Equiv.symm_apply_apply] using C.equiv.prod_comp F
    _ = ∏ o : Orbit P I J hIJ x, ∏ j ∈ Finset.range (orbitLength P I J hIJ x o),
        etaMultiplier D.BI.matrix * modularPhi D.BI.matrix (C.A o j) (C.B o j)
          (C.argument o j) (D.BI.tau : ℂ) := by
      rw [prod_fibre_eq_prod_inverse_range P I J hIJ x F]
      rfl
    _ = _ := Finset.prod_congr rfl (fun o _ => C.weighted_orbit_product o)

end HermiteData.Chart

end SICLean.L5.DistributionGeneralValuesAux
