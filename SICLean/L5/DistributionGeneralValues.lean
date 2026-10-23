import SICLean.L5.PeriodPowerValues
import SICLean.L5.DistributionHermite
import SICLean.L5.DistributionOrbitGeometry
import SICLean.L5.DistributionOrbitCocycle
import SICLean.L5.DistributionGeneralValuesHermiteAux
import SICLean.L5.DistributionGeneralValuesAssemblyAux

set_option autoImplicit false

/-!
# Proposition 3(i): arbitrary-index distribution

The arbitrary-index distribution is [RW-rec, p. 4, Prop. 3(i), (10)], with
the argument in [RW-rec, Appendix A, pp. 18--20]. The values and multipliers
are those of [RW26, p. 2, (1)--(2)], [RW26, p. 6, (16)--(18)], and
[RW26, p. 14, Prop. 8]. [RW26, p. 14, Prop. 9] is the order-two product.

Every E and μ below is the analytic value or multiplier of the actual
lattice. The identities are theorems. Representatives live in K/I, while
the corresponding E is evaluated at its own positive orbit period.
-/

noncomputable section

open scoped Classical BigOperators MatrixGroups
open SICLean.L3

namespace SICLean.L5.DistributionGeneral

open DistributionOrbitGeometry

universe u
variable {K : Type u} [Field K] [NumberField K]

def distributionFactor (P : PeriodData K) (I J : StablePseudolattice P) : ℂ :=
  PeriodPower.multiplier P I ^ inclusionIndex I.val J.val / PeriodPower.multiplier P J

def orbitLabel (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) :
    PseudolatticeGroup
      (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
      (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o)) :=
  pseudolatticeMk _ _ (orbitLift P I J hIJ x o) (orbitLift_mem P I J hIJ x o)

def orbitValue (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) : ℂ :=
  M72.value
    (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
    (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
      (orbitLength_pos P I J hIJ x o)) (orbitLabel P I J hIJ x o)

def orbitProduct (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) : ℂ :=
  ∏ o : Orbit P I J hIJ x, orbitValue P I J hIJ x o

/-- [RW-rec, Appendix A, p. 18]. [RW26, p. 2, (2)] is the matrix convention.
Simultaneous existence of the two bases. -/
theorem hermite_presentations (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) :
    ∃ (BI BJ : L4.DistributionBasis) (n m : ℕ) (k : ℤ),
      PseudolatticePresentation P I BI ∧ PseudolatticePresentation P J BJ ∧
      0 < n ∧ 0 < m ∧
      BI.tau = ((n : ℝ) * BJ.tau + (k : ℝ)) / (m : ℝ) ∧
      BI.scale = (m : ℝ) * BJ.scale ∧ BI.scaleConj = (m : ℝ) * BJ.scaleConj ∧
      (BI.matrix : Matrix (Fin 2) (Fin 2) ℤ) * !![(n : ℤ), k; 0, (m : ℤ)] =
        !![(n : ℤ), k; 0, (m : ℤ)] * (BJ.matrix : Matrix (Fin 2) (Fin 2) ℤ) ∧
      inclusionIndex I.val J.val = n * m := by
  exact DistributionGeneralValuesAux.hermite_presentations_aux P I J hIJ

/-- [RW-rec, p. 4, Prop. 3(i)]; [RW26, p. 3].
The phase remains explicit until normalization. -/
theorem distributionFactor_ne_zero (P : PeriodData K) (I J : StablePseudolattice P) :
    distributionFactor P I J ≠ 0 := by
  exact div_ne_zero
    (pow_ne_zero _ (L4.etaMultiplier_ne_zero _ (M72.chosenBasis_spec P I).1.1))
    (L4.etaMultiplier_ne_zero _ (M72.chosenBasis_spec P J).1.1)

/-- Integer powers and quotients of the eta multipliers are 24th roots of unity.
[RW-rec, p. 4, Prop. 3(i)]; [RW26, p. 3]. -/
theorem distributionFactor_pow_twentyFour (P : PeriodData K)
    (I J : StablePseudolattice P) : distributionFactor P I J ^ 24 = 1 := by
  rw [distributionFactor, div_pow, ← pow_mul, mul_comm _ 24, pow_mul]
  simp only [PeriodPower.multiplier,
    L4.etaMultiplier_pow_twentyFour _ (M72.chosenBasis_spec P I).1.1,
    L4.etaMultiplier_pow_twentyFour _ (M72.chosenBasis_spec P J).1.1,
    one_pow, div_one]

/-- [RW-rec, Appendix A, pp. 19--20]; [RW26, p. 6, (16)]; [RW26, p. 14, Prop. 8].
Any field representative of any point of the same ε-orbit gives the same E. -/
theorem orbitValue_representative (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) (z : K)
    (hz : z ∈ pseudolatticePeriodPoints
      (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
      (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o)))
    (ho : ∃ a : ℤ, ((ambientUnit P I).toEquiv ^ a) (ambientMk I.val z) =
      (orbitRepresentative P I J hIJ x o).val) :
    M72.value _ _ (pseudolatticeMk _ _ z hz) = orbitValue P I J hIJ x o := by
  let r := orbitLength P I J hIJ x o
  have hr : 0 < r := orbitLength_pos P I J hIJ x o
  let Q := PeriodPower.powPeriod P r hr
  let L := PeriodPower.powLattice P I r hr
  let e : Equiv.Perm (PseudolatticeGroup Q L) :=
    (PeriodPower.epsilonAction P I r hr).toEquiv
  let f : Equiv.Perm (AmbientGroup I.val) := (ambientUnit P I).toEquiv
  let t : PseudolatticeGroup Q L → AmbientGroup I.val := toAmbient Q L
  let E : PseudolatticeGroup Q L → ℂ := M72.value Q L
  have ht (g : PseudolatticeGroup Q L) : t (e g) = f (t g) := by
    induction g using Quotient.inductionOn with
    | h y =>
      change toAmbient Q L
        (PeriodPower.epsilonAction P I r hr (pseudolatticeMk Q L y.val y.property)) = _
      rw [PeriodPower.epsilonAction_mk, toAmbient_mk]
      change ambientMk I.val (P.epsilon * y.val) =
        ambientUnit P I (toAmbient Q L (pseudolatticeMk Q L y.val y.property))
      rw [toAmbient_mk]
      rfl
  have hti (g : PseudolatticeGroup Q L) : t (e⁻¹ g) = f⁻¹ (t g) := by
    apply f.injective
    simpa using (ht (e⁻¹ g)).symm
  have htZ (a : ℤ) : ∀ g, t ((e ^ a) g) = (f ^ a) (t g) := by
    induction a using Int.induction_on with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      simp only [zpow_add_one, Equiv.Perm.mul_apply]
      rw [ih, ht]
    | pred n ih =>
      intro g
      simp only [zpow_sub_one, Equiv.Perm.mul_apply]
      rw [ih, hti]
  have hE (g : PseudolatticeGroup Q L) : E (e g) = E g :=
    PeriodPower.value_epsilon_invariant P I r hr g
  have hEi (g : PseudolatticeGroup Q L) : E (e⁻¹ g) = E g := by
    simpa using (hE (e⁻¹ g)).symm
  have hEZ (a : ℤ) : ∀ g, E ((e ^ a) g) = E g := by
    induction a using Int.induction_on with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      simp only [zpow_add_one, Equiv.Perm.mul_apply]
      rw [ih, hE]
    | pred n ih =>
      intro g
      simp only [zpow_sub_one, Equiv.Perm.mul_apply]
      rw [ih, hEi]
  obtain ⟨a, ha⟩ := ho
  have hlabel : (e ^ a) (pseudolatticeMk Q L z hz) = orbitLabel P I J hIJ x o := by
    apply toAmbient_injective Q L
    change t ((e ^ a) (pseudolatticeMk Q L z hz)) = t (orbitLabel P I J hIJ x o)
    rw [htZ]
    change (f ^ a) (toAmbient Q L (pseudolatticeMk Q L z hz)) = _
    rw [toAmbient_mk]
    have hlift : toAmbient Q L (orbitLabel P I J hIJ x o) =
        (orbitRepresentative P I J hIJ x o).val := by
      rw [orbitLabel, toAmbient_mk]
      exact Quotient.out_eq _
    exact ha.trans hlift.symm
  exact (hEZ a (pseudolatticeMk Q L z hz)).symm.trans (congrArg E hlabel)

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6].
Includes the separate positive-root zero orbit. -/
theorem orbitValue_ne_zero (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) : orbitValue P I J hIJ x o ≠ 0 := by
  exact M72.value_ne_zero _ _ _

/-- [RW-rec, Appendix A, p. 19]: the zero orbit contributes the positive
square root of ε, with length one. -/
theorem orbitValue_zero (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) (ho : (orbitRepresentative P I J hIJ x o).val = 0) :
    orbitValue P I J hIJ x o = (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) := by
  have hlabel : orbitLabel P I J hIJ x o = 0 := by
    apply toAmbient_injective
      (PeriodPower.powPeriod P _ (orbitLength_pos P I J hIJ x o))
      (PeriodPower.powLattice P I _ (orbitLength_pos P I J hIJ x o))
    rw [map_zero, orbitLabel, toAmbient_mk]
    exact (Quotient.out_eq (orbitRepresentative P I J hIJ x o).val).trans ho
  rw [orbitValue, hlabel, M72.value_zero]
  change (Real.sqrt (P.sigma₁ (P.epsilon ^ orbitLength P I J hIJ x o)) : ℂ) = _
  rw [zero_orbit_length P I J hIJ x o ho, pow_one]

/-- [RW-rec, p. 4, Prop. 3(i), (10)]; proof in [RW-rec, Appendix A, pp. 18--20]. -/
theorem distribution_general (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    distributionFactor P I J * M72.value P J x = orbitProduct P I J hIJ x := by
  obtain ⟨BI, BJ, n, m, k, hBI, hBJ, hn, hm, htau, hs, hsc, hmat, hind⟩ :=
    hermite_presentations P I J hIJ
  let D : DistributionGeneralValuesAux.HermiteData P I J :=
    { BI := BI, BJ := BJ, hBI := hBI, hBJ := hBJ
      bI := DistributionGeneralValuesAux.fieldBasis P I BI hBI
      bJ := DistributionGeneralValuesAux.fieldBasis P J BJ hBJ
      n := n, m := m, k := k, hn := hn, hm := hm
      tau := htau, scale := hs, conjugateScale := hsc, matrix := hmat, index := hind }
  let C := D.chart hIJ x
  have hgeneral : L4.etaMultiplier D.BI.matrix ^ inclusionIndex I.val J.val *
        M72.value P J x = L4.etaMultiplier D.BJ.matrix * orbitProduct P I J hIJ x := by
    rw [C.weighted_grid_product, C.grid_product_eq_orbit_product, orbitProduct]
    apply congrArg (L4.etaMultiplier D.BJ.matrix * ·)
    apply Finset.prod_congr rfl
    intro o _
    exact orbitValue_representative P I J hIJ x o (C.point o 0) (C.point_mem o)
      ⟨0, by simpa using C.point_initial o⟩
  have hmuI := PeriodPower.multiplier_presentation P I D.BI D.hBI
  have hmuJ := PeriodPower.multiplier_presentation P J D.BJ D.hBJ
  rw [distributionFactor, hmuI, hmuJ, div_mul_eq_mul_div]
  exact (div_eq_iff (L4.etaMultiplier_ne_zero D.BJ.matrix D.hBJ.1.1)).mpr
    (by simpa only [mul_comm] using hgeneral)

/-- [RW-rec, p. 20, (10)], in cross-multiplied form. -/
theorem distribution_general_cross_mul (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    PeriodPower.multiplier P I ^ inclusionIndex I.val J.val * M72.value P J x =
      PeriodPower.multiplier P J * orbitProduct P I J hIJ x := by
  have hmu : PeriodPower.multiplier P J ≠ 0 :=
    L4.etaMultiplier_ne_zero _ (M72.chosenBasis_spec P J).1.1
  calc
    _ = PeriodPower.multiplier P J *
        (distributionFactor P I J * M72.value P J x) := by
      dsimp only [distributionFactor]
      field_simp
    _ = _ := congrArg (PeriodPower.multiplier P J * ·)
      (distribution_general P I J hIJ x)

/-- [RW-rec, Appendix A, pp. 19--20, (10)]: the origin is included. -/
theorem distribution_general_zero (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) :
    orbitProduct P I J hIJ 0 = distributionFactor P I J *
      (Real.sqrt (P.sigma₁ P.epsilon) : ℂ) := by
  simpa only [M72.value_zero] using (distribution_general P I J hIJ 0).symm

/-- [RW-rec, p. 3, Def. 1]; [RW-rec, p. 4, Prop. 3(i)]; [RW26, p. 2, (2)].
The identity for an arbitrary admissible matrix presentation of J,
at the same lattice and the same field. -/
theorem distribution_general_presentation (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (BJ : L4.DistributionBasis)
    (hBJ : PseudolatticePresentation P J BJ) (z : K)
    (hz : z ∈ pseudolatticePeriodPoints P J) :
    distributionFactor P I J * M72.basisValue P BJ z =
      orbitProduct P I J hIJ (pseudolatticeMk P J z hz) := by
  simpa only [M72.value_mk P J BJ hBJ z hz] using
    distribution_general P I J hIJ (pseudolatticeMk P J z hz)

#print distributionFactor
#print orbitLabel
#print orbitValue
#print orbitProduct
#check @M72.value_mk
#check distribution_general

end SICLean.L5.DistributionGeneral
