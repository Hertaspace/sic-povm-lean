import SICLean.L5.PeriodPowerValues
import SICLean.L5.DistributionHermite
import SICLean.L5.DistributionOrbitGeometry
import SICLean.L5.DistributionOrbitCocycle
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

/-!
Auxiliary assembly of actual arbitrary-index distribution. The Hermite
points are ordered by the inverse unit. The origin uses the unshifted
removable value and never uses off-lattice factor cancellation.
-/

noncomputable section

open scoped Classical BigOperators MatrixGroups Topology
open SICLean.L3 SICLean.L4

namespace SICLean.L5.DistributionGeneralValuesAux

open DistributionOrbitGeometry DistributionHermite DistributionOrbitCocycle

universe u
variable {K : Type u} [Field K] [NumberField K]

theorem fixedPoint_phi_continuous (B : DistributionBasis) (hB : B.Valid)
    (A C : ℤ) (z : ℂ)
    (hz : z ∉ modularPhiPseudoLattice (B.tau : ℂ) ∨ (z = 0 ∧ A = 0 ∧ C = 0)) :
    ContinuousAt (fun w : ℂ => modularPhi B.matrix A C w (B.tau : ℂ)) z := by
  rcases hz with hz | ⟨rfl, rfl, rfl⟩
  · exact (DistributionBasisValuesAux.nonlattice_continuous_ne_zero B.matrix hB.1
      A C B.tau (dBasis_period_pos B hB) z hz).1
  · have hT : 0 < (etaDenom B.matrix (B.tau : ℂ)).re := by
      simpa [etaDenom, distributionPeriod] using dBasis_period_pos B hB
    have hvalue := DistributionOrbitCocycle.modularPhi_zero_fixedPoint_value
      B.matrix B.tau hB.1 hB.2.1 hB.2.2.1 hT
    have hcont : ContinuousAt
        (fun w : ℂ × ℂ => modularPhi B.matrix 0 0 w.1 w.2) (0, (B.tau : ℂ)) := by
      simpa only [ContinuousAt, hvalue] using
        DistributionOrbitCocycle.modularPhi_zero_fixedPoint_tendsto
          B.matrix B.tau hB.1 hB.2.1 hB.2.2.1 hT
    exact hcont.comp (f := fun w : ℂ => (w, (B.tau : ℂ)))
      (continuousAt_id.prodMk continuousAt_const)

theorem hermitePhi_value_of_continuous
    (MI MJ : SL(2, ℤ)) (n m : ℕ) (k u : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (hI : 0 < MI 1 0) (hJ : 0 < MJ 1 0)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * DistributionHermite.hermiteMatrix n m k =
      DistributionHermite.hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ))
    (hτ : τ ∈ modularPhiDomain MJ)
    (hcontJ : ContinuousAt (fun w : ℂ => modularPhi MJ u 0 w τ) z)
    (hcontI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range m,
      ContinuousAt (fun w : ℂ => modularPhi MI
        (DistributionHermite.hermiteNumIndex n u i)
        (DistributionHermite.hermiteDenIndex MJ n i j)
        (DistributionHermite.hermiteArgument m i j w τ)
        (DistributionHermite.hermiteTau n m k τ)) z) :
    modularPhi MJ u 0 z τ = DistributionHermite.hermiteProduct MI MJ n m k u z τ := by
  apply ModularCocycleAux.eq_of_germ hcontJ
    (show ContinuousAt (fun w => DistributionHermite.hermiteProduct MI MJ n m k u w τ) z from
      tendsto_finsetProd _ fun i hi => tendsto_finsetProd _ fun j hj => hcontI i hi j hj)
  exact DistributionHermite.hermitePhi_germ MI MJ n m k u z τ hn hm hI hJ hH hτ


structure FieldBasis (P : PeriodData K) (I : StablePseudolattice P)
    (B : DistributionBasis) where
  one : K
  two : K
  one_mem : one ∈ I.val
  two_mem : two ∈ I.val
  one_embedding : pseudolatticeEmbedding P one = distributionBetaOne B
  two_embedding : pseudolatticeEmbedding P two = distributionBetaTwo B

def fieldBasis (P : PeriodData K) (I : StablePseudolattice P)
    (B : DistributionBasis) (hB : PseudolatticePresentation P I B) : FieldBasis P I B :=
  Classical.choice <| by
    have h₁ := dBasis_betaOne_mem B
    have h₂ := dBasis_betaTwo_mem B
    rw [hB.2.2] at h₁ h₂
    obtain ⟨a, ha, hea⟩ := h₁
    obtain ⟨b, hb, heb⟩ := h₂
    exact ⟨⟨a, b, ha, hb, hea, heb⟩⟩

namespace FieldBasis

variable {P : PeriodData K} {I : StablePseudolattice P} {B : DistributionBasis}

lemma one_sigma (b : FieldBasis P I B) : P.sigma₁ b.one = B.scale * B.tau :=
  congrArg Prod.fst b.one_embedding

lemma two_sigma (b : FieldBasis P I B) : P.sigma₁ b.two = B.scale :=
  congrArg Prod.fst b.two_embedding

lemma mem_iff (b : FieldBasis P I B) (hB : PseudolatticePresentation P I B) (z : K) :
    z ∈ I.val ↔ ∃ a c : ℤ, z = (a : K) * b.one + (c : K) * b.two := by
  constructor
  · intro hz
    have he : pseudolatticeEmbedding P z ∈ distributionLattice B := by
      rw [hB.2.2]
      exact ⟨z, hz, rfl⟩
    obtain ⟨v, hv⟩ := (distributionLattice_mem_iff B _).mp he
    refine ⟨v 0, v 1, ?_⟩
    apply pseudolatticeEmbedding_injective P
    simpa [map_add, map_mul, ← zsmul_eq_mul, b.one_embedding, b.two_embedding] using hv
  · rintro ⟨a, c, rfl⟩
    exact I.val.add_mem (by simpa [← zsmul_eq_mul] using I.val.smul_mem a b.one_mem)
      (by simpa [← zsmul_eq_mul] using I.val.smul_mem c b.two_mem)

lemma coefficients_unique (b : FieldBasis P I B) (hB : PseudolatticePresentation P I B)
    (a c a' c' : ℤ)
    (he : (a : K) * b.one + (c : K) * b.two =
      (a' : K) * b.one + (c' : K) * b.two) : a = a' ∧ c = c' := by
  have h := congrArg P.sigma₁ he
  simp only [map_add, map_mul, map_intCast, b.one_sigma, b.two_sigma] at h
  have hs : B.scale ≠ 0 := hB.1.2.2.2.2.1.ne'
  apply dl_int_coeff_eq (distributionBasis_spectral B hB.1).1 a c a' c'
  apply mul_left_cancel₀ hs
  simpa only [mul_add, mul_assoc, mul_left_comm, mul_comm] using h

lemma normalized_mem_iff (b : FieldBasis P I B) (hB : PseudolatticePresentation P I B)
    (z : K) : ((P.sigma₁ z / B.scale : ℝ) : ℂ) ∈ modularPhiPseudoLattice (B.tau : ℂ) ↔
      z ∈ I.val := by
  have hs : B.scale ≠ 0 := hB.1.2.2.2.2.1.ne'
  constructor
  · rintro ⟨a, c, hac⟩
    apply (b.mem_iff hB z).mpr
    refine ⟨a, c, P.sigma₁.injective ?_⟩
    have hr := congrArg Complex.re hac
    simp only [map_add, map_mul, map_intCast, b.one_sigma, b.two_sigma]
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
      Complex.intCast_im, Complex.ofReal_im, mul_zero, sub_zero] at hr
    have hm := (div_eq_iff hs).mp hr
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hm
  · rintro hz
    obtain ⟨a, c, rfl⟩ := (b.mem_iff hB z).mp hz
    refine ⟨a, c, ?_⟩
    have hr : P.sigma₁ ((a : K) * b.one + (c : K) * b.two) / B.scale =
        (a : ℝ) * B.tau + (c : ℝ) := by
      simp only [map_add, map_mul, map_intCast, b.one_sigma, b.two_sigma]
      field_simp
      <;> ring
    exact_mod_cast hr


lemma difference_expansion (b : FieldBasis P I B)
    (hB : PseudolatticePresentation P I B) (z : K)
    (hz : z ∈ pseudolatticePeriodPoints P I) :
    P.epsilon⁻¹ * z - z =
      (distributionIntegerCoordinates B
        (distributionPeriodDifference B (pseudolatticeEmbedding P z)) 0 : K) * b.one +
      (distributionIntegerCoordinates B
        (distributionPeriodDifference B (pseudolatticeEmbedding P z)) 1 : K) * b.two := by
  apply P.sigma₁.injective
  have h := congrArg Prod.fst
    (distributionPeriodPoints_expansion B hB.1 (pseudolatticeEmbedding P z)
      (pseudolatticePresentation_point_mem P I B hB z hz))
  simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_intCast, distributionBetaOne, distributionBetaTwo,
    zsmul_eq_mul] at h
  change ((distributionPeriod B)⁻¹ - 1) * P.sigma₁ z = _ at h
  simp only [map_sub, map_add, map_mul, map_inv₀, map_intCast, b.one_sigma, b.two_sigma]
  rw [hB.2.1] at h
  linear_combination h

lemma inverse_combination (b : FieldBasis P I B)
    (hB : PseudolatticePresentation P I B) (a c : ℤ) :
    P.epsilon⁻¹ * ((a : K) * b.one + (c : K) * b.two) =
      ((B.matrix 1 1 * a - B.matrix 1 0 * c : ℤ) : K) * b.one +
      ((-B.matrix 0 1 * a + B.matrix 0 0 * c : ℤ) : K) * b.two := by
  apply P.sigma₁.injective
  have h := congrArg Prod.fst
    (DistributionBasisValuesAux.periodDifference_combination B hB.1 a c)
  simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_intCast, distributionBetaOne, distributionBetaTwo,
    zsmul_eq_mul] at h
  change ((distributionPeriod B)⁻¹ - 1) *
    ((a : ℝ) * (B.scale * B.tau) + (c : ℝ) * B.scale) = _ at h
  simp only [map_add, map_mul, map_inv₀, map_intCast, b.one_sigma, b.two_sigma]
  rw [hB.2.1] at h
  push_cast at h ⊢
  linear_combination h


def coordinates (b : FieldBasis P I B) (hB : PseudolatticePresentation P I B)
    (z : K) (hz : z ∈ I.val) : ℤ × ℤ :=
  let h := (b.mem_iff hB z).mp hz
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

lemma coordinates_spec (b : FieldBasis P I B) (hB : PseudolatticePresentation P I B)
    (z : K) (hz : z ∈ I.val) :
    z = (b.coordinates hB z hz).1 * b.one + (b.coordinates hB z hz).2 * b.two :=
  Classical.choose_spec (Classical.choose_spec ((b.mem_iff hB z).mp hz))

lemma coordinates_zero (b : FieldBasis P I B) (hB : PseudolatticePresentation P I B)
    (hz : (0 : K) ∈ I.val) : b.coordinates hB 0 hz = (0, 0) := by
  have h := b.coefficients_unique hB (b.coordinates hB 0 hz).1
    (b.coordinates hB 0 hz).2 0 0 (by simpa using (b.coordinates_spec hB 0 hz).symm)
  exact Prod.ext h.1 h.2

end FieldBasis

lemma basis_tau_irrational (B : DistributionBasis) (hB : B.Valid) : Irrational B.tau :=
  modularPhi_real_fixedPoint_irrational B.matrix hB.1 hB.2.1 B.tau
    (lt_trans zero_lt_one hB.2.2.2.1) hB.2.2.1

lemma basis_etaDenom (P : PeriodData K) (I : StablePseudolattice P)
    (B : DistributionBasis) (hB : PseudolatticePresentation P I B) :
    etaDenom B.matrix (B.tau : ℂ) = (P.sigma₁ P.epsilon : ℂ) := by
  simpa only [etaDenom, distributionPeriod, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_intCast] using congrArg (fun t : ℝ => (t : ℂ)) hB.2.1

lemma basis_etaDenom_pos (B : DistributionBasis) (hB : B.Valid) :
    0 < (etaDenom B.matrix (B.tau : ℂ)).re := by
  simpa [etaDenom, distributionPeriod] using lt_trans zero_lt_one hB.2.2.2.1

lemma fieldBasis_hermite (P : PeriodData K) (I J : StablePseudolattice P)
    (BI BJ : DistributionBasis) (hBI : PseudolatticePresentation P I BI)
    (hBJ : PseudolatticePresentation P J BJ)
    (bI : FieldBasis P I BI) (bJ : FieldBasis P J BJ) (n m : ℕ) (k : ℤ)
    (hm : 0 < m) (htau : BI.tau = ((n : ℝ) * BJ.tau + (k : ℝ)) / (m : ℝ))
    (hs : BI.scale = (m : ℝ) * BJ.scale) :
    bI.one = (n : K) * bJ.one + (k : K) * bJ.two ∧
      bI.two = (m : K) * bJ.two := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · apply P.sigma₁.injective
    simp only [map_add, map_mul, map_natCast, map_intCast,
      bI.one_sigma, bJ.one_sigma, bJ.two_sigma, htau, hs]
    field_simp
    <;> ring
  · apply P.sigma₁.injective
    simp only [map_mul, map_natCast, bI.two_sigma, bJ.two_sigma, hs]


theorem perm_minimalPeriod_inv {α : Type*} (f : Equiv.Perm α) (a : α) :
    Function.minimalPeriod (f⁻¹ : Equiv.Perm α) a = Function.minimalPeriod f a := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change (f⁻¹ ^ n) a = a ↔ (f ^ n) a = a
  rw [inv_pow]
  constructor
  · intro h
    have h' := congrArg (f ^ n) h
    simpa using h'.symm
  · intro h
    have h' := congrArg ((f ^ n)⁻¹ : Equiv.Perm α) h
    simpa using h'.symm


def inverseOrbitPoint (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) (j : Fin (orbitLength P I J hIJ x o)) :
    Fibre P I J hIJ x :=
  ((fibrePerm P I J hIJ x)⁻¹ ^ (j : ℕ)) (orbitRepresentative P I J hIJ x o)

theorem inverseOrbitPoint_orbit (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) (j : Fin (orbitLength P I J hIJ x o)) :
    Quotient.mk (orbitSetoid P I J hIJ x) (inverseOrbitPoint P I J hIJ x o j) = o := by
  calc
    _ = Quotient.mk _ (orbitRepresentative P I J hIJ x o) := by
      apply Quotient.sound
      change ∃ n : ℤ, (fibrePerm P I J hIJ x ^ n)
        (inverseOrbitPoint P I J hIJ x o j) = orbitRepresentative P I J hIJ x o
      refine ⟨(j : ℕ), ?_⟩
      simp [inverseOrbitPoint, zpow_natCast, inv_pow]
    _ = o := Quotient.out_eq o

theorem inverseOrbitPoint_injective (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    Function.Injective (fun s : Σ o : Orbit P I J hIJ x, Fin (orbitLength P I J hIJ x o) =>
      inverseOrbitPoint P I J hIJ x s.1 s.2) := by
  intro a b hab
  obtain ⟨o, j⟩ := a
  obtain ⟨p, k⟩ := b
  change inverseOrbitPoint P I J hIJ x o j = inverseOrbitPoint P I J hIJ x p k at hab
  have hop : o = p := by
    rw [← inverseOrbitPoint_orbit P I J hIJ x o j,
      ← inverseOrbitPoint_orbit P I J hIJ x p k]
    exact congrArg (Quotient.mk _) hab
  subst p
  have hjk : (j : ℕ) = (k : ℕ) := by
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (f := ((fibrePerm P I J hIJ x)⁻¹ : Equiv.Perm _))
      (x := orbitRepresentative P I J hIJ x o) ?_ ?_).mp
    · exact hab
    · rw [perm_minimalPeriod_inv]
      exact j.isLt
    · rw [perm_minimalPeriod_inv]
      exact k.isLt
  exact congrArg (Sigma.mk o) (Fin.ext hjk)

def inverseOrbitEquiv (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) :
    (Σ o : Orbit P I J hIJ x, Fin (orbitLength P I J hIJ x o)) ≃ Fibre P I J hIJ x :=
  Equiv.ofBijective (fun s => inverseOrbitPoint P I J hIJ x s.1 s.2) <|
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨
      inverseOrbitPoint_injective P I J hIJ x, by
        simp only [Fintype.card_sigma, Fintype.card_fin]
        rw [sum_orbitLength P I J hIJ x]
        exact (fibre_finite_card P I J hIJ x).2.symm.trans Nat.card_eq_fintype_card⟩

@[simp]
theorem inverseOrbitEquiv_apply (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ x) (j : Fin (orbitLength P I J hIJ x o)) :
    inverseOrbitEquiv P I J hIJ x ⟨o, j⟩ =
      ((fibrePerm P I J hIJ x)⁻¹ ^ (j : ℕ)) (orbitRepresentative P I J hIJ x o) := rfl

theorem prod_fibre_eq_prod_inverse {M : Type*} [CommMonoid M]
    (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (F : Fibre P I J hIJ x → M) :
    (∏ a, F a) = ∏ o : Orbit P I J hIJ x, ∏ j : Fin (orbitLength P I J hIJ x o),
      F (((fibrePerm P I J hIJ x)⁻¹ ^ (j : ℕ)) (orbitRepresentative P I J hIJ x o)) := by
  rw [← (inverseOrbitEquiv P I J hIJ x).prod_comp F, Fintype.prod_sigma]
  rfl

theorem prod_fibre_eq_prod_inverse_range {M : Type*} [CommMonoid M]
    (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J)
    (F : Fibre P I J hIJ x → M) :
    (∏ a, F a) = ∏ o : Orbit P I J hIJ x, ∏ j ∈ Finset.range (orbitLength P I J hIJ x o),
      F (((fibrePerm P I J hIJ x)⁻¹ ^ j) (orbitRepresentative P I J hIJ x o)) := by
  rw [prod_fibre_eq_prod_inverse P I J hIJ x F]
  apply Finset.prod_congr rfl
  intro o _
  exact Fin.prod_univ_eq_prod_range
    (fun j => F (((fibrePerm P I J hIJ x)⁻¹ ^ j) (orbitRepresentative P I J hIJ x o))) _


theorem weighted_product_eq_value_off_lattice
    (P : PeriodData K) (I : StablePseudolattice P)
    (BI : DistributionBasis) (hBI : PseudolatticePresentation P I BI)
    (r : ℕ) (hr : 0 < r) (z : K)
    (hz : z ∈ pseudolatticePeriodPoints
      (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr))
    (hzI : z ∉ I.val)
    (y : ℕ → ℂ) (A B p q h : ℕ → ℤ)
    (hp0 : p 0 = 0) (hAr : A r = A 0)
    (hrep : ∀ j, j < r → y 0 / etaDenom BI.matrix (BI.tau : ℂ) ^ j =
      y j + (p j : ℂ) * (BI.tau : ℂ) + (q j : ℂ))
    (hindex : ∀ j, j < r → A (j + 1) = B j + h j)
    (hcoord : ∀ j, j < r → BI.matrix 1 1 * p j - BI.matrix 1 0 * q j =
      p (j + 1) - h j)
    (hy0 : y 0 = ((P.sigma₁ z / BI.scale : ℝ) : ℂ))
    (hbalance : y 0 / etaDenom BI.matrix (BI.tau : ℂ) ^ r - y 0 =
      (p r : ℂ) * (BI.tau : ℂ) + (q r : ℂ)) :
    (∏ j ∈ Finset.range r,
      etaMultiplier BI.matrix * modularPhi BI.matrix (A j) (B j) (y j) (BI.tau : ℂ)) =
      M72.value (PeriodPower.powPeriod P r hr) (PeriodPower.powLattice P I r hr)
        (pseudolatticeMk _ _ z hz) := by
  let Q := PeriodPower.powPeriod P r hr
  let L := PeriodPower.powLattice P I r hr
  let C := PeriodPower.powBasis BI r
  have hC : PseudolatticePresentation Q L C :=
    PeriodPower.powBasis_presentation P I BI hBI r hr
  have hmem : pseudolatticeEmbedding Q z ∈ distributionPeriodPoints C :=
    pseudolatticePresentation_point_mem Q L C hC z hz
  have hnot : pseudolatticeEmbedding Q z ∉ distributionLattice C := by
    rw [hC.2.2]
    rintro ⟨w, hw, hwz⟩
    exact hzI (pseudolatticeEmbedding_injective Q hwz ▸ hw)
  have hy : y 0 ∉ modularPhiPseudoLattice (BI.tau : ℂ) := by
    rw [hy0]
    exact fun hy => hnot
      ((distributionPeriodPoints_first_lattice_iff C hC.1 _ hmem).mp hy)
  have hT : 0 < (etaDenom BI.matrix (BI.tau : ℂ)).re := by
    simpa only [etaDenom, Complex.add_re, Complex.mul_re, Complex.intCast_re,
      Complex.ofReal_re, Complex.intCast_im, Complex.ofReal_im, zero_mul,
      sub_zero, distributionPeriod] using dBasis_period_pos BI hBI.1
  have hden := (modularPhi_pow_fixedPoint_domain BI.matrix hBI.1.1 hBI.1.2.1
    BI.tau hBI.1.2.2.1 hT r).2.1
  let v := distributionIntegerCoordinates C
    (distributionPeriodDifference C (pseudolatticeEmbedding Q z))
  have harg := DistributionBasisValuesAux.periodPoint_argument C hC.1 _ hmem
  change ((P.sigma₁ z / BI.scale : ℝ) : ℂ) /
      etaDenom (BI.matrix ^ r) (BI.tau : ℂ) =
    ((P.sigma₁ z / BI.scale : ℝ) : ℂ) +
      (v 0 : ℂ) * (BI.tau : ℂ) + (v 1 : ℂ) at harg
  rw [hden, ← hy0] at harg
  have hcoeff : (v 0 : ℂ) * (BI.tau : ℂ) + (v 1 : ℂ) =
      (p r : ℂ) * (BI.tau : ℂ) + (q r : ℂ) := by
    linear_combination hbalance - harg
  have hv : v 0 = p r := (dl_int_coeff_eq (distributionBasis_spectral BI hBI.1).1
    (v 0) (v 1) (p r) (q r) (by exact_mod_cast hcoeff)).1
  rw [M72.value_mk Q L C hC z hz, M72.basisValue_off_lattice Q L C hC z hz hzI]
  change _ = etaMultiplier (BI.matrix ^ r) *
    modularPhi (BI.matrix ^ r) (v 0) 0
      ((P.sigma₁ z / BI.scale : ℝ) : ℂ) (BI.tau : ℂ)
  rw [hv, ← hy0]
  exact DistributionOrbitCocycle.orbit_weighted_product_off_lattice BI.matrix BI.tau r
    y A B p q h hr hBI.1.1 hBI.1.2.1 hBI.1.2.2.1 hT
    hp0 hAr hrep hindex hcoord hy hbalance



lemma ambientMk_eq_iff (I : Submodule ℤ K) (a b : K) :
    ambientMk I a = ambientMk I b ↔ a - b ∈ I :=
  QuotientAddGroup.eq_iff_sub_mem

lemma ambientUnit_inv_mk (P : PeriodData K) (I : StablePseudolattice P) (z : K) :
    (ambientUnit P I).symm (ambientMk I.val z) = ambientMk I.val (P.epsilon⁻¹ * z) := rfl

lemma fibre_inverse_val (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) (a : Fibre P I J hIJ x) :
    ((fibrePerm P I J hIJ x)⁻¹ a).val = (ambientUnit P I).symm a.val := rfl

lemma fibre_inverse_pow_val (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P J) (a : Fibre P I J hIJ x) (j : ℕ) :
    (((fibrePerm P I J hIJ x)⁻¹ ^ j) a).val =
      ((ambientUnit P I).symm.toEquiv ^ j) a.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, fibre_inverse_val, ih,
      pow_succ', Equiv.Perm.mul_apply]
    rfl

lemma ambientUnit_inv_pow_mk (P : PeriodData K) (I : StablePseudolattice P)
    (z : K) (j : ℕ) :
    ((ambientUnit P I).symm.toEquiv ^ j) (ambientMk I.val z) =
      ambientMk I.val ((P.epsilon⁻¹ ^ j) * z) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    change ambientMk I.val (P.epsilon⁻¹ * (P.epsilon⁻¹ ^ j * z)) = _
    congr 1
    rw [pow_succ']
    ring

/-- Simultaneous Hermite presentations, together with their actual field bases. -/
structure HermiteData (P : PeriodData K) (I J : StablePseudolattice P) where
  BI : DistributionBasis
  BJ : DistributionBasis
  hBI : PseudolatticePresentation P I BI
  hBJ : PseudolatticePresentation P J BJ
  bI : FieldBasis P I BI
  bJ : FieldBasis P J BJ
  n : ℕ
  m : ℕ
  k : ℤ
  hn : 0 < n
  hm : 0 < m
  tau : BI.tau = ((n : ℝ) * BJ.tau + (k : ℝ)) / (m : ℝ)
  scale : BI.scale = (m : ℝ) * BJ.scale
  conjugateScale : BI.scaleConj = (m : ℝ) * BJ.scaleConj
  matrix : (BI.matrix : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
    hermiteMatrix n m k * (BJ.matrix : Matrix (Fin 2) (Fin 2) ℤ)
  index : inclusionIndex I.val J.val = n * m

namespace HermiteData

variable {P : PeriodData K} {I J : StablePseudolattice P}

lemma one_eq (D : HermiteData P I J) :
    D.bI.one = (D.n : K) * D.bJ.one + (D.k : K) * D.bJ.two :=
  (fieldBasis_hermite P I J D.BI D.BJ D.hBI D.hBJ D.bI D.bJ D.n D.m D.k
    D.hm D.tau D.scale).1

lemma two_eq (D : HermiteData P I J) : D.bI.two = (D.m : K) * D.bJ.two :=
  (fieldBasis_hermite P I J D.BI D.BJ D.hBI D.hBJ D.bI D.bJ D.n D.m D.k
    D.hm D.tau D.scale).2

abbrev Grid (D : HermiteData P I J) := Fin D.n × Fin D.m

def gridLift (D : HermiteData P I J) (z : K) (ij : D.Grid) : K :=
  z + (ij.1.val : K) * D.bJ.one + (ij.2.val : K) * D.bJ.two

lemma gridLift_sub_mem (D : HermiteData P I J) (z : K) (ij : D.Grid) :
    D.gridLift z ij - z ∈ J.val := by
  have h := J.val.add_mem (J.val.smul_mem (ij.1.val : ℤ) D.bJ.one_mem)
    (J.val.smul_mem (ij.2.val : ℤ) D.bJ.two_mem)
  convert h using 1 <;> simp [gridLift, zsmul_eq_mul] <;> ring

lemma gridLift_argument (D : HermiteData P I J) (z : K) (ij : D.Grid) :
    ((P.sigma₁ (D.gridLift z ij) / D.BI.scale : ℝ) : ℂ) =
      hermiteArgument D.m ij.1.val ij.2.val
        ((P.sigma₁ z / D.BJ.scale : ℝ) : ℂ) (D.BJ.tau : ℂ) := by
  have hs : D.BJ.scale ≠ 0 := D.hBJ.1.2.2.2.2.1.ne'
  have hm : (D.m : ℝ) ≠ 0 := by exact_mod_cast D.hm.ne'
  have hr : P.sigma₁ (D.gridLift z ij) / D.BI.scale =
      (P.sigma₁ z / D.BJ.scale + (ij.1.val : ℝ) * D.BJ.tau + (ij.2.val : ℝ)) /
        (D.m : ℝ) := by
    simp only [gridLift, map_add, map_mul, map_natCast, D.bJ.one_sigma, D.bJ.two_sigma,
      D.scale]
    field_simp
    <;> ring
  simpa [hermiteArgument] using congrArg (fun t : ℝ => (t : ℂ)) hr

lemma tau_complex (D : HermiteData P I J) :
    (D.BI.tau : ℂ) = hermiteTau D.n D.m D.k (D.BJ.tau : ℂ) := by
  simpa [hermiteTau] using congrArg (fun t : ℝ => (t : ℂ)) D.tau

lemma ambientProject_mk (hIJ : I.val ≤ J.val) (z : K) :
    ambientProject I.val J.val hIJ (ambientMk I.val z) = ambientMk J.val z := rfl

def gridFibre (D : HermiteData P I J) (hIJ : I.val ≤ J.val)
    (x : PseudolatticeGroup P J) (z : K) (hz : z ∈ pseudolatticePeriodPoints P J)
    (he : pseudolatticeMk P J z hz = x) (ij : D.Grid) : Fibre P I J hIJ x :=
  ⟨ambientMk I.val (D.gridLift z ij), by
    rw [ambientProject_mk, ← he, toAmbient_mk]
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (D.gridLift_sub_mem z ij)⟩

lemma gridFibre_injective (D : HermiteData P I J) (hIJ : I.val ≤ J.val)
    (x : PseudolatticeGroup P J) (z : K) (hz : z ∈ pseudolatticePeriodPoints P J)
    (he : pseudolatticeMk P J z hz = x) :
    Function.Injective (D.gridFibre hIJ x z hz he) := by
  intro a b hab
  have hmem : D.gridLift z a - D.gridLift z b ∈ I.val :=
    QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val hab)
  obtain ⟨p, q, hpq⟩ := (D.bI.mem_iff D.hBI _).mp hmem
  rw [D.one_eq, D.two_eq] at hpq
  have hcoeff : (((a.1.val : ℤ) - (b.1.val : ℤ)) : K) * D.bJ.one +
        (((a.2.val : ℤ) - (b.2.val : ℤ)) : K) * D.bJ.two =
      ((p * (D.n : ℤ) : ℤ) : K) * D.bJ.one +
        ((p * D.k + q * (D.m : ℤ) : ℤ) : K) * D.bJ.two := by
    push_cast
    dsimp [gridLift] at hpq
    linear_combination hpq
  obtain ⟨hc₁, hc₂⟩ := D.bJ.coefficients_unique D.hBJ
    ((a.1.val : ℤ) - (b.1.val : ℤ)) ((a.2.val : ℤ) - (b.2.val : ℤ))
    (p * (D.n : ℤ)) (p * D.k + q * (D.m : ℤ)) (by simpa only [Int.cast_sub, Int.cast_natCast] using hcoeff)
  have h₁ : a.1.val = b.1.val := by
    have hc := congrArg (fun t : ℤ => t % (D.n : ℤ))
      (show (a.1.val : ℤ) = (b.1.val : ℤ) + p * (D.n : ℤ) by omega)
    simp only [Int.add_mul_emod_self_right] at hc
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast a.1.isLt),
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast b.1.isLt)] at hc
    exact_mod_cast hc
  have hp : p = 0 := by
    have hn : (D.n : ℤ) ≠ 0 := by exact_mod_cast D.hn.ne'
    rw [h₁, sub_self] at hc₁
    exact (mul_eq_zero.mp hc₁.symm).resolve_right hn
  have h₂ : a.2.val = b.2.val := by
    rw [hp, zero_mul, zero_add] at hc₂
    have hc := congrArg (fun t : ℤ => t % (D.m : ℤ))
      (show (a.2.val : ℤ) = (b.2.val : ℤ) + q * (D.m : ℤ) by omega)
    simp only [Int.add_mul_emod_self_right] at hc
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast a.2.isLt),
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast b.2.isLt)] at hc
    exact_mod_cast hc
  exact Prod.ext (Fin.ext h₁) (Fin.ext h₂)

def gridEquivFibre (D : HermiteData P I J) (hIJ : I.val ≤ J.val)
    (x : PseudolatticeGroup P J) (z : K) (hz : z ∈ pseudolatticePeriodPoints P J)
    (he : pseudolatticeMk P J z hz = x) : D.Grid ≃ Fibre P I J hIJ x :=
  Equiv.ofBijective (D.gridFibre hIJ x z hz he)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨D.gridFibre_injective hIJ x z hz he, by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card,
        (fibre_finite_card P I J hIJ x).2, D.index]⟩)


structure Chart (D : HermiteData P I J) (hIJ : I.val ≤ J.val)
    (x : PseudolatticeGroup P J) where
  z : K
  mem : z ∈ pseudolatticePeriodPoints P J
  represents : pseudolatticeMk P J z mem = x
  zero : x = 0 → z = 0

def chart (D : HermiteData P I J) (hIJ : I.val ≤ J.val)
    (x : PseudolatticeGroup P J) : D.Chart hIJ x := by
  classical
  by_cases hx : x = 0
  · refine ⟨0, (pseudolatticePeriodPoints P J).zero_mem, ?_, fun _ => rfl⟩
    exact (show pseudolatticeMk P J 0
      (pseudolatticePeriodPoints P J).zero_mem = 0 from rfl).trans hx.symm
  · refine ⟨(Quotient.out x).val, (Quotient.out x).property, Quotient.out_eq x, ?_⟩
    exact fun h => False.elim (hx h)


namespace Chart

variable {D : HermiteData P I J} {hIJ : I.val ≤ J.val} {x : PseudolatticeGroup P J}

def equiv (C : D.Chart hIJ x) : D.Grid ≃ Fibre P I J hIJ x :=
  D.gridEquivFibre hIJ x C.z C.mem C.represents

def grid (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) : D.Grid :=
  C.equiv.symm (((fibrePerm P I J hIJ x)⁻¹ ^ j) (orbitRepresentative P I J hIJ x o))

def point (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) : K :=
  D.gridLift C.z (C.grid o j)

def argument (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) : ℂ :=
  ((P.sigma₁ (C.point o j) / D.BI.scale : ℝ) : ℂ)

def sourceIndex (C : D.Chart hIJ x) : ℤ :=
  distributionIntegerCoordinates D.BJ
    (distributionPeriodDifference D.BJ (pseudolatticeEmbedding P C.z)) 0

def A (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) : ℤ :=
  hermiteNumIndex D.n C.sourceIndex (C.grid o j).1.val

def B (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) : ℤ :=
  hermiteDenIndex D.BJ.matrix D.n (C.grid o j).1.val (C.grid o j).2.val

lemma grid_val (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    ambientMk I.val (C.point o j) =
      (((fibrePerm P I J hIJ x)⁻¹ ^ j) (orbitRepresentative P I J hIJ x o)).val := by
  exact congrArg Subtype.val (C.equiv.apply_symm_apply _)

lemma point_initial (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) :
    ambientMk I.val (C.point o 0) = (orbitRepresentative P I J hIJ x o).val := by
  simpa using C.grid_val o 0

lemma point_relation (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    P.epsilon⁻¹ ^ j * C.point o 0 - C.point o j ∈ I.val := by
  apply (ambientMk_eq_iff _ _ _).mp
  rw [← ambientUnit_inv_pow_mk, C.point_initial, C.grid_val, fibre_inverse_pow_val]

lemma point_step (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    P.epsilon⁻¹ * C.point o j - C.point o (j + 1) ∈ I.val := by
  apply (ambientMk_eq_iff _ _ _).mp
  rw [← ambientUnit_inv_mk, C.grid_val, C.grid_val, pow_succ', Equiv.Perm.mul_apply,
    fibre_inverse_val]

lemma grid_closed (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) :
    C.grid o (orbitLength P I J hIJ x o) = C.grid o 0 := by
  unfold grid
  simp only [pow_zero, Equiv.Perm.one_apply]
  apply congrArg C.equiv.symm
  apply (fibrePerm P I J hIJ x ^ orbitLength P I J hIJ x o).injective
  simpa [inv_pow] using (orbitLength_returns P I J hIJ x o).symm


lemma point_closed (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) :
    C.point o (orbitLength P I J hIJ x o) = C.point o 0 := by
  unfold point
  rw [C.grid_closed]

lemma A_closed (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) :
    C.A o (orbitLength P I J hIJ x o) = C.A o 0 := by
  unfold A
  rw [C.grid_closed]

def shift (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) : ℤ × ℤ :=
  D.bI.coordinates D.hBI _ (C.point_relation o j)

def step (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) : ℤ × ℤ :=
  D.bI.coordinates D.hBI _ (C.point_step o j)

lemma shift_spec (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    P.epsilon⁻¹ ^ j * C.point o 0 - C.point o j =
      ((C.shift o j).1 : K) * D.bI.one + ((C.shift o j).2 : K) * D.bI.two :=
  D.bI.coordinates_spec D.hBI _ (C.point_relation o j)

lemma step_spec (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    P.epsilon⁻¹ * C.point o j - C.point o (j + 1) =
      ((C.step o j).1 : K) * D.bI.one + ((C.step o j).2 : K) * D.bI.two :=
  D.bI.coordinates_spec D.hBI _ (C.point_step o j)

lemma shift_zero (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) :
    C.shift o 0 = (0, 0) := by
  unfold shift
  convert D.bI.coordinates_zero D.hBI (I.val.zero_mem) using 1 <;> simp

lemma argument_rep (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    C.argument o 0 / etaDenom D.BI.matrix (D.BI.tau : ℂ) ^ j =
      C.argument o j + ((C.shift o j).1 : ℂ) * (D.BI.tau : ℂ) +
        ((C.shift o j).2 : ℂ) := by
  have hs : D.BI.scale ≠ 0 := D.hBI.1.2.2.2.2.1.ne'
  have hε : P.sigma₁ P.epsilon ≠ 0 := (lt_trans zero_lt_one P.epsilon_gt_one).ne'
  have h := congrArg P.sigma₁ (C.shift_spec o j)
  simp only [map_sub, map_add, map_mul, map_pow, map_inv₀, map_intCast,
    D.bI.one_sigma, D.bI.two_sigma] at h
  have hr : P.sigma₁ (C.point o 0) / D.BI.scale / (P.sigma₁ P.epsilon) ^ j =
      P.sigma₁ (C.point o j) / D.BI.scale +
        ((C.shift o j).1 : ℝ) * D.BI.tau + ((C.shift o j).2 : ℝ) := by
    rw [inv_pow] at h
    field_simp [hs, hε] at h ⊢
    linear_combination h
  rw [basis_etaDenom P I D.BI D.hBI]
  simpa only [argument, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_intCast] using
    congrArg (fun t : ℝ => (t : ℂ)) hr

lemma argument_step (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    C.argument o j / etaDenom D.BI.matrix (D.BI.tau : ℂ) =
      C.argument o (j + 1) + ((C.step o j).1 : ℂ) * (D.BI.tau : ℂ) +
        ((C.step o j).2 : ℂ) := by
  have hs : D.BI.scale ≠ 0 := D.hBI.1.2.2.2.2.1.ne'
  have hε : P.sigma₁ P.epsilon ≠ 0 := (lt_trans zero_lt_one P.epsilon_gt_one).ne'
  have h := congrArg P.sigma₁ (C.step_spec o j)
  simp only [map_sub, map_add, map_mul, map_inv₀, map_intCast,
    D.bI.one_sigma, D.bI.two_sigma] at h
  have hr : P.sigma₁ (C.point o j) / D.BI.scale / P.sigma₁ P.epsilon =
      P.sigma₁ (C.point o (j + 1)) / D.BI.scale +
        ((C.step o j).1 : ℝ) * D.BI.tau + ((C.step o j).2 : ℝ) := by
    field_simp [hs, hε] at h ⊢
    linear_combination h
  rw [basis_etaDenom P I D.BI D.hBI]
  simpa only [argument, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_intCast] using
    congrArg (fun t : ℝ => (t : ℂ)) hr

lemma coordinate_step (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    D.BI.matrix 1 1 * (C.shift o j).1 - D.BI.matrix 1 0 * (C.shift o j).2 =
      (C.shift o (j + 1)).1 - (C.step o j).1 :=
  orbit_coordinate_step D.BI.matrix D.BI.tau D.hBI.1.1 D.hBI.1.2.1
    D.hBI.1.2.2.1 (basis_etaDenom_pos D.BI D.hBI.1)
    (C.argument o 0) (C.argument o j) (C.argument o (j + 1)) j
    (C.shift o j).1 (C.shift o j).2 (C.shift o (j + 1)).1 (C.shift o (j + 1)).2
    (C.step o j).1 (C.step o j).2 (C.argument_rep o j) (C.argument_rep o (j + 1))
    (C.argument_step o j)

lemma source_value (C : D.Chart hIJ x) :
    M72.value P J x = etaMultiplier D.BJ.matrix *
      modularPhi D.BJ.matrix C.sourceIndex 0
        ((P.sigma₁ C.z / D.BJ.scale : ℝ) : ℂ) (D.BJ.tau : ℂ) := by
  have hv : M72.value P J x = M72.basisValue P D.BJ C.z := by
    calc
      _ = M72.value P J (pseudolatticeMk P J C.z C.mem) :=
        congrArg (M72.value P J) C.represents.symm
      _ = _ := M72.value_mk P J D.BJ D.hBJ C.z C.mem
  rw [hv]
  by_cases hx : x = 0
  · have hz : C.z = 0 := C.zero hx
    have hu : C.sourceIndex = 0 := by
      simp [sourceIndex, hz, distributionIntegerCoordinates, distributionCoordinates]
    rw [hz, hu, M72.basisValue_on_lattice P J D.BJ D.hBJ 0 J.val.zero_mem]
    simp only [map_zero, zero_div, Complex.ofReal_zero]
    rw [modularPhi_zero_fixedPoint_value D.BJ.matrix D.BJ.tau
      D.hBJ.1.1 D.hBJ.1.2.1 D.hBJ.1.2.2.1 (basis_etaDenom_pos D.BJ D.hBJ.1)]
    rw [show (D.BJ.matrix 1 0 : ℝ) * D.BJ.tau + (D.BJ.matrix 1 1 : ℝ) =
      P.sigma₁ P.epsilon from D.hBJ.2.1]
    simp [etaMultiplier_ne_zero D.BJ.matrix D.hBJ.1.1]
  · apply M72.basisValue_off_lattice P J D.BJ D.hBJ C.z C.mem
    intro hz
    apply hx
    rw [← C.represents]
    exact (M72.mk_eq_iff P J C.z 0 C.mem (pseudolatticePeriodPoints P J).zero_mem).mpr
      (by simpa using hz)


lemma index_step (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) (j : ℕ) :
    C.A o (j + 1) = C.B o j + (C.step o j).1 := by
  have hd := D.bJ.difference_expansion D.hBJ C.z C.mem
  have hi := D.bJ.inverse_combination D.hBJ
    ((C.grid o j).1.val : ℤ) ((C.grid o j).2.val : ℤ)
  have hs := C.step_spec o j
  rw [D.one_eq, D.two_eq] at hs
  have he :
      ((C.sourceIndex + D.BJ.matrix 1 1 * ((C.grid o j).1.val : ℤ) -
          D.BJ.matrix 1 0 * ((C.grid o j).2.val : ℤ) -
          ((C.grid o (j + 1)).1.val : ℤ) : ℤ) : K) * D.bJ.one +
        ((distributionIntegerCoordinates D.BJ
          (distributionPeriodDifference D.BJ (pseudolatticeEmbedding P C.z)) 1 +
          -D.BJ.matrix 0 1 * ((C.grid o j).1.val : ℤ) +
          D.BJ.matrix 0 0 * ((C.grid o j).2.val : ℤ) -
          ((C.grid o (j + 1)).2.val : ℤ) : ℤ) : K) * D.bJ.two =
      (((D.n : ℤ) * (C.step o j).1 : ℤ) : K) * D.bJ.one +
        ((D.k * (C.step o j).1 + (D.m : ℤ) * (C.step o j).2 : ℤ) : K) * D.bJ.two := by
    dsimp only [point, gridLift] at hs
    dsimp only [sourceIndex]
    push_cast at hi ⊢
    linear_combination hs - hd - hi
  have hc := (D.bJ.coefficients_unique D.hBJ _ _ _ _ he).1
  exact hermite_orbit_index_match D.BJ.matrix D.n D.hn C.sourceIndex
    (C.step o j).1 (C.grid o j).1.val (C.grid o j).2.val
    (C.grid o (j + 1)).1.val (by omega)

lemma point_mem (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) :
    C.point o 0 ∈ pseudolatticePeriodPoints
      (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
      (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
        (orbitLength_pos P I J hIJ x o)) := by
  apply orbit_member_mem P I J hIJ x o
  exact ⟨0, by simpa using C.point_initial o⟩

lemma argument_balance (C : D.Chart hIJ x) (o : Orbit P I J hIJ x) :
    C.argument o 0 / etaDenom D.BI.matrix (D.BI.tau : ℂ) ^ orbitLength P I J hIJ x o -
        C.argument o 0 =
      ((C.shift o (orbitLength P I J hIJ x o)).1 : ℂ) * (D.BI.tau : ℂ) +
        ((C.shift o (orbitLength P I J hIJ x o)).2 : ℂ) := by
  have h := C.argument_rep o (orbitLength P I J hIJ x o)
  change _ = ((P.sigma₁ (C.point o _) / D.BI.scale : ℝ) : ℂ) + _ + _ at h
  rw [C.point_closed] at h
  dsimp only [argument] at h ⊢
  linear_combination h

lemma weighted_product_off_lattice (C : D.Chart hIJ x) (o : Orbit P I J hIJ x)
    (hzI : C.point o 0 ∉ I.val) :
    (∏ j ∈ Finset.range (orbitLength P I J hIJ x o),
      etaMultiplier D.BI.matrix * modularPhi D.BI.matrix (C.A o j) (C.B o j)
        (C.argument o j) (D.BI.tau : ℂ)) =
      M72.value
        (PeriodPower.powPeriod P (orbitLength P I J hIJ x o) (orbitLength_pos P I J hIJ x o))
        (PeriodPower.powLattice P I (orbitLength P I J hIJ x o)
          (orbitLength_pos P I J hIJ x o))
        (pseudolatticeMk _ _ (C.point o 0) (C.point_mem o)) := by
  apply weighted_product_eq_value_off_lattice P I D.BI D.hBI _
    (orbitLength_pos P I J hIJ x o) (C.point o 0) (C.point_mem o) hzI
    (C.argument o) (C.A o) (C.B o) (fun j => (C.shift o j).1)
    (fun j => (C.shift o j).2) (fun j => (C.step o j).1)
  · exact congrArg Prod.fst (C.shift_zero o)
  · exact C.A_closed o
  · intro j _; exact C.argument_rep o j
  · intro j _; exact C.index_step o j
  · intro j _; exact C.coordinate_step o j
  · rfl
  · exact C.argument_balance o

end Chart

end HermiteData

end SICLean.L5.DistributionGeneralValuesAux
