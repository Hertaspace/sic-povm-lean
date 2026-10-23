import SICLean.L5.OddPrimeValues
import SICLean.L5.OddPrimeCharacterAverageAux
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.FiniteAbelian.Duality

set_option autoImplicit false

/-!
# Character extensions and the actual-lattice average in Lemma 2

Character-extension counting, orthogonality, and the actual lattice average. [RW-rec, p.
8]. The general distribution input here is the existing `distribution_subgroup` (11).
The finite-character wrappers can use Mathlib's `domRestrict_surjective`,
`card_domRestrictHom_ker`, and complex finite Pontryagin duality. For an arbitrary
finite homomorphism, extension count = index of range, whereas fibre size = cardinality
of kernel. Equality of source and target cardinalities is an explicit hypothesis of the
fibre/average wrappers. For actual period groups this follows from their common
cardinality N. In particular `periodProject` is never assumed to be surjective.
-/

noncomputable section

open scoped Classical BigOperators
open SICLean.L3

namespace SICLean.L5.OddPrimeCharacterAverage

section FiniteCharacters

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H]

/-- All complex character extensions along the given map, including when its range is a proper
subgroup. This definition contains no existence law. -/
def extensionFinset (φ : G →+ H) (θ : AddChar G ℂ) : Finset (AddChar H ℂ) :=
  Finset.univ.filter (fun χ => ∀ x : G, χ (φ x) = θ x)

/-- A real function's ordinary complex transform with an explicit common normalization. The actual
application uses inverse positive sqrt(N). -/
def realFourier (normalization : ℂ) (f : G → ℝ) (θ : AddChar G ℂ) : ℂ :=
  normalization * ∑ x : G, (f x : ℂ) * (θ x)⁻¹

/-- [RW-rec, p. 8]: compatibility means equality on every source label. -/
theorem mem_extensionFinset (φ : G →+ H) (θ : AddChar G ℂ)
    (χ : AddChar H ℂ) :
    χ ∈ extensionFinset φ θ ↔ ∀ x : G, χ (φ x) = θ x := by
  simp only [extensionFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- [RW-rec, p. 8]: a character descends exactly when it kills the kernel; every character of the
range extends to the finite target group. -/
theorem extensionFinset_nonempty_iff (φ : G →+ H) (θ : AddChar G ℂ) :
    (extensionFinset φ θ).Nonempty ↔ ∀ x ∈ φ.ker, θ x = 1 := by
  exact OddPrimeCharacterAverageAux.extension_nonempty_iff φ θ

/-- [RW-rec, p. 8] finite-character counting wrapper. The general count is the index of the range;
equality with kernel size is not assumed here. -/
theorem extensionFinset_card (φ : G →+ H) (θ : AddChar G ℂ)
    (hθ : ∀ x ∈ φ.ker, θ x = 1) :
    (extensionFinset φ θ).card = φ.range.index := by
  exact OddPrimeCharacterAverageAux.extension_card φ θ hθ

/-- [RW-rec, p. 8] on-image orthogonality. The factor is the number of extensions, even when the
natural map has a nontrivial cokernel. -/
theorem extension_orthogonality_on_range (φ : G →+ H) (θ : AddChar G ℂ)
    (hθ : ∀ x ∈ φ.ker, θ x = 1) (x : G) :
    ∑ χ ∈ extensionFinset φ θ, (χ (φ x))⁻¹ =
      (φ.range.index : ℂ) * (θ x)⁻¹ := by
  calc
    _ = ∑ _χ ∈ extensionFinset φ θ, (θ x)⁻¹ :=
      Finset.sum_congr rfl fun χ hχ =>
        congrArg (fun z : ℂ => z⁻¹) ((mem_extensionFinset φ θ χ).mp hχ x)
    _ = _ := by simp [extensionFinset_card φ θ hθ, nsmul_eq_mul]

/-- [RW-rec, p. 8]: the annihilator-character sum vanishes off the range. -/
theorem extension_orthogonality_off_range (φ : G →+ H) (θ : AddChar G ℂ)
    (hθ : ∀ x ∈ φ.ker, θ x = 1) (y : H) (hy : y ∉ φ.range) :
    ∑ χ ∈ extensionFinset φ θ, (χ y)⁻¹ = 0 := by
  exact OddPrimeCharacterAverageAux.extension_sum_off_range φ θ hθ y hy

/-- [RW-rec, p. 8]: replacing the extension sum by a source fibre sum requires equal source/target
cardinality. Both sides then have the same factor D; no surjectivity hypothesis appears. -/
theorem extension_orthogonality_fibre (φ : G →+ H) (θ : AddChar G ℂ)
    (hcard : Nat.card G = Nat.card H) (hθ : ∀ x ∈ φ.ker, θ x = 1) (y : H) :
    ∑ χ ∈ extensionFinset φ θ, (χ y)⁻¹ =
      ∑ x ∈ Finset.univ.filter (fun x : G => φ x = y), (θ x)⁻¹ := by
  exact OddPrimeCharacterAverageAux.extension_sum_fibre φ θ hcard hθ y

/-- [RW-rec, p. 8]: pure finite-sum form of Lemma 2, after valuation has supplied the actual
distribution identity. The same normalization is used on both groups. Its nonvanishing is
unnecessary for this identity. -/
theorem realFourier_extension_average (φ : G →+ H) (θ : AddChar G ℂ)
    (hcard : Nat.card G = Nat.card H) (hθ : ∀ x ∈ φ.ker, θ x = 1)
    (normalization : ℂ) (f : G → ℝ) (g : H → ℝ)
    (hdistribution : ∀ x : G, g (φ x) = ∑ h : φ.ker, f (x + h.val)) :
    realFourier normalization f θ =
      (φ.range.index : ℂ)⁻¹ *
        ∑ χ ∈ extensionFinset φ θ, realFourier normalization g χ := by
  have hindex : φ.range.index = Fintype.card φ.ker := by
    simpa only [Nat.card_eq_fintype_card] using
      OddPrimeCharacterAverageAux.range_index_eq_card_ker φ hcard
  have hD : (φ.range.index : ℂ) ≠ 0 := by
    rw [hindex]
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ χ ∈ extensionFinset φ θ, realFourier normalization g χ) =
      (φ.range.index : ℂ) * realFourier normalization f θ := by
    calc
      _ = normalization * ∑ y : H, (g y : ℂ) *
          ∑ χ ∈ extensionFinset φ θ, (χ y)⁻¹ := by
        simp only [realFourier, ← Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = normalization * ∑ y : H,
          ∑ x ∈ Finset.univ.filter (fun x : G => φ x = y),
            (g y : ℂ) * (θ x)⁻¹ := by
        simp_rw [extension_orthogonality_fibre φ θ hcard hθ, Finset.mul_sum]
      _ = normalization * ∑ x : G, (g (φ x) : ℂ) * (θ x)⁻¹ := by
        congr 1
        calc
          _ = ∑ y : H, ∑ x ∈ Finset.univ.filter (fun x : G => φ x = y),
              (g (φ x) : ℂ) * (θ x)⁻¹ := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x hx
            rw [(Finset.mem_filter.mp hx).2]
          _ = _ := Finset.sum_fiberwise Finset.univ φ _
      _ = normalization * ∑ x : G, ∑ h : φ.ker,
          (f (x + h.val) : ℂ) * (θ x)⁻¹ := by
        simp_rw [hdistribution, Complex.ofReal_sum, Finset.sum_mul]
      _ = normalization * ∑ h : φ.ker, ∑ x : G,
          (f (x + h.val) : ℂ) * (θ x)⁻¹ := by
        rw [Finset.sum_comm]
      _ = normalization * ∑ _h : φ.ker, ∑ x : G, (f x : ℂ) * (θ x)⁻¹ := by
        congr 1
        apply Finset.sum_congr rfl
        intro h _
        have he (x : G) : θ (x + h.val) = θ x := by
          rw [AddChar.map_add_eq_mul, hθ h.val h.property, mul_one]
        have hs := Equiv.sum_comp (Equiv.addRight h.val)
          (fun x : G => (f x : ℂ) * (θ x)⁻¹)
        change (∑ x : G, (f (x + h.val) : ℂ) * (θ (x + h.val))⁻¹) = _ at hs
        simpa only [he] using hs
      _ = (φ.range.index : ℂ) * realFourier normalization f θ := by
        simp only [realFourier, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hindex]
        ring
  rw [hsum, inv_mul_cancel_left₀ hD]

end FiniteCharacters

universe u
variable {K : Type u} [Field K] [NumberField K]

open DistributionOrbitGeometry OddPrimeValues

local instance groupFinite (P : PeriodData K) (I : StablePseudolattice P) :
    Finite (PseudolatticeGroup P I) := (pseudolatticeGroup_finite_card P I).1

local instance groupFintype (P : PeriodData K) (I : StablePseudolattice P) :
    Fintype (PseudolatticeGroup P I) := Fintype.ofFinite _

/-- The literal additive lattice quotient J/I, using restriction of I to J. -/
abbrev LatticeQuotient {P : PeriodData K} (I J : StablePseudolattice P) :=
  J.val.toAddSubgroup ⧸
    I.val.toAddSubgroup.comap J.val.toAddSubgroup.subtype

/-- [RW-rec, p. 8]: the kernel condition at an actual field representative. This is induced by the
identity on K, not an abstract quotient map. -/
theorem periodProject_kernel_mk (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (z : K) (hz : z ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeMk P I z hz ∈ (periodProject P I J hIJ).ker ↔ z ∈ J.val := by
  change periodProject P I J hIJ (pseudolatticeMk P I z hz) = 0 ↔ z ∈ J.val
  rw [periodProject_mk]
  exact DistributionSubgroupLatticeAux.mk_eq_zero_iff P J z _

/-- [RW-rec, p. 8]: (epsilon-1)J <= I puts all of J/I in G_I, and the actual natural map has
precisely that additive kernel. -/
theorem periodProject_kernel_equiv (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val)
    (hperiod : ∀ z ∈ J.val, (P.epsilon - 1) * z ∈ I.val) :
    Nonempty (LatticeQuotient I J ≃+ (periodProject P I J hIJ).ker) := by
  let hzP (z : J.val.toAddSubgroup) : z.val ∈ pseudolatticePeriodPoints P I :=
    (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I z.val).mpr
      (hperiod z.val z.property)
  let q : J.val.toAddSubgroup →+ (periodProject P I J hIJ).ker :=
    { toFun := fun z => ⟨pseudolatticeMk P I z.val (hzP z),
        (periodProject_kernel_mk P I J hIJ z.val (hzP z)).mpr z.property⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hq : Function.Surjective q := by
    intro x
    let z := Quotient.out x.val
    have hzJ : z.val ∈ J.val := by
      apply (periodProject_kernel_mk P I J hIJ z.val z.property).mp
      have ho : pseudolatticeMk P I z.val z.property = x.val := Quotient.out_eq x.val
      exact ho.symm ▸ x.property
    refine ⟨⟨z.val, hzJ⟩, Subtype.ext ?_⟩
    exact Quotient.out_eq x.val
  have hker : q.ker = I.val.toAddSubgroup.comap J.val.toAddSubgroup.subtype := by
    ext z
    change q z = 0 ↔ z.val ∈ I.val
    rw [Subtype.ext_iff]
    exact DistributionSubgroupLatticeAux.mk_eq_zero_iff P I z.val (hzP z)
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective q hq)⟩

/-- [RW-rec, p. 8]: kernel cardinality is the actual lattice index D [J:I], using hperiod rather
than a surjectivity shortcut. -/
theorem periodProject_kernel_card (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val)
    (hperiod : ∀ z ∈ J.val, (P.epsilon - 1) * z ∈ I.val) :
    Nat.card (periodProject P I J hIJ).ker = inclusionIndex I.val J.val := by
  exact (Nat.card_congr
    (Classical.choice (periodProject_kernel_equiv P I J hIJ hperiod)).toEquiv).symm

/-- [RW-rec, p. 8]: because both period groups have N elements, the range has index D in G_J. The
map itself need not be surjective. -/
theorem periodProject_range_index (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val)
    (hperiod : ∀ z ∈ J.val, (P.epsilon - 1) * z ∈ I.val) :
    (periodProject P I J hIJ).range.index = inclusionIndex I.val J.val := by
  let φ := periodProject P I J hIJ
  have hcard : Nat.card (PseudolatticeGroup P I) = Nat.card (PseudolatticeGroup P J) :=
    (pseudolatticeGroup_finite_card P I).2.trans (pseudolatticeGroup_finite_card P J).2.symm
  have hker : Nat.card φ.ker * Nat.card φ.range = Nat.card (PseudolatticeGroup P I) := by
    rw [← AddSubgroup.index_ker]
    exact φ.ker.card_mul_index
  have heq : φ.range.index = Nat.card φ.ker := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card φ.range)
    rw [φ.range.card_mul_index, ← hcard, ← hker, Nat.mul_comm]
  exact heq.trans (periodProject_kernel_card P I J hIJ hperiod)

/-- [RW-rec, p. 8] bridge to the existing arbitrary-subgroup (11). The lattice rebuilt from the
literal kernel is the given upper lattice J. -/
theorem subgroupLattice_kernel_eq (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val)
    (hperiod : ∀ z ∈ J.val, (P.epsilon - 1) * z ∈ I.val) :
    DistributionSubgroups.subgroupLattice P I (periodProject P I J hIJ).ker = J := by
  apply Subtype.ext
  ext z
  change (∃ hz : z ∈ pseudolatticePeriodPoints P I,
    pseudolatticeMk P I z hz ∈ (periodProject P I J hIJ).ker) ↔ z ∈ J.val
  constructor
  · rintro ⟨hz, h⟩
    exact (periodProject_kernel_mk P I J hIJ z hz).mp h
  · intro hz
    have hzP := (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I z).mpr
      (hperiod z hz)
    exact ⟨hzP, (periodProject_kernel_mk P I J hIJ z hzP).mpr hz⟩

set_option maxHeartbeats 400000 in
/-- [RW-rec, p. 8]: take valuations in existing (11), using `distribution_subgroup` and
`subgroupLattice_kernel_eq`. Every eta multiplier is a root of unity, so its valuation is zero for
any v. No unit hypothesis on the E-values, and no cancellation of the origin, is assumed. -/
theorem weight_distribution (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val)
    (hperiod : ∀ z ∈ J.val, (P.epsilon - 1) * z ∈ I.val)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (x : PseudolatticeGroup P I) :
    weight P J v (periodProject P I J hIJ x) =
      ∑ h : (periodProject P I J hIJ).ker, weight P I v (x + h.val) := by
  let φ := periodProject P I J hIJ
  have hJ : DistributionSubgroups.subgroupLattice P I φ.ker = J :=
    subgroupLattice_kernel_eq P I J hIJ hperiod
  have hk : Nat.card φ.ker = inclusionIndex I.val J.val :=
    periodProject_kernel_card P I J hIJ hperiod
  have hvalue (L L' : StablePseudolattice P) (hIL : I.val ≤ L.val)
      (hIL' : I.val ≤ L'.val) (hLL' : L = L') :
      M72.value P L (periodProject P I L hIL x) =
        M72.value P L' (periodProject P I L' hIL' x) := by
    subst L'
    rfl
  have hproj : M72.value P (DistributionSubgroups.subgroupLattice P I φ.ker)
      (DistributionSubgroups.project P I φ.ker x) = M72.value P J (φ x) :=
    hvalue _ _ (DistributionSubgroups.le_overlattice P I φ.ker) hIJ hJ
  have hd : DistributionGeneral.distributionFactor P I J * M72.value P J (φ x) =
      ∏ h : φ.ker, M72.value P I (x + h.val) := by
    have hd' := DistributionNormalized.distribution_subgroup P I φ.ker x
    simp only [hproj, hJ, hk] at hd'
    exact hd'.trans (OddPrimeCharacterAverageAux.prod_univ_eq _ _ _ _)
  have hp : M72.value P J (φ x) ^ 24 =
      (∏ h : φ.ker, M72.value P I (x + h.val)) ^ 24 := by
    calc
      _ = (DistributionGeneral.distributionFactor P I J * M72.value P J (φ x)) ^ 24 := by
        rw [mul_pow, DistributionGeneral.distributionFactor_pow_twentyFour, one_mul]
      _ = _ := congrArg (fun a : ℂ => a ^ 24) hd
  have hl : lift P J (φ x) ^ 24 = (∏ h : φ.ker, lift P I (x + h.val)) ^ 24 := by
    apply Galois.embed.injective
    change Galois.embed (lift P J (φ x) ^ 24) =
      Galois.embed ((∏ h : φ.ker, lift P I (x + h.val)) ^ 24)
    rw [map_pow, map_pow, map_prod, embed_lift]
    simpa only [embed_lift] using hp
  have hprod (s : Finset φ.ker) :
      ValuationSupport.realValue v (∏ h ∈ s, lift P I (x + h.val)) =
        ∑ h ∈ s, weight P I v (x + h.val) := by
    induction s using Finset.induction_on with
    | empty => simp [ValuationSupport.realValue]
    | @insert h s hs ih =>
      rw [Finset.prod_insert hs, Finset.sum_insert hs,
        ValuationSupport.realValue_mul v (lift_ne_zero P I _)
          (Finset.prod_ne_zero_iff.mpr fun h _ => lift_ne_zero P I _), ih]
      rfl
  have hv := congrArg (ValuationSupport.realValue v) hl
  rw [ValuationSupport.realValue_pow v (lift_ne_zero P J _) 24,
    ValuationSupport.realValue_pow v
      (Finset.prod_ne_zero_iff.mpr fun h _ => lift_ne_zero P I _) 24,
    hprod] at hv
  exact nsmul_right_injective (by decide : (24 : ℕ) ≠ 0) hv

/-- [RW-rec, p. 8]: the finite family being averaged has exactly D members, including for a proper
image of the natural period map. -/
theorem periodProject_extension_card (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val)
    (hperiod : ∀ z ∈ J.val, (P.epsilon - 1) * z ∈ I.val)
    (θ : AddChar (PseudolatticeGroup P I) ℂ)
    (hθ : ∀ x ∈ (periodProject P I J hIJ).ker, θ x = 1) :
    (extensionFinset (periodProject P I J hIJ) θ).card =
      inclusionIndex I.val J.val := by
  exact (extensionFinset_card _ θ hθ).trans (periodProject_range_index P I J hIJ hperiod)

set_option maxHeartbeats 400000 in
/-- [RW-rec, Lemma 2, p. 8] for the actual M72 values and every v. The displayed sum is over all and
only compatible target characters; the denominator is the positive index D [J:I], not |G_I| or 1. -/
theorem lemma2_average (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val)
    (hperiod : ∀ z ∈ J.val, (P.epsilon - 1) * z ∈ I.val)
    (v : AddValuation Galois.Qbar (WithTop ℝ))
    (θ : AddChar (PseudolatticeGroup P I) ℂ)
    (hθ : ∀ x ∈ (periodProject P I J hIJ).ker, θ x = 1) :
    valuationFourier P I v θ =
      (inclusionIndex I.val J.val : ℂ)⁻¹ *
        ∑ χ ∈ Finset.univ.filter
          (fun χ : AddChar (PseudolatticeGroup P J) ℂ =>
            ∀ x : PseudolatticeGroup P I, χ (periodProject P I J hIJ x) = θ x),
          valuationFourier P J v χ := by
  have hcard : Nat.card (PseudolatticeGroup P I) = Nat.card (PseudolatticeGroup P J) :=
    (pseudolatticeGroup_finite_card P I).2.trans (pseudolatticeGroup_finite_card P J).2.symm
  simpa only [valuationFourier, realFourier, extensionFinset,
    periodProject_range_index P I J hIJ hperiod] using
    realFourier_extension_average (periodProject P I J hIJ) θ hcard hθ
      (Real.sqrt (P.N : ℝ) : ℂ)⁻¹ (weight P I v) (weight P J v)
      (fun x => (weight_distribution P I J hIJ hperiod v x).trans
        (OddPrimeCharacterAverageAux.sum_univ_eq _ _ _ _))

#check @AddChar.compAddMonoidHom
#check @MonoidHom.domRestrict_surjective
#check @periodProject_range_index
#check @lemma2_average
#print extensionFinset
#print realFourier

end SICLean.L5.OddPrimeCharacterAverage
