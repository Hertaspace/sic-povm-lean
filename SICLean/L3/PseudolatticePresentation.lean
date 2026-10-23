import SICLean.L3.Pseudolattice
import SICLean.L4.DistributionOrderTwo
import SICLean.L3.PseudolatticePresentationAux

set_option autoImplicit false

/-!
# Arithmetic lattices and the two-embedding model

Background formulas: [RW26, p. 2, (2)--(3)] and [RW26, p. 14, Prop. 9].

The arithmetic source is a full ℤ-lattice in K. No finiteness claim is made
for every `DistributionBasis.Valid` presentation with arbitrary real scales.
The quotient uses ε⁻¹ − 1, as in the distribution lattice.
-/

noncomputable section

open Set

namespace SICLean.L3

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The two specified embeddings of the same element of K. -/
def pseudolatticeEmbedding (P : PeriodData K) : K →+ ℝ × ℝ :=
  P.sigma₁.toAddMonoidHom.prod P.sigma₂.toAddMonoidHom

def pseudolatticeEmbeddingImage (P : PeriodData K) (I : Submodule ℤ K) :
    AddSubgroup (ℝ × ℝ) :=
  I.toAddSubgroup.map (pseudolatticeEmbedding P)

/-- The actual period points, not a quotient by the two-torsion subgroup. -/
def pseudolatticePeriodPoints (P : PeriodData K) (I : StablePseudolattice P) :
    AddSubgroup K :=
  I.val.toAddSubgroup.comap (AddMonoidHom.mulLeft (P.epsilon⁻¹ - 1))

/-- The quotient is formed in the period points. The inclusion I ≤ P
is `pseudolattice_le_periodPoints`. -/
abbrev PseudolatticeGroup (P : PeriodData K) (I : StablePseudolattice P) :=
  pseudolatticePeriodPoints P I ⧸
    I.val.toAddSubgroup.addSubgroupOf (pseudolatticePeriodPoints P I)

def pseudolatticeMk (P : PeriodData K) (I : StablePseudolattice P) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints P I) : PseudolatticeGroup P I :=
  QuotientAddGroup.mk (⟨x, hx⟩ : pseudolatticePeriodPoints P I)

def pseudolatticeRepresentative (P : PeriodData K) (I : StablePseudolattice P)
    (g : PseudolatticeGroup P I) : K :=
  (Quotient.out g).val

def pseudolatticeOverlattice (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) : Submodule ℤ K :=
  I.val ⊔ Submodule.span ℤ {pseudolatticeRepresentative P I h}

/-- A realization identifies the actual lattice and the common period.
It contains no analytic law, value algebraicity or family finiteness. -/
def PseudolatticePresentation (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) : Prop :=
  B.Valid ∧ L4.distributionPeriod B = P.sigma₁ P.epsilon ∧
    L4.distributionLattice B = pseudolatticeEmbeddingImage P I.val

/-- The two real embeddings are jointly injective. -/
theorem pseudolatticeEmbedding_injective (P : PeriodData K) :
    Function.Injective (pseudolatticeEmbedding P) := by
  intro x y h
  exact P.sigma₁.injective (congrArg Prod.fst h)

/-- No positivity is required for this equality of images. -/
theorem pseudolatticeEmbeddingImage_scale (P : PeriodData K)
    (lam : K) (I : Submodule ℤ K) :
    pseudolatticeEmbeddingImage P (pseudolatticeScale lam I) =
      (pseudolatticeEmbeddingImage P I).map
        (L4.distributionHomothety (pseudolatticeScales P lam)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff lam x I).mp hx
    refine ⟨pseudolatticeEmbedding P y, ⟨y, hy, rfl⟩, ?_⟩
    ext <;> simp [pseudolatticeEmbedding, L4.distributionHomothety,
      pseudolatticeScales]
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨lam * y, (pseudolatticeScale_mem_iff lam (lam * y) I).mpr
      ⟨y, hy, rfl⟩, ?_⟩
    ext <;> simp [pseudolatticeEmbedding, L4.distributionHomothety,
      pseudolatticeScales]

/-- Stability proves the full I <= P inclusion. -/
theorem pseudolattice_le_periodPoints (P : PeriodData K)
    (I : StablePseudolattice P) :
    I.val.toAddSubgroup ≤ pseudolatticePeriodPoints P I := by
  have hstable : pseudolatticeScale P.epsilon I.val = I.val := I.property.2
  have hinv : pseudolatticeScale P.epsilon⁻¹ I.val = I.val := by
    calc
      pseudolatticeScale P.epsilon⁻¹ I.val =
          pseudolatticeScale P.epsilon⁻¹ (pseudolatticeScale P.epsilon I.val) :=
        congrArg (pseudolatticeScale P.epsilon⁻¹) hstable.symm
      _ = I.val := (pseudolatticeScale_inv P.epsilon P.epsilon_ne_zero I.val).1
  intro x hx
  change (P.epsilon⁻¹ - 1) * x ∈ I.val
  rw [sub_mul, one_mul]
  refine I.val.sub_mem ?_ hx
  rw [← hinv]
  exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩

/-- Existence is a conclusion from the raw K-lattice, not a required field. -/
theorem exists_pseudolatticePresentation (P : PeriodData K)
    (I : StablePseudolattice P) :
    ∃ B : L4.DistributionBasis, PseudolatticePresentation P I B := by
  exact exists_distributionBasis_of_pseudolattice P I

/-- The image exhausts the real period points, not merely the lattice. -/
theorem pseudolatticePresentation_periodPoints (P : PeriodData K)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) :
    L4.distributionPeriodPoints B =
      (pseudolatticePeriodPoints P I).map (pseudolatticeEmbedding P) := by
  have hcomm (x : K) :
      L4.distributionPeriodDifference B (pseudolatticeEmbedding P x) =
        pseudolatticeEmbedding P ((P.epsilon⁻¹ - 1) * x) := by
    ext <;> simp [L4.distributionPeriodDifference, pseudolatticeEmbedding,
      hB.2.1, P.epsilon_conj]
  have hepspos : 0 < P.sigma₁ P.epsilon := lt_trans zero_lt_one P.epsilon_gt_one
  have hfirst : (P.sigma₁ P.epsilon)⁻¹ - 1 ≠ 0 := by
    have := (inv_lt_one₀ hepspos).mpr P.epsilon_gt_one
    linarith
  have hsecond : P.sigma₁ P.epsilon - 1 ≠ 0 := by
    linarith [P.epsilon_gt_one]
  have hdelta : P.epsilon⁻¹ - 1 ≠ 0 := by
    intro h
    apply hfirst
    simpa using congrArg P.sigma₁ h
  have hinj : Function.Injective (L4.distributionPeriodDifference B) := by
    intro x y h
    apply Prod.ext
    · exact mul_right_injective₀ hfirst
        (by simpa [L4.distributionPeriodDifference, hB.2.1] using congrArg Prod.fst h)
    · exact mul_right_injective₀ hsecond
        (by simpa [L4.distributionPeriodDifference, hB.2.1] using congrArg Prod.snd h)
  ext z
  constructor
  · intro hz
    change L4.distributionPeriodDifference B z ∈ L4.distributionLattice B at hz
    rw [hB.2.2] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    refine ⟨(P.epsilon⁻¹ - 1)⁻¹ * y, ?_, ?_⟩
    · change (P.epsilon⁻¹ - 1) * ((P.epsilon⁻¹ - 1)⁻¹ * y) ∈ I.val
      simpa [← mul_assoc, hdelta] using hy
    · apply hinj
      rw [hcomm]
      simpa [← mul_assoc, hdelta] using hyz
  · rintro ⟨x, hx, rfl⟩
    change L4.distributionPeriodDifference B (pseudolatticeEmbedding P x) ∈
      L4.distributionLattice B
    rw [hcomm, hB.2.2]
    exact ⟨(P.epsilon⁻¹ - 1) * x, hx, rfl⟩

/-- Callable point-membership bridge for the dependent mk formula below. -/
theorem pseudolatticePresentation_point_mem (P : PeriodData K)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeEmbedding P x ∈ L4.distributionPeriodPoints B := by
  rw [pseudolatticePresentation_periodPoints P I B hB]
  exact ⟨x, hx, rfl⟩

/-- The equation on all representatives determines the identification. -/
theorem pseudolatticeGroup_equiv_exists (P : PeriodData K)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) :
    ∃ e : PseudolatticeGroup P I ≃+ L4.DistributionGroup B,
      ∀ (x : K) (hx : x ∈ pseudolatticePeriodPoints P I),
        e (pseudolatticeMk P I x hx) =
          L4.distributionMk B (pseudolatticeEmbedding P x)
            (pseudolatticePresentation_point_mem P I B hB x hx) := by
  let f : pseudolatticePeriodPoints P I →+ L4.distributionPeriodPoints B :=
    { toFun := fun x => ⟨pseudolatticeEmbedding P x.val,
        pseudolatticePresentation_point_mem P I B hB x.val x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.val y.val) }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (pseudolatticeEmbedding_injective P (congrArg Subtype.val h))
    · intro y
      have hy : y.val ∈ (pseudolatticePeriodPoints P I).map (pseudolatticeEmbedding P) := by
        simpa only [pseudolatticePresentation_periodPoints P I B hB] using y.property
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := AddEquiv.ofBijective f hf
  have he : (I.val.toAddSubgroup.addSubgroupOf (pseudolatticePeriodPoints P I)).map
      e.toAddMonoidHom =
      (L4.distributionLattice B).addSubgroupOf (L4.distributionPeriodPoints B) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change pseudolatticeEmbedding P x.val ∈ L4.distributionLattice B
      rw [hB.2.2]
      exact ⟨x.val, hx, rfl⟩
    · intro hy
      change y.val ∈ L4.distributionLattice B at hy
      rw [hB.2.2] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, pseudolattice_le_periodPoints P I hx⟩, hx, Subtype.ext hxy⟩
  refine ⟨QuotientAddGroup.congr _ _ e he, ?_⟩
  intro x hx
  rfl

def pseudolatticeGroupEquiv (P : PeriodData K) (I : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B) :
    PseudolatticeGroup P I ≃+ L4.DistributionGroup B :=
  Classical.choose (pseudolatticeGroup_equiv_exists P I B hB)

/-- The chosen equivalence has the specified representative formula. -/
theorem pseudolatticeGroupEquiv_mk (P : PeriodData K)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeGroupEquiv P I B hB (pseudolatticeMk P I x hx) =
      L4.distributionMk B (pseudolatticeEmbedding P x)
        (pseudolatticePresentation_point_mem P I B hB x hx) := by
  exact Classical.choose_spec (pseudolatticeGroup_equiv_exists P I B hB) x hx

/--
Every group has N elements.
This includes even N and trivial groups at N=1.
-/
theorem pseudolatticeGroup_finite_card (P : PeriodData K)
    (I : StablePseudolattice P) :
    Finite (PseudolatticeGroup P I) ∧ Nat.card (PseudolatticeGroup P I) = P.N := by
  obtain ⟨B, hB⟩ := exists_pseudolatticePresentation P I
  let e := pseudolatticeGroupEquiv P I B hB
  obtain ⟨hfinite, hcard⟩ := L4.distributionGroup_finite_card B hB.1
  have := hfinite
  refine ⟨Finite.of_equiv _ e.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e.toEquiv, hcard]
  have heps : P.sigma₁ P.epsilon ≠ 0 := ne_of_gt (lt_trans zero_lt_one P.epsilon_gt_one)
  have hpoly := congrArg P.sigma₁ P.epsilon_polynomial
  simp only [map_add, map_sub, map_pow, map_mul, map_natCast, map_ofNat, map_one,
    map_zero] at hpoly
  have htrace := (L4.distributionBasis_spectral B hB.1).2.2.2
  rw [hB.2.1] at htrace
  have hreal : (B.matrix 0 0 : ℝ) + (B.matrix 1 1 : ℝ) - 2 = (P.N : ℝ) := by
    field_simp at htrace
    nlinarith
  have hint : B.matrix 0 0 + B.matrix 1 1 - 2 = (P.N : ℤ) := by
    exact_mod_cast hreal
  rw [hint, Int.toNat_natCast]

/-- Arbitrary lifts give the same K-overlattice. -/
theorem pseudolatticeOverlattice_lift (P : PeriodData K)
    (I : StablePseudolattice P) (h : PseudolatticeGroup P I) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints P I) (he : pseudolatticeMk P I x hx = h) :
    pseudolatticeOverlattice P I h = I.val ⊔ Submodule.span ℤ {x} := by
  have hq : pseudolatticeMk P I (pseudolatticeRepresentative P I h)
      (Quotient.out h).property = pseudolatticeMk P I x hx := by
    exact (Quotient.out_eq h).trans he.symm
  have hdiff : pseudolatticeRepresentative P I h - x ∈ I.val :=
    QuotientAddGroup.eq_iff_sub_mem.mp hq
  have hle (y z : K) (hyz : y - z ∈ I.val) :
      I.val ⊔ Submodule.span ℤ {y} ≤ I.val ⊔ Submodule.span ℤ {z} := by
    refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    have h₁ : y - z ∈ I.val ⊔ Submodule.span ℤ {z} :=
      (show I.val ≤ I.val ⊔ Submodule.span ℤ {z} from le_sup_left) hyz
    have h₂ : z ∈ I.val ⊔ Submodule.span ℤ {z} :=
      (show Submodule.span ℤ {z} ≤ I.val ⊔ Submodule.span ℤ {z} from le_sup_right)
        (Submodule.mem_span_singleton_self z)
    simpa using (I.val ⊔ Submodule.span ℤ {z}).add_mem h₁ h₂
  exact le_antisymm (hle _ _ hdiff)
    (hle _ _ (by simpa only [neg_sub] using I.val.neg_mem hdiff))

/-- I ≤ J ≤ (1/2) I in K. -/
theorem pseudolatticeOverlattice_bounds (P : PeriodData K)
    (I : StablePseudolattice P) (h : PseudolatticeGroup P I)
    (hh : h ≠ 0 ∧ h + h = 0) :
    I.val ≤ pseudolatticeOverlattice P I h ∧
      ∀ x ∈ pseudolatticeOverlattice P I h, (2 : ℤ) • x ∈ I.val := by
  have hq : (QuotientAddGroup.mk (Quotient.out h + Quotient.out h) :
      PseudolatticeGroup P I) = 0 := by
    rw [QuotientAddGroup.mk_add]
    simpa only [Quotient.out_eq] using hh.2
  have hr : (2 : ℤ) • pseudolatticeRepresentative P I h ∈ I.val := by
    have hm := (QuotientAddGroup.eq_zero_iff _).mp hq
    change pseudolatticeRepresentative P I h + pseudolatticeRepresentative P I h ∈ I.val at hm
    simpa only [two_zsmul] using hm
  refine ⟨le_sup_left, ?_⟩
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [smul_add, smul_comm (2 : ℤ) n]
  exact I.val.add_mem (I.val.smul_mem _ hy) (I.val.smul_mem _ hr)

/-- No invertibility as a Z[epsilon]-ideal is imposed. -/
theorem pseudolatticeOverlattice_isLattice (P : PeriodData K)
    (I : StablePseudolattice P) (h : PseudolatticeGroup P I)
    (hh : h ≠ 0 ∧ h + h = 0) :
    Submodule.IsLattice ℚ (pseudolatticeOverlattice P I h) := by
  let := I.property.1
  refine ⟨I.property.1.fg.sup (Submodule.fg_span_singleton _), ?_⟩
  apply top_unique
  rw [← Submodule.IsLattice.span_eq_top (A := ℚ) (M := I.val)]
  exact Submodule.span_mono (show (I.val : Set K) ⊆
    (pseudolatticeOverlattice P I h : Set K) from
      fun _ hx => (show I.val ≤ pseudolatticeOverlattice P I h from le_sup_left) hx)

/-- ε J = J, using both ε and ε⁻¹. -/
theorem pseudolatticeOverlattice_periodStable (P : PeriodData K)
    (I : StablePseudolattice P) (h : PseudolatticeGroup P I)
    (hh : h ≠ 0 ∧ h + h = 0) :
    PeriodStable P (pseudolatticeOverlattice P I h) := by
  let J := pseudolatticeOverlattice P I h
  let r := pseudolatticeRepresentative P I h
  have hstable : pseudolatticeScale P.epsilon I.val = I.val := I.property.2
  have hinv : pseudolatticeScale P.epsilon⁻¹ I.val = I.val := by
    calc
      pseudolatticeScale P.epsilon⁻¹ I.val =
          pseudolatticeScale P.epsilon⁻¹ (pseudolatticeScale P.epsilon I.val) :=
        congrArg (pseudolatticeScale P.epsilon⁻¹) hstable.symm
      _ = I.val := (pseudolatticeScale_inv P.epsilon P.epsilon_ne_zero I.val).1
  have hmulI (a : K) (ha : pseudolatticeScale a I.val = I.val)
      (x : K) (hx : x ∈ I.val) : a * x ∈ I.val := by
    rw [← ha]
    exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩
  have hr : P.epsilon⁻¹ * r - r ∈ I.val := by
    have hx := (Quotient.out h).property
    change (P.epsilon⁻¹ - 1) * r ∈ I.val at hx
    simpa only [sub_mul, one_mul] using hx
  have hrmem : r ∈ J :=
    (show Submodule.span ℤ {r} ≤ J from le_sup_right) (Submodule.mem_span_singleton_self r)
  have hrinv : P.epsilon⁻¹ * r ∈ J := by
    simpa using J.add_mem
      (show P.epsilon⁻¹ * r - r ∈ J from (show I.val ≤ J from le_sup_left) hr) hrmem
  have hreps : P.epsilon * r ∈ J := by
    have hm := hmulI P.epsilon hstable _ hr
    have heq : P.epsilon * (P.epsilon⁻¹ * r - r) = r - P.epsilon * r := by
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ P.epsilon_ne_zero, one_mul]
    rw [heq] at hm
    have hmJ : r - P.epsilon * r ∈ J := (show I.val ≤ J from le_sup_left) hm
    simpa using J.sub_mem hrmem hmJ
  have hmulJ (a : K) (ha : pseudolatticeScale a I.val = I.val)
      (har : a * r ∈ J) : pseudolatticeScale a J ≤ J := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff a x J).mp hx
    obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [mul_add, mul_smul_comm]
    exact J.add_mem ((show I.val ≤ J from le_sup_left) (hmulI a ha z hz))
      (J.smul_mem n har)
  change pseudolatticeScale P.epsilon J = J
  refine le_antisymm (hmulJ P.epsilon hstable hreps) ?_
  intro x hx
  refine (pseudolatticeScale_mem_iff _ _ _).mpr ⟨P.epsilon⁻¹ * x, ?_, ?_⟩
  · exact hmulJ P.epsilon⁻¹ hinv hrinv
      ((pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩)
  · rw [← mul_assoc, mul_inv_cancel₀ P.epsilon_ne_zero, one_mul]

def stablePseudolatticeOverlattice (P : PeriodData K) (I : StablePseudolattice P)
    (h : PseudolatticeGroup P I) (hh : h ≠ 0 ∧ h + h = 0) :
    StablePseudolattice P :=
  ⟨pseudolatticeOverlattice P I h,
    pseudolatticeOverlattice_isLattice P I h hh,
    pseudolatticeOverlattice_periodStable P I h hh⟩

/-- The K-extension agrees with the distribution-lattice extension, for
either choice of `Quotient.out`. -/
theorem pseudolatticePresentation_overlattice (P : PeriodData K)
    (I : StablePseudolattice P) (B : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) (h : PseudolatticeGroup P I) :
    pseudolatticeEmbeddingImage P (pseudolatticeOverlattice P I h) =
      L4.distributionOverlattice B (pseudolatticeGroupEquiv P I B hB h) := by
  have he : L4.distributionMk B
      (pseudolatticeEmbedding P (pseudolatticeRepresentative P I h))
      (pseudolatticePresentation_point_mem P I B hB _ (Quotient.out h).property) =
        pseudolatticeGroupEquiv P I B hB h := by
    rw [← pseudolatticeGroupEquiv_mk P I B hB]
    congr 1
    exact Quotient.out_eq h
  rw [L4.distributionOverlattice_lift B hB.1 _ _ _ he]
  change (I.val ⊔ Submodule.span ℤ {pseudolatticeRepresentative P I h}).toAddSubgroup.map
    (pseudolatticeEmbedding P) = _
  rw [Submodule.sup_toAddSubgroup, AddSubgroup.map_sup,
    Submodule.span_int_eq_addSubgroupClosure, ← AddSubgroup.zmultiples_eq_closure,
    AddMonoidHom.map_zmultiples]
  rw [hB.2.2]
  rfl

#check @L4.distributionBasisFromEmbeddings_valid
#check @L4.distribution_exists_overlattice_basis
#check @Submodule.IsLattice
#print PseudolatticePresentation
#print pseudolatticeOverlattice
#check pseudolatticePresentation_overlattice

end SICLean.L3
