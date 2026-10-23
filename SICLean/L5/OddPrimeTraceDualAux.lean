import SICLean.L5.DistributionSubgroupLattice
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.Group.AddChar
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option autoImplicit false

noncomputable section

open scoped Classical
open SICLean.L3
open Module

namespace SICLean.L5.OddPrimeTraceDualAux

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The trace phase, before passing to any quotient. -/
def phase (a x : K) : ℂ :=
  L4.e ((Algebra.trace ℚ K (a * x) : ℚ) : ℂ)

theorem phase_zero_right (a : K) : phase a 0 = 1 := by
  simp [phase, L4.e]

theorem phase_zero_left (x : K) : phase 0 x = 1 := by
  simp [phase, L4.e]

theorem phase_add_right (a x y : K) : phase a (x + y) = phase a x * phase a y := by
  simp only [phase, mul_add, map_add, Rat.cast_add, L4.e_add']

theorem phase_add_left (a b x : K) : phase (a + b) x = phase a x * phase b x := by
  simp only [phase, add_mul, map_add, Rat.cast_add, L4.e_add']

theorem phase_eq_one_iff (a x : K) :
    phase a x = 1 ↔ Algebra.trace ℚ K (a * x) ∈ (algebraMap ℤ ℚ).range := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := L4.e_eq_one_iff_int h
    refine ⟨n, ?_⟩
    change (n : ℚ) = Algebra.trace ℚ K (a * x)
    exact_mod_cast hn.symm
  · rintro ⟨n, hn⟩
    change L4.e ((Algebra.trace ℚ K (a * x) : ℚ) : ℂ) = 1
    rw [← hn]
    simpa using L4.e_intCast n

theorem phase_eq_of_sub_mem (I : Submodule ℤ K)
    (a : Submodule.traceDual ℤ ℚ I) (x y : K) (hxy : x - y ∈ I) :
    phase a.val x = phase a.val y := by
  have h : phase a.val (x - y) = 1 :=
    (phase_eq_one_iff _ _).mpr ((Submodule.mem_traceDual.mp a.property) _ hxy)
  calc
    phase a.val x = phase a.val ((x - y) + y) := by rw [sub_add_cancel]
    _ = phase a.val (x - y) * phase a.val y := phase_add_right _ _ _
    _ = phase a.val y := by rw [h, one_mul]

theorem phase_representative (P : PeriodData K) (I : StablePseudolattice P)
    (a : Submodule.traceDual ℤ ℚ I.val) (x : K)
    (hx : x ∈ pseudolatticePeriodPoints P I) :
    phase a.val (pseudolatticeRepresentative P I (pseudolatticeMk P I x hx)) =
      phase a.val x := by
  apply phase_eq_of_sub_mem I.val a
  exact QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq
    (pseudolatticeMk P I x hx))

/-- Stability identifies the two signs of the period relation. -/
theorem scale_period_relation (P : PeriodData K) (J : Submodule ℤ K)
    (hJ : PeriodStable P J) :
    pseudolatticeScale (P.epsilon - 1) J =
      pseudolatticeScale (P.epsilon⁻¹ - 1) J := by
  have heps (x : K) (hx : x ∈ J) : P.epsilon * x ∈ J := by
    rw [← hJ]
    exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩
  have hinv : pseudolatticeScale P.epsilon⁻¹ J = J := by
    calc
      pseudolatticeScale P.epsilon⁻¹ J =
          pseudolatticeScale P.epsilon⁻¹ (pseudolatticeScale P.epsilon J) :=
        congrArg (pseudolatticeScale P.epsilon⁻¹) hJ.symm
      _ = J := (pseudolatticeScale_inv P.epsilon P.epsilon_ne_zero J).1
  have hepsinv (x : K) (hx : x ∈ J) : P.epsilon⁻¹ * x ∈ J := by
    rw [← hinv]
    exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩
  ext z
  simp only [pseudolatticeScale_mem_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨-(P.epsilon * x), J.neg_mem (heps x hx), ?_⟩
    calc
      (P.epsilon⁻¹ - 1) * -(P.epsilon * x) =
          (-(P.epsilon⁻¹ * P.epsilon) + P.epsilon) * x := by ring
      _ = (P.epsilon - 1) * x := by rw [inv_mul_cancel₀ P.epsilon_ne_zero]; ring
  · rintro ⟨x, hx, rfl⟩
    refine ⟨-(P.epsilon⁻¹ * x), J.neg_mem (hepsinv x hx), ?_⟩
    calc
      (P.epsilon - 1) * -(P.epsilon⁻¹ * x) =
          (-(P.epsilon * P.epsilon⁻¹) + P.epsilon⁻¹) * x := by ring
      _ = (P.epsilon⁻¹ - 1) * x := by rw [mul_inv_cancel₀ P.epsilon_ne_zero]; ring

lemma lattice_basis (I : Submodule ℤ K) (hI : Submodule.IsLattice ℚ I) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℚ K,
      I = Submodule.span ℤ (Set.range b) := by
  let := hI
  let bz := Module.finBasis ℤ I
  let b := bz.extendOfIsLattice ℚ
  refine ⟨b.reindex (b.indexEquiv (Module.finBasis ℚ K)), ?_⟩
  rw [Basis.range_reindex]
  have hb : Submodule.span ℤ (Set.range (fun i => (bz i).val)) = I := by
    change Submodule.span ℤ (Set.range (I.subtype ∘ bz)) = I
    rw [Set.range_comp, ← Submodule.map_span, bz.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hbr : (b : _ → K) = (fun i => (bz i).val) := by
    funext i
    exact Basis.extendOfIsLattice_apply ℚ bz i
  rw [hbr]
  exact hb.symm

lemma traceDual_isLattice (I : Submodule ℤ K) (hI : Submodule.IsLattice ℚ I) :
    Submodule.IsLattice ℚ (Submodule.traceDual ℤ ℚ I) := by
  obtain ⟨b, hb⟩ := lattice_basis I hI
  have hd : Submodule.traceDual ℤ ℚ I = Submodule.span ℤ (Set.range b.traceDual) :=
    Submodule.traceDual_span_of_basis ℤ I b hb
  rw [hd]
  constructor
  · exact Submodule.fg_span (Set.finite_range _)
  · rw [Submodule.span_span_of_tower ℤ, b.traceDual.span_eq]

lemma traceDual_traceDual (I : Submodule ℤ K) (hI : Submodule.IsLattice ℚ I) :
    Submodule.traceDual ℤ ℚ (Submodule.traceDual ℤ ℚ I) = I := by
  obtain ⟨b, hb⟩ := lattice_basis I hI
  have hd : Submodule.traceDual ℤ ℚ I = Submodule.span ℤ (Set.range b.traceDual) :=
    Submodule.traceDual_span_of_basis ℤ I b hb
  calc
    Submodule.traceDual ℤ ℚ (Submodule.traceDual ℤ ℚ I) =
        Submodule.span ℤ (Set.range b.traceDual.traceDual) :=
      Submodule.traceDual_span_of_basis ℤ _ b.traceDual hd
    _ = I := by rw [b.traceDual_traceDual, ← hb]

lemma traceDual_changeMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Basis ι ℚ K) :
    b.traceDual.toMatrix c.traceDual = (c.toMatrix b).transpose := by
  ext i j
  simp only [Basis.toMatrix_apply, Basis.traceDual_repr_apply, Matrix.transpose_apply]
  have he := Basis.traceDual_repr_apply c.traceDual (b i) j
  rw [c.traceDual_traceDual] at he
  rw [he]
  simp only [Algebra.traceForm_apply, mul_comm]

lemma traceDual_index (I J : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (hJ : Submodule.IsLattice ℚ J) (hIJ : I ≤ J) :
    DistributionOrbitGeometry.inclusionIndex (Submodule.traceDual ℤ ℚ J)
      (Submodule.traceDual ℤ ℚ I) =
      DistributionOrbitGeometry.inclusionIndex I J := by
  obtain ⟨b, hb⟩ := lattice_basis I hI
  obtain ⟨c, hc⟩ := lattice_basis J hJ
  have hdb : Submodule.traceDual ℤ ℚ I = Submodule.span ℤ (Set.range b.traceDual) :=
    Submodule.traceDual_span_of_basis ℤ I b hb
  have hdc : Submodule.traceDual ℤ ℚ J = Submodule.span ℤ (Set.range c.traceDual) :=
    Submodule.traceDual_span_of_basis ℤ J c hc
  have hanti : Submodule.traceDual ℤ ℚ J ≤ Submodule.traceDual ℤ ℚ I := by
    intro x hx
    exact Submodule.mem_traceDual.mpr (fun y hy => Submodule.mem_traceDual.mp hx y (hIJ hy))
  have hb' : I.toAddSubgroup = AddSubgroup.closure (Set.range b) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]
    exact hb
  have hc' : J.toAddSubgroup = AddSubgroup.closure (Set.range c) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]
    exact hc
  have hdb' : (Submodule.traceDual ℤ ℚ I).toAddSubgroup =
      AddSubgroup.closure (Set.range b.traceDual) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]
    exact hdb
  have hdc' : (Submodule.traceDual ℤ ℚ J).toAddSubgroup =
      AddSubgroup.closure (Set.range c.traceDual) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]
    exact hdc
  apply Nat.cast_injective (R := ℚ)
  change ((Submodule.traceDual ℤ ℚ J).toAddSubgroup.relIndex
      (Submodule.traceDual ℤ ℚ I).toAddSubgroup : ℚ) =
      (I.toAddSubgroup.relIndex J.toAddSubgroup : ℚ)
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hanti c.traceDual b.traceDual hdc' hdb',
    AddSubgroup.relIndex_eq_abs_det _ _ hIJ b c hb' hc']
  simp only [Basis.det_apply, traceDual_changeMatrix, Matrix.det_transpose]


/-- Trace duality exchanges a nonzero field homothety with its inverse. This uses arbitrary integer
submodules and needs no maximal-order hypothesis. -/
theorem traceDual_scale (I : Submodule ℤ K) (c : K) (hc : c ≠ 0) :
    Submodule.traceDual ℤ ℚ (pseudolatticeScale c I) =
      pseudolatticeScale c⁻¹ (Submodule.traceDual ℤ ℚ I) := by
  ext a
  constructor
  · intro ha
    apply (pseudolatticeScale_mem_iff _ _ _).mpr
    refine ⟨c * a, ?_, ?_⟩
    · apply Submodule.mem_traceDual.mpr
      intro x hx
      have hcx : c * x ∈ pseudolatticeScale c I :=
        (pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩
      have h := Submodule.mem_traceDual.mp ha (c * x) hcx
      simpa only [Algebra.traceForm_apply, mul_assoc, mul_left_comm, mul_comm] using h
    · simp [hc]
  · rintro ha
    obtain ⟨b, hb, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp ha
    apply Submodule.mem_traceDual.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
    have h := Submodule.mem_traceDual.mp hb y hy
    simpa only [Algebra.traceForm_apply, mul_mul_mul_comm, inv_mul_cancel₀ hc,
      one_mul] using h

/-- The annihilator of the inverse image under multiplication by `c` is exactly `c` times the
original trace dual. -/
theorem trace_integral_on_mul_preimage_iff (I : Submodule ℤ K) (c : K)
    (hc : c ≠ 0) (a : K) :
    (∀ x : K, c * x ∈ I →
      Algebra.trace ℚ K (a * x) ∈ (algebraMap ℤ ℚ).range) ↔
        a ∈ pseudolatticeScale c (Submodule.traceDual ℤ ℚ I) := by
  constructor
  · intro ha
    apply (pseudolatticeScale_mem_iff _ _ _).mpr
    refine ⟨c⁻¹ * a, ?_, ?_⟩
    · apply Submodule.mem_traceDual.mpr
      intro x hx
      have h := ha (c⁻¹ * x) (by simpa [← mul_assoc, hc] using hx)
      simpa only [Algebra.traceForm_apply, mul_assoc, mul_left_comm, mul_comm] using h
    · simp [hc]
  · intro ha x hx
    obtain ⟨b, hb, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp ha
    have h := Submodule.mem_traceDual.mp hb (c * x) hx
    simpa only [Algebra.traceForm_apply, mul_assoc, mul_left_comm, mul_comm] using h

/-- Nonvanishing of the period difference, from its specified real embedding. -/
theorem epsilon_sub_one_ne_zero (P : PeriodData K) : P.epsilon - 1 ≠ 0 := by
  intro h
  have he : P.epsilon = 1 := sub_eq_zero.mp h
  have hpos := P.epsilon_gt_one
  simp [he] at hpos

/-- The full trace-annihilator criterion for the actual period points. The inverse-period convention
is converted by the already verified period-point membership identity. -/
theorem trace_integral_on_periodPoints_iff (P : PeriodData K)
    (I : StablePseudolattice P) (a : K) :
    (∀ x ∈ pseudolatticePeriodPoints P I,
      Algebra.trace ℚ K (a * x) ∈ (algebraMap ℤ ℚ).range) ↔
        a ∈ pseudolatticeScale (P.epsilon - 1)
          (Submodule.traceDual ℤ ℚ I.val) := by
  simpa only [DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem] using
    trace_integral_on_mul_preimage_iff I.val (P.epsilon - 1)
      (epsilon_sub_one_ne_zero P) a

/-- Multiplication by the period difference identifies the period points with the lattice itself. -/
def periodPointsMulEquiv (P : PeriodData K) (I : StablePseudolattice P) :
    pseudolatticePeriodPoints P I ≃+ I.val where
  toFun x := ⟨(P.epsilon - 1) * x.val,
    (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I x.val).mp x.property⟩
  invFun x := ⟨(P.epsilon - 1)⁻¹ * x.val, by
    apply (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I _).mpr
    simp [epsilon_sub_one_ne_zero P]⟩
  left_inv x := by
    apply Subtype.ext
    simp [epsilon_sub_one_ne_zero P]
  right_inv x := by
    apply Subtype.ext
    simp [epsilon_sub_one_ne_zero P]
  map_add' x y := by
    apply Subtype.ext
    exact mul_add _ _ _

/-- The multiplication equivalence sends the original relation subgroup to the literal
`(epsilon - 1)I` inside `I`. -/
theorem periodPointsMulEquiv_map_lattice (P : PeriodData K)
    (I : StablePseudolattice P) :
    (I.val.toAddSubgroup.addSubgroupOf (pseudolatticePeriodPoints P I)).map
        (periodPointsMulEquiv P I).toAddMonoidHom =
      (pseudolatticeScale (P.epsilon - 1) I.val).toAddSubgroup.comap
        I.val.toAddSubgroup.subtype := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨y.val, hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
    exact ⟨⟨y, pseudolattice_le_periodPoints P I hy⟩, hy, Subtype.ext hxy⟩

/-- `I/(epsilon - 1)I` is the already existing actual period quotient. -/
def periodCokernelEquiv (P : PeriodData K) (I : StablePseudolattice P) :
    (I.val ⧸ (pseudolatticeScale (P.epsilon - 1) I.val).toAddSubgroup.comap
      I.val.toAddSubgroup.subtype) ≃+ PseudolatticeGroup P I :=
  (QuotientAddGroup.congr _ _ (periodPointsMulEquiv P I)
    (periodPointsMulEquiv_map_lattice P I)).symm

/-- The literal period cokernel is finite and has cardinality `P.N`. -/
theorem periodCokernel_finite_card (P : PeriodData K) (I : StablePseudolattice P) :
    Finite (I.val ⧸
      (pseudolatticeScale (P.epsilon - 1) I.val).toAddSubgroup.comap
        I.val.toAddSubgroup.subtype) ∧
    Nat.card (I.val ⧸
      (pseudolatticeScale (P.epsilon - 1) I.val).toAddSubgroup.comap
        I.val.toAddSubgroup.subtype) = P.N := by
  obtain ⟨hfinite, hcard⟩ := pseudolatticeGroup_finite_card P I
  have := hfinite
  exact ⟨Finite.of_equiv _ (periodCokernelEquiv P I).symm.toEquiv,
    (Nat.card_congr (periodCokernelEquiv P I).toEquiv).trans hcard⟩

section CharacterCardinality

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]

/-- For finite abelian groups of the same order, an injective complex character homomorphism is
bijective by the character-counting theorem. -/
theorem characterHom_bijective_of_injective_of_card
    (f : A →+ AddChar B ℂ) (hf : Function.Injective f)
    (hcard : Nat.card A = Nat.card B) : Function.Bijective f := by
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hf, ?_⟩
  rw [AddChar.card_eq]
  simpa only [Nat.card_eq_fintype_card] using hcard

end CharacterCardinality


/-- A full integer lattice in a nontrivial number field has a nonzero element. -/
theorem exists_nonzero_lattice_element (I : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) : ∃ a : I, a.val ≠ 0 := by
  have hIne : I ≠ ⊥ := by
    intro hIbot
    have hspan := hI.span_eq_top
    rw [hIbot] at hspan
    have hone : (1 : K) ∈ Submodule.span ℚ ((⊥ : Submodule ℤ K) : Set K) := by
      rw [hspan]
      trivial
    simp at hone
  obtain ⟨a, ha, hane⟩ := I.ne_bot_iff.mp hIne
  exact ⟨⟨a, ha⟩, hane⟩

/-- A nonzero homothety of a full lattice contains a nonzero element. -/
theorem exists_nonzero_scaled_lattice_element (I : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (c : K) (hc : c ≠ 0) :
    ∃ a : K, a ∈ pseudolatticeScale c I ∧ a ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_nonzero_lattice_element I hI
  exact ⟨c * a.val, (pseudolatticeScale_mem_iff _ _ _).mpr
    ⟨a.val, a.property, rfl⟩, mul_ne_zero hc ha⟩

/-- Stability makes the period relation a genuine sublattice of the lattice. -/
theorem scale_period_sub_one_le (P : PeriodData K) (I : Submodule ℤ K)
    (hI : PeriodStable P I) : pseudolatticeScale (P.epsilon - 1) I ≤ I := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
  rw [sub_mul, one_mul]
  apply I.sub_mem _ hy
  rw [← hI]
  exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨y, hy, rfl⟩

/-- A full stable lattice has a nonzero literal period relation. This supplies a nonzero label even
for the trivial character. -/
theorem exists_nonzero_period_relation (P : PeriodData K) (I : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (hstable : PeriodStable P I) :
    ∃ a : I, a.val ≠ 0 ∧ a.val ∈ pseudolatticeScale (P.epsilon - 1) I := by
  obtain ⟨a, ha, hane⟩ := exists_nonzero_scaled_lattice_element I hI
    (P.epsilon - 1) (epsilon_sub_one_ne_zero P)
  exact ⟨⟨a, scale_period_sub_one_le P I hstable ha⟩, hane, ha⟩

/-- A surjective homomorphism with a nonzero kernel element admits nonzero representatives of all
target elements, including zero. -/
theorem exists_nonzero_preimage {A B : Type*} [AddGroup A] [AddGroup B]
    (f : A →+ B) (hf : Function.Surjective f)
    (hker : ∃ a : A, a ≠ 0 ∧ f a = 0) (b : B) :
    ∃ a : A, a ≠ 0 ∧ f a = b := by
  by_cases hb : b = 0
  · obtain ⟨a, ha, hfa⟩ := hker
    exact ⟨a, ha, hfa.trans hb.symm⟩
  · obtain ⟨a, hfa⟩ := hf b
    refine ⟨a, ?_, hfa⟩
    intro ha
    apply hb
    simpa [ha] using hfa.symm


section FiniteCharacterDuality

universe v

variable {G : Type u} {D : Type v} [AddCommGroup G] [AddCommGroup D]

def characterPrecompEquiv (e : D ≃+ G) : AddChar G ℂ ≃+ AddChar D ℂ where
  toFun ψ := ψ.compAddMonoidHom e.toAddMonoidHom
  invFun ψ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  left_inv ψ := by ext x; simp
  right_inv ψ := by ext x; simp
  map_add' ψ χ := by ext x; rfl

def pairingEquiv [Finite G] (e : D ≃+ AddChar G ℂ) : G ≃+ AddChar D ℂ :=
  AddChar.doubleDualEquiv.trans (characterPrecompEquiv e)

@[simp] theorem pairingEquiv_apply [Finite G] (e : D ≃+ AddChar G ℂ) (g : G) (d : D) :
    pairingEquiv e g d = e d g := rfl

def characterKernel (ψ : AddChar G ℂ) : AddSubgroup G := ψ.toAddMonoidHom.ker

@[simp] theorem mem_characterKernel (ψ : AddChar G ℂ) (g : G) :
    g ∈ characterKernel ψ ↔ ψ g = 1 := Iff.rfl

def characterKernelEquivQuotientDual [Finite G] (e : D ≃+ AddChar G ℂ) (a : D) :
    characterKernel (e a) ≃ AddChar (D ⧸ AddSubgroup.zmultiples a) ℂ where
  toFun g := AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift (AddSubgroup.zmultiples a)
      (pairingEquiv e g.val).toAddMonoidHom
      (AddSubgroup.zmultiples_le.mpr g.property)
  invFun ψ := ⟨(pairingEquiv e).symm
    (ψ.compAddMonoidHom (QuotientAddGroup.mk' (AddSubgroup.zmultiples a))), by
      change e a ((pairingEquiv e).symm _) = 1
      rw [← pairingEquiv_apply, AddEquiv.apply_symm_apply]
      change ψ (QuotientAddGroup.mk a) = 1
      rw [show (QuotientAddGroup.mk a : D ⧸ AddSubgroup.zmultiples a) = 0 from
        (QuotientAddGroup.eq_zero_iff a).mpr (AddSubgroup.mem_zmultiples a)]
      exact ψ.map_zero_eq_one⟩
  left_inv g := by
    apply Subtype.ext
    apply (pairingEquiv e).injective
    rw [AddEquiv.apply_symm_apply]
    ext d
    rfl
  right_inv ψ := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H d =>
      change (pairingEquiv e ((pairingEquiv e).symm
        (ψ.compAddMonoidHom (QuotientAddGroup.mk' (AddSubgroup.zmultiples a))))) d = _
      simp

theorem characterKernel_card [Finite G] [Finite D] (e : D ≃+ AddChar G ℂ) (a : D) :
    Nat.card (characterKernel (e a)) = Nat.card (D ⧸ AddSubgroup.zmultiples a) := by
  rw [Nat.card_congr (characterKernelEquivQuotientDual e a)]
  let := Fintype.ofFinite (D ⧸ AddSubgroup.zmultiples a)
  simp only [Nat.card_eq_fintype_card, AddChar.card_eq]

theorem primary_restriction_injective_iff_kernel_primeTo [Finite G]
    (ψ : AddChar G ℂ) (p : ℕ) (hp : p.Prime) :
    Function.Injective (fun x : AddCommGroup.primaryComponent G p => ψ x.val) ↔
      ¬ p ∣ Nat.card (characterKernel ψ) := by
  let : Fact p.Prime := ⟨hp⟩
  change Function.Injective
    (ψ.compAddMonoidHom (AddCommGroup.primaryComponent G p).subtype) ↔ _
  rw [AddChar.injective_iff]
  constructor
  · intro hinj hdvd
    obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := characterKernel ψ) p hdvd
    have hgP : g.val ∈ AddCommGroup.primaryComponent G p := by
      apply AddCommGroup.mem_primaryComponent_iff_addOrderOf.mpr
      exact ⟨1, by simpa using hg⟩
    have hz : (g : G) = 0 := congrArg Subtype.val (hinj (x := ⟨g.val, hgP⟩) g.property)
    have hg0 : g = 0 := Subtype.ext hz
    have : p = 1 := by simpa [hg0] using hg.symm
    exact hp.ne_one this
  · intro h x hx
    apply Subtype.ext
    obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent_iff_addOrderOf.mp x.property
    have hord : addOrderOf x.val ∣ Nat.card (characterKernel ψ) :=
      (characterKernel ψ).addOrderOf_dvd_natCard hx
    cases n with
    | zero => exact AddMonoid.addOrderOf_eq_one_iff.mp (by simpa using hn)
    | succ n =>
      exfalso
      exact h ((dvd_pow_self p (Nat.succ_ne_zero n)).trans (hn ▸ hord))

theorem primary_faithful_iff_dual_quotient_primeTo [Finite G] [Finite D]
    (e : D ≃+ AddChar G ℂ) (a : D) (p : ℕ) (hp : p.Prime) :
    Function.Injective (fun x : AddCommGroup.primaryComponent G p => e a x.val) ↔
      ¬ p ∣ Nat.card (D ⧸ AddSubgroup.zmultiples a) := by
  rw [primary_restriction_injective_iff_kernel_primeTo (e a) p hp,
    characterKernel_card e a]


end FiniteCharacterDuality

end SICLean.L5.OddPrimeTraceDualAux
