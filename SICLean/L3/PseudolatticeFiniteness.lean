import SICLean.L3.PseudolatticeIdeal
import SICLean.L3.PseudolatticeFinitenessAux
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false

/-!
# Finite positive-homothety classes of stable pseudolattices

Finite intermediate integer submodules of `a / fa` include all normalized
stable lattices. They are not all declared ε-stable, so the argument does not
require the original `ℤ[ε]`-module to be invertible.

The argument uses Mathlib's free and finite integer-module instances for
fractional ideals, `Submodule.finiteQuotientOfFreeOfRankEq`, and
`Submodule.comapMkQRelIso`. This file has no analytic inputs.
-/

noncomputable section

open scoped nonZeroDivisors NumberField

namespace SICLean.L3

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- `fa` as a submodule of `a` itself, rather than of the ambient field. -/
def fractionalIdealMultiples (a : FractionalIdeal (𝓞 K)⁰ K) (f : ℕ) :
    Submodule ℤ (fractionalIdealCarrier a) :=
  LinearMap.range (LinearMap.lsmul ℤ (fractionalIdealCarrier a) (f : ℤ))

abbrev FractionalIdealResidue (a : FractionalIdeal (𝓞 K)⁰ K) (f : ℕ) :=
  fractionalIdealCarrier a ⧸ fractionalIdealMultiples a f

/-- The whole interval of additive integer submodules between `fa` and `a`. -/
abbrev FractionalIdealIntermediate (a : FractionalIdeal (𝓞 K)⁰ K) (f : ℕ) :=
  { I : Submodule ℤ K //
      pseudolatticeScale (f : K) (fractionalIdealCarrier a) ≤ I ∧
        I ≤ fractionalIdealCarrier a }

/-- Stability is retained as a separate restriction on the finite interval. -/
abbrev StableFractionalIdealIntermediate (P : PeriodData K)
    (a : FractionalIdeal (𝓞 K)⁰ K) (f : ℕ) :=
  { I : StablePseudolattice P //
      pseudolatticeScale (f : K) (fractionalIdealCarrier a) ≤ I.1 ∧
        I.1 ≤ fractionalIdealCarrier a }

/- Identify the image of multiplication by f inside a. -/
theorem fractionalIdealMultiples_mem_iff (a : FractionalIdeal (𝓞 K)⁰ K) (f : ℕ)
    (x : fractionalIdealCarrier a) :
    x ∈ fractionalIdealMultiples a f ↔
      ∃ y : fractionalIdealCarrier a, (f : ℤ) • y = x := by
  rw [fractionalIdealMultiples, LinearMap.mem_range]
  simp only [LinearMap.lsmul_apply]

/- The multiple submodule maps to fa in the ambient field. -/
theorem fractionalIdealMultiples_map (a : FractionalIdeal (𝓞 K)⁰ K) (f : ℕ) :
    (fractionalIdealMultiples a f).map (fractionalIdealCarrier a).subtype =
      pseudolatticeScale (f : K) (fractionalIdealCarrier a) := by
  rw [fractionalIdealMultiples]
  conv_lhs => rw [← LinearMap.range_comp]
  conv_rhs =>
    rw [pseudolatticeScale, ← Submodule.range_subtype (fractionalIdealCarrier a),
      ← LinearMap.range_comp]
  congr 1
  ext z
  simp [LinearMap.lsmul_apply, LinearMap.mulLeft_apply]

/- Nonzero integer multiplication has full rank on a. -/
theorem fractionalIdealMultiples_finrank (a : FractionalIdeal (𝓞 K)⁰ K)
    (f : ℕ) (hf : 0 < f) :
    Module.finrank ℤ (fractionalIdealMultiples a f) =
      Module.finrank ℤ (fractionalIdealCarrier a) := by
  have h : Function.Injective
      (LinearMap.lsmul ℤ (fractionalIdealCarrier a) (f : ℤ)) := by
    apply LinearMap.lsmul_injective
    exact_mod_cast hf.ne'
  exact LinearMap.finrank_range_of_inj h

/- `Submodule.finiteQuotientOfFreeOfRankEq`, using that fractional ideals are finite free ℤ-modules.
-/
theorem fractionalIdealResidue_finite (a : FractionalIdeal (𝓞 K)⁰ K)
    (f : ℕ) (hf : 0 < f) : Finite (FractionalIdealResidue a f) := by
  haveI : Module.Free ℤ (fractionalIdealCarrier a) := fractionalIdealCarrier_free a
  haveI : Module.Finite ℤ (fractionalIdealCarrier a) := fractionalIdealCarrier_finite a
  exact Submodule.finiteQuotientOfFreeOfRankEq _
    (fractionalIdealMultiples_finrank a f hf)

/-- Correspondence of submodules is used after restricting to `a`. -/
theorem fractionalIdealIntermediate_equiv (a : FractionalIdeal (𝓞 K)⁰ K) (f : ℕ) :
    Nonempty (FractionalIdealIntermediate a f ≃
      Submodule ℤ (FractionalIdealResidue a f)) := by
  classical
  refine ⟨{
    toFun := fun I => (Submodule.comap (fractionalIdealCarrier a).subtype I.1).map
      (fractionalIdealMultiples a f).mkQ
    invFun := fun U => ⟨(Submodule.comap (fractionalIdealMultiples a f).mkQ U).map
      (fractionalIdealCarrier a).subtype, ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · rw [← fractionalIdealMultiples_map a f]
    exact Submodule.map_mono
      (Submodule.le_comap_mkQ (p := fractionalIdealMultiples a f) U)
  · exact Submodule.map_subtype_le _ _
  · intro I
    apply Subtype.ext
    show ((Submodule.comap (fractionalIdealMultiples a f).mkQ
      ((Submodule.comap (fractionalIdealCarrier a).subtype I.1).map
        (fractionalIdealMultiples a f).mkQ)).map
      (fractionalIdealCarrier a).subtype) = I.1
    rw [Submodule.comap_map_mkQ]
    have hle : fractionalIdealMultiples a f ≤
        Submodule.comap (fractionalIdealCarrier a).subtype I.1 := by
      rw [← Submodule.map_le_iff_le_comap, fractionalIdealMultiples_map]
      exact I.2.1
    rw [sup_eq_right.mpr hle]
    exact Submodule.map_comap_eq_self (by simpa using I.2.2)
  · intro U
    show ((Submodule.comap (fractionalIdealCarrier a).subtype
      ((Submodule.comap (fractionalIdealMultiples a f).mkQ U).map
        (fractionalIdealCarrier a).subtype)).map
      (fractionalIdealMultiples a f).mkQ) = U
    rw [Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]
    exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_mkQ]
      exact le_top)

/- Submodules of the finite additive quotient a/fa form a finite type. -/
theorem fractionalIdealIntermediate_finite (a : FractionalIdeal (𝓞 K)⁰ K)
    (f : ℕ) (hf : 0 < f) : Finite (FractionalIdealIntermediate a f) := by
  obtain ⟨e⟩ := fractionalIdealIntermediate_equiv a f
  haveI : Finite (FractionalIdealResidue a f) := fractionalIdealResidue_finite a f hf
  exact Finite.of_equiv _ e.symm

/- Every intermediate integer subgroup between fa and a is a full finitely generated lattice. -/
theorem fractionalIdealIntermediate_isLattice (a : FractionalIdeal (𝓞 K)⁰ K)
    (ha : a ≠ 0) (f : ℕ) (hf : 0 < f) (I : FractionalIdealIntermediate a f) :
    Submodule.IsLattice ℚ I.1 := by
  have hbase : Submodule.IsLattice ℚ (fractionalIdealCarrier a) :=
    fractionalIdealCarrier_isLattice a ha
  have hfg : I.1.FG := Submodule.FG.of_le hbase.fg I.2.2
  refine ⟨hfg, ?_⟩
  rw [eq_top_iff, ← hbase.span_eq_top]
  apply Submodule.span_le.mpr
  intro x hx
  have hfx : (f : K) * x ∈ I.1 :=
    I.2.1 ((pseudolatticeScale_mem_iff (f : K) ((f : K) * x) _).mpr ⟨x, hx, rfl⟩)
  have hq : ((f : ℚ))⁻¹ • ((f : K) * x) = x := by
    rw [Algebra.smul_def, map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact_mod_cast hf.ne'
  rw [← hq]
  exact Submodule.smul_mem (Submodule.span ℚ (I.1 : Set K)) ((f : ℚ))⁻¹
    (Submodule.subset_span hfx)

/- The stable pseudolattices form a subtype of the finite interval; arbitrary intermediate subgroups
are not assumed stable. -/
theorem stableFractionalIdealIntermediate_finite (P : PeriodData K)
    (a : FractionalIdeal (𝓞 K)⁰ K) (f : ℕ) (hf : 0 < f) :
    Finite (StableFractionalIdealIntermediate P a f) := by
  haveI : Finite (FractionalIdealIntermediate a f) :=
    fractionalIdealIntermediate_finite a f hf
  refine Finite.of_injective
    (fun I : StableFractionalIdealIntermediate P a f =>
      (⟨I.1.1, I.2⟩ : FractionalIdealIntermediate a f)) ?_
  intro I J h
  have h1 : I.1.1 = J.1.1 :=
    congrArg (fun x : FractionalIdealIntermediate a f => x.1) h
  exact Subtype.ext (Subtype.ext h1)

/- A=λa_i transports fa⊆I⊆a to fa_i⊆λ⁻¹I⊆a_i. -/
theorem stablePseudolattice_normalized_sandwich (P : PeriodData K)
    (I : StablePseudolattice P) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (lam : K) (hlam : TotallyPositive P lam)
    (ha : fractionalIdealCarrier (pseudolatticeSaturation P I) =
      pseudolatticeScale lam (fractionalIdealCarrier (a : FractionalIdeal (𝓞 K)⁰ K))) :
    pseudolatticeScale (pseudolatticeConductor P : K)
        (fractionalIdealCarrier (a : FractionalIdeal (𝓞 K)⁰ K)) ≤
      pseudolatticeScale lam⁻¹ I.1 ∧
      pseudolatticeScale lam⁻¹ I.1 ≤
        fractionalIdealCarrier (a : FractionalIdeal (𝓞 K)⁰ K) := by
  have hlam0 : lam ≠ 0 := totallyPositive_ne_zero P lam hlam
  constructor
  · have hlow : pseudolatticeScale (pseudolatticeConductor P : K)
        (pseudolatticeScale lam
          (fractionalIdealCarrier (a : FractionalIdeal (𝓞 K)⁰ K))) ≤ I.1 := by
      rw [← ha]
      exact pseudolatticeSaturation_conductor_le P I
    have hlow' : pseudolatticeScale lam
        (pseudolatticeScale (pseudolatticeConductor P : K)
          (fractionalIdealCarrier (a : FractionalIdeal (𝓞 K)⁰ K))) ≤ I.1 := by
      rwa [pseudolatticeScale_comm lam (pseudolatticeConductor P : K)]
    have h2 := pseudolatticeScale_mono lam⁻¹ hlow'
    rwa [pseudolatticeScale_inv_cancel lam hlam0] at h2
  · have hup : I.1 ≤ pseudolatticeScale lam
        (fractionalIdealCarrier (a : FractionalIdeal (𝓞 K)⁰ K)) := by
      rw [← ha]
      exact pseudolatticeSaturation_contains P I
    have h2 := pseudolatticeScale_mono lam⁻¹ hup
    rwa [pseudolatticeScale_inv_cancel lam hlam0] at h2

/-- A finite list of maximal-order ideals covers the normalized sandwiches. -/
theorem finiteNormalizedIdealCover (P : PeriodData K) :
    ∃ n : ℕ, 0 < n ∧
      ∃ a : Fin n → (FractionalIdeal (𝓞 K)⁰ K)ˣ,
        ∀ I : StablePseudolattice P, ∃ i : Fin n, ∃ lam : K,
          TotallyPositive P lam ∧
            pseudolatticeScale (pseudolatticeConductor P : K)
                (fractionalIdealCarrier (a i : FractionalIdeal (𝓞 K)⁰ K)) ≤
              pseudolatticeScale lam⁻¹ I.1 ∧
            pseudolatticeScale lam⁻¹ I.1 ≤
              fractionalIdealCarrier (a i : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  obtain ⟨reps, hreps⟩ := positiveFractionalIdealRepresentatives P
  let n := Fintype.card (ClassGroup (𝓞 K) × Fin 4)
  have hn : 0 < n :=
    Fintype.card_pos_iff.mpr ⟨(ClassGroup.mk K 1, 0)⟩
  let e : (ClassGroup (𝓞 K) × Fin 4) ≃ Fin n := Fintype.equivFin _
  refine ⟨n, hn, fun i => reps (e.symm i), ?_⟩
  intro I
  obtain ⟨i0, lam, htp, hcar⟩ := hreps (pseudolatticeSaturationUnit P I)
  refine ⟨e i0, lam, htp, ?_⟩
  have hval : (pseudolatticeSaturationUnit P I : FractionalIdeal (𝓞 K)⁰ K) =
      pseudolatticeSaturation P I := rfl
  have hcar' : fractionalIdealCarrier (pseudolatticeSaturation P I) =
      pseudolatticeScale lam (fractionalIdealCarrier ↑(reps i0)) := by
    rw [← hval]
    exact hcar
  have h := stablePseudolattice_normalized_sandwich P I
    (reps (e.symm (e i0))) lam htp ?_
  · simpa using h
  · simpa using hcar'

/- The order ℤ[ε] is a stable pseudolattice, so a family indexed by `Fin n` is nonempty. -/
theorem stablePseudolattice_nonempty (P : PeriodData K) :
    Nonempty (StablePseudolattice P) := by
  exact ⟨⟨(epsilonOrder P).toSubmodule, epsilonOrder_isStablePseudolattice P⟩⟩

/- Choose stable members from the finitely many normalized sandwich intervals. -/
theorem finiteHomothetyCover (P : PeriodData K) :
    ∃ s : Finset (StablePseudolattice P),
      ∀ I : StablePseudolattice P, ∃ J ∈ s, PositiveHomothetic P I.1 J.1 := by
  classical
  obtain ⟨n, hn, a, hcover⟩ := finiteNormalizedIdealCover P
  let f := pseudolatticeConductor P
  haveI : ∀ i, Finite (StableFractionalIdealIntermediate P (a i) f) := fun i =>
    stableFractionalIdealIntermediate_finite P (a i) f (pseudolatticeConductor_pos P)
  haveI : ∀ i, Fintype (StableFractionalIdealIntermediate P (a i) f) := fun _ =>
    Fintype.ofFinite _
  let s : Finset (StablePseudolattice P) :=
    Finset.univ.image (fun x : (i : Fin n) ×
      StableFractionalIdealIntermediate P (a i) f => x.2.1)
  refine ⟨s, ?_⟩
  intro I
  obtain ⟨i, lam, htp, h1, h2⟩ := hcover I
  have hlam : lam ≠ 0 := totallyPositive_ne_zero P lam htp
  let J : StablePseudolattice P :=
    ⟨pseudolatticeScale lam⁻¹ I.1,
      pseudolatticeScale_isLattice I.1 I.2.1 lam⁻¹ (inv_ne_zero hlam),
      pseudolatticeScale_periodStable P I.1 I.2.2 lam⁻¹⟩
  have hJ : J ∈ s := by
    refine Finset.mem_image.mpr ⟨⟨i, ⟨J, ?_, ?_⟩⟩, Finset.mem_univ _, rfl⟩
    · exact h1
    · exact h2
  refine ⟨J, hJ, lam, htp, ?_⟩
  exact ((pseudolatticeScale_inv lam hlam I.1).2).symm

/- Equality in the setoid quotient means a totally positive field homothety. -/
theorem stablePseudolatticeClass_eq_iff (P : PeriodData K)
    (I J : StablePseudolattice P) :
    (Quotient.mk (stablePseudolatticeSetoid P) I : StablePseudolatticeClass P) =
        Quotient.mk (stablePseudolatticeSetoid P) J ↔
      PositiveHomothetic P I.1 J.1 := by
  exact Quotient.eq

/- Finiteness follows from saturation, the conductor sandwich, finite ideal-class representatives,
and finite intermediate subgroups. -/
theorem quotientFinite (P : PeriodData K) : Finite (StablePseudolatticeClass P) := by
  classical
  obtain ⟨s, hs⟩ := finiteHomothetyCover P
  refine Finite.of_surjective
    (fun J : {x // x ∈ s} => Quotient.mk (stablePseudolatticeSetoid P) J.1) ?_
  intro q
  induction q using Quotient.ind with
  | _ I =>
    obtain ⟨J, hJ, hPH⟩ := hs I
    exact ⟨⟨J, hJ⟩, (stablePseudolatticeClass_eq_iff P J I).mpr
      (positiveHomothetic_symm P I.1 J.1 hPH)⟩

/-- The final output needed by the finite distribution family. Each
representative is an actual stable lattice, and the scalar lies in `K`. -/
theorem finiteRepresentatives (P : PeriodData K) :
    ∃ n : ℕ, 0 < n ∧ ∃ reps : Fin n → StablePseudolattice P,
      ∀ I : StablePseudolattice P, ∃ i : Fin n, ∃ lam : K,
        TotallyPositive P lam ∧ I.1 = pseudolatticeScale lam (reps i).1 := by
  classical
  haveI : Finite (StablePseudolatticeClass P) := quotientFinite P
  haveI : Fintype (StablePseudolatticeClass P) := Fintype.ofFinite _
  let n := Fintype.card (StablePseudolatticeClass P)
  have hn : 0 < n := by
    rw [Fintype.card_pos_iff]
    exact ⟨Quotient.mk (stablePseudolatticeSetoid P)
      (Classical.choice (stablePseudolattice_nonempty P))⟩
  let e : StablePseudolatticeClass P ≃ Fin n := Fintype.equivFin _
  let reps : Fin n → StablePseudolattice P := fun i => Quotient.out (e.symm i)
  refine ⟨n, hn, reps, ?_⟩
  intro I
  have hq : Quotient.mk (stablePseudolatticeSetoid P)
        (reps (e (Quotient.mk (stablePseudolatticeSetoid P) I))) =
      Quotient.mk (stablePseudolatticeSetoid P) I := by
    simp only [reps]
    rw [Equiv.symm_apply_apply, Quotient.out_eq]
  have hPH := (stablePseudolatticeClass_eq_iff P
    (reps (e (Quotient.mk (stablePseudolatticeSetoid P) I))) I).mp hq
  obtain ⟨lam, htp, heq⟩ := positiveHomothetic_symm P _ _ hPH
  exact ⟨e (Quotient.mk (stablePseudolatticeSetoid P) I), lam, htp, heq⟩

end SICLean.L3
