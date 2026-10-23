import SICLean.L3.Pseudolattice
import SICLean.L3.PseudolatticeIdealAux
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

set_option autoImplicit false

/-!
# Maximal-order saturation and a uniform conductor bound

An ε-stable integer lattice is generally neither an
`𝓞 K`-submodule nor an invertible ideal of the nonmaximal order `ℤ[ε]`.
Only its maximal-order saturation is sent to `ClassGroup (𝓞 K)`.

The argument uses `NumberField.RingOfIntegers.instFintypeClassGroup`,
`FractionalIdeal.isFractional_of_fg`, `Submodule.FG.span`, and
`RingOfIntegers.exponent`, through the ordinary class group.
-/

noncomputable section

open scoped nonZeroDivisors NumberField

namespace SICLean.L3

universe u

variable {K : Type u} [Field K] [NumberField K]

def epsilonOrder (P : PeriodData K) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({P.epsilon} : Set K)

def epsilonInteger (P : PeriodData K) : 𝓞 K :=
  ⟨P.epsilon, P.epsilon_integral⟩

/-- A fixed positive integer in the conductor suffices. It need not be
identified with the index of the order or with an optimal conductor. -/
def pseudolatticeConductor (P : PeriodData K) : ℕ :=
  RingOfIntegers.exponent (epsilonInteger P)

def fractionalIdealCarrier (a : FractionalIdeal (𝓞 K)⁰ K) : Submodule ℤ K :=
  (a : Submodule (𝓞 K) K).restrictScalars ℤ

/-- Actual saturation `𝓞_K I`. Fractionality comes from finite generation
over the ring of integers, rather than being included in the input. -/
def pseudolatticeSaturation (P : PeriodData K) (I : StablePseudolattice P) :
    FractionalIdeal (𝓞 K)⁰ K :=
  ⟨Submodule.span (𝓞 K) (I.1 : Set K),
    FractionalIdeal.isFractional_of_fg I.property.1.fg.span⟩

/-- Nonzero fractional ideals over the maximal order are invertible. -/
def pseudolatticeSaturationUnit (P : PeriodData K) (I : StablePseudolattice P) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (pseudolatticeSaturation P I) (by
    intro h
    apply pseudolattice_maximalSpan_ne_bot I.1 I.property.1
    simpa only [pseudolatticeSaturation, FractionalIdeal.coe_mk, FractionalIdeal.coe_zero] using
      congrArg (fun a : FractionalIdeal (𝓞 K)⁰ K => (a : Submodule (𝓞 K) K)) h)

def pseudolatticeOrdinaryClass (P : PeriodData K) (I : StablePseudolattice P) :
    ClassGroup (𝓞 K) :=
  ClassGroup.mk K (pseudolatticeSaturationUnit P I)

/- Integrality of ε makes ℤ[ε] finite over ℤ. -/
theorem epsilonOrder_fg (P : PeriodData K) : (epsilonOrder P).toSubmodule.FG := by
  exact P.epsilon_integral.fg_adjoin_singleton

/- ℚ[ε]=K and ε⁻¹=N+2-ε make ℤ[ε] a full ε-stable lattice. -/
theorem epsilonOrder_isStablePseudolattice (P : PeriodData K) :
    Submodule.IsLattice ℚ (epsilonOrder P).toSubmodule ∧
      PeriodStable P (epsilonOrder P).toSubmodule := by
  have he : P.epsilon ∈ epsilonOrder P := Algebra.subset_adjoin (Set.mem_singleton _)
  have hi : ((P.N : K) + 2) - P.epsilon ∈ epsilonOrder P :=
    (epsilonOrder P).sub_mem
      ((epsilonOrder P).add_mem ((epsilonOrder P).natCast_mem _) ((epsilonOrder P).natCast_mem _)) he
  have heq : P.epsilon * (((P.N : K) + 2) - P.epsilon) = 1 := by
    linear_combination -P.epsilon_polynomial
  constructor
  · refine ⟨epsilonOrder_fg P, ?_⟩
    change Submodule.span ℚ ((Algebra.adjoin ℤ {P.epsilon}).toSubmodule : Set K) = ⊤
    rw [Algebra.adjoin_eq_span, Submodule.span_span_of_tower,
      ← Algebra.adjoin_eq_span, P.epsilon_adjoin_eq_top]
    rfl
  · apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
      exact (epsilonOrder P).mul_mem he hy
    · intro x hx
      apply (pseudolatticeScale_mem_iff _ _ _).mpr
      refine ⟨(((P.N : K) + 2) - P.epsilon) * x, (epsilonOrder P).mul_mem hi hx, ?_⟩
      rw [← mul_assoc, heq, one_mul]

/- The full order has a nonzero positive integer in its conductor. The chosen integer is
`RingOfIntegers.exponent`. -/
theorem pseudolatticeConductor_pos (P : PeriodData K) :
    0 < pseudolatticeConductor P := by
  classical
  let O := (epsilonOrder P).toSubmodule
  have hs : Submodule.span ℚ (O : Set K) = ⊤ :=
    (epsilonOrder_isStablePseudolattice P).1.span_eq_top
  have hpoint : ∀ a : K, ∃ (d : ℤ), d ≠ 0 ∧ d • a ∈ O := by
    intro a
    have ha : a ∈ Submodule.span ℚ (O : Set K) := by
      rw [hs]
      trivial
    obtain ⟨y, hy, d, hd⟩ := (IsLocalization.mem_span_iff ℤ⁰).mp ha
    refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.prop, ?_⟩
    have heq : (d : ℤ) • a = y := by
      rw [hd, ← IsScalarTower.algebraMap_smul ℚ (d : ℤ), smul_smul,
        mul_comm, IsLocalization.mk'_spec]
      simp only [map_one, one_smul]
    rw [heq]
    simpa only [Submodule.span_eq] using hy
  have hden : ∀ (J : Submodule ℤ K), J.FG →
      ∃ (d : ℤ), d ≠ 0 ∧ ∀ a ∈ J, d • a ∈ O := by
    intro J hJ
    refine Submodule.fg_induction (motive := fun J _ =>
      ∃ (d : ℤ), d ≠ 0 ∧ ∀ a ∈ J, d • a ∈ O) ?_ ?_ J hJ
    · intro a
      obtain ⟨d, hd, hda⟩ := hpoint a
      refine ⟨d, hd, ?_⟩
      intro b hb
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      simpa only [smul_smul, mul_comm] using O.smul_mem c hda
    · intro J₁ J₂ _ _ h₁ h₂
      obtain ⟨d₁, hd₁, h₁⟩ := h₁
      obtain ⟨d₂, hd₂, h₂⟩ := h₂
      refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
      intro a ha
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
      rw [smul_add]
      exact O.add_mem
        (by simpa only [smul_smul, mul_comm] using O.smul_mem d₂ (h₁ a₁ ha₁))
        (by simpa only [smul_smul] using O.smul_mem d₁ (h₂ a₂ ha₂))
  let J : Submodule ℤ K := (⊤ : Submodule ℤ (𝓞 K)).map
    (IsScalarTower.toAlgHom ℤ (𝓞 K) K).toLinearMap
  have hJ : J.FG :=
    (Submodule.FG.of_finite (N := (⊤ : Submodule ℤ (𝓞 K)))).map _
  obtain ⟨d, hd, hdm⟩ := hden J hJ
  have hmap : (Algebra.adjoin ℤ ({epsilonInteger P} : Set (𝓞 K))).map
      (IsScalarTower.toAlgHom ℤ (𝓞 K) K) = epsilonOrder P := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    rfl
  have hc : (d : 𝓞 K) ∈ conductor ℤ (epsilonInteger P) := by
    apply mem_conductor_iff.mpr
    intro x
    have hx : (x : K) ∈ J :=
      Submodule.mem_map.mpr ⟨x, Submodule.mem_top, rfl⟩
    have hdx : (d : K) * (x : K) ∈ epsilonOrder P := by
      simpa only [O, zsmul_eq_mul, Subalgebra.mem_toSubmodule] using hdm _ hx
    rw [← hmap] at hdx
    obtain ⟨y, hy, heq⟩ := Subalgebra.mem_map.mp hdx
    have heq' : y = (d : 𝓞 K) * x := by
      apply NumberField.RingOfIntegers.coe_injective
      simpa only [map_mul, map_intCast, IsScalarTower.coe_toAlgHom',
        NumberField.RingOfIntegers.coe_eq_algebraMap] using heq
    exact heq' ▸ hy
  have hdvd : ((pseudolatticeConductor P : ℕ) : ℤ) ∣ d :=
    Int.cast_mem_ideal_iff.mp hc
  apply Nat.pos_of_ne_zero
  intro hzero
  rw [hzero, Int.natCast_zero, zero_dvd_iff] at hdvd
  exact hd hdvd

/-- This is the only conductor property used by the sandwich argument. -/
theorem pseudolatticeConductor_mul_mem_epsilonOrder (P : PeriodData K) (x : 𝓞 K) :
    (pseudolatticeConductor P : K) * (x : K) ∈ epsilonOrder P := by
  have hf : (pseudolatticeConductor P : 𝓞 K) ∈ conductor ℤ (epsilonInteger P) :=
    Int.absNorm_under_mem (conductor ℤ (epsilonInteger P))
  have hm := (mem_conductor_iff.mp hf) x
  have hm' : (algebraMap (𝓞 K) K) ((pseudolatticeConductor P : 𝓞 K) * x) ∈
      (Algebra.adjoin ℤ ({epsilonInteger P} : Set (𝓞 K))).map
        (IsScalarTower.toAlgHom ℤ (𝓞 K) K) :=
    Subalgebra.mem_map.mpr ⟨_, hm, rfl⟩
  rw [AlgHom.map_adjoin, Set.image_singleton] at hm'
  change (algebraMap (𝓞 K) K) ((pseudolatticeConductor P : 𝓞 K) * x) ∈ epsilonOrder P at hm'
  simpa only [map_mul, map_natCast] using hm'

/- ε-stability extends to multiplication by the generated order. -/
theorem periodStable_order_smul (P : PeriodData K) (I : StablePseudolattice P)
    (a x : K) (ha : a ∈ epsilonOrder P) (hx : x ∈ I.1) : a * x ∈ I.1 := by
  have hact : ∀ a ∈ Algebra.adjoin ℤ ({P.epsilon} : Set K),
      ∀ x ∈ I.1, a * x ∈ I.1 := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases Set.mem_singleton_iff.mp ha with rfl
      intro x hx
      rw [← I.property.2]
      exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩
    | algebraMap z =>
      intro x hx
      change (z : K) * x ∈ I.1
      simpa only [zsmul_eq_mul] using I.1.smul_mem z hx
    | add a b ha hb ih₁ ih₂ =>
      intro x hx
      rw [add_mul]
      exact I.1.add_mem (ih₁ x hx) (ih₂ x hx)
    | mul a b ha hb ih₁ ih₂ =>
      intro x hx
      rw [mul_assoc]
      exact ih₁ _ (ih₂ x hx)
  exact hact a ha x hx

/- The fractional ideal has the specified maximal-order span as its actual carrier. -/
theorem pseudolatticeSaturation_coe (P : PeriodData K) (I : StablePseudolattice P) :
    (pseudolatticeSaturation P I : Submodule (𝓞 K) K) =
      Submodule.span (𝓞 K) (I.1 : Set K) := by
  rfl

/- Saturation of a full lattice is nonzero, so its maximal-order fractional ideal is invertible. -/
theorem pseudolatticeSaturation_ne_zero (P : PeriodData K) (I : StablePseudolattice P) :
    pseudolatticeSaturation P I ≠ 0 := by
  exact Units.ne_zero (pseudolatticeSaturationUnit P I)

/- Upper sandwich inclusion I⊆a for a=𝓞_K I. -/
theorem pseudolatticeSaturation_contains (P : PeriodData K) (I : StablePseudolattice P) :
    I.1 ≤ fractionalIdealCarrier (pseudolatticeSaturation P I) := by
  intro x hx
  exact Submodule.subset_span hx

/- Lower sandwich inclusion fa⊆I: combine f𝓞_K⊆ℤ[ε] with ℤ[ε]I=I. -/
theorem pseudolatticeSaturation_conductor_le (P : PeriodData K) (I : StablePseudolattice P) :
    pseudolatticeScale (pseudolatticeConductor P : K)
      (fractionalIdealCarrier (pseudolatticeSaturation P I)) ≤ I.1 := by
  have hs : ∀ y ∈ Submodule.span (𝓞 K) (I.1 : Set K),
      ∀ a : 𝓞 K, (pseudolatticeConductor P : K) * (a : K) * y ∈ I.1 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro a
      exact periodStable_order_smul P I _ _
        (pseudolatticeConductor_mul_mem_epsilonOrder P a) hy
    | zero =>
      intro a
      simp
    | add x y hx hy ihx ihy =>
      intro a
      rw [mul_add]
      exact I.1.add_mem (ihx a) (ihy a)
    | smul a y hy ih =>
      intro b
      simpa [Algebra.smul_def, mul_assoc] using ih (b * a)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
  change y ∈ Submodule.span (𝓞 K) (I.1 : Set K) at hy
  simpa using hs y hy 1

/- A nonzero maximal-order fractional ideal is a full lattice; `NumberField.basisOfFractionalIdeal`
supplies its rational span. -/
theorem fractionalIdealCarrier_isLattice (a : FractionalIdeal (𝓞 K)⁰ K) (ha : a ≠ 0) :
    Submodule.IsLattice ℚ (fractionalIdealCarrier a) := by
  let u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 a ha
  refine ⟨?_, ?_⟩
  · exact (Module.Finite.iff_fg).mp (inferInstance : Module.Finite ℤ a)
  · have hh : Set.range (NumberField.basisOfFractionalIdeal K u) ⊆
        (fractionalIdealCarrier a : Set K) := by
      intro x hx
      exact (NumberField.mem_span_basisOfFractionalIdeal (I := u)).mp
        (Submodule.subset_span hx)
    apply top_unique
    rw [← (NumberField.basisOfFractionalIdeal K u).span_eq]
    exact Submodule.span_mono hh

/- Principal-ideal multiplication agrees with field scaling of the integer carrier. -/
theorem fractionalIdealCarrier_scale (lam : K) (a : FractionalIdeal (𝓞 K)⁰ K) :
    fractionalIdealCarrier (FractionalIdeal.spanSingleton (𝓞 K)⁰ lam * a) =
      pseudolatticeScale lam (fractionalIdealCarrier a) := by
  ext x
  change x ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ lam * a ↔ _
  rw [FractionalIdeal.mem_singleton_mul, pseudolatticeScale_mem_iff]
  constructor <;> rintro ⟨y, hy, h⟩ <;> exact ⟨y, hy, h.symm⟩

/- Maximal-order saturation commutes with a nonzero field homothety. -/
theorem pseudolatticeSaturation_scale (P : PeriodData K) (lam : K) (hlam : lam ≠ 0)
    (I : StablePseudolattice P) :
    pseudolatticeSaturation P (stablePseudolatticeScale P lam hlam I) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ lam * pseudolatticeSaturation P I := by
  apply FractionalIdeal.coeToSubmodule_injective
  change (pseudolatticeSaturation P (stablePseudolatticeScale P lam hlam I) : Submodule (𝓞 K) K) =
    ((FractionalIdeal.spanSingleton (𝓞 K)⁰ lam * pseudolatticeSaturation P I :
      FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  rw [pseudolatticeSaturation_coe, FractionalIdeal.coe_mul, pseudolatticeSaturation_coe,
    FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  change Submodule.span (𝓞 K) (pseudolatticeScale lam I.1 : Set K) = _
  rw [Submodule.smul_span]
  congr 1

/-- Ordinary classes give representatives up to arbitrary nonzero field
scalars. Finiteness is Mathlib's class-group instance for the ring of integers. -/
theorem ordinaryFractionalIdealRepresentatives (P : PeriodData K) :
    ∃ reps : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∀ a : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ lam : Kˣ,
        (a : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (lam : K) *
            (reps (ClassGroup.mk K a) : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  have hsurj : ∀ c : ClassGroup (𝓞 K),
      ∃ a : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K a = c := by
    intro c
    exact ClassGroup.induction K (fun a => ⟨a, rfl⟩) c
  choose reps hreps using hsurj
  refine ⟨reps, fun a => ?_⟩
  have hmap (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      Units.mapEquiv (↑(FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K K)) b = b := by
    apply Units.ext
    simp
  have hquot :
      QuotientGroup.mk' (toPrincipalIdeal (𝓞 K) K).range
          (reps (ClassGroup.mk K a)) =
        QuotientGroup.mk' (toPrincipalIdeal (𝓞 K) K).range a := by
    simpa only [ClassGroup.equiv_mk, hmap] using
      congrArg (ClassGroup.equiv K) (hreps (ClassGroup.mk K a))
  obtain ⟨z, hz, hza⟩ := (QuotientGroup.mk'_eq_mk' _).mp hquot
  obtain ⟨lam, hlam⟩ := hz
  refine ⟨lam, ?_⟩
  rw [← hlam] at hza
  have hval := congrArg (fun u : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
    (u : FractionalIdeal (𝓞 K)⁰ K)) hza
  simpa only [Units.val_mul, coe_toPrincipalIdeal, mul_comm] using hval.symm

/-- Choose one field unit for each realized pair of signs and fill any
unused slots arbitrarily. Four slots suffice. -/
theorem fieldSignRepresentatives (P : PeriodData K) :
    ∃ signs : Fin 4 → Kˣ, ∀ lam : Kˣ, ∃ s : Fin 4,
      TotallyPositive P ((lam : K) / (signs s : K)) := by
  classical
  let pattern (lam : Kˣ) : Bool × Bool :=
    (decide (0 < P.sigma₁ (lam : K)), decide (0 < P.sigma₂ (lam : K)))
  let signs₀ : Bool × Bool → Kˣ := Function.invFun pattern
  let e : (Bool × Bool) ≃ Fin 4 := by
    simpa using Fintype.equivFin (Bool × Bool)
  refine ⟨fun i => signs₀ (e.symm i), fun lam => ⟨e (pattern lam), ?_⟩⟩
  simp only [Equiv.symm_apply_apply]
  have hp : pattern (signs₀ (pattern lam)) = pattern lam := Function.apply_invFun_apply
  have divpos (f : K →+* ℝ) (u v : Kˣ)
      (h : decide (0 < f (u : K)) = decide (0 < f (v : K))) :
      0 < f ((u : K) / (v : K)) := by
    rw [map_div₀]
    have hu : f (u : K) ≠ 0 := by simpa using f.injective.ne (Units.ne_zero u)
    have hv : f (v : K) ≠ 0 := by simpa using f.injective.ne (Units.ne_zero v)
    have he : 0 < f (u : K) ↔ 0 < f (v : K) := decide_eq_decide.mp h
    by_cases hpos : 0 < f (u : K)
    · exact div_pos hpos (he.mp hpos)
    · exact div_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt hpos) hu)
        (lt_of_le_of_ne (le_of_not_gt (mt he.mpr hpos)) hv)
  exact ⟨divpos P.sigma₁ _ _ (congrArg Prod.fst hp.symm),
    divpos P.sigma₂ _ _ (congrArg Prod.snd hp.symm)⟩

/- Ordinary class representatives plus the four sign patterns give the positive representatives. -/
theorem positiveFractionalIdealRepresentatives (P : PeriodData K) :
    ∃ reps : ClassGroup (𝓞 K) × Fin 4 → (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∀ a : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
        ∃ i : ClassGroup (𝓞 K) × Fin 4, ∃ lam : K,
          TotallyPositive P lam ∧
            fractionalIdealCarrier (a : FractionalIdeal (𝓞 K)⁰ K) =
              pseudolatticeScale lam
                (fractionalIdealCarrier (reps i : FractionalIdeal (𝓞 K)⁰ K)) := by
  obtain ⟨ordinary, hord⟩ := ordinaryFractionalIdealRepresentatives P
  obtain ⟨signs, hsign⟩ := fieldSignRepresentatives P
  let reps (i : ClassGroup (𝓞 K) × Fin 4) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    toPrincipalIdeal (𝓞 K) K (signs i.2) * ordinary i.1
  refine ⟨reps, fun a => ?_⟩
  obtain ⟨lam, hlam⟩ := hord a
  obtain ⟨s, hs⟩ := hsign lam
  refine ⟨(ClassGroup.mk K a, s), (lam : K) / (signs s : K), hs, ?_⟩
  rw [← fractionalIdealCarrier_scale]
  congr 1
  change (a : FractionalIdeal (𝓞 K)⁰ K) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ ((lam : K) / (signs s : K)) *
      ((toPrincipalIdeal (𝓞 K) K (signs s) * ordinary (ClassGroup.mk K a) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  rw [Units.val_mul, coe_toPrincipalIdeal, ← mul_assoc,
    FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ (Units.ne_zero (signs s))]
  exact hlam

end SICLean.L3
