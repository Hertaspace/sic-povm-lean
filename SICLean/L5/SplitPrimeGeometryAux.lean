import SICLean.L5.SplitPrimeLattice
import Mathlib.RingTheory.Trace.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.FiniteAbelian.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped NumberField

namespace SICLean.L5.SplitPrimeGeometryAux

open L3

variable {K : Type} [Field K] [NumberField K]

/-- The quadratic characteristic equation, evaluated at the two specified real embeddings, computes
trace and norm of a nonrational element. -/
theorem trace_norm_of_distinct_embeddings (P : PeriodData K) (x : K)
    (hne : P.sigma₁ x ≠ P.sigma₂ x) :
    (Algebra.trace ℚ K x : ℝ) = P.sigma₁ x + P.sigma₂ x ∧
      (Algebra.norm ℚ x : ℝ) = P.sigma₁ x * P.sigma₂ x := by
  letI : Algebra.IsQuadraticExtension ℚ K := ⟨P.finrank_eq_two⟩
  have h := Algebra.IsQuadraticExtension.sq_sub_trace_smul_add_norm_eq_zero ℚ x
  have h₁ : (P.sigma₁ x) ^ 2 - (Algebra.trace ℚ K x : ℝ) * P.sigma₁ x +
      (Algebra.norm ℚ x : ℝ) = 0 := by
    simpa [Algebra.smul_def] using congrArg P.sigma₁ h
  have h₂ : (P.sigma₂ x) ^ 2 - (Algebra.trace ℚ K x : ℝ) * P.sigma₂ x +
      (Algebra.norm ℚ x : ℝ) = 0 := by
    simpa [Algebra.smul_def] using congrArg P.sigma₂ h
  have hm : (P.sigma₁ x - P.sigma₂ x) *
      (P.sigma₁ x + P.sigma₂ x - (Algebra.trace ℚ K x : ℝ)) = 0 := by
    nlinarith [h₁, h₂]
  have ht : (Algebra.trace ℚ K x : ℝ) = P.sigma₁ x + P.sigma₂ x := by
    have := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne)
    linarith
  refine ⟨ht, ?_⟩
  rw [ht] at h₁
  nlinarith [h₁]

/-- Norm one of the period yields the exact trace identity after any nonzero rational scaling of
epsilon minus one. -/
theorem trace_div_period_sub_one (P : PeriodData K) (c : ℚ) (hc : c ≠ 0) :
    Algebra.trace ℚ K ((P.epsilon - 1) / (c : K)) =
      -c * Algebra.norm ℚ ((P.epsilon - 1) / (c : K)) := by
  let x : K := (P.epsilon - 1) / (c : K)
  have hcK : (c : K) ≠ 0 := Rat.cast_ne_zero.mpr hc
  have hcR : (c : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hc
  have h₁ : P.sigma₁ P.epsilon = 1 + (c : ℝ) * P.sigma₁ x := by
    dsimp [x]
    simp only [map_div₀, map_sub, map_one, map_ratCast]
    field_simp
    <;> ring
  have h₂ : P.sigma₂ P.epsilon = 1 + (c : ℝ) * P.sigma₂ x := by
    dsimp [x]
    simp only [map_div₀, map_sub, map_one, map_ratCast]
    field_simp
    <;> ring
  have he : P.sigma₁ P.epsilon ≠ P.sigma₂ P.epsilon := by
    intro he
    have hi := P.epsilon_conj
    rw [← he] at hi
    have hepos := P.epsilon_gt_one
    have he0 : P.sigma₁ P.epsilon ≠ 0 := by linarith
    have hsq : P.sigma₁ P.epsilon * P.sigma₁ P.epsilon = 1 := by
      calc
        _ = (P.sigma₁ P.epsilon)⁻¹ * P.sigma₁ P.epsilon := congrArg
          (fun a : ℝ => a * P.sigma₁ P.epsilon) hi
        _ = 1 := inv_mul_cancel₀ he0
    nlinarith
  have hxe : P.sigma₁ x ≠ P.sigma₂ x := by
    intro hx
    apply he
    rw [h₁, h₂, hx]
  obtain ⟨ht, hn⟩ := trace_norm_of_distinct_embeddings P x hxe
  have hprod : P.sigma₁ P.epsilon * P.sigma₂ P.epsilon = 1 := by
    rw [P.epsilon_conj]
    exact mul_inv_cancel₀ (by have := P.epsilon_gt_one; linarith)
  rw [h₁, h₂] at hprod
  have hm : (c : ℝ) *
      (P.sigma₁ x + P.sigma₂ x + (c : ℝ) * (P.sigma₁ x * P.sigma₂ x)) = 0 := by
    nlinarith [hprod]
  have heq := (mul_eq_zero.mp hm).resolve_left hcR
  apply Rat.cast_injective (α := ℝ)
  change (Algebra.trace ℚ K x : ℝ) = ((-c * Algebra.norm ℚ x : ℚ) : ℝ)
  rw [Rat.cast_mul, Rat.cast_neg, ht, hn]
  linarith

/-- Addition identifies two disjoint subgroups with their sum. -/
def disjointSumEquiv {G : Type*} [AddCommGroup G] (A B : AddSubgroup G)
    (hd : Disjoint A B) : A × B ≃+ ↥(A ⊔ B) := by
  let f : A × B →+ ↥(A ⊔ B) :=
    { toFun := fun z => ⟨z.1.val + z.2.val,
        AddSubgroup.mem_sup.mpr ⟨_, z.1.property, _, z.2.property, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp; abel }
  apply AddEquiv.ofBijective f
  constructor
  · intro x y hxy
    exact AddSubgroup.add_injective_of_disjoint hd (congrArg Subtype.val hxy)
  · intro z
    obtain ⟨x, y, hxy⟩ := AddSubgroup.mem_sup'.mp z.property
    exact ⟨(x, y), Subtype.ext hxy⟩

/-- Choosing generators of two order-p subgroups gives coordinates on their actual sum, with the two
axes spanning the specified subgroups. -/
theorem coordinates_of_prime_order {G : Type*} [AddCommGroup G]
    {p : ℕ} [Fact p.Prime] (A B H : AddSubgroup G) (hd : Disjoint A B)
    (hs : A ⊔ B = H) (hA : Nat.card A = p) (hB : Nat.card B = p) :
    ∃ c : (ZMod p × ZMod p) ≃+ H,
      AddSubgroup.zmultiples (c (1, 0)).val = A ∧
        AddSubgroup.zmultiples (c (0, 1)).val = B := by
  let a : ZMod p ≃+ A := (ZMod.ringEquivCongr hA.symm).toAddEquiv.trans
    (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card hA))
  let b : ZMod p ≃+ B := (ZMod.ringEquivCongr hB.symm).toAddEquiv.trans
    (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card hB))
  let e : ↥(A ⊔ B) ≃+ H :=
    { toFun := fun x => ⟨x.val, hs ▸ x.property⟩
      invFun := fun x => ⟨x.val, hs.symm ▸ x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl }
  let c := ((a.prodCongr b).trans (disjointSumEquiv A B hd)).trans e
  have ha : AddSubgroup.zmultiples (a 1) = ⊤ :=
    zmultiples_eq_top_of_prime_card hA (by
      intro hzero
      have := a.injective (hzero.trans a.map_zero.symm)
      exact one_ne_zero this)
  have hb : AddSubgroup.zmultiples (b 1) = ⊤ :=
    zmultiples_eq_top_of_prime_card hB (by
      intro hzero
      have := b.injective (hzero.trans b.map_zero.symm)
      exact one_ne_zero this)
  have hca : (c (1, 0)).val = ((a 1 : A) : G) := by
    change ((a 1 : A) : G) + ((b 0 : B) : G) = _
    simp only [map_zero, AddSubgroup.coe_zero, add_zero]
  have hcb : (c (0, 1)).val = ((b 1 : B) : G) := by
    change ((a 0 : A) : G) + ((b 1 : B) : G) = _
    simp only [map_zero, AddSubgroup.coe_zero, zero_add]
  refine ⟨c, ?_, ?_⟩
  · rw [hca]
    simpa only [AddSubgroup.subtype_apply, ha, AddSubgroup.map_top, AddSubgroup.range_subtype] using
      (AddMonoidHom.map_zmultiples A.subtype (a 1)).symm
  · rw [hcb]
    simpa only [AddSubgroup.subtype_apply, hb, AddSubgroup.map_top, AddSubgroup.range_subtype] using
      (AddMonoidHom.map_zmultiples B.subtype (b 1)).symm

/-- The two coordinates of any surjective residue map sum to the integral trace. -/
theorem trace_residues (P : PeriodData K) {p : ℕ} [Fact p.Prime]
    (ρ : 𝓞 K →+* ZMod p × ZMod p) (hρ : Function.Surjective ρ) (a : 𝓞 K) :
    (Algebra.trace ℤ (𝓞 K) a : ZMod p) = (ρ a).1 + (ρ a).2 := by
  let : Algebra.IsQuadraticExtension ℤ (𝓞 K) :=
    ⟨(NumberField.RingOfIntegers.rank K).trans P.finrank_eq_two⟩
  have hpoly (x : 𝓞 K) :
      (ρ x).1 ^ 2 - (Algebra.trace ℤ (𝓞 K) x : ZMod p) * (ρ x).1 +
        (Algebra.norm ℤ x : ZMod p) = 0 ∧
      (ρ x).2 ^ 2 - (Algebra.trace ℤ (𝓞 K) x : ZMod p) * (ρ x).2 +
        (Algebra.norm ℤ x : ZMod p) = 0 := by
    have hx : x ^ 2 - (Algebra.trace ℤ (𝓞 K) x : 𝓞 K) * x +
        (Algebra.norm ℤ x : 𝓞 K) = 0 := by
      simpa [Algebra.smul_def] using
        (Algebra.IsQuadraticExtension.sq_sub_trace_smul_add_norm_eq_zero ℤ x)
    constructor
    · let f : 𝓞 K →+* ZMod p := (RingHom.fst _ _).comp ρ
      have hf := congrArg f hx
      simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at hf
      exact hf
    · let f : 𝓞 K →+* ZMod p := (RingHom.snd _ _).comp ρ
      have hf := congrArg f hx
      simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at hf
      exact hf
  have hneq (x : 𝓞 K) (hx : (ρ x).1 ≠ (ρ x).2) :
      (Algebra.trace ℤ (𝓞 K) x : ZMod p) = (ρ x).1 + (ρ x).2 := by
    have hxpoly := hpoly x
    have hf : ((ρ x).1 - (ρ x).2) *
        ((ρ x).1 + (ρ x).2 - (Algebra.trace ℤ (𝓞 K) x : ZMod p)) = 0 := by
      linear_combination hxpoly.1 - hxpoly.2
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hx))).symm
  by_cases ha : (ρ a).1 ≠ (ρ a).2
  · exact hneq a ha
  · obtain ⟨x, hx⟩ := hρ (1, 0)
    have hxt := hneq x (by simp [hx])
    have hax : (ρ (a + x)).1 ≠ (ρ (a + x)).2 := by
      intro he
      simp only [map_add, hx, Prod.fst_add, Prod.snd_add] at he
      apply one_ne_zero (α := ZMod p)
      linear_combination he - (not_ne_iff.mp ha)
    have hat := hneq (a + x) hax
    simp only [map_add, Int.cast_add, hx, Prod.fst_add, Prod.snd_add,
      add_zero] at hxt hat
    linear_combination hat - hxt

/-- The trace identity forces opposite residues without any unit hypothesis. -/
theorem period_div_opposite (P : PeriodData K) {p s : ℕ} [Fact p.Prime]
    (hs : 1 ≤ s) (ρ : 𝓞 K →+* ZMod p × ZMod p)
    (hρ : Function.Surjective ρ) (B : 𝓞 K)
    (hB : (B : K) = (P.epsilon - 1) / (p : K) ^ s) :
    (ρ B).2 = -(ρ B).1 := by
  have htrace : Algebra.trace ℤ (𝓞 K) B =
      -(p : ℤ) ^ s * Algebra.norm ℤ B := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [Algebra.coe_trace_int, Algebra.coe_norm_int]
    rw [hB]
    simpa only [Rat.cast_pow, Rat.cast_natCast] using
      trace_div_period_sub_one P ((p : ℚ) ^ s)
        (pow_ne_zero s (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  have hsum := trace_residues P ρ hρ B
  have hcast : (Algebra.trace ℤ (𝓞 K) B : ZMod p) = 0 := by
    rw [htrace]
    push_cast
    simp [Nat.ne_zero_of_lt hs]
    ring
  rw [hcast] at hsum
  exact eq_neg_of_add_eq_zero_right hsum.symm


open SplitPrimeLattice DistributionOrbitGeometry DistributionSubgroups

/-- Coprime integer annihilators detect membership in any lattice. -/
theorem mem_of_coprime_nsmul_mem (I : Submodule ℤ K) {m n : ℕ}
    (h : Nat.Coprime m n) (x : K) (hm : m • x ∈ I) (hn : n • x ∈ I) :
    x ∈ I := by
  have hm' : m • ambientMk I x = 0 := by
    rw [← map_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr hm
  have hn' : n • ambientMk I x = 0 := by
    rw [← map_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr hn
  have hz : ambientMk I x = 0 := by
    have hh := (gcd_nsmul_eq_zero (a := ambientMk I x) (m := m) (n := n)).mpr
      ⟨hm', hn'⟩
    simpa [h.gcd_eq_one] using hh
  exact (QuotientAddGroup.eq_zero_iff _).mp hz

/-- Prime-to-p saturation does not create any p-power division points. -/
theorem mem_of_saturation_mem (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hm : LocallyMaximal P I p) (k : ℕ) (x : K)
    (hx : x ∈ fractionalIdealCarrier (pseudolatticeSaturation P I))
    (hpx : p ^ k • x ∈ I.val) : x ∈ I.val := by
  let S := fractionalIdealCarrier (pseudolatticeSaturation P I)
  have hix : inclusionIndex I.val S • x ∈ I.val :=
    I.val.toAddSubgroup.nsmul_relIndex_mem hx
  exact mem_of_coprime_nsmul_mem I.val (hm.pow_left k) x hpx hix

/-- An element outside a maximal ideal generates a comaximal ideal. -/
theorem span_coprime_of_not_mem {R : Type*} [CommRing R]
    (J : Ideal R) [J.IsMaximal] (b : R) (hb : b ∉ J) :
    IsCoprime (Ideal.span {b}) J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq := Ideal.IsMaximal.eq_of_le (inferInstance : J.IsMaximal) hne
    (show J ≤ Ideal.span {b} ⊔ J from le_sup_right)
  have hb' : b ∈ Ideal.span {b} ⊔ J :=
    (show Ideal.span {b} ≤ Ideal.span {b} ⊔ J from le_sup_left)
      (Ideal.subset_span (by simp))
  exact hb (heq.symm ▸ hb')

/-- A leading term which is a unit at both split primes is coprime to p in the full ring of
integers. No O_K action on I is used. -/
theorem split_coprime (p : ℕ) {r q : FinitePlace.Prime K}
    (h : IsSplitPair p r q) (B : 𝓞 K) (hr : B ∉ r.asIdeal) (hq : B ∉ q.asIdeal) :
    IsCoprime B (p : 𝓞 K) := by
  apply (Ideal.isCoprime_span_singleton_iff B (p : 𝓞 K)).mp
  rw [← h.2]
  exact (span_coprime_of_not_mem r.asIdeal B hr).mul_right
    (span_coprime_of_not_mem q.asIdeal B hq)

/-- Bezout clearing inside the maximal-order saturation. -/
theorem saturation_mem_of_coprime_mul_mem (P : PeriodData K)
    (I : StablePseudolattice P) {B a : 𝓞 K} (h : IsCoprime B a) (x : K)
    (hBx : (B : K) * x ∈ fractionalIdealCarrier (pseudolatticeSaturation P I))
    (hax : (a : K) * x ∈ fractionalIdealCarrier (pseudolatticeSaturation P I)) :
    x ∈ fractionalIdealCarrier (pseudolatticeSaturation P I) := by
  obtain ⟨u, v, huv⟩ := h
  have huvK : (u : K) * (B : K) + (v : K) * (a : K) = 1 := by
    exact_mod_cast huv
  have hu := (pseudolatticeSaturation P I).1.smul_mem u hBx
  have hv := (pseudolatticeSaturation P I).1.smul_mem v hax
  have hh := (pseudolatticeSaturation P I).1.add_mem hu hv
  change (u : K) * ((B : K) * x) + (v : K) * ((a : K) * x) ∈
    fractionalIdealCarrier (pseudolatticeSaturation P I) at hh
  simpa only [← mul_assoc, ← add_mul, huvK, one_mul] using hh


/-- A prescribed p-power part in a product decomposition is exactly the primary subgroup, since the
complementary factor has prime-to-p order. -/
def primaryProdEquiv {G H C : Type*} [AddCommGroup G] [AddCommGroup H]
    [AddCommGroup C] {p s : ℕ} (hH : ∀ x : H, p ^ s • x = 0)
    (hC : Nat.Coprime p (Nat.card C)) (e : (H × C) ≃+ G) :
    H ≃+ AddCommGroup.primaryComponent G p := by
  let f : H →+ AddCommGroup.primaryComponent G p :=
    { toFun := fun x => ⟨e (x, 0), AddCommGroup.mem_primaryComponent.mpr
        ⟨s, by rw [← map_nsmul]; simp [hH]⟩⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by intro x y; apply Subtype.ext; simp [← map_add] }
  apply AddEquiv.ofBijective f
  constructor
  · intro x y hxy
    have heq : e (x, 0) = e (y, 0) := congrArg Subtype.val hxy
    exact congrArg Prod.fst (e.injective heq)
  · intro y
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp y.property
    have hpk : p ^ k • (e.symm y.val).2 = 0 := by
      have hh := congrArg (fun z : G => (e.symm z).2) hk
      simpa using hh
    have hcz : (e.symm y.val).2 = 0 := by
      have hh := (gcd_nsmul_eq_zero (a := (e.symm y.val).2)).mpr
        ⟨hpk, card_nsmul_eq_zero'⟩
      simpa only [(hC.pow_left k).gcd_eq_one, one_nsmul] using hh
    refine ⟨(e.symm y.val).1, ?_⟩
    apply Subtype.ext
    change e ((e.symm y.val).1, 0) = y.val
    rw [← hcz, Prod.mk.eta, e.apply_symm_apply]

/-- Division torsion in the ambient quotient of a rank-two lattice, without a split-prime or
local-maximality hypothesis. -/
theorem ambient_division_equiv (P : PeriodData K) (I : StablePseudolattice P)
    (n : ℕ) (hn : n ≠ 0) :
    Nonempty ((LocalFourierSetup.pTorsion n (G := AmbientGroup I.val)) ≃+
      (Fin 2 → ZMod n)) := by
  obtain ⟨b⟩ := pseudolattice_exists_basis P I.val I.property.1
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let T := LocalFourierSetup.pTorsion n (G := AmbientGroup I.val)
  let f : I.val →+ T :=
    { toFun := fun x => ⟨ambientMk I.val ((n : K)⁻¹ * x.val), by
        change n • ambientMk I.val ((n : K)⁻¹ * x.val) = 0
        rw [← map_nsmul]
        apply (QuotientAddGroup.eq_zero_iff _).mpr
        change n • ((n : K)⁻¹ * x.val) ∈ I.val
        simpa only [nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hnK, one_mul]
          using x.property⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by intro x y; apply Subtype.ext; simp [mul_add] }
  let g : I.val →+ (Fin 2 → ZMod n) :=
    { toFun := fun x i => (b.equivFun x i : ZMod n)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective I.val.toAddSubgroup y.val
    have hzn : n • z ∈ I.val := by
      have hy := y.property
      change n • y.val = 0 at hy
      rw [← hz, ← map_nsmul] at hy
      exact (QuotientAddGroup.eq_zero_iff _).mp hy
    refine ⟨⟨n • z, hzn⟩, ?_⟩
    apply Subtype.ext
    change ambientMk I.val ((n : K)⁻¹ * (n • z)) = y.val
    rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hnK, one_mul]
    exact hz
  have hg : Function.Surjective g := by
    intro y
    choose a ha using fun i => ZMod.intCast_surjective (y i)
    refine ⟨b.equivFun.symm a, ?_⟩
    funext i
    change (b.equivFun (b.equivFun.symm a) i : ZMod n) = y i
    rw [b.equivFun.apply_symm_apply]
    exact ha i
  have hker : f.ker = g.ker := by
    ext x
    change f x = 0 ↔ g x = 0
    constructor
    · intro hx
      have hxmem : (n : K)⁻¹ * x.val ∈ I.val := by
        change (n : K)⁻¹ * x.val ∈ I.val.toAddSubgroup
        apply (QuotientAddGroup.eq_zero_iff _).mp
        exact congrArg Subtype.val hx
      let y : I.val := ⟨(n : K)⁻¹ * x.val, hxmem⟩
      have he : n • y = x := by
        apply Subtype.ext
        change n • ((n : K)⁻¹ * x.val) = x.val
        rw [nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hnK, one_mul]
      rw [← he, map_nsmul]
      ext i
      simp [nsmul_eq_mul]
    · intro hx
      have hx0 : ∀ i, (b.equivFun x i : ZMod n) = 0 := fun i => congrFun hx i
      choose a ha using fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp (hx0 i)
      let y : I.val := b.equivFun.symm a
      have he : x = (n : ℤ) • y := by
        apply b.equivFun.injective
        rw [map_smul]
        ext i
        change b.equivFun x i = ((n : ℤ) • b.equivFun y) i
        simp only [Pi.smul_apply, smul_eq_mul, y, b.equivFun.apply_symm_apply]
        exact ha i
      have hd : (n : K)⁻¹ * x.val = y.val := by
        rw [he]
        change (n : K)⁻¹ * ((n : ℤ) • y.val) = y.val
        rw [zsmul_eq_mul, Int.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hnK, one_mul]
      apply Subtype.ext
      change ambientMk I.val ((n : K)⁻¹ * x.val) = 0
      rw [hd]
      exact (QuotientAddGroup.eq_zero_iff _).mpr y.property
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective g hg))⟩

/-- Restrict an injective homomorphism to a subgroup whose image has been identified with a
specified subgroup of the codomain. -/
def subgroupEquivOfMapEq {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (f : G →+ A) (hf : Function.Injective f) (H : AddSubgroup G)
    (T : AddSubgroup A) (h : H.map f = T) : H ≃+ T := by
  let e : H.map f ≃+ T :=
    { toFun := fun x => ⟨x.val, h ▸ x.property⟩
      invFun := fun x => ⟨x.val, h.symm ▸ x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl }
  exact (H.equivMapOfInjective f hf).trans e

/-- Cardinality of the primary subgroup fixes the common exponent of a rank-two p-primary part. -/
theorem plane_exponent_unique {G C : Type*} [AddCommGroup G] [AddCommGroup C]
    {p s t : ℕ} (hp : p.Prime) (hC : Nat.Coprime p (Nat.card C))
    (e : ((Fin 2 → ZMod (p ^ s)) × C) ≃+ G)
    (f : AddCommGroup.primaryComponent G p ≃+ (Fin 2 → ZMod (p ^ t))) :
    s = t := by
  have hkill (x : Fin 2 → ZMod (p ^ s)) : p ^ s • x = 0 := by
    ext i
    change p ^ s • x i = 0
    simp [nsmul_eq_mul]
  let g := primaryProdEquiv hkill hC e
  have hc : (p ^ s) ^ 2 = (p ^ t) ^ 2 := by
    calc
      _ = Nat.card (Fin 2 → ZMod (p ^ s)) := by simp [Nat.card_fun]
      _ = Nat.card (AddCommGroup.primaryComponent G p) := Nat.card_congr g.toEquiv
      _ = Nat.card (Fin 2 → ZMod (p ^ t)) := Nat.card_congr f.toEquiv
      _ = _ := by simp [Nat.card_fun]
  have he : p ^ s = p ^ t := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hc
  exact Nat.pow_right_injective hp.two_le he

/-- Exact leading terms identify p-primary period points with the literal p^s-division subgroup of
K/I. -/
theorem primary_ambient_image_of_division (P : PeriodData K) (I : StablePseudolattice P)
    {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (hB : IsIntegral ℤ (((P.epsilon - 1) / (p : K) ^ s)))
    (hr : (⟨((P.epsilon - 1) / (p : K) ^ s), hB⟩ : 𝓞 K) ∉ r.asIdeal)
    (hq : (⟨((P.epsilon - 1) / (p : K) ^ s), hB⟩ : 𝓞 K) ∉ q.asIdeal) :
    (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p).map (toAmbient P I) =
      LocalFourierSetup.pTorsion (p ^ s) (G := AmbientGroup I.val) := by
  let B : 𝓞 K := ⟨((P.epsilon - 1) / (p : K) ^ s), hB⟩
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have heq : (p : K) ^ s * (B : K) = P.epsilon - 1 := by
    dsimp [B]
    exact mul_div_cancel₀ _ (pow_ne_zero _ hpK)
  have hcop : IsCoprime B (p : 𝓞 K) := split_coprime p h B hr hq
  let S := fractionalIdealCarrier (pseudolatticeSaturation P I)
  have hIS : I.val ≤ S := pseudolatticeSaturation_contains P I
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hu
    induction u using QuotientAddGroup.induction_on with
    | H u =>
      have hpk : p ^ k • u.val ∈ I.val := by
        have hi := congrArg (toAmbient P I) hk
        rw [map_nsmul, map_zero] at hi
        change p ^ k • ambientMk I.val u.val = 0 at hi
        rw [← map_nsmul] at hi
        exact (QuotientAddGroup.eq_zero_iff _).mp hi
      have hperiod : (P.epsilon - 1) * u.val ∈ I.val :=
        (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I _).mp u.property
      let x : K := (p : K) ^ s * u.val
      have hBx : (B : K) * x ∈ S := by
        apply hIS
        simpa only [x, ← mul_assoc, mul_comm (B : K) ((p : K) ^ s), heq] using hperiod
      have hax : (p : K) ^ k * x ∈ S := by
        have hi : (p : K) ^ s * (p ^ k • u.val) ∈ I.val := by
          simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
            using I.val.smul_mem (p ^ s : ℤ) hpk
        apply hIS
        simpa only [x, nsmul_eq_mul, Nat.cast_pow,
          mul_left_comm] using hi
      have hxS : x ∈ S := saturation_mem_of_coprime_mul_mem P I hcop.pow_right x hBx
        (by simpa only [map_pow, map_natCast] using hax)
      have hpx : p ^ k • x ∈ I.val := by
        have hi := I.val.smul_mem (p ^ s : ℤ) hpk
        simpa only [x, nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast,
          Nat.cast_pow, mul_left_comm] using hi
      have hxI := mem_of_saturation_mem P I hm k x hxS hpx
      change (p ^ s) • ambientMk I.val u.val = 0
      rw [← map_nsmul]
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      change p ^ s • u.val ∈ I.val
      simpa only [x, nsmul_eq_mul, Nat.cast_pow] using hxI
  · intro hy
    induction y using QuotientAddGroup.induction_on with
    | H y =>
      have hps : p ^ s • y ∈ I.val := by
        change p ^ s • ambientMk I.val y = 0 at hy
        rw [← map_nsmul] at hy
        exact (QuotientAddGroup.eq_zero_iff _).mp hy
      have hBi : (B : K) * ((p : K) ^ s * y) ∈ S := by
        exact (pseudolatticeSaturation P I).1.smul_mem B (hIS (by
          simpa only [nsmul_eq_mul, Nat.cast_pow] using hps))
      have hperS : (P.epsilon - 1) * y ∈ S := by
        simpa only [← mul_assoc, mul_comm (B : K) ((p : K) ^ s), heq] using hBi
      have hperpow : p ^ s • ((P.epsilon - 1) * y) ∈ I.val := by
        have hstable : (P.epsilon - 1) * (p ^ s • y) ∈ I.val := by
          rw [sub_mul, one_mul]
          apply I.val.sub_mem
          · rw [← I.property.2]
            exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨_, hps, rfl⟩
          · exact hps
        simpa only [nsmul_eq_mul, Nat.cast_pow, mul_left_comm] using hstable
      have hper := mem_of_saturation_mem P I hm s _ hperS hperpow
      have hyper : y ∈ pseudolatticePeriodPoints P I :=
        (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I _).mpr hper
      refine ⟨pseudolatticeMk P I y hyper, ?_, rfl⟩
      apply AddCommGroup.mem_primaryComponent.mpr
      refine ⟨s, ?_⟩
      apply toAmbient_injective P I
      rw [map_nsmul, map_zero, toAmbient_mk, ← map_nsmul]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hps


section FinitePrimarySplitting

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- A common annihilator prime to p forces the group order prime to p. -/
theorem coprime_card_of_annihilator {p m : ℕ} (hp : p.Prime)
    (hpm : Nat.Coprime p m) (hm : ∀ x : G, m • x = 0) :
    Nat.Coprime p (Nat.card G) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := G) p hdiv
  have hh : addOrderOf x ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (hm x)
  rw [hx] at hh
  exact (hp.coprime_iff_not_dvd.mp hpm) hh

/-- The p-primary component of a finite abelian group has a complement of order prime to p, with the
actual sum map providing the equivalence. -/
theorem finite_primary_splitting (p : ℕ) (hp : p.Prime) :
    ∃ C : AddSubgroup G, Nat.Coprime p (Nat.card C) ∧
      Nonempty ((AddCommGroup.primaryComponent G p × C) ≃+ G) := by
  let k := (Nat.card G).factorization p
  let a := p ^ k
  let m := ordCompl[p] (Nat.card G)
  have ham : a * m = Nat.card G := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hpm : Nat.Coprime p m := Nat.coprime_ordCompl hp Nat.card_pos.ne'
  have hcop : Nat.Coprime a m := hpm.pow_left k
  let C := LocalFourierSetup.pTorsion m (G := G)
  have hC : Nat.Coprime p (Nat.card C) :=
    coprime_card_of_annihilator hp hpm (fun x => Subtype.ext x.property)
  let H := AddCommGroup.primaryComponent G p
  let f : H × C →+ G :=
    { toFun := fun x => x.1.val + x.2.val
      map_zero' := by simp
      map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add,
        AddSubgroup.coe_add]; abel }
  have hf : Function.Bijective f := by
    constructor
    · apply (injective_iff_map_eq_zero f).mpr
      rintro ⟨x, y⟩ hxy
      change x.val + y.val = 0 at hxy
      obtain ⟨j, hj⟩ := AddCommGroup.mem_primaryComponent.mp x.property
      have hmy : m • y.val = 0 := y.property
      have hmx : m • x.val = 0 := by
        have hh := congrArg (fun z : G => m • z) hxy
        simpa only [smul_add, hmy, smul_zero, add_zero] using hh
      have hx0 : x.val = 0 := by
        have hh := (gcd_nsmul_eq_zero (a := x.val) (m := p ^ j) (n := m)).mpr
          ⟨hj, hmx⟩
        simpa only [(hpm.pow_left j).gcd_eq_one, one_smul] using hh
      have hy0 : y.val = 0 := by simpa only [hx0, zero_add] using hxy
      apply Prod.ext
      · exact Subtype.ext hx0
      · exact Subtype.ext hy0
    · intro z
      have haz : a • (m • z) = 0 := by
        rw [← mul_smul, ham]
        exact card_nsmul_eq_zero'
      have hmz : m • (a • z) = 0 := by
        rw [← mul_smul, mul_comm m a, ham]
        exact card_nsmul_eq_zero'
      let x : G := (Nat.gcdB a m) • (m • z)
      let y : G := (Nat.gcdA a m) • (a • z)
      have hx : x ∈ H := by
        apply AddCommGroup.mem_primaryComponent.mpr
        refine ⟨k, ?_⟩
        change a • ((Nat.gcdB a m) • (m • z)) = 0
        rw [smul_comm, haz, smul_zero]
      have hy : y ∈ C := by
        change m • ((Nat.gcdA a m) • (a • z)) = 0
        rw [smul_comm, hmz, smul_zero]
      refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
      change x + y = z
      have hbez : (a : ℤ) * Nat.gcdA a m + (m : ℤ) * Nat.gcdB a m = 1 := by
        rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
        rfl
      dsimp [x, y]
      rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul]
      have hc : Nat.gcdB a m * (m : ℤ) + Nat.gcdA a m * (a : ℤ) = 1 := by
        linear_combination hbez
      rw [hc, one_smul]
  exact ⟨C, hC, ⟨AddEquiv.ofBijective f hf⟩⟩

end FinitePrimarySplitting


theorem cyclic_torsion_generator {H : Type*} [AddCommGroup H] [Finite H]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s) (hcyc : IsAddCyclic H)
    (hcard : Nat.card H = p ^ s) :
    ∃ g : H, addOrderOf (p ^ (s - 1) • g) = p ∧
      LocalFourierSetup.pTorsion p = AddSubgroup.zmultiples (p ^ (s - 1) • g) := by
  classical
  letI : IsAddCyclic H := hcyc
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨g, hg⟩ := isAddCyclic_iff_exists_addOrderOf_eq_natCard.mp hcyc
  have hpow : p ^ s = p ^ (s - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have horder : addOrderOf (p ^ (s - 1) • g) = p := by
    rw [addOrderOf_nsmul, hg, hcard,
      Nat.gcd_eq_right (pow_dvd_pow p (by omega : s - 1 ≤ s)), hpow]
    exact Nat.mul_div_cancel_left p (pow_pos (Fact.out : p.Prime).pos _)
  have hbound : Nat.card (LocalFourierSetup.pTorsion p (G := H)) ≤ p := by
    change Nat.card {x : H // p • x = 0} ≤ p
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsAddCyclic.card_nsmul_eq_zero_le (Fact.out : p.Prime).pos
  have hmem : p ^ (s - 1) • g ∈ LocalFourierSetup.pTorsion p := by
    change p • (p ^ (s - 1) • g) = 0
    simpa only [horder] using addOrderOf_nsmul_eq_zero (p ^ (s - 1) • g)
  have hle : AddSubgroup.zmultiples (p ^ (s - 1) • g) ≤
      LocalFourierSetup.pTorsion p := AddSubgroup.zmultiples_le.mpr hmem
  have heq := AddSubgroup.eq_of_le_of_card_ge hle (by
    simpa only [Nat.card_zmultiples, horder] using hbound)
  exact ⟨g, horder, heq.symm⟩


theorem cyclic_line_torsion_card {G : Type*} [AddCommGroup G] [Finite G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s) (L : AddSubgroup G)
    (hcyc : IsAddCyclic L) (hcard : Nat.card L = p ^ s) :
    Nat.card ↥(L ⊓ LocalFourierSetup.pTorsion p (G := G)) = p := by
  obtain ⟨g, horder, hgen⟩ := cyclic_torsion_generator hs hcyc hcard
  let e : ↥(L ⊓ LocalFourierSetup.pTorsion p (G := G)) ≃
      ↥(LocalFourierSetup.pTorsion p (G := L)) :=
    { toFun := fun z => ⟨⟨z.val, z.prop.1⟩, by
        change p • (⟨z.val, z.prop.1⟩ : L) = 0
        exact Subtype.ext z.prop.2⟩
      invFun := fun z => ⟨z.val.val, ⟨z.val.prop, by
        change p • z.val.val = 0
        have hz : p • z.val = 0 := z.prop
        exact congrArg Subtype.val hz⟩⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  rw [Nat.card_congr e, hgen, Nat.card_zmultiples, horder]

theorem cyclic_line_torsion_lift {G : Type*} [AddCommGroup G] [Finite G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s) (L : AddSubgroup G)
    (hcyc : IsAddCyclic L) (hcard : Nat.card L = p ^ s)
    (z : G) (hz : z ∈ L ⊓ LocalFourierSetup.pTorsion p) :
    ∃ y ∈ L, p ^ (s - 1) • y = z := by
  obtain ⟨g, horder, hgen⟩ := cyclic_torsion_generator hs hcyc hcard
  have hzt : (⟨z, hz.1⟩ : L) ∈ LocalFourierSetup.pTorsion p (G := L) := by
    change p • (⟨z, hz.1⟩ : L) = 0
    exact Subtype.ext hz.2
  rw [hgen] at hzt
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hzt
  refine ⟨(n • g : L).val, (n • g : L).prop, ?_⟩
  have hsmul : p ^ (s - 1) • (n • g) = (⟨z, hz.1⟩ : L) := by
    rw [smul_comm]
    exact hn
  exact congrArg Subtype.val hsmul



/-- A finite additive group with at most p elements killed by p has at most p^n elements whenever
p^n annihilates the group. -/
theorem card_le_pow_of_torsion_card_le
    {H : Type*} [AddCommGroup H] [Finite H] (p n : ℕ)
    (hcard : Nat.card (LocalFourierSetup.pTorsion p (G := H)) ≤ p)
    (hkill : ∀ x : H, p ^ n • x = 0) : Nat.card H ≤ p ^ n := by
  induction n generalizing H with
  | zero =>
    haveI : Subsingleton H := ⟨fun x y => by
      have hx := hkill x
      have hy := hkill y
      simpa only [pow_zero, one_nsmul] using hx.trans hy.symm⟩
    simp
  | succ n ih =>
    let f : H →+ H := nsmulAddMonoidHom p
    have hker : Nat.card f.ker ≤ p := hcard
    have hrcard : Nat.card (LocalFourierSetup.pTorsion p (G := f.range)) ≤ p := by
      let j : LocalFourierSetup.pTorsion p (G := f.range) →
          LocalFourierSetup.pTorsion p (G := H) := fun x =>
        ⟨x.val.val, by
          change p • x.val.val = 0
          exact congrArg Subtype.val x.property⟩
      exact (Nat.card_le_card_of_injective j (fun x y hxy =>
        Subtype.ext (Subtype.ext (show x.val.val = y.val.val from
          congrArg (fun t : LocalFourierSetup.pTorsion p (G := H) => t.val)
            hxy)))).trans hcard
    have hrkill : ∀ x : f.range, p ^ n • x = 0 := by
      rintro ⟨x, y, rfl⟩
      apply Subtype.ext
      change p ^ n • (p • y) = 0
      simpa only [pow_succ', mul_nsmul] using hkill y
    have hr := ih hrcard hrkill
    calc
      Nat.card H = Nat.card f.ker * Nat.card f.range := by
        rw [← AddSubgroup.index_ker f, AddSubgroup.card_mul_index]
      _ ≤ p * p ^ n := Nat.mul_le_mul hker hr
      _ = p ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- A finite abelian p-group is cyclic if its elements of order dividing p form a subgroup of order
at most p. -/
theorem isAddCyclic_of_prime_power_torsion_card_le
    {H : Type*} [AddCommGroup H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hpower : ∀ x : H, ∃ n : ℕ, p ^ n • x = 0)
    (hcard : Nat.card (LocalFourierSetup.pTorsion p (G := H)) ≤ p) :
    IsAddCyclic H := by
  have hP : IsPGroup p (Multiplicative H) := fun x => hpower x
  obtain ⟨n, hn⟩ := hP.exists_exponent_eq_pow
  have hkill : ∀ x : H, p ^ n • x = 0 := by
    intro x
    change AddMonoid.exponent H = p ^ n at hn
    rw [← hn]
    exact AddMonoid.exponent_nsmul_eq_zero x
  have hc := card_le_pow_of_torsion_card_le p n hcard hkill
  apply IsAddCyclic.of_exponent_eq_card
  change AddMonoid.exponent H = p ^ n at hn
  exact le_antisymm (Nat.le_of_dvd Nat.card_pos AddGroup.exponent_dvd_nat_card)
    (hc.trans_eq hn.symm)

/-- It suffices to bound p-torsion in the whole finite abelian group. -/
theorem primary_cyclic_of_torsion_card_le
    {H : Type*} [AddCommGroup H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card (LocalFourierSetup.pTorsion p (G := H)) ≤ p) :
    IsAddCyclic (AddCommGroup.primaryComponent H p) := by
  let j : LocalFourierSetup.pTorsion p
      (G := AddCommGroup.primaryComponent H p) →
      LocalFourierSetup.pTorsion p (G := H) := fun x =>
    ⟨x.val.val, by
      change p • x.val.val = 0
      exact congrArg Subtype.val x.property⟩
  have hj : Function.Injective j := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg
      (fun t : LocalFourierSetup.pTorsion p (G := H) => t.val) hxy))
  apply isAddCyclic_of_prime_power_torsion_card_le (p := p)
  · intro x
    obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.mp x.property
    exact ⟨n, Subtype.ext hn⟩
  · exact (Nat.card_le_card_of_injective j hj).trans hcard

/-- If epsilon minus one does not carry the lattice into its multiple by p, the image of G_J[p] is a
proper subgroup of the ambient p-division group. -/
theorem period_pTorsion_image_lt_ambient (P : PeriodData K)
    (J : StablePseudolattice P) {p : ℕ} (hp : p ≠ 0)
    (h : ¬ pseudolatticeScale (P.epsilon - 1) J.val ≤
      pseudolatticeScale (p : K) J.val) :
    (LocalFourierSetup.pTorsion p (G := PseudolatticeGroup P J)).map
        (toAmbient P J) <
      LocalFourierSetup.pTorsion p (G := AmbientGroup J.val) := by
  have hle : (LocalFourierSetup.pTorsion p (G := PseudolatticeGroup P J)).map
      (toAmbient P J) ≤ LocalFourierSetup.pTorsion p (G := AmbientGroup J.val) := by
    rintro _ ⟨x, hx, rfl⟩
    change p • toAmbient P J x = 0
    change p • x = 0 at hx
    rw [← map_nsmul, hx, map_zero]
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply h
  intro x hx
  obtain ⟨z, hz, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
  let y : K := (p : K)⁻¹ * z
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hpy : (p : K) * y = z := by
    dsimp [y]
    rw [← mul_assoc, mul_inv_cancel₀ hpK, one_mul]
  have hy : ambientMk J.val y ∈ LocalFourierSetup.pTorsion p := by
    change p • ambientMk J.val y = 0
    rw [← map_nsmul]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    change p • y ∈ J.val
    simpa only [nsmul_eq_mul, hpy] using hz
  rw [← heq] at hy
  obtain ⟨u, _, hu⟩ := hy
  have hyfix := (mem_range_toAmbient_iff P J (ambientMk J.val y)).mp ⟨u, hu⟩
  have hyper : (P.epsilon - 1) * y ∈ J.val := by
    change ambientMk J.val (P.epsilon * y) = ambientMk J.val y at hyfix
    have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hyfix
    change P.epsilon * y - y ∈ J.val at hmem
    simpa only [sub_mul, one_mul] using hmem
  refine (pseudolatticeScale_mem_iff _ _ _).mpr
    ⟨(P.epsilon - 1) * y, hyper, ?_⟩
  calc
    (p : K) * ((P.epsilon - 1) * y) = (P.epsilon - 1) * ((p : K) * y) := by ring
    _ = (P.epsilon - 1) * z := by rw [hpy]

/-- A proper subgroup of a group of order p² has at most p elements. -/
theorem card_le_prime_of_lt_prime_sq {H : Type*} [AddGroup H]
    {p : ℕ} (hp : p.Prime) (A B : AddSubgroup H) [Finite B]
    (hAB : A < B) (hB : Nat.card B = p ^ 2) : Nat.card A ≤ p := by
  have hd : Nat.card A ∣ p ^ 2 := hB ▸ AddSubgroup.card_dvd_of_le hAB.le
  obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hlt := AddSubgroup.card_lt_of_lt hAB
  rw [hB] at hlt
  interval_cases k
  · simpa [heq] using hp.one_le
  · simpa [heq] using (le_refl p)
  · exact False.elim ((ne_of_lt hlt) heq)

/-- The cyclicity criterion with explicit rank-two division coordinates. -/
theorem primary_cyclic_of_not_mul_sub_one_le_pScale_of_equiv (P : PeriodData K)
    (J : StablePseudolattice P) {p : ℕ} [Fact p.Prime]
    (d : LocalFourierSetup.pTorsion p (G := AmbientGroup J.val) ≃+
      (Fin 2 → ZMod p))
    (h : ¬ pseudolatticeScale (P.epsilon - 1) J.val ≤
      pseudolatticeScale (p : K) J.val) :
    IsAddCyclic (AddCommGroup.primaryComponent (PseudolatticeGroup P J) p) := by
  letI : Finite (LocalFourierSetup.pTorsion p (G := AmbientGroup J.val)) :=
    Finite.of_equiv (Fin 2 → ZMod p) d.symm.toEquiv
  have hdiv : Nat.card (LocalFourierSetup.pTorsion p (G := AmbientGroup J.val)) = p ^ 2 := by
    rw [Nat.card_congr d.toEquiv]
    simp
  have hlt := period_pTorsion_image_lt_ambient P J
    (show p ≠ 0 from (Fact.out : p.Prime).ne_zero) h
  have hcard := card_le_prime_of_lt_prime_sq (Fact.out : p.Prime) _ _ hlt hdiv
  rw [AddSubgroup.card_map_of_injective (toAmbient_injective P J)] at hcard
  exact primary_cyclic_of_torsion_card_le hcard

/-- A nonzero period endomorphism modulo p forces the actual p-primary period group of a rank-two
pseudolattice to be cyclic. -/
theorem primary_cyclic_of_not_mul_sub_one_le_pScale (P : PeriodData K)
    (J : StablePseudolattice P) {p : ℕ} [Fact p.Prime]
    (h : ¬ pseudolatticeScale (P.epsilon - 1) J.val ≤
      pseudolatticeScale (p : K) J.val) :
    IsAddCyclic (AddCommGroup.primaryComponent (PseudolatticeGroup P J) p) := by
  obtain ⟨d⟩ := ambient_division_equiv P J p (Fact.out : p.Prime).ne_zero
  exact primary_cyclic_of_not_mul_sub_one_le_pScale_of_equiv P J d h




set_option backward.isDefEq.respectTransparency false in
theorem only_two_invariant_lines_of_stable {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (b : ZMod p) (hb : b ≠ 0) (L : AddSubgroup (ZMod p × ZMod p))
    (hL : Nat.card L = p)
    (hstable : ∀ z ∈ L, (b * z.1, -b * z.2) ∈ L) :
    L = (⊤ : AddSubgroup (ZMod p)).prod ⊥ ∨
      L = (⊥ : AddSubgroup (ZMod p)).prod ⊤ := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    exact hodd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz))
  have htwo_b : (2 : ZMod p) * b ≠ 0 := mul_ne_zero htwo hb
  have hmul (a : ZMod p) {z : ZMod p × ZMod p} (hz : z ∈ L) :
      (a * z.1, a * z.2) ∈ L := by
    have hmem := L.nsmul_mem hz a.val
    change (a.val • z.1, a.val • z.2) ∈ L at hmem
    simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using hmem
  have hproj₁ (z : ZMod p × ZMod p) (hz : z ∈ L) : (z.1, 0) ∈ L := by
    have hsum := L.add_mem (hstable z hz) (hmul b hz)
    have heq : (b * z.1, -b * z.2) + (b * z.1, b * z.2) =
        ((2 * b) * z.1, 0) := by
      apply Prod.ext
      · change b * z.1 + b * z.1 = (2 * b) * z.1
        rw [mul_assoc, two_mul]
      · change (-b) * z.2 + b * z.2 = 0
        erw [neg_mul, neg_add_cancel]
    rw [heq] at hsum
    simpa only [← mul_assoc, inv_mul_cancel₀ htwo_b, one_mul, mul_zero] using
      hmul (2 * b)⁻¹ hsum
  have hproj₂ (z : ZMod p × ZMod p) (hz : z ∈ L) : (0, z.2) ∈ L := by
    have hmem := L.sub_mem hz (hproj₁ z hz)
    change (z.1 - z.1, z.2 - 0) ∈ L at hmem
    simpa only [sub_self, sub_zero] using hmem
  have hne : L ≠ ⊥ := by
    apply (AddSubgroup.one_lt_card_iff_ne_bot L).mp
    simpa only [hL] using (Fact.out : p.Prime).one_lt
  rcases L.bot_or_exists_ne_zero with hbot | ⟨z, hz, hz0⟩
  · exact (hne hbot).elim
  by_cases hz₁ : z.1 = 0
  · right
    have hz₂ : z.2 ≠ 0 := by
      intro hz₂
      exact hz0 (Prod.ext hz₁ hz₂)
    have haxis : (⊥ : AddSubgroup (ZMod p)).prod ⊤ ≤ L := by
      intro w hw
      have hw₁ : w.1 = 0 := by simpa using hw.1
      have hw_eq : (0, w.2) = w := Prod.ext hw₁.symm rfl
      rw [← hw_eq]
      have hmem := hmul (w.2 * z.2⁻¹) (hproj₂ z hz)
      simpa only [mul_zero, mul_assoc, inv_mul_cancel₀ hz₂, mul_one] using hmem
    apply (AddSubgroup.eq_of_le_of_card_ge haxis ?_).symm
    rw [hL, Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv]
    simp [Nat.card_eq_fintype_card]
  · left
    have haxis : (⊤ : AddSubgroup (ZMod p)).prod ⊥ ≤ L := by
      intro w hw
      have hw₂ : w.2 = 0 := by simpa using hw.2
      have hw_eq : (w.1, 0) = w := Prod.ext rfl hw₂.symm
      rw [← hw_eq]
      have hmem := hmul (w.1 * z.1⁻¹) (hproj₁ z hz)
      simpa only [mul_zero, mul_assoc, inv_mul_cancel₀ hz₁, mul_one] using hmem
    apply (AddSubgroup.eq_of_le_of_card_ge haxis ?_).symm
    rw [hL, Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv]
    simp [Nat.card_eq_fintype_card]


/-- The actual saturation index clears multiplication by every integral element. -/
def saturationIndex (P : PeriodData K) (I : StablePseudolattice P) : ℕ :=
  inclusionIndex I.val (fractionalIdealCarrier (pseudolatticeSaturation P I))

theorem saturationIndex_mul_mem (P : PeriodData K) (I : StablePseudolattice P)
    (x : K) (hx : x ∈ fractionalIdealCarrier (pseudolatticeSaturation P I)) :
    (saturationIndex P I : K) * x ∈ I.val := by
  have hh : saturationIndex P I • x ∈ I.val :=
    I.val.toAddSubgroup.nsmul_relIndex_mem hx
  simpa only [nsmul_eq_mul] using hh

theorem clearedIntegral_preserves (P : PeriodData K) (I : StablePseudolattice P)
    (B : 𝓞 K) (x : K) (hx : x ∈ I.val) :
    ((saturationIndex P I : K) * (B : K)) * x ∈ I.val := by
  rw [mul_assoc]
  apply saturationIndex_mul_mem P I
  exact (pseudolatticeSaturation P I).1.smul_mem B
    (pseudolatticeSaturation_contains P I hx)

/-- Field multiplication descends whenever it preserves the original lattice. -/
def ambientScalar (I : Submodule ℤ K) (a : K)
    (ha : ∀ x ∈ I, a * x ∈ I) : AmbientGroup I →+ AmbientGroup I :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft a) ha

theorem scalar_preserves_periodPoints (P : PeriodData K) (I : StablePseudolattice P)
    (a : K) (ha : ∀ x ∈ I.val, a * x ∈ I.val)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    a * x ∈ pseudolatticePeriodPoints P I := by
  rw [DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem] at hx ⊢
  simpa only [mul_left_comm] using ha _ hx

def periodScalar (P : PeriodData K) (I : StablePseudolattice P) (a : K)
    (ha : ∀ x ∈ I.val, a * x ∈ I.val) :
    PseudolatticeGroup P I →+ PseudolatticeGroup P I :=
  QuotientAddGroup.map _ _
    { toFun := fun x => ⟨a * x.val, scalar_preserves_periodPoints P I a ha x x.property⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [mul_add] }
    (by intro x hx; exact ha x hx)

@[simp] theorem ambientScalar_mk (I : Submodule ℤ K) (a : K)
    (ha : ∀ x ∈ I, a * x ∈ I) (x : K) :
    ambientScalar I a ha (ambientMk I x) = ambientMk I (a * x) := rfl

@[simp] theorem periodScalar_mk (P : PeriodData K) (I : StablePseudolattice P)
    (a : K) (ha : ∀ x ∈ I.val, a * x ∈ I.val)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    periodScalar P I a ha (pseudolatticeMk P I x hx) =
      pseudolatticeMk P I (a * x) (scalar_preserves_periodPoints P I a ha x hx) := rfl

theorem toAmbient_periodScalar (P : PeriodData K) (I : StablePseudolattice P)
    (a : K) (ha : ∀ x ∈ I.val, a * x ∈ I.val) (x : PseudolatticeGroup P I) :
    toAmbient P I (periodScalar P I a ha x) =
      ambientScalar I.val a ha (toAmbient P I x) := by
  induction x using QuotientAddGroup.induction_on with
  | H x => rfl

/-- A contracted-prime relation annihilates the literal colon line. -/
theorem ambientScalar_primeLine (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) (A : 𝓞 K)
    (hA : ∀ x ∈ I.val, (A : K) * x ∈ I.val) (d : ℕ)
    (hr : A - (d : 𝓞 K) ∈ r.asIdeal)
    (x : AmbientGroup I.val) (hx : x ∈ primeLine P I r) :
    ambientScalar I.val (A : K) hA x = d • x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [ambientScalar_mk, ← map_nsmul]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  have hpres : ∀ z ∈ I.val, ((A - (d : 𝓞 K) : 𝓞 K) : K) * z ∈ I.val := by
    intro z hz
    simpa only [map_sub, map_natCast, sub_mul, nsmul_eq_mul] using
      I.val.sub_mem (hA z hz) (I.val.nsmul_mem hz d)
  change y ∈ inversePrimeCarrier P I r at hy
  simp only [inversePrimeCarrier, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mulLeft_apply] at hy
  have hkill := hy ⟨A - (d : 𝓞 K), hr, hpres⟩
  change (A : K) * y - d • y ∈ I.val
  simpa only [map_sub, map_natCast, sub_mul, nsmul_eq_mul] using hkill

theorem periodScalar_periodLine (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) (A : 𝓞 K)
    (hA : ∀ x ∈ I.val, (A : K) * x ∈ I.val) (d : ℕ)
    (hr : A - (d : 𝓞 K) ∈ r.asIdeal)
    (x : PseudolatticeGroup P I) (hx : x ∈ periodLine P I r) :
    periodScalar P I (A : K) hA x = d • x := by
  apply toAmbient_injective P I
  rw [toAmbient_periodScalar, map_nsmul]
  exact ambientScalar_primeLine P I r A hA d hr _ hx

/-- Additive coordinates determine a diagonal action from its two generators. -/
theorem diagonal_action_of_axes {G : Type*} [AddCommGroup G]
    {p : ℕ} [Fact p.Prime] (f : G →+ G)
    (c : (ZMod p × ZMod p) →+ G) (b : ZMod p)
    (hf₁ : f (c (1, 0)) = b.val • c (1, 0))
    (hf₂ : f (c (0, 1)) = (-b).val • c (0, 1)) (z : ZMod p × ZMod p) :
    f (c z) = c (b * z.1, -b * z.2) := by
  have hdec (w : ZMod p × ZMod p) :
      w = w.1.val • (1, 0) + w.2.val • (0, 1) := by
    ext <;> simp [nsmul_eq_mul]
  calc
    f (c z) = z.1.val • f (c (1, 0)) + z.2.val • f (c (0, 1)) := by
      conv_lhs => rw [hdec z]
      simp only [map_add, map_nsmul]
    _ = z.1.val • (b.val • c (1, 0)) +
        z.2.val • ((-b).val • c (0, 1)) := by rw [hf₁, hf₂]
    _ = c (z.1.val • (b.val • (1, 0)) +
        z.2.val • ((-b).val • (0, 1))) := by simp only [map_add, map_nsmul]
    _ = c (b * z.1, -b * z.2) := by
      congr 1
      ext <;> simp [nsmul_eq_mul, mul_comm]

theorem first_axis_zmultiples {p : ℕ} [Fact p.Prime] :
    (⊤ : AddSubgroup (ZMod p)).prod (⊥ : AddSubgroup (ZMod p)) =
      AddSubgroup.zmultiples ((1, 0) : ZMod p × ZMod p) := by
  ext z
  constructor
  · intro hz
    have hz₂ : z.2 = 0 := hz.2
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(z.1.val : ℤ), ?_⟩
    ext <;> simp [zsmul_eq_mul, hz₂]
  · rintro ⟨n, rfl⟩
    simp [AddSubgroup.mem_prod]

theorem second_axis_zmultiples {p : ℕ} [Fact p.Prime] :
    (⊥ : AddSubgroup (ZMod p)).prod (⊤ : AddSubgroup (ZMod p)) =
      AddSubgroup.zmultiples ((0, 1) : ZMod p × ZMod p) := by
  ext z
  constructor
  · intro hz
    have hz₁ : z.1 = 0 := hz.1
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(z.2.val : ℤ), ?_⟩
    ext <;> simp [zsmul_eq_mul, hz₁]
  · rintro ⟨n, rfl⟩
    simp [AddSubgroup.mem_prod]

/-- Transport the diagonal classification through actual torsion coordinates. -/
theorem invariant_line_of_coordinates {G : Type*} [AddCommGroup G]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (H A B : AddSubgroup G) (c : (ZMod p × ZMod p) ≃+ H)
    (hc₁ : AddSubgroup.zmultiples (c (1, 0)).val = A)
    (hc₂ : AddSubgroup.zmultiples (c (0, 1)).val = B)
    (f : G →+ G) (b : ZMod p) (hb : b ≠ 0)
    (hdiag : ∀ z, f (c z).val = (c (b * z.1, -b * z.2)).val)
    (N : AddSubgroup G) (hNH : N ≤ H) (hN : Nat.card N = p)
    (hstable : ∀ x ∈ N, f x ∈ N) : N = A ∨ N = B := by
  let F : (ZMod p × ZMod p) →+ G := H.subtype.comp c.toAddMonoidHom
  let M := N.comap F
  let fM : M →+ N :=
    { toFun := fun z => ⟨F z.val, z.property⟩
      map_zero' := by ext; exact F.map_zero
      map_add' := by intro z w; ext; exact F.map_add z.val w.val }
  let e : M ≃+ N := AddEquiv.ofBijective fM
    (by
      constructor
      · intro z w hzw
        apply Subtype.ext
        apply c.injective
        apply Subtype.ext
        have hh := congrArg (fun z : N => z.val) hzw
        change (c z.val).val = (c w.val).val at hh
        exact hh
      · intro y
        refine ⟨⟨c.symm ⟨y.val, hNH y.property⟩, ?_⟩, ?_⟩
        · change (c (c.symm ⟨y.val, hNH y.property⟩)).val ∈ N
          simpa using y.property
        · ext
          change (c (c.symm ⟨y.val, hNH y.property⟩)).val = y.val
          simp)
  have hM : Nat.card M = p := (Nat.card_congr e.toEquiv).trans hN
  have hMstable : ∀ z ∈ M, (b * z.1, -b * z.2) ∈ M := by
    intro z hz
    change (c (b * z.1, -b * z.2)).val ∈ N
    rw [← hdiag z]
    exact hstable _ hz
  have hmap : M.map F = N := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      refine ⟨c.symm ⟨x, hNH hx⟩, ?_, ?_⟩
      · change (c (c.symm ⟨x, hNH hx⟩)).val ∈ N
        simpa using hx
      · change (c (c.symm ⟨x, hNH hx⟩)).val = x
        simp
  rcases only_two_invariant_lines_of_stable hodd b hb M hM hMstable with hfirst | hsecond
  · left
    rw [← hmap, hfirst, first_axis_zmultiples, AddMonoidHom.map_zmultiples]
    exact hc₁
  · right
    rw [← hmap, hsecond, second_axis_zmultiples, AddMonoidHom.map_zmultiples]
    exact hc₂

/-- The cleared integral action has exactly the two actual split-prime lines as invariant order-p
subgroups of the period p-torsion. -/
theorem clearedIntegral_invariant_line (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p)
    (ρ : 𝓞 K →+* ZMod p × ZMod p)
    (hρ : Function.Surjective ρ ∧
      (∀ a : 𝓞 K, (ρ a).1 = 0 ↔ a ∈ r.asIdeal) ∧
      (∀ a : 𝓞 K, (ρ a).2 = 0 ↔ a ∈ q.asIdeal))
    (B : 𝓞 K) (b : ZMod p) (hb : b ≠ 0) (hB : ρ B = (b, -b))
    (N : AddSubgroup (PseudolatticeGroup P I))
    (hNH : N ≤ LocalFourierSetup.pTorsion p) (hN : Nat.card N = p)
    (hstable : ∀ x ∈ N,
      periodScalar P I ((saturationIndex P I : K) * (B : K))
        (clearedIntegral_preserves P I B) x ∈ N) :
    N = periodLine P I r ∨ N = periodLine P I q := by
  let m := saturationIndex P I
  let A : 𝓞 K := (m : 𝓞 K) * B
  let a : ZMod p := (m : ZMod p) * b
  have ha : a ≠ 0 := by
    apply mul_ne_zero ?_ hb
    exact ((ZMod.isUnit_iff_coprime m p).mpr hm.symm).ne_zero
  have hA : ∀ x ∈ I.val, (A : K) * x ∈ I.val := by
    intro x hx
    simpa only [A, map_mul, map_natCast] using clearedIntegral_preserves P I B x hx
  have hρA : ρ A = (a, -a) := by
    dsimp [A]
    rw [map_mul, map_natCast, hB]
    apply Prod.ext
    · rfl
    · change (m : ZMod p) * -b = -((m : ZMod p) * b)
      exact mul_neg _ _
  have hrA : A - (a.val : 𝓞 K) ∈ r.asIdeal := by
    apply (hρ.2.1 _).mp
    rw [map_sub, map_natCast, hρA]
    change a - (a.val : ZMod p) = 0
    simp
  have hqA : A - ((-a).val : 𝓞 K) ∈ q.asIdeal := by
    apply (hρ.2.2 _).mp
    rw [map_sub, map_natCast, hρA]
    change -a - ((-a).val : ZMod p) = 0
    simp
  obtain ⟨hsp, hd, hcr, hcq⟩ := periodLine_decomposition P I (Fact.out : p.Prime) hm h hη
  obtain ⟨c, hc₁, hc₂⟩ := coordinates_of_prime_order
    (periodLine P I r) (periodLine P I q) (LocalFourierSetup.pTorsion p) hd hsp hcr hcq
  let F : (ZMod p × ZMod p) →+ PseudolatticeGroup P I :=
    (LocalFourierSetup.pTorsion p).subtype.comp c.toAddMonoidHom
  have hf₁ : periodScalar P I (A : K) hA (F (1, 0)) = a.val • F (1, 0) := by
    apply periodScalar_periodLine P I r A hA a.val hrA
    rw [← hc₁]
    exact AddSubgroup.mem_zmultiples _
  have hf₂ : periodScalar P I (A : K) hA (F (0, 1)) = (-a).val • F (0, 1) := by
    apply periodScalar_periodLine P I q A hA (-a).val hqA
    rw [← hc₂]
    exact AddSubgroup.mem_zmultiples _
  apply invariant_line_of_coordinates hodd _ _ _ c hc₁ hc₂
    (periodScalar P I (A : K) hA) a ha ?_ N hNH hN ?_
  · exact diagonal_action_of_axes _ F a hf₁ hf₂
  · intro x hx
    simpa only [A, map_mul, map_natCast] using hstable x hx

/-- If epsilon minus one maps the overlattice into p times itself, the cleared exact leading action
stabilizes the cyclic subgroup's p-torsion. -/
theorem clearedLeading_stable_of_containment (P : PeriodData K)
    (I : StablePseudolattice P) {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s)
    (B : 𝓞 K) (heq : (p : K) ^ s * (B : K) = P.epsilon - 1)
    (L : AddSubgroup (PseudolatticeGroup P I))
    (hlift : ∀ x ∈ L ⊓ LocalFourierSetup.pTorsion p,
      ∃ y ∈ L, p ^ (s - 1) • y = x)
    (hcontain : pseudolatticeScale (P.epsilon - 1) (subgroupLattice P I L).val ≤
      pseudolatticeScale (p : K) (subgroupLattice P I L).val) :
    ∀ x ∈ L ⊓ LocalFourierSetup.pTorsion p,
      periodScalar P I ((saturationIndex P I : K) * (B : K))
        (clearedIntegral_preserves P I B) x ∈ L ⊓ LocalFourierSetup.pTorsion p := by
  let J := (subgroupLattice P I L).val
  let m := saturationIndex P I
  let f := periodScalar P I ((m : K) * (B : K)) (clearedIntegral_preserves P I B)
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpow : (p : K) ^ s = (p : K) * (p : K) ^ (s - 1) := by
    nth_rw 1 [← Nat.sub_add_cancel hs]
    rw [pow_succ]
    ring
  intro x hx
  constructor
  · obtain ⟨y, hy, hxy⟩ := hlift x hx
    let z := pseudolatticeRepresentative P I y
    have hz : z ∈ J := by
      refine ⟨(Quotient.out y).property, ?_⟩
      simpa only [z, DistributionSubgroupLatticeAux.mk_representative] using hy
    let t := (p : K) ^ (s - 1) * (B : K) * z
    have het : (p : K) * t = (P.epsilon - 1) * z := by
      rw [← heq, hpow]
      dsimp [t]
      ring
    have hmul : (P.epsilon - 1) * z ∈ pseudolatticeScale (P.epsilon - 1) J :=
      (pseudolatticeScale_mem_iff _ _ _).mpr ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hw_eq⟩ := (pseudolatticeScale_mem_iff _ _ _).mp (hcontain hmul)
    have htw : t = w := mul_left_cancel₀ hpK (het.trans hw_eq.symm)
    have htJ : t ∈ J := htw.symm ▸ hw
    have hmtJ : (m : K) * t ∈ J := by
      have hh : m • t ∈ J := J.nsmul_mem htJ m
      simpa only [nsmul_eq_mul] using hh
    obtain ⟨hmtper, hmtL⟩ := hmtJ
    have hfx : f x = pseudolatticeMk P I ((m : K) * t) hmtper := by
      apply toAmbient_injective P I
      calc
        toAmbient P I (f x) =
            ambientScalar I.val ((m : K) * (B : K))
              (clearedIntegral_preserves P I B) (toAmbient P I x) :=
          toAmbient_periodScalar P I _ _ x
        _ = ambientScalar I.val ((m : K) * (B : K))
              (clearedIntegral_preserves P I B)
              (p ^ (s - 1) • ambientMk I.val z) := by
          rw [← hxy, map_nsmul, DistributionSubgroupLatticeAux.toAmbient_representative]
        _ = ambientMk I.val ((m : K) * t) := by
          rw [map_nsmul, ambientScalar_mk, ← map_nsmul]
          congr 1
          simp only [t, nsmul_eq_mul, Nat.cast_pow]
          ring
        _ = toAmbient P I (pseudolatticeMk P I ((m : K) * t) hmtper) := rfl
    change f x ∈ L
    exact hfx.symm ▸ hmtL
  · change p • f x = 0
    rw [← map_nsmul]
    have hpx : p • x = 0 := hx.2
    rw [hpx, map_zero]

/-- Exact leading data and a noncharacteristic cyclic subgroup force the local nondivisibility used
by the rank-two cyclicity criterion. -/
theorem noncharacteristic_not_containment_of_leading_data (P : PeriodData K)
    (I : StablePseudolattice P) {p s : ℕ} [Fact p.Prime]
    (hodd : p ≠ 2) (hs : 1 ≤ s) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p)
    (B : 𝓞 K) (heq : (p : K) ^ s * (B : K) = P.epsilon - 1)
    (ρ : 𝓞 K →+* ZMod p × ZMod p)
    (hρ : Function.Surjective ρ ∧
      (∀ a : 𝓞 K, (ρ a).1 = 0 ↔ a ∈ r.asIdeal) ∧
      (∀ a : 𝓞 K, (ρ a).2 = 0 ↔ a ∈ q.asIdeal))
    (b : ZMod p) (hb : b ≠ 0) (hB : ρ B = (b, -b))
    (L : AddSubgroup (PseudolatticeGroup P I))
    (hcyc : IsAddCyclic L) (hcard : Nat.card L = p ^ s)
    (hrL : L ⊓ LocalFourierSetup.pTorsion p ≠ periodLine P I r)
    (hqL : L ⊓ LocalFourierSetup.pTorsion p ≠ periodLine P I q) :
    ¬ pseudolatticeScale (P.epsilon - 1) (subgroupLattice P I L).val ≤
      pseudolatticeScale (p : K) (subgroupLattice P I L).val := by
  intro hcontain
  have hlinecard := cyclic_line_torsion_card hs L hcyc hcard
  have hlift := cyclic_line_torsion_lift hs L hcyc hcard
  have hstable := clearedLeading_stable_of_containment P I (Fact.out : p.Prime)
    hs B heq L hlift hcontain
  rcases clearedIntegral_invariant_line P I hodd hm h hη ρ hρ B b hb hB
    (L ⊓ LocalFourierSetup.pTorsion p) inf_le_right hlinecard hstable with hr | hq
  · exact hrL hr
  · exact hqL hq

end SICLean.L5.SplitPrimeGeometryAux
