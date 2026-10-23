import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false

/-!
# Finite group algebra for [RW-rec, Lemma 6]

The counting argument first counts generators and then divides by the
number of generators of one full cyclic subgroup. Character kernels are handled
separately, using a primitive coordinate character and an explicit complement.
Completeness of complex characters detects the integer group-ring identity. No
split-prime or special-value result is imported.
-/

noncomputable section
open scoped BigOperators Classical

namespace SICLean.L5.SplitGroupRingAux

variable {H : Type*} [AddCommGroup H]

def exponentEval {A : Type*} [CommGroup A] (g : H → A)
    (w : AddMonoidAlgebra ℤ H) : A := w.coeff.prod (fun x n => g x ^ n)

theorem exponent_sum {A ι : Type*} [CommGroup A] (g : H → A)
    (S : Finset ι) (f : ι → AddMonoidAlgebra ℤ H) :
    exponentEval g (∑ i ∈ S, f i) = ∏ i ∈ S, exponentEval g (f i) := by
  induction S using Finset.induction_on with
  | empty => simp [exponentEval]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hadd (v w : AddMonoidAlgebra ℤ H) :
        exponentEval g (v + w) = exponentEval g v * exponentEval g w :=
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ => zpow_add _)
    rw [hadd, ih]

@[simp] theorem exponent_single {A : Type*} [CommGroup A] (g : H → A) (x : H) (n : ℤ) :
    exponentEval g (AddMonoidAlgebra.single x n) = g x ^ n := by
  simp [exponentEval]

/-- Evaluation at a genuine character is a ring homomorphism. -/
def characterHom (χ : AddChar H ℂ) : AddMonoidAlgebra ℤ H →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (Int.castRingHom ℂ) χ.toMonoidHom
    (fun _ _ => Commute.all _ _)

theorem characterHom_apply (χ : AddChar H ℂ) (v : AddMonoidAlgebra ℤ H) :
    characterHom χ v = v.coeff.sum (fun x n => (n : ℂ) * χ x) := rfl

@[simp] theorem characterHom_single (χ : AddChar H ℂ) (x : H) (n : ℤ) :
    characterHom χ (AddMonoidAlgebra.single x n) = (n : ℂ) * χ x := by
  simp [characterHom]

theorem characterHom_fintype [Fintype H] (χ : AddChar H ℂ)
    (v : AddMonoidAlgebra ℤ H) :
    characterHom χ v = ∑ x, (v.coeff x : ℂ) * χ x := by
  rw [characterHom_apply, Finsupp.sum_fintype]
  intro x
  simp

/-- Completeness of complex characters also detects integer coefficients. -/
theorem characterHom_ext [Fintype H] (v w : AddMonoidAlgebra ℤ H)
    (h : ∀ χ : AddChar H ℂ, characterHom χ v = characterHom χ w) : v = w := by
  let T : (H → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∑ x, ((v.coeff x : ℂ) - (w.coeff x : ℂ)) * f x
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm] }
  have hT : T = 0 := by
    apply (AddChar.complexBasis H).ext
    intro χ
    simp only [AddChar.complexBasis_apply, LinearMap.zero_apply]
    change (∑ x, ((v.coeff x : ℂ) - (w.coeff x : ℂ)) * χ x) = 0
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (by simpa only [characterHom_fintype] using h χ)
  ext x
  have hx := LinearMap.congr_fun hT (fun y => if y = x then 1 else 0)
  have hx' : (v.coeff x : ℂ) = (w.coeff x : ℂ) := by
    simpa [T, sub_eq_zero] using hx
  exact_mod_cast hx'

/-- The character sum over a subgroup has only the trivial-character term. -/
theorem character_sum (χ : AddChar H ℂ) (L : AddSubgroup H) [Fintype L] :
    (∑ l : L, χ l.val) = if ∀ l : L, χ l.val = 1 then (Nat.card L : ℂ) else 0 := by
  let ψ := χ.compAddMonoidHom L.subtype
  have heq : ψ = 0 ↔ ∀ l : L, χ l.val = 1 := by
    constructor
    · intro h l
      exact DFunLike.congr_fun h l
    · intro h
      ext l
      exact h l
  calc
    (∑ l : L, χ l.val) = ∑ l : L, ψ l := by
      apply Finset.sum_congr rfl
      intro l _
      rfl
    _ = _ := by
      rw [AddChar.sum_eq_ite]
      simp only [heq, Nat.card_eq_fintype_card]

section CyclicCounting
variable [Fintype H]

theorem card_zmultiples_fiber (L : AddSubgroup H) (q : ℕ)
    (hcyc : IsAddCyclic L) (hq : Nat.card L = q) :
    (Finset.univ.filter fun x : H => AddSubgroup.zmultiples x = L).card = q.totient := by
  letI : IsAddCyclic L := hcyc
  letI : Fintype L := Fintype.ofFinite L
  let e : {x : H // AddSubgroup.zmultiples x = L} ≃ {x : L // addOrderOf x = q} :=
    { toFun := fun x => ⟨⟨x.1, by
        simpa only [x.2] using AddSubgroup.mem_zmultiples x.1⟩, by
          rw [← AddSubgroup.addOrderOf_coe, ← Nat.card_zmultiples, x.2, hq]⟩
      invFun := fun x => ⟨x.1.1, by
        apply AddSubgroup.eq_of_le_of_card_ge
        · exact AddSubgroup.zmultiples_le.mpr x.1.2
        · rw [hq, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe, x.2]⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr e, Fintype.card_subtype]
  apply IsAddCyclic.card_addOrderOf_eq_totient
  rw [← Nat.card_eq_fintype_card, hq]

theorem card_generators_of_finset (S : Finset (AddSubgroup H)) (q : ℕ)
    (hS : ∀ L ∈ S, IsAddCyclic L ∧ Nat.card L = q) :
    (Finset.univ.filter fun x : H => AddSubgroup.zmultiples x ∈ S).card =
      S.card * q.totient := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ S
    (fun x : H => AddSubgroup.zmultiples x)]
  calc
    ∑ L ∈ S, (Finset.univ.filter fun x : H => AddSubgroup.zmultiples x = L).card =
        ∑ _L ∈ S, q.totient := by
      apply Finset.sum_congr rfl
      intro L hL
      exact card_zmultiples_fiber L q (hS L hL).1 (hS L hL).2
    _ = S.card * q.totient := by simp

theorem card_preimage_finset {G : Type*} [AddCommGroup G]
    (f : H →+ G) (T : Finset G) (hT : ∀ y ∈ T, y ∈ Set.range f) :
    (Finset.univ.filter fun x : H => f x ∈ T).card = T.card * Nat.card f.ker := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ T f]
  calc
    ∑ y ∈ T, (Finset.univ.filter fun x : H => f x = y).card =
        ∑ _y ∈ T, Nat.card f.ker := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [AddMonoidHom.card_fiber_eq_of_mem_range f (hT y hy) ⟨0, map_zero f⟩]
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      rfl
    _ = _ := by simp

theorem card_avoid_two_subgroups (K A B : AddSubgroup H) (p : ℕ) (hp : 1 ≤ p)
    (hA : A ≤ K) (hB : B ≤ K) (hd : Disjoint A B)
    (hK : Nat.card K = p ^ 2) (hAc : Nat.card A = p) (hBc : Nat.card B = p) :
    (Finset.univ.filter fun y : H => y ∈ K ∧ y ∉ A ∧ y ∉ B).card = (p - 1) ^ 2 := by
  let U := Finset.univ.filter fun y : H => y ∈ K
  let V := Finset.univ.filter fun y : H => y ∈ A
  let W := Finset.univ.filter fun y : H => y ∈ B
  have hUc : U.card = p ^ 2 := by
    simpa only [U, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card] using hK
  have hVc : V.card = p := by
    simpa only [V, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card] using hAc
  have hWc : W.card = p := by
    simpa only [W, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card] using hBc
  have hsub : V ∪ W ⊆ U := by
    intro y hy
    simp only [Finset.mem_union, V, W, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hy.elim (fun hy => hA hy) (fun hy => hB hy)
  have hi : V ∩ W = {0} := by
    ext y
    simp only [V, W, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · intro hy
      exact AddSubgroup.disjoint_def.mp hd hy.1 hy.2
    · rintro rfl
      exact ⟨A.zero_mem, B.zero_mem⟩
  have heq : (Finset.univ.filter fun y : H => y ∈ K ∧ y ∉ A ∧ y ∉ B) = U \ (V ∪ W) := by
    ext y
    simp [U, V, W]
  rw [heq]
  have hcunion := Finset.card_union_add_card_inter V W
  have hcsdiff := Finset.card_sdiff_add_card_eq_card hsub
  rw [hi, Finset.card_singleton, hVc, hWc] at hcunion
  rw [hUc] at hcsdiff
  have hpm := Nat.sub_add_cancel hp
  nlinarith

theorem zmultiples_inf_nsmul_ker (p k : ℕ) (hp : p ≠ 0) (x : H)
    (hx : addOrderOf x = p * k) :
    AddSubgroup.zmultiples x ⊓ (nsmulAddMonoidHom p : H →+ H).ker =
      AddSubgroup.zmultiples (k • x) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy.1
    have hy2 : p • (n • x) = 0 := hy.2
    have hz : ((p : ℤ) * n) • x = 0 := by
      simpa only [mul_zsmul, natCast_zsmul] using hy2
    have hd : (k : ℤ) ∣ n := by
      have hh := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
      rw [hx, Nat.cast_mul] at hh
      exact (mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr hp)).mp hh
    obtain ⟨m, rfl⟩ := hd
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m, ?_⟩
    rw [mul_comm (k : ℤ) m, mul_zsmul, natCast_zsmul]
  · apply AddSubgroup.zmultiples_le.mpr
    constructor
    · exact AddSubgroup.nsmul_mem_zmultiples x k
    · change p • (k • x) = 0
      rw [smul_smul, ← hx, addOrderOf_nsmul_eq_zero]

theorem card_pi_nsmul_ker (n d m : ℕ) [NeZero n] :
    Nat.card (nsmulAddMonoidHom m : (Fin d → ZMod n) →+ (Fin d → ZMod n)).ker =
      n.gcd m ^ d := by
  let K := (nsmulAddMonoidHom m : ZMod n →+ ZMod n).ker
  let e : (nsmulAddMonoidHom m : (Fin d → ZMod n) →+ (Fin d → ZMod n)).ker ≃
      (Fin d → K) :=
    { toFun := fun x i => ⟨x.1 i, by
        have hx : m • x.1 = 0 := x.2
        exact congrFun hx i⟩
      invFun := fun x => ⟨fun i => (x i).1, by
        change m • (fun i => (x i).1) = 0
        funext i
        exact (x i).2⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by funext i; apply Subtype.ext; rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin]
  congr 1
  dsimp [K]
  rw [IsAddCyclic.card_nsmulAddMonoidHom_ker]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem zmod_isUnit_of_top_nsmul_ne_zero {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (u : ZMod (p ^ s)) (hu : p ^ (s - 1) • u ≠ 0) : IsUnit u := by
  rw [← ZMod.natCast_zmod_val u]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (by omega)).mpr
  rintro ⟨v, hv⟩
  apply hu
  rw [← ZMod.natCast_zmod_val u, hv, nsmul_eq_mul, ← Nat.cast_mul]
  have heq : p ^ (s - 1) * (p * v) = p ^ s * v := by
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hs]
  rw [heq, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem zmultiples_isCompl_ker_eval_of_isUnit (n d : ℕ) [NeZero n]
    (x : Fin d → ZMod n) (i : Fin d) (hi : IsUnit (x i)) :
    IsCompl (AddSubgroup.zmultiples x) (Pi.evalAddMonoidHom (fun _ : Fin d => ZMod n) i).ker := by
  constructor
  · apply AddSubgroup.disjoint_def.mpr
    intro y hy hK
    obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    have hK' : (z • x) i = 0 := hK
    have hc : (z : ZMod n) * x i = 0 := by
      simpa only [Pi.smul_apply, zsmul_eq_mul] using hK'
    have hz : (z : ZMod n) = 0 := hi.mul_right_cancel (by simpa using hc)
    funext j
    simp only [Pi.smul_apply, zsmul_eq_mul, hz, zero_mul, Pi.zero_apply]
  · apply codisjoint_iff_le_sup.mpr
    intro y _
    obtain ⟨u, hu⟩ := hi
    let r : ZMod n := y i * (↑u⁻¹ : ZMod n)
    let l : Fin d → ZMod n := r.val • x
    have hr : r * x i = y i := by
      dsimp [r]
      rw [← hu, mul_assoc, Units.inv_mul, mul_one]
    have hl : l i = y i := by
      change r.val • x i = y i
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
      exact hr
    apply AddSubgroup.mem_sup.mpr
    refine ⟨l, AddSubgroup.nsmul_mem_zmultiples x r.val, y - l, ?_, ?_⟩
    · change (y - l) i = 0
      simp only [Pi.sub_apply, hl, sub_self]
    · exact add_sub_cancel l y

end CyclicCounting

section Kernel
variable {R A : Type*} [AddCommGroup R] [AddCommGroup A]

def kernelSnd (f : R × R →+ A) : f.ker →+ R :=
  (AddMonoidHom.snd R R).comp f.ker.subtype

theorem kernelSnd_bijective (f : R × R →+ A)
    (hi : Function.Injective (f.comp (AddMonoidHom.inl R R)))
    (hr : ∀ y : R, ∃ x : R, f (x, 0) = f (0, y)) :
    Function.Bijective (kernelSnd f) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · apply hi
      change f (x.val.1, 0) = f (y.val.1, 0)
      have hx := x.property
      have hy := y.property
      change f x.val = 0 at hx
      change f y.val = 0 at hy
      change x.val.2 = y.val.2 at hxy
      have hfx : f (x.val.1, 0) + f (0, x.val.2) = 0 := by
        rw [← map_add]
        simpa using hx
      have hfy : f (y.val.1, 0) + f (0, x.val.2) = 0 := by
        rw [hxy, ← map_add]
        simpa using hy
      exact add_right_cancel (hfx.trans hfy.symm)
    · exact hxy
  · intro y
    obtain ⟨x, hx⟩ := hr (-y)
    refine ⟨⟨(x, y), ?_⟩, rfl⟩
    change f (x, y) = 0
    have hx' : f (x, 0) = - f (0, y) := by
      rw [show (0, -y) = (-(0, y) : R × R) by simp, map_neg] at hx
      exact hx
    calc
      f (x, y) = f (x, 0) + f (0, y) := by
        simp only [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      _ = 0 := by rw [hx', neg_add_cancel]

def kernelEquiv (f : R × R →+ A)
    (hi : Function.Injective (f.comp (AddMonoidHom.inl R R)))
    (hr : ∀ y : R, ∃ x : R, f (x, 0) = f (0, y)) :
    f.ker ≃+ R := AddEquiv.ofBijective (kernelSnd f) (kernelSnd_bijective f hi hr)

theorem kernel_isCompl (f : R × R →+ A)
    (hi : Function.Injective (f.comp (AddMonoidHom.inl R R)))
    (hr : ∀ y : R, ∃ x : R, f (x, 0) = f (0, y)) :
    IsCompl f.ker (AddMonoidHom.inl R R).range := by
  constructor
  · rw [AddSubgroup.disjoint_def]
    intro x hx hx'
    obtain ⟨r, rfl⟩ := hx'
    have hzero : f (r, 0) = f (0, 0) := by
      change f (r, 0) = f 0
      simpa using hx
    have hrzero : r = 0 := hi hzero
    simp [hrzero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨z, hz⟩ := (kernelSnd_bijective f hi hr).2 x.2
    refine AddSubgroup.mem_sup.mpr ⟨z, z.property, (x.1-z.val.1, 0), ?_, ?_⟩
    · exact ⟨x.1-z.val.1, rfl⟩
    · apply Prod.ext
      · simp
      · simpa [kernelSnd] using hz

end Kernel

def unitCharacter (χ : AddChar H ℂ) : H →+ Additive ℂˣ where
  toFun x := Additive.ofMul (χ.val_isUnit x).unit
  map_zero' := by
    change (χ.val_isUnit 0).unit = 1
    apply Units.ext
    simp only [IsUnit.unit_spec, AddChar.map_zero_eq_one, Units.val_one]
  map_add' x y := by
    change (χ.val_isUnit (x + y)).unit =
      (χ.val_isUnit x).unit * (χ.val_isUnit y).unit
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul, AddChar.map_add_eq_mul]

@[simp] theorem unitCharacter_eq_zero (χ : AddChar H ℂ) (x : H) :
    unitCharacter χ x = 0 ↔ χ x = 1 := by
  change (χ.val_isUnit x).unit = 1 ↔ χ x = 1
  rw [Units.ext_iff]
  simp only [IsUnit.unit_spec, Units.val_one]

theorem unitCharacter_eq_iff (χ : AddChar H ℂ) (x y : H) :
    unitCharacter χ x = unitCharacter χ y ↔ χ x = χ y := by
  change (χ.val_isUnit x).unit = (χ.val_isUnit y).unit ↔ χ x = χ y
  rw [Units.ext_iff]
  simp only [IsUnit.unit_spec, Units.val_one]

theorem zmod_character_apply {n : ℕ} [NeZero n] (χ : AddChar (ZMod n) ℂ)
    (x : ZMod n) : χ x = χ 1 ^ x.val := by
  simpa only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] using
    χ.map_nsmul_eq_pow x.val 1

theorem zmod_character_injective {n : ℕ} [NeZero n] (χ : AddChar (ZMod n) ℂ)
    (hχ : IsPrimitiveRoot (χ 1) n) : Function.Injective χ := by
  rw [AddChar.injective_iff]
  intro x hx
  rw [zmod_character_apply] at hx
  have hn := (hχ.pow_eq_one_iff_dvd x.val).mp hx
  rw [← ZMod.natCast_zmod_val x]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hn

theorem zmod_character_pow {n : ℕ} [NeZero n] (χ : AddChar (ZMod n) ℂ)
    (x : ZMod n) : χ x ^ n = 1 := by
  rw [← χ.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

theorem primitive_character_kernel {n : ℕ} [NeZero n]
    (χ : AddChar (ZMod n × ZMod n) ℂ)
    (hχ : IsPrimitiveRoot (χ (1, 0)) n) :
    IsAddCyclic (unitCharacter χ).ker ∧
    Nat.card (unitCharacter χ).ker = n ∧
    ∃ T : AddSubgroup (ZMod n × ZMod n),
      IsCompl (unitCharacter χ).ker T := by
  let f := unitCharacter χ
  have hi : Function.Injective (f.comp (AddMonoidHom.inl (ZMod n) (ZMod n))) := by
    intro x y hxy
    exact zmod_character_injective (χ.compAddMonoidHom (AddMonoidHom.inl _ _))
      hχ ((unitCharacter_eq_iff χ _ _).mp hxy)
  have hr : ∀ y : ZMod n, ∃ x : ZMod n, f (x, 0) = f (0, y) := by
    intro y
    have hy : χ (0, y) ^ n = 1 :=
      zmod_character_pow (χ.compAddMonoidHom (AddMonoidHom.inr _ _)) y
    obtain ⟨i, _, hi⟩ := hχ.eq_pow_of_pow_eq_one hy
    refine ⟨i, (unitCharacter_eq_iff χ _ _).mpr ?_⟩
    calc
      χ ((i : ZMod n), 0) = χ (1, 0) ^ i := by
        simpa [nsmul_eq_mul] using χ.map_nsmul_eq_pow i (1, 0)
      _ = χ (0, y) := hi
  have e := kernelEquiv f hi hr
  refine ⟨e.isAddCyclic.mpr inferInstance, ?_, ⟨_, kernel_isCompl f hi hr⟩⟩
  calc
    Nat.card f.ker = Nat.card (ZMod n) := Nat.card_congr e.toEquiv
    _ = n := Nat.card_zmod n

theorem zmod_pTorsion {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s) :
    (nsmulAddMonoidHom p : ZMod (p ^ s) →+ ZMod (p ^ s)).ker =
      AddSubgroup.zmultiples (p ^ (s - 1) : ZMod (p ^ s)) := by
  have htop : AddSubgroup.zmultiples (1 : ZMod (p ^ s)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simp⟩
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpow : p ^ s = p * p ^ (s - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hs]
  simpa only [htop, top_inf_eq, nsmul_eq_mul, mul_one, Nat.cast_pow] using
    zmultiples_inf_nsmul_ker p (p ^ (s - 1)) hp (1 : ZMod (p ^ s))
      ((ZMod.addOrderOf_one _).trans hpow)

theorem character_primitive_of_top_ne_one {p s : ℕ} [Fact p.Prime]
    (hs : 1 ≤ s) (χ : AddChar (ZMod (p ^ s)) ℂ)
    (hχ : χ (p ^ (s - 1)) ≠ 1) :
    IsPrimitiveRoot (χ 1) (p ^ s) := by
  letI : NeZero (p ^ s) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  have hnot : χ 1 ^ (p ^ (s - 1)) ≠ 1 := by
    simpa [← χ.map_nsmul_eq_pow, nsmul_eq_mul] using hχ
  have hfin : χ 1 ^ (p ^ ((s - 1) + 1)) = 1 := by
    rw [Nat.sub_add_cancel hs]
    exact zmod_character_pow χ 1
  simpa only [Nat.sub_add_cancel hs] using orderOf_eq_prime_pow hnot hfin

theorem character_primitive_coordinate {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (χ : AddChar (ZMod (p ^ s) × ZMod (p ^ s)) ℂ)
    (a : ZMod (p ^ s) × ZMod (p ^ s))
    (ha : p • a = 0) (hχ : χ a ≠ 1) :
    IsPrimitiveRoot (χ (1, 0)) (p ^ s) ∨
    IsPrimitiveRoot (χ (0, 1)) (p ^ s) := by
  by_cases h0 : χ (p ^ (s - 1), 0) ≠ 1
  · exact Or.inl <| character_primitive_of_top_ne_one hs
      (χ.compAddMonoidHom (AddMonoidHom.inl _ _)) h0
  by_cases h1 : χ (0, p ^ (s - 1)) ≠ 1
  · exact Or.inr <| character_primitive_of_top_ne_one hs
      (χ.compAddMonoidHom (AddMonoidHom.inr _ _)) h1
  have ha0 : a.1 ∈ (nsmulAddMonoidHom p :
      ZMod (p ^ s) →+ ZMod (p ^ s)).ker := by
    change p • a.1 = 0
    simpa using congrArg Prod.fst ha
  have ha1 : a.2 ∈ (nsmulAddMonoidHom p :
      ZMod (p ^ s) →+ ZMod (p ^ s)).ker := by
    change p • a.2 = 0
    simpa using congrArg Prod.snd ha
  rw [zmod_pTorsion hs] at ha0 ha1
  obtain ⟨i, hi⟩ := AddSubgroup.mem_zmultiples_iff.mp ha0
  obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp ha1
  apply False.elim
  apply hχ
  have heq : a = i • ((p ^ (s - 1), 0) : ZMod (p ^ s) × ZMod (p ^ s)) +
      j • ((0, p ^ (s - 1)) : ZMod (p ^ s) × ZMod (p ^ s)) := by
    apply Prod.ext
    · simpa using hi.symm
    · simpa using hj.symm
  rw [heq, χ.map_add_eq_mul, χ.map_zsmul_eq_zpow, χ.map_zsmul_eq_zpow,
    not_not.mp h0, not_not.mp h1, one_zpow, one_zpow, one_mul]

theorem cyclic_card_complement_map {G J : Type*} [AddCommGroup G] [AddCommGroup J]
    (e : G ≃+ J) (L : AddSubgroup G) (n : ℕ)
    (hL : IsAddCyclic L ∧ Nat.card L = n ∧
      ∃ T : AddSubgroup G, IsCompl L T) :
    IsAddCyclic (L.map e.toAddMonoidHom) ∧
      Nat.card (L.map e.toAddMonoidHom) = n ∧
      ∃ T : AddSubgroup J, IsCompl (L.map e.toAddMonoidHom) T := by
  have he := e.addSubgroupMap L
  refine ⟨he.isAddCyclic.mp hL.1, ?_, ?_⟩
  · exact (Nat.card_congr he.toEquiv).symm.trans hL.2.1
  · obtain ⟨T, hT⟩ := hL.2.2
    exact ⟨T.map e.toAddMonoidHom, e.mapAddSubgroup.isCompl_iff.mp hT⟩

theorem character_kernel_map {G J : Type*} [AddCommGroup G] [AddCommGroup J]
    (e : G ≃+ J) (χ : AddChar J ℂ) :
    ((unitCharacter (χ.compAddMonoidHom e.toAddMonoidHom)).ker).map
        e.toAddMonoidHom = (unitCharacter χ).ker := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change unitCharacter χ (e y) = 0
    rw [unitCharacter_eq_zero]
    exact (unitCharacter_eq_zero _ y).mp hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change unitCharacter (χ.compAddMonoidHom e.toAddMonoidHom) (e.symm x) = 0
    rw [unitCharacter_eq_zero]
    simpa using (unitCharacter_eq_zero _ x).mp hx

theorem character_kernel_structure {G : Type*} [AddCommGroup G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : (ZMod (p ^ s) × ZMod (p ^ s)) ≃+ G)
    (χ : AddChar G ℂ) (a : G) (ha : p • a = 0) (hχ : χ a ≠ 1) :
    IsAddCyclic (unitCharacter χ).ker ∧
    Nat.card (unitCharacter χ).ker = p ^ s ∧
    ∃ T : AddSubgroup G, IsCompl (unitCharacter χ).ker T := by
  letI : NeZero (p ^ s) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let ψ := χ.compAddMonoidHom e.toAddMonoidHom
  have ha' : p • e.symm a = 0 := by
    apply e.injective
    simpa only [map_nsmul, e.apply_symm_apply, map_zero] using ha
  have hχ' : ψ (e.symm a) ≠ 1 := by simpa [ψ] using hχ
  have hψ : IsAddCyclic (unitCharacter ψ).ker ∧
      Nat.card (unitCharacter ψ).ker = p ^ s ∧
      ∃ T, IsCompl (unitCharacter ψ).ker T := by
    rcases character_primitive_coordinate hs ψ (e.symm a) ha' hχ' with h0 | h1
    · exact primitive_character_kernel ψ h0
    · let swap : (ZMod (p ^ s) × ZMod (p ^ s)) ≃+
          (ZMod (p ^ s) × ZMod (p ^ s)) := AddEquiv.prodComm
      have hprim : IsPrimitiveRoot
          ((ψ.compAddMonoidHom swap.toAddMonoidHom) (1, 0)) (p ^ s) := h1
      have hs' := primitive_character_kernel
        (ψ.compAddMonoidHom swap.toAddMonoidHom) hprim
      have hm := cyclic_card_complement_map swap _ _ hs'
      rw [character_kernel_map] at hm
      exact hm
  have hm := cyclic_card_complement_map e _ _ hψ
  rw [character_kernel_map] at hm
  exact hm

theorem exists_zmultiples_eq {G : Type*} [AddCommGroup G]
    (L : AddSubgroup G) (hL : IsAddCyclic L) :
    ∃ x : G, AddSubgroup.zmultiples x = L := by
  letI : IsAddCyclic L := hL
  obtain ⟨x, hx⟩ := IsAddCyclic.exists_generator (α := L)
  refine ⟨x.val, le_antisymm (AddSubgroup.zmultiples_le.mpr x.property) ?_⟩
  intro y hy
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hx ⟨y, hy⟩)
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, congrArg Subtype.val hk⟩

theorem unique_character_kernel_expanded {G : Type*} [AddCommGroup G] [Fintype G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) ≃+ G) (a b : G) (hat : p • a = 0)
    (χ : AddChar G ℂ) (ha : χ a ≠ 1) (hb : χ b ≠ 1) :
    ∃! L : AddSubgroup G,
      L ∈ (Finset.univ.image fun x : G => AddSubgroup.zmultiples x).filter
        (fun (L : AddSubgroup G) =>
          (IsAddCyclic L ∧ Nat.card L = p ^ s ∧ ∃ T : AddSubgroup G, IsCompl L T) ∧
          L ⊓ (nsmulAddMonoidHom p : G →+ G).ker ≠ AddSubgroup.zmultiples a ∧
          L ⊓ (nsmulAddMonoidHom p : G →+ G).ker ≠ AddSubgroup.zmultiples b) ∧
      ∀ l : L, χ l.val = 1 := by
  classical
  let e2 : (ZMod (p ^ s) × ZMod (p ^ s)) ≃+ G :=
    (LinearEquiv.finTwoArrow (ZMod (p ^ s)) (ZMod (p ^ s))).toAddEquiv.symm.trans e
  let K := (unitCharacter χ).ker
  have hK := character_kernel_structure hs e2 χ a hat ha
  obtain ⟨g, hg⟩ := exists_zmultiples_eq K hK.1
  have haK : K ⊓ (nsmulAddMonoidHom p : G →+ G).ker ≠ AddSubgroup.zmultiples a := by
    intro heq
    have hmem : a ∈ K ⊓ (nsmulAddMonoidHom p : G →+ G).ker := by
      rw [heq]
      exact AddSubgroup.mem_zmultiples a
    exact ha ((unitCharacter_eq_zero χ a).mp hmem.1)
  have hbK : K ⊓ (nsmulAddMonoidHom p : G →+ G).ker ≠ AddSubgroup.zmultiples b := by
    intro heq
    have hmem : b ∈ K ⊓ (nsmulAddMonoidHom p : G →+ G).ker := by
      rw [heq]
      exact AddSubgroup.mem_zmultiples b
    exact hb ((unitCharacter_eq_zero χ b).mp hmem.1)
  refine ⟨K, ⟨Finset.mem_filter.mpr ⟨?_, hK, haK, hbK⟩, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, hg⟩
  · intro l
    exact (unitCharacter_eq_zero χ l.val).mp l.property
  · intro L hL
    have hle : L ≤ K := by
      intro x hx
      exact (unitCharacter_eq_zero χ x).mpr (hL.2 ⟨x, hx⟩)
    apply AddSubgroup.eq_of_le_of_card_ge hle
    have hcard := (Finset.mem_filter.mp hL.1).2.1.2.1
    rw [hK.2.1, hcard]

section TopDigitCounting
variable [Fintype H]

theorem zmultiples_eq_iff_of_order_eq (x a : H) (h : addOrderOf x = addOrderOf a) :
    AddSubgroup.zmultiples x = AddSubgroup.zmultiples a ↔
      x ∈ AddSubgroup.zmultiples a := by
  constructor
  · intro heq
    rw [← heq]
    exact AddSubgroup.mem_zmultiples x
  · intro hx
    apply AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr hx)
    simp only [Nat.card_zmultiples, h, le_refl]

def nsmulKerEquiv {G : Type*} [AddCommGroup G] (e : G ≃+ H) (m : ℕ) :
    (nsmulAddMonoidHom m : G →+ G).ker ≃ (nsmulAddMonoidHom m : H →+ H).ker where
  toFun x := ⟨e x.1, by
    have hx : m • x.1 = 0 := x.2
    change m • e x.1 = 0
    simpa only [map_nsmul, map_zero] using congrArg e hx⟩
  invFun x := ⟨e.symm x.1, by
    have hx : m • x.1 = 0 := x.2
    change m • e.symm x.1 = 0
    simpa only [map_nsmul, map_zero] using congrArg e.symm hx⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.1

theorem exponent_nsmul_zero_of_pi_equiv {n d : ℕ} (e : (Fin d → ZMod n) ≃+ H) (x : H) :
    n • x = 0 := by
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy : n • y = 0 := by
    funext i
    change n • y i = 0
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  simpa only [map_nsmul, map_zero] using congrArg e hy

theorem card_equiv_pi_nsmul_ker {n d : ℕ} [NeZero n]
    (e : (Fin d → ZMod n) ≃+ H) (m : ℕ) :
    Nat.card (nsmulAddMonoidHom m : H →+ H).ker = n.gcd m ^ d := by
  rw [← Nat.card_congr (nsmulKerEquiv e m)]
  exact card_pi_nsmul_ker n d m

theorem exists_compl_of_top_nsmul_ne_zero {p s d : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : (Fin d → ZMod (p ^ s)) ≃+ H) (x : H) (hx : p ^ (s - 1) • x ≠ 0) :
    ∃ T : AddSubgroup H, IsCompl (AddSubgroup.zmultiples x) T := by
  have hy : p ^ (s - 1) • e.symm x ≠ 0 := by
    intro h
    apply hx
    simpa only [map_nsmul, map_zero, e.apply_symm_apply] using congrArg e h
  obtain ⟨i, hi⟩ : ∃ i, p ^ (s - 1) • (e.symm x) i ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    funext i
    exact h i
  have hu := zmod_isUnit_of_top_nsmul_ne_zero hs ((e.symm x) i) hi
  let K := (Pi.evalAddMonoidHom (fun _ : Fin d => ZMod (p ^ s)) i).ker
  have hc : IsCompl (AddSubgroup.zmultiples (e.symm x)) K :=
    zmultiples_isCompl_ker_eval_of_isUnit (p ^ s) d (e.symm x) i hu
  refine ⟨K.map (e : (Fin d → ZMod (p ^ s)) →+ H), ?_⟩
  have he : IsCompl ((AddSubgroup.zmultiples (e.symm x)).map (e : _ →+ H))
      (K.map (e : _ →+ H)) :=
    ⟨AddSubgroup.disjoint_map e.injective hc.disjoint,
      AddSubgroup.codisjoint_map e.surjective hc.codisjoint⟩
  have hmap : (AddSubgroup.zmultiples (e.symm x)).map (e : _ →+ H) =
      AddSubgroup.zmultiples x := by
    rw [AddMonoidHom.map_zmultiples]
    congr 1
    exact e.apply_symm_apply x
  rw [hmap] at he
  exact he

theorem top_nsmul_data {p s d : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : (Fin d → ZMod (p ^ s)) ≃+ H) :
    (nsmulAddMonoidHom (p ^ (s - 1)) : H →+ H).range =
        (nsmulAddMonoidHom p : H →+ H).ker ∧
      Nat.card (nsmulAddMonoidHom p : H →+ H).ker = p ^ d ∧
      Nat.card (nsmulAddMonoidHom (p ^ (s - 1)) : H →+ H).ker =
        (p ^ (s - 1)) ^ d := by
  let k := p ^ (s - 1)
  have hpk : p * k = p ^ s := by
    dsimp [k]
    rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel hs]
  have hdp : p ∣ p ^ s := ⟨k, hpk.symm⟩
  have hdk : k ∣ p ^ s := by
    rw [← hpk]
    exact dvd_mul_left _ _
  have hcP : Nat.card (nsmulAddMonoidHom p : H →+ H).ker = p ^ d := by
    rw [card_equiv_pi_nsmul_ker e p, Nat.gcd_eq_right hdp]
  have hcK : Nat.card (nsmulAddMonoidHom k : H →+ H).ker = k ^ d := by
    rw [card_equiv_pi_nsmul_ker e k, Nat.gcd_eq_right hdk]
  refine ⟨?_, hcP, hcK⟩
  let f := (nsmulAddMonoidHom k : H →+ H)
  apply AddSubgroup.eq_of_le_of_card_ge
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    change p • (k • x) = 0
    rw [smul_smul, hpk]
    exact exponent_nsmul_zero_of_pi_equiv e x
  · have hcH : Nat.card H = (p ^ s) ^ d := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fin]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hf : k ^ d * Nat.card f.range = (p ^ s) ^ d := by
      rw [← hcK, ← AddSubgroup.index_ker f, AddSubgroup.card_mul_index, hcH]
    have hr : Nat.card f.range = p ^ d := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos (Fact.out : p.Prime).pos _) _)
      calc
        k ^ d * Nat.card f.range = (p ^ s) ^ d := hf
        _ = k ^ d * p ^ d := by rw [← hpk, mul_pow, mul_comm]
    change Nat.card (nsmulAddMonoidHom p : H →+ H).ker ≤ Nat.card f.range
    rw [hcP, hr]

theorem card_top_nsmul_avoid_two_axes {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) ≃+ H) (A B : AddSubgroup H)
    (hA : A ≤ (nsmulAddMonoidHom p : H →+ H).ker)
    (hB : B ≤ (nsmulAddMonoidHom p : H →+ H).ker)
    (hd : Disjoint A B) (hAc : Nat.card A = p) (hBc : Nat.card B = p) :
    (Finset.univ.filter fun x : H =>
      p ^ (s - 1) • x ∉ A ∧ p ^ (s - 1) • x ∉ B).card =
        (p - 1) ^ 2 * (p ^ (s - 1)) ^ 2 := by
  let f := (nsmulAddMonoidHom (p ^ (s - 1)) : H →+ H)
  let K := (nsmulAddMonoidHom p : H →+ H).ker
  let T := Finset.univ.filter fun y : H => y ∈ K ∧ y ∉ A ∧ y ∉ B
  have hdata := top_nsmul_data hs e
  have hf : ∀ x, f x ∈ K := by
    intro x
    change f x ∈ (nsmulAddMonoidHom p : H →+ H).ker
    rw [← hdata.1]
    exact ⟨x, rfl⟩
  have hTc : T.card = (p - 1) ^ 2 :=
    card_avoid_two_subgroups K A B p (Fact.out : p.Prime).one_lt.le
      hA hB hd hdata.2.1 hAc hBc
  have hT : ∀ y ∈ T, y ∈ Set.range f := by
    intro y hy
    have hyK : y ∈ K := (Finset.mem_filter.mp hy).2.1
    change y ∈ (nsmulAddMonoidHom p : H →+ H).ker at hyK
    rw [← hdata.1] at hyK
    exact AddMonoidHom.mem_range.mp hyK
  have heq : (Finset.univ.filter fun x : H => f x ∈ T) =
      (Finset.univ.filter fun x : H =>
        p ^ (s - 1) • x ∉ A ∧ p ^ (s - 1) • x ∉ B) := by
    ext x
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_right (hf x)
  rw [← heq, card_preimage_finset f T hT, hTc, hdata.2.2]

theorem cyclic_summands_count_of_generator_iff {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) ≃+ H) (A B : AddSubgroup H)
    (hA : A ≤ (nsmulAddMonoidHom p : H →+ H).ker)
    (hB : B ≤ (nsmulAddMonoidHom p : H →+ H).ker)
    (hd : Disjoint A B) (hAc : Nat.card A = p) (hBc : Nat.card B = p)
    (S : Finset (AddSubgroup H))
    (hS : ∀ L ∈ S, IsAddCyclic L ∧ Nat.card L = p ^ s)
    (hgen : ∀ x : H, AddSubgroup.zmultiples x ∈ S ↔
      p ^ (s - 1) • x ∉ A ∧ p ^ (s - 1) • x ∉ B) :
    S.card = (p - 1) * p ^ (s - 1) := by
  have hc := card_generators_of_finset S (p ^ s) hS
  have heq : (Finset.univ.filter fun x : H => AddSubgroup.zmultiples x ∈ S) =
      (Finset.univ.filter fun x : H =>
        p ^ (s - 1) • x ∉ A ∧ p ^ (s - 1) • x ∉ B) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hgen]
  rw [heq, card_top_nsmul_avoid_two_axes hs e A B hA hB hd hAc hBc,
    Nat.totient_prime_pow (Fact.out : p.Prime) (by omega)] at hc
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _)
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
  calc
    (p ^ (s - 1) * (p - 1)) * S.card =
        (p - 1) ^ 2 * (p ^ (s - 1)) ^ 2 := by
      simpa only [mul_comm] using hc.symm
    _ = (p ^ (s - 1) * (p - 1)) * ((p - 1) * p ^ (s - 1)) := by ring

theorem noncharacteristic_generator_iff_expanded {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) ≃+ H) (a b : H)
    (ha : a ≠ 0) (hb : b ≠ 0) (hat : p • a = 0) (hbt : p • b = 0) (x : H) :
    AddSubgroup.zmultiples x ∈
        (Finset.univ.image fun y : H => AddSubgroup.zmultiples y).filter
          (fun (L : AddSubgroup H) => (IsAddCyclic L ∧ Nat.card L = p ^ s ∧
              ∃ T : AddSubgroup H, IsCompl L T) ∧
            L ⊓ (nsmulAddMonoidHom p : H →+ H).ker ≠ AddSubgroup.zmultiples a ∧
            L ⊓ (nsmulAddMonoidHom p : H →+ H).ker ≠ AddSubgroup.zmultiples b) ↔
      p ^ (s - 1) • x ∉ AddSubgroup.zmultiples a ∧
        p ^ (s - 1) • x ∉ AddSubgroup.zmultiples b := by
  let k := p ^ (s - 1)
  have hpk : p * k = p ^ s := by
    dsimp [k]
    rw [← pow_succ', Nat.sub_add_cancel hs]
  have hkpos : 0 < k := pow_pos (Fact.out : p.Prime).pos _
  have hklt : k < p ^ s := by
    rw [← hpk]
    have hp := (Fact.out : p.Prime).one_lt
    nlinarith
  have hinf (hx : addOrderOf x = p ^ s) :
      AddSubgroup.zmultiples x ⊓ (nsmulAddMonoidHom p : H →+ H).ker =
        AddSubgroup.zmultiples (k • x) :=
    zmultiples_inf_nsmul_ker p k (Fact.out : p.Prime).ne_zero x (hx.trans hpk.symm)
  have hpt : p • (k • x) = 0 := by
    rw [smul_smul, hpk]
    exact exponent_nsmul_zero_of_pi_equiv e x
  constructor
  · intro hx
    have hcond := (Finset.mem_filter.mp hx).2
    have hxord : addOrderOf x = p ^ s := by
      rw [← Nat.card_zmultiples]
      exact hcond.1.2.1
    have hne : k • x ≠ 0 := by
      intro hz
      have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
      rw [hxord] at hd
      exact Nat.not_dvd_of_pos_of_lt hkpos hklt hd
    have htop := addOrderOf_eq_prime hpt hne
    constructor
    · intro hm
      apply hcond.2.1
      exact (hinf hxord).trans
        ((zmultiples_eq_iff_of_order_eq (k • x) a
          (htop.trans (addOrderOf_eq_prime hat ha).symm)).mpr hm)
    · intro hm
      apply hcond.2.2
      exact (hinf hxord).trans
        ((zmultiples_eq_iff_of_order_eq (k • x) b
          (htop.trans (addOrderOf_eq_prime hbt hb).symm)).mpr hm)
  · intro hx
    have hne : k • x ≠ 0 := by
      intro hz
      apply hx.1
      rw [hz]
      exact (AddSubgroup.zmultiples a).zero_mem
    have hxord : addOrderOf x = p ^ s := by
      have hfin : p ^ ((s - 1) + 1) • x = 0 := by
        rw [Nat.sub_add_cancel hs]
        exact exponent_nsmul_zero_of_pi_equiv e x
      simpa only [Nat.sub_add_cancel hs] using addOrderOf_eq_prime_pow hne hfin
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩,
      ⟨inferInstance, ?_, exists_compl_of_top_nsmul_ne_zero hs e x hne⟩, ?_, ?_⟩
    · rw [Nat.card_zmultiples, hxord]
    · intro heq
      apply hx.1
      rw [← heq, hinf hxord]
      exact AddSubgroup.mem_zmultiples (k • x)
    · intro heq
      apply hx.2
      rw [← heq, hinf hxord]
      exact AddSubgroup.mem_zmultiples (k • x)

end TopDigitCounting

end SICLean.L5.SplitGroupRingAux
