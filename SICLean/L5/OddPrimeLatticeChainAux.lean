import SICLean.L5.OddPrimeTraceDual
import SICLean.L3.PseudolatticeIdeal
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.RingTheory.IntegralDomain

set_option autoImplicit false

/-!
Elementary lattice and finite-group tools for the concrete chain in [RW-rec, Lemma 3].
-/

noncomputable section

open scoped Classical
open SICLean.L3

namespace SICLean.L5.OddPrimeLatticeChainAux

open OddPrimeTraceDual

universe u
variable {K : Type u} [Field K] [NumberField K]

theorem scale_mono (c : K) {L M : Submodule ℤ K} (h : L ≤ M) :
    pseudolatticeScale c L ≤ pseudolatticeScale c M :=
  Submodule.map_mono h

theorem scale_sup (c : K) (L M : Submodule ℤ K) :
    pseudolatticeScale c (L ⊔ M) = pseudolatticeScale c L ⊔ pseudolatticeScale c M :=
  Submodule.map_sup _ _ _

theorem delta_scale_le (P : PeriodData K) (L : Submodule ℤ K)
    (hL : PeriodStable P L) : pseudolatticeScale (P.epsilon - 1) L ≤ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
  have he : P.epsilon * y ∈ L := by
    rw [← hL]
    exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨y, hy, rfl⟩
  simpa only [sub_mul, one_mul] using L.sub_mem he hy

theorem stable_sup (P : PeriodData K) (L M : Submodule ℤ K)
    (hL : PeriodStable P L) (hM : PeriodStable P M) : PeriodStable P (L ⊔ M) := by
  change pseudolatticeScale P.epsilon (L ⊔ M) = L ⊔ M
  rw [scale_sup, hL, hM]

theorem principal_le (P : PeriodData K) (L : StablePseudolattice P)
    (a : L.val) : pseudolatticeScale a.val (epsilonOrder P).toSubmodule ≤ L.val := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
  simpa only [mul_comm] using periodStable_order_smul P L b a.val hb a.property

theorem mem_principal (P : PeriodData K) (a : K) :
    a ∈ pseudolatticeScale a (epsilonOrder P).toSubmodule := by
  exact (pseudolatticeScale_mem_iff _ _ _).mpr
    ⟨1, (epsilonOrder P).one_mem, mul_one a⟩

theorem module_properties (P : PeriodData K) (I : StablePseudolattice P)
    (a : traceDual I.val) (ha : a.val ≠ 0) (i : ℕ) :
    Submodule.IsLattice ℚ
        (pseudolatticeScale a.val (epsilonOrder P).toSubmodule ⊔
          pseudolatticeScale ((P.epsilon - 1) ^ i) (traceDual I.val)) ∧
      PeriodStable P
        (pseudolatticeScale a.val (epsilonOrder P).toSubmodule ⊔
          pseudolatticeScale ((P.epsilon - 1) ^ i) (traceDual I.val)) ∧
      a.val ∈ (pseudolatticeScale a.val (epsilonOrder P).toSubmodule ⊔
          pseudolatticeScale ((P.epsilon - 1) ^ i) (traceDual I.val)) := by
  have hA := pseudolatticeScale_isLattice (epsilonOrder P).toSubmodule
    (epsilonOrder_isStablePseudolattice P).1 a.val ha
  have hM := traceDual_isLattice I.val I.property.1
  haveI := hA
  refine ⟨Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ le_sup_left
    (hA.fg.sup (hM.fg.map _)), ?_,
      (show pseudolatticeScale a.val (epsilonOrder P).toSubmodule ≤ _ from le_sup_left)
        (mem_principal P a.val)⟩
  exact stable_sup P _ _
    (pseudolatticeScale_periodStable P _ (epsilonOrder_isStablePseudolattice P).2 _)
    (pseudolatticeScale_periodStable P _ (traceDual_periodStable P I) _)

theorem dual_scaled_le (L M : Submodule ℤ K) (c : K)
    (h : pseudolatticeScale c L ≤ M) :
    pseudolatticeScale c (traceDual M) ≤ traceDual L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
  apply (mem_traceDual L _).mpr
  intro z hz
  have hcz : c * z ∈ M :=
    h ((pseudolatticeScale_mem_iff _ _ _).mpr ⟨z, hz, rfl⟩)
  simpa only [mul_assoc, mul_left_comm] using (mem_traceDual M y).mp hy _ hcz

theorem scale_epsilon_pow (P : PeriodData K) (L : Submodule ℤ K)
    (hL : PeriodStable P L) (j : ℕ) : pseudolatticeScale (P.epsilon ^ j) L = L := by
  induction j with
  | zero => simp only [pow_zero, pseudolatticeScale_one]
  | succ j ih => rw [pow_succ', pseudolatticeScale_mul, ih, hL]

theorem delta_sq (P : PeriodData K) : (P.epsilon - 1) ^ 2 = (P.N : K) * P.epsilon := by
  linear_combination P.epsilon_polynomial

theorem even_scale (P : PeriodData K) (L : Submodule ℤ K)
    (hL : PeriodStable P L) (j : ℕ) :
    pseudolatticeScale ((P.epsilon - 1) ^ (2 * j)) L =
      pseudolatticeScale ((P.N : K) ^ j) L := by
  rw [pow_mul, delta_sq, mul_pow, pseudolatticeScale_mul, scale_epsilon_pow P L hL]

theorem traceCharacter_transport (P : PeriodData K) {I J : StablePseudolattice P}
    (h : I = J) (a : traceDual I.val) (b : traceDual J.val) (hab : a.val = b.val) :
    (traceCharacter P I a).compAddMonoidHom
        (Eq.ndrec (motive := fun J => PseudolatticeGroup P I ≃+ PseudolatticeGroup P J)
          (AddEquiv.refl _) h).symm.toAddMonoidHom = traceCharacter P J b := by
  subst J
  have hab' : a = b := Subtype.ext hab
  subst b
  rfl

section PrimaryGroups

universe v
variable {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]

def primaryMap (f : A →+ B) (p : ℕ) :
    AddCommGroup.primaryComponent A p →+ AddCommGroup.primaryComponent B p where
  toFun x := ⟨f x, by
    rcases x.property with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← map_nsmul, hk, map_zero]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.val y.val)

theorem primary_eq_zero_of_nsmul {p q : ℕ} (hp : p.Prime) (hq : ¬p ∣ q)
    {x : A} (hx : x ∈ AddCommGroup.primaryComponent A p) (hqx : q • x = 0) : x = 0 := by
  rcases hx with ⟨k, hk⟩
  have horder : addOrderOf x = 1 := Nat.eq_one_of_dvd_coprimes
    ((hp.coprime_iff_not_dvd.mpr hq).pow_left k)
    (addOrderOf_dvd_of_nsmul_eq_zero hk) (addOrderOf_dvd_of_nsmul_eq_zero hqx)
  exact AddMonoid.addOrderOf_eq_one_iff.mp horder

theorem primaryMap_bijective_of_annihilators (f : A →+ B) {p q : ℕ}
    (hp : p.Prime) (hq : ¬p ∣ q)
    (hker : ∀ x : A, f x = 0 → q • x = 0)
    (hcoker : ∀ y : B, ∃ x : A, f x = q • y) :
    Function.Bijective (primaryMap f p) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply primary_eq_zero_of_nsmul hp hq
      ((AddCommGroup.primaryComponent A p).sub_mem x.property y.property)
    apply hker
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val h
  · rintro ⟨b, k, hb⟩
    obtain ⟨a, ha⟩ := hcoker b
    have hpa : f (p ^ k • a) = 0 := by
      rw [map_nsmul, ha, smul_smul, Nat.mul_comm, ← smul_smul, hb, smul_zero]
    have hqa : p ^ k • (q • a) = 0 := by
      rw [smul_smul, Nat.mul_comm, ← smul_smul]
      exact hker _ hpa
    have hcop : (q * q).Coprime (addOrderOf b) := by
      have h := (((hp.coprime_iff_not_dvd.mpr hq).symm.pow_left 2).pow_right k).coprime_dvd_right
        (addOrderOf_dvd_of_nsmul_eq_zero hb)
      simpa only [pow_two] using h
    obtain ⟨n, hn⟩ := exists_nsmul_eq_self_of_coprime hcop
    refine ⟨⟨n • (q • a), ?_⟩, ?_⟩
    · refine ⟨k, ?_⟩
      rw [smul_smul, Nat.mul_comm, ← smul_smul, hqa, smul_zero]
    · apply Subtype.ext
      change f (n • (q • a)) = b
      rw [map_nsmul, map_nsmul, ha, smul_smul]
      simpa only [smul_smul, mul_assoc] using hn

theorem finite_eventual_primeTo_nsmul_range (A : Type u) [AddCommGroup A] [Finite A]
    {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      (∀ x : AddCommGroup.primaryComponent A p, N ^ j • (x.val : A) = 0) ∧
        ¬p ∣ Nat.card (nsmulAddMonoidHom (α := A) (N ^ j)).range := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, m, hm, hcard⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := A)).ne' p hp.ne_one
  refine ⟨r, fun j hj => ?_⟩
  have hdiv : p ^ r ∣ N ^ j :=
    (pow_dvd_pow_of_dvd hpN r).trans (Nat.pow_dvd_pow N hj)
  obtain ⟨s, hs⟩ := hdiv
  have hkill (a : A) : Nat.card A • a = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard a)
  have hrange (a : A) : m • (N ^ j • a) = 0 := by
    calc
      _ = (m * N ^ j) • a := smul_smul _ _ _
      _ = (s * Nat.card A) • a := by
        congr 1
        rw [hs, hcard]
        ring
      _ = s • (Nat.card A • a) := (smul_smul _ _ _).symm
      _ = 0 := by rw [hkill, smul_zero]
  constructor
  · intro x
    have hpx : p ^ r • (x.val : A) = 0 := by
      apply primary_eq_zero_of_nsmul hp hm
        ((AddCommGroup.primaryComponent A p).nsmul_mem x.property (p ^ r))
      rw [smul_smul, Nat.mul_comm, ← hcard, hkill]
    rw [hs, Nat.mul_comm, mul_smul, hpx, smul_zero]
  · intro h
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
    have hmx : m • x = 0 := by
      apply Subtype.ext
      obtain ⟨a, ha⟩ := x.property
      change m • (x.val : A) = 0
      rw [← ha]
      exact hrange a
    have hpm : p ∣ m := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hmx
    exact hm hpm

theorem not_dvd_card_quotient_iff_primary_le (H : AddSubgroup A) [Finite A]
    {p : ℕ} (hp : p.Prime) :
    (¬p ∣ Nat.card (A ⧸ H)) ↔ AddCommGroup.primaryComponent A p ≤ H := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hq x hx
    have hxQ : QuotientAddGroup.mk' H x ∈ AddCommGroup.primaryComponent (A ⧸ H) p :=
      (primaryMap (QuotientAddGroup.mk' H) p ⟨x, hx⟩).property
    have hx0 : QuotientAddGroup.mk' H x = 0 :=
      primary_eq_zero_of_nsmul hp hq hxQ
        (addOrderOf_dvd_iff_nsmul_eq_zero.mp
          (addOrderOf_dvd_natCard (QuotientAddGroup.mk' H x)))
    exact (QuotientAddGroup.eq_zero_iff x).mp hx0
  · intro hprim hdiv
    obtain ⟨r, m, hm, hcard⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := A)).ne' p hp.ne_one
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hdiv
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective x
    have hma : m • a ∈ AddCommGroup.primaryComponent A p := by
      refine ⟨r, ?_⟩
      rw [smul_smul, ← hcard]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard a)
    have hmx : m • x = 0 := by
      rw [← ha, ← QuotientAddGroup.mk_nsmul]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (hprim hma)
    exact hm (hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hmx)

theorem not_dvd_card_quotient_zmultiples_of_primaryMap_surjective
    [Finite B] (f : A →+ B) {p : ℕ} (hp : p.Prime) (a : A)
    (ha : AddSubgroup.zmultiples a = ⊤)
    (hf : Function.Surjective (primaryMap f p)) :
    ¬p ∣ Nat.card (B ⧸ AddSubgroup.zmultiples (f a)) := by
  apply (not_dvd_card_quotient_iff_primary_le _ hp).mpr
  intro b hb
  obtain ⟨x, hx⟩ := hf ⟨b, hb⟩
  have hxa : x.val ∈ AddSubgroup.zmultiples a := by rw [ha]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hxa
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨n, ?_⟩
  rw [← map_zsmul, hn]
  exact congrArg Subtype.val hx

end PrimaryGroups

theorem isAddCyclic_of_faithful_complex_character {G : Type u}
    [AddCommGroup G] [Finite G] (theta : AddChar G ℂ)
    (hfaith : Function.Injective theta) : IsAddCyclic G := by
  apply isCyclic_multiplicative_iff.mp
  exact isCyclic_of_injective_ringHom theta.toMonoidHom hfaith

theorem primaryComponent_nontrivial_of_prime_dvd_card {G : Type u}
    [AddCommGroup G] [Finite G] (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) :
    Nontrivial (AddCommGroup.primaryComponent G p) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := G) p hdvd
  obtain ⟨hpx, hx0⟩ := addOrderOf_eq_prime_iff.mp hx
  apply (AddSubgroup.nontrivial_iff_exists_ne_zero _).mpr
  exact ⟨x, AddCommGroup.mem_primaryComponent.mpr ⟨1, by simpa using hpx⟩, hx0⟩

abbrev rawPrincipalOrder (P : PeriodData K) (a : K) : Submodule ℤ K :=
  pseudolatticeScale a (epsilonOrder P).toSubmodule

abbrev RawOrderPeriodGroup (P : PeriodData K) (a : K) :=
  rawPrincipalOrder P a ⧸
    (pseudolatticeScale (P.epsilon - 1) (rawPrincipalOrder P a)).toAddSubgroup.addSubgroupOf
      (rawPrincipalOrder P a).toAddSubgroup

def rawOrderGenerator (P : PeriodData K) (a : K) : RawOrderPeriodGroup P a :=
  QuotientAddGroup.mk (⟨a, mem_principal P a⟩ : rawPrincipalOrder P a)

theorem order_coordinates (P : PeriodData K) (x : K) :
    x ∈ epsilonOrder P ↔ ∃ m n : ℤ, x = (m : K) + (n : K) * P.epsilon := by
  constructor
  · intro hx
    change x ∈ Algebra.adjoin ℤ ({P.epsilon} : Set K) at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨0, 1, by simp⟩
    | algebraMap z => exact ⟨z, 0, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨m, n, rfl⟩ := ihx
      obtain ⟨p, q, rfl⟩ := ihy
      exact ⟨m + p, n + q, by push_cast; ring⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨m, n, rfl⟩ := ihx
      obtain ⟨p, q, rfl⟩ := ihy
      refine ⟨m * p - n * q,
        m * q + n * p + n * q * ((P.N : ℤ) + 2), ?_⟩
      push_cast
      linear_combination (n : K) * (q : K) * P.epsilon_polynomial
  · rintro ⟨m, n, rfl⟩
    exact (epsilonOrder P).add_mem ((epsilonOrder P).intCast_mem m)
      ((epsilonOrder P).mul_mem ((epsilonOrder P).intCast_mem n)
        (Algebra.subset_adjoin (Set.mem_singleton _)))

theorem order_coordinates_zero (P : PeriodData K) (m n : ℤ)
    (h : (m : K) + (n : K) * P.epsilon = 0) : m = 0 ∧ n = 0 := by
  have hn : n = 0 := by
    by_contra hn
    have h1 := congrArg P.sigma₁ h
    have h2 := congrArg P.sigma₂ h
    simp only [map_add, map_mul, map_intCast, map_zero] at h1 h2
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have heq : P.sigma₁ P.epsilon = P.sigma₂ P.epsilon := by
      apply mul_left_cancel₀ hnr
      linarith
    have hi : P.sigma₁ P.epsilon = (P.sigma₁ P.epsilon)⁻¹ :=
      heq.trans P.epsilon_conj
    have he : P.sigma₁ P.epsilon ≠ 0 :=
      ne_of_gt (lt_trans zero_lt_one P.epsilon_gt_one)
    have hsq : P.sigma₁ P.epsilon * P.sigma₁ P.epsilon = 1 := by
      have hmul := congrArg (fun t : ℝ => t * P.sigma₁ P.epsilon) hi
      simpa [inv_mul_cancel₀ he] using hmul
    nlinarith [P.epsilon_gt_one]
  refine ⟨?_, hn⟩
  simp only [hn, Int.cast_zero, zero_mul, add_zero] at h
  exact_mod_cast h

def principalInteger (P : PeriodData K) (a : K) (z : ℤ) : rawPrincipalOrder P a :=
  ⟨(z : K) * a, (pseudolatticeScale_mem_iff _ _ _).mpr
    ⟨(z : K), (epsilonOrder P).intCast_mem z, mul_comm _ _⟩⟩

theorem int_mem_relation_iff (P : PeriodData K) (a : K) (ha : a ≠ 0) (z : ℤ) :
    (z : K) * a ∈ pseudolatticeScale (P.epsilon - 1) (rawPrincipalOrder P a) ↔
      (P.N : ℤ) ∣ z := by
  constructor
  · intro hz
    obtain ⟨b, hb, hb_eq⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hz
    obtain ⟨x, hx, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hb
    obtain ⟨m, n, rfl⟩ := (order_coordinates P x).mp hx
    have heq : (P.epsilon - 1) * ((m : K) + (n : K) * P.epsilon) = (z : K) := by
      apply mul_left_cancel₀ ha
      calc
        a * ((P.epsilon - 1) * ((m : K) + (n : K) * P.epsilon)) =
            (P.epsilon - 1) * (a * ((m : K) + (n : K) * P.epsilon)) := by ring
        _ = (z : K) * a := hb_eq
        _ = a * (z : K) := mul_comm _ _
    have hcoef : ((-m - n - z : ℤ) : K) +
        ((m + ((P.N : ℤ) + 1) * n : ℤ) : K) * P.epsilon = 0 := by
      push_cast
      linear_combination heq - (n : K) * P.epsilon_polynomial
    obtain ⟨hm, hn⟩ := order_coordinates_zero P _ _ hcoef
    exact ⟨n, by nlinarith⟩
  · rintro ⟨n, rfl⟩
    let t : K := (n : K) * (P.epsilon - ((P.N : K) + 1))
    have ht : t ∈ epsilonOrder P := by
      apply (epsilonOrder P).mul_mem ((epsilonOrder P).intCast_mem n)
      apply (epsilonOrder P).sub_mem (Algebra.subset_adjoin (Set.mem_singleton _))
      exact (epsilonOrder P).add_mem ((epsilonOrder P).natCast_mem _)
        ((epsilonOrder P).one_mem)
    apply (pseudolatticeScale_mem_iff _ _ _).mpr
    refine ⟨a * t, (pseudolatticeScale_mem_iff _ _ _).mpr ⟨t, ht, rfl⟩, ?_⟩
    dsimp [t]
    push_cast
    linear_combination a * (n : K) * P.epsilon_polynomial

def generatorHom (P : PeriodData K) (a : K) : ℤ →+ RawOrderPeriodGroup P a :=
  zmultiplesHom _ (rawOrderGenerator P a)

theorem generatorHom_mk (P : PeriodData K) (a : K) (z : ℤ) :
    generatorHom P a z = QuotientAddGroup.mk (principalInteger P a z) := by
  change z • rawOrderGenerator P a = _
  rw [rawOrderGenerator, ← QuotientAddGroup.mk_zsmul]
  congr 1
  ext
  simp [principalInteger, zsmul_eq_mul]

theorem generatorHom_ker (P : PeriodData K) (a : K) (ha : a ≠ 0) :
    (generatorHom P a).ker = AddSubgroup.zmultiples (P.N : ℤ) := by
  ext z
  change generatorHom P a z = 0 ↔ z ∈ AddSubgroup.zmultiples (P.N : ℤ)
  rw [generatorHom_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    Int.mem_zmultiples_iff]
  exact int_mem_relation_iff P a ha z

theorem generatorHom_surjective (P : PeriodData K) (a : K) :
    Function.Surjective (generatorHom P a) := by
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro b
  obtain ⟨x, hx, hax⟩ := (pseudolatticeScale_mem_iff _ _ _).mp b.property
  obtain ⟨m, n, hxrep⟩ := (order_coordinates P x).mp hx
  refine ⟨m + n, ?_⟩
  rw [generatorHom_mk]
  change QuotientAddGroup.mk' _ (principalInteger P a (m + n)) =
    QuotientAddGroup.mk' _ b
  apply (QuotientAddGroup.mk'_eq_mk' _).mpr
  refine ⟨b - principalInteger P a (m + n), ?_, by abel⟩
  rw [AddSubgroup.mem_addSubgroupOf]
  apply (pseudolatticeScale_mem_iff _ _ _).mpr
  refine ⟨a * (n : K),
    (pseudolatticeScale_mem_iff _ _ _).mpr
      ⟨(n : K), (epsilonOrder P).intCast_mem n, rfl⟩, ?_⟩
  change (P.epsilon - 1) * (a * (n : K)) =
    b.val - ((m + n : ℤ) : K) * a
  rw [← hax, hxrep]
  push_cast
  ring

theorem orderPeriodGroup_equiv_zmod_proof (P : PeriodData K) (a : K) (ha : a ≠ 0) :
    ∃ e : RawOrderPeriodGroup P a ≃+ ZMod P.N, e (rawOrderGenerator P a) = 1 := by
  let ef := QuotientAddGroup.quotientKerEquivOfSurjective
    (generatorHom P a) (generatorHom_surjective P a)
  let ec := (QuotientAddGroup.quotientAddEquivOfEq (generatorHom_ker P a ha)).trans
    (Int.quotientZMultiplesNatEquivZMod P.N)
  have hg : ef (QuotientAddGroup.mk (1 : ℤ)) = rawOrderGenerator P a := by
    change (1 : ℤ) • rawOrderGenerator P a = rawOrderGenerator P a
    simp
  refine ⟨ef.symm.trans ec, ?_⟩
  change ec (ef.symm (rawOrderGenerator P a)) = 1
  rw [← hg, ef.symm_apply_apply]
  change (Int.quotientZMultiplesNatEquivZMod P.N) (QuotientAddGroup.mk (1 : ℤ)) = 1
  change
    (QuotientAddGroup.quotientKerEquivOfRightInverse
      (Int.castAddHom (ZMod P.N)) ZMod.cast ZMod.intCast_zmod_cast)
      ((QuotientAddGroup.quotientAddEquivOfEq
        (ZMod.ker_intCastAddHom P.N)).symm (QuotientAddGroup.mk (1 : ℤ))) = 1
  have hcast :
      (QuotientAddGroup.quotientAddEquivOfEq
        (ZMod.ker_intCastAddHom P.N)).symm (QuotientAddGroup.mk (1 : ℤ)) =
          QuotientAddGroup.mk (1 : ℤ) := by
    apply (AddEquiv.symm_apply_eq _).mpr
    rfl
  rw [hcast]
  change ((1 : ℤ) : ZMod P.N) = 1
  exact Int.cast_one

theorem index_nsmul_mem (L M : Submodule ℤ K) (x : M) :
    DistributionOrbitGeometry.inclusionIndex L M • x.val ∈ L := by
  let Q := M ⧸ L.toAddSubgroup.addSubgroupOf M.toAddSubgroup
  have h : Nat.card Q • (QuotientAddGroup.mk x : Q) = 0 := card_nsmul_eq_zero'
  have h' : (QuotientAddGroup.mk
      (DistributionOrbitGeometry.inclusionIndex L M • x) : Q) = 0 := by
    rw [QuotientAddGroup.mk_nsmul]
    exact h
  exact (QuotientAddGroup.eq_zero_iff _).mp h'

abbrev LatticePeriodQuotient (L : Submodule ℤ K) (c : K) :=
  L ⧸ (pseudolatticeScale c L).toAddSubgroup.addSubgroupOf L.toAddSubgroup

theorem latticePeriod_primary_bijective (L M : Submodule ℤ K) (hLM : L ≤ M) (c : K)
    (f : LatticePeriodQuotient L c →+ LatticePeriodQuotient M c)
    (hf : ∀ x : L, f (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (⟨x.val, hLM x.property⟩ : M))
    {p : ℕ} (hp : p.Prime) (hq : ¬p ∣ DistributionOrbitGeometry.inclusionIndex L M) :
    Function.Bijective (primaryMap f p) := by
  let q := DistributionOrbitGeometry.inclusionIndex L M
  apply primaryMap_bijective_of_annihilators f hp hq
  · intro x
    refine QuotientAddGroup.induction_on x ?_
    intro l hl
    rw [hf] at hl
    have hlM : l.val ∈ pseudolatticeScale c M := (QuotientAddGroup.eq_zero_iff _).mp hl
    obtain ⟨m, hm, heq⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hlM
    rw [← QuotientAddGroup.mk_nsmul]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    change q • l.val ∈ pseudolatticeScale c L
    rw [nsmul_eq_mul]
    apply (pseudolatticeScale_mem_iff _ _ _).mpr
    refine ⟨(q : K) * m, ?_, ?_⟩
    · simpa only [nsmul_eq_mul] using index_nsmul_mem L M ⟨m, hm⟩
    · rw [← heq]
      ring
  · intro y
    refine QuotientAddGroup.induction_on y ?_
    intro m
    let l : L := ⟨q • m.val, index_nsmul_mem L M m⟩
    refine ⟨QuotientAddGroup.mk l, ?_⟩
    rw [hf, ← QuotientAddGroup.mk_nsmul]
    rfl

section RelativeQuotients

variable {A : Type u} [AddCommGroup A]

def relativeToAmbient (L M : AddSubgroup A) : M ⧸ L.addSubgroupOf M →+ A ⧸ L :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' L).comp M.subtype) (by
    intro x hx
    exact (QuotientAddGroup.eq_zero_iff x.val).mpr hx)

theorem relativeToAmbient_injective (L M : AddSubgroup A) :
    Function.Injective (relativeToAmbient L M) := by
  intro x y h
  apply sub_eq_zero.mp
  have hz : relativeToAmbient L M (x - y) = 0 := by rw [map_sub, h, sub_self]
  revert hz
  refine QuotientAddGroup.induction_on (x - y) ?_
  intro m hm
  apply (QuotientAddGroup.eq_zero_iff m).mpr
  exact (QuotientAddGroup.eq_zero_iff m.val).mp hm

theorem relIndex_eq_card_map (L M : AddSubgroup A) :
    L.relIndex M = Nat.card (M.map (QuotientAddGroup.mk' L)) := by
  let f := (QuotientAddGroup.mk' L).comp M.subtype
  have hrange : f.range = M.map (QuotientAddGroup.mk' L) := by
    rw [AddMonoidHom.range_comp, AddSubgroup.range_subtype]
  have hker : f.ker = L.addSubgroupOf M := by
    ext x
    exact QuotientAddGroup.eq_zero_iff x.val
  rw [← hrange]
  change Nat.card (M ⧸ L.addSubgroupOf M) = _
  rw [← hker]
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv

end RelativeQuotients

theorem relative_nsmul_range_card (L M : Submodule ℤ K) (n : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := M ⧸
      L.toAddSubgroup.addSubgroupOf M.toAddSubgroup) n).range =
      Nat.card ((pseudolatticeScale (n : K) M).toAddSubgroup.map
        (QuotientAddGroup.mk' L.toAddSubgroup)) := by
  let Q := M ⧸ L.toAddSubgroup.addSubgroupOf M.toAddSubgroup
  let f := relativeToAmbient L.toAddSubgroup M.toAddSubgroup
  let R := (nsmulAddMonoidHom (α := Q) n).range
  have hrange : R.map f = (pseudolatticeScale (n : K) M).toAddSubgroup.map
      (QuotientAddGroup.mk' L.toAddSubgroup) := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      obtain ⟨m, rfl⟩ := QuotientAddGroup.mk_surjective z
      refine ⟨(n : K) * m.val, ?_, ?_⟩
      · exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨m.val, m.property, rfl⟩
      · change QuotientAddGroup.mk' L.toAddSubgroup ((n : K) * m.val) =
          f (n • (QuotientAddGroup.mk m : Q))
        rw [map_nsmul]
        change QuotientAddGroup.mk' L.toAddSubgroup ((n : K) * m.val) =
          n • QuotientAddGroup.mk' L.toAddSubgroup m.val
        simpa only [nsmul_eq_mul] using map_nsmul (QuotientAddGroup.mk' L.toAddSubgroup) n m.val
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨m, hm, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
      refine ⟨n • (QuotientAddGroup.mk (⟨m, hm⟩ : M) : Q), ⟨_, rfl⟩, ?_⟩
      rw [map_nsmul]
      change n • QuotientAddGroup.mk' L.toAddSubgroup m =
        QuotientAddGroup.mk' L.toAddSubgroup ((n : K) * m)
      simpa only [nsmul_eq_mul] using
        (map_nsmul (QuotientAddGroup.mk' L.toAddSubgroup) n m).symm
  rw [← hrange]
  exact Nat.card_congr
    (R.equivMapOfInjective f (relativeToAmbient_injective _ _)).toEquiv

end SICLean.L5.OddPrimeLatticeChainAux
