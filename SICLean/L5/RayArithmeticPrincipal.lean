import SICLean.L5.RayArithmeticSigns
import SICLean.L5.RayArithmeticPrincipalAux

set_option autoImplicit false

/-!
# Integral ray generators and their action on the actual quotient

Ideals here are arbitrary nonzero integral ideals prime to cm; primality is never
assumed. Both generator criteria are equivalences and remain valid when t=1. Their
witnesses include the global congruence and multiplier-order membership needed
downstream. Sources: [RW26, p. 20] (objects and labels). No special-value reciprocity is
assumed.
-/

noncomputable section
open scoped MatrixGroups NumberField Classical nonZeroDivisors
open NumberField ClassFieldTheory

namespace SICLean.L5.RayArithmeticPrincipal

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM
local notation "P" => ActualField.periodData M hM
local notation "I" => ActualLattice.stableLattice M hM

/-- Source: an integral principal ideal has an integral generator, [RW-rec]; The ideal is integral.
[RW26, p. 20]. -/
theorem principal_generator_integral (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (b : Kˣ) (hb : toPrincipalIdeal (𝓞 K) K b =
      RayArithmeticModulus.fractionalIdeal M hM a ha) :
    IsIntegral ℤ (b : K) := by
  have h := congrArg Units.val hb
  rw [coe_toPrincipalIdeal] at h
  change FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) =
    (a : FractionalIdeal (𝓞 K)⁰ K) at h
  have hbmem := FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (b : K)
  rw [h] at hbmem
  obtain ⟨z, _, hz⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hbmem
  rw [← hz]
  exact z.property

/-- Source: cm O_K subset m O implies alpha in O, [RW-rec]; [RW26, p. 20]. -/
theorem globallyCongruent_mem_order (m : ℕ) (a : K)
    (ha : RayArithmeticModulus.GloballyCongruent M hM m a) :
    a ∈ RayArithmeticOrder.multiplierOrder M hM := by
  obtain ⟨b, hb⟩ := ha
  have he : a = 1 + (RayArithmeticModulus.level M hM m : K) * (b : K) := by
    linear_combination hb
  rw [he]
  exact RayArithmeticOrder.one_add_cm_mem_order M hM m b

/-- Source: mx in I and cm O_K subset m O, [RW-rec]; This uses the actual inverse-period point
convention. [RW26, p. 20]. -/
theorem sub_one_mul_point_mem (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : K) (ha : RayArithmeticModulus.GloballyCongruent M hM m a)
    (x : K) (hx : x ∈ L3.pseudolatticePeriodPoints P I) :
    (a - 1) * x ∈ (I).val := by
  obtain ⟨b, hb⟩ := ha
  obtain ⟨c, hc⟩ := RayArithmeticOrder.cm_mul_eq_level_mul_order M hM m b
  change a - 1 = ((RayArithmeticOrder.conductor M hM * m : ℕ) : K) * (b : K) at hb
  rw [hb, hc]
  have hmem := (RayArithmeticOrder.mem_multiplierOrder M hM (c : K)).mp c.property
    ((m : K) * x) (RayArithmeticOrder.level_mul_point_mem M hM m hm x hx)
  convert hmem using 1
  ring

/-- Source: the preceding assertion on the existing G_I representatives; [RW26, p. 20]; [RW-rec]. -/
theorem sub_one_mul_representative_mem (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : K) (ha : RayArithmeticModulus.GloballyCongruent M hM m a)
    (x : ActualLattice.Group M hM) :
    (a - 1) * L3.pseudolatticeRepresentative P I x ∈ (I).val := by
  exact sub_one_mul_point_mem M hM m hm a ha _ (Quotient.out x).property

/-- Source: multiplier-order action preserves actual period points, [RW-rec]; [RW26, p. 20]. -/
theorem mul_point_mem (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : K) (ha : RayArithmeticModulus.GloballyCongruent M hM m a)
    (x : K) (hx : x ∈ L3.pseudolatticePeriodPoints P I) :
    a * x ∈ L3.pseudolatticePeriodPoints P I := by
  change ((P).epsilon⁻¹ - 1) * (a * x) ∈ (I).val
  rw [mul_left_comm]
  exact (RayArithmeticOrder.mem_multiplierOrder M hM a).mp
    (globallyCongruent_mem_order M hM m a ha) _ hx

/-- Source: literal quotient equality alpha*x=x, not a changed row label; [RW26, p. 20]; [RW-rec].
-/
theorem mk_mul_eq (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : K) (ha : RayArithmeticModulus.GloballyCongruent M hM m a)
    (x : K) (hx : x ∈ L3.pseudolatticePeriodPoints P I) :
    L3.pseudolatticeMk P I (a * x) (mul_point_mem M hM m hm a ha x hx) =
      L3.pseudolatticeMk P I x hx := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change a * x - x ∈ (I).val
  convert sub_one_mul_point_mem M hM m hm a ha x hx using 1
  ring

/-- Source: for a double-negative generator beta=-alpha is positive and beta*x=-x in the quotient;
[RW-rec] plus positive homothety (1). This is not a mixed-sign analytic formula. [RW26, p. 20]. -/
theorem mk_neg_mul_eq (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : K) (ha : RayArithmeticModulus.GloballyCongruent M hM m a)
    (x : K) (hx : x ∈ L3.pseudolatticePeriodPoints P I) :
    ∃ hax : -a * x ∈ L3.pseudolatticePeriodPoints P I,
      L3.pseudolatticeMk P I (-a * x) hax = -L3.pseudolatticeMk P I x hx := by
  have hax : -a * x ∈ L3.pseudolatticePeriodPoints P I := by
    simpa only [neg_mul] using
      (L3.pseudolatticePeriodPoints P I).neg_mem (mul_point_mem M hM m hm a ha x hx)
  refine ⟨hax, ?_⟩
  calc
    L3.pseudolatticeMk P I (-a * x) hax =
        -L3.pseudolatticeMk P I (a * x) (mul_point_mem M hM m hm a ha x hx) := by
      change QuotientAddGroup.mk (⟨-a * x, hax⟩ : L3.pseudolatticePeriodPoints P I) =
        -QuotientAddGroup.mk (⟨a * x, _⟩ : L3.pseudolatticePeriodPoints P I)
      rw [← QuotientAddGroup.mk_neg]
      apply congrArg QuotientAddGroup.mk
      apply Subtype.ext
      exact neg_mul a x
    _ = -L3.pseudolatticeMk P I x hx := congrArg Neg.neg (mk_mul_eq M hM m hm a ha x hx)

/-- Source: ray-principal kernel, [RW-rec]; integral/global upgrade and O membership. It includes
composite integral ideals. [RW26, p. 20]. -/
theorem idealClass_eq_one_iff (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m a) :
    RayArithmeticModulus.idealClass M hM m a ha hc = 1 ↔
      ∃ b : 𝓞 K, a = Ideal.span {b} ∧
        0 < ActualField.sigma₁ M hM (b : K) ∧
        0 < ActualField.sigma₂ M hM (b : K) ∧
        RayArithmeticModulus.GloballyCongruent M hM m (b : K) ∧
        (b : K) ∈ RayArithmeticOrder.multiplierOrder M hM := by
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := (RayArithmeticModulus.class_eq_one_iff M hM m
      ⟨RayArithmeticModulus.fractionalIdeal M hM a ha,
        RayArithmeticModulus.fractionalIdeal_mem_primeTo M hM m a ha hc⟩).mp h
    let z : 𝓞 K := ⟨(b : K), principal_generator_integral M hM a ha b he⟩
    have hz : (z : K) ≠ 0 := b.ne_zero
    have hunit : Units.mk0 (z : K) hz = b := Units.ext rfl
    have hgen : a = Ideal.span {z} :=
      (RayArithmeticPrincipalAux.principal_eq_fractional_iff M hM a ha z hz).mp
        (by simpa only [hunit] using he)
    obtain ⟨hf, h₁, h₂⟩ := (RayArithmeticModulus.isRayCongruent_iff M hM m b).mp hb
    have hg : RayArithmeticModulus.GloballyCongruent M hM m (z : K) :=
      (RayArithmeticModulus.finiteCongruent_iff_global M hM m hm z hz).mp
        (by simpa only [hunit] using hf)
    exact ⟨z, hgen, h₁, h₂, hg, globallyCongruent_mem_order M hM m (z : K) hg⟩
  · rintro ⟨b, he, h₁, h₂, hg, _⟩
    have hb : (b : K) ≠ 0 := fun h => by simp [h] at h₁
    have hf := (RayArithmeticModulus.finiteCongruent_iff_global M hM m hm b hb).mpr hg
    calc
      RayArithmeticModulus.idealClass M hM m a ha hc =
          RayArithmeticModulus.principalClass M hM m (Units.mk0 (b : K) hb) hf :=
        RayArithmeticPrincipalAux.idealClass_eq_principalClass M hM m a ha hc b hb hf he
      _ = 1 := RayArithmeticSigns.principalClass_of_pos_pos M hM m _ hf h₁ h₂

/-- Source: product of the two sign classes and arbitrary integral ideals, [RW-rec]. No assumption
t!=1 is made. [RW26, p. 20]. -/
theorem idealClass_eq_t_iff (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m a) :
    RayArithmeticModulus.idealClass M hM m a ha hc = RayArithmeticSigns.t M hM m hm ↔
      ∃ b : 𝓞 K, a = Ideal.span {b} ∧
        ActualField.sigma₁ M hM (b : K) < 0 ∧
        ActualField.sigma₂ M hM (b : K) < 0 ∧
        RayArithmeticModulus.GloballyCongruent M hM m (b : K) ∧
        (b : K) ∈ RayArithmeticOrder.multiplierOrder M hM := by
  constructor
  · intro h
    let d : 𝓞 K := 1 - (RayArithmeticModulus.level M hM m : 𝓞 K)
    have hdval : (d : K) = 1 - (RayArithmeticModulus.level M hM m : K) := by
      simp only [d, map_sub, map_one, map_natCast]
    obtain ⟨hd₁, hd₂⟩ := RayArithmeticPrincipalAux.one_sub_level_signs M hM m hm
    rw [← hdval] at hd₁ hd₂
    have hd : (d : K) ≠ 0 := fun he => by simp [he] at hd₁
    have hgd : RayArithmeticModulus.GloballyCongruent M hM m (d : K) := by
      rw [hdval]
      exact RayArithmeticPrincipalAux.one_sub_level_congruent M hM m
    let u : Kˣ := Units.mk0 (d : K) hd
    have hfu : RayArithmeticModulus.FiniteCongruent M hM m u :=
      (RayArithmeticModulus.finiteCongruent_iff_global M hM m hm d hd).mpr hgd
    have hu : RayArithmeticModulus.principalClass M hM m u hfu =
        RayArithmeticSigns.t M hM m hm :=
      RayArithmeticSigns.principalClass_of_neg_neg M hM m hm u hfu hd₁ hd₂
    rw [← hu] at h
    obtain ⟨b, hb, he⟩ := (RayArithmeticPrincipalAux.class_eq_principal_iff M hM m
      ⟨RayArithmeticModulus.fractionalIdeal M hM a ha,
        RayArithmeticModulus.fractionalIdeal_mem_primeTo M hM m a ha hc⟩ u hfu).mp h
    let z : 𝓞 K := ⟨(b * u : Kˣ), principal_generator_integral M hM a ha (b * u) he⟩
    have hz : (z : K) ≠ 0 := (b * u).ne_zero
    have hunit : Units.mk0 (z : K) hz = b * u := Units.ext rfl
    have hgen : a = Ideal.span {z} :=
      (RayArithmeticPrincipalAux.principal_eq_fractional_iff M hM a ha z hz).mp
        (by simpa only [hunit] using he)
    obtain ⟨hfb, hb₁, hb₂⟩ := (RayArithmeticModulus.isRayCongruent_iff M hM m b).mp hb
    have hgz : RayArithmeticModulus.GloballyCongruent M hM m (z : K) :=
      (RayArithmeticModulus.finiteCongruent_iff_global M hM m hm z hz).mp
        (by
          change IsRayCongruent (RayArithmeticModulus.finiteModulus M hM m)
            (Units.mk0 (z : K) hz)
          rw [hunit]
          exact IsRayCongruent.mul hfb hfu)
    have hz₁ : ActualField.sigma₁ M hM (z : K) < 0 := by
      change ActualField.sigma₁ M hM ((b : K) * (u : K)) < 0
      rw [map_mul]
      exact mul_neg_of_pos_of_neg hb₁ hd₁
    have hz₂ : ActualField.sigma₂ M hM (z : K) < 0 := by
      change ActualField.sigma₂ M hM ((b : K) * (u : K)) < 0
      rw [map_mul]
      exact mul_neg_of_pos_of_neg hb₂ hd₂
    exact ⟨z, hgen, hz₁, hz₂, hgz, globallyCongruent_mem_order M hM m (z : K) hgz⟩
  · rintro ⟨b, he, h₁, h₂, hg, _⟩
    have hb : (b : K) ≠ 0 := fun h => by simp [h] at h₁
    have hf := (RayArithmeticModulus.finiteCongruent_iff_global M hM m hm b hb).mpr hg
    calc
      RayArithmeticModulus.idealClass M hM m a ha hc =
          RayArithmeticModulus.principalClass M hM m (Units.mk0 (b : K) hb) hf :=
        RayArithmeticPrincipalAux.idealClass_eq_principalClass M hM m a ha hc b hb hf he
      _ = RayArithmeticSigns.t M hM m hm :=
        RayArithmeticSigns.principalClass_of_neg_neg M hM m hm _ hf h₁ h₂

/-- Source: positive principal-generator calculation; [RW-rec]; [RW26, p. 20]. The same generator
works for every x, including zero. -/
theorem class_one_generator (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m a)
    (hclass : RayArithmeticModulus.idealClass M hM m a ha hc = 1) :
    ∃ b : 𝓞 K, a = Ideal.span {b} ∧
      0 < ActualField.sigma₁ M hM (b : K) ∧
      0 < ActualField.sigma₂ M hM (b : K) ∧
      RayArithmeticModulus.GloballyCongruent M hM m (b : K) ∧
      (b : K) ∈ RayArithmeticOrder.multiplierOrder M hM ∧
      ∀ x : ActualLattice.Group M hM,
        ((b : K) - 1) * L3.pseudolatticeRepresentative P I x ∈ (I).val := by
  obtain ⟨b, he, h₁, h₂, hg, ho⟩ := (idealClass_eq_one_iff M hM m hm a ha hc).mp hclass
  exact ⟨b, he, h₁, h₂, hg, ho, sub_one_mul_representative_mem M hM m hm (b : K) hg⟩

/-- Source: double-negative generator calculation, same sources, with the beta=-alpha label change.
Still valid when t=1. [RW26, p. 20]. -/
theorem class_t_generator (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m a)
    (hclass : RayArithmeticModulus.idealClass M hM m a ha hc = RayArithmeticSigns.t M hM m hm) :
    ∃ b : 𝓞 K, a = Ideal.span {b} ∧
      ActualField.sigma₁ M hM (b : K) < 0 ∧
      ActualField.sigma₂ M hM (b : K) < 0 ∧
      RayArithmeticModulus.GloballyCongruent M hM m (b : K) ∧
      (b : K) ∈ RayArithmeticOrder.multiplierOrder M hM ∧
      ∀ x : ActualLattice.Group M hM,
        ((b : K) - 1) * L3.pseudolatticeRepresentative P I x ∈ (I).val := by
  obtain ⟨b, he, h₁, h₂, hg, ho⟩ := (idealClass_eq_t_iff M hM m hm a ha hc).mp hclass
  exact ⟨b, he, h₁, h₂, hg, ho, sub_one_mul_representative_mem M hM m hm (b : K) hg⟩

/-- The integral inclusion of the actual multiplier order. -/
def orderToIntegers : RayArithmeticOrder.multiplierOrder M hM →+* 𝓞 K where
  toFun a := ⟨(a : K), RayArithmeticOrder.multiplierOrder_integral M hM (a : K) a.property⟩
  map_one' := by ext; rfl
  map_mul' := by intros; ext; rfl
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

def contraction (a : Ideal (𝓞 K)) : Ideal (RayArithmeticOrder.multiplierOrder M hM) :=
  Ideal.comap (orderToIntegers M hM) a

/-- Source: contraction of a conductor-prime principal ideal, [RW-rec]; [RW26, p. 20]. -/
theorem contraction_principal (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : 𝓞 K) (ha : RayArithmeticModulus.GloballyCongruent M hM m (a : K)) :
    contraction M hM (Ideal.span {a}) =
      Ideal.span {(⟨(a : K), globallyCongruent_mem_order M hM m (a : K) ha⟩ :
        RayArithmeticOrder.multiplierOrder M hM)} := by
  ext x
  constructor
  · intro hx
    change orderToIntegers M hM x ∈ Ideal.span {a} at hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    have hyK : (x : K) = (a : K) * (y : K) := by
      have he := congrArg (algebraMap (𝓞 K) K) hy
      have hxcoe : (algebraMap (𝓞 K) K) (orderToIntegers M hM x) = (x : K) := rfl
      rw [hxcoe, map_mul] at he
      exact he
    have hmul : ((a : K) - 1) * (y : K) ∈ RayArithmeticOrder.multiplierOrder M hM := by
      obtain ⟨b, hb⟩ := ha
      rw [hb]
      have hmem := RayArithmeticOrder.conductor_mul_mem M hM
        ((m : 𝓞 K) * b * y)
      convert hmem using 1 <;>
        simp only [RayArithmeticModulus.level, Nat.cast_mul, map_mul, map_natCast] <;> ring
    have hyO : (y : K) ∈ RayArithmeticOrder.multiplierOrder M hM := by
      convert (RayArithmeticOrder.multiplierOrder M hM).sub_mem x.property hmul using 1
      rw [hyK]
      ring
    apply Ideal.mem_span_singleton.mpr
    refine ⟨⟨(y : K), hyO⟩, ?_⟩
    exact Subtype.ext hyK
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    change orderToIntegers M hM x ∈ Ideal.span {a}
    apply Ideal.mem_span_singleton.mpr
    refine ⟨orderToIntegers M hM y, ?_⟩
    rw [hy, map_mul]
    congr 1

def doubleNegativeInteger (m : ℕ) : 𝓞 K := 1 - (RayArithmeticModulus.level M hM m : 𝓞 K)
def doubleNegativeIdeal (m : ℕ) : Ideal (𝓞 K) := Ideal.span {doubleNegativeInteger M hM m}

/-- Source: the explicit nonprime witness (1-cm) O_K. [RW26, p. 20]. -/
theorem doubleNegativeIdeal_valid (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    doubleNegativeIdeal M hM m ≠ ⊥ ∧
      RayArithmeticModulus.CoprimeIdeal M hM m (doubleNegativeIdeal M hM m) := by
  constructor
  · intro he
    have hz : doubleNegativeInteger M hM m = 0 := Ideal.span_singleton_eq_bot.mp he
    have hs := (RayArithmeticPrincipalAux.one_sub_level_signs M hM m hm).1
    have hv : (doubleNegativeInteger M hM m : K) =
        1 - (RayArithmeticModulus.level M hM m : K) := by
      simp only [doubleNegativeInteger, map_sub, map_one, map_natCast]
    simp [← hv, hz] at hs
  · change IsCoprime (Ideal.span {1 - (RayArithmeticModulus.level M hM m : 𝓞 K)})
      (Ideal.span {(RayArithmeticModulus.level M hM m : 𝓞 K)})
    rw [Ideal.isCoprime_span_singleton_iff]
    exact ⟨1, 1, by ring⟩

/-- Source: its negative congruent generator represents the product sign, [RW-rec]; including the
t=1 branch. [RW26, p. 20]. -/
theorem doubleNegativeIdeal_class (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    RayArithmeticModulus.idealClass M hM m (doubleNegativeIdeal M hM m)
        (doubleNegativeIdeal_valid M hM m hm).1 (doubleNegativeIdeal_valid M hM m hm).2 =
      RayArithmeticSigns.t M hM m hm := by
  apply (idealClass_eq_t_iff M hM m hm _
    (doubleNegativeIdeal_valid M hM m hm).1 (doubleNegativeIdeal_valid M hM m hm).2).mpr
  have hv : (doubleNegativeInteger M hM m : K) =
      1 - (RayArithmeticModulus.level M hM m : K) := by
    simp only [doubleNegativeInteger, map_sub, map_one, map_natCast]
  have hs := RayArithmeticPrincipalAux.one_sub_level_signs M hM m hm
  have hg : RayArithmeticModulus.GloballyCongruent M hM m
      (doubleNegativeInteger M hM m : K) := by
    rw [hv]
    exact RayArithmeticPrincipalAux.one_sub_level_congruent M hM m
  refine ⟨doubleNegativeInteger M hM m, rfl, ?_, ?_, hg,
    globallyCongruent_mem_order M hM m _ hg⟩
  · simpa only [hv] using hs.1
  · simpa only [hv] using hs.2

/-- Source: the separate t=1 argument. The two sign choices coexist. [RW26, p. 20]. -/
theorem t_eq_one_both_generators (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (ht : RayArithmeticSigns.t M hM m hm = 1) :
    ∃ b : 𝓞 K, doubleNegativeIdeal M hM m = Ideal.span {b} ∧
      0 < ActualField.sigma₁ M hM (b : K) ∧
      0 < ActualField.sigma₂ M hM (b : K) ∧
      RayArithmeticModulus.GloballyCongruent M hM m (b : K) ∧
      (b : K) ∈ RayArithmeticOrder.multiplierOrder M hM ∧
      ActualField.sigma₁ M hM (doubleNegativeInteger M hM m : K) < 0 ∧
      ActualField.sigma₂ M hM (doubleNegativeInteger M hM m : K) < 0 ∧
      RayArithmeticModulus.GloballyCongruent M hM m (doubleNegativeInteger M hM m : K) ∧
      (doubleNegativeInteger M hM m : K) ∈ RayArithmeticOrder.multiplierOrder M hM := by
  have hclass := (doubleNegativeIdeal_class M hM m hm).trans ht
  obtain ⟨b, he, h₁, h₂, hg, ho⟩ := (idealClass_eq_one_iff M hM m hm _
    (doubleNegativeIdeal_valid M hM m hm).1 (doubleNegativeIdeal_valid M hM m hm).2).mp hclass
  have hv : (doubleNegativeInteger M hM m : K) =
      1 - (RayArithmeticModulus.level M hM m : K) := by
    simp only [doubleNegativeInteger, map_sub, map_one, map_natCast]
  have hs := RayArithmeticPrincipalAux.one_sub_level_signs M hM m hm
  have hgd : RayArithmeticModulus.GloballyCongruent M hM m
      (doubleNegativeInteger M hM m : K) := by
    rw [hv]
    exact RayArithmeticPrincipalAux.one_sub_level_congruent M hM m
  refine ⟨b, he, h₁, h₂, hg, ho, ?_, ?_, hgd,
    globallyCongruent_mem_order M hM m _ hgd⟩
  · simpa only [hv] using hs.1
  · simpa only [hv] using hs.2

#check @idealClass_eq_one_iff
#check @idealClass_eq_t_iff
#check @class_one_generator
#check @class_t_generator
#print contraction
#print doubleNegativeIdeal

end SICLean.L5.RayArithmeticPrincipal
