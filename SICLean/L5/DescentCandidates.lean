import SICLean.L5.SplitFrobeniusFinite
import SICLean.L4.PseudolatticeHomothety

set_option autoImplicit false

/-!
# The two principal-ideal candidates

The field, period, lattice, label maps, ℚ̄ lifts, and normalization are
those of the actual values. In particular `normalizedLift` is
`valueLift x / valueLift 0`, and zero is retained.

[RW26, p. 20, (37)] identifies the actual objects. Positive homothety is
[RW-rec, p. 3, (1)]; the principal calculation is [RW-rec, p. 14, Lem. 8];
the same-sign branches are [RW-rec, p. 20, Prop. 8], continued on
[RW-rec, p. 21]. No mixed-sign homothety is used here.

The colon ideal is defined for an arbitrary integral ideal. Primality is
used to match the candidate lattices of [RW-rec, Thm. 8]. The candidate
identities have the `hr` / `hq` shapes of `theorem8_identity_target` and
`theorem8_reflection_target`. Their ray classes are arithmetic hypotheses;
membership of a value in a ray class field is not a hypothesis. Both
candidates are treated before any membership of an ideal translate in a
finite field is assumed.
-/

noncomputable section
open scoped NumberField MatrixGroups Classical

namespace SICLean.L5.DescentCandidates

open L3 SplitPrimeLattice SplitPrimeValues SplitFrobenius

variable {K : Type} [Field K] [NumberField K]

/-- Positive homothety for the algebraic lift, including zero.
[RW26, pp. 2--3, (2)]; [RW26, p. 20, (37)]; [RW-rec, p. 3, (1)];
[RW-rec, p. 20, Prop. 8]. -/
theorem valueLift_scale (P0 : PeriodData K) (I J : StablePseudolattice P0)
    (a : K) (ha : TotallyPositive P0 a)
    (hJ : J.val = pseudolatticeScale a I.val)
    (x : PseudolatticeGroup P0 I) :
    valueLift P0 J
        (M72.scaleEquiv P0 I J a (totallyPositive_ne_zero P0 a ha) hJ x) =
      valueLift P0 I x := by
  apply Galois.embed.injective
  change Galois.embed (valueLift P0 J
      (M72.scaleEquiv P0 I J a (totallyPositive_ne_zero P0 a ha) hJ x)) =
    Galois.embed (valueLift P0 I x)
  rw [embed_valueLift, embed_valueLift]
  exact M72.value_scale P0 I J a ha hJ x

/-- The same positive homothety, divided by the value at zero.
[RW26, pp. 2--3, (2)]; [RW26, p. 20, (37)]; [RW-rec, p. 3, Def. 1];
[RW-rec, p. 20, Prop. 8]. -/
theorem normalizedLift_scale (P0 : PeriodData K) (I J : StablePseudolattice P0)
    (a : K) (ha : TotallyPositive P0 a)
    (hJ : J.val = pseudolatticeScale a I.val)
    (x : PseudolatticeGroup P0 I) :
    normalizedLift P0 J
        (M72.scaleEquiv P0 I J a (totallyPositive_ne_zero P0 a ha) hJ x) =
      normalizedLift P0 I x := by
  unfold normalizedLift
  have hzero := valueLift_scale P0 I J a ha hJ 0
  rw [map_zero] at hzero
  rw [valueLift_scale P0 I J a ha hJ x, hzero]

/-- Since an additive lattice is closed under negation, replacing α by
β = -α does not change its inverse homothety. The identity holds at zero.
[RW26, p. 20, (37)]; [RW-rec, p. 20, Prop. 8]; [RW-rec, p. 21]. -/
theorem inverseScale_neg (P0 : PeriodData K) (I : StablePseudolattice P0)
    (a : K) :
    pseudolatticeScale a⁻¹ I.val = pseudolatticeScale (-a)⁻¹ I.val := by
  ext x
  rw [pseudolatticeScale_mem_iff, pseudolatticeScale_mem_iff]
  constructor <;> rintro ⟨y, hy, hxy⟩
  · refine ⟨-y, I.val.neg_mem hy, ?_⟩
    simpa only [inv_neg, neg_mul, mul_neg, neg_neg] using hxy
  · refine ⟨-y, I.val.neg_mem hy, ?_⟩
    simpa only [inv_neg, neg_mul, mul_neg, neg_neg] using hxy

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K0" => ActualField.baseField M hM
local notation "P0" => ActualField.periodData M hM
local notation "I0" => ActualLattice.stableLattice M hM

/-- The contraction colon of an arbitrary integral ideal.
[RW26, p. 20, (37)]; [RW-rec, §8, p. 13]; [RW-rec, p. 14, Lem. 8].
No homothety or value identity is part of the definition. -/
def inverseIdealCarrier (a : Ideal (𝓞 K0)) : Submodule ℤ K0 :=
  ⨅ b : RayArithmeticPrincipal.contraction M hM a,
    (I0).val.comap (LinearMap.mulLeft ℤ (b.val.val : K0))

/-- The principal colon for any nonzero integral generator, including
composite ideals. [RW26, p. 20, (37)]; [RW-rec, §8]; [RW-rec, p. 14, Lem. 8].
The congruence places α in the multiplier order. -/
theorem principal_inverseIdealCarrier (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : 𝓞 K0) (ha : (a : K0) ≠ 0)
    (hcong : RayArithmeticModulus.GloballyCongruent M hM m (a : K0)) :
    inverseIdealCarrier M hM (Ideal.span {a}) =
      pseudolatticeScale (a : K0)⁻¹ (I0).val := by
  let b : RayArithmeticOrder.multiplierOrder M hM :=
    ⟨(a : K0), RayArithmeticPrincipal.globallyCongruent_mem_order M hM m (a : K0) hcong⟩
  have hc : RayArithmeticPrincipal.contraction M hM (Ideal.span {a}) =
      Ideal.span {b} := RayArithmeticPrincipal.contraction_principal M hM m hm a hcong
  ext x
  simp only [inverseIdealCarrier, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mulLeft_apply]
  constructor
  · intro hx
    have hb : b ∈ RayArithmeticPrincipal.contraction M hM (Ideal.span {a}) := by
      rw [hc]
      exact Ideal.subset_span (Set.mem_singleton b)
    have hax : (a : K0) * x ∈ (I0).val := hx ⟨b, hb⟩
    exact (pseudolatticeScale_mem_iff _ _ _).mpr
      ⟨(a : K0) * x, hax, by simp [ha]⟩
  · intro hx z
    obtain ⟨y, hy, hxy⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
    have hz : z.val ∈ Ideal.span {b} := by
      rw [← hc]
      exact z.property
    obtain ⟨c, hzc⟩ := Ideal.mem_span_singleton.mp hz
    have hzcK : (z.val.val : K0) = (a : K0) * (c : K0) :=
      congrArg Subtype.val hzc
    change (z.val.val : K0) * x ∈ (I0).val
    rw [← hxy, hzcK]
    have he : ((a : K0) * (c : K0)) * ((a : K0)⁻¹ * y) = (c : K0) * y := by
      field_simp
    rw [he]
    exact (RayArithmeticOrder.mem_multiplierOrder M hM (c : K0)).mp c.property y hy

/-- The same contracted principal ideal, specialized to the prime candidate
lattice via `actual_principal_inverse`.
[RW26, p. 20, (37)]; [RW-rec, §8]; [RW-rec, p. 14, Lem. 8].
Maximal-order stability of the original lattice is not assumed. -/
theorem principal_inversePrimeLattice (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (r : FinitePlace.Prime K0) (a : 𝓞 K0)
    (hcong : RayArithmeticModulus.GloballyCongruent M hM m (a : K0))
    (hprincipal : r.asIdeal = Ideal.span {a}) :
    (inversePrimeLattice P0 I0 r).val =
      pseudolatticeScale (a : K0)⁻¹ (I0).val := by
  have ha : (a : K0) ≠ 0 := by
    intro hz
    have ha0 : a = 0 := Subtype.ext hz
    apply r.ne_bot
    simpa [ha0] using hprincipal
  let b : RayArithmeticOrder.multiplierOrder M hM :=
    ⟨(a : K0), RayArithmeticPrincipal.globallyCongruent_mem_order M hM m (a : K0) hcong⟩
  have hb : b ≠ 0 := fun hz => ha (congrArg Subtype.val hz)
  exact SplitFrobeniusFinite.actual_principal_inverse M hM r b hb (by
    rw [hprincipal]
    exact RayArithmeticPrincipal.contraction_principal M hM m hm a hcong)

/-- Positive scaling after the identity-on-representatives projection sends
every label back to x, because (α - 1)x lies in the original lattice.
[RW26, p. 20, (37)]; [RW-rec, p. 14, Lem. 8]; [RW-rec, p. 3, (1)]. -/
theorem positive_project_label (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (J : StablePseudolattice P0) (a : K0)
    (hcong : RayArithmeticModulus.GloballyCongruent M hM m a)
    (hpos : TotallyPositive P0 a) (hIJ : (I0).val ≤ J.val)
    (hscale : (I0).val = pseudolatticeScale a J.val)
    (x : ActualLattice.Group M hM) :
    M72.scaleEquiv P0 J I0 a (totallyPositive_ne_zero P0 a hpos) hscale
        (DistributionOrbitGeometry.periodProject P0 I0 J hIJ x) = x := by
  refine Quotient.inductionOn x ?_
  intro z
  change M72.scaleEquiv P0 J I0 a (totallyPositive_ne_zero P0 a hpos) hscale
    (DistributionOrbitGeometry.periodProject P0 I0 J hIJ
      (pseudolatticeMk P0 I0 z.val z.property)) = pseudolatticeMk P0 I0 z.val z.property
  rw [DistributionOrbitGeometry.periodProject_mk, M72.scaleEquiv_mk]
  exact RayArithmeticPrincipal.mk_mul_eq M hM m hm a hcong z.val z.property

/-- For a double-negative α, the positive element β = -α sends the projected
label to -x. The congruence for α is used, so β need not be 1 modulo cm.
This includes x = 0. [RW26, p. 20, (37)]; [RW-rec, p. 14, Lem. 8];
[RW-rec, p. 20, Prop. 8]; [RW-rec, p. 21]. -/
theorem negative_project_label (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (J : StablePseudolattice P0) (a : K0)
    (hcong : RayArithmeticModulus.GloballyCongruent M hM m a)
    (hpos : TotallyPositive P0 (-a)) (hIJ : (I0).val ≤ J.val)
    (hscale : (I0).val = pseudolatticeScale (-a) J.val)
    (x : ActualLattice.Group M hM) :
    M72.scaleEquiv P0 J I0 (-a) (totallyPositive_ne_zero P0 (-a) hpos) hscale
        (DistributionOrbitGeometry.periodProject P0 I0 J hIJ x) = -x := by
  refine Quotient.inductionOn x ?_
  intro z
  change M72.scaleEquiv P0 J I0 (-a) (totallyPositive_ne_zero P0 (-a) hpos) hscale
    (DistributionOrbitGeometry.periodProject P0 I0 J hIJ
      (pseudolatticeMk P0 I0 z.val z.property)) = -pseudolatticeMk P0 I0 z.val z.property
  rw [DistributionOrbitGeometry.periodProject_mk, M72.scaleEquiv_mk]
  obtain ⟨hz, he⟩ := RayArithmeticPrincipal.mk_neg_mul_eq M hM m hm a hcong z.val z.property
  exact he

/-- A globally congruent, totally positive integral generator collapses the
prime candidate to the original normalized value.
[RW26, p. 20, (37)]; [RW-rec, p. 14, Lem. 8]; [RW-rec, p. 3, (1)]. -/
theorem principal_identity_target (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (r : FinitePlace.Prime K0) (a : 𝓞 K0)
    (hprincipal : r.asIdeal = Ideal.span {a})
    (hcong : RayArithmeticModulus.GloballyCongruent M hM m (a : K0))
    (h₁ : 0 < ActualField.sigma₁ M hM (a : K0))
    (h₂ : 0 < ActualField.sigma₂ M hM (a : K0)) :
    ∀ x : ActualLattice.Group M hM,
      normalizedLift P0 (inversePrimeLattice P0 I0 r) (projectInverse P0 I0 r x) =
        normalizedLift P0 I0 x := by
  have hpos : TotallyPositive P0 (a : K0) := ⟨h₁, h₂⟩
  have ha := totallyPositive_ne_zero P0 (a : K0) hpos
  have hJ := principal_inversePrimeLattice M hM m hm r a hcong hprincipal
  have hscale : (I0).val =
      pseudolatticeScale (a : K0) (inversePrimeLattice P0 I0 r).val := by
    rw [hJ]
    exact (pseudolatticeScale_inv (a : K0) ha (I0).val).2.symm
  intro x
  calc
    normalizedLift P0 (inversePrimeLattice P0 I0 r) (projectInverse P0 I0 r x) =
        normalizedLift P0 I0 (M72.scaleEquiv P0 (inversePrimeLattice P0 I0 r) I0
          (a : K0) ha hscale (projectInverse P0 I0 r x)) :=
      (normalizedLift_scale P0 (inversePrimeLattice P0 I0 r) I0 (a : K0) hpos hscale _).symm
    _ = normalizedLift P0 I0 x := congrArg (normalizedLift P0 I0)
      (positive_project_label M hM m hm _ (a : K0) hcong hpos
        (le_inversePrime P0 I0 r) hscale x)

/-- A double-negative generator gives label reflection, by β = -α and
positive homothety. The value itself is neither inverted nor conjugated.
Normalization at zero extends the formula to every x.
[RW26, p. 20, (37)]; [RW-rec, p. 14, Lem. 8]; [RW-rec, p. 20, Prop. 8];
[RW-rec, p. 21]. -/
theorem principal_reflection_target (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (r : FinitePlace.Prime K0) (a : 𝓞 K0)
    (hprincipal : r.asIdeal = Ideal.span {a})
    (hcong : RayArithmeticModulus.GloballyCongruent M hM m (a : K0))
    (h₁ : ActualField.sigma₁ M hM (a : K0) < 0)
    (h₂ : ActualField.sigma₂ M hM (a : K0) < 0) :
    ∀ x : ActualLattice.Group M hM,
      normalizedLift P0 (inversePrimeLattice P0 I0 r) (projectInverse P0 I0 r x) =
        normalizedLift P0 I0 (-x) := by
  have hpos : TotallyPositive P0 (-(a : K0)) := by
    change 0 < ActualField.sigma₁ M hM (-(a : K0)) ∧
      0 < ActualField.sigma₂ M hM (-(a : K0))
    simpa only [map_neg, neg_pos] using And.intro h₁ h₂
  have ha := totallyPositive_ne_zero P0 (-(a : K0)) hpos
  have hJ := principal_inversePrimeLattice M hM m hm r a hcong hprincipal
  rw [inverseScale_neg P0 I0 (a : K0)] at hJ
  have hscale : (I0).val =
      pseudolatticeScale (-(a : K0)) (inversePrimeLattice P0 I0 r).val := by
    rw [hJ]
    exact (pseudolatticeScale_inv (-(a : K0)) ha (I0).val).2.symm
  intro x
  calc
    normalizedLift P0 (inversePrimeLattice P0 I0 r) (projectInverse P0 I0 r x) =
        normalizedLift P0 I0 (M72.scaleEquiv P0 (inversePrimeLattice P0 I0 r) I0
          (-(a : K0)) ha hscale (projectInverse P0 I0 r x)) :=
      (normalizedLift_scale P0 (inversePrimeLattice P0 I0 r) I0 (-(a : K0)) hpos hscale _).symm
    _ = normalizedLift P0 I0 (-x) := congrArg (normalizedLift P0 I0)
      (negative_project_label M hM m hm _ (a : K0) hcong hpos
        (le_inversePrime P0 I0 r) hscale x)

/-- The `hr` / `hq` identity-target shape for the trivial arithmetic ray class.
`class_one_generator` is applied once for every label x.
[RW26, p. 20, (37)]; [RW-rec, p. 14, Lem. 8]; [RW-rec, p. 15, Prop. 4].
There is no value-membership hypothesis and no nonzero-label hypothesis. -/
theorem class_one_identity_target (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (r : FinitePlace.Prime K0)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m r.asIdeal)
    (hclass : RayArithmeticModulus.idealClass M hM m r.asIdeal r.ne_bot hc = 1) :
    ∀ x : ActualLattice.Group M hM,
      normalizedLift P0 (inversePrimeLattice P0 I0 r) (projectInverse P0 I0 r x) =
        normalizedLift P0 I0 x := by
  obtain ⟨a, hprincipal, h₁, h₂, hcong, _, _⟩ :=
    RayArithmeticPrincipal.class_one_generator M hM m hm r.asIdeal r.ne_bot hc hclass
  exact principal_identity_target M hM m hm r a hprincipal hcong h₁ h₂

/-- The reflection-target shape for t = s₁ s₂, including t = 1.
`class_t_generator` is applied once, and then β = -α.
Both signs are taken simultaneously.
[RW26, p. 20, (37)]; [RW-rec, p. 14, Lem. 8]; [RW-rec, p. 15];
[RW-rec, p. 20, Prop. 8]. -/
theorem class_t_reflection_target (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (r : FinitePlace.Prime K0)
    (hc : RayArithmeticModulus.CoprimeIdeal M hM m r.asIdeal)
    (hclass : RayArithmeticModulus.idealClass M hM m r.asIdeal r.ne_bot hc =
      RayArithmeticSigns.t M hM m hm) :
    ∀ x : ActualLattice.Group M hM,
      normalizedLift P0 (inversePrimeLattice P0 I0 r) (projectInverse P0 I0 r x) =
        normalizedLift P0 I0 (-x) := by
  obtain ⟨a, hprincipal, h₁, h₂, hcong, _, _⟩ :=
    RayArithmeticPrincipal.class_t_generator M hM m hm r.asIdeal r.ne_bot hc hclass
  exact principal_reflection_target M hM m hm r a hprincipal hcong h₁ h₂

/-- Both prime candidates are the identity target when both arithmetic ray
classes are trivial. This applies in particular to a conjugate split pair;
the two class equalities are those of the class-field comparison.
[RW26, p. 20, (37)]; [RW-rec, p. 14, Lem. 8]; [RW-rec, p. 15, Prop. 4]. -/
theorem class_one_pair_targets (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (r q : FinitePlace.Prime K0)
    (hcr : RayArithmeticModulus.CoprimeIdeal M hM m r.asIdeal)
    (hcq : RayArithmeticModulus.CoprimeIdeal M hM m q.asIdeal)
    (hrclass : RayArithmeticModulus.idealClass M hM m r.asIdeal r.ne_bot hcr = 1)
    (hqclass : RayArithmeticModulus.idealClass M hM m q.asIdeal q.ne_bot hcq = 1) :
    (∀ x : ActualLattice.Group M hM,
      normalizedLift P0 (inversePrimeLattice P0 I0 r) (projectInverse P0 I0 r x) =
        normalizedLift P0 I0 x) ∧
    (∀ x : ActualLattice.Group M hM,
      normalizedLift P0 (inversePrimeLattice P0 I0 q) (projectInverse P0 I0 q x) =
        normalizedLift P0 I0 x) := by
  exact ⟨class_one_identity_target M hM m hm r hcr hrclass,
    class_one_identity_target M hM m hm q hcq hqclass⟩

/-- Both t-class candidates are the same reflected label, including when t = 1.
[RW-rec, Thm. 8] does not require a preferred orientation of the pair.
[RW26, p. 20, (37)]; [RW-rec, p. 14, Lem. 8]; [RW-rec, p. 15];
[RW-rec, p. 20, Prop. 8]. -/
theorem class_t_pair_targets (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (r q : FinitePlace.Prime K0)
    (hcr : RayArithmeticModulus.CoprimeIdeal M hM m r.asIdeal)
    (hcq : RayArithmeticModulus.CoprimeIdeal M hM m q.asIdeal)
    (hrclass : RayArithmeticModulus.idealClass M hM m r.asIdeal r.ne_bot hcr =
      RayArithmeticSigns.t M hM m hm)
    (hqclass : RayArithmeticModulus.idealClass M hM m q.asIdeal q.ne_bot hcq =
      RayArithmeticSigns.t M hM m hm) :
    (∀ x : ActualLattice.Group M hM,
      normalizedLift P0 (inversePrimeLattice P0 I0 r) (projectInverse P0 I0 r x) =
        normalizedLift P0 I0 (-x)) ∧
    (∀ x : ActualLattice.Group M hM,
      normalizedLift P0 (inversePrimeLattice P0 I0 q) (projectInverse P0 I0 q x) =
        normalizedLift P0 I0 (-x)) := by
  exact ⟨class_t_reflection_target M hM m hm r hcr hrclass,
    class_t_reflection_target M hM m hm q hcq hqclass⟩

/-- At a finite place, the normalized family in F satisfies the identity-target
congruence of [RW-rec, Thm. 8]: both principal candidates agree with it.
[RW26, p. 20, (37)]; [RW-rec, pp. 12--13, Thm. 8]; [RW-rec, p. 14, Lem. 8];
[RW-rec, p. 15, Prop. 4]. -/
theorem theorem8_identity_of_classes (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hlocal : LocallyMaximal P0 I0 p)
    {r q : FinitePlace.Prime K0} (hsplit : IsSplitPair p r q)
    (hcr : RayArithmeticModulus.CoprimeIdeal M hM m r.asIdeal)
    (hcq : RayArithmeticModulus.CoprimeIdeal M hM m q.asIdeal)
    (hrclass : RayArithmeticModulus.idealClass M hM m r.asIdeal r.ne_bot hcr = 1)
    (hqclass : RayArithmeticModulus.idealClass M hM m q.asIdeal q.ne_bot hcq = 1)
    (P : FinitePlace.Prime F) (hP : FinitePlace.residueChar P = p)
    (u : ActualLattice.Group M hM → F)
    (hu : ∀ x, (u x : Galois.Qbar) = normalizedLift P0 I0 x) :
    ∀ x : ActualLattice.Group M hM,
      GoodReductionLocal.congruentAt F P (u x ^ p) (u x) := by
  obtain ⟨hr, hq⟩ := class_one_pair_targets M hM m hm r q hcr hcq hrclass hqclass
  exact SplitFrobeniusFinite.theorem8_identity_target F P0 I0 hodd hlocal hsplit
    P hP u hu hr hq

/-- At a finite place, Frobenius of a normalized value is congruent to the
reflected label of the same family. No translated value is adjoined, and t
may be 1. [RW26, p. 20, (37)]; [RW-rec, pp. 12--13, Thm. 8];
[RW-rec, p. 14, Lem. 8]; [RW-rec, p. 20, Prop. 8]. -/
theorem theorem8_reflection_of_classes (m : ℕ)
    (hm : RayArithmeticOrder.ValidLevel M hM m)
    (F : IntermediateField ℚ Galois.Qbar) [NumberField F]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hlocal : LocallyMaximal P0 I0 p)
    {r q : FinitePlace.Prime K0} (hsplit : IsSplitPair p r q)
    (hcr : RayArithmeticModulus.CoprimeIdeal M hM m r.asIdeal)
    (hcq : RayArithmeticModulus.CoprimeIdeal M hM m q.asIdeal)
    (hrclass : RayArithmeticModulus.idealClass M hM m r.asIdeal r.ne_bot hcr =
      RayArithmeticSigns.t M hM m hm)
    (hqclass : RayArithmeticModulus.idealClass M hM m q.asIdeal q.ne_bot hcq =
      RayArithmeticSigns.t M hM m hm)
    (P : FinitePlace.Prime F) (hP : FinitePlace.residueChar P = p)
    (u : ActualLattice.Group M hM → F)
    (hu : ∀ x, (u x : Galois.Qbar) = normalizedLift P0 I0 x) :
    ∀ x : ActualLattice.Group M hM,
      GoodReductionLocal.congruentAt F P (u x ^ p) (u (-x)) := by
  obtain ⟨hr, hq⟩ := class_t_pair_targets M hM m hm r q hcr hcq hrclass hqclass
  exact SplitFrobeniusFinite.theorem8_reflection_target F P0 I0 hodd hlocal hsplit
    P hP u hu hr hq

end SICLean.L5.DescentCandidates
