import SICLean.L4.G2RepellingPointValues
import SICLean.L4.G2SpecialValueBridgeAux

set_option autoImplicit false

/-!
# Actual auxiliary F± and the transport contract

Source conventions
are those of G2ReflectionGeometry.lean. The new functions have the explicit
repelling μΦ formula and the two separate zero constants. They are not
defined by pulling back attracting values or by selecting functions with
Fourier/pentagon properties. Quotient.lift uses the pointwise bridge for
well-definedness.

The repelling plus zero used here is ε^(-1/2). [RW26, (2)]. It matches the existing attracting F+
after
inverse reflection. The minus zero is matched separately, without swapping.

The final two iff statements only transport finite-sum identities.
They do not assert either identity or an RWAnalyticInput, and require no G1.
-/

noncomputable section

open Classical Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2.SpecialValueBridge

open SICLean.L4.G2.ReflectionGeometry SICLean.L4.G2.RepellingPointValues

/--
[RW26, p. 2, (2)] gives the nonzero expression. The repelling zero
is normalized for the inverse reflection.
-/
def repellingPlusLift (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℂ :=
  if x ∈ specialValueLattice M then (Real.sqrt (epsilon M) : ℂ)⁻¹
  else repellingRaw M x

/--
The other explicit zero constant; [RW26, p. 3, (4)] describes the matched attracting value.
-/
def repellingMinusLift (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℂ :=
  if x ∈ specialValueLattice M then (Real.sqrt (epsilon M) : ℂ)
  else repellingRaw M x

/--
All integer representatives, including every nonzero lattice vector.
Nonzero classes use repellingRaw_reflection; each lattice branch uses its
own root; [RW26, p. 2, p. 3, (2), (4)]
are the attracting definitions being matched, not an extra analytic input.
-/
theorem repellingValues_lift_reflection (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) :
    repellingPlusLift M x = specialValuePlusLift (modularInverseReflection M) (x.1, -x.2) ∧
      repellingMinusLift M x =
        specialValueMinusLift (modularInverseReflection M) (x.1, -x.2) := by
  have hx := G2SpecialValueBridgeAux.rowReflection_mem_lattice_iff M x
  by_cases hxM : x ∈ specialValueLattice M
  · have hxR := hx.mpr hxM
    simp only [repellingPlusLift, repellingMinusLift, specialValuePlusLift,
      specialValueMinusLift, if_pos hxM, if_pos hxR, reflection_sqrt M hM, inv_inv,
      and_self]
  · have hxR := mt hx.mp hxM
    simpa only [repellingPlusLift, repellingMinusLift, specialValuePlusLift,
      specialValueMinusLift, if_neg hxM, if_neg hxR, and_self] using
      repellingRaw_reflection M hM x hxM

/--
Descent of this explicit plus lift. Well-definedness follows from
the pointwise bridge and existing descent; [RW26, p. 12, Lemma 2].
-/
def repellingPlus (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    SpecialValueGroup M → ℂ :=
  Quotient.lift (repellingPlusLift M) (by
    intro a b hab
    rw [(repellingValues_lift_reflection M hM a).1,
      (repellingValues_lift_reflection M hM b).1]
    have heq : specialValueMk M a = specialValueMk M b := Quotient.sound hab
    have hr := congrArg (reflectionEquiv M) heq
    simpa only [reflectionEquiv_mk, specialValuePlus_mk] using
      congrArg (specialValuePlus (modularInverseReflection M) (reflection_admissible M hM)) hr)

/--
The separate minus lift. Well-definedness follows from the same bridge. [RW26, p. 12, Lemma 2].
-/
def repellingMinus (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    SpecialValueGroup M → ℂ :=
  Quotient.lift (repellingMinusLift M) (by
    intro a b hab
    rw [(repellingValues_lift_reflection M hM a).2,
      (repellingValues_lift_reflection M hM b).2]
    have heq : specialValueMk M a = specialValueMk M b := Quotient.sound hab
    have hr := congrArg (reflectionEquiv M) heq
    simpa only [reflectionEquiv_mk, specialValueMinus_mk] using
      congrArg (specialValueMinus (modularInverseReflection M) (reflection_admissible M hM)) hr)

/--
Concrete sum divided by the positive √N. Finiteness is supplied by the
existing theorem, not a new assumption or a hidden analytic property; [RW26, p. 3, (6), (7)].
-/
def normalizedValueSum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : SpecialValueGroup M → ℂ) : ℂ :=
  letI : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  letI : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  (Real.sqrt (specialValueOrder M : ℝ) : ℂ)⁻¹ * ∑ x, f x

/--
The concrete auxiliary functions on every representative; [RW26, p. 12, Lemma 2] supplies descent.
-/
theorem repellingValues_mk (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    repellingPlus M hM (specialValueMk M x) = repellingPlusLift M x ∧
      repellingMinus M hM (specialValueMk M x) = repellingMinusLift M x := by
  exact ⟨rfl, rfl⟩

/--
Both zero constants, with no appeal to the raw value at (m,n)=(0,0); [RW26, p. 3, (4)]
gives the corresponding attracting constants.
-/
theorem repellingValues_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    repellingPlus M hM 0 = (Real.sqrt (epsilon M) : ℂ)⁻¹ ∧
      repellingMinus M hM 0 = (Real.sqrt (epsilon M) : ℂ) := by
  have h := repellingValues_mk M hM 0
  simpa only [map_zero, repellingPlusLift, repellingMinusLift,
    AddSubgroup.zero_mem, if_true] using h

/--
Outside the actual zero class both auxiliary functions are the same
specified μΦ; [RW26, p. 2, p. 3, (2), footnote 2]. A congruence S_x≡0 is not a zero-class test.
-/
theorem repellingValues_nonzero_class (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : ℤ × ℤ) (hx : specialValueMk M x ≠ 0) :
    repellingPlus M hM (specialValueMk M x) = repellingRaw M x ∧
      repellingMinus M hM (specialValueMk M x) = repellingRaw M x := by
  have hxM : x ∉ specialValueLattice M := by
    intro hxM
    exact hx ((QuotientAddGroup.eq_zero_iff x).mpr hxM)
  simpa only [repellingPlusLift, repellingMinusLift, if_neg hxM] using
    repellingValues_mk M hM x

/--
Quotient-level plus bridge, pointwise for every class, with the same μ.
[RW26, p. 6, p. 3] (μ definition).
-/
theorem repellingPlus_reflection (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    repellingPlus M hM x =
      specialValuePlus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M x) := by
  refine Quotient.inductionOn x fun y => ?_
  change repellingPlus M hM (specialValueMk M y) =
    specialValuePlus (modularInverseReflection M) (reflection_admissible M hM)
      (reflectionEquiv M (specialValueMk M y))
  rw [(repellingValues_mk M hM y).1, reflectionEquiv_mk, specialValuePlus_mk]
  exact (repellingValues_lift_reflection M hM y).1

/--
Quotient-level minus bridge, including its own inverse origin constant; [RW26, p. 6, p. 3].
Neither bridge interchanges the plus and minus branches.
-/
theorem repellingMinus_reflection (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    repellingMinus M hM x =
      specialValueMinus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M x) := by
  refine Quotient.inductionOn x fun y => ?_
  change repellingMinus M hM (specialValueMk M y) =
    specialValueMinus (modularInverseReflection M) (reflection_admissible M hM)
      (reflectionEquiv M (specialValueMk M y))
  rw [(repellingValues_mk M hM y).2, reflectionEquiv_mk, specialValueMinus_mk]
  exact (repellingValues_lift_reflection M hM y).2

/--
The statement applies to an arbitrary attracting matrix. The transformed
matrix is used at its REPelling root; no positivity of 1-ε_attract is claimed. [RW26, p. 13].
-/
theorem attractingValues_from_repelling (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : SpecialValueGroup M) :
    specialValuePlus M hM x =
      repellingPlus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M x) ∧
      specialValueMinus M hM x =
        repellingMinus (modularInverseReflection M) (reflection_admissible M hM)
          (reflectionEquiv M x) := by
  refine Quotient.inductionOn x fun y => ?_
  change specialValuePlus M hM (specialValueMk M y) =
      repellingPlus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M (specialValueMk M y)) ∧
    specialValueMinus M hM (specialValueMk M y) =
      repellingMinus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M (specialValueMk M y))
  rw [specialValuePlus_mk, specialValueMinus_mk, reflectionEquiv_mk,
    (repellingValues_mk _ (reflection_admissible M hM) (y.1, -y.2)).1,
    (repellingValues_mk _ (reflection_admissible M hM) (y.1, -y.2)).2]
  have h := repellingValues_lift_reflection (modularInverseReflection M)
    (reflection_admissible M hM) (y.1, -y.2)
  simpa only [reflection_involutive, neg_neg] using And.intro h.1.symm h.2.symm

/--
Auxiliary nonvanishing is inherited through the actual bridge; it is not postulated as a property of
a chosen function; [RW26, p. 6, p. 12].
-/
theorem repellingValues_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    repellingPlus M hM x ≠ 0 ∧ repellingMinus M hM x ≠ 0 := by
  rw [repellingPlus_reflection, repellingMinus_reflection]
  exact ⟨specialValuePlus_ne_zero _ _ _, specialValueMinus_ne_zero _ _ _⟩

/--
The existing footnote-2 property transported to the auxiliary pair; [RW26, p. 3, footnote 2].
The two separately normalized origins are excluded.
-/
theorem repellingValues_agree_off_zero (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (x : SpecialValueGroup M) (hx : x ≠ 0) :
    repellingPlus M hM x = repellingMinus M hM x := by
  rw [repellingPlus_reflection, repellingMinus_reflection]
  apply specialValue_agree_off_zero
  exact fun h => hx ((reflectionEquiv M).injective (h.trans (map_zero _).symm))

/--
Full Fourier summand and normalization transport by the explicit
quotient equivalence, valid also at u=0; [RW26, p. 3, (3), (6)].
This equality of sums does not assert the Fourier identity.
-/
theorem repelling_fourierSum_reflection (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : SpecialValueGroup M) :
    normalizedValueSum M hM
      (fun x => specialValuePairing M hM x u * repellingPlus M hM x) =
    normalizedValueSum (modularInverseReflection M) (reflection_admissible M hM)
      (fun x => specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
        x (reflectionEquiv M u) *
          specialValuePlus (modularInverseReflection M) (reflection_admissible M hM) x) := by
  unfold normalizedValueSum
  rw [reflection_order]
  congr 1
  apply G2SpecialValueBridgeAux.sum_reflection M hM
  intro x
  rw [reflection_pairing, repellingPlus_reflection]

/--
Full ratio summand transport, including x+v and all zero cases; [RW26, p. 3, (3), (7)].
No assumption v≠0 or (u,v)≠(0,0) is needed for reindexing.
-/
theorem repelling_ratioSum_reflection (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u v : SpecialValueGroup M) :
    normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
      (repellingPlus M hM x / repellingMinus M hM (x + v))) =
    normalizedValueSum (modularInverseReflection M) (reflection_admissible M hM)
      (fun x => specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
        x (reflectionEquiv M u) *
          (specialValuePlus (modularInverseReflection M) (reflection_admissible M hM) x /
            specialValueMinus (modularInverseReflection M) (reflection_admissible M hM)
              (x + reflectionEquiv M v))) := by
  unfold normalizedValueSum
  rw [reflection_order]
  congr 1
  apply G2SpecialValueBridgeAux.sum_reflection M hM
  intro x
  rw [reflection_pairing, repellingPlus_reflection, repellingMinus_reflection, map_add]

/--
The Fourier constant is the same actual etaMultiplier M for all u, by exact equality.
[RW26, p. 3, (6)].
-/
theorem attracting_fourier_iff_repelling (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) :
    (∀ u : SpecialValueGroup M,
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
        specialValuePlus M hM x) = etaMultiplier M / specialValueMinus M hM u) ↔
    (∀ u : SpecialValueGroup (modularInverseReflection M),
      normalizedValueSum (modularInverseReflection M) (reflection_admissible M hM)
        (fun x => specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
          x u * repellingPlus (modularInverseReflection M) (reflection_admissible M hM) x) =
        etaMultiplier (modularInverseReflection M) /
          repellingMinus (modularInverseReflection M) (reflection_admissible M hM) u) := by
  have hplus (x : SpecialValueGroup M) :
      repellingPlus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M x) = specialValuePlus M hM x :=
    (attractingValues_from_repelling M hM x).1.symm
  have hminus (x : SpecialValueGroup M) :
      repellingMinus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M x) = specialValueMinus M hM x :=
    (attractingValues_from_repelling M hM x).2.symm
  have hsum (u : SpecialValueGroup M) :
      normalizedValueSum (modularInverseReflection M) (reflection_admissible M hM)
        (fun x => specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
          x (reflectionEquiv M u) *
            repellingPlus (modularInverseReflection M) (reflection_admissible M hM) x) =
        normalizedValueSum M hM
          (fun x => specialValuePairing M hM x u * specialValuePlus M hM x) := by
    unfold normalizedValueSum
    rw [reflection_order]
    congr 1
    symm
    apply G2SpecialValueBridgeAux.sum_reflection M hM
    intro x
    rw [reflection_pairing, hplus]
  constructor
  · intro h u
    obtain ⟨x, rfl⟩ := (reflectionEquiv M).surjective u
    rw [hsum, hminus, etaMultiplier_inverse_reflection M hM.1]
    exact h x
  · intro h u
    have hu := h (reflectionEquiv M u)
    rw [hsum, hminus, etaMultiplier_inverse_reflection M hM.1] at hu
    exact hu

/--
Full all-parameter pentagon transport, including the origin term -N F+(0) at (0,0).
This is an equivalence of the two identities, not a proof of either. [RW26, p. 3, (7)].
-/
theorem attracting_pentagon_iff_repelling (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) :
    (∀ u v : SpecialValueGroup M,
      normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
        (specialValuePlus M hM x / specialValueMinus M hM (x + v))) =
      specialValuePlus M hM (u + v) / (specialValueMinus M hM u * specialValueMinus M hM v) -
        (if u = 0 ∧ v = 0 then (specialValueOrder M : ℂ) * specialValuePlus M hM 0 else 0)) ↔
    (∀ u v : SpecialValueGroup (modularInverseReflection M),
      normalizedValueSum (modularInverseReflection M) (reflection_admissible M hM)
        (fun x => specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
          x u * (repellingPlus (modularInverseReflection M) (reflection_admissible M hM) x /
            repellingMinus (modularInverseReflection M) (reflection_admissible M hM) (x + v))) =
      repellingPlus (modularInverseReflection M) (reflection_admissible M hM) (u + v) /
        (repellingMinus (modularInverseReflection M) (reflection_admissible M hM) u *
          repellingMinus (modularInverseReflection M) (reflection_admissible M hM) v) -
        (if u = 0 ∧ v = 0 then (specialValueOrder (modularInverseReflection M) : ℂ) *
          repellingPlus (modularInverseReflection M) (reflection_admissible M hM) 0 else 0)) := by
  have hplus (x : SpecialValueGroup M) :
      repellingPlus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M x) = specialValuePlus M hM x :=
    (attractingValues_from_repelling M hM x).1.symm
  have hminus (x : SpecialValueGroup M) :
      repellingMinus (modularInverseReflection M) (reflection_admissible M hM)
        (reflectionEquiv M x) = specialValueMinus M hM x :=
    (attractingValues_from_repelling M hM x).2.symm
  have hplus0 : repellingPlus (modularInverseReflection M) (reflection_admissible M hM) 0 =
      specialValuePlus M hM 0 := by
    simpa only [map_zero] using hplus 0
  have hzero (x : SpecialValueGroup M) : reflectionEquiv M x = 0 ↔ x = 0 := by
    constructor
    · intro hx
      exact (reflectionEquiv M).injective (hx.trans (map_zero _).symm)
    · rintro rfl
      exact map_zero _
  have hsum (u v : SpecialValueGroup M) :
      normalizedValueSum (modularInverseReflection M) (reflection_admissible M hM)
        (fun x => specialValuePairing (modularInverseReflection M) (reflection_admissible M hM)
          x (reflectionEquiv M u) *
            (repellingPlus (modularInverseReflection M) (reflection_admissible M hM) x /
              repellingMinus (modularInverseReflection M) (reflection_admissible M hM)
                (x + reflectionEquiv M v))) =
        normalizedValueSum M hM (fun x => specialValuePairing M hM x u *
          (specialValuePlus M hM x / specialValueMinus M hM (x + v))) := by
    unfold normalizedValueSum
    rw [reflection_order]
    congr 1
    symm
    apply G2SpecialValueBridgeAux.sum_reflection M hM
    intro x
    rw [reflection_pairing, hplus, ← map_add (reflectionEquiv M), hminus]
  constructor
  · intro h u v
    obtain ⟨x, rfl⟩ := (reflectionEquiv M).surjective u
    obtain ⟨y, rfl⟩ := (reflectionEquiv M).surjective v
    simpa only [hsum, ← map_add (reflectionEquiv M), hplus, hminus, hzero,
      reflection_order, hplus0] using h x y
  · intro h u v
    have huv := h (reflectionEquiv M u) (reflectionEquiv M v)
    simpa only [hsum, ← map_add (reflectionEquiv M), hplus, hminus, hzero,
      reflection_order, hplus0] using huv

#check @specialValueGroup_finite
#check @Fintype.ofFinite
#check @Equiv.sum_comp
#check @specialValue_mixed_reflection
#check @etaMultiplier_inverse_reflection
#print repellingPlusLift
#print repellingMinusLift
#print repellingPlus
#print repellingMinus
#print normalizedValueSum
#check attractingValues_from_repelling
#check attracting_fourier_iff_repelling
#check attracting_pentagon_iff_repelling

end SICLean.L4.G2.SpecialValueBridge
