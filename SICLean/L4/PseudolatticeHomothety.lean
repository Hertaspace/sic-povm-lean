import SICLean.L4.PseudolatticeValues
import SICLean.L4.PseudolatticeHomothetyAux

set_option autoImplicit false

/-!
# The explicit K-homothety on quotient groups

The quotient equivalence has prescribed maps x |-> lambda*x and
y |-> lambda^-1*y. Its proof fields
only justify membership, descent, additivity and inverse identities.
Value invariance is a separate theorem. In finite-family normalization
I=lambda*J, distributionTransport goes from G_I to G_J, by lambda^-1.

[RW26, p. 2, p. 3, (2)] row quotient; [RW26, p. 20] lattice dictionary. These are bridges,
not a finiteness claim for arbitrary independently real-scaled bases.
-/

noncomputable section

namespace SICLean.L3.M72

universe u
variable {K : Type u} [Field K] [NumberField K]

open L4.PseudolatticeHomothetyAux (scale_mem inverse_mem embedding_mul embedding_inverse_mul)

/--
Arithmetic period points scale in K. [RW26, p. 20] lattice dictionary.
-/
theorem scaledPoint_mem (P : PeriodData K) (I J : StablePseudolattice P)
    (lam : K) (hlam : lam ≠ 0) (hJ : J.val = pseudolatticeScale lam I.val)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    lam * x ∈ pseudolatticePeriodPoints P J := by
  change (P.epsilon⁻¹ - 1) * (lam * x) ∈ J.val
  have h := scale_mem I.val J.val lam hJ ((P.epsilon⁻¹ - 1) * x) hx
  convert h using 1
  ring

/--
Inverse direction for normalization. [RW26, p. 20] dictionary.
-/
theorem inversePoint_mem (P : PeriodData K) (I J : StablePseudolattice P)
    (lam : K) (hlam : lam ≠ 0) (hJ : J.val = pseudolatticeScale lam I.val)
    (y : K) (hy : y ∈ pseudolatticePeriodPoints P J) :
    lam⁻¹ * y ∈ pseudolatticePeriodPoints P I := by
  change (P.epsilon⁻¹ - 1) * (lam⁻¹ * y) ∈ I.val
  have h := inverse_mem I.val J.val lam hlam hJ ((P.epsilon⁻¹ - 1) * y) hy
  convert h using 1
  ring

def scaleEquiv (P : PeriodData K) (I J : StablePseudolattice P)
    (lam : K) (hlam : lam ≠ 0) (hJ : J.val = pseudolatticeScale lam I.val) :
    PseudolatticeGroup P I ≃+ PseudolatticeGroup P J where
  toFun := Quotient.lift
    (fun x : pseudolatticePeriodPoints P I =>
      pseudolatticeMk P J (lam * x.val) (scaledPoint_mem P I J lam hlam hJ x.val x.property))
    (by
      intro x y hxy
      apply (L4.PseudolatticeHomothetyAux.mk_eq_iff P J _ _ _ _).mpr
      rw [← mul_sub]
      exact scale_mem I.val J.val lam hJ _
        ((L4.PseudolatticeHomothetyAux.mk_eq_iff P I _ _ _ _).mp
          (Quotient.sound hxy)))
  invFun := Quotient.lift
    (fun y : pseudolatticePeriodPoints P J =>
      pseudolatticeMk P I (lam⁻¹ * y.val)
        (inversePoint_mem P I J lam hlam hJ y.val y.property)) (by
      intro x y hxy
      apply (L4.PseudolatticeHomothetyAux.mk_eq_iff P I _ _ _ _).mpr
      rw [← mul_sub]
      exact inverse_mem I.val J.val lam hlam hJ _
        ((L4.PseudolatticeHomothetyAux.mk_eq_iff P J _ _ _ _).mp
          (Quotient.sound hxy)))
  left_inv := by
    intro g
    refine Quotient.inductionOn g ?_
    intro x
    change pseudolatticeMk P I (lam⁻¹ * (lam * x.val)) _ =
      pseudolatticeMk P I x.val x.property
    apply (L4.PseudolatticeHomothetyAux.mk_eq_iff P I _ _ _ _).mpr
    simp [hlam]
  right_inv := by
    intro g
    refine Quotient.inductionOn g ?_
    intro y
    change pseudolatticeMk P J (lam * (lam⁻¹ * y.val)) _ =
      pseudolatticeMk P J y.val y.property
    apply (L4.PseudolatticeHomothetyAux.mk_eq_iff P J _ _ _ _).mpr
    simp [hlam]
  map_add' := by
    intro g h
    refine Quotient.inductionOn₂ g h ?_
    intro x y
    change pseudolatticeMk P J (lam * (x.val + y.val)) _ =
      pseudolatticeMk P J (lam * x.val + lam * y.val) _
    apply (L4.PseudolatticeHomothetyAux.mk_eq_iff P J _ _ _ _).mpr
    simp [mul_add]

/--
The defining representative formula. [RW26, p. 3] quotient.
-/
theorem scaleEquiv_mk (P : PeriodData K) (I J : StablePseudolattice P)
    (lam : K) (hlam : lam ≠ 0) (hJ : J.val = pseudolatticeScale lam I.val)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    scaleEquiv P I J lam hlam hJ (pseudolatticeMk P I x hx) =
      pseudolatticeMk P J (lam * x) (scaledPoint_mem P I J lam hlam hJ x hx) := by
  rfl

/--
The inverse is multiplication by lambda^-1; [RW26, p. 20] dictionary.
-/
theorem scaleEquiv_symm_mk (P : PeriodData K) (I J : StablePseudolattice P)
    (lam : K) (hlam : lam ≠ 0) (hJ : J.val = pseudolatticeScale lam I.val)
    (y : K) (hy : y ∈ pseudolatticePeriodPoints P J) :
    (scaleEquiv P I J lam hlam hJ).symm (pseudolatticeMk P J y hy) =
      pseudolatticeMk P I (lam⁻¹ * y) (inversePoint_mem P I J lam hlam hJ y hy) := by
  rfl

/--
Both real scales come from this one K-element. [RW26, p. 20] dictionary.
-/
theorem scale_presentation (P : PeriodData K) (I J : StablePseudolattice P)
    (B : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (lam : K) (hlam : TotallyPositive P lam)
    (hJ : J.val = pseudolatticeScale lam I.val) :
    PseudolatticePresentation P J (L4.distributionScale B (pseudolatticeScales P lam)) := by
  obtain ⟨hvalid, hperiod, hlattice⟩ :=
    L4.distributionScale_valid B hB.1 (pseudolatticeScales P lam) hlam
  refine ⟨hvalid, hperiod.trans hB.2.1, ?_⟩
  rw [hlattice, hB.2.2, hJ, pseudolatticeEmbeddingImage_scale]

/--
Literal E_(lambda I)(lambda x)=E_I(x), including lattice points.
[RW26, p. 2, (2)].
-/
theorem basisValue_scale (P : PeriodData K) (I J : StablePseudolattice P)
    (B C : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (hC : PseudolatticePresentation P J C) (lam : K) (hlam : TotallyPositive P lam)
    (hJ : J.val = pseudolatticeScale lam I.val)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    basisValue P C (lam * x) = basisValue P B x := by
  have hs := scale_presentation P I J B hB lam hlam hJ
  calc
    basisValue P C (lam * x) =
        basisValue P (L4.distributionScale B (pseudolatticeScales P lam)) (lam * x) :=
      presentation_value P J _ C hs hC _
        (scaledPoint_mem P I J lam (totallyPositive_ne_zero P lam hlam) hJ x hx)
    _ = basisValue P B x := by
      unfold basisValue
      rw [embedding_mul]
      exact L4.distributionBasisValue_scale B hB.1 (pseudolatticeScales P lam) hlam _
        (pseudolatticePresentation_point_mem P I B hB x hx)

/--
Full quotient-level homothety invariance. [RW26, p. 2, (2)].
-/
theorem value_scale (P : PeriodData K) (I J : StablePseudolattice P)
    (lam : K) (hlam : TotallyPositive P lam)
    (hJ : J.val = pseudolatticeScale lam I.val) (g : PseudolatticeGroup P I) :
    value P J (scaleEquiv P I J lam (totallyPositive_ne_zero P lam hlam) hJ g) =
      value P I g := by
  refine Quotient.inductionOn g ?_
  intro x
  change value P J (scaleEquiv P I J lam (totallyPositive_ne_zero P lam hlam) hJ
    (pseudolatticeMk P I x.val x.property)) = value P I (pseudolatticeMk P I x.val x.property)
  rw [scaleEquiv_mk, value_mk P J (chosenBasis P J) (chosenBasis_spec P J),
    value_mk P I (chosenBasis P I) (chosenBasis_spec P I)]
  exact basisValue_scale P I J _ _ (chosenBasis_spec P I) (chosenBasis_spec P J)
    lam hlam hJ x.val x.property

/--
Minus origin stays the inverse positive root, never an inverse of
all E values; [RW26, p. 3, footnote 2].
-/
theorem minusValue_scale (P : PeriodData K) (I J : StablePseudolattice P)
    (lam : K) (hlam : TotallyPositive P lam)
    (hJ : J.val = pseudolatticeScale lam I.val) (g : PseudolatticeGroup P I) :
    minusValue P J (scaleEquiv P I J lam (totallyPositive_ne_zero P lam hlam) hJ g) =
      minusValue P I g := by
  classical
  have hz : scaleEquiv P I J lam (totallyPositive_ne_zero P lam hlam) hJ g = 0 ↔ g = 0 :=
    (scaleEquiv P I J lam (totallyPositive_ne_zero P lam hlam) hJ).map_eq_zero_iff
  simp only [minusValue, hz, value_scale P I J lam hlam hJ]

/--
Same actual eta multiplier after positive homothety and rebase.
[RW26, p. 3, p. 6, (17)].
-/
theorem multiplier_scale (P : PeriodData K) (I J : StablePseudolattice P)
    (B C : L4.DistributionBasis) (hB : PseudolatticePresentation P I B)
    (hC : PseudolatticePresentation P J C) (lam : K) (hlam : TotallyPositive P lam)
    (hJ : J.val = pseudolatticeScale lam I.val) :
    L4.etaMultiplier C.matrix = L4.etaMultiplier B.matrix := by
  have hs := scale_presentation P I J B hB lam hlam hJ
  exact presentation_multiplier P J (L4.distributionScale B (pseudolatticeScales P lam)) C hs hC

def distributionTransport (P : PeriodData K) (I J : StablePseudolattice P)
    (C : L4.DistributionBasis) (hC : PseudolatticePresentation P J C)
    (lam : K) (hlam : TotallyPositive P lam)
    (hI : I.val = pseudolatticeScale lam J.val) :
    PseudolatticeGroup P I ≃+ L4.DistributionGroup C :=
  (scaleEquiv P J I lam (totallyPositive_ne_zero P lam hlam) hI).symm.trans
    (pseudolatticeGroupEquiv P J C hC)

/--
Explicit all-lifts normalization formula; [RW26, p. 20] dictionary.
-/
theorem distributionTransport_mk (P : PeriodData K) (I J : StablePseudolattice P)
    (C : L4.DistributionBasis) (hC : PseudolatticePresentation P J C)
    (lam : K) (hlam : TotallyPositive P lam)
    (hI : I.val = pseudolatticeScale lam J.val)
    (x : K) (hx : x ∈ pseudolatticePeriodPoints P I) :
    distributionTransport P I J C hC lam hlam hI (pseudolatticeMk P I x hx) =
      L4.distributionMk C (pseudolatticeEmbedding P (lam⁻¹ * x))
        (pseudolatticePresentation_point_mem P J C hC _
          (inversePoint_mem P J I lam (totallyPositive_ne_zero P lam hlam) hI x hx)) := by
  change pseudolatticeGroupEquiv P J C hC
    ((scaleEquiv P J I lam (totallyPositive_ne_zero P lam hlam) hI).symm
      (pseudolatticeMk P I x hx)) = _
  rw [scaleEquiv_symm_mk, pseudolatticeGroupEquiv_mk]

/--
Same actual complex number on either quotient. [RW26, p. 2, (2)].
-/
theorem distributionTransport_value (P : PeriodData K) (I J : StablePseudolattice P)
    (C : L4.DistributionBasis) (hC : PseudolatticePresentation P J C)
    (lam : K) (hlam : TotallyPositive P lam)
    (hI : I.val = pseudolatticeScale lam J.val) (g : PseudolatticeGroup P I) :
    L4.distributionValue C (distributionTransport P I J C hC lam hlam hI g) =
      value P I g := by
  let e := scaleEquiv P J I lam (totallyPositive_ne_zero P lam hlam) hI
  change L4.distributionValue C (pseudolatticeGroupEquiv P J C hC (e.symm g)) = _
  rw [← value_eq_distribution P J C hC]
  exact (value_scale P J I lam hlam hI (e.symm g)).symm.trans
    (congrArg (value P I) (e.apply_symm_apply g))

/--
Agreement with inverse-scale map, including its
Quotient.out choice; [RW26, p. 14, Prop. 9].
-/
theorem distributionTransport_eq_scaledProject (P : PeriodData K)
    (I J : StablePseudolattice P) (B C : L4.DistributionBasis)
    (hB : PseudolatticePresentation P I B) (hC : PseudolatticePresentation P J C)
    (lam : K) (hlam : TotallyPositive P lam)
    (hI : I.val = pseudolatticeScale lam J.val)
    (hP : L4.distributionPeriodPoints B ≤ (L4.distributionPeriodPoints C).comap
      (L4.distributionHomothety
        ((pseudolatticeScales P lam).1⁻¹, (pseudolatticeScales P lam).2⁻¹)))
    (g : L4.DistributionGroup B) :
    distributionTransport P I J C hC lam hlam hI
        ((pseudolatticeGroupEquiv P I B hB).symm g) =
      L4.distributionScaledProject B C (pseudolatticeScales P lam) hP g := by
  obtain ⟨x, hx⟩ := (pseudolatticeGroupEquiv P I B hB).surjective g
  subst g
  refine Quotient.inductionOn x ?_
  intro x
  change distributionTransport P I J C hC lam hlam hI
    ((pseudolatticeGroupEquiv P I B hB).symm
      (pseudolatticeGroupEquiv P I B hB (pseudolatticeMk P I x.val x.property))) =
    L4.distributionScaledProject B C (pseudolatticeScales P lam) hP
      (pseudolatticeGroupEquiv P I B hB (pseudolatticeMk P I x.val x.property))
  rw [AddEquiv.symm_apply_apply, distributionTransport_mk, pseudolatticeGroupEquiv_mk]
  have hs := scale_presentation P J I C hC lam hlam hI
  have hle : L4.distributionLattice B ≤
      L4.distributionLattice (L4.distributionScale C (pseudolatticeScales P lam)) := by
    rw [hB.2.2, hs.2.2]
  rw [L4.distributionScaledProject_mk B C hB.1 hC.1 (pseudolatticeScales P lam) hlam hP hle]
  simp only [embedding_inverse_mul]

#check @Quotient.lift
#print scaleEquiv
#print distributionTransport
#check distributionTransport_mk
#check distributionTransport_eq_scaledProject

end SICLean.L3.M72
