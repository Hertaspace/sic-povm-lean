import SICLean.L5.SplitPrimeGeometry
import SICLean.L5.SplitUniformDirection
import SICLean.L5.LocalActualFourier
import SICLean.L5.ActualOriginal
import SICLean.L5.SplitPrimeValuesAux

set_option autoImplicit false

/-!
# Actual values and the two Fourier calls

[RW-rec, Thm. 7] [RW-rec, pp. 11--12]. [RW-rec, Def. 1, Prop. 2, p. 3, p. 4]; [RW26,
Prop. 8, p. 2, p. 3, p. 14, p. 20, (2), (4), (37), footnote 2]. [RW26, p. 3, p. 18, (6),
(36)]. Adapters below reuse the actual chosen basis, row equivalence, Qbar lifts, and
positive square root from existing modules. No new analytic E, germ, modularPhi,
phiExtended, etaMultiplier, or root branch is introduced. Public Theorem 7 has no E-unit
hypothesis: its proof consumes the odd-prime conclusion of Theorem 5. The conditional
Fourier lemmas merely expose that proof dependency; they do not redefine Theorem 5 as an
assumption.
-/

noncomputable section
open scoped NumberField MatrixGroups BigOperators Classical

namespace SICLean.L5.SplitPrimeValues

open L3 SplitPrimeLattice SplitPrimeGeometry LocalFourierSetup DistributionOrbitGeometry

variable {K : Type} [Field K] [NumberField K]

/-- Existing arithmetic-to-row label maps composed in their actual order. -/
def matrixLabels (P : PeriodData K) (I : StablePseudolattice P) :
    PseudolatticeGroup P I ≃+ L4.SpecialValueGroup (M72.chosenBasis P I).matrix :=
  (pseudolatticeGroupEquiv P I (M72.chosenBasis P I) (M72.chosenBasis_spec P I)).trans
    (M72.rowEquiv (M72.chosenBasis P I) (M72.chosenBasis_spec P I).1).symm

/-- The already defined algebraic matrix value, transported by those labels. -/
def valueLift (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) : Galois.Qbar :=
  FiniteAlgebraicTransport.value (M72.chosenBasis P I).matrix
    (M72.basis_parameters _ (M72.chosenBasis_spec P I).1).1 (matrixLabels P I x)

/-- Normalization in Qbar by the actual origin; complex normalization remains the existing
DistributionNormalized.normalizedValue. -/
def normalizedLift (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) : Galois.Qbar :=
  valueLift P I x / valueLift P I 0

def pairing (P : PeriodData K) (I : StablePseudolattice P)
    (x y : PseudolatticeGroup P I) : Galois.Qbar :=
  FiniteAlgebraicTransport.pairing (M72.chosenBasis P I).matrix
    (M72.basis_parameters _ (M72.chosenBasis_spec P I).1).1
    (matrixLabels P I x) (matrixLabels P I y)

def sqrtOrder (P : PeriodData K) (I : StablePseudolattice P) : Galois.Qbar :=
  FiniteAlgebraicTransport.sqrtOrder (M72.chosenBasis P I).matrix
    (M72.basis_parameters _ (M72.chosenBasis_spec P I).1).1

/-- Recovery of exactly the actual point value, including zero. -/
theorem embed_valueLift (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) : Galois.embed (valueLift P I x) = M72.value P I x := by
  rw [valueLift, FiniteAlgebraicTransport.embed_value,
    M72.value_eq_distribution P I _ (M72.chosenBasis_spec P I)]
  exact (M72.distributionPlus_eq_specialPlus _ (M72.chosenBasis_spec P I).1
    (matrixLabels P I x)).symm.trans (congrArg _ (by
      simp only [matrixLabels, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]))

/-- Actual-field bridge: no independent choice of algebraic solution. -/
theorem actual_valueLift (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : ActualLattice.Group M hM) :
    valueLift (ActualField.periodData M hM) (ActualLattice.stableLattice M hM) x =
      ActualValues.valueLift M hM x := by
  apply Galois.embed.injective
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [embed_valueLift, ActualValues.embed_valueLift]
  rfl

/-- [RW-rec]: every lattice at the same period has the same nonzero origin. It is sqrt(epsilon), not
epsilon. -/
theorem valueLift_origins (P : PeriodData K) (I J : StablePseudolattice P) :
    valueLift P I 0 = valueLift P J 0 ∧ valueLift P I 0 ≠ 0 ∧
      Galois.embed (valueLift P I 0) = PeriodPower.root P := by
  refine ⟨Galois.embed.injective ?_, ?_, ?_⟩
  · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      embed_valueLift, M72.value_zero]
  · intro hz
    have he := congrArg Galois.embed hz
    rw [embed_valueLift, map_zero] at he
    exact M72.value_ne_zero P I 0 he
  · exact (embed_valueLift P I 0).trans (M72.value_zero P I)

/-- Existing complex normalization is recovered literally. -/
theorem embed_normalizedLift (P : PeriodData K) (I : StablePseudolattice P)
    (x : PseudolatticeGroup P I) :
    Galois.embed (normalizedLift P I x) = DistributionNormalized.normalizedValue P I x := by
  simp only [normalizedLift, map_div₀, embed_valueLift,
    M72.value_zero, DistributionNormalized.normalizedValue]

/-- [RW-rec]: zero is always retained and normalizes to one. -/
theorem normalizedLift_zero (P : PeriodData K) (I : StablePseudolattice P) :
    normalizedLift P I 0 = 1 := by
  exact div_self (valueLift_origins P I I).2.1

/-- [RW-rec, (8)]; [RW26, p. 14]. The old label is sent by the existing periodPowerInclusion, not by
an arbitrary equal-cardinality map. -/
theorem valueLift_power (P : PeriodData K) (I : StablePseudolattice P)
    (d : ℕ) (hd : 0 < d) (x : PseudolatticeGroup P I) :
    valueLift (PeriodPower.powPeriod P d hd) (PeriodPower.powLattice P I d hd)
      (PeriodPower.periodPowerInclusion P I d hd x) = valueLift P I x ^ d := by
  apply Galois.embed.injective
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [embed_valueLift, map_pow, embed_valueLift]
  exact PeriodPower.value_pow P I d hd x

/-- [RW-rec]: the origin is raised to the same power. -/
theorem normalizedLift_power (P : PeriodData K) (I : StablePseudolattice P)
    (d : ℕ) (hd : 0 < d) (x : PseudolatticeGroup P I) :
    normalizedLift (PeriodPower.powPeriod P d hd) (PeriodPower.powLattice P I d hd)
      (PeriodPower.periodPowerInclusion P I d hd x) = normalizedLift P I x ^ d := by
  unfold normalizedLift
  rw [valueLift_power, ← map_zero (PeriodPower.periodPowerInclusion P I d hd),
    valueLift_power, div_pow]

/-- Transports the existing pairing and positive normalization. -/
theorem spectral_transport (P : PeriodData K) (I : StablePseudolattice P) :
    IsBicharacter (pairing P I) ∧ Nondegenerate (pairing P I) ∧
      sqrtOrder P I ^ 2 = (Fintype.card (PseudolatticeGroup P I) : Galois.Qbar) := by
  let M := (M72.chosenBasis P I).matrix
  let hM := (M72.basis_parameters _ (M72.chosenBasis_spec P I).1).1
  let e := matrixLabels P I
  letI : Finite (L4.SpecialValueGroup M) := L4.specialValueGroup_finite M hM
  letI : Fintype (L4.SpecialValueGroup M) := Fintype.ofFinite _
  have hB := LocalActualFourier.actual_isBicharacter M hM
  have hn := LocalActualFourier.actual_nondegenerate M hM
  refine ⟨⟨fun x y => hB.1 (e x) (e y), ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro x x' y
    change FiniteAlgebraicTransport.pairing M hM (e (x + x')) (e y) = _
    rw [map_add]
    exact hB.2.1 _ _ _
  · intro x y y'
    change FiniteAlgebraicTransport.pairing M hM (e x) (e (y + y')) = _
    rw [map_add]
    exact hB.2.2 _ _ _
  · intro x hx
    apply e.injective
    rw [map_zero]
    exact hn.1 _ (fun y => by
      obtain ⟨y, rfl⟩ := e.surjective y
      exact hx y)
  · intro y hy
    apply e.injective
    rw [map_zero]
    exact hn.2 _ (fun x => by
      obtain ⟨x, rfl⟩ := e.surjective x
      exact hy x)
  · change FiniteAlgebraicTransport.sqrtOrder M hM ^ 2 = _
    rw [LocalActualFourier.actual_normalization_sq M hM,
      Fintype.card_congr e.toEquiv]

/-- [RW-rec]: the two Fourier transforms of E and E inverse. -/
theorem value_fouriers_integral (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hu : UnitValued v (valueLift P I)) :
    Integral v (fourier (pairing P I) (sqrtOrder P I) (valueLift P I)) ∧
      Integral v (fourier (pairing P I) (sqrtOrder P I) (fun x => (valueLift P I x)⁻¹)) := by
  let M := (M72.chosenBasis P I).matrix
  let hM := (M72.basis_parameters _ (M72.chosenBasis_spec P I).1).1
  let e := matrixLabels P I
  letI : Finite (L4.SpecialValueGroup M) := L4.specialValueGroup_finite M hM
  letI : Fintype (L4.SpecialValueGroup M) := Fintype.ofFinite _
  have hf : Integral v (FiniteAlgebraicTransport.value M hM) := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact le_of_eq (hu x).symm
  constructor
  · intro y
    change 0 ≤ v (fourier (fun x y => FiniteAlgebraicTransport.pairing M hM (e x) (e y))
      (FiniteAlgebraicTransport.sqrtOrder M hM)
      (fun x => FiniteAlgebraicTransport.value M hM (e x)) y)
    rw [SplitPrimeValuesAux.fourier_comp, LocalActualFourier.generic_fourier_eq]
    exact LocalActualFourier.actual_fourier_integral M hM v hf (e y)
  · intro y
    change 0 ≤ v (fourier (fun x y => FiniteAlgebraicTransport.pairing M hM (e x) (e y))
      (FiniteAlgebraicTransport.sqrtOrder M hM)
      (fun x => (FiniteAlgebraicTransport.value M hM (e x))⁻¹) y)
    rw [SplitPrimeValuesAux.fourier_comp e (FiniteAlgebraicTransport.pairing M hM) _
      (fun x => (FiniteAlgebraicTransport.value M hM x)⁻¹) y,
      LocalActualFourier.generic_fourier_eq]
    exact LocalActualFourier.actual_inverse_fourier_integral M hM v hf (e y)

/-- [RW-rec]: integrality for the literal R_h and its inverse. -/
theorem ratio_fouriers_integral (P : PeriodData K) (I : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hu : UnitValued v (valueLift P I))
    (h : PseudolatticeGroup P I) :
    Integral v (fourier (pairing P I) (sqrtOrder P I)
      (LocalLemmaOne.translationRatio (valueLift P I) h)) ∧
      Integral v (fourier (pairing P I) (sqrtOrder P I)
        (fun x => (LocalLemmaOne.translationRatio (valueLift P I) h x)⁻¹)) := by
  let M := (M72.chosenBasis P I).matrix
  let hM := (M72.basis_parameters _ (M72.chosenBasis_spec P I).1).1
  let e := matrixLabels P I
  letI : Finite (L4.SpecialValueGroup M) := L4.specialValueGroup_finite M hM
  letI : Fintype (L4.SpecialValueGroup M) := Fintype.ofFinite _
  have hum : UnitValued v (FiniteAlgebraicTransport.value M hM) := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact hu x
  have hratio : LocalLemmaOne.translationRatio (valueLift P I) h =
      fun x => FiniteAlgebraicTransport.ratio M hM (e h) (e x) := by
    funext x
    simp only [LocalLemmaOne.translationRatio, valueLift,
      FiniteAlgebraicTransport.ratio, map_add]
    rfl
  rw [hratio]
  have hi := LocalActualFourier.actual_ratio_fouriers_integral M hM v hum (e h)
  constructor
  · intro y
    change 0 ≤ v (fourier (fun x y => FiniteAlgebraicTransport.pairing M hM (e x) (e y))
      (FiniteAlgebraicTransport.sqrtOrder M hM)
      (fun x => FiniteAlgebraicTransport.ratio M hM (e h) (e x)) y)
    rw [SplitPrimeValuesAux.fourier_comp, LocalActualFourier.generic_fourier_eq]
    exact hi.1 (e y)
  · intro y
    change 0 ≤ v (fourier (fun x y => FiniteAlgebraicTransport.pairing M hM (e x) (e y))
      (FiniteAlgebraicTransport.sqrtOrder M hM)
      (fun x => (FiniteAlgebraicTransport.ratio M hM (e h) (e x))⁻¹) y)
    rw [SplitPrimeValuesAux.fourier_comp e (FiniteAlgebraicTransport.pairing M hM) _
      (fun x => (FiniteAlgebraicTransport.ratio M hM (e h) x)⁻¹) y,
      LocalActualFourier.generic_fourier_eq]
    exact hi.2 (e y)

/-- [RW-rec]: cyclicization + Theorem 4 + existing subgroup distribution. The proof uses the unit
values; this is not an extra unit axiom. -/
theorem noncharacteristic_product_invariant (P : PeriodData K) (I : StablePseudolattice P)
    {p s : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hs : 1 ≤ s)
    (hm : LocallyMaximal P I p) {r q : FinitePlace.Prime K}
    (h : IsSplitPair p r q) (hη : PeriodOneMod P p)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (C : AddSubgroup (PseudolatticeGroup P I)) (hC : Nat.Coprime p (Nat.card C))
    (e : (FiniteCosetMoments.Point p s 2 × C) ≃+ PseudolatticeGroup P I)
    (L : AddSubgroup (PseudolatticeGroup P I))
    (hL : SplitGroupRing.FullCyclicSummand p s L)
    (hr : L ⊓ LocalFourierSetup.pTorsion p ≠ periodLine P I r)
    (hq : L ⊓ LocalFourierSetup.pTorsion p ≠ periodLine P I q)
    (x u : PseudolatticeGroup P I) (hu : p • u = 0) :
    reduce v (∏ l : L, valueLift P I (x + u + l.val)) =
      reduce v (∏ l : L, valueLift P I (x + l.val)) := by
  have he (y : PseudolatticeGroup P I) : valueLift P I y = OddPrimeValues.lift P I y :=
    OddPrimeValues.lift_of_embed P I y _ (embed_valueLift P I y)
  simp_rw [he]
  exact SplitPrimeValuesAux.cyclic_subgroup_product P I hodd v hp L
    (noncharacteristic_cyclic P I hodd hs hm h hη C hC e L hL hr hq) x u hu

/-- [RW-rec]: Lemma 6 separates factors in split-axis coordinates, for every actual coset; no
direction has yet been selected. -/
theorem value_coset_factorization (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (c : SplitUniformDirection.Coordinates (G := PseudolatticeGroup P I) p)
    (hc1 : AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 1 0) = periodLine P I r)
    (hc2 : AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 0 1) = periodLine P I q) :
    ∀ x : PseudolatticeGroup P I, ∃ A D : ZMod p → Residue v, ∀ u w,
      reduce v (valueLift P I (x + SplitUniformDirection.coordinate c u w)) = A u * D w := by
  obtain ⟨s, C, hs, hC, ⟨e⟩⟩ := primary_decomposition P I (Fact.out : p.Prime) hm h hη
  letI : CharP (Residue v) p := residue_charP v hp
  have hu : UnitValued v (valueLift P I) := fun x =>
    OddPrimeSpecialization.odd_prime_any_preimage P I p hodd v hp x _
      (embed_valueLift P I x)
  have hn (x : PseudolatticeGroup P I) : reduce v (valueLift P I x) ≠ 0 :=
    (reduce_ne_zero_iff v _ (le_of_eq (hu x).symm)).mpr (hu x)
  let g : PseudolatticeGroup P I → (Residue v)ˣ :=
    fun x => Units.mk0 (reduce v (valueLift P I x)) (hn x)
  have hprod (L : AddSubgroup (PseudolatticeGroup P I))
      (hL : SplitGroupRing.FullCyclicSummand p s L)
      (hr : L ⊓ pTorsion p ≠ AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 1 0))
      (hq : L ⊓ pTorsion p ≠ AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 0 1))
      (x u : PseudolatticeGroup P I) (hpu : p • u = 0) :
      SplitGroupRing.cosetProduct g L (x + u) = SplitGroupRing.cosetProduct g L x := by
    apply Units.ext
    simp only [SplitGroupRing.cosetProduct, Units.coe_prod, g, Units.val_mk0]
    have hUniv : @Finset.univ L (Fintype.ofFinite L) = (Finset.univ : Finset L) := by
      ext l
      simp
    rw [hUniv]
    rw [← SplitPrimeValuesAux.reduce_prod_of_units v Finset.univ _ (fun l _ => hu _),
      ← SplitPrimeValuesAux.reduce_prod_of_units v Finset.univ _ (fun l _ => hu _)]
    exact noncharacteristic_product_invariant P I hodd hs hm h hη v hp C hC e L hL
      (by simpa only [hc1] using hr) (by simpa only [hc2] using hq) x u hpu
  have hmix := SplitPrimeValuesAux.mixed_of_primary_products hs hC e c g hprod
  have hfactor := SplitUniformDirection.factorization_of_mixed g c hmix
  intro x
  refine ⟨fun u => reduce v (valueLift P I (x + SplitUniformDirection.coordinate c u 0)),
    fun w => reduce v (valueLift P I (x + SplitUniformDirection.coordinate c 0 w)) /
      reduce v (valueLift P I x), ?_⟩
  intro u w
  simpa only [g, Units.val_mk0, Units.val_mul, Units.val_div_eq_div_val, mul_div_assoc] using
    congrArg Units.val (hfactor x u w)

/-- [RW-rec, Thm. 7]: the selected ideal is outside both universal quantifiers. In particular there
is no x≠0 restriction and no nonconstancy input. -/
theorem theorem7 (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1) :
    ∃ t : FinitePlace.Prime K, (t = r ∨ t = q) ∧
      ∀ (x : PseudolatticeGroup P I) (a : periodLine P I t),
        reduce v (valueLift P I (x + a.val)) = reduce v (valueLift P I x) := by
  obtain ⟨s, C, hs, hC, ⟨e⟩⟩ := primary_decomposition P I (Fact.out : p.Prime) hm h hη
  obtain ⟨c, hc1, hc2⟩ := exists_split_coordinates P I hm h hη
  change AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 1 0) = periodLine P I r at hc1
  change AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 0 1) = periodLine P I q at hc2
  have hu : UnitValued v (valueLift P I) := fun x =>
    OddPrimeSpecialization.odd_prime_any_preimage P I p hodd v hp x _
      (embed_valueLift P I x)
  have hspec := spectral_transport P I
  have hF := value_fouriers_integral P I v hu
  have hd := SplitUniformDirection.uniform_direction v hp hodd hs
    (by simpa only [Nat.card_eq_fintype_card] using hC) e
    (pairing P I) hspec.1 hspec.2.1 (sqrtOrder P I) hspec.2.2
    (valueLift P I) hu hF.1 hF.2
    (fun z => (ratio_fouriers_integral P I v hu z).1)
    (fun z => (ratio_fouriers_integral P I v hu z).2) c
    (value_coset_factorization P I hodd hm h hη v hp c hc1 hc2)
  rcases SplitUniformDirection.uniform_translation v (valueLift P I) c hd with hr | hq
  · refine ⟨r, Or.inl rfl, ?_⟩
    intro x a
    have ha : a.val ∈ AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 1 0) := by
      rw [hc1]
      exact a.property
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
    rw [← hn, ← SplitPrimeValuesAux.first_axis_multiple c n]
    exact hr x (n : ZMod p)
  · refine ⟨q, Or.inr rfl, ?_⟩
    intro x a
    have ha : a.val ∈ AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 0 1) := by
      rw [hc2]
      exact a.property
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
    rw [← hn, ← SplitPrimeValuesAux.second_axis_multiple c n]
    exact hq x (n : ZMod p)

/-- [RW-rec]: normalization preserves the same uniform direction. This is the translation interface
used in Theorem 8. -/
theorem theorem7_normalized (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1) :
    ∃ t : FinitePlace.Prime K, (t = r ∨ t = q) ∧
      ∀ (x : PseudolatticeGroup P I) (a : periodLine P I t),
        reduce v (normalizedLift P I (x + a.val)) = reduce v (normalizedLift P I x) := by
  obtain ⟨t, ht, htrans⟩ := theorem7 P I hodd hm h hη v hp
  refine ⟨t, ht, ?_⟩
  have hu : UnitValued v (valueLift P I) := fun x =>
    OddPrimeSpecialization.odd_prime_any_preimage P I p hodd v hp x _
      (embed_valueLift P I x)
  intro x a
  simp only [normalizedLift, SplitPrimeValuesAux.reduce_div_of_units v _ _ (hu _) (hu 0),
    htrans x a]


end SICLean.L5.SplitPrimeValues
