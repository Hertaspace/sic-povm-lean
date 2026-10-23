import SICLean.L5.OddPrimeSpecialization
import SICLean.L5.SplitPrimeGeometry
import SICLean.L5.SplitUniformDirection

set_option autoImplicit false

/-!
# Auxiliary transports for split-prime values

[RW-rec, §7]: transport noncharacteristic cyclic summands from the primary factor into
the actual period group, and apply Lemma 6 separately on each translate. [RW-rec, Prop.
3(ii), Thm. 4] give the subgroup-product reduction. The unit input is the existing
odd-prime theorem, not an additional premise on actual values. The Fourier lemma only
reindexes the existing negative-kernel transform.
-/

noncomputable section
open scoped BigOperators Classical

namespace SICLean.L5.SplitPrimeValuesAux

open LocalFourierSetup

/-- Reindex the negative-kernel Fourier transform along an additive equivalence. -/
theorem fourier_comp {G H L : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] [Field L] (e : G ≃+ H)
    (B : H → H → L) (r : L) (f : H → L) (y : G) :
    fourier (fun x y => B (e x) (e y)) r (fun x => f (e x)) y =
      fourier B r f (e y) := by
  simp only [LocalFourierSetup.fourier, map_neg]
  exact congrArg (fun z => r⁻¹ * z)
    (e.toEquiv.sum_comp (fun x => f x * B x (-e y)))

theorem valuation_prod_zero {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℝ)) {ι : Type*} (s : Finset ι) (f : ι → L)
    (hu : ∀ i ∈ s, v (f i) = 0) : v (∏ i ∈ s, f i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, v.map_mul, hu i (Finset.mem_insert_self _ _),
      ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)), zero_add]

theorem reduce_prod_of_units {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℝ)) {ι : Type*} (s : Finset ι) (f : ι → L)
    (hu : ∀ i ∈ s, v (f i) = 0) :
    reduce v (∏ i ∈ s, f i) = ∏ i ∈ s, reduce v (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, reduce_eq_residue v 1 (by simp)]
    change IsLocalRing.residue (integers v) 1 = 1
    exact map_one _
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      reduce_mul v _ _ (le_of_eq (hu i (Finset.mem_insert_self _ _)).symm)
        (le_of_eq (valuation_prod_zero v s f
          (fun j hj => hu j (Finset.mem_insert_of_mem hj))).symm),
      ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))]

theorem reduce_div_of_units {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℝ)) (a b : L) (ha : v a = 0) (hb : v b = 0) :
    reduce v (a / b) = reduce v a / reduce v b := by
  have hbi : v b⁻¹ = 0 := by rw [v.map_inv, hb, neg_zero]
  rw [div_eq_mul_inv, reduce_mul v a b⁻¹ (le_of_eq ha.symm)
    (le_of_eq hbi.symm), reduce_inv v b hb, div_eq_mul_inv]

open L3 DistributionSubgroups

variable {K : Type} [Field K] [NumberField K]

/-- Theorem 4 applied to a possibly zero p-torsion translation. -/
theorem cyclic_lift_translation (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hc : IsAddCyclic (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p))
    (u x : PseudolatticeGroup P I) (hu : p • u = 0) :
    reduce v (OddPrimeValues.lift P I (x + u)) = reduce v (OddPrimeValues.lift P I x) := by
  by_cases hz : u = 0
  · simp [hz]
  have hmem : u ∈ AddCommGroup.primaryComponent (PseudolatticeGroup P I) p :=
    AddCommGroup.mem_primaryComponent.mpr ⟨1, by simpa using hu⟩
  letI : Nontrivial (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p) :=
    ⟨⟨⟨u, hmem⟩, 0, fun he => hz (congrArg Subtype.val he)⟩⟩
  have hr := (OddPrimeCyclic.translation_reduce_one P I p hodd v hp hc
    inferInstance u x (addOrderOf_eq_prime hu hz)).2
  rw [LocalLemmaOne.translationRatio, reduce_div_of_units v _ _
    (OddPrimeUnits.odd_prime_valuation_zero P I p hodd v hp (x + u))
    (OddPrimeUnits.odd_prime_valuation_zero P I p hodd v hp x)] at hr
  apply (div_eq_one_iff_eq ?_).mp hr
  exact (reduce_ne_zero_iff v _ (by
    rw [OddPrimeUnits.odd_prime_valuation_zero P I p hodd v hp x])).mpr
      (OddPrimeUnits.odd_prime_valuation_zero P I p hodd v hp x)

/-- Transport the already proved subgroup distribution before taking residues. -/
theorem lift_subgroup_cross_mul (P : PeriodData K) (I : StablePseudolattice P)
    (H : AddSubgroup (PseudolatticeGroup P I)) (x : PseudolatticeGroup P I) :
    OddPrimeValues.lift P (subgroupLattice P I H) (project P I H x) *
        (∏ a : H, OddPrimeValues.lift P I a.val) =
      OddPrimeValues.lift P I 0 * (∏ a : H, OddPrimeValues.lift P I (x + a.val)) := by
  apply Galois.embed.injective
  simp only [map_mul, map_prod, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    OddPrimeValues.embed_lift, M72.value_zero]
  exact DistributionNormalized.distribution_normalized_cross_mul P I H x

/-- Cyclicization and distribution give invariance of the actual subgroup product. -/
theorem cyclic_subgroup_product (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (H : AddSubgroup (PseudolatticeGroup P I))
    (hc : IsAddCyclic (AddCommGroup.primaryComponent
      (PseudolatticeGroup P (subgroupLattice P I H)) p))
    (x u : PseudolatticeGroup P I) (hu : p • u = 0) :
    reduce v (∏ a : H, OddPrimeValues.lift P I (x + u + a.val)) =
      reduce v (∏ a : H, OddPrimeValues.lift P I (x + a.val)) := by
  let J := subgroupLattice P I H
  let k := (∏ a : H, OddPrimeValues.lift P I a.val) / OddPrimeValues.lift P I 0
  have hk : v k = 0 := by
    dsimp [k]
    rw [v.map_div, valuation_prod_zero v Finset.univ _
      (fun a _ => OddPrimeUnits.odd_prime_valuation_zero P I p hodd v hp a.val),
      OddPrimeUnits.odd_prime_valuation_zero P I p hodd v hp 0]
    simp
  have hprod (y : PseudolatticeGroup P I) :
      (∏ a : H, OddPrimeValues.lift P I (y + a.val)) =
        OddPrimeValues.lift P J (project P I H y) * k := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (OddPrimeValues.lift_ne_zero P I 0)).mpr
    simpa only [mul_comm] using (lift_subgroup_cross_mul P I H y).symm
  rw [hprod, hprod]
  rw [reduce_mul v _ _ (by
      rw [OddPrimeUnits.odd_prime_valuation_zero P J p hodd v hp]) (le_of_eq hk.symm),
    reduce_mul v _ _ (by
      rw [OddPrimeUnits.odd_prime_valuation_zero P J p hodd v hp]) (le_of_eq hk.symm)]
  congr 1
  rw [map_add]
  apply cyclic_lift_translation P J hodd v hp hc
  rw [← map_nsmul, hu, map_zero]

theorem first_axis_multiple {G : Type*} [AddCommGroup G] {p : ℕ}
    (c : SplitUniformDirection.Coordinates (G := G) p) (n : ℤ) :
    SplitUniformDirection.coordinate c (n : ZMod p) 0 =
      n • SplitUniformDirection.coordinate c 1 0 := by
  simpa [SplitUniformDirection.coordinate, Prod.smul_mk, zsmul_eq_mul] using
    congrArg Subtype.val (map_zsmul c n ((1, 0) : ZMod p × ZMod p))

theorem second_axis_multiple {G : Type*} [AddCommGroup G] {p : ℕ}
    (c : SplitUniformDirection.Coordinates (G := G) p) (n : ℤ) :
    SplitUniformDirection.coordinate c 0 (n : ZMod p) =
      n • SplitUniformDirection.coordinate c 0 1 := by
  simpa [SplitUniformDirection.coordinate, Prod.smul_mk, zsmul_eq_mul] using
    congrArg Subtype.val (map_zsmul c n ((0, 1) : ZMod p × ZMod p))

section PrimaryTransport

variable {G H C : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup C]

/-- Inclusion of the full primary factor, keeping the complementary coordinate zero. -/
def leftMap (e : (H × C) ≃+ G) : H →+ G :=
  e.toAddMonoidHom.comp (AddMonoidHom.inl H C)

theorem leftMap_injective (e : (H × C) ≃+ G) : Function.Injective (leftMap e) := by
  intro x y hxy
  exact congrArg Prod.fst (e.injective hxy)

theorem leftMap_ptorsion {p : ℕ} (hC : Nat.Coprime p (Nat.card C))
    (e : (H × C) ≃+ G) (x : pTorsion p (G := G)) :
    leftMap e (e.symm x.val).1 = x.val := by
  have hpx : p • x.val = 0 := x.property
  have hz : p • (e.symm x.val).2 = 0 := by
    have hx := congrArg (fun y => (e.symm y).2) hpx
    simpa only [map_nsmul, Prod.smul_snd, map_zero, Prod.snd_zero] using hx
  have hc : (e.symm x.val).2 = 0 :=
    hC.symm.nsmul_right_bijective.injective (hz.trans (smul_zero _).symm)
  change e ((e.symm x.val).1, 0) = x.val
  rw [← hc, Prod.mk.eta, e.apply_symm_apply]

/-- The p-torsion chart on the primary factor, with no torsion in C. -/
def pTorsionLeftEquiv {p : ℕ} (hC : Nat.Coprime p (Nat.card C))
    (e : (H × C) ≃+ G) :
    pTorsion p (G := G) ≃+ pTorsion p (G := H) where
  toFun x := ⟨(e.symm x.val).1, by
    change p • (e.symm x.val).1 = 0
    have hpx : p • x.val = 0 := x.property
    have hx := congrArg (fun y => (e.symm y).1) hpx
    simpa only [map_nsmul, Prod.smul_fst, map_zero, Prod.fst_zero] using hx⟩
  invFun x := ⟨leftMap e x.val, by
    change p • leftMap e x.val = 0
    rw [← map_nsmul, show p • x.val = 0 from x.property, map_zero]⟩
  left_inv x := Subtype.ext (leftMap_ptorsion hC e x)
  right_inv x := by
    apply Subtype.ext
    change (e.symm (e (x.val, 0))).1 = x.val
    rw [e.symm_apply_apply]
  map_add' x y := by
    apply Subtype.ext
    change (e.symm (x.val + y.val)).1 = (e.symm x.val).1 + (e.symm y.val).1
    rw [map_add, Prod.fst_add]

theorem leftMap_torsion_image {p : ℕ} (hC : Nat.Coprime p (Nat.card C))
    (e : (H × C) ≃+ G) :
    (pTorsion p (G := H)).map (leftMap e) = pTorsion p (G := G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change p • leftMap e y = 0
    rw [← map_nsmul, show p • y = 0 from hy, map_zero]
  · intro hx
    exact ⟨(pTorsionLeftEquiv hC e ⟨x, hx⟩).val,
      (pTorsionLeftEquiv hC e ⟨x, hx⟩).property, leftMap_ptorsion hC e ⟨x, hx⟩⟩

theorem leftMap_fullCyclic {p s : ℕ} [Fintype H] [Fintype G]
    (e : (H × C) ≃+ G) (S : AddSubgroup H)
    (hS : SplitGroupRing.FullCyclicSummand p s S) :
    SplitGroupRing.FullCyclicSummand p s (S.map (leftMap e)) := by
  let j := leftMap e
  have hj := leftMap_injective e
  let d := S.equivMapOfInjective j hj
  letI : IsAddCyclic S := hS.1
  refine ⟨isAddCyclic_of_surjective d d.surjective, ?_, ?_⟩
  · exact (Nat.card_congr d.toEquiv).symm.trans hS.2.1
  · obtain ⟨T, hT⟩ := hS.2.2
    refine ⟨(T.prod ⊤).map e.toAddMonoidHom, ?_, ?_⟩
    · apply AddSubgroup.disjoint_def.mpr
      rintro z ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
      have hab : b = (a, 0) := e.injective he
      have haT : a ∈ T := hab ▸ hb |>.1
      have ha0 := AddSubgroup.disjoint_def.mp hT.disjoint ha haT
      simp only [ha0, map_zero]
    · apply codisjoint_iff.mpr
      apply top_unique
      intro z _
      have hz : (e.symm z).1 ∈ S ⊔ T := by rw [hT.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hz
      apply AddSubgroup.mem_sup.mpr
      refine ⟨j a, ⟨a, ha, rfl⟩, e (b, (e.symm z).2), ⟨(b, (e.symm z).2), ⟨hb, trivial⟩, rfl⟩, ?_⟩
      change e (a, 0) + e (b, (e.symm z).2) = z
      rw [← map_add]
      apply e.symm.injective
      simp only [e.symm_apply_apply]
      exact Prod.ext hab (zero_add _)

theorem cosetProduct_leftMap {A : Type*} [CommGroup A] [Fintype H] [Fintype G]
    (e : (H × C) ≃+ G) (g : G → A) (S : AddSubgroup H) (x : G) (y : H) :
    SplitGroupRing.cosetProduct (fun z => g (x + leftMap e z)) S y =
      SplitGroupRing.cosetProduct g (S.map (leftMap e)) (x + leftMap e y) := by
  let d := S.equivMapOfInjective (leftMap e) (leftMap_injective e)
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (S.map (leftMap e)) := Fintype.ofFinite _
  unfold SplitGroupRing.cosetProduct
  calc
    _ = ∏ z : S, g (x + leftMap e y + (d z).val) := by
      apply Finset.prod_congr rfl
      intro z _
      simp only [d, AddSubgroup.coe_equivMapOfInjective_apply, map_add, add_assoc]
    _ = _ := d.toEquiv.prod_comp (fun z => g (x + leftMap e y + z.val))

theorem leftMap_coordinate {p : ℕ} (hC : Nat.Coprime p (Nat.card C))
    (e : (H × C) ≃+ G) (c : SplitUniformDirection.Coordinates (G := G) p)
    (u w : ZMod p) :
    leftMap e (SplitUniformDirection.coordinate (c.trans (pTorsionLeftEquiv hC e)) u w) =
      SplitUniformDirection.coordinate c u w :=
  leftMap_ptorsion hC e (c (u, w))

theorem leftMap_noncharacteristic {p : ℕ} (hC : Nat.Coprime p (Nat.card C))
    (e : (H × C) ≃+ G) (S : AddSubgroup H) (a : H)
    (ha : S ⊓ pTorsion p ≠ AddSubgroup.zmultiples a) :
    S.map (leftMap e) ⊓ pTorsion p ≠ AddSubgroup.zmultiples (leftMap e a) := by
  intro heq
  apply ha
  apply AddSubgroup.map_injective (leftMap_injective e)
  rw [AddSubgroup.map_inf _ _ _ (leftMap_injective e), leftMap_torsion_image hC e,
    AddMonoidHom.map_zmultiples]
  exact heq

end PrimaryTransport

/-- Lemma 6 on each translate of the primary factor. The complementary factor is kept fixed, and the
noncharacteristic subgroups are counted in the primary factor before their injective images are used
in G. -/
theorem mixed_of_primary_products {G C k : Type*}
    [AddCommGroup G] [Fintype G] [AddCommGroup C] [Fintype C] [Field k]
    {p s : ℕ} [Fact p.Prime] [CharP k p] (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Nat.card C))
    (e : (FiniteCosetMoments.Point p s 2 × C) ≃+ G)
    (c : SplitUniformDirection.Coordinates (G := G) p) (g : G → kˣ)
    (hg : ∀ S : AddSubgroup G, SplitGroupRing.FullCyclicSummand p s S →
      S ⊓ pTorsion p ≠ AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 1 0) →
      S ⊓ pTorsion p ≠ AddSubgroup.zmultiples (SplitUniformDirection.coordinate c 0 1) →
      ∀ x u, p • u = 0 →
        SplitGroupRing.cosetProduct g S (x + u) = SplitGroupRing.cosetProduct g S x) :
    ∀ x : G,
      g (x + SplitUniformDirection.coordinate c 1 0 + SplitUniformDirection.coordinate c 0 1) *
          g x = g (x + SplitUniformDirection.coordinate c 1 0) *
            g (x + SplitUniformDirection.coordinate c 0 1) := by
  let cH := c.trans (pTorsionLeftEquiv hC e)
  let a := SplitUniformDirection.coordinate cH 1 0
  let b := SplitUniformDirection.coordinate cH 0 1
  have ha : leftMap e a = SplitUniformDirection.coordinate c 1 0 :=
    leftMap_coordinate hC e c 1 0
  have hb : leftMap e b = SplitUniformDirection.coordinate c 0 1 :=
    leftMap_coordinate hC e c 0 1
  intro x
  let gx := fun z => g (x + leftMap e z)
  have hprod : SplitGroupRing.ProductsInvariant p s a b gx := by
    intro S hS y u hu
    have hprops := (Finset.mem_filter.mp hS).2
    have hSa := leftMap_noncharacteristic hC e S a hprops.2.1
    have hSb := leftMap_noncharacteristic hC e S b hprops.2.2
    rw [ha] at hSa
    rw [hb] at hSb
    change SplitGroupRing.cosetProduct (fun z => g (x + leftMap e z)) S (y + u) =
      SplitGroupRing.cosetProduct (fun z => g (x + leftMap e z)) S y
    rw [cosetProduct_leftMap, cosetProduct_leftMap, map_add, ← add_assoc]
    apply hg (S.map (leftMap e)) (leftMap_fullCyclic e S hprops.1) hSa hSb
    rw [← map_nsmul, hu, map_zero]
  have hm := SplitGroupRing.lemma6_residue hs (AddEquiv.refl _)
    a b (SplitUniformDirection.coordinate_basis cH) gx hprod 0
  simpa only [gx, map_add, map_zero, add_zero, zero_add, ha, hb, add_assoc] using hm

end SICLean.L5.SplitPrimeValuesAux
