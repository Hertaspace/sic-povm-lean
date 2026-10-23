import SICLean.L5.SplitFrobenius
import SICLean.L5.RayArithmeticPrincipal
import SICLean.L5.GoodReductionSeparation
import SICLean.L5.OddPrimeSpecialization
import SICLean.L5.SplitFrobeniusFiniteAux

set_option autoImplicit false

/-!
# Finite-place statements

[RW-rec, Thm. 7--8, Lemma 8, §8, pp. 12--13, p. 14] supplies the principal-ideal use,
and Proposition 4 the finite-field use. The colon bridge uses the
already defined `RayArithmeticPrincipal.contraction`, not a second definition of an
order. Algebraicity is [RW26, Thm. 1, p. 3], and the matrix dictionary is [RW26, (37),
p. 20]. One finite field and one prime are fixed for the whole family. An extension of
that valuation to Qbar is proved here, and is not an extra input. `congruentAt`
includes both local-integrality conditions. The final common-target statements need only the
base values in the base field. They may identify both ideal candidates with U_I(x) or
U_I(-x) before any finite-field membership of the ideal-translated values has been
assumed.
-/

noncomputable section
open scoped NumberField MatrixGroups

namespace SICLean.L5.SplitFrobeniusFinite

open L3 SplitPrimeLattice SplitPrimeValues SplitFrobenius

variable (F : IntermediateField ℚ Galois.Qbar) [NumberField F]

/-- [RW-rec]: extend the prescribed normalized finite valuation to the same Qbar. This is a genuine
valuation-extension obligation. -/
theorem exists_normalized_extension (P : FinitePlace.Prime F) :
    ∃ v : AddValuation Galois.Qbar (WithTop ℝ),
      ∀ x : F, v (x : Galois.Qbar) = FinitePlace.valuation P x := by
  obtain ⟨v, _, hv⟩ := OddPrimeValues.exists_valuation_extension P F.val
  exact ⟨v, hv⟩

/-- [RW-rec]: injective residue comparison under an extension; the residue fields need not be equal,
nor need either equal F_p. -/
theorem extension_reduction_iff (P : FinitePlace.Prime F)
    (v : AddValuation Galois.Qbar (WithTop ℝ))
    (hv : ∀ x : F, v (x : Galois.Qbar) = FinitePlace.valuation P x)
    (x y : F) (hx : FinitePlace.IntegralAt P x) (hy : FinitePlace.IntegralAt P y) :
    LocalFourierSetup.reduce v (x : Galois.Qbar) = LocalFourierSetup.reduce v (y : Galois.Qbar) ↔
      FinitePlace.red P x hx = FinitePlace.red P y hy := by
  have hxv : 0 ≤ v (x : Galois.Qbar) := by rw [hv]; exact hx
  have hyv : 0 ≤ v (y : Galois.Qbar) := by rw [hv]; exact hy
  rw [LocalFourierSetup.reduce_eq_iff v _ _ hxv hyv,
    FinitePlace.red_eq_iff P x y hx hy]
  change 0 < v ((x - y : F) : Galois.Qbar) ↔
    0 < FinitePlace.valuation P (x - y)
  rw [hv]

/-- [RW-rec]: the stronger downstream congruence convention requires the displayed integrality
hypotheses as well as equal residues. -/
theorem extension_congruentAt_iff (P : FinitePlace.Prime F)
    (v : AddValuation Galois.Qbar (WithTop ℝ))
    (hv : ∀ x : F, v (x : Galois.Qbar) = FinitePlace.valuation P x)
    (x y : F) (hx : FinitePlace.IntegralAt P x) (hy : FinitePlace.IntegralAt P y) :
    GoodReductionLocal.congruentAt F P x y ↔
      LocalFourierSetup.reduce v (x : Galois.Qbar) = LocalFourierSetup.reduce v (y : Galois.Qbar) := by
  have hxi := (OddPrimeSpecialization.integralAt_iff_goodReduction F P x).mp hx
  have hyi := (OddPrimeSpecialization.integralAt_iff_goodReduction F P y).mp hy
  rw [extension_reduction_iff F P v hv x y hx hy, FinitePlace.red_eq_iff P x y hx hy,
    SplitFrobeniusFiniteAux.congruent_iff_multiplicative_lt]
  exact ⟨fun h => h.2.2, fun h => ⟨hxi, hyi, h⟩⟩

/-- [RW-rec]; [RW26, p. 20]. Uses the conductor of the lattice. -/
theorem actual_locallyMaximal (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    {p : ℕ} (hp : p.Prime) (hc : ¬ p ∣ RayArithmeticOrder.conductor M hM) :
    LocallyMaximal (ActualField.periodData M hM) (ActualLattice.stableLattice M hM) p := by
  apply locallyMaximal_of_bound (ActualField.periodData M hM)
    (ActualLattice.stableLattice M hM) hp (RayArithmeticOrder.conductor_pos M hM) hc
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
  change y ∈ Submodule.span (𝓞 (ActualField.baseField M hM))
    ((ActualLattice.stableLattice M hM).val : Set (ActualField.baseField M hM)) at hy
  have hspan : ∀ z ∈ Submodule.span (𝓞 (ActualField.baseField M hM))
      ((ActualLattice.stableLattice M hM).val : Set (ActualField.baseField M hM)),
      ∀ b : 𝓞 (ActualField.baseField M hM),
        (RayArithmeticOrder.conductor M hM : ActualField.baseField M hM) *
          (b : ActualField.baseField M hM) * z ∈ (ActualLattice.stableLattice M hM).val := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        intro b
        exact (RayArithmeticOrder.mem_multiplierOrder M hM _).mp
          (RayArithmeticOrder.conductor_mul_mem M hM b) z hz
    | zero => intro b; simp
    | add z w hz hw ihz ihw =>
        intro b
        rw [mul_add]
        exact (ActualLattice.stableLattice M hM).val.add_mem (ihz b) (ihw b)
    | smul a z hz ih =>
        intro b
        simpa [Algebra.smul_def, mul_assoc] using ih (b * a)
  simpa using hspan y hy 1

/-- [RW-rec]: connect the general colon to the actual contracted order ideal. No maximal-order
saturation replaces I. -/
theorem actual_contracted_colon (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (r : FinitePlace.Prime (ActualField.baseField M hM)) :
    inversePrimeCarrier (ActualField.periodData M hM) (ActualLattice.stableLattice M hM) r =
      ⨅ a : RayArithmeticPrincipal.contraction M hM r.asIdeal,
        (ActualLattice.stableLattice M hM).val.comap
          (LinearMap.mulLeft ℤ (a.val.val : ActualField.baseField M hM)) := by
  ext x
  rw [mem_inversePrimeCarrier]
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply]
  constructor
  · intro hx a
    exact hx (RayArithmeticPrincipal.orderToIntegers M hM a.val) a.property
      ((RayArithmeticOrder.mem_multiplierOrder M hM _).mp a.val.property)
  · intro hx a ha hstable
    let b : RayArithmeticOrder.multiplierOrder M hM := ⟨(a : _), hstable⟩
    have hb : b ∈ RayArithmeticPrincipal.contraction M hM r.asIdeal := by
      change RayArithmeticPrincipal.orderToIntegers M hM b ∈ r.asIdeal
      have he : RayArithmeticPrincipal.orderToIntegers M hM b = a := Subtype.ext rfl
      rwa [he]
    exact hx ⟨b, hb⟩

/-- [RW-rec]: a principal contracted ideal gives the literal inverse homothety. Sign-dependent value
transport is handled separately. -/
theorem actual_principal_inverse (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (r : FinitePlace.Prime (ActualField.baseField M hM))
    (a : RayArithmeticOrder.multiplierOrder M hM) (ha : a ≠ 0)
    (hprincipal : RayArithmeticPrincipal.contraction M hM r.asIdeal = Ideal.span {a}) :
    inversePrimeCarrier (ActualField.periodData M hM) (ActualLattice.stableLattice M hM) r =
      pseudolatticeScale (a.val)⁻¹ (ActualLattice.stableLattice M hM).val := by
  rw [actual_contracted_colon M hM r, hprincipal]
  have haK : (a.val : ActualField.baseField M hM) ≠ 0 := by
    intro he
    apply ha
    exact Subtype.ext he
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply]
  rw [pseudolatticeScale_mem_iff]
  constructor
  · intro hx
    have hax := hx ⟨a, Ideal.subset_span (Set.mem_singleton a)⟩
    exact ⟨a.val * x, hax, inv_mul_cancel_left₀ haK x⟩
  · rintro ⟨y, hy, rfl⟩ b
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp b.property
    have hb : b.val.val = a.val * c.val := congrArg Subtype.val hc
    rw [hb]
    have hcI := (RayArithmeticOrder.mem_multiplierOrder M hM _).mp c.property y hy
    convert hcI using 1
    field_simp

variable {K : Type} [Field K] [NumberField K]

/-- [RW-rec, Thm. 5]'s odd-prime conclusion, applied to the existing normalization. This is a
specialization for finite-field calls, not a separate statement or input package. -/
theorem normalized_units (P0 : PeriodData K) (I : StablePseudolattice P0)
    (P : FinitePlace.Prime F) (hodd : FinitePlace.residueChar P ≠ 2)
    (u : PseudolatticeGroup P0 I → F)
    (hu : ∀ x, (u x : Galois.Qbar) = normalizedLift P0 I x) :
    ∀ x, FinitePlace.UnitAt P (u x) := by
  intro x
  apply OddPrimeSpecialization.normalized_unitAt_of_embed P0 I F.val P hodd x (u x)
  change Galois.embed (u x : Galois.Qbar) = _
  rw [hu x]
  exact embed_normalizedLift P0 I x

/-- [RW-rec, Thm. 7] at an arbitrary fixed finite prime. No Qbar valuation or per-label choice
remains in the public finite statement. -/
theorem theorem7_finite (P0 : PeriodData K) (I : StablePseudolattice P0)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P0 I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P0 p)
    (P : FinitePlace.Prime F) (hP : FinitePlace.residueChar P = p)
    (f : PseudolatticeGroup P0 I → F)
    (hf : ∀ x, (f x : Galois.Qbar) = valueLift P0 I x) :
    ∃ t : FinitePlace.Prime K, (t = r ∨ t = q) ∧
      ∀ (x : PseudolatticeGroup P0 I) (a : periodLine P0 I t),
        GoodReductionLocal.congruentAt F P (f (x + a.val)) (f x) := by
  obtain ⟨v, hv⟩ := exists_normalized_extension F P
  have hpv : v (p : Galois.Qbar) = 1 := by
    calc
      v (p : Galois.Qbar) = FinitePlace.valuation P (p : F) := by
        simpa using hv (p : F)
      _ = 1 := by simpa only [hP] using FinitePlace.valuation_residueChar P
  have hoddP : FinitePlace.residueChar P ≠ 2 := by simpa only [hP] using hodd
  have hfunit (x : PseudolatticeGroup P0 I) : FinitePlace.UnitAt P (f x) := by
    apply OddPrimeSpecialization.unitAt_of_embed P0 I F.val P hoddP x (f x)
    change Galois.embed (f x : Galois.Qbar) = _
    rw [hf x]
    exact embed_valueLift P0 I x
  obtain ⟨t, ht, hdir⟩ := SplitPrimeValues.theorem7 P0 I hodd hm h hη v hpv
  refine ⟨t, ht, ?_⟩
  intro x a
  apply (extension_congruentAt_iff F P v hv _ _
    (FinitePlace.unitAt_integral P (hfunit _))
    (FinitePlace.unitAt_integral P (hfunit _))).mpr
  simpa only [hf] using hdir x a

/-- [RW-rec, Thm. 8]: two candidate families already in F. The disjunction is outside ∀x, and
congruentAt supplies local integrality. -/
theorem theorem8_finite (P0 : PeriodData K) (I : StablePseudolattice P0)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P0 I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (P : FinitePlace.Prime F) (hP : FinitePlace.residueChar P = p)
    (u ur uq : PseudolatticeGroup P0 I → F)
    (hu : ∀ x, (u x : Galois.Qbar) = normalizedLift P0 I x)
    (hr : ∀ x, (ur x : Galois.Qbar) = normalizedLift P0 (inversePrimeLattice P0 I r)
      (projectInverse P0 I r x))
    (hq : ∀ x, (uq x : Galois.Qbar) = normalizedLift P0 (inversePrimeLattice P0 I q)
      (projectInverse P0 I q x)) :
    (∀ x, GoodReductionLocal.congruentAt F P (ur x) (u x ^ p)) ∨
      (∀ x, GoodReductionLocal.congruentAt F P (uq x) (u x ^ p)) := by
  obtain ⟨v, hv⟩ := exists_normalized_extension F P
  have hpv : v (p : Galois.Qbar) = 1 := by
    calc
      v (p : Galois.Qbar) = FinitePlace.valuation P (p : F) := by
        simpa using hv (p : F)
      _ = 1 := by simpa only [hP] using FinitePlace.valuation_residueChar P
  have hoddP : FinitePlace.residueChar P ≠ 2 := by simpa only [hP] using hodd
  have hui (x : PseudolatticeGroup P0 I) : FinitePlace.IntegralAt P (u x) :=
    FinitePlace.unitAt_integral P (normalized_units F P0 I P hoddP u hu x)
  have candidate (t : FinitePlace.Prime K) (ut : PseudolatticeGroup P0 I → F)
      (hut : ∀ x, (ut x : Galois.Qbar) = normalizedLift P0 (inversePrimeLattice P0 I t)
        (projectInverse P0 I t x))
      (hdir : ∀ x : PseudolatticeGroup P0 I,
        LocalFourierSetup.reduce v (normalizedLift P0 (inversePrimeLattice P0 I t)
          (projectInverse P0 I t x)) = LocalFourierSetup.reduce v (normalizedLift P0 I x) ^ p) :
      ∀ x, GoodReductionLocal.congruentAt F P (ut x) (u x ^ p) := by
    intro x
    have huti : FinitePlace.IntegralAt P (ut x) := by
      apply FinitePlace.unitAt_integral P
      apply OddPrimeSpecialization.normalized_unitAt_of_embed P0
        (inversePrimeLattice P0 I t) F.val P hoddP (projectInverse P0 I t x) (ut x)
      change Galois.embed (ut x : Galois.Qbar) = _
      rw [hut x]
      exact embed_normalizedLift _ _ _
    apply (extension_congruentAt_iff F P v hv _ _ huti
      (FinitePlace.integralAt_pow P (hui x) p)).mpr
    have hxv : 0 ≤ v (u x : Galois.Qbar) := by rw [hv]; exact hui x
    rw [IntermediateField.coe_pow, SplitFrobeniusFiniteAux.reduce_pow v _ hxv, hut x, hu x]
    exact hdir x
  obtain ⟨t, ht, hdir⟩ := SplitFrobenius.theorem8 P0 I hodd hm h v hpv
  rcases ht with ht | ht
  · subst t
    exact Or.inl (candidate _ ur hr hdir)
  · subst t
    exact Or.inr (candidate _ uq hq hdir)

/-- [RW-rec]: both order-prime candidates have the same target. Only u and w need lie in F, so this
can be called before adjoining any ideal-translated values. This is the general elimination
interface. -/
theorem theorem8_common_target (P0 : PeriodData K) (I : StablePseudolattice P0)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P0 I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (P : FinitePlace.Prime F) (hP : FinitePlace.residueChar P = p)
    (u w : PseudolatticeGroup P0 I → F)
    (hu : ∀ x, (u x : Galois.Qbar) = normalizedLift P0 I x)
    (hr : ∀ x, normalizedLift P0 (inversePrimeLattice P0 I r) (projectInverse P0 I r x) =
      (w x : Galois.Qbar))
    (hq : ∀ x, normalizedLift P0 (inversePrimeLattice P0 I q) (projectInverse P0 I q x) =
      (w x : Galois.Qbar)) :
    ∀ x, GoodReductionLocal.congruentAt F P (u x ^ p) (w x) := by
  have hcongr := theorem8_finite F P0 I hodd hm h P hP u w w hu
    (fun x => (hr x).symm) (fun x => (hq x).symm)
  rcases hcongr with hr' | hq'
  · exact fun x => GoodReductionLocal.congruentAt_symm F P (hr' x)
  · exact fun x => GoodReductionLocal.congruentAt_symm F P (hq' x)

/-- [RW-rec]. Both positive principal-ideal identities give U(x)^p ≡ U(x). No class-field membership
of the values is assumed. -/
theorem theorem8_identity_target (P0 : PeriodData K) (I : StablePseudolattice P0)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P0 I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (P : FinitePlace.Prime F) (hP : FinitePlace.residueChar P = p)
    (u : PseudolatticeGroup P0 I → F)
    (hu : ∀ x, (u x : Galois.Qbar) = normalizedLift P0 I x)
    (hr : ∀ x, normalizedLift P0 (inversePrimeLattice P0 I r) (projectInverse P0 I r x) =
      normalizedLift P0 I x)
    (hq : ∀ x, normalizedLift P0 (inversePrimeLattice P0 I q) (projectInverse P0 I q x) =
      normalizedLift P0 I x) :
    ∀ x, GoodReductionLocal.congruentAt F P (u x ^ p) (u x) := by
  exact theorem8_common_target F P0 I hodd hm h P hP u u hu
    (fun x => (hr x).trans (hu x).symm) (fun x => (hq x).trans (hu x).symm)

/-- [RW-rec, Thm. 8]. Both double-negative identities give U(x)^p ≡ U(-x). This is reflection of the
label, with no reciprocal or conjugation added. -/
theorem theorem8_reflection_target (P0 : PeriodData K) (I : StablePseudolattice P0)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P0 I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (P : FinitePlace.Prime F) (hP : FinitePlace.residueChar P = p)
    (u : PseudolatticeGroup P0 I → F)
    (hu : ∀ x, (u x : Galois.Qbar) = normalizedLift P0 I x)
    (hr : ∀ x, normalizedLift P0 (inversePrimeLattice P0 I r) (projectInverse P0 I r x) =
      normalizedLift P0 I (-x))
    (hq : ∀ x, normalizedLift P0 (inversePrimeLattice P0 I q) (projectInverse P0 I q x) =
      normalizedLift P0 I (-x)) :
    ∀ x, GoodReductionLocal.congruentAt F P (u x ^ p) (u (-x)) := by
  exact theorem8_common_target F P0 I hodd hm h P hP u (fun x => u (-x)) hu
    (fun x => (hr x).trans (hu (-x)).symm) (fun x => (hq x).trans (hu (-x)).symm)


end SICLean.L5.SplitFrobeniusFinite
