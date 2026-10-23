import SICLean.L5.RayArithmeticModulus
import Mathlib.RingTheory.FractionalIdeal.Operations
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

/-!
Proof tools for the actual quadratic conjugation. Integral ideal multiplicities give the
transported adic valuations and fractional-ideal counts. The completion-defined
higher-unit condition is then expressed using the original field valuation, with the
same normalization at all finite primes. All auxiliary declarations stay in the
namespace below.
-/

noncomputable section
open scoped MatrixGroups NumberField Classical
open NumberField IsDedekindDomain

namespace SICLean.L5.RayArithmeticConjugationAux

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM

theorem integerConjugation_involutive :
    Function.Involutive (RayArithmeticPlaces.integerConjugation M hM) := by
  intro x
  apply RingOfIntegers.ext
  exact RayArithmeticPlaces.conjugation_involutive M hM x

theorem integerConjugation_trans :
    (RayArithmeticPlaces.integerConjugation M hM).trans
      (RayArithmeticPlaces.integerConjugation M hM) = RingEquiv.refl (𝓞 K) := by
  apply RingEquiv.ext
  intro x
  exact integerConjugation_involutive M hM x

/-- Forward transport, as a multiplicative equivalence of integral ideals. -/
def idealMapEquiv {R : Type*} [CommRing R] (e : R ≃+* R) : Ideal R ≃* Ideal R where
  toFun I := I.map e
  invFun I := I.map e.symm
  left_inv _ := Ideal.map_of_equiv e
  right_inv _ := Ideal.map_of_equiv e.symm
  map_mul' I J := Ideal.map_mul e I J

theorem prime_map {R : Type*} [CommRing R] (e : R ≃+* R)
    (v : HeightOneSpectrum R) :
    (HeightOneSpectrum.equivOfRingEquiv e v).asIdeal = v.asIdeal.map e := by
  ext x
  exact Ideal.symm_apply_mem_of_equiv_iff

theorem factorization_map {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (v : HeightOneSpectrum R) (I : Ideal R) :
    factorization (I.map e) (HeightOneSpectrum.equivOfRingEquiv e v).asIdeal =
      factorization I v.asIdeal := by
  by_cases hI : I = 0
  · subst I
    have hz : Ideal.map e (0 : Ideal R) = 0 := Ideal.map_bot
    rw [hz, factorization_zero]
    rfl
  have hmap : I.map e ≠ 0 := by
    intro h
    apply hI
    apply (idealMapEquiv e).injective
    exact h.trans (by change (0 : Ideal R) = Ideal.map e 0; simp)
  rw [HeightOneSpectrum.factorization_eq_multiplicity hmap,
    HeightOneSpectrum.factorization_eq_multiplicity hI, prime_map]
  exact multiplicity_map_eq (idealMapEquiv e)

theorem intValuation_conjugation (v : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    (HeightOneSpectrum.equivOfRingEquiv
      (RayArithmeticPlaces.integerConjugation M hM) v).intValuation
      (RayArithmeticPlaces.integerConjugation M hM r) = v.intValuation r := by
  by_cases hr : r = 0
  · subst r
    simp
  have her : RayArithmeticPlaces.integerConjugation M hM r ≠ 0 :=
    by simpa only [map_zero] using
      (RayArithmeticPlaces.integerConjugation M hM).injective.ne hr
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ her,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hr]
  congr 2
  rw [prime_map]
  have hspan : Ideal.span {RayArithmeticPlaces.integerConjugation M hM r} =
      (Ideal.span {r}).map (RayArithmeticPlaces.integerConjugation M hM) := by
    simp [Ideal.map_span]
  rw [hspan]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (multiplicity_map_eq (idealMapEquiv (RayArithmeticPlaces.integerConjugation M hM)))

theorem valuation_conjugation (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (HeightOneSpectrum.equivOfRingEquiv
      (RayArithmeticPlaces.integerConjugation M hM) v).valuation K
      (RayArithmeticPlaces.conjugation M hM x) = v.valuation K x := by
  obtain ⟨r, d, hrd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 K)) x
  rw [← hrd, IsFractionRing.mk'_eq_div, map_div₀, map_div₀, map_div₀]
  change
    (HeightOneSpectrum.equivOfRingEquiv
      (RayArithmeticPlaces.integerConjugation M hM) v).valuation K
        (algebraMap (𝓞 K) K (RayArithmeticPlaces.integerConjugation M hM r)) /
      (HeightOneSpectrum.equivOfRingEquiv
        (RayArithmeticPlaces.integerConjugation M hM) v).valuation K
        (algebraMap (𝓞 K) K (RayArithmeticPlaces.integerConjugation M hM d)) = _
  simp only [HeightOneSpectrum.valuation_of_algebraMap, intValuation_conjugation]

theorem fractionRing_conjugation :
    IsFractionRing.ringEquivOfRingEquiv (L := K)
      (RayArithmeticPlaces.integerConjugation M hM) =
      (RayArithmeticPlaces.conjugation M hM).toRingEquiv := by
  apply RingEquiv.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := 𝓞 K)
  intro x
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

theorem fractional_map_coe (I : Ideal (𝓞 K)) :
    FractionalIdeal.ringEquivOfRingEquiv K K
      (RayArithmeticPlaces.integerConjugation M hM) I =
      (I.map (RayArithmeticPlaces.integerConjugation M hM) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  have := RingHomInvPair.of_ringEquiv (RayArithmeticPlaces.integerConjugation M hM)
  have := RingHomInvPair.of_ringEquiv_symm (RayArithmeticPlaces.integerConjugation M hM)
  ext x
  change x ∈ Submodule.map
      (IsFractionRing.semilinearEquivOfRingEquiv K K
        (RayArithmeticPlaces.integerConjugation M hM)).toLinearMap
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K).val ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    apply (FractionalIdeal.mem_coeIdeal _).mpr
    refine ⟨RayArithmeticPlaces.integerConjugation M hM r,
      Ideal.mem_map_of_mem _ hr, ?_⟩
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap _ r).symm
  · intro hx
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
    obtain ⟨s, hs, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (RayArithmeticPlaces.integerConjugation M hM).surjective).mp hr
    refine ⟨algebraMap (𝓞 K) K s, (FractionalIdeal.mem_coeIdeal _).mpr ⟨s, hs, rfl⟩, ?_⟩
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ s

theorem count_coe_eq_factorization {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (I : Ideal R) :
    FractionalIdeal.count F v I = (factorization I v.asIdeal : ℤ) := by
  by_cases hI : I = 0
  · subst I
    rw [show ((0 : Ideal R) : FractionalIdeal (nonZeroDivisors R) F) = 0 from
      FractionalIdeal.coeIdeal_bot, FractionalIdeal.count_zero, factorization_zero]
    rfl
  rw [FractionalIdeal.count_coe F v hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot, factorization_eq_count]

theorem fractional_count_conjugation (v : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    FractionalIdeal.count K
      (HeightOneSpectrum.equivOfRingEquiv (RayArithmeticPlaces.integerConjugation M hM) v)
      (FractionalIdeal.ringEquivOfRingEquiv K K
        (RayArithmeticPlaces.integerConjugation M hM) I) = FractionalIdeal.count K v I := by
  obtain ⟨a, J, ha, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  rw [← FractionalIdeal.one_div_spanSingleton, one_div,
    ← FractionalIdeal.coeIdeal_span_singleton]
  rw [map_mul, map_inv₀, fractional_map_coe, fractional_map_coe]
  have hspan : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by simpa using ha
  have hspan' : Ideal.map (RayArithmeticPlaces.integerConjugation M hM)
      (Ideal.span {a}) ≠ 0 := by
    simp only [Ideal.map_span, Set.image_singleton, Ideal.zero_eq_bot, ne_eq,
      Ideal.span_singleton_eq_bot]
    simpa only [map_zero] using (RayArithmeticPlaces.integerConjugation M hM).injective.ne ha
  by_cases hJ : J = 0
  · subst J
    simp only [Ideal.zero_eq_bot, Ideal.map_bot, FractionalIdeal.coeIdeal_bot, mul_zero,
      FractionalIdeal.count_zero]
  have hJ' : J.map (RayArithmeticPlaces.integerConjugation M hM) ≠ 0 := by
    intro hz
    have := congrArg (Ideal.map (RayArithmeticPlaces.integerConjugation M hM).symm) hz
    change (idealMapEquiv (RayArithmeticPlaces.integerConjugation M hM)).symm
      ((idealMapEquiv (RayArithmeticPlaces.integerConjugation M hM)) J) = _ at this
    rw [MulEquiv.symm_apply_apply] at this
    exact hJ (this.trans Ideal.map_bot)
  rw [FractionalIdeal.count_mul, FractionalIdeal.count_mul,
    FractionalIdeal.count_inv, FractionalIdeal.count_inv]
  · simp only [count_coe_eq_factorization, factorization_map]
  all_goals simp only [ne_eq, inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero, ← Ideal.zero_eq_bot, hspan, hspan',
    hJ, hJ', not_false_eq_true]

theorem fractional_conjugation_involutive :
    Function.Involutive
      (FractionalIdeal.ringEquivOfRingEquiv K K
        (RayArithmeticPlaces.integerConjugation M hM)) := by
  intro I
  rw [← FractionalIdeal.ringEquivOfRingEquiv_trans_apply,
    integerConjugation_trans, FractionalIdeal.ringEquivOfRingEquiv_refl]
  rfl

theorem fractional_principal_conjugation (x : Kˣ) :
    Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K
        (RayArithmeticPlaces.integerConjugation M hM)).toMulEquiv
        (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 K) K
        (Units.mapEquiv (RayArithmeticPlaces.conjugation M hM).toRingEquiv.toMulEquiv x) := by
  apply Units.ext
  simp only [Units.coe_mapEquiv, coe_toPrincipalIdeal]
  change FractionalIdeal.ringEquivOfRingEquiv K K
      (RayArithmeticPlaces.integerConjugation M hM)
      (FractionalIdeal.spanSingleton _ (x : K)) =
    FractionalIdeal.spanSingleton _ (RayArithmeticPlaces.conjugation M hM x)
  rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton, fractionRing_conjugation]
  rfl

omit M hM in
theorem withZero_lt_one_iff (q : WithZero (Multiplicative ℤ)) :
    q < 1 ↔ q ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hq : q = 0
  · simp [hq]
  rw [← WithZero.exp_log hq]
  simp only [WithZero.exp_lt_one_iff, WithZero.exp_le_exp]
  omega

omit M hM in
theorem valuation_algebraMap {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

omit M hM in
/-- The normalization is the same at every prime: a uniformizer has value exp(-1). -/
theorem local_pow_mem_iff {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (t : v.adicCompletionIntegers F) :
    t ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n ↔
      Valued.v (t : v.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨r, hr⟩ := v.intValuation_exists_uniformizer
  let π : v.adicCompletionIntegers F := algebraMap (𝓞 F) _ r
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = _
    rw [show algebraMap (𝓞 F) (v.adicCompletion F) r =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) from rfl,
      valuation_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, hr]
  have hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π} := by
    ext y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
      Ideal.mem_span_singleton,
      (HeightOneSpectrum.adicCompletionIntegers.integers F v).dvd_iff_le]
    change Valued.v (y : v.adicCompletion F) ≠ 1 ↔
      Valued.v (y : v.adicCompletion F) ≤ Valued.v (π : v.adicCompletion F)
    rw [hπ, ← withZero_lt_one_iff]
    exact (lt_iff_le_and_ne.trans (and_iff_right y.2)).symm
  rw [hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers F v).dvd_iff_le]
  change Valued.v (t : v.adicCompletion F) ≤ Valued.v ((π : v.adicCompletion F) ^ n) ↔ _
  rw [map_pow, hπ, ← WithZero.exp_nsmul]
  simp

omit M hM in
/-- Express the completion-defined higher-unit condition by the original valuation. -/
theorem finiteUnit_mem_iff {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (x : Fˣ) :
    ClassFieldTheory.finitePlaceUnitEmbedding v x ∈
      ClassFieldTheory.rayLocalHigherUnitGroup v n ↔
      v.valuation F (x : F) = 1 ∧
        v.valuation F ((x : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  change ClassFieldTheory.finitePlaceUnitEmbedding v x ∈ RayClass.localHigherUnitGroup v n ↔ _
  rw [RayClass.mem_localHigherUnitGroup_iff]
  constructor
  · rintro ⟨y, hy, hcong⟩
    have hyval : ((RayClass.localIntegralValue v y) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (x : F) := by
      exact congrArg Units.val hy
    rw [RayClass.localHigherUnitMap_eq_one_iff, local_pow_mem_iff] at hcong
    constructor
    · have hunit := (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mp
        y.property
      change Valued.v ((RayClass.localIntegralValue v y) : v.adicCompletion F) = 1 at hunit
      rwa [hyval, valuation_algebraMap] at hunit
    · change Valued.v (((RayClass.localIntegralValue v y) : v.adicCompletion F) - 1) ≤ _ at hcong
      rwa [hyval, ← map_one (algebraMap F (v.adicCompletion F)), ← map_sub,
        valuation_algebraMap] at hcong
  · rintro ⟨hx, hsub⟩
    let y : (v.adicCompletionIntegers F).units :=
      ⟨ClassFieldTheory.finitePlaceUnitEmbedding v x,
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mpr (by
          change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
          rw [valuation_algebraMap]
          exact hx)⟩
    refine ⟨y, rfl, ?_⟩
    rw [RayClass.localHigherUnitMap_eq_one_iff, local_pow_mem_iff]
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F) - 1) ≤ _
    rw [← map_one (algebraMap F (v.adicCompletion F)), ← map_sub,
      valuation_algebraMap]
    exact hsub

theorem finitePart_at_conjugate (m : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (RayArithmeticModulus.modulus M hM m).finitePart
      (HeightOneSpectrum.equivOfRingEquiv (RayArithmeticPlaces.integerConjugation M hM) v) =
      (RayArithmeticModulus.modulus M hM m).finitePart v := by
  simp only [RayArithmeticModulus.finitePart_apply]
  have hmap : (RayArithmeticModulus.finiteIdeal M hM m).map
      (RayArithmeticPlaces.integerConjugation M hM) =
      RayArithmeticModulus.finiteIdeal M hM m := by
    simp [RayArithmeticModulus.finiteIdeal, Ideal.map_span]
  have h := factorization_map (RayArithmeticPlaces.integerConjugation M hM) v
    (RayArithmeticModulus.finiteIdeal M hM m)
  rwa [hmap] at h

theorem finiteCongruent_conjugation (m : ℕ) (x : Kˣ) :
    RayArithmeticModulus.FiniteCongruent M hM m x →
      RayArithmeticModulus.FiniteCongruent M hM m
        (Units.mapEquiv (RayArithmeticPlaces.conjugation M hM).toRingEquiv.toMulEquiv x) := by
  intro hx
  refine ⟨?_, by simp [RayArithmeticModulus.finiteModulus]⟩
  intro v hv
  obtain ⟨w, rfl⟩ := (HeightOneSpectrum.equivOfRingEquiv
    (RayArithmeticPlaces.integerConjugation M hM)).surjective v
  have hw : w ∈ (RayArithmeticModulus.finiteModulus M hM m).finitePart.support := by
    simpa only [RayArithmeticModulus.finiteModulus, Finsupp.mem_support_iff,
      finitePart_at_conjugate] using hv
  have hlocal := (finiteUnit_mem_iff w _ x).mp (hx.1 w hw)
  rw [finiteUnit_mem_iff]
  change (HeightOneSpectrum.equivOfRingEquiv
      (RayArithmeticPlaces.integerConjugation M hM) w).valuation K
        (RayArithmeticPlaces.conjugation M hM x) = 1 ∧
    (HeightOneSpectrum.equivOfRingEquiv
      (RayArithmeticPlaces.integerConjugation M hM) w).valuation K
        (RayArithmeticPlaces.conjugation M hM x - 1) ≤ _
  rw [valuation_conjugation, ← map_one (RayArithmeticPlaces.conjugation M hM),
    ← map_sub, valuation_conjugation]
  simpa only [RayArithmeticModulus.finiteModulus, finitePart_at_conjugate] using hlocal

omit M hM in
theorem subgroup_map_eq_of_involutive {G : Type*} [Group G] (e : G ≃* G)
    (he : Function.Involutive e) (H : Subgroup G)
    (hH : ∀ x ∈ H, e x ∈ H) : H.map e.toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hH y hy
  · intro hx
    exact ⟨e x, hH x hx, he x⟩

omit M hM in
theorem ideal_map_isCoprime_iff {R : Type*} [CommRing R] (e : R ≃+* R)
    (a b : Ideal R) : IsCoprime (a.map e) (b.map e) ↔ IsCoprime a b := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup]
  constructor
  · intro h
    apply (idealMapEquiv e).injective
    exact h.trans (Ideal.map_top _).symm
  · intro h
    rw [h, Ideal.map_top]

end SICLean.L5.RayArithmeticConjugationAux
