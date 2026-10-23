import SICLean.L5.ClassFieldModulus
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.GaloisAction
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete

set_option autoImplicit false

/-! Transport lemmas for ideals and ray congruences. -/
noncomputable section
open scoped NumberField MatrixGroups Classical nonZeroDivisors
open NumberField IsDedekindDomain ClassFieldTheory

namespace SICLean.L5.ClassFieldIdealActionAux

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
lemma primeEquiv_asIdeal (e : 𝓞 K ≃+* 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (HeightOneSpectrum.equivOfRingEquiv e v).asIdeal = v.asIdeal.map e := by
  ext x
  exact Ideal.symm_apply_mem_of_equiv_iff

lemma ideal_count_map (e : 𝓞 K ≃+* 𝓞 K) (v : HeightOneSpectrum (𝓞 K))
    (I : Ideal (𝓞 K)) :
    (Associates.mk (v.asIdeal.map e)).count (Associates.mk (I.map e)).factors =
      (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  by_cases hI : I = 0
  · subst I
    simp only [Ideal.zero_eq_bot, Ideal.map_bot]
    change (Associates.mk (v.asIdeal.map e)).count (Associates.mk (0 : Ideal (𝓞 K))).factors =
      (Associates.mk v.asIdeal).count (Associates.mk (0 : Ideal (𝓞 K))).factors
    rw [Associates.mk_zero, Associates.factors_zero]
    simp only [Associates.count]
    split_ifs <;> rfl
  have hIe : I.map e ≠ 0 :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr hI
  have hp := (HeightOneSpectrum.equivOfRingEquiv e v).associates_irreducible
  rw [primeEquiv_asIdeal] at hp
  have hle : ∀ k : ℕ,
      k ≤ (Associates.mk (v.asIdeal.map e)).count (Associates.mk (I.map e)).factors ↔
        k ≤ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    intro k
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hIe) hp,
      ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI) v.associates_irreducible,
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd, ← Ideal.map_pow,
      Ideal.dvd_iff_le, Ideal.dvd_iff_le]
    exact e.idealComapOrderIso.symm.le_iff_le
  exact Nat.le_antisymm ((hle _).mp le_rfl) ((hle _).mpr le_rfl)

lemma fractionRing_map (e : K ≃ₐ[ℚ] K) :
    IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
      (RingOfIntegers.mapRingEquiv e.toRingEquiv) = e.toRingEquiv := by
  have h : (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
      (RingOfIntegers.mapRingEquiv e.toRingEquiv)).toRingHom = e.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 K)
    intro x
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  exact RingEquiv.ext (RingHom.congr_fun h)

lemma fractional_map_coe (e : K ≃ₐ[ℚ] K) (I : Ideal (𝓞 K)) :
    FractionalIdeal.ringEquivOfRingEquiv K K (RingOfIntegers.mapRingEquiv e.toRingEquiv)
      (I : FractionalIdeal (𝓞 K)⁰ K) =
        (I.map (RingOfIntegers.mapRingEquiv e.toRingEquiv) :
          FractionalIdeal (𝓞 K)⁰ K) := by
  ext x
  simp only [FractionalIdeal.ringEquivOfRingEquiv_apply, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e.toRingEquiv r,
      Ideal.mem_map_of_mem _ hr,
      (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap K K _ r).symm⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (RingOfIntegers.mapRingEquiv e.toRingEquiv).surjective).mp hr
    exact ⟨algebraMap (𝓞 K) K s, ⟨s, hs, rfl⟩,
      IsFractionRing.semilinearEquivOfRingEquiv_algebraMap K K _ s⟩

lemma fractional_count_map (e : K ≃ₐ[ℚ] K) (v : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.count K
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e.toRingEquiv) v)
      (FractionalIdeal.ringEquivOfRingEquiv K K
        (RingOfIntegers.mapRingEquiv e.toRingEquiv) I) = FractionalIdeal.count K v I := by
  let E := FractionalIdeal.ringEquivOfRingEquiv K K
    (RingOfIntegers.mapRingEquiv e.toRingEquiv)
  by_cases hI : I = 0
  · rw [hI, map_zero, FractionalIdeal.count_zero, FractionalIdeal.count_zero]
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hEI : E I ≠ 0 := (map_ne_zero E).mpr hI
  have hEIJ : E I =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv e.toRingEquiv a))⁻¹ *
      (J.map (RingOfIntegers.mapRingEquiv e.toRingEquiv) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hIJ, map_mul, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton,
      fractionRing_map, map_inv₀, fractional_map_coe]
    rfl
  rw [FractionalIdeal.count_well_defined K _ hEI hEIJ,
    FractionalIdeal.count_well_defined K _ hI hIJ, primeEquiv_asIdeal,
    ideal_count_map]
  congr 1
  have hspan : Ideal.span ({RingOfIntegers.mapRingEquiv e.toRingEquiv a} : Set _) =
      (Ideal.span ({a} : Set _)).map (RingOfIntegers.mapRingEquiv e.toRingEquiv) := by
    simp [Ideal.map_span]
  rw [hspan, ideal_count_map]

lemma local_mem_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      ∃ y : (v.adicCompletionIntegers K)ˣ,
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm y :
          (v.adicCompletion K)ˣ) = x ∧
        (y : v.adicCompletionIntegers K) - 1 ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
  rw [rayLocalHigherUnitGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    let z := (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y
    refine ⟨z, congrArg Subtype.val
      ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm_apply_apply y), ?_⟩
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem (I :=
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) _).mp
    exact congrArg Units.val hy
  · rintro ⟨y, rfl, hy⟩
    refine ⟨(v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm y, ?_, rfl⟩
    apply Units.ext
    exact (Ideal.Quotient.mk_eq_one_iff_sub_mem (I :=
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) _).mpr hy

lemma local_pow_mem_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  let V : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial V
  have hval : V (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [hπ.val, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)]
    rfl
  refine (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
    V (x := (show V.valuationSubring from x)) hπ n).trans ?_
  change V (x : v.adicCompletion K) ≤ V ((π : v.adicCompletion K) ^ n) ↔ _
  rw [map_pow, hval, ← WithZero.exp_nsmul]
  simp [V]

lemma local_mem_valuation_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      Valued.v (x : v.adicCompletion K) = 1 ∧
        Valued.v ((x : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [local_mem_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩
    constructor
    · exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := v)).mp
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm y).property
    · simpa using (local_pow_mem_iff v n _).mp hy
  · rintro ⟨hx, hsub⟩
    let z : (v.adicCompletionIntegers K).units :=
      ⟨x, (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := v)).mpr hx⟩
    let y := (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType z
    refine ⟨y, congrArg Subtype.val
      ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm_apply_apply z), ?_⟩
    exact (local_pow_mem_iff v n _).mpr hsub

lemma finite_congr_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : Kˣ) :
    finitePlaceUnitEmbedding v x ∈ rayLocalHigherUnitGroup v n ↔
      v.valuation K (x : K) = 1 ∧
        v.valuation K ((x : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [local_mem_valuation_iff]
  change Valued.v (algebraMap K (v.adicCompletion K) (x : K)) = 1 ∧
      Valued.v ((algebraMap K (v.adicCompletion K) (x : K)) - 1) ≤ _ ↔ _
  have hsub : (algebraMap K (v.adicCompletion K) (x : K)) - 1 =
      algebraMap K (v.adicCompletion K) ((x : K) - 1) := by simp
  have hv (z : K) : Valued.v (algebraMap K (v.adicCompletion K) z) =
      v.valuation K z := by
    change Valued.v (z : v.adicCompletion K) = v.valuation K z
    exact v.valuedAdicCompletion_eq_valuation' z
  rw [hsub, hv, hv]

lemma finite_congr_map (e : K ≃ₐ[ℚ] K) (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (x : Kˣ) :
    finitePlaceUnitEmbedding
        (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e.toRingEquiv) v)
        (Units.mapEquiv e.toMulEquiv x) ∈
      rayLocalHigherUnitGroup
        (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e.toRingEquiv) v) n ↔
      finitePlaceUnitEmbedding v x ∈ rayLocalHigherUnitGroup v n := by
  rw [finite_congr_iff, finite_congr_iff]
  change (finitePlaceEquiv ℚ K e v).valuation K (e (x : K)) = 1 ∧
      (finitePlaceEquiv ℚ K e v).valuation K (e (x : K) - 1) ≤ _ ↔ _
  have hsub : e ((x : K) - 1) = e (x : K) - 1 := by simp
  rw [← hsub, valuation_finitePlaceEquiv, valuation_finitePlaceEquiv]

lemma fractional_map_principal (e : K ≃ₐ[ℚ] K) (x : Kˣ) :
    Units.mapEquiv
        (FractionalIdeal.ringEquivOfRingEquiv K K
          (RingOfIntegers.mapRingEquiv e.toRingEquiv)).toMulEquiv
        (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 K) K (Units.mapEquiv e.toMulEquiv x) := by
  apply Units.ext
  rw [Units.coe_mapEquiv, coe_toPrincipalIdeal, coe_toPrincipalIdeal]
  change FractionalIdeal.ringEquivOfRingEquiv K K
      (RingOfIntegers.mapRingEquiv e.toRingEquiv)
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (e (x : K))
  rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton, fractionRing_map]
  rfl

lemma fractional_map_symm (e : K ≃ₐ[ℚ] K) (a : NumberFieldFractionalIdealGroup K) :
    Units.mapEquiv
        (FractionalIdeal.ringEquivOfRingEquiv K K
          (RingOfIntegers.mapRingEquiv e.symm.toRingEquiv)).toMulEquiv
      (Units.mapEquiv
        (FractionalIdeal.ringEquivOfRingEquiv K K
          (RingOfIntegers.mapRingEquiv e.toRingEquiv)).toMulEquiv a) = a := by
  apply Units.ext
  change FractionalIdeal.ringEquivOfRingEquiv K K
      (RingOfIntegers.mapRingEquiv e.symm.toRingEquiv)
      (FractionalIdeal.ringEquivOfRingEquiv K K
        (RingOfIntegers.mapRingEquiv e.toRingEquiv) (a : FractionalIdeal _ _)) = _
  have he : RingOfIntegers.mapRingEquiv e.symm.toRingEquiv =
      (RingOfIntegers.mapRingEquiv e.toRingEquiv).symm := rfl
  rw [he, ← FractionalIdeal.ringEquivOfRingEquiv_symm_eq]
  exact RingEquiv.symm_apply_apply _ _

lemma realEmbedding_cases (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (f : ClassFieldModulus.Base M hM →+* ℝ) :
    f = ClassFieldModulus.realEmbedding M hM 0 ∨
      f = ClassFieldModulus.realEmbedding M hM 1 := by
  let φ := Complex.ofRealHom.comp f
  have hφ : NumberField.ComplexEmbedding.IsReal φ := by
    apply NumberField.ComplexEmbedding.isReal_iff.mpr
    ext x
    simp [φ, NumberField.ComplexEmbedding.conjugate_coe_eq]
  let w : RayClassRealPlace (ClassFieldModulus.Base M hM) :=
    ⟨InfinitePlace.mk φ, φ, hφ, rfl⟩
  have hw : w.1.embedding_of_isReal w.2 = f := by
    ext x
    apply Complex.ofReal_injective
    rw [InfinitePlace.embedding_of_isReal_apply,
      InfinitePlace.embedding_mk_eq_of_isReal hφ]
    rfl
  rcases ClassFieldModulus.realPlace_exhaustive M hM w with h | h
  · left
    simpa only [h, ClassFieldModulus.realPlace_embedding] using hw.symm
  · right
    simpa only [h, ClassFieldModulus.realPlace_embedding] using hw.symm

lemma realEmbedding_ne (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    ClassFieldModulus.realEmbedding M hM 0 ≠ ClassFieldModulus.realEmbedding M hM 1 := by
  intro h
  apply ClassFieldModulus.realPlace_ne M hM
  apply Subtype.ext
  change InfinitePlace.mk (Complex.ofRealHom.comp (ClassFieldModulus.realEmbedding M hM 0)) =
    InfinitePlace.mk (Complex.ofRealHom.comp (ClassFieldModulus.realEmbedding M hM 1))
  rw [h]

end SICLean.L5.ClassFieldIdealActionAux
