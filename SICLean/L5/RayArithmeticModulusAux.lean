import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.LocalRing.Basic

set_option autoImplicit false

/-!
# Integral interpretation of finite ray congruences

This file supplies the local-to-global bridge for finite congruences. No arithmetic
property of the particular quadratic field is used.
-/

noncomputable section

open scoped NumberField WithZero
open NumberField IsDedekindDomain ClassFieldTheory

namespace SICLean.L5.RayArithmeticModulusAux

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Powers of the maximal ideal in the completed integers are the expected valuation balls. -/
theorem completionInteger_mem_maximalIdeal_pow_iff
    (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletionIntegers K) (n : ℕ) :
    x ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  let w : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  let π : v.adicCompletionIntegers K := algebraMap (𝓞 K) _ p
  have hπ : w (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (((algebraMap (𝓞 K) K p : K)) : v.adicCompletion K) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap, hp]
  have hgen : (Valuation.IsRankOneDiscrete.generator w : ℤᵐ⁰) =
      WithZero.exp (-1 : ℤ) := by
    rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      ⟨(π : v.adicCompletion K), hπ⟩]
    rfl
  have hπu : w.IsUniformizer (π : v.adicCompletion K) := by
    rw [Valuation.IsUniformizer.iff, hgen, hπ]
  have hmax : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {π} := hπu.is_generator
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hπpow : w (π : v.adicCompletion K) ^ n = WithZero.exp (-(n : ℤ)) := by
    rw [hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  constructor
  · rintro ⟨a, rfl⟩
    change w ((a : v.adicCompletion K) * (π : v.adicCompletion K) ^ n) ≤ _
    rw [map_mul, map_pow, hπpow]
    exact mul_le_of_le_one_left' a.property
  · intro hx
    let a : v.adicCompletion K := (x : v.adicCompletion K) / (π : v.adicCompletion K) ^ n
    have ha : w a ≤ 1 := by
      change w ((x : v.adicCompletion K) / (π : v.adicCompletion K) ^ n) ≤ 1
      rwa [map_div₀, map_pow, hπpow, div_le_one₀ (by simp)]
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    change a * (π : v.adicCompletion K) ^ n = (x : v.adicCompletion K)
    dsimp [a]
    rw [div_mul_cancel₀ _ (pow_ne_zero n hπu.ne_zero)]

/-- Embedding a global integer in the completed integers preserves membership in every power of the
corresponding prime ideal. -/
theorem algebraMap_mem_maximalIdeal_pow_iff
    (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (n : ℕ) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) a ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n ↔
      a ∈ v.asIdeal ^ n := by
  rw [completionInteger_mem_maximalIdeal_pow_iff]
  change Valued.v (((algebraMap (𝓞 K) K a : K)) : v.adicCompletion K) ≤ _ ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_le_pow_iff_mem]

/-- The integer represented by a unit of the local integer submonoid. -/
def localIntegralValue
    (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletionIntegers K).units) :
    v.adicCompletionIntegers K :=
  ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType z).1

/-- The defining higher-unit reduction map detects subtraction of one. -/
theorem higherUnitMap_eq_one_iff
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (z : (v.adicCompletionIntegers K).units) :
    rayLocalHigherUnitMap v n z = 1 ↔
      localIntegralValue v z - 1 ∈
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  rw [Units.ext_iff]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _

/-- At positive depth an integral representative belongs to the higher-unit group precisely when it
is one modulo the maximal ideal power. -/
theorem mem_higherUnitGroup_iff_sub_mem
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (x : (v.adicCompletion K)ˣ) (y : v.adicCompletionIntegers K)
    (hy : (y : v.adicCompletion K) = (x : v.adicCompletion K)) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      y - 1 ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    have hzsub := (higherUnitMap_eq_one_iff v n z).mp (MonoidHom.mem_ker.mp hz)
    have hzy : localIntegralValue v z = y := by
      apply Subtype.ext
      exact (congrArg Units.val hzx).trans hy.symm
    rwa [hzy] at hzsub
  · intro hsub
    have hsubmax : y - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
      (Ideal.pow_le_self hn.ne') hsub
    have hnon : 1 - y ∈ nonunits (v.adicCompletionIntegers K) := by
      apply (IsLocalRing.mem_maximalIdeal _).mp
      simpa only [neg_sub] using
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).neg_mem hsubmax
    obtain ⟨u, hu⟩ := IsLocalRing.isUnit_of_mem_nonunits_one_sub_self y hnon
    let z : (v.adicCompletionIntegers K).units :=
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm u
    apply Subgroup.mem_map.mpr
    refine ⟨z, MonoidHom.mem_ker.mpr ?_, ?_⟩
    · apply (higherUnitMap_eq_one_iff v n z).mpr
      simpa only [localIntegralValue, z, MulEquiv.apply_symm_apply, hu] using hsub
    · apply Units.ext
      change ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = _
      rw [hu]
      exact hy

/-- A positive-depth finite local congruence for a global integral element is membership of its
difference from one in the corresponding prime power. -/
theorem finitePlaceUnitEmbedding_mem_iff
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    finitePlaceUnitEmbedding v (Units.mk0 (a : K) ha) ∈ rayLocalHigherUnitGroup v n ↔
      a - 1 ∈ v.asIdeal ^ n := by
  rw [mem_higherUnitGroup_iff_sub_mem v n hn _
    (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) (by rfl)]
  rw [← map_one (algebraMap (𝓞 K) (v.adicCompletionIntegers K)), ← map_sub,
    algebraMap_mem_maximalIdeal_pow_iff]

/-- Finite congruence at a prescribed prime-power factorization is congruence in the product ideal.
This applies to every ideal represented by such a factorization and does not require a principal
generator. -/
theorem isRayCongruent_iff_sub_mem
    (m : RayClassModulus K) (hinfinite : m.infinitePart = ∅)
    (I : Ideal (𝓞 K))
    (hprod : ∏ v ∈ m.finitePart.support, v.asIdeal ^ m.finitePart v = I)
    (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    IsRayCongruent m (Units.mk0 (a : K) ha) ↔ a - 1 ∈ I := by
  classical
  have hinf :
      (m.finitePart.support.inf fun v => v.asIdeal ^ m.finitePart v) = I :=
    (HeightOneSpectrum.inf_pow_eq_prod m.finitePart.support
      (fun v => m.finitePart v) id (fun _ _ _ _ h => h)).trans hprod
  have hmem : a - 1 ∈ I ↔
      ∀ v ∈ m.finitePart.support, a - 1 ∈ v.asIdeal ^ m.finitePart v := by
    rw [← hinf, Finset.inf_eq_iInf]
    simp only [Submodule.mem_iInf]
  rw [hmem]
  constructor
  · intro h v hv
    exact (finitePlaceUnitEmbedding_mem_iff v (m.finitePart v)
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)) a ha).mp (h.1 v hv)
  · intro h
    constructor
    · intro v hv
      exact (finitePlaceUnitEmbedding_mem_iff v (m.finitePart v)
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)) a ha).mpr (h v hv)
    · intro v hv
      rw [hinfinite] at hv
      simp only [Finset.notMem_empty] at hv

end SICLean.L5.RayArithmeticModulusAux
