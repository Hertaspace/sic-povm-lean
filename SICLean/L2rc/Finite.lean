import SICLean.L2rc.FiniteAux
import SICLean.L2rc.Inputs

set_option autoImplicit false

/-!
# Rank-r transport into the generic derivation of [RW26, Thm. 2]

The transport follows (4)--(7), then reflection and Fourier, then (36), (33),
and (31). The generic theorems give the corresponding steps for an arbitrary
finite group.
-/

noncomputable section

namespace SICLean.L2rc

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem originPlus_eq_generic_rw (d r : ℕ) [Fact (L2r.Admissible d r)] :
    originPlus d r = Generic.originPlus (RWGroup d r) := by
  simp only [originPlus, Generic.originPlus, card_RWGroup]

theorem originMinus_eq_generic_rw (d r : ℕ) [Fact (L2r.Admissible d r)] :
    originMinus d r = Generic.originMinus (RWGroup d r) := by
  simp only [originMinus, Generic.originMinus, card_RWGroup]

theorem originPlus_eq_generic (d r : ℕ) [Fact (L2r.Admissible d r)] :
    originPlus d r = Generic.originPlus (L2r.G d r) := by
  simp only [originPlus, Generic.originPlus, L2r.card_G]

theorem originMinus_eq_generic (d r : ℕ) [Fact (L2r.Admissible d r)] :
    originMinus d r = Generic.originMinus (L2r.G d r) := by
  simp only [originMinus, Generic.originMinus, L2r.card_G]

/-- The positive root is derived from (4) and the already defined η.
The downstream FQD origin value is not a new analytic assumption. -/
theorem originPlus_eq_originValue (d r : ℕ) [Fact (L2r.Admissible d r)] :
    originPlus d r = L2r.originValue d r := by
  have hplus := Generic.originPlus_quadratic (A := L2r.G d r)
  rw [← originPlus_eq_generic, ← sqrtOrder_eq_sqrtCard] at hplus
  have heta : 0 < L2r.eta d r :=
    lt_trans (by norm_num) (L2r.unit_properties (Fact.out : L2r.Admissible d r)).2.2
  have hv : L2r.originValue d r ≠ 0 := by
    unfold L2r.originValue
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr heta))
  have hn := (L2r.normalizer_identities (Fact.out : L2r.Admissible d r)).1
  rw [← L2r.sqrtCard_G d r, ← sqrtOrder_eq_sqrtCard] at hn
  have hm := congrArg (fun z : ℂ => z * L2r.originValue d r) hn
  simp only [sub_mul, inv_mul_cancel₀ hv] at hm
  have hval : L2r.originValue d r ^ 2 =
      sqrtOrder d r * L2r.originValue d r + 1 := by
    linear_combination hm
  have hplusR :
      Real.sqrt (((L2r.groupOrder d r : ℝ) + 2 +
        Real.sqrt ((L2r.groupOrder d r : ℝ) ^ 2 +
          4 * (L2r.groupOrder d r : ℝ))) / 2) ^ 2 =
      Real.sqrt (L2r.groupOrder d r : ℝ) *
        Real.sqrt (((L2r.groupOrder d r : ℝ) + 2 +
          Real.sqrt ((L2r.groupOrder d r : ℝ) ^ 2 +
            4 * (L2r.groupOrder d r : ℝ))) / 2) + 1 := by
    unfold originPlus sqrtOrder at hplus
    exact_mod_cast hplus
  have hvalR : Real.sqrt (L2r.eta d r) ^ 2 =
      Real.sqrt (L2r.groupOrder d r : ℝ) * Real.sqrt (L2r.eta d r) + 1 := by
    unfold L2r.originValue sqrtOrder at hval
    exact_mod_cast hval
  unfold originPlus L2r.originValue
  congr 1
  exact FiniteAux.nonneg_quadratic_unique _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hplusR hvalR

theorem originMinus_eq_inverse (d r : ℕ) [Fact (L2r.Admissible d r)] :
    originMinus d r = (originPlus d r)⁻¹ := by
  rw [originMinus_eq_generic, originPlus_eq_generic]
  exact Generic.originMinus_eq_inverse

theorem originPlus_quadratic (d r : ℕ) [Fact (L2r.Admissible d r)] :
    originPlus d r ^ 2 = sqrtOrder d r * originPlus d r + 1 := by
  rw [originPlus_eq_generic, sqrtOrder_eq_sqrtCard]
  exact Generic.originPlus_quadratic

variable {d r : ℕ} [Fact (L2r.Admissible d r)]
variable {Fplus Fminus : RWGroup d r → ℂ}

/-- Only the proved cardinality, polarization and normalization identities
separate the raw matrix statement from the generic finite-group statement. -/
theorem rw_theorem2Input (h : Theorem2Input d r Fplus Fminus) :
    Generic.Theorem2Input (RWGroup d r) (gaussian d r) Fplus Fminus := by
  refine
    { origin_plus := h.origin_plus.trans (originPlus_eq_generic_rw d r)
      origin_minus := h.origin_minus.trans (originMinus_eq_generic_rw d r)
      mixed_reflection := h.mixed_reflection
      fourier := ?_
      ratio_sum := ?_
      agree_off_zero := h.agree_off_zero }
  · obtain ⟨μ, hμ, hf⟩ := h.fourier
    refine ⟨μ, hμ, ?_⟩
    intro u
    simpa only [normalizedSum_eq_generic, pairing_eq_polarization] using hf u
  · intro u v huv
    simpa only [normalizedSum_eq_generic, pairing_eq_polarization] using
      h.ratio_sum u v huv

/-- Both branches are transported along the same already proved bijection. -/
theorem concrete_theorem2Input (h : Theorem2Input d r Fplus Fminus) :
    Generic.Theorem2Input (L2r.G d r) (L2r.gaussian d r)
      (concreteValues d r Fplus) (concreteValues d r Fminus) := by
  have hinj := (L2r.rwIndexMap_bijective d r).1
  have hzero : ∀ x : L2r.G d r, L2r.rwIndexMap d r x = 0 → x = 0 := by
    intro x hx
    apply hinj
    simpa only [map_zero] using hx
  refine
    { origin_plus := ?_
      origin_minus := ?_
      mixed_reflection := ?_
      fourier := ?_
      ratio_sum := ?_
      agree_off_zero := ?_ }
  · simpa only [concreteValues, Function.comp_apply, map_zero,
      ← originPlus_eq_generic] using h.origin_plus
  · simpa only [concreteValues, Function.comp_apply, map_zero,
      ← originMinus_eq_generic] using h.origin_minus
  · intro g
    simpa only [concreteValues, Function.comp_apply, map_neg, gaussian_rwIndexMap]
      using h.mixed_reflection (L2r.rwIndexMap d r g)
  · obtain ⟨μ, hμ, hf⟩ := h.fourier
    refine ⟨μ, hμ, ?_⟩
    intro g
    have he := hf (L2r.rwIndexMap d r g)
    rw [normalizedSum_toConcrete] at he
    simpa only [concreteValues, Function.comp_def, pairing_rwIndexMap] using he
  · intro u v huv
    have hne : (L2r.rwIndexMap d r u, L2r.rwIndexMap d r v) ≠ (0, 0) := by
      intro hh
      obtain ⟨hu, hv⟩ := Prod.mk.inj hh
      exact huv (Prod.ext (hzero u hu) (hzero v hv))
    have he := h.ratio_sum (L2r.rwIndexMap d r u) (L2r.rwIndexMap d r v) hne
    rw [normalizedSum_toConcrete] at he
    simpa only [concreteValues, Function.comp_def, map_add, pairing_rwIndexMap]
      using he
  · intro u hu
    exact h.agree_off_zero _ (fun h0 => hu (hzero u h0))

theorem concrete_origin (h : Theorem2Input d r Fplus Fminus) :
    concreteValues d r Fplus 0 = L2r.originValue d r := by
  change Fplus (L2r.rwIndexMap d r 0) = _
  rw [map_zero, h.origin_plus, originPlus_eq_originValue]

theorem special_values_ne_zero (h : Theorem2Input d r Fplus Fminus)
    (u : RWGroup d r) : Fplus u ≠ 0 ∧ Fminus u ≠ 0 := by
  exact Generic.special_values_ne_zero (rw_isMetricGaussian d r) (rw_theorem2Input h) u

theorem inverse_minus (h : Theorem2Input d r Fplus Fminus) (u : RWGroup d r) :
    (Fminus u)⁻¹ = gaussian d r u * Fplus (-u) := by
  exact Generic.inverse_minus (rw_isMetricGaussian d r) (rw_theorem2Input h) u

theorem concrete_reflection_all (h : Theorem2Input d r Fplus Fminus)
    (g : L2r.G d r) :
    concreteValues d r Fplus g * concreteValues d r Fplus (-g) * L2r.gaussian d r g =
      1 + L2b.sqrtCard (L2r.G d r) * concreteValues d r Fplus 0 *
        (if g = 0 then 1 else 0) := by
  have he := Generic.reflection_all (L2r.concrete_isMetricGaussian d r)
    (concrete_theorem2Input h) g
  by_cases hg : g = 0 <;> simpa only [if_pos, if_neg, hg] using he

theorem concrete_fourier_proportional (h : Theorem2Input d r Fplus Fminus)
    (g : L2r.G d r) :
    L2b.fourier (L2r.gaussian d r) (concreteValues d r Fplus) g =
      L2b.fourierScalar (L2r.gaussian d r) (concreteValues d r Fplus) *
        L2r.gaussian d r g * concreteValues d r Fplus g := by
  exact Generic.fourier_proportional (L2r.concrete_isMetricGaussian d r)
    (concrete_theorem2Input h) g

theorem concrete_fourierScalar_ne_zero (h : Theorem2Input d r Fplus Fminus) :
    L2b.fourierScalar (L2r.gaussian d r) (concreteValues d r Fplus) ≠ 0 := by
  exact Generic.fourierScalar_ne_zero (L2r.concrete_isMetricGaussian d r)
    (concrete_theorem2Input h)

/-- Full (36) in the concrete coordinates, with the double-delta term kept. -/
theorem concrete_pentagon36_of_theorem2 (h : Theorem2Input d r Fplus Fminus)
    (x y : L2r.G d r) :
    L2b.normalizedSum (fun t => concreteValues d r Fplus t * L2r.gaussian d r t *
      concreteValues d r Fplus (x - t) * L2b.metricPairing (L2r.gaussian d r) t y) =
      L2r.gaussian d r (x + y) * concreteValues d r Fplus (-x - y) *
        concreteValues d r Fplus x * concreteValues d r Fplus y -
      (L2r.groupOrder d r : ℂ) * concreteValues d r Fplus 0 *
        (if x = 0 ∧ y = 0 then 1 else 0) := by
  have he := Generic.pentagon36_of_theorem2 (L2r.concrete_isMetricGaussian d r)
    (concrete_theorem2Input h) x y
  by_cases hxy : x = 0 ∧ y = 0 <;>
    simpa only [L2r.card_G, if_pos, if_neg, hxy] using he

/-- (33) with C=-Ê(0), prior to the generic inverse Fourier step. -/
theorem concrete_transformed_pentagon_of_theorem2
    (h : Theorem2Input d r Fplus Fminus) (x w : L2r.G d r) :
    concreteValues d r Fplus x *
      L2b.fourier (L2r.gaussian d r) (concreteValues d r Fplus) (w - x) =
      (-L2b.fourier (L2r.gaussian d r) (concreteValues d r Fplus) 0) *
        L2b.sqrtCard (L2r.G d r) * (if w = 0 then 1 else 0) +
      L2b.fourier (L2r.gaussian d r) (concreteValues d r Fplus) w *
        L2b.fourier (L2r.gaussian d r)
          (L2b.pentagonKernel (L2r.gaussian d r) (concreteValues d r Fplus) x) w := by
  have he := Generic.transformed_pentagon_of_theorem2 (L2r.concrete_isMetricGaussian d r)
    (concrete_theorem2Input h) x w
  by_cases hw : w = 0 <;> simpa only [if_pos, if_neg, hw] using he

theorem concrete_pentagon_of_theorem2 (h : Theorem2Input d r Fplus Fminus) :
    L2b.Pentagon (L2r.gaussian d r) (concreteValues d r Fplus)
      (-L2b.fourier (L2r.gaussian d r) (concreteValues d r Fplus) 0) := by
  exact Generic.pentagon_of_theorem2 (L2r.concrete_isMetricGaussian d r)
    (concrete_theorem2Input h)

theorem isFiniteQuantumDilogarithm_of_theorem2 (h : Theorem2Input d r Fplus Fminus) :
    L2b.IsFiniteQuantumDilogarithm (L2r.gaussian d r) (concreteValues d r Fplus) := by
  exact Generic.isFiniteQuantumDilogarithm_of_theorem2 (L2r.concrete_isMetricGaussian d r)
    (concrete_theorem2Input h)

theorem concrete_epsilon_invariant (h : RWAnalyticInput d r Fplus Fminus)
    (g : L2r.G d r) :
    concreteValues d r Fplus g =
      concreteValues d r Fplus (L2r.epsilonAut d r g) := by
  change Fplus (L2r.rwIndexMap d r g) = Fplus (L2r.rwIndexMap d r (L2r.epsilonAut d r g))
  rw [← epsilonAction_rwIndexMap]
  exact h.epsilon_invariant _

end SICLean.L2rc
