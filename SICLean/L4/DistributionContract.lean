import SICLean.L4.DistributionValues
import SICLean.L3.Algebraicity

set_option autoImplicit false

/-!
# Coefficients, extended valuations and the L3 contract

The coefficient field contains √N, Gaussians and κ, with no E values in its generators. Lattice
enumeration, finiteness modulo positive homothety and the actual Q2/Q3 equations are not asserted
here. The single IsSolution wrapper explicitly takes the remaining Q1--Q3 hypotheses. In particular
this file does not construct a full L2c/L2rc.RWAnalyticInput, or assert actual E algebraicity.

[RW26, p. 3, (5), (7), p. 14, Prop. 9] are background. The Q4 relation and its κ are formalized
here; cf. [RW26, p. 23, Thm. 11]. The generic valuation corollaries below are consequences obtained
from the exact root relation and the `SICLean.L3.ValuationSupport.value_pow_eq_one`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace SICLean.L4

universe u v w w'

variable {I : Type u} [Fintype I] {G : I → Type v}
variable [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]

/-- Actual complex coefficients for every order-two label. No arithmetic property is assumed in
this definition. -/
def distributionFamilyKappa (B : I → DistributionBasis)
    (target : ∀ i, L3.OrderTwo I G i → I) (i : I) (h : L3.OrderTwo I G i) : ℂ :=
  distributionKappa (B i) (B (target i h))

/-- Actual E coordinates through specified additive coordinate equivalences. -/
def distributionFamilyPoint (B : I → DistributionBasis)
    (label : ∀ i, G i ≃+ DistributionGroup (B i)) : L3.Coordinate I G → ℂ :=
  fun c => distributionValue (B c.1) (label c.1 c.2)

/-- Transport the actual natural projection. It is only a set map, as required by L3; hP is an
inclusion of explicit period-point subgroups. -/
def distributionFamilyProject (B : I → DistributionBasis)
    (label : ∀ i, G i ≃+ DistributionGroup (B i))
    (target : ∀ i, L3.OrderTwo I G i → I)
    (ρ : ∀ i, L3.OrderTwo I G i → ℝ × ℝ)
    (hP : ∀ i h, distributionPeriodPoints (B i) ≤
      (distributionPeriodPoints (B (target i h))).comap
        (distributionHomothety ((ρ i h).1⁻¹, (ρ i h).2⁻¹)))
    (i : I) (h : L3.OrderTwo I G i) (x : G i) : G (target i h) :=
  (label (target i h)).symm
    (distributionScaledProject (B i) (B (target i h)) (ρ i h) (hP i h) (label i x))

/-- The coefficient generators intentionally exclude all E coordinates. -/
def distributionCoefficientSet (N : ℕ) (gaussian : ∀ i, G i → ℂ)
    (B : I → DistributionBasis) (target : ∀ i, L3.OrderTwo I G i → I) : Set ℂ :=
  {(Real.sqrt (N : ℝ) : ℂ)} ∪
    Set.range (fun c : L3.Coordinate I G => gaussian c.1 c.2) ∪
    Set.range (fun c : (Σ i, L3.OrderTwo I G i) => distributionFamilyKappa B target c.1 c.2)

def distributionCoefficientField (N : ℕ) (gaussian : ∀ i, G i → ℂ)
    (B : I → DistributionBasis) (target : ∀ i, L3.OrderTwo I G i → I) :
    IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (distributionCoefficientSet N gaussian B target)

/-- Generator membership. [RW26, p. 3, (4)] supplies the radical background. -/
theorem distributionCoefficient_sqrt_mem (N : ℕ) (gaussian : ∀ i, G i → ℂ)
    (B : I → DistributionBasis) (target : ∀ i, L3.OrderTwo I G i → I) :
    (Real.sqrt (N : ℝ) : ℂ) ∈ distributionCoefficientField N gaussian B target := by
  exact IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inl rfl))

/-- Gaussian membership. [RW26, p. 2, (3)]. -/
theorem distributionCoefficient_gaussian_mem (N : ℕ) (gaussian : ∀ i, G i → ℂ)
    (B : I → DistributionBasis) (target : ∀ i, L3.OrderTwo I G i → I)
    (i : I) (x : G i) :
    gaussian i x ∈ distributionCoefficientField N gaussian B target := by
  exact IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inr ⟨⟨i, x⟩, rfl⟩))

/-- Exact actual κ membership. [RW26, p. 3, μ]. -/
theorem distributionCoefficient_kappa_mem (N : ℕ) (gaussian : ∀ i, G i → ℂ)
    (B : I → DistributionBasis) (target : ∀ i, L3.OrderTwo I G i → I)
    (i : I) (h : L3.OrderTwo I G i) :
    distributionFamilyKappa B target i h ∈ distributionCoefficientField N gaussian B target := by
  exact IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨⟨i, h⟩, rfl⟩)

/-- Concrete coefficient element. Its image is fixed before using another field's valuation; a
complex number is not passed directly to that valuation. -/
def distributionKappaCoefficient (N : ℕ) (gaussian : ∀ i, G i → ℂ)
    (B : I → DistributionBasis) (target : ∀ i, L3.OrderTwo I G i → I)
    (i : I) (h : L3.OrderTwo I G i) : distributionCoefficientField N gaussian B target :=
  ⟨distributionFamilyKappa B target i h,
    distributionCoefficient_kappa_mem N gaussian B target i h⟩

/-- All coefficients, not the unknown E-values, are algebraic. N>0 is essential for the Gaussian
exponent 2N. [RW26, p. 2, (3), p. 3, μ]. -/
theorem distributionCoefficientField_isAlgebraic (N : ℕ) (hN : 0 < N)
    (gaussian : ∀ i, G i → ℂ) (hgaussian : ∀ i x, gaussian i x ^ (2 * N) = 1)
    (B : I → DistributionBasis) (hB : ∀ i, (B i).Valid)
    (target : ∀ i, L3.OrderTwo I G i → I) :
    Algebra.IsAlgebraic ℚ (distributionCoefficientField N gaussian B target) := by
  have hgen : ∀ y ∈ distributionCoefficientSet N gaussian B target, IsAlgebraic ℚ y := by
    rintro y ((hy | hy) | hy)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      apply IsAlgebraic.of_pow (show 0 < 2 by norm_num)
      have hsq : (Real.sqrt (N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
        norm_num
      rw [hsq]
      exact isAlgebraic_natCast N
    · obtain ⟨⟨i, y⟩, rfl⟩ := hy
      apply IsAlgebraic.of_pow (show 0 < 2 * N by omega)
      rw [hgaussian i y]
      exact isAlgebraic_one
    · obtain ⟨⟨i, h⟩, rfl⟩ := hy
      simpa only [distributionFamilyKappa, distributionKappa] using
        etaKappa_isAlgebraic (B i).matrix (B (target i h)).matrix
          (hB i).1 (hB (target i h)).1
  refine ⟨fun x => ?_⟩
  have hx : IsAlgebraic ℚ (x : ℂ) :=
    IntermediateField.adjoin_induction (F := ℚ)
      (s := distributionCoefficientSet N gaussian B target)
      (p := fun y _ => IsAlgebraic ℚ y) (fun y hy => hgen y hy)
      (fun q => isAlgebraic_algebraMap q) (fun a b _ _ ha hb => ha.add hb)
      (fun a _ ha => ha.inv) (fun a b _ _ ha hb => ha.mul hb) x.property
  exact (IntermediateField.coe_isIntegral_iff
    (S := distributionCoefficientField N gaussian B target)).mp hx.isIntegral |>.isAlgebraic

/-- Pinned scalar image of the concrete coefficient lift. [RW26, p. 3, μ]. -/
theorem distributionKappaCoefficient_map (N : ℕ) (gaussian : ∀ i, G i → ℂ)
    (B : I → DistributionBasis) (target : ∀ i, L3.OrderTwo I G i → I)
    (i : I) (h : L3.OrderTwo I G i) :
    algebraMap (distributionCoefficientField N gaussian B target) ℂ
        (distributionKappaCoefficient N gaussian B target i h) =
      distributionFamilyKappa B target i h := by
  rfl

/-- Exact root relation descends along an injective scalar map. This is the contract needed to fill
FiniteSystem.multiplier_order. [RW26, p. 3, μ]. -/
theorem distributionKappa_lift_pow_twentyFour {k : Type w} [Field k] [Algebra k ℂ]
    (B C : DistributionBasis) (hB : B.Valid) (hC : C.Valid)
    (κ₀ : k) (hκ : algebraMap k ℂ κ₀ = distributionKappa B C) : κ₀ ^ 24 = 1 := by
  apply (algebraMap k ℂ).injective
  rw [map_pow, hκ, map_one, distributionKappa_pow_twentyFour B C hB hC]

/-- The lifted coefficient is nonzero. [RW26, p. 3, μ]. -/
theorem distributionKappa_lift_ne_zero {k : Type w} [Field k] [Algebra k ℂ]
    (B C : DistributionBasis) (hB : B.Valid) (hC : C.Valid)
    (κ₀ : k) (hκ : algebraMap k ℂ κ₀ = distributionKappa B C) : κ₀ ≠ 0 := by
  intro h
  have h0 : algebraMap k ℂ κ₀ = 0 := by rw [h, map_zero]
  rw [hκ] at h0
  exact distributionKappa_ne_zero B C hB hC h0

/-- Any extension and any additive valuation, in particular any normalized valuation above 2 on an
algebraically closed algebraic extension. No v(2)=1, algebraicity-of-E or archimedean modulus
premise is needed. The proof uses `SICLean.L3.ValuationSupport.value_pow_eq_one` with
n=24. [RW26, p. 3, μ]. -/
theorem distributionKappa_lift_valuation {k : Type w} [Field k] [Algebra k ℂ]
    (B C : DistributionBasis) (hB : B.Valid) (hC : C.Valid)
    (κ₀ : k) (hκ : algebraMap k ℂ κ₀ = distributionKappa B C)
    (L : Type w') [Field L] [Algebra k L] (v₂ : AddValuation L (WithTop ℝ)) :
    v₂ (algebraMap k L κ₀) = 0 := by
  have hpow : (algebraMap k L κ₀) ^ 24 = 1 := by
    rw [← map_pow, distributionKappa_lift_pow_twentyFour B C hB hC κ₀ hκ, map_one]
  exact SICLean.L3.ValuationSupport.value_pow_eq_one v₂ (by norm_num) hpow

/-- Algebraic-integer units follow from exact finite order, not from complex modulus 1. This is only
about κ and κ⁻¹. [RW26, p. 3, μ]. -/
theorem distributionKappa_integral_unit (B C : DistributionBasis)
    (hB : B.Valid) (hC : C.Valid) :
    IsIntegral ℤ (distributionKappa B C) ∧ IsIntegral ℤ (distributionKappa B C)⁻¹ := by
  constructor
  · apply IsIntegral.of_pow (show 0 < 24 by norm_num)
    rw [distributionKappa_pow_twentyFour B C hB hC]
    exact isIntegral_one
  · apply IsIntegral.of_pow (show 0 < 24 by norm_num)
    rw [inv_pow, distributionKappa_pow_twentyFour B C hB hC, inv_one]
    exact isIntegral_one

/-- The exact complex family coefficient order, including every 2-torsion label. [RW26, p. 3, μ]. -/
theorem distributionFamily_multiplier_order (B : I → DistributionBasis)
    (hB : ∀ i, (B i).Valid) (target : ∀ i, L3.OrderTwo I G i → I) :
    ∀ i h, distributionFamilyKappa B target i h ^ 24 = 1 := by
  intro i h
  simpa only [distributionFamilyKappa, distributionKappa] using
    distributionKappa_pow_twentyFour (B i) (B (target i h)) (hB i) (hB (target i h))

/-- The Q4 relation. Cross-family assumptions identify the common period and actual overlattice up
to positive homothety, as required for a finite family. They are not analytic equations; the inverse
homothety is part of the concrete map. [RW26, p. 14, Prop. 9]. -/
theorem distributionFamily_q4 (B : I → DistributionBasis) (hB : ∀ i, (B i).Valid)
    (label : ∀ i, G i ≃+ DistributionGroup (B i))
    (target : ∀ i, L3.OrderTwo I G i → I)
    (ρ : ∀ i, L3.OrderTwo I G i → ℝ × ℝ)
    (hρ : ∀ i h, 0 < (ρ i h).1 ∧ 0 < (ρ i h).2)
    (hε : ∀ i h, distributionPeriod (B (target i h)) = distributionPeriod (B i))
    (hJ : ∀ i h, distributionLattice (distributionScale (B (target i h)) (ρ i h)) =
      distributionOverlattice (B i) (label i h.val))
    (hP : ∀ i h, distributionPeriodPoints (B i) ≤
      (distributionPeriodPoints (B (target i h))).comap
        (distributionHomothety ((ρ i h).1⁻¹, (ρ i h).2⁻¹))) :
    ∀ i (h : L3.OrderTwo I G i) (x : G i),
      distributionFamilyPoint B label ⟨i, x⟩ *
          distributionFamilyPoint B label ⟨i, x + h.val⟩ =
        distributionFamilyKappa B target i h *
          distributionFamilyPoint B label
            ⟨target i h, distributionFamilyProject B label target ρ hP i h x⟩ := by
  intro i h x
  have hh : label i h.val ≠ 0 ∧ label i h.val + label i h.val = 0 := by
    constructor
    · intro he
      exact h.2.1 ((label i).injective (by simpa using he))
    · rw [← (label i).map_add, h.2.2, map_zero]
  have hmain := distributionValue_distribution_scaled (B i) (B (target i h))
    (hB i) (hB (target i h)) (label i h.val) hh (ρ i h) (hρ i h)
    (hε i h) (hJ i h) (hP i h) (label i x)
  rw [← (label i).map_add] at hmain
  simpa [distributionFamilyPoint, distributionFamilyKappa, distributionFamilyProject]
    using hmain

/-- Explicit arithmetic dependence of the exceptional coordinate. [RW26, p. 3, (4)]. -/
theorem distributionFamily_orderTwo_value (B : I → DistributionBasis)
    (hB : ∀ i, (B i).Valid) (label : ∀ i, G i ≃+ DistributionGroup (B i))
    (target : ∀ i, L3.OrderTwo I G i → I)
    (ρ : ∀ i, L3.OrderTwo I G i → ℝ × ℝ)
    (hρ : ∀ i h, 0 < (ρ i h).1 ∧ 0 < (ρ i h).2)
    (hε : ∀ i h, distributionPeriod (B (target i h)) = distributionPeriod (B i))
    (hJ : ∀ i h, distributionLattice (distributionScale (B (target i h)) (ρ i h)) =
      distributionOverlattice (B i) (label i h.val)) :
    ∀ i (h : L3.OrderTwo I G i),
      distributionFamilyPoint B label ⟨i, h.val⟩ = distributionFamilyKappa B target i h := by
  intro i h
  have hh : label i h.val ≠ 0 ∧ label i h.val + label i h.val = 0 := by
    constructor
    · intro he
      exact h.2.1 ((label i).injective (by simpa using he))
    · rw [← (label i).map_add, h.2.2, map_zero]
  have hsc := distributionScale_valid (B (target i h)) (hB (target i h)) (ρ i h) (hρ i h)
  have hmain := distributionValue_orderTwo (B i) (distributionScale (B (target i h)) (ρ i h))
    (hB i) hsc.1 (label i h.val) hh (hsc.2.1.trans (hε i h)) (hJ i h)
  simpa [distributionFamilyPoint, distributionFamilyKappa, distributionKappa, distributionScale]
    using hmain

/-- Q4 is supplied by this block. Actual Q1, Q2 (reflection (5)), and Q3 (from (5), (7)) are
explicit premises. This does not assert their validity, any actual IsSolution, or E algebraicity.
[RW26, p. 3, (5), (7)]. No Fourier identity and no appeal to [RW26, Prop. 8] is required. -/
theorem distributionFamily_isSolution_of_remaining_equations
    {k : Type w} [Field k] [Algebra k ℂ] (D : L3.FiniteSystem I G k)
    (B : I → DistributionBasis) (hB : ∀ i, (B i).Valid)
    (label : ∀ i, G i ≃+ DistributionGroup (B i))
    (ρ : ∀ i, L3.OrderTwo I G i → ℝ × ℝ)
    (hρ : ∀ i h, 0 < (ρ i h).1 ∧ 0 < (ρ i h).2)
    (hε : ∀ i h, distributionPeriod (B (D.target i h)) = distributionPeriod (B i))
    (hJ : ∀ i h, distributionLattice (distributionScale (B (D.target i h)) (ρ i h)) =
      distributionOverlattice (B i) (label i h.val))
    (hP : ∀ i h, distributionPeriodPoints (B i) ≤
      (distributionPeriodPoints (B (D.target i h))).comap
        (distributionHomothety ((ρ i h).1⁻¹, (ρ i h).2⁻¹)))
    (hproject : ∀ i h, D.project i h = distributionFamilyProject B label D.target ρ hP i h)
    (hκ : ∀ i h, algebraMap k ℂ (D.multiplier i h) =
      distributionFamilyKappa B D.target i h)
    (hq1 : ∀ i, distributionFamilyPoint B label ⟨i, 0⟩ ^ 2 -
      algebraMap k ℂ D.sqrtN * distributionFamilyPoint B label ⟨i, 0⟩ - 1 = 0)
    (hq2 : ∀ i (x : G i), x ≠ 0 →
      distributionFamilyPoint B label ⟨i, x⟩ * distributionFamilyPoint B label ⟨i, -x⟩ =
        algebraMap k ℂ (D.gaussian i x)⁻¹)
    (hq3 : ∀ i (x : G i), x ≠ 0 →
      algebraMap k ℂ D.sqrtN * distributionFamilyPoint B label ⟨i, x + x⟩ =
        distributionFamilyPoint B label ⟨i, x⟩ ^ 2 * ∑ s : G i,
          algebraMap k ℂ (D.gaussian i s) * distributionFamilyPoint B label ⟨i, x + s⟩ *
            distributionFamilyPoint B label ⟨i, x - s⟩) :
    D.IsSolution ℂ (distributionFamilyPoint B label) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hq1
  · intro i x hx
    exact hq2 i x hx
  · intro i x hx
    exact hq3 i x hx
  · intro i h x
    have hq := distributionFamily_q4 B hB label D.target ρ hρ hε hJ hP i h x
    rw [hκ i h, congrFun (hproject i h) x]
    exact hq

#print distributionCoefficientSet
#print distributionFamilyProject
#check @L3.FiniteSystem.multiplier_order
#check @L3.FiniteSystem.IsSolution
#check @L3.ValuationSupport.value_pow_eq_one
#check @L3.FiniteSystem.solution_isAlgebraic
#check @L3.FiniteSystem.solution_valuation_eq_zero
#print distributionFamily_isSolution_of_remaining_equations

end SICLean.L4
