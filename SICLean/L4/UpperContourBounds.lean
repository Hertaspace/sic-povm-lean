import SICLean.L4.UpperContourShifts
import SICLean.L4.UpperContourBoundsAux

set_option autoImplicit false

/-!
# Template estimates and the discrete negative quadratic

Template and discrete-decay theorems. Constants on a compact
parameter set are chosen before x,m,z,j,k. The single-function bound retains the actual |Q|
and the integer triangular exponent; a separate common majorant permits
uniform summation. No uniformity at Im τ=0 is asserted.

[RW26, pp. 28--29].
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContour

def productLower (r q : ℝ) : ℝ := ∏' ν : ℕ, (1 - r * q ^ ν)
def productUpper (D q : ℝ) : ℝ := ∏' ν : ℕ, (1 + D * q ^ ν)

/-- Exactly D^(ck)|Q|^(ck(ck+1)/2), not an informal O-symbol. -/
def quadraticWeight (c : ℕ) (D Q : ℝ) (k : ℕ) : ℝ :=
  D ^ (c * k) * Q ^ triangular (c * k)

/--
Strictly positive infinite product; [RW26, pp. 28--29].
-/
theorem productLower_pos (r q : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < productLower r q := by
  exact UpperContourBoundsAux.productLower_pos r q hr0 hr1 hq0 hq1

/--
Every finite denominator length has the same lower bound; [RW26, pp. 28--29].
-/
theorem finite_product_lower (u q : ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq1 : ‖q‖ < 1) (hu : ‖u‖ ≤ r) (N : ℕ) :
    productLower r ‖q‖ ≤ ‖qPochhammerNat u q N‖ := by
  exact UpperContourBoundsAux.finite_product_lower u q r hr0 hr1 hq1 hu N

/--
Positive finite common upper-product constant; [RW26, pp. 28--29].
-/
theorem productUpper_pos (D q : ℝ) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < productUpper D q := by
  exact UpperContourBoundsAux.productUpper_pos D q hD hq0 hq1

/--
Numerator arguments need only be bounded, not <1; [RW26, pp. 28--29].
-/
theorem finite_product_upper (v q : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hq1 : ‖q‖ < 1) (hv : ‖v‖ ≤ D) (N : ℕ) :
    ‖qPochhammerNat v q N‖ ≤ productUpper D ‖q‖ := by
  exact UpperContourBoundsAux.finite_product_upper v q D hD hq1 hv N

/--
Exact discrete quadratic, with the real coefficients visible; [RW26, pp. 28--29].
-/
theorem quadratic_log_exact (c k : ℕ) (D Q : ℝ) (hD : 0 < D) (hQ : 0 < Q) :
    Real.log (quadraticWeight c D Q k) =
      ((c : ℝ) ^ 2 / 2 * Real.log Q) * (k : ℝ) ^ 2 +
        ((c : ℝ) * Real.log D + (c : ℝ) / 2 * Real.log Q) * (k : ℝ) := by
  have ht : (2 : ℝ) * (triangular (c * k) : ℝ) =
      (c : ℝ) * (k : ℝ) * ((c : ℝ) * (k : ℝ) + 1) := by
    exact_mod_cast triangular_twice (c * k)
  have ht' : (triangular (c * k) : ℝ) =
      (c : ℝ) * (k : ℝ) * ((c : ℝ) * (k : ℝ) + 1) / 2 := by linarith
  unfold quadraticWeight
  rw [Real.log_mul (pow_pos hD _).ne' (pow_pos hQ _).ne', Real.log_pow,
    Real.log_pow, ht']
  push_cast
  ring

/--
The coefficient of k² is strictly negative, independently of D; [RW26, pp. 28--29].
-/
theorem quadratic_coefficient_neg (c : ℕ) (hc : 0 < c) (Q : ℝ)
    (hQ0 : 0 < Q) (hQ1 : Q < 1) : (c : ℝ) ^ 2 / 2 * Real.log Q < 0 := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  exact mul_neg_of_pos_of_neg (by positivity) (Real.log_neg hQ0 hQ1)

/--
The discrete Gaussian is summable for every positive D; [RW26, pp. 28--29].
-/
theorem quadratic_summable (c : ℕ) (hc : 0 < c) (D Q : ℝ)
    (hD : 0 < D) (hQ0 : 0 < Q) (hQ1 : Q < 1) :
    Summable (quadraticWeight c D Q) := by
  let a : ℝ := (c : ℝ) ^ 2 / 2 * Real.log Q
  let b : ℝ := (c : ℝ) * Real.log D + (c : ℝ) / 2 * Real.log Q
  have ha : a < 0 := quadratic_coefficient_neg c hc Q hQ0 hQ1
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((b + 1) / (-a))
  have hN' : b + 1 ≤ (-a) * (N : ℝ) := by
    have := (div_lt_iff₀ (neg_pos.mpr ha)).mp hN
    nlinarith
  refine Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hbk : b + 1 ≤ (-a) * (k : ℝ) := by nlinarith
  have hpoly : a * (k : ℝ) ^ 2 + b * (k : ℝ) ≤ -(k : ℝ) := by
    have := mul_le_mul_of_nonneg_right hbk (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith
  have hw : 0 < quadraticWeight c D Q k := by
    unfold quadraticWeight
    positivity
  rw [Real.norm_eq_abs, abs_of_pos hw, ← Real.exp_log hw, quadratic_log_exact c k D Q hD hQ0]
  exact Real.exp_le_exp.mpr hpoly

/--
Decay along integer truncations; [RW26, pp. 28--29].
-/
theorem quadratic_tendsto_zero (c : ℕ) (hc : 0 < c) (D Q : ℝ)
    (hD : 0 < D) (hQ0 : 0 < Q) (hQ1 : Q < 1) :
    Tendsto (quadraticWeight c D Q) atTop (𝓝 0) := by
  exact (quadratic_summable c hc D Q hD hQ0 hQ1).tendsto_atTop_zero

/--
Fixed parameters permit the exact rates |A|^c, |B|^c; [RW26, pp. 28--29].
All residue classes use the same two constants.
-/
theorem fixed_template_bounds (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ M₀ D : ℝ, 0 < M₀ ∧ 0 < D ∧
      ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ z ∈ UpperWindow.templates M (m : ℤ) n δ x.1, ∀ j k : ℕ,
        ‖kernel .ratio M (m : ℤ) n h ℓ p x (translate M x.1 z j k)‖ ≤
          M₀ * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
            (‖UpperWindow.B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat) ^ k ∧
        ‖kernel .single M (m : ℤ) n h ℓ p x (translate M x.1 z j k)‖ ≤
          M₀ * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
            quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k := by
  obtain ⟨M₀, D, hM₀, hD, hbounds⟩ :=
    UpperContourBoundsAux.compact_exact_template_bounds M h ℓ p n ψ σ ρ δ hc
      {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
  exact ⟨M₀, D, hM₀, hD, hbounds x (Set.mem_singleton x)⟩

/--
Main template export. Uses compact_common_margins; all constants
precede all varying points; [RW26, pp. 28--29].
-/
theorem compact_template_bounds (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ M₀ D rA rB : ℝ, 0 < M₀ ∧ 0 < D ∧ 0 < rA ∧ rA < 1 ∧ 0 < rB ∧ rB < 1 ∧
      ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ z ∈ UpperWindow.templates M (m : ℤ) n δ x.1, ∀ j k : ℕ,
        ‖kernel .ratio M (m : ℤ) n h ℓ p x (translate M x.1 z j k)‖ ≤ M₀ * rA ^ j * rB ^ k ∧
        ‖kernel .single M (m : ℤ) n h ℓ p x (translate M x.1 z j k)‖ ≤
          M₀ * rA ^ j * quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k := by
  obtain ⟨M₀, D, hM₀, hD, hbounds⟩ :=
    UpperContourBoundsAux.compact_exact_template_bounds M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨rA, rB, hrA0, hrA1, hrB0, hrB1, hrates⟩ :=
    UpperWindow.compact_AB_rates M h ℓ p ψ σ ρ δ hc K hK hKU
  refine ⟨M₀, D, rA, rB, hM₀, hD, hrA0, hrA1, hrB0, hrB1, ?_⟩
  intro x hx m hm z hz j k
  have hAj := pow_le_pow_left₀ (by positivity) (hrates x hx).1 j
  have hBk := pow_le_pow_left₀ (by positivity) (hrates x hx).2 k
  constructor
  · refine (hbounds x hx m hm z hz j k).1.trans ?_
    gcongr
  · refine (hbounds x hx m hm z hz j k).2.trans ?_
    change M₀ * (‖UpperWindow.A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat) ^ j *
      quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k ≤ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAj hM₀.le)
      (by unfold quadraticWeight; positivity)

/--
A common summable majorant for any chosen D; discrete k² coefficient
is bounded above by -a on K; [RW26, pp. 28--29].
-/
theorem compact_quadratic_domination (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKU : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ)
    (D : ℝ) (hD : 0 < D) :
    ∃ Q₀ a : ℝ, 0 < Q₀ ∧ Q₀ < 1 ∧ 0 < a ∧
      Summable (quadraticWeight (M 1 0).toNat D Q₀) ∧
      ∀ x ∈ K, ((M 1 0 : ℝ) ^ 2 / 2) * Real.log ‖e (etaMobius M x.1)‖ ≤ -a ∧
        ∀ k : ℕ, quadraticWeight (M 1 0).toNat D ‖e (etaMobius M x.1)‖ k ≤
          quadraticWeight (M 1 0).toNat D Q₀ k := by
  obtain ⟨η, R, Q₀, hη, hR, hQ₀, hQ₁, hparameters⟩ :=
    UpperWindow.compact_parameter_bounds M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨a, ha, hmargin⟩ :=
    UpperWindow.compact_quadratic_margin M h ℓ p ψ σ ρ δ hc K hK hKU
  have hM : 0 < M 1 0 := hc.1
  have hcNat : 0 < (M 1 0).toNat := by omega
  refine ⟨Q₀, a, hQ₀, hQ₁, ha,
    quadratic_summable (M 1 0).toNat hcNat D Q₀ hD hQ₀ hQ₁, ?_⟩
  intro x hx
  refine ⟨(hmargin x hx).1, ?_⟩
  intro k
  have hQx : ‖e (etaMobius M x.1)‖ ≤ Q₀ :=
    (hparameters x hx).2.2.2.2.2.2.2.2.2.1
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hQx _) (pow_nonneg hD.le _)

/--
Uniform summation uses this tail, not just pointwise decay of its terms; [RW26, pp. 28--29].
-/
theorem quadratic_tail_tendsto_zero (c : ℕ) (hc : 0 < c) (D Q : ℝ)
    (hD : 0 < D) (hQ0 : 0 < Q) (hQ1 : Q < 1) :
    Tendsto (fun R : ℕ => ∑' k : ℕ, quadraticWeight c D Q (R + k)) atTop (𝓝 0) := by
  simpa only [Nat.add_comm] using tendsto_sum_nat_add (quadraticWeight c D Q)

#print quadraticWeight
#check quadratic_log_exact
#check compact_template_bounds
#check compact_quadratic_domination

end SICLean.L4.UpperContour
