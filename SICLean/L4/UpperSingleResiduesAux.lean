import SICLean.L4.UpperResidueParameters
import SICLean.L4.UpperResidueIndex
import SICLean.L4.UpperWindowCompactAux
import SICLean.L4.UpperContourClosure

set_option autoImplicit false

/-!
# Auxiliary proofs for the direct single-function residue sum

The compact estimates use the two strict bounds |A|<1 and |Q*C|<1 in the
initial upper window. The local calculation removes one vanishing Q factor,
uses the exponential divided difference, and retains its derivative 1/T.
All comparisons at a pole are punctured; no center value is assigned; [RW26, p. 28, p. 29, (55),
(56)] (residue method).
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperSingleResiduesAux
open UpperResidueParameters UpperResidueIndex UpperWindow.CompactAux

/-- A real radius majorizes every diagonal finite-product denominator. -/
lemma diagonal_norm_lower (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : ℂ) (hq : ‖q‖ ≤ r) (n : ℕ) :
    ‖qPochhammerNat (r : ℂ) (r : ℂ) n‖ ≤ ‖qPochhammerNat q q n‖ := by
  induction n with
  | zero => simp [qPochhammerNat_zero]
  | succ n ih =>
    rw [qPochhammerNat_succ, qPochhammerNat_succ, norm_mul, norm_mul]
    have hfactor : ‖1 - (r : ℂ) * (r : ℂ) ^ n‖ ≤ ‖1 - q * q ^ n‖ := by
      have hpow : r ^ (n + 1) ≤ 1 := pow_le_one₀ hr.le hr1.le
      calc
        ‖1 - (r : ℂ) * (r : ℂ) ^ n‖ = |1 - r ^ (n + 1)| := by
          rw [← pow_succ']
          norm_cast
        _ = 1 - r ^ (n + 1) := abs_of_nonneg (sub_nonneg.mpr hpow)
        _ ≤ 1 - ‖q‖ ^ (n + 1) :=
          sub_le_sub_left (pow_le_pow_left₀ (norm_nonneg q) hq _) 1
        _ = ‖(1 : ℂ)‖ - ‖q * q ^ n‖ := by
          simp [norm_pow, pow_succ']
        _ ≤ ‖1 - q * q ^ n‖ := norm_sub_norm_le _ _
    exact mul_le_mul ih hfactor (norm_nonneg _) (norm_nonneg _)

/-- On a closed disk of radius less than one, all finite denominators have
one common inverse-norm bound, including the empty product. -/
lemma diagonal_inverse_bound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ q : ℂ, ‖q‖ ≤ r → ∀ n : ℕ,
      ‖(qPochhammerNat q q n)⁻¹‖ ≤ B := by
  have hrc : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hd := tendsto_qPochhammerNat (r : ℂ) (r : ℂ)
    (by simpa only [hrc] using hr) (by simpa only [hrc] using hr1)
  have hz := qPochhammer_q_ne_zero (r : ℂ)
    (by simpa only [hrc] using hr) (by simpa only [hrc] using hr1)
  obtain ⟨B, hB, hb⟩ := (Metric.isBounded_range_of_tendsto
    (fun n => (qPochhammerNat (r : ℂ) (r : ℂ) n)⁻¹) (hd.inv₀ hz)).exists_pos_norm_le
  refine ⟨B, hB, fun q hq n => ?_⟩
  have hl := diagonal_norm_lower r hr hr1 q hq n
  have hp : 0 < ‖qPochhammerNat (r : ℂ) (r : ℂ) n‖ :=
    norm_pos_iff.mpr (qPochhammerNat_q_ne_zero _ n
      (by simpa only [hrc] using hr) (by simpa only [hrc] using hr1))
  calc
    ‖(qPochhammerNat q q n)⁻¹‖ ≤ ‖(qPochhammerNat (r : ℂ) (r : ℂ) n)⁻¹‖ := by
      simp only [norm_inv]
      exact (inv_le_inv₀ (hp.trans_le hl) hp).mpr hl
    _ ≤ B := hb _ (mem_range_self n)

/-- The concrete coefficient, defined in this auxiliary file. -/
def rawWeight (M : SL(2, ℤ)) (h ℓ : ℤ) (x : UpperWindow.Parameters)
    (k : ℕ × ℕ) : ℂ :=
  prefactor M x.1 * singleResidueSeriesTerm (UpperWindow.A ℓ x.1 x.2.1)
    (UpperWindow.C M h x.1 x.2.1) (e x.1) (e (etaMobius M x.1)) k

/-- A geometric bound for the separated Euler coefficient. -/
lemma norm_term_le (d A C q Q : ℂ) (D a b Bq BQ : ℝ) (k : ℕ × ℕ)
    (hd : ‖d‖ ≤ D) (hA : ‖A‖ ≤ a) (hC : ‖Q * C‖ ≤ b)
    (hQ : ‖Q‖ ≤ 1) (hBq : ‖(qPochhammerNat q q k.1)⁻¹‖ ≤ Bq)
    (hBQ : ‖(qPochhammerNat Q Q k.2)⁻¹‖ ≤ BQ)
    (hD : 0 ≤ D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hBq0 : 0 ≤ Bq) (_hBQ0 : 0 ≤ BQ) :
    ‖d * singleResidueSeriesTerm A C q Q k‖ ≤
      (D * Bq * BQ) * (a ^ k.1 * b ^ k.2) := by
  have hK : ‖eulerInverseTerm A q k.1‖ ≤ a ^ k.1 * Bq := by
    simp only [eulerInverseTerm, div_eq_mul_inv, norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hA _) hBq
      (norm_nonneg _) (pow_nonneg ha _)
  have hJ : ‖eulerTerm (Q * C) Q k.2‖ ≤ b ^ k.2 * BQ := by
    simp only [eulerTerm, div_eq_mul_inv, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul]
    rw [← norm_mul Q C]
    have hp := pow_le_one₀ (norm_nonneg Q) hQ (n := k.2 * (k.2 - 1) / 2)
    calc
      ‖Q‖ ^ (k.2 * (k.2 - 1) / 2) * ‖Q * C‖ ^ k.2 *
          ‖(qPochhammerNat Q Q k.2)⁻¹‖ ≤ (1 * b ^ k.2) * BQ :=
        mul_le_mul (mul_le_mul hp (pow_le_pow_left₀ (norm_nonneg _) hC _)
          (pow_nonneg (norm_nonneg _) _) zero_le_one) hBQ
          (norm_nonneg _) (by positivity)
      _ = b ^ k.2 * BQ := by ring
  calc
    ‖d * singleResidueSeriesTerm A C q Q k‖ =
        ‖d‖ * (‖eulerInverseTerm A q k.1‖ * ‖eulerTerm (Q * C) Q k.2‖) := by
      simp only [singleResidueSeriesTerm, norm_mul]
    _ ≤ D * ((a ^ k.1 * Bq) * (b ^ k.2 * BQ)) :=
      mul_le_mul hd (mul_le_mul hK hJ (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hD
    _ = (D * Bq * BQ) * (a ^ k.1 * b ^ k.2) := by ring

/-- A compact family in the two open unit disks has one summable majorant. -/
lemma compact_majorant_of_continuous {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (d A C q Q : X → ℂ)
    (hd : ContinuousOn d K) (hA : ContinuousOn A K)
    (hC : ContinuousOn (fun x => Q x * C x) K)
    (hq : ContinuousOn q K) (hQ : ContinuousOn Q K)
    (hA1 : ∀ x ∈ K, ‖A x‖ < 1) (hC1 : ∀ x ∈ K, ‖Q x * C x‖ < 1)
    (hq1 : ∀ x ∈ K, ‖q x‖ < 1) (hQ1 : ∀ x ∈ K, ‖Q x‖ < 1) :
    ∃ g : ℕ × ℕ → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∀ x ∈ K, ∀ k, ‖d x * singleResidueSeriesTerm (A x) (C x) (q x) (Q x) k‖ ≤ g k := by
  obtain ⟨D, hD, hbD⟩ := positive_bound hK hd.norm
  obtain ⟨a, ha, ha1, hba⟩ := strict_upper_bound hK hA.norm hA1
  obtain ⟨b, hb, hb1, hbb⟩ := strict_upper_bound hK hC.norm hC1
  obtain ⟨r, hr, hr1, hbr⟩ := strict_upper_bound hK hq.norm hq1
  obtain ⟨s, hs, hs1, hbs⟩ := strict_upper_bound hK hQ.norm hQ1
  obtain ⟨Bq, hBq, hbq⟩ := diagonal_inverse_bound r hr hr1
  obtain ⟨BQ, hBQ, hbQ⟩ := diagonal_inverse_bound s hs hs1
  refine ⟨fun k => (D * Bq * BQ) * (a ^ k.1 * b ^ k.2), ?_, ?_, ?_⟩
  · intro k
    positivity
  · exact ((summable_geometric_of_lt_one ha.le ha1).mul_of_nonneg
      (summable_geometric_of_lt_one hb.le hb1)
      (fun n => pow_nonneg ha.le n) (fun n => pow_nonneg hb.le n)).mul_left _
  · intro x hx k
    exact norm_term_le _ _ _ _ _ _ _ _ _ _ k (hbD x hx) (hba x hx) (hbb x hx)
      (hQ1 x hx).le (hbq _ (hbr x hx) _) (hbQ _ (hbs x hx) _)
      hD.le ha.le hb.le hBq.le hBQ.le

/-- A summable uniform majorant gives convergence along the original integer
squares, for any family of sums with the specified pointwise values. -/
lemma square_limit_of_majorant {X : Type*} (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (K : Set X) (f : X → ℕ × ℕ → ℂ) (v : X → ℂ) (g : ℕ × ℕ → ℝ)
    (hg : Summable g) (hbound : ∀ x ∈ K, ∀ k, ‖f x k‖ ≤ g k)
    (hsum : ∀ x ∈ K, HasSum (f x) (v x)) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x ∈ K,
      ‖squareSum M R (f x) - v x‖ < ε := by
  have ht := tendstoUniformlyOn_tsum hg (fun k x hx => hbound x hx k)
  have hsq : Tendsto (square M) atTop atTop :=
    (square_mono M).tendsto_atTop_finset (fun k => (square_exhaust M hM k).exists)
  intro ε hε
  have hev := hsq.eventually ((Metric.tendstoUniformlyOn_iff.mp ht) ε hε)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hev
  refine ⟨R₀, fun R hR x hx => ?_⟩
  have hb := hR₀ R hR x hx
  rw [(hsum x hx).tsum_eq] at hb
  simpa only [squareSum, dist_eq_norm, norm_sub_rev] using hb

/-- Continuity of a diagonal infinite product inside the unit disk. -/
lemma continuousAt_diagonal_product (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ContinuousAt (fun z : ℂ => qPochhammer z z) q := by
  exact (analyticOnNhd_qPochhammer_joint (q, q) ⟨hq0, hq1⟩).continuousAt.comp (f := fun z : ℂ => (z, z))
    (show ContinuousAt (fun z : ℂ => (z, z)) q from by fun_prop)

/-- Continuity of the literal prefactor requires only the two disk conditions
and the nonzero modular denominator. -/
lemma continuousAt_prefactor (M : SL(2, ℤ)) (τ : ℂ)
    (hT : etaDenom M τ ≠ 0)
    (hq0 : 0 < ‖e τ‖) (hq1 : ‖e τ‖ < 1)
    (hQ0 : 0 < ‖e (etaMobius M τ)‖) (hQ1 : ‖e (etaMobius M τ)‖ < 1) :
    ContinuousAt (prefactor M) τ := by
  have hq : ContinuousAt e τ := continuous_e.continuousAt
  have hQ : ContinuousAt (fun z => e (etaMobius M z)) τ :=
    (continuous_e.continuousAt).comp (continuousAt_etaMobius M τ hT)
  have hPq : ContinuousAt (fun z => qPochhammer (e z) (e z)) τ :=
    (continuousAt_diagonal_product _ hq0 hq1).comp (f := e) hq
  have hPQ : ContinuousAt (fun z => qPochhammer (e (etaMobius M z))
      (e (etaMobius M z))) τ :=
    (continuousAt_diagonal_product _ hQ0 hQ1).comp
      (f := fun z => e (etaMobius M z)) hQ
  exact ((continuous_etaDenom M).continuousAt.mul hPq).div hPQ
    (qPochhammer_q_ne_zero _ hQ0 hQ1)

/-- The initial upper window gives one compact summable bound for its concrete
single-residue coefficients. Empty compact sets are included. -/
lemma rawWeight_compact_majorant (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKD : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ g : ℕ × ℕ → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∀ x ∈ K, ∀ k, ‖rawWeight M h ℓ x k‖ ≤ g k := by
  have hq : ContinuousOn (fun x : UpperWindow.Parameters => e x.1) K := by fun_prop
  have hA : ContinuousOn (fun x : UpperWindow.Parameters => UpperWindow.A ℓ x.1 x.2.1) K := by
    unfold UpperWindow.A
    fun_prop (disch := simp [e_ne_zero])
  have hQ : ContinuousOn (fun x : UpperWindow.Parameters => e (etaMobius M x.1)) K := by
    intro x hx
    have hT := (tau_facts M h ℓ p ψ σ ρ δ hc (hKD hx)).2.2.2.1
    apply ContinuousAt.continuousWithinAt
    exact (continuous_e.continuousAt).comp
      ((continuousAt_etaMobius M x.1 hT).comp (by fun_prop))
  have hC : ContinuousOn (fun x : UpperWindow.Parameters => UpperWindow.C M h x.1 x.2.1) K := by
    intro x hx
    have hT := (tau_facts M h ℓ p ψ σ ρ δ hc (hKD hx)).2.2.2.1
    have hmob : ContinuousAt (fun x : UpperWindow.Parameters => etaMobius M x.1) x :=
      (continuousAt_etaMobius M x.1 hT).comp (by fun_prop)
    apply ContinuousAt.continuousWithinAt
    unfold UpperWindow.C
    fun_prop (disch := first | exact hT | simp [e_ne_zero])
  have hd : ContinuousOn (fun x : UpperWindow.Parameters => prefactor M x.1) K := by
    intro x hx
    obtain ⟨_, _, _, hT, hq0, hq1, hQ0, hQ1⟩ :=
      tau_facts M h ℓ p ψ σ ρ δ hc (hKD hx)
    exact ((continuousAt_prefactor M x.1 hT hq0 hq1 hQ0 hQ1).comp
      (show ContinuousAt (fun x : UpperWindow.Parameters => x.1) x by fun_prop)).continuousWithinAt
  apply compact_majorant_of_continuous K hK (fun x => prefactor M x.1)
    (fun x => UpperWindow.A ℓ x.1 x.2.1) (fun x => UpperWindow.C M h x.1 x.2.1)
    (fun x => e x.1) (fun x => e (etaMobius M x.1)) hd hA (hQ.mul hC) hq hQ
  · intro x hx
    exact (six_arguments_norm_lt_one M h ℓ p ψ σ ρ δ hc x (hKD hx)).2.2.1
  · intro x hx
    exact (six_arguments_norm_lt_one M h ℓ p ψ σ ρ δ hc x (hKD hx)).2.2.2.2.2
  · intro x hx
    exact (tau_facts M h ℓ p ψ σ ρ δ hc (hKD hx)).2.2.2.2.2.1
  · intro x hx
    exact (tau_facts M h ℓ p ψ σ ρ δ hc (hKD hx)).2.2.2.2.2.2.2

/-! ## The punctured local q-product calculation -/

lemma inverse_pochhammer_residue (Q T : ℂ) (J : ℕ)
    (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) (hT : T ≠ 0) :
    Tendsto (fun ζ : ℂ => ζ / qPochhammer (Q ^ (-(J : ℤ)) * e (ζ / T)) Q)
      (𝓝[≠] 0)
      (𝓝 ((-T / (2 * (Real.pi : ℂ) * Complex.I)) *
        (((-1 : ℂ) ^ J * Q ^ UpperContour.triangular J) /
          (qPochhammerNat Q Q J * qPochhammer Q Q)))) := by
  let d : ℂ → ℂ := fun ζ => e (ζ / T)
  let D : ℂ → ℂ := fun ζ =>
    (-d ζ) ^ J * Q ^ (-(UpperContour.triangular J : ℤ)) *
      qPochhammerNat (Q / d ζ) Q J * qPochhammer (d ζ * Q) Q
  have hQ : Q ≠ 0 := norm_pos_iff.mp hQ0
  have hd (ζ : ℂ) : d ζ ≠ 0 := e_ne_zero _
  have hd0 : d 0 = 1 := by simp [d, e]
  have hdc : Continuous d := by dsimp [d]; unfold e; fun_prop
  have hPc : Continuous (fun ζ : ℂ => qPochhammer (d ζ * Q) Q) :=
    (differentiable_qPochhammer_x Q hQ0 hQ1).continuous.comp (hdc.mul_const Q)
  have hPNc : Continuous (fun ζ : ℂ => qPochhammerNat (Q / d ζ) Q J) := by
    unfold qPochhammerNat
    fun_prop (disch := exact hd _)
  have hDc : Continuous D := ((hdc.neg.pow J).mul continuous_const).mul hPNc |>.mul hPc
  have hD0 : D 0 = (-1 : ℂ) ^ J * Q ^ (-(UpperContour.triangular J : ℤ)) *
      qPochhammerNat Q Q J * qPochhammer Q Q := by simp [D, hd0]
  have hDne : D 0 ≠ 0 := by
    rw [hD0]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (zpow_ne_zero _ hQ)) (qPochhammerNat_q_ne_zero Q J hQ0 hQ1))
      (qPochhammer_q_ne_zero Q hQ0 hQ1)
  have hfac (ζ : ℂ) :
      qPochhammer (Q ^ (-(J : ℤ)) * d ζ) Q = (1 - d ζ) * D ζ := by
    rw [mul_comm (Q ^ (-(J : ℤ))) (d ζ),
      UpperContour.qPochhammer_backward_cleared (d ζ) Q (hd ζ) hQ0 hQ1 J]
    rw [qPochhammer_shift_nat (d ζ) Q 1 hQ0 hQ1]
    rw [show qPochhammerNat (d ζ) Q 1 = 1 - d ζ by simp [qPochhammerNat]]
    simp only [pow_one]
    dsimp only [D]
    ring
  have hGc : ContinuousAt (fun ζ : ℂ => m37b_expSlope (ζ / T)) 0 := by
    have hG : ContinuousAt m37b_expSlope ((0 : ℂ) / T) := by
      simpa only [zero_div] using m37b_expSlope_analytic_zero.continuousAt
    exact hG.comp (f := fun ζ : ℂ => ζ / T) (x := 0) (continuousAt_id.div_const T)
  have hGne : m37b_expSlope ((0 : ℂ) / T) ≠ 0 := by
    simpa only [zero_div] using m37b_expSlope_zero_ne
  have hlim := ((continuousAt_const.div (hGc.mul hDc.continuousAt)
    (mul_ne_zero hGne hDne)) : ContinuousAt
      (fun ζ : ℂ => -T / (m37b_expSlope (ζ / T) * D ζ)) 0).tendsto
  have hevD : ∀ᶠ ζ : ℂ in 𝓝[≠] 0, D ζ ≠ 0 :=
    (hDc.continuousAt.eventually_ne hDne).filter_mono nhdsWithin_le_nhds
  have hevG : ∀ᶠ ζ : ℂ in 𝓝[≠] 0, m37b_expSlope (ζ / T) ≠ 0 :=
    (hGc.eventually_ne hGne).filter_mono nhdsWithin_le_nhds
  have heq : (fun ζ : ℂ => ζ / qPochhammer (Q ^ (-(J : ℤ)) * e (ζ / T)) Q) =ᶠ[𝓝[≠] 0]
      (fun ζ : ℂ => -T / (m37b_expSlope (ζ / T) * D ζ)) := by
    filter_upwards [self_mem_nhdsWithin, hevD, hevG] with ζ hζ hD hG
    change ζ / qPochhammer (Q ^ (-(J : ℤ)) * d ζ) Q = _
    rw [hfac]
    have he := m37b_expSlope_mul (ζ / T)
    change ζ / ((1 - e (ζ / T)) * D ζ) = _
    have hE : 1 - e (ζ / T) = -(ζ / T) * m37b_expSlope (ζ / T) := by
      linear_combination he
    rw [hE]
    have hζ0 : ζ ≠ 0 := by simpa using hζ
    field_simp
  have hval : -T / (m37b_expSlope ((0 : ℂ) / T) * D 0) =
      (-T / (2 * (Real.pi : ℂ) * Complex.I)) *
        (((-1 : ℂ) ^ J * Q ^ UpperContour.triangular J) /
          (qPochhammerNat Q Q J * qPochhammer Q Q)) := by
    rw [zero_div, m37b_expSlope_zero, hD0, zpow_neg, zpow_natCast]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← inv_pow, inv_neg_one]
    ring
  rw [← hval]
  exact (hlim.mono_left nhdsWithin_le_nhds).congr' heq.symm

lemma pole_qProduct_expression (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (hτ : 0 < τ.im) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m + 1) n) (z : ℂ) :
    let z₀ := modularPhiPolePoint M (m + 1) n τ k.1 k.2
    modularPhiQProduct M (m + 1) n z τ =
      qPochhammer ((e τ) ^ (k.1 + 1) * e (z - z₀)) (e τ) /
        qPochhammer ((e (etaMobius M τ)) ^ (-(k.2 : ℤ)) *
          e ((z - z₀) / etaDenom M τ)) (e (etaMobius M τ)) := by
  have hlab : Int.ModEq (M 1 0) ((k.2 : ℤ) + M 1 1 * (k.1 : ℤ))
      (M 1 1 * m - n) := by simpa [modularPhiPoleLabels] using hk
  obtain ⟨L, hL⟩ := Int.ModEq.dvd hlab
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hLC := congrArg (fun r : ℤ => (r : ℂ)) hL
  push_cast at hLC
  have hlat : modularPhiPolePoint M (m + 1) n τ k.1 k.2 =
      (((k.1 : ℤ) - m : ℤ) : ℂ) * τ + ((-L : ℤ) : ℂ) := by
    unfold modularPhiPolePoint
    apply (div_eq_iff hc).mpr
    push_cast
    unfold etaDenom
    linear_combination -hLC
  have hK : (k.1 : ℤ) - m + (m + 1) = ((k.1 + 1 : ℕ) : ℤ) := by omega
  have hJ : M 1 1 * ((k.1 : ℤ) - m) - M 1 0 * (-L) + n = -(k.2 : ℤ) := by
    linear_combination -hL
  have hζ : z - ((((k.1 : ℤ) - m : ℤ) : ℂ) * τ) - ((-L : ℤ) : ℂ) =
      z - modularPhiPolePoint M (m + 1) n τ k.1 k.2 := by rw [hlat]; ring
  dsimp only
  unfold modularPhiQProduct
  rw [m37c_qNumerator_lattice (m + 1) ((k.1 : ℤ) - m) (-L) z τ,
    m37c_qDenominator_lattice M n ((k.1 : ℤ) - m) (-L) z τ
      (mem_modularPhiDomain_of_im_pos M hM hτ), hK, hJ, hζ, zpow_natCast]

lemma euler_q_mul (Q C : ℂ) (J : ℕ) :
    eulerTerm (Q * C) Q J =
      ((-1 : ℂ) ^ J * Q ^ UpperContour.triangular J / qPochhammerNat Q Q J) * C ^ J := by
  have htri : J * (J - 1) / 2 + J = UpperContour.triangular J := by
    have h := Finset.sum_range_succ (fun j : ℕ => j) J
    rw [Finset.sum_range_id, Finset.sum_range_id] at h
    simpa [UpperContour.triangular, Nat.mul_comm] using h.symm
  unfold eulerTerm
  rw [mul_pow, ← htri, pow_add]
  ring

lemma single_qKernel_residue (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n h ℓ p : ℤ) (x : UpperWindow.Parameters) (hτ : 0 < x.1.im)
    (k : ℕ × ℕ) (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    let z₀ := modularPhiPolePoint M (m + 1) n x.1 k.1 k.2
    Tendsto (fun z : ℂ => (z - z₀) * UpperContour.qKernel .single M m n h ℓ p x z)
      (𝓝[≠] z₀)
      (𝓝 (UpperResidueParameters.prefactor M x.1 *
        singleResidueSeriesTerm (UpperWindow.A ℓ x.1 x.2.1)
          (UpperWindow.C M h x.1 x.2.1) (e x.1) (e (etaMobius M x.1)) k /
        (-2 * (Real.pi : ℂ) * Complex.I))) := by
  let z₀ := modularPhiPolePoint M (m + 1) n x.1 k.1 k.2
  let q := e x.1
  let Q := e (etaMobius M x.1)
  let T := etaDenom M x.1
  have hq0 : 0 < ‖q‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hq1 : ‖q‖ < 1 := norm_e_lt_one ⟨_, hτ⟩
  have hQ0 : 0 < ‖Q‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hQ1 : ‖Q‖ < 1 := norm_e_lt_one ⟨_, m37c_upper_mobius M x.1 hτ⟩
  have hT : T ≠ 0 := etaDenom_ne_zero_of_mem M
    (mem_modularPhiDomain_of_im_pos M hM hτ)
  have htrans : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : ContinuousAt (fun z : ℂ => z - z₀) z₀ := by fun_prop
      simpa only [sub_self] using ht.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa only [mem_compl_iff, mem_singleton_iff, sub_eq_zero] using hz
  have hnumc : Continuous (fun z : ℂ => qPochhammer (q ^ (k.1 + 1) * e (z - z₀)) q) :=
    (differentiable_qPochhammer_x q hq0 hq1).continuous.comp (by unfold e; fun_prop)
  have hnum : Tendsto (fun z : ℂ => qPochhammer (q ^ (k.1 + 1) * e (z - z₀)) q)
      (𝓝[≠] z₀) (𝓝 (qPochhammer (q ^ (k.1 + 1)) q)) := by
    have ht := hnumc.continuousAt (x := z₀)
    have ht' : Tendsto (fun z : ℂ => qPochhammer (q ^ (k.1 + 1) * e (z - z₀)) q)
        (𝓝 z₀) (𝓝 (qPochhammer (q ^ (k.1 + 1)) q)) := by
      simpa only [sub_self, show e 0 = 1 by simp [e], mul_one] using ht.tendsto
    exact ht'.mono_left nhdsWithin_le_nhds
  have hphasec : Continuous (fun z : ℂ => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)) := by
    unfold UpperWindow.phase e
    fun_prop
  have hphase : Tendsto (fun z : ℂ => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z))
      (𝓝[≠] z₀) (𝓝 (UpperWindow.A ℓ x.1 x.2.1 ^ k.1 *
        UpperWindow.C M h x.1 x.2.1 ^ k.2)) := by
    rw [← UpperResidueParameters.phase_at_pole M hM m n h ℓ x.1 x.2.1 hτ k hk]
    exact hphasec.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hi := (inverse_pochhammer_residue Q T k.2 hQ0 hQ1 hT).comp htrans
  have hlim := (hnum.mul hi).mul hphase
  have hNK : qPochhammerNat q q k.1 ≠ 0 := qPochhammerNat_q_ne_zero q k.1 hq0 hq1
  have hNJ : qPochhammerNat Q Q k.2 ≠ 0 := qPochhammerNat_q_ne_zero Q k.2 hQ0 hQ1
  have hPQ : qPochhammer Q Q ≠ 0 := qPochhammer_q_ne_zero Q hQ0 hQ1
  have hnumval : qPochhammer (q ^ (k.1 + 1)) q = qPochhammer q q / qPochhammerNat q q k.1 := by
    apply (eq_div_iff hNK).mpr
    have hs := qPochhammer_shift_nat q q k.1 hq0 hq1
    simpa only [pow_succ, mul_comm] using hs.symm
  have hval : (qPochhammer (q ^ (k.1 + 1)) q *
      ((-T / (2 * (Real.pi : ℂ) * Complex.I)) *
        (((-1 : ℂ) ^ k.2 * Q ^ UpperContour.triangular k.2) /
          (qPochhammerNat Q Q k.2 * qPochhammer Q Q)))) *
      (UpperWindow.A ℓ x.1 x.2.1 ^ k.1 * UpperWindow.C M h x.1 x.2.1 ^ k.2) =
      UpperResidueParameters.prefactor M x.1 *
        singleResidueSeriesTerm (UpperWindow.A ℓ x.1 x.2.1)
          (UpperWindow.C M h x.1 x.2.1) q Q k / (-2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hnumval]
    unfold singleResidueSeriesTerm eulerInverseTerm
    rw [euler_q_mul]
    change _ = (T * qPochhammer q q / qPochhammer Q Q) *
      ((UpperWindow.A ℓ x.1 x.2.1 ^ k.1 / qPochhammerNat q q k.1) *
        (((-1 : ℂ) ^ k.2 * Q ^ UpperContour.triangular k.2 / qPochhammerNat Q Q k.2) *
          UpperWindow.C M h x.1 x.2.1 ^ k.2)) / (-2 * (Real.pi : ℂ) * Complex.I)
    field_simp
  dsimp only
  rw [← hval]
  apply hlim.congr'
  exact Eventually.of_forall (fun z => by
    simp only [UpperContour.qKernel]
    rw [pole_qProduct_expression M hM m n x.1 hτ k hk]
    dsimp only [Function.comp_apply, z₀, q, Q, T]
    ring)


end SICLean.L4.UpperSingleResiduesAux
