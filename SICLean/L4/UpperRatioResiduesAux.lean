import SICLean.L4.UpperResidueParameters
import SICLean.L4.UpperContourClosure
import SICLean.L4.UpperResidueIndex
import SICLean.L4.UpperWindowCompactAux

set_option autoImplicit false

/-!
Local q-quotient residue limits, uniform q-binomial bounds, and convergence
of the original integer squares. All helpers stay in this module's namespace.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperRatioResiduesAux

lemma finite_numerator_comparison {A r : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r)
    {a q : ℂ} (ha : ‖a‖ ≤ A) (hq : ‖q‖ ≤ r) (n : ℕ) :
    ‖qPochhammerNat a q n‖ ≤ ‖qPochhammerNat (-A : ℂ) (r : ℂ) n‖ := by
  simp only [qPochhammerNat, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  have hre : (1 : ℂ) - (-A : ℂ) * (r : ℂ) ^ j = ((1 + A * r ^ j : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hre, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    ‖(1 : ℂ) - a * q ^ j‖ ≤ 1 + ‖a‖ * ‖q‖ ^ j := by
      simpa only [norm_one, norm_mul, norm_pow] using norm_sub_le (1 : ℂ) (a * q ^ j)
    _ ≤ 1 + A * r ^ j := by
      gcongr

lemma finite_denominator_comparison {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {q : ℂ} (hq : ‖q‖ ≤ r) (n : ℕ) :
    ‖qPochhammerNat (r : ℂ) (r : ℂ) n‖ ≤ ‖qPochhammerNat q q n‖ := by
  simp only [qPochhammerNat, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  have hre : (1 : ℂ) - (r : ℂ) * (r : ℂ) ^ j = ((1 - r ^ (j + 1) : ℝ) : ℂ) := by
    push_cast
    rw [pow_succ']
  rw [hre, Complex.norm_real, Real.norm_of_nonneg (by
    exact (sub_pos.mpr (pow_lt_one₀ hr hr1 (Nat.add_one_ne_zero j))).le)]
  have hqp : ‖q * q ^ j‖ ≤ r ^ (j + 1) := by
    rw [norm_mul, norm_pow, pow_succ']
    gcongr
  calc
    1 - r ^ (j + 1) ≤ 1 - ‖q * q ^ j‖ := sub_le_sub_left hqp 1
    _ ≤ ‖(1 : ℂ) - q * q ^ j‖ := by
      simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) (q * q ^ j)

/-- A single fixed real base bounds every finite numerator and every inverse
finite diagonal denominator throughout the closed disk of radius `r`. -/
lemma finite_product_bounds {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hr1 : r < 1) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧
      (∀ a q : ℂ, ‖a‖ ≤ A → ‖q‖ ≤ r → ∀ n : ℕ, ‖qPochhammerNat a q n‖ ≤ U) ∧
      (∀ q : ℂ, ‖q‖ ≤ r → ∀ n : ℕ, ‖(qPochhammerNat q q n)⁻¹‖ ≤ V) := by
  have hrn : ‖(r : ℂ)‖ = r := by simp [Real.norm_of_nonneg hr.le]
  have hrc0 : 0 < ‖(r : ℂ)‖ := by simpa only [hrn] using hr
  have hrc1 : ‖(r : ℂ)‖ < 1 := by simpa only [hrn] using hr1
  have htU := tendsto_qPochhammerNat (-A : ℂ) (r : ℂ) hrc0 hrc1
  obtain ⟨U, hU, hUb⟩ := (Metric.isBounded_range_of_tendsto _ htU).exists_pos_norm_le
  have htV := (tendsto_qPochhammerNat (r : ℂ) (r : ℂ) hrc0 hrc1).inv₀
    (qPochhammer_q_ne_zero (r : ℂ) hrc0 hrc1)
  obtain ⟨V, hV, hVb⟩ := (Metric.isBounded_range_of_tendsto _ htV).exists_pos_norm_le
  refine ⟨U, V, hU, hV, ?_, ?_⟩
  · intro a q ha hq n
    exact (finite_numerator_comparison hA hr.le ha hq n).trans (hUb _ (mem_range_self n))
  · intro q hq n
    have hd := finite_denominator_comparison hr.le hr1 hq n
    have hp : 0 < ‖qPochhammerNat (r : ℂ) (r : ℂ) n‖ :=
      norm_pos_iff.mpr (qPochhammerNat_q_ne_zero (r : ℂ) n hrc0 hrc1)
    calc
      ‖(qPochhammerNat q q n)⁻¹‖ = 1 / ‖qPochhammerNat q q n‖ := by simp
      _ ≤ 1 / ‖qPochhammerNat (r : ℂ) (r : ℂ) n‖ := one_div_le_one_div_of_le hp hd
      _ = ‖(qPochhammerNat (r : ℂ) (r : ℂ) n)⁻¹‖ := by simp
      _ ≤ V := hVb _ (mem_range_self n)

lemma qBinomial_bound {A r s : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hr1 : r < 1)
    (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ a z q : ℂ, ‖a‖ ≤ A → ‖q‖ ≤ r → ‖z‖ ≤ s →
      ∀ n : ℕ, ‖qBinomialTerm a z q n‖ ≤ C * s ^ n := by
  obtain ⟨U, V, hU, hV, hUb, hVb⟩ := finite_product_bounds hA hr hr1
  refine ⟨U * V, mul_pos hU hV, ?_⟩
  intro a z q ha hq hz n
  calc
    ‖qBinomialTerm a z q n‖ =
        ‖qPochhammerNat a q n‖ * ‖z‖ ^ n * ‖(qPochhammerNat q q n)⁻¹‖ := by
      simp only [qBinomialTerm, div_eq_mul_inv, norm_mul, norm_pow]
    _ ≤ U * s ^ n * V := by
      gcongr
      · exact hUb a q ha hq n
      · exact hVb q hq n
    _ = (U * V) * s ^ n := by ring

lemma compact_qBinomial_bound {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (a z q : X → ℂ)
    (ha : ContinuousOn a K) (hz : ContinuousOn z K) (hq : ContinuousOn q K)
    (hz1 : ∀ x ∈ K, ‖z x‖ < 1) (hq1 : ∀ x ∈ K, ‖q x‖ < 1) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ s < 1 ∧
      ∀ x ∈ K, ∀ n : ℕ, ‖qBinomialTerm (a x) (z x) (q x) n‖ ≤ C * s ^ n := by
  obtain ⟨A, hA, hAb⟩ := UpperWindow.CompactAux.positive_bound hK ha.norm
  obtain ⟨r, hr, hr1, hrb⟩ := UpperWindow.CompactAux.strict_upper_bound hK hq.norm hq1
  obtain ⟨s, hs, hs1, hsb⟩ := UpperWindow.CompactAux.strict_upper_bound hK hz.norm hz1
  obtain ⟨C, hC, hCb⟩ := qBinomial_bound hA.le hr hr1 hs.le
  exact ⟨C, s, hC, hs, hs1, fun x hx n => hCb _ _ _ (hAb x hx) (hrb x hx) (hsb x hx) n⟩

/-- The numerator parameters are unrestricted. Only the two series arguments
and bases need to remain in their open unit disks. -/
lemma compact_product_majorant {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (P a A q b B Q : X → ℂ)
    (hP : ContinuousOn P K) (ha : ContinuousOn a K) (hA : ContinuousOn A K)
    (hq : ContinuousOn q K) (hb : ContinuousOn b K) (hB : ContinuousOn B K)
    (hQ : ContinuousOn Q K)
    (hA1 : ∀ x ∈ K, ‖A x‖ < 1) (hB1 : ∀ x ∈ K, ‖B x‖ < 1)
    (hq1 : ∀ x ∈ K, ‖q x‖ < 1) (hQ1 : ∀ x ∈ K, ‖Q x‖ < 1) :
    ∃ g : ℕ × ℕ → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∀ x ∈ K, ∀ k, ‖P x * ratioResidueSeriesTerm (a x) (A x) (q x)
        (b x) (B x) (Q x) k‖ ≤ g k := by
  obtain ⟨C, r, hC, hr, hr1, hCr⟩ := compact_qBinomial_bound hK a A q ha hA hq hA1 hq1
  obtain ⟨D, s, hD, hs, hs1, hDs⟩ := compact_qBinomial_bound hK b B Q hb hB hQ hB1 hQ1
  obtain ⟨E, hE, hEb⟩ := UpperWindow.CompactAux.positive_bound hK hP.norm
  let g : ℕ × ℕ → ℝ := fun k => (E * C * D) * (r ^ k.1 * s ^ k.2)
  have hgeomr : Summable (fun n : ℕ => ‖r ^ n‖) := by
    simpa only [norm_pow, Real.norm_of_nonneg hr.le] using summable_geometric_of_lt_one hr.le hr1
  have hgeoms : Summable (fun n : ℕ => ‖s ^ n‖) := by
    simpa only [norm_pow, Real.norm_of_nonneg hs.le] using summable_geometric_of_lt_one hs.le hs1
  refine ⟨g, fun k => by dsimp [g]; positivity,
    (summable_mul_of_summable_norm hgeomr hgeoms).mul_left (E * C * D), ?_⟩
  intro x hx k
  calc
    ‖P x * ratioResidueSeriesTerm (a x) (A x) (q x) (b x) (B x) (Q x) k‖ =
        ‖P x‖ * (‖qBinomialTerm (a x) (A x) (q x) k.1‖ *
          ‖qBinomialTerm (b x) (B x) (Q x) k.2‖) := by
      simp only [ratioResidueSeriesTerm, norm_mul]
    _ ≤ E * ((C * r ^ k.1) * (D * s ^ k.2)) := by
      gcongr
      · exact hEb x hx
      · exact hCr x hx k.1
      · exact hDs x hx k.2
    _ = g k := by dsimp [g]; ring

lemma continuousOn_qPochhammer {X : Type*} [TopologicalSpace X] {K : Set X}
    (u v : X → ℂ) (hu : ContinuousOn u K) (hv : ContinuousOn v K)
    (hv0 : ∀ x ∈ K, 0 < ‖v x‖) (hv1 : ∀ x ∈ K, ‖v x‖ < 1) :
    ContinuousOn (fun x => qPochhammer (u x) (v x)) K := by
  exact analyticOnNhd_qPochhammer_joint.continuousOn.comp (hu.prodMk hv)
    (fun x hx => ⟨hv0 x hx, hv1 x hx⟩)

/-- An explicit specialization, definitionally equal to the ratio residue weight. -/
lemma compact_weight_majorant (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKD : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ g : ℕ × ℕ → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∀ x ∈ K, ∀ k, ‖UpperResidueParameters.prefactor M x.1 *
        (qPochhammer (UpperResidueParameters.t M x) (e (etaMobius M x.1)) /
          qPochhammer (UpperResidueParameters.a p x) (e x.1)) *
        ratioResidueSeriesTerm (UpperResidueParameters.a p x) (UpperWindow.A ℓ x.1 x.2.1)
          (e x.1) (UpperResidueParameters.b M x)
          (UpperWindow.B M h x.1 x.2.1 x.2.2) (e (etaMobius M x.1)) k‖ ≤ g k := by
  have htau (x : UpperWindow.Parameters) (hx : x ∈ K) :=
    UpperWindow.CompactAux.tau_facts M h ℓ p ψ σ ρ δ hc (hKD hx)
  have hT (x : UpperWindow.Parameters) (hx : x ∈ K) : etaDenom M x.1 ≠ 0 :=
    (htau x hx).2.2.2.1
  have hq0 (x : UpperWindow.Parameters) (hx : x ∈ K) : 0 < ‖e x.1‖ :=
    (htau x hx).2.2.2.2.1
  have hq1 (x : UpperWindow.Parameters) (hx : x ∈ K) : ‖e x.1‖ < 1 :=
    (htau x hx).2.2.2.2.2.1
  have hQ0 (x : UpperWindow.Parameters) (hx : x ∈ K) : 0 < ‖e (etaMobius M x.1)‖ :=
    (htau x hx).2.2.2.2.2.2.1
  have hQ1 (x : UpperWindow.Parameters) (hx : x ∈ K) : ‖e (etaMobius M x.1)‖ < 1 :=
    (htau x hx).2.2.2.2.2.2.2
  have hq : ContinuousOn (fun x : UpperWindow.Parameters => e x.1) K := by fun_prop
  have hQ : ContinuousOn (fun x : UpperWindow.Parameters => e (etaMobius M x.1)) K := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := exact hT x hx)
  have ha : ContinuousOn (UpperResidueParameters.a p) K := by
    unfold UpperResidueParameters.a
    fun_prop (disch := simp [e_ne_zero])
  have ht : ContinuousOn (UpperResidueParameters.t M) K := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    unfold UpperResidueParameters.t
    fun_prop (disch := exact hT x hx)
  have hb : ContinuousOn (UpperResidueParameters.b M) K :=
    hQ.div ht (fun x hx => e_ne_zero _)
  have hA : ContinuousOn (fun x : UpperWindow.Parameters => UpperWindow.A ℓ x.1 x.2.1) K := by
    unfold UpperWindow.A
    fun_prop (disch := simp [e_ne_zero])
  have hB : ContinuousOn (fun x : UpperWindow.Parameters =>
      UpperWindow.B M h x.1 x.2.1 x.2.2) K := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    unfold UpperWindow.B UpperWindow.C
    fun_prop (disch := simp [e_ne_zero, hT x hx])
  have hqp := continuousOn_qPochhammer _ _ hq hq hq0 hq1
  have hQp := continuousOn_qPochhammer _ _ hQ hQ hQ0 hQ1
  have htp := continuousOn_qPochhammer _ _ ht hQ hQ0 hQ1
  have hap := continuousOn_qPochhammer _ _ ha hq hq0 hq1
  have hpref : ContinuousOn (fun x : UpperWindow.Parameters => UpperResidueParameters.prefactor M x.1) K := by
    have hTc : ContinuousOn (fun x : UpperWindow.Parameters => etaDenom M x.1) K := by fun_prop
    exact (hTc.mul hqp).div hQp (fun x hx => qPochhammer_q_ne_zero _ (hQ0 x hx) (hQ1 x hx))
  have hP : ContinuousOn (fun x : UpperWindow.Parameters => UpperResidueParameters.prefactor M x.1 *
      (qPochhammer (UpperResidueParameters.t M x) (e (etaMobius M x.1)) /
        qPochhammer (UpperResidueParameters.a p x) (e x.1))) K :=
    hpref.mul (htp.div hap (fun x hx => qPochhammer_ne_zero_of_norm_lt_one _ _
      (UpperResidueParameters.six_arguments_norm_lt_one M h ℓ p ψ σ ρ δ hc x (hKD hx)).1
      (hq0 x hx) (hq1 x hx)))
  apply compact_product_majorant hK _ _ _ _ _ _ _ hP ha hA hq hb hB hQ
  · intro x hx
    exact (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x (hKD hx)).2.1
  · intro x hx
    exact (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x (hKD hx)).2.2.2
  · exact hq1
  · exact hQ1

/-- A summable majorant gives uniform convergence along any cofinal finite
exhaustion, without a compactness or continuity assumption. -/
lemma uniform_finset_limit {X ι : Type*} {K : Set X}
    (f : X → ι → ℂ) (F : X → ℂ) (g : ι → ℝ)
    (hg : Summable g) (hbound : ∀ x ∈ K, ∀ k, ‖f x k‖ ≤ g k)
    (hsum : ∀ x ∈ K, HasSum (f x) (F x))
    (s : ℕ → Finset ι) (hex : Tendsto s atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x ∈ K,
      ‖(∑ k ∈ s R, f x k) - F x‖ < ε := by
  have hu := tendstoUniformlyOn_tsum (f := fun k x => f x k) hg
    (fun k x hx => hbound x hx k)
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
    (hex.eventually ((Metric.tendstoUniformlyOn_iff.mp hu) ε hε))
  refine ⟨R₀, ?_⟩
  intro R hR x hx
  have hh := hR₀ R hR x hx
  rw [(hsum x hx).tsum_eq, dist_eq_norm, norm_sub_rev] at hh
  exact hh

/-- The same integer squares used by the finite residue partition. -/
lemma uniform_square_limit {X : Type*} {K : Set X}
    (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (f : X → ℕ × ℕ → ℂ) (F : X → ℂ) (g : ℕ × ℕ → ℝ)
    (hg : Summable g) (hbound : ∀ x ∈ K, ∀ k, ‖f x k‖ ≤ g k)
    (hsum : ∀ x ∈ K, HasSum (f x) (F x)) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x ∈ K,
      ‖UpperResidueIndex.squareSum M R (f x) - F x‖ < ε := by
  have hex : Tendsto (UpperResidueIndex.square M) atTop atTop := by
    apply tendsto_atTop.2
    intro s
    apply (s.eventually_all).2
    intro k hk
    filter_upwards [eventually_ge_atTop (k.1 + k.2 + 1)] with R hR
    have hc : 1 ≤ (M 1 0).toNat := by omega
    have hmul : R ≤ (M 1 0).toNat * R := by nlinarith
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  exact uniform_finset_limit f F g hg hbound hsum (UpperResidueIndex.square M) hex

/-! Local residue calculation. The only singular factor is
`1 - e ((z-z₀)/T)`; all q-product cancellations below are exact cleared
identities. No integral identity or residue coefficient is assumed. -/

section LocalResidues
set_option maxHeartbeats 1000000

lemma exponent_constant_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
    Complex.I_ne_zero

lemma vanishing_factor_limit (T z₀ : ℂ) (hT : T ≠ 0) :
    Tendsto (fun z : ℂ => (z-z₀) / (1-e ((z-z₀)/T))) (𝓝[≠] z₀)
      (𝓝 (-T / (2 * (Real.pi : ℂ) * Complex.I))) := by
  have hd : HasDerivAt (fun z : ℂ => 1-e ((z-z₀)/T))
      (-(2 * (Real.pi : ℂ) * Complex.I) / T) z₀ := by
    have h := ((((hasDerivAt_id z₀).sub_const z₀).div_const T).const_mul
      (2 * (Real.pi : ℂ) * Complex.I)).cexp
    simpa [e, div_eq_mul_inv] using h.const_sub 1
  have hn : -(2 * (Real.pi : ℂ) * Complex.I) / T ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr exponent_constant_ne_zero) hT
  have hh := hd.tendsto_slope.inv₀ hn
  simpa [slope_def_field, e, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh

lemma continuous_qPochhammerNat (q : ℂ) (J : ℕ) :
    Continuous (fun x : ℂ => qPochhammerNat x q J) := by
  unfold qPochhammerNat
  fun_prop

lemma pole_lattice (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (τ : ℂ) (K J : ℕ) (hk : (K,J) ∈ modularPhiPoleLabels M (m+1) n) :
    ∃ l : ℤ,
      modularPhiPolePoint M (m+1) n τ K J = ((K:ℤ)-m : ℤ) * τ + (l:ℂ) ∧
      M 1 1 * ((K:ℤ)-m) - M 1 0 * l + n = -(J:ℤ) := by
  obtain ⟨r, hr⟩ := Int.ModEq.dvd hk
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨-r, ?_, ?_⟩
  · change (_ / (M 1 0 : ℂ)) = _
    apply (div_eq_iff hc).mpr
    have hrC := congrArg (fun t : ℤ => (t:ℂ)) hr
    push_cast at hrC ⊢
    unfold etaDenom
    linear_combination -hrC
  · dsimp at hr
    linear_combination -hr

lemma pole_arguments (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (τ : ℂ) (hτ : 0 < τ.im) (K J : ℕ)
    (hk : (K,J) ∈ modularPhiPoleLabels M (m+1) n) :
    let z₀ := modularPhiPolePoint M (m+1) n τ K J
    (e τ)^(m+1) * e z₀ = (e τ)^(K+1) ∧
      (e (etaMobius M τ))^n * e (z₀/etaDenom M τ) =
        (e (etaMobius M τ))^(-(J:ℤ)) := by
  obtain ⟨l, hl, hbalance⟩ := pole_lattice M hM m n τ K J hk
  dsimp only
  rw [hl]
  constructor
  · rw [e_add', e_intCast, mul_one, ← e_int_mul, ← zpow_add₀ (e_ne_zero τ)]
    convert (zpow_natCast (e τ) (K+1)) using 2 <;> (push_cast; ring)
  · rw [modularPhi_lattice_mobius M _ l τ
      (mem_modularPhiDomain_of_im_pos M hM hτ), e_add', e_intCast, mul_one,
      ← e_int_mul, ← zpow_add₀ (e_ne_zero _)]
    congr 1
    linarith

def backRegular (Q T z₀ : ℂ) (J : ℕ) (z : ℂ) : ℂ :=
  (-e ((z-z₀)/T))^J * Q^(-(UpperContour.triangular J:ℤ)) *
    qPochhammerNat (Q/e ((z-z₀)/T)) Q J * qPochhammer (Q*e ((z-z₀)/T)) Q

lemma backRegular_factor (Q T z₀ : ℂ) (J : ℕ) (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1)
    (z : ℂ) :
    qPochhammer (Q^(-(J:ℤ))*e ((z-z₀)/T)) Q =
      backRegular Q T z₀ J z * (1-e ((z-z₀)/T)) := by
  have hb := UpperContour.qPochhammer_backward_cleared (e ((z-z₀)/T)) Q
    (e_ne_zero _) hQ0 hQ1 J
  have hs := qPochhammer_shift_nat (e ((z-z₀)/T)) Q 1 hQ0 hQ1
  simp only [qPochhammerNat, Finset.prod_range_one, pow_zero, mul_one, pow_one] at hs
  rw [mul_comm (Q^(-(J:ℤ))), hb, hs]
  rw [mul_comm (e ((z-z₀)/T)) Q]
  unfold backRegular
  ring

lemma backRegular_value (Q T z₀ : ℂ) (J : ℕ) :
    backRegular Q T z₀ J z₀ = (-1:ℂ)^J * Q^(-(UpperContour.triangular J:ℤ)) *
      qPochhammerNat Q Q J * qPochhammer Q Q := by
  simp [backRegular, e]

lemma backRegular_continuousAt (Q T z₀ : ℂ) (J : ℕ)
    (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) :
    ContinuousAt (backRegular Q T z₀ J) z₀ := by
  have he : Continuous (fun z : ℂ => e ((z-z₀)/T)) := by unfold e; fun_prop
  have hN : ContinuousAt (fun z : ℂ => qPochhammerNat (Q/e ((z-z₀)/T)) Q J) z₀ :=
    (continuous_qPochhammerNat Q J).continuousAt.comp
    ((continuousAt_const.div he.continuousAt (e_ne_zero _)))
  have hP : ContinuousAt (fun z : ℂ => qPochhammer (Q*e ((z-z₀)/T)) Q) z₀ :=
    ((differentiable_qPochhammer_x Q hQ0 hQ1).continuous.continuousAt).comp
    (continuousAt_const.mul he.continuousAt)
  exact (((he.continuousAt.neg.pow J).mul continuousAt_const).mul hN).mul hP

lemma backRegular_ne_zero (Q T z₀ : ℂ) (J : ℕ)
    (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) :
    backRegular Q T z₀ J z₀ ≠ 0 := by
  rw [backRegular_value]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (norm_pos_iff.mp hQ0)))
    (qPochhammerNat_q_ne_zero Q J hQ0 hQ1)) (qPochhammer_q_ne_zero Q hQ0 hQ1)

lemma quotient_residue_limit (T z₀ : ℂ) (hT : T ≠ 0)
    (N C D B E R : ℂ → ℂ)
    (hN : ContinuousAt N z₀) (hC : ContinuousAt C z₀) (hB : ContinuousAt B z₀)
    (hE : ContinuousAt E z₀) (hR : ContinuousAt R z₀)
    (hBn : B z₀ ≠ 0) (hRn : R z₀ ≠ 0)
    (hD : ∀ z, D z = R z * (1-e ((z-z₀)/T))) :
    Tendsto (fun z => (z-z₀) * ((N z / D z)/(B z/C z)*E z)) (𝓝[≠] z₀)
      (𝓝 ((-T / (2*(Real.pi:ℂ)*Complex.I)) *
        ((N z₀*C z₀)/(R z₀*B z₀))*E z₀)) := by
  have hr : Tendsto (fun z => (N z*C z)/(R z*B z)) (𝓝[≠] z₀)
      (𝓝 ((N z₀*C z₀)/(R z₀*B z₀))) :=
    ((hN.mul hC).div (hR.mul hB) (mul_ne_zero hRn hBn)).tendsto.mono_left nhdsWithin_le_nhds
  have he : Tendsto E (𝓝[≠] z₀) (𝓝 (E z₀)) := hE.tendsto.mono_left nhdsWithin_le_nhds
  convert ((vanishing_factor_limit T z₀ hT).mul hr).mul he using 1
  ext z
  rw [hD]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma arguments_near_pole (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n p : ℤ)
    (τ y : ℂ) (hτ : 0 < τ.im) (K J : ℕ)
    (hk : (K,J) ∈ modularPhiPoleLabels M (m+1) n) (z : ℂ) :
    let z₀ := modularPhiPolePoint M (m+1) n τ K J
    (e τ)^(m+1) * e z = (e τ)^(K+1) * e (z-z₀) ∧
    (e τ)^(m+p) * e (z+y) = ((e τ)^p*e y) * (e τ)^K * e (z-z₀) ∧
    (e (etaMobius M τ))^n * e (z/etaDenom M τ) =
      (e (etaMobius M τ))^(-(J:ℤ)) * e ((z-z₀)/etaDenom M τ) ∧
    (e (etaMobius M τ))^n * e ((z+y)/etaDenom M τ) =
      e (y/etaDenom M τ) * (e (etaMobius M τ))^(-(J:ℤ)) *
        e ((z-z₀)/etaDenom M τ) := by
  let z₀ := modularPhiPolePoint M (m+1) n τ K J
  obtain ⟨ha, hd⟩ := pole_arguments M hM m n τ hτ K J hk
  have hz : e z = e z₀ * e (z-z₀) := by rw [← e_add']; congr 1; ring
  have hzT : e (z/etaDenom M τ) =
      e (z₀/etaDenom M τ) * e ((z-z₀)/etaDenom M τ) := by
    rw [← e_add']; congr 1; ring
  have ham : (e τ)^m * e z₀ = (e τ)^K := by
    apply mul_left_cancel₀ (e_ne_zero τ)
    simpa only [zpow_add_one₀ (e_ne_zero τ), pow_succ', mul_assoc,
      mul_left_comm, mul_comm] using ha
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hz, ← mul_assoc, ha]
  · rw [e_add', hz, zpow_add₀ (e_ne_zero τ)]
    calc
      _ = (e τ)^p * e y * ((e τ)^m * e z₀) * e (z-z₀) := by ring
      _ = _ := by rw [ham]
  · rw [hzT, ← mul_assoc, hd]
  · rw [add_div, e_add', hzT]
    calc
      _ = e (y/etaDenom M τ) * ((e (etaMobius M τ))^n * e (z₀/etaDenom M τ)) *
          e ((z-z₀)/etaDenom M τ) := by ring
      _ = _ := by rw [hd]

lemma coefficient_eq (q Q T a t A C : ℂ) (K J : ℕ)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1)
    (ht : t ≠ 0) (ha : qPochhammer a q ≠ 0) :
    (-T/(2*(Real.pi:ℂ)*Complex.I)) *
      (qPochhammer (q^(K+1)) q * qPochhammer (t*Q^(-(J:ℤ))) Q /
        (((-1:ℂ)^J * Q^(-(UpperContour.triangular J:ℤ)) * qPochhammerNat Q Q J *
          qPochhammer Q Q) * qPochhammer (a*q^K) q)) * (A^K*C^J) =
    (T*qPochhammer q q/qPochhammer Q Q * (qPochhammer t Q/qPochhammer a q) *
      (qBinomialTerm a A q K * qBinomialTerm (Q/t) (t*C) Q J)) /
        (-2*(Real.pi:ℂ)*Complex.I) := by
  have hqK := qPochhammerNat_q_ne_zero q K hq0 hq1
  have hQJ := qPochhammerNat_q_ne_zero Q J hQ0 hQ1
  have hQQ := qPochhammer_q_ne_zero Q hQ0 hQ1
  have hneg : (-1:ℂ)^J ≠ 0 := pow_ne_zero _ (by norm_num)
  have hQpow : Q^(-(UpperContour.triangular J:ℤ)) ≠ 0 :=
    zpow_ne_zero _ (norm_pos_iff.mp hQ0)
  have hns := qPochhammer_shift_nat q q K hq0 hq1
  have hbs := qPochhammer_shift_nat a q K hq0 hq1
  have haK : qPochhammerNat a q K ≠ 0 := by
    intro h
    rw [h, zero_mul] at hbs
    exact ha hbs
  have hn : qPochhammer (q^(K+1)) q = qPochhammer q q/qPochhammerNat q q K := by
    apply (eq_div_iff hqK).mpr
    simpa only [pow_succ', mul_comm] using hns.symm
  have hb : qPochhammer (a*q^K) q = qPochhammer a q/qPochhammerNat a q K := by
    apply (eq_div_iff haK).mpr
    simpa only [mul_comm] using hbs.symm
  rw [hn, hb, UpperContour.qPochhammer_backward_cleared t Q ht hQ0 hQ1 J]
  rw [show (-t)^J = (-1:ℂ)^J*t^J by exact neg_pow t J]
  simp only [qBinomialTerm, mul_pow]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hqK, hQJ, hQQ, haK, ha, hneg, hQpow, hpi]

lemma q_residue_limit_explicit (M : SL(2, ℤ)) (m n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m+1) n) :
    let z₀ := modularPhiPolePoint M (m+1) n x.1 k.1 k.2
    Tendsto (fun z : ℂ => (z-z₀) * UpperContour.qKernel .ratio M m n h ℓ p x z)
      (𝓝[≠] z₀)
      (𝓝 ((UpperResidueParameters.prefactor M x.1 *
        (qPochhammer (UpperResidueParameters.t M x) (e (etaMobius M x.1)) /
          qPochhammer (UpperResidueParameters.a p x) (e x.1)) *
        ratioResidueSeriesTerm (UpperResidueParameters.a p x) (UpperWindow.A ℓ x.1 x.2.1)
          (e x.1) (UpperResidueParameters.b M x) (UpperWindow.B M h x.1 x.2.1 x.2.2)
          (e (etaMobius M x.1)) k) / (-2*(Real.pi:ℂ)*Complex.I))) := by
  let q := e x.1
  let Q := e (etaMobius M x.1)
  let T := etaDenom M x.1
  let z₀ := modularPhiPolePoint M (m+1) n x.1 k.1 k.2
  let a := UpperResidueParameters.a p x
  let t := UpperResidueParameters.t M x
  let A := UpperWindow.A ℓ x.1 x.2.1
  let C := UpperWindow.C M h x.1 x.2.1
  have hτ : 0 < x.1.im := hx.1.1
  have hq0 : 0 < ‖q‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hq1 : ‖q‖ < 1 := norm_e_lt_one ⟨_,hτ⟩
  have hQ0 : 0 < ‖Q‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hQ1 : ‖Q‖ < 1 := norm_e_lt_one ⟨_,m37c_upper_mobius M x.1 hτ⟩
  have hT : T ≠ 0 := etaDenom_ne_zero_of_mem M (mem_modularPhiDomain_of_im_pos M hc.1 hτ)
  have ht : t ≠ 0 := e_ne_zero _
  have ha : qPochhammer a q ≠ 0 :=
    (UpperResidueParameters.infinite_products_ne_zero M h ℓ p ψ σ ρ δ hc x hx).2.2.1
  let N : ℂ → ℂ := fun z => qPochhammer (q^(k.1+1)*e (z-z₀)) q
  let D : ℂ → ℂ := fun z => qPochhammer (Q^(-(k.2:ℤ))*e ((z-z₀)/T)) Q
  let B : ℂ → ℂ := fun z => qPochhammer (a*q^k.1*e (z-z₀)) q
  let H : ℂ → ℂ := fun z => qPochhammer (t*Q^(-(k.2:ℤ))*e ((z-z₀)/T)) Q
  let E : ℂ → ℂ := fun z => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 z)
  have he : Continuous (fun z : ℂ => e (z-z₀)) := by unfold e; fun_prop
  have heT : Continuous (fun z : ℂ => e ((z-z₀)/T)) := by unfold e; fun_prop
  have hN : ContinuousAt N z₀ :=
    (differentiable_qPochhammer_x q hq0 hq1).continuous.continuousAt.comp
      (continuousAt_const.mul he.continuousAt)
  have hB : ContinuousAt B z₀ :=
    (differentiable_qPochhammer_x q hq0 hq1).continuous.continuousAt.comp
      (continuousAt_const.mul he.continuousAt)
  have hH : ContinuousAt H z₀ :=
    (differentiable_qPochhammer_x Q hQ0 hQ1).continuous.continuousAt.comp
      (continuousAt_const.mul heT.continuousAt)
  have hE : ContinuousAt E z₀ := by dsimp [E]; unfold e UpperWindow.phase; fun_prop
  have hN0 : N z₀ = qPochhammer (q^(k.1+1)) q := by simp [N,e]
  have hB0 : B z₀ = qPochhammer (a*q^k.1) q := by simp [B,e]
  have hH0 : H z₀ = qPochhammer (t*Q^(-(k.2:ℤ))) Q := by simp [H,e]
  have hE0 : E z₀ = A^k.1*C^k.2 :=
    UpperResidueParameters.phase_at_pole M hc.1 m n h ℓ x.1 x.2.1 hτ k hk
  have hBn : B z₀ ≠ 0 := by
    rw [hB0]
    intro hz
    have hs := qPochhammer_shift_nat a q k.1 hq0 hq1
    rw [hz,mul_zero] at hs
    exact ha hs
  have hkernel (z : ℂ) : UpperContour.qKernel .ratio M m n h ℓ p x z =
      (N z / D z)/(B z/H z)*E z := by
    obtain ⟨h1,h2,h3,h4⟩ := arguments_near_pole M hc.1 m n p x.1 x.2.2 hτ
      k.1 k.2 hk z
    unfold UpperContour.qKernel modularPhiQProduct modularPhiQNumerator modularPhiQDenominator
    rw [h1,h2,h3,h4]
    rfl
  have hlim := quotient_residue_limit T z₀ hT N H D B E (backRegular Q T z₀ k.2)
    hN hH hB hE (backRegular_continuousAt Q T z₀ k.2 hQ0 hQ1) hBn
    (backRegular_ne_zero Q T z₀ k.2 hQ0 hQ1)
    (backRegular_factor Q T z₀ k.2 hQ0 hQ1)
  rw [hN0,hB0,hH0,hE0,backRegular_value] at hlim
  rw [coefficient_eq q Q T a t A C k.1 k.2 hq0 hq1 hQ0 hQ1 ht ha] at hlim
  convert hlim using 1
  · ext z
    rw [hkernel]
  · rfl

end LocalResidues

end SICLean.L4.UpperRatioResiduesAux
