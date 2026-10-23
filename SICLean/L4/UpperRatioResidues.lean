import SICLean.L4.UpperResidueIndex
import SICLean.L4.UpperResidueParameters
import SICLean.L4.UpperContourClosure
import SICLean.L4.UpperRatioResiduesAux

set_option autoImplicit false

/-!
# Ratio residues and two independent q-binomial sums

There is no dependency on UpperSingleResidues. The full coordinate box supplies the nonzero
(a;q)∞ in the residue prefactor; |A|,|B|<1 alone would not supply it.
Finite diagonal denominators, infinite prefactor denominators, each
one-variable series, and the product-index sum are checked separately.
The kernel at a numerator pole is never evaluated by a raw 0/0 quotient. [RW26, p. 28, p. 29, (58),
Appendix A.2].
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperRatioResidues
open UpperResidueParameters UpperResidueIndex

/-- Explicit candidate for -2πi Res, with b=Q/t. No residue property in the body. -/
def weight (M : SL(2, ℤ)) (h ℓ p : ℤ) (x : UpperWindow.Parameters)
    (k : ℕ × ℕ) : ℂ :=
  prefactor M x.1 * (qPochhammer (t M x) (e (etaMobius M x.1)) /
    qPochhammer (a p x) (e x.1)) *
    ratioResidueSeriesTerm (a p x) (UpperWindow.A ℓ x.1 x.2.1) (e x.1)
      (b M x) (UpperWindow.B M h x.1 x.2.1 x.2.2) (e (etaMobius M x.1)) k

/--
[RW26, p. 29]. Differentiate the one vanishing
Q-factor in a punctured germ; the nonzero (a;q)∞ is proved separately.
-/
theorem q_residue_limit (M : SL(2, ℤ)) (m n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    let z₀ := modularPhiPolePoint M (m + 1) n x.1 k.1 k.2
    Tendsto (fun z : ℂ => (z - z₀) * UpperContour.qKernel .ratio M m n h ℓ p x z)
      (𝓝[≠] z₀) (𝓝 (weight M h ℓ p x k / (-2 * (Real.pi : ℂ) * Complex.I))) := by
  simpa only [weight] using UpperRatioResiduesAux.q_residue_limit_explicit
    M m n h ℓ p ψ σ ρ δ hc x hx k hk

/--
[RW26, p. 29].
The actual Φ representative is reached through a punctured germ.
-/
theorem scaled_residue (M : SL(2, ℤ)) (m n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    -2 * (Real.pi : ℂ) * Complex.I *
      UpperContour.simpleResidue (UpperContour.kernel .ratio M m n h ℓ p x)
        (modularPhiPolePoint M (m + 1) n x.1 k.1 k.2) = weight M h ℓ p x k := by
  rw [UpperContour.simpleResidue_germ_congr _ _ _
    (UpperContour.kernel_eq_qKernel_germ .ratio M hc.1 m n h ℓ p x hx.1.1 _)]
  unfold UpperContour.simpleResidue
  rw [(q_residue_limit M m n h ℓ p ψ σ ρ δ hc x hx k hk).limUnder_eq]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/--
[RW26, p. 28, p. 29, (58)]. The first one-variable absolute convergence check.
-/
theorem K_summable_norm (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Summable (fun K : ℕ =>
      ‖qBinomialTerm (a p x) (UpperWindow.A ℓ x.1 x.2.1) (e x.1) K‖) := by
  exact summable_norm_qBinomialTerm _ _ _
    (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx).2.1
    (norm_pos_iff.mpr (e_ne_zero _)) (norm_e_lt_one ⟨x.1, hx.1.1⟩)

/--
[RW26, p. 28, p. 29, (58)]. No bound on the numerator parameter b is needed.
-/
theorem J_summable_norm (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Summable (fun J : ℕ => ‖qBinomialTerm (b M x)
      (UpperWindow.B M h x.1 x.2.1 x.2.2) (e (etaMobius M x.1)) J‖) := by
  have ht := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  exact summable_norm_qBinomialTerm _ _ _
    (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx).2.2.2
    ht.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2

/--
[RW26, p. 28, p. 29, (58)]. The first q-binomial theorem, with |A|<1.
-/
theorem K_hasSum (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    HasSum (qBinomialTerm (a p x) (UpperWindow.A ℓ x.1 x.2.1) (e x.1))
      (qPochhammer (a p x * UpperWindow.A ℓ x.1 x.2.1) (e x.1) /
        qPochhammer (UpperWindow.A ℓ x.1 x.2.1) (e x.1)) := by
  have hA := (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx).2.1
  have hq0 := norm_pos_iff.mpr (e_ne_zero x.1)
  have hq1 := norm_e_lt_one (⟨x.1, hx.1.1⟩ : UpperHalfPlane)
  exact hasSum_qBinomial _ _ _ hA hq0 hq1
    (qPochhammer_ne_zero_of_norm_lt_one _ _ hA hq0 hq1)

/--
[RW26, p. 28, p. 29, (58)]. The second q-binomial theorem, with bB=QC.
-/
theorem J_hasSum (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    HasSum (qBinomialTerm (b M x) (UpperWindow.B M h x.1 x.2.1 x.2.2)
      (e (etaMobius M x.1)))
      (qPochhammer (e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1)
        (e (etaMobius M x.1)) /
        qPochhammer (UpperWindow.B M h x.1 x.2.1 x.2.2) (e (etaMobius M x.1))) := by
  have ht := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have hB := (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx).2.2.2
  have hQ0 := ht.2.2.2.2.2.2.1
  have hQ1 := ht.2.2.2.2.2.2.2
  have hs := hasSum_qBinomial (b M x) _ _ hB hQ0 hQ1
    (qPochhammer_ne_zero_of_norm_lt_one _ _ hB hQ0 hQ1)
  have harg : b M x * UpperWindow.B M h x.1 x.2.1 x.2.2 =
      e (etaMobius M x.1) * UpperWindow.C M h x.1 x.2.1 := by
    simp [b, UpperWindow.B, t, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      e_ne_zero]
  rw [harg] at hs
  exact hs

/--
[RW26, p. 28, p. 29, (58)]. Absolute convergence of the scaled double coefficients.
-/
theorem weight_summable_norm (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Summable (fun k : ℕ × ℕ => ‖weight M h ℓ p x k‖) := by
  have ht := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have hab := UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx
  have hs := summable_norm_ratioResidueSeriesTerm (a p x) _ _ (b M x) _ _
    hab.2.1 hab.2.2.2 ht.2.2.2.2.1 ht.2.2.2.2.2.1
    ht.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2
  simpa only [weight, norm_mul] using hs.mul_left
    ‖prefactor M x.1 * (qPochhammer (t M x) (e (etaMobius M x.1)) /
      qPochhammer (a p x) (e x.1))‖

/--
[RW26, p. 28, p. 29, (58)]. Both iterated orders after absolute convergence.
-/
theorem double_tsum_orders (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    (∑' k, weight M h ℓ p x k) = (∑' K, ∑' J, weight M h ℓ p x (K, J)) ∧
      (∑' K, ∑' J, weight M h ℓ p x (K, J)) =
        (∑' J, ∑' K, weight M h ℓ p x (K, J)) := by
  have hs := (weight_summable_norm M h ℓ p ψ σ ρ δ hc x hx).of_norm
  refine ⟨hs.tsum_prod, ?_⟩
  have hsc : Summable (Function.uncurry (fun K J => weight M h ℓ p x (K, J))) := hs
  exact hsc.tsum_comm.symm

/--
[RW26, p. 28, p. 29, (58)]. Combine the two justified q-binomial sums.
-/
theorem weight_hasSum_product (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    HasSum (weight M h ℓ p x) (ratioProduct M h ℓ p x) := by
  have hs : Summable (fun k : ℕ × ℕ =>
      qBinomialTerm (a p x) (UpperWindow.A ℓ x.1 x.2.1) (e x.1) k.1 *
        qBinomialTerm (b M x) (UpperWindow.B M h x.1 x.2.1 x.2.2)
          (e (etaMobius M x.1)) k.2) := by
    have ht := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
    have hab := UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx
    exact (summable_norm_ratioResidueSeriesTerm (a p x) _ _ (b M x) _ _
      hab.2.1 hab.2.2.2 ht.2.2.2.2.1 ht.2.2.2.2.2.1
      ht.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2).of_norm
  have hsum := ((K_hasSum M h ℓ p ψ σ ρ δ hc x hx).mul
    (J_hasSum M h ℓ p ψ σ ρ δ hc x hx) hs).mul_left
      (prefactor M x.1 * (qPochhammer (t M x) (e (etaMobius M x.1)) /
        qPochhammer (a p x) (e x.1)))
  change HasSum (fun k => weight M h ℓ p x k) _
  simpa only [weight, ratioResidueSeriesTerm, ratioProduct, mul_assoc] using hsum

/--
[RW26, p. 29]. The residue-class partition is performed finitely.
-/
theorem finite_box_sum (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) :
    -2 * (Real.pi : ℂ) * Complex.I *
      (∑ m ∈ Finset.range (M 1 0).toNat,
        UpperContour.residueBox (UpperContour.kernel .ratio M (m : ℤ) n h ℓ p x)
          M (m : ℤ) n x.1 R) = squareSum M R (weight M h ℓ p x) := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ m ∈ Finset.range (M 1 0).toNat,
        ∑ k ∈ UpperContour.boxLabels M (m : ℤ) n R, weight M h ℓ p x k := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [UpperContour.residueBox, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact scaled_residue M (m : ℤ) n h ℓ p ψ σ ρ δ hc x hx k
        (Finset.mem_filter.mp hk).2
    _ = _ := sum_boxes_eq_square M hc.1 n R _

/--
[RW26, p. 29]. Finite contour identity with all four sides retained.
-/
theorem finite_clockwise_sum (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) (hR : 1 ≤ R) :
    (∑ m ∈ Finset.range (M 1 0).toNat,
      UpperContour.clockwiseBoundary (UpperContour.kernel .ratio M (m : ℤ) n h ℓ p x)
        (UpperWindow.base M (m : ℤ) n δ x.1) (etaDenom M x.1) R) =
      squareSum M R (weight M h ℓ p x) := by
  rw [← finite_box_sum M n h ℓ p ψ σ ρ δ hc x hx R, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact UpperContour.finite_clockwise_residue .ratio M h ℓ p (m : ℤ) n
    ψ σ ρ δ hc x hx R hR

/--
[RW26, p. 28, p. 29, (58)]. Integer finite-box limit export.
-/
theorem integer_box_limit (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => -2 * (Real.pi : ℂ) * Complex.I *
      (∑ m ∈ Finset.range (M 1 0).toNat,
        UpperContour.residueBox (UpperContour.kernel .ratio M (m : ℤ) n h ℓ p x)
          M (m : ℤ) n x.1 R)) atTop (𝓝 (ratioProduct M h ℓ p x)) := by
  have hs := squareSum_tendsto M hc.1 (weight M h ℓ p x)
    (weight_summable_norm M h ℓ p ψ σ ρ δ hc x hx)
  rw [(weight_hasSum_product M h ℓ p ψ σ ρ δ hc x hx).tsum_eq] at hs
  simpa only [finite_box_sum M n h ℓ p ψ σ ρ δ hc x hx] using hs

/--
[RW26, p. 28, (58)] (series input). Normal convergence on compact
subsets holds; no Im τ↓0 uniformity is asserted.
-/
theorem compact_majorant (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKD : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ g : ℕ × ℕ → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∀ x ∈ K, ∀ k, ‖weight M h ℓ p x k‖ ≤ g k := by
  simpa only [weight] using UpperRatioResiduesAux.compact_weight_majorant
    M h ℓ p ψ σ ρ δ hc K hK hKD

/--
[RW26, p. 28, (58)].
Uniform limit on the initial compact box family, along integer R.
-/
theorem compact_square_limit (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKD : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x ∈ K,
      ‖squareSum M R (weight M h ℓ p x) - ratioProduct M h ℓ p x‖ < ε := by
  obtain ⟨g, -, hg, hb⟩ := compact_majorant M h ℓ p ψ σ ρ δ hc K hK hKD
  exact UpperRatioResiduesAux.uniform_square_limit M hc.1
    (weight M h ℓ p) (ratioProduct M h ℓ p) g hg hb
    (fun x hx => weight_hasSum_product M h ℓ p ψ σ ρ δ hc x (hKD hx))

#print weight
#check UpperContour.kernel_eq_qKernel_germ
#check hasSum_qBinomial
#check q_residue_limit
#check weight_hasSum_product
#check integer_box_limit

end SICLean.L4.UpperRatioResidues
