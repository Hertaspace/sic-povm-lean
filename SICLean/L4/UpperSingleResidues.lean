import SICLean.L4.UpperResidueIndex
import SICLean.L4.UpperResidueParameters
import SICLean.L4.UpperContourClosure
import SICLean.L4.UpperSingleResiduesAux

set_option autoImplicit false

/-!
# Direct single-function residues and the two Euler sums

The proofs use the imported interfaces. This file has no
dependency on UpperRatioResidues, and no limit of a ratio integral occurs.
`weight` is the scaled coefficient -2πi Res.
That it is a residue is a theorem below.
The local q calculation is punctured; it assigns no kernel value at a pole.
[RW26, p. 28, p. 29, (55), (56)] (residue method) and (product comparison).
The single-function calculation is formalized directly.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperSingleResidues
open UpperResidueParameters UpperResidueIndex

/-- Explicit -2πi-scaled candidate; the J factor is Euler at Q*C. -/
def weight (M : SL(2, ℤ)) (h ℓ : ℤ) (x : UpperWindow.Parameters)
    (k : ℕ × ℕ) : ℂ :=
  prefactor M x.1 * singleResidueSeriesTerm (UpperWindow.A ℓ x.1 x.2.1)
    (UpperWindow.C M h x.1 x.2.1) (e x.1) (e (etaMobius M x.1)) k

/--
[RW26, p. 29] (residue method).
This is a limit on a punctured neighborhood, never the center value.
-/
theorem q_residue_limit (M : SL(2, ℤ)) (m n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    let z₀ := modularPhiPolePoint M (m + 1) n x.1 k.1 k.2
    Tendsto (fun z : ℂ => (z - z₀) * UpperContour.qKernel .single M m n h ℓ p x z)
      (𝓝[≠] z₀) (𝓝 (weight M h ℓ x k / (-2 * (Real.pi : ℂ) * Complex.I))) := by
  exact UpperSingleResiduesAux.single_qKernel_residue M hc.1 m n h ℓ p x hx.1.1 k hk

/--
[RW26, p. 29].
Transfer by qKernel germ and simpleResidue_germ_congr.
-/
theorem scaled_residue (M : SL(2, ℤ)) (m n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (k : ℕ × ℕ)
    (hk : k ∈ modularPhiPoleLabels M (m + 1) n) :
    -2 * (Real.pi : ℂ) * Complex.I *
      UpperContour.simpleResidue (UpperContour.kernel .single M m n h ℓ p x)
        (modularPhiPolePoint M (m + 1) n x.1 k.1 k.2) = weight M h ℓ x k := by
  rw [UpperContour.simpleResidue_germ_congr _ _ _
    (UpperContour.kernel_eq_qKernel_germ .single M hc.1 m n h ℓ p x hx.1.1 _)]
  unfold UpperContour.simpleResidue
  rw [(q_residue_limit M m n h ℓ p ψ σ ρ δ hc x hx k hk).limUnder_eq]
  have hscale : -2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp

/--
[RW26, p. 28, (56)].
Absolute convergence of the K sum, before summing J.
-/
theorem K_summable_norm (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Summable (fun K : ℕ => ‖eulerInverseTerm (UpperWindow.A ℓ x.1 x.2.1) (e x.1) K‖) := by
  have hτ := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  exact summable_norm_eulerInverseTerm _ _
    (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx).2.1
    hτ.2.2.2.2.1 hτ.2.2.2.2.2.1

/--
[RW26, p. 28, (55)].
C is unrestricted; in particular |C|<1 is not assumed.
-/
theorem J_summable_norm (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ C : ℂ) (hτ : 0 < τ.im) :
    Summable (fun J : ℕ => ‖eulerTerm (e (etaMobius M τ) * C) (e (etaMobius M τ)) J‖) := by
  exact summable_norm_eulerTerm _ _ (norm_pos_iff.mpr (e_ne_zero _))
    (norm_e_lt_one ⟨_, m37c_upper_mobius M τ hτ⟩)

/--
[RW26, p. 28, (56)].
First Euler formula with its own convergence and nonzero denominator.
-/
theorem K_hasSum (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    HasSum (eulerInverseTerm (UpperWindow.A ℓ x.1 x.2.1) (e x.1))
      (qPochhammer (UpperWindow.A ℓ x.1 x.2.1) (e x.1))⁻¹ := by
  have hτ := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  exact hasSum_eulerInverse _ _
    (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx).2.1
    hτ.2.2.2.2.1 hτ.2.2.2.2.2.1

/--
[RW26, p. 28, (55)]. All-C Euler theorem. The argument is Q*C, not C.
-/
theorem J_hasSum (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ C : ℂ) (hτ : 0 < τ.im) :
    HasSum (eulerTerm (e (etaMobius M τ) * C) (e (etaMobius M τ)))
      (qPochhammer (e (etaMobius M τ) * C) (e (etaMobius M τ))) := by
  exact hasSum_euler _ _ (norm_pos_iff.mpr (e_ne_zero _))
    (norm_e_lt_one ⟨_, m37c_upper_mobius M τ hτ⟩)

/--
[RW26, p. 28, (55), (56)]. Absolute convergence of the scaled double coefficient.
-/
theorem weight_summable_norm (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Summable (fun k : ℕ × ℕ => ‖weight M h ℓ x k‖) := by
  have hτ := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have hs := summable_norm_singleResidueSeriesTerm
    (UpperWindow.A ℓ x.1 x.2.1) (UpperWindow.C M h x.1 x.2.1)
    (e x.1) (e (etaMobius M x.1))
    (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx).2.1
    hτ.2.2.2.2.1 hτ.2.2.2.2.2.1 hτ.2.2.2.2.2.2.1 hτ.2.2.2.2.2.2.2
  simpa only [weight, norm_mul] using hs.mul_left ‖prefactor M x.1‖

/--
[RW26, p. 28, (55), (56)]. Both iterated orders follow after absolute convergence.
-/
theorem double_tsum_orders (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    (∑' k, weight M h ℓ x k) = (∑' K, ∑' J, weight M h ℓ x (K, J)) ∧
      (∑' K, ∑' J, weight M h ℓ x (K, J)) =
        (∑' J, ∑' K, weight M h ℓ x (K, J)) := by
  exact tsum_orders _ (weight_summable_norm M h ℓ p ψ σ ρ δ hc x hx)

/--
[RW26, p. 28, (55), (56)]. Direct Euler evaluation; no ratio limit is permitted.
-/
theorem weight_hasSum_product (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    HasSum (weight M h ℓ x) (singleProduct M h ℓ x) := by
  have hτ := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have hA := (UpperWindow.AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x hx).2.1
  exact (hasSum_singleResidue _ _ _ _ hA hτ.2.2.2.2.1 hτ.2.2.2.2.2.1
    hτ.2.2.2.2.2.2.1 hτ.2.2.2.2.2.2.2
    (qPochhammer_ne_zero_of_norm_lt_one _ _ hA hτ.2.2.2.2.1
      hτ.2.2.2.2.2.1)).mul_left (prefactor M x.1)

/--
[RW26, p. 29]. This identity is finite, including R=0.
-/
theorem finite_box_sum (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) :
    -2 * (Real.pi : ℂ) * Complex.I *
      (∑ m ∈ Finset.range (M 1 0).toNat,
        UpperContour.residueBox (UpperContour.kernel .single M (m : ℤ) n h ℓ p x)
          M (m : ℤ) n x.1 R) = squareSum M R (weight M h ℓ x) := by
  rw [← sum_boxes_eq_square M hc.1 n R (weight M h ℓ x)]
  simp only [UpperContour.residueBox, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  exact scaled_residue M (m : ℤ) n h ℓ p ψ σ ρ δ hc x hx k
    (by simpa [modularPhiPoleLabels] using
      ((UpperContour.mem_boxLabels M (m : ℤ) n R k.1 k.2).mp hk).2.2)

/--
[RW26, p. 29]. All four finite sides remain present before R→∞.
-/
theorem finite_clockwise_sum (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) (hR : 1 ≤ R) :
    (∑ m ∈ Finset.range (M 1 0).toNat,
      UpperContour.clockwiseBoundary (UpperContour.kernel .single M (m : ℤ) n h ℓ p x)
        (UpperWindow.base M (m : ℤ) n δ x.1) (etaDenom M x.1) R) =
      squareSum M R (weight M h ℓ x) := by
  calc
    _ = ∑ m ∈ Finset.range (M 1 0).toNat,
        -2 * (Real.pi : ℂ) * Complex.I *
          UpperContour.residueBox (UpperContour.kernel .single M (m : ℤ) n h ℓ p x)
            M (m : ℤ) n x.1 R := by
      apply Finset.sum_congr rfl
      intro m hm
      exact UpperContour.finite_clockwise_residue .single M h ℓ p (m : ℤ) n
        ψ σ ρ δ hc x hx R hR
    _ = _ := by
      rw [← Finset.mul_sum]
      exact finite_box_sum M n h ℓ p ψ σ ρ δ hc x hx R

/--
[RW26, p. 28, p. 29, (55), (56)]. Integer finite-box limit export.
-/
theorem integer_box_limit (M : SL(2, ℤ)) (n h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    Tendsto (fun R : ℕ => -2 * (Real.pi : ℂ) * Complex.I *
      (∑ m ∈ Finset.range (M 1 0).toNat,
        UpperContour.residueBox (UpperContour.kernel .single M (m : ℤ) n h ℓ p x)
          M (m : ℤ) n x.1 R)) atTop (𝓝 (singleProduct M h ℓ x)) := by
  simp_rw [finite_box_sum M n h ℓ p ψ σ ρ δ hc x hx]
  rw [← (weight_hasSum_product M h ℓ p ψ σ ρ δ hc x hx).tsum_eq]
  exact squareSum_tendsto M hc.1 _ (weight_summable_norm M h ℓ p ψ σ ρ δ hc x hx)

/--
[RW26, p. 28, (55), (56)]. Compact normal convergence.
K stays in Im τ>0; it may be empty.
-/
theorem compact_majorant (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKD : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∃ g : ℕ × ℕ → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∀ x ∈ K, ∀ k, ‖weight M h ℓ x k‖ ≤ g k := by
  simpa only [weight, UpperSingleResiduesAux.rawWeight] using
    UpperSingleResiduesAux.rawWeight_compact_majorant M h ℓ p ψ σ ρ δ hc K hK hKD

/--
[RW26, p. 28, (55), (56)].
Uniform convergence on each compact subset, with the same integer squares.
-/
theorem compact_square_limit (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (K : Set UpperWindow.Parameters)
    (hK : IsCompact K) (hKD : K ⊆ UpperWindow.domain M h ℓ p ψ σ ρ δ) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x ∈ K,
      ‖squareSum M R (weight M h ℓ x) - singleProduct M h ℓ x‖ < ε := by
  obtain ⟨g, _, hg, hbound⟩ := compact_majorant M h ℓ p ψ σ ρ δ hc K hK hKD
  exact UpperSingleResiduesAux.square_limit_of_majorant M hc.1 K
    (weight M h ℓ) (singleProduct M h ℓ) g hg hbound
    (fun x hx => weight_hasSum_product M h ℓ p ψ σ ρ δ hc x (hKD hx))

#print weight
#check UpperContour.residueBox_eq_qKernel
#check hasSum_eulerInverse
#check hasSum_euler
#check q_residue_limit
#check weight_hasSum_product
#check integer_box_limit

end SICLean.L4.UpperSingleResidues
