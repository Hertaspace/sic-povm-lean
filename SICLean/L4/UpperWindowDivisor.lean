import SICLean.L4.UpperWindowParameters
import SICLean.L4.ModularDivisor
import SICLean.L4.UpperWindowDivisorAux

set_option autoImplicit false

/-!
# Actual divisor separation and templates

The divisor is exactly
the labeled divisor of the existing modularPhi, not a new pole model.
Coordinate identities hold for every candidate K,J, so in particular for
the labels satisfying the two different existing congruences.
[RW26, p. 6, p. 28, Appendix A.2].

Unit-domain membership below excludes both poles and zeros of the actual
specified representative. Thus it is safe for point values and reciprocals,
unlike a statement only about the meromorphic germ of a reciprocal. No
germ equality is used to assign a value at a common q-product zero.
-/

noncomputable section
open Complex Set
open scoped Topology MatrixGroups

namespace SICLean.L4.UpperWindow

def base (M : SL(2, ℤ)) (m n : ℤ) (δ : ℝ) (τ : ℂ) : ℂ :=
  ((n : ℂ) - (m : ℂ) * etaDenom M τ) / (M 1 0 : ℂ) -
    (δ : ℂ) * (etaDenom M τ + 1)

/-- Increasing t gives the required upward orientation. -/
def line (M : SL(2, ℤ)) (m n : ℤ) (ψ δ : ℝ) (τ : ℂ) (t : ℝ) : ℂ :=
  base M m n δ τ + (t : ℂ) * (Complex.I * rotation ψ)

def templates (M : SL(2, ℤ)) (m n : ℤ) (δ : ℝ) (τ : ℂ) : Set ℂ :=
  (fun u : ℝ => base M m n δ τ + (u : ℂ)) '' Icc 0 1 ∪
    (fun u : ℝ => base M m n δ τ + (u : ℂ) * etaDenom M τ) '' Icc 0 1

def aArg (m : ℤ) (τ z : ℂ) : ℂ := (e τ) ^ (m + 1) * e z

def bArg (m p : ℤ) (τ y z : ℂ) : ℂ := (e τ) ^ (m + p) * e (z + y)

def dArg (M : SL(2, ℤ)) (n : ℤ) (τ z : ℂ) : ℂ :=
  (e (etaMobius M τ)) ^ n * e (z / etaDenom M τ)

def cArg (M : SL(2, ℤ)) (n : ℤ) (τ y z : ℂ) : ℂ :=
  (e (etaMobius M τ)) ^ n * e ((z + y) / etaDenom M τ)

/-- The actual E_m. -/
def phase (M : SL(2, ℤ)) (m n h ℓ : ℤ) (τ w z : ℂ) : ℂ :=
  (((M 1 0 : ℂ) * z - (n : ℂ) + etaDenom M τ * (m : ℂ)) * w) /
      etaDenom M τ +
    (ℓ : ℂ) * (z + (m : ℂ) * τ) +
    (h : ℂ) * (z / etaDenom M τ + (n : ℂ) * etaMobius M τ)

def singleKernel (M : SL(2, ℤ)) (m n h ℓ : ℤ) (τ w z : ℂ) : ℂ :=
  modularPhi M (m + 1) n z τ * e (phase M m n h ℓ τ w z)

def ratioKernel (M : SL(2, ℤ)) (m n h ℓ p : ℤ) (τ w y z : ℂ) : ℂ :=
  (modularPhi M (m + 1) n z τ / modularPhi M (m + p) n (z + y) τ) *
    e (phase M m n h ℓ τ w z)

/--
Exact positive-cone coordinates, before restricting to pole labels; [RW26, p. 6].
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem numerator_pole_coords (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (δ : ℝ) (τ : ℂ) (hτ : τ.im ≠ 0) (K J : ℕ) :
    coords (etaDenom M τ) (modularPhiPolePoint M (m + 1) n τ K J - base M m n δ τ) =
      (δ + (K : ℝ) / (M 1 0 : ℝ), δ + (J : ℝ) / (M 1 0 : ℝ)) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  apply (coords_eq_iff _ _ (denom_im_ne_zero M hM τ hτ) _ _).mpr
  unfold modularPhiPolePoint base
  push_cast
  field_simp
  <;> ring

/--
General-y negative-cone formula; at the center H_T=H_1=ρ; [RW26, p. 6].
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem inverse_denominator_pole_coords (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n p : ℤ) (δ : ℝ) (τ y : ℂ) (hτ : τ.im ≠ 0) (K J : ℕ) :
    let H := coords (etaDenom M τ) (height M p τ y)
    coords (etaDenom M τ)
      (modularPhiZeroPoint M (m + p) n τ K J - y - base M m n δ τ) =
      (δ - (H.1 + (K : ℝ)) / (M 1 0 : ℝ),
        δ - (H.2 + (J : ℝ)) / (M 1 0 : ℝ)) := by
  dsimp only
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hH := coords_reconstruct (etaDenom M τ) (height M p τ y)
    (denom_im_ne_zero M hM τ hτ)
  apply (coords_eq_iff _ _ (denom_im_ne_zero M hM τ hτ) _ _).mpr
  unfold modularPhiZeroPoint base
  push_cast
  field_simp
  unfold height at hH ⊢
  linear_combination hH

/--
Other two divisor families, needed for actual reciprocal point values.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem other_divisor_coords (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n p : ℤ) (δ : ℝ) (τ y : ℂ) (hτ : τ.im ≠ 0) (K J : ℕ) :
    let H := coords (etaDenom M τ) (height M p τ y)
    coords (etaDenom M τ) (modularPhiZeroPoint M (m + 1) n τ K J - base M m n δ τ) =
      (δ - (1 + (K : ℝ)) / (M 1 0 : ℝ), δ - (1 + (J : ℝ)) / (M 1 0 : ℝ)) ∧
    coords (etaDenom M τ)
      (modularPhiPolePoint M (m + p) n τ K J - y - base M m n δ τ) =
      (δ + (1 + (K : ℝ) - H.1) / (M 1 0 : ℝ),
        δ + (1 + (J : ℝ) - H.2) / (M 1 0 : ℝ)) := by
  dsimp only
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  constructor
  · apply (coords_eq_iff _ _ (denom_im_ne_zero M hM τ hτ) _ _).mpr
    unfold modularPhiZeroPoint base
    push_cast
    field_simp
    <;> ring
  · have hH := coords_reconstruct (etaDenom M τ) (height M p τ y)
      (denom_im_ne_zero M hM τ hτ)
    apply (coords_eq_iff _ _ (denom_im_ne_zero M hM τ hτ) _ _).mpr
    unfold modularPhiPolePoint base
    push_cast
    field_simp
    unfold height at hH ⊢
    linear_combination hH

/--
The centered negative-cone formula.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem center_inverse_denominator_coords (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n p : ℤ) (ρ δ : ℝ) (τ : ℂ) (hτ : τ.im ≠ 0) (K J : ℕ) :
    coords (etaDenom M τ)
      (modularPhiZeroPoint M (m + p) n τ K J - centerY M p ρ τ - base M m n δ τ) =
      (δ - ρ / (M 1 0 : ℝ) - (K : ℝ) / (M 1 0 : ℝ),
        δ - ρ / (M 1 0 : ℝ) - (J : ℝ) / (M 1 0 : ℝ)) := by
  have hT := denom_im_ne_zero M hM τ hτ
  have hH := (center_equations M hM 0 0 p 0 ρ τ).2
  rw [inverse_denominator_pole_coords M hM m n p δ τ _ hτ,
    hH, show (ρ : ℂ) * (etaDenom M τ + 1) =
      (ρ : ℂ) * etaDenom M τ + (ρ : ℂ) by ring,
    coords_real_combination _ hT]
  apply Prod.ext <;> dsimp only <;> ring

/--
All candidate branches, hence both actual labeled divisor families,
have the required strict signs on one common domain.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem pole_coordinate_signs (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ)
    (K J : ℕ) :
    let P := coords (etaDenom M x.1)
      (modularPhiPolePoint M (m + 1) n x.1 K J - base M m n δ x.1)
    let Z := coords (etaDenom M x.1)
      (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2 - base M m n δ x.1)
    0 < P.1 ∧ 0 < P.2 ∧ Z.1 < 0 ∧ Z.2 < 0 := by
  dsimp only
  have hτ : x.1.im ≠ 0 := ne_of_gt hx.1.1
  have hineq := coordinate_inequalities M h ℓ p ψ σ ρ δ hc x hx
  have hcR : (0 : ℝ) < M 1 0 := by exact_mod_cast hc.1
  rw [numerator_pole_coords M hc.1 m n δ x.1 hτ K J,
    inverse_denominator_pole_coords M hc.1 m n p δ x.1 x.2.2 hτ K J]
  dsimp only
  refine ⟨add_pos_of_pos_of_nonneg hc.2.2.2.2.2.2.1 (div_nonneg (Nat.cast_nonneg K) hcR.le),
    add_pos_of_pos_of_nonneg hc.2.2.2.2.2.2.1 (div_nonneg (Nat.cast_nonneg J) hcR.le), ?_, ?_⟩
  · have hd : δ < ((coords (etaDenom M x.1) (height M p x.1 x.2.2)).1 + K) /
        (M 1 0 : ℝ) := (lt_div_iff₀ hcR).mpr (by nlinarith [hineq.2.2.1, (show (0 : ℝ) ≤ K from Nat.cast_nonneg K)])
    linarith
  · have hd : δ < ((coords (etaDenom M x.1) (height M p x.1 x.2.2)).2 + J) /
        (M 1 0 : ℝ) := (lt_div_iff₀ hcR).mpr (by nlinarith [hineq.2.2.2.1, (show (0 : ℝ) ≤ J from Nat.cast_nonneg J)])
    linarith

/--
Actual pole families lie on opposite sides of the oriented tilted line; [RW26, p. 28].
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem pole_sides (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ)
    (K J : ℕ) :
    0 < side ψ (modularPhiPolePoint M (m + 1) n x.1 K J - base M m n δ x.1) ∧
      side ψ (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2 - base M m n δ x.1) < 0 := by
  have hτ : x.1.im ≠ 0 := ne_of_gt hx.1.1
  have hT := denom_im_ne_zero M hc.1 x.1 hτ
  have hh := pole_coordinate_signs M h ℓ p m n ψ σ ρ δ hc x hx K J
  have hp := coords_reconstruct (etaDenom M x.1)
    (modularPhiPolePoint M (m + 1) n x.1 K J - base M m n δ x.1) hT
  have hz := coords_reconstruct (etaDenom M x.1)
    (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2 - base M m n δ x.1) hT
  constructor
  · rw [← hp]
    exact side_positive_combination _ _ _ _ hx.1.2.1 hx.1.2.2 hc.2.2.1 hh.1 hh.2.1
  · rw [← hz]
    exact side_negative_combination _ _ _ _ hx.1.2.1 hx.1.2.2 hc.2.2.1 hh.2.2.1 hh.2.2.2

/--
Disjointness retains the two different divisor congruences; no equivalence with the later
real-boundary pinch set.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem no_pinch (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    Disjoint ((fun k : ℕ × ℕ => modularPhiPolePoint M (m + 1) n x.1 k.1 k.2) ''
      modularPhiPoleLabels M (m + 1) n)
      ((fun k : ℕ × ℕ => modularPhiZeroPoint M (m + p) n x.1 k.1 k.2 - x.2.2) ''
        modularPhiZeroLabels M (m + p) n) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨k, hk, rfl⟩ ⟨j, hj, heq⟩
  have hp := (pole_sides M h ℓ p m n ψ σ ρ δ hc x hx k.1 k.2).1
  have hz := (pole_sides M h ℓ p m n ψ σ ρ δ hc x hx j.1 j.2).2
  dsimp only at heq
  rw [heq] at hz
  linarith

/--
Both actual Φ values are units on the entire tilted line.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem line_divisor_free (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ)
    (t : ℝ) :
    (line M m n ψ δ x.1 t, x.1) ∈ modularPhiNonvanishingDomain M (m + 1) n ∧
      (line M m n ψ δ x.1 t + x.2.2, x.1) ∈ modularPhiNonvanishingDomain M (m + p) n := by
  have hτ : x.1.im ≠ 0 := ne_of_gt hx.1.1
  have hTi := denom_im_ne_zero M hc.1 x.1 hτ
  have hD := (tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).1
  have hs (K J : ℕ) := window_affine_signs M h ℓ p ψ σ ρ δ hc x hx K J
  have havoid (q : ℂ)
      (hq : (0 < (coords (etaDenom M x.1) (q - base M m n δ x.1)).1 ∧
          0 < (coords (etaDenom M x.1) (q - base M m n δ x.1)).2) ∨
        ((coords (etaDenom M x.1) (q - base M m n δ x.1)).1 < 0 ∧
          (coords (etaDenom M x.1) (q - base M m n δ x.1)).2 < 0)) :
      line M m n ψ δ x.1 t ≠ q := by
    intro he
    apply tilted_ne_cone _ ψ t _ hx.1.2.1 hx.1.2.2 hc.2.2.1 hTi hq
    simpa only [line, add_sub_cancel_left] using congrArg (fun z => z - base M m n δ x.1) he
  constructor
  · apply nonvanishingDomain_of_avoids _ _ _ _ _ hD
    · intro K J
      apply havoid
      left
      rw [numerator_pole_coords M hc.1 m n δ x.1 hτ K J]
      exact ⟨(hs K J).1.1, (hs K J).2.1⟩
    · intro K J
      apply havoid
      right
      rw [(other_divisor_coords M hc.1 m n p δ x.1 x.2.2 hτ K J).1]
      exact ⟨(hs K J).1.2.2.1, (hs K J).2.2.2.1⟩
  · apply nonvanishingDomain_of_avoids _ _ _ _ _ hD
    · intro K J he
      have hh := havoid (modularPhiPolePoint M (m + p) n x.1 K J - x.2.2) (by
        left
        rw [(other_divisor_coords M hc.1 m n p δ x.1 x.2.2 hτ K J).2]
        exact ⟨(hs K J).1.2.2.2, (hs K J).2.2.2.2⟩)
      apply hh
      linear_combination he
    · intro K J he
      have hh := havoid (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2) (by
        right
        rw [inverse_denominator_pole_coords M hc.1 m n p δ x.1 x.2.2 hτ K J]
        exact ⟨(hs K J).1.2.1, (hs K J).2.2.1⟩)
      apply hh
      linear_combination he

/--
All nonnegative integer translates of both templates avoid both full
divisors. This is not a claim for arbitrary real translations.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem grid_divisor_free (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ)
    (z : ℂ) (hz : z ∈ templates M m n δ x.1) (j k : ℕ) :
    (z + (j : ℂ) * etaDenom M x.1 + (k : ℂ), x.1) ∈
        modularPhiNonvanishingDomain M (m + 1) n ∧
      (z + (j : ℂ) * etaDenom M x.1 + (k : ℂ) + x.2.2, x.1) ∈
        modularPhiNonvanishingDomain M (m + p) n := by
  have hτ : x.1.im ≠ 0 := ne_of_gt hx.1.1
  have hTi := denom_im_ne_zero M hc.1 x.1 hτ
  have hD := (tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).1
  have hb := window_height_bounds M h ℓ p ψ σ ρ δ hc x hx
  have hs (K J : ℕ) := window_affine_signs M h ℓ p ψ σ ρ δ hc x hx K J
  let v := z + (j : ℂ) * etaDenom M x.1 + (k : ℂ)
  have hg : 0 ≤ (coords (etaDenom M x.1) (v - base M m n δ x.1)).1 ∧
      0 ≤ (coords (etaDenom M x.1) (v - base M m n δ x.1)).2 ∧
      ((coords (etaDenom M x.1) (v - base M m n δ x.1)).1 = (j : ℝ) ∨
        (coords (etaDenom M x.1) (v - base M m n δ x.1)).2 = (k : ℝ)) := by
    rcases hz with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hh : coords (etaDenom M x.1)
          ((base M m n δ x.1 + (u : ℂ) + (j : ℂ) * etaDenom M x.1 + (k : ℂ)) -
            base M m n δ x.1) = ((j : ℝ), u + k) := by
        apply (coords_eq_iff _ _ hTi _ _).mpr
        push_cast
        ring
      dsimp only [v]
      rw [hh]
      exact ⟨Nat.cast_nonneg j, add_nonneg hu.1 (Nat.cast_nonneg k), Or.inl rfl⟩
    · have hh : coords (etaDenom M x.1)
          ((base M m n δ x.1 + (u : ℂ) * etaDenom M x.1 +
            (j : ℂ) * etaDenom M x.1 + (k : ℂ)) - base M m n δ x.1) = (u + j, (k : ℝ)) := by
        apply (coords_eq_iff _ _ hTi _ _).mpr
        push_cast
        ring
      dsimp only [v]
      rw [hh]
      exact ⟨add_nonneg hu.1 (Nat.cast_nonneg j), Nat.cast_nonneg k, Or.inr rfl⟩
  constructor
  · apply nonvanishingDomain_of_avoids _ _ _ v _ hD
    · intro K J he
      have hh := congrArg (fun q => coords (etaDenom M x.1) (q - base M m n δ x.1)) he
      rw [numerator_pole_coords M hc.1 m n δ x.1 hτ K J] at hh
      have hi := hg.2.2
      rw [hh] at hi
      rcases hi with hi | hi
      · exact delta_grid_ne (M 1 0) hc.1 δ hb.2.1 hb.2.2.1 K j hi
      · exact delta_grid_ne (M 1 0) hc.1 δ hb.2.1 hb.2.2.1 J k hi
    · intro K J he
      have hh := congrArg (fun q => coords (etaDenom M x.1) (q - base M m n δ x.1)) he
      rw [(other_divisor_coords M hc.1 m n p δ x.1 x.2.2 hτ K J).1] at hh
      have hi := hg.1
      rw [hh] at hi
      exact (not_lt_of_ge hi) (hs K J).1.2.2.1
  · apply nonvanishingDomain_of_avoids _ _ _ (v + x.2.2) _ hD
    · intro K J he
      have he' : v = modularPhiPolePoint M (m + p) n x.1 K J - x.2.2 := by
        linear_combination he
      have hh := congrArg (fun q => coords (etaDenom M x.1) (q - base M m n δ x.1)) he'
      rw [(other_divisor_coords M hc.1 m n p δ x.1 x.2.2 hτ K J).2] at hh
      have hi := hg.2.2
      rw [hh] at hi
      rcases hi with hi | hi
      · exact height_grid_ne (M 1 0) hc.1 δ _ hb.2.1 hb.2.2.2.1 hb.2.2.2.2.2.1 K j hi
      · exact height_grid_ne (M 1 0) hc.1 δ _ hb.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.2 J k hi
    · intro K J he
      have he' : v = modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2 := by
        linear_combination he
      have hh := congrArg (fun q => coords (etaDenom M x.1) (q - base M m n δ x.1)) he'
      rw [inverse_denominator_pole_coords M hc.1 m n p δ x.1 x.2.2 hτ K J] at hh
      have hi := hg.1
      rw [hh] at hi
      exact (not_lt_of_ge hi) (hs K J).1.2.1

/--
Both closed rotation sectors are divisor free, including radius zero. It asserts no integral or
decay estimate.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem sector_divisor_free (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ)
    (r θ : ℝ) (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ) ∨
      θ ∈ Icc (-Real.pi / 2 + ψ) 0) :
    (base M m n δ x.1 + (r : ℂ) * rotation θ, x.1) ∈
        modularPhiNonvanishingDomain M (m + 1) n ∧
      (base M m n δ x.1 + (r : ℂ) * rotation θ + x.2.2, x.1) ∈
        modularPhiNonvanishingDomain M (m + p) n := by
  have hτ : x.1.im ≠ 0 := ne_of_gt hx.1.1
  have hTi := denom_im_ne_zero M hc.1 x.1 hτ
  have hD := (tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).1
  have hs (K J : ℕ) := window_affine_signs M h ℓ p ψ σ ρ δ hc x hx K J
  have hv : (0 ≤ ((r : ℂ) * rotation θ).im ∧
        0 ≤ ((r : ℂ) * rotation θ / etaDenom M x.1).im) ∨
      (((r : ℂ) * rotation θ).im ≤ 0 ∧
        ((r : ℂ) * rotation θ / etaDenom M x.1).im ≤ 0) := by
    rcases hθ with hθ | hθ
    · have hh := upper_direction_im_nonneg _ ψ θ hx.1.2.1 hx.1.2.2 hc.2.2.1 hθ
      left
      simpa only [mul_div_assoc, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using
        And.intro (mul_nonneg hr hh.1) (mul_nonneg hr hh.2)
    · have hh := lower_direction_im_nonneg _ ψ θ hx.1.2.1 hx.1.2.2 hc.2.2.1 hθ
      have hi : (rotation θ).im ≤ 0 := by simpa using hh.1
      have hd : (rotation θ / etaDenom M x.1).im ≤ 0 := by
        simpa only [neg_div, Complex.neg_im, neg_nonneg] using hh.2.le
      right
      simpa only [mul_div_assoc, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using
        And.intro (mul_nonpos_of_nonneg_of_nonpos hr hi) (mul_nonpos_of_nonneg_of_nonpos hr hd)
  have havoid (q : ℂ)
      (hq : (0 < (coords (etaDenom M x.1) (q - base M m n δ x.1)).1 ∧
          0 < (coords (etaDenom M x.1) (q - base M m n δ x.1)).2) ∨
        ((coords (etaDenom M x.1) (q - base M m n δ x.1)).1 < 0 ∧
          (coords (etaDenom M x.1) (q - base M m n δ x.1)).2 < 0)) :
      base M m n δ x.1 + (r : ℂ) * rotation θ ≠ q := by
    intro he
    apply quadrant_ne_cone _ _ _ (im_etaDenom_pos_of_im_pos M hc.1 hx.1.1) hv hq
    linear_combination he
  constructor
  · apply nonvanishingDomain_of_avoids _ _ _ _ _ hD
    · intro K J
      apply havoid
      left
      rw [numerator_pole_coords M hc.1 m n δ x.1 hτ K J]
      exact ⟨(hs K J).1.1, (hs K J).2.1⟩
    · intro K J
      apply havoid
      right
      rw [(other_divisor_coords M hc.1 m n p δ x.1 x.2.2 hτ K J).1]
      exact ⟨(hs K J).1.2.2.1, (hs K J).2.2.2.1⟩
  · apply nonvanishingDomain_of_avoids _ _ _ _ _ hD
    · intro K J he
      have hh := havoid (modularPhiPolePoint M (m + p) n x.1 K J - x.2.2) (by
        left
        rw [(other_divisor_coords M hc.1 m n p δ x.1 x.2.2 hτ K J).2]
        exact ⟨(hs K J).1.2.2.2, (hs K J).2.2.2.2⟩)
      apply hh
      linear_combination he
    · intro K J he
      have hh := havoid (modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2) (by
        right
        rw [inverse_denominator_pole_coords M hc.1 m n p δ x.1 x.2.2 hτ K J]
        exact ⟨(hs K J).1.2.1, (hs K J).2.2.1⟩)
      apply hh
      linear_combination he

/--
The two denominator arguments in the finite shift products; not an assertion that all raw
q-quotient denominators have modulus <1 along these templates.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem template_q_bounds (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ)
    (z : ℂ) (hz : z ∈ templates M m n δ x.1) :
    ‖aArg m x.1 z‖ < 1 ∧ ‖e (etaMobius M x.1) / dArg M n x.1 z‖ < 1 := by
  have hτ : x.1.im ≠ 0 := ne_of_gt hx.1.1
  have hTi := denom_im_ne_zero M hc.1 x.1 hτ
  have hb := window_height_bounds M h ℓ p ψ σ ρ δ hc x hx
  rcases tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1 with
    ⟨_, _, _, _, hq0, hq1, hQ0, hQ1⟩
  have hcR : (M 1 0 : ℝ) ≠ 0 := ne_of_gt hb.1
  have hcC : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc.1
  obtain ⟨a, b, ha, hb', hz'⟩ : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      z = base M m n δ x.1 + (a : ℂ) * etaDenom M x.1 + (b : ℂ) := by
    rcases hz with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact ⟨0, u, le_rfl, hu.1, by simp⟩
    · exact ⟨u, 0, hu.1, le_rfl, by simp⟩
  have hzcoords : coords (etaDenom M x.1) z =
      (-(m : ℝ) / (M 1 0 : ℝ) - δ + a, (n : ℝ) / (M 1 0 : ℝ) - δ + b) := by
    apply (coords_eq_iff _ _ hTi _ _).mpr
    rw [hz']
    unfold base
    push_cast
    field_simp
    <;> ring
  have hna : ‖aArg m x.1 z‖ = Real.rpow ‖e x.1‖
      (1 - (M 1 0 : ℝ) * δ + (M 1 0 : ℝ) * a) := by
    unfold aArg
    rw [norm_q_argument M hc.1 _ _ _ hτ, hzcoords]
    congr 1
    push_cast
    field_simp
    <;> ring
  have hnd : ‖dArg M n x.1 z‖ = Real.rpow ‖e (etaMobius M x.1)‖
      ((M 1 0 : ℝ) * δ - (M 1 0 : ℝ) * b) := by
    unfold dArg
    rw [norm_Q_argument M hc.1 _ _ _ hτ, hzcoords]
    congr 1
    dsimp only
    field_simp
    <;> ring
  have hnQ : ‖e (etaMobius M x.1) / dArg M n x.1 z‖ =
      Real.rpow ‖e (etaMobius M x.1)‖
        (1 - (M 1 0 : ℝ) * δ + (M 1 0 : ℝ) * b) := by
    convert reflected_norm _ _ (e_ne_zero _) _ hnd using 1 <;> ring
  constructor
  · rw [hna, Real.rpow_eq_pow]
    exact (Real.rpow_lt_one_iff_of_pos hq0).mpr (Or.inr ⟨hq1, by
      linarith [mul_nonneg hb.1.le ha, hb.2.2.1]⟩)
  · rw [hnQ, Real.rpow_eq_pow]
    exact (Real.rpow_lt_one_iff_of_pos hQ0).mpr (Or.inr ⟨hQ1, by
      linarith [mul_nonneg hb.1.le hb', hb.2.2.1]⟩)

/--
General-coordinate version of all four vertex moduli; center recovered by H_T=H_1=ρ.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem vertex_moduli (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    let z := base M m n δ x.1
    let H := coords (etaDenom M x.1) (height M p x.1 x.2.2)
    let χ := (M 1 0 : ℝ) * δ
    ‖aArg m x.1 z‖ = Real.rpow ‖e x.1‖ (1 - χ) ∧
      ‖bArg m p x.1 x.2.2 z‖ = Real.rpow ‖e x.1‖ (H.1 - χ) ∧
      ‖dArg M n x.1 z‖ = Real.rpow ‖e (etaMobius M x.1)‖ χ ∧
      ‖cArg M n x.1 x.2.2 z‖ = Real.rpow ‖e (etaMobius M x.1)‖ (1 - H.2 + χ) := by
  dsimp only
  have hτ : x.1.im ≠ 0 := ne_of_gt hx.1.1
  have hTi := denom_im_ne_zero M hc.1 x.1 hτ
  have hcR : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc.1
  have hcC : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc.1
  have hz : coords (etaDenom M x.1) (base M m n δ x.1) =
      (-(m : ℝ) / (M 1 0 : ℝ) - δ, (n : ℝ) / (M 1 0 : ℝ) - δ) := by
    apply (coords_eq_iff _ _ hTi _ _).mpr
    unfold base
    push_cast
    field_simp
    <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold aArg
    rw [norm_q_argument M hc.1 _ _ _ hτ, hz]
    congr 1
    push_cast
    field_simp
    <;> ring
  · unfold bArg
    rw [norm_q_argument M hc.1 _ _ _ hτ, coords_add, hz,
      coords_height M hc.1 p x.1 x.2.2 hτ]
    simp only [Prod.fst_add]
    congr 1
    push_cast
    field_simp
    <;> ring
  · unfold dArg
    rw [norm_Q_argument M hc.1 _ _ _ hτ, hz]
    congr 1
    dsimp only
    field_simp
    <;> ring
  · unfold cArg
    rw [norm_Q_argument M hc.1 _ _ _ hτ, coords_add, hz,
      coords_height M hc.1 p x.1 x.2.2 hτ]
    simp only [Prod.snd_add]
    congr 1
    field_simp
    <;> ring

/--
General-coordinate version of all four reflected vertex moduli.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem reflected_vertex_moduli (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    let z := base M m n δ x.1
    let H := coords (etaDenom M x.1) (height M p x.1 x.2.2)
    let χ := (M 1 0 : ℝ) * δ
    ‖e x.1 / aArg m x.1 z‖ = Real.rpow ‖e x.1‖ χ ∧
      ‖e (etaMobius M x.1) / dArg M n x.1 z‖ = Real.rpow ‖e (etaMobius M x.1)‖ (1 - χ) ∧
      ‖e x.1 / bArg m p x.1 x.2.2 z‖ = Real.rpow ‖e x.1‖ (1 - H.1 + χ) ∧
      ‖e (etaMobius M x.1) / cArg M n x.1 x.2.2 z‖ =
        Real.rpow ‖e (etaMobius M x.1)‖ (H.2 - χ) := by
  dsimp only
  have hv := vertex_moduli M h ℓ p m n ψ σ ρ δ hc x hx
  dsimp only at hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert reflected_norm _ _ (e_ne_zero x.1) _ hv.1 using 1 <;> ring
  · exact reflected_norm _ _ (e_ne_zero _) _ hv.2.2.1
  · convert reflected_norm _ _ (e_ne_zero x.1) _ hv.2.1 using 1 <;> ring
  · convert reflected_norm _ _ (e_ne_zero _) _ hv.2.2.2 using 1 <;> ring

#print line
#print phase
#check numerator_pole_coords
#check inverse_denominator_pole_coords
#check no_pinch
#check grid_divisor_free
#check modularPhi_eq_qProduct_germ
#check modularPhi_eq_qProduct
#check modularPhi_ne_zero_iff

end SICLean.L4.UpperWindow
