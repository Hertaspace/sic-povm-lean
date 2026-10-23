import SICLean.L4.UpperWindowCompact
import SICLean.L4.FinitePrincipalParts
import SICLean.L4.ModularCocycle
import SICLean.L4.UpperContourGeometryAux

set_option autoImplicit false

/-!
# Explicit clockwise parallelograms and finite pole boxes

Twelve fixed geometric and analytic interfaces. All sets, kernels,
integrals and residue candidates below have literal definition bodies.
`simpleResidue` is the punctured limit of (z-a)f(z); its existence and
identification as a Laurent coefficient are theorems in `UpperContourClosure`, for at-most-simple
poles only. It is not a general higher-order residue operator.
At a cancelled numerator pole we retain its label and its zero residue.
[RW26, pp. 28--29, Appendix A.2] contour and residue calculus is formalized here.
All principal branches, Φ, φ and μ are inherited without redefinition.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContour

inductive Kind where
  | single
  | ratio
  deriving DecidableEq

/-- Just selects the existing point-value kernel; no new continuation. -/
def kernel (kind : Kind) (M : SL(2, ℤ)) (m n h ℓ p : ℤ)
    (x : UpperWindow.Parameters) (z : ℂ) : ℂ :=
  match kind with
  | .single => UpperWindow.singleKernel M m n h ℓ x.1 x.2.1 z
  | .ratio => UpperWindow.ratioKernel M m n h ℓ p x.1 x.2.1 x.2.2 z

def closedBox (v T : ℂ) (R : ℝ) : Set ℂ :=
  {z | 0 ≤ (UpperWindow.coords T (z - v)).1 ∧
    (UpperWindow.coords T (z - v)).1 ≤ R ∧
    0 ≤ (UpperWindow.coords T (z - v)).2 ∧
    (UpperWindow.coords T (z - v)).2 ≤ R}

def openBox (v T : ℂ) (R : ℝ) : Set ℂ :=
  {z | 0 < (UpperWindow.coords T (z - v)).1 ∧
    (UpperWindow.coords T (z - v)).1 < R ∧
    0 < (UpperWindow.coords T (z - v)).2 ∧
    (UpperWindow.coords T (z - v)).2 < R}

def boxBoundary (v T : ℂ) (R : ℝ) : Set ℂ := closedBox v T R \ openBox v T R

/-- z*+R → z*: incoming real edge. -/
def firstSide (f : ℂ → ℂ) (v : ℂ) (R : ℕ) : ℂ :=
  ∫ t : ℝ in (R : ℝ)..0, f (v + (t : ℂ))

/-- z* → z*+RT: outgoing T edge, including dz=T dt. -/
def secondSide (f : ℂ → ℂ) (v T : ℂ) (R : ℕ) : ℂ :=
  ∫ t : ℝ in 0..(R : ℝ), f (v + (t : ℂ) * T) * T

/-- z*+RT → z*+RT+R: remote real edge. -/
def thirdSide (f : ℂ → ℂ) (v T : ℂ) (R : ℕ) : ℂ :=
  ∫ t : ℝ in 0..(R : ℝ), f (v + (R : ℂ) * T + (t : ℂ))

/-- z*+RT+R → z*+R: remote T edge, including dz=T dt. -/
def fourthSide (f : ℂ → ℂ) (v T : ℂ) (R : ℕ) : ℂ :=
  ∫ t : ℝ in (R : ℝ)..0, f (v + (R : ℂ) + (t : ℂ) * T) * T

def clockwiseBoundary (f : ℂ → ℂ) (v T : ℂ) (R : ℕ) : ℂ :=
  firstSide f v R + secondSide f v T R + thirdSide f v T R + fourthSide f v T R

def rayPullback (f : ℂ → ℂ) (v d : ℂ) (t : ℝ) : ℂ := f (v + (t : ℂ) * d) * d

def rayFinite (f : ℂ → ℂ) (v d : ℂ) (r : ℝ) : ℂ :=
  ∫ t : ℝ in 0..r, rayPullback f v d t

def rayIntegral (f : ℂ → ℂ) (v d : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, rayPullback f v d t

def vIntegral (f : ℂ → ℂ) (v T : ℂ) : ℂ :=
  -rayIntegral f v 1 + rayIntegral f v T

def arcPoint (v : ℂ) (r θ : ℝ) : ℂ := v + (r : ℂ) * UpperWindow.rotation θ

def arcPullback (f : ℂ → ℂ) (v : ℂ) (r θ : ℝ) : ℂ :=
  f (arcPoint v r θ) * (Complex.I * (r : ℂ) * UpperWindow.rotation θ)

/-- Increasing angle. Reversed incoming rays are accounted for separately. -/
def arcIntegral (f : ℂ → ℂ) (v : ℂ) (r a b : ℝ) : ℂ :=
  ∫ θ : ℝ in a..b, arcPullback f v r θ

def linePullback (f : ℂ → ℂ) (v : ℂ) (ψ t : ℝ) : ℂ :=
  f (v + (t : ℂ) * (Complex.I * UpperWindow.rotation ψ)) *
    (Complex.I * UpperWindow.rotation ψ)

def lineIntegral (f : ℂ → ℂ) (v : ℂ) (ψ : ℝ) : ℂ :=
  ∫ t : ℝ, linePullback f v ψ t

/-- A concrete candidate, insensitive to f(a). No existence is assumed. -/
def simpleResidue (f : ℂ → ℂ) (a : ℂ) : ℂ :=
  Filter.limUnder (𝓝[≠] a) (fun z : ℂ => (z - a) * f z)

/-- Literal finite box, retaining the existing congruence, including c=1. -/
def boxLabels (M : SL(2, ℤ)) (m n : ℤ) (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range ((M 1 0).toNat * R)).product
    (Finset.range ((M 1 0).toNat * R))).filter
      (fun k => k ∈ modularPhiPoleLabels M (m + 1) n)

def boxCenters (M : SL(2, ℤ)) (m n : ℤ) (τ : ℂ) (R : ℕ) : Finset ℂ :=
  (boxLabels M m n R).image
    (fun k => modularPhiPolePoint M (m + 1) n τ k.1 k.2)

def residueBox (f : ℂ → ℂ) (M : SL(2, ℤ)) (m n : ℤ) (τ : ℂ) (R : ℕ) : ℂ :=
  ∑ k ∈ boxLabels M m n R,
    simpleResidue f (modularPhiPolePoint M (m + 1) n τ k.1 k.2)

/--
Basis bookkeeping. [RW26, pp. 28--29].
-/
theorem coords_affine (v T : ℂ) (hT : T.im ≠ 0) (a b : ℝ) :
    UpperWindow.coords T (v + (a : ℂ) * T + (b : ℂ) - v) = (a, b) := by
  convert UpperWindow.coords_real_combination T hT a b using 1 <;> congr 1 <;> ring

/--
The defined box is z*+[0,R] T+[0,R]; [RW26, pp. 28--29].
-/
theorem closedBox_eq_image (v T : ℂ) (hT : T.im ≠ 0) (R : ℝ) :
    closedBox v T R = (fun u : ℝ × ℝ => v + (u.1 : ℂ) * T + (u.2 : ℂ)) ''
      (Icc 0 R ×ˢ Icc 0 R) := by
  ext z
  constructor
  · intro hz
    refine ⟨UpperWindow.coords T (z - v), ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩, ?_⟩
    dsimp
    linear_combination UpperWindow.coords_reconstruct T (z - v) hT
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    change 0 ≤ (UpperWindow.coords T _).1 ∧ _
    rw [coords_affine v T hT a b]
    exact ⟨ha.1, ha.2, hb.1, hb.2⟩

/--
Finite compact region, with no analytic input; [RW26, pp. 28--29].
-/
theorem closedBox_isCompact (v T : ℂ) (hT : T.im ≠ 0) (R : ℝ) :
    IsCompact (closedBox v T R) := by
  rw [closedBox_eq_image v T hT R]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

/--
Exact four edge sets in the displayed clockwise order; [RW26, pp. 28--29].
-/
theorem boundary_eq_four_edges (v T : ℂ) (hT : T.im ≠ 0) (R : ℕ) :
    boxBoundary v T (R : ℝ) =
      (fun t : ℝ => v + (t : ℂ)) '' Icc 0 (R : ℝ) ∪
      (fun t : ℝ => v + (t : ℂ) * T) '' Icc 0 (R : ℝ) ∪
      (fun t : ℝ => v + (R : ℂ) * T + (t : ℂ)) '' Icc 0 (R : ℝ) ∪
      (fun t : ℝ => v + (R : ℂ) + (t : ℂ) * T) '' Icc 0 (R : ℝ) := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  ext z
  constructor
  · rintro ⟨⟨ha, haR, hb, hbR⟩, hn⟩
    have hrec : v + ((UpperWindow.coords T (z - v)).1 : ℂ) * T +
        ((UpperWindow.coords T (z - v)).2 : ℂ) = z := by
      linear_combination UpperWindow.coords_reconstruct T (z - v) hT
    by_cases ha0 : (UpperWindow.coords T (z - v)).1 = 0
    · refine Or.inl (Or.inl (Or.inl ⟨_, ⟨hb, hbR⟩, ?_⟩))
      simpa only [ha0, Complex.ofReal_zero, zero_mul, add_zero] using hrec
    by_cases hb0 : (UpperWindow.coords T (z - v)).2 = 0
    · refine Or.inl (Or.inl (Or.inr ⟨_, ⟨ha, haR⟩, ?_⟩))
      simpa only [hb0, Complex.ofReal_zero, add_zero] using hrec
    by_cases haR' : (UpperWindow.coords T (z - v)).1 = (R : ℝ)
    · refine Or.inl (Or.inr ⟨_, ⟨hb, hbR⟩, ?_⟩)
      simpa only [haR', Complex.ofReal_natCast] using hrec
    by_cases hbR' : (UpperWindow.coords T (z - v)).2 = (R : ℝ)
    · refine Or.inr ⟨_, ⟨ha, haR⟩, ?_⟩
      rw [hbR', Complex.ofReal_natCast] at hrec
      linear_combination hrec
    exact (hn ⟨lt_of_le_of_ne ha (Ne.symm ha0), lt_of_le_of_ne haR haR',
      lt_of_le_of_ne hb (Ne.symm hb0), lt_of_le_of_ne hbR hbR'⟩).elim
  · intro hz
    change (0 ≤ (UpperWindow.coords T (z - v)).1 ∧
      (UpperWindow.coords T (z - v)).1 ≤ (R : ℝ) ∧
      0 ≤ (UpperWindow.coords T (z - v)).2 ∧
      (UpperWindow.coords T (z - v)).2 ≤ (R : ℝ)) ∧
      ¬ (0 < (UpperWindow.coords T (z - v)).1 ∧
        (UpperWindow.coords T (z - v)).1 < (R : ℝ) ∧
        0 < (UpperWindow.coords T (z - v)).2 ∧
        (UpperWindow.coords T (z - v)).2 < (R : ℝ))
    rcases hz with ((hz | hz) | hz) | hz
    · rcases hz with ⟨t, ht, rfl⟩
      have hcoord := coords_affine v T hT 0 t
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at hcoord
      rw [hcoord]
      exact ⟨⟨le_rfl, hR, ht.1, ht.2⟩, fun h => (lt_irrefl 0) h.1⟩
    · rcases hz with ⟨t, ht, rfl⟩
      have hcoord := coords_affine v T hT t 0
      simp only [Complex.ofReal_zero, add_zero] at hcoord
      rw [hcoord]
      exact ⟨⟨ht.1, ht.2, le_rfl, hR⟩, fun h => (lt_irrefl 0) h.2.2.1⟩
    · rcases hz with ⟨t, ht, rfl⟩
      have hcoord := coords_affine v T hT (R : ℝ) t
      simp only [Complex.ofReal_natCast] at hcoord
      rw [hcoord]
      exact ⟨⟨hR, le_rfl, ht.1, ht.2⟩, fun h => (lt_irrefl (R : ℝ)) h.2.1⟩
    · rcases hz with ⟨t, ht, rfl⟩
      have hcoord := coords_affine v T hT t (R : ℝ)
      simp only [Complex.ofReal_natCast] at hcoord
      have heq : v + (R : ℂ) + (t : ℂ) * T = v + (t : ℂ) * T + (R : ℂ) := by ring
      dsimp only
      rw [heq, hcoord]
      exact ⟨⟨ht.1, ht.2, hR, le_rfl⟩, fun h => (lt_irrefl (R : ℝ)) h.2.2.2⟩

/--
Exact finite-index export. [RW26, p. 29].
-/
theorem mem_boxLabels (M : SL(2, ℤ)) (m n : ℤ) (R K J : ℕ) :
    (K, J) ∈ boxLabels M m n R ↔
      K < (M 1 0).toNat * R ∧ J < (M 1 0).toNat * R ∧
        Int.ModEq (M 1 0) ((J : ℤ) + M 1 1 * (K : ℤ)) (M 1 1 * m - n) := by
  simp only [boxLabels, Finset.mem_filter]
  constructor
  · rintro ⟨hbox, hlabel⟩
    obtain ⟨hK, hJ⟩ := Finset.mem_product.mp hbox
    exact ⟨Finset.mem_range.mp hK, Finset.mem_range.mp hJ,
      by simpa only [modularPhiPoleLabels, Set.mem_setOf_eq, add_sub_cancel_right] using hlabel⟩
  · rintro ⟨hK, hJ, hlabel⟩
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hK, Finset.mem_range.mpr hJ⟩,
      by simpa only [modularPhiPoleLabels, Set.mem_setOf_eq, add_sub_cancel_right] using hlabel⟩

/--
Each candidate numerator branch is inside exactly for the stated index bounds.
No congruence is needed for this geometry. [RW26, p. 29].
-/
theorem pole_mem_openBox_iff (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (δ : ℝ) (hδ : 0 < δ) (hχ : (M 1 0 : ℝ) * δ < 1)
    (τ : ℂ) (hτ : 0 < τ.im) (R K J : ℕ) (hR : 1 ≤ R) :
    modularPhiPolePoint M (m + 1) n τ K J ∈
        openBox (UpperWindow.base M m n δ τ) (etaDenom M τ) (R : ℝ) ↔
      K < (M 1 0).toNat * R ∧ J < (M 1 0).toNat * R := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hK := UpperContourGeometryAux.shifted_index_bounds (M 1 0) hM δ hδ hχ R K
  have hJ := UpperContourGeometryAux.shifted_index_bounds (M 1 0) hM δ hδ hχ R J
  change 0 < (UpperWindow.coords _ _).1 ∧ _ ↔ _
  rw [UpperWindow.numerator_pole_coords M hM m n δ τ (ne_of_gt hτ) K J]
  have hK₀ : 0 < δ + (K : ℝ) / (M 1 0 : ℝ) :=
    add_pos_of_pos_of_nonneg hδ (div_nonneg (Nat.cast_nonneg K) hc.le)
  have hJ₀ : 0 < δ + (J : ℝ) / (M 1 0 : ℝ) :=
    add_pos_of_pos_of_nonneg hδ (div_nonneg (Nat.cast_nonneg J) hc.le)
  simpa only [hK₀, hJ₀, true_and] using and_congr hK.1 hJ.1

/--
Including the boundary adds no numerator labels. [RW26, p. 29]. Integral R is essential here.
-/
theorem pole_mem_closedBox_iff (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (δ : ℝ) (hδ : 0 < δ) (hχ : (M 1 0 : ℝ) * δ < 1)
    (τ : ℂ) (hτ : 0 < τ.im) (R K J : ℕ) (hR : 1 ≤ R) :
    modularPhiPolePoint M (m + 1) n τ K J ∈
        closedBox (UpperWindow.base M m n δ τ) (etaDenom M τ) (R : ℝ) ↔
      K < (M 1 0).toNat * R ∧ J < (M 1 0).toNat * R := by
  have hc : 0 < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hK := UpperContourGeometryAux.shifted_index_bounds (M 1 0) hM δ hδ hχ R K
  have hJ := UpperContourGeometryAux.shifted_index_bounds (M 1 0) hM δ hδ hχ R J
  change 0 ≤ (UpperWindow.coords _ _).1 ∧ _ ↔ _
  rw [UpperWindow.numerator_pole_coords M hM m n δ τ (ne_of_gt hτ) K J]
  have hK₀ : 0 ≤ δ + (K : ℝ) / (M 1 0 : ℝ) :=
    add_nonneg hδ.le (div_nonneg (Nat.cast_nonneg K) hc.le)
  have hJ₀ : 0 ≤ δ + (J : ℝ) / (M 1 0 : ℝ) :=
    add_nonneg hδ.le (div_nonneg (Nat.cast_nonneg J) hc.le)
  simpa only [hK₀, hJ₀, true_and] using and_congr hK.2 hJ.2

/--
Distinct labels give distinct points in this upper-plane block. [RW26, p. 6, p. 29].
-/
theorem polePoint_injective (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Function.Injective (fun k : ℕ × ℕ => modularPhiPolePoint M (m + 1) n τ k.1 k.2) := by
  intro k l heq
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hcoords := congrArg
    (fun z => UpperWindow.coords (etaDenom M τ) (z - UpperWindow.base M m n 0 τ)) heq
  rw [UpperWindow.numerator_pole_coords M hM m n 0 τ (ne_of_gt hτ) k.1 k.2,
    UpperWindow.numerator_pole_coords M hM m n 0 τ (ne_of_gt hτ) l.1 l.2] at hcoords
  have h₁ := congrArg Prod.fst hcoords
  have h₂ := congrArg Prod.snd hcoords
  simp only [Prod.fst, Prod.snd, zero_add, div_left_inj' hc] at h₁ h₂
  exact Prod.ext (by exact_mod_cast h₁) (by exact_mod_cast h₂)

/--
No inverse-denominator pole even in the closed finite box.
[RW26, pp. 28--29].
-/
theorem inverse_poles_outside (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R K J : ℕ) :
    modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2 ∉
      closedBox (UpperWindow.base M m n δ x.1) (etaDenom M x.1) (R : ℝ) := by
  intro hz
  have hneg := (UpperWindow.pole_coordinate_signs M h ℓ p m n ψ σ ρ δ hc x hx K J).2.2.1
  exact (not_lt_of_ge hz.1) hneg

/--
Both actual representatives are units on every side; [RW26, pp. 28--29].
-/
theorem boundary_divisor_free (M : SL(2, ℤ)) (h ℓ p m n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ)
    (z : ℂ) (hz : z ∈ boxBoundary (UpperWindow.base M m n δ x.1)
      (etaDenom M x.1) (R : ℝ)) :
    (z, x.1) ∈ modularPhiNonvanishingDomain M (m + 1) n ∧
      (z + x.2.2, x.1) ∈ modularPhiNonvanishingDomain M (m + p) n := by
  have hT := (UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1).2.1
  rw [boundary_eq_four_edges _ _ (ne_of_gt hT) R] at hz
  rcases hz with ((hz | hz) | hz) | hz
  · rcases hz with ⟨t, ht, rfl⟩
    simpa only [Nat.cast_zero, zero_mul, add_zero] using
      UpperContourGeometryAux.real_grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx t ht.1 0
  · rcases hz with ⟨t, ht, rfl⟩
    simpa only [Nat.cast_zero, add_zero] using
      UpperContourGeometryAux.denom_grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx t ht.1 0
  · rcases hz with ⟨t, ht, rfl⟩
    exact UpperContourGeometryAux.real_grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx t ht.1 R
  · rcases hz with ⟨t, ht, rfl⟩
    exact UpperContourGeometryAux.denom_grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx t ht.1 R

/--
Meromorphy of the existing kernels; no point-value claim at a pole; [RW26, pp. 28--29].
-/
theorem kernel_meromorphic (kind : Kind) (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n h ℓ p : ℤ) (x : UpperWindow.Parameters) (hτ : x.1 ∈ modularPhiDomain M) :
    MeromorphicOn (kernel kind M m n h ℓ p x) univ := by
  intro z _
  have ha : MeromorphicAt (fun w : ℂ => modularPhi M (m + 1) n w x.1) z :=
    modularPhi_meromorphic M hM (m + 1) n x.1 hτ z (mem_univ z)
  have he : AnalyticAt ℂ (fun w : ℂ => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 w)) z := by
    dsimp [UpperWindow.phase, e]
    fun_prop
  cases kind with
  | single => exact ha.mul he.meromorphicAt
  | ratio =>
      have hb : MeromorphicAt
          (fun w : ℂ => modularPhi M (m + p) n (w + x.2.2) x.1) z := by
        simpa only [Function.comp_def] using
          (modularPhi_meromorphic M hM (m + p) n x.1 hτ (z + x.2.2)
            (mem_univ _)).comp_analyticAt (g := fun w : ℂ => w + x.2.2) (x := z)
            (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w + x.2.2) z)
      exact (ha.div hb).mul he.meromorphicAt

/--
All numerator centers are kept, even when a ratio pole cancels. Denominator
Φ poles away from them give removable zeros of its reciprocal with the existing
zero-at-poles convention. A cancelled center is not deleted, and its raw
0/0 value is not used as the removable value. [RW26, p. 29].
-/
theorem kernel_analytic_off_box (kind : Kind) (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ) (R : ℕ) (hR : 1 ≤ R) :
    AnalyticOnNhd ℂ (kernel kind M m n h ℓ p x)
      (closedBox (UpperWindow.base M m n δ x.1) (etaDenom M x.1) (R : ℝ) \
        (boxCenters M m n x.1 R : Set ℂ)) := by
  have hM : 0 < M 1 0 := hc.1
  have hτim : 0 < x.1.im := hx.1.1
  have hτ : x.1 ∈ modularPhiDomain M :=
    (UpperWindow.tauRegion_properties M hM ψ hc.2.2.1 x.1 hx.1).1
  have hδ : 0 < δ := hc.2.2.2.2.2.2.1
  have hχ : (M 1 0 : ℝ) * δ < 1 :=
    (UpperWindow.radius_margins M ψ σ ρ δ hc).2.2.2.2.2
  intro z hz
  have hnp : modularPhiPoleMultiplicity M (m + 1) n z x.1 = 0 := by
    have hempty : modularPhiPoleIndices M (m + 1) n z x.1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨K, J⟩ ⟨hlab, heq⟩
      have hbounds : K < (M 1 0).toNat * R ∧ J < (M 1 0).toNat * R :=
        (pole_mem_closedBox_iff M hM m n δ hδ hχ x.1 hτim R K J hR).mp
          (heq ▸ hz.1)
      have hlabel : (K, J) ∈ boxLabels M m n R := by
        apply (mem_boxLabels M m n R K J).mpr
        refine ⟨hbounds.1, hbounds.2, ?_⟩
        simpa [modularPhiPoleLabels] using hlab
      apply hz.2
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(K, J), hlabel, heq.symm⟩)
    simp [modularPhiPoleMultiplicity, hempty]
  have ha : AnalyticAt ℂ (fun w : ℂ => modularPhi M (m + 1) n w x.1) z := by
    simpa only [Function.comp_def] using
      (modularPhi_joint_analytic_no_poles M hM (m + 1) n (z, x.1) ⟨hτ, hnp⟩).comp
        (x := z) (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (w, x.1)) z)
  have he : AnalyticAt ℂ
      (fun w : ℂ => e (UpperWindow.phase M m n h ℓ x.1 x.2.1 w)) z := by
    dsimp [UpperWindow.phase, e]
    fun_prop
  cases kind with
  | single => exact ha.mul he
  | ratio =>
      have hnz : modularPhiZeroMultiplicity M (m + p) n (z + x.2.2) x.1 = 0 := by
        have hempty : modularPhiZeroIndices M (m + p) n (z + x.2.2) x.1 = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro ⟨K, J⟩ ⟨_, heq⟩
          have heq' : modularPhiZeroPoint M (m + p) n x.1 K J - x.2.2 = z := by
            rw [← heq]
            ring
          apply inverse_poles_outside M h ℓ p m n ψ σ ρ δ hc x hx R K J
          rw [heq']
          exact hz.1
        simp [modularPhiZeroMultiplicity, hempty]
      have hb : AnalyticAt ℂ
          (fun w : ℂ => (modularPhi M (m + p) n (w + x.2.2) x.1)⁻¹) z := by
        simpa only [Function.comp_def] using
          (UpperContourGeometryAux.reciprocal_analyticAt M hM (m + p) n
            (z + x.2.2, x.1) hτ hnz).comp (x := z)
            (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (w + x.2.2, x.1)) z)
      change AnalyticAt ℂ (fun w : ℂ =>
        (modularPhi M (m + 1) n w x.1 / modularPhi M (m + p) n (w + x.2.2) x.1) *
          e (UpperWindow.phase M m n h ℓ x.1 x.2.1 w)) z
      simp only [div_eq_mul_inv]
      exact (ha.mul hb).mul he

#print clockwiseBoundary
#print simpleResidue
#print boxLabels
#check mem_boxLabels
#check boundary_divisor_free
#check kernel_analytic_off_box

end SICLean.L4.UpperContour
