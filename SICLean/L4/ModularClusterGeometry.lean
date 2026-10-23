import SICLean.L4.ModularClusterGeometryAux

set_option autoImplicit false

/-!
# Labeled finite clusters and fixed circles

Parameter-dependent circles on closed complex balls are formalized here. [RW26, p. 6].

Each KernelData has its own circles. A common parameter radius for finitely
many data does not require circles for different m to be disjoint. Labels
are retained until grouping by their location at τ₀; thus a rational center
can contain several labels. No regularity, bound, integral identity, or
existence assertion is a field of KernelData or Circles.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.ModularCluster

/--
Arithmetic inputs for the two G1 kernels. `ratio=false` is the single
function. The other inputs are allowed to be complex but held fixed in τ.
-/
structure KernelData where
  m : ℤ
  n : ℤ
  p : ℤ
  ell : ℤ
  h : ℤ
  w : ℂ
  y : ℂ
  ratio : Bool

/-- Vary only the continuous spectral parameters, keeping the integer
indices and the choice of single/ratio kernel fixed. -/
def withParameters (k : KernelData) (w y : ℂ) : KernelData :=
  { k with w := w, y := y }

/-- Geometry only: no properties are stored. -/
structure Circles where
  centers : Finset ℂ
  radius : ℂ → ℝ

/-- true = numerator pole; false = inverse-denominator pole. -/
abbrev Label := Bool × (ℕ × ℕ)

/--
Actual possible pole labels of the kernel; never a pseudolattice.
-/
def labels (M : SL(2, ℤ)) (k : KernelData) : Set Label :=
  {b | if b.1 = true then b.2 ∈ modularPhiPoleLabels M (k.m + 1) k.n
    else k.ratio = true ∧ b.2 ∈ modularPhiZeroLabels M (k.m + k.p) k.n}

def branchPoint (M : SL(2, ℤ)) (k : KernelData) (τ : ℂ) (b : Label) : ℂ :=
  if b.1 = true then modularPhiPolePoint M (k.m + 1) k.n τ b.2.1 b.2.2
  else modularPhiZeroPoint M (k.m + k.p) k.n τ b.2.1 b.2.2 - k.y

/-- Full fiber, including all labels that coalesce. -/
def fiber (M : SL(2, ℤ)) (k : KernelData) (a τ : ℂ) : Set Label :=
  {b | b ∈ labels M k ∧ branchPoint M k τ b = a}

/-- An upper bound on kernel pole order, not an assertion of no cancellation
between numerator and denominator. Used together with `fiber_finite`. -/
def poleBudget (M : SL(2, ℤ)) (k : KernelData) (a τ : ℂ) : ℕ :=
  Nat.card (fiber M k a τ)

def boundedCenters (M : SL(2, ℤ)) (k : KernelData) (τ : ℂ) (R : ℝ) : Set ℂ :=
  {a | ‖a‖ ≤ R ∧ ∃ b ∈ labels M k, branchPoint M k τ b = a}

def movingCenters (M : SL(2, ℤ)) (k : KernelData) (τ a : ℂ) (r : ℝ) : Set ℂ :=
  {z | dist z a < r ∧ ∃ b ∈ labels M k, branchPoint M k τ b = z}

/--
Literal per-kernel cross-class nonintersection. Same-class collisions are allowed.
-/
def crossSeparated (M : SL(2, ℤ)) (k : KernelData) (τ : ℂ) : Prop :=
  ∀ b ∈ labels M k, ∀ b' ∈ labels M k,
    branchPoint M k τ b = branchPoint M k τ b' → b.1 = b'.1

/-- Union of the fixed geometric boundaries. -/
def boundaries (C : Circles) : Set ℂ :=
  {z | ∃ a ∈ C.centers, z ∈ Metric.sphere a (C.radius a)}

/-- Explicit affine form of one labeled branch in `etaDenom M τ`. -/
lemma branchPoint_eq_affine (M : SL(2, ℤ)) (k : KernelData) (b : Label) :
    ∃ u v : ℂ, ∀ τ, branchPoint M k τ b = u + v * etaDenom M τ := by
  rcases b with ⟨b1, K, J⟩
  cases b1
  · refine ⟨((k.n : ℂ) - 1 - (J : ℂ)) / (M 1 0 : ℂ) - k.y,
      (-((k.m : ℂ) + (k.p : ℂ) + (K : ℂ))) / (M 1 0 : ℂ), ?_⟩
    intro τ
    simp only [branchPoint, Bool.false_eq_true, if_false, modularPhiZeroPoint, etaDenom]
    by_cases hc : ((M 1 0 : ℤ) : ℂ) = 0
    · simp [hc]
    · field_simp
      push_cast
      ring
  · refine ⟨((k.n : ℂ) + (J : ℂ)) / (M 1 0 : ℂ),
      ((K : ℂ) - (k.m : ℂ)) / (M 1 0 : ℂ), ?_⟩
    intro τ
    simp only [branchPoint, if_true, modularPhiPolePoint, etaDenom]
    by_cases hc : ((M 1 0 : ℤ) : ℂ) = 0
    · simp [hc]
    · field_simp
      push_cast
      ring

/-- The labeled branch is affine in τ, so its increment scales linearly. -/
lemma branchPoint_affine (M : SL(2, ℤ)) (k : KernelData) (b : Label) (τ τ₀ : ℂ) :
    branchPoint M k τ b - branchPoint M k τ₀ b =
      (τ - τ₀) * (branchPoint M k (τ₀ + 1) b - branchPoint M k τ₀ b) := by
  obtain ⟨u, v, h⟩ := branchPoint_eq_affine M k b
  rw [h τ, h τ₀, h (τ₀ + 1)]
  simp only [etaDenom]
  ring

/-- Norm form of the affine increment. -/
lemma norm_branchPoint_sub (M : SL(2, ℤ)) (k : KernelData) (b : Label) (τ τ₀ : ℂ) :
    ‖branchPoint M k τ b - branchPoint M k τ₀ b‖ =
      ‖τ - τ₀‖ * ‖branchPoint M k (τ₀ + 1) b - branchPoint M k τ₀ b‖ := by
  rw [branchPoint_affine, norm_mul]

/--
Affine branches, including the translation by -y; [RW26, p. 6].
-/
theorem branchPoint_analytic (M : SL(2, ℤ)) (k : KernelData) (b : Label) :
    AnalyticOnNhd ℂ (fun τ => branchPoint M k τ b) Set.univ := by
  intro τ _
  rcases b with ⟨b1, K, J⟩
  cases b1
  · simp only [branchPoint, Bool.false_eq_true, if_false]
    unfold modularPhiZeroPoint etaDenom
    fun_prop
  · simp only [branchPoint, if_true]
    unfold modularPhiPolePoint etaDenom
    fun_prop

/--
Same formulas, with no change of branch or φ representative; [RW26, p. 6].
-/
theorem branchPoint_cases (M : SL(2, ℤ)) (k : KernelData) (τ : ℂ) (K J : ℕ) :
    branchPoint M k τ (true, K, J) =
        modularPhiPolePoint M (k.m + 1) k.n τ K J ∧
      branchPoint M k τ (false, K, J) =
        modularPhiZeroPoint M (k.m + k.p) k.n τ K J - k.y := by
  constructor <;> simp [branchPoint]

/--
Finite label fiber before any Nat.card argument; [RW26, p. 6], including labeled multiplicities.
-/
theorem fiber_finite (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData)
    (a τ : ℂ) (hτ : τ ∈ modularPhiDomain M) : (fiber M k a τ).Finite := by
  obtain ⟨hP, _⟩ := modularPhiDivisor_indices_finite M hM (k.m + 1) k.n a τ hτ
  obtain ⟨_, hZ⟩ := modularPhiDivisor_indices_finite M hM (k.m + k.p) k.n (a + k.y) τ hτ
  refine Set.Finite.subset
    ((hP.image (fun p => (true, p))).union (hZ.image (fun p => (false, p)))) ?_
  intro b hb
  rw [fiber, Set.mem_ofPred_eq] at hb
  obtain ⟨hbl, hbeq⟩ := hb
  rcases b with ⟨b1, p⟩
  cases b1
  · right
    refine ⟨p, ⟨?_, ?_⟩, rfl⟩
    · simp only [labels, Bool.false_eq_true, if_false, Set.mem_ofPred_eq] at hbl
      exact hbl.2
    · simp only [branchPoint, Bool.false_eq_true, if_false] at hbeq
      rw [sub_eq_iff_eq_add] at hbeq
      exact hbeq.symm
  · left
    refine ⟨p, ⟨?_, ?_⟩, rfl⟩
    · simp only [labels, if_true, Set.mem_ofPred_eq] at hbl
      exact hbl
    · simp only [branchPoint, if_true] at hbeq
      exact hbeq.symm

/--
Homogeneity is conditional on cross-class separation, not on irrationality; [RW26, p. 6] sets.
-/
theorem fiber_same_class (M : SL(2, ℤ)) (k : KernelData) (a τ : ℂ)
    (hsep : crossSeparated M k τ) (b b' : Label)
    (hb : b ∈ fiber M k a τ) (hb' : b' ∈ fiber M k a τ) : b.1 = b'.1 := by
  exact hsep b hb.1 b' hb'.1 (hb.2.trans hb'.2.symm)

/--
Distinct centers, not labels, index the circles; [RW26, p. 6].
-/
theorem boundedCenters_finite (M : SL(2, ℤ)) (hM : 0 < M 1 0) (k : KernelData)
    (τ : ℂ) (hτ : τ ∈ modularPhiDomain M) (R : ℝ) (hR : 0 ≤ R) :
    (boundedCenters M k τ R).Finite := by
  have hdom : ({τ} : Set ℂ) ⊆ modularPhiDomain M := by
    rintro x rfl; exact hτ
  obtain ⟨hP, _⟩ := modularPhiDivisor_compact_finiteness M hM (k.m + 1) k.n
    ({τ} : Set ℂ) isCompact_singleton hdom R hR
  obtain ⟨_, hZ⟩ := modularPhiDivisor_compact_finiteness M hM (k.m + k.p) k.n
    ({τ} : Set ℂ) isCompact_singleton hdom (R + ‖k.y‖) (by positivity)
  have hP' : {p : ℕ × ℕ | p ∈ modularPhiPoleLabels M (k.m + 1) k.n ∧
      ‖modularPhiPolePoint M (k.m + 1) k.n τ p.1 p.2‖ ≤ R}.Finite := by
    refine hP.subset ?_
    rintro p ⟨hp, hb⟩
    exact ⟨hp, τ, by simp, hb⟩
  have hZ' : {p : ℕ × ℕ | p ∈ modularPhiZeroLabels M (k.m + k.p) k.n ∧
      ‖modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2‖ ≤ R + ‖k.y‖}.Finite := by
    refine hZ.subset ?_
    rintro p ⟨hp, hb⟩
    exact ⟨hp, τ, by simp, hb⟩
  have hL : {b : Label | b ∈ labels M k ∧ ‖branchPoint M k τ b‖ ≤ R}.Finite := by
    refine Set.Finite.subset
      ((hP'.image (fun p => (true, p))).union (hZ'.image (fun p => (false, p)))) ?_
    rintro b ⟨hbl, hbn⟩
    rcases b with ⟨b1, p⟩
    cases b1
    · right
      refine ⟨p, ⟨?_, ?_⟩, rfl⟩
      · simp only [labels, Bool.false_eq_true, if_false, Set.mem_ofPred_eq] at hbl
        exact hbl.2
      · have hbn' : ‖modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2 - k.y‖ ≤ R := by
          simpa only [branchPoint, Bool.false_eq_true, if_false] using hbn
        calc ‖modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2‖
            = ‖(modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2 - k.y) + k.y‖ := by ring_nf
          _ ≤ ‖modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2 - k.y‖ + ‖k.y‖ :=
              norm_add_le _ _
          _ ≤ R + ‖k.y‖ := by linarith
    · left
      refine ⟨p, ⟨?_, ?_⟩, rfl⟩
      · simp only [labels, if_true, Set.mem_ofPred_eq] at hbl
        exact hbl
      · simpa only [branchPoint, if_true] using hbn
  refine (hL.image (branchPoint M k τ)).subset ?_
  rintro a ⟨hna, b, hbl, hbeq⟩
  exact ⟨b, ⟨hbl, by rw [hbeq]; exact hna⟩, hbeq⟩

/--
Uniform finite labels on a closed full parameter ball. [RW26, p. 6].
-/
theorem exists_uniform_finite_labels (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      {b | b ∈ labels M k ∧ ∃ τ ∈ Metric.closedBall τ₀ ρ,
        ‖branchPoint M k τ b‖ ≤ R}.Finite := by
  obtain ⟨ρ₁, hρ₁, hdom₁, hP, _⟩ :=
    modularPhiDivisor_uniform_local_finiteness M hM (k.m + 1) k.n τ₀ hτ₀ R hR
  obtain ⟨ρ₂, hρ₂, hdom₂, _, hZ⟩ :=
    modularPhiDivisor_uniform_local_finiteness M hM (k.m + k.p) k.n τ₀ hτ₀
      (R + ‖k.y‖) (by positivity)
  refine ⟨min ρ₁ ρ₂ / 2, by positivity, ?_, ?_⟩
  · intro τ hτ
    have hlt : dist τ τ₀ < ρ₁ := by
      have hle := Metric.mem_closedBall.mp hτ
      have hmin : min ρ₁ ρ₂ / 2 < ρ₁ := by
        have := min_le_left ρ₁ ρ₂; linarith [hρ₁]
      linarith
    exact hdom₁ τ hlt
  · refine Set.Finite.subset
      ((hP.image (fun p => (true, p))).union (hZ.image (fun p => (false, p)))) ?_
    rintro b ⟨hbl, τ, hτ, hbn⟩
    rcases b with ⟨b1, p⟩
    cases b1
    · right
      have hlt : dist τ τ₀ < ρ₂ := by
        have hle := Metric.mem_closedBall.mp hτ
        have hmin : min ρ₁ ρ₂ / 2 < ρ₂ := by
          have := min_le_right ρ₁ ρ₂; linarith [hρ₂]
        linarith
      refine ⟨p, ⟨?_, τ, hlt, ?_⟩, rfl⟩
      · simp only [labels, Bool.false_eq_true, if_false, Set.mem_ofPred_eq] at hbl
        exact hbl.2
      · have hbn' : ‖modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2 - k.y‖ ≤ R := by
          simpa only [branchPoint, Bool.false_eq_true, if_false] using hbn
        calc ‖modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2‖
            = ‖(modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2 - k.y) + k.y‖ := by ring_nf
          _ ≤ ‖modularPhiZeroPoint M (k.m + k.p) k.n τ p.1 p.2 - k.y‖ + ‖k.y‖ :=
              norm_add_le _ _
          _ ≤ R + ‖k.y‖ := by linarith
    · left
      have hlt : dist τ τ₀ < ρ₁ := by
        have hle := Metric.mem_closedBall.mp hτ
        have hmin : min ρ₁ ρ₂ / 2 < ρ₁ := by
          have := min_le_left ρ₁ ρ₂; linarith [hρ₁]
        linarith
      refine ⟨p, ⟨?_, τ, hlt, ?_⟩, rfl⟩
      · simp only [labels, if_true, Set.mem_ofPred_eq] at hbl
        exact hbl
      · simpa only [branchPoint, if_true] using hbn

/--
Fixed, disjoint disks with saturated label fibers and explicit margins.
Every branch entering the bounded target is captured. Nothing is required
of individual residues; [RW26, p. 6] divisor sets.
-/
theorem exists_fixed_circles (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ (ρ : ℝ) (C : Circles), 0 < ρ ∧
      Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      (C.centers : Set ℂ) = boundedCenters M k τ₀ R ∧
      (∀ a ∈ C.centers, 0 < C.radius a ∧ C.radius a < 1) ∧
      (∀ a ∈ C.centers, ∀ a' ∈ C.centers, a ≠ a' →
        Disjoint (Metric.closedBall a (C.radius a))
          (Metric.closedBall a' (C.radius a'))) ∧
      (∀ a ∈ C.centers, ∀ b ∈ labels M k, ∀ τ ∈ Metric.closedBall τ₀ ρ,
        (branchPoint M k τ₀ b = a → dist (branchPoint M k τ b) a < C.radius a / 2) ∧
        (branchPoint M k τ₀ b ≠ a → C.radius a < dist (branchPoint M k τ b) a)) ∧
      (∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ b ∈ labels M k,
        ‖branchPoint M k τ b‖ ≤ R → branchPoint M k τ₀ b ∈ C.centers) := by
  -- The enlarged target: every branch that can come within `1` of a center.
  obtain ⟨ρ₀, hρ₀, hdom₀, hL⟩ :=
    exists_uniform_finite_labels M hM k τ₀ hτ₀ (R + 1) (by linarith)
  have hA : (boundedCenters M k τ₀ R).Finite :=
    boundedCenters_finite M hM k τ₀ hτ₀ R hR
  set Ls : Finset Label := hL.toFinset with hLs
  set As : Finset ℂ := hA.toFinset with hAs
  have hmemL : ∀ b : Label, b ∈ Ls ↔
      b ∈ labels M k ∧ ∃ τ ∈ Metric.closedBall τ₀ ρ₀,
        ‖branchPoint M k τ b‖ ≤ R + 1 := by
    intro b
    rw [hLs]
    exact Set.Finite.mem_toFinset hL
  have hmemA : ∀ a : ℂ, a ∈ As ↔ a ∈ boundedCenters M k τ₀ R := by
    intro a
    rw [hAs]
    exact Set.Finite.mem_toFinset hA
  have hAcoe : (As : Set ℂ) = boundedCenters M k τ₀ R := by
    rw [hAs]
    exact Set.Finite.coe_toFinset hA
  -- A uniform slope bound over the finite enlarged set.
  set M₀ : ℝ := ∑ b ∈ Ls, ‖branchPoint M k (τ₀ + 1) b - branchPoint M k τ₀ b‖ with hM₀def
  have hM₀_nonneg : 0 ≤ M₀ := by
    rw [hM₀def]
    exact Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have hM₀_le : ∀ b ∈ Ls,
      ‖branchPoint M k (τ₀ + 1) b - branchPoint M k τ₀ b‖ ≤ M₀ := by
    intro b hb
    rw [hM₀def]
    exact Finset.single_le_sum
      (fun x _ => norm_nonneg (branchPoint M k (τ₀ + 1) x - branchPoint M k τ₀ x)) hb
  -- The finite list of positive separation constraints.
  set s : Finset ℝ :=
    (((As.product Ls).filter (fun p : ℂ × Label => p.2 ∉ fiber M k p.1 τ₀)).image
        (fun p : ℂ × Label => dist (branchPoint M k τ₀ p.2) p.1))
      ∪ (((As.product As).filter (fun p : ℂ × ℂ => p.1 ≠ p.2)).image
        (fun p : ℂ × ℂ => dist p.1 p.2))
      ∪ ((Ls.filter (fun b : Label => R < ‖branchPoint M k τ₀ b‖)).image
        (fun b : Label => ‖branchPoint M k τ₀ b‖ - R)) with hs_def
  have hpos : ∀ x ∈ s, 0 < x := by
    intro x hx
    rw [hs_def] at hx
    rcases Finset.mem_union.mp hx with hxAB | hxC
    · rcases Finset.mem_union.mp hxAB with hxA | hxB
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxA
        obtain ⟨hp', hnf⟩ := Finset.mem_filter.mp hp
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp'
        rw [dist_pos]
        intro heq
        exact hnf (by
          rw [fiber, Set.mem_ofPred_eq]
          exact ⟨((hmemL p.2).mp hb).1, heq⟩)
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxB
        obtain ⟨hp', hne⟩ := Finset.mem_filter.mp hp
        rw [dist_pos]
        exact hne
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hxC
      obtain ⟨hb', hRlt⟩ := Finset.mem_filter.mp hb
      linarith
  obtain ⟨ε, hε, hεle⟩ := exists_pos_le_of_finset s (fun x => x) hpos
  have hε_fib : ∀ a ∈ As, ∀ b ∈ Ls, b ∉ fiber M k a τ₀ →
      ε ≤ dist (branchPoint M k τ₀ b) a := by
    intro a ha b hb hnf
    refine hεle _ ?_
    rw [hs_def]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
      (Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hnf⟩, rfl⟩))))
  have hε_ctr : ∀ a ∈ As, ∀ a' ∈ As, a ≠ a' → ε ≤ dist a a' := by
    intro a ha a' ha' hne
    refine hεle _ ?_
    rw [hs_def]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
      (Finset.mem_image.mpr ⟨(a, a'),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha'⟩, hne⟩, rfl⟩))))
  have hε_nrm : ∀ b ∈ Ls, R < ‖branchPoint M k τ₀ b‖ →
      ε ≤ ‖branchPoint M k τ₀ b‖ - R := by
    intro b hb hRlt
    refine hεle _ ?_
    rw [hs_def]
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hRlt⟩, rfl⟩))
  -- The auxiliary positive radius `c` and the final common parameter radius.
  set c : ℝ := min (1 / 2) (ε / 3) with hc_def
  have hc_pos : 0 < c := lt_min (by norm_num) (by linarith)
  have hc_le_half : c ≤ 1 / 2 := min_le_left _ _
  have hc_le_eps3 : c ≤ ε / 3 := min_le_right _ _
  set D : ℝ := c / (4 * (M₀ + 1)) with hD_def
  have hD_pos : 0 < D := by
    rw [hD_def]
    have : 0 < M₀ + 1 := by linarith
    positivity
  set ρ : ℝ := min ρ₀ (min 1 D) / 2 with hρ_def
  have hρ_pos : 0 < ρ := by
    rw [hρ_def]
    have : 0 < min ρ₀ (min 1 D) := lt_min hρ₀ (lt_min one_pos hD_pos)
    positivity
  have hρ_lt_ρ₀ : ρ < ρ₀ := by
    rw [hρ_def]
    have := min_le_left ρ₀ (min 1 D)
    linarith
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := le_of_lt hρ_lt_ρ₀
  have hρ_lt_D : ρ < D := by
    rw [hρ_def]
    have hle : min ρ₀ (min 1 D) ≤ D :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hP_lt : ρ * (M₀ + 1) < c / 4 := by
    have h4 : (0 : ℝ) < 4 * (M₀ + 1) := by
      have : 0 < M₀ + 1 := by linarith
      positivity
    have h := hρ_lt_D
    rw [hD_def] at h
    rw [lt_div_iff₀ h4] at h
    nlinarith
  have hP_nonneg : 0 ≤ ρ * (M₀ + 1) :=
    mul_nonneg hρ_pos.le (by linarith)
  have hρM_le : ρ * M₀ ≤ ρ * (M₀ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hρ_pos.le
  -- The constructed radius value.
  set r : ℝ := 2 * ρ * (M₀ + 1) + c / 2 with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    have h2 : 0 < 2 * ρ * (M₀ + 1) := by positivity
    linarith
  have hr_lt_c : r < c := by
    rw [hr_def]
    have h2 : 2 * ρ * (M₀ + 1) < c / 2 := by nlinarith [hP_lt]
    linarith
  have hr_lt_one : r < 1 := by
    have := hr_lt_c
    linarith
  have hr_lt_eps3 : r < ε / 3 := by
    have := hr_lt_c
    linarith
  have hr_half : r / 2 = ρ * (M₀ + 1) + c / 4 := by
    rw [hr_def]
    ring
  -- Movement of any label in the enlarged finite set.
  have hmove : ∀ b ∈ Ls, ∀ τ ∈ Metric.closedBall τ₀ ρ,
      dist (branchPoint M k τ b) (branchPoint M k τ₀ b) ≤
        ρ * ‖branchPoint M k (τ₀ + 1) b - branchPoint M k τ₀ b‖ := by
    intro b _ τ hτ
    rw [dist_eq_norm, norm_branchPoint_sub]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hτ) (norm_nonneg _)
  have hmoveM : ∀ b ∈ Ls, ∀ τ ∈ Metric.closedBall τ₀ ρ,
      dist (branchPoint M k τ b) (branchPoint M k τ₀ b) ≤ ρ * M₀ := by
    intro b hb τ hτ
    exact le_trans (hmove b hb τ hτ)
      (mul_le_mul_of_nonneg_left (hM₀_le b hb) hρ_pos.le)
  have hballρ₀ : ∀ τ ∈ Metric.closedBall τ₀ ρ, τ ∈ Metric.closedBall τ₀ ρ₀ := by
    intro τ hτ
    rw [Metric.mem_closedBall] at hτ ⊢
    linarith
  set radiusFn : ℂ → ℝ := fun z => if z ∈ (As : Set ℂ) then r else 1 / 2 with hradiusFn
  have hradius : ∀ a ∈ As, radiusFn a = r := by
    intro a ha
    show (if a ∈ (As : Set ℂ) then r else 1 / 2) = r
    rw [if_pos (Finset.mem_coe.mpr ha)]
  refine ⟨ρ, ⟨As, radiusFn⟩, hρ_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact hdom₀ (hballρ₀ τ hτ)
  · change (As : Set ℂ) = boundedCenters M k τ₀ R
    exact hAcoe
  · intro a ha
    change 0 < radiusFn a ∧ radiusFn a < 1
    rw [hradius a ha]
    exact ⟨hr_pos, hr_lt_one⟩
  · intro a ha a' ha' hne
    change Disjoint (Metric.closedBall a (radiusFn a))
      (Metric.closedBall a' (radiusFn a'))
    rw [hradius a ha, hradius a' ha']
    apply Metric.closedBall_disjoint_closedBall
    have hdist : ε ≤ dist a a' := hε_ctr a ha a' ha' hne
    linarith
  · intro a ha b hb τ hτ
    change (branchPoint M k τ₀ b = a → dist (branchPoint M k τ b) a < radiusFn a / 2) ∧
      (branchPoint M k τ₀ b ≠ a → radiusFn a < dist (branchPoint M k τ b) a)
    rw [hradius a ha]
    constructor
    · intro heq
      rw [hr_half, ← heq]
      have hbL : b ∈ Ls := by
        refine (hmemL b).mpr ⟨hb, τ₀, ?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_self]; exact hρ₀.le
        · rw [heq]
          exact le_trans ((hmemA a).mp ha).1 (by linarith)
      have h := hmoveM b hbL τ hτ
      linarith [h, hρM_le, hc_pos]
    · intro hne
      by_cases hbL : b ∈ Ls
      · have hnf : b ∉ fiber M k a τ₀ := fun hf => hne hf.2
        have hδ : ε ≤ dist (branchPoint M k τ₀ b) a := hε_fib a ha b hbL hnf
        have hmv := hmoveM b hbL τ hτ
        have htri : dist (branchPoint M k τ₀ b) a ≤
            dist (branchPoint M k τ₀ b) (branchPoint M k τ b) +
              dist (branchPoint M k τ b) a := dist_triangle _ _ _
        rw [dist_comm (branchPoint M k τ₀ b) (branchPoint M k τ b)] at htri
        linarith [hδ, hmv, htri, hr_lt_eps3, hρM_le, hP_lt, hc_le_eps3, hε]
      · have hbnotL : b ∉ {b : Label | b ∈ labels M k ∧
            ∃ τ ∈ Metric.closedBall τ₀ ρ₀, ‖branchPoint M k τ b‖ ≤ R + 1} :=
          fun hmem => hbL ((hmemL b).mpr hmem)
        have hτρ₀ : τ ∈ Metric.closedBall τ₀ ρ₀ := hballρ₀ τ hτ
        have hbig : R + 1 < ‖branchPoint M k τ b‖ := by
          by_contra hle
          exact hbnotL ⟨hb, τ, hτρ₀, not_lt.mp hle⟩
        have hna : ‖a‖ ≤ R := ((hmemA a).mp ha).1
        have htri : ‖branchPoint M k τ b‖ ≤
            dist (branchPoint M k τ b) a + ‖a‖ := by
          calc ‖branchPoint M k τ b‖
              = ‖(branchPoint M k τ b - a) + a‖ := by ring_nf
            _ ≤ ‖branchPoint M k τ b - a‖ + ‖a‖ := norm_add_le _ _
            _ = dist (branchPoint M k τ b) a + ‖a‖ := by rw [dist_eq_norm]
        have hgt : 1 < dist (branchPoint M k τ b) a := by linarith
        linarith [hr_lt_one]
  · intro τ hτ b hb hbn
    have hτρ₀ : τ ∈ Metric.closedBall τ₀ ρ₀ := hballρ₀ τ hτ
    have hbL : b ∈ Ls := (hmemL b).mpr ⟨hb, τ, hτρ₀, by linarith⟩
    have hnorm_le : ‖branchPoint M k τ₀ b‖ ≤ R := by
      by_contra hle
      have hRlt : R < ‖branchPoint M k τ₀ b‖ := not_le.mp hle
      have hεb : ε ≤ ‖branchPoint M k τ₀ b‖ - R := hε_nrm b hbL hRlt
      have hmv := hmoveM b hbL τ hτ
      have htri : ‖branchPoint M k τ₀ b‖ ≤
          ‖branchPoint M k τ b‖ + dist (branchPoint M k τ b) (branchPoint M k τ₀ b) := by
        calc ‖branchPoint M k τ₀ b‖
            = ‖branchPoint M k τ b +
                (branchPoint M k τ₀ b - branchPoint M k τ b)‖ := by ring_nf
          _ ≤ ‖branchPoint M k τ b‖ +
                ‖branchPoint M k τ₀ b - branchPoint M k τ b‖ := norm_add_le _ _
          _ = ‖branchPoint M k τ b‖ +
                dist (branchPoint M k τ b) (branchPoint M k τ₀ b) := by
                rw [dist_eq_norm, norm_sub_rev]
      linarith [hbn, hmv, htri, hρM_le, hP_lt, hc_le_eps3, hε]
    exact (hmemA _).mpr ⟨hnorm_le, b, hb, rfl⟩

/--
Direct pole-free boundary consequence; divisor sets of [RW26, p. 6].
-/
theorem boundary_avoids_labels (M : SL(2, ℤ)) (k : KernelData)
    (τ₀ : ℂ) (ρ : ℝ) (C : Circles)
    (hiso : ∀ a ∈ C.centers, ∀ b ∈ labels M k, ∀ τ ∈ Metric.closedBall τ₀ ρ,
      (branchPoint M k τ₀ b = a → dist (branchPoint M k τ b) a < C.radius a / 2) ∧
      (branchPoint M k τ₀ b ≠ a → C.radius a < dist (branchPoint M k τ b) a))
    (hr : ∀ a ∈ C.centers, 0 < C.radius a) :
    ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ z ∈ boundaries C,
      ∀ b ∈ labels M k, z ≠ branchPoint M k τ b := by
  intro τ hτ z hz b hb hEq
  rw [boundaries, Set.mem_ofPred_eq] at hz
  obtain ⟨a, haC, hza⟩ := hz
  have hda : dist z a = C.radius a := Metric.mem_sphere.mp hza
  have hcase := hiso a haC b hb τ hτ
  rcases eq_or_ne (branchPoint M k τ₀ b) a with heq | hne
  · have hlt := hcase.1 heq
    rw [hEq] at hda
    rw [hda] at hlt
    have hpos := hr a haC
    linarith
  · have hlt := hcase.2 hne
    rw [hEq] at hda
    rw [hda] at hlt
    exact (lt_irrefl _ hlt).elim

/--
Saturation includes every member of a rational multiple cluster; [RW26, p. 6].
-/
theorem inside_iff_center_fiber (M : SL(2, ℤ)) (k : KernelData)
    (τ₀ τ a : ℂ) (r : ℝ) (hr : 0 < r)
    (hiso : ∀ b ∈ labels M k,
      (branchPoint M k τ₀ b = a → dist (branchPoint M k τ b) a < r / 2) ∧
      (branchPoint M k τ₀ b ≠ a → r < dist (branchPoint M k τ b) a)) :
    ∀ b ∈ labels M k, dist (branchPoint M k τ b) a < r ↔ b ∈ fiber M k a τ₀ := by
  intro b hb
  constructor
  · intro hd
    rw [fiber, Set.mem_ofPred_eq]
    refine ⟨hb, ?_⟩
    by_contra hne
    have := (hiso b hb).2 hne
    linarith
  · intro hf
    have := (hiso b hb).1 hf.2
    linarith

/--
Conservation counts labels, not distinct moving positions; [RW26, p. 6], with multiplicity.
-/
theorem inside_label_count (M : SL(2, ℤ)) (k : KernelData)
    (τ₀ τ a : ℂ) (r : ℝ)
    (hinside : ∀ b ∈ labels M k,
      dist (branchPoint M k τ b) a < r ↔ b ∈ fiber M k a τ₀) :
    Nat.card {b | b ∈ labels M k ∧ dist (branchPoint M k τ b) a < r} =
      poleBudget M k a τ₀ := by
  have hset : {b : Label | b ∈ labels M k ∧ dist (branchPoint M k τ b) a < r} =
      fiber M k a τ₀ := by
    ext b
    simp only [fiber, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hb, hd⟩; exact (hinside b hb).mp hd
    · intro hf; exact ⟨hf.1, (hinside b hf.1).mpr hf⟩
  rw [hset]
  rfl

/--
Entire captured disk remains one class. No separation between different
m is asserted; [RW26, p. 6].
-/
theorem inside_same_class (M : SL(2, ℤ)) (k : KernelData)
    (τ₀ τ a : ℂ) (r : ℝ) (hsep : crossSeparated M k τ₀)
    (hinside : ∀ b ∈ labels M k,
      dist (branchPoint M k τ b) a < r ↔ b ∈ fiber M k a τ₀)
    (b b' : Label) (hb : b ∈ labels M k) (hb' : b' ∈ labels M k)
    (hin : dist (branchPoint M k τ b) a < r)
    (hin' : dist (branchPoint M k τ b') a < r) : b.1 = b'.1 := by
  have hbf : b ∈ fiber M k a τ₀ := (hinside b hb).mp hin
  have hbf' : b' ∈ fiber M k a τ₀ := (hinside b' hb').mp hin'
  exact hsep b hb b' hb' (hbf.2.trans hbf'.2.symm)

/--
Simultaneous finite-index selection with one ρ and per-kernel circles.
This is the circle geometry outlet; [RW26, p. 6] divisor sets; for full balls.
-/
theorem finite_family_fixed_circles (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (S : Finset KernelData) (τ₀ : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ (ρ : ℝ) (C : KernelData → Circles), 0 < ρ ∧
      Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M ∧
      ∀ k ∈ S,
        ((C k).centers : Set ℂ) = boundedCenters M k τ₀ R ∧
        (∀ a ∈ (C k).centers, 0 < (C k).radius a ∧ (C k).radius a < 1) ∧
        (∀ a ∈ (C k).centers, ∀ a' ∈ (C k).centers, a ≠ a' →
          Disjoint (Metric.closedBall a ((C k).radius a))
            (Metric.closedBall a' ((C k).radius a'))) ∧
        (∀ a ∈ (C k).centers, ∀ b ∈ labels M k, ∀ τ ∈ Metric.closedBall τ₀ ρ,
          (branchPoint M k τ₀ b = a →
            dist (branchPoint M k τ b) a < (C k).radius a / 2) ∧
          (branchPoint M k τ₀ b ≠ a →
            (C k).radius a < dist (branchPoint M k τ b) a)) ∧
        (∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ b ∈ labels M k,
          ‖branchPoint M k τ b‖ ≤ R → branchPoint M k τ₀ b ∈ (C k).centers) := by
  choose ρk Ck hspec using fun k : KernelData =>
    exists_fixed_circles M hM k τ₀ hτ₀ R hR
  obtain ⟨ρd, hρd, hdomd⟩ : ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall τ₀ ρ ⊆ modularPhiDomain M := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_modularPhiDomain M) τ₀ hτ₀
    refine ⟨ε / 2, by positivity, ?_⟩
    intro τ hτ
    apply hball
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hτ
    linarith [hε]
  obtain ⟨ρS, hρS, hρSle⟩ := exists_pos_le_of_finset S (fun k => ρk k)
    (fun k _ => (hspec k).1)
  refine ⟨min ρd ρS, Ck, lt_min hρd hρS, ?_, ?_⟩
  · intro τ hτ
    apply hdomd
    rw [Metric.mem_closedBall] at hτ ⊢
    have : min ρd ρS ≤ ρd := min_le_left _ _
    linarith
  · intro k hk
    obtain ⟨_, hdomk, hcent, hrad, hdisj, hiso, hcov⟩ := hspec k
    have hsub : Metric.closedBall τ₀ (min ρd ρS) ⊆ Metric.closedBall τ₀ (ρk k) := by
      intro τ hτ
      rw [Metric.mem_closedBall] at hτ ⊢
      have h1 : min ρd ρS ≤ ρS := min_le_right _ _
      have h2 : ρS ≤ ρk k := hρSle k hk
      linarith
    exact ⟨hcent, hrad, hdisj,
      fun a ha b hb τ hτ => hiso a ha b hb τ (hsub hτ),
      fun τ hτ b hb hbn => hcov τ (hsub hτ) b hb hbn⟩

#check modularPhiDivisor_uniform_local_finiteness
#check modularPhiDivisor_compact_finiteness
#check modularPhiDivisor_indices_finite
#check Set.Finite.toFinset
#check Nat.card
#print KernelData
#print withParameters
#print labels
#print branchPoint
#print fiber
#print poleBudget

end SICLean.L4.ModularCluster
