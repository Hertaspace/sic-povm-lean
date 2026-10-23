import Mathlib

set_option autoImplicit false

/-!
# The finite Q1--Q4 system, independent of the analytic construction

The family and its groups are finite. No parity, surjectivity, or exclusion of
`u + u = 0` is imposed. The facts `card (G i) = N` and `ker π = {0,h}` are
not used in the abstract argument.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L3

universe u v w w'

variable (I : Type u) (G : I → Type v)
variable [Fintype I] [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]

/-- The nonzero elements killed by 2. In particular, the trivial group gives
an empty type here, rather than an additional hypothesis. -/
def OrderTwo (i : I) := {h : G i // h ≠ 0 ∧ h + h = 0}

/-- A single coordinate remembers which member of the finite family it uses. -/
abbrev Coordinate := (i : I) × G i

variable (k : Type w) [Field k]

/-- Coefficients and cross-family labels.
Only the set map underlying π is used. Its source includes every nonzero
2-torsion element, and Q4 below includes every x, including 0 and h. -/
structure FiniteSystem (I : Type u) [Fintype I] (G : I → Type v)
    [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)] (k : Type w) [Field k] where
  N : ℕ
  N_pos : 0 < N
  sqrtN : k
  sqrtN_sq : sqrtN ^ 2 = (N : k)
  gaussian : ∀ i, G i → k
  gaussian_zero : ∀ i, gaussian i 0 = 1
  gaussian_neg : ∀ i x, gaussian i (-x) = gaussian i x
  gaussian_order : ∀ i x, gaussian i x ^ (2 * N) = 1
  target : ∀ i, OrderTwo I G i → I
  project : ∀ i (h : OrderTwo I G i), G i → G (target i h)
  multiplier : ∀ i, OrderTwo I G i → k
  multiplier_order : ∀ i h, multiplier i h ^ 24 = 1

variable {I G k}

namespace FiniteSystem

variable (D : FiniteSystem I G k)
variable (L : Type w') [Field L] [Algebra k L]

/-- A point of exactly Q1--Q4 after the specified scalar map. There is no
analytic input and no algebraicity assumption on the point. -/
structure IsSolution (z : Coordinate I G → L) : Prop where
  q1 : ∀ i, z ⟨i, 0⟩ ^ 2 - algebraMap k L D.sqrtN * z ⟨i, 0⟩ - 1 = 0
  q2 : ∀ i (x : G i), x ≠ 0 →
    z ⟨i, x⟩ * z ⟨i, -x⟩ = algebraMap k L (D.gaussian i x)⁻¹
  q3 : ∀ i (u : G i), u ≠ 0 →
    algebraMap k L D.sqrtN * z ⟨i, u + u⟩ =
      z ⟨i, u⟩ ^ 2 * ∑ s : G i,
        algebraMap k L (D.gaussian i s) * z ⟨i, u + s⟩ * z ⟨i, u - s⟩
  q4 : ∀ i (h : OrderTwo I G i) (x : G i),
    z ⟨i, x⟩ * z ⟨i, x + h.val⟩ =
      algebraMap k L (D.multiplier i h) * z ⟨D.target i h, D.project i h x⟩

/-- The actual polynomial for Q1. -/
def q1Polynomial (i : I) : MvPolynomial (Coordinate I G) k :=
  MvPolynomial.X ⟨i, 0⟩ ^ 2 -
    MvPolynomial.C D.sqrtN * MvPolynomial.X ⟨i, 0⟩ - 1

def q2Polynomial (i : I) (x : G i) : MvPolynomial (Coordinate I G) k :=
  MvPolynomial.X ⟨i, x⟩ * MvPolynomial.X ⟨i, -x⟩ -
    MvPolynomial.C (D.gaussian i x)⁻¹

def q3Polynomial (i : I) (u : G i) : MvPolynomial (Coordinate I G) k :=
  MvPolynomial.C D.sqrtN * MvPolynomial.X ⟨i, u + u⟩ -
    MvPolynomial.X ⟨i, u⟩ ^ 2 * ∑ s : G i,
      MvPolynomial.C (D.gaussian i s) *
        MvPolynomial.X ⟨i, u + s⟩ * MvPolynomial.X ⟨i, u - s⟩

def q4Polynomial (i : I) (h : OrderTwo I G i) (x : G i) :
    MvPolynomial (Coordinate I G) k :=
  MvPolynomial.X ⟨i, x⟩ * MvPolynomial.X ⟨i, x + h.val⟩ -
    MvPolynomial.C (D.multiplier i h) *
      MvPolynomial.X ⟨D.target i h, D.project i h x⟩

/-- A finite set of generators. Q2 and Q3 are only imposed off zero. -/
def equations : Set (MvPolynomial (Coordinate I G) k) :=
  {p | (∃ i, p = D.q1Polynomial i) ∨
    (∃ i, ∃ x : G i, x ≠ 0 ∧ p = D.q2Polynomial i x) ∨
    (∃ i, ∃ u : G i, u ≠ 0 ∧ p = D.q3Polynomial i u) ∨
    (∃ i, ∃ h : OrderTwo I G i, ∃ x : G i, p = D.q4Polynomial i h x)}

def equationIdeal : Ideal (MvPolynomial (Coordinate I G) k) :=
  Ideal.span D.equations

def solutionSet : Set (Coordinate I G → L) := {z | D.IsSolution L z}

def coordinateImage (c : Coordinate I G) : Set L :=
  (fun z : Coordinate I G → L => z c) '' D.solutionSet L

theorem equations_finite : D.equations.Finite := by
  classical
  haveI (i : I) : Finite (OrderTwo I G i) :=
    inferInstanceAs (Finite {h : G i // h ≠ 0 ∧ h + h = 0})
  let f₂ : Coordinate I G → MvPolynomial (Coordinate I G) k :=
    fun c => D.q2Polynomial c.1 c.2
  let f₃ : Coordinate I G → MvPolynomial (Coordinate I G) k :=
    fun c => D.q3Polynomial c.1 c.2
  let f₄ : (Σ i, OrderTwo I G i × G i) → MvPolynomial (Coordinate I G) k :=
    fun c => D.q4Polynomial c.1 c.2.1 c.2.2
  refine (((Set.finite_range D.q1Polynomial).union (Set.finite_range f₂)).union
    ((Set.finite_range f₃).union (Set.finite_range f₄))).subset ?_
  rintro p (⟨i, rfl⟩ | ⟨i, x, _, rfl⟩ | ⟨i, x, _, rfl⟩ | ⟨i, h, x, rfl⟩)
  · exact Or.inl (Or.inl ⟨i, rfl⟩)
  · exact Or.inl (Or.inr ⟨⟨i, x⟩, rfl⟩)
  · exact Or.inr (Or.inl ⟨⟨i, x⟩, rfl⟩)
  · exact Or.inr (Or.inr ⟨⟨i, h, x⟩, rfl⟩)

/-- The polynomial and point interfaces refer to the same equations. -/
theorem isSolution_iff_mem_zeroLocus (z : Coordinate I G → L) :
    D.IsSolution L z ↔ z ∈ MvPolynomial.zeroLocus L D.equationIdeal := by
  rw [equationIdeal, MvPolynomial.zeroLocus_span]
  constructor
  · intro hz p hp
    rcases hp with ⟨i, rfl⟩ | ⟨i, x, hx, rfl⟩ | ⟨i, x, hx, rfl⟩ | ⟨i, h, x, rfl⟩
    · simpa [q1Polynomial] using hz.q1 i
    · simpa [q2Polynomial, sub_eq_zero] using hz.q2 i x hx
    · simpa [q3Polynomial, sub_eq_zero] using hz.q3 i x hx
    · simpa [q4Polynomial, sub_eq_zero] using hz.q4 i h x
  · intro hz
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simpa [q1Polynomial] using hz _ (Or.inl ⟨i, rfl⟩)
    · intro i x hx
      simpa [q2Polynomial, sub_eq_zero] using
        hz _ (Or.inr (Or.inl ⟨i, x, hx, rfl⟩))
    · intro i x hx
      simpa [q3Polynomial, sub_eq_zero] using
        hz _ (Or.inr (Or.inr (Or.inl ⟨i, x, hx, rfl⟩)))
    · intro i h x
      simpa [q4Polynomial, sub_eq_zero] using
        hz _ (Or.inr (Or.inr (Or.inr ⟨i, h, x, rfl⟩)))

theorem solution_coordinate_ne_zero (z : Coordinate I G → L)
    (hz : D.IsSolution L z) (c : Coordinate I G) : z c ≠ 0 := by
  obtain ⟨i, x⟩ := c
  intro he
  by_cases hx : x = 0
  · subst x
    simpa [he] using hz.q1 i
  · have hg : D.gaussian i x ≠ 0 := by
      intro h
      have := D.gaussian_order i x
      simp [h, ne_of_gt D.N_pos] at this
    have hq := hz.q2 i x hx
    simp [he, map_inv₀] at hq
    exact hg ((algebraMap k L).injective (hq.symm.trans (map_zero _).symm))

end FiniteSystem
end SICLean.L3

#check @SICLean.L3.FiniteSystem
#check @SICLean.L3.FiniteSystem.IsSolution
#print SICLean.L3.FiniteSystem
#print SICLean.L3.FiniteSystem.IsSolution
