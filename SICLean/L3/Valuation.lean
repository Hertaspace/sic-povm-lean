import SICLean.L3.ValuationSupport

set_option autoImplicit false

/-!
# The additive valuation argument for the whole finite family

Values lie in `WithTop ℝ`, so the additive normalization is v(2) = 1.
This file makes no assertion about prime ideals or global algebraic units.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L3

universe u v w w'

variable {I : Type u} [Fintype I] {G : I → Type v}
variable [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]
variable {k : Type w} [Field k]

namespace FiniteSystem

open ValuationSupport

variable (D : FiniteSystem I G k)
variable {L : Type w'} [Field L] [CharZero L] [Algebra k L]

/-- Roots of unity have additive value 0, while s_N has nonnegative value.
Keeping the s_N term is necessary when N is even. -/
theorem coefficient_valuations (v : AddValuation L (WithTop ℝ))
    (h2 : v (2 : L) = 1) :
    0 ≤ v (algebraMap k L D.sqrtN) ∧
      (∀ i x, v (algebraMap k L (D.gaussian i x)) = 0) ∧
      (∀ i h, v (algebraMap k L (D.multiplier i h)) = 0) := by
  have hs : (algebraMap k L D.sqrtN) ^ 2 = (D.N : L) := by
    simpa using congrArg (algebraMap k L) D.sqrtN_sq
  refine ⟨nonneg_of_square v (hs ▸ natCast_nonneg v D.N), ?_, ?_⟩
  · intro i x
    apply value_pow_eq_one v (n := 2 * D.N) (by have := D.N_pos; omega)
    simpa using congrArg (algebraMap k L) (D.gaussian_order i x)
  · intro i h
    apply value_pow_eq_one v (by decide : (24 : ℕ) ≠ 0)
    simpa using congrArg (algebraMap k L) (D.multiplier_order i h)

theorem origin_valuation (z : Coordinate I G → L) (hz : D.IsSolution L z)
    (v : AddValuation L (WithTop ℝ)) (h2 : v (2 : L) = 1) (i : I) :
    v (z ⟨i, 0⟩) = 0 := by
  let s := algebraMap k L D.sqrtN
  let e := z ⟨i, 0⟩
  have hs2 : s ^ 2 = (D.N : L) := by
    simpa [s] using congrArg (algebraMap k L) D.sqrtN_sq
  have hs0 : s ≠ 0 := by
    intro h
    have hN : (D.N : L) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.N_pos)
    exact hN (by simpa [h] using hs2.symm)
  have he0 : e ≠ 0 := D.solution_coordinate_ne_zero L z hz ⟨i, 0⟩
  let a := realValue v s
  let r := realValue v e
  have ha : 0 ≤ a := WithTop.untop₀_nonneg.mpr (D.coefficient_valuations v h2).1
  have hvse : v (s * e) = ((a + r : ℝ) : WithTop ℝ) := by
    rw [v.map_mul, ← coe_realValue v hs0, ← coe_realValue v he0, ← WithTop.coe_add]
  have hve2 : v (e ^ 2) = ((r + r : ℝ) : WithTop ℝ) := by
    rw [v.map_pow, two_nsmul, ← coe_realValue v he0, ← WithTop.coe_add]
  have heq : e ^ 2 = s * e + 1 := by
    dsimp [e, s]
    linear_combination hz.q1 i
  have hone : e ^ 2 - s * e = 1 := by rw [heq]; ring
  have hb := v.map_add (s * e) 1
  rw [← heq, hve2, hvse, v.map_one] at hb
  have hb' : min (a + r) 0 ≤ r + r := by exact_mod_cast hb
  have hc := v.map_sub (e ^ 2) (s * e)
  rw [hone, hve2, hvse, v.map_one] at hc
  have hc' : min (r + r) (a + r) ≤ 0 := by exact_mod_cast hc
  have hr : r = 0 := by
    rcases lt_trichotomy r 0 with hr | hr | hr
    · have hm : r ≤ min (a + r) 0 := le_min (by linarith) hr.le
      linarith
    · exact hr
    · have hm : 0 < min (r + r) (a + r) := lt_min (by linarith) (by linarith)
      linarith
  change v e = 0
  rw [← coe_realValue v he0]
  change (r : WithTop ℝ) = 0
  simp [hr]

/-- Minimize over *all* coordinates. Q4 raises each 2-torsion term from
the possible value 4m to at least 2m. The paired terms have value ≥ 1+4m.
No hypothesis `u+u ≠ 0` or surjectivity of `project` is available. -/
theorem solution_valuation_nonneg (z : Coordinate I G → L)
    (hz : D.IsSolution L z) (v : AddValuation L (WithTop ℝ))
    (h2 : v (2 : L) = 1) (c : Coordinate I G) : 0 ≤ v (z c) := by
  classical
  let r : Coordinate I G → ℝ := fun b => realValue v (z b)
  have hvals (b : Coordinate I G) : v (z b) = (r b : WithTop ℝ) :=
    (coe_realValue v (D.solution_coordinate_ne_zero L z hz b)).symm
  have : Nonempty (Coordinate I G) := ⟨c⟩
  obtain ⟨⟨i, u⟩, hmin⟩ := Finite.exists_min r
  let m : ℝ := r ⟨i, u⟩
  apply WithTop.untop₀_nonneg.mp
  change 0 ≤ r c
  by_contra hc
  have hm : m < 0 := lt_of_le_of_lt (hmin c) (lt_of_not_ge hc)
  have hu : u ≠ 0 := by
    intro h
    subst u
    have he := D.origin_valuation z hz v h2 i
    have hm0 : m = 0 := by simp [m, r, realValue, he]
    linarith
  let f : G i → L := fun s =>
    algebraMap k L (D.gaussian i s) * z ⟨i, u + s⟩ * z ⟨i, u - s⟩
  have hfneg (s : G i) : f (-s) = f s := by
    simp only [f, D.gaussian_neg, sub_eq_add_neg, neg_neg]
    ring
  obtain ⟨T, _, _, hpair⟩ := exists_neg_pair_sum f hfneg
  have hf0 : f 0 = z ⟨i, u⟩ ^ 2 := by
    simp [f, D.gaussian_zero, pow_two]
  have hsplit : algebraMap k L D.sqrtN * z ⟨i, u + u⟩ =
      z ⟨i, u⟩ ^ 4 +
        ((∑ h : {h : G i // h ≠ 0 ∧ h + h = 0}, z ⟨i, u⟩ ^ 2 * f h.val) +
          2 * z ⟨i, u⟩ ^ 2 * ∑ s ∈ T, f s) := by
    rw [hz.q3 i u hu, hpair, hf0, mul_add, mul_add, Finset.mul_sum]
    ring
  obtain ⟨hsqrt, hgauss, hmult⟩ := D.coefficient_valuations v h2
  have hvf (s : G i) :
      v (f s) = ((r ⟨i, u + s⟩ + r ⟨i, u - s⟩ : ℝ) : WithTop ℝ) := by
    dsimp [f]
    rw [v.map_mul, v.map_mul, hgauss, hvals, hvals, zero_add, ← WithTop.coe_add]
  have hfixed (h : OrderTwo I G i) :
      z ⟨i, u⟩ ^ 2 * f h.val =
        algebraMap k L (D.gaussian i h.val) *
          (algebraMap k L (D.multiplier i h) *
            z ⟨D.target i h, D.project i h u⟩) ^ 2 := by
    have hh : -h.val = h.val :=
      (eq_neg_iff_add_eq_zero.mpr h.property.2).symm
    calc
      _ = algebraMap k L (D.gaussian i h.val) *
          (z ⟨i, u⟩ * z ⟨i, u + h.val⟩) ^ 2 := by
        simp only [f, sub_eq_add_neg, hh]
        ring
      _ = _ := by rw [hz.q4 i h u]
  have hfixed_lt (h : OrderTwo I G i) :
      ((4 * m : ℝ) : WithTop ℝ) < v (z ⟨i, u⟩ ^ 2 * f h.val) := by
    rw [hfixed, v.map_mul, hgauss, v.map_pow, v.map_mul, hmult, zero_add,
      zero_add, hvals, ← WithTop.coe_nsmul, WithTop.coe_lt_coe]
    have hb := hmin ⟨D.target i h, D.project i h u⟩
    change m ≤ r ⟨D.target i h, D.project i h u⟩ at hb
    simp only [two_nsmul]
    linarith
  have hfixed_sum : ((4 * m : ℝ) : WithTop ℝ) <
      v (∑ h : {h : G i // h ≠ 0 ∧ h + h = 0}, z ⟨i, u⟩ ^ 2 * f h.val) := by
    exact v.map_lt_sum WithTop.coe_ne_top (fun h _ => hfixed_lt h)
  have hpaired_lt (s : G i) : ((4 * m : ℝ) : WithTop ℝ) <
      v (2 * z ⟨i, u⟩ ^ 2 * f s) := by
    rw [v.map_mul, v.map_mul, h2, v.map_pow, hvals, hvf,
      ← WithTop.coe_nsmul, ← WithTop.coe_one,
      ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_lt_coe]
    have hp := hmin ⟨i, u + s⟩
    have hn := hmin ⟨i, u - s⟩
    change m ≤ r ⟨i, u + s⟩ at hp
    change m ≤ r ⟨i, u - s⟩ at hn
    change 4 * m < 1 + 2 • m + (r ⟨i, u + s⟩ + r ⟨i, u - s⟩)
    simp only [two_nsmul]
    linarith
  have hpaired_sum : ((4 * m : ℝ) : WithTop ℝ) <
      v (2 * z ⟨i, u⟩ ^ 2 * ∑ s ∈ T, f s) := by
    rw [Finset.mul_sum]
    exact v.map_lt_sum WithTop.coe_ne_top (fun s _ => hpaired_lt s)
  have hrest := v.map_lt_add hfixed_sum hpaired_sum
  have hfour : v (z ⟨i, u⟩ ^ 4) = ((4 * m : ℝ) : WithTop ℝ) := by
    rw [v.map_pow, hvals, ← WithTop.coe_nsmul]
    congr 1
    simp [m, nsmul_eq_mul]
  have hright : v (algebraMap k L D.sqrtN * z ⟨i, u + u⟩) =
      ((4 * m : ℝ) : WithTop ℝ) := by
    rw [hsplit, v.map_add_eq_of_lt_left (hfour ▸ hrest), hfour]
  have hleft : (m : WithTop ℝ) ≤
      v (algebraMap k L D.sqrtN * z ⟨i, u + u⟩) := by
    rw [v.map_mul]
    calc
      (m : WithTop ℝ) ≤ v (z ⟨i, u + u⟩) := by
        rw [hvals, WithTop.coe_le_coe]
        exact hmin ⟨i, u + u⟩
      _ ≤ _ := by simpa [add_comm] using add_le_add_right hsqrt (v (z ⟨i, u + u⟩))
  rw [hright, WithTop.coe_le_coe] at hleft
  linarith

/-- Reflection upgrades integrality to being a unit at this valuation.
This theorem concerns arbitrary solutions in a valued characteristic-zero
field, and does not assume their coordinates are algebraic. -/
theorem solution_valuation_eq_zero (z : Coordinate I G → L)
    (hz : D.IsSolution L z) (v : AddValuation L (WithTop ℝ))
    (h2 : v (2 : L) = 1) (c : Coordinate I G) : v (z c) = 0 := by
  obtain ⟨i, x⟩ := c
  by_cases hx : x = 0
  · subst x
    exact D.origin_valuation z hz v h2 i
  · have hq := congrArg v (hz.q2 i x hx)
    have hg := (D.coefficient_valuations v h2).2.1 i x
    rw [v.map_mul, map_inv₀, v.map_inv, hg, neg_zero] at hq
    have hp := D.solution_valuation_nonneg z hz v h2 ⟨i, x⟩
    have hn := D.solution_valuation_nonneg z hz v h2 ⟨i, -x⟩
    apply le_antisymm _ hp
    calc
      v (z ⟨i, x⟩) ≤ v (z ⟨i, x⟩) + v (z ⟨i, -x⟩) := by
        simpa [add_comm] using add_le_add_left hn (v (z ⟨i, x⟩))
      _ = 0 := hq

end FiniteSystem
end SICLean.L3

#check @AddValuation
#check @AddValuation.comap
#check @AddValuation.map_pow
#check @SICLean.L3.FiniteSystem.solution_valuation_eq_zero
