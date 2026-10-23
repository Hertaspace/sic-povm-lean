import SICLean.L4.SpecialValueDescent

set_option autoImplicit false

/-!
# Auxiliary lemmas
Elementary exponential, parity and row-action facts used by
`SpecialValueReflection.lean`. Nothing here mentions the definitions of that
file, so it can be imported before them.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4

/-! ## The phase `e` at half integers -/

/-- `e (n/2) = (-1)^n`, the exact bridge between the sign and the phase. -/
lemma e_half_int (n : ℤ) : e ((n : ℂ) / 2) = (-1 : ℂ) ^ n := by
  have h1 : e ((1 : ℂ) / 2) = -1 := by
    simp only [e]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℂ) / 2) = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have h2 : e ((1 : ℂ) / 2) ^ n = e ((n : ℂ) * ((1 : ℂ) / 2)) := e_int_mul _ _
  rw [show (n : ℂ) / 2 = (n : ℂ) * ((1 : ℂ) / 2) by ring, ← h2, h1]

/-- Equal parities give equal signs. -/
lemma neg_one_zpow_congr {p q : ℤ} (h : Even (p - q)) :
    (-1 : ℂ) ^ p = (-1 : ℂ) ^ q := by
  obtain ⟨k, hk⟩ := h
  have hp : p = q + 2 * k := by linarith
  have h2k : Even (2 * k : ℤ) := ⟨k, by ring⟩
  rw [hp, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), h2k.neg_one_zpow, mul_one]

/-! ## The row action -/

/-- The row action of `M - 1` is the difference of the row actions. -/
lemma rowAction_sub_one_apply (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u =
      L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u := by
  ext <;>
    simp [L2r.rowAction, Matrix.sub_apply, Matrix.one_apply] <;> ring

/-- The two row generators of the lattice are the rows of `M - 1`. -/
lemma rowAction_sub_one_fst (M : SL(2, ℤ)) :
    L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) (1, 0) =
      ((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1, (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
  ext <;> simp [L2r.rowAction, Matrix.sub_apply, Matrix.one_apply]

lemma rowAction_sub_one_snd (M : SL(2, ℤ)) :
    L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) (0, 1) =
      ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) := by
  ext <;> simp [L2r.rowAction, Matrix.sub_apply, Matrix.one_apply]

/-- The determinant of `M - 1` is `-N`, where `N = tr M - 2`. -/
lemma det_sub_one (M : SL(2, ℤ)) :
    (((M : Matrix (Fin 2) (Fin 2) ℤ) - 1).det : ℤ) = -specialValueOrder M := by
  have h := det_coe_int M
  rw [Matrix.det_fin_two]
  simp [Matrix.sub_apply, Matrix.one_apply, specialValueOrder]
  nlinarith [h]

/-- Cayley--Hamilton in the form `(M-1)^2 = N M`. -/
lemma reflAux_sub_one_sq (M : SL(2, ℤ)) :
    ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) * ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) =
      (specialValueOrder M) • (M : Matrix (Fin 2) (Fin 2) ℤ) := by
  have h := det_coe_int M
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Fin.sum_univ_two, specialValueOrder] <;>
    nlinarith [h]

/-- Applying the row action of `M-1` twice is multiplication by `N`. -/
lemma reflAux_rowAction_sub_one_sq (M : SL(2, ℤ)) (w : ℤ × ℤ) :
    L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
        (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w) =
      (specialValueOrder M) • L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w := by
  have h := reflAux_sub_one_sq M
  have hmul : L2r.rowAction (((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) *
      ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)) w =
      L2r.rowAction ((specialValueOrder M) • (M : Matrix (Fin 2) (Fin 2) ℤ)) w := by
    rw [h]
  have h1 : L2r.rowAction (((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) *
      ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)) w =
      L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
        (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w) := by
    ext <;> simp [L2r.rowAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have h2 : L2r.rowAction ((specialValueOrder M) • (M : Matrix (Fin 2) (Fin 2) ℤ)) w =
      (specialValueOrder M) • L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w := by
    ext <;> simp [L2r.rowAction, Matrix.smul_apply] <;> ring
  rw [← h1, hmul, h2]

/-- The alternating form of two `X`-images is `det X` times the original. -/
lemma alt_rowAction_rowAction (X : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℤ × ℤ) :
    let z := L2r.rowAction X x
    let w := L2r.rowAction X y
    z.1 * w.2 - z.2 * w.1 = X.det * (x.1 * y.2 - x.2 * y.1) := by
  simp only [L2r.rowAction, Matrix.det_fin_two]
  ring

/-- Scaling a vector scales the alternating form. -/
lemma alt_smul_left (n : ℤ) (x y : ℤ × ℤ) :
    let z := n • x
    z.1 * y.2 - z.2 * y.1 = n * (x.1 * y.2 - x.2 * y.1) := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The row action of `M - 1` on `x` in terms of the two lattice generators. -/
lemma reflAux_rowAction_sub_one_eq (M : SL(2, ℤ)) (x : ℤ × ℤ) :
    L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) x =
      x.1 • ((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1, (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) +
      x.2 • ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) := by
  ext <;> simp [L2r.rowAction, Matrix.sub_apply] <;> ring

end SICLean.L4

namespace SICLean.L4

/-- Composition of row actions. -/
lemma rowAction_rowAction (M N : Matrix (Fin 2) (Fin 2) ℤ) (w : ℤ × ℤ) :
    L2r.rowAction M (L2r.rowAction N w) = L2r.rowAction (N * M) w := by
  ext <;> simp [L2r.rowAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `M` commutes with `M - 1`. -/
lemma mul_sub_one_comm (M : Matrix (Fin 2) (Fin 2) ℤ) :
    M * (M - 1) = (M - 1) * M := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]

/-- The `M`-image of `(M-1)w` is the `(M-1)`-image of `Mw`. -/
lemma rowAction_apply_sub_one (M : Matrix (Fin 2) (Fin 2) ℤ) (w : ℤ × ℤ) :
    L2r.rowAction M (L2r.rowAction (M - 1) w) =
      L2r.rowAction (M - 1) (L2r.rowAction M w) := by
  rw [rowAction_rowAction, rowAction_rowAction, mul_sub_one_comm]

end SICLean.L4

namespace SICLean.L4

/-- The finite field check behind the Gaussian parity: over `ZMod 2`, every
`SL₂` matrix `M = [[a,b],[c,d]]` satisfies `q((M-1)w) = ω(Mw,w)`. -/
lemma parity_zmod_two (a b c d w1 w2 : ZMod 2) (h : a * d - b * c = 1) :
    ((a - 1) * w1 + c * w2) + (b * w1 + (d - 1) * w2) +
        ((a - 1) * w1 + c * w2) * (b * w1 + (d - 1) * w2) =
      (a * w1 + c * w2) * w2 - (b * w1 + d * w2) * w1 := by
  revert h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases w1 <;> fin_cases w2 <;> decide

/-- Parity form: for `v = (M-1)w`, `q(v) - ω(Mw,w)` is even. -/
lemma even_parity_key (a b c d w1 w2 : ℤ) (h : a * d - b * c = 1) :
    Even (((a - 1) * w1 + c * w2) + (b * w1 + (d - 1) * w2) +
        ((a - 1) * w1 + c * w2) * (b * w1 + (d - 1) * w2) -
      ((a * w1 + c * w2) * w2 - (b * w1 + d * w2) * w1)) := by
  rw [← ZMod.intCast_eq_zero_iff_even]
  push_cast
  have hdet : (a : ZMod 2) * (d : ZMod 2) - (b : ZMod 2) * (c : ZMod 2) = 1 := by
    have h' : ((a * d - b * c : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) := by rw [h]
    push_cast at h'
    exact h'
  have := parity_zmod_two (a : ZMod 2) (b : ZMod 2) (c : ZMod 2) (d : ZMod 2)
    (w1 : ZMod 2) (w2 : ZMod 2) hdet
  linear_combination this

end SICLean.L4
