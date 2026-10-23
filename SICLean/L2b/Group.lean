import SICLean.L2b.FiniteQD

set_option autoImplicit false

/-!
# The concrete group for γ = α³, in Smith coordinates

[RW26, §4.3--§4.4]. All arithmetic structure is defined here.
`Fact (4 ≤ M)` packages only the dimension bound, never a property of G or E.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2b

abbrev cofactor (M : ℕ) : ℕ := M - 3
abbrev longModulus (M : ℕ) : ℕ := M * cofactor M
abbrev groupOrder (M : ℕ) : ℕ := M ^ 2 * cofactor M

/-- Smith coordinates. A representative (x,y) has numerator
`(a,b)=(x,y-(M-2)x)` relative to ε⁻³−1, as in [RW26]. -/
abbrev G (M : ℕ) := ZMod M × ZMod (longModulus M)

instance validMNeZero (M : ℕ) [Fact (4 ≤ M)] : NeZero M :=
  ⟨by have := (Fact.out : 4 ≤ M); omega⟩

instance cofactorNeZero (M : ℕ) [Fact (4 ≤ M)] : NeZero (cofactor M) :=
  ⟨by have := (Fact.out : 4 ≤ M); simp only [cofactor]; omega⟩

instance longModulusNeZero (M : ℕ) [Fact (4 ≤ M)] : NeZero (longModulus M) :=
  ⟨by
    have h4 := (Fact.out : 4 ≤ M)
    exact Nat.mul_ne_zero (by omega) (by simp only [cofactor]; omega)⟩

def coordinate (M : ℕ) (x y : ℤ) : G M := (x, y)

def numerator (M : ℕ) (g : G M) : ℤ × ℤ :=
  (g.1.val, (g.2.val : ℤ) - ((M : ℤ) - 2) * g.1.val)

def alpha (M : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(M : ℤ) - 1, -1; 1, 0]

def gamma (M : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := alpha M ^ 3

/-- γ−I in RW's row convention. Its bottom-right entry is −M. -/
def gammaMinusOne (M : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(M : ℤ) * ((M : ℤ) ^ 2 - 3 * M + 1), -(M : ℤ) * ((M : ℤ) - 2);
    (M : ℤ) * ((M : ℤ) - 2), -(M : ℤ)]

def smithLeft (M : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-((M : ℤ) - 1), (M : ℤ) * ((M : ℤ) - 2);
    (M : ℤ) - 2, -((M : ℤ) ^ 2 - 3 * M + 1)]

def smithRight (M : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, (M : ℤ) - 2; 0, 1]

variable (M : ℕ) [Fact (4 ≤ M)]

theorem gamma_sub_one : gamma M - 1 = gammaMinusOne M := by
  have h2 : alpha M ^ 2 = !![((M : ℤ) - 1) ^ 2 - 1, -((M : ℤ) - 1); (M : ℤ) - 1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alpha, pow_two, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two] <;> ring
  have h3 : alpha M ^ 3 =
      !![(M : ℤ) * ((M : ℤ) ^ 2 - 3 * (M : ℤ) + 1) + 1, -((M : ℤ) * ((M : ℤ) - 2));
        (M : ℤ) * ((M : ℤ) - 2), -((M : ℤ) - 1)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alpha, h2, pow_succ, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two] <;>
        ring
  ext i j
  simp only [gamma, h3, Matrix.sub_apply, Matrix.one_apply, gammaMinusOne, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> ring

theorem gamma_trace : (gamma M).trace = (groupOrder M : ℤ) + 2 := by
  have h5 : (groupOrder M : ℤ) = (M : ℤ) ^ 3 - 3 * (M : ℤ) ^ 2 := by
    have h4 : (cofactor M : ℤ) = (M : ℤ) - 3 :=
      Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)
    simp only [groupOrder, Nat.cast_mul, Nat.cast_pow]
    rw [h4]
    ring
  rw [h5]
  simp only [gamma, alpha, Matrix.trace, Matrix.diag_apply, pow_succ, pow_zero,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, one_mul, zero_mul, add_zero,
    zero_add, mul_zero, mul_one]
  ring

theorem smith_diagonal :
    smithLeft M * gammaMinusOne M * smithRight M =
      !![(M : ℤ), 0; 0, (longModulus M : ℤ)] := by
  have hn : (longModulus M : ℤ) = (M : ℤ) * ((M : ℤ) - 3) := by
    simp only [longModulus, cofactor, Nat.cast_mul]
    exact congrArg ((M : ℤ) * ·) (Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega))
  rw [hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smithLeft, smithRight, gammaMinusOne, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, one_mul, zero_mul, add_zero, zero_add, mul_zero, mul_one] <;>
      ring

theorem smith_unimodular : (smithLeft M).det = -1 ∧ (smithRight M).det = 1 := by
  constructor
  · simp only [smithLeft, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.tail_cons] <;> ring
  · simp only [smithRight, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.tail_cons] <;> ring

theorem gamma_entries_gcd :
    Int.gcd (gammaMinusOne M 0 0)
      (Int.gcd (gammaMinusOne M 0 1)
        (Int.gcd (gammaMinusOne M 1 0) (gammaMinusOne M 1 1))) = M := by
  simp only [gammaMinusOne, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]
  set e00 := (M : ℤ) * ((M : ℤ) ^ 2 - 3 * (M : ℤ) + 1) with he00
  set e01 := -((M : ℤ)) * ((M : ℤ) - 2) with he01
  set e10 := (M : ℤ) * ((M : ℤ) - 2) with he10
  set e11 := -((M : ℤ)) with he11
  -- the nested gcd divides the last entry -M, hence M
  have hle : (↑(Int.gcd e00 (Int.gcd e01 (Int.gcd e10 e11))) : ℤ) ∣ (M : ℤ) :=
    Int.dvd_neg.mp (((Int.gcd_dvd_right e00 (Int.gcd e01 (Int.gcd e10 e11))).trans
      (Int.gcd_dvd_right e01 (Int.gcd e10 e11))).trans (Int.gcd_dvd_right e10 e11))
  -- M divides every entry, hence the nested gcd
  have hd01 : ((M : ℤ)) ∣ (-((M : ℤ)) * ((M : ℤ) - 2)) := ⟨-((M : ℤ) - 2), by ring⟩
  have hd11 : ((M : ℤ)) ∣ (-((M : ℤ))) := ⟨-1, by ring⟩
  have hg1 : M ∣ Int.gcd e10 e11 := Int.dvd_gcd (dvd_mul_right _ _) hd11
  have hg2 : M ∣ Int.gcd e01 (Int.gcd e10 e11) :=
    Int.dvd_gcd hd01 (Int.natCast_dvd_natCast.mpr hg1)
  have hge : M ∣ Int.gcd e00 (Int.gcd e01 (Int.gcd e10 e11)) :=
    Int.dvd_gcd (dvd_mul_right _ _) (Int.natCast_dvd_natCast.mpr hg2)
  exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp hle) hge

theorem card_G : Fintype.card (G M) = groupOrder M := by
  simp only [G, Fintype.card_prod, ZMod.card, groupOrder, cofactor, longModulus]
  ring

theorem card_G_gt_four : 4 < Fintype.card (G M) := by
  have h4 : (4 : ℕ) ≤ M := Fact.out
  rw [card_G]
  simp only [groupOrder, cofactor, pow_two]
  have h3 : (1 : ℕ) ≤ M - 3 := by omega
  have h16 : (16 : ℕ) ≤ M * M := Nat.mul_le_mul h4 h4
  have h2 : M * M * 1 ≤ M * M * (M - 3) := Nat.mul_le_mul_left _ h3
  omega

theorem sqrtCard_G : sqrtCard (G M) = (M : ℂ) * L2a.convolutionScalar M := by
  have h4 : (4 : ℕ) ≤ M := Fact.out
  have hc : ((groupOrder M : ℕ) : ℝ) = ((M : ℝ)) ^ 2 * ((M : ℝ) - 3) := by
    have h3 : (3 : ℕ) ≤ M := by omega
    simp only [groupOrder, cofactor, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h3]
    push_cast
    ring
  have hsq : Real.sqrt (((M : ℝ)) ^ 2 * ((M : ℝ) - 3)) = (M : ℝ) * Real.sqrt ((M : ℝ) - 3) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [sqrtCard, card_G, hc, hsq, Complex.ofReal_mul]
  rfl

/-- ε² = (M−1)ε − 1, transferred to ℂ. -/
private theorem epsilon_quad_complex :
    (L2a.epsilon M : ℂ) ^ 2 - ((M : ℂ) - 1) * (L2a.epsilon M : ℂ) + 1 = 0 := by
  exact_mod_cast (L2a.epsilon_quadratic (Fact.out : 4 ≤ M))

private theorem epsilon_ne_zero : (L2a.epsilon M : ℂ) ≠ 0 := by
  intro h
  have hq := epsilon_quad_complex (M := M)
  rw [h] at hq
  norm_num at hq

private theorem epsilon_cube :
    (L2a.epsilon M : ℂ) ^ 3 =
      (((M : ℂ) - 1) ^ 2 - 1) * (L2a.epsilon M : ℂ) - ((M : ℂ) - 1) := by
  have hq := epsilon_quad_complex (M := M)
  linear_combination ((L2a.epsilon M : ℂ) + ((M : ℂ) - 1)) * hq

/-- 1 − ε³ = M(1 − uε) with u = M − 2. -/
private theorem one_sub_epsilon_cube :
    (M : ℂ) * (1 - ((M : ℂ) - 2) * (L2a.epsilon M : ℂ)) = 1 - (L2a.epsilon M : ℂ) ^ 3 := by
  linear_combination epsilon_cube (M := M)

private theorem epsilon_cube_ne_one : (L2a.epsilon M : ℂ) ^ 3 ≠ 1 := by
  have hε1 : 1 < L2a.epsilon M := L2a.epsilon_gt_one (Fact.out : 4 ≤ M)
  have hε3 : 1 < (L2a.epsilon M : ℝ) ^ 3 := by
    have h2 : 1 < (L2a.epsilon M : ℝ) * (L2a.epsilon M : ℝ) := by nlinarith [hε1]
    nlinarith [h2]
  intro h
  have hc : (((L2a.epsilon M : ℝ) ^ 3 : ℝ) : ℂ) = (1 : ℂ) := by
    push_cast
    rw [h]
  have hr : (L2a.epsilon M : ℝ) ^ 3 = 1 := Complex.ofReal_inj.mp hc
  linarith

/-- (1 − uε)² = (M−3)·ε³. -/
private theorem one_sub_u_sq :
    (1 - ((M : ℂ) - 2) * (L2a.epsilon M : ℂ)) ^ 2 =
      ((M : ℂ) - 3) * (L2a.epsilon M : ℂ) ^ 3 := by
  linear_combination (((M : ℂ) - 2) ^ 2) * epsilon_quad_complex (M := M)
    - ((M : ℂ) - 3) * epsilon_cube (M := M)

private theorem longModulus_cast_c :
    (longModulus M : ℂ) = (M : ℂ) * ((M : ℂ) - 3) := by
  simp only [longModulus, cofactor, Nat.cast_mul]
  exact congrArg ((M : ℂ) * ·) (Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega))

private theorem longModulus_cast_q :
    (longModulus M : ℚ) = (M : ℚ) * ((M : ℚ) - 3) := by
  simp only [longModulus, cofactor, Nat.cast_mul]
  exact congrArg ((M : ℚ) * ·) (Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega))

theorem epsilon_sub_one_sq :
    ((L2a.epsilon M : ℂ) - 1) ^ 2 =
      (cofactor M : ℂ) * (L2a.epsilon M : ℂ) := by
  have hco : (cofactor M : ℂ) = (M : ℂ) - 3 :=
    Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)
  rw [hco]
  linear_combination epsilon_quad_complex (M := M)

/-- The scalar identity behind the rational-torus coordinates. -/
theorem inverse_epsilon_cube_sub_one :
    (((L2a.epsilon M : ℂ)⁻¹) ^ 3 - 1)⁻¹ =
      (1 - ((M : ℂ) - 2) * (L2a.epsilon M : ℂ)) / (longModulus M : ℂ) := by
  have h4 : (4 : ℕ) ≤ M := Fact.out
  have hM : ((M : ℂ)) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hm : ((M : ℂ) - 3) ≠ 0 := by
    have h3 : (3 : ℕ) ≤ M := by omega
    have hco : ((M : ℂ)) - 3 = ((M - 3 : ℕ) : ℂ) := (Nat.cast_sub h3).symm
    rw [hco]
    exact_mod_cast (by omega : (M - 3 : ℕ) ≠ 0)
  have h13 : (1 : ℂ) - (L2a.epsilon M : ℂ) ^ 3 ≠ 0 :=
    sub_ne_zero_of_ne (epsilon_cube_ne_one M).symm
  have hε0 : (L2a.epsilon M : ℂ) ≠ 0 := epsilon_ne_zero M
  have hE : (((L2a.epsilon M : ℂ)) ^ 3)⁻¹ - 1
      = (1 - (L2a.epsilon M : ℂ) ^ 3) / (L2a.epsilon M : ℂ) ^ 3 := by
    field_simp
  have h1 := one_sub_epsilon_cube M
  have h2 := one_sub_u_sq M
  rw [longModulus_cast_c, inv_pow, hE, inv_div,
    div_eq_div_iff h13 (mul_ne_zero hM hm)]
  linear_combination (1 - ((M : ℂ) - 2) * (L2a.epsilon M : ℂ)) * h1
    - ((M : ℂ)) * h2

/-- The rational vector space with basis (ε,1). -/
abbrev QuadraticCoordinates := ℚ × ℚ

def integerCoordinates : (ℤ × ℤ) →+ QuadraticCoordinates where
  toFun z := (z.1, z.2)
  map_zero' := rfl
  map_add' := fun a b => by ext <;> simp

def integerLattice : AddSubgroup QuadraticCoordinates := integerCoordinates.range

abbrev RationalTorus := QuadraticCoordinates ⧸ integerLattice

/-- Multiplication by ε on coefficient pairs, using ε²=(M−1)ε−1. -/
def epsilonOnRationals : QuadraticCoordinates →+ QuadraticCoordinates where
  toFun z := (((M : ℚ) - 1) * z.1 + z.2, -z.1)
  map_zero' := by simp
  map_add' := by
    intro a b
    ext <;> simp <;> ring
theorem epsilon_preserves_lattice :
    integerLattice ≤ integerLattice.comap (epsilonOnRationals M) := by
  intro z hz
  rw [AddSubgroup.mem_comap]
  have hz' : ∃ k : ℤ × ℤ, integerCoordinates k = z := AddMonoidHom.mem_range.mp hz
  obtain ⟨k, rfl⟩ := hz'
  show ∃ k' : ℤ × ℤ, integerCoordinates k' = epsilonOnRationals M (integerCoordinates k)
  refine ⟨((((M : ℤ) - 1) * k.1 + k.2, -k.1) : ℤ × ℤ), ?_⟩
  ext <;> simp [integerCoordinates, epsilonOnRationals] <;> push_cast <;> ring

def epsilonOnTorus (M : ℕ) [Fact (4 ≤ M)] : RationalTorus →+ RationalTorus :=
  QuotientAddGroup.map integerLattice integerLattice (epsilonOnRationals M)
    (epsilon_preserves_lattice M)

/-- This is (ε³−1)⁻¹ℤ[ε]/ℤ[ε], expressed without choosing a real embedding. -/
def fixedTorus : AddSubgroup RationalTorus :=
  ((epsilonOnTorus M).comp ((epsilonOnTorus M).comp (epsilonOnTorus M)) -
    AddMonoidHom.id RationalTorus).ker

/-- The explicit rational representative for a Smith-coordinate lift. -/
def pointLift (x y : ℤ) : QuadraticCoordinates :=
  ((-(cofactor M : ℚ) * x - ((M : ℚ) - 2) * y) / (longModulus M : ℚ),
    (y : ℚ) / (longModulus M : ℚ))

theorem pointLift_evaluate (x y : ℤ) :
    ((pointLift M x y).1 : ℂ) * (L2a.epsilon M : ℂ) +
        ((pointLift M x y).2 : ℂ) =
      ((x : ℂ) * (L2a.epsilon M : ℂ) + (y : ℂ) - ((M : ℂ) - 2) * x) /
        (((L2a.epsilon M : ℂ)⁻¹) ^ 3 - 1) := by
  have hn : ((longModulus M : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have e1 : ((pointLift M x y).1 : ℂ) =
      (-(cofactor M : ℂ) * (x : ℂ) - ((M : ℂ) - 2) * (y : ℂ)) / ((longModulus M : ℂ)) := by
    simp only [pointLift]
    push_cast
    ring
  have e2 : ((pointLift M x y).2 : ℂ) = ((y : ℂ)) / ((longModulus M : ℂ)) := by
    simp only [pointLift]
    push_cast
    ring
  have hco : ((cofactor M : ℂ)) = ((M : ℂ)) - 3 :=
    Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)
  rw [div_eq_mul_inv, inverse_epsilon_cube_sub_one, ← mul_div_assoc, eq_comm,
    div_eq_iff hn, e1, e2, hco]
  field_simp
  linear_combination ((x : ℂ) * (2 - (M : ℂ))) * epsilon_quad_complex (M := M)

/-! Coordinate helpers shared by the maps below. -/
private theorem coordinate_eq_of_dvd {a a' b b' : ℤ} (ha : ((M : ℤ)) ∣ a - a')
    (hb : ((longModulus M : ℤ)) ∣ b - b') :
    coordinate M a b = coordinate M a' b' := by
  have ha' : ((M : ℤ)) ∣ a' - a := by rw [← neg_sub]; exact Int.dvd_neg.mpr ha
  have hb' : ((longModulus M : ℤ)) ∣ b' - b := by rw [← neg_sub]; exact Int.dvd_neg.mpr hb
  simp only [coordinate, Prod.ext_iff]
  exact ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ha',
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hb'⟩

private theorem coordinate_val (g : G M) :
    coordinate M (g.1.val : ℤ) (g.2.val : ℤ) = g := by
  refine Prod.ext ?_ ?_
  · simp only [coordinate]
    push_cast
    exact ZMod.natCast_zmod_val g.1
  · simp only [coordinate]
    push_cast
    exact ZMod.natCast_zmod_val g.2

private theorem coordinate_add (a b c d : ℤ) :
    coordinate M a b + coordinate M c d = coordinate M (a + c) (b + d) := by
  simp only [coordinate, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  constructor <;> push_cast <;> ring

private theorem coordinate_sub (a b c d : ℤ) :
    coordinate M a b - coordinate M c d = coordinate M (a - c) (b - d) := by
  simp only [coordinate, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
  constructor <;> push_cast <;> ring

private theorem hcoℤ : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 :=
  Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)

private theorem hnmℤ : ((longModulus M : ℤ)) = ((M : ℤ)) * ((cofactor M : ℤ)) := by
  simp only [longModulus, cofactor, Nat.cast_mul]

private theorem coordinate_fst_val (a b : ℤ) :
    ((coordinate M a b).1.val : ℤ) = ((a : ℤ)) % ((M : ℤ)) := by
  simp only [coordinate]
  exact_mod_cast ZMod.val_intCast a

private theorem coordinate_snd_val (a b : ℤ) :
    ((coordinate M a b).2.val : ℤ) = ((b : ℤ)) % ((longModulus M : ℤ)) := by
  simp only [coordinate]
  exact_mod_cast ZMod.val_intCast b

/-- The head symbol of epsilonAut on any integer pair: only mods get reduced. -/
private theorem epsAut_on_coordinate (x y : ℤ) :
    coordinate M (((coordinate M x y).1.val : ℤ) + ((coordinate M x y).2.val : ℤ))
        (((cofactor M : ℤ)) * ((coordinate M x y).1.val : ℤ)
          + ((M : ℤ) - 2) * ((coordinate M x y).2.val : ℤ))
      = coordinate M (x + y) (((cofactor M : ℤ)) * x + ((M : ℤ) - 2) * y) := by
  rw [coordinate_fst_val, coordinate_snd_val]
  have hA := Int.mul_ediv_add_emod (x : ℤ) ((M : ℤ))
  have hB := Int.mul_ediv_add_emod (y : ℤ) ((longModulus M : ℤ))
  have h1 : (x : ℤ) % ((M : ℤ)) - x = -(((M : ℤ)) * (x / ((M : ℤ)))) := by
    linear_combination hA
  have h2 : (y : ℤ) % ((longModulus M : ℤ)) - y
      = -(((longModulus M : ℤ)) * (y / ((longModulus M : ℤ)))) := by
    linear_combination hB
  have h3 : ((M : ℤ)) * ((cofactor M : ℤ)) = ((longModulus M : ℤ)) := hnmℤ M
  refine coordinate_eq_of_dvd (M := M) ?_ ?_
  · refine ⟨-(x / ((M : ℤ))) - ((cofactor M : ℤ)) * (y / ((longModulus M : ℤ))), ?_⟩
    linear_combination h1 + h2 + (y / ((longModulus M : ℤ))) * h3
  · refine ⟨-(x / ((M : ℤ))) - ((M : ℤ) - 2) * (y / ((longModulus M : ℤ))), ?_⟩
    linear_combination ((cofactor M : ℤ)) * h1 + ((M : ℤ) - 2) * h2
      - (x / ((M : ℤ))) * h3

def torusPoint (M : ℕ) [Fact (4 ≤ M)] : G M →+ RationalTorus where
  toFun g := QuotientAddGroup.mk (pointLift M g.1.val g.2.val)
  map_zero' := by
    show QuotientAddGroup.mk (pointLift M (0 : ZMod M).val (0 : ZMod (longModulus M)).val) = 0
    simp only [pointLift, ZMod.val_zero]
    push_cast
    norm_num
    exact AddMonoidHom.mem_range.mpr ⟨(0, 0), rfl⟩
  map_add' := by
    intro g₁ g₂
    have hN0 : ((longModulus M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
    have hnℚ : ((longModulus M : ℚ)) = ((M : ℚ)) * (((M : ℚ)) - 3) := longModulus_cast_q M
    have hmℚ : ((cofactor M : ℚ)) = ((M : ℚ)) - 3 :=
      Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)
    have e1 : (g₁ + g₂).1.val = (g₁.1.val + g₂.1.val) % M := by
      rw [Prod.fst_add]
      exact ZMod.val_add _ _
    have e2 : (g₁ + g₂).2.val = (g₁.2.val + g₂.2.val) % (longModulus M) := by
      rw [Prod.snd_add]
      exact ZMod.val_add _ _
    have hAℤ : ((M : ℤ)) * (((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ)))
        + ((g₁ + g₂).1.val : ℤ) = ((g₁.1.val : ℤ)) + ((g₂.1.val : ℤ)) := by
      have e1' : ((g₁ + g₂).1.val : ℤ)
          = (((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) % ((M : ℤ))) := by
        exact_mod_cast e1
      have hz := Int.mul_ediv_add_emod (((g₁.1.val : ℤ) + (g₂.1.val : ℤ))) ((M : ℤ))
      rw [← e1'] at hz
      linarith
    have hBℤ : ((longModulus M : ℤ)) * (((g₁.2.val : ℤ) + (g₂.2.val : ℤ))
        / ((longModulus M : ℤ))) + ((g₁ + g₂).2.val : ℤ)
        = ((g₁.2.val : ℤ)) + ((g₂.2.val : ℤ)) := by
      have e2' : ((g₁ + g₂).2.val : ℤ)
          = (((g₁.2.val : ℤ) + (g₂.2.val : ℤ)) % ((longModulus M : ℤ))) := by
        exact_mod_cast e2
      have hz := Int.mul_ediv_add_emod (((g₁.2.val : ℤ) + (g₂.2.val : ℤ)))
        ((longModulus M : ℤ))
      rw [← e2'] at hz
      linarith
    have hAq : (((M : ℕ)) : ℚ) * ((((((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ))) : ℤ)) : ℚ)
        + ((g₁ + g₂).1.val : ℚ)
        = ((g₁.1.val : ℕ) : ℚ) + ((g₂.1.val : ℕ) : ℚ) := by
      have hc : (((M : ℕ)) : ℚ) * ((((((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ))) : ℤ)) : ℚ)
          = ((((((M : ℤ)) * (((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ))))) : ℤ) : ℚ) := by
        push_cast
        ring
      rw [hc]
      exact_mod_cast hAℤ
    have hBq : ((longModulus M : ℕ) : ℚ)
        * ((((((g₁.2.val : ℤ) + (g₂.2.val : ℤ)) / ((longModulus M : ℤ))) : ℤ)) : ℚ)
        + ((g₁ + g₂).2.val : ℚ)
        = ((g₁.2.val : ℕ) : ℚ) + ((g₂.2.val : ℕ) : ℚ) := by
      have hc : ((longModulus M : ℕ) : ℚ)
          * ((((((g₁.2.val : ℤ) + (g₂.2.val : ℤ)) / ((longModulus M : ℤ))) : ℤ)) : ℚ)
          = ((((((longModulus M : ℤ)) * (((g₁.2.val : ℤ) + (g₂.2.val : ℤ))
            / ((longModulus M : ℤ))))) : ℤ) : ℚ) := by
        push_cast
        ring
      rw [hc]
      exact_mod_cast hBℤ
    have hpl1 : ∀ x y : ℤ, ((longModulus M : ℚ)) * (pointLift M x y).1
        = -((cofactor M : ℚ)) * (x : ℚ) - ((M : ℚ) - 2) * (y : ℚ) := by
      intro x y
      simp only [pointLift]
      rw [mul_comm, div_mul_cancel₀ _ hN0]
    have hpl2 : ∀ x y : ℤ, ((longModulus M : ℚ)) * (pointLift M x y).2 = ((y : ℚ)) := by
      intro x y
      simp only [pointLift]
      rw [mul_comm, div_mul_cancel₀ _ hN0]
    have c1 : ((longModulus M : ℚ)) * ((pointLift M (g₁ + g₂).1.val (g₁ + g₂).2.val).1
          - ((pointLift M g₁.1.val g₁.2.val).1 + (pointLift M g₂.1.val g₂.2.val).1))
        = ((longModulus M : ℚ)) * (((((((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ))) : ℤ)) : ℚ)
          + (((M : ℚ)) - 2) * ((((((g₁.2.val : ℤ) + (g₂.2.val : ℤ))
            / ((longModulus M : ℤ))) : ℤ)) : ℚ)) := by
      rw [mul_sub, mul_add, hpl1, hpl1, hpl1]
      linear_combination -((cofactor M : ℚ)) * hAq - (((M : ℚ) - 2)) * hBq
        + (((M : ℚ)) * ((((((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ))) : ℤ)) : ℚ)) * hmℚ
        - ((((((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ))) : ℤ)) : ℚ) * hnℚ
    have c2 : ((longModulus M : ℚ)) * ((pointLift M (g₁ + g₂).1.val (g₁ + g₂).2.val).2
          - ((pointLift M g₁.1.val g₁.2.val).2 + (pointLift M g₂.1.val g₂.2.val).2))
        = -((longModulus M : ℚ)) * ((((((g₁.2.val : ℤ) + (g₂.2.val : ℤ))
          / ((longModulus M : ℤ))) : ℤ) : ℚ)) := by
      rw [mul_sub, mul_add, hpl2, hpl2, hpl2]
      linear_combination hBq
    show QuotientAddGroup.mk (pointLift M (g₁ + g₂).1.val (g₁ + g₂).2.val)
        = QuotientAddGroup.mk (pointLift M g₁.1.val g₁.2.val)
          + QuotientAddGroup.mk (pointLift M g₂.1.val g₂.2.val)
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem,
      integerLattice, AddMonoidHom.mem_range]
    refine ⟨(((((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ)))
        + ((M : ℤ) - 2) * (((g₁.2.val : ℤ) + (g₂.2.val : ℤ))
          / ((longModulus M : ℤ)))),
      -((((g₁.2.val : ℤ) + (g₂.2.val : ℤ)) / ((longModulus M : ℤ))))), ?_⟩
    refine Prod.ext ?_ ?_
    · apply mul_right_cancel₀ hN0
      show ((((((g₁.1.val : ℤ) + (g₂.1.val : ℤ)) / ((M : ℤ)))
        + ((M : ℤ) - 2) * (((g₁.2.val : ℤ) + (g₂.2.val : ℤ))
          / ((longModulus M : ℤ)))) : ℤ) : ℚ) * ((longModulus M : ℚ))
        = ((pointLift M (g₁ + g₂).1.val (g₁ + g₂).2.val).1
          - ((pointLift M g₁.1.val g₁.2.val).1 + (pointLift M g₂.1.val g₂.2.val).1))
          * ((longModulus M : ℚ))
      push_cast at c1 ⊢
      linear_combination -c1
    · apply mul_right_cancel₀ hN0
      show (((-((((g₁.2.val : ℤ) + (g₂.2.val : ℤ))
        / ((longModulus M : ℤ)))) : ℤ) : ℚ)) * ((longModulus M : ℚ))
        = ((pointLift M (g₁ + g₂).1.val (g₁ + g₂).2.val).2
          - ((pointLift M g₁.1.val g₁.2.val).2 + (pointLift M g₂.1.val g₂.2.val).2))
          * ((longModulus M : ℚ))
      push_cast at c2 ⊢
      linear_combination -c2

private theorem pointLift_mul_one (M : ℕ) [Fact (4 ≤ M)] (x y : ℤ) :
    ((longModulus M : ℚ)) * (pointLift M x y).1
    = -((cofactor M : ℚ)) * (x : ℚ) - ((M : ℚ) - 2) * (y : ℚ) := by
  have hN : ((longModulus M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  simp only [pointLift]
  rw [mul_comm, div_mul_cancel₀ _ hN]

private theorem pointLift_mul_two (M : ℕ) [Fact (4 ≤ M)] (x y : ℤ) :
    ((longModulus M : ℚ)) * (pointLift M x y).2 = ((y : ℚ)) := by
  have hN : ((longModulus M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  simp only [pointLift]
  rw [mul_comm, div_mul_cancel₀ _ hN]

theorem torusPoint_injective : Function.Injective (torusPoint M) := by
  have hm0 : ((cofactor M : ℤ)) ≠ 0 := by exact_mod_cast (NeZero.ne _)
  have hnmℤ : ((longModulus M : ℤ)) = ((M : ℤ)) * ((cofactor M : ℤ)) := by
    simp only [longModulus, cofactor, Nat.cast_mul]
  intro g₁ g₂ hq
  have hq : QuotientAddGroup.mk (pointLift M g₁.1.val g₁.2.val)
      = QuotientAddGroup.mk (pointLift M g₂.1.val g₂.2.val) := hq
  rw [QuotientAddGroup.eq_iff_sub_mem, integerLattice, AddMonoidHom.mem_range] at hq
  obtain ⟨k, hk⟩ := hq
  have e1 := congrArg Prod.fst hk
  have e2 := congrArg Prod.snd hk
  simp only [integerCoordinates] at e1 e2
  have hY₁ : ((g₁.2.val : ℤ)) < ((longModulus M : ℤ)) := by
    exact_mod_cast ZMod.val_lt g₁.2
  have hY₂ : ((g₂.2.val : ℤ)) < ((longModulus M : ℤ)) := by
    exact_mod_cast ZMod.val_lt g₂.2
  have hNq : ((longModulus M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have heq2 : ((longModulus M : ℤ)) * k.2 = ((g₁.2.val : ℤ) - (g₂.2.val : ℤ)) := by
    have e2' : (((k.2 : ℤ)) : ℚ)
        = (pointLift M g₁.1.val g₁.2.val).2 - (pointLift M g₂.1.val g₂.2.val).2 := by
      have hke := e2
      rw [Prod.snd_sub] at hke
      exact hke
    have h2 := pointLift_mul_two M g₁.1.val g₁.2.val
    have h2' := pointLift_mul_two M g₂.1.val g₂.2.val
    have hq2 : ((longModulus M : ℚ)) * (((k.2 : ℤ)) : ℚ)
        = (((g₁.2.val : ℕ)) : ℚ) - (((g₂.2.val : ℕ)) : ℚ) := by
      rw [e2', mul_sub, h2, h2']
      push_cast
      rfl
    have hmℚ : ((cofactor M : ℚ)) = ((M : ℚ)) - 3 :=
      Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)
    have hc : (((((longModulus M : ℤ)) * k.2 : ℤ)) : ℚ)
        = (((((g₁.2.val : ℤ) - (g₂.2.val : ℤ)) : ℤ)) : ℚ) := by
      rw [longModulus_cast_q M] at hq2
      push_cast at hq2 ⊢
      rw [hmℚ]
      linarith
    exact_mod_cast hc
  have hYeq : ((g₁.2.val : ℤ)) - ((g₂.2.val : ℤ)) = 0 := by
    have hdvd : ((longModulus M : ℤ)) ∣ ((g₁.2.val : ℤ) - (g₂.2.val : ℤ)) :=
      ⟨k.2, heq2.symm⟩
    have habs : ((g₁.2.val : ℤ) - (g₂.2.val : ℤ)).natAbs < ((longModulus M : ℤ)).natAbs := by
      rw [Int.natAbs_natCast]
      rcases Int.natAbs_eq ((g₁.2.val : ℤ) - (g₂.2.val : ℤ)) with h | h <;>
        rw [h] <;> omega
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd habs
  have heq1 : ((longModulus M : ℤ)) * k.1
      = -((cofactor M : ℤ)) * ((g₁.1.val : ℤ) - (g₂.1.val : ℤ))
        - (((M : ℤ)) - 2) * ((g₁.2.val : ℤ) - (g₂.2.val : ℤ)) := by
    have e1' : (((k.1 : ℤ)) : ℚ)
        = (pointLift M g₁.1.val g₁.2.val).1 - (pointLift M g₂.1.val g₂.2.val).1 := by
      have hke := e1
      rw [Prod.fst_sub] at hke
      exact hke
    have h1 := pointLift_mul_one M g₁.1.val g₁.2.val
    have h1' := pointLift_mul_one M g₂.1.val g₂.2.val
    have hq1 : ((longModulus M : ℚ)) * (((k.1 : ℤ)) : ℚ)
        = -((cofactor M : ℚ)) * ((((((g₁.1.val : ℤ)) - ((g₂.1.val : ℤ))) : ℤ)) : ℚ)
          - (((M : ℚ)) - 2) * ((((((g₁.2.val : ℤ)) - ((g₂.2.val : ℤ))) : ℤ)) : ℚ) := by
      rw [e1', mul_sub, h1, h1']
      push_cast
      ring
    have hc : ((((((longModulus M : ℤ)) * k.1) : ℤ) : ℚ)) = ((((-((cofactor M : ℤ)) * (((g₁.1.val : ℤ)) - ((g₂.1.val : ℤ))) - (((M : ℤ)) - 2) * (((g₁.2.val : ℤ)) - ((g₂.2.val : ℤ))))) : ℤ) : ℚ) := by
      have hX : ((((((longModulus M : ℤ)) * k.1) : ℤ) : ℚ)) = (((longModulus M : ℚ)) * (((k.1 : ℤ)) : ℚ)) := by
        push_cast
        ring
      have hY : ((((-((cofactor M : ℤ)) * (((g₁.1.val : ℤ)) - ((g₂.1.val : ℤ))) - (((M : ℤ)) - 2) * (((g₁.2.val : ℤ)) - ((g₂.2.val : ℤ))))) : ℤ) : ℚ) = -((cofactor M : ℚ)) * ((((((((g₁.1.val : ℤ)) - ((g₂.1.val : ℤ)))) : ℤ)) : ℚ)) - (((M : ℚ)) - 2) * ((((((((g₁.2.val : ℤ)) - ((g₂.2.val : ℤ)))) : ℤ)) : ℚ)) := by
        push_cast
        ring
      rw [hX, hY]
      exact hq1
    exact Int.cast_inj.mp hc
  have hX₁ : ((g₁.1.val : ℤ)) < ((M : ℤ)) := by exact_mod_cast ZMod.val_lt g₁.1
  have hX₂ : ((g₂.1.val : ℤ)) < ((M : ℤ)) := by exact_mod_cast ZMod.val_lt g₂.1
  have hc : ((M : ℤ)) * k.1 = -((g₁.1.val : ℤ) - (g₂.1.val : ℤ)) := by
    refine mul_right_cancel₀ hm0 ?_
    linear_combination heq1 - k.1 * hnmℤ - (((M : ℤ)) - 2) * hYeq
  have hdvdX : ((M : ℤ)) ∣ ((g₁.1.val : ℤ) - (g₂.1.val : ℤ)) :=
    ⟨-k.1, by linear_combination hc⟩
  have hXeq : ((g₁.1.val : ℤ)) - ((g₂.1.val : ℤ)) = 0 := by
    have habs : ((g₁.1.val : ℤ) - (g₂.1.val : ℤ)).natAbs < ((M : ℤ)).natAbs := by
      rw [Int.natAbs_natCast]
      rcases Int.natAbs_eq ((g₁.1.val : ℤ) - (g₂.1.val : ℤ)) with h | h <;>
        rw [h] <;> omega
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvdX habs
    omega
  refine Prod.ext ?_ ?_ <;> exact ZMod.val_injective _ (by omega)

private theorem pointLift_mod (x y : ℤ) :
    pointLift M (x % ((M : ℤ))) (y % ((longModulus M : ℤ)))
      = pointLift M x y + (((x / ((M : ℤ)) + ((M : ℤ) - 2) * (y / ((longModulus M : ℤ))) : ℤ) : ℚ),
        ((-(y / ((longModulus M : ℤ))) : ℤ) : ℚ)) := by
  have e1 : ((M : ℤ)) * (x / ((M : ℤ))) + x % ((M : ℤ)) = x :=
    Int.mul_ediv_add_emod x ((M : ℤ))
  have e2 : ((longModulus M : ℤ)) * (y / ((longModulus M : ℤ))) + y % ((longModulus M : ℤ)) = y :=
    Int.mul_ediv_add_emod y ((longModulus M : ℤ))
  have e1q : ((M : ℚ)) * ((x / ((M : ℤ)) : ℤ) : ℚ) + ((x % ((M : ℤ)) : ℤ) : ℚ) = ((x : ℤ) : ℚ) := by
    exact_mod_cast e1
  have e2q : ((longModulus M : ℚ)) * ((y / ((longModulus M : ℤ)) : ℤ) : ℚ)
      + ((y % ((longModulus M : ℤ)) : ℤ) : ℚ) = ((y : ℤ) : ℚ) := by
    exact_mod_cast e2
  have hcoQ : ((cofactor M : ℚ)) = ((M : ℚ)) - 3 := by exact_mod_cast hcoℤ M
  have hnmQ : ((longModulus M : ℚ)) = ((M : ℚ)) * (((M : ℚ)) - 3) := longModulus_cast_q M
  have hn : ((longModulus M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  refine Prod.ext ?_ ?_
  · show (pointLift M (x % ((M : ℤ))) (y % ((longModulus M : ℤ)))).1 = ((pointLift M x y).1 + ((x / ((M : ℤ)) + ((M : ℤ) - 2) * (y / ((longModulus M : ℤ))) : ℤ) : ℚ))
    simp only [pointLift]
    apply mul_left_cancel₀ hn
    field_simp
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    linear_combination -((cofactor M : ℚ)) * e1q - ((M : ℚ) - 2) * e2q
      + ((x / ((M : ℤ)) : ℤ) : ℚ) * ((M : ℚ)) * hcoQ
      - ((x / ((M : ℤ)) : ℤ) : ℚ) * hnmQ
  · show (pointLift M (x % ((M : ℤ))) (y % ((longModulus M : ℤ)))).2 = ((pointLift M x y).2 + ((-(y / ((longModulus M : ℤ))) : ℤ) : ℚ))
    simp only [pointLift]
    apply mul_left_cancel₀ hn
    field_simp
    simp only [Int.cast_neg]
    linear_combination e2q

private theorem torusPoint_coordinate (x y : ℤ) :
    torusPoint M (coordinate M x y) = QuotientAddGroup.mk (pointLift M x y) := by
  change QuotientAddGroup.mk
      (pointLift M ((coordinate M x y).1.val : ℤ) ((coordinate M x y).2.val : ℤ)) = _
  rw [coordinate_fst_val, coordinate_snd_val, QuotientAddGroup.eq_iff_sub_mem, pointLift_mod]
  refine AddMonoidHom.mem_range.mpr
    ⟨(x / (M : ℤ) + ((M : ℤ) - 2) * (y / (longModulus M : ℤ)),
      -(y / (longModulus M : ℤ))), ?_⟩
  ext <;> simp [integerCoordinates]

private theorem fixedTorus_mk_iff (z : QuadraticCoordinates) :
    QuotientAddGroup.mk z ∈ fixedTorus M ↔
      epsilonOnRationals M (epsilonOnRationals M (epsilonOnRationals M z)) - z ∈
        integerLattice := by
  change epsilonOnTorus M (epsilonOnTorus M (epsilonOnTorus M
    (QuotientAddGroup.mk z))) - QuotientAddGroup.mk z = 0 ↔ _
  simp only [epsilonOnTorus, QuotientAddGroup.map_mk]
  rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]

private theorem epsilon_cube_defect (z : QuadraticCoordinates) :
    epsilonOnRationals M (epsilonOnRationals M (epsilonOnRationals M z)) - z =
      ((M : ℚ) * ((longModulus M : ℚ) + 1) * z.1 +
          (M : ℚ) * ((M : ℚ) - 2) * z.2,
        -(M : ℚ) * ((M : ℚ) - 2) * z.1 - (M : ℚ) * z.2) := by
  rw [longModulus_cast_q]
  have he (w : QuadraticCoordinates) : epsilonOnRationals M w =
      (((M : ℚ) - 1) * w.1 + w.2, -w.1) := rfl
  ext <;> simp only [he, Prod.fst_sub, Prod.snd_sub] <;> ring

private theorem pointLift_fixed (x y : ℤ) :
    QuotientAddGroup.mk (pointLift M x y) ∈ fixedTorus M := by
  have hn : (longModulus M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hm : (cofactor M : ℚ) = (M : ℚ) - 3 :=
    Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)
  have hp1 := pointLift_mul_one M x y
  have hp2 := pointLift_mul_two M x y
  rw [fixedTorus_mk_iff, epsilon_cube_defect, integerLattice, AddMonoidHom.mem_range]
  refine ⟨(-((longModulus M : ℤ) + 1) * x - (M : ℤ) * ((M : ℤ) - 2) * y,
    ((M : ℤ) - 2) * x + ((M : ℤ) - 1) * y), ?_⟩
  apply Prod.ext
  · change (((-((longModulus M : ℤ) + 1) * x - (M : ℤ) * ((M : ℤ) - 2) * y) : ℤ) : ℚ) = _
    apply mul_left_cancel₀ hn
    push_cast at hp1 hp2 ⊢
    simp only [hm, longModulus_cast_q M] at hp1 hp2 ⊢
    linear_combination -((M : ℚ) * ((M : ℚ) * ((M : ℚ) - 3) + 1)) * hp1 -
      ((M : ℚ) * ((M : ℚ) - 2)) * hp2
  · change (((((M : ℤ) - 2) * x + ((M : ℤ) - 1) * y) : ℤ) : ℚ) = _
    apply mul_left_cancel₀ hn
    push_cast at hp1 hp2 ⊢
    simp only [hm, longModulus_cast_q M] at hp1 hp2 ⊢
    linear_combination ((M : ℚ) * ((M : ℚ) - 2)) * hp1 + (M : ℚ) * hp2

theorem torusPoint_range : (torusPoint M).range = fixedTorus M := by
  have hn : (longModulus M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hm : (cofactor M : ℚ) = (M : ℚ) - 3 :=
    Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)
  apply le_antisymm
  · rintro z ⟨g, rfl⟩
    exact pointLift_fixed M (g.1.val : ℤ) (g.2.val : ℤ)
  · intro z hz
    revert hz
    refine QuotientAddGroup.induction_on z ?_
    intro a ha
    rw [fixedTorus_mk_iff, epsilon_cube_defect, integerLattice,
      AddMonoidHom.mem_range] at ha
    obtain ⟨k, hk⟩ := ha
    have he1 : (k.1 : ℚ) = (M : ℚ) * ((longModulus M : ℚ) + 1) * a.1 +
        (M : ℚ) * ((M : ℚ) - 2) * a.2 := congrArg Prod.fst hk
    have he2 : (k.2 : ℚ) = -(M : ℚ) * ((M : ℚ) - 2) * a.1 -
        (M : ℚ) * a.2 := congrArg Prod.snd hk
    let x : ℤ := ((M : ℤ) - 1) * k.1 + (M : ℤ) * ((M : ℤ) - 2) * k.2
    let y : ℤ := -((M : ℤ) - 2) * k.1 - ((longModulus M : ℤ) + 1) * k.2
    have hp : pointLift M x y = a := by
      apply Prod.ext
      · apply mul_left_cancel₀ hn
        rw [pointLift_mul_one]
        dsimp only [x, y]
        push_cast at he1 he2 ⊢
        simp only [hm, longModulus_cast_q M] at he1 he2 ⊢
        linear_combination he1 + ((M : ℚ) - 2) * he2
      · apply mul_left_cancel₀ hn
        rw [pointLift_mul_two]
        dsimp only [y]
        push_cast at he1 he2 ⊢
        simp only [hm, longModulus_cast_q M] at he1 he2 ⊢
        linear_combination -((M : ℚ) - 2) * he1 -
          ((M : ℚ) * ((M : ℚ) - 3) + 1) * he2
    exact AddMonoidHom.mem_range.mpr ⟨coordinate M x y, by rw [torusPoint_coordinate, hp]⟩


private theorem epsAutInv_on_coordinate (x y : ℤ) :
    coordinate M (((M : ℤ) - 2) * ((coordinate M x y).1.val : ℤ)
        - ((coordinate M x y).2.val : ℤ))
        (-((cofactor M : ℤ)) * ((coordinate M x y).1.val : ℤ)
          + ((coordinate M x y).2.val : ℤ))
      = coordinate M (((M : ℤ) - 2) * x - y) (-((cofactor M : ℤ)) * x + y) := by
  have h1 := Int.mul_ediv_add_emod (x : ℤ) ((M : ℤ))
  have h2 := Int.mul_ediv_add_emod (y : ℤ) ((longModulus M : ℤ))
  have hnm : ((M : ℤ)) * ((cofactor M : ℤ)) = ((longModulus M : ℤ)) := hnmℤ M
  have hf := coordinate_fst_val M x y
  have hs := coordinate_snd_val M x y
  refine coordinate_eq_of_dvd (M := M) ⟨-((M : ℤ) - 2) * (x / ((M : ℤ)))
      + ((cofactor M : ℤ)) * (y / ((longModulus M : ℤ))), ?_⟩
    ⟨(x / ((M : ℤ))) - (y / ((longModulus M : ℤ))), ?_⟩
  · rw [hf, hs]
    linear_combination ((M : ℤ) - 2) * h1 - h2
      - (y / ((longModulus M : ℤ))) * hnm
  · rw [hf, hs]
    linear_combination (x / ((M : ℤ))) * hnm - ((cofactor M : ℤ)) * h1 + h2

/-- Explicit multiplication by ε; its inverse is (u x−y, −m x+y). -/
def epsilonAut (M : ℕ) [Fact (4 ≤ M)] : G M ≃+ G M where
  toFun g := coordinate M ((g.1.val : ℤ) + g.2.val)
    ((cofactor M : ℤ) * g.1.val + ((M : ℤ) - 2) * g.2.val)
  invFun g := coordinate M (((M : ℤ) - 2) * g.1.val - g.2.val)
    (-(cofactor M : ℤ) * g.1.val + g.2.val)
  left_inv := by
    intro g
    rw [← coordinate_val M g]
    have hA : (fun g' : G M => coordinate M ((g'.1.val : ℤ) + g'.2.val)
        (((cofactor M : ℤ)) * g'.1.val + ((M : ℤ) - 2) * g'.2.val))
        (coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ)))
      = coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))) :=
      epsAut_on_coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))
    rw [hA]
    have hB : (fun g' : G M => coordinate M (((M : ℤ) - 2) * g'.1.val - g'.2.val)
        (-((cofactor M : ℤ)) * g'.1.val + g'.2.val))
        (coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))))
      = coordinate M (((M : ℤ) - 2) * (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          - (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))))
        (-((cofactor M : ℤ)) * (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          + (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ)))) :=
      epsAutInv_on_coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
        (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ)))
    rw [hB]
    have hco : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 := hcoℤ M
    rw [hco]
    exact coordinate_eq_of_dvd (M := M) ⟨0, by ring⟩ ⟨0, by ring⟩
  right_inv := by
    intro g
    rw [← coordinate_val M g]
    have hA : (fun g' : G M => coordinate M (((M : ℤ) - 2) * g'.1.val - g'.2.val)
        (-((cofactor M : ℤ)) * g'.1.val + g'.2.val))
        (coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ)))
      = coordinate M (((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
        (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))) :=
      epsAutInv_on_coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))
    rw [hA]
    have hB : (fun g' : G M => coordinate M ((g'.1.val : ℤ) + g'.2.val)
        (((cofactor M : ℤ)) * g'.1.val + ((M : ℤ) - 2) * g'.2.val))
        (coordinate M (((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
          (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))))
      = coordinate M ((((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
          + (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))))
        (((cofactor M : ℤ)) * (((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
          + ((M : ℤ) - 2) * (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))) :=
      epsAut_on_coordinate M (((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
        (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))
    rw [hB]
    have hco : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 := hcoℤ M
    rw [hco]
    exact coordinate_eq_of_dvd (M := M) ⟨0, by ring⟩ ⟨0, by ring⟩
  map_add' := by
    intro g₁ g₂
    rw [show g₁ = coordinate M ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ)) from (coordinate_val M g₁).symm,
      show g₂ = coordinate M ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ)) from (coordinate_val M g₂).symm,
      show coordinate M ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))
          + coordinate M ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))
        = coordinate M (((g₁.1.val : ℤ)) + (g₂.1.val : ℤ))
          (((g₁.2.val : ℤ)) + (g₂.2.val : ℤ))
        from coordinate_add M ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))
          ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))]
    rw [epsAut_on_coordinate M (((g₁.1.val : ℤ)) + (g₂.1.val : ℤ))
        (((g₁.2.val : ℤ)) + (g₂.2.val : ℤ)),
      epsAut_on_coordinate M ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ)),
      epsAut_on_coordinate M ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ)), coordinate_add]
    exact coordinate_eq_of_dvd (M := M) ⟨0, by ring⟩ ⟨0, by ring⟩

private theorem epsilonAut_coordinate (x y : ℤ) :
    epsilonAut M (coordinate M x y)
      = coordinate M (x + y) (((cofactor M : ℤ)) * x + ((M : ℤ) - 2) * y) :=
  epsAut_on_coordinate M x y

theorem epsilonAut_cube (g : G M) :
    epsilonAut M (epsilonAut M (epsilonAut M g)) = g := by
  rw [← coordinate_val M g, epsilonAut_coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ)),
    epsilonAut_coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
      (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))),
    epsilonAut_coordinate M ((((g.1.val : ℤ)) + ((g.2.val : ℤ)))
        + (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))))
      (((cofactor M : ℤ)) * (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
        + ((M : ℤ) - 2) * (((cofactor M : ℤ)) * ((g.1.val : ℤ))
          + ((M : ℤ) - 2) * ((g.2.val : ℤ))))]
  have hco : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 := hcoℤ M
  have hco2 : ((longModulus M : ℤ)) = ((M : ℤ)) * (((M : ℤ)) - 3) := by
    rw [hnmℤ M, hcoℤ M]
  rw [hco]
  exact coordinate_eq_of_dvd (M := M)
    ⟨((M : ℤ) - 3) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ)), by ring⟩
    ⟨((M : ℤ) - 2) * ((g.1.val : ℤ)) + ((M : ℤ) - 1) * ((g.2.val : ℤ)), by
      rw [hco2]
      ring⟩

private theorem pointLift_epsilon (x y : ℤ) :
    pointLift M (x + y) (((cofactor M : ℤ)) * x + ((M : ℤ) - 2) * y)
      = epsilonOnRationals M (pointLift M x y) := by
  have hn : ((longModulus M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hcoQ : ((cofactor M : ℚ)) = ((M : ℚ)) - 3 := by exact_mod_cast hcoℤ M
  refine Prod.ext ?_ ?_
  · show (-((cofactor M : ℚ)) * ((x + y : ℤ) : ℚ) - ((M : ℚ) - 2) * (((cofactor M : ℤ)) * x + ((M : ℤ) - 2) * y : ℤ)) / ((longModulus M : ℚ))
      = (((M : ℚ) - 1) * ((-((cofactor M : ℚ)) * (x : ℤ) - ((M : ℚ) - 2) * (y : ℤ)) / ((longModulus M : ℚ)))) + ((y : ℤ) / ((longModulus M : ℚ)))
    field_simp
    push_cast
    linear_combination -((y : ℚ)) * hcoQ
  · show (((((cofactor M : ℤ)) * x + ((M : ℤ) - 2) * y : ℤ)) : ℚ)
        / ((longModulus M : ℚ))
      = -(((-((cofactor M : ℚ)) * ((x : ℤ)) - ((M : ℚ) - 2) * ((y : ℤ))))
        / ((longModulus M : ℚ)))
    field_simp
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    ring

theorem epsilonAut_torusPoint (g : G M) :
    torusPoint M (epsilonAut M g) = epsilonOnTorus M (torusPoint M g) := by
  rw [← coordinate_val M g, epsilonAut_coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))]
  show (QuotientAddGroup.mk (pointLift M ((coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ))) (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ)))).1.val) ((coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ))) (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ)))).2.val))) = (epsilonOnTorus M) (QuotientAddGroup.mk (pointLift M ((coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))).1.val) ((coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))).2.val)))
  rw [coordinate_fst_val M (((g.1.val : ℤ)) + ((g.2.val : ℤ))) (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))), coordinate_snd_val M (((g.1.val : ℤ)) + ((g.2.val : ℤ))) (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))),
    show (epsilonOnTorus M) (QuotientAddGroup.mk (pointLift M ((coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))).1.val) ((coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))).2.val)))
      = QuotientAddGroup.mk (epsilonOnRationals M (pointLift M ((coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))).1.val) ((coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))).2.val))) from rfl,
    QuotientAddGroup.eq_iff_sub_mem]
  have hP := pointLift_epsilon M ((g.1.val : ℤ)) ((g.2.val : ℤ))
  have hM1 := pointLift_mod M (((g.1.val : ℤ)) + ((g.2.val : ℤ))) (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ)))
  have hM2 := pointLift_mod M ((g.1.val : ℤ)) ((g.2.val : ℤ))
  have hE := (epsilonOnRationals M).map_add (pointLift M ((g.1.val : ℤ)) ((g.2.val : ℤ))) (((((((g.1.val : ℤ)) / ((M : ℤ))) + ((M : ℤ) - 2) * (((g.2.val : ℤ)) / ((longModulus M : ℤ))) : ℤ) : ℚ)), (((-(((g.2.val : ℤ)) / ((longModulus M : ℤ))) : ℤ) : ℚ)))
  refine AddMonoidHom.mem_range.mpr ⟨(((((g.1.val : ℤ)) + ((g.2.val : ℤ))) / ((M : ℤ))) + ((M : ℤ) - 2) * ((((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))) / ((longModulus M : ℤ))) - (((M : ℤ) - 1) * ((((g.1.val : ℤ)) / ((M : ℤ))) + ((M : ℤ) - 2) * (((g.2.val : ℤ)) / ((longModulus M : ℤ)))) + (-(((g.2.val : ℤ)) / ((longModulus M : ℤ))))), -((((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))) / ((longModulus M : ℤ))) - (-((((g.1.val : ℤ)) / ((M : ℤ))) + ((M : ℤ) - 2) * (((g.2.val : ℤ)) / ((longModulus M : ℤ)))))), ?_⟩
  rw [coordinate_fst_val M ((g.1.val : ℤ)) ((g.2.val : ℤ)),
    coordinate_snd_val M ((g.1.val : ℤ)) ((g.2.val : ℤ)), hM2, hE, hM1, hP]
  ext <;> simp [integerCoordinates, epsilonOnRationals] <;> push_cast <;> ring

/-- ι(i,j) represents (i ε+j)/M, in precisely L2a's coordinate order. -/
def iota (M : ℕ) [Fact (4 ≤ M)] : L2a.Index M →+ G M where
  toFun h := coordinate M (2 * (h.2.val : ℤ) - h.1.val)
    ((cofactor M : ℤ) * h.2.val)
  map_zero' := by
    simp [coordinate]
  map_add' := by
    intro a b
    have h4 : (4 : ℕ) ≤ M := Fact.out
    haveI : NeZero M := NeZero.of_pos (by omega)
    have hm1 : ((M : ℤ)) * (((a.1.val : ℤ) + b.1.val) / ((M : ℤ)))
        + (((a.1.val : ℤ) + b.1.val) % ((M : ℤ))) = (a.1.val : ℤ) + b.1.val :=
      Int.mul_ediv_add_emod _ _
    have hm2 : ((M : ℤ)) * (((a.2.val : ℤ) + b.2.val) / ((M : ℤ)))
        + (((a.2.val : ℤ) + b.2.val) % ((M : ℤ))) = (a.2.val : ℤ) + b.2.val :=
      Int.mul_ediv_add_emod _ _
    have hL : coordinate M (2 * ((a + b).2.val : ℤ) - (a + b).1.val)
        (((cofactor M : ℤ)) * (a + b).2.val) = coordinate M
        (2 * (((a.2.val : ℤ) + b.2.val) % ((M : ℤ)))
          - (((a.1.val : ℤ) + b.1.val) % ((M : ℤ))))
        (((cofactor M : ℤ)) * (((a.2.val : ℤ) + b.2.val) % ((M : ℤ)))) := by
      simp only [Prod.fst_add, Prod.snd_add, ZMod.val_add]
      push_cast
      rfl
    have hR : coordinate M (2 * (a.2.val : ℤ) - a.1.val) (((cofactor M : ℤ)) * (a.2.val : ℤ))
        + coordinate M (2 * (b.2.val : ℤ) - b.1.val) (((cofactor M : ℤ)) * (b.2.val : ℤ))
        = coordinate M
        ((2 * (a.2.val : ℤ) - a.1.val) + (2 * (b.2.val : ℤ) - b.1.val))
        (((cofactor M : ℤ)) * (a.2.val : ℤ) + ((cofactor M : ℤ)) * (b.2.val : ℤ)) :=
      coordinate_add M (2 * (a.2.val : ℤ) - a.1.val) (((cofactor M : ℤ)) * (a.2.val : ℤ))
        (2 * (b.2.val : ℤ) - b.1.val) (((cofactor M : ℤ)) * (b.2.val : ℤ))
    rw [hL, hR]
    have hnm := hnmℤ M
    refine coordinate_eq_of_dvd
      (a := 2 * (((a.2.val : ℤ) + b.2.val) % ((M : ℤ)))
        - (((a.1.val : ℤ) + b.1.val) % ((M : ℤ))))
      (a' := (2 * (a.2.val : ℤ) - a.1.val) + (2 * (b.2.val : ℤ) - b.1.val))
      (b := ((cofactor M : ℤ)) * (((a.2.val : ℤ) + b.2.val) % ((M : ℤ))))
      (b' := ((cofactor M : ℤ)) * (a.2.val : ℤ) + ((cofactor M : ℤ)) * (b.2.val : ℤ))
      (ha := ⟨(((a.1.val : ℤ) + b.1.val) / ((M : ℤ))) - 2 * (((a.2.val : ℤ) + b.2.val) / ((M : ℤ))),
        by linear_combination 2 * hm2 - hm1⟩)
      (hb := ⟨-(((a.2.val : ℤ) + b.2.val) / ((M : ℤ))),
        by linear_combination ((cofactor M : ℤ)) * hm2
          + (((a.2.val : ℤ) + b.2.val) / ((M : ℤ))) * hnm⟩)

theorem iota_torusPoint (h : L2a.Index M) :
    torusPoint M (iota M h) =
      QuotientAddGroup.mk ((h.1.val : ℚ) / M, (h.2.val : ℚ) / M) := by
  show QuotientAddGroup.mk (pointLift M
      ((coordinate M (2 * (h.2.val : ℤ) - h.1.val) (((cofactor M : ℤ)) * h.2.val)).1.val)
      ((coordinate M (2 * (h.2.val : ℤ) - h.1.val) (((cofactor M : ℤ)) * h.2.val)).2.val))
    = QuotientAddGroup.mk (((h.1.val : ℚ)) / M, ((h.2.val : ℚ)) / M)
  rw [coordinate_fst_val M (2 * (h.2.val : ℤ) - h.1.val) (((cofactor M : ℤ)) * h.2.val),
    coordinate_snd_val M (2 * (h.2.val : ℤ) - h.1.val) (((cofactor M : ℤ)) * h.2.val),
    QuotientAddGroup.eq_iff_sub_mem,
    pointLift_mod M (2 * (h.2.val : ℤ) - h.1.val) (((cofactor M : ℤ)) * h.2.val)]
  refine AddMonoidHom.mem_range.mpr ⟨(((2 * (h.2.val : ℤ) - h.1.val) / ((M : ℤ))
      + ((M : ℤ) - 2) * ((((cofactor M : ℤ)) * h.2.val) / ((longModulus M : ℤ)))) - h.2.val,
    -((((cofactor M : ℤ)) * h.2.val) / ((longModulus M : ℤ)))), ?_⟩
  have hcoQ : ((cofactor M : ℚ)) = ((M : ℚ)) - 3 := by exact_mod_cast hcoℤ M
  have hnmQ : ((longModulus M : ℚ)) = ((M : ℚ)) * ((cofactor M : ℚ)) := by exact_mod_cast hnmℤ M
  have hM : ((M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hN : ((longModulus M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hcN : ((cofactor M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  ext <;> simp [pointLift, integerCoordinates] <;> field_simp <;> push_cast <;> ring

private theorem nat_eq_of_modEq_lt (n a b : ℕ) (h : a ≡ b [MOD n]) (ha : a < n) (hb : b < n) :
    a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · rw [Nat.modEq_iff_dvd' (Nat.le_of_lt hab)] at h
    obtain ⟨k, hk⟩ := h
    match k with
    | 0 => omega
    | k + 1 =>
      have hge : n ≤ n * (k + 1) := Nat.le_mul_of_pos_right n (by omega)
      omega
  · exact hab
  · have h2 := h.symm
    rw [Nat.modEq_iff_dvd' (Nat.le_of_lt hab)] at h2
    obtain ⟨k, hk⟩ := h2
    match k with
    | 0 => omega
    | k + 1 =>
      have hge : n ≤ n * (k + 1) := Nat.le_mul_of_pos_right n (by omega)
      omega

theorem iota_injective : Function.Injective (iota M) := by
  intro a b hab
  have h4 : (4 : ℕ) ≤ M := Fact.out
  haveI : NeZero M := NeZero.of_pos (by omega)
  have hcℤ : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 := hcoℤ M
  have hco0 : ((cofactor M : ℤ)) ≠ 0 := by omega
  have hab1 : ((iota M a).1 : ZMod M) = ((iota M b).1 : ZMod M) := congrArg Prod.fst hab
  have hab2 : ((iota M a).2 : ZMod (longModulus M)) = ((iota M b).2 : ZMod (longModulus M)) :=
    congrArg Prod.snd hab
  have e1 : ((iota M a).1 : ZMod M) = (((2 * (a.2.val : ℤ) - a.1.val : ℤ)) : ZMod M) := rfl
  have e1' : ((iota M b).1 : ZMod M) = (((2 * (b.2.val : ℤ) - b.1.val : ℤ)) : ZMod M) := rfl
  have e2 : ((iota M a).2 : ZMod (longModulus M))
      = (((((cofactor M : ℤ)) * a.2.val : ℤ)) : ZMod (longModulus M)) := rfl
  have e2' : ((iota M b).2 : ZMod (longModulus M))
      = (((((cofactor M : ℤ)) * b.2.val : ℤ)) : ZMod (longModulus M)) := rfl
  rw [e1, e1'] at hab1
  rw [e2, e2'] at hab2
  have h1 : ((M : ℤ)) ∣ ((2 * (b.2.val : ℤ) - b.1.val) - (2 * (a.2.val : ℤ) - a.1.val)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (2 * (a.2.val : ℤ) - a.1.val)
      (2 * (b.2.val : ℤ) - b.1.val) M).mp hab1
  have h2 : ((longModulus M : ℤ)) ∣ (((cofactor M : ℤ)) * b.2.val - ((cofactor M : ℤ)) * a.2.val) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (((cofactor M : ℤ)) * a.2.val)
      (((cofactor M : ℤ)) * b.2.val) (longModulus M)).mp hab2
  rw [← mul_sub, hnmℤ M, mul_comm ((M : ℤ)) ((cofactor M : ℤ))] at h2
  have hs : ((M : ℤ)) ∣ ((b.2.val : ℤ) - a.2.val) :=
    (Int.mul_dvd_mul_iff_left hco0).mp h2
  have hr : ((M : ℤ)) ∣ ((b.1.val : ℤ) - a.1.val) := by
    obtain ⟨k1, hk1⟩ := hs
    obtain ⟨k2, hk2⟩ := h1
    refine ⟨2 * k1 - k2, ?_⟩
    linear_combination 2 * hk1 - hk2
  refine Prod.ext ?_ ?_
  · exact ZMod.val_injective M
      (nat_eq_of_modEq_lt M _ _ ((Nat.modEq_iff_dvd).mpr hr) (ZMod.val_lt _) (ZMod.val_lt _))
  · exact ZMod.val_injective M
      (nat_eq_of_modEq_lt M _ _ ((Nat.modEq_iff_dvd).mpr hs) (ZMod.val_lt _) (ZMod.val_lt _))

private theorem zmod_nsmul_eq_zero_iff (M N : ℕ) (x : ℤ) :
    M • ((x : ZMod N)) = 0 ↔ ((N : ℤ)) ∣ ((M : ℤ)) * x := by
  constructor
  · intro h
    have eM : ((M : ZMod N)) = ((((M : ℤ)) : ZMod N)) := by push_cast; rfl
    rw [nsmul_eq_mul, eM, ← Int.cast_mul] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  · intro h
    have key : ((((M : ℤ) * x : ℤ)) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    have eM : ((M : ZMod N)) = ((((M : ℤ)) : ZMod N)) := by push_cast; rfl
    rw [nsmul_eq_mul, eM, ← Int.cast_mul]
    exact key

theorem iota_range_eq_torsion :
    ((iota M).range : Set (G M)) = {g : G M | M • g = 0} := by
  have h4 : (4 : ℕ) ≤ M := Fact.out
  haveI : NeZero M := NeZero.of_pos (by omega)
  have hco := hcoℤ M
  have hnm := hnmℤ M
  haveI : NeZero (longModulus M) := by
    refine ⟨fun hc => ?_⟩
    have e0 : ((longModulus M : ℤ)) = 0 := by rw [hc]; simp
    rw [hnm, hco] at e0
    rcases Int.mul_eq_zero.mp e0 with h1 | h2 <;> omega
  ext g
  constructor
  · intro hg
    rw [SetLike.mem_coe] at hg
    obtain ⟨h, rfl⟩ := AddMonoidHom.mem_range.mp hg
    show (M • ((((2 * (h.2.val : ℤ) - h.1.val : ℤ)) : ZMod M),
      (((((cofactor M : ℤ)) * h.2.val : ℤ)) : ZMod (longModulus M)))) = (0, 0)
    rw [Prod.smul_def, Prod.mk_zero_zero]
    refine Prod.ext ?_ ?_
    · exact (zmod_nsmul_eq_zero_iff _ _ _).mpr (dvd_mul_right _ _)
    · exact (zmod_nsmul_eq_zero_iff _ _ _).mpr (by
        refine ⟨(h.2.val : ℤ), ?_⟩
        rw [hnm]
        ring)
  · intro hg
    rw [SetLike.mem_coe, AddMonoidHom.mem_range]
    have hsn : M • (g.2 : ZMod (longModulus M)) = 0 := by
      have := congrArg Prod.snd hg
      simpa using this
    have hgc : (g.2 : ZMod (longModulus M)) = ((((g.2.val : ℤ)) : ZMod (longModulus M))) := by
      simp [ZMod.natCast_val, Int.cast_natCast]
    rw [hgc] at hsn
    have hdvd := (zmod_nsmul_eq_zero_iff M (longModulus M) ((g.2.val : ℤ))).mp hsn
    rw [hnm] at hdvd
    have hc0 : ((M : ℤ)) ≠ 0 := by omega
    have hcov : ((cofactor M : ℤ)) ∣ ((g.2.val : ℤ)) := (Int.mul_dvd_mul_iff_left hc0).mp hdvd
    have hvt : ((cofactor M : ℤ)) * (((((g.2.val : ℤ))) / (((cofactor M : ℤ))))) = ((g.2.val : ℤ)) := by
      have e := Int.mul_ediv_add_emod ((g.2.val : ℤ)) ((cofactor M : ℤ))
      rw [Int.emod_eq_zero_of_dvd hcov, add_zero] at e
      exact e
    refine ⟨((((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - (g.1.val : ℤ) : ℤ)) : ZMod M), (((((g.2.val : ℤ)) / ((cofactor M : ℤ)) : ℤ)) : ZMod M)), ?_⟩
    show coordinate M (2 * (((((((g.2.val : ℤ)) / ((cofactor M : ℤ)) : ℤ)) : ZMod M).val : ℤ)) - (((((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - (g.1.val : ℤ) : ℤ)) : ZMod M).val : ℤ))) ((((cofactor M : ℤ)) * (((((((g.2.val : ℤ)) / ((cofactor M : ℤ)) : ℤ)) : ZMod M).val : ℤ)))) = g
    rw [ZMod.val_intCast, ZMod.val_intCast]
    have et : ((M : ℤ)) * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) / ((M : ℤ))) + ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ))) = (((g.2.val : ℤ)) / ((cofactor M : ℤ))) := Int.mul_ediv_add_emod _ _
    have eu : ((M : ℤ)) * ((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) / ((M : ℤ))) + ((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) % ((M : ℤ))) = (2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) := Int.mul_ediv_add_emod _ _
    have hco0' : ((cofactor M : ℤ)) ≠ 0 := by have := hcoℤ M; omega
    have hnum : ((2 : ℤ)) * ((g.2.val : ℤ))
        = ((2 : ℤ)) * (((cofactor M : ℤ)) * (((g.2.val : ℤ)) / ((cofactor M : ℤ)))) := by
      rw [hvt]
    have h2T : (((2 : ℤ)) * ((g.2.val : ℤ))) / ((cofactor M : ℤ))
        = ((2 : ℤ)) * (((g.2.val : ℤ)) / ((cofactor M : ℤ))) := by
      rw [hnum, ← mul_assoc, mul_comm ((2 : ℤ)) ((cofactor M : ℤ)), mul_assoc,
        Int.mul_ediv_cancel_left (((2 : ℤ)) * (((g.2.val : ℤ)) / ((cofactor M : ℤ)))) hco0']
    have hcoord : coordinate M (2 * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ))) - ((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) % ((M : ℤ)))) (((cofactor M : ℤ)) * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ))))
        = coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ)) :=
      coordinate_eq_of_dvd
        (a := (2 * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ))) - ((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) % ((M : ℤ)))))
        (a' := (g.1.val : ℤ))
        (b := (((cofactor M : ℤ)) * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ)))))
        (b' := (g.2.val : ℤ))
        (ha := ⟨((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) / ((M : ℤ))) - 2 * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) / ((M : ℤ))), by linear_combination 2 * et - eu - h2T⟩)
        (hb := ⟨-((((g.2.val : ℤ)) / ((cofactor M : ℤ))) / ((M : ℤ))), by
          linear_combination ((cofactor M : ℤ)) * et + hvt + ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) / ((M : ℤ))) * hnm⟩)
    exact hcoord.trans (coordinate_val M g)


def annihilatorGenerator : G M := coordinate M 0 (-(M : ℤ))

/-- A lift of the generator of G/H. Its M-multiple is annihilatorGenerator. -/
def quotientGenerator : G M := coordinate M 0 (-1)

def quotientMap (M : ℕ) [Fact (4 ≤ M)] : G M →+ ZMod (cofactor M) where
  toFun g := -(g.2.val : ZMod (cofactor M))
  map_zero' := by simp
  map_add' := by
    intro g₁ g₂
    have h4 : (4 : ℕ) ≤ M := Fact.out
    have hco := hcoℤ M
    have hnm := hnmℤ M
    haveI : NeZero M := NeZero.of_pos (by omega)
    haveI : NeZero (cofactor M) := by
      refine ⟨fun hc => ?_⟩
      have hc' : ((cofactor M : ℤ)) = 0 := by rw [hc]; simp
      rw [hco] at hc'
      omega
    haveI : NeZero (longModulus M) := by
      refine ⟨fun hc => ?_⟩
      have e0 : ((longModulus M : ℤ)) = 0 := by rw [hc]; simp
      rw [hnm, hco] at e0
      rcases Int.mul_eq_zero.mp e0 with h1 | h2 <;> omega
    have hcd : cofactor M ∣ longModulus M := ⟨M, by simp [longModulus, mul_comm]⟩
    simp only [Prod.snd_add, ZMod.natCast_val]
    rw [ZMod.cast_add hcd]
    ring

private theorem quotientMap_coordinate (x y : ℤ) :
    quotientMap M (coordinate M x y) = -(y : ZMod (cofactor M)) := by
  have hcd : cofactor M ∣ longModulus M := ⟨M, by simp [longModulus, mul_comm]⟩
  change -(((y : ZMod (longModulus M)).val : ℕ) : ZMod (cofactor M)) = _
  rw [ZMod.natCast_val, ZMod.cast_intCast hcd]

private theorem nsmul_coordinate (k : ℕ) (x y : ℤ) :
    k • coordinate M x y = coordinate M ((k : ℤ) * x) ((k : ℤ) * y) := by
  ext <;> simp [coordinate, nsmul_eq_mul]

theorem quotientMap_surjective : Function.Surjective (quotientMap M) := by
  intro c
  refine ⟨coordinate M 0 (-((c.val : ℤ))), ?_⟩
  rw [quotientMap_coordinate]
  simp

theorem quotientMap_kernel : (quotientMap M).ker = (iota M).range := by
  apply SetLike.coe_injective
  rw [iota_range_eq_torsion M]
  ext g
  change quotientMap M g = 0 ↔ M • g = 0
  rw [← coordinate_val M g, quotientMap_coordinate]
  simp only [coordinate, Prod.smul_mk, Prod.mk_eq_zero, neg_eq_zero,
    zmod_nsmul_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_mul_right, true_and]
  rw [hnmℤ M, Int.mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr (NeZero.ne M))]

theorem quotient_cyclic :
    Nonempty ((G M ⧸ (iota M).range) ≃+ ZMod (cofactor M)) := by
  rw [← quotientMap_kernel M]
  exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective (quotientMap M)
    (quotientMap_surjective M)⟩

theorem annihilatorGenerator_order : addOrderOf (annihilatorGenerator M) = cofactor M := by
  simp only [annihilatorGenerator, coordinate, Int.cast_zero, Int.cast_neg, Int.cast_natCast,
    Prod.addOrderOf_mk, addOrderOf_zero, Nat.lcm_one_left, addOrderOf_neg]
  rw [ZMod.addOrderOf_coe M (NeZero.ne (longModulus M))]
  simp [longModulus, Nat.gcd_comm, NeZero.ne M]

theorem annihilatorGenerator_torusPoint :
    torusPoint M (annihilatorGenerator M) =
      QuotientAddGroup.mk ((1 : ℚ) / cofactor M, -(1 : ℚ) / cofactor M) := by
  unfold annihilatorGenerator
  rw [torusPoint_coordinate, QuotientAddGroup.eq_iff_sub_mem]
  refine AddMonoidHom.mem_range.mpr ⟨(1, 0), ?_⟩
  have hM : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hm : (cofactor M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hco : (cofactor M : ℚ) = (M : ℚ) - 3 := by exact_mod_cast hcoℤ M
  have hnm : (longModulus M : ℚ) = (M : ℚ) * (cofactor M : ℚ) := by
    exact_mod_cast hnmℤ M
  change ((1 : ℚ), (0 : ℚ)) = pointLift M 0 (-(M : ℤ)) -
    ((1 : ℚ) / cofactor M, -(1 : ℚ) / cofactor M)
  rw [hco] at hm hnm ⊢
  ext <;> simp [pointLift, hnm, hco] <;> field_simp <;> ring

theorem quotientGenerator_mul : M • quotientGenerator M = annihilatorGenerator M := by
  ext <;> simp [quotientGenerator, annihilatorGenerator, coordinate, nsmul_eq_mul]

/-- The exact sequence in [RW26] is 0→H→G --[M]→MG→0. -/
theorem mul_M_eq_quotient (g : G M) :
    M • g = (quotientMap M g).val • annihilatorGenerator M := by
  have hd : ((cofactor M : ℤ)) ∣ ((quotientMap M g).val : ℤ) + (g.2.val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    change -(g.2.val : ZMod (cofactor M)) + (g.2.val : ZMod (cofactor M)) = 0
    exact neg_add_cancel _
  have hL : M • g = coordinate M ((M : ℤ) * (g.1.val : ℤ))
      ((M : ℤ) * (g.2.val : ℤ)) := by
    conv_lhs => rw [← coordinate_val M g]
    exact nsmul_coordinate M M _ _
  rw [hL, annihilatorGenerator, nsmul_coordinate]
  apply coordinate_eq_of_dvd
  · exact ⟨(g.1.val : ℤ), by ring⟩
  · obtain ⟨k, hk⟩ := hd
    refine ⟨k, ?_⟩
    rw [hnmℤ M]
    linear_combination (M : ℤ) * hk

theorem epsilonAut_fixes_annihilatorGenerator :
    epsilonAut M (annihilatorGenerator M) = annihilatorGenerator M := by
  unfold annihilatorGenerator
  rw [epsilonAut_coordinate]
  apply coordinate_eq_of_dvd (M := M)
  · exact ⟨-1, by ring⟩
  · refine ⟨-1, ?_⟩
    rw [hnmℤ M, hcoℤ M]
    ring

/-- The witness w, using canonical lifts of h=(r,s). -/
def witnessW (h : L2a.Index M) : G M :=
  coordinate M ((h.1.val : ℤ) - h.2.val)
    (((M : ℤ) - 1) * h.1.val - ((M : ℤ) - 2) * h.2.val)

theorem witnessW_epsilon (h : L2a.Index M) :
    epsilonAut M (witnessW M h) = witnessW M h + iota M h := by
  change epsilonAut M (coordinate M _ _) = coordinate M _ _ + coordinate M _ _
  rw [epsilonAut_coordinate, coordinate_add, hcoℤ M]
  apply coordinate_eq_of_dvd (M := M)
  · exact ⟨(h.1.val : ℤ) - h.2.val, by ring⟩
  · refine ⟨(h.1.val : ℤ) - h.2.val, ?_⟩
    rw [hnmℤ M, hcoℤ M]
    ring

/-- A concrete finite coset decomposition, not a structural hypothesis. -/
theorem sum_over_cosets (f : G M → ℂ) :
    (∑ g : G M, f g) =
      ∑ j : Fin (cofactor M), ∑ h : L2a.Index M,
        f (iota M h + j.val • quotientGenerator M) := by
  have hi (h : L2a.Index M) : quotientMap M (iota M h) = 0 := by
    change iota M h ∈ (quotientMap M).ker
    rw [quotientMap_kernel]
    exact AddMonoidHom.mem_range.mpr ⟨h, rfl⟩
  have hg : quotientMap M (quotientGenerator M) = 1 := by
    simp [quotientGenerator, quotientMap_coordinate]
  let φ : Fin (cofactor M) × L2a.Index M → G M :=
    fun p => iota M p.2 + p.1.val • quotientGenerator M
  have hφ (p : Fin (cofactor M) × L2a.Index M) :
      quotientMap M (φ p) = (p.1.val : ZMod (cofactor M)) := by
    dsimp only [φ]
    rw [map_add, hi, map_nsmul, hg]
    simp [nsmul_eq_mul]
  have hinj : Function.Injective φ := by
    intro a b hab
    have hj : a.1 = b.1 := by
      apply Fin.ext
      have he := congrArg (fun g => (quotientMap M g).val) hab
      rw [hφ, hφ, ZMod.val_natCast_of_lt a.1.isLt,
        ZMod.val_natCast_of_lt b.1.isLt] at he
      exact he
    have hh : a.2 = b.2 := by
      apply iota_injective M
      have he : iota M a.2 + a.1.val • quotientGenerator M =
          iota M b.2 + a.1.val • quotientGenerator M := by
        simpa only [φ, hj] using hab
      exact add_right_cancel he
    exact Prod.ext hj hh
  have hsurj : Function.Surjective φ := by
    intro g
    let j : Fin (cofactor M) := ⟨(quotientMap M g).val, ZMod.val_lt _⟩
    have hj : (j.val : ZMod (cofactor M)) = quotientMap M g :=
      ZMod.natCast_zmod_val _
    have hk : g - j.val • quotientGenerator M ∈ (iota M).range := by
      rw [← quotientMap_kernel, AddMonoidHom.mem_ker]
      rw [map_sub, map_nsmul, hg]
      simp only [nsmul_eq_mul, mul_one, hj, sub_self]
    obtain ⟨h, hh⟩ := AddMonoidHom.mem_range.mp hk
    refine ⟨(j, h), ?_⟩
    change iota M h + j.val • quotientGenerator M = g
    rw [hh, sub_add_cancel]
  have hsum := (Equiv.ofBijective φ ⟨hinj, hsurj⟩).sum_comp f
  rw [← hsum, Fintype.sum_prod_type]
  rfl

end SICLean.L2b
