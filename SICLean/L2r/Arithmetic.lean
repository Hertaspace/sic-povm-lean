import SICLean.L2b.Main

set_option autoImplicit false

/-!
# Principal rank-r arithmetic

The recurrence index is a conclusion, not an input or a choice in the construction.
-/

noncomputable section

namespace SICLean.L2r

/-- The main range of the existence theorem. -/
structure Admissible (d r : ℕ) : Prop where
  rank_pos : 1 ≤ r
  main_range : 2 * r + 1 < d
  divides : r * (d - r) ∣ d ^ 2 - 1

def level (d r : ℕ) : ℕ := (d ^ 2 - 1) / (r * (d - r))
def ell (d r : ℕ) : ℕ := level d r - 2
def cofactor (d r : ℕ) : ℕ := level d r - 4
def longModulus (d r : ℕ) : ℕ := d * cofactor d r
def groupOrder (d r : ℕ) : ℕ := d ^ 2 * cofactor d r
def gap (d r : ℕ) : ℤ := (d : ℤ) - 2 * r

/-- The attracting unit of L, whereas the period of γ is `eta`. -/
def unit (d r : ℕ) : ℝ :=
  ((ell d r : ℝ) + Real.sqrt ((ell d r : ℝ) ^ 2 - 4)) / 2

def alpha (d r : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(ell d r : ℤ), -1; 1, 0]

/-- β = (d-r)I-rL⁻¹; later β=L^m. All subtractions here are in ℤ. -/
def beta (d r : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(d : ℤ) - r, -(r : ℤ);
    (r : ℤ), (d : ℤ) - r - (ell d r : ℤ) * r]

def gamma (d r : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  beta d r ^ 2 * alpha d r

def eta (d r : ℕ) : ℝ :=
  unit d r * ((d : ℝ) - r - (r : ℝ) / unit d r) ^ 2

def originValue (d r : ℕ) : ℂ := (Real.sqrt (eta d r) : ℂ)
def rootLevel (d r : ℕ) : ℂ := (Real.sqrt (level d r) : ℂ)

/-- An integer recurrence suffices; fundamental units and maximal orders are unnecessary. -/


def rankSequence (l : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => l * rankSequence l (k + 1) - rankSequence l k



/-! ### Recurrence helpers for `grid_position` -/

private lemma rankSequence_conic (L : ℕ) (m : ℕ) :
    (rankSequence (L : ℤ) m) ^ 2 + (rankSequence (L : ℤ) (m + 1)) ^ 2 -
      (L : ℤ) * rankSequence (L : ℤ) m * rankSequence (L : ℤ) (m + 1) = 1 := by
  induction m with
  | zero => simp [rankSequence]
  | succ k ih =>
      rw [show k + 1 + 1 = k + 2 by omega]
      have hrec : rankSequence (L : ℤ) (k + 2) =
          (L : ℤ) * rankSequence (L : ℤ) (k + 1) - rankSequence (L : ℤ) k := by
        rw [rankSequence]
      rw [hrec]
      linear_combination ih

private lemma rankSequence_pos_lt (L : ℕ) (hL : 3 ≤ L) :
    ∀ k : ℕ, 1 ≤ k →
      0 < rankSequence (L : ℤ) k ∧ rankSequence (L : ℤ) k < rankSequence (L : ℤ) (k + 1) := by
  refine Nat.le_induction ?_ ?_
  · constructor
    · simp [rankSequence]
    · simp [rankSequence]
      omega
  · intro k hk ih
    refine ⟨lt_trans (show 0 < rankSequence (L : ℤ) k from ih.1) ih.2, ?_⟩
    rw [show k + 1 + 1 = k + 2 by omega]
    have hrec : rankSequence (L : ℤ) (k + 2) =
        (L : ℤ) * rankSequence (L : ℤ) (k + 1) - rankSequence (L : ℤ) k := by
      rw [rankSequence]
    rw [hrec]
    have hLz : (3 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    nlinarith [ih.1, ih.2]

private lemma rankSequence_strict_mono (L : ℕ) (hL : 3 ≤ L) :
    ∀ i j : ℕ, 1 ≤ i → i < j →
      rankSequence (L : ℤ) i < rankSequence (L : ℤ) j := by
  intro i j
  induction j with
  | zero =>
      intro _ hlt
      omega
  | succ j ih =>
      intro hij hlt
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · exact lt_trans (ih hij h) (rankSequence_pos_lt L hL j (by omega)).2
      · subst h
        exact (rankSequence_pos_lt L hL i hij).2

private lemma rankSequence_grid_exists (L : ℕ) (hL : 3 ≤ L) :
    ∀ r : ℕ, 1 ≤ r → ∀ s : ℕ, r < s →
      (r : ℤ) ^ 2 + (s : ℤ) ^ 2 - (L : ℤ) * (r : ℤ) * (s : ℤ) = 1 →
      ∃ m : ℕ, 1 ≤ m ∧ rankSequence (L : ℤ) m = (r : ℤ) ∧
        rankSequence (L : ℤ) (m + 1) = (s : ℤ) := by
  intro r
  refine Nat.strong_induction_on r ?_
  intro r ih hr s hrs hcon
  by_cases hr1 : r = 1
  · subst hr1
    have hs : s = L := by
      have hz : (1 : ℤ) + (s : ℤ) ^ 2 - (L : ℤ) * (s : ℤ) = 1 := by simpa using hcon
      have hmul : (s : ℤ) * ((s : ℤ) - (L : ℤ)) = 0 := by nlinarith
      rcases Int.mul_eq_zero.mp hmul with h | h
      · have : (0 : ℤ) < (s : ℤ) := by exact_mod_cast (by omega : 0 < s)
        omega
      · exact_mod_cast (sub_eq_zero.mp h)
    subst hs
    refine ⟨1, by norm_num, ?_, ?_⟩
    · simp [rankSequence]
    · simp [rankSequence]
  · have hs0z : (0 : ℤ) < (s : ℤ) := by exact_mod_cast (by omega : 0 < s)
    have hrz : (0 : ℤ) < (r : ℤ) := by exact_mod_cast (by omega : 0 < r)
    have hsLr : s ≤ L * r := by
      by_contra hle
      push_neg at hle
      have hA : (0 : ℤ) < (s : ℤ) - (L : ℤ) * (r : ℤ) := by
        have : (L : ℤ) * (r : ℤ) < (s : ℤ) := by exact_mod_cast hle
        omega
      have hprod : 0 < (s : ℤ) * ((s : ℤ) - (L : ℤ) * (r : ℤ)) :=
        mul_pos hs0z hA
      nlinarith
    have hsgt : ((L : ℤ) - 1) * (r : ℤ) < (s : ℤ) := by
      by_contra hle
      push_neg at hle
      have hA : (s : ℤ) - (L : ℤ) * (r : ℤ) ≤ -(r : ℤ) := by nlinarith
      have hprod : (s : ℤ) * ((s : ℤ) - (L : ℤ) * (r : ℤ)) ≤ -((s : ℤ) * (r : ℤ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hA (le_of_lt hs0z)]
      have hrsz : (0 : ℤ) < (s : ℤ) - (r : ℤ) := by
        have : (r : ℤ) < (s : ℤ) := by exact_mod_cast hrs
        omega
      nlinarith
    let t : ℕ := L * r - s
    have htcast : (t : ℤ) = (L : ℤ) * (r : ℤ) - (s : ℤ) := by
      exact Nat.cast_sub hsLr
    have ht_lt_r : t < r := by
      have hz : (L : ℤ) * (r : ℤ) - (s : ℤ) < (r : ℤ) := by nlinarith
      have : (t : ℤ) < (r : ℤ) := by
        rw [htcast]
        exact hz
      exact_mod_cast this
    have ht_pos : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · exfalso
        have htz : (t : ℤ) = 0 := by omega
        rw [htcast] at htz
        have hs_eq : (s : ℤ) = (L : ℤ) * (r : ℤ) := by omega
        have hr2 : (r : ℤ) ^ 2 = 1 := by nlinarith
        have hr1z : (r : ℤ) = 1 := by
          nlinarith [sq_nonneg ((r : ℤ) - 1), hrz]
        have : r = 1 := by exact_mod_cast hr1z
        omega
      · exact hpos
    have hcon' : (t : ℤ) ^ 2 + (r : ℤ) ^ 2 -
        (L : ℤ) * (t : ℤ) * (r : ℤ) = 1 := by
      rw [htcast]
      nlinarith
    obtain ⟨m, hm1, hmr, hmr1⟩ := ih t ht_lt_r ht_pos r ht_lt_r hcon'
    refine ⟨m + 1, by omega, ?_, ?_⟩
    · simpa [Nat.add_assoc] using hmr1
    · rw [show m + 1 + 1 = m + 2 by omega]
      have hrec : rankSequence (L : ℤ) (m + 2) =
          (L : ℤ) * rankSequence (L : ℤ) (m + 1) - rankSequence (L : ℤ) m := by
        rw [rankSequence]
      rw [hrec, hmr1, hmr, htcast]
      ring


def shift (d r : ℕ) : ℤ := 1 - (level d r : ℤ)
def twistScalar (d r : ℕ) : ℤ := (r : ℤ) * ((d : ℤ) - level d r)
def phaseModulus (d : ℕ) : ℕ := if Even d then 2 * d else d

/-- Used with an explicit local `letI`: r cannot be inferred from the target NeZero d. -/
def admissibleDimensionNeZero (d r : ℕ) [Fact (Admissible d r)] : NeZero d :=
  ⟨by
    have h := (Fact.out : Admissible d r)
    have hr : 1 ≤ r := h.rank_pos
    have hd : 2 * r + 1 < d := h.main_range
    omega⟩

private lemma level_pos {d r : ℕ} (h : Admissible d r) : 0 < r * (d - r) := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  exact Nat.mul_pos (by omega) (by omega)

theorem level_ge_five {d r : ℕ} (h : Admissible d r) : 5 ≤ level d r := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hpos : 0 < r * (d - r) := level_pos h
  have hgt : 4 * (r * (d - r)) < d ^ 2 - 1 := by
    have hg : 2 ≤ d - 2 * r := by omega
    have hsq : 4 ≤ (d - 2 * r) ^ 2 := by nlinarith
    have hle : 2 * r ≤ d := by omega
    have hdecomp : d ^ 2 = (d - 2 * r) ^ 2 + 4 * (r * (d - r)) := by
      have hdr : ((d - r : ℕ) : ℤ) = (d : ℤ) - r := Nat.cast_sub (by omega)
      zify [hle, Nat.le_of_lt hd]
      rw [hdr]
      ring
    omega
  have hlt : 4 < level d r := by
    rw [level, Nat.lt_div_iff_mul_lt' h.divides]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgt
  omega

instance admissibleCofactorNeZero (d r : ℕ) [Fact (Admissible d r)] :
    NeZero (cofactor d r) :=
  ⟨by have h := level_ge_five (Fact.out : Admissible d r); simp only [cofactor]; omega⟩

instance admissibleLongModulusNeZero (d r : ℕ) [Fact (Admissible d r)] :
    NeZero (longModulus d r) :=
  ⟨by
    have h := (Fact.out : Admissible d r)
    have hr : 1 ≤ r := h.rank_pos
    have hd : 2 * r + 1 < d := h.main_range
    have hco : 0 < cofactor d r := NeZero.pos (cofactor d r)
    exact Nat.mul_ne_zero (by omega) (by omega)⟩

theorem level_identity {d r : ℕ} (h : Admissible d r) :
    level d r * r * (d - r) = d ^ 2 - 1 := by
  have hnat := Nat.div_mul_cancel h.divides
  unfold level
  simpa [mul_assoc, mul_comm, mul_left_comm] using hnat

private lemma level_identity_int {d r : ℕ} (h : Admissible d r) :
    (level d r : ℤ) * (r : ℤ) * ((d : ℤ) - r) = (d : ℤ) ^ 2 - 1 := by
  have hli := level_identity h
  have hli' : ((level d r * r * (d - r) : ℕ) : ℤ) = ((d ^ 2 - 1 : ℕ) : ℤ) := by
    exact_mod_cast hli
  have hdr : ((d - r : ℕ) : ℤ) = (d : ℤ) - r := Nat.cast_sub (by
    have := h.main_range
    omega)
  push_cast at hli'
  rw [hdr] at hli'
  have hd2 : (1 : ℕ) ≤ d ^ 2 := by
    have : 1 ≤ d := by have := h.main_range; omega
    nlinarith
  rw [Nat.cast_sub hd2] at hli'
  push_cast at hli'
  exact hli'

theorem principal_conic {d r : ℕ} (h : Admissible d r) :
    (r : ℤ) ^ 2 + ((d : ℤ) - r) ^ 2 -
      (ell d r : ℤ) * r * ((d : ℤ) - r) = 1 := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hlev : 5 ≤ level d r := level_ge_five h
  have hli := level_identity h
  have hcast : (level d r : ℤ) * (r : ℤ) * ((d : ℤ) - r) = (d : ℤ) ^ 2 - 1 := by
    have hli' : ((level d r * r * (d - r) : ℕ) : ℤ) = ((d ^ 2 - 1 : ℕ) : ℤ) := by
      exact_mod_cast hli
    have hdr : ((d - r : ℕ) : ℤ) = (d : ℤ) - r := Nat.cast_sub (by omega)
    push_cast at hli'
    rw [hdr] at hli'
    have hd2 : (1 : ℕ) ≤ d ^ 2 := by
      have : 1 ≤ d := by omega
      nlinarith
    rw [Nat.cast_sub hd2] at hli'
    push_cast at hli'
    exact hli'
  have hell : (ell d r : ℤ) = (level d r : ℤ) - 2 := by
    simp only [ell]
    exact Nat.cast_sub (by omega)
  rw [hell]
  have hsq : ((d : ℤ) - r) ^ 2 + 2 * (r : ℤ) * ((d : ℤ) - r) + (r : ℤ) ^ 2 = (d : ℤ) ^ 2 := by
    ring
  linear_combination -hcast + hsq

theorem grid_position {d r : ℕ} (h : Admissible d r) :
    ∃! m : ℕ, 1 ≤ m ∧ rankSequence (ell d r) m = (r : ℤ) ∧
      rankSequence (ell d r) (m + 1) = (d : ℤ) - r := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hlt : r < d - r := by omega
  have hlev : 5 ≤ level d r := level_ge_five h
  have hell : 3 ≤ ell d r := by simp only [ell]; omega
  have hdr : ((d - r : ℕ) : ℤ) = (d : ℤ) - r := Nat.cast_sub (by omega)
  have hcon : (r : ℤ) ^ 2 + ((d - r : ℕ) : ℤ) ^ 2 -
      (ell d r : ℤ) * (r : ℤ) * ((d - r : ℕ) : ℤ) = 1 := by
    rw [hdr]
    exact principal_conic h
  obtain ⟨m, hm1, hmr, hms⟩ := rankSequence_grid_exists (ell d r) hell r hr (d - r) hlt hcon
  have hms' : rankSequence (ell d r) (m + 1) = (d : ℤ) - r := by rw [hms, hdr]
  refine ⟨m, ⟨hm1, hmr, hms'⟩, ?_⟩
  intro m' hm'
  have heq : rankSequence (ell d r) m' = rankSequence (ell d r) m := by
    rw [hm'.2.1, hmr]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt' | hlt'
  · have := rankSequence_strict_mono (ell d r) hell m' m hm'.1 hlt'
    omega
  · have := rankSequence_strict_mono (ell d r) hell m m' hm1 hlt'
    omega


private lemma alpha_pow_formula (d r : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    alpha d r ^ m = !![rankSequence (ell d r) (m + 1), -rankSequence (ell d r) m;
      rankSequence (ell d r) m, -rankSequence (ell d r) (m - 1)] := by
  refine Nat.le_induction ?_ ?_ m hm
  · simp [alpha, rankSequence]
  · intro k hk ih
    rw [pow_succ, ih]
    have hrec2 : rankSequence (ell d r) (k + 2) =
        (ell d r : ℤ) * rankSequence (ell d r) (k + 1) - rankSequence (ell d r) k := by
      rw [rankSequence]
    have hrec1 : rankSequence (ell d r) (k + 1) =
        (ell d r : ℤ) * rankSequence (ell d r) k - rankSequence (ell d r) (k - 1) := by
      rw [show k + 1 = (k - 1) + 2 by omega, rankSequence,
        show k - 1 + 1 = k by omega]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alpha, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, hrec2, hrec1]
    all_goals ring

theorem beta_eq_alpha_pow {d r : ℕ} (h : Admissible d r) (m : ℕ)
    (hm : 1 ≤ m) (hr : rankSequence (ell d r) m = (r : ℤ))
    (hs : rankSequence (ell d r) (m + 1) = (d : ℤ) - r) :
    beta d r = alpha d r ^ m ∧ gamma d r = alpha d r ^ (2 * m + 1) := by
  have hform := alpha_pow_formula d r m hm
  have hprev : rankSequence (ell d r) (m - 1) = (ell d r : ℤ) * (r : ℤ) - ((d : ℤ) - r) := by
    have hrec : rankSequence (ell d r) (m + 1) =
        (ell d r : ℤ) * rankSequence (ell d r) m - rankSequence (ell d r) (m - 1) := by
      rw [show m + 1 = (m - 1) + 2 by omega, rankSequence,
        show m - 1 + 1 = m by omega]
    rw [hs, hr] at hrec
    linarith
  have hbeta : beta d r = alpha d r ^ m := by
    rw [hform]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [beta, hr, hs, hprev] <;> ring
  refine ⟨hbeta, ?_⟩
  rw [gamma, hbeta, show 2 * m + 1 = m + m + 1 by omega, pow_add, pow_add,
    pow_one, pow_two]

theorem gamma_arithmetic {d r : ℕ} (h : Admissible d r) :
    (alpha d r).det = 1 ∧ (beta d r).det = 1 ∧ (gamma d r).det = 1 ∧
      (gamma d r).trace = (groupOrder d r : ℤ) + 2 ∧
      gamma d r 1 0 = (d : ℤ) * gap d r := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hcon := principal_conic h
  have hlev : 5 ≤ level d r := level_ge_five h
  have hell : (ell d r : ℤ) = (level d r : ℤ) - 2 := by
    simp only [ell]
    exact Nat.cast_sub (by omega)
  have hlevel : (level d r : ℤ) = (ell d r : ℤ) + 2 := by omega
  have hco : (cofactor d r : ℤ) = (ell d r : ℤ) - 2 := by
    have : (cofactor d r : ℤ) = (level d r : ℤ) - 4 := by
      simp only [cofactor]
      exact Nat.cast_sub (by omega)
    omega
  have hliZ : (level d r : ℤ) * (r : ℤ) * ((d : ℤ) - r) = (d : ℤ) ^ 2 - 1 := by
    have hli := level_identity h
    have hli' : ((level d r * r * (d - r) : ℕ) : ℤ) = ((d ^ 2 - 1 : ℕ) : ℤ) := by
      exact_mod_cast hli
    have hdr : ((d - r : ℕ) : ℤ) = (d : ℤ) - r := Nat.cast_sub (by omega)
    push_cast at hli'
    rw [hdr] at hli'
    have hd2 : (1 : ℕ) ≤ d ^ 2 := by
      have : 1 ≤ d := by omega
      nlinarith
    rw [Nat.cast_sub hd2] at hli'
    push_cast at hli'
    exact hli'
  have hgo : (groupOrder d r : ℤ) = (d : ℤ) ^ 2 * (cofactor d r : ℤ) := by
    simp only [groupOrder, Nat.cast_mul, Nat.cast_pow]
  have hdetA : (alpha d r).det = 1 := by
    simp [alpha, Matrix.det_fin_two]
  have hdetB : (beta d r).det = 1 := by
    simp only [beta, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    nlinarith
  have hdetG : (gamma d r).det = 1 := by
    rw [gamma, Matrix.det_mul, Matrix.det_pow, hdetA, hdetB]
    ring
  have htrace : (gamma d r).trace = (groupOrder d r : ℤ) + 2 := by
    have hgf : (gamma d r).trace =
        (ell d r : ℤ) * ((r : ℤ) ^ 2 + ((d : ℤ) - r) ^ 2)
          - 4 * (r : ℤ) * ((d : ℤ) - r) := by
      simp only [gamma, beta, alpha, Matrix.trace, Matrix.mul_apply, Matrix.diag_apply,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, pow_two]
      ring
    rw [hgf, hgo, hco]
    nlinarith
  have h10 : gamma d r 1 0 = (d : ℤ) * gap d r := by
    have hgf : gamma d r 1 0 = ((d : ℤ) - r) ^ 2 - (r : ℤ) ^ 2 := by
      simp only [gamma, beta, alpha, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
        pow_two]
      ring
    rw [hgf]
    simp only [gap]
    ring
  exact ⟨hdetA, hdetB, hdetG, htrace, h10⟩

theorem gamma_sub_one {d r : ℕ} (h : Admissible d r) :
    gamma d r - 1 = (d : ℤ) • (beta d r * (alpha d r - 1)) := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hcon := principal_conic h
  have hG : gamma d r =
      !![(ell d r : ℤ) * ((d : ℤ) - r) ^ 2 - 2 * (r : ℤ) * ((d : ℤ) - r),
        (r : ℤ) ^ 2 - ((d : ℤ) - r) ^ 2;
        ((d : ℤ) - r) ^ 2 - (r : ℤ) ^ 2,
        (ell d r : ℤ) * (r : ℤ) ^ 2 - 2 * (r : ℤ) * ((d : ℤ) - r)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gamma, beta, alpha, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
        pow_two]
    all_goals ring
  have hR : beta d r * (alpha d r - 1) =
      !![((d : ℤ) - r) * (ell d r : ℤ) - ((d : ℤ) - r) - (r : ℤ),
        (r : ℤ) - ((d : ℤ) - r);
        ((d : ℤ) - r) - (r : ℤ),
        (ell d r : ℤ) * (r : ℤ) - (r : ℤ) - ((d : ℤ) - r)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [beta, alpha, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.sub_apply, Matrix.one_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    all_goals ring
  rw [hG, hR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  all_goals nlinarith

theorem unit_properties {d r : ℕ} (h : Admissible d r) :
    1 < unit d r ∧ unit d r ^ 2 - (ell d r : ℝ) * unit d r + 1 = 0 ∧
      1 < eta d r := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hlev : 5 ≤ level d r := level_ge_five h
  have hell : 3 ≤ ell d r := by simp only [ell]; omega
  have hdisc : 0 ≤ (ell d r : ℝ) ^ 2 - 4 := by
    have : (3 : ℝ) ≤ (ell d r : ℝ) := by exact_mod_cast hell
    nlinarith
  have hsq : (Real.sqrt ((ell d r : ℝ) ^ 2 - 4)) ^ 2 =
      (ell d r : ℝ) ^ 2 - 4 := Real.sq_sqrt hdisc
  have hu1 : 1 < unit d r := by
    unfold unit
    have hnon := Real.sqrt_nonneg ((ell d r : ℝ) ^ 2 - 4)
    have : (3 : ℝ) ≤ (ell d r : ℝ) := by exact_mod_cast hell
    linarith
  have hquad : unit d r ^ 2 - (ell d r : ℝ) * unit d r + 1 = 0 := by
    unfold unit
    nlinarith
  refine ⟨hu1, hquad, ?_⟩
  unfold eta
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hru : (r : ℝ) / unit d r < (r : ℝ) := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < unit d r)]
    nlinarith
  have hgapNat : 2 * r + 2 ≤ d := by omega
  have hgap : (2 : ℝ) ≤ (d : ℝ) - 2 * r := by
    have : ((2 * r + 2 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hgapNat
    push_cast at this
    linarith
  have hw : 1 < (d : ℝ) - r - (r : ℝ) / unit d r := by linarith
  have hw2 : 1 < ((d : ℝ) - r - (r : ℝ) / unit d r) ^ 2 := by nlinarith
  nlinarith [hu1, hw2]

theorem eta_from_gamma {d r : ℕ} (h : Admissible d r) :
    eta d r = (gamma d r 1 0 : ℝ) * unit d r + (gamma d r 1 1 : ℝ) := by
  have h10 : gamma d r 1 0 = ((d : ℤ) - r) ^ 2 - (r : ℤ) ^ 2 := by
    simp only [gamma, beta, alpha, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      pow_two]
    ring
  have h11 : gamma d r 1 1 = (ell d r : ℤ) * (r : ℤ) ^ 2 - 2 * (r : ℤ) * ((d : ℤ) - r) := by
    simp only [gamma, beta, alpha, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      pow_two]
    ring
  rw [h10, h11]
  push_cast
  unfold eta
  have hu := (unit_properties h).2.1
  have hu1 := (unit_properties h).1
  have hu0 : unit d r ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < unit d r)
  field_simp
  nlinarith [hu]


private lemma eta_minus_sq {d r : ℕ} (h : Admissible d r) :
    (eta d r - 1) ^ 2 = (d : ℝ) ^ 2 * (cofactor d r : ℝ) * eta d r := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hlev : 5 ≤ level d r := level_ge_five h
  have hell : 3 ≤ ell d r := by simp only [ell]; omega
  have hdisc : 0 ≤ (ell d r : ℝ) ^ 2 - 4 := by
    have : (3 : ℝ) ≤ (ell d r : ℝ) := by exact_mod_cast hell
    nlinarith
  set q : ℝ := Real.sqrt ((ell d r : ℝ) ^ 2 - 4) with hqdef
  have hq2 : q ^ 2 = (ell d r : ℝ) ^ 2 - 4 := by
    rw [hqdef]
    exact Real.sq_sqrt hdisc
  have hunit : unit d r = ((ell d r : ℝ) + q) / 2 := by
    rw [unit, hqdef]
  have hconR : (r : ℝ) ^ 2 + ((d : ℝ) - r) ^ 2 -
      (ell d r : ℝ) * (r : ℝ) * ((d : ℝ) - r) = 1 := by
    exact_mod_cast principal_conic h
  have hcoR : (cofactor d r : ℝ) = (ell d r : ℝ) - 2 := by
    have hco : (cofactor d r : ℤ) = (ell d r : ℤ) - 2 := by
      have : (cofactor d r : ℤ) = (level d r : ℤ) - 4 := by
        simp only [cofactor]
        exact Nat.cast_sub (by omega)
      have hell' : (ell d r : ℤ) = (level d r : ℤ) - 2 := by
        simp only [ell]
        exact Nat.cast_sub (by omega)
      omega
    exact_mod_cast hco
  have hlevelR : (level d r : ℝ) = (ell d r : ℝ) + 2 := by
    have hell' : (ell d r : ℤ) = (level d r : ℤ) - 2 := by
      simp only [ell]
      exact Nat.cast_sub (by omega)
    have : (level d r : ℤ) = (ell d r : ℤ) + 2 := by omega
    exact_mod_cast this
  have hliR : (level d r : ℝ) * (r : ℝ) * ((d : ℝ) - r) = (d : ℝ) ^ 2 - 1 := by
    have hli := level_identity h
    have hli' : ((level d r * r * (d - r) : ℕ) : ℝ) = ((d ^ 2 - 1 : ℕ) : ℝ) := by
      exact_mod_cast hli
    have hdr : ((d - r : ℕ) : ℝ) = (d : ℝ) - r := Nat.cast_sub (by omega)
    push_cast at hli'
    rw [hdr] at hli'
    have hd2 : (1 : ℕ) ≤ d ^ 2 := by
      have : 1 ≤ d := by omega
      nlinarith
    rw [Nat.cast_sub hd2] at hli'
    push_cast at hli'
    exact hli'
  set s : ℝ := (d : ℝ) - r with hs
  have hdrs : (d : ℝ) = s + r := by rw [hs]; ring
  have hconR' : (r : ℝ) ^ 2 + s ^ 2 - (ell d r : ℝ) * (r : ℝ) * s = 1 := by
    rw [hs]
    simpa using hconR
  simp only [eta, hunit, hcoR, hdrs]
  have huq : (ell d r : ℝ) + q ≠ 0 := by nlinarith
  have hu0 : ((ell d r : ℝ) + q) / 2 ≠ 0 := by positivity
  field_simp [hu0, huq]
  linear_combination (-6 * (ell d r : ℝ)^2 * (r : ℝ)^2 * s^2 - 12 * (ell d r : ℝ)^2 * (r : ℝ) * s^3 + (ell d r : ℝ)^2 * s^4 - 2 * (ell d r : ℝ) * q * (r : ℝ)^2 * s^2 - 4 * (ell d r : ℝ) * q * (r : ℝ) * s^3 + 2 * (ell d r : ℝ) * q * s^4 + 8 * (ell d r : ℝ) * (r : ℝ)^3 * s + 28 * (ell d r : ℝ) * (r : ℝ)^2 * s^2 + 8 * (ell d r : ℝ) * (r : ℝ) * s^3 + 12 * (ell d r : ℝ) * s^4 - 12 * (ell d r : ℝ) * s^2 + q^2 * s^4 + 4 * q * (r : ℝ)^2 * s^2 + 4 * q * s^4 - 4 * q * s^2 - 16 * (r : ℝ)^3 * s - 8 * (r : ℝ)^2 * s^2 - 16 * (r : ℝ) * s^3 + 16 * (r : ℝ) * s - 4 * s^4 + 4) * hq2 + (8 * (ell d r : ℝ)^3 * (r : ℝ) * s + 16 * (ell d r : ℝ)^3 * s^2 + 8 * (ell d r : ℝ)^2 * q * (r : ℝ) * s + 16 * (ell d r : ℝ)^2 * q * s^2 - 8 * (ell d r : ℝ)^2 * (r : ℝ)^2 - 32 * (ell d r : ℝ)^2 * (r : ℝ) * s - 8 * (ell d r : ℝ)^2 * s^2 - 8 * (ell d r : ℝ)^2 - 8 * (ell d r : ℝ) * q * (r : ℝ)^2 - 32 * (ell d r : ℝ) * q * (r : ℝ) * s - 8 * (ell d r : ℝ) * q * s^2 - 8 * (ell d r : ℝ) * q + 16 * (ell d r : ℝ) * (r : ℝ)^2 - 16 * (ell d r : ℝ) * (r : ℝ) * s - 48 * (ell d r : ℝ) * s^2 + 16 * q * (r : ℝ)^2 - 16 * q * s^2 + 16 * (r : ℝ)^2 + 64 * (r : ℝ) * s + 16 * s^2 + 16) * hconR'

private lemma eta_plus_sq {d r : ℕ} (h : Admissible d r) :
    (eta d r + 1) ^ 2 = (gap d r : ℝ) ^ 2 * (level d r : ℝ) * eta d r := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hlev : 5 ≤ level d r := level_ge_five h
  have hell : 3 ≤ ell d r := by simp only [ell]; omega
  have hdisc : 0 ≤ (ell d r : ℝ) ^ 2 - 4 := by
    have : (3 : ℝ) ≤ (ell d r : ℝ) := by exact_mod_cast hell
    nlinarith
  set q : ℝ := Real.sqrt ((ell d r : ℝ) ^ 2 - 4) with hqdef
  have hq2 : q ^ 2 = (ell d r : ℝ) ^ 2 - 4 := by
    rw [hqdef]
    exact Real.sq_sqrt hdisc
  have hunit : unit d r = ((ell d r : ℝ) + q) / 2 := by
    rw [unit, hqdef]
  have hconR : (r : ℝ) ^ 2 + ((d : ℝ) - r) ^ 2 -
      (ell d r : ℝ) * (r : ℝ) * ((d : ℝ) - r) = 1 := by
    exact_mod_cast principal_conic h
  have hlevelR : (level d r : ℝ) = (ell d r : ℝ) + 2 := by
    have hell' : (ell d r : ℤ) = (level d r : ℤ) - 2 := by
      simp only [ell]
      exact Nat.cast_sub (by omega)
    have : (level d r : ℤ) = (ell d r : ℤ) + 2 := by omega
    exact_mod_cast this
  have hliR : (level d r : ℝ) * (r : ℝ) * ((d : ℝ) - r) = (d : ℝ) ^ 2 - 1 := by
    have hli := level_identity h
    have hli' : ((level d r * r * (d - r) : ℕ) : ℝ) = ((d ^ 2 - 1 : ℕ) : ℝ) := by
      exact_mod_cast hli
    have hdr : ((d - r : ℕ) : ℝ) = (d : ℝ) - r := Nat.cast_sub (by omega)
    push_cast at hli'
    rw [hdr] at hli'
    have hd2 : (1 : ℕ) ≤ d ^ 2 := by
      have : 1 ≤ d := by omega
      nlinarith
    rw [Nat.cast_sub hd2] at hli'
    push_cast at hli'
    exact hli'
  set s : ℝ := (d : ℝ) - r with hs
  have hdrs : (d : ℝ) = s + r := by rw [hs]; ring
  have hconR' : (r : ℝ) ^ 2 + s ^ 2 - (ell d r : ℝ) * (r : ℝ) * s = 1 := by
    rw [hs]
    simpa using hconR
  have hgapR : (gap d r : ℝ) = s - r := by
    rw [hs]
    simp only [gap]
    push_cast
    ring
  simp only [eta, hunit, hgapR, hdrs, hlevelR]
  have huq : (ell d r : ℝ) + q ≠ 0 := by nlinarith
  have hu0 : ((ell d r : ℝ) + q) / 2 ≠ 0 := by positivity
  field_simp [hu0, huq]
  linear_combination (-6 * (ell d r : ℝ)^2 * (r : ℝ)^2 * s^2 + 12 * (ell d r : ℝ)^2 * (r : ℝ) * s^3 + (ell d r : ℝ)^2 * s^4 - 2 * (ell d r : ℝ) * q * (r : ℝ)^2 * s^2 + 4 * (ell d r : ℝ) * q * (r : ℝ) * s^3 + 2 * (ell d r : ℝ) * q * s^4 + 8 * (ell d r : ℝ) * (r : ℝ)^3 * s - 28 * (ell d r : ℝ) * (r : ℝ)^2 * s^2 + 8 * (ell d r : ℝ) * (r : ℝ) * s^3 - 12 * (ell d r : ℝ) * s^4 + 12 * (ell d r : ℝ) * s^2 + q^2 * s^4 - 4 * q * (r : ℝ)^2 * s^2 - 4 * q * s^4 + 4 * q * s^2 + 16 * (r : ℝ)^3 * s - 8 * (r : ℝ)^2 * s^2 + 16 * (r : ℝ) * s^3 - 16 * (r : ℝ) * s - 4 * s^4 + 4) * hq2 + (8 * (ell d r : ℝ)^3 * (r : ℝ) * s - 16 * (ell d r : ℝ)^3 * s^2 + 8 * (ell d r : ℝ)^2 * q * (r : ℝ) * s - 16 * (ell d r : ℝ)^2 * q * s^2 - 8 * (ell d r : ℝ)^2 * (r : ℝ)^2 + 32 * (ell d r : ℝ)^2 * (r : ℝ) * s - 8 * (ell d r : ℝ)^2 * s^2 - 8 * (ell d r : ℝ)^2 - 8 * (ell d r : ℝ) * q * (r : ℝ)^2 + 32 * (ell d r : ℝ) * q * (r : ℝ) * s - 8 * (ell d r : ℝ) * q * s^2 - 8 * (ell d r : ℝ) * q - 16 * (ell d r : ℝ) * (r : ℝ)^2 - 16 * (ell d r : ℝ) * (r : ℝ) * s + 48 * (ell d r : ℝ) * s^2 - 16 * q * (r : ℝ)^2 + 16 * q * s^2 + 16 * (r : ℝ)^2 - 64 * (r : ℝ) * s + 16 * s^2 + 16) * hconR'

theorem normalizer_identities {d r : ℕ} (h : Admissible d r) :
    originValue d r - (originValue d r)⁻¹ =
        (d : ℂ) * (Real.sqrt (cofactor d r) : ℂ) ∧
      originValue d r + (originValue d r)⁻¹ = (gap d r : ℂ) * rootLevel d r := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have htuple := unit_properties h
  have heta1 : 1 < eta d r := htuple.2.2
  have heta0 : 0 < eta d r := by linarith
  set R : ℝ := Real.sqrt (eta d r) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact Real.sqrt_pos.mpr heta0
  have hRsq : R ^ 2 = eta d r := by
    rw [hRdef]
    exact Real.sq_sqrt (le_of_lt heta0)
  have hco_pos : (0 : ℝ) < (cofactor d r : ℝ) := by
    have h := level_ge_five h
    have : 0 < cofactor d r := by simp only [cofactor]; omega
    exact_mod_cast this
  have hco_sq : (Real.sqrt (cofactor d r : ℝ)) ^ 2 = (cofactor d r : ℝ) :=
    Real.sq_sqrt (le_of_lt hco_pos)
  have hd_pos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hlev_pos : (0 : ℝ) < (level d r : ℝ) := by
    have : 0 < level d r := by have := level_ge_five h; omega
    exact_mod_cast this
  have hlev_sq : (Real.sqrt (level d r : ℝ)) ^ 2 = (level d r : ℝ) :=
    Real.sq_sqrt (le_of_lt hlev_pos)
  have hgap_pos : (0 : ℝ) < (gap d r : ℝ) := by
    have hgap_nat : 0 < d - 2 * r := by omega
    have hgapR : (gap d r : ℝ) = (d : ℝ) - 2 * r := by
      simp only [gap]
      push_cast
      ring
    have hcast : ((d - 2 * r : ℕ) : ℝ) = (d : ℝ) - 2 * r := by
      have h := Nat.cast_sub (R := ℝ) (by omega : 2 * r ≤ d)
      push_cast at h
      exact h
    rw [hgapR, ← hcast]
    exact_mod_cast hgap_nat
  have hminus_real : R - R⁻¹ = (d : ℝ) * Real.sqrt (cofactor d r : ℝ) := by
    have hminus := eta_minus_sq h
    have hR0 : R ≠ 0 := ne_of_gt hRpos
    have hsqx : (R - R⁻¹) ^ 2 =
        ((d : ℝ) * Real.sqrt (cofactor d r : ℝ)) ^ 2 := by
      field_simp [hR0]
      rw [hRsq, hco_sq, hminus]
      ring
    have hRgt1 : 1 < R := by nlinarith [hRpos, hRsq, heta1]
    have hx_nn : 0 ≤ R - R⁻¹ := by
      have hinv : R⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hRpos]
        linarith
      linarith
    have hy_pos : 0 < (d : ℝ) * Real.sqrt (cofactor d r : ℝ) := by positivity
    nlinarith [hsqx, hx_nn, hy_pos]
  have hplus_real : R + R⁻¹ = (gap d r : ℝ) * Real.sqrt (level d r : ℝ) := by
    have hplus := eta_plus_sq h
    have hR0 : R ≠ 0 := ne_of_gt hRpos
    have hsqx : (R + R⁻¹) ^ 2 =
        ((gap d r : ℝ) * Real.sqrt (level d r : ℝ)) ^ 2 := by
      field_simp [hR0]
      rw [hRsq, hlev_sq, hplus]
      ring
    have hx_pos : 0 < R + R⁻¹ := by positivity
    have hy_pos : 0 < (gap d r : ℝ) * Real.sqrt (level d r : ℝ) := by positivity
    nlinarith [hsqx, hx_pos, hy_pos]
  constructor
  · have hcast := congrArg (fun x : ℝ => (x : ℂ)) hminus_real
    simpa [originValue, hRdef, Complex.ofReal_inv] using hcast
  · have hcast := congrArg (fun x : ℝ => (x : ℂ)) hplus_real
    simpa [originValue, rootLevel, hRdef, Complex.ofReal_inv] using hcast

theorem rootLevel_sq {d r : ℕ} (h : Admissible d r) :
    rootLevel d r ^ 2 = (level d r : ℂ) ∧ rootLevel d r ≠ 0 := by
  have hpos : (0 : ℝ) < (level d r : ℝ) := by
    have : 0 < level d r := by have := level_ge_five h; omega
    exact_mod_cast this
  constructor
  · unfold rootLevel
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hpos)]
    norm_num
  · unfold rootLevel
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hpos))

theorem rsicConst_eq_inv_level {d r : ℕ} (h : Admissible d r) :
    rsicConst d r = (level d r : ℝ)⁻¹ := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hli := level_identity_int h
  have hliR : (level d r : ℝ) * (r : ℝ) * ((d : ℝ) - r) = (d : ℝ) ^ 2 - 1 := by
    exact_mod_cast hli
  have hA : (0 : ℝ) < (r : ℝ) * ((d : ℝ) - r) := by
    have hnat : 0 < r * (d - r) := Nat.mul_pos (by omega) (by omega)
    have hcast : ((r * (d - r) : ℕ) : ℝ) = (r : ℝ) * ((d : ℝ) - r) := by
      push_cast
      rw [Nat.cast_sub (by omega)]
    rw [← hcast]
    exact_mod_cast hnat
  have hN : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by
    have hd2 : (1 : ℕ) < d ^ 2 := by nlinarith
    have : (1 : ℝ) < (d : ℝ) ^ 2 := by exact_mod_cast hd2
    linarith
  have hmul : (level d r : ℝ) * rsicConst d r = 1 := by
    unfold rsicConst
    field_simp [ne_of_gt hN]
    nlinarith [hliR]
  have hlevel_ne : (level d r : ℝ) ≠ 0 := by
    have : 0 < level d r := by have := level_ge_five h; omega
    exact_mod_cast (ne_of_gt this)
  field_simp [hlevel_ne]
  linarith [hmul]

theorem twistScalar_coprime {d r : ℕ} (h : Admissible d r) :
    IsCoprime (twistScalar d r) (phaseModulus d : ℤ) := by
  have hliZ := level_identity_int h
  have hcd : IsCoprime (twistScalar d r) ((d : ℤ)) := by
    refine ⟨(d : ℤ) - r, (d : ℤ) - (r : ℤ) * ((d : ℤ) - r), ?_⟩
    have hbez : twistScalar d r * ((d : ℤ) - r) +
        (d : ℤ) * ((d : ℤ) - (r : ℤ) * ((d : ℤ) - r)) = 1 := by
      simp only [twistScalar]
      nlinarith [hliZ]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbez
  by_cases hEven : Even d
  · have hcodd : Odd (twistScalar d r) := by
      have hdEvenZ : Even (d : ℤ) := hEven.natCast
      have hd2Even : Even ((d : ℤ) ^ 2) := by
        simpa [pow_two] using hdEvenZ.mul_right (d : ℤ)
      have hrhsOdd : Odd ((d : ℤ) ^ 2 - 1) := hd2Even.sub_odd odd_one
      have hprodOdd : Odd ((level d r : ℤ) * (r : ℤ) * ((d : ℤ) - r)) := by
        rw [hliZ]
        exact hrhsOdd
      have hlevelOdd : Odd (level d r : ℤ) := by
        by_contra hnot
        have heven : Even (level d r : ℤ) := Int.not_odd_iff_even.mp hnot
        have hprodEven : Even ((level d r : ℤ) * (r : ℤ) * ((d : ℤ) - r)) :=
          (heven.mul_right (r : ℤ)).mul_right ((d : ℤ) - r)
        rw [hliZ] at hprodEven
        exact (Int.not_even_iff_odd.mpr hrhsOdd) hprodEven
      have hrOdd : Odd (r : ℤ) := by
        by_contra hnot
        have heven : Even (r : ℤ) := Int.not_odd_iff_even.mp hnot
        have hprodEven : Even ((level d r : ℤ) * (r : ℤ) * ((d : ℤ) - r)) :=
          (heven.mul_left (level d r : ℤ)).mul_right ((d : ℤ) - r)
        rw [hliZ] at hprodEven
        exact (Int.not_even_iff_odd.mpr hrhsOdd) hprodEven
      have hdsubOdd : Odd ((d : ℤ) - (level d r : ℤ)) := hdEvenZ.sub_odd hlevelOdd
      simpa [twistScalar, mul_comm, mul_left_comm, mul_assoc] using hrOdd.mul hdsubOdd
    have hc2 : IsCoprime (twistScalar d r) (2 : ℤ) := by
      obtain ⟨k, hk⟩ := hcodd
      refine ⟨1, -k, ?_⟩
      rw [hk]
      ring
    have hphase : ((phaseModulus d : ℕ) : ℤ) = 2 * (d : ℤ) := by
      simp [phaseModulus, hEven]
    rw [hphase]
    exact IsCoprime.mul_right hc2 hcd
  · have hphase : ((phaseModulus d : ℕ) : ℤ) = (d : ℤ) := by
      simp [phaseModulus, hEven]
    rw [hphase]
    exact hcd

end SICLean.L2r
