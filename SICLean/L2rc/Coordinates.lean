import SICLean.L2r.Gaussian

set_option autoImplicit false

/-!
# [RW26, (3)] for the rank-r period γ = β²L

All integer vectors are rows. `RWGroup` is the L2r row-lattice quotient.
The congruence kernel in [RW26, (3)] is defined separately and identified with
that lattice. Its cardinality, Gaussian, pairing, and base-L action are
conclusions, not fields of an analytic input. The defined functions descend
along quotient lifts.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2rc

abbrev IntegerPair := ℤ × ℤ
abbrev RWGroup (d r : ℕ) := L2r.RWGroup d r

def rowGamma (d r : ℕ) (u : IntegerPair) : IntegerPair :=
  L2r.rowAction (L2r.gamma d r) u

def omega (u v : IntegerPair) : ℤ := u.1 * v.2 - u.2 * v.1

/-- Exactly u ↦ uγ-u modulo N, where N=tr(γ)-2. -/
def congruenceMap (d r : ℕ) : IntegerPair →+
    (ZMod (L2r.groupOrder d r) × ZMod (L2r.groupOrder d r)) where
  toFun u := ((rowGamma d r u).1 - u.1, (rowGamma d r u).2 - u.2)
  map_zero' := by
    ext <;> simp [rowGamma, L2r.rowAction]
  map_add' := by
    intro u v
    ext <;> simp [rowGamma, L2r.rowAction] <;> ring

/-- The congruence lattice Λγ in [RW26, (3)]. -/
def lattice (d r : ℕ) : AddSubgroup IntegerPair := (congruenceMap d r).ker

def mk (d r : ℕ) : IntegerPair →+ RWGroup d r :=
  QuotientAddGroup.mk' (L2r.rowLattice (L2r.gamma d r - 1))

/-! ### Row-lattice bookkeeping -/

private lemma rowAction_mul' (M N : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    L2r.rowAction (M * N) v = L2r.rowAction N (L2r.rowAction M v) := by
  ext <;> simp [L2r.rowAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma rowAction_surjective' (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 1) :
    Function.Surjective (L2r.rowAction M) := by
  intro v
  refine ⟨L2r.rowAction M.adjugate v, ?_⟩
  rw [← rowAction_mul', Matrix.adjugate_mul, hM]
  simp [L2r.rowAction]

private lemma rowLattice_mul' (M N : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 1) :
    L2r.rowLattice (M * N) = L2r.rowLattice N := by
  ext v
  change (∃ w, L2r.rowAction (M * N) w = v) ↔ ∃ w, L2r.rowAction N w = v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨L2r.rowAction M w, (rowAction_mul' M N w).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := rowAction_surjective' M hM w
    exact ⟨z, by rw [rowAction_mul', hz]⟩

private lemma cofactor_cast_l2r {d r : ℕ} (h : L2r.Admissible d r) :
    (L2r.cofactor d r : ℤ) = (L2r.ell d r : ℤ) - 2 := by
  have hlev : 5 ≤ L2r.level d r := L2r.level_ge_five h
  have h1 : (L2r.cofactor d r : ℤ) = (L2r.level d r : ℤ) - 4 := by
    simp only [L2r.cofactor]
    exact Nat.cast_sub (by omega)
  have h2 : (L2r.ell d r : ℤ) = (L2r.level d r : ℤ) - 2 := by
    simp only [L2r.ell]
    exact Nat.cast_sub (by omega)
  omega

private lemma longModulus_cast_l2r {d r : ℕ} (h : L2r.Admissible d r) :
    (L2r.longModulus d r : ℤ) = (d : ℤ) * ((L2r.ell d r : ℤ) - 2) := by
  rw [L2r.longModulus, Nat.cast_mul, cofactor_cast_l2r h]

private lemma rowLattice_mem_iff' {d r : ℕ} (h : L2r.Admissible d r) (v : ℤ × ℤ) :
    v ∈ L2r.rowLattice (L2r.gamma d r - 1) ↔
      (d : ℤ) ∣ v.1 ∧ (L2r.longModulus d r : ℤ) ∣ v.1 + v.2 := by
  rw [L2r.gamma_sub_one h, ← Matrix.mul_smul,
    rowLattice_mul' _ _ (L2r.gamma_arithmetic h).2.1]
  have hlong : (L2r.longModulus d r : ℤ) = (d : ℤ) * ((L2r.ell d r : ℤ) - 2) :=
    longModulus_cast_l2r h
  have hrow (k : ℤ × ℤ) :
      L2r.rowAction ((d : ℤ) • (L2r.alpha d r - 1)) k =
        ((d : ℤ) * (((L2r.ell d r : ℤ) - 1) * k.1 + k.2),
          (L2r.longModulus d r : ℤ) * k.1 -
            (d : ℤ) * (((L2r.ell d r : ℤ) - 1) * k.1 + k.2)) := by
    ext <;> simp [L2r.rowAction, L2r.alpha, Matrix.sub_apply, Matrix.smul_apply, hlong] <;>
      ring
  change (∃ k, L2r.rowAction ((d : ℤ) • (L2r.alpha d r - 1)) k = v) ↔ _
  constructor
  · rintro ⟨k, rfl⟩
    rw [hrow]
    exact ⟨⟨((L2r.ell d r : ℤ) - 1) * k.1 + k.2, rfl⟩, ⟨k.1, by simp⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨(y, x - ((L2r.ell d r : ℤ) - 1) * y), ?_⟩
    rw [hrow]
    ext <;> dsimp
    · linear_combination -hx
    · linear_combination hx - hy

private lemma coordinate_add' (d r : ℕ) (a b c e : ℤ) :
    L2r.coordinate d r a b + L2r.coordinate d r c e =
      L2r.coordinate d r (a + c) (b + e) := by
  ext <;> simp [L2r.coordinate, Prod.fst_add, Prod.snd_add] <;> push_cast <;> ring

private lemma rowAction_smul' (c : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    L2r.rowAction (c • M) v = c • L2r.rowAction M v := by
  ext <;> simp [L2r.rowAction, Matrix.smul_apply] <;> ring

private lemma rwNumerator_mem_iff' {d r : ℕ} (h : L2r.Admissible d r) (x y : ℤ) :
    L2r.rwNumerator d r x y ∈ L2r.rowLattice (L2r.gamma d r - 1) ↔
      (d : ℤ) ∣ x ∧ (L2r.longModulus d r : ℤ) ∣ y := by
  rw [rowLattice_mem_iff' h]
  have hco := cofactor_cast_l2r h
  have hlong : (L2r.longModulus d r : ℤ) = (d : ℤ) * (L2r.cofactor d r : ℤ) := by
    simp only [L2r.longModulus, Nat.cast_mul]
  have hnum : L2r.rwNumerator d r x y =
      (-L2r.gap d r * x + ((d : ℤ) - r) * y,
        (((L2r.ell d r : ℤ) - 1) * ((d : ℤ) - r) - r) * x +
          ((r : ℤ) - (L2r.ell d r : ℤ) * ((d : ℤ) - r)) * y) := by
    ext <;> simp [L2r.rwNumerator, L2r.rwIndexMatrix, L2r.rowAction] <;> ring
  have hinv : L2r.rowAction (L2r.rwIndexMatrix d r).adjugate
      (L2r.rwNumerator d r x y) = (x, y) := by
    rw [L2r.rwNumerator, ← rowAction_mul', Matrix.mul_adjugate,
      L2r.rwIndexMatrix_det h, one_smul]
    simp [L2r.rowAction]
  have hinv1 : x =
      ((r : ℤ) - ((L2r.ell d r : ℤ) - 1) * ((d : ℤ) - r)) *
          (L2r.rwNumerator d r x y).1 - ((d : ℤ) - r) *
          ((L2r.rwNumerator d r x y).1 + (L2r.rwNumerator d r x y).2) := by
    have hh := congrArg Prod.fst hinv
    simp [L2r.rowAction, L2r.rwIndexMatrix, Matrix.adjugate_fin_two] at hh
    linear_combination -hh
  have hinv2 : y =
      -(L2r.cofactor d r : ℤ) * ((d : ℤ) - r) * (L2r.rwNumerator d r x y).1 -
        L2r.gap d r * ((L2r.rwNumerator d r x y).1 + (L2r.rwNumerator d r x y).2) := by
    have hh := congrArg Prod.snd hinv
    simp [L2r.rowAction, L2r.rwIndexMatrix, Matrix.adjugate_fin_two] at hh
    rw [hco]
    simp only [L2r.gap] at hh ⊢
    linear_combination -hh
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨t, ht⟩⟩
    constructor
    · refine ⟨((r : ℤ) - ((L2r.ell d r : ℤ) - 1) * ((d : ℤ) - r)) * k -
        ((d : ℤ) - r) * (L2r.cofactor d r : ℤ) * t, ?_⟩
      rw [hinv1, ht, hk, hlong]
      ring
    · refine ⟨-((d : ℤ) - r) * k - L2r.gap d r * t, ?_⟩
      rw [hinv2, ht, hk, hlong]
      ring
  · rintro ⟨⟨k, rfl⟩, ⟨t, rfl⟩⟩
    rw [hnum]
    dsimp
    constructor
    · refine ⟨-L2r.gap d r * k + ((d : ℤ) - r) * (L2r.cofactor d r : ℤ) * t, ?_⟩
      rw [hlong]
      ring
    · refine ⟨((d : ℤ) - r) * k +
        ((r : ℤ) - ((L2r.ell d r : ℤ) - 1) * ((d : ℤ) - r)) * t, ?_⟩
      rw [hlong, hco]
      simp only [L2r.gap]
      ring

private lemma rwNumerator_sub' (d r : ℕ) (x y X Y : ℤ) :
    L2r.rwNumerator d r (x - X) (y - Y) =
      L2r.rwNumerator d r x y - L2r.rwNumerator d r X Y := by
  exact (L2r.rowActionHom (L2r.rwIndexMatrix d r)).map_sub (x, y) (X, Y)

private lemma val_sub_dvd' (N : ℕ) [NeZero N] (x : ℤ) :
    (N : ℤ) ∣ (((x : ZMod N).val : ℕ) : ℤ) - x := by
  have hv : (((x : ZMod N).val : ℕ) : ℤ) = x % (N : ℤ) := ZMod.val_intCast x
  refine ⟨-(x / (N : ℤ)), ?_⟩
  rw [hv]
  linarith [Int.emod_add_mul_ediv x (N : ℤ)]

private lemma rowGamma_sub_one_apply {d r : ℕ} (u : ℤ × ℤ) :
    L2r.rowAction (L2r.gamma d r - 1) u = rowGamma d r u - u := by
  ext <;> simp [rowGamma, L2r.rowAction, Matrix.sub_apply, Matrix.one_apply] <;> ring

theorem lattice_mem_iff (d r : ℕ) (u : IntegerPair) :
    u ∈ lattice d r ↔
      (L2r.groupOrder d r : ℤ) ∣ (rowGamma d r u).1 - u.1 ∧
      (L2r.groupOrder d r : ℤ) ∣ (rowGamma d r u).2 - u.2 := by
  rw [lattice, AddMonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : ((rowGamma d r u).1 : ZMod (L2r.groupOrder d r)) -
        (u.1 : ZMod (L2r.groupOrder d r)) = 0 := congrArg Prod.fst h
    have h2 : ((rowGamma d r u).2 : ZMod (L2r.groupOrder d r)) -
        (u.2 : ZMod (L2r.groupOrder d r)) = 0 := congrArg Prod.snd h
    constructor
    · have hh1 := (ZMod.intCast_eq_intCast_iff_dvd_sub (rowGamma d r u).1 u.1
        (L2r.groupOrder d r)).mp (sub_eq_zero.mp h1)
      exact Int.dvd_neg.mp (by simpa only [neg_sub] using hh1)
    · have hh2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (rowGamma d r u).2 u.2
        (L2r.groupOrder d r)).mp (sub_eq_zero.mp h2)
      exact Int.dvd_neg.mp (by simpa only [neg_sub] using hh2)
  · rintro ⟨h1, h2⟩
    ext
    · change ((rowGamma d r u).1 : ZMod (L2r.groupOrder d r)) -
        (u.1 : ZMod (L2r.groupOrder d r)) = 0
      rw [sub_eq_zero]
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
        (by simpa only [neg_sub] using Int.dvd_neg.mpr h1)
    · change ((rowGamma d r u).2 : ZMod (L2r.groupOrder d r)) -
        (u.2 : ZMod (L2r.groupOrder d r)) = 0
      rw [sub_eq_zero]
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
        (by simpa only [neg_sub] using Int.dvd_neg.mpr h2)

private lemma lattice_mem_iff_rowLattice {d r : ℕ} (h : L2r.Admissible d r)
    (u : ℤ × ℤ) :
    u ∈ lattice d r ↔ u ∈ L2r.rowLattice (L2r.gamma d r - 1) := by
  set s : ℤ := (d : ℤ) - r with hs
  set L : ℤ := (L2r.ell d r : ℤ) with hL
  set K : ℤ := L - 2 with hK
  have hcof : (L2r.cofactor d r : ℤ) = K := by
    rw [hK, hL]
    exact cofactor_cast_l2r h
  have hlong : (L2r.longModulus d r : ℤ) = (d : ℤ) * K := by
    rw [L2r.longModulus, Nat.cast_mul, hcof]
  have hgo : (L2r.groupOrder d r : ℤ) = (d : ℤ) * ((d : ℤ) * K) := by
    rw [L2r.groupOrder, Nat.cast_mul, Nat.cast_pow, hcof]
    ring
  have hd0 : (d : ℤ) ≠ 0 := by
    have := h.main_range
    omega
  have hK0 : K ≠ 0 := by
    rw [hK, hL]
    have := L2r.level_ge_five h
    have : (5 : ℤ) ≤ (L2r.level d r : ℤ) := by exact_mod_cast ‹5 ≤ L2r.level d r›
    have hell : (L2r.ell d r : ℤ) = (L2r.level d r : ℤ) - 2 := by
      simp only [L2r.ell]
      exact Nat.cast_sub (by omega)
    rw [hell]
    omega
  have hcon : (r : ℤ) ^ 2 + s ^ 2 - L * (r : ℤ) * s = 1 := by
    rw [hs, hL]
    exact L2r.principal_conic h
  have hcon' : (r : ℤ) ^ 2 + ((d : ℤ) - r) ^ 2 - L * (r : ℤ) * ((d : ℤ) - r) = 1 := by
    simpa [hs] using hcon
  set R : Matrix (Fin 2) (Fin 2) ℤ := L2r.beta d r * (L2r.alpha d r - 1) with hRdef
  have hR00 : R 0 0 = s * (L - 1) - r := by
    rw [hRdef]
    simp [L2r.beta, L2r.alpha, Matrix.mul_apply, Fin.sum_univ_two, hs, hL]
    ring
  have hR01 : R 0 1 = (r : ℤ) - s := by
    rw [hRdef]
    simp [L2r.beta, L2r.alpha, Matrix.mul_apply, Fin.sum_univ_two, hs, hL]
    ring
  have hR10 : R 1 0 = s - r := by
    rw [hRdef]
    simp [L2r.beta, L2r.alpha, Matrix.mul_apply, Fin.sum_univ_two, hs, hL]
    ring
  have hR11 : R 1 1 = (r : ℤ) * (L - 1) - s := by
    rw [hRdef]
    simp [L2r.beta, L2r.alpha, Matrix.mul_apply, Fin.sum_univ_two, hs, hL]
    ring
  set a : ℤ := u.1 with ha
  set b : ℤ := u.2 with hb
  set u1 : ℤ := a * R 0 0 + b * R 1 0 with hu1
  set u2 : ℤ := a * R 0 1 + b * R 1 1 with hu2
  have hRrow : L2r.rowAction R u = (u1, u2) := by
    ext <;> simp [L2r.rowAction, u1, u2, a, b]
  have hgamma : L2r.gamma d r - 1 = (d : ℤ) • R := L2r.gamma_sub_one h
  have hru : rowGamma d r u - u = ((d : ℤ) * u1, (d : ℤ) * u2) := by
    rw [← rowGamma_sub_one_apply (d := d) (r := r) u, hgamma, rowAction_smul', hRrow]
    rfl
  have hlat : u ∈ lattice d r ↔ (d : ℤ) * K ∣ u1 ∧ (d : ℤ) * K ∣ u2 := by
    rw [lattice_mem_iff]
    have h1' : (rowGamma d r u).1 - u.1 = (d : ℤ) * u1 := congrArg Prod.fst hru
    have h2' : (rowGamma d r u).2 - u.2 = (d : ℤ) * u2 := congrArg Prod.snd hru
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1', hgo] at h1
      rw [h2', hgo] at h2
      constructor
      · exact Int.dvd_of_mul_dvd_mul_left hd0 h1
      · exact Int.dvd_of_mul_dvd_mul_left hd0 h2
    · rintro ⟨h1, h2⟩
      constructor
      · rw [h1', hgo]
        exact mul_dvd_mul_left (d : ℤ) h1
      · rw [h2', hgo]
        exact mul_dvd_mul_left (d : ℤ) h2
  have hrow : u ∈ L2r.rowLattice (L2r.gamma d r - 1) ↔
      (d : ℤ) ∣ a ∧ (d : ℤ) * K ∣ a + b := by
    rw [rowLattice_mem_iff' h u, hlong, ha, hb]
  rw [hlat, hrow]
  have hcop : IsCoprime (s - (r : ℤ)) K := by
    refine ⟨s - r, -(s * r), ?_⟩
    rw [hK]
    linear_combination hcon
  constructor
  · intro hmem
    obtain ⟨hu1d, hu2d⟩ := hmem
    have hKd : K * (d : ℤ) ∣ K * a := by
      have hE : R 1 0 * u2 - R 1 1 * u1 = K * a := by
        rw [hu1, hu2, hR00, hR01, hR10, hR11, hK, hs]
        linear_combination ((L - 2) * a) * hcon'
      rw [← hE]
      have hcomb : (d : ℤ) * K ∣ R 1 0 * u2 - R 1 1 * u1 :=
        dvd_sub (dvd_mul_of_dvd_right hu2d _) (dvd_mul_of_dvd_right hu1d _)
      simpa [mul_comm] using hcomb
    have hdiva : (d : ℤ) ∣ a :=
      Int.dvd_of_mul_dvd_mul_right hK0 (by simpa [mul_comm] using hKd)
    have hKb : K * (d : ℤ) ∣ K * b := by
      have hE : R 0 1 * u1 - R 0 0 * u2 = K * b := by
        rw [hu1, hu2, hR00, hR01, hR10, hR11, hK, hs]
        linear_combination ((L - 2) * b) * hcon'
      rw [← hE]
      have hcomb : (d : ℤ) * K ∣ R 0 1 * u1 - R 0 0 * u2 :=
        dvd_sub (dvd_mul_of_dvd_right hu1d _) (dvd_mul_of_dvd_right hu2d _)
      simpa [mul_comm] using hcomb
    have hdivb : (d : ℤ) ∣ b :=
      Int.dvd_of_mul_dvd_mul_right hK0 (by simpa [mul_comm] using hKb)
    refine ⟨hdiva, ?_⟩
    obtain ⟨B, hB⟩ := hdiva
    obtain ⟨C, hC⟩ := hdivb
    have hsum : K ∣ B + C := by
      have hu1' : K ∣ R 0 0 * B + R 1 0 * C := by
        have htmp := hu1d
        rw [hu1, hB, hC] at htmp
        have htmp' : (d : ℤ) * K ∣ (d : ℤ) * (R 0 0 * B + R 1 0 * C) := by
          convert htmp using 1 <;> ring
        exact Int.dvd_of_mul_dvd_mul_left hd0 htmp'
      have hmod : R 0 0 * B + R 1 0 * C = (s - r) * (B + C) + K * (s * B) := by
        rw [hR00, hR10, hK]
        ring
      have h1 : K ∣ (s - r) * (B + C) := by
        have hA : K ∣ (s - r) * (B + C) + K * (s * B) := by
          rwa [← hmod]
        simpa [add_sub_cancel_right] using dvd_sub hA (dvd_mul_right K (s * B))
      exact hcop.symm.dvd_of_dvd_mul_left h1
    rw [hB, hC]
    rw [show (d : ℤ) * B + (d : ℤ) * C = (d : ℤ) * (B + C) by ring]
    exact mul_dvd_mul_left (d : ℤ) hsum
  · rintro ⟨hda, hsum⟩
    obtain ⟨B, hB⟩ := hda
    have hdb : (d : ℤ) ∣ b := by
      have hdvd : (d : ℤ) ∣ a + b := dvd_trans (dvd_mul_right (d : ℤ) K) hsum
      have hda' : (d : ℤ) ∣ a := ⟨B, hB⟩
      have hb' : (d : ℤ) ∣ (a + b) - a := dvd_sub hdvd hda'
      simpa using hb'
    obtain ⟨C, hC⟩ := hdb
    have hsum' : (d : ℤ) * K ∣ a + b := hsum
    rw [hB, hC] at hsum'
    have hsum'' : K ∣ B + C := Int.dvd_of_mul_dvd_mul_left hd0 (by simpa [mul_add] using hsum')
    constructor
    · rw [hu1, hR00, hR10, hB, hC]
      rw [show (d : ℤ) * B * (s * (L - 1) - r) + (d : ℤ) * C * (s - r) =
          (d : ℤ) * ((s - r) * (B + C) + K * (s * B)) by
        rw [hK]; ring]
      exact mul_dvd_mul_left (d : ℤ) (dvd_add (dvd_mul_of_dvd_right hsum'' _) (dvd_mul_right K (s * B)))
    · rw [hu2, hR01, hR11, hB, hC]
      rw [show (d : ℤ) * B * (r - s) + (d : ℤ) * C * (r * (L - 1) - s) =
          (d : ℤ) * (-(s - r) * (B + C) + K * (r * C)) by
        rw [hK]; ring]
      exact mul_dvd_mul_left (d : ℤ)
        (dvd_add (dvd_mul_of_dvd_right (by simpa [mul_comm] using hsum'') _)
          (dvd_mul_right K (r * C)))

/-- This equality connects the original congruence definition to the actual
quotient used by `L2r.RWGroup`; it is not an assumption on F. -/
theorem lattice_eq_row_range (d r : ℕ) [Fact (L2r.Admissible d r)] :
    lattice d r = L2r.rowLattice (L2r.gamma d r - 1) := by
  ext u
  exact lattice_mem_iff_rowLattice (Fact.out : L2r.Admissible d r) u

theorem mk_eq_zero_iff (d r : ℕ) [Fact (L2r.Admissible d r)] (u : IntegerPair) :
    mk d r u = 0 ↔ u ∈ lattice d r := by
  change (QuotientAddGroup.mk u : RWGroup d r) = 0 ↔ u ∈ lattice d r
  rw [QuotientAddGroup.eq_zero_iff, ← lattice_eq_row_range]

theorem quotient_eq_iff (d r : ℕ) [Fact (L2r.Admissible d r)] (u v : IntegerPair) :
    mk d r u = mk d r v ↔ u - v ∈ lattice d r := by
  change (QuotientAddGroup.mk u : RWGroup d r) = QuotientAddGroup.mk v ↔
    u - v ∈ lattice d r
  rw [QuotientAddGroup.eq_iff_sub_mem, ← lattice_eq_row_range]

/-- The arithmetic results supply the hypotheses of [RW26, Thm. 2]. -/
theorem gamma_parameters (d r : ℕ) [Fact (L2r.Admissible d r)] :
    (L2r.gamma d r).det = 1 ∧
      (L2r.gamma d r).trace = (L2r.groupOrder d r : ℤ) + 2 ∧
      0 < L2r.gamma d r 1 0 := by
  have hgar := L2r.gamma_arithmetic (Fact.out : L2r.Admissible d r)
  refine ⟨hgar.2.2.1, hgar.2.2.2.1, ?_⟩
  rw [hgar.2.2.2.2]
  have hd : (0 : ℤ) < (d : ℤ) := by
    have := (Fact.out : L2r.Admissible d r).main_range
    omega
  have hgap : 0 < L2r.gap d r := by
    simp only [L2r.gap]
    have := (Fact.out : L2r.Admissible d r).main_range
    omega
  exact mul_pos hd hgap

/-- This repackages `grid_position` and `beta_eq_alpha_pow`.
No chosen exponent occurs in the definitions or final input. -/
theorem gamma_odd_power (d r : ℕ) [Fact (L2r.Admissible d r)] :
    ∃ m : ℕ, 1 ≤ m ∧ L2r.beta d r = L2r.alpha d r ^ m ∧
      L2r.gamma d r = L2r.alpha d r ^ (2 * m + 1) := by
  have h : L2r.Admissible d r := Fact.out
  obtain ⟨m, hm, _⟩ := L2r.grid_position h
  exact ⟨m, hm.1, L2r.beta_eq_alpha_pow h m hm.1 hm.2.1 hm.2.2⟩

/-- Forward map: the row-index homomorphism of [RW26].
The inverse is the inverse of that surjection. -/
def rwIndexEquiv (d r : ℕ) [Fact (L2r.Admissible d r)] :
    L2r.G d r ≃+ RWGroup d r where
  toFun := L2r.rwIndexMap d r
  invFun := Function.surjInv (L2r.rwIndexMap_bijective d r).2
  left_inv := Function.leftInverse_surjInv (L2r.rwIndexMap_bijective d r)
  right_inv := Function.rightInverse_surjInv (L2r.rwIndexMap_bijective d r).2
  map_add' := (L2r.rwIndexMap d r).map_add

instance rwFintype (d r : ℕ) [Fact (L2r.Admissible d r)] :
    Fintype (RWGroup d r) :=
  Fintype.ofEquiv (L2r.G d r) (rwIndexEquiv d r).toEquiv

instance rwDecidableEq (d r : ℕ) : DecidableEq (RWGroup d r) := Classical.decEq _

theorem card_RWGroup (d r : ℕ) [Fact (L2r.Admissible d r)] :
    Fintype.card (RWGroup d r) = L2r.groupOrder d r := by
  rw [← L2r.card_G]
  exact (Fintype.card_congr (rwIndexEquiv d r).toEquiv).symm

/-- Valid for every integer lift, not just the pair of ZMod.val representatives. -/
theorem rwIndexMap_coordinate (d r : ℕ) [Fact (L2r.Admissible d r)] (x y : ℤ) :
    L2r.rwIndexMap d r (L2r.coordinate d r x y) =
      mk d r (L2r.rwNumerator d r x y) := by
  letI : NeZero d := L2r.admissibleDimensionNeZero d r
  letI : NeZero (L2r.longModulus d r) := L2r.admissibleLongModulusNeZero d r
  have h : L2r.Admissible d r := Fact.out
  change QuotientAddGroup.mk (L2r.rwNumerator d r
      (L2r.coordinate d r x y).1.val (L2r.coordinate d r x y).2.val) =
    QuotientAddGroup.mk (L2r.rwNumerator d r x y)
  rw [QuotientAddGroup.eq_iff_sub_mem, ← rwNumerator_sub', rwNumerator_mem_iff' h]
  constructor
  · have h1 : (d : ℤ) ∣ (((x : ZMod d).val : ℕ) : ℤ) - x := val_sub_dvd' d x
    simpa [L2r.coordinate] using h1
  · have h2 : (L2r.longModulus d r : ℤ) ∣
        ((((y : ZMod (L2r.longModulus d r)).val : ℕ) : ℤ)) - y :=
      val_sub_dvd' (L2r.longModulus d r) y
    simpa [L2r.coordinate] using h2

private theorem e_scale' (c M : ℕ) (hc : c ≠ 0) (hM : M ≠ 0) (z : ℤ) :
    L2a.e (c * M) ((c : ℤ) * z) = L2a.e M z := by
  simp only [L2a.e]
  apply congrArg Complex.exp
  push_cast
  have hc' : ((c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hM' : ((M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hM
  field_simp

private lemma omega_beta_alpha {d r : ℕ} (h : L2r.Admissible d r) (x y X Y : ℤ) :
    omega (L2r.rowAction (L2r.beta d r * (L2r.alpha d r - 1))
        (L2r.rwNumerator d r x y)) (L2r.rwNumerator d r X Y) =
      (-(L2r.cofactor d r : ℤ) * L2r.gap d r * x * X -
          (L2r.cofactor d r : ℤ) * (r : ℤ) * (x * Y + y * X) +
          L2r.gap d r * y * Y) +
        (L2r.longModulus d r : ℤ) * (x * Y) := by
  set L : ℤ := (L2r.ell d r : ℤ) with hL
  set c : ℤ := (L2r.cofactor d r : ℤ) with hc
  have hlong : (L2r.longModulus d r : ℤ) = (d : ℤ) * c := by
    simp only [L2r.longModulus, Nat.cast_mul, hc]
  have hcof : c = L - 2 := by
    rw [hc, hL]
    exact cofactor_cast_l2r h
  have hcof0 : (L2r.cofactor d r : ℤ) = L - 2 := by
    rw [hL]
    exact cofactor_cast_l2r h
  have hcon : (r : ℤ) ^ 2 + ((d : ℤ) - r) ^ 2 - L * (r : ℤ) * ((d : ℤ) - r) = 1 := by
    rw [hL]
    exact L2r.principal_conic h
  let R : Matrix (Fin 2) (Fin 2) ℤ := L2r.beta d r * (L2r.alpha d r - 1)
  change omega (L2r.rowAction R (L2r.rwNumerator d r x y))
      (L2r.rwNumerator d r X Y) = _
  have hR00 : R 0 0 = ((d : ℤ) - r) * (L - 1) - r := by
    dsimp only [R]
    simp [L2r.beta, L2r.alpha, Matrix.mul_apply, Fin.sum_univ_two, hL]
    ring
  have hR01 : R 0 1 = (r : ℤ) - ((d : ℤ) - r) := by
    dsimp only [R]
    simp [L2r.beta, L2r.alpha, Matrix.mul_apply, Fin.sum_univ_two, hL]
    ring
  have hR10 : R 1 0 = (d : ℤ) - 2 * r := by
    dsimp only [R]
    simp [L2r.beta, L2r.alpha, Matrix.mul_apply, Fin.sum_univ_two, hL]
    ring
  have hR11 : R 1 1 = (r : ℤ) * (L - 1) - ((d : ℤ) - r) := by
    dsimp only [R]
    simp [L2r.beta, L2r.alpha, Matrix.mul_apply, Fin.sum_univ_two, hL]
    ring
  have hnum (a b : ℤ) : L2r.rwNumerator d r a b =
      (-L2r.gap d r * a + ((d : ℤ) - r) * b,
        (((L - 1) * ((d : ℤ) - r) - r) * a +
          ((r : ℤ) - L * ((d : ℤ) - r)) * b)) := by
    ext <;> simp [L2r.rwNumerator, L2r.rwIndexMatrix, L2r.rowAction, hL] <;> ring
  rw [hnum x y, hnum X Y, hlong, hcof]
  have hrow : L2r.rowAction R
      (-L2r.gap d r * x + ((d : ℤ) - r) * y,
        ((L - 1) * ((d : ℤ) - r) - r) * x +
          ((r : ℤ) - L * ((d : ℤ) - r)) * y) =
      (((-L2r.gap d r * x + ((d : ℤ) - r) * y) * R 0 0 +
          (((L - 1) * ((d : ℤ) - r) - r) * x +
            ((r : ℤ) - L * ((d : ℤ) - r)) * y) * R 1 0),
        ((-L2r.gap d r * x + ((d : ℤ) - r) * y) * R 0 1 +
          (((L - 1) * ((d : ℤ) - r) - r) * x +
            ((r : ℤ) - L * ((d : ℤ) - r)) * y) * R 1 1)) := by
    ext <;> simp [L2r.rowAction]
  rw [hrow, omega, hR00, hR01, hR10, hR11]
  simp only [L2r.gap]
  linear_combination ((L - 2) * ((r : ℤ) - ((d : ℤ) - r)) * x * X +
      (L - 2) * ((d : ℤ) - r) * x * Y - (L - 2) * (r : ℤ) * y * X -
      ((r : ℤ) - ((d : ℤ) - r)) * y * Y) * hcon

/-- Gaussian from [RW26, (3)], before taking the quotient. -/
def gaussianLift (d r : ℕ) (u : IntegerPair) : ℂ :=
  (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) *
    L2a.e (2 * L2r.groupOrder d r) (omega (rowGamma d r u) u)

/-- Positive-sign pairing from [RW26, (3)], before taking the quotient. -/
def pairingLift (d r : ℕ) (u v : IntegerPair) : ℂ :=
  L2a.e (L2r.groupOrder d r) (omega (rowGamma d r u - u) v)

theorem gaussianLift_rwNumerator (d r : ℕ) [Fact (L2r.Admissible d r)]
    (x y : ℤ) :
    gaussianLift d r (L2r.rwNumerator d r x y) = L2r.gaussianLift d r x y := by
  simpa only [gaussianLift, omega, rowGamma] using
    (L2r.gaussian_rw_row_formula (Fact.out : L2r.Admissible d r) x y).symm

private lemma omega_smul_left (c : ℤ) (u v : ℤ × ℤ) :
    omega (c • u) v = c * omega u v := by
  simp only [omega, Prod.smul_fst, Prod.smul_snd]
  ring

private lemma rwNumerator_surjective {d r : ℕ} (h : L2r.Admissible d r) (v : ℤ × ℤ) :
    ∃ x y : ℤ, v = L2r.rwNumerator d r x y := by
  obtain ⟨w, hw⟩ := rowAction_surjective' (L2r.rwIndexMatrix d r) (L2r.rwIndexMatrix_det h) v
  exact ⟨w.1, w.2, by simpa [L2r.rwNumerator] using hw.symm⟩

theorem pairingLift_rwNumerator (d r : ℕ) [Fact (L2r.Admissible d r)]
    (x y X Y : ℤ) :
    pairingLift d r (L2r.rwNumerator d r x y) (L2r.rwNumerator d r X Y) =
      L2r.pairingLift d r x y X Y := by
  have h : L2r.Admissible d r := Fact.out
  have hd0 : (d : ℤ) ≠ 0 := by
    have := h.main_range
    omega
  have hL0 : L2r.longModulus d r ≠ 0 := NeZero.ne _
  have hNnat : L2r.groupOrder d r = d * L2r.longModulus d r := by
    simp only [L2r.groupOrder, L2r.longModulus]
    ring
  have hN : (L2r.groupOrder d r : ℤ) =
      (d : ℤ) * (L2r.longModulus d r : ℤ) := by
    exact_mod_cast hNnat
  have hgamma : L2r.gamma d r =
      1 + (d : ℤ) • (L2r.beta d r * (L2r.alpha d r - 1)) := by
    rw [← L2r.gamma_sub_one h]
    abel
  have hsub : rowGamma d r (L2r.rwNumerator d r x y) - L2r.rwNumerator d r x y =
      (d : ℤ) • L2r.rowAction (L2r.beta d r * (L2r.alpha d r - 1))
        (L2r.rwNumerator d r x y) := by
    rw [← rowGamma_sub_one_apply (d := d) (r := r) (u := L2r.rwNumerator d r x y),
      hgamma]
    simp only [add_sub_cancel_left]
    exact rowAction_smul' (d : ℤ) (L2r.beta d r * (L2r.alpha d r - 1))
      (L2r.rwNumerator d r x y)
  have hE : omega (rowGamma d r (L2r.rwNumerator d r x y) - L2r.rwNumerator d r x y)
      (L2r.rwNumerator d r X Y) =
      (d : ℤ) * (-(L2r.cofactor d r : ℤ) * L2r.gap d r * x * X -
          (L2r.cofactor d r : ℤ) * (r : ℤ) * (x * Y + y * X) +
          L2r.gap d r * y * Y) +
        (L2r.groupOrder d r : ℤ) * (x * Y) := by
    rw [hsub, omega_smul_left, omega_beta_alpha h, hN]
    ring
  rw [pairingLift, hE]
  have hdvd : (L2r.groupOrder d r : ℤ) ∣
      ((d : ℤ) * (-(L2r.cofactor d r : ℤ) * L2r.gap d r * x * X -
          (L2r.cofactor d r : ℤ) * (r : ℤ) * (x * Y + y * X) +
          L2r.gap d r * y * Y) +
        (L2r.groupOrder d r : ℤ) * (x * Y)) -
      (d : ℤ) * (-(L2r.cofactor d r : ℤ) * L2r.gap d r * x * X -
        (L2r.cofactor d r : ℤ) * (r : ℤ) * (x * Y + y * X) +
        L2r.gap d r * y * Y) := ⟨x * Y, by ring⟩
  rw [L2a.e_eq_of_dvd hdvd, hNnat]
  exact e_scale' d (L2r.longModulus d r) (by omega) hL0
    (-(L2r.cofactor d r : ℤ) * L2r.gap d r * x * X -
      (L2r.cofactor d r : ℤ) * (r : ℤ) * (x * Y + y * X) +
      L2r.gap d r * y * Y)

theorem pairingLift_eq_polarization (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u v : IntegerPair) :
    pairingLift d r u v =
      gaussianLift d r (u + v) / (gaussianLift d r u * gaussianLift d r v) := by
  have h : L2r.Admissible d r := Fact.out
  obtain ⟨x, y, hxy⟩ := rwNumerator_surjective (d := d) (r := r) h u
  obtain ⟨X, Y, hXY⟩ := rwNumerator_surjective (d := d) (r := r) h v
  rw [hxy, hXY]
  obtain ⟨x', y', hxy'⟩ := rwNumerator_surjective (d := d) (r := r) h
    (L2r.rwNumerator d r x y + L2r.rwNumerator d r X Y)
  have hsum : L2r.rwNumerator d r x y + L2r.rwNumerator d r X Y =
      L2r.rwNumerator d r (x + X) (y + Y) := by
    exact ((L2r.rowActionHom (L2r.rwIndexMatrix d r)).map_add (x, y) (X, Y)).symm
  have hpre : L2r.rwNumerator d r x' y' =
      L2r.rwNumerator d r (x + X) (y + Y) := by
    rw [← hxy', hsum]
  have hcoord : L2r.coordinate d r x' y' = L2r.coordinate d r (x + X) (y + Y) := by
    apply (L2r.rwIndexMap_bijective d r).1
    rw [rwIndexMap_coordinate, rwIndexMap_coordinate, hpre]
  rw [hxy', pairingLift_rwNumerator,
    gaussianLift_rwNumerator, gaussianLift_rwNumerator, gaussianLift_rwNumerator,
    ← L2r.pairing_formula (d := d) (r := r) x y X Y]
  rw [L2b.metricPairing, coordinate_add',
    ← L2r.gaussian_eq_lift (d := d) (r := r) x' y', hcoord,
    L2r.gaussian_eq_lift (d := d) (r := r) (x + X) (y + Y),
    L2r.gaussian_eq_lift (d := d) (r := r) x y,
    L2r.gaussian_eq_lift (d := d) (r := r) X Y]

theorem gaussianLift_periodic (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u k : IntegerPair) (hk : k ∈ lattice d r) :
    gaussianLift d r (u + k) = gaussianLift d r u := by
  have h : L2r.Admissible d r := Fact.out
  obtain ⟨x, y, hxy⟩ := rwNumerator_surjective (d := d) (r := r) h u
  rw [hxy]
  obtain ⟨x', y', hxy'⟩ := rwNumerator_surjective (d := d) (r := r) h
    (L2r.rwNumerator d r x y + k)
  have hmk : mk d r (L2r.rwNumerator d r x' y') =
      mk d r (L2r.rwNumerator d r x y) := by
    rw [← hxy', map_add, (mk_eq_zero_iff d r k).mpr hk, add_zero]
  have hcoord : L2r.coordinate d r x' y' = L2r.coordinate d r x y := by
    apply (L2r.rwIndexMap_bijective d r).1
    rw [rwIndexMap_coordinate, rwIndexMap_coordinate, hmk]
  rw [hxy', gaussianLift_rwNumerator, gaussianLift_rwNumerator,
    ← L2r.gaussian_eq_lift (d := d) (r := r) x' y',
    ← L2r.gaussian_eq_lift (d := d) (r := r) x y, hcoord]

theorem pairingLift_periodic (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u v k l : IntegerPair) (hk : k ∈ lattice d r) (hl : l ∈ lattice d r) :
    pairingLift d r (u + k) (v + l) = pairingLift d r u v := by
  have h : L2r.Admissible d r := Fact.out
  obtain ⟨x, y, hxy⟩ := rwNumerator_surjective (d := d) (r := r) h u
  obtain ⟨X, Y, hXY⟩ := rwNumerator_surjective (d := d) (r := r) h v
  rw [hxy, hXY]
  obtain ⟨x', y', hxy'⟩ := rwNumerator_surjective (d := d) (r := r) h
    (L2r.rwNumerator d r x y + k)
  obtain ⟨X', Y', hXY'⟩ := rwNumerator_surjective (d := d) (r := r) h
    (L2r.rwNumerator d r X Y + l)
  have hmk : mk d r (L2r.rwNumerator d r x' y') =
      mk d r (L2r.rwNumerator d r x y) := by
    rw [← hxy', map_add, (mk_eq_zero_iff d r k).mpr hk, add_zero]
  have hmk' : mk d r (L2r.rwNumerator d r X' Y') =
      mk d r (L2r.rwNumerator d r X Y) := by
    rw [← hXY', map_add, (mk_eq_zero_iff d r l).mpr hl, add_zero]
  have hcoord : L2r.coordinate d r x' y' = L2r.coordinate d r x y := by
    apply (L2r.rwIndexMap_bijective d r).1
    rw [rwIndexMap_coordinate, rwIndexMap_coordinate, hmk]
  have hcoord' : L2r.coordinate d r X' Y' = L2r.coordinate d r X Y := by
    apply (L2r.rwIndexMap_bijective d r).1
    rw [rwIndexMap_coordinate, rwIndexMap_coordinate, hmk']
  rw [hxy', hXY', pairingLift_rwNumerator, pairingLift_rwNumerator,
    ← L2r.pairing_formula (d := d) (r := r) x' y' X' Y',
    ← L2r.pairing_formula (d := d) (r := r) x y X Y, hcoord, hcoord']

def gaussian (d r : ℕ) [Fact (L2r.Admissible d r)] : RWGroup d r → ℂ :=
  Quotient.lift (gaussianLift d r) (by
    intro a b hab
    have hrow : -a + b ∈ L2r.rowLattice (L2r.gamma d r - 1) := by
      rw [← QuotientAddGroup.leftRel_apply]
      exact hab
    have hlat : -a + b ∈ lattice d r := by
      rwa [lattice_eq_row_range]
    have h := gaussianLift_periodic d r a (-a + b) hlat
    rw [show a + (-a + b) = b by abel] at h
    exact h.symm)

def pairing (d r : ℕ) [Fact (L2r.Admissible d r)] :
    RWGroup d r → RWGroup d r → ℂ :=
  Quotient.lift
    (fun u => Quotient.lift (pairingLift d r u) (by
      intro a b hab
      have hrow : -a + b ∈ L2r.rowLattice (L2r.gamma d r - 1) := by
        rw [← QuotientAddGroup.leftRel_apply]
        exact hab
      have hlat : -a + b ∈ lattice d r := by
        rwa [lattice_eq_row_range]
      have h := pairingLift_periodic d r u a 0 (-a + b) (zero_mem (lattice d r)) hlat
      simpa using h.symm))
    (by
      intro a b hab
      have hrow : -a + b ∈ L2r.rowLattice (L2r.gamma d r - 1) := by
        rw [← QuotientAddGroup.leftRel_apply]
        exact hab
      have hlat : -a + b ∈ lattice d r := by
        rwa [lattice_eq_row_range]
      funext v
      refine QuotientAddGroup.induction_on v ?_
      intro c
      have h := pairingLift_periodic d r a c (-a + b) 0 hlat (zero_mem (lattice d r))
      rw [show a + (-a + b) = b by abel, add_zero] at h
      exact h.symm)

theorem gaussian_mk (d r : ℕ) [Fact (L2r.Admissible d r)] (u : IntegerPair) :
    gaussian d r (mk d r u) = gaussianLift d r u := by
  rfl

theorem pairing_mk (d r : ℕ) [Fact (L2r.Admissible d r)] (u v : IntegerPair) :
    pairing d r (mk d r u) (mk d r v) = pairingLift d r u v := by
  rfl

private lemma G_eq_coordinate (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2r.G d r) :
    g = L2r.coordinate d r (g.1.val : ℤ) (g.2.val : ℤ) := by
  letI : NeZero d := L2r.admissibleDimensionNeZero d r
  letI : NeZero (L2r.longModulus d r) := L2r.admissibleLongModulusNeZero d r
  apply Prod.ext
  · simpa [L2r.coordinate] using (ZMod.natCast_zmod_val g.1).symm
  · simpa [L2r.coordinate] using (ZMod.natCast_zmod_val g.2).symm

theorem gaussian_rwIndexMap (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2r.G d r) :
    gaussian d r (L2r.rwIndexMap d r g) = L2r.gaussian d r g := by
  rw [G_eq_coordinate (d := d) (r := r) g, rwIndexMap_coordinate, gaussian_mk,
    gaussianLift_rwNumerator, ← L2r.gaussian_eq_lift (d := d) (r := r)
      ((g.1.val : ℕ) : ℤ) ((g.2.val : ℕ) : ℤ)]

theorem pairing_rwIndexMap (d r : ℕ) [Fact (L2r.Admissible d r)]
    (g k : L2r.G d r) :
    pairing d r (L2r.rwIndexMap d r g) (L2r.rwIndexMap d r k) =
      L2b.metricPairing (L2r.gaussian d r) g k := by
  rw [G_eq_coordinate (d := d) (r := r) g, G_eq_coordinate (d := d) (r := r) k,
    rwIndexMap_coordinate, rwIndexMap_coordinate, pairing_mk, pairingLift_rwNumerator]
  rw [L2r.pairing_formula (d := d) (r := r) ((g.1.val : ℕ) : ℤ) ((g.2.val : ℕ) : ℤ)
    ((k.1.val : ℕ) : ℤ) ((k.2.val : ℕ) : ℤ)]

theorem pairing_eq_polarization (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u v : RWGroup d r) :
    pairing d r u v = L2b.metricPairing (gaussian d r) u v := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  refine QuotientAddGroup.induction_on v ?_
  intro b
  change pairingLift d r a b =
    gaussian d r (mk d r a + mk d r b) /
      (gaussian d r (mk d r a) * gaussian d r (mk d r b))
  rw [← map_add, gaussian_mk, gaussian_mk, gaussian_mk, pairingLift_eq_polarization]

private lemma gaussian_eq_l2r (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u : RWGroup d r) :
    gaussian d r u = L2r.gaussian d r ((rwIndexEquiv d r).symm u) := by
  obtain ⟨g, rfl⟩ := (L2r.rwIndexMap_bijective d r).2 u
  rw [gaussian_rwIndexMap]
  have h : (rwIndexEquiv d r).symm (L2r.rwIndexMap d r g) = g := by
    change (rwIndexEquiv d r).symm ((rwIndexEquiv d r) g) = g
    exact (rwIndexEquiv d r).symm_apply_apply g
  rw [h]

private lemma pairing_eq_l2r (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u v : RWGroup d r) :
    pairing d r u v = L2b.metricPairing (L2r.gaussian d r)
      ((rwIndexEquiv d r).symm u) ((rwIndexEquiv d r).symm v) := by
  obtain ⟨g, rfl⟩ := (L2r.rwIndexMap_bijective d r).2 u
  obtain ⟨k, rfl⟩ := (L2r.rwIndexMap_bijective d r).2 v
  rw [pairing_rwIndexMap]
  have hg : (rwIndexEquiv d r).symm (L2r.rwIndexMap d r g) = g := by
    change (rwIndexEquiv d r).symm ((rwIndexEquiv d r) g) = g
    exact (rwIndexEquiv d r).symm_apply_apply g
  have hk : (rwIndexEquiv d r).symm (L2r.rwIndexMap d r k) = k := by
    change (rwIndexEquiv d r).symm ((rwIndexEquiv d r) k) = k
    exact (rwIndexEquiv d r).symm_apply_apply k
  rw [hg, hk]

theorem rw_isMetricGaussian (d r : ℕ) [Fact (L2r.Admissible d r)] :
    L2b.IsMetricGaussian (gaussian d r) := by
  have hq := L2r.concrete_isMetricGaussian (d := d) (r := r)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [gaussian_eq_l2r]
    exact hq.nonzero _
  · intro x
    rw [gaussian_eq_l2r, gaussian_eq_l2r, map_neg]
    exact hq.even _
  · intro x y z
    rw [← pairing_eq_polarization (d := d) (r := r) (u := x + y) (v := z),
      ← pairing_eq_polarization (d := d) (r := r) (u := x) (v := z),
      ← pairing_eq_polarization (d := d) (r := r) (u := y) (v := z)]
    rw [pairing_eq_l2r, pairing_eq_l2r, pairing_eq_l2r, (rwIndexEquiv d r).symm.map_add]
    exact hq.add_left _ _ _
  · intro x y z
    rw [← pairing_eq_polarization (d := d) (r := r) (u := x) (v := y + z),
      ← pairing_eq_polarization (d := d) (r := r) (u := x) (v := y),
      ← pairing_eq_polarization (d := d) (r := r) (u := x) (v := z)]
    rw [pairing_eq_l2r, pairing_eq_l2r, pairing_eq_l2r, (rwIndexEquiv d r).symm.map_add]
    exact hq.add_right _ _ _
  · intro x hx
    have h0 : (rwIndexEquiv d r).symm x = 0 := by
      apply hq.nondegenerate ((rwIndexEquiv d r).symm x)
      intro z
      have hz := hx (L2r.rwIndexMap d r z)
      rw [← pairing_eq_polarization (d := d) (r := r) (u := x)
        (v := L2r.rwIndexMap d r z), pairing_eq_l2r] at hz
      have hzz : (rwIndexEquiv d r).symm (L2r.rwIndexMap d r z) = z := by
        change (rwIndexEquiv d r).symm ((rwIndexEquiv d r) z) = z
        exact (rwIndexEquiv d r).symm_apply_apply z
      rwa [hzz] at hz
    calc x = L2r.rwIndexMap d r ((rwIndexEquiv d r).symm x) :=
          ((rwIndexEquiv d r).apply_symm_apply x).symm
      _ = L2r.rwIndexMap d r 0 := by rw [h0]
      _ = 0 := map_zero _

/-- Row multiplication by the base matrix L, called `alpha` in L2r. -/
def rowAlpha (d r : ℕ) : IntegerPair →+ IntegerPair where
  toFun := L2r.rowAction (L2r.alpha d r)
  map_zero' := by
    ext <;> simp [L2r.rowAction]
  map_add' := by
    intro u v
    ext <;> simp [L2r.rowAction] <;> ring

private lemma rwIndexMap_val (d r : ℕ) [Fact (L2r.Admissible d r)] (g : L2r.G d r) :
    L2r.rwIndexMap d r g =
      mk d r (L2r.rwNumerator d r (g.1.val : ℤ) (g.2.val : ℤ)) := by
  rfl

theorem rowAlpha_mem_lattice (d r : ℕ) [Fact (L2r.Admissible d r)]
    (u : IntegerPair) (hu : u ∈ lattice d r) :
    rowAlpha d r u ∈ lattice d r := by
  have h : L2r.Admissible d r := Fact.out
  obtain ⟨m, hm, _, hgamma⟩ := gamma_odd_power d r
  have hcomm : L2r.alpha d r * L2r.gamma d r = L2r.gamma d r * L2r.alpha d r := by
    rw [hgamma, ← pow_succ', ← pow_succ]
  rw [lattice_eq_row_range] at hu ⊢
  change ∃ w, L2r.rowAction (L2r.gamma d r - 1) w = u at hu
  obtain ⟨w, hw⟩ := hu
  refine ⟨rowAlpha d r w, ?_⟩
  rw [← hw]
  change L2r.rowAction (L2r.gamma d r - 1)
      (L2r.rowAction (L2r.alpha d r) w) =
    L2r.rowAction (L2r.alpha d r)
      (L2r.rowAction (L2r.gamma d r - 1) w)
  rw [← rowAction_mul', ← rowAction_mul']
  congr 1
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm]

/-- The lift identity is exact over ℤ, before either side is reduced modulo a
period. Thus Proposition 8 is applied to uL, not to uγ. -/
theorem rowAlpha_rwNumerator (d r : ℕ) [Fact (L2r.Admissible d r)] (x y : ℤ) :
    rowAlpha d r (L2r.rwNumerator d r x y) =
      L2r.rwNumerator d r (((L2r.ell d r : ℤ) - 1) * x + y)
        ((L2r.cofactor d r : ℤ) * x + y) := by
  have hlev : 5 ≤ L2r.level d r := L2r.level_ge_five (Fact.out : L2r.Admissible d r)
  have hell : (L2r.ell d r : ℤ) = (L2r.level d r : ℤ) - 2 := by
    simp only [L2r.ell]
    exact Nat.cast_sub (by omega)
  have hco : (L2r.cofactor d r : ℤ) = (L2r.level d r : ℤ) - 4 := by
    simp only [L2r.cofactor]
    exact Nat.cast_sub (by omega)
  ext <;>
    simp [rowAlpha, L2r.rwNumerator, L2r.rwIndexMatrix, L2r.rowAction, L2r.alpha,
      L2r.gap, L2r.longModulus, hell, hco] <;> ring

def epsilonAction (d r : ℕ) [Fact (L2r.Admissible d r)] :
    RWGroup d r →+ RWGroup d r :=
  QuotientAddGroup.lift (L2r.rowLattice (L2r.gamma d r - 1))
    ((mk d r).comp (rowAlpha d r)) (by
      intro a ha
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      change mk d r (rowAlpha d r a) = 0
      rw [mk_eq_zero_iff]
      exact rowAlpha_mem_lattice d r a (by rwa [lattice_eq_row_range]))

theorem epsilonAction_mk (d r : ℕ) [Fact (L2r.Admissible d r)] (u : IntegerPair) :
    epsilonAction d r (mk d r u) = mk d r (rowAlpha d r u) := by
  rw [epsilonAction]
  change (QuotientAddGroup.lift (L2r.rowLattice (L2r.gamma d r - 1))
    ((mk d r).comp (rowAlpha d r)) _) (u : RWGroup d r) = mk d r (rowAlpha d r u)
  rw [QuotientAddGroup.lift_mk', AddMonoidHom.comp_apply]

theorem epsilonAction_rwIndexMap (d r : ℕ) [Fact (L2r.Admissible d r)]
    (g : L2r.G d r) :
    epsilonAction d r (L2r.rwIndexMap d r g) =
      L2r.rwIndexMap d r (L2r.epsilonAut d r g) := by
  rw [rwIndexMap_val (d := d) (r := r) g, epsilonAction_mk, rowAlpha_rwNumerator]
  rw [show L2r.rwIndexMap d r (L2r.epsilonAut d r g) =
      mk d r (L2r.rwNumerator d r
        (((L2r.ell d r : ℤ) - 1) * (g.1.val : ℤ) + (g.2.val : ℤ))
        ((L2r.cofactor d r : ℤ) * (g.1.val : ℤ) + (g.2.val : ℤ))) by
    change L2r.rwIndexMap d r (L2r.coordinate d r
      (((L2r.ell d r : ℤ) - 1) * (g.1.val : ℤ) + (g.2.val : ℤ))
      ((L2r.cofactor d r : ℤ) * (g.1.val : ℤ) + (g.2.val : ℤ))) = _
    rw [rwIndexMap_coordinate]]

def sqrtOrder (d r : ℕ) : ℂ := (Real.sqrt (L2r.groupOrder d r) : ℂ)

/-- The denominator is the explicit trace-minus-two N of [RW26]. -/
def normalizedSum (d r : ℕ) [Fact (L2r.Admissible d r)]
    (f : RWGroup d r → ℂ) : ℂ :=
  (∑ u : RWGroup d r, f u) / sqrtOrder d r

/-- The downstream E is F⁺ transported by the proved row-index bijection. -/
def concreteValues (d r : ℕ) [Fact (L2r.Admissible d r)]
    (F : RWGroup d r → ℂ) : L2r.G d r → ℂ :=
  F ∘ L2r.rwIndexMap d r

theorem concreteValues_coordinate (d r : ℕ) [Fact (L2r.Admissible d r)]
    (F : RWGroup d r → ℂ) (x y : ℤ) :
    concreteValues d r F (L2r.coordinate d r x y) =
      F (mk d r (L2r.rwNumerator d r x y)) := by
  change F (L2r.rwIndexMap d r (L2r.coordinate d r x y)) =
    F (mk d r (L2r.rwNumerator d r x y))
  rw [rwIndexMap_coordinate]

theorem sqrtOrder_eq_sqrtCard_rw (d r : ℕ) [Fact (L2r.Admissible d r)] :
    sqrtOrder d r = L2b.sqrtCard (RWGroup d r) := by
  rw [sqrtOrder, L2b.sqrtCard, card_RWGroup]

theorem sqrtOrder_eq_sqrtCard (d r : ℕ) [Fact (L2r.Admissible d r)] :
    sqrtOrder d r = L2b.sqrtCard (L2r.G d r) := by
  rw [sqrtOrder, L2b.sqrtCard, L2r.card_G]

theorem normalizedSum_eq_generic (d r : ℕ) [Fact (L2r.Admissible d r)]
    (f : RWGroup d r → ℂ) :
    normalizedSum d r f = L2b.normalizedSum f := by
  rw [normalizedSum, L2b.normalizedSum, sqrtOrder_eq_sqrtCard_rw]

theorem normalizedSum_toConcrete (d r : ℕ) [Fact (L2r.Admissible d r)]
    (f : RWGroup d r → ℂ) :
    normalizedSum d r f = L2b.normalizedSum (concreteValues d r f) := by
  rw [normalizedSum_eq_generic, L2b.normalizedSum, L2b.normalizedSum]
  have hsq : L2b.sqrtCard (RWGroup d r) = L2b.sqrtCard (L2r.G d r) := by
    rw [← sqrtOrder_eq_sqrtCard_rw, sqrtOrder_eq_sqrtCard]
  rw [hsq]
  congr 1
  exact Fintype.sum_equiv (rwIndexEquiv d r).symm.toEquiv (fun u => f u)
    (fun g => concreteValues d r f g)
    (fun u => by
      change f u = f (L2r.rwIndexMap d r ((rwIndexEquiv d r).symm u))
      rw [show L2r.rwIndexMap d r ((rwIndexEquiv d r).symm u) = u from by
        change (rwIndexEquiv d r) ((rwIndexEquiv d r).symm u) = u
        exact (rwIndexEquiv d r).apply_symm_apply u])

end SICLean.L2rc
