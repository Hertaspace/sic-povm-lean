import SICLean.L2b.Main

set_option autoImplicit false

/-!
# [RW26, (3)], in the matrix quotient rather than Smith coordinates

Source: [RW26, p. 3, (3)] and [RW26, §4.3--§4.4].
The quotient, the phases and the coordinate maps are definitions. Their
properties below are proved, and are not hypotheses on the special values.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2c

abbrev IntegerPair := ℤ × ℤ

/-- Row multiplication by γ = α³, with α fixed in L2b. -/
def rowGamma (M : ℕ) (u : IntegerPair) : IntegerPair :=
  (u.1 * L2b.gamma M 0 0 + u.2 * L2b.gamma M 1 0,
   u.1 * L2b.gamma M 0 1 + u.2 * L2b.gamma M 1 1)

def omega (u v : IntegerPair) : ℤ := u.1 * v.2 - u.2 * v.1

/-! ### Entries of γ and integer expansions -/

private theorem gamma_apply00 (M : ℕ) [Fact (4 ≤ M)] :
    L2b.gamma M 0 0 = (M : ℤ) * ((M : ℤ) ^ 2 - 3 * (M : ℤ) + 1) + 1 := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 0) (L2b.gamma_sub_one (M := M))
  simp [L2b.gammaMinusOne] at h
  linarith

private theorem gamma_apply01 (M : ℕ) [Fact (4 ≤ M)] :
    L2b.gamma M 0 1 = -((M : ℤ) * ((M : ℤ) - 2)) := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 1) (L2b.gamma_sub_one (M := M))
  simp [L2b.gammaMinusOne] at h
  linarith

private theorem gamma_apply10 (M : ℕ) [Fact (4 ≤ M)] :
    L2b.gamma M 1 0 = (M : ℤ) * ((M : ℤ) - 2) := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 1 0) (L2b.gamma_sub_one (M := M))
  simp [L2b.gammaMinusOne] at h
  linarith

private theorem gamma_apply11 (M : ℕ) [Fact (4 ≤ M)] :
    L2b.gamma M 1 1 = -((M : ℤ) - 1) := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 1 1) (L2b.gamma_sub_one (M := M))
  simp [L2b.gammaMinusOne] at h
  linarith

private theorem longModulus_cast' (M : ℕ) [Fact (4 ≤ M)] :
    ((L2b.longModulus M : ℕ) : ℤ) = (M : ℤ) * ((M : ℤ) - 3) := by
  simp only [L2b.longModulus, Nat.cast_mul]
  rw [show ((L2b.cofactor M : ℕ) : ℤ) = (M : ℤ) - 3 from by
    simp only [L2b.cofactor]
    exact Nat.cast_sub (by have := Fact.out (p := 4 ≤ M); omega)]

private theorem groupOrder_cast' (M : ℕ) [Fact (4 ≤ M)] :
    (L2b.groupOrder M : ℤ) = (M : ℤ) * (L2b.longModulus M : ℤ) := by
  simp only [L2b.groupOrder, L2b.longModulus, Nat.cast_mul, Nat.cast_pow]
  ring

private theorem cofactor_cast' (M : ℕ) [Fact (4 ≤ M)] :
    ((L2b.cofactor M : ℕ) : ℤ) = (M : ℤ) - 3 := by
  simp only [L2b.cofactor]
  exact Nat.cast_sub (by have := Fact.out (p := 4 ≤ M); omega)

/-- Rescaling a phase: `e (c*M) (c*z) = e M z`. -/
private theorem e_scale (c M : ℕ) (hc : c ≠ 0) (hM : M ≠ 0) (z : ℤ) :
    L2a.e (c * M) ((c : ℤ) * z) = L2a.e M z := by
  simp only [L2a.e]
  apply congrArg Complex.exp
  push_cast
  have hc' : ((c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hM' : ((M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hM
  field_simp

/-- The standard representative is congruent to any integer lift. -/
private theorem val_sub_dvd (N : ℕ) [NeZero N] (x : ℤ) :
    (N : ℤ) ∣ (((x : ZMod N).val : ℕ) : ℤ) - x := by
  have hv : (((x : ZMod N).val : ℕ) : ℤ) = x % (N : ℤ) := ZMod.val_intCast x
  refine ⟨-(x / (N : ℤ)), ?_⟩
  rw [hv]
  linarith [Int.emod_add_mul_ediv x (N : ℤ)]

/-- Equality of coordinates from congruence of the two integer entries. -/
private theorem coordinate_congr (M : ℕ) [Fact (4 ≤ M)] {x x' y y' : ℤ}
    (hx : (M : ℤ) ∣ x - x') (hy : (L2b.longModulus M : ℤ) ∣ y - y') :
    L2b.coordinate M x y = L2b.coordinate M x' y' := by
  apply Prod.ext
  · exact (ZMod.intCast_eq_intCast_iff_dvd_sub x x' M).mpr
      (by simpa only [neg_sub] using Int.dvd_neg.mpr hx)
  · exact (ZMod.intCast_eq_intCast_iff_dvd_sub y y' (L2b.longModulus M)).mpr
      (by simpa only [neg_sub] using Int.dvd_neg.mpr hy)

/-- The two coordinates of `rowGamma u − u`, written out. -/
private theorem rowGamma_sub_one_fst (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    (rowGamma M u).1 - u.1 =
      (M : ℤ) * (u.1 * ((L2b.longModulus M : ℤ) + 1) + u.2 * ((M : ℤ) - 2)) := by
  simp only [rowGamma]
  rw [gamma_apply00, gamma_apply10, longModulus_cast']
  ring

private theorem rowGamma_sub_one_snd (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    (rowGamma M u).2 - u.2 = -((M : ℤ) * (u.1 * ((M : ℤ) - 2) + u.2)) := by
  simp only [rowGamma]
  rw [gamma_apply01, gamma_apply11]
  ring

/-- The congruence in (3): uγ − u modulo N, in both coordinates. -/
def congruenceMap (M : ℕ) :
    IntegerPair →+ (ZMod (L2b.groupOrder M) × ZMod (L2b.groupOrder M)) where
  toFun u := ((rowGamma M u).1 - u.1, (rowGamma M u).2 - u.2)
  map_zero' := by
    ext <;> simp [rowGamma]
  map_add' := by
    intro u v
    ext <;> simp [rowGamma] <;> ring

def lattice (M : ℕ) : AddSubgroup IntegerPair := (congruenceMap M).ker

abbrev RWGroup (M : ℕ) := IntegerPair ⧸ lattice M

def mk (M : ℕ) : IntegerPair →+ RWGroup M := QuotientAddGroup.mk' (lattice M)

/-- The other description of Λ in (3), with row vectors. -/
def rowLatticeMap (M : ℕ) : IntegerPair →+ IntegerPair where
  toFun u := rowGamma M u - u
  map_zero' := by
    ext <;> simp [rowGamma]
  map_add' := by
    intro u v
    ext <;> simp [rowGamma] <;> ring

/-- (a,b)S = (a,(M−2)a+b), with the two different Smith moduli. -/
def smithLift (M : ℕ) : IntegerPair →+ L2b.G M where
  toFun u := (u.1, ((M : ℤ) - 2) * u.1 + u.2)
  map_zero' := by
    ext <;> simp
  map_add' := by
    intro u v
    ext <;> simp <;> ring

theorem lattice_mem_iff (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    u ∈ lattice M ↔
      (L2b.groupOrder M : ℤ) ∣ (rowGamma M u).1 - u.1 ∧
      (L2b.groupOrder M : ℤ) ∣ (rowGamma M u).2 - u.2 := by
  rw [lattice, AddMonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : ((rowGamma M u).1 : ZMod (L2b.groupOrder M)) - (u.1 : ZMod (L2b.groupOrder M)) = 0 := by
      have hh := congrArg Prod.fst h
      exact hh
    have h2 : ((rowGamma M u).2 : ZMod (L2b.groupOrder M)) - (u.2 : ZMod (L2b.groupOrder M)) = 0 := by
      have hh := congrArg Prod.snd h
      exact hh
    constructor
    · have hh1 := (ZMod.intCast_eq_intCast_iff_dvd_sub (rowGamma M u).1 u.1
        (L2b.groupOrder M)).mp (sub_eq_zero.mp h1)
      exact Int.dvd_neg.mp (by simpa only [neg_sub] using hh1)
    · have hh2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (rowGamma M u).2 u.2
        (L2b.groupOrder M)).mp (sub_eq_zero.mp h2)
      exact Int.dvd_neg.mp (by simpa only [neg_sub] using hh2)
  · rintro ⟨h1, h2⟩
    ext
    · change ((rowGamma M u).1 : ZMod (L2b.groupOrder M)) - (u.1 : ZMod (L2b.groupOrder M)) = 0
      rw [sub_eq_zero]
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
        (by simpa only [neg_sub] using Int.dvd_neg.mpr h1)
    · change ((rowGamma M u).2 : ZMod (L2b.groupOrder M)) - (u.2 : ZMod (L2b.groupOrder M)) = 0
      rw [sub_eq_zero]
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
        (by simpa only [neg_sub] using Int.dvd_neg.mpr h2)

private theorem longModulus_ne' (M : ℕ) [Fact (4 ≤ M)] :
    ((L2b.longModulus M : ℕ) : ℤ) ≠ 0 := by
  have h4 : 4 ≤ M := Fact.out
  rw [longModulus_cast']
  have h1 : (M : ℤ) ≠ 0 := by omega
  have h2 : (M : ℤ) - 3 ≠ 0 := by omega
  exact mul_ne_zero h1 h2

/-- The congruence kernel is exactly the kernel of the Smith lift. -/
private theorem lattice_mem_iff_smith (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    u ∈ lattice M ↔
      (M : ℤ) ∣ u.1 ∧ (L2b.longModulus M : ℤ) ∣ ((M : ℤ) - 2) * u.1 + u.2 := by
  have h4 : 4 ≤ M := Fact.out
  have hM0 : (M : ℤ) ≠ 0 := by omega
  have hm0 : ((M : ℤ) - 3) ≠ 0 := by omega
  rw [lattice_mem_iff, groupOrder_cast']
  constructor
  · rintro ⟨h1, h2⟩
    rw [rowGamma_sub_one_fst] at h1
    rw [rowGamma_sub_one_snd] at h2
    have h1' : (L2b.longModulus M : ℤ) ∣
        u.1 * ((L2b.longModulus M : ℤ) + 1) + u.2 * ((M : ℤ) - 2) :=
      Int.dvd_of_mul_dvd_mul_left hM0 h1
    have h2m : (M : ℤ) * (L2b.longModulus M : ℤ) ∣
        (M : ℤ) * (-(u.1 * ((M : ℤ) - 2) + u.2)) := by
      convert h2 using 1
      ring
    have h2' : (L2b.longModulus M : ℤ) ∣ ((M : ℤ) - 2) * u.1 + u.2 := by
      have h := Int.dvd_neg.mp (Int.dvd_of_mul_dvd_mul_left hM0 h2m)
      convert h using 1
      ring
    have hcomb : (L2b.longModulus M : ℤ) ∣ ((M : ℤ) - 3) * u.1 := by
      have hsub := Int.dvd_sub h1' (dvd_mul_of_dvd_right h2' ((M : ℤ) - 2))
      convert hsub using 1
      rw [longModulus_cast']
      ring
    have hML : (L2b.longModulus M : ℤ) = ((M : ℤ) - 3) * (M : ℤ) := by
      rw [longModulus_cast']
      ring
    have hc : ((M : ℤ) - 3) * (M : ℤ) ∣ ((M : ℤ) - 3) * u.1 := by
      rw [← hML]
      exact hcomb
    exact ⟨Int.dvd_of_mul_dvd_mul_left hm0 hc, h2'⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [rowGamma_sub_one_fst]
      obtain ⟨t, ht⟩ := h1
      obtain ⟨s, hs⟩ := h2
      have hu2 : u.2 = (L2b.longModulus M : ℤ) * s - ((M : ℤ) - 2) * (M : ℤ) * t := by
        have h := hs
        rw [ht] at h
        linarith
      refine ⟨((M : ℤ) - 2) * s + t, ?_⟩
      rw [ht, hu2, longModulus_cast']
      ring
    · rw [rowGamma_sub_one_snd]
      obtain ⟨s, hs⟩ := h2
      have hs' : u.1 * ((M : ℤ) - 2) + u.2 = (L2b.longModulus M : ℤ) * s := by
        linear_combination hs
      refine ⟨-s, ?_⟩
      rw [hs']
      ring

theorem lattice_eq_row_range (M : ℕ) [Fact (4 ≤ M)] :
    lattice M = (rowLatticeMap M).range := by
  ext u
  obtain ⟨u1, u2⟩ := u
  rw [lattice_mem_iff_smith, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨hM, hL⟩
    obtain ⟨t, ht⟩ := hM
    obtain ⟨s, hs⟩ := hL
    have ht' : u1 = (M : ℤ) * t := ht
    have hs' : ((M : ℤ) - 2) * u1 + u2 = (L2b.longModulus M : ℤ) * s := hs
    have hu2 : u2 = (L2b.longModulus M : ℤ) * s - ((M : ℤ) - 2) * (M : ℤ) * t := by
      rw [ht'] at hs'
      linarith
    refine ⟨(((M : ℤ) - 2) * s - ((M : ℤ) - 1) * t,
      -(((L2b.longModulus M : ℤ)) + 1) * s + ((M : ℤ) - 2) * (M : ℤ) * t), ?_⟩
    change rowGamma M (((M : ℤ) - 2) * s - ((M : ℤ) - 1) * t,
      -(((L2b.longModulus M : ℤ)) + 1) * s + ((M : ℤ) - 2) * (M : ℤ) * t) -
      (((M : ℤ) - 2) * s - ((M : ℤ) - 1) * t,
      -(((L2b.longModulus M : ℤ)) + 1) * s + ((M : ℤ) - 2) * (M : ℤ) * t) = (u1, u2)
    ext <;> simp only [rowGamma, Prod.fst_sub, Prod.snd_sub] <;>
      simp only [gamma_apply00, gamma_apply01, gamma_apply10, gamma_apply11, ht', hu2,
        longModulus_cast'] <;> ring
  · rintro ⟨x, hx⟩
    obtain ⟨p, q⟩ := x
    rw [← hx]
    rw [show rowLatticeMap M = fun u : IntegerPair => rowGamma M u - u from rfl]
    constructor
    · simp only [Prod.fst_sub]
      rw [rowGamma_sub_one_fst]
      exact dvd_mul_right _ _
    · simp only [Prod.fst_sub, Prod.snd_sub]
      rw [rowGamma_sub_one_fst, rowGamma_sub_one_snd]
      refine ⟨(M : ℤ) * p * ((M : ℤ) - 2) + ((M : ℤ) - 1) * q, ?_⟩
      rw [longModulus_cast']
      ring

theorem lattice_eq_smith_kernel (M : ℕ) [Fact (4 ≤ M)] :
    lattice M = (smithLift M).ker := by
  ext u
  rw [lattice_mem_iff_smith, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨h1, h2⟩
    apply Prod.ext
    · simpa [smithLift] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
    · simpa [smithLift] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  · intro h
    constructor
    · have h1 : ((u.1 : ℤ) : ZMod M) = 0 := by
        have hh := congrArg Prod.fst h
        simpa [smithLift] using hh
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1
    · have h2 : ((((M : ℤ) - 2) * u.1 + u.2 : ℤ) : ZMod (L2b.longModulus M)) = 0 := by
        have hh := congrArg Prod.snd h
        simpa [smithLift] using hh
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2

private theorem smithLift_eq_zero_of_mem (M : ℕ) [Fact (4 ≤ M)] {l : IntegerPair}
    (hl : l ∈ lattice M) : smithLift M l = 0 := by
  rw [← AddMonoidHom.mem_ker, ← lattice_eq_smith_kernel]
  exact hl

theorem smithLift_surjective (M : ℕ) [Fact (4 ≤ M)] :
    Function.Surjective (smithLift M) := by
  intro g
  refine ⟨((g.1.val : ℤ), (g.2.val : ℤ) - ((M : ℤ) - 2) * (g.1.val : ℤ)), ?_⟩
  rw [show smithLift M = fun u : IntegerPair =>
    ((u.1 : ZMod M), ((M : ℤ) - 2 : ZMod (L2b.longModulus M)) * (u.1 : ZMod (L2b.longModulus M)) +
      (u.2 : ZMod (L2b.longModulus M))) from rfl]
  apply Prod.ext <;> simp

private theorem smithLift_numerator (M : ℕ) [Fact (4 ≤ M)] (g : L2b.G M) :
    smithLift M (L2b.numerator M g) = g := by
  rw [show smithLift M = fun u : IntegerPair =>
    ((u.1 : ZMod M), ((M : ℤ) - 2 : ZMod (L2b.longModulus M)) * (u.1 : ZMod (L2b.longModulus M)) +
      (u.2 : ZMod (L2b.longModulus M))) from rfl]
  apply Prod.ext <;> simp [L2b.numerator]

private theorem smithLift_coordinate (M : ℕ) [Fact (4 ≤ M)] (a : IntegerPair) :
    smithLift M a = L2b.coordinate M a.1 (((M : ℤ) - 2) * a.1 + a.2) := by
  rw [show smithLift M = fun u : IntegerPair =>
    ((u.1 : ZMod M), ((M : ℤ) - 2 : ZMod (L2b.longModulus M)) * (u.1 : ZMod (L2b.longModulus M)) +
      (u.2 : ZMod (L2b.longModulus M))) from rfl]
  apply Prod.ext <;> simp [L2b.coordinate]

/-- Descent uses the kernel theorem, not an input field. -/
def toSmith (M : ℕ) [Fact (4 ≤ M)] : RWGroup M →+ L2b.G M :=
  QuotientAddGroup.lift (lattice M) (smithLift M) (by
    intro u hu
    obtain ⟨h1, h2⟩ := (lattice_mem_iff_smith M u).mp hu
    apply Prod.ext
    · simpa [smithLift] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
    · simpa [smithLift] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2)

/-- Explicit inverse on standard integer representatives. -/
def fromSmith (M : ℕ) [Fact (4 ≤ M)] (g : L2b.G M) : RWGroup M :=
  mk M (L2b.numerator M g)

theorem toSmith_mk (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    toSmith M (mk M u) = smithLift M u := by
  change (QuotientAddGroup.lift (lattice M) (smithLift M) _) (u : RWGroup M) = smithLift M u
  rw [QuotientAddGroup.lift_mk']

theorem quotient_eq_iff (M : ℕ) [Fact (4 ≤ M)] (u v : IntegerPair) :
    mk M u = mk M v ↔ smithLift M u = smithLift M v := by
  change (u : RWGroup M) = (v : RWGroup M) ↔ smithLift M u = smithLift M v
  rw [QuotientAddGroup.eq_iff_sub_mem, lattice_eq_smith_kernel, AddMonoidHom.mem_ker,
    map_sub, sub_eq_zero]

theorem fromSmith_toSmith (M : ℕ) [Fact (4 ≤ M)] (u : RWGroup M) :
    fromSmith M (toSmith M u) = u := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  change fromSmith M (toSmith M (mk M a)) = mk M a
  rw [toSmith_mk]
  change mk M (L2b.numerator M (smithLift M a)) = mk M a
  rw [quotient_eq_iff, smithLift_numerator]

theorem toSmith_fromSmith (M : ℕ) [Fact (4 ≤ M)] (g : L2b.G M) :
    toSmith M (fromSmith M g) = g := by
  change toSmith M (mk M (L2b.numerator M g)) = g
  rw [toSmith_mk, smithLift_numerator]

/-- This formula holds for arbitrary integer lifts, including negative ones. -/
theorem fromSmith_coordinate (M : ℕ) [Fact (4 ≤ M)] (x y : ℤ) :
    fromSmith M (L2b.coordinate M x y) =
      mk M (x, y - ((M : ℤ) - 2) * x) := by
  change mk M (L2b.numerator M (L2b.coordinate M x y)) = mk M (x, y - ((M : ℤ) - 2) * x)
  rw [quotient_eq_iff, smithLift_numerator, smithLift_coordinate]
  apply Prod.ext <;> simp [L2b.coordinate]

def smithEquiv (M : ℕ) [Fact (4 ≤ M)] : RWGroup M ≃+ L2b.G M where
  toFun := toSmith M
  invFun := fromSmith M
  left_inv := fromSmith_toSmith M
  right_inv := toSmith_fromSmith M
  map_add' := (toSmith M).map_add

instance rwFintype (M : ℕ) [Fact (4 ≤ M)] : Fintype (RWGroup M) :=
  Fintype.ofEquiv (L2b.G M) (smithEquiv M).symm.toEquiv

instance rwDecidableEq (M : ℕ) : DecidableEq (RWGroup M) := Classical.decEq _

theorem card_RWGroup (M : ℕ) [Fact (4 ≤ M)] :
    Fintype.card (RWGroup M) = L2b.groupOrder M := by
  rw [← L2b.card_G]
  exact Fintype.card_congr (smithEquiv M).toEquiv

/-- The literal first formula (3), with an integer exponent on −1. -/
def gaussianLift (M : ℕ) (u : IntegerPair) : ℂ :=
  (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) *
    L2a.e (2 * L2b.groupOrder M) (omega (rowGamma M u) u)

/-- The literal second formula (3), independent of the polarization definition. -/
def pairingLift (M : ℕ) (u v : IntegerPair) : ℂ :=
  L2a.e (L2b.groupOrder M) (omega (rowGamma M u - u) v)

/-- Integer expansion of (3), before any phases or quotient representatives. -/
theorem omega_rowGamma_self (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    omega (rowGamma M u) u =
      (M : ℤ) * ((M : ℤ) - 2) *
        (u.1 ^ 2 + u.2 ^ 2 + ((M : ℤ) - 1) * u.1 * u.2) := by
  simp only [omega, rowGamma]
  rw [gamma_apply00, gamma_apply01, gamma_apply10, gamma_apply11]
  ring

theorem omega_gammaDifference (M : ℕ) [Fact (4 ≤ M)] (u v : IntegerPair) :
    omega (rowGamma M u - u) v =
      (M : ℤ) * (((M : ℤ) - 2) * (u.1 * v.1 + u.2 * v.2) +
        ((L2b.longModulus M : ℤ) + 1) * u.1 * v.2 + u.2 * v.1) := by
  simp only [omega, rowGamma, Prod.fst_sub, Prod.snd_sub]
  rw [gamma_apply00, gamma_apply01, gamma_apply10, gamma_apply11, longModulus_cast']
  ring

/-- Compare integer lifts first. This also supplies the periodicity proof below. -/
theorem gaussianLift_eq_smith (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    gaussianLift M u = L2b.gaussian M (smithLift M u) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have hL0 : L2b.longModulus M ≠ 0 := NeZero.ne _
  have h2L0 : 2 * L2b.longModulus M ≠ 0 := Nat.mul_ne_zero (by norm_num) hL0
  have h2N : 2 * L2b.groupOrder M = M * (2 * L2b.longModulus M) := by
    simp only [L2b.groupOrder, L2b.longModulus]
    ring
  rw [smithLift_coordinate, L2b.gaussian_rw_formula]
  simp only [gaussianLift, omega_rowGamma_self]
  rw [h2N]
  have hexp : (M : ℤ) * ((M : ℤ) - 2) *
      (u.1 ^ 2 + u.2 ^ 2 + ((M : ℤ) - 1) * u.1 * u.2)
      = (M : ℤ) * (((M : ℤ) - 2) *
        (u.1 ^ 2 + u.2 ^ 2 + ((M : ℤ) - 1) * u.1 * u.2)) := by ring
  rw [hexp, e_scale M (2 * L2b.longModulus M) hM0 h2L0]

theorem pairingLift_eq_smith (M : ℕ) [Fact (4 ≤ M)] (u v : IntegerPair) :
    pairingLift M u v =
      L2b.metricPairing (L2b.gaussian M) (smithLift M u) (smithLift M v) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have hL0 : L2b.longModulus M ≠ 0 := NeZero.ne _
  have hGL : L2b.groupOrder M = M * L2b.longModulus M := by
    simp only [L2b.groupOrder, L2b.longModulus]
    ring
  rw [smithLift_coordinate (M := M) (a := u), smithLift_coordinate (M := M) (a := v),
    L2b.pairing_rw_formula]
  simp only [pairingLift, omega_gammaDifference]
  rw [hGL, e_scale M (L2b.longModulus M) hM0 hL0]
  refine L2a.e_eq_of_dvd ⟨u.1 * v.2, ?_⟩
  ring

theorem gaussianLift_periodic (M : ℕ) [Fact (4 ≤ M)]
    (u l : IntegerPair) (hl : l ∈ lattice M) :
    gaussianLift M (u + l) = gaussianLift M u := by
  rw [gaussianLift_eq_smith (M := M) (u := u + l), gaussianLift_eq_smith (M := M) (u := u)]
  have h : smithLift M (u + l) = smithLift M u := by
    rw [map_add, smithLift_eq_zero_of_mem M hl, add_zero]
  rw [h]

theorem pairingLift_periodic (M : ℕ) [Fact (4 ≤ M)]
    (u v l k : IntegerPair) (hl : l ∈ lattice M) (hk : k ∈ lattice M) :
    pairingLift M (u + l) (v + k) = pairingLift M u v := by
  rw [pairingLift_eq_smith (M := M) (u := u + l) (v := v + k),
    pairingLift_eq_smith (M := M) (u := u) (v := v)]
  have h1 : smithLift M (u + l) = smithLift M u := by
    rw [map_add, smithLift_eq_zero_of_mem M hl, add_zero]
  have h2 : smithLift M (v + k) = smithLift M v := by
    rw [map_add, smithLift_eq_zero_of_mem M hk, add_zero]
  rw [h1, h2]

def gaussian (M : ℕ) [Fact (4 ≤ M)] : RWGroup M → ℂ :=
  Quotient.lift (gaussianLift M) (by
    intro a b hab
    have hab' : -a + b ∈ lattice M := by
      rw [← QuotientAddGroup.leftRel_apply]
      exact hab
    have h := gaussianLift_periodic M a (-a + b) hab'
    rw [show a + (-a + b) = b by abel] at h
    exact h.symm)

def pairing (M : ℕ) [Fact (4 ≤ M)] : RWGroup M → RWGroup M → ℂ :=
  Quotient.lift
    (fun u => Quotient.lift (pairingLift M u) (by
      intro a b hab
      have hab' : -a + b ∈ lattice M := by
        rw [← QuotientAddGroup.leftRel_apply]
        exact hab
      have h := pairingLift_periodic M u a 0 (-a + b) (zero_mem (lattice M)) hab'
      simpa using h.symm))
    (by
      intro a b hab
      have hab' : -a + b ∈ lattice M := by
        rw [← QuotientAddGroup.leftRel_apply]
        exact hab
      funext v
      refine QuotientAddGroup.induction_on v ?_
      intro c
      have h := pairingLift_periodic M a c (-a + b) 0 hab' (zero_mem (lattice M))
      rw [show a + (-a + b) = b by abel, add_zero] at h
      exact h.symm)

theorem gaussian_mk (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    gaussian M (mk M u) = gaussianLift M u := by
  rfl

theorem pairing_mk (M : ℕ) [Fact (4 ≤ M)] (u v : IntegerPair) :
    pairing M (mk M u) (mk M v) = pairingLift M u v := by
  rfl

theorem gaussian_eq_smith (M : ℕ) [Fact (4 ≤ M)] (u : RWGroup M) :
    gaussian M u = L2b.gaussian M (toSmith M u) := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  change gaussian M (mk M a) = L2b.gaussian M (toSmith M (mk M a))
  rw [gaussian_mk, toSmith_mk, gaussianLift_eq_smith]

theorem pairing_eq_smith (M : ℕ) [Fact (4 ≤ M)] (u v : RWGroup M) :
    pairing M u v = L2b.metricPairing (L2b.gaussian M) (toSmith M u) (toSmith M v) := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  refine QuotientAddGroup.induction_on v ?_
  intro b
  change pairing M (mk M a) (mk M b) =
    L2b.metricPairing (L2b.gaussian M) (toSmith M (mk M a)) (toSmith M (mk M b))
  rw [pairing_mk, toSmith_mk, toSmith_mk, pairingLift_eq_smith]

theorem pairing_eq_polarization (M : ℕ) [Fact (4 ≤ M)] (u v : RWGroup M) :
    pairing M u v = L2b.metricPairing (gaussian M) u v := by
  rw [pairing_eq_smith]
  show L2b.metricPairing (L2b.gaussian M) (toSmith M u) (toSmith M v) =
    L2b.metricPairing (gaussian M) u v
  simp only [L2b.metricPairing]
  rw [← (toSmith M).map_add]
  rw [← gaussian_eq_smith (M := M) (u := u + v)]
  rw [← gaussian_eq_smith (M := M) (u := u)]
  rw [← gaussian_eq_smith (M := M) (u := v)]

theorem rw_isMetricGaussian (M : ℕ) [Fact (4 ≤ M)] :
    L2b.IsMetricGaussian (gaussian M) := by
  have hq := L2b.concrete_isMetricGaussian (M := M)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [gaussian_eq_smith]
    exact hq.nonzero (toSmith M x)
  · intro x
    rw [gaussian_eq_smith, gaussian_eq_smith, map_neg]
    exact hq.even (toSmith M x)
  · intro x y z
    rw [← pairing_eq_polarization (M := M) (u := x + y) (v := z)]
    rw [← pairing_eq_polarization (M := M) (u := x) (v := z)]
    rw [← pairing_eq_polarization (M := M) (u := y) (v := z)]
    rw [pairing_eq_smith (M := M) (u := x + y) (v := z)]
    rw [pairing_eq_smith (M := M) (u := x) (v := z)]
    rw [pairing_eq_smith (M := M) (u := y) (v := z)]
    rw [map_add]
    exact hq.add_left (toSmith M x) (toSmith M y) (toSmith M z)
  · intro x y z
    rw [← pairing_eq_polarization (M := M) (u := x) (v := y + z)]
    rw [← pairing_eq_polarization (M := M) (u := x) (v := y)]
    rw [← pairing_eq_polarization (M := M) (u := x) (v := z)]
    rw [pairing_eq_smith (M := M) (u := x) (v := y + z)]
    rw [pairing_eq_smith (M := M) (u := x) (v := y)]
    rw [pairing_eq_smith (M := M) (u := x) (v := z)]
    rw [map_add]
    exact hq.add_right (toSmith M x) (toSmith M y) (toSmith M z)
  · intro x hx
    have h : ∀ z : L2b.G M, L2b.metricPairing (L2b.gaussian M) (toSmith M x) z = 1 := by
      intro z
      have hz := hx (fromSmith M z)
      rw [← pairing_eq_polarization, pairing_eq_smith, toSmith_fromSmith] at hz
      exact hz
    have h0 : toSmith M x = 0 := hq.nondegenerate (toSmith M x) h
    have hz0 : fromSmith M 0 = 0 := by
      change mk M (L2b.numerator M 0) = 0
      rw [show L2b.numerator M 0 = (0, 0) from by simp [L2b.numerator]]
      exact map_zero (mk M)
    rw [← fromSmith_toSmith M x, h0, hz0]

/-- Multiplication by the base matrix α, not by γ = α³. -/
def rowAlpha (M : ℕ) : IntegerPair →+ IntegerPair where
  toFun u := (((M : ℤ) - 1) * u.1 + u.2, -u.1)
  map_zero' := by
    ext <;> simp
  map_add' := by
    intro u v
    ext <;> simp <;> ring

private theorem rowAlpha_mem_lattice (M : ℕ) [Fact (4 ≤ M)] {a : IntegerPair}
    (ha : a ∈ lattice M) : rowAlpha M a ∈ lattice M := by
  have hchar := (lattice_mem_iff_smith M a).mp ha
  rw [lattice_mem_iff_smith]
  obtain ⟨q, hq⟩ := hchar.1
  obtain ⟨s, hs⟩ := hchar.2
  have hML : (M : ℤ) ∣ (L2b.longModulus M : ℤ) := ⟨(M : ℤ) - 3, by rw [longModulus_cast']⟩
  have ha2 : (M : ℤ) ∣ a.2 := by
    have h1 : (M : ℤ) ∣ ((M : ℤ) - 2) * a.1 + a.2 := hML.trans hchar.2
    have h2 : (M : ℤ) ∣ ((M : ℤ) - 2) * a.1 := dvd_mul_of_dvd_right hchar.1 _
    have hid : a.2 = ((M : ℤ) - 2) * a.1 + a.2 - ((M : ℤ) - 2) * a.1 := by ring
    rw [hid]
    exact dvd_sub h1 h2
  change (M : ℤ) ∣ ((M : ℤ) - 1) * a.1 + a.2 ∧
    (L2b.longModulus M : ℤ) ∣
      ((M : ℤ) - 2) * (((M : ℤ) - 1) * a.1 + a.2) + (-a.1)
  constructor
  · exact dvd_add (dvd_mul_of_dvd_right hchar.1 _) ha2
  · have hexp : ((M : ℤ) - 2) * (((M : ℤ) - 1) * a.1 + a.2) + (-a.1)
        = ((M : ℤ) - 2) * (((M : ℤ) - 2) * a.1 + a.2) + ((M : ℤ) - 3) * a.1 := by
      ring
    rw [hexp]
    refine ⟨((M : ℤ) - 2) * s + q, ?_⟩
    rw [hs, hq, longModulus_cast']
    ring

def epsilonAction (M : ℕ) [Fact (4 ≤ M)] : RWGroup M →+ RWGroup M :=
  QuotientAddGroup.lift (lattice M) ((mk M).comp (rowAlpha M)) (by
    intro a ha
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
    change (rowAlpha M a : RWGroup M) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact rowAlpha_mem_lattice M ha)

theorem epsilonAction_mk (M : ℕ) [Fact (4 ≤ M)] (u : IntegerPair) :
    epsilonAction M (mk M u) = mk M (rowAlpha M u) := by
  rw [epsilonAction]
  change (QuotientAddGroup.lift (lattice M) ((mk M).comp (rowAlpha M)) _) (u : RWGroup M)
    = mk M (rowAlpha M u)
  rw [QuotientAddGroup.lift_mk', AddMonoidHom.comp_apply]

theorem epsilonAction_toSmith (M : ℕ) [Fact (4 ≤ M)] (u : RWGroup M) :
    toSmith M (epsilonAction M u) = L2b.epsilonAut M (toSmith M u) := by
  refine QuotientAddGroup.induction_on u ?_
  intro a
  change toSmith M (epsilonAction M (mk M a)) = L2b.epsilonAut M (toSmith M (mk M a))
  rw [epsilonAction_mk]
  conv_rhs => rw [toSmith_mk]
  rw [toSmith_mk, smithLift_coordinate (M := M) (a := rowAlpha M a)]
  rw [show rowAlpha M = fun u : IntegerPair => (((M : ℤ) - 1) * u.1 + u.2, -u.1) from rfl]
  rw [show L2b.epsilonAut M = fun g : L2b.G M =>
    L2b.coordinate M (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ))
      (((L2b.cofactor M : ℤ)) * ((g.1.val : ℕ) : ℤ) +
        ((M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ)) from rfl]
  rw [smithLift_coordinate (M := M) (a := a)]
  dsimp only [L2b.coordinate]
  set val1 : ℤ := (((a.1 : ZMod M).val : ℕ) : ℤ) with hval1def
  set val2 : ℤ :=
    ((((((M : ℤ) - 2) * a.1 + a.2 : ℤ) : ZMod (L2b.longModulus M)).val : ℕ) : ℤ) with hval2def
  apply coordinate_congr
  · have h1v : (M : ℤ) ∣ val1 - a.1 := by
      rw [hval1def]
      exact val_sub_dvd M a.1
    have h2v : (L2b.longModulus M : ℤ) ∣
        val2 - (((M : ℤ) - 2) * a.1 + a.2) := by
      rw [hval2def]
      exact val_sub_dvd (L2b.longModulus M) _
    have hML : (M : ℤ) ∣ (L2b.longModulus M : ℤ) := ⟨(M : ℤ) - 3, by rw [longModulus_cast']⟩
    have h2M : (M : ℤ) ∣ val2 - (((M : ℤ) - 2) * a.1 + a.2) := hML.trans h2v
    have h0 : (M : ℤ) ∣ a.1 + ((M : ℤ) - 2) * a.1 + a.2 -
        (((M : ℤ) - 1) * a.1 + a.2) := by
      rw [show a.1 + ((M : ℤ) - 2) * a.1 + a.2 - (((M : ℤ) - 1) * a.1 + a.2) = 0 by ring]
      exact dvd_zero _
    have htot := Int.dvd_add (Int.dvd_add h1v h2M) h0
    have htot' : (M : ℤ) ∣ (val1 + val2) - (((M : ℤ) - 1) * a.1 + a.2) := by
      convert htot using 1
      ring
    simpa only [neg_sub] using (Int.dvd_neg.mpr htot')
  · have h1v : (M : ℤ) ∣ val1 - a.1 := by
      rw [hval1def]
      exact val_sub_dvd M a.1
    have h2v : (L2b.longModulus M : ℤ) ∣
        val2 - (((M : ℤ) - 2) * a.1 + a.2) := by
      rw [hval2def]
      exact val_sub_dvd (L2b.longModulus M) _
    have hm : (L2b.longModulus M : ℤ) ∣ (L2b.cofactor M : ℤ) * (val1 - a.1) := by
      obtain ⟨w, hw⟩ := h1v
      refine ⟨w, ?_⟩
      rw [hw, longModulus_cast', cofactor_cast']
      ring
    have hk : (L2b.longModulus M : ℤ) ∣
        ((M : ℤ) - 2) * (val2 - (((M : ℤ) - 2) * a.1 + a.2)) :=
      dvd_mul_of_dvd_right h2v _
    have h0 : (L2b.longModulus M : ℤ) ∣
        (L2b.cofactor M : ℤ) * a.1 + ((M : ℤ) - 2) * (((M : ℤ) - 2) * a.1 + a.2) -
          (((M : ℤ) - 2) * (((M : ℤ) - 1) * a.1 + a.2) + (-a.1)) := by
      rw [show (L2b.cofactor M : ℤ) * a.1 + ((M : ℤ) - 2) * (((M : ℤ) - 2) * a.1 + a.2) -
          (((M : ℤ) - 2) * (((M : ℤ) - 1) * a.1 + a.2) + (-a.1)) = 0 by
        rw [cofactor_cast']; ring]
      exact dvd_zero _
    have htot := Int.dvd_add (Int.dvd_add hm hk) h0
    have htot' : (L2b.longModulus M : ℤ) ∣
        ((L2b.cofactor M : ℤ) * val1 + ((M : ℤ) - 2) * val2) -
          (((M : ℤ) - 2) * (((M : ℤ) - 1) * a.1 + a.2) + (-a.1)) := by
      convert htot using 1
      ring
    simpa only [neg_sub] using (Int.dvd_neg.mpr htot')

/-- The positive square root √N of [RW26], embedded into ℂ. -/
def sqrtOrder (M : ℕ) : ℂ := (Real.sqrt (L2b.groupOrder M) : ℂ)

/-- The denominator is the N in the matrix statement, rather than an assumed card. -/
def normalizedSum (M : ℕ) [Fact (4 ≤ M)] (f : RWGroup M → ℂ) : ℂ :=
  (∑ u : RWGroup M, f u) / sqrtOrder M

def smithValues (M : ℕ) [Fact (4 ≤ M)] (F : RWGroup M → ℂ) : L2b.G M → ℂ :=
  F ∘ fromSmith M

theorem smithValues_coordinate (M : ℕ) [Fact (4 ≤ M)]
    (F : RWGroup M → ℂ) (x y : ℤ) :
    smithValues M F (L2b.coordinate M x y) =
      F (mk M (x, y - ((M : ℤ) - 2) * x)) := by
  change F (fromSmith M (L2b.coordinate M x y)) = F (mk M (x, y - ((M : ℤ) - 2) * x))
  rw [fromSmith_coordinate]

theorem sqrtOrder_eq_sqrtCard (M : ℕ) [Fact (4 ≤ M)] :
    sqrtOrder M = L2b.sqrtCard (L2b.G M) := by
  rw [sqrtOrder, L2b.sqrtCard, L2b.card_G]

theorem normalizedSum_toSmith (M : ℕ) [Fact (4 ≤ M)] (f : RWGroup M → ℂ) :
    normalizedSum M f = L2b.normalizedSum (smithValues M f) := by
  rw [normalizedSum, L2b.normalizedSum, sqrtOrder_eq_sqrtCard]
  congr 1
  exact Fintype.sum_equiv (smithEquiv M).toEquiv (fun u => f u) (fun g => smithValues M f g)
    (fun u => by
      show f u = f (fromSmith M (toSmith M u))
      rw [fromSmith_toSmith])

end SICLean.L2c
