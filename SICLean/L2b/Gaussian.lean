import SICLean.L2b.Group

set_option autoImplicit false

/-!
# The explicit Gaussian and character filter

[RW26, §4.4]. Nondegeneracy holds on G, and is not asserted on the restriction to H.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2b

/-- The Gaussian of [RW26, §4.4] after the Smith change of coordinates. -/
def gaussianLift (M : ℕ) (x y : ℤ) : ℂ :=
  L2a.e M (x ^ 2 + x * y) *
    L2a.e (2 * longModulus M) (((longModulus M : ℤ) + (M : ℤ) - 2) * y ^ 2)

def gaussian (M : ℕ) (g : G M) : ℂ := gaussianLift M g.1.val g.2.val

/-- The displayed bicharacter formula, on integer Smith lifts. -/
def pairingLift (M : ℕ) (x y z w : ℤ) : ℂ :=
  L2a.e (longModulus M)
    ((cofactor M : ℤ) * (2 * x * z + x * w + y * z) + ((M : ℤ) - 2) * y * w)

/-! ### Generic helper lemmas about `L2a.e` and parity -/

private theorem e_ne_zero (N : ℕ) (t : ℤ) : L2a.e N t ≠ 0 := by
  rw [L2a.e_eq_omega_zpow]
  exact zpow_ne_zero _ (omega_ne_zero N)

/-- `e N t = 1` exactly on the multiples of the modulus. -/
private theorem e_eq_one_iff_dvd {N : ℕ} (hN : N ≠ 0) (t : ℤ) :
    L2a.e N t = 1 ↔ ((N : ℕ) : ℤ) ∣ t := by
  rw [L2a.e_eq_omega_zpow]
  constructor
  · intro h
    by_contra hc
    have : NeZero N := ⟨hN⟩
    exact omega_ne_one_of_not_dvd hc h
  · exact omega_zpow_dvd N

/-- Rescaling the modulus: `e M z = e N (c * z)` when `N = c * M` with `c, M ≠ 0`. -/
private theorem e_mod_cast (c M N : ℕ) (hc : c ≠ 0) (hM : M ≠ 0) (hN : N = c * M) (z : ℤ) :
    L2a.e M z = L2a.e N ((c : ℤ) * z) := by
  have hc' : ((c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hM' : ((M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [L2a.e_eq_omega_zpow, L2a.e_eq_omega_zpow, omega_exp, omega_exp, hN]
  push_cast
  apply congrArg Complex.exp
  field_simp

private theorem e_two_eq_neg_one (t : ℤ) : L2a.e 2 t = (-1 : ℂ) ^ t := by
  have h2 : omega 2 = -1 := by
    rw [omega]
    have h : (2 * Real.pi * Complex.I / (2 : ℕ) : ℂ) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [h, Complex.exp_mul_I]
    norm_num
  rw [L2a.e_eq_omega_zpow, h2]

private theorem e_pow (N : ℕ) (t : ℤ) : ∀ k : ℕ, L2a.e N (k * t) = (L2a.e N t) ^ k
  | 0 => by simp [L2a.e]
  | k + 1 => by
    push_cast
    rw [add_mul, one_mul, ← L2a.e_mul, e_pow N t k, pow_succ]

private theorem two_dvd_sq_sub_self (t : ℤ) : (2 : ℤ) ∣ t ^ 2 - t := by
  rcases Int.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨2 * k ^ 2 - k, ?_⟩
    subst hk
    ring
  · refine ⟨2 * k ^ 2 + k, ?_⟩
    subst hk
    ring

private theorem two_dvd_mul_consec (t : ℤ) : (2 : ℤ) ∣ t * (t + 1) := by
  have h := two_dvd_sq_sub_self (t + 1)
  have hid : (t + 1) ^ 2 - (t + 1) = t * (t + 1) := by ring
  rwa [hid] at h

/-- The quadratic coefficient in the §4.4 formula is always odd. -/
private theorem exists_half_odd (t : ℤ) : ∃ p : ℤ, t ^ 2 - 3 * t + 3 = 2 * p + 1 := by
  rcases Int.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨2 * k ^ 2 - 3 * k + 1, by subst hk; ring⟩
  · exact ⟨2 * k ^ 2 - k, by subst hk; ring⟩

/-- The quadratic coefficient in the ι formula is always even. -/
private theorem exists_half_even (t : ℤ) : ∃ p : ℤ, t ^ 2 - 5 * t + 8 = 2 * p := by
  rcases Int.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨2 * k ^ 2 - 5 * k + 4, by subst hk; ring⟩
  · exact ⟨2 * k ^ 2 - 3 * k + 2, by subst hk; ring⟩

/-- Powers of a single `e`-phase divide. -/
private theorem e_div (N : ℕ) (u v p q : ℤ) :
    L2a.e N u * L2a.e N v / (L2a.e N p * L2a.e N q) = L2a.e N (u + v - p - q) := by
  rw [div_eq_mul_inv, mul_inv, L2a.e_inv, L2a.e_inv]
  simp only [L2a.e_mul]
  congr 1
  ring

variable (M : ℕ) [Fact (4 ≤ M)]

/-! ### Cast bookkeeping for the Smith coordinates -/

private theorem cofactor_cast : ((cofactor M : ℕ) : ℤ) = (M : ℤ) - 3 := by
  have h4 : 4 ≤ M := Fact.out
  rw [Nat.cast_sub (by omega : (3 : ℕ) ≤ M)]
  push_cast
  ring

private theorem longModulus_cast :
    ((longModulus M : ℕ) : ℤ) = (M : ℤ) * ((M : ℤ) - 3) := by
  rw [Nat.cast_mul, cofactor_cast]

private theorem longModulus_ne : longModulus M ≠ 0 := NeZero.ne _

private theorem cofactor_ne : cofactor M ≠ 0 := NeZero.ne _

private theorem M_ne : M ≠ 0 := NeZero.ne M

/-- Converting from modulus `M` up to modulus `2n`. -/
private theorem e_to_2n (s : ℤ) :
    L2a.e M s = L2a.e (2 * longModulus M) (2 * (cofactor M : ℤ) * s) :=
  e_mod_cast (2 * cofactor M) M (2 * longModulus M)
    (by intro h; have := cofactor_ne M; omega) (M_ne M)
    (by rw [show longModulus M = cofactor M * M from Nat.mul_comm M (cofactor M)]; ring) s

/-- The sign hidden in a half-period: `(-1) ^ t = e_{2n} (n * t)`. -/
private theorem neg_one_eq (t : ℤ) :
    (-1 : ℂ) ^ t = L2a.e (2 * longModulus M) ((longModulus M : ℤ) * t) := by
  rw [← e_two_eq_neg_one, e_mod_cast (longModulus M) 2 (2 * longModulus M) (longModulus_ne M)
    two_ne_zero (by ring)]

theorem longModulus_even : Even (longModulus M) := by
  have h4 : 4 ≤ M := Fact.out
  rcases Nat.even_or_odd M with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨k * (M - 3), ?_⟩
    rw [show longModulus M = M * (M - 3) from rfl, hk]
    ring
  · refine ⟨M * (k - 1), ?_⟩
    have hsub : 2 * k + 1 - 3 = 2 * (k - 1) := by omega
    rw [show longModulus M = M * (M - 3) from rfl, hk, hsub]
    ring

/-- The Gaussian is computed on any integer lift of the Smith coordinates. -/
private theorem gaussian_cast_eq (x y : ℤ) :
    gaussian M ((x : ZMod M), (y : ZMod (longModulus M))) = gaussianLift M x y := by
  have hvx : ((M : ℕ) : ℤ) ∣ (((x : ZMod M).val : ℕ) : ℤ) - x := by
    have hv : (((x : ZMod M).val : ℕ) : ℤ) = x % ((M : ℕ) : ℤ) := ZMod.val_intCast x
    refine ⟨-(x / ((M : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv x ((M : ℕ) : ℤ)]
  have hvy : ((longModulus M : ℕ) : ℤ) ∣ (((y : ZMod (longModulus M)).val : ℕ) : ℤ) - y := by
    have hv : (((y : ZMod (longModulus M)).val : ℕ) : ℤ) = y % ((longModulus M : ℕ) : ℤ) :=
      ZMod.val_intCast y
    refine ⟨-(y / ((longModulus M : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv y ((longModulus M : ℕ) : ℤ)]
  set v : ℤ := (((x : ZMod M).val : ℕ) : ℤ) with hvdef
  set w : ℤ := (((y : ZMod (longModulus M)).val : ℕ) : ℤ) with hwdef
  have hMn : ((M : ℕ) : ℤ) ∣ ((longModulus M : ℕ) : ℤ) := by
    refine ⟨(cofactor M : ℤ), ?_⟩
    push_cast
    ring
  have hd1 : ((M : ℕ) : ℤ) ∣ (v ^ 2 + v * w) - (x ^ 2 + x * y) := by
    have hid : (v ^ 2 + v * w) - (x ^ 2 + x * y)
        = (v - x) * (v + x) + v * (w - y) + (v - x) * y := by ring
    rw [hid]
    exact dvd_add
      (dvd_add (dvd_mul_of_dvd_left hvx _)
        (dvd_trans hMn (dvd_mul_of_dvd_right hvy v)))
      (dvd_mul_of_dvd_left hvx _)
  obtain ⟨k, hk⟩ := hvy
  obtain ⟨k', hk'⟩ := longModulus_even M
  have hk'2 : ((longModulus M : ℕ) : ℤ) = 2 * k' := by
    have := hk'
    push_cast
    linarith
  have hd2 : ((2 * longModulus M : ℕ) : ℤ) ∣
      ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * w ^ 2) -
        (((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * y ^ 2 := by
    have hw2 : w = y + ((longModulus M : ℕ) : ℤ) * k := by linear_combination hk
    have hdiv : ((2 * longModulus M : ℕ) : ℤ) = 2 * (2 * k') := by
      have h2 := hk'2
      push_cast at h2
      push_cast
      linarith
    refine ⟨(((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * (y * k + k' * k ^ 2), ?_⟩
    rw [hw2, hk'2, hdiv]
    ring
  show L2a.e M (v ^ 2 + v * w) *
      L2a.e (2 * longModulus M) ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * w ^ 2) =
    gaussianLift M x y
  rw [L2a.e_eq_of_dvd hd1, L2a.e_eq_of_dvd hd2]
  rfl

theorem gaussianLift_periodic (x y a b : ℤ) :
    gaussianLift M (x + (M : ℤ) * a) (y + (longModulus M : ℤ) * b) =
      gaussianLift M x y := by
  have h1 : (((x + (M : ℤ) * a : ℤ)) : ZMod M) = ((x : ZMod M)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨-a, by ring⟩
  have h2 : (((y + (longModulus M : ℤ) * b : ℤ)) : ZMod (longModulus M)) =
      ((y : ZMod (longModulus M))) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨-b, by ring⟩
  rw [← gaussian_cast_eq, ← gaussian_cast_eq, h1, h2, gaussian_cast_eq]

/-- Any group element is its own canonical lift of the Smith coordinates. -/
private theorem G_eq_val_cast (g : G M) :
    g = (((g.1.val : ℤ) : ZMod M), ((g.2.val : ℤ) : ZMod (longModulus M))) := by
  refine Prod.ext ?_ ?_
  · exact ((ZMod.intCast_eq_iff M ((g.1.val : ℕ) : ℤ) g.1).2 ⟨0, by simp⟩).symm
  · exact ((ZMod.intCast_eq_iff (longModulus M) ((g.2.val : ℕ) : ℤ) g.2).2 ⟨0, by simp⟩).symm

/-- Comparison with the second Gaussian displayed in §4.4. -/
theorem gaussian_rw_formula (a b : ℤ) :
    gaussian M (coordinate M a (((M : ℤ) - 2) * a + b)) =
      (-1 : ℂ) ^ (a + b + a * b) *
        L2a.e (2 * longModulus M)
          (((M : ℤ) - 2) * (a ^ 2 + b ^ 2 + ((M : ℤ) - 1) * a * b)) := by
  simp only [coordinate]
  rw [gaussian_cast_eq]
  show L2a.e M (a ^ 2 + a * (((M : ℤ) - 2) * a + b)) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * (((M : ℤ) - 2) * a + b) ^ 2) =
    (-1 : ℂ) ^ (a + b + a * b) *
      L2a.e (2 * longModulus M)
        (((M : ℤ) - 2) * (a ^ 2 + b ^ 2 + ((M : ℤ) - 1) * a * b))
  rw [e_to_2n M, neg_one_eq M, L2a.e_mul, L2a.e_mul]
  obtain ⟨p, hp⟩ := exists_half_odd ((M : ℕ) : ℤ)
  obtain ⟨qa, hqa⟩ := two_dvd_sq_sub_self a
  obtain ⟨qb, hqb⟩ := two_dvd_sq_sub_self b
  refine L2a.e_eq_of_dvd ⟨qa + p * a ^ 2 + qb + ((M : ℤ) - 2) * a * b, ?_⟩
  have h1 : (2 * (cofactor M : ℤ) * (a ^ 2 + a * (((M : ℤ) - 2) * a + b)) +
        (((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * (((M : ℤ) - 2) * a + b) ^ 2) -
      (((longModulus M : ℕ) : ℤ) * (a + b + a * b) +
        ((M : ℤ) - 2) * (a ^ 2 + b ^ 2 + ((M : ℤ) - 1) * a * b)) =
      ((longModulus M : ℕ) : ℤ) *
        (((M : ℤ) ^ 2 - 3 * (M : ℤ) + 3) * a ^ 2 + b ^ 2 - a - b +
          2 * ((M : ℤ) - 2) * a * b) := by
    rw [cofactor_cast M, longModulus_cast M]
    ring
  have h2n : ((2 * longModulus M : ℕ) : ℤ) = 2 * ((longModulus M : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_two]
  have h2 : ((longModulus M : ℕ) : ℤ) *
        (((M : ℤ) ^ 2 - 3 * (M : ℤ) + 3) * a ^ 2 + b ^ 2 - a - b +
          2 * ((M : ℤ) - 2) * a * b) =
      ((2 * longModulus M : ℕ) : ℤ) *
        (qa + p * a ^ 2 + qb + ((M : ℤ) - 2) * a * b) := by
    rw [h2n]
    linear_combination ((longModulus M : ℕ) : ℤ) * (a ^ 2 * hp + hqa + hqb)
  exact h1.trans h2

theorem gaussian_ne_zero (g : G M) : gaussian M g ≠ 0 := by
  show L2a.e M _ * L2a.e (2 * longModulus M) _ ≠ 0
  exact mul_ne_zero (e_ne_zero M _) (e_ne_zero (2 * longModulus M) _)

theorem gaussian_zero : gaussian M 0 = 1 := by
  simp [gaussian, gaussianLift, ZMod.val_zero, L2a.e]

theorem gaussian_even (g : G M) : gaussian M (-g) = gaussian M g := by
  rw [G_eq_val_cast M g]
  have hneg : (-(((g.1.val : ℤ) : ZMod M), ((g.2.val : ℤ) : ZMod (longModulus M))) :
      G M) = (((Int.cast (-(g.1.val : ℤ))) : ZMod M),
        ((Int.cast (-(g.2.val : ℤ))) : ZMod (longModulus M))) := by
    refine Prod.ext ?_ ?_
    · simp [Int.cast_neg]
    · simp [Int.cast_neg]
  rw [hneg, gaussian_cast_eq, gaussian_cast_eq]
  show L2a.e M _ * L2a.e (2 * longModulus M) _ = L2a.e M _ * L2a.e (2 * longModulus M) _
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/-! ### The bicharacter on integer Smith lifts -/

private theorem cast_pair_add (x y z w : ℤ) :
    ((x : ZMod M), (y : ZMod (longModulus M))) + ((z : ZMod M), (w : ZMod (longModulus M))) =
      (((x + z : ℤ) : ZMod M), ((y + w : ℤ) : ZMod (longModulus M))) := by
  refine Prod.ext ?_ ?_
  · simp
  · simp

/-- Down to the long modulus: `e_M s = e_n (m s)`. -/
private theorem e_to_n (s : ℤ) :
    L2a.e M s = L2a.e (longModulus M) ((cofactor M : ℤ) * s) :=
  e_mod_cast (cofactor M) M (longModulus M) (cofactor_ne M) (M_ne M)
    (Nat.mul_comm M (cofactor M)) s

private theorem e_n_to_2n (s : ℤ) :
    L2a.e (longModulus M) s = L2a.e (2 * longModulus M) (2 * s) :=
  e_mod_cast 2 (longModulus M) (2 * longModulus M) two_ne_zero (longModulus_ne M) rfl s

omit [Fact (4 ≤ M)] in
private theorem two_longModulus_cast :
    ((2 * longModulus M : ℕ) : ℤ) = 2 * ((longModulus M : ℕ) : ℤ) := by
  rw [Nat.cast_mul, Nat.cast_two]

/-- The displayed bicharacter formula, on integer lifts. -/
private theorem metricPairing_lift (x y z w : ℤ) :
    metricPairing (gaussian M) ((x : ZMod M), (y : ZMod (longModulus M)))
        ((z : ZMod M), (w : ZMod (longModulus M))) =
      L2a.e (longModulus M)
        ((cofactor M : ℤ) * (2 * x * z + x * w + y * z) + ((M : ℤ) - 2) * y * w) := by
  show gaussian M (((x : ZMod M), (y : ZMod (longModulus M))) +
      ((z : ZMod M), (w : ZMod (longModulus M)))) /
    (gaussian M ((x : ZMod M), (y : ZMod (longModulus M))) *
      gaussian M ((z : ZMod M), (w : ZMod (longModulus M)))) = _
  rw [cast_pair_add M x y z w, gaussian_cast_eq, gaussian_cast_eq, gaussian_cast_eq]
  show L2a.e M ((x + z) ^ 2 + (x + z) * (y + w)) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * (y + w) ^ 2) /
    (L2a.e M (x ^ 2 + x * y) *
      L2a.e (2 * longModulus M) ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * y ^ 2) *
    (L2a.e M (z ^ 2 + z * w) *
      L2a.e (2 * longModulus M) ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * w ^ 2))) =
    L2a.e (longModulus M)
      ((cofactor M : ℤ) * (2 * x * z + x * w + y * z) + ((M : ℤ) - 2) * y * w)
  rw [e_to_2n M, e_to_2n M, e_to_2n M, e_n_to_2n M]
  rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
  rw [L2a.e_inv, L2a.e_inv, L2a.e_inv, L2a.e_inv]
  simp only [L2a.e_mul]
  refine L2a.e_eq_of_dvd ⟨y * w, ?_⟩
  rw [cofactor_cast M, two_longModulus_cast, longModulus_cast]
  ring

theorem concrete_pairing_formula (g h : G M) :
    metricPairing (gaussian M) g h =
      pairingLift M g.1.val g.2.val h.1.val h.2.val := by
  have key := metricPairing_lift M g.1.val g.2.val h.1.val h.2.val
  rw [← G_eq_val_cast M g, ← G_eq_val_cast M h] at key
  exact key

theorem pairing_rw_formula (a b c d : ℤ) :
    metricPairing (gaussian M)
        (coordinate M a (((M : ℤ) - 2) * a + b))
        (coordinate M c (((M : ℤ) - 2) * c + d)) =
      L2a.e (longModulus M) (((M : ℤ) - 2) * (a * c + b * d) + a * d + b * c) := by
  simp only [coordinate]
  rw [metricPairing_lift M a (((M : ℤ) - 2) * a + b) c (((M : ℤ) - 2) * c + d)]
  refine L2a.e_eq_of_dvd ⟨((M : ℤ) - 1) * a * c + a * d + b * c, ?_⟩
  rw [cofactor_cast M, longModulus_cast]
  ring

/-- The entire metric-group structure is a conclusion from the definitions. -/
theorem concrete_isMetricGaussian : IsMetricGaussian (gaussian M) := by
  refine ⟨gaussian_ne_zero M, gaussian_even M, ?_, ?_, ?_⟩
  · intro x y z
    rw [G_eq_val_cast M x, G_eq_val_cast M y, G_eq_val_cast M z, cast_pair_add M,
      metricPairing_lift M, metricPairing_lift M, metricPairing_lift M, L2a.e_mul]
    exact L2a.e_eq_of_dvd ⟨0, by rw [cofactor_cast M]; ring⟩
  · intro x y z
    rw [G_eq_val_cast M x, G_eq_val_cast M y, G_eq_val_cast M z, cast_pair_add M,
      metricPairing_lift M, metricPairing_lift M, metricPairing_lift M, L2a.e_mul]
    exact L2a.e_eq_of_dvd ⟨0, by rw [cofactor_cast M]; ring⟩
  · intro x hx
    have e10 := hx (((1 : ℤ) : ZMod M), ((0 : ℤ) : ZMod (longModulus M)))
    rw [G_eq_val_cast M x, metricPairing_lift M] at e10
    have e01 := hx (((0 : ℤ) : ZMod M), ((1 : ℤ) : ZMod (longModulus M)))
    rw [G_eq_val_cast M x, metricPairing_lift M] at e01
    obtain ⟨k1, hk1⟩ := (e_eq_one_iff_dvd (longModulus_ne M) _).1 e10
    rw [cofactor_cast M, longModulus_cast M] at hk1
    have h4 : 4 ≤ M := Fact.out
    have hm3 : ((M : ℤ) - 3) ≠ 0 := by
      rw [← cofactor_cast M]
      exact_mod_cast (cofactor_ne M)
    have hM : ((M : ℕ) : ℤ) ∣ 2 * ((x.1.val : ℕ) : ℤ) + ((x.2.val : ℕ) : ℤ) := by
      refine ⟨k1, ?_⟩
      have hc : ((M : ℤ) - 3) * (2 * ((x.1.val : ℕ) : ℤ) + ((x.2.val : ℕ) : ℤ)) =
          ((M : ℤ) - 3) * ((M : ℤ) * k1) := by
        linear_combination hk1
      exact mul_left_cancel₀ hm3 hc
    obtain ⟨k2, hk2⟩ := (e_eq_one_iff_dvd (longModulus_ne M) _).1 e01
    have hn : ((longModulus M : ℕ) : ℤ) ∣
        ((cofactor M : ℤ) * ((x.1.val : ℕ) : ℤ) + ((M : ℤ) - 2) * ((x.2.val : ℕ) : ℤ)) :=
      ⟨k2, by linear_combination hk2⟩
    obtain ⟨c1, hc1⟩ := hM
    obtain ⟨c2, hc2⟩ := hn
    rw [longModulus_cast M, cofactor_cast M] at hc2
    have hdivX : ((M : ℕ) : ℤ) ∣ ((x.1.val : ℕ) : ℤ) := by
      refine ⟨-((M : ℤ) - 2) * c1 + ((M : ℤ) - 3) * c2 + (x.1.val : ℕ), ?_⟩
      linear_combination -((M : ℤ) - 2) * hc1 + hc2
    have hX0 : ((x.1.val : ℕ) : ℤ) = 0 :=
      (Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
        (by exact_mod_cast ZMod.val_lt x.1)).symm.trans (Int.emod_eq_zero_of_dvd hdivX)
    rw [hX0] at hc1
    have hdivY : ((M : ℕ) : ℤ) ∣ ((x.2.val : ℕ) : ℤ) :=
      ⟨c1, by linear_combination hc1⟩
    obtain ⟨y', hy'⟩ := hdivY
    rw [hX0, hy'] at hc2
    have hMne : ((M : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (M_ne M)
    have hmy : ((M : ℤ) - 3) * c2 = ((M : ℤ) - 2) * y' :=
      mul_left_cancel₀ hMne (by linear_combination -hc2)
    have hdivY2 : ((longModulus M : ℕ) : ℤ) ∣ ((x.2.val : ℕ) : ℤ) := by
      refine ⟨c2 - y', ?_⟩
      rw [longModulus_cast M]
      linear_combination -(M : ℤ) * hmy + hy'
    have hY0 : ((x.2.val : ℕ) : ℤ) = 0 :=
      (Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
        (by exact_mod_cast ZMod.val_lt x.2)).symm.trans (Int.emod_eq_zero_of_dvd hdivY2)
    exact Prod.ext ((ZMod.val_eq_zero _).1 (by exact_mod_cast hX0))
      ((ZMod.val_eq_zero _).1 (by exact_mod_cast hY0))

theorem epsilonAut_preserves_gaussian (g : G M) :
    gaussian M (epsilonAut M g) = gaussian M g := by
  show gaussian M (coordinate M (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((g.1.val : ℕ) : ℤ) + ((M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ))) =
    gaussian M g
  simp only [coordinate]
  rw [gaussian_cast_eq]
  show L2a.e M ((((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ)) ^ 2 +
      (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ)) *
        ((cofactor M : ℤ) * ((g.1.val : ℕ) : ℤ) + ((M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ))) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) *
          ((cofactor M : ℤ) * ((g.1.val : ℕ) : ℤ) +
            ((M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ)) ^ 2) =
    L2a.e M (((g.1.val : ℕ) : ℤ) ^ 2 + ((g.1.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ) ^ 2)
  rw [e_to_2n M, e_to_2n M, L2a.e_mul, L2a.e_mul]
  obtain ⟨p1, hp1⟩ := two_dvd_mul_consec (((M : ℤ) - 3))
  obtain ⟨p2, hp2⟩ := two_dvd_mul_consec (((M : ℤ) - 2))
  refine L2a.e_eq_of_dvd ⟨p1 * ((g.1.val : ℕ) : ℤ) ^ 2 +
      ((M : ℤ) - 2) * ((M : ℤ) - 2) * ((g.1.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ) +
      p2 * ((g.2.val : ℕ) : ℤ) ^ 2, ?_⟩
  rw [two_longModulus_cast, longModulus_cast, cofactor_cast]
  linear_combination ((M : ℤ) * ((M : ℤ) - 3)) *
    (hp1 * ((g.1.val : ℕ) : ℤ) ^ 2 + hp2 * ((g.2.val : ℕ) : ℤ) ^ 2)

/-- Exact agreement with L2a's e_M(i²−ij+j²), with its positive sign. -/
theorem gaussian_iota (h : L2a.Index M) :
    gaussian M (iota M h) = L2a.gaussian M h := by
  show gaussian M (coordinate M (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ))) = L2a.gaussian M h
  simp only [coordinate]
  rw [gaussian_cast_eq]
  show L2a.e M ((2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ)) ^ 2 +
      (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ)) *
        ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ))) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) *
          ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)) ^ 2) =
    L2a.e M (((h.1.val : ℕ) : ℤ) ^ 2 - ((h.1.val : ℕ) : ℤ) * ((h.2.val : ℕ) : ℤ) +
      ((h.2.val : ℕ) : ℤ) ^ 2)
  rw [e_to_2n M, e_to_2n M, L2a.e_mul]
  obtain ⟨p, hp⟩ := exists_half_even ((M : ℕ) : ℤ)
  refine L2a.e_eq_of_dvd ⟨-((h.1.val : ℕ) : ℤ) * ((h.2.val : ℕ) : ℤ) +
      p * ((h.2.val : ℕ) : ℤ) ^ 2, ?_⟩
  rw [two_longModulus_cast, longModulus_cast, cofactor_cast]
  linear_combination ((M : ℤ) * ((M : ℤ) - 3)) * (((h.2.val : ℕ) : ℤ) ^ 2) * hp

theorem pairing_iota (h k : L2a.Index M) :
    metricPairing (gaussian M) (iota M h) (iota M k) = L2a.pairing M h k := by
  show gaussian M (iota M h + iota M k) /
      (gaussian M (iota M h) * gaussian M (iota M k)) = L2a.pairing M h k
  rw [← (iota M).map_add h k, gaussian_iota M (h + k), gaussian_iota M h, gaussian_iota M k]
  rfl

theorem pairing_mixed (g : G M) (h : L2a.Index M) :
    metricPairing (gaussian M) g (iota M h) =
      L2a.e M ((g.1.val : ℤ) * ((h.2.val : ℤ) - 2 * h.1.val) -
        (g.2.val : ℤ) * h.1.val) := by
  have hiota : iota M h = coordinate M (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)) := rfl
  rw [hiota]
  simp only [coordinate]
  nth_rw 1 [G_eq_val_cast M g]
  rw [metricPairing_lift M ((g.1.val : ℕ) : ℤ) ((g.2.val : ℕ) : ℤ)
      (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)), e_n_to_2n M, e_to_2n M]
  refine L2a.e_eq_of_dvd ⟨((h.2.val : ℕ) : ℤ) *
      (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ)), ?_⟩
  rw [two_longModulus_cast, longModulus_cast, cofactor_cast]
  ring

theorem pairing_witnessW (h k : L2a.Index M) :
    metricPairing (gaussian M) (witnessW M h) (iota M k) =
      L2a.e M (-(k.1.val : ℤ) * h.1.val +
        (k.2.val : ℤ) * ((h.1.val : ℤ) - h.2.val)) := by
  have hw : witnessW M h = coordinate M (((h.1.val : ℕ) : ℤ) - ((h.2.val : ℕ) : ℤ))
      (((M : ℤ) - 1) * ((h.1.val : ℕ) : ℤ) - ((M : ℤ) - 2) * ((h.2.val : ℕ) : ℤ)) := rfl
  have hiota : iota M k = coordinate M (2 * ((k.2.val : ℕ) : ℤ) - ((k.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((k.2.val : ℕ) : ℤ)) := rfl
  rw [hw, hiota]
  simp only [coordinate]
  rw [metricPairing_lift M (((h.1.val : ℕ) : ℤ) - ((h.2.val : ℕ) : ℤ))
      (((M : ℤ) - 1) * ((h.1.val : ℕ) : ℤ) - ((M : ℤ) - 2) * ((h.2.val : ℕ) : ℤ))
      (2 * ((k.2.val : ℕ) : ℤ) - ((k.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((k.2.val : ℕ) : ℤ)), e_n_to_2n M, e_to_2n M]
  refine L2a.e_eq_of_dvd ⟨((M : ℤ) * ((h.1.val : ℕ) : ℤ) * ((k.2.val : ℕ) : ℤ) -
      ((M : ℤ) - 1) * ((h.2.val : ℕ) : ℤ) * ((k.2.val : ℕ) : ℤ) -
      ((h.1.val : ℕ) : ℤ) * ((k.1.val : ℕ) : ℤ) +
      ((h.2.val : ℕ) : ℤ) * ((k.1.val : ℕ) : ℤ)), ?_⟩
  rw [two_longModulus_cast, longModulus_cast, cofactor_cast]
  ring

private theorem smul_cast_pair (t x y : ℤ) :
    t • (((x : ZMod M), (y : ZMod (longModulus M)))) =
      ((((t * x : ℤ) : ZMod M), ((t * y : ℤ) : ZMod (longModulus M)))) := by
  simp [Prod.smul_def, zsmul_eq_mul, Int.cast_mul]

/-- Converting from modulus `cofactor M` up to modulus `n`. -/
private theorem e_m_to_n (z : ℤ) :
    L2a.e (cofactor M) z = L2a.e (longModulus M) ((M : ℤ) * z) :=
  e_mod_cast M (cofactor M) (longModulus M) (M_ne M) (cofactor_ne M) rfl z

theorem pairing_annihilatorGenerator (j : ℤ) (g : G M) :
    metricPairing (gaussian M) (j • annihilatorGenerator M) g =
      L2a.e (cofactor M) (-j * (g.2.val : ℤ)) := by
  have hgen : annihilatorGenerator M = coordinate M 0 (-(M : ℤ)) := rfl
  rw [hgen]
  simp only [coordinate]
  rw [smul_cast_pair M j 0 (-(M : ℤ))]
  nth_rw 1 [G_eq_val_cast M g]
  rw [metricPairing_lift M (j * 0) (j * (-(M : ℤ))) ((g.1.val : ℕ) : ℤ)
      ((g.2.val : ℕ) : ℤ), e_m_to_n M]
  refine L2a.e_eq_of_dvd ⟨-j * (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ)), ?_⟩
  rw [longModulus_cast, cofactor_cast]
  ring

/-- If `c` divides both the modulus and `x`, it divides the reduced value of `x`. -/
private theorem dvd_val_cast {N : ℕ} [NeZero N] (x c : ℤ) (hcN : c ∣ ((N : ℕ) : ℤ))
    (hcx : c ∣ x) : c ∣ ((((x : ZMod N).val : ℕ) : ℤ)) := by
  have hv : ((((x : ZMod N).val : ℕ) : ℤ)) = x % ((N : ℕ) : ℤ) := ZMod.val_intCast x
  obtain ⟨k, hk⟩ := hcx
  obtain ⟨l, hl⟩ := hcN
  rw [hv]
  refine ⟨k - (x / ((N : ℕ) : ℤ)) * l, ?_⟩
  linear_combination Int.mul_ediv_add_emod x ((N : ℕ) : ℤ) + hk - (x / ((N : ℕ) : ℤ)) * hl

/-- The annihilator of H is cyclic even when the pairing on H is degenerate. -/
theorem orthogonal_iota :
    {g : G M | ∀ h : L2a.Index M, metricPairing (gaussian M) g (iota M h) = 1} =
      (AddSubgroup.zmultiples (annihilatorGenerator M) : Set (G M)) := by
  have hgen : annihilatorGenerator M = coordinate M 0 (-(M : ℤ)) := rfl
  ext g
  simp only [SetLike.mem_coe]
  refine ⟨fun hg => ?_, fun hmem h => ?_⟩
  · have h4 : 4 ≤ M := Fact.out
    haveI : Fact (1 < M) := ⟨by have := Fact.out (p := 4 ≤ M); omega⟩
    have hv2 : (((((0 : ZMod M), (1 : ZMod M)) : L2a.Index M).2.val : ℕ) : ℤ) = 1 := by
      show (((1 : ZMod M).val : ℕ) : ℤ) = 1
      exact_mod_cast ZMod.val_one M
    have hv1 : (((((0 : ZMod M), (1 : ZMod M)) : L2a.Index M).1.val : ℕ) : ℤ) = 0 := by
      show (((0 : ZMod M).val : ℕ) : ℤ) = 0
      simp
    have hA := hg (((0 : ZMod M), (1 : ZMod M)) : L2a.Index M)
    rw [pairing_mixed M g, hv2, hv1] at hA
    obtain ⟨k1, hk1⟩ := (e_eq_one_iff_dvd (M_ne M) _).1 hA
    ring_nf at hk1
    have hX0 : ((g.1.val : ℕ) : ℤ) = 0 := by
      have hlt : ((g.1.val : ℕ) : ℤ) < ((M : ℕ) : ℤ) := by
        exact_mod_cast ZMod.val_lt g.1
      have hge : (0 : ℤ) ≤ ((g.1.val : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
      have hMpos : (0 : ℤ) < ((M : ℕ) : ℤ) := by omega
      have hk10 : k1 = 0 := by
        rcases lt_trichotomy k1 0 with hk | hk | hk
        · have hneg : ((M : ℕ) : ℤ) * k1 < 0 := mul_neg_of_pos_of_neg hMpos hk
          omega
        · exact hk
        · have hle : ((M : ℕ) : ℤ) ≤ ((M : ℕ) : ℤ) * k1 := by
            nlinarith
          omega
      rw [hk10, mul_zero] at hk1
      omega
    have hv2' : (((((1 : ZMod M), (0 : ZMod M)) : L2a.Index M).2.val : ℕ) : ℤ) = 0 := by
      show (((0 : ZMod M).val : ℕ) : ℤ) = 0
      simp
    have hv1' : (((((1 : ZMod M), (0 : ZMod M)) : L2a.Index M).1.val : ℕ) : ℤ) = 1 := by
      show (((1 : ZMod M).val : ℕ) : ℤ) = 1
      exact_mod_cast ZMod.val_one M
    have hB := hg (((1 : ZMod M), (0 : ZMod M)) : L2a.Index M)
    rw [pairing_mixed M g, hv2', hv1'] at hB
    obtain ⟨k2, hk2⟩ := (e_eq_one_iff_dvd (M_ne M) _).1 hB
    ring_nf at hk2
    rw [hX0] at hk2
    ring_nf at hk2
    obtain ⟨t, ht⟩ : ((M : ℕ) : ℤ) ∣ ((g.2.val : ℕ) : ℤ) := ⟨-k2, by linear_combination -hk2⟩
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-t, ?_⟩
    have hgt : g = coordinate M 0 ((M : ℤ) * t) := by
      rw [G_eq_val_cast M g]
      simp only [coordinate]
      refine Prod.ext ?_ ?_
      · rw [hX0]
      · rw [ht]
    rw [hgt, hgen]
    simp only [coordinate]
    rw [smul_cast_pair M (-t) 0 (-(M : ℤ))]
    refine Prod.ext ?_ ?_
    · simp
    · rw [Int.neg_mul_neg, Int.mul_comm t ((M : ℕ) : ℤ)]
  · obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hiota : iota M h = coordinate M (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ))
        ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)) := rfl
    rw [← hz, pairing_annihilatorGenerator M z (iota M h), hiota,
      e_eq_one_iff_dvd (cofactor_ne M)]
    simp only [coordinate]
    refine dvd_mul_of_dvd_right ?_ (-z)
    exact dvd_val_cast ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)) ((cofactor M : ℕ) : ℤ)
      (by refine ⟨((M : ℕ) : ℤ), ?_⟩; rw [longModulus_cast M, cofactor_cast M]; ring)
      ⟨((h.2.val : ℕ) : ℤ), rfl⟩
private theorem e_pow_nat {N : ℕ} (k : ℤ) (n : ℕ) :
    L2a.e N (((n : ℕ) : ℤ) * k) = (L2a.e N k) ^ n := by
  induction n with
  | zero => simp [L2a.e]
  | succ n ih =>
    have hcast : (((n + 1 : ℕ) : ℤ) * k) = (((n : ℕ) : ℤ) * k) + k := by
      push_cast
      ring
    rw [hcast, ← L2a.e_mul, ih, pow_succ]

private theorem nsmul_val' {n : ℕ} [NeZero n] (k : ℕ) (a : ZMod n) :
    ((k • a : ZMod n)).val = k * a.val % n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_smul, one_smul, ZMod.val_add, ih, Nat.add_comm (k * a.val % n) a.val,
      Nat.add_mod_mod, Nat.add_mul, one_mul, Nat.add_comm a.val (k * a.val)]

private theorem zsmul_cast_nat (n : ℕ) (a : G M) :
    ((n : ℕ) : ℤ) • a = n • a := by
  simp

private theorem mem_range_iff (g : G M) :
    g ∈ (iota M).range ↔ ((cofactor M : ℕ) : ℤ) ∣ ((g.2.val : ℕ) : ℤ) := by
  have hset := iota_range_eq_torsion M
  constructor
  · intro h
    have h0 : ((M : ℕ) • g : G M) = 0 := by
      have h' : g ∈ ((iota M).range : Set (G M)) := h
      rw [hset] at h'
      exact h'
    have hs : ((M : ℕ) • g.2 : ZMod (longModulus M)) = 0 := by
      have h1 := congrArg Prod.snd h0
      simpa using h1
    have hv0 : M * g.2.val % (longModulus M) = 0 := by
      have h2 := congrArg ZMod.val hs
      rwa [nsmul_val', ZMod.val_zero] at h2
    have hdd : (longModulus M) ∣ (M * g.2.val) := Nat.dvd_of_mod_eq_zero hv0
    exact (Int.natCast_dvd_natCast).mpr
      (Nat.dvd_of_mul_dvd_mul_left (by have := Fact.out (p := 4 ≤ M); omega) hdd)
  · intro hdvd
    have h' : g ∈ {g : G M | (M : ℕ) • g = 0} := by
      show ((M : ℕ) • g : G M) = 0
      have hd : (cofactor M : ℕ) ∣ g.2.val := Int.natCast_dvd_natCast.mp hdvd
      refine Prod.ext ?_ ?_
      · show ((M : ℕ) • g.1 : ZMod M) = 0
        apply ZMod.val_injective
        rw [nsmul_val', Nat.mul_mod_right, ZMod.val_zero]
      · show ((M : ℕ) • g.2 : ZMod (longModulus M)) = 0
        apply ZMod.val_injective
        rw [nsmul_val', ZMod.val_zero]
        exact Nat.mod_eq_zero_of_dvd (mul_dvd_mul_left M hd)
    rw [← hset] at h'
    exact h'

/-- The averaging step in (40). The sum has one term when M=4. -/
theorem character_filter (g : G M) :
    (∑ j : Fin (cofactor M),
      metricPairing (gaussian M) (j.val • annihilatorGenerator M) g) /
        (cofactor M : ℂ) = if g ∈ (iota M).range then 1 else 0 := by
  have hmne : ((cofactor M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (cofactor_ne M)
  have hterm : ∀ j : Fin (cofactor M),
      metricPairing (gaussian M) (j.val • annihilatorGenerator M) g =
        L2a.e (cofactor M) (-((j.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) := by
    intro j
    rw [← zsmul_cast_nat]
    exact pairing_annihilatorGenerator M ((j.val : ℕ) : ℤ) g
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    Fin.sum_univ_eq_sum_range
      (fun i => L2a.e (cofactor M) (-((i : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)))]
  set c : ℂ := L2a.e (cofactor M) (-((g.2.val : ℕ) : ℤ)) with hc
  have hpow : ∀ i : ℕ,
      L2a.e (cofactor M) (-((i : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) = c ^ i := by
    intro i
    have hneg : (-((i : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) =
        ((i : ℕ) : ℤ) * (-((g.2.val : ℕ) : ℤ)) := by ring
    rw [hneg, e_pow_nat, ← hc]
  rw [Finset.sum_congr rfl (fun i _ => hpow i)]
  have hcm : c ^ (cofactor M) = 1 := by
    rw [hc, ← e_pow_nat]
    exact (e_eq_one_iff_dvd (cofactor_ne M) _).2 ⟨-((g.2.val : ℕ) : ℤ), rfl⟩
  by_cases hc1 : c = 1
  · have hdvd : ((cofactor M : ℕ) : ℤ) ∣ ((g.2.val : ℕ) : ℤ) := by
      have h1 := (e_eq_one_iff_dvd (cofactor_ne M) _).1 hc1
      obtain ⟨k, hk⟩ := h1
      exact ⟨-k, by linear_combination -hk⟩
    have hsum : (∑ i ∈ Finset.range (cofactor M), c ^ i) = ((cofactor M : ℕ) : ℂ) := by
      rw [hc1]
      simp
    rw [if_pos ((mem_range_iff M g).mpr hdvd), hsum, div_self hmne]
  · have hnd : ¬ (((cofactor M : ℕ) : ℤ) ∣ ((g.2.val : ℕ) : ℤ)) := by
      intro hdvd
      apply hc1
      rw [hc]
      refine (e_eq_one_iff_dvd (cofactor_ne M) _).2 ?_
      obtain ⟨k, hk⟩ := hdvd
      exact ⟨-k, by linear_combination -hk⟩
    rw [if_neg (fun hin => hnd ((mem_range_iff M g).mp hin)), geom_sum_eq hc1, hcm, sub_self,
      zero_div, zero_div]

theorem sum_character_filter (f : G M → ℂ) :
    (∑ j : Fin (cofactor M), ∑ g : G M,
      f g * metricPairing (gaussian M) (j.val • annihilatorGenerator M) g) =
      (cofactor M : ℂ) * ∑ h : L2a.Index M, f (iota M h) := by
  have hmne : ((cofactor M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (cofactor_ne M)
  have ht2 : ∀ (j : Fin (cofactor M)) (g : G M),
      metricPairing (gaussian M) (j.val • annihilatorGenerator M) g =
        L2a.e (cofactor M) (-((j.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) := by
    intro j g
    rw [← zsmul_cast_nat]
    exact pairing_annihilatorGenerator M ((j.val : ℕ) : ℤ) g
  have hcf : ∀ g : G M,
      (∑ j : Fin (cofactor M),
        L2a.e (cofactor M) (-((j.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ))) =
        ((cofactor M : ℕ) : ℂ) * (if g ∈ (iota M).range then 1 else 0) := by
    intro g
    have h0 := character_filter M g
    rw [Finset.sum_congr rfl (fun j _ => ht2 j g)] at h0
    rw [← h0, mul_div_cancel₀ _ hmne]
  have hint : ∀ g : G M,
      f g * (((cofactor M : ℕ) : ℂ) * (if g ∈ (iota M).range then 1 else 0)) =
        ((cofactor M : ℕ) : ℂ) * (if g ∈ (iota M).range then f g else 0) := by
    intro g
    by_cases hg : g ∈ (iota M).range
    · rw [if_pos hg, if_pos hg, mul_one, mul_comm]
    · rw [if_neg hg, if_neg hg, mul_zero, mul_zero]
  have hterm2 : ∀ (j : Fin (cofactor M)) (g : G M),
      f g * metricPairing (gaussian M) (j.val • annihilatorGenerator M) g =
        f g * L2a.e (cofactor M) (-((j.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) := fun j g => by
    rw [ht2 j g]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun j _ => hterm2 j g))]
  simp only [← Finset.mul_sum, hcf, hint]
  congr 1
  rw [← Finset.sum_filter]
  have himg : (Finset.univ.filter (fun x : G M => x ∈ (iota M).range)) =
      Finset.univ.image (iota M) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      AddMonoidHom.mem_range]
  rw [himg, Finset.sum_image]
  exact fun _ _ _ _ hab => iota_injective M hab

end SICLean.L2b
