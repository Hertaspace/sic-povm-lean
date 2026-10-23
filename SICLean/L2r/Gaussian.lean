import SICLean.L2r.Group

set_option autoImplicit false

/-!
# The Gaussian and character projection

The explicit polynomial is [RW-rec, Def. 1, (2)].
Its polarization is [RW-rec, (3)]. These are conclusions, never inputs on E.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2r

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def alternating (z w : QuadraticCoordinates) : ℚ := z.1 * w.2 - z.2 * w.1

def periodDifference (d r : ℕ) (x y : ℤ) : ℤ × ℤ :=
  (gap d r * x + (r : ℤ) * y,
    (((ell d r : ℤ) - 1) * r - ((d : ℤ) - r)) * x +
      ((d : ℤ) - r - (ell d r : ℤ) * r) * y)

def gaussianLift (d r : ℕ) (x y : ℤ) : ℂ :=
  (-1 : ℂ) ^ (x + y + x * y) *
    L2a.e (2 * longModulus d r)
      (gap d r * (-(cofactor d r : ℤ) * x ^ 2 + (cofactor d r : ℤ) * x * y + y ^ 2))

def gaussian (d r : ℕ) (g : G d r) : ℂ := gaussianLift d r g.1.val g.2.val

def pairingLift (d r : ℕ) (x y X Y : ℤ) : ℂ :=
  L2a.e (longModulus d r)
    (-(cofactor d r : ℤ) * gap d r * x * X -
      (cofactor d r : ℤ) * r * (x * Y + y * X) + gap d r * y * Y)

def quadraticForm (d r : ℕ) (p : ℤ × ℤ) : ℤ :=
  p.1 ^ 2 - (ell d r : ℤ) * p.1 * p.2 + p.2 ^ 2

def torsionGaussian (d r : ℕ) (p : Index d) : ℂ :=
  L2a.e d ((r : ℤ) * quadraticForm d r (lift p))


private theorem conicZ {d r : ℕ} (h : Admissible d r) :
    (gap d r) ^ 2 - ((cofactor d r : ℕ) : ℤ) * (r : ℤ) * ((d : ℤ) - r) = 1 := by
  have hp := principal_conic h
  have he : ((ell d r : ℕ) : ℤ) = (level d r : ℤ) - 2 := by
    have h5 := level_ge_five h
    rw [ell, Nat.cast_sub (by omega : 2 ≤ level d r)]; norm_num
  have hc : ((cofactor d r : ℕ) : ℤ) = (level d r : ℤ) - 4 := by
    have h5 := level_ge_five h
    rw [cofactor, Nat.cast_sub (by omega : 4 ≤ level d r)]; norm_num
  rw [he] at hp; rw [gap, hc]; linear_combination hp
private theorem cofactor_castQ {d r : ℕ} (h : Admissible d r) :
    ((cofactor d r : ℕ) : ℚ) = (level d r : ℚ) - 4 := by
  have h5 := level_ge_five h
  rw [cofactor, Nat.cast_sub (by omega : 4 ≤ level d r)]; norm_num
private theorem ell_castQ {d r : ℕ} (h : Admissible d r) :
    ((ell d r : ℕ) : ℚ) = (level d r : ℚ) - 2 := by
  have h5 := level_ge_five h
  rw [ell, Nat.cast_sub (by omega : 2 ≤ level d r)]; norm_num
private theorem longModulus_castQ {d r : ℕ} (h : Admissible d r) :
    ((longModulus d r : ℕ) : ℚ) = (d : ℚ) * ((level d r : ℚ) - 4) := by
  rw [longModulus, Nat.cast_mul, cofactor_castQ h]

private theorem cofactor_castQ_eq {d r : ℕ} (h : Admissible d r) :
    ((cofactor d r : ℕ) : ℚ) = (ell d r : ℚ) - 2 := by
  rw [cofactor_castQ h, ell_castQ h]; ring

private theorem conicQ {d r : ℕ} (h : Admissible d r) :
    (gap d r : ℚ) ^ 2 - ((cofactor d r : ℕ) : ℚ) * (r : ℚ) * ((d : ℚ) - r) = 1 := by
  have hZ := conicZ h
  have hZq : ((gap d r : ℚ)) ^ 2 - (((cofactor d r : ℕ) : ℤ) : ℚ) * (r:ℚ) * ((d:ℚ)-r) = 1 := by
    have := congrArg (fun z : ℤ => (z:ℚ)) hZ
    push_cast at this
    exact this
  push_cast at hZq
  exact hZq

private theorem gamma00x {d r : ℕ} :
    gamma d r (0:Fin 2) (0:Fin 2) = (ell d r : ℤ) * ((d:ℤ)-r)^2 - 2*((d:ℤ)-r)*(r:ℤ) := by
  simp [gamma, beta, alpha, pow_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
private theorem gamma10x {d r : ℕ} :
    gamma d r (1:Fin 2) (0:Fin 2) = ((d:ℤ)-r)^2 - (r:ℤ)^2 := by
  simp [gamma, beta, alpha, pow_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
private theorem gamma01x {d r : ℕ} :
    gamma d r (0:Fin 2) (1:Fin 2) = (r:ℤ)^2 - ((d:ℤ)-r)^2 := by
  simp [gamma, beta, alpha, pow_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
private theorem gamma11x {d r : ℕ} :
    gamma d r (1:Fin 2) (1:Fin 2) = (ell d r : ℤ) * (r:ℤ)^2 - 2*((d:ℤ)-r)*(r:ℤ) := by
  simp [gamma, beta, alpha, pow_two, Matrix.mul_apply, Fin.sum_univ_two]; ring


private theorem d_ne_zero {d r : ℕ} (h : Admissible d r) : d ≠ 0 := by
  have := h.main_range; omega

private theorem cofactor_ne_zero {d r : ℕ} (h : Admissible d r) : cofactor d r ≠ 0 := by
  have h5 := level_ge_five h
  unfold cofactor; omega

private theorem longModulus_ne_zero {d r : ℕ} (h : Admissible d r) : longModulus d r ≠ 0 := by
  have h5 := level_ge_five h
  have hd : 0 < d := by have := h.main_range; omega
  have hc : 0 < cofactor d r := by unfold cofactor; omega
  unfold longModulus
  positivity

private theorem ell_cast_level {d r : ℕ} (h : Admissible d r) :
    ((ell d r : ℕ) : ℤ) = (level d r : ℤ) - 2 := by
  have h5 := level_ge_five h
  rw [ell, Nat.cast_sub (by omega : 2 ≤ level d r)]
  norm_num

private theorem cofactor_cast_level {d r : ℕ} (h : Admissible d r) :
    ((cofactor d r : ℕ) : ℤ) = (level d r : ℤ) - 4 := by
  have h5 := level_ge_five h
  rw [cofactor, Nat.cast_sub (by omega : 4 ≤ level d r)]
  norm_num

private theorem cofactor_castZ {d r : ℕ} (h : Admissible d r) :
    ((cofactor d r : ℕ) : ℤ) = (ell d r : ℤ) - 2 := by
  rw [cofactor_cast_level h, ell_cast_level h]
  ring

private theorem e_ne_zero (N : ℕ) (t : ℤ) : L2a.e N t ≠ 0 := by
  rw [L2a.e_eq_omega_zpow]
  exact zpow_ne_zero _ (omega_ne_zero N)

private theorem e_eq_one_iff_dvd {N : ℕ} (hN : N ≠ 0) (t : ℤ) :
    L2a.e N t = 1 ↔ ((N : ℕ) : ℤ) ∣ t := by
  rw [L2a.e_eq_omega_zpow]
  constructor
  · intro h
    by_contra hc
    have : NeZero N := ⟨hN⟩
    exact omega_ne_one_of_not_dvd hc h
  · exact omega_zpow_dvd N

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

private theorem neg_one_eq2n {d r : ℕ} (h : Admissible d r) (t : ℤ) :
    (-1 : ℂ) ^ t = L2a.e (2 * longModulus d r) ((longModulus d r : ℤ) * t) := by
  rw [← e_two_eq_neg_one]
  exact e_mod_cast (longModulus d r) 2 (2 * longModulus d r)
    (longModulus_ne_zero h) two_ne_zero (by ring) t


private theorem periodDifference_eq_aux {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    actOnCoordinates (gamma d r) (pointLift d r x y) - pointLift d r x y =
      (((periodDifference d r x y).1 : ℚ), ((periodDifference d r x y).2 : ℚ)) := by
  have hn : ((longModulus d r : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast longModulus_ne_zero h
  apply Prod.ext
  · apply mul_left_cancel₀ hn
    simp only [actOnCoordinates, pointLift, periodDifference, Prod.fst_sub, gamma00x, gamma10x,
      cofactor_castQ_eq h]
    push_cast
    field_simp
    rw [longModulus_castQ h, ell_castQ h]
    push_cast
    set L : ℚ := (level d r : ℚ) with hL
    have hc0 : (gap d r:ℚ)^2 - ((level d r:ℚ) - 4)*(r:ℚ)*((d:ℚ)-r) = 1 := by
      simpa [cofactor_castQ h] using conicQ h
    have hc' : (d:ℚ)^2 - L*(r:ℚ)*((d:ℚ)-r) = 1 := by
      rw [hL]; unfold gap at hc0; push_cast at hc0; linear_combination hc0
    simp only [gap] at hc' ⊢
    push_cast at hc' ⊢
    ring_nf at hc' ⊢
    linear_combination (y:ℚ) * hc'
  · apply mul_left_cancel₀ hn
    simp only [actOnCoordinates, pointLift, periodDifference, Prod.fst_sub, Prod.snd_sub, gamma01x, gamma11x,
      cofactor_castQ_eq h]
    push_cast
    field_simp
    rw [longModulus_castQ h, ell_castQ h]
    push_cast
    set L : ℚ := (level d r : ℚ) with hL
    have hc0 : (gap d r:ℚ)^2 - ((level d r:ℚ) - 4)*(r:ℚ)*((d:ℚ)-r) = 1 := by
      simpa [cofactor_castQ h] using conicQ h
    have hc' : (d:ℚ)^2 - L*(r:ℚ)*((d:ℚ)-r) = 1 := by
      rw [hL]; unfold gap at hc0; push_cast at hc0; linear_combination hc0
    push_cast at hc' ⊢
    ring_nf at hc' ⊢
    linear_combination (((level d r:ℚ) - 2) * x - ((level d r:ℚ) - 2) * y - 2*x + y) * hc'

private def gExp (d r : ℕ) (x y : ℤ) : ℤ :=
  gap d r * (-(cofactor d r : ℤ) * x ^ 2 + (cofactor d r : ℤ) * x * y + y ^ 2) +
    (longModulus d r : ℤ) * (x + y + x * y)

private theorem gaussianLift_eq_exp {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    gaussianLift d r x y = L2a.e (2 * longModulus d r) (gExp d r x y) := by
  have hn := longModulus_ne_zero h
  rw [gaussianLift, neg_one_eq2n h (x + y + x * y), L2a.e_mul]
  congr 1
  simp only [gExp]
  ring

private theorem even_q0_iff (a b : ℤ) : Even (a + b + a * b) ↔ Even a ∧ Even b := by
  constructor
  · intro h
    rcases Int.even_or_odd a with ha | ha
    · rcases Int.even_or_odd b with hb | hb
      · exact ⟨ha, hb⟩
      · exfalso
        obtain ⟨m, hm⟩ := h
        obtain ⟨ka, hka⟩ := ha
        obtain ⟨kb, hkb⟩ := hb
        rw [hka, hkb] at hm
        ring_nf at hm
        omega
    · rcases Int.even_or_odd b with hb | hb
      · exfalso
        obtain ⟨m, hm⟩ := h
        obtain ⟨ka, hka⟩ := ha
        obtain ⟨kb, hkb⟩ := hb
        rw [hka, hkb] at hm
        ring_nf at hm
        omega
      · exfalso
        obtain ⟨m, hm⟩ := h
        obtain ⟨ka, hka⟩ := ha
        obtain ⟨kb, hkb⟩ := hb
        rw [hka, hkb] at hm
        ring_nf at hm
        omega
  · rintro ⟨ha, hb⟩
    obtain ⟨ka, hka⟩ := ha
    obtain ⟨kb, hkb⟩ := hb
    exact ⟨ka + kb + 2 * ka * kb, by rw [hka, hkb]; ring⟩

private theorem even_q0_rowAction {a b c d : ℤ} (hdet : a * d - b * c = 1) (x y : ℤ) :
    Even ((a * x + b * y) + (c * x + d * y) + (a * x + b * y) * (c * x + d * y)) ↔
      Even (x + y + x * y) := by
  rw [even_q0_iff, even_q0_iff]
  constructor
  · rintro ⟨hX, hY⟩
    constructor
    · obtain ⟨k, hk⟩ := hX
      obtain ⟨m, hm⟩ := hY
      refine ⟨d * k - b * m, ?_⟩
      linear_combination -x * hdet + d * hk - b * hm
    · obtain ⟨k, hk⟩ := hX
      obtain ⟨m, hm⟩ := hY
      refine ⟨a * m - c * k, ?_⟩
      linear_combination -y * hdet + a * hm - c * hk
  · rintro ⟨hx, hy⟩
    constructor
    · obtain ⟨k, hk⟩ := hx
      obtain ⟨m, hm⟩ := hy
      exact ⟨a * k + b * m, by rw [hk, hm]; ring⟩
    · obtain ⟨k, hk⟩ := hx
      obtain ⟨m, hm⟩ := hy
      exact ⟨c * k + d * m, by rw [hk, hm]; ring⟩

private theorem even_sub_of_iff {p q : ℤ} (h : Even p ↔ Even q) : Even (p - q) := by
  rcases Int.even_or_odd p with hp | hp
  · obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := h.mp ⟨a, ha⟩
    exact ⟨a - b, by rw [ha, hb]; ring⟩
  · have hq : Odd q := by
      rcases Int.even_or_odd q with hq | hq
      · exfalso
        obtain ⟨c, hc⟩ := h.mpr hq
        obtain ⟨d, hd⟩ := hp
        rw [hd] at hc
        omega
      · exact hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a - b, by rw [ha, hb]; ring⟩

/-- The period matrix, whose row action is `periodDifference`. -/
private def periodMatrix (d r : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![gap d r, ((ell d r : ℤ) - 1) * (r : ℤ) - ((d : ℤ) - r);
    (r : ℤ), ((d : ℤ) - r) - (ell d r : ℤ) * (r : ℤ)]

private theorem periodDifference_rowAction (d r : ℕ) (x y : ℤ) :
    periodDifference d r x y = rowAction (periodMatrix d r) (x, y) := by
  apply Prod.ext <;> simp [periodDifference, periodMatrix, rowAction] <;> ring

private theorem periodMatrix_det {d r : ℕ} (h : Admissible d r) :
    (periodMatrix d r).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [periodMatrix]
  simp only [gap]
  linear_combination principal_conic h


private theorem alternating_eq {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    alternating (pointLift d r x y) (actOnCoordinates (gamma d r) (pointLift d r x y)) =
      ((gap d r * (-(cofactor d r : ℤ) * x ^ 2 + (cofactor d r : ℤ) * x * y + y ^ 2) : ℤ) : ℚ) /
        (longModulus d r : ℚ) := by
  have hn : ((longModulus d r : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast longModulus_ne_zero h
  have hc : ((cofactor d r : ℕ) : ℚ) = (ell d r : ℚ) - 2 := by
    rw [cofactor_castQ h, ell_castQ h]
    ring
  apply mul_left_cancel₀ hn
  simp only [alternating, actOnCoordinates, pointLift, gamma00x, gamma01x, gamma10x, gamma11x, Prod.fst_sub,
    Prod.snd_sub]
  field_simp
  rw [show ((longModulus d r : ℕ) : ℚ) = (d : ℚ) * ((cofactor d r : ℕ) : ℚ) by rw [longModulus, Nat.cast_mul]]
  push_cast
  rw [hc]
  simp only [gap]
  push_cast
  ring

private theorem gaussian_rw_formula_aux {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    gaussianLift d r x y =
      (-1 : ℂ) ^ ((periodDifference d r x y).1 + (periodDifference d r x y).2 +
        (periodDifference d r x y).1 * (periodDifference d r x y).2) *
      Complex.exp (Real.pi * Complex.I *
        (alternating (pointLift d r x y)
          (actOnCoordinates (gamma d r) (pointLift d r x y)) : ℂ)) := by
  set E : ℤ := gap d r * (-(cofactor d r : ℤ) * x ^ 2 + (cofactor d r : ℤ) * x * y + y ^ 2) with hE
  set P : ℤ := (periodDifference d r x y).1 + (periodDifference d r x y).2 +
    (periodDifference d r x y).1 * (periodDifference d r x y).2 with hP
  have halt : alternating (pointLift d r x y) (actOnCoordinates (gamma d r) (pointLift d r x y))
      = (E : ℚ) / (longModulus d r : ℚ) := by rw [hE]; exact alternating_eq h x y
  have hexp : Complex.exp (Real.pi * Complex.I * ((E : ℂ) / (longModulus d r : ℂ))) =
      L2a.e (2 * longModulus d r) E := by
    have hnC : ((longModulus d r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast longModulus_ne_zero h
    rw [L2a.e]
    congr 1
    push_cast
    field_simp
  rw [gaussianLift_eq_exp h x y, halt]
  push_cast
  rw [hexp]
  rw [neg_one_eq2n h P, L2a.e_mul]
  have hProw : ((periodMatrix d r 0 0 * x + periodMatrix d r 1 0 * y) +
      (periodMatrix d r 0 1 * x + periodMatrix d r 1 1 * y) +
      (periodMatrix d r 0 0 * x + periodMatrix d r 1 0 * y) *
      (periodMatrix d r 0 1 * x + periodMatrix d r 1 1 * y)) = P := by
    rw [hP, periodDifference_rowAction]
    simp [rowAction, periodMatrix]
    ring
  have hiff : Even P ↔ Even (x + y + x * y) := by
    have hdet : periodMatrix d r 0 0 * periodMatrix d r 1 1 -
        periodMatrix d r 1 0 * periodMatrix d r 0 1 = 1 := by
      have hh := periodMatrix_det h
      rw [Matrix.det_fin_two] at hh
      linear_combination hh
    have hrow := even_q0_rowAction (a := periodMatrix d r 0 0) (b := periodMatrix d r 1 0)
      (c := periodMatrix d r 0 1) (d := periodMatrix d r 1 1) hdet x y
    rwa [hProw] at hrow
  have hpar : Even (P - (x + y + x * y)) := even_sub_of_iff hiff
  obtain ⟨w, hw⟩ := hpar
  have hdvd : ((2 * longModulus d r : ℕ) : ℤ) ∣
      gExp d r x y - ((longModulus d r : ℤ) * P + E) := by
    refine ⟨-w, ?_⟩
    simp only [gExp, hE]
    push_cast
    linear_combination (-(longModulus d r : ℤ)) * hw
  exact L2a.e_eq_of_dvd hdvd

private theorem longModulus_castQ2 {d r : ℕ} (h : Admissible d r) :
    ((longModulus d r : ℕ) : ℚ) = (d : ℚ) * ((cofactor d r : ℕ) : ℚ) := by
  rw [longModulus, Nat.cast_mul]

private theorem longModulus_castZ {d r : ℕ} (h : Admissible d r) :
    ((longModulus d r : ℕ) : ℤ) = (d : ℤ) * ((cofactor d r : ℕ) : ℤ) := by
  rw [longModulus, Nat.cast_mul]

private theorem even_mul_pred_self (t : ℤ) : Even (t * (t - 1)) := by
  rcases Int.even_or_odd t with h | h
  · exact Int.even_mul.mpr (Or.inl h)
  · exact Int.even_mul.mpr (Or.inr (Int.even_sub_one.mpr (Int.not_even_iff_odd.mpr h)))

private theorem even_mul_succ_self (t : ℤ) : Even (t * (t + 1)) := by
  rcases Int.even_or_odd t with h | h
  · exact Int.even_mul.mpr (Or.inl h)
  · exact Int.even_mul.mpr (Or.inr (Int.even_add_one.mpr (Int.not_even_iff_odd.mpr h)))

private theorem gaussian_periodic_aux {d r : ℕ} (h : Admissible d r) (x y k l : ℤ) :
    gaussianLift d r (x + (d : ℤ) * k) (y + (longModulus d r : ℤ) * l) =
      gaussianLift d r x y := by
  rw [gaussianLift_eq_exp h, gaussianLift_eq_exp h]
  apply L2a.e_eq_of_dvd
  set c : ℤ := (cofactor d r : ℤ) with hcdef
  set E0 : ℤ := -c * (d:ℤ)^2 * k * l + c * (d:ℤ) * k * l * (r:ℤ) + c * (d:ℤ) * l^2 * (r:ℤ)
    - c * (d:ℤ) * l * x + c * l * (r:ℤ) * x - (d:ℤ) * k^2 * (r:ℤ) + (d:ℤ) * k * x
    - (d:ℤ) * k * y - (d:ℤ) * l * y - 2 * k * (r:ℤ) * x + k * (r:ℤ) * y + 2 * l * (r:ℤ) * y with hE0
  have h1 : Even ((d:ℤ) * k * ((d:ℤ) * k - 1)) := even_mul_pred_self _
  have h2 : Even (c * (d:ℤ) * l * ((d:ℤ) * l + 1)) := by
    have := even_mul_succ_self ((d:ℤ) * l)
    obtain ⟨a, ha⟩ := this
    exact ⟨c * a, by linear_combination c * ha⟩
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨-(a - b + E0), ?_⟩
  have hD : gExp d r (x + (d:ℤ) * k) (y + (longModulus d r : ℤ) * l) - gExp d r x y =
      -(c * (d:ℤ)) * ((d:ℤ) * k * ((d:ℤ) * k - 1) - c * (d:ℤ) * l * ((d:ℤ) * l + 1) + 2 * E0) := by
    simp only [gExp]
    rw [longModulus_castZ h, ← hcdef]
    simp only [gap]
    push_cast
    ring
  have hG : (d:ℤ) * k * ((d:ℤ) * k - 1) - c * (d:ℤ) * l * ((d:ℤ) * l + 1) + 2 * E0
      = 2 * (a - b + E0) := by
    linear_combination ha - hb
  rw [hD, hG]
  push_cast
  rw [longModulus_castZ h]
  ring

private theorem gaussian_eq_lift_aux (d r : ℕ) [Fact (Admissible d r)] (x y : ℤ) :
    gaussian d r (coordinate d r x y) = gaussianLift d r x y := by
  have h : Admissible d r := Fact.out
  haveI : NeZero d := ⟨d_ne_zero h⟩
  have hn : ((longModulus d r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast longModulus_ne_zero h
  have hvx : ((d : ℕ) : ℤ) ∣ ((((x : ZMod d).val : ℕ) : ℤ)) - x := by
    have hv : ((((x : ZMod d).val : ℕ) : ℤ)) = x % ((d : ℕ) : ℤ) := ZMod.val_intCast x
    refine ⟨-(x / ((d : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv x ((d : ℕ) : ℤ)]
  have hvy : ((longModulus d r : ℕ) : ℤ) ∣ ((((y : ZMod (longModulus d r)).val : ℕ) : ℤ)) - y := by
    have hv : ((((y : ZMod (longModulus d r)).val : ℕ) : ℤ)) = y % ((longModulus d r : ℕ) : ℤ) :=
      ZMod.val_intCast y
    refine ⟨-(y / ((longModulus d r : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv y ((longModulus d r : ℕ) : ℤ)]
  obtain ⟨k, hk⟩ := hvx
  obtain ⟨l, hl⟩ := hvy
  show gaussianLift d r ((((x : ZMod d).val : ℕ) : ℤ)) ((((y : ZMod (longModulus d r)).val : ℕ) : ℤ)) =
    gaussianLift d r x y
  rw [show ((((x : ZMod d).val : ℕ) : ℤ)) = x + (d : ℤ) * k from by linear_combination hk,
    show ((((y : ZMod (longModulus d r)).val : ℕ) : ℤ)) = y + (longModulus d r : ℤ) * l from by
      linear_combination hl]
  exact gaussian_periodic_aux (d := d) (r := r) h x y k l

private theorem pairingLift_eq_exp {d r : ℕ} (h : Admissible d r) (x y X Y : ℤ) :
    pairingLift d r x y X Y =
      L2a.e (2 * longModulus d r)
        (2 * (-(cofactor d r : ℤ) * gap d r * x * X -
          (cofactor d r : ℤ) * (r : ℤ) * (x * Y + y * X) + gap d r * y * Y)) := by
  have hn := longModulus_ne_zero h
  rw [pairingLift]
  exact e_mod_cast 2 (longModulus d r) (2 * longModulus d r) two_ne_zero hn rfl _

private theorem pairing_formula_aux (d r : ℕ) [Fact (Admissible d r)] (x y X Y : ℤ) :
    L2b.metricPairing (gaussian d r) (coordinate d r x y) (coordinate d r X Y) =
      pairingLift d r x y X Y := by
  have h : Admissible d r := Fact.out
  have hn : longModulus d r ≠ 0 := longModulus_ne_zero h
  have hadd : coordinate d r x y + coordinate d r X Y = coordinate d r (x + X) (y + Y) := by
    apply Prod.ext <;> simp [coordinate]
  rw [L2b.metricPairing, hadd, gaussian_eq_lift_aux, gaussian_eq_lift_aux,
    gaussian_eq_lift_aux, pairingLift_eq_exp h]
  rw [gaussianLift_eq_exp h, gaussianLift_eq_exp h, gaussianLift_eq_exp h]
  rw [div_eq_mul_inv, mul_inv, L2a.e_inv, L2a.e_inv, ← mul_assoc, L2a.e_mul, L2a.e_mul]
  apply L2a.e_eq_of_dvd
  refine ⟨X * y + Y * x, ?_⟩
  simp only [gExp, gap]
  push_cast
  rw [longModulus_castZ h]
  ring

private theorem pairing_rw_formula_aux (d r : ℕ) [Fact (Admissible d r)] (x y X Y : ℤ) :
    pairingLift d r x y X Y = Complex.exp (2 * Real.pi * Complex.I *
      (alternating (pointLift d r x y -
        actOnCoordinates (gamma d r) (pointLift d r x y))
        (pointLift d r X Y) : ℂ)) := by
  have h : Admissible d r := Fact.out
  have hn : longModulus d r ≠ 0 := longModulus_ne_zero h
  set T : ℤ := (gap d r * x + (r:ℤ) * y) * (((ell d r : ℤ) - 2) * X - ((ell d r : ℤ) - 1) * Y) -
    ((((ell d r : ℤ) - 1) * (r:ℤ) - ((d:ℤ) - r)) * x + (((d:ℤ) - r) - (ell d r : ℤ) * (r:ℤ)) * y) * Y with hT
  have hc : ((cofactor d r : ℕ) : ℚ) = (ell d r : ℚ) - 2 := by
    rw [cofactor_castQ h, ell_castQ h]; ring
  have hsub : pointLift d r x y - actOnCoordinates (gamma d r) (pointLift d r x y) =
      -(((periodDifference d r x y).1 : ℚ), ((periodDifference d r x y).2 : ℚ)) := by
    have := congrArg Neg.neg (periodDifference_eq_aux h x y)
    simpa using this
  have halt : alternating (pointLift d r x y - actOnCoordinates (gamma d r) (pointLift d r x y))
      (pointLift d r X Y) = -(T : ℚ) / (longModulus d r : ℚ) := by
    have hnQ : ((longModulus d r : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hn
    rw [hsub]
    simp only [alternating, pointLift, T, periodDifference, Prod.fst_neg, Prod.snd_neg]
    field_simp
    push_cast
    rw [hc]
    simp only [gap]
    ring
  rw [halt]
  push_cast
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (-(T : ℂ) / (longModulus d r : ℂ))) =
      L2a.e (longModulus d r) (-T) := by
    have hnC : ((longModulus d r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [L2a.e]
    congr 1
    push_cast
    field_simp
  rw [hexp, pairingLift]
  rw [cofactor_castZ h]
  apply L2a.e_eq_of_dvd
  refine ⟨-(Y * x), ?_⟩
  simp only [T, gap]
  rw [longModulus_castZ h, cofactor_castZ h]
  ring


private theorem G_eq_coordinate {d r : ℕ} [Fact (Admissible d r)] (g : G d r) :
    g = coordinate d r (g.1.val : ℤ) (g.2.val : ℤ) := by
  have h : Admissible d r := Fact.out
  haveI : NeZero d := ⟨d_ne_zero h⟩
  haveI : NeZero (longModulus d r) := ⟨longModulus_ne_zero h⟩
  apply Prod.ext
  · exact ((ZMod.intCast_eq_iff d ((g.1.val : ℕ) : ℤ) g.1).2 ⟨0, by simp⟩).symm
  · exact ((ZMod.intCast_eq_iff (longModulus d r) ((g.2.val : ℕ) : ℤ) g.2).2 ⟨0, by simp⟩).symm

private theorem e_dvd_of_eq_one {N : ℕ} (hN : N ≠ 0) {t : ℤ} (h : L2a.e N t = 1) :
    ((N : ℕ) : ℤ) ∣ t :=
  (e_eq_one_iff_dvd hN t).1 h

private theorem gaussian_epsilon_aux (d r : ℕ) [Fact (Admissible d r)] (g : G d r) :
    gaussian d r (epsilonAut d r g) = gaussian d r g := by
  have h : Admissible d r := Fact.out
  have hn : longModulus d r ≠ 0 := longModulus_ne_zero h
  have heps : epsilonAut d r g =
      coordinate d r (((ell d r : ℤ) - 1) * (g.1.val : ℤ) + (g.2.val : ℤ))
        ((cofactor d r : ℤ) * (g.1.val : ℤ) + (g.2.val : ℤ)) := rfl
  have hRHS : gaussian d r g = gaussianLift d r (g.1.val : ℤ) (g.2.val : ℤ) := by
    conv_lhs => rw [G_eq_coordinate (d := d) (r := r) g]
    exact gaussian_eq_lift_aux d r _ _
  rw [heps, gaussian_eq_lift_aux, hRHS, gaussianLift_eq_exp h, gaussianLift_eq_exp h]
  apply L2a.e_eq_of_dvd
  set x : ℤ := (g.1.val : ℤ) with hx
  set y : ℤ := (g.2.val : ℤ) with hy
  set c : ℤ := (cofactor d r : ℤ) with hc
  have hce : c = (ell d r : ℤ) - 2 := by rw [hc]; exact cofactor_castZ h
  obtain ⟨pc, hpc⟩ := even_mul_succ_self c
  obtain ⟨py, hpy⟩ := even_mul_succ_self y
  refine ⟨pc * x ^ 2 + c * x * y + c * x + py, ?_⟩
  have hD : gExp d r (((ell d r : ℤ) - 1) * x + y) (c * x + y) - gExp d r x y =
      c * (d : ℤ) * (c * (c + 1) * x ^ 2 + 2 * c * x * y + 2 * c * x + y * (y + 1)) := by
    simp only [gExp, longModulus_castZ h, ← hc]
    rw [hce]
    simp only [gap]
    push_cast
    ring
  have hH : c * (c + 1) * x ^ 2 + 2 * c * x * y + 2 * c * x + y * (y + 1)
      = 2 * (pc * x ^ 2 + c * x * y + c * x + py) := by
    linear_combination hpc * x ^ 2 + hpy
  rw [hD, hH]
  rw [show ((2 * longModulus d r : ℕ) : ℤ) = 2 * (d : ℤ) * c from by
    rw [Nat.cast_mul, Nat.cast_two, longModulus_castZ h, ← hc]
    ring]
  ring

private theorem gaussian_iota_aux (d r : ℕ) [Fact (Admissible d r)] (p : Index d) :
    gaussian d r (iota d r p) = torsionGaussian d r p := by
  have h : Admissible d r := Fact.out
  have hn : longModulus d r ≠ 0 := longModulus_ne_zero h
  have hd : d ≠ 0 := d_ne_zero h
  have hcne : cofactor d r ≠ 0 := cofactor_ne_zero h
  have hiota : iota d r p =
      coordinate d r (((ell d r : ℤ) - 1) * (p.2.val : ℤ) - (p.1.val : ℤ))
        ((cofactor d r : ℤ) * (p.2.val : ℤ)) := rfl
  rw [hiota, gaussian_eq_lift_aux, gaussianLift_eq_exp h, torsionGaussian]
  have hscale : L2a.e d ((r : ℤ) * quadraticForm d r (lift p)) =
      L2a.e (2 * longModulus d r) ((2 * cofactor d r : ℕ) * ((r : ℤ) * quadraticForm d r (lift p))) := by
    refine e_mod_cast (2 * cofactor d r) d (2 * longModulus d r) ?_ hd ?_ _
    · omega
    · unfold longModulus; ring
  rw [hscale]
  apply L2a.e_eq_of_dvd
  set p1 : ℤ := (p.1.val : ℤ) with hp1
  set p2 : ℤ := (p.2.val : ℤ) with hp2
  set c : ℤ := (cofactor d r : ℤ) with hc
  have hce : c = (ell d r : ℤ) - 2 := by rw [hc]; exact cofactor_castZ h
  obtain ⟨pc, hpc⟩ := even_mul_succ_self c
  obtain ⟨p1e, hp1e⟩ := even_mul_succ_self p1
  obtain ⟨p2e, hp2e⟩ := even_mul_pred_self p2
  refine ⟨-( -pc * p2 ^ 2 - c * p2 + p1e - p1 * p2 + p2e), ?_⟩
  have hquad : quadraticForm d r (lift p) = p1 ^ 2 - (ell d r : ℤ) * p1 * p2 + p2 ^ 2 := by
    simp [quadraticForm, lift, hp1, hp2]
  have h2c : ((2 * cofactor d r : ℕ) : ℤ) = 2 * c := by
    rw [Nat.cast_mul, Nat.cast_two, ← hc]
  have hD : gExp d r (((ell d r : ℤ) - 1) * p2 - p1) (c * p2) -
      (2 * cofactor d r : ℕ) * ((r : ℤ) * quadraticForm d r (lift p)) =
      -(c * (d : ℤ)) * (-(c * (c + 1)) * p2 ^ 2 - 2 * c * p2 + (p1 * (p1 + 1)) - 2 * p1 * p2 + (p2 * (p2 - 1))) := by
    simp only [gExp, longModulus_castZ h, hquad, ← hp1, ← hp2]
    rw [h2c, ← hc, hce]
    simp only [gap]
    push_cast
    ring
  have hH : -(c * (c + 1)) * p2 ^ 2 - 2 * c * p2 + (p1 * (p1 + 1)) - 2 * p1 * p2 + (p2 * (p2 - 1))
      = 2 * (-pc * p2 ^ 2 - c * p2 + p1e - p1 * p2 + p2e) := by
    linear_combination -hpc * p2 ^ 2 + hp1e + hp2e
  rw [hD, hH]
  rw [show ((2 * longModulus d r : ℕ) : ℤ) = 2 * (d : ℤ) * c from by
    rw [Nat.cast_mul, Nat.cast_two, longModulus_castZ h, ← hc]
    ring]
  ring

private theorem level_eq_ell_add_two {d r : ℕ} (h : Admissible d r) : level d r = ell d r + 2 := by
  unfold ell
  have h5 := level_ge_five h
  omega

private theorem level_eq_cofactor_add_four {d r : ℕ} (h : Admissible d r) :
    (level d r : ℤ) = (cofactor d r : ℤ) + 4 := by
  rw [cofactor_castZ h, level_eq_ell_add_two h]; push_cast; ring


private theorem pairing_witnessY_aux (d r : ℕ) [Fact (Admissible d r)] (p q : Index d) :
    L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) =
      L2a.e d ((r : ℤ) * symplectic (lift p) (shiftedAlpha d r (lift q))) := by
  have h : Admissible d r := Fact.out
  have hn : longModulus d r ≠ 0 := longModulus_ne_zero h
  have hd : d ≠ 0 := d_ne_zero h
  have hc : cofactor d r ≠ 0 := cofactor_ne_zero h
  set p1 : ℤ := (p.1.val : ℤ) with hp1
  set p2 : ℤ := (p.2.val : ℤ) with hp2
  set q1 : ℤ := (q.1.val : ℤ) with hq1
  set q2 : ℤ := (q.2.val : ℤ) with hq2
  set c : ℤ := (cofactor d r : ℤ) with hcl
  have hce : c = (ell d r : ℤ) - 2 := by rw [hcl]; exact cofactor_castZ h
  have hY : witnessY d r p = coordinate d r p2 (p2 - p1) := by
    simp [witnessY, coordinate, hp1, hp2]
  have hI : iota d r q = coordinate d r (((ell d r : ℤ) - 1) * q2 - q1) (c * q2) := by
    rw [hq1, hq2, hcl]
    rfl
  have hsym : symplectic (lift p) (shiftedAlpha d r (lift q)) =
      -p1 * (q1 - ((ell d r : ℤ) + 1) * q2) + p2 * (-q1 - q2) := by
    simp [symplectic, shiftedAlpha, shift, lift, level_eq_ell_add_two h, hp1, hp2, hq1, hq2]
    ring
  rw [hY, hI, pairing_formula_aux, hsym]
  have hscale : L2a.e d ((r : ℤ) * (-p1 * (q1 - ((ell d r : ℤ) + 1) * q2) + p2 * (-q1 - q2))) =
      L2a.e (longModulus d r) (c * ((r : ℤ) * (-p1 * (q1 - ((ell d r : ℤ) + 1) * q2) + p2 * (-q1 - q2)))) := by
    refine e_mod_cast (cofactor d r) d (longModulus d r) hc hd ?_ _
    unfold longModulus; ring
  rw [hscale, pairingLift]
  apply L2a.e_eq_of_dvd
  refine ⟨-(c * p2 * q2 + p1 * q2 - p2 * q1), ?_⟩
  have hD : (-(cofactor d r : ℤ) * gap d r * p2 * (((ell d r : ℤ) - 1) * q2 - q1) -
      (cofactor d r : ℤ) * (r : ℤ) * (p2 * (c * q2) + (p2 - p1) * (((ell d r : ℤ) - 1) * q2 - q1)) +
      gap d r * (p2 - p1) * (c * q2)) -
      c * ((r : ℤ) * (-p1 * (q1 - ((ell d r : ℤ) + 1) * q2) + p2 * (-q1 - q2))) =
      -(c * (d : ℤ)) * (c * p2 * q2 + p1 * q2 - p2 * q1) := by
    simp only [gap]
    rw [← hcl, hce]
    ring
  have hDn : -(c * (d : ℤ)) * (c * p2 * q2 + p1 * q2 - p2 * q1) =
      (longModulus d r : ℤ) * (-(c * p2 * q2 + p1 * q2 - p2 * q1)) := by
    rw [longModulus_castZ h]
    ring
  rw [hD, hDn]

private theorem metricPairing_vals (d r : ℕ) [Fact (Admissible d r)] (g hh : G d r) :
    L2b.metricPairing (gaussian d r) g hh =
      pairingLift d r (g.1.val : ℤ) (g.2.val : ℤ) (hh.1.val : ℤ) (hh.2.val : ℤ) := by
  conv_lhs => rw [G_eq_coordinate (d := d) (r := r) g, G_eq_coordinate (d := d) (r := r) hh]
  exact pairing_formula_aux d r _ _ _ _

private theorem conic_gap_coprime {d r : ℕ} (h : Admissible d r) :
    IsCoprime (gap d r) ((cofactor d r : ℕ) : ℤ) := by
  refine ⟨gap d r, -((r : ℤ) * ((d : ℤ) - r)), ?_⟩
  have hc := conicZ h
  linear_combination hc

private theorem coprime_r_d {d r : ℕ} (h : Admissible d r) : IsCoprime (r : ℤ) (d : ℤ) := by
  have hdiv : (r : ℤ) ∣ (d : ℤ) ^ 2 - 1 := by
    have hN : (r : ℕ) ∣ d ^ 2 - 1 := dvd_trans (dvd_mul_right r (d - r)) h.divides
    have hZ := Int.natCast_dvd_natCast.mpr hN
    have h1 : 1 ≤ d ^ 2 := by have := h.main_range; nlinarith
    rw [Nat.cast_sub h1] at hZ
    push_cast at hZ
    exact hZ
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨-t, (d : ℤ), ?_⟩
  linear_combination ht

private theorem coprime_level_d {d r : ℕ} (h : Admissible d r) : IsCoprime (level d r : ℤ) (d : ℤ) := by
  have hid := level_identity h
  have hdiv : (level d r : ℤ) ∣ (d : ℤ) ^ 2 - 1 := by
    have hN : level d r ∣ d ^ 2 - 1 := by
      rw [← hid]; exact ⟨r * (d - r), by ring⟩
    have hZ := Int.natCast_dvd_natCast.mpr hN
    have h1 : 1 ≤ d ^ 2 := by have := h.main_range; nlinarith
    rw [Nat.cast_sub h1] at hZ
    push_cast at hZ
    exact hZ
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨-t, (d : ℤ), ?_⟩
  linear_combination ht

private theorem concrete_isMetricGaussian_aux (d r : ℕ) [Fact (Admissible d r)] :
    L2b.IsMetricGaussian (gaussian d r) := by
  have h : Admissible d r := Fact.out
  haveI : NeZero d := ⟨d_ne_zero h⟩
  have hn : longModulus d r ≠ 0 := longModulus_ne_zero h
  have hc : (cofactor d r : ℤ) ≠ 0 := by exact_mod_cast cofactor_ne_zero h
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast d_ne_zero h
  have hnz : ((longModulus d r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hn
  have hlev : (level d r : ℤ) = (cofactor d r : ℤ) + 4 := by
    rw [cofactor_castZ h, level_eq_ell_add_two h]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g
    conv_lhs => rw [G_eq_coordinate (d := d) (r := r) g]
    rw [gaussian_eq_lift_aux, gaussianLift]
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (e_ne_zero _ _)
  · intro g
    have hneg : -g = coordinate d r (-(g.1.val : ℤ)) (-(g.2.val : ℤ)) := by
      conv_lhs => rw [G_eq_coordinate (d := d) (r := r) g]
      apply Prod.ext <;> simp [coordinate]
    conv_lhs => rw [hneg]
    conv_rhs => rw [G_eq_coordinate (d := d) (r := r) g]
    rw [gaussian_eq_lift_aux, gaussian_eq_lift_aux, gaussianLift_eq_exp h, gaussianLift_eq_exp h]
    apply L2a.e_eq_of_dvd
    refine ⟨-((g.1.val : ℤ) + (g.2.val : ℤ)), ?_⟩
    simp only [gExp, gap]
    push_cast
    ring
  · intro x y z
    rw [G_eq_coordinate (d := d) (r := r) x, G_eq_coordinate (d := d) (r := r) y,
      G_eq_coordinate (d := d) (r := r) z]
    rw [show coordinate d r (x.1.val : ℤ) (x.2.val : ℤ) + coordinate d r (y.1.val : ℤ) (y.2.val : ℤ)
        = coordinate d r ((x.1.val : ℤ) + (y.1.val : ℤ)) ((x.2.val : ℤ) + (y.2.val : ℤ)) from by
      apply Prod.ext <;> simp [coordinate]]
    rw [pairing_formula_aux, pairing_formula_aux, pairing_formula_aux]
    simp only [pairingLift]
    rw [L2a.e_mul]
    apply L2a.e_eq_of_dvd
    refine ⟨0, ?_⟩
    simp only [gap]
    push_cast
    ring
  · intro x y z
    rw [G_eq_coordinate (d := d) (r := r) x, G_eq_coordinate (d := d) (r := r) y,
      G_eq_coordinate (d := d) (r := r) z]
    rw [show coordinate d r (y.1.val : ℤ) (y.2.val : ℤ) + coordinate d r (z.1.val : ℤ) (z.2.val : ℤ)
        = coordinate d r ((y.1.val : ℤ) + (z.1.val : ℤ)) ((y.2.val : ℤ) + (z.2.val : ℤ)) from by
      apply Prod.ext <;> simp [coordinate]]
    rw [pairing_formula_aux, pairing_formula_aux, pairing_formula_aux]
    simp only [pairingLift]
    rw [L2a.e_mul]
    apply L2a.e_eq_of_dvd
    refine ⟨0, ?_⟩
    simp only [gap]
    push_cast
    ring
  · intro x hx
    set a : ℤ := (x.1.val : ℤ) with ha
    set b : ℤ := (x.2.val : ℤ) with hb
    have hcx : x = coordinate d r a b := by rw [ha, hb]; exact G_eq_coordinate x
    have ha0 : 0 ≤ a := by rw [ha]; exact_mod_cast Nat.zero_le _
    have hb0 : 0 ≤ b := by rw [hb]; exact_mod_cast Nat.zero_le _
    have halt_a : a < (d : ℤ) := by rw [ha]; exact_mod_cast ZMod.val_lt x.1
    have halt_b : b < (longModulus d r : ℤ) := by rw [hb]; exact_mod_cast ZMod.val_lt x.2
    have h1 := hx (coordinate d r 1 0)
    rw [hcx] at h1
    rw [pairing_formula_aux] at h1
    simp only [pairingLift] at h1
    have h2 := hx (coordinate d r 0 1)
    rw [hcx] at h2
    rw [pairing_formula_aux] at h2
    simp only [pairingLift] at h2
    have hd1raw := e_dvd_of_eq_one hn h1
    have hd1 : ((longModulus d r : ℕ) : ℤ) ∣ -((cofactor d r : ℤ) * (gap d r * a + (r : ℤ) * b)) := by
      convert hd1raw using 1 <;> ring
    have hd2raw := e_dvd_of_eq_one hn h2
    have hd2 : ((longModulus d r : ℕ) : ℤ) ∣ -((cofactor d r : ℤ) * ((r : ℤ) * a)) + gap d r * b := by
      convert hd2raw using 1 <;> ring
    have hdn : ∀ X : ℤ, ((longModulus d r : ℕ) : ℤ) ∣ (cofactor d r : ℤ) * X → (d : ℤ) ∣ X := by
      intro X hX
      rw [longModulus_castZ h] at hX
      obtain ⟨k, hk⟩ := hX
      refine ⟨k, ?_⟩
      have hcc : (cofactor d r : ℤ) * X = (cofactor d r : ℤ) * ((d : ℤ) * k) := by
        linear_combination hk
      exact mul_left_cancel₀ hc hcc
    have hga : (d : ℤ) ∣ gap d r * a + (r : ℤ) * b :=
      hdn (gap d r * a + (r : ℤ) * b) (dvd_neg.mp hd1)
    have hcr : (d : ℤ) ∣ (cofactor d r : ℤ) * (r : ℤ) * a - gap d r * b := by
      have hdvd : (d : ℤ) ∣ ((longModulus d r : ℕ) : ℤ) := by
        rw [longModulus_castZ h]; exact ⟨(cofactor d r : ℤ), by ring⟩
      have h2' : (d : ℤ) ∣ -(-((cofactor d r : ℤ) * ((r : ℤ) * a)) + gap d r * b) :=
        dvd_trans hdvd (dvd_neg.mpr hd2)
      have heq : -(-((cofactor d r : ℤ) * ((r : ℤ) * a)) + gap d r * b) =
          (cofactor d r : ℤ) * (r : ℤ) * a - gap d r * b := by ring
      rwa [heq] at h2'
    have hrd : IsCoprime (d : ℤ) (r : ℤ) := (coprime_r_d h).symm
    have hb2a : (d : ℤ) ∣ b - 2 * a := by
      have h : (d : ℤ) ∣ (r : ℤ) * (b - 2 * a) := by
        have hga' : (r : ℤ) * (b - 2 * a) = (gap d r * a + (r : ℤ) * b) - (d : ℤ) * a := by
          simp only [gap]; ring
        rw [hga']
        exact dvd_sub hga (dvd_mul_right (d : ℤ) a)
      exact IsCoprime.dvd_of_dvd_mul_left hrd h
    have hca2b : (d : ℤ) ∣ (cofactor d r : ℤ) * a + 2 * b := by
      have h : (d : ℤ) ∣ (r : ℤ) * ((cofactor d r : ℤ) * a + 2 * b) := by
        have hcr' : (r : ℤ) * ((cofactor d r : ℤ) * a + 2 * b) =
            ((cofactor d r : ℤ) * (r : ℤ) * a - gap d r * b) + (d : ℤ) * b := by
          simp only [gap]; ring
        rw [hcr']
        exact dvd_add hcr (dvd_mul_right (d : ℤ) b)
      exact IsCoprime.dvd_of_dvd_mul_left hrd h
    have hla : (d : ℤ) ∣ (level d r : ℤ) * a := by
      have hh : (d : ℤ) ∣ ((cofactor d r : ℤ) * a + 2 * b) - 2 * (b - 2 * a) :=
        dvd_sub hca2b (dvd_mul_of_dvd_right hb2a 2)
      have heq : ((cofactor d r : ℤ) * a + 2 * b) - 2 * (b - 2 * a) = (level d r : ℤ) * a := by
        rw [level_eq_cofactor_add_four (d := d) (r := r) h]; ring
      rwa [heq] at hh
    have hda_div : (d : ℤ) ∣ a := by
      have hcop : IsCoprime (d : ℤ) (level d r : ℤ) := (coprime_level_d h).symm
      exact IsCoprime.dvd_of_dvd_mul_left hcop hla
    obtain ⟨ka, hka⟩ := hda_div
    have haz : a = 0 := by
      have hlt : (d : ℤ) * ka < (d : ℤ) * 1 := by
        nlinarith [hka, halt_a]
      have hk0 : ka = 0 := by
        by_contra hk
        rcases lt_or_gt_of_ne hk with hk' | hk'
        · have : (d : ℤ) * ka ≤ 0 := by
            nlinarith [hk', show (0:ℤ) < (d:ℤ) from by exact_mod_cast (Nat.pos_of_ne_zero (d_ne_zero h))]
          nlinarith [hka, ha0, this]
        · have : (1:ℤ) ≤ ka := by omega
          nlinarith [hlt, this, show (0:ℤ) < (d:ℤ) from by exact_mod_cast (Nat.pos_of_ne_zero (d_ne_zero h))]
      rw [hka, hk0, mul_zero]
    have hdb : (d : ℤ) ∣ b := by
      have h := hb2a
      rw [haz] at h
      simpa using h
    obtain ⟨b0, hb0⟩ := hdb
    have hb0nonneg : 0 ≤ b0 := by
      by_contra hneg
      push_neg at hneg
      nlinarith [hb0, show (0:ℤ) < (d:ℤ) from by exact_mod_cast (Nat.pos_of_ne_zero (d_ne_zero h))]
    have hb0lt : b0 < (cofactor d r : ℤ) := by
      have hb' : b < ((longModulus d r : ℕ) : ℤ) := halt_b
      rw [longModulus_castZ h] at hb'
      have hdpos : (0:ℤ) < (d:ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero (d_ne_zero h))
      nlinarith [hb0, hb']
    have hcb0 : (cofactor d r : ℤ) ∣ b0 := by
      have hdvd : ((longModulus d r : ℕ) : ℤ) ∣ gap d r * b := by
        have := hd2
        rw [haz] at this
        simpa using this
      have hgd : ((longModulus d r : ℕ) : ℤ) ∣ (d : ℤ) * (gap d r * b0) := by
        convert hdvd using 1
        rw [hb0]; ring
      have hcdvd : (cofactor d r : ℤ) ∣ gap d r * b0 := by
        rw [longModulus_castZ h] at hgd
        obtain ⟨k, hk⟩ := hgd
        refine ⟨k, ?_⟩
        have hkk : (d : ℤ) * (gap d r * b0) = (d : ℤ) * ((cofactor d r : ℤ) * k) := by
          linear_combination hk
        exact mul_left_cancel₀ (show (d:ℤ) ≠ 0 from hd) hkk
      exact IsCoprime.dvd_of_dvd_mul_left (conic_gap_coprime h).symm hcdvd
    have hb0z : b0 = 0 := by
      obtain ⟨k, hk⟩ := hcb0
      have hlt : (cofactor d r : ℤ) * k < (cofactor d r : ℤ) * 1 := by
        nlinarith [hk, hb0lt]
      have hk0 : k = 0 := by
        by_contra hk'
        rcases lt_or_gt_of_ne hk' with hk'' | hk''
        · have : (cofactor d r : ℤ) * k ≤ 0 := by
            nlinarith [hk'', show (0:ℤ) < (cofactor d r : ℤ) from by exact_mod_cast (Nat.pos_of_ne_zero (cofactor_ne_zero h))]
          nlinarith [hk, hb0nonneg, this]
        · have : (1:ℤ) ≤ k := by omega
          nlinarith [hlt, this, show (0:ℤ) < (cofactor d r : ℤ) from by exact_mod_cast (Nat.pos_of_ne_zero (cofactor_ne_zero h))]
      rw [hk, hk0, mul_zero]
    have hbz : b = 0 := by rw [hb0, hb0z, mul_zero]
    rw [hcx, haz, hbz]
    simp [coordinate]

private def Bexp (d r : ℕ) (x y : ℤ) : ℤ :=
  -(((ell d r : ℤ) - 1) * (gap d r * x + (r : ℤ) * y)) -
    (cofactor d r : ℤ) * (r : ℤ) * x + gap d r * y

private theorem pairing_iota_formula (d r : ℕ) [Fact (Admissible d r)] (g : G d r) (p : Index d) :
    L2b.metricPairing (gaussian d r) g (iota d r p) =
      L2a.e d ((gap d r * (g.1.val : ℤ) + (r : ℤ) * (g.2.val : ℤ)) * (p.1.val : ℤ) +
        Bexp d r (g.1.val : ℤ) (g.2.val : ℤ) * (p.2.val : ℤ)) := by
  have h : Admissible d r := Fact.out
  have hc : cofactor d r ≠ 0 := cofactor_ne_zero h
  have hd : d ≠ 0 := d_ne_zero h
  have hi : iota d r p = coordinate d r (((ell d r : ℤ) - 1) * (p.2.val : ℤ) - (p.1.val : ℤ))
      ((cofactor d r : ℤ) * (p.2.val : ℤ)) := rfl
  conv_lhs => rw [G_eq_coordinate (d := d) (r := r) g]
  rw [hi, pairing_formula_aux]
  simp only [pairingLift, Bexp]
  rw [e_mod_cast (cofactor d r) d (longModulus d r) hc hd (by rw [longModulus, Nat.mul_comm])]
  apply L2a.e_eq_of_dvd
  refine ⟨0, ?_⟩
  ring


private theorem forall_e_d_iff (d : ℕ) [NeZero d] [Fact (1 < d)] (a b : ℤ) :
    (∀ p : Index d, L2a.e d (a * (p.1.val : ℤ) + b * (p.2.val : ℤ)) = 1) ↔
      ((d : ℤ) ∣ a ∧ (d : ℤ) ∣ b) := by
  have hd : d ≠ 0 := NeZero.ne d
  constructor
  · intro h
    have h10 := h (1, 0)
    have h01 := h (0, 1)
    simp only [Prod.fst, Prod.snd, ZMod.val_one d, ZMod.val_zero, mul_zero, mul_one, add_zero] at h10 h01
    push_cast at h10 h01
    have h10' : L2a.e d a = 1 := by simpa using h10
    have h01' : L2a.e d b = 1 := by simpa using h01
    exact ⟨(e_eq_one_iff_dvd hd a).1 h10', (e_eq_one_iff_dvd hd b).1 h01'⟩
  · rintro ⟨ha, hb⟩ p
    exact (e_eq_one_iff_dvd hd _).2 (dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left hb _))

private theorem val_smul_annihilator {d r : ℕ} [Fact (Admissible d r)] (z : ℤ) :
    (d : ℤ) ∣ ((((z • annihilatorGenerator d r).2).val : ℕ) : ℤ) := by
  have h : Admissible d r := Fact.out
  have hc : cofactor d r ≠ 0 := cofactor_ne_zero h
  have hd : d ≠ 0 := d_ne_zero h
  haveI : NeZero (longModulus d r) := ⟨longModulus_ne_zero h⟩
  have h1 : (z • annihilatorGenerator d r).2 = ((z * (d : ℤ) : ℤ) : ZMod (longModulus d r)) := by
    simp [annihilatorGenerator, coordinate, zsmul_eq_mul]
  have hval : ((((z • annihilatorGenerator d r).2).val : ℕ) : ℤ) =
      (z * (d : ℤ)) % ((longModulus d r : ℕ) : ℤ) := by
    rw [h1, ZMod.val_intCast]
  rw [hval, longModulus_castZ h]
  have hq := Int.emod_add_mul_ediv (z * (d : ℤ)) ((d : ℤ) * (cofactor d r : ℤ))
  refine ⟨z - (cofactor d r : ℤ) * (z * (d : ℤ) / ((d : ℤ) * (cofactor d r : ℤ))), ?_⟩
  linear_combination hq

private theorem small_subgroup_condition (d r : ℕ) [Fact (Admissible d r)] (g : G d r) :
    g ∈ smallSubgroup d r ↔
      ((d : ℤ) ∣ gap d r * (g.1.val : ℤ) + (r : ℤ) * (g.2.val : ℤ) ∧
        (d : ℤ) ∣ Bexp d r (g.1.val : ℤ) (g.2.val : ℤ)) := by
  have h : Admissible d r := Fact.out
  have hc : cofactor d r ≠ 0 := cofactor_ne_zero h
  have hd : d ≠ 0 := d_ne_zero h
  haveI : NeZero d := ⟨hd⟩
  have hdpos : (0:ℤ) < (d:ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  constructor
  · intro hg
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
    have hx0 : (g.1.val : ℤ) = 0 := by
      have h1 : g.1 = 0 := by rw [← hz]; simp [annihilatorGenerator, coordinate]
      rw [h1]; simp
    have hy : (d : ℤ) ∣ (g.2.val : ℤ) := by
      have hval := val_smul_annihilator (d := d) (r := r) z
      rw [← hz]
      exact hval
    constructor
    · rw [hx0]
      have hpd : gap d r * 0 + (r : ℤ) * (g.2.val : ℤ) = (r : ℤ) * (g.2.val : ℤ) := by ring
      rw [hpd]
      exact dvd_mul_of_dvd_right hy (r : ℤ)
    · rw [Bexp, hx0]
      have hpd : gap d r * 0 + (r : ℤ) * (g.2.val : ℤ) = (r : ℤ) * (g.2.val : ℤ) := by ring
      rw [hpd]
      have hrep : -(((ell d r : ℤ) - 1) * ((r : ℤ) * (g.2.val : ℤ))) - (cofactor d r : ℤ) * (r : ℤ) * 0 +
          gap d r * (g.2.val : ℤ) =
          (-((ell d r : ℤ) - 1) * (r : ℤ) + gap d r) * (g.2.val : ℤ) := by ring
      rw [hrep]
      exact dvd_mul_of_dvd_right hy _
  · rintro ⟨hpd1, hB⟩
    set x : ℤ := (g.1.val : ℤ) with hx
    set y : ℤ := (g.2.val : ℤ) with hy
    have hx0 : 0 ≤ x := by rw [hx]; exact_mod_cast Nat.zero_le _
    have hy0 : 0 ≤ y := by rw [hy]; exact_mod_cast Nat.zero_le _
    have hxlt : x < (d : ℤ) := by rw [hx]; exact_mod_cast ZMod.val_lt g.1
    have hylt : y < ((longModulus d r : ℕ) : ℤ) := by rw [hy]; exact_mod_cast ZMod.val_lt g.2
    have hpd1' : (d : ℤ) ∣ gap d r * x + (r : ℤ) * y := hpd1
    have hB' : (d : ℤ) ∣ Bexp d r x y := hB
    have hrd : IsCoprime (d : ℤ) (r : ℤ) := (coprime_r_d h).symm
    have hy2x : (d : ℤ) ∣ y - 2 * x := by
      have hh : (d : ℤ) ∣ (r : ℤ) * (y - 2 * x) := by
        have heq : (r : ℤ) * (y - 2 * x) = (gap d r * x + (r : ℤ) * y) - (d : ℤ) * x := by
          simp only [gap]; ring
        rw [heq]
        exact dvd_sub hpd1' (dvd_mul_right (d : ℤ) x)
      exact IsCoprime.dvd_of_dvd_mul_left hrd hh
    have hB2 : (d : ℤ) ∣ (cofactor d r : ℤ) * (r : ℤ) * x - gap d r * y := by
      have heq : (cofactor d r : ℤ) * (r : ℤ) * x - gap d r * y =
          - Bexp d r x y - ((ell d r : ℤ) - 1) * (gap d r * x + (r : ℤ) * y) := by
        simp only [Bexp]; ring
      rw [heq]
      exact dvd_sub (dvd_neg.mpr hB') (dvd_mul_of_dvd_right hpd1' _)
    have hca2b : (d : ℤ) ∣ (cofactor d r : ℤ) * x + 2 * y := by
      have hh : (d : ℤ) ∣ (r : ℤ) * ((cofactor d r : ℤ) * x + 2 * y) := by
        have heq : (r : ℤ) * ((cofactor d r : ℤ) * x + 2 * y) =
            ((cofactor d r : ℤ) * (r : ℤ) * x - gap d r * y) + (d : ℤ) * y := by
          simp only [gap]; ring
        rw [heq]
        exact dvd_add hB2 (dvd_mul_right (d : ℤ) y)
      exact IsCoprime.dvd_of_dvd_mul_left hrd hh
    have hla : (d : ℤ) ∣ (level d r : ℤ) * x := by
      have hh : (d : ℤ) ∣ ((cofactor d r : ℤ) * x + 2 * y) - 2 * (y - 2 * x) :=
        dvd_sub hca2b (dvd_mul_of_dvd_right hy2x 2)
      have heq : ((cofactor d r : ℤ) * x + 2 * y) - 2 * (y - 2 * x) = (level d r : ℤ) * x := by
        rw [level_eq_cofactor_add_four h]; ring
      rwa [heq] at hh
    have hcop : IsCoprime (d : ℤ) (level d r : ℤ) := (coprime_level_d h).symm
    have hdx : (d : ℤ) ∣ x := IsCoprime.dvd_of_dvd_mul_left hcop hla
    obtain ⟨kx, hkx⟩ := hdx
    have hxz : x = 0 := by
      have hlt : (d : ℤ) * kx < (d : ℤ) * 1 := by nlinarith [hkx, hxlt]
      have hk0 : kx = 0 := by
        by_contra hk
        rcases lt_or_gt_of_ne hk with hk' | hk'
        · have : (d : ℤ) * kx ≤ 0 := by nlinarith [hk', hdpos]
          nlinarith [hkx, hx0, this]
        · have h1 : (1:ℤ) ≤ kx := by omega
          nlinarith [hlt, h1, hdpos]
      rw [hkx, hk0, mul_zero]
    have hdy : (d : ℤ) ∣ y := by
      have hh := hy2x
      rw [hxz] at hh
      simpa using hh
    obtain ⟨j, hj⟩ := hdy
    have hgen : g = j • annihilatorGenerator d r := by
      rw [G_eq_coordinate (d := d) (r := r) g, ← hx, ← hy, hxz, hj]
      simp [annihilatorGenerator, coordinate, zsmul_eq_mul]
      ring
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨j, hgen.symm⟩

private noncomputable def zmodEquivFin (N : ℕ) [NeZero N] : ZMod N ≃ Fin N where
  toFun u := ⟨u.val, ZMod.val_lt u⟩
  invFun k := (k : ZMod N)
  left_inv u := by simpa using ZMod.natCast_zmod_val u
  right_inv k := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt k.isLt

private theorem sum_e_zmod (N : ℕ) [NeZero N] (a : ℤ) :
    (∑ u : ZMod N, L2a.e N (a * (u.val : ℤ))) = if (N : ℤ) ∣ a then (N : ℂ) else 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  by_cases h : (N : ℤ) ∣ a
  · have h1 : ∀ u : ZMod N, L2a.e N (a * (u.val : ℤ)) = 1 := by
      intro u
      exact (e_eq_one_iff_dvd hN _).2 (dvd_mul_of_dvd_left h _)
    rw [if_pos h, Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_const, Finset.card_univ, ZMod.card]
    simp
  · rw [if_neg h]
    have hsum : (∑ u : ZMod N, L2a.e N (a * (u.val : ℤ))) =
        ∑ k : Fin N, L2a.e N (a * (k.val : ℤ)) := by
      refine Fintype.sum_equiv (zmodEquivFin N) _ _ ?_
      intro u
      rfl
    rw [hsum]
    simp only [L2a.e_eq_omega_zpow]
    exact sum_omega_pow_eq_zero h

private theorem sum_e_zmod_prod (N : ℕ) [NeZero N] (a b : ℤ) :
    (∑ p : ZMod N × ZMod N, L2a.e N (a * (p.1.val : ℤ) + b * (p.2.val : ℤ))) =
      if ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) then (N : ℂ) ^ 2 else 0 := by
  have hsplit : ∀ p : ZMod N × ZMod N,
      L2a.e N (a * (p.1.val : ℤ) + b * (p.2.val : ℤ)) =
        L2a.e N (a * (p.1.val : ℤ)) * L2a.e N (b * (p.2.val : ℤ)) := by
    intro p; rw [L2a.e_mul]
  rw [Finset.sum_congr rfl (fun p _ => hsplit p), Fintype.sum_prod_type]
  simp only [Prod.fst, Prod.snd]
  rw [← Fintype.sum_mul_sum, sum_e_zmod N a, sum_e_zmod N b]
  by_cases ha : (N : ℤ) ∣ a <;> by_cases hb : (N : ℤ) ∣ b <;> simp [ha, hb, pow_two]

private theorem orthogonal_torsion_aux (d r : ℕ) [Fact (Admissible d r)] :
    {g : G d r | ∀ p : Index d, L2b.metricPairing (gaussian d r) g (iota d r p) = 1} =
      (smallSubgroup d r : Set (G d r)) := by
  have h : Admissible d r := Fact.out
  have hd : d ≠ 0 := d_ne_zero h
  haveI : NeZero d := ⟨hd⟩
  haveI : Fact (1 < d) := ⟨by have := h.main_range; omega⟩
  ext g
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  rw [small_subgroup_condition]
  constructor
  · intro hg
    have hforall : ∀ p : Index d,
        L2a.e d ((gap d r * (g.1.val : ℤ) + (r : ℤ) * (g.2.val : ℤ)) * (p.1.val : ℤ) +
          Bexp d r (g.1.val : ℤ) (g.2.val : ℤ) * (p.2.val : ℤ)) = 1 := by
      intro p
      rw [← pairing_iota_formula]
      exact hg p
    exact (forall_e_d_iff d _ _).1 hforall
  · rintro ⟨h1, h2⟩ p
    rw [pairing_iota_formula]
    exact (forall_e_d_iff d _ _).2 ⟨h1, h2⟩ p

private theorem groupOrder_castZ {d r : ℕ} (h : Admissible d r) :
    ((groupOrder d r : ℕ) : ℤ) = (d : ℤ) ^ 2 * ((cofactor d r : ℕ) : ℤ) := by
  rw [groupOrder, Nat.cast_mul, Nat.cast_pow]

private theorem neg_one_eq_2GO {d r : ℕ} (h : Admissible d r) (t : ℤ) :
    (-1 : ℂ) ^ t = L2a.e (2 * groupOrder d r) ((groupOrder d r : ℤ) * t) := by
  have hgo : groupOrder d r ≠ 0 := by
    have h5 := level_ge_five h
    have hd : 0 < d := by have := h.main_range; omega
    have hc : 0 < cofactor d r := by unfold cofactor; omega
    unfold groupOrder; positivity
  rw [← e_two_eq_neg_one]
  exact e_mod_cast (groupOrder d r) 2 (2 * groupOrder d r) hgo two_ne_zero (by ring) t

private theorem gaussian_rw_row_formula_aux {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    let w := rwNumerator d r x y
    let wg := rowAction (gamma d r) w
    gaussianLift d r x y = (-1 : ℂ) ^ (w.1 + w.2 + w.1 * w.2) *
      L2a.e (2 * groupOrder d r) (wg.1 * w.2 - wg.2 * w.1) := by
  set c : ℤ := (cofactor d r : ℤ) with hcdef
  have hce : c = (ell d r : ℤ) - 2 := by rw [hcdef]; exact cofactor_castZ h
  have hell : (ell d r : ℤ) = c + 2 := by rw [hce]; ring
  set w1 : ℤ := -(gap d r) * x + ((d : ℤ) - r) * y with hw1
  set w2 : ℤ := (((ell d r : ℤ) - 1) * ((d : ℤ) - r) - r) * x +
    (r - (ell d r : ℤ) * ((d : ℤ) - r)) * y with hw2
  set g1 : ℤ := (ell d r : ℤ) * ((d : ℤ) - r) ^ 2 - 2 * ((d : ℤ) - r) * r with hg1
  set g2 : ℤ := (r : ℤ) ^ 2 - ((d : ℤ) - r) ^ 2 with hg2
  set g3 : ℤ := ((d : ℤ) - r) ^ 2 - (r : ℤ) ^ 2 with hg3
  set g4 : ℤ := (ell d r : ℤ) * (r : ℤ) ^ 2 - 2 * ((d : ℤ) - r) * r with hg4
  set wg1 : ℤ := w1 * g1 + w2 * g3 with hwg1
  set wg2 : ℤ := w1 * g2 + w2 * g4 with hwg2
  set W : ℤ := w1 + w2 + w1 * w2 with hW
  have hw : rwNumerator d r x y = (w1, w2) := by
    apply Prod.ext <;> simp [rwNumerator, rwIndexMatrix, rowAction, hw1, hw2] <;> ring
  have hwg : rowAction (gamma d r) (w1, w2) = (wg1, wg2) := by
    apply Prod.ext <;>
      simp [rowAction, gamma00x, gamma01x, gamma10x, gamma11x, hwg1, hwg2, hg1, hg2, hg3, hg4] <;> ring
  dsimp only
  rw [gaussianLift_eq_exp h, hw, hwg]
  rw [neg_one_eq_2GO h W, L2a.e_mul]
  have hZ : wg1 * w2 - wg2 * w1 = (d : ℤ) * (gap d r * (-c * x ^ 2 + c * x * y + y ^ 2)) := by
    simp only [hwg1, hwg2, hw1, hw2, hg1, hg2, hg3, hg4, hce]
    simp only [gap]
    have hcon : ((d : ℤ) - 2 * (r : ℤ)) ^ 2 - ((ell d r : ℤ) - 2) * (r : ℤ) * ((d : ℤ) - r) = 1 := by
      have hh := conicZ h
      rw [cofactor_castZ h] at hh
      simpa [gap] using hh
    linear_combination ((d : ℤ) * (((d : ℤ) - 2 * (r : ℤ)) * (-((ell d r : ℤ) - 2) * x ^ 2 + ((ell d r : ℤ) - 2) * x * y + y ^ 2))) * hcon
  rw [hZ]
  -- convert LHS modulus
  have h2n : 2 * longModulus d r ≠ 0 := by
    have := longModulus_ne_zero h; positivity
  have hconv : L2a.e (2 * longModulus d r) (gExp d r x y) =
      L2a.e (2 * groupOrder d r) ((d : ℤ) * gExp d r x y) := by
    refine e_mod_cast d (2 * longModulus d r) (2 * groupOrder d r) (d_ne_zero h) h2n ?_ _
    unfold groupOrder longModulus; ring
  rw [hconv]
  -- parity of W vs x+y+xy
  have hdet : (((rwIndexMatrix d r) 0 0) * ((rwIndexMatrix d r) 1 1) -
      ((rwIndexMatrix d r) 1 0) * ((rwIndexMatrix d r) 0 1)) = 1 := by
    have hh := rwIndexMatrix_det h
    rw [Matrix.det_fin_two] at hh
    linear_combination hh
  have hrow := even_q0_rowAction (a := (rwIndexMatrix d r) 0 0) (b := (rwIndexMatrix d r) 1 0)
    (c := (rwIndexMatrix d r) 0 1) (d := (rwIndexMatrix d r) 1 1) hdet x y
  have hpar : Even (W - (x + y + x * y)) := by
    apply even_sub_of_iff
    have hx1 : (rwIndexMatrix d r) 0 0 = -gap d r := by simp [rwIndexMatrix]
    have hx2 : (rwIndexMatrix d r) 1 0 = (d : ℤ) - r := by simp [rwIndexMatrix]
    have hx3 : (rwIndexMatrix d r) 0 1 = ((ell d r : ℤ) - 1) * ((d:ℤ)-r) - r := by simp [rwIndexMatrix]
    have hx4 : (rwIndexMatrix d r) 1 1 = r - (ell d r : ℤ) * ((d:ℤ)-r) := by simp [rwIndexMatrix]
    rw [hx1, hx2, hx3, hx4] at hrow
    have hWrow : (((-gap d r) * x + ((d : ℤ) - r) * y) +
        ((((ell d r : ℤ) - 1) * ((d:ℤ)-r) - r) * x + (r - (ell d r : ℤ) * ((d:ℤ)-r)) * y) +
        ((-gap d r) * x + ((d : ℤ) - r) * y) *
        ((((ell d r : ℤ) - 1) * ((d:ℤ)-r) - r) * x + (r - (ell d r : ℤ) * ((d:ℤ)-r)) * y)) = W := by
      rw [hW, hw1, hw2]
    rwa [hWrow] at hrow
  obtain ⟨u, hu⟩ := hpar
  apply L2a.e_eq_of_dvd
  refine ⟨-u, ?_⟩
  have hgo : ((2 * groupOrder d r : ℕ) : ℤ) = 2 * (d : ℤ) ^ 2 * c := by
    rw [Nat.cast_mul, Nat.cast_two, groupOrder_castZ h, ← hcdef]; ring
  have hgo' : (groupOrder d r : ℤ) = (d : ℤ) ^ 2 * c := by
    rw [groupOrder_castZ h, ← hcdef]
  rw [hgo, hgo']
  simp only [gExp, gap]
  rw [longModulus_castZ h, ← hcdef]
  linear_combination (-((d : ℤ) ^ 2 * c)) * hu


private theorem torsion_character_sum_aux (d r : ℕ) [Fact (Admissible d r)] (g : G d r) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ p : Index d, L2b.metricPairing (gaussian d r) g (iota d r p)) =
      if g ∈ smallSubgroup d r then (d : ℂ) ^ 2 else 0 := by
  classical
  letI : NeZero d := admissibleDimensionNeZero d r
  have h : Admissible d r := Fact.out
  have hd : d ≠ 0 := d_ne_zero h
  haveI : Fact (1 < d) := ⟨by have := h.main_range; omega⟩
  have hterm : ∀ p : Index d,
      L2b.metricPairing (gaussian d r) g (iota d r p) =
        L2a.e d ((gap d r * (g.1.val : ℤ) + (r : ℤ) * (g.2.val : ℤ)) * (p.1.val : ℤ) +
          Bexp d r (g.1.val : ℤ) (g.2.val : ℤ) * (p.2.val : ℤ)) := by
    intro p
    rw [pairing_iota_formula]
  have hL : (∑ p : Index d, L2b.metricPairing (gaussian d r) g (iota d r p)) =
      if ((d : ℤ) ∣ gap d r * (g.1.val : ℤ) + (r : ℤ) * (g.2.val : ℤ) ∧
          (d : ℤ) ∣ Bexp d r (g.1.val : ℤ) (g.2.val : ℤ)) then (d : ℂ) ^ 2 else 0 := by
    rw [Finset.sum_congr rfl (fun p _ => hterm p)]
    exact sum_e_zmod_prod d _ _
  rw [hL]
  haveI : Decidable (g ∈ smallSubgroup d r) := Classical.propDecidable _
  by_cases hg : g ∈ smallSubgroup d r
  · have hcond := (small_subgroup_condition (d := d) (r := r) g).1 hg
    rw [if_pos hcond]
    rw [if_pos hg]
  · have hcond : ¬ ((d : ℤ) ∣ gap d r * (g.1.val : ℤ) + (r : ℤ) * (g.2.val : ℤ) ∧
        (d : ℤ) ∣ Bexp d r (g.1.val : ℤ) (g.2.val : ℤ)) :=
      fun hc => hg ((small_subgroup_condition (d := d) (r := r) g).2 hc)
    rw [if_neg hcond]
    rw [if_neg hg]



theorem periodDifference_eq {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    actOnCoordinates (gamma d r) (pointLift d r x y) - pointLift d r x y =
      (((periodDifference d r x y).1 : ℚ), ((periodDifference d r x y).2 : ℚ)) :=
  periodDifference_eq_aux h x y

theorem gaussian_rw_formula {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    gaussianLift d r x y =
      (-1 : ℂ) ^ ((periodDifference d r x y).1 + (periodDifference d r x y).2 +
        (periodDifference d r x y).1 * (periodDifference d r x y).2) *
      Complex.exp (Real.pi * Complex.I *
        (alternating (pointLift d r x y)
          (actOnCoordinates (gamma d r) (pointLift d r x y)) : ℂ)) :=
  gaussian_rw_formula_aux h x y

/-- The same Gaussian in the row coordinates of [RW26, (3)]. -/
theorem gaussian_rw_row_formula {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    let w := rwNumerator d r x y
    let wg := rowAction (gamma d r) w
    gaussianLift d r x y = (-1 : ℂ) ^ (w.1 + w.2 + w.1 * w.2) *
      L2a.e (2 * groupOrder d r) (wg.1 * w.2 - wg.2 * w.1) :=
  gaussian_rw_row_formula_aux h x y

theorem gaussian_periodic {d r : ℕ} (h : Admissible d r) (x y k l : ℤ) :
    gaussianLift d r (x + (d : ℤ) * k) (y + (longModulus d r : ℤ) * l) =
      gaussianLift d r x y :=
  gaussian_periodic_aux h x y k l

theorem gaussian_eq_lift (d r : ℕ) [Fact (Admissible d r)] (x y : ℤ) :
    gaussian d r (coordinate d r x y) = gaussianLift d r x y :=
  gaussian_eq_lift_aux d r x y

theorem pairing_formula (d r : ℕ) [Fact (Admissible d r)] (x y X Y : ℤ) :
    L2b.metricPairing (gaussian d r) (coordinate d r x y) (coordinate d r X Y) =
      pairingLift d r x y X Y :=
  pairing_formula_aux d r x y X Y

theorem pairing_rw_formula (d r : ℕ) [Fact (Admissible d r)] (x y X Y : ℤ) :
    pairingLift d r x y X Y = Complex.exp (2 * Real.pi * Complex.I *
      (alternating (pointLift d r x y -
        actOnCoordinates (gamma d r) (pointLift d r x y))
        (pointLift d r X Y) : ℂ)) :=
  pairing_rw_formula_aux d r x y X Y

theorem concrete_isMetricGaussian (d r : ℕ) [Fact (Admissible d r)] :
    L2b.IsMetricGaussian (gaussian d r) :=
  concrete_isMetricGaussian_aux d r

theorem gaussian_epsilon (d r : ℕ) [Fact (Admissible d r)] (g : G d r) :
    gaussian d r (epsilonAut d r g) = gaussian d r g :=
  gaussian_epsilon_aux d r g

theorem gaussian_iota (d r : ℕ) [Fact (Admissible d r)] (p : Index d) :
    gaussian d r (iota d r p) = torsionGaussian d r p :=
  gaussian_iota_aux d r p

theorem orthogonal_torsion (d r : ℕ) [Fact (Admissible d r)] :
    {g : G d r | ∀ p : Index d, L2b.metricPairing (gaussian d r) g (iota d r p) = 1} =
      (smallSubgroup d r : Set (G d r)) :=
  orthogonal_torsion_aux d r

theorem torsion_character_sum (d r : ℕ) [Fact (Admissible d r)] (g : G d r) :
    letI : NeZero d := admissibleDimensionNeZero d r
    (∑ p : Index d, L2b.metricPairing (gaussian d r) g (iota d r p)) =
      if g ∈ smallSubgroup d r then (d : ℂ) ^ 2 else 0 :=
  torsion_character_sum_aux d r g

theorem pairing_witnessY (d r : ℕ) [Fact (Admissible d r)] (p q : Index d) :
    L2b.metricPairing (gaussian d r) (witnessY d r p) (iota d r q) =
      L2a.e d ((r : ℤ) * symplectic (lift p) (shiftedAlpha d r (lift q))) :=
  pairing_witnessY_aux d r p q

end SICLean.L2r
