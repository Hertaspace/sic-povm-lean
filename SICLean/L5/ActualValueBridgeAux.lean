import SICLean.L5.ActualPseudolattice

set_option autoImplicit false

/-!
Elementary coordinate and parity computations for the Gaussian of [RW-rec, (2)].
`coord`, `alt`, `sign`, and `qAt` are the expressions used in `ActualValueBridge`.
These definitions are independent of any Gaussian identification theorem.
-/

noncomputable section
open scoped Classical MatrixGroups

namespace SICLean.L5.ActualValueBridgeAux

open ActualField ActualLattice

def coord (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM) : ℝ × ℝ :=
  ((sigma₁ M hM x - sigma₂ M hM x) /
      (L4.specialValueTau M - conjugateTau M),
    (L4.specialValueTau M * sigma₂ M hM x - conjugateTau M * sigma₁ M hM x) /
      (L4.specialValueTau M - conjugateTau M))

def alt (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x y : baseField M hM) : ℝ :=
  (coord M hM x).1 * (coord M hM y).2 -
    (coord M hM x).2 * (coord M hM y).1

def sign (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM) : ℂ :=
  if x ∈ L3.pseudolatticeScale (2 : baseField M hM) (lattice M hM) then 1 else -1

def qAt (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM) : ℂ :=
  sign M hM ((epsilon M hM - 1) * x) *
    L4.e ((alt M hM x (epsilon M hM * x) / 2 : ℝ) : ℂ)

theorem tau_sub_conjugate_ne_zero (M : SL(2, ℤ))
    (hM : L4.SpecialValueAdmissible M) :
    L4.specialValueTau M - conjugateTau M ≠ 0 := by
  have hc : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM.1
  have ht : (2 : ℝ) < (M 0 0 : ℝ) + (M 1 1 : ℝ) := by exact_mod_cast hM.2
  have hs : 0 < Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have hd : L4.specialValueTau M - conjugateTau M =
      Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4) / (M 1 0 : ℝ) := by
    unfold L4.specialValueTau conjugateTau
    ring
  rw [hd]
  exact ne_of_gt (div_pos hs hc)

theorem coord_rat (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (a b : ℚ) :
    coord M hM ((a : baseField M hM) * tau M hM + b) = ((a : ℝ), (b : ℝ)) := by
  have hd := tau_sub_conjugate_ne_zero M hM
  ext <;>
    simp only [coord, map_add, map_mul, map_ratCast, sigma₁_tau, sigma₂_tau] <;>
    field_simp <;> ring

def row (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) : baseField M hM :=
  (u.1 : baseField M hM) * tau M hM + u.2

theorem row_injective (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    Function.Injective (row M hM) := by
  intro u v huv
  have h := congrArg (sigma₁ M hM) huv
  simp only [row, map_add, map_mul, map_intCast, sigma₁_tau] at h
  have hh : (((u.1 - v.1 : ℤ) : ℝ)) * L4.specialValueTau M + (u.2 - v.2 : ℤ) = 0 := by
    push_cast
    linarith
  obtain ⟨h1, h2⟩ := L4.int_linear_eq_zero (L4.specialValueTau_irrational M hM) hh
  exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)

theorem lattice_mem_iff (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM) : x ∈ lattice M hM ↔ ∃ u : ℤ × ℤ, row M hM u = x := by
  rw [lattice_eq_span, Submodule.mem_span_pair]
  simp only [row, zsmul_eq_mul, mul_one]
  exact ⟨fun ⟨a, b, h⟩ => ⟨(a, b), h⟩, fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩⟩

theorem row_mul_epsilon (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    epsilon M hM * row M hM u =
      row M hM (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) := by
  have h := (epsilon_basis M hM).1
  have he := (epsilon_basis M hM).2
  simp only [row, L2r.rowAction]
  push_cast
  linear_combination (u.1 : baseField M hM) * h + (u.2 : baseField M hM) * he

theorem row_mem_double_iff (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    row M hM u ∈ L3.pseudolatticeScale (2 : baseField M hM) (lattice M hM) ↔
      Even u.1 ∧ Even u.2 := by
  rw [L3.pseudolatticeScale_mem_iff]
  constructor
  · rintro ⟨y, hy, hyu⟩
    obtain ⟨v, rfl⟩ := (lattice_mem_iff M hM y).mp hy
    have hv : row M hM (2 * v.1, 2 * v.2) = row M hM u := by
      convert hyu using 1
      simp [row]
      ring
    have huv := row_injective M hM hv
    exact ⟨⟨v.1, by simpa [two_mul] using (congrArg Prod.fst huv).symm⟩,
      ⟨v.2, by simpa [two_mul] using (congrArg Prod.snd huv).symm⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨row M hM (a, b), (lattice_mem_iff M hM _).mpr ⟨(a, b), rfl⟩, ?_⟩
    simp only [row, ha, hb, Int.cast_add]
    ring

theorem epsilon_ne_one (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    epsilon M hM ≠ 1 := by
  intro he
  have h := epsilon_gt_one M hM
  rw [he, map_one] at h
  exact (lt_irrefl _ h)

theorem inverse_difference_ne_zero (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    (epsilon M hM)⁻¹ - 1 ≠ 0 := by
  exact sub_ne_zero.mpr (inv_ne_one.mpr (epsilon_ne_one M hM))

theorem rowPoint_surjective (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM)
    (hx : x ∈ L3.pseudolatticePeriodPoints (periodData M hM) (stableLattice M hM)) :
    ∃ u : ℤ × ℤ, rowPoint M hM u = x := by
  change ((epsilon M hM)⁻¹ - 1) * x ∈ lattice M hM at hx
  obtain ⟨u, hu⟩ := (lattice_mem_iff M hM _).mp hx
  refine ⟨u, ?_⟩
  change row M hM u / ((epsilon M hM)⁻¹ - 1) = x
  rw [hu, mul_div_cancel_left₀ x (inverse_difference_ne_zero M hM)]

theorem epsilon_polynomial_int (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    epsilon M hM ^ 2 - ((L4.specialValueOrder M : baseField M hM) + 2) *
      epsilon M hM + 1 = 0 := by
  have hn : (L4.specialValueOrder M : baseField M hM) =
      ((L4.specialValueOrder M).toNat : baseField M hM) := by
    exact_mod_cast (order_nat M hM).2
  rw [hn]
  exact epsilon_polynomial M hM

theorem rowPoint_formula (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) : rowPoint M hM u =
      ((1 - epsilon M hM) * row M hM u) / (L4.specialValueOrder M : baseField M hM) := by
  have he : epsilon M hM ≠ 0 := (periodData M hM).epsilon_ne_zero
  have hn : (L4.specialValueOrder M : baseField M hM) ≠ 0 := by
    exact_mod_cast ne_of_gt (L4.specialValueOrder_pos M hM)
  change row M hM u / ((epsilon M hM)⁻¹ - 1) = _
  apply (div_eq_iff (inverse_difference_ne_zero M hM)).mpr
  field_simp
  linear_combination -(row M hM u) * epsilon_polynomial_int M hM

theorem rowPoint_eq_rat (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    let v := u - L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u
    rowPoint M hM u =
      (((v.1 : ℚ) / (L4.specialValueOrder M : ℚ) : ℚ) : baseField M hM) * tau M hM +
      (((v.2 : ℚ) / (L4.specialValueOrder M : ℚ) : ℚ) : baseField M hM) := by
  dsimp only
  rw [rowPoint_formula, sub_mul, one_mul, row_mul_epsilon]
  simp only [row, Prod.fst_sub, Prod.snd_sub, Rat.cast_div, Rat.cast_intCast,
    Int.cast_sub]
  push_cast
  ring

theorem coord_epsilon_rat (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) (r s : ℚ) :
    coord M hM (epsilon M hM * ((r : baseField M hM) * tau M hM + s)) =
      (((M 0 0 : ℝ) * r + (M 1 0 : ℝ) * s),
        ((M 0 1 : ℝ) * r + (M 1 1 : ℝ) * s)) := by
  have hh : epsilon M hM * ((r : baseField M hM) * tau M hM + s) =
      (((M 0 0 : ℚ) * r + (M 1 0 : ℚ) * s : ℚ) : baseField M hM) * tau M hM +
      (((M 0 1 : ℚ) * r + (M 1 1 : ℚ) * s : ℚ) : baseField M hM) := by
    push_cast
    linear_combination (r : baseField M hM) * (epsilon_basis M hM).1 +
      (s : baseField M hM) * (epsilon_basis M hM).2
  rw [hh, coord_rat]
  push_cast
  rfl

theorem even_quadratic_iff (m n : ℤ) :
    Even (m + n + m * n) ↔ Even m ∧ Even n := by
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn <;>
    simp [Int.even_iff, Int.add_emod, Int.mul_emod, hm, hn]

theorem epsilon_double_mem_iff (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (z : baseField M hM) :
    epsilon M hM * z ∈ L3.pseudolatticeScale (2 : baseField M hM) (lattice M hM) ↔
      z ∈ L3.pseudolatticeScale (2 : baseField M hM) (lattice M hM) := by
  let J := L3.pseudolatticeScale (2 : baseField M hM) (lattice M hM)
  have hJ : L3.pseudolatticeScale (epsilon M hM) J = J := by
    dsimp only [J]
    rw [← L3.pseudolatticeScale_mul, mul_comm, L3.pseudolatticeScale_mul]
    exact congrArg (L3.pseudolatticeScale (2 : baseField M hM)) (lattice_periodStable M hM)
  have he : epsilon M hM ≠ 0 := (periodData M hM).epsilon_ne_zero
  change epsilon M hM * z ∈ J ↔ z ∈ J
  constructor
  · intro hz
    have hz' : epsilon M hM * z ∈ L3.pseudolatticeScale (epsilon M hM) J := by
      rwa [hJ]
    obtain ⟨w, hw, hwz⟩ := (L3.pseudolatticeScale_mem_iff _ _ _).mp hz'
    exact (mul_left_cancel₀ he hwz) ▸ hw
  · intro hz
    rw [← hJ]
    exact (L3.pseudolatticeScale_mem_iff _ _ _).mpr ⟨z, hz, rfl⟩

theorem period_difference_rowPoint (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    (epsilon M hM - 1) * rowPoint M hM u = -(epsilon M hM * row M hM u) := by
  have he : epsilon M hM ≠ 0 := (periodData M hM).epsilon_ne_zero
  have hd := inverse_difference_ne_zero M hM
  have h1 : 1 - epsilon M hM ≠ 0 := sub_ne_zero.mpr (Ne.symm (epsilon_ne_one M hM))
  change (epsilon M hM - 1) * (row M hM u / ((epsilon M hM)⁻¹ - 1)) = _
  field_simp [h1]
  ring

theorem sign_rowPoint (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    sign M hM ((epsilon M hM - 1) * rowPoint M hM u) =
      (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) := by
  unfold sign
  simp only [period_difference_rowPoint, Submodule.neg_mem_iff, epsilon_double_mem_iff,
    row_mem_double_iff, neg_one_zpow_eq_ite, even_quadratic_iff]

theorem alternating_difference (a b c d m n : ℝ) (hdet : a * d - b * c = 1) :
    (m - (a * m + c * n)) *
        (b * (m - (a * m + c * n)) + d * (n - (b * m + d * n))) -
      (n - (b * m + d * n)) *
        (a * (m - (a * m + c * n)) + c * (n - (b * m + d * n))) =
      (a + d - 2) * ((a * m + c * n) * n - (b * m + d * n) * m) := by
  linear_combination -((a * m + c * n) * n - (b * m + d * n) * m) * hdet

theorem alt_rowPoint (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    alt M hM (rowPoint M hM u) (epsilon M hM * rowPoint M hM u) =
      (L4.specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u : ℝ) /
        (L4.specialValueOrder M : ℝ) := by
  have hn : (L4.specialValueOrder M : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (L4.specialValueOrder_pos M hM)
  have hd : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    exact_mod_cast L4.det_coe_int M
  have hal := alternating_difference (M 0 0) (M 0 1) (M 1 0) (M 1 1) u.1 u.2 hd
  unfold alt
  rw [rowPoint_eq_rat]
  simp only [coord_rat, coord_epsilon_rat, Prod.fst_sub, Prod.snd_sub]
  push_cast
  simp only [L2r.rowAction, L4.specialValueOmega] at hal ⊢
  push_cast
  field_simp
  convert hal using 1 <;>
    (try simp only [L4.specialValueOrder, Int.cast_add, Int.cast_sub, Int.cast_ofNat]) <;> ring

theorem qAt_rowPoint (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (u : ℤ × ℤ) : qAt M hM (rowPoint M hM u) = L4.specialValueGaussianLift M u := by
  unfold qAt
  rw [sign_rowPoint, alt_rowPoint]
  unfold L4.specialValueGaussianLift
  congr 2
  push_cast
  ring

theorem qAt_eq_matrix (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x : baseField M hM)
    (hx : x ∈ L3.pseudolatticePeriodPoints (periodData M hM) (stableLattice M hM)) :
    qAt M hM x = L4.specialValueGaussian M hM
      ((labelEquiv M hM).symm (L3.pseudolatticeMk (periodData M hM) (stableLattice M hM) x hx)) := by
  obtain ⟨u, rfl⟩ := rowPoint_surjective M hM x hx
  rw [qAt_rowPoint, ← labelEquiv_mk, AddEquiv.symm_apply_apply,
    L4.specialValueGaussian_mk]

theorem qAt_periodic (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (x t : baseField M hM)
    (hx : x ∈ L3.pseudolatticePeriodPoints (periodData M hM) (stableLattice M hM))
    (ht : t ∈ lattice M hM) : qAt M hM (x + t) = qAt M hM x := by
  have hxt := (L3.pseudolatticePeriodPoints (periodData M hM) (stableLattice M hM)).add_mem
    hx (L3.pseudolattice_le_periodPoints (periodData M hM) (stableLattice M hM) ht)
  rw [qAt_eq_matrix M hM (x + t) hxt, qAt_eq_matrix M hM x hx]
  congr 2
  apply (L3.M72.mk_eq_iff (periodData M hM) (stableLattice M hM) (x + t) x hxt hx).mpr
  change (x + t) - x ∈ lattice M hM
  simpa only [add_sub_cancel_left] using ht

theorem qAt_representative_label (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (g : L4.SpecialValueGroup M) :
    qAt M hM (L3.pseudolatticeRepresentative (periodData M hM)
      (stableLattice M hM) (labelEquiv M hM g)) = L4.specialValueGaussian M hM g := by
  have hq := qAt_eq_matrix M hM
    (L3.pseudolatticeRepresentative (periodData M hM) (stableLattice M hM) (labelEquiv M hM g))
    (Quotient.out (labelEquiv M hM g)).property
  have hmk : L3.pseudolatticeMk (periodData M hM) (stableLattice M hM)
      (L3.pseudolatticeRepresentative (periodData M hM) (stableLattice M hM)
        (labelEquiv M hM g)) (Quotient.out (labelEquiv M hM g)).property = labelEquiv M hM g :=
    Quotient.out_eq _
  rw [hmk, AddEquiv.symm_apply_apply] at hq
  exact hq

end SICLean.L5.ActualValueBridgeAux
