import SICLean.L4.ModularDistribution
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false
/-! Finite-product and analytic helpers for the Hermite statements.
Helper declarations stay in this namespace. The elementary coordinate
definitions are repeated, so this file does not import the statement file. -/

noncomputable section
open SICLean.L4 Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical
namespace SICLean.L5.DistributionHermiteAux

theorem hermite_roots_product (m : ℕ) (hm : 0 < m) (X : ℂ) :
    ∏ j ∈ Finset.range m, (1 - e ((j : ℂ) / (m : ℂ)) * X) = 1 - X ^ m := by
  have hζ : IsPrimitiveRoot (e (1 / (m : ℂ))) m := by
    convert Complex.isPrimitiveRoot_exp m (Nat.ne_of_gt hm) using 1
    unfold e
    congr 1
    ring
  have hp := X_pow_sub_C_eq_prod hζ hm (rfl : X ^ m = X ^ m)
  have he := congrArg (Polynomial.eval (1 : ℂ)) hp
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod, one_pow] at he
  rw [he]
  apply Finset.prod_congr rfl
  intro j hj
  rw [e_nat_mul]
  congr 3
  ring

theorem hermite_qPochhammer_roots (m : ℕ) (hm : 0 < m) (X q : ℂ)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ∏ j ∈ Finset.range m, qPochhammer (e ((j : ℂ) / (m : ℂ)) * X) q =
      qPochhammer (X ^ m) (q ^ m) := by
  have hP := hasProd_prod (s := Finset.range m)
    (fun j hj => hasProd_qPochhammer (e ((j : ℂ) / (m : ℂ)) * X) q hq0 hq1)
  have hq02 : 0 < ‖q ^ m‖ := by rw [norm_pow]; positivity
  have hq12 : ‖q ^ m‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq1 hm.ne'
  apply hP.unique
  apply (hasProd_qPochhammer (X ^ m) (q ^ m) hq02 hq12).congr_fun
  intro a
  symm
  calc
    1 - X ^ m * (q ^ m) ^ a = 1 - (X * q ^ a) ^ m := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m a]
    _ = ∏ j ∈ Finset.range m, (1 - e ((j : ℂ) / (m : ℂ)) * (X * q ^ a)) :=
      (hermite_roots_product m hm (X * q ^ a)).symm
    _ = _ := by simp only [mul_assoc]

def hermiteTau (n m : ℕ) (k : ℤ) (τ : ℂ) : ℂ :=
  ((n : ℂ) * τ + (k : ℂ)) / (m : ℂ)

def hermiteArgument (m i j : ℕ) (z τ : ℂ) : ℂ :=
  (z + (i : ℂ) * τ + (j : ℂ)) / (m : ℂ)

def hermiteNumIndex (n : ℕ) (u : ℤ) (i : ℕ) : ℤ := -(((i : ℤ) - u) / (n : ℤ))

lemma index_residue (n : ℕ) (u : ℤ) (i : ℕ) :
    (i : ℤ) + (n : ℤ) * hermiteNumIndex n u i =
      u + ((i : ℤ) - u) % (n : ℤ) := by
  have h := Int.emod_add_mul_ediv ((i : ℤ) - u) (n : ℤ)
  dsimp [hermiteNumIndex]
  linear_combination -h

lemma prod_shift_mod (n : ℕ) (hn : 0 < n) (u : ℤ) (F : ℕ → ℂ) :
    (∏ i ∈ Finset.range n, F (((i : ℤ) - u) % (n : ℤ)).toNat) =
      ∏ r ∈ Finset.range n, F r := by
  have hnZ : 0 < (n : ℤ) := by exact_mod_cast hn
  have hmem (a : ℤ) : (a % (n : ℤ)).toNat ∈ Finset.range n := by
    have h0 := Int.emod_nonneg a hnZ.ne'
    have h1 := Int.emod_lt_of_pos a hnZ
    simp only [Finset.mem_range]
    omega
  refine Finset.prod_bij'
    (fun i hi => (((i : ℤ) - u) % (n : ℤ)).toNat)
    (fun j hj => (((j : ℤ) + u) % (n : ℤ)).toNat)
    (fun i hi => hmem _) (fun j hj => hmem _) ?_ ?_ (fun i hi => rfl)
  · intro i hi
    have hi0 : 0 ≤ (i : ℤ) := by positivity
    have hin : (i : ℤ) < n := by exact_mod_cast Finset.mem_range.mp hi
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hnZ.ne'), Int.emod_add_emod,
      sub_add_cancel, Int.emod_eq_of_lt hi0 hin]
    simp
  · intro j hj
    have hj0 : 0 ≤ (j : ℤ) := by positivity
    have hjn : (j : ℤ) < n := by exact_mod_cast Finset.mem_range.mp hj
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hnZ.ne'), Int.emod_sub_emod,
      add_sub_cancel_right, Int.emod_eq_of_lt hj0 hjn]
    simp

lemma argument_split (m i j : ℕ) (z τ : ℂ) :
    e (hermiteArgument m i j z τ) =
      e ((j : ℂ) / (m : ℂ)) * e (hermiteArgument m i 0 z τ) := by
  rw [← e_add']
  congr 1
  simp only [hermiteArgument, Nat.cast_zero, add_zero]
  ring

lemma tau_power (n m : ℕ) (hm : 0 < m) (k : ℤ) (τ : ℂ) :
    e (hermiteTau n m k τ) ^ m = e τ ^ n := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [e_nat_mul, e_nat_mul]
  rw [show (m : ℂ) * hermiteTau n m k τ = (n : ℂ) * τ + (k : ℂ) by
    unfold hermiteTau
    field_simp]
  rw [e_add', e_intCast, mul_one]

lemma argument_power (n m : ℕ) (hm : 0 < m) (k a : ℤ) (i : ℕ) (z τ : ℂ) :
    (e (hermiteTau n m k τ) ^ a * e (hermiteArgument m i 0 z τ)) ^ m =
      e τ ^ ((i : ℤ) + (n : ℤ) * a) * e z := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [e_int_mul, ← e_add', e_nat_mul]
  rw [show (m : ℂ) * ((a : ℂ) * hermiteTau n m k τ +
      hermiteArgument m i 0 z τ) =
      (((i : ℤ) + (n : ℤ) * a : ℤ) : ℂ) * τ + z + ((a * k : ℤ) : ℂ) by
    unfold hermiteTau hermiteArgument
    push_cast
    field_simp
    ring]
  rw [e_add', e_intCast, mul_one, e_add', e_int_mul]

theorem hermite_q_numerators (n m : ℕ) (k u : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (hτ : 0 < τ.im) :
    (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m,
      modularPhiQNumerator (hermiteNumIndex n u i)
        (hermiteArgument m i j z τ) (hermiteTau n m k τ)) =
      modularPhiQNumerator u z τ := by
  have hτH : 0 < (hermiteTau n m k τ).im := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    simpa [hermiteTau] using div_pos (mul_pos hnR hτ) hmR
  have hqH0 : 0 < ‖e (hermiteTau n m k τ)‖ :=
    norm_pos_iff.mpr (e_ne_zero _)
  have hqH1 : ‖e (hermiteTau n m k τ)‖ < 1 := norm_e_lt_one ⟨_, hτH⟩
  have hq0 : 0 < ‖e τ‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hq1 : ‖e τ‖ < 1 := norm_e_lt_one ⟨_, hτ⟩
  have hnZ : 0 < (n : ℤ) := by exact_mod_cast hn
  calc
    _ = ∏ i ∈ Finset.range n,
        qPochhammer (e τ ^ ((i : ℤ) + (n : ℤ) * hermiteNumIndex n u i) * e z)
          (e τ ^ n) := by
      apply Finset.prod_congr rfl
      intro i hi
      calc
        _ = ∏ j ∈ Finset.range m,
            qPochhammer (e ((j : ℂ) / (m : ℂ)) *
              (e (hermiteTau n m k τ) ^ hermiteNumIndex n u i *
                e (hermiteArgument m i 0 z τ))) (e (hermiteTau n m k τ)) := by
          apply Finset.prod_congr rfl
          intro j hj
          unfold modularPhiQNumerator
          rw [argument_split]
          congr 1
          ring
        _ = _ := by
          rw [hermite_qPochhammer_roots m hm _ _ hqH0 hqH1,
            argument_power n m hm k (hermiteNumIndex n u i) i z τ,
            tau_power n m hm k τ]
    _ = ∏ i ∈ Finset.range n,
        qPochhammer ((e τ ^ u * e z) *
          e τ ^ (((i : ℤ) - u) % (n : ℤ)).toNat) (e τ ^ n) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [index_residue, zpow_add₀ (e_ne_zero τ)]
      have hcast : ((((i : ℤ) - u) % (n : ℤ)).toNat : ℤ) =
          ((i : ℤ) - u) % (n : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ hnZ.ne')
      rw [← hcast, zpow_natCast, Int.toNat_natCast]
      congr 1
      ring
    _ = ∏ r ∈ Finset.range n,
        qPochhammer ((e τ ^ u * e z) * e τ ^ r) (e τ ^ n) :=
      prod_shift_mod n hn u (fun r => qPochhammer ((e τ ^ u * e z) * e τ ^ r) (e τ ^ n))
    _ = _ := (qPochhammer_residue_classes (e τ ^ u * e z) (e τ) n hn hq0 hq1).symm


def hermiteMatrix (n m : ℕ) (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(n : ℤ), k; 0, (m : ℤ)]
def hermiteDenIndex (MJ : SL(2, ℤ)) (n i j : ℕ) : ℤ :=
  -((MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ)) / (n : ℤ))
def hermiteResidue (MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (ij : ℤ × ℤ) : ℤ × ℤ :=
  let a := MJ 1 1 * ij.1 - MJ 1 0 * ij.2
  let b := -MJ 0 1 * ij.1 + MJ 0 0 * ij.2
  let t := -(a / (n : ℤ))
  (a + (n : ℤ) * t, (b + k * t) % (m : ℤ))

theorem hermite_indices_eq_ceil (MJ : SL(2, ℤ)) (n : ℕ) (_hn : 0 < n)
    (u : ℤ) (i j : ℕ) :
    hermiteNumIndex n u i = ⌈((u : ℚ) - (i : ℚ)) / (n : ℚ)⌉ ∧
      hermiteDenIndex MJ n i j =
        ⌈(-(MJ 1 1 : ℚ) * (i : ℚ) + (MJ 1 0 : ℚ) * (j : ℚ)) / (n : ℚ)⌉ := by
  constructor
  · rw [hermiteNumIndex, show (u : ℚ) - i = -((i : ℤ) - u : ℤ) by push_cast; ring,
      neg_div, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast]
  · rw [hermiteDenIndex,
      show -(MJ 1 1 : ℚ) * i + (MJ 1 0 : ℚ) * j =
        -((MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ) : ℤ) : ℚ) by push_cast; ring,
      neg_div, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast]

theorem hermite_den_residue_bounds (MJ : SL(2, ℤ)) (n : ℕ) (hn : 0 < n) (i j : ℕ) :
    0 ≤ MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ) + (n : ℤ) * hermiteDenIndex MJ n i j ∧
      MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ) +
        (n : ℤ) * hermiteDenIndex MJ n i j < (n : ℤ) := by
  have hres : MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ) +
      (n : ℤ) * hermiteDenIndex MJ n i j =
      (MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ)) % n := by
    have hh := Int.emod_add_mul_ediv (MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ)) (n : ℤ)
    dsimp [hermiteDenIndex]
    nlinarith
  rw [hres]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

theorem hermite_orbit_index_match (MJ : SL(2, ℤ)) (n : ℕ) (hn : 0 < n)
    (u h : ℤ) (i j i' : ℕ)
    (hstep : u + MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ) = (i' : ℤ) + (n : ℤ) * h) :
    hermiteNumIndex n u i' = hermiteDenIndex MJ n i j + h := by
  have heq : (i' : ℤ) - u = (MJ 1 1 * (i : ℤ) - MJ 1 0 * (j : ℤ)) + (-h) * n := by linear_combination -hstep
  simp only [hermiteNumIndex, hermiteDenIndex, heq,
    Int.add_mul_ediv_right _ _ (show (n : ℤ) ≠ 0 by omega)]
  omega


theorem hermite_matrix_entries (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) :
    MI 0 0 * (n : ℤ) = (n : ℤ) * MJ 0 0 + k * MJ 1 0 ∧
    MI 0 0 * k + MI 0 1 * (m : ℤ) = (n : ℤ) * MJ 0 1 + k * MJ 1 1 ∧
    MI 1 0 * (n : ℤ) = (m : ℤ) * MJ 1 0 ∧
    MI 1 0 * k + MI 1 1 * (m : ℤ) = (m : ℤ) * MJ 1 1 := by
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 0) hH
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 1) hH
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) hH
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 1) hH
  simp [hermiteMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem hermite_denom (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (τ : ℂ)
    (hm : 0 < m)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) :
    etaDenom MI (hermiteTau n m k τ) = etaDenom MJ τ := by
  obtain ⟨_, _, h10, h11⟩ := hermite_matrix_entries MI MJ n m k hH
  have h10c : (MI 1 0 : ℂ) * (n : ℂ) = (m : ℂ) * (MJ 1 0 : ℂ) := by exact_mod_cast h10
  have h11c : (MI 1 0 : ℂ) * (k : ℂ) + (MI 1 1 : ℂ) * (m : ℂ) =
      (m : ℂ) * (MJ 1 1 : ℂ) := by exact_mod_cast h11
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  dsimp [etaDenom, hermiteTau]
  field_simp
  linear_combination h10c * τ + h11c

theorem hermite_automorphy (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (τ : ℂ)
    (_hn : 0 < n) (hm : 0 < m)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ))
    (hden : etaDenom MJ τ ≠ 0) :
    etaDenom MI (hermiteTau n m k τ) = etaDenom MJ τ ∧
      etaMobius MI (hermiteTau n m k τ) = hermiteTau n m k (etaMobius MJ τ) := by
  have hd := hermite_denom MI MJ n m k τ hm hH
  refine ⟨hd, ?_⟩
  obtain ⟨h00, h01, _, _⟩ := hermite_matrix_entries MI MJ n m k hH
  have h00c : (MI 0 0 : ℂ) * (n : ℂ) =
      (n : ℂ) * (MJ 0 0 : ℂ) + (k : ℂ) * (MJ 1 0 : ℂ) := by exact_mod_cast h00
  have h01c : (MI 0 0 : ℂ) * (k : ℂ) + (MI 0 1 : ℂ) * (m : ℂ) =
      (n : ℂ) * (MJ 0 1 : ℂ) + (k : ℂ) * (MJ 1 1 : ℂ) := by exact_mod_cast h01
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  unfold etaMobius
  rw [hd]
  dsimp [hermiteTau]
  field_simp
  dsimp [etaDenom]
  linear_combination h00c * τ + h01c

theorem hermite_domain (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (τ : ℂ)
    (_hn : 0 < n) (hm : 0 < m)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) :
    hermiteTau n m k τ ∈ modularPhiDomain MI ↔ τ ∈ modularPhiDomain MJ := by
  simp only [modularPhiDomain, Set.mem_ofPred_eq, hermite_denom MI MJ n m k τ hm hH]


theorem hermite_inverse_lattice (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) (x : ℤ × ℤ) :
    ∃ s t : ℤ,
      x.1 = MJ 0 0 * (hermiteResidue MJ n m k x).1 +
        MJ 1 0 * (hermiteResidue MJ n m k x).2 + (n : ℤ) * s ∧
      x.2 = MJ 0 1 * (hermiteResidue MJ n m k x).1 +
        MJ 1 1 * (hermiteResidue MJ n m k x).2 + k * s + (m : ℤ) * t := by
  obtain ⟨h00, h01, h10, h11⟩ := hermite_matrix_entries MI MJ n m k hH
  have hdet : MJ 0 0 * MJ 1 1 - MJ 0 1 * MJ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using MJ.det_coe
  let a := MJ 1 1 * x.1 - MJ 1 0 * x.2
  let b := -MJ 0 1 * x.1 + MJ 0 0 * x.2
  let r := -(a / (n : ℤ))
  let q := (b + k * r) / (m : ℤ)
  have hr1 : (hermiteResidue MJ n m k x).1 = a + n * r := rfl
  have hr2 : (hermiteResidue MJ n m k x).2 + (m : ℤ) * q = b + k * r := by
    exact Int.emod_add_mul_ediv (b + k * r) (m : ℤ)
  have hx1 : x.1 = MJ 0 0 * a + MJ 1 0 * b := by
    dsimp [a, b]
    linear_combination -x.1 * hdet
  have hx2 : x.2 = MJ 0 1 * a + MJ 1 1 * b := by
    dsimp [a, b]
    linear_combination -x.2 * hdet
  refine ⟨-MI 0 0 * r + MI 1 0 * q, -MI 0 1 * r + MI 1 1 * q, ?_, ?_⟩
  · linear_combination hx1 - MJ 0 0 * hr1 - MJ 1 0 * hr2 + r * h00 - q * h10
  · linear_combination hx2 - MJ 0 1 * hr1 - MJ 1 1 * hr2 + r * h01 - q * h11

theorem hermite_inverse_residues_bijOn (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ)
    (hn : 0 < n) (hm : 0 < m)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) :
    Set.BijOn (hermiteResidue MJ n m k)
      ((Set.Ico 0 (n : ℤ)) ×ˢ (Set.Ico 0 (m : ℤ)))
      ((Set.Ico 0 (n : ℤ)) ×ˢ (Set.Ico 0 (m : ℤ))) := by
  have hnZ : 0 < (n : ℤ) := by exact_mod_cast hn
  have hmZ : 0 < (m : ℤ) := by exact_mod_cast hm
  have maps : Set.MapsTo (hermiteResidue MJ n m k)
      ((Set.Ico 0 (n : ℤ)) ×ˢ (Set.Ico 0 (m : ℤ)))
      ((Set.Ico 0 (n : ℤ)) ×ˢ (Set.Ico 0 (m : ℤ))) := by
    intro x _
    change (0 ≤ (hermiteResidue MJ n m k x).1 ∧ (hermiteResidue MJ n m k x).1 < n) ∧
      (0 ≤ (hermiteResidue MJ n m k x).2 ∧ (hermiteResidue MJ n m k x).2 < m)
    have hr : (hermiteResidue MJ n m k x).1 =
        (MJ 1 1 * x.1 - MJ 1 0 * x.2) % n := by
      have hh := Int.emod_add_mul_ediv (MJ 1 1 * x.1 - MJ 1 0 * x.2) (n : ℤ)
      dsimp [hermiteResidue]
      nlinarith
    rw [hr]
    exact ⟨⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩,
      Int.emod_nonneg _ hmZ.ne', Int.emod_lt_of_pos _ hmZ⟩
  apply ((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) m)).injOn_iff_bijOn_of_mapsTo maps |>.mp
  intro x hx y hy heq
  obtain ⟨sx, tx, hx1, hx2⟩ := hermite_inverse_lattice MI MJ n m k hH x
  obtain ⟨sy, ty, hy1, hy2⟩ := hermite_inverse_lattice MI MJ n m k hH y
  rw [heq] at hx1 hx2
  have hfirst : x.1 = y.1 + (n : ℤ) * (sx - sy) := by linear_combination hx1 - hy1
  have hfirsteq : x.1 = y.1 := by
    have hmod := congrArg (fun a : ℤ => a % (n : ℤ)) hfirst
    simpa only [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hx.1.1 hx.1.2,
      Int.emod_eq_of_lt hy.1.1 hy.1.2] using hmod
  have hs : sx = sy := by
    have hmul : (n : ℤ) * (sx - sy) = 0 := by omega
    have := (mul_eq_zero.mp hmul).resolve_left hnZ.ne'
    omega
  have hsecond : x.2 = y.2 + (m : ℤ) * (tx - ty) := by
    rw [hs] at hx2
    linear_combination hx2 - hy2
  have hsecondeq : x.2 = y.2 := by
    have hmod := congrArg (fun a : ℤ => a % (m : ℤ)) hsecond
    simpa only [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hx.2.1 hx.2.2,
      Int.emod_eq_of_lt hy.2.1 hy.2.2] using hmod
  exact Prod.ext hfirsteq hsecondeq


lemma denominator_term (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ))
    (hD : etaDenom MJ τ ≠ 0) (i j : ℕ) :
    modularPhiQDenominator MI (hermiteDenIndex MJ n i j)
      (hermiteArgument m i j z τ) (hermiteTau n m k τ) =
    modularPhiQNumerator 0
      (hermiteArgument m (hermiteResidue MJ n m k ((i : ℤ), (j : ℤ))).1.toNat
        (hermiteResidue MJ n m k ((i : ℤ), (j : ℤ))).2.toNat
        (z / etaDenom MJ τ) (etaMobius MJ τ))
      (hermiteTau n m k (etaMobius MJ τ)) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  let a : ℤ := MJ 1 1 * i - MJ 1 0 * j
  let b : ℤ := -MJ 0 1 * i + MJ 0 0 * j
  let B := hermiteDenIndex MJ n i j
  let r := hermiteResidue MJ n m k ((i : ℤ), (j : ℤ))
  have hr1 : 0 ≤ r.1 := (hermite_den_residue_bounds MJ n hn i j).1
  have hr2 : 0 ≤ r.2 := Int.emod_nonneg _ hmZ
  have hr1C : ((r.1.toNat : ℕ) : ℂ) = (a : ℂ) + (n : ℂ) * (B : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hr1]
    change ((a + (n : ℤ) * B : ℤ) : ℂ) = _
    push_cast
    rfl
  have hr2Z : r.2 + (m : ℤ) * ((b + k * B) / (m : ℤ)) = b + k * B :=
    Int.emod_add_mul_ediv _ _
  have hr2C : ((r.2.toNat : ℕ) : ℂ) + (m : ℂ) * (((b + k * B) / (m : ℤ) : ℤ) : ℂ) =
      (b : ℂ) + (k : ℂ) * (B : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hr2]
    exact_mod_cast hr2Z
  have hdet : (MJ 0 0 : ℂ) * (MJ 1 1 : ℂ) -
      (MJ 0 1 : ℂ) * (MJ 1 0 : ℂ) = 1 := by exact_mod_cast det_coe_int MJ
  have hcoord : (i : ℂ) * τ + (j : ℂ) =
      ((a : ℂ) * etaMobius MJ τ + (b : ℂ)) * etaDenom MJ τ := by
    dsimp [a, b]
    push_cast
    unfold etaMobius
    field_simp [hD]
    simp only [etaDenom] at *
    linear_combination -((i : ℂ) * τ + (j : ℂ)) * hdet
  have hphase : (B : ℂ) * hermiteTau n m k (etaMobius MJ τ) +
      hermiteArgument m i j z τ / etaDenom MJ τ =
      hermiteArgument m r.1.toNat r.2.toNat (z / etaDenom MJ τ) (etaMobius MJ τ) +
        (((b + k * B) / (m : ℤ) : ℤ) : ℂ) := by
    dsimp only [hermiteTau, hermiteArgument]
    rw [hr1C]
    field_simp [hmC, hD]
    linear_combination hcoord - etaDenom MJ τ * hr2C
  dsimp only [modularPhiQDenominator, modularPhiQNumerator]
  rw [(hermite_automorphy MI MJ n m k τ hn hm hH hD).1,
    (hermite_automorphy MI MJ n m k τ hn hm hH hD).2]
  rw [zpow_zero, one_mul, e_int_mul, ← e_add', hphase, e_add', e_intCast, mul_one]


lemma denominator_product (MI MJ : SL(2, ℤ)) (n m : ℕ) (k : ℤ) (z τ : ℂ)
    (hn : 0 < n) (hm : 0 < m) (_hI : 0 < MI 1 0) (_hJ : 0 < MJ 1 0)
    (hH : (MI : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix n m k =
      hermiteMatrix n m k * (MJ : Matrix (Fin 2) (Fin 2) ℤ)) (hτ : 0 < τ.im) :
    (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m,
      modularPhiQDenominator MI (hermiteDenIndex MJ n i j)
        (hermiteArgument m i j z τ) (hermiteTau n m k τ)) =
      modularPhiQDenominator MJ 0 z τ := by
  let S := (Finset.range n) ×ˢ (Finset.range m)
  let R : ℕ × ℕ → ℕ × ℕ := fun p =>
    let r := hermiteResidue MJ n m k ((p.1 : ℤ), (p.2 : ℤ))
    (r.1.toNat, r.2.toNat)
  have hin (p : ℕ × ℕ) (hp : p ∈ S) :
      ((p.1 : ℤ), (p.2 : ℤ)) ∈
        ((Set.Ico 0 (n : ℤ)) ×ˢ (Set.Ico 0 (m : ℤ))) := by
    simp only [S, Finset.mem_product, Finset.mem_range] at hp
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hbij := hermite_inverse_residues_bijOn MI MJ n m k hn hm hH
  have hcast (p : ℕ × ℕ) (hp : p ∈ S) :
      ((R p).1 : ℤ) = (hermiteResidue MJ n m k ((p.1 : ℤ), (p.2 : ℤ))).1 ∧
      ((R p).2 : ℤ) = (hermiteResidue MJ n m k ((p.1 : ℤ), (p.2 : ℤ))).2 := by
    have hr := hbij.mapsTo (hin p hp)
    exact ⟨Int.toNat_of_nonneg hr.1.1, Int.toNat_of_nonneg hr.2.1⟩
  have hRS (p : ℕ × ℕ) (hp : p ∈ S) : R p ∈ S := by
    have hr := hbij.mapsTo (hin p hp)
    have hc := hcast p hp
    have hrn := hr.1.2
    have hrm := hr.2.2
    simp only [S, Finset.mem_product, Finset.mem_range]
    constructor <;> omega
  have hprod : (∏ p ∈ S,
      modularPhiQNumerator 0
        (hermiteArgument m (R p).1 (R p).2 (z / etaDenom MJ τ) (etaMobius MJ τ))
        (hermiteTau n m k (etaMobius MJ τ))) =
      ∏ p ∈ S, modularPhiQNumerator 0
        (hermiteArgument m p.1 p.2 (z / etaDenom MJ τ) (etaMobius MJ τ))
        (hermiteTau n m k (etaMobius MJ τ)) := by
    apply Finset.prod_bij (fun p _ => R p) hRS
    · intro p hp q hq hpq
      have hR : hermiteResidue MJ n m k ((p.1 : ℤ), (p.2 : ℤ)) =
          hermiteResidue MJ n m k ((q.1 : ℤ), (q.2 : ℤ)) := by
        apply Prod.ext
        · rw [← (hcast p hp).1, ← (hcast q hq).1, hpq]
        · rw [← (hcast p hp).2, ← (hcast q hq).2, hpq]
      have heq := hbij.injOn (hin p hp) (hin q hq) hR
      exact Prod.ext (by simpa using congrArg Prod.fst heq)
        (by simpa using congrArg Prod.snd heq)
    · intro q hq
      obtain ⟨p, hp, hpq⟩ := hbij.surjOn (hin q hq)
      let pN : ℕ × ℕ := (p.1.toNat, p.2.toNat)
      have hcN : ((pN.1 : ℤ), (pN.2 : ℤ)) = p := by
        exact Prod.ext (Int.toNat_of_nonneg hp.1.1) (Int.toNat_of_nonneg hp.2.1)
      have hpN : pN ∈ S := by
        simp only [S, Finset.mem_product, Finset.mem_range]
        have h1 := congrArg Prod.fst hcN
        have h2 := congrArg Prod.snd hcN
        have hpn := hp.1.2
        have hpm := hp.2.2
        constructor <;> omega
      refine ⟨pN, hpN, ?_⟩
      have heq : hermiteResidue MJ n m k ((pN.1 : ℤ), (pN.2 : ℤ)) =
          ((q.1 : ℤ), (q.2 : ℤ)) := hcN ▸ hpq
      apply Prod.ext
      · have hh := congrArg Prod.fst heq
        rw [← (hcast pN hpN).1] at hh
        simpa only [Prod.fst, Prod.snd, Int.natCast_inj] using hh
      · have hh := congrArg Prod.snd heq
        rw [← (hcast pN hpN).2] at hh
        simpa only [Prod.fst, Prod.snd, Int.natCast_inj] using hh
    · intro p hp
      rfl
  have hzero (i : ℕ) (hi : i ∈ Finset.range n) : hermiteNumIndex n 0 i = 0 := by
    have hi' := Finset.mem_range.mp hi
    unfold hermiteNumIndex
    simp only [sub_zero]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega), neg_zero]
  rw [← Finset.prod_product']
  calc
    (∏ p ∈ S, modularPhiQDenominator MI (hermiteDenIndex MJ n p.1 p.2)
      (hermiteArgument m p.1 p.2 z τ) (hermiteTau n m k τ)) =
        ∏ p ∈ S, modularPhiQNumerator 0
          (hermiteArgument m (R p).1 (R p).2 (z / etaDenom MJ τ) (etaMobius MJ τ))
          (hermiteTau n m k (etaMobius MJ τ)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact denominator_term MI MJ n m k z τ hn hm hH
        (ModularCocycleUpperAux.etaDenom_ne_zero_upper MJ hτ) p.1 p.2
    _ = _ := hprod
    _ = modularPhiQDenominator MJ 0 z τ := by
      rw [Finset.prod_product]
      have hnum := hermite_q_numerators n m k 0 (z / etaDenom MJ τ) (etaMobius MJ τ)
        hn hm (ModularCocycleUpperAux.etaMobius_im_pos MJ hτ)
      convert hnum using 1
      · apply Finset.prod_congr rfl
        intro i hi
        rw [hzero i hi]
      · rfl



/-- Continue finite products through compatible analytic quotient charts. -/
theorem product_chart_cross_mul_of_upper {α : Type*} [Fintype α]
    (M N : SL(2, ℤ)) (hM : 0 < M 1 0) (hN : 0 < N 1 0)
    (u v : ℤ) (r s : α → ℤ) (T : ℂ → ℂ) (Z : α → ℂ → ℂ → ℂ)
    (hmap : ∀ t p, AnalyticAt ℂ (fun q : ℂ × ℂ => (Z t q.1 q.2, T q.2)) p)
    (hslice : ∀ t z τ, Tendsto (fun w => Z t w τ) (𝓝[≠] z) (𝓝[≠] (Z t z τ)))
    (hdom : ∀ τ, T τ ∈ modularPhiDomain N ↔ τ ∈ modularPhiDomain M)
    (hupper : ∀ z τ : ℂ, 0 < τ.im →
      (fun w => modularPhi M u v w τ) =ᶠ[𝓝[≠] z]
        (fun w => ∏ t, modularPhi N (r t) (s t) (Z t w τ) (T τ)))
    (κ : ℕ → ℤ) (κI : α → ℕ → ℤ) (z₀ τ₀ : ℂ)
    (hκ : (z₀, τ₀) ∈ modularPhiChartDomain M u v κ)
    (hL : ∀ t, (Z t z₀ τ₀, T τ₀) ∈ modularPhiChartDomain N (r t) (s t) (κI t)) :
    modularPhiChartNumerator M u v κ z₀ τ₀ *
        (∏ t, modularPhiChartDenominator N (r t) (s t) (κI t) (Z t z₀ τ₀) (T τ₀)) =
      modularPhiChartDenominator M u v κ z₀ τ₀ *
        (∏ t, modularPhiChartNumerator N (r t) (s t) (κI t) (Z t z₀ τ₀) (T τ₀)) := by
  let ι := (ℕ → ℤ) × (α → ℕ → ℤ)
  let F : α → (ℂ × ℂ) → ℂ × ℂ := fun t p => (Z t p.1 p.2, T p.2)
  let Ω : Set (ℂ × ℂ) := Set.univ ×ˢ modularPhiDomain M
  let U : ι → Set (ℂ × ℂ) := fun i =>
    {p | p ∈ modularPhiChartDomain M u v i.1 ∧
      ∀ t, F t p ∈ modularPhiChartDomain N (r t) (s t) (i.2 t)}
  let a : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiChartNumerator M u v i.1 p.1 p.2
  let b : ι → (ℂ × ℂ) → ℂ := fun i p =>
    ∏ t, modularPhiChartNumerator N (r t) (s t) (i.2 t) (F t p).1 (F t p).2
  let x : ι → (ℂ × ℂ) → ℂ := fun i p =>
    modularPhiChartDenominator M u v i.1 p.1 p.2
  let y : ι → (ℂ × ℂ) → ℂ := fun i p =>
    ∏ t, modularPhiChartDenominator N (r t) (s t) (i.2 t) (F t p).1 (F t p).2
  have hΩ : IsPreconnected Ω := isPreconnected_univ.prod
    (ModularCocycleAux.modularPhiDomain_isPreconnected M hM.ne')
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    have hf : ∀ t, Continuous (F t) := fun t => continuous_iff_continuousAt.mpr
      (fun p => (hmap t p).continuousAt)
    have hfi : IsOpen {p | ∀ t, F t p ∈ modularPhiChartDomain N (r t) (s t) (i.2 t)} := by
      have heq : {p | ∀ t, F t p ∈ modularPhiChartDomain N (r t) (s t) (i.2 t)} =
          ⋂ t : α, (F t) ⁻¹' modularPhiChartDomain N (r t) (s t) (i.2 t) := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
      rw [heq]
      exact isOpen_iInter_of_finite fun t : α =>
        (modularPhiChartDomain_isOpen N (r t) (s t) (i.2 t)).preimage (hf t)
    exact (modularPhiChartDomain_isOpen M u v i.1).inter hfi
  have hsub : ∀ i, U i ⊆ Ω := fun _ _ hp => ⟨Set.mem_univ _, hp.1.1⟩
  have hcover : ∀ p ∈ Ω, ∃ i, p ∈ U i := by
    intro p hp
    obtain ⟨κp, hκp⟩ := ModularDistributionAux.chart_cover M u v p hp.2
    have hf : ∀ t, ∃ Lt, F t p ∈ modularPhiChartDomain N (r t) (s t) Lt :=
      fun t => ModularDistributionAux.chart_cover N (r t) (s t) (F t p)
        ((hdom p.2).mpr hp.2)
    choose Lp hLp using hf
    exact ⟨(κp, Lp), hκp, hLp⟩
  have ha : ∀ i, AnalyticOnNhd ℂ (a i) (U i) := fun i p hp =>
    (modularPhiChart_analytic M hM u v i.1).1 p hp.1
  have hx : ∀ i, AnalyticOnNhd ℂ (x i) (U i) := fun i p hp =>
    (modularPhiChart_analytic M hM u v i.1).2 p hp.1
  have hb : ∀ i, AnalyticOnNhd ℂ (b i) (U i) := by
    intro i
    apply Finset.analyticOnNhd_fun_prod
    intro t ht p hp
    exact ((modularPhiChart_analytic N hN (r t) (s t) (i.2 t)).1 (F t p) (hp.2 t)).comp
      (hmap t p)
  have hy : ∀ i, AnalyticOnNhd ℂ (y i) (U i) := by
    intro i
    apply Finset.analyticOnNhd_fun_prod
    intro t ht p hp
    exact ((modularPhiChart_analytic N hN (r t) (s t) (i.2 t)).2 (F t p) (hp.2 t)).comp
      (hmap t p)
  have hne : ∀ i p, p ∈ U i → ∀ᶠ w in 𝓝[≠] p.1,
      x i (w, p.2) ≠ 0 ∧ y i (w, p.2) ≠ 0 ∧ (1 : ℂ) ≠ 0 := by
    intro i p hp
    have hLp : ∀ᶠ w in 𝓝[≠] p.1, ∀ t,
        modularPhiChartDenominator N (r t) (s t) (i.2 t) (Z t w p.2) (T p.2) ≠ 0 :=
      Filter.eventually_all.mpr fun t => (hslice t p.1 p.2).eventually
        (ModularDistributionAux.chart_den_eventually N hN (r t) (s t) (i.2 t) (F t p) (hp.2 t))
    filter_upwards [ModularDistributionAux.chart_den_eventually M hM u v i.1 p hp.1, hLp]
      with w hw hwt
    exact ⟨hw, Finset.prod_ne_zero_iff.mpr (fun t _ => hwt t), one_ne_zero⟩
  have hcompat : ∀ i j p, p ∈ U i → p ∈ U j →
      a i p * x j p = a j p * x i p ∧
      b i p * y j p = b j p * y i p ∧ (1 : ℂ) * 1 = 1 * 1 := by
    intro i j p hi hj
    refine ⟨modularPhiChart_overlap_cross_mul M hM u v i.1 j.1 p hi.1 hj.1, ?_, rfl⟩
    dsimp only [b, y]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t ht
    exact modularPhiChart_overlap_cross_mul N hN (r t) (s t) (i.2 t) (j.2 t)
      (F t p) (hi.2 t) (hj.2 t)
  have hcross : ∀ i p, p ∈ U i → 0 < p.2.im → a i p * y i p = b i p * x i p := by
    intro i p hp hpu
    have hemb : ContinuousAt (fun w : ℂ => (w, p.2)) p.1 :=
      continuousAt_id.prodMk continuousAt_const
    have hsliceC {f : (ℂ × ℂ) → ℂ} (hf : ContinuousAt f p) :
        ContinuousAt (fun w => f (w, p.2)) p.1 :=
      hf.comp (f := fun w : ℂ => (w, p.2)) hemb
    have hloc : ∀ᶠ w in 𝓝[≠] p.1, (w, p.2) ∈ U i :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (hemb.preimage_mem_nhds ((hU i).mem_nhds hp))
    have hratio : (fun w => a i (w, p.2) / x i (w, p.2)) =ᶠ[𝓝[≠] p.1]
        (fun w => (b i (w, p.2) / y i (w, p.2)) * (1 / 1)) := by
      filter_upwards [hupper p.1 p.2 hpu, hloc] with w hw hwi
      have hpw : (∏ t, modularPhi N (r t) (s t) (Z t w p.2) (T p.2)) =
          b i (w, p.2) / y i (w, p.2) := by
        dsimp only [b, y, F]
        rw [← Finset.prod_div_distrib]
        apply Finset.prod_congr rfl
        intro t ht
        exact modularPhi_eq_chart N hN (r t) (s t) (i.2 t) (F t (w, p.2)) (hwi.2 t)
      rw [modularPhi_eq_chart M hM u v i.1 (w, p.2) hwi.1, hpw] at hw
      simpa only [modularPhiChart, a, x, div_self one_ne_zero, mul_one] using hw
    simpa only [mul_one] using ModularCocycleContinuationAux.cross_mul_of_quotient_germ
      (fun w => a i (w, p.2)) (fun w => b i (w, p.2)) (fun _ => 1)
      (fun w => x i (w, p.2)) (fun w => y i (w, p.2)) (fun _ => 1) p.1
      (hsliceC (ha i p hp).continuousAt) (hsliceC (hb i p hp).continuousAt) continuousAt_const
      (hsliceC (hx i p hp).continuousAt) (hsliceC (hy i p hp).continuousAt) continuousAt_const
      (hne i p hp) hratio
  obtain ⟨i₀, hi₀⟩ := hcover (0, Complex.I)
    ⟨Set.mem_univ _, upper_mem_modularPhiDomain M hM UpperHalfPlane.I⟩
  have hzero : (fun p => a i₀ p * y i₀ p * 1 - b i₀ p * 1 * x i₀ p)
      =ᶠ[𝓝 (0, Complex.I)] 0 := by
    have hu : IsOpen {p : ℂ × ℂ | 0 < p.2.im} :=
      isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd)
    filter_upwards [(hU i₀).mem_nhds hi₀, hu.mem_nhds (by norm_num)] with p hp hpu
    change a i₀ p * y i₀ p * 1 - b i₀ p * 1 * x i₀ p = 0
    simpa only [mul_one] using sub_eq_zero.mpr (hcross i₀ p hp hpu)
  have hid := ModularCocycleContinuationAux.cocycle_atlas_identity Ω U a b (fun _ _ => 1)
    x y (fun _ _ => 1) hΩ hU hsub hcover ha hb (fun _ => analyticOnNhd_const)
    hx hy (fun _ => analyticOnNhd_const) hne hcompat i₀ (0, Complex.I) hi₀ hzero
    (κ, κI) (z₀, τ₀) ⟨hκ, hL⟩
  dsimp only [a, b, x, y, F] at hid
  simpa only [mul_one, one_mul, mul_comm] using hid

theorem product_germ_of_chart_cross_mul {α : Type*} [Fintype α]
    (M N : SL(2, ℤ)) (hM : 0 < M 1 0) (hN : 0 < N 1 0)
    (u v : ℤ) (r s : α → ℤ) (T : ℂ → ℂ) (Z : α → ℂ → ℂ → ℂ)
    (hmap : ∀ t p, AnalyticAt ℂ (fun q : ℂ × ℂ => (Z t q.1 q.2, T q.2)) p)
    (hslice : ∀ t z τ, Tendsto (fun w => Z t w τ) (𝓝[≠] z) (𝓝[≠] (Z t z τ)))
    (hdom : ∀ τ, T τ ∈ modularPhiDomain N ↔ τ ∈ modularPhiDomain M)
    (hcross : ∀ (κ : ℕ → ℤ) (κI : α → ℕ → ℤ) (z τ : ℂ),
      (z, τ) ∈ modularPhiChartDomain M u v κ →
      (∀ t, (Z t z τ, T τ) ∈ modularPhiChartDomain N (r t) (s t) (κI t)) →
      modularPhiChartNumerator M u v κ z τ *
          (∏ t, modularPhiChartDenominator N (r t) (s t) (κI t) (Z t z τ) (T τ)) =
        modularPhiChartDenominator M u v κ z τ *
          (∏ t, modularPhiChartNumerator N (r t) (s t) (κI t) (Z t z τ) (T τ)))
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M u v w τ) =ᶠ[𝓝[≠] z]
      (fun w => ∏ t, modularPhi N (r t) (s t) (Z t w τ) (T τ)) := by
  let F : α → (ℂ × ℂ) → ℂ × ℂ := fun t p => (Z t p.1 p.2, T p.2)
  obtain ⟨κ, hκ⟩ := ModularDistributionAux.chart_cover M u v (z, τ) hτ
  have hf : ∀ t, ∃ κt, F t (z, τ) ∈ modularPhiChartDomain N (r t) (s t) κt :=
    fun t => ModularDistributionAux.chart_cover N (r t) (s t) (F t (z, τ))
      ((hdom τ).mpr hτ)
  choose κI hκI using hf
  have hemb : ContinuousAt (fun w : ℂ => (w, τ)) z :=
    continuousAt_id.prodMk continuousAt_const
  have hlocJ : ∀ᶠ w in 𝓝[≠] z, (w, τ) ∈ modularPhiChartDomain M u v κ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hemb.preimage_mem_nhds ((modularPhiChartDomain_isOpen M u v κ).mem_nhds hκ))
  have hlocI : ∀ᶠ w in 𝓝[≠] z, ∀ t,
      F t (w, τ) ∈ modularPhiChartDomain N (r t) (s t) (κI t) := by
    apply Filter.eventually_all.mpr
    intro t
    have hc : ContinuousAt (fun w : ℂ => F t (w, τ)) z :=
      (hmap t (z, τ)).continuousAt.comp (f := fun w : ℂ => (w, τ)) hemb
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hc.preimage_mem_nhds
        ((modularPhiChartDomain_isOpen N (r t) (s t) (κI t)).mem_nhds (hκI t)))
  have hdenI : ∀ᶠ w in 𝓝[≠] z, ∀ t,
      modularPhiChartDenominator N (r t) (s t) (κI t) (Z t w τ) (T τ) ≠ 0 :=
    Filter.eventually_all.mpr fun t => (hslice t z τ).eventually
      (ModularDistributionAux.chart_den_eventually N hN (r t) (s t) (κI t) (F t (z, τ)) (hκI t))
  filter_upwards [hlocJ, hlocI,
    ModularDistributionAux.chart_den_eventually M hM u v κ (z, τ) hκ, hdenI]
    with w hwJ hwI hdJ hdI
  rw [modularPhi_eq_chart M hM u v κ (w, τ) hwJ]
  have hprod : (∏ t, modularPhi N (r t) (s t) (Z t w τ) (T τ)) =
      (∏ t, modularPhiChartNumerator N (r t) (s t) (κI t) (Z t w τ) (T τ)) /
        (∏ t, modularPhiChartDenominator N (r t) (s t) (κI t) (Z t w τ) (T τ)) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro t ht
    exact modularPhi_eq_chart N hN (r t) (s t) (κI t) (F t (w, τ)) (hwI t)
  rw [hprod]
  apply (div_eq_div_iff hdJ (Finset.prod_ne_zero_iff.mpr (fun t _ => hdI t))).mpr
  simpa only [mul_comm] using hcross κ κI w τ hwJ hwI

theorem product_germ_of_upper {α : Type*} [Fintype α]
    (M N : SL(2, ℤ)) (hM : 0 < M 1 0) (hN : 0 < N 1 0)
    (u v : ℤ) (r s : α → ℤ) (T : ℂ → ℂ) (Z : α → ℂ → ℂ → ℂ)
    (hmap : ∀ t p, AnalyticAt ℂ (fun q : ℂ × ℂ => (Z t q.1 q.2, T q.2)) p)
    (hslice : ∀ t z τ, Tendsto (fun w => Z t w τ) (𝓝[≠] z) (𝓝[≠] (Z t z τ)))
    (hdom : ∀ τ, T τ ∈ modularPhiDomain N ↔ τ ∈ modularPhiDomain M)
    (hupper : ∀ z τ : ℂ, 0 < τ.im →
      (fun w => modularPhi M u v w τ) =ᶠ[𝓝[≠] z]
        (fun w => ∏ t, modularPhi N (r t) (s t) (Z t w τ) (T τ)))
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M u v w τ) =ᶠ[𝓝[≠] z]
      (fun w => ∏ t, modularPhi N (r t) (s t) (Z t w τ) (T τ)) := by
  exact product_germ_of_chart_cross_mul M N hM hN u v r s T Z hmap hslice hdom
    (product_chart_cross_mul_of_upper M N hM hN u v r s T Z hmap hslice hdom hupper) z τ hτ


end SICLean.L5.DistributionHermiteAux
