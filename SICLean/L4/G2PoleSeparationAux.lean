import SICLean.L4.G2RepresentativeWindow

set_option autoImplicit false

noncomputable section
open Classical Set
open scoped MatrixGroups

namespace SICLean.L4.G2PoleSeparationAux

open G2

/-- The characteristic equation clears the positive translation length. -/
theorem collision_identity (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (k : ℤ) (U V : ℕ)
    (hc : inverseOffset M v = (k : ℝ) * length M -
      epsilon M * (U : ℝ) - (V : ℝ)) :
    (U : ℝ) + (V : ℝ) + epsilon M *
      ((sIndex M v - k * specialValueOrder M -
        (specialValueOrder M + 1) * (U : ℤ) - (V : ℤ) : ℤ) : ℝ) = 0 := by
  have hL := length_pos M hM
  have hs : inverseOffset M v * length M = epsilon M * (sIndex M v : ℝ) := by
    dsimp [inverseOffset, scale]
    field_simp
  have hcL := congrArg (fun t : ℝ => t * length M) hc
  have hNU := congrArg (fun t : ℝ => t * (U : ℝ)) (epsilon_characteristic M hM)
  have hNk := congrArg (fun t : ℝ => (k : ℝ) * t) (length_sq M hM)
  push_cast
  rw [hs] at hcL
  dsimp [length] at hcL hNk
  nlinarith

/-- An irrational real number has no nontrivial integral affine relation. -/
theorem irrational_linear (e : ℝ) (he : Irrational e) (A B : ℤ)
    (h : (A : ℝ) + e * (B : ℝ) = 0) : A = 0 ∧ B = 0 := by
  have hB : B = 0 := by
    by_contra hn
    apply he.ne_rational (-A) B
    apply (eq_div_iff (by exact_mod_cast hn)).2
    push_cast
    linarith
  refine ⟨?_, hB⟩
  rw [hB, Int.cast_zero, mul_zero, add_zero] at h
  exact_mod_cast h

/-- The deep window excludes every possible difference of allowed translates. -/
theorem no_collision (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hw : RepresentativeWindow M u v)
    (k : ℤ) (hk : 1 - M 1 0 ≤ k) (U V : ℕ) :
    inverseOffset M v ≠ (k : ℝ) * length M -
      epsilon M * (U : ℝ) - (V : ℝ) := by
  intro hc
  have hid := collision_identity M hM v k U V hc
  have hid' : (((U : ℤ) + (V : ℤ) : ℤ) : ℝ) + epsilon M *
      ((sIndex M v - k * specialValueOrder M -
        (specialValueOrder M + 1) * (U : ℤ) - (V : ℤ) : ℤ) : ℝ) = 0 := by
    simpa only [Int.cast_add, Int.cast_natCast] using hid
  obtain ⟨hUV, hS⟩ := irrational_linear _ (epsilon_irrational M hM) _ _ hid'
  have hU : U = 0 := by omega
  have hV : V = 0 := by omega
  simp only [hU, hV, Nat.cast_zero, mul_zero, sub_zero] at hS
  have hN := specialValueOrder_pos M hM
  have hbound := mul_le_mul_of_nonneg_right hk hN.le
  have hwin := hw.2.2.2
  nlinarith

/-- Only finitely many nonnegative labels lie below any finite height. -/
theorem grid_sublevel_finite (e : ℝ) (he : 0 < e) (b : ℝ) :
    {q : ℕ × ℕ | e * (q.1 : ℝ) + (q.2 : ℝ) ≤ b}.Finite := by
  obtain ⟨A, hA⟩ := exists_nat_gt (b / e)
  obtain ⟨B, hB⟩ := exists_nat_gt b
  apply ((finite_le_nat A).prod (finite_le_nat B)).subset
  intro q hq
  change e * (q.1 : ℝ) + (q.2 : ℝ) ≤ b at hq
  have hq1 : (q.1 : ℝ) < (A : ℝ) := by
    apply lt_of_le_of_lt _ hA
    apply (le_div_iff₀ he).2
    nlinarith [Nat.cast_nonneg (α := ℝ) q.2]
  have hq2 : (q.2 : ℝ) < (B : ℝ) := by
    have hmul := mul_nonneg he.le (Nat.cast_nonneg (α := ℝ) q.1)
    linarith
  exact ⟨by exact_mod_cast hq1.le, by exact_mod_cast hq2.le⟩

/-- Absorb the terminal family into the last of the ordinary translates. -/
theorem terminal_union_eq (n : ℕ) (hn : 0 < n) (S T : Set ℝ) (L : ℝ)
    (hT : (fun x => x + (n : ℝ) * L) '' T ⊆
      (fun x => x + ((n : ℝ) - 1) * L) '' S) :
    (⋃ j : Fin n, (fun x => x + (j : ℝ) * L) '' S) ∪
        (fun x => x + (n : ℝ) * L) '' T =
      ⋃ j : Fin n, (fun x => x + (j : ℝ) * L) '' S := by
  apply union_eq_left.2
  intro x hx
  refine mem_iUnion.2 ⟨⟨n - 1, by omega⟩, ?_⟩
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  simpa only [hcast] using hT hx

theorem terminal_union_eq_int (c : ℤ) (hc : 0 < c) (S T : Set ℝ) (L : ℝ)
    (hT : (fun x => x + (c : ℝ) * L) '' T ⊆
      (fun x => x + ((c : ℝ) - 1) * L) '' S) :
    (⋃ j : Fin c.toNat, (fun x => x + (j : ℝ) * L) '' S) ∪
        (fun x => x + (c : ℝ) * L) '' T =
      ⋃ j : Fin c.toNat, (fun x => x + (j : ℝ) * L) '' S := by
  have hcast : (c.toNat : ℝ) = (c : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hc.le
  simpa only [hcast] using terminal_union_eq c.toNat (by omega) S T L
    (by simpa only [hcast] using hT)

theorem right_grid_locally_finite (e : ℝ) (he : 0 < e) (t lo hi : ℝ) :
    ({x : ℝ | ∃ K J : ℕ, x = e * (K : ℝ) + (J : ℝ) + t} ∩ Icc lo hi).Finite := by
  apply ((grid_sublevel_finite e he (hi - t)).image
    (fun q : ℕ × ℕ => e * (q.1 : ℝ) + (q.2 : ℝ) + t)).subset
  rintro x ⟨⟨K, J, rfl⟩, hlo, hhi⟩
  exact ⟨(K, J), by change e * (K : ℝ) + (J : ℝ) ≤ hi - t; linarith, rfl⟩

theorem left_grid_locally_finite (e : ℝ) (he : 0 < e) (t lo hi : ℝ) :
    ({x : ℝ | ∃ K J : ℕ, x = t - e * (K : ℝ) - (J : ℝ)} ∩ Icc lo hi).Finite := by
  apply ((grid_sublevel_finite e he (t - lo)).image
    (fun q : ℕ × ℕ => t - e * (q.1 : ℝ) - (q.2 : ℝ))).subset
  rintro x ⟨⟨K, J, rfl⟩, hlo, hhi⟩
  exact ⟨(K, J), by change e * (K : ℝ) + (J : ℝ) ≤ t - lo; linarith, rfl⟩

theorem fin_int_modEq_eq {c : ℤ} (hc : 0 < c)
    (i j : Fin c.toNat) (h : Int.ModEq c (i : ℤ) (j : ℤ)) : i = j := by
  have hi : (i : ℤ) < c := by
    have h := i.isLt
    omega
  have hj : (j : ℤ) < c := by
    have h := j.isLt
    omega
  have heq : (i : ℤ) = (j : ℤ) := by
    simpa only [Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg i.val) hi,
      Int.emod_eq_of_lt (Int.natCast_nonneg j.val) hj] using h
  exact Fin.ext (Int.ofNat.inj heq)

theorem existsUnique_linear_residue (M : SL(2, ℤ))
    (hc : 0 < M 1 0) (z : ℤ) :
    ∃! m : Fin (M 1 0).toNat, Int.ModEq (M 1 0) z (M 1 1 * (m : ℤ)) := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.2
  have had : Int.ModEq (M 1 0) (M 1 1 * M 0 0) 1 := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-M 0 1, ?_⟩
    nlinarith [hdet]
  obtain ⟨r, hr, hmod⟩ := Int.existsUnique_equiv_nat (M 0 0 * z) hc
  let m : Fin (M 1 0).toNat := ⟨r, by omega⟩
  have hm : Int.ModEq (M 1 0) z (M 1 1 * (m : ℤ)) := by
    have h1 : Int.ModEq (M 1 0) (M 1 1 * (m : ℤ))
        (M 1 1 * (M 0 0 * z)) := hmod.mul_left (M 1 1)
    have h2 : Int.ModEq (M 1 0) (M 1 1 * (M 0 0 * z)) z := by
      simpa only [mul_assoc, one_mul] using had.mul_right z
    exact (h1.trans h2).symm
  refine ⟨m, hm, ?_⟩
  intro n hn
  have hcop : IsCoprime (M 1 0) (M 1 1) :=
    Matrix.SpecialLinearGroup.isCoprime_row M 1
  have hdvd : M 1 0 ∣ M 1 1 * ((m : ℤ) - (n : ℤ)) := by
    simpa only [mul_sub] using (hn.symm.trans hm).dvd
  have heqmod : Int.ModEq (M 1 0) (n : ℤ) (m : ℤ) :=
    Int.modEq_of_dvd (hcop.dvd_of_dvd_mul_left hdvd)
  exact fin_int_modEq_eq hc n m heqmod

lemma repelling_etaDenom (M : SL(2, ℤ)) :
    etaDenom M (repellingTau M : ℂ) = (epsilon M : ℂ) := by
  simp [etaDenom, G2.epsilon, g1T]

lemma c_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (M 1 0 : ℝ) ≠ 0 := by
  exact_mod_cast ne_of_gt hM.1

lemma right_label_iff (M : SL(2, ℤ)) (m : ℤ) (K J : ℕ) :
    Int.ModEq (M 1 0) (M 1 1 * (K : ℤ) + (J : ℤ)) (M 1 1 * m) ↔
      (K, J) ∈ modularPhiPoleLabels M (m + 1) 0 := by
  simp [modularPhiPoleLabels, add_comm]

lemma left_label_iff (M : SL(2, ℤ)) (v : ℤ × ℤ) (m : ℤ) (K J : ℕ) :
    Int.ModEq (M 1 0) (M 1 1 * (K : ℤ) + (J : ℤ))
      (-M 1 1 * (m + v.1)) ↔
      (K, J) ∈ modularPhiZeroLabels M (m + (v.1 - M 0 0)) 0 := by
  have hi : -1 - M 1 1 * (m + (v.1 - M 0 0)) =
      -M 1 1 * (m + v.1) + M 0 1 * M 1 0 := by
    linear_combination det_coe_int M
  simp only [modularPhiZeroLabels, Set.mem_ofPred_eq, zero_sub, hi]
  rw [Int.modEq_add_mul_modulus_iff]
  simp [add_comm]

lemma right_point_affine_iff (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m : ℤ) (x : ℝ) (K J : ℕ) :
    (((x - epsilon M * (m : ℝ)) / (M 1 0 : ℝ) : ℝ) : ℂ) =
      modularPhiPolePoint M (m + 1) 0 (repellingTau M : ℂ) K J ↔
        x = epsilon M * (K : ℝ) + (J : ℝ) := by
  have hp : modularPhiPolePoint M (m + 1) 0 (repellingTau M : ℂ) K J =
      (((-(m : ℝ) * epsilon M + (K : ℝ) * epsilon M + (J : ℝ)) /
        (M 1 0 : ℝ) : ℝ) : ℂ) := by
    simp [modularPhiPolePoint, repelling_etaDenom]
  rw [hp, Complex.ofReal_inj, div_left_inj' (c_ne_zero M hM)]
  constructor <;> intro h <;> linarith

lemma translatedY_mul_c (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) :
    (M 1 0 : ℝ) * translatedY M v = inverseOffset M v +
      epsilon M * ((M 0 0 : ℝ) - (v.1 : ℝ)) - 1 := by
  have harg := (coefficient_formulas M hM v v).2
  have hfix := fixedPoint_translate M hM
  unfold translatedY
  linear_combination harg + hfix

lemma left_point_affine_iff (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m : ℤ) (x : ℝ) (K J : ℕ) :
    (((x - epsilon M * (m : ℝ)) / (M 1 0 : ℝ) : ℝ) : ℂ) =
      modularPhiZeroPoint M (m + (v.1 - M 0 0)) 0
        (repellingTau M : ℂ) K J - (translatedY M v : ℂ) ↔
        x = -inverseOffset M v - epsilon M * (K : ℝ) - (J : ℝ) := by
  have hp : modularPhiZeroPoint M (m + (v.1 - M 0 0)) 0
      (repellingTau M : ℂ) K J =
      (((-1 - ((m : ℝ) + ((v.1 : ℝ) - (M 0 0 : ℝ))) * epsilon M -
        (K : ℝ) * epsilon M - (J : ℝ)) / (M 1 0 : ℝ) : ℝ) : ℂ) := by
    simp [modularPhiZeroPoint, repelling_etaDenom]
  rw [hp, ← Complex.ofReal_sub, Complex.ofReal_inj]
  rw [eq_sub_iff_add_eq]
  have hr : (x - epsilon M * (m : ℝ)) / (M 1 0 : ℝ) + translatedY M v =
      ((x - epsilon M * (m : ℝ)) + (M 1 0 : ℝ) * translatedY M v) /
        (M 1 0 : ℝ) := by
    field_simp [c_ne_zero M hM]
  rw [hr, div_left_inj' (c_ne_zero M hM), translatedY_mul_c M hM v]
  constructor <;> intro h <;> linarith

end SICLean.L4.G2PoleSeparationAux
