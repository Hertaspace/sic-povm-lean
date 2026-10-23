import SICLean.L4.G2RepellingGeometry

set_option autoImplicit false

/-!
Deterministic integer representatives and strict windows. The quotient stays ℤ²/Λ; S mod N is not a
coordinate isomorphism and is not a zero-class test.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2

def sIndex (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℤ :=
  (1 - M 1 1) * x.1 + M 1 0 * x.2

def latticeStep (M : SL(2, ℤ)) : ℤ × ℤ := (M 0 0 - 1, M 0 1)

def upperRepresentative (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℤ × ℤ :=
  x + (-((sIndex M x - 1) / specialValueOrder M)) • latticeStep M

def deepRepresentative (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℤ × ℤ :=
  x + (-(sIndex M x / specialValueOrder M) - M 1 0) • latticeStep M

/-- Only integer inequalities. In particular no analytic claim is a field. -/
def RepresentativeWindow (M : SL(2, ℤ)) (u v : ℤ × ℤ) : Prop :=
  0 < sIndex M u ∧ sIndex M u ≤ specialValueOrder M ∧
    -(M 1 0 * specialValueOrder M) ≤ sIndex M v ∧
    sIndex M v < -((M 1 0 - 1) * specialValueOrder M)

def upperCoefficient (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℝ :=
  epsilon M + scale M * (sIndex M u : ℝ)

def inverseOffset (M : SL(2, ℤ)) (v : ℤ × ℤ) : ℝ :=
  scale M * (sIndex M v : ℝ)

def translatedY (M : SL(2, ℤ)) (v : ℤ × ℤ) : ℝ :=
  argument M v + (M 0 0 : ℝ) * repellingTau M + (M 0 1 : ℝ)

theorem sIndex_latticeStep (M : SL(2, ℤ)) :
    sIndex M (latticeStep M) = specialValueOrder M := by
  dsimp [sIndex, latticeStep, specialValueOrder]
  linear_combination -det_coe_int M

theorem latticeStep_mem (M : SL(2, ℤ)) :
    latticeStep M ∈ specialValueLattice M := by
  change ∃ x, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) x = latticeStep M
  exact ⟨(1, 0), by simp [L2r.rowAction, latticeStep, Matrix.sub_apply]⟩

theorem sIndex_add_zsmul (M : SL(2, ℤ)) (x : ℤ × ℤ) (k : ℤ) :
    sIndex M (x + k • latticeStep M) = sIndex M x + k * specialValueOrder M := by
  rw [← sIndex_latticeStep M]
  simp [sIndex, latticeStep]
  ring

theorem upperRepresentative_class (M : SL(2, ℤ)) (x : ℤ × ℤ) :
    specialValueMk M (upperRepresentative M x) = specialValueMk M x := by
  have hstep : specialValueMk M (latticeStep M) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (latticeStep_mem M)
  rw [upperRepresentative, map_add, map_zsmul, hstep, smul_zero, add_zero]

theorem deepRepresentative_class (M : SL(2, ℤ)) (x : ℤ × ℤ) :
    specialValueMk M (deepRepresentative M x) = specialValueMk M x := by
  have hstep : specialValueMk M (latticeStep M) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (latticeStep_mem M)
  rw [deepRepresentative, map_add, map_zsmul, hstep, smul_zero, add_zero]

theorem upperRepresentative_window (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    0 < sIndex M (upperRepresentative M x) ∧
      sIndex M (upperRepresentative M x) ≤ specialValueOrder M := by
  rw [upperRepresentative, sIndex_add_zsmul]
  have hN := specialValueOrder_pos M hM
  have hnonneg := Int.emod_nonneg (sIndex M x - 1) (ne_of_gt hN)
  have hlt := Int.emod_lt_of_pos (sIndex M x - 1) hN
  have hdiv := Int.emod_add_mul_ediv (sIndex M x - 1) (specialValueOrder M)
  constructor <;> nlinarith

theorem deepRepresentative_window (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    -(M 1 0 * specialValueOrder M) ≤ sIndex M (deepRepresentative M x) ∧
      sIndex M (deepRepresentative M x) < -((M 1 0 - 1) * specialValueOrder M) := by
  rw [deepRepresentative, sIndex_add_zsmul]
  have hN := specialValueOrder_pos M hM
  have hnonneg := Int.emod_nonneg (sIndex M x) (ne_of_gt hN)
  have hlt := Int.emod_lt_of_pos (sIndex M x) hN
  have hdiv := Int.emod_add_mul_ediv (sIndex M x) (specialValueOrder M)
  constructor <;> nlinarith

theorem representativeWindow_construct (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    RepresentativeWindow M (upperRepresentative M u) (deepRepresentative M v) := by
  exact ⟨(upperRepresentative_window M hM u).1,
    (upperRepresentative_window M hM u).2,
    (deepRepresentative_window M hM v).1,
    (deepRepresentative_window M hM v).2⟩

theorem argument_common_coordinate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    (M 1 0 : ℝ) * argument M x + epsilon M * (x.1 : ℝ) =
      scale M * (sIndex M x : ℝ) := by
  have he : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have hL : 1 - epsilon M ≠ 0 := ne_of_gt (sub_pos.mpr (epsilon_lt_one M hM))
  have hT : (M 1 0 : ℝ) * repellingTau M + (M 1 1 : ℝ) = epsilon M := rfl
  simp only [argument, scale, length, sIndex, Int.cast_add, Int.cast_mul,
    Int.cast_sub, Int.cast_one]
  field_simp [he, hL]
  linear_combination (x.1 : ℝ) * hT

theorem coefficient_formulas (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    g1S M (repellingTau M) (argument M u) 0 (u.1 + 1) = upperCoefficient M u ∧
    (M 1 0 : ℝ) * argument M v + epsilon M * (v.1 : ℝ) = inverseOffset M v := by
  have hx := argument_common_coordinate M hM u
  constructor
  · simp only [g1S, Int.cast_zero, Int.cast_add, Int.cast_one, add_zero,
      upperCoefficient]
    change (M 1 0 : ℝ) * argument M u + ((u.1 : ℝ) + 1) * epsilon M = _
    linarith
  · exact argument_common_coordinate M hM v

theorem strict_window_bounds (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    epsilon M < upperCoefficient M u ∧ upperCoefficient M u ≤ 1 ∧
      inverseOffset M v < 0 ∧ upperCoefficient M u + inverseOffset M v < 1 := by
  rcases hwin with ⟨hu0, huN, _, hvN⟩
  have hscale := (scale_identities M hM).1
  have hscaleN : scale M * (specialValueOrder M : ℝ) = length M := by
    rw [(scale_identities M hM).2]
    exact div_mul_cancel₀ _ (by exact_mod_cast (ne_of_gt (specialValueOrder_pos M hM)))
  have hu0' : 0 < (sIndex M u : ℝ) := by exact_mod_cast hu0
  have huN' : (sIndex M u : ℝ) ≤ (specialValueOrder M : ℝ) := by exact_mod_cast huN
  have hv0 : sIndex M v < 0 := by
    have hc : 0 ≤ M 1 0 - 1 := by have := hM.1; omega
    exact lt_of_lt_of_le hvN (neg_nonpos.mpr (mul_nonneg hc (specialValueOrder_pos M hM).le))
  have hv0' : (sIndex M v : ℝ) < 0 := by exact_mod_cast hv0
  have hs0 : epsilon M < upperCoefficient M u := by
    dsimp [upperCoefficient]
    exact lt_add_of_pos_right _ (mul_pos hscale hu0')
  have hs1 : upperCoefficient M u ≤ 1 := by
    dsimp [upperCoefficient]
    have := mul_le_mul_of_nonneg_left huN' hscale.le
    dsimp [length] at hscaleN
    linarith
  have hY : inverseOffset M v < 0 := mul_neg_of_pos_of_neg hscale hv0'
  exact ⟨hs0, hs1, hY, by linarith⟩

/-- The final G1 ratio uses p'=v₁-a and y'=y+aτ+b; raw coefficients are different. This statement
does not assume G1 or any convergence. -/
theorem raw_and_final_windows (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v) :
    0 < (upperCoefficient M u - epsilon M) / epsilon M ∧
    (upperCoefficient M u + inverseOffset M v - 1) / epsilon M < 0 ∧
    0 < g1S M (repellingTau M) (argument M u) 0 (u.1 + 1) ∧
    g1L M (repellingTau M) (argument M u) (translatedY M v)
      0 (u.1 + 1) (v.1 - M 0 0) < 0 := by
  rcases strict_window_bounds M hM u v hwin with ⟨hs, _, _, hsum⟩
  have he := epsilon_pos M hM
  have hS := (coefficient_formulas M hM u v).1
  have hY := (coefficient_formulas M hM u v).2
  refine ⟨div_pos (sub_pos.mpr hs) he, div_neg_of_neg_of_pos (by linarith) he,
    by linarith, ?_⟩
  have htranslate := fixedPoint_translate M hM
  have hL : g1L M (repellingTau M) (argument M u) (translatedY M v)
      0 (u.1 + 1) (v.1 - M 0 0) =
      upperCoefficient M u + inverseOffset M v - 1 - epsilon M := by
    simp only [g1L, hS, translatedY, Int.cast_sub]
    change upperCoefficient M u + (M 1 0 : ℝ) *
      (argument M v + (M 0 0 : ℝ) * repellingTau M + (M 0 1 : ℝ)) +
      ((v.1 : ℝ) - (M 0 0 : ℝ) - 1) * epsilon M = _
    nlinarith [htranslate, hY]
  rw [hL]
  linarith

/-- Full lattice exclusion, not merely S_v mod N≠0. -/
theorem phase_ne_one (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (hv : specialValueMk M v ≠ 0) :
    e ((argument M v : ℂ) / (epsilon M : ℂ)) ≠ 1 := by
  intro heq
  obtain ⟨k, hk⟩ := e_eq_one_iff_int heq
  have hkR : argument M v / epsilon M = (k : ℝ) := by exact_mod_cast hk
  have he0 : epsilon M ≠ 0 := ne_of_gt (epsilon_pos M hM)
  have hL0 : 1 - epsilon M ≠ 0 := ne_of_gt (sub_pos.mpr (epsilon_lt_one M hM))
  have harg : argument M v / epsilon M =
      ((v.1 : ℝ) * repellingTau M + (v.2 : ℝ)) / (1 - epsilon M) := by
    unfold argument
    field_simp [he0, hL0]
  rw [harg] at hkR
  have hrel := (div_eq_iff hL0).mp hkR
  have hT : (M 1 0 : ℝ) * repellingTau M + (M 1 1 : ℝ) = epsilon M := rfl
  have hlinear : ((v.1 + k * M 1 0 : ℤ) : ℝ) * repellingTau M =
      ((-(v.2 + k * (M 1 1 - 1)) : ℤ) : ℝ) := by
    push_cast
    linear_combination hrel + (k : ℝ) * hT
  have hfirst : v.1 + k * M 1 0 = 0 := by
    by_contra hn
    exact ((repellingTau_irrational M hM).intCast_mul hn).ne_int _ hlinear
  have hsecond : v.2 + k * (M 1 1 - 1) = 0 := by
    rw [hfirst, Int.cast_zero, zero_mul] at hlinear
    have hz : -(v.2 + k * (M 1 1 - 1)) = 0 := Int.cast_eq_zero.mp hlinear.symm
    omega
  -- Thus v is -k times the second row of M-I, hence represents the zero class.
  apply hv
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  change ∃ x, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) x = v
  refine ⟨(0, -k), ?_⟩
  ext <;> simp [L2r.rowAction, Matrix.sub_apply] <;> omega

#print upperRepresentative
#print deepRepresentative
#check raw_and_final_windows
#check @specialValueLattice_mem_iff

end SICLean.L4.G2
