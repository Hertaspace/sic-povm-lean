import SICLean.L4.G1RealInterface
import SICLean.L4.SpecialValueGeometry
import SICLean.L4.G2RepellingGeometryAux

set_option autoImplicit false

/-!
Explicit repelling geometry. [RW26, p. 12]. This does not redefine the attracting `SpecialValue*`
functions. The inverse-reflection bridge back to them is separate. The proofs use the explicit
smaller root and det M = 1.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2

def repellingTau (M : SL(2, ℤ)) : ℝ :=
  ((M 0 0 : ℝ) - (M 1 1 : ℝ) -
    Real.sqrt (((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4)) / (2 * (M 1 0 : ℝ))

def epsilon (M : SL(2, ℤ)) : ℝ := g1T M (repellingTau M)

/-- G2's positive length L, distinct from G1's negative lower coefficient. -/
def length (M : SL(2, ℤ)) : ℝ := 1 - epsilon M

def scale (M : SL(2, ℤ)) : ℝ := epsilon M / length M

def argument (M : SL(2, ℤ)) (x : ℤ × ℤ) : ℝ :=
  ((x.1 : ℝ) * repellingTau M + (x.2 : ℝ)) / ((epsilon M)⁻¹ - 1)

theorem epsilon_formula (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    epsilon M = ((specialValueOrder M : ℝ) + 2 -
      Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2 := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  have hD : (specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ) =
      ((M 0 0 : ℝ) + (M 1 1 : ℝ)) ^ 2 - 4 := by
    simp only [specialValueOrder, Int.cast_sub, Int.cast_add, Int.cast_ofNat]
    ring
  rw [hD]
  simp only [epsilon, g1T, repellingTau, specialValueOrder, Int.cast_sub,
    Int.cast_add, Int.cast_ofNat]
  field_simp
  ring

theorem repellingTau_fixedPoint (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    etaMobius M (repellingTau M : ℂ) = (repellingTau M : ℂ) := by
  have hN := G2RepellingGeometryAux.order_pos M hM
  have hNr : 0 < (specialValueOrder M : ℝ) := by exact_mod_cast hN
  obtain ⟨hepos, _, hechar⟩ :=
    G2RepellingGeometryAux.small_root_properties (specialValueOrder M : ℝ) hNr
  rw [← epsilon_formula M hM] at hepos hechar
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  have hd : (M 0 0 : ℝ) * (M 1 1 : ℝ) -
      (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    exact_mod_cast det_coe_int M
  have hp : (M 1 0 : ℝ) *
      ((M 0 0 : ℝ) * repellingTau M + (M 0 1 : ℝ) -
        repellingTau M * ((M 1 0 : ℝ) * repellingTau M + (M 1 1 : ℝ))) = 0 := by
    simp only [epsilon, g1T, specialValueOrder, Int.cast_sub, Int.cast_add,
      Int.cast_ofNat] at hechar
    nlinarith [hechar, hd]
  have hp' := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hc)
  have hden : etaDenom M (repellingTau M : ℂ) ≠ 0 := by
    change ((M 1 0 : ℂ) * (repellingTau M : ℂ) + (M 1 1 : ℂ)) ≠ 0
    exact_mod_cast ne_of_gt hepos
  apply (div_eq_iff hden).2
  unfold etaDenom
  exact_mod_cast hp'

theorem epsilon_pos (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < epsilon M := by
  have hN : 0 < (specialValueOrder M : ℝ) := by
    exact_mod_cast G2RepellingGeometryAux.order_pos M hM
  rw [epsilon_formula M hM]
  exact (G2RepellingGeometryAux.small_root_properties _ hN).1

theorem epsilon_lt_one (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    epsilon M < 1 := by
  have hN : 0 < (specialValueOrder M : ℝ) := by
    exact_mod_cast G2RepellingGeometryAux.order_pos M hM
  rw [epsilon_formula M hM]
  exact (G2RepellingGeometryAux.small_root_properties _ hN).2.1

theorem epsilon_characteristic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    epsilon M ^ 2 - ((specialValueOrder M : ℝ) + 2) * epsilon M + 1 = 0 := by
  have hN : 0 < (specialValueOrder M : ℝ) := by
    exact_mod_cast G2RepellingGeometryAux.order_pos M hM
  rw [epsilon_formula M hM]
  exact (G2RepellingGeometryAux.small_root_properties _ hN).2.2

theorem epsilon_irrational (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    Irrational (epsilon M) := by
  have hN := G2RepellingGeometryAux.order_pos M hM
  rw [epsilon_formula M hM]
  exact G2RepellingGeometryAux.small_root_irrational _ hN

theorem length_pos (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < length M := by
  exact sub_pos.mpr (epsilon_lt_one M hM)

theorem length_sq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    length M ^ 2 = (specialValueOrder M : ℝ) * epsilon M := by
  unfold length
  nlinarith [epsilon_characteristic M hM]

theorem scale_identities (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    0 < scale M ∧ scale M = length M / (specialValueOrder M : ℝ) := by
  have hN : 0 < (specialValueOrder M : ℝ) := by
    exact_mod_cast G2RepellingGeometryAux.order_pos M hM
  refine ⟨div_pos (epsilon_pos M hM) (length_pos M hM), ?_⟩
  apply (div_eq_div_iff (ne_of_gt (length_pos M hM)) (ne_of_gt hN)).mpr
  nlinarith [length_sq M hM]

theorem normalized_length (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    length M / Real.sqrt (epsilon M) = Real.sqrt (specialValueOrder M : ℝ) := by
  have hN : 0 < (specialValueOrder M : ℝ) := by
    exact_mod_cast G2RepellingGeometryAux.order_pos M hM
  apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (epsilon_pos M hM)))).mpr
  rw [← Real.sqrt_mul hN.le, ← length_sq M hM, Real.sqrt_sq (length_pos M hM).le]

theorem repellingTau_irrational (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    Irrational (repellingTau M) := by
  have h := (epsilon_irrational M hM).of_add_intCast (M 1 1)
  exact h.of_intCast_mul (M 1 0)

theorem fixedPoint_translate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (M 1 0 : ℝ) * ((M 0 0 : ℝ) * repellingTau M + (M 0 1 : ℝ)) =
      (M 0 0 : ℝ) * epsilon M - 1 := by
  clear hM
  have hd : (M 0 0 : ℝ) * (M 1 1 : ℝ) -
      (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    exact_mod_cast det_coe_int M
  unfold epsilon g1T
  nlinarith [hd]

/-- The same argument formula, specialized to the other fixed point. -/
theorem argument_eq_modular (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) :
    (argument M x : ℂ) = modularPhiSpecialArgument M ![x.1, x.2]
      (repellingTau M : ℂ) := by
  clear hM
  simp [argument, modularPhiSpecialArgument, epsilon, g1T, etaDenom]

#check @modularPhi_fixedPoint_lattice_value
#check @modularPhiSpecialArgument
#print repellingTau
#check epsilon_irrational

end SICLean.L4.G2
