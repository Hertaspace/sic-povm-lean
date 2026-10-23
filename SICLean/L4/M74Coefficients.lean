import SICLean.L4.M74Gaussian

set_option autoImplicit false

/-!
# The coefficient field and the actual FiniteSystem

The field is exactly the distributionCoefficientField, now
specialized to the actual Gaussian for the finite arithmetic family.
Its generators are sqrtN, Gaussian and etaKappa; none is an E coordinate.
The FiniteSystem below supplies coefficient laws and the existing target
and projection. Constructing this data asserts no Q3 or IsSolution.
[RW26, p. 3, p. 23, (3)--(4), Theorem 11].
The Q4 scalar is the squared eta multiplier. [RW26, p. 23, Theorem 11].
-/

noncomputable section

namespace SICLean.L3.M74

universe u

variable {K : Type u} [Field K] [NumberField K] {P : PeriodData K}

/-- The coefficient field, with the Gaussian fixed independently of the analytic values E. -/
def coefficientField (F : FinitePseudolatticeFamily P) : IntermediateField ℚ ℂ :=
  L4.distributionCoefficientField P.N (familyGaussian F)
    (pseudolatticeFamilyBasis F) (pseudolatticeFamilyTarget F)

/--
The coefficient field with its generators listed explicitly. No algebraicity of any unknown E is
needed to form this field; [RW26, p. 3, (3)--(4)].
-/
theorem coefficientField_eq_adjoin (F : FinitePseudolatticeFamily P) :
    coefficientField F = IntermediateField.adjoin ℚ
      ({(Real.sqrt (P.N : ℝ) : ℂ)} ∪
        Set.range (fun c : Coordinate (Fin F.size) (PseudolatticeFamilyGroup F) =>
          familyGaussian F c.1 c.2) ∪
        Set.range (fun c : (Σ i, OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) =>
          L4.distributionFamilyKappa (pseudolatticeFamilyBasis F)
            (pseudolatticeFamilyTarget F) c.1 c.2)) := by
  rfl

/-- The positive real sqrtN, lifted by the membership theorem. -/
def sqrtNCoefficient (F : FinitePseudolatticeFamily P) : coefficientField F :=
  ⟨(Real.sqrt (P.N : ℝ) : ℂ), L4.distributionCoefficient_sqrt_mem P.N
    (familyGaussian F) (pseudolatticeFamilyBasis F) (pseudolatticeFamilyTarget F)⟩

/--
The actual complex scalar is pinned, including the positive sign; [RW26, p. 3, (4)].
-/
theorem sqrtNCoefficient_map (F : FinitePseudolatticeFamily P) :
    algebraMap (coefficientField F) ℂ (sqrtNCoefficient F) =
      (Real.sqrt (P.N : ℝ) : ℂ) := by
  rfl

/--
The FiniteSystem.sqrtN_sq field, in the coefficient field itself; [RW26, p. 3, (4)].
-/
theorem sqrtNCoefficient_sq (F : FinitePseudolatticeFamily P) :
    sqrtNCoefficient F ^ 2 = (P.N : coefficientField F) := by
  apply Subtype.ext
  change (Real.sqrt (P.N : ℝ) : ℂ) ^ 2 = (P.N : ℂ)
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg P.N : (0 : ℝ) ≤ (P.N : ℝ))

/--
Excludes choosing the other square root while retaining sqrtN_sq; [RW26, p. 3, (4)] (positive-root
normalization).
-/
theorem sqrtNCoefficient_re_pos (F : FinitePseudolatticeFamily P) :
    0 < (algebraMap (coefficientField F) ℂ (sqrtNCoefficient F)).re := by
  rw [sqrtNCoefficient_map, Complex.ofReal_re]
  exact Real.sqrt_pos.2 (Nat.cast_pos.2 P.N_pos)

/-- Actual Gaussian coefficient, using only the membership map. -/
def gaussianCoefficient (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (x : PseudolatticeFamilyGroup F i) : coefficientField F :=
  ⟨familyGaussian F i x, L4.distributionCoefficient_gaussian_mem P.N
    (familyGaussian F) (pseudolatticeFamilyBasis F) (pseudolatticeFamilyTarget F) i x⟩

/--
Identifies precisely the Gaussian used by the actual reflection law; [RW26, p. 3, (3)].
-/
theorem gaussianCoefficient_map (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (x : PseudolatticeFamilyGroup F i) :
    algebraMap (coefficientField F) ℂ (gaussianCoefficient F i x) = familyGaussian F i x := by
  rfl

/--
FiniteSystem.gaussian_zero, after the injective coefficient lift; [RW26, p. 3, (3)].
-/
theorem gaussianCoefficient_zero (F : FinitePseudolatticeFamily P) :
    ∀ i, gaussianCoefficient F i 0 = 1 := by
  intro i
  apply Subtype.ext
  exact familyGaussian_zero F i

/--
FiniteSystem.gaussian_neg, for every actual quotient label; [RW26, p. 3, (3)].
-/
theorem gaussianCoefficient_neg (F : FinitePseudolatticeFamily P) :
    ∀ i (x : PseudolatticeFamilyGroup F i),
      gaussianCoefficient F i (-x) = gaussianCoefficient F i x := by
  intro i x
  apply Subtype.ext
  exact familyGaussian_neg F i x

/--
FiniteSystem.gaussian_order, with the same fixed N at every i; [RW26, p. 3, (3)].
-/
theorem gaussianCoefficient_order (F : FinitePseudolatticeFamily P) :
    ∀ i (x : PseudolatticeFamilyGroup F i), gaussianCoefficient F i x ^ (2 * P.N) = 1 := by
  intro i x
  apply Subtype.ext
  change familyGaussian F i x ^ (2 * P.N) = 1
  exact familyGaussian_order F i x

/-- The proof uses the existing lift of the actual eta multiplier ratio. -/
def kappaCoefficient (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) : coefficientField F :=
  L4.distributionKappaCoefficient P.N (familyGaussian F)
    (pseudolatticeFamilyBasis F) (pseudolatticeFamilyTarget F) i h

/--
The literal etaKappa, with its square in the numerator. [RW26, p. 3].
-/
theorem kappaCoefficient_map (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    algebraMap (coefficientField F) ℂ (kappaCoefficient F i h) =
      L4.distributionFamilyKappa (pseudolatticeFamilyBasis F)
        (pseudolatticeFamilyTarget F) i h := by
  rfl

/--
Direct reuse of the finite-order lift; no E premise. [RW26, p. 3].
-/
theorem kappaCoefficient_order (F : FinitePseudolatticeFamily P) :
    ∀ i h, kappaCoefficient F i h ^ 24 = 1 := by
  intro i h
  exact L4.distributionKappa_lift_pow_twentyFour
    (pseudolatticeFamilyBasis F i)
    (pseudolatticeFamilyBasis F (pseudolatticeFamilyTarget F i h))
    (familyBasis_valid F i)
    (familyBasis_valid F (pseudolatticeFamilyTarget F i h))
    (kappaCoefficient F i h) (kappaCoefficient_map F i h)

/--
Specialize distributionCoefficientField_isAlgebraic using the
now uniform actual Gaussian order. This is coefficient algebraicity only. [RW26, p. 3].
-/
theorem coefficientField_isAlgebraic (F : FinitePseudolatticeFamily P) :
    Algebra.IsAlgebraic ℚ (coefficientField F) := by
  exact L4.distributionCoefficientField_isAlgebraic P.N P.N_pos
    (familyGaussian F) (familyGaussian_order F)
    (pseudolatticeFamilyBasis F) (familyBasis_valid F) (pseudolatticeFamilyTarget F)

/--
Full coefficient/geometric data. All proof fields reference
separate statements above; no Q1--Q4 property is hidden in this definition.
-/
def system (F : FinitePseudolatticeFamily P) :
    FiniteSystem (Fin F.size) (PseudolatticeFamilyGroup F) (coefficientField F) where
  N := P.N
  N_pos := P.N_pos
  sqrtN := sqrtNCoefficient F
  sqrtN_sq := sqrtNCoefficient_sq F
  gaussian := gaussianCoefficient F
  gaussian_zero := gaussianCoefficient_zero F
  gaussian_neg := gaussianCoefficient_neg F
  gaussian_order := gaussianCoefficient_order F
  target := pseudolatticeFamilyTarget F
  project := pseudolatticeFamilyProject F
  multiplier := kappaCoefficient F
  multiplier_order := kappaCoefficient_order F

/--
Pins FiniteSystem.N to PeriodData.N. [RW26, p. 3, (3)].
-/
theorem system_N (F : FinitePseudolatticeFamily P) : (system F).N = P.N := by
  rfl

/--
Scalar form used verbatim in IsSolution.q1 and IsSolution.q3. [RW26, p. 3, (4)].
-/
theorem system_sqrtN_map (F : FinitePseudolatticeFamily P) :
    algebraMap (coefficientField F) ℂ (system F).sqrtN =
      (Real.sqrt (P.N : ℝ) : ℂ) := by
  exact sqrtNCoefficient_map F

/--
Scalar form used verbatim in IsSolution.q2; [RW26, p. 3, (3), (5)].
-/
theorem system_gaussian_map (F : FinitePseudolatticeFamily P)
    (i : Fin F.size) (x : PseudolatticeFamilyGroup F i) :
    algebraMap (coefficientField F) ℂ ((system F).gaussian i x) = familyGaussian F i x := by
  exact gaussianCoefficient_map F i x

/--
Scalar form used verbatim in IsSolution.q4, with every order-two label; [RW26, p. 23].
-/
theorem system_multiplier_map (F : FinitePseudolatticeFamily P) (i : Fin F.size)
    (h : OrderTwo (Fin F.size) (PseudolatticeFamilyGroup F) i) :
    algebraMap (coefficientField F) ℂ ((system F).multiplier i h) =
      L4.distributionFamilyKappa (pseudolatticeFamilyBasis F)
        (pseudolatticeFamilyTarget F) i h := by
  exact kappaCoefficient_map F i h

#print L4.distributionCoefficientSet
#print coefficientField
#print system
#check @system_gaussian_map
#check @coefficientField_isAlgebraic

end SICLean.L3.M74
