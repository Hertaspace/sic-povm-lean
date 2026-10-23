import SICLean.L5.RayArithmeticConjugation
import SICLean.L5.RayArithmeticSignsAux

set_option autoImplicit false

/-!
# Explicit real sign classes, including the trivial cases

The representatives are 1-cm(epsilon-1) and its actual quadratic conjugate. Their signs,
congruences and class laws are conclusions, not hypotheses of a sign-class structure. No
nontriviality of either sign class or their product is assumed. Sources: [RW-rec], and
[RW26, p. 20] identify K, epsilon, I and their embeddings.
-/

noncomputable section
open scoped MatrixGroups NumberField Classical IsMulCommutative
open NumberField

namespace SICLean.L5.RayArithmeticSigns

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM

def generator₁ (m : ℕ) : K :=
  1 - (RayArithmeticModulus.level M hM m : K) * (ActualField.epsilon M hM - 1)

def generator₂ (m : ℕ) : K := RayArithmeticPlaces.conjugation M hM (generator₁ M hM m)

/-- Source: epsilon is integral; [RW-rec]. This proof also uses preservation of integrality by
quadratic conjugation. [RW26, p. 20]. -/
theorem generators_integral (m : ℕ) :
    IsIntegral ℤ (generator₁ M hM m) ∧ IsIntegral ℤ (generator₂ M hM m) := by
  have hε := (ActualField.epsilon_totallyPositive_unit M hM).2.1
  have hg : IsIntegral ℤ (generator₁ M hM m) :=
    isIntegral_one.sub ((isIntegral_natCast (RayArithmeticModulus.level M hM m)).mul
      (hε.sub isIntegral_one))
  exact ⟨hg, hg.map (RayArithmeticPlaces.conjugation M hM)⟩

/-- Source: explicit sign representative bridge for [RW-rec]. N>0 and the norm-one period imply
epsilon>2 at sigma_1; cm>=4. [RW26, p. 20]. -/
theorem generator₁_signs (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    ActualField.sigma₁ M hM (generator₁ M hM m) < 0 ∧
      0 < ActualField.sigma₂ M hM (generator₁ M hM m) := by
  have hn : (4 : ℝ) ≤ RayArithmeticModulus.level M hM m := by
    exact_mod_cast RayArithmeticModulus.four_le_level M hM m hm
  have he := RayArithmeticSignsAux.epsilon_gt_two M hM
  have he1 := ActualField.epsilon_gt_one M hM
  have he0 : 0 < ActualField.sigma₁ M hM (ActualField.epsilon M hM) := by linarith
  have hi : (ActualField.sigma₁ M hM (ActualField.epsilon M hM))⁻¹ < 1 :=
    (inv_lt_one₀ he0).mpr he1
  simp only [generator₁, map_sub, map_one, map_mul, map_natCast,
    ActualField.sigma₂_epsilon]
  constructor
  · nlinarith
  · nlinarith

/-- Source: same explicit bridge, after exchanging the two real embeddings. [RW26, p. 20]. -/
theorem generator₂_signs (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    0 < ActualField.sigma₁ M hM (generator₂ M hM m) ∧
      ActualField.sigma₂ M hM (generator₂ M hM m) < 0 := by
  simpa only [generator₂, RayArithmeticPlaces.sigma₁_conjugation,
    RayArithmeticPlaces.sigma₂_conjugation] using (generator₁_signs M hM m hm).symm

/-- Source: literal finite congruence of the representatives, [RW-rec]. [RW26, p. 20]. -/
theorem generators_globallyCongruent (m : ℕ) :
    RayArithmeticModulus.GloballyCongruent M hM m (generator₁ M hM m) ∧
      RayArithmeticModulus.GloballyCongruent M hM m (generator₂ M hM m) := by
  have hε := (ActualField.epsilon_totallyPositive_unit M hM).2.1
  have hg : RayArithmeticModulus.GloballyCongruent M hM m (generator₁ M hM m) := by
    refine ⟨⟨-(ActualField.epsilon M hM - 1), (hε.sub isIntegral_one).neg⟩, ?_⟩
    change 1 - _ * _ - 1 = _ * (-_)
    ring
  exact ⟨hg, RayArithmeticSignsAux.globallyCongruent_conjugation M hM m _ hg⟩

def generatorUnit₁ (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) : Kˣ :=
  Units.mk0 (generator₁ M hM m) (by
    intro h
    have hs := (generator₁_signs M hM m hm).1
    rw [h, map_zero] at hs
    exact (lt_irrefl (0 : ℝ)) hs)

def generatorUnit₂ (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) : Kˣ :=
  Units.mk0 (generator₂ M hM m) (by
    intro h
    have hs := (generator₂_signs M hM m hm).1
    rw [h, map_zero] at hs
    exact (lt_irrefl (0 : ℝ)) hs)

/-- Source: local/global congruence bridge for the integral representatives, [RW-rec]; [RW26, p.
20]. -/
theorem generators_finiteCongruent (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    RayArithmeticModulus.FiniteCongruent M hM m (generatorUnit₁ M hM m hm) ∧
      RayArithmeticModulus.FiniteCongruent M hM m (generatorUnit₂ M hM m hm) := by
  constructor
  · exact (RayArithmeticModulus.finiteCongruent_iff_global M hM m hm
      ⟨generator₁ M hM m, (generators_integral M hM m).1⟩
      (Units.ne_zero (generatorUnit₁ M hM m hm))).mpr
        (generators_globallyCongruent M hM m).1
  · exact (RayArithmeticModulus.finiteCongruent_iff_global M hM m hm
      ⟨generator₂ M hM m, (generators_integral M hM m).2⟩
      (Units.ne_zero (generatorUnit₂ M hM m hm))).mpr
        (generators_globallyCongruent M hM m).2

def s₁ (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    RayArithmeticModulus.Group M hM m :=
  RayArithmeticModulus.principalClass M hM m (generatorUnit₁ M hM m hm)
    (generators_finiteCongruent M hM m hm).1

def s₂ (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    RayArithmeticModulus.Group M hM m :=
  RayArithmeticModulus.principalClass M hM m (generatorUnit₂ M hM m hm)
    (generators_finiteCongruent M hM m hm).2

def t (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    RayArithmeticModulus.Group M hM m := s₁ M hM m hm * s₂ M hM m hm

/-- Source: independence of the (-,+) principal representative, [RW-rec]. The generator may be a
nonintegral field unit. [RW26, p. 20]. -/
theorem principalClass_of_neg_pos (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : Kˣ) (ha : RayArithmeticModulus.FiniteCongruent M hM m a)
    (h₁ : ActualField.sigma₁ M hM (a : K) < 0)
    (h₂ : 0 < ActualField.sigma₂ M hM (a : K)) :
    RayArithmeticModulus.principalClass M hM m a ha = s₁ M hM m hm := by
  exact RayArithmeticSignsAux.principalClass_eq_of_same_sign M hM m a
    (generatorUnit₁ M hM m hm) ha (generators_finiteCongruent M hM m hm).1
    (Or.inr ⟨h₁, (generator₁_signs M hM m hm).1⟩)
    (Or.inl ⟨h₂, (generator₁_signs M hM m hm).2⟩)

/-- Source: independence of the (+,-) principal representative, [RW-rec]. [RW26, p. 20]. -/
theorem principalClass_of_pos_neg (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : Kˣ) (ha : RayArithmeticModulus.FiniteCongruent M hM m a)
    (h₁ : 0 < ActualField.sigma₁ M hM (a : K))
    (h₂ : ActualField.sigma₂ M hM (a : K) < 0) :
    RayArithmeticModulus.principalClass M hM m a ha = s₂ M hM m hm := by
  exact RayArithmeticSignsAux.principalClass_eq_of_same_sign M hM m a
    (generatorUnit₂ M hM m hm) ha (generators_finiteCongruent M hM m hm).2
    (Or.inl ⟨h₁, (generator₂_signs M hM m hm).1⟩)
    (Or.inr ⟨h₂, (generator₂_signs M hM m hm).2⟩)

/-- Source: the ray-principal quotient kernel, [RW-rec]. [RW26, p. 20]. -/
theorem principalClass_of_pos_pos (m : ℕ) (a : Kˣ)
    (ha : RayArithmeticModulus.FiniteCongruent M hM m a)
    (h₁ : 0 < ActualField.sigma₁ M hM (a : K))
    (h₂ : 0 < ActualField.sigma₂ M hM (a : K)) :
    RayArithmeticModulus.principalClass M hM m a ha = 1 := by
  apply (RayArithmeticModulus.class_eq_one_iff M hM m _).mpr
  exact ⟨a, (RayArithmeticModulus.isRayCongruent_iff M hM m a).mpr
    ⟨ha, h₁, h₂⟩, rfl⟩

/-- Source: product of the two real sign classes, [RW-rec]; [RW26, p. 20]. -/
theorem principalClass_of_neg_neg (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m)
    (a : Kˣ) (ha : RayArithmeticModulus.FiniteCongruent M hM m a)
    (h₁ : ActualField.sigma₁ M hM (a : K) < 0)
    (h₂ : ActualField.sigma₂ M hM (a : K) < 0) :
    RayArithmeticModulus.principalClass M hM m a ha = t M hM m hm := by
  have hf₁ := (generators_finiteCongruent M hM m hm).1
  have hf₂ := (generators_finiteCongruent M hM m hm).2
  have hs₁ := generator₁_signs M hM m hm
  have hs₂ := generator₂_signs M hM m hm
  have hsign₁ : ActualField.sigma₁ M hM
      ((generatorUnit₁ M hM m hm * generatorUnit₂ M hM m hm : Kˣ) : K) < 0 := by
    simpa only [Units.val_mul, map_mul, generatorUnit₁, generatorUnit₂, Units.val_mk0] using mul_neg_of_neg_of_pos hs₁.1 hs₂.1
  have hsign₂ : ActualField.sigma₂ M hM
      ((generatorUnit₁ M hM m hm * generatorUnit₂ M hM m hm : Kˣ) : K) < 0 := by
    simpa only [Units.val_mul, map_mul, generatorUnit₁, generatorUnit₂, Units.val_mk0] using mul_neg_of_pos_of_neg hs₁.2 hs₂.2
  calc
    RayArithmeticModulus.principalClass M hM m a ha =
        RayArithmeticModulus.principalClass M hM m
          (generatorUnit₁ M hM m hm * generatorUnit₂ M hM m hm)
          (ClassFieldTheory.IsRayCongruent.mul hf₁ hf₂) :=
      RayArithmeticSignsAux.principalClass_eq_of_same_sign M hM m a _ ha _
        (Or.inr ⟨h₁, hsign₁⟩) (Or.inr ⟨h₂, hsign₂⟩)
    _ = t M hM m hm := RayArithmeticSignsAux.principalClass_mul M hM m _ _ hf₁ hf₂

/-- Source: square of a one-place sign is totally positive, [RW-rec]. Includes s_1=1. [RW26, p. 20].
-/
theorem s₁_sq (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    s₁ M hM m hm ^ 2 = 1 := by
  rw [pow_two, s₁, ← RayArithmeticSignsAux.principalClass_mul M hM m
    (generatorUnit₁ M hM m hm) (generatorUnit₁ M hM m hm)
    (generators_finiteCongruent M hM m hm).1 (generators_finiteCongruent M hM m hm).1]
  apply principalClass_of_pos_pos
  · simpa only [Units.val_mul, map_mul, generatorUnit₁, generatorUnit₂, Units.val_mk0] using
      mul_pos_of_neg_of_neg (generator₁_signs M hM m hm).1 (generator₁_signs M hM m hm).1
  · simpa only [Units.val_mul, map_mul, generatorUnit₁, generatorUnit₂, Units.val_mk0] using
      mul_pos (generator₁_signs M hM m hm).2 (generator₁_signs M hM m hm).2

/-- Source: the same sign-square computation. Includes s_2=1. [RW26, p. 20]. -/
theorem s₂_sq (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    s₂ M hM m hm ^ 2 = 1 := by
  rw [pow_two, s₂, ← RayArithmeticSignsAux.principalClass_mul M hM m
    (generatorUnit₂ M hM m hm) (generatorUnit₂ M hM m hm)
    (generators_finiteCongruent M hM m hm).2 (generators_finiteCongruent M hM m hm).2]
  apply principalClass_of_pos_pos
  · simpa only [Units.val_mul, map_mul, generatorUnit₁, generatorUnit₂, Units.val_mk0] using
      mul_pos (generator₂_signs M hM m hm).1 (generator₂_signs M hM m hm).1
  · simpa only [Units.val_mul, map_mul, generatorUnit₁, generatorUnit₂, Units.val_mk0] using
      mul_pos_of_neg_of_neg (generator₂_signs M hM m hm).2 (generator₂_signs M hM m hm).2

/-- Source: quadratic conjugation exchanges the two sign classes, [RW-rec]. [RW26, p. 20]. -/
theorem conjugation_exchange (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    RayArithmeticConjugation.rayConjugation M hM m (s₁ M hM m hm) = s₂ M hM m hm ∧
      RayArithmeticConjugation.rayConjugation M hM m (s₂ M hM m hm) =
        s₁ M hM m hm := by
  have hg : RayArithmeticConjugation.unitConjugation M hM (generatorUnit₁ M hM m hm) =
      generatorUnit₂ M hM m hm := by
    apply Units.ext
    rfl
  have hfirst : RayArithmeticConjugation.rayConjugation M hM m (s₁ M hM m hm) =
      s₂ M hM m hm := by
    simpa only [s₁, s₂, hg] using
      RayArithmeticConjugation.rayConjugation_principalClass M hM m
        (generatorUnit₁ M hM m hm) (generators_finiteCongruent M hM m hm).1
  refine ⟨hfirst, ?_⟩
  have h := congrArg (RayArithmeticConjugation.rayConjugation M hM m) hfirst
  rw [RayArithmeticConjugation.rayConjugation_involutive M hM m] at h
  exact h.symm

/-- Source: commutativity and sign squares, [RW-rec]; Includes t=1. [RW26, p. 20]. -/
theorem t_sq (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    t M hM m hm ^ 2 = 1 := by
  rw [t, mul_pow (s₁ M hM m hm) (s₂ M hM m hm) 2, s₁_sq, s₂_sq]
  exact one_mul (1 : RayArithmeticModulus.Group M hM m)

/-- Source: conjugation fixes the product of the exchanged signs, [RW-rec]; [RW26, p. 20]. -/
theorem conjugation_t (m : ℕ) (hm : RayArithmeticOrder.ValidLevel M hM m) :
    RayArithmeticConjugation.rayConjugation M hM m (t M hM m hm) =
      t M hM m hm := by
  rw [t, map_mul, (conjugation_exchange M hM m hm).1,
    (conjugation_exchange M hM m hm).2]
  exact mul_comm (s₂ M hM m hm) (s₁ M hM m hm)

#print generator₁
#print s₁
#print s₂
#print t

end SICLean.L5.RayArithmeticSigns
