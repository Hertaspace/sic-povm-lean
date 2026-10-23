import SICLean.Final.Unconditional

set_option autoImplicit false

/-!
Elementary support for the fixed quadratic field: an explicit annihilating
polynomial, degree and realness of a simple adjoin, and the quadratic trace
identity identifying trace minus one real embedding with the conjugate.
-/

noncomputable section
open scoped MatrixGroups BigOperators
open Polynomial

namespace SICLean.L5.ActualQuadraticFieldAux

theorem tau_poly_real (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    (M 1 0 : ℝ) * L4.specialValueTau M ^ 2 +
      ((M 1 1 : ℝ) - (M 0 0 : ℝ)) * L4.specialValueTau M +
      (-(M 0 1 : ℝ)) = 0 := by
  have h := L4.specialValueTau_real_relation M hM
  nlinarith

def tauPoly (M : SL(2, ℤ)) : ℚ[X] :=
  C (M 1 0 : ℚ) * X ^ 2 + C ((M 1 1 - M 0 0 : ℤ) : ℚ) * X +
    C (-(M 0 1 : ℚ))

theorem tauPoly_natDegree (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    (tauPoly M).natDegree = 2 := by
  apply Polynomial.natDegree_quadratic
  exact_mod_cast ne_of_gt hM.1

theorem tauPoly_ne_zero (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    tauPoly M ≠ 0 := by
  intro h
  have hd := tauPoly_natDegree M hM
  simp [h] at hd

theorem tau_isAlgebraic (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M) :
    IsAlgebraic ℚ (L4.specialValueTau M : ℂ) := by
  refine ⟨tauPoly M, tauPoly_ne_zero M hM, ?_⟩
  have hreal := tau_poly_real M hM
  have hcomplex :
      (M 1 0 : ℂ) * (L4.specialValueTau M : ℂ) ^ 2 +
        ((M 1 1 : ℂ) - (M 0 0 : ℂ)) * (L4.specialValueTau M : ℂ) +
        (-(M 0 1 : ℂ)) = 0 := by
    exact_mod_cast hreal
  simpa [tauPoly] using hcomplex

theorem adjoin_finrank_eq_two {E : Type*} [Field E] [Algebra ℚ E]
    (x : E) (p : ℚ[X]) (hp : p ≠ 0) (hpd : p.natDegree = 2)
    (hx : Polynomial.aeval x p = 0)
    (hirr : x ∉ (algebraMap ℚ E).range) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({x} : Set E)) = 2 := by
  have hint : IsIntegral ℚ x := (show IsAlgebraic ℚ x from ⟨p, hp, hx⟩).isIntegral
  rw [IntermediateField.adjoin.finrank hint]
  apply Nat.le_antisymm
  · have hdiv := minpoly.dvd ℚ x hx
    exact (Polynomial.natDegree_le_of_dvd hdiv hp).trans hpd.le
  · exact (minpoly.two_le_natDegree_iff hint).mpr hirr

theorem real_adjoin (x : Galois.Qbar) (hx : (Galois.embed x).im = 0) :
    ∀ a : IntermediateField.adjoin ℚ ({x} : Set Galois.Qbar),
      (Galois.embed (a : Galois.Qbar)).im = 0 := by
  intro a
  refine IntermediateField.adjoin_induction ℚ
    (p := fun y _ => (Galois.embed y).im = 0) ?_ ?_ ?_ ?_ ?_ a.property
  · intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    simpa [hyx] using hx
  · intro q
    simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro y _ hy
    simp [Complex.inv_im, hy]
  · intro y z _ _ hy hz
    simp [Complex.mul_im, hy, hz]

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem quadratic_exists_nontrivial_aut (hK : Module.finrank ℚ K = 2) :
    ∃ κ : K ≃ₐ[ℚ] K, κ ≠ AlgEquiv.refl := by
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hK]
  obtain ⟨κ, hκ, _⟩ := (Nat.card_eq_two_iff' ((AlgEquiv.refl : K ≃ₐ[ℚ] K))).mp hcard
  exact ⟨κ, hκ⟩

theorem quadratic_aut_eq (hK : Module.finrank ℚ K = 2)
    {κ η : K ≃ₐ[ℚ] K} (hκ : κ ≠ AlgEquiv.refl) (hη : η ≠ AlgEquiv.refl) : κ = η := by
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hK]
  exact ExistsUnique.unique ((Nat.card_eq_two_iff' ((AlgEquiv.refl : K ≃ₐ[ℚ] K))).mp hcard)
    hκ hη

theorem quadratic_trace_eq_add (hK : Module.finrank ℚ K = 2)
    (κ : K ≃ₐ[ℚ] K) (hκ : κ ≠ AlgEquiv.refl) (x : K) :
    algebraMap ℚ K (Algebra.trace ℚ K x) = x + κ x := by
  classical
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hcases : ∀ η : K ≃ₐ[ℚ] K, η = AlgEquiv.refl ∨ η = κ := by
    intro η
    by_cases hη : η = AlgEquiv.refl
    · exact Or.inl hη
    · exact Or.inr (quadratic_aut_eq hK hη hκ)
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {AlgEquiv.refl, κ} := by
    ext η
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcases η
  rw [trace_eq_sum_automorphisms, huniv]
  simp [Ne.symm hκ]

theorem trace_sub_eq_conjugate (hK : Module.finrank ℚ K = 2)
    (f : K →+* ℝ) (κ : K ≃ₐ[ℚ] K) (hκ : κ ≠ AlgEquiv.refl) (x : K) :
    (Algebra.trace ℚ K x : ℝ) - f x = f (κ x) := by
  have h := congrArg f (quadratic_trace_eq_add hK κ hκ x)
  simp only [map_add, RingHom.map_rat_algebraMap] at h
  change (Algebra.trace ℚ K x : ℝ) = f x + f (κ x) at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

theorem trace_sub_map_one (hK : Module.finrank ℚ K = 2) (f : K →+* ℝ) :
    (Algebra.trace ℚ K (1 : K) : ℝ) - f 1 = 1 := by
  obtain ⟨κ, hκ⟩ := quadratic_exists_nontrivial_aut hK
  rw [trace_sub_eq_conjugate hK f κ hκ]
  simp

theorem trace_sub_map_mul (hK : Module.finrank ℚ K = 2) (f : K →+* ℝ) (x y : K) :
    (Algebra.trace ℚ K (x * y) : ℝ) - f (x * y) =
      ((Algebra.trace ℚ K x : ℝ) - f x) * ((Algebra.trace ℚ K y : ℝ) - f y) := by
  obtain ⟨κ, hκ⟩ := quadratic_exists_nontrivial_aut hK
  rw [trace_sub_eq_conjugate hK f κ hκ (x * y),
    trace_sub_eq_conjugate hK f κ hκ x, trace_sub_eq_conjugate hK f κ hκ y]
  simp

theorem trace_sub_map_zero (f : K →+* ℝ) :
    (Algebra.trace ℚ K (0 : K) : ℝ) - f 0 = 0 := by simp

theorem trace_sub_map_add (f : K →+* ℝ) (x y : K) :
    (Algebra.trace ℚ K (x + y) : ℝ) - f (x + y) =
      ((Algebra.trace ℚ K x : ℝ) - f x) + ((Algebra.trace ℚ K y : ℝ) - f y) := by
  simp only [map_add, Rat.cast_add]
  ring

theorem trace_of_quadratic_relation (hK : Module.finrank ℚ K = 2)
    (κ : K ≃ₐ[ℚ] K) (hκ : κ ≠ AlgEquiv.refl) (x : K) (hfix : κ x ≠ x)
    (c s b : ℚ) (hc : c ≠ 0)
    (hx : algebraMap ℚ K c * x ^ 2 + algebraMap ℚ K s * x + algebraMap ℚ K b = 0) :
    Algebra.trace ℚ K x = -s / c := by
  have hy := congrArg κ hx
  simp only [map_add, map_mul, map_pow, AlgEquiv.commutes, map_zero] at hy
  have hfactor : (x - κ x) *
      (algebraMap ℚ K c * (x + κ x) + algebraMap ℚ K s) = 0 := by
    linear_combination hx - hy
  have hsum := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr (Ne.symm hfix))
  apply (algebraMap ℚ K).injective
  rw [quadratic_trace_eq_add hK κ hκ x, map_div₀, map_neg]
  apply (eq_div_iff ((map_ne_zero (algebraMap ℚ K)).mpr hc)).mpr
  linear_combination hsum

variable {E : Type*} [Field E] [Algebra ℚ E]

/-- A nonidentity automorphism of a simple adjoin moves its generator.
Rebase the ring homomorphisms locally to the adjoin's rational algebra. -/
theorem nontrivial_not_fixed_adjoin (t : E)
    (κ : IntermediateField.adjoin ℚ ({t} : Set E) ≃ₐ[ℚ]
      IntermediateField.adjoin ℚ ({t} : Set E)) (hκ : κ ≠ AlgEquiv.refl) :
    κ ⟨t, IntermediateField.subset_adjoin ℚ {t} (Set.mem_singleton t)⟩ ≠
      ⟨t, IntermediateField.subset_adjoin ℚ {t} (Set.mem_singleton t)⟩ := by
  intro hfix
  have hfun : ∀ x, κ x = x := by
    let T := IntermediateField.adjoin ℚ ({t} : Set E)
    let : Algebra ℚ T := T.algebra'
    have hhom : κ.toRingHom.toRatAlgHom = (RingHom.id T).toRatAlgHom := by
      apply IntermediateField.adjoin_algHom_ext ℚ
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact hfix
    intro x
    exact DFunLike.congr_fun hhom x
  exact hκ (AlgEquiv.ext hfun)

theorem inducesNontrivial_iff_trace_sub
    (K : IntermediateField ℚ Galois.Qbar) (hK : Module.finrank ℚ K = 2)
    (f : K →+* ℝ) (hf : ∀ x : K, Galois.embed (x : Galois.Qbar) = (f x : ℂ))
    (σ : Galois.QbarAut) :
    Galois.InducesNontrivial K σ ↔
      ∀ x : K, Galois.embed (σ (x : Galois.Qbar)) =
        (((Algebra.trace ℚ K x : ℝ) - f x : ℝ) : ℂ) := by
  constructor
  · rintro ⟨κ, hκ, hσ⟩ x
    rw [hσ x, hf (κ x), trace_sub_eq_conjugate hK f κ hκ x]
  · intro hσ
    obtain ⟨κ, hκ⟩ := quadratic_exists_nontrivial_aut hK
    refine ⟨κ, hκ, ?_⟩
    intro x
    apply Galois.embed.injective
    change Galois.embed (σ (x : Galois.Qbar)) = Galois.embed (κ x : Galois.Qbar)
    rw [hσ x, hf (κ x), trace_sub_eq_conjugate hK f κ hκ x]


end SICLean.L5.ActualQuadraticFieldAux
