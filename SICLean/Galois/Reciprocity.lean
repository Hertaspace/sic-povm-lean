import SICLean.Galois.AlgebraicClosure

set_option autoImplicit false

/-!
# The statement of [RW-rec, Prop. 7]

This file states the conclusion of [RW-rec, §9.2, Prop. 7] on the algebraic special values
and transports it. The statement is proved in `SICLean.L5.ActualProp7` (`matrix_prop7`).
-/

noncomputable section

namespace SICLean.Galois

/-- A real quadratic field in the fixed copy of ℚbar. -/
structure IsRealQuadratic (K : IntermediateField ℚ Qbar) : Prop where
  degree_two : Module.finrank ℚ K = 2
  real : ∀ a : K, (embed (a : Qbar)).im = 0

/-- σ restricts to the nontrivial ℚ-automorphism of K. This is an actual
restriction equation, not merely the assertion σ ≠ 1 on all of ℚbar. -/
def InducesNontrivial (K : IntermediateField ℚ Qbar) (σ : QbarAut) : Prop :=
  ∃ κ : K ≃ₐ[ℚ] K, κ ≠ AlgEquiv.refl ∧
    ∀ a : K, σ (a : Qbar) = (κ a : Qbar)

/-- Ordinary normal lifting is legitimate for K ⊆ ℚbar. This supplies a
single σ when using the universal quantifier of the literal Proposition 7. -/
theorem exists_nontrivial_lift (K : IntermediateField ℚ Qbar)
    (hK : IsRealQuadratic K) :
    ∃ σ : QbarAut, InducesNontrivial K σ := by
  have hfin : Module.Finite ℚ K := Module.finite_of_finrank_eq_succ (n := 1) hK.degree_two
  have hquad : Algebra.IsQuadraticExtension ℚ K := ⟨hK.degree_two⟩
  have hgal : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hK.degree_two]
  haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ K
  have hcard2 : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  have hgt : 1 < Fintype.card (K ≃ₐ[ℚ] K) := by rw [hcard2]; norm_num
  obtain ⟨κ, hκ⟩ := Fintype.exists_ne_of_one_lt_card (a := AlgEquiv.refl) hgt
  refine ⟨κ.liftNormal Qbar, κ, hκ, ?_⟩
  intro a
  exact κ.liftNormal_commutes Qbar a

variable {J : Type*} [Zero J]

/-- [RW-rec, Prop. 7] has no condition on the zero class. -/
def Prop7Conclusion (a : J → Qbar) (σ : QbarAut) : Prop :=
  ∀ x : J, x ≠ 0 → ‖embed (σ (a x))‖ = 1

/-- The form of [RW-rec, Prop. 7] quantifying over every automorphism that
induces the nontrivial automorphism of K. For the actual values it is proved in
`SICLean.L5.ActualProp7`. -/
def Prop7ForValues (K : IntermediateField ℚ Qbar) (a : J → Qbar) : Prop :=
  ∀ σ : QbarAut, InducesNontrivial K σ → Prop7Conclusion a σ

/-- Consequence of algebraicity plus one [RW-rec, Prop. 7] witness.
The field K and the restriction equation are part of the data.
They do not require σ to fix roots of unity or any square-root sign. -/
structure Prop7Input (E : J → ℂ) : Prop where
  algebraic : ∀ x, IsAlgebraic ℚ (E x)
  common_flip : ∃ K : IntermediateField ℚ Qbar, IsRealQuadratic K ∧
    ∃ σ : QbarAut, InducesNontrivial K σ ∧
      Prop7Conclusion (fun x => algebraicLift (E x) (algebraic x)) σ

/-- Pass from the universal form of [RW-rec, Prop. 7] to one witness.
This implication does not include the analytic or lattice hypotheses. -/
theorem prop7Input_of_forall (E : J → ℂ)
    (hAlg : ∀ x, IsAlgebraic ℚ (E x))
    (K : IntermediateField ℚ Qbar) (hK : IsRealQuadratic K)
    (h7 : Prop7ForValues K (fun x => algebraicLift (E x) (hAlg x))) :
    Prop7Input E := by
  obtain ⟨σ, hσ⟩ := exists_nontrivial_lift K hK
  exact ⟨hAlg, K, hK, σ, hσ, h7 σ hσ⟩

/-- The same σ and the same complex values occur on both sides. -/
theorem unitCircle_of_sigma (E : J → ℂ)
    (hAlg : ∀ x, IsAlgebraic ℚ (E x)) (σ : QbarAut)
    (h7 : Prop7Conclusion (fun x => algebraicLift (E x) (hAlg x)) σ) :
    ∃ T : ℂ ≃ₐ[ℚ] ℂ, Extends σ T ∧
      ∀ x : J, x ≠ 0 → ‖T (E x)‖ = 1 := by
  obtain ⟨T, hT⟩ := exists_complex_extension σ
  refine ⟨T, hT, ?_⟩
  intro x hx
  rw [← embed_algebraicLift (E x) (hAlg x), hT]
  exact h7 x hx

theorem unitCircle_of_prop7 (E : J → ℂ) (h : Prop7Input E) :
    ∃ τ : ℂ →+* ℂ, ∀ x : J, x ≠ 0 → ‖τ (E x)‖ = 1 := by
  obtain ⟨hAlg, K, hK, σ, hσ, h7⟩ := h
  obtain ⟨T, -, hnorm⟩ := unitCircle_of_sigma E hAlg σ h7
  exact ⟨T.toAlgHom.toRingHom, hnorm⟩

/-- For a norm-one period, the origin square root maps to ± its inverse.
This is separate from the unit-circle conclusion of [RW-rec, Prop. 7] off zero.
The restriction equation is the one supplied by `InducesNontrivial`. -/
theorem map_period_sqrt (K : IntermediateField ℚ Qbar)
    (κ : K ≃ₐ[ℚ] K) (σ : QbarAut)
    (hσ : ∀ a : K, σ (a : Qbar) = (κ a : Qbar))
    (ε : K) (hε : κ ε = ε⁻¹) (hε0 : ε ≠ 0)
    (s : ℂ) (hs : s ^ 2 = embed (ε : Qbar))
    (T : ℂ ≃ₐ[ℚ] ℂ) (hT : Extends σ T) :
    T s = s⁻¹ ∨ T s = -s⁻¹ := by
  have hsq : (T s) ^ 2 = (s⁻¹) ^ 2 := by
    calc (T s) ^ 2 = T (s ^ 2) := (map_pow T s 2).symm
      _ = T (embed (ε : Qbar)) := by rw [hs]
      _ = embed (σ (ε : Qbar)) := hT (ε : Qbar)
      _ = embed ((κ ε : K) : Qbar) := by rw [hσ ε]
      _ = embed ((ε⁻¹ : K) : Qbar) := by rw [hε]
      _ = (embed (ε : Qbar))⁻¹ := by simp
      _ = (s ^ 2)⁻¹ := by rw [← hs]
      _ = (s⁻¹) ^ 2 := by rw [inv_pow]
  have hzero : (T s - s⁻¹) * (T s + s⁻¹) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hzero with h | h
  · left; linear_combination h
  · right; linear_combination h

end SICLean.Galois

#check @SICLean.Galois.Prop7Conclusion
#check @SICLean.Galois.Prop7ForValues
#print SICLean.Galois.Prop7Input
#print SICLean.Galois.unitCircle_of_sigma
