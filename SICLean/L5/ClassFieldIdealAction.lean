import SICLean.L5.ClassFieldModulus
import SICLean.L5.ClassFieldIdealActionAux

set_option autoImplicit false

/-!
# Conjugation of the actual modulus and its ideal classes

Sources: [RW-rec, §8]; the field K is [RW26, p. 20].
The ideal action is defined on ideals, before comparing embedded class fields.
-/

noncomputable section
open scoped NumberField MatrixGroups Classical
open NumberField IsDedekindDomain ClassFieldTheory
open SICLean.L5.ClassFieldModulus

namespace SICLean.L5.ClassFieldIdealAction

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)

/-- Actual real quadraticity implies normality over Q. -/
theorem base_normal : Normal ℚ (Base M hM) := by
  let : Algebra.IsQuadraticExtension ℚ (Base M hM) :=
    ⟨(ActualField.baseField_isRealQuadratic M hM).degree_two⟩
  infer_instance
attribute [instance] base_normal

def baseAction (ρ : Galois.QbarAut) : Base M hM ≃ₐ[ℚ] Base M hM :=
  ρ.restrictNormal (Base M hM)

def integerAction (ρ : Galois.QbarAut) : 𝓞 (Base M hM) ≃+* 𝓞 (Base M hM) :=
  RingOfIntegers.mapRingEquiv (baseAction M hM ρ).toRingEquiv

def fractionalAction (ρ : Galois.QbarAut) :
    NumberFieldFractionalIdealGroup (Base M hM) ≃*
      NumberFieldFractionalIdealGroup (Base M hM) :=
  Units.mapEquiv
    (FractionalIdeal.ringEquivOfRingEquiv (Base M hM) (Base M hM)
      (integerAction M hM ρ)).toMulEquiv

theorem baseAction_apply (ρ : Galois.QbarAut) (x : Base M hM) :
    (baseAction M hM ρ x : Galois.Qbar) = ρ (x : Galois.Qbar) := by
  exact AlgEquiv.restrictNormal_apply (Base M hM) ρ x

/-- Integral and fractional ideals use the same field automorphism. -/
theorem integerAction_coe (ρ : Galois.QbarAut) (x : 𝓞 (Base M hM)) :
    (integerAction M hM ρ x : Base M hM) = baseAction M hM ρ (x : Base M hM) :=
  by rfl

theorem prime_image (ρ : Galois.QbarAut) (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    (v.asIdeal.map (integerAction M hM ρ)).IsPrime ∧
      v.asIdeal.map (integerAction M hM ρ) ≠ ⊥ := by
  exact ⟨inferInstance,
    (Ideal.map_eq_bot_iff_of_injective (integerAction M hM ρ).injective).not.mpr v.ne_bot⟩

def primeAction (ρ : Galois.QbarAut) (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    HeightOneSpectrum (𝓞 (Base M hM)) :=
  ⟨v.asIdeal.map (integerAction M hM ρ), (prime_image M hM ρ v).1,
    (prime_image M hM ρ v).2⟩

/-- n is rational: the exponent of every conjugate prime is unchanged. -/
theorem finiteExponent_conjugate (n : ℕ) (ρ : Galois.QbarAut)
    (v : HeightOneSpectrum (𝓞 (Base M hM))) :
    (modulus M hM n).finitePart (primeAction M hM ρ v) =
      (modulus M hM n).finitePart v := by
  rw [modulus_finitePart, modulus_finitePart]
  change (Associates.mk (v.asIdeal.map (integerAction M hM ρ))).count
      (Associates.mk (Ideal.span ({(n : 𝓞 (Base M hM))} : Set _))).factors = _
  have hn : (Ideal.span ({(n : 𝓞 (Base M hM))} : Set _)).map
      (integerAction M hM ρ) = Ideal.span {(n : 𝓞 (Base M hM))} := by
    simp [Ideal.map_span]
  simpa only [hn, finiteExponent] using
    ClassFieldIdealActionAux.ideal_count_map (integerAction M hM ρ) v
      (Ideal.span ({(n : 𝓞 (Base M hM))} : Set _))

/-- The full infinite part is preserved, with an actual permutation of the two embeddings. -/
theorem realPlace_permuted (ρ : Galois.QbarAut) :
    ∃ π : Equiv.Perm (Fin 2), ∀ i,
      (realEmbedding M hM i).comp (baseAction M hM ρ).toRingHom =
        realEmbedding M hM (π i) := by
  have hinj : Function.Injective
      (fun f : Base M hM →+* ℝ => f.comp (baseAction M hM ρ).toRingHom) := by
    intro f g h
    ext x
    obtain ⟨y, rfl⟩ := (baseAction M hM ρ).surjective x
    exact RingHom.congr_fun h y
  have hne := ClassFieldIdealActionAux.realEmbedding_ne M hM
  rcases ClassFieldIdealActionAux.realEmbedding_cases M hM
    ((realEmbedding M hM 0).comp (baseAction M hM ρ).toRingHom) with h0 | h0
  · rcases ClassFieldIdealActionAux.realEmbedding_cases M hM
      ((realEmbedding M hM 1).comp (baseAction M hM ρ).toRingHom) with h1 | h1
    · exact (hne (hinj (h0.trans h1.symm))).elim
    · refine ⟨Equiv.refl _, ?_⟩
      intro i
      fin_cases i
      · exact h0
      · exact h1
  · rcases ClassFieldIdealActionAux.realEmbedding_cases M hM
      ((realEmbedding M hM 1).comp (baseAction M hM ρ).toRingHom) with h1 | h1
    · refine ⟨Equiv.swap 0 1, ?_⟩
      intro i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · exact (hne (hinj (h0.trans h1.symm))).elim

theorem rayIdeal_mem_iff (n : ℕ) (ρ : Galois.QbarAut)
    (a : NumberFieldFractionalIdealGroup (Base M hM)) :
    fractionalAction M hM ρ a ∈ rayClassPrimeToIdeals (modulus M hM n) ↔
      a ∈ rayClassPrimeToIdeals (modulus M hM n) := by
  let p := HeightOneSpectrum.equivOfRingEquiv (integerAction M hM ρ)
  have hp (v : HeightOneSpectrum (𝓞 (Base M hM))) :
      p v = primeAction M hM ρ v :=
    HeightOneSpectrum.ext (ClassFieldIdealActionAux.primeEquiv_asIdeal _ v)
  have hc (v : HeightOneSpectrum (𝓞 (Base M hM))) :
      FractionalIdeal.count (Base M hM) (p v)
        (fractionalAction M hM ρ a : FractionalIdeal _ _) =
          FractionalIdeal.count (Base M hM) v (a : FractionalIdeal _ _) :=
    ClassFieldIdealActionAux.fractional_count_map (baseAction M hM ρ) v a
  have hs (v : HeightOneSpectrum (𝓞 (Base M hM))) :
      p v ∈ (modulus M hM n).finitePart.support ↔
        v ∈ (modulus M hM n).finitePart.support := by
    simp only [Finsupp.mem_support_iff, hp, finiteExponent_conjugate]
  change (∀ v, v ∈ (modulus M hM n).finitePart.support →
    FractionalIdeal.count (Base M hM) v
      (fractionalAction M hM ρ a : FractionalIdeal _ _) = 0) ↔
    (∀ v, v ∈ (modulus M hM n).finitePart.support →
      FractionalIdeal.count (Base M hM) v (a : FractionalIdeal _ _) = 0)
  constructor
  · intro h v hv
    rw [← hc v]
    exact h (p v) ((hs v).mpr hv)
  · intro h v hv
    obtain ⟨w, rfl⟩ := p.surjective v
    rw [hc w]
    exact h w ((hs w).mp hv)

def rayIdealAction (n : ℕ) (ρ : Galois.QbarAut) : RayIdeal M hM n →* RayIdeal M hM n :=
  (((fractionalAction M hM ρ).toMonoidHom).comp
    (rayClassPrimeToIdeals (modulus M hM n)).subtype).codRestrict
      (rayClassPrimeToIdeals (modulus M hM n))
      (fun a => (rayIdeal_mem_iff M hM n ρ a.1).mpr a.2)

/-- The principal congruence subgroup is preserved before taking the quotient. -/
theorem rayPrincipal_stable (n : ℕ) (ρ : Galois.QbarAut) :
    rayPrincipalIdealSubgroupInPrimeTo (modulus M hM n) ≤
      (rayPrincipalIdealSubgroupInPrimeTo (modulus M hM n)).comap
        (rayIdealAction M hM n ρ) := by
  intro a ha
  change (fractionalAction M hM ρ a.1) ∈ rayPrincipalIdealSubgroup (modulus M hM n)
  obtain ⟨x, hx, hxa⟩ :=
    (mem_rayPrincipalIdealSubgroup_iff (modulus M hM n) a.1).mp ha
  let y := Units.mapEquiv (baseAction M hM ρ).toMulEquiv x
  refine (mem_rayPrincipalIdealSubgroup_iff _ _).mpr ⟨y, ⟨?_, ?_⟩, ?_⟩
  · intro w hw
    let p := HeightOneSpectrum.equivOfRingEquiv (integerAction M hM ρ)
    obtain ⟨v, rfl⟩ := p.surjective w
    have hp : p v = primeAction M hM ρ v :=
      HeightOneSpectrum.ext (ClassFieldIdealActionAux.primeEquiv_asIdeal _ v)
    have hm : (modulus M hM n).finitePart (p v) =
        (modulus M hM n).finitePart v := by
      rw [hp, finiteExponent_conjugate]
    have hv : v ∈ (modulus M hM n).finitePart.support := by
      simpa only [Finsupp.mem_support_iff, hm] using hw
    rw [hm]
    exact (ClassFieldIdealActionAux.finite_congr_map (baseAction M hM ρ) v _ x).mpr
      (hx.1 v hv)
  · intro w _
    obtain ⟨π, hπ⟩ := realPlace_permuted M hM ρ
    have hpos (i : Fin 2) : 0 < realEmbedding M hM i (x : Base M hM) := by
      rw [← realPlace_embedding M hM i]
      exact hx.2 (realPlace M hM i) (by simp [modulus])
    have hpos' (i : Fin 2) : 0 < realEmbedding M hM i (y : Base M hM) := by
      change 0 < realEmbedding M hM i (baseAction M hM ρ (x : Base M hM))
      have hi := RingHom.congr_fun (hπ i) (x : Base M hM)
      change realEmbedding M hM i (baseAction M hM ρ (x : Base M hM)) = _ at hi
      rw [hi]
      exact hpos (π i)
    rcases realPlace_exhaustive M hM w with rfl | rfl
    · simpa only [realPlace_embedding] using hpos' 0
    · simpa only [realPlace_embedding] using hpos' 1
  · rw [← hxa]
    exact (ClassFieldIdealActionAux.fractional_map_principal (baseAction M hM ρ) x).symm

def rayAction (n : ℕ) (ρ : Galois.QbarAut) : RayGroup M hM n →* RayGroup M hM n :=
  QuotientGroup.map _ _ (rayIdealAction M hM n ρ) (rayPrincipal_stable M hM n ρ)

theorem rayAction_ideal (n : ℕ) (ρ : Galois.QbarAut) (a : RayIdeal M hM n) :
    rayAction M hM n ρ (idealClass M hM n a) =
      idealClass M hM n (rayIdealAction M hM n ρ a) := by
  rfl

theorem rayAction_inv (n : ℕ) (ρ : Galois.QbarAut) (a : RayGroup M hM n) :
    rayAction M hM n ρ⁻¹ (rayAction M hM n ρ a) = a := by
  obtain ⟨b, rfl⟩ := idealClass_surjective M hM n a
  rw [rayAction_ideal, rayAction_ideal]
  congr 1
  apply Subtype.ext
  change fractionalAction M hM ρ⁻¹ (fractionalAction M hM ρ b.1) = b.1
  have he : baseAction M hM ρ⁻¹ = (baseAction M hM ρ).symm :=
    (AlgEquiv.restrictNormalHom (Base M hM)).map_inv ρ
  change Units.mapEquiv
      (FractionalIdeal.ringEquivOfRingEquiv (Base M hM) (Base M hM)
        (RingOfIntegers.mapRingEquiv (baseAction M hM ρ⁻¹).toRingEquiv)).toMulEquiv
      (fractionalAction M hM ρ b.1) = b.1
  rw [he]
  exact ClassFieldIdealActionAux.fractional_map_symm (baseAction M hM ρ) b.1

/-- Every automorphism flipping K exchanges the two real embeddings.
`ActualField.sigma₂` is the trace minus `sigma₁`. -/
theorem baseAction_flip (τ : Galois.QbarAut)
    (hτ : Galois.InducesNontrivial (ActualField.baseField M hM) τ) :
    (realEmbedding M hM 0).comp (baseAction M hM τ).toRingHom = realEmbedding M hM 1 ∧
      (realEmbedding M hM 1).comp (baseAction M hM τ).toRingHom = realEmbedding M hM 0 :=
  by
    have hfirst : ∀ x : Base M hM,
        ActualField.sigma₁ M hM (baseAction M hM τ x) = ActualField.sigma₂ M hM x := by
      intro x
      have h := (ActualField.inducesNontrivial_iff M hM τ).mp hτ x
      simpa [← baseAction_apply M hM τ x, ActualField.sigma₁] using congrArg Complex.re h
    constructor
    · ext x
      simpa [realEmbedding] using hfirst x
    · ext x
      change ActualField.sigma₂ M hM (baseAction M hM τ x) = ActualField.sigma₁ M hM x
      change (Algebra.trace ℚ (Base M hM) (baseAction M hM τ x) : ℝ) -
        ActualField.sigma₁ M hM (baseAction M hM τ x) = ActualField.sigma₁ M hM x
      rw [Algebra.trace_eq_of_algEquiv (baseAction M hM τ), hfirst]
      change (Algebra.trace ℚ (Base M hM) x : ℝ) -
        ((Algebra.trace ℚ (Base M hM) x : ℝ) - ActualField.sigma₁ M hM x) = _
      ring

end SICLean.L5.ClassFieldIdealAction

#check @FractionalIdeal.ringEquivOfRingEquiv
#check @RingOfIntegers.mapRingEquiv
#check @QuotientGroup.map
