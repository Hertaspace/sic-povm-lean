import Mathlib

set_option autoImplicit false

/-! The closed-point bridge for a coordinate projection of an affine zero locus. -/

noncomputable section

namespace SICLean.L3.FiniteSystem.CoordinateImageGeometry

open MvPolynomial Polynomial Topology

universe u v

variable {A : Type u} [Field A]

def polyPoint (a : A) : PrimeSpectrum A[X] :=
  ⟨RingHom.ker (Polynomial.evalRingHom a),
    RingHom.ker_isPrime (Polynomial.evalRingHom a)⟩

@[simp] lemma mem_polyPoint (p : A[X]) (a : A) :
    p ∈ (polyPoint a).asIdeal ↔ p.eval a = 0 := Iff.rfl

omit [Field A] in
lemma finite_or_cofinite_union {s t : Set A}
    (hs : s.Finite ∨ sᶜ.Finite) (ht : t.Finite ∨ tᶜ.Finite) :
    (s ∪ t).Finite ∨ (s ∪ t)ᶜ.Finite := by
  rcases hs with hs | hs
  · rcases ht with ht | ht
    · exact .inl (hs.union ht)
    · exact .inr (ht.subset (by intro a ha; exact fun ht => ha (.inr ht)))
  · exact .inr (hs.subset (by intro a ha; exact fun hs => ha (.inl hs)))

lemma basic_pullback_finite_or_cofinite
    (C : PrimeSpectrum.BasicConstructibleSetData A[X]) :
    (polyPoint ⁻¹' C.toSet).Finite ∨ (polyPoint ⁻¹' C.toSet)ᶜ.Finite := by
  classical
  by_cases hg : ∃ i, C.g i ≠ 0
  · obtain ⟨i, hi⟩ := hg
    left
    apply (Polynomial.finite_setOfPred_isRoot hi).subset
    intro a ha
    exact ha.1 (Set.mem_range_self i)
  · have hg : ∀ i, C.g i = 0 := by simpa using hg
    by_cases hf : C.f = 0
    · left
      have h : polyPoint ⁻¹' C.toSet = ∅ := by
        ext a
        simp [PrimeSpectrum.BasicConstructibleSetData.toSet, hf]
      exact h ▸ Set.finite_empty
    · right
      apply (Polynomial.finite_setOfPred_isRoot hf).subset
      intro a ha
      change C.f.eval a = 0
      by_contra h
      apply ha
      constructor
      · rintro _ ⟨i, rfl⟩
        simp [hg]
      · intro h'
        exact h (h' (Set.mem_singleton _))

lemma constructible_pullback_finite_or_cofinite
    {s : Set (PrimeSpectrum A[X])} (hs : IsConstructible s) :
    (polyPoint ⁻¹' s).Finite ∨ (polyPoint ⁻¹' s)ᶜ.Finite := by
  classical
  obtain ⟨S, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hs
  clear hs
  induction S using Finset.induction_on with
  | empty => simp [PrimeSpectrum.ConstructibleSetData.toSet]
  | @insert C S hC ih =>
    have heq : PrimeSpectrum.ConstructibleSetData.toSet (insert C S) =
        C.toSet ∪ PrimeSpectrum.ConstructibleSetData.toSet S := by
      simp [PrimeSpectrum.ConstructibleSetData.toSet]
    rw [heq, Set.preimage_union]
    exact finite_or_cofinite_union (basic_pullback_finite_or_cofinite C) ih

variable {σ : Type v} [Finite σ] [IsAlgClosed A]

lemma coordinate_zeroLocus_finite_or_cofinite
    (J : Ideal (MvPolynomial σ A)) (c : σ) :
    ((fun z : σ → A => z c) '' MvPolynomial.zeroLocus A J).Finite ∨
      ((fun z : σ → A => z c) '' MvPolynomial.zeroLocus A J)ᶜ.Finite := by
  classical
  let f : A[X] →+* MvPolynomial σ A :=
    (Polynomial.aeval (MvPolynomial.X c)).toRingHom
  have hcomp : f.comp Polynomial.C = MvPolynomial.C := by
    ext a
    simp [f]
  have hf : f.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := Polynomial.C)
    rw [hcomp]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hJ : IsConstructible
      (PrimeSpectrum.zeroLocus (J : Set (MvPolynomial σ A))) := by
    rw [← isConstructible_compl]
    exact
      (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg
        J.fg_of_isNoetherianRing).isConstructible
        (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have himg := PrimeSpectrum.isConstructible_comap_image hf hJ
  have hfeval (z : σ → A) :
      (MvPolynomial.aeval z).toRingHom.comp f =
        Polynomial.evalRingHom (z c) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [f]
    · simp [f]
  have heq :
      (fun z : σ → A => z c) '' MvPolynomial.zeroLocus A J =
        polyPoint ⁻¹'
          (PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (J : Set _)) := by
    ext a
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨MvPolynomial.pointToPoint (k := A) z, ?_, ?_⟩
      · intro p hp
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff z p).mpr (hz p hp)
      · apply PrimeSpectrum.ext
        ext p
        change f p ∈ MvPolynomial.vanishingIdeal A {z} ↔
          p.eval (z c) = 0
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        change ((MvPolynomial.aeval z).toRingHom.comp f) p = 0 ↔ _
        rw [hfeval]
        rfl
    · rintro ⟨P, hP, hPa⟩
      obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
      obtain ⟨z, hz⟩ :=
        MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hM
      have hker : (polyPoint a).asIdeal = M.comap f := by
        have hmax : (polyPoint a).asIdeal.IsMaximal :=
          RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom a)
            (by intro b; exact ⟨Polynomial.C b, by simp⟩)
        apply hmax.eq_of_le (Ideal.comap_ne_top f hM.ne_top)
        rw [← hPa]
        exact Ideal.comap_mono hPM
      refine ⟨z, ?_, ?_⟩
      · intro p hp
        apply (MvPolynomial.mem_vanishingIdeal_singleton_iff z p).mp
        rw [← hz]
        exact hPM (hP hp)
      · have hx : Polynomial.X - Polynomial.C a ∈
            (polyPoint a).asIdeal := by simp
        rw [hker] at hx
        change f (Polynomial.X - Polynomial.C a) ∈ M at hx
        rw [hz] at hx
        have hzero := (MvPolynomial.mem_vanishingIdeal_singleton_iff z _).mp hx
        exact sub_eq_zero.mp (by simpa [f] using hzero)
  rw [heq]
  exact constructible_pullback_finite_or_cofinite himg

end SICLean.L3.FiniteSystem.CoordinateImageGeometry
