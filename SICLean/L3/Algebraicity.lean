import SICLean.L3.Valuation
import SICLean.L3.CoordinateImageGeometry

set_option autoImplicit false

/-!
# Finite coordinate images and algebraicity of every complex solution

No constructibility, finiteness, or valuation conclusion is among the
hypotheses of the final theorem.
-/

noncomputable section

namespace SICLean.L3

universe u v w w'

variable {I : Type u} [Fintype I] {G : I → Type v}
variable [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]
variable {k : Type w} [Field k]

/-- A normalized valuation above 2 exists on an algebraically closed
algebraic extension of ℚ. This is a theorem, not a new input. -/
theorem exists_twoAdicValuation (A : Type w') [Field A] [CharZero A]
    [Algebra ℚ A] [Algebra.IsAlgebraic ℚ A] [IsAlgClosed A] :
    ∃ v : AddValuation A (WithTop ℝ), v (2 : A) = 1 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : A →ₐ[ℚ] PadicAlgCl 2 := IsAlgClosed.lift
  let vf : PadicAlgCl 2 → WithTop ℝ :=
    fun x ↦ if x = 0 then ⊤ else ↑(-Real.log ‖x‖ / Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : vf 0 = ⊤ := by simp [vf]
  have h1 : vf 1 = 0 := by simp [vf]
  have ha : ∀ x y, min (vf x) (vf y) ≤ vf (x + y) := by
    intro x y
    by_cases hx : x = 0
    · subst x
      simp [vf]
    by_cases hy : y = 0
    · subst y
      simp [vf]
    by_cases hxy : x + y = 0
    · simp [vf, hxy]
    simp only [vf, hx, hy, hxy, ↓reduceIte]
    rcases le_total ‖x‖ ‖y‖ with hn | hn
    · apply (min_le_right _ _).trans
      apply WithTop.coe_le_coe.mpr
      exact div_le_div_of_nonneg_right
        (neg_le_neg (Real.log_le_log (norm_pos_iff.mpr hxy)
          ((PadicAlgCl.isNonarchimedean 2 x y).trans
            (max_eq_right hn).le))) hlog.le
    · apply (min_le_left _ _).trans
      apply WithTop.coe_le_coe.mpr
      exact div_le_div_of_nonneg_right
        (neg_le_neg (Real.log_le_log (norm_pos_iff.mpr hxy)
          ((PadicAlgCl.isNonarchimedean 2 x y).trans
            (max_eq_left hn).le))) hlog.le
  have hm : ∀ x y, vf (x * y) = vf x + vf y := by
    intro x y
    by_cases hx : x = 0
    · subst x
      simp [vf]
    by_cases hy : y = 0
    · subst y
      simp [vf]
    simp only [vf, hx, hy, mul_ne_zero hx hy, ↓reduceIte, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]
    rw [← WithTop.coe_add]
    congr 1
    ring
  let v0 : AddValuation (PadicAlgCl 2) (WithTop ℝ) :=
    AddValuation.of vf h0 h1 ha hm
  refine ⟨v0.comap f.toRingHom, ?_⟩
  have hn : ‖(2 : PadicAlgCl 2)‖ = (2 : ℝ)⁻¹ := by
    have hh := congrArg (fun x : NNReal ↦ (x : ℝ)) (PadicAlgCl.valuation_p 2)
    simpa using hh
  change vf (f 2) = 1
  simp [vf, map_ofNat, hn, Real.log_inv, ne_of_gt hlog]

namespace FiniteSystem

variable (D : FiniteSystem I G k)

/-- Chevalley's constructible-image theorem, including the bridge from
prime spectra to A-valued points of the finite polynomial system. -/
theorem coordinateImage_finite_or_cofinite (A : Type w') [Field A]
    [Algebra k A] [IsAlgClosed A] (c : Coordinate I G) :
    (D.coordinateImage A c).Finite ∨ (D.coordinateImage A c)ᶜ.Finite := by
  classical
  let J := Ideal.map (MvPolynomial.map (algebraMap k A)) D.equationIdeal
  have hmap (z : Coordinate I G → A) :
      (MvPolynomial.aeval (R := A) z).toRingHom.comp
          (MvPolynomial.map (algebraMap k A)) =
        (MvPolynomial.aeval (R := k) z).toRingHom := by
    ext <;> simp
  have heq : D.solutionSet A = MvPolynomial.zeroLocus A J := by
    ext z
    change D.IsSolution A z ↔ _
    rw [D.isSolution_iff_mem_zeroLocus]
    constructor
    · intro hz
      have hle : J ≤ MvPolynomial.vanishingIdeal A {z} := by
        apply Ideal.map_le_iff_le_comap.mpr
        intro p hp
        rw [Ideal.mem_comap, MvPolynomial.mem_vanishingIdeal_singleton_iff]
        change ((MvPolynomial.aeval (R := A) z).toRingHom.comp
          (MvPolynomial.map (algebraMap k A))) p = 0
        rw [hmap]
        exact hz p hp
      intro p hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff z p).mp (hle hp)
    · intro hz p hp
      have hx :=
        hz _ (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap k A)) hp)
      change ((MvPolynomial.aeval (R := A) z).toRingHom.comp
        (MvPolynomial.map (algebraMap k A))) p = 0 at hx
      rwa [hmap] at hx
  simpa only [FiniteSystem.coordinateImage, heq] using
    CoordinateImageGeometry.coordinate_zeroLocus_finite_or_cofinite J c

/-- The valuation theorem rules out the cofinite alternative using positive powers of 2.
The coefficient field and the point field use a compatible ℚ-algebra tower. -/
theorem coordinateImage_finite (A : Type w') [Field A] [CharZero A]
    [Algebra ℚ k] [Algebra k A] [Algebra ℚ A] [IsScalarTower ℚ k A]
    [Algebra.IsAlgebraic ℚ A] [IsAlgClosed A] (c : Coordinate I G) :
    (D.coordinateImage A c).Finite := by
  classical
  rcases D.coordinateImage_finite_or_cofinite A c with h | h
  · exact h
  obtain ⟨v, hv⟩ := exists_twoAdicValuation A
  let f : ℕ → A := fun n => (2 : A) ^ (n + 1)
  have hvf (n : ℕ) : v (f n) = (n + 1 : ℕ) := by
    simp [f, v.map_pow, hv, nsmul_one]
  have hf : Function.Injective f := by
    intro m n hmn
    have he := congrArg v hmn
    rw [hvf, hvf] at he
    have he' : m + 1 = n + 1 := by exact_mod_cast he
    omega
  have hsub : Set.range f ⊆ (D.coordinateImage A c)ᶜ := by
    rintro _ ⟨n, rfl⟩ ⟨z, hz, he⟩
    change z c = f n at he
    have he0 := D.solution_valuation_eq_zero z hz v hv c
    rw [he, hvf] at he0
    have he' : n + 1 = 0 := by exact_mod_cast he0
    omega
  exact False.elim (((Set.infinite_range_of_injective hf).mono hsub).not_finite h)

/-- Nullstellensatz transfer, stated separately so its only extra
hypothesis (finite A-coordinate images) is visible. It also handles an empty
solution set: the empty product is 1, so complex points are then excluded. -/
theorem isAlgebraic_of_finite_coordinateImages
    (A : Type w') [Field A] [Algebra ℚ k] [Algebra k A]
    [Algebra ℚ A] [IsScalarTower ℚ k A]
    [Algebra.IsAlgebraic ℚ A] [IsAlgClosed A]
    [Algebra k ℂ] [IsScalarTower ℚ k ℂ]
    (hfinite : ∀ c : Coordinate I G, (D.coordinateImage A c).Finite)
    (z : Coordinate I G → ℂ) (hz : D.IsSolution ℂ z) (c : Coordinate I G) :
    IsAlgebraic ℚ (z c) := by
  classical
  let S : Finset A := (hfinite c).toFinset
  let q : Polynomial ℚ := S.prod (minpoly ℚ)
  have hq : q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact minpoly.ne_zero (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  let p : MvPolynomial (Coordinate I G) k :=
    Polynomial.aeval (MvPolynomial.X c) q
  have hpA : p ∈ MvPolynomial.vanishingIdeal k
      (MvPolynomial.zeroLocus A D.equationIdeal) := by
    intro x hx
    have heval : MvPolynomial.aeval x p = Polynomial.aeval (x c) q := by
      simpa [p] using (Polynomial.aeval_algHom_apply
        ((MvPolynomial.aeval x).restrictScalars ℚ)
        (MvPolynomial.X c : MvPolynomial (Coordinate I G) k) q).symm
    rw [heval]
    change Polynomial.aeval (x c) (S.prod (minpoly ℚ)) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero (i := x c)
    · change x c ∈ (hfinite c).toFinset
      simpa using (show x c ∈ D.coordinateImage A c from
        ⟨x, (D.isSolution_iff_mem_zeroLocus A x).mpr hx, rfl⟩)
    · exact minpoly.aeval ℚ (x c)
  have hpRad : p ∈ D.equationIdeal.radical := by
    rwa [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := A)] at hpA
  have hpC : MvPolynomial.aeval z p = 0 :=
    MvPolynomial.radical_le_vanishingIdeal_zeroLocus D.equationIdeal hpRad z
      ((D.isSolution_iff_mem_zeroLocus ℂ z).mp hz)
  have heval : MvPolynomial.aeval z p = Polynomial.aeval (z c) q := by
    simpa [p] using (Polynomial.aeval_algHom_apply
      ((MvPolynomial.aeval z).restrictScalars ℚ)
      (MvPolynomial.X c : MvPolynomial (Coordinate I G) k) q).symm
  exact ⟨q, hq, heval ▸ hpC⟩

/-- Every complex solution of the finite Q1--Q4 system has algebraic
coordinates. This does not assume an analytic construction, existence of an
algebraic solution, or odd order. The coefficient field is algebraic over ℚ. -/
theorem solution_isAlgebraic [CharZero k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] [Algebra k ℂ] [IsScalarTower ℚ k ℂ]
    (z : Coordinate I G → ℂ) (hz : D.IsSolution ℂ z) (c : Coordinate I G) :
    IsAlgebraic ℚ (z c) := by
  let A := AlgebraicClosure k
  have : Algebra.IsAlgebraic ℚ A := Algebra.IsAlgebraic.trans ℚ k A
  exact D.isAlgebraic_of_finite_coordinateImages A
    (D.coordinateImage_finite A) z hz c

end FiniteSystem
end SICLean.L3

#check @MvPolynomial.zeroLocus
#check @MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
#check @PrimeSpectrum.isConstructible_range_comap
#check @IsAlgebraic.restrictScalars
#check @SICLean.L3.FiniteSystem.solution_isAlgebraic
#print SICLean.L3.FiniteSystem.solution_isAlgebraic
