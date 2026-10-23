import SICLean.L5.OddPrimeValues
import SICLean.L5.OddPrimeCharacterAverage

set_option autoImplicit false

/-!
# The finite global Fourier maximum and equality in Lemma 2

The finite maximum argument for the ordinary complex Fourier coefficients. The finite coefficient
range
is [RW-rec, p. 7] and the maximum argument is [RW-rec, p. 9]. [RW26, p. 2, (2)] is the
analytic homothety. The coefficient range is the concrete range of `valuationFourier` on
all stable lattices and all complex characters. Finiteness and existence of a global
maximum are conclusions, using `finiteRepresentatives` and the existing `scaleEquiv`
`value_scale`; they are never hypotheses to the existence theorem. Only the subsequent
equality/propagation lemmas accept an explicit maximality hypothesis, supplied by that
existence theorem. The average lemma includes A=0 and requires a nonempty averaging
family (equivalently positive D). The chain lemma is purely finite and introduces no
import of OddPrimeLatticeChain or OddPrimeCyclic.
-/

noncomputable section

open scoped Classical BigOperators
open SICLean.L3

namespace SICLean.L5.OddPrimeMaximum

open OddPrimeCharacterAverage

section ComplexAverages

variable {ι : Type*}

/-- [RW-rec, p. 9]: equality in a complex average inside the closed disk of radius |A| forces every
summand to equal A. The conclusion also holds when A=0; nonemptiness excludes a zero denominator. -/
theorem average_eq_implies_all_eq (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℂ) (A : ℂ)
    (haverage : A = (s.card : ℂ)⁻¹ * ∑ i ∈ s, a i)
    (hbound : ∀ i ∈ s, ‖a i‖ ≤ ‖A‖) :
    ∀ i ∈ s, a i = A := by
  have hcard : (s.card : ℂ) ≠ 0 := by
    exact_mod_cast hs.card_pos.ne'
  have hsum : ∑ i ∈ s, a i = (s.card : ℂ) * A := by
    rw [haverage, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  have hre : ∀ i ∈ s, (star A * a i).re ≤ ‖A‖ ^ 2 := by
    intro i hi
    calc
      (star A * a i).re ≤ ‖star A * a i‖ := Complex.re_le_norm _
      _ = ‖A‖ * ‖a i‖ := by rw [norm_mul, norm_star]
      _ ≤ ‖A‖ ^ 2 := by nlinarith [hbound i hi, norm_nonneg A]
  have hsumre : ∑ i ∈ s, (star A * a i).re = ∑ _i ∈ s, ‖A‖ ^ 2 := by
    rw [← Complex.re_sum, ← Finset.mul_sum, hsum]
    simp [Complex.mul_re, Complex.normSq_apply, ← Complex.normSq_eq_norm_sq]
    ring
  intro i hi
  have heq := (Finset.sum_eq_sum_iff_of_le hre).mp hsumre i hi
  have hnorm : ‖a i - A‖ ^ 2 ≤ 0 := by
    have hsq : ‖a i‖ ^ 2 ≤ ‖A‖ ^ 2 := by
      nlinarith [hbound i hi, norm_nonneg (a i), norm_nonneg A]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im] at heq hsq ⊢
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [sq_nonneg ‖a i - A‖]))

/-- [RW-rec, p. 9]: the same equality lemma with the displayed denominator D and its actual counting
identity. D>0 is explicit. -/
theorem index_average_eq_implies_all_eq (s : Finset ι) (D : ℕ)
    (hD : 0 < D) (hcard : s.card = D) (a : ι → ℂ) (A : ℂ)
    (haverage : A = (D : ℂ)⁻¹ * ∑ i ∈ s, a i)
    (hbound : ∀ i ∈ s, ‖a i‖ ≤ ‖A‖) :
    ∀ i ∈ s, a i = A := by
  apply average_eq_implies_all_eq s (Finset.card_pos.mp (hcard ▸ hD)) a A
  · simpa only [hcard] using haverage
  · exact hbound

/-- [RW-rec, p. 9]: induction along a finite path of maximum-modulus averages. Each step's
membership supplies nonemptiness of its averaging family. The family members are states, so repeated
complex coefficient values retain their multiplicity as distinct states. -/
theorem finite_chain_constant_of_maximum (coefficient : ι → ℂ) (n : ℕ)
    (path : Fin (n + 1) → ι) (successors : Fin n → Finset ι)
    (hstep : ∀ i : Fin n, path i.succ ∈ successors i)
    (haverage : ∀ i : Fin n,
      coefficient (path i.castSucc) =
        ((successors i).card : ℂ)⁻¹ * ∑ j ∈ successors i, coefficient j)
    (hmaximum : ∀ j : ι, ‖coefficient j‖ ≤ ‖coefficient (path 0)‖) :
    ∀ i : Fin (n + 1), coefficient (path i) = coefficient (path 0) := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    apply average_eq_implies_all_eq (successors i) ⟨path i.succ, hstep i⟩
      coefficient (coefficient (path 0)) _ (fun j _ => hmaximum j) _ (hstep i)
    rw [← ih]
    exact haverage i

end ComplexAverages

section FiniteFourier

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Character transport follows the inverse of the concrete group equivalence, preserving the
character at the transported point. -/
def transportCharacter (e : G ≃+ H) (θ : AddChar G ℂ) : AddChar H ℂ :=
  θ.compAddMonoidHom e.symm.toAddMonoidHom

/-- [RW-rec, p. 9]: finite complex Fourier inversion. The explicit normalization must be nonzero; no
completeness assumption is an input. -/
theorem realFourier_zero_iff [Fintype G] (normalization : ℂ)
    (hnormalization : normalization ≠ 0) (f : G → ℝ) :
    (∀ θ : AddChar G ℂ, realFourier normalization f θ = 0) ↔
      ∀ x : G, f x = 0 := by
  classical
  constructor
  · intro h x
    have hsum (θ : AddChar G ℂ) : ∑ y : G, (f y : ℂ) * (θ y)⁻¹ = 0 := by
      exact (mul_eq_zero.mp (h θ)).resolve_left hnormalization
    have hinversion :
        ∑ θ : AddChar G ℂ, (∑ y : G, (f y : ℂ) * (θ y)⁻¹) * θ x =
          (f x : ℂ) * (Fintype.card G : ℂ) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      calc
        ∑ y : G, ∑ θ : AddChar G ℂ, (f y : ℂ) * (θ y)⁻¹ * θ x =
            ∑ y : G, (f y : ℂ) * ∑ θ : AddChar G ℂ, θ (x - y) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          rw [AddChar.map_sub_eq_div, div_eq_mul_inv]
          ring
        _ = (f x : ℂ) * (Fintype.card G : ℂ) := by
          simp [AddChar.sum_apply_eq_ite, sub_eq_zero]
    rw [show (∑ θ : AddChar G ℂ,
        (∑ y : G, (f y : ℂ) * (θ y)⁻¹) * θ x) = 0 by simp [hsum]] at hinversion
    have hf : (f x : ℂ) = 0 := (mul_eq_zero.mp hinversion.symm).resolve_right
      (by exact_mod_cast Fintype.card_ne_zero (α := G))
    exact_mod_cast hf
  · intro h θ
    simp [realFourier, h]

/-- [RW-rec, p. 9]: invariance under one translation kills a Fourier coefficient whose character is
nontrivial on that translation. The normalization may be arbitrary for this vanishing statement. -/
theorem realFourier_eq_zero_of_translation [Fintype G]
    (normalization : ℂ) (f : G → ℝ) (θ : AddChar G ℂ) (u : G)
    (htranslation : ∀ x : G, f (x + u) = f x) (hθ : θ u ≠ 1) :
    realFourier normalization f θ = 0 := by
  classical
  have hshift : (θ u)⁻¹ * (∑ x : G, (f x : ℂ) * (θ x)⁻¹) =
      ∑ x : G, (f x : ℂ) * (θ x)⁻¹ := by
    calc
      (θ u)⁻¹ * (∑ x : G, (f x : ℂ) * (θ x)⁻¹) =
          ∑ x : G, (f (x + u) : ℂ) * (θ (x + u))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [htranslation x, AddChar.map_add_eq_mul, mul_inv_rev]
        ring
      _ = ∑ x : G, (f x : ℂ) * (θ x)⁻¹ :=
        Equiv.sum_comp (Equiv.addRight u) (fun x : G => (f x : ℂ) * (θ x)⁻¹)
  have hsum : ∑ x : G, (f x : ℂ) * (θ x)⁻¹ = 0 :=
    eq_zero_of_mul_eq_self_left (by simpa using hθ) hshift
  simp [realFourier, hsum]

end FiniteFourier

universe u
variable {K : Type u} [Field K] [NumberField K]

open OddPrimeValues DistributionOrbitGeometry

local instance groupFinite (P : PeriodData K) (I : StablePseudolattice P) :
    Finite (PseudolatticeGroup P I) := (pseudolatticeGroup_finite_card P I).1

local instance groupFintype (P : PeriodData K) (I : StablePseudolattice P) :
    Fintype (PseudolatticeGroup P I) := Fintype.ofFinite _

/-- Actual coefficient values, with no bound or maximum built into the definition, and no
restriction to a preselected representative family. -/
def coefficientRange (P : PeriodData K)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) : Set ℂ :=
  {z | ∃ (I : StablePseudolattice P) (θ : AddChar (PseudolatticeGroup P I) ℂ),
    z = valuationFourier P I v θ}

/-- [RW-rec, p. 7, p. 9]: positive K-homothety transports the actual weight function. Wrapper of
OddPrimeValues.weight_scale, ultimately existing M72.value_scale; no new values or lattices are
chosen. -/
theorem weight_homothety (P : PeriodData K) (I J : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (a : K) (ha : TotallyPositive P a)
    (hJ : J.val = pseudolatticeScale a I.val) (x : PseudolatticeGroup P I) :
    weight P J v (M72.scaleEquiv P I J a (totallyPositive_ne_zero P a ha) hJ x) =
      weight P I v x := by
  exact weight_scale P I J v a ha hJ x

/-- [RW-rec, p. 7, p. 9]: change variables by scaleEquiv. The target character is transported by
lambda inverse, in the same direction as the existing value_scale statement. -/
theorem valuationFourier_homothety (P : PeriodData K) (I J : StablePseudolattice P)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (a : K) (ha : TotallyPositive P a)
    (hJ : J.val = pseudolatticeScale a I.val)
    (θ : AddChar (PseudolatticeGroup P I) ℂ) :
    valuationFourier P J v
      (transportCharacter
        (M72.scaleEquiv P I J a (totallyPositive_ne_zero P a ha) hJ) θ) =
      valuationFourier P I v θ := by
  let e := M72.scaleEquiv P I J a (totallyPositive_ne_zero P a ha) hJ
  unfold valuationFourier
  congr 1
  symm
  apply Fintype.sum_equiv e.toEquiv
  intro x
  change (weight P I v x : ℂ) * (θ x)⁻¹ =
    (weight P J v (M72.scaleEquiv P I J a (totallyPositive_ne_zero P a ha) hJ x) : ℂ) *
      (transportCharacter e θ (e x))⁻¹
  rw [weight_homothety P I J v a ha hJ]
  simp [transportCharacter, e]

/-- [RW-rec, p. 7]: use existing finiteRepresentatives and the finite complex dual of each
representative, then valuationFourier_homothety. This proves finiteness over every stable lattice,
not just a chosen family. -/
theorem finite_coefficient_range (P : PeriodData K)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) :
    (coefficientRange P v).Finite := by
  classical
  obtain ⟨n, _hn, reps, hcover⟩ := finiteRepresentatives P
  let coefficients : ((i : Fin n) × AddChar (PseudolatticeGroup P (reps i)) ℂ) → ℂ :=
    fun iθ => valuationFourier P (reps iθ.1) v iθ.2
  apply (Set.finite_range coefficients).subset
  rintro z ⟨I, θ, rfl⟩
  obtain ⟨i, a, ha, hI⟩ := hcover I
  let e := M72.scaleEquiv P (reps i) I a (totallyPositive_ne_zero P a ha) hI
  let χ := θ.compAddMonoidHom e.toAddMonoidHom
  have hχ : transportCharacter e χ = θ := by
    ext x
    simp [transportCharacter, χ]
  refine ⟨⟨i, χ⟩, ?_⟩
  change valuationFourier P (reps i) v χ = valuationFourier P I v θ
  rw [← hχ]
  exact (valuationFourier_homothety P (reps i) I v a ha hI χ).symm

/-- [RW-rec, p. 9]: an attained maximum over all stable lattices and characters. Neither a uniform
bound nor a maximum is an assumed premise; existence follows from finite_coefficient_range and a
nonempty lattice. -/
theorem exists_global_maximum (P : PeriodData K)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) :
    ∃ (I : StablePseudolattice P) (θ : AddChar (PseudolatticeGroup P I) ℂ),
      ∀ (J : StablePseudolattice P) (χ : AddChar (PseudolatticeGroup P J) ℂ),
        ‖valuationFourier P J v χ‖ ≤ ‖valuationFourier P I v θ‖ := by
  classical
  let s := (finite_coefficient_range P v).toFinset
  have hs : s.Nonempty := by
    obtain ⟨I⟩ := stablePseudolattice_nonempty P
    refine ⟨valuationFourier P I v 0, ?_⟩
    exact ((finite_coefficient_range P v).mem_toFinset).mpr ⟨I, 0, rfl⟩
  obtain ⟨z, hz, hmax⟩ := s.exists_max_image (fun z : ℂ => ‖z‖) hs
  obtain ⟨I, θ, hval⟩ := ((finite_coefficient_range P v).mem_toFinset).mp hz
  refine ⟨I, θ, ?_⟩
  intro J χ
  rw [← hval]
  apply hmax
  exact ((finite_coefficient_range P v).mem_toFinset).mpr ⟨J, χ, rfl⟩

/-- [RW-rec, p. 9]: one use of Lemma 2 leaves every compatible successor equal to the same global
maximum A. Compatibility implies triviality on the source kernel; extension_card gives D, and
inclusionIndex_pos gives D>0. The bound covers the given successor J even if J is not a chosen
homothety representative. -/
theorem compatible_coefficient_eq_of_maximum (P : PeriodData K)
    (I J : StablePseudolattice P) (hIJ : I.val ≤ J.val)
    (hperiod : ∀ z ∈ J.val, (P.epsilon - 1) * z ∈ I.val)
    (v : AddValuation Galois.Qbar (WithTop ℝ))
    (θ : AddChar (PseudolatticeGroup P I) ℂ) (A : ℂ)
    (hA : valuationFourier P I v θ = A)
    (hmaximum : ∀ (L : StablePseudolattice P)
      (ψ : AddChar (PseudolatticeGroup P L) ℂ), ‖valuationFourier P L v ψ‖ ≤ ‖A‖)
    (χ : AddChar (PseudolatticeGroup P J) ℂ)
    (hcompatible : ∀ x : PseudolatticeGroup P I,
      χ (periodProject P I J hIJ x) = θ x) :
    valuationFourier P J v χ = A := by
  have hθ : ∀ x ∈ (periodProject P I J hIJ).ker, θ x = 1 := by
    intro x hx
    rw [← hcompatible x, AddMonoidHom.mem_ker.mp hx, χ.map_zero_eq_one]
  apply index_average_eq_implies_all_eq
    (extensionFinset (periodProject P I J hIJ) θ) (inclusionIndex I.val J.val)
    (inclusionIndex_pos P I J hIJ)
    (periodProject_extension_card P I J hIJ hperiod θ hθ)
    (valuationFourier P J v) A
  · rw [← hA]
    exact lemma2_average P I J hIJ hperiod v θ hθ
  · intro ψ _
    exact hmaximum J ψ
  · exact (mem_extensionFinset _ _ _).mpr hcompatible

/-- [RW-rec, p. 9]: Theorem 4 supplies the translation invariance; faithfulness on a nontrivial
primary subgroup supplies hθ in the caller. This wrapper assumes neither cyclicity nor any unit
conclusion itself. -/
theorem valuationFourier_eq_zero_of_translation (P : PeriodData K)
    (I : StablePseudolattice P) (v : AddValuation Galois.Qbar (WithTop ℝ))
    (θ : AddChar (PseudolatticeGroup P I) ℂ) (u : PseudolatticeGroup P I)
    (htranslation : ∀ x : PseudolatticeGroup P I,
      weight P I v (x + u) = weight P I v x) (hθ : θ u ≠ 1) :
    valuationFourier P I v θ = 0 := by
  exact realFourier_eq_zero_of_translation _ _ θ u htranslation hθ

/-- [RW-rec, p. 9]: actual-weight Fourier inversion, with the positive N of PeriodData justifying
the nonzero inverse-sqrt normalization. -/
theorem weight_zero_iff_fourier_zero (P : PeriodData K)
    (I : StablePseudolattice P) (v : AddValuation Galois.Qbar (WithTop ℝ)) :
    (∀ x : PseudolatticeGroup P I, weight P I v x = 0) ↔
      ∀ θ : AddChar (PseudolatticeGroup P I) ℂ, valuationFourier P I v θ = 0 := by
  exact (realFourier_zero_iff _ (inv_ne_zero (by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast P.N_pos)).ne')) _).symm

/-- [RW-rec, p. 9]: once an attained global maximum is zero, every coefficient on every stable
lattice vanishes. -/
theorem all_fourier_zero_of_maximum_zero (P : PeriodData K)
    (v : AddValuation Galois.Qbar (WithTop ℝ))
    (I : StablePseudolattice P) (θ : AddChar (PseudolatticeGroup P I) ℂ)
    (hmaximum : ∀ (J : StablePseudolattice P)
      (χ : AddChar (PseudolatticeGroup P J) ℂ),
      ‖valuationFourier P J v χ‖ ≤ ‖valuationFourier P I v θ‖)
    (hzero : valuationFourier P I v θ = 0) :
    ∀ (J : StablePseudolattice P) (χ : AddChar (PseudolatticeGroup P J) ℂ),
      valuationFourier P J v χ = 0 := by
  intro J χ
  apply norm_eq_zero.mp
  have hbound := hmaximum J χ
  rw [hzero, norm_zero] at hbound
  exact le_antisymm hbound (norm_nonneg _)

/-- [RW-rec, p. 9]: finish the maximum argument by finite inversion. The arithmetic input is exactly
hzero for the chosen maximum; this theorem does not silently assume all E-values are units. -/
theorem all_weights_zero_of_maximum_zero (P : PeriodData K)
    (v : AddValuation Galois.Qbar (WithTop ℝ))
    (I : StablePseudolattice P) (θ : AddChar (PseudolatticeGroup P I) ℂ)
    (hmaximum : ∀ (J : StablePseudolattice P)
      (χ : AddChar (PseudolatticeGroup P J) ℂ),
      ‖valuationFourier P J v χ‖ ≤ ‖valuationFourier P I v θ‖)
    (hzero : valuationFourier P I v θ = 0) :
    ∀ (J : StablePseudolattice P) (x : PseudolatticeGroup P J), weight P J v x = 0 := by
  intro J
  exact (weight_zero_iff_fourier_zero P J v).mpr
    (all_fourier_zero_of_maximum_zero P v I θ hmaximum hzero J)

#check @L3.finiteRepresentatives
#check @exists_global_maximum
#check @compatible_coefficient_eq_of_maximum
#print coefficientRange
#print transportCharacter

end SICLean.L5.OddPrimeMaximum
