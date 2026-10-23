import SICLean.L4.ModularPhi
import SICLean.L4.ModularCocycleMatrixAux
import SICLean.L4.ModularCocycleAux

set_option autoImplicit false

/-!
# Finite inversion and dedicated inverse reflection

These helpers depend only on the already constructed modular Φ and acyclic
matrix/filter auxiliaries.  The dedicated inverse reflection permutes the
factors by complementary residue classes and then applies φ self-duality.
Its η identity is proved for the actual η quotients using conjugation.
The reflection exponential follows from finite Faddeev inversion.  Its η
normalization is supplied separately, so this module does not import the
modular reflection statements that use it.
-/
noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4.ModularCocycleReflectionAux

lemma sqrt_inv_of_mem_slitPlane {T : ℂ} (hT : T ∈ Complex.slitPlane)
    (hi : T⁻¹ ∈ Complex.slitPlane) :
    Complex.sqrt T⁻¹ = (Complex.sqrt T)⁻¹ := by
  have hs : Complex.sqrt T ^ 2 = T := by
    simpa [sq] using EtaMultiplierAux.sqrt_mul_self T
  have hsi : Complex.sqrt T⁻¹ ^ 2 = T⁻¹ := by
    simpa [sq] using EtaMultiplierAux.sqrt_mul_self T⁻¹
  have he : Complex.sqrt T⁻¹ ^ 2 = ((Complex.sqrt T)⁻¹) ^ 2 := by
    rw [inv_pow, hs, hsi]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact h
  · have ha := sqrt_re_pos_of_mem_slitPlane hi
    have hb := admissibleB_inv (Complex.sqrt T) (sqrt_re_pos_of_mem_slitPlane hT)
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re] at hr
    dsimp [AdmissibleB] at hb
    linarith

lemma inverse_reflection_index (M N : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : N 1 0 = M 1 0) (hd : N 1 1 = M 0 0)
    (m n : ℤ) (j : ℕ) (hj : j ∈ Finset.range (M 1 0).toNat) :
    modularPhiIndex N (1 - n) (1 - m)
      ((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat) =
    M 0 0 - 1 + M 0 0 * modularPhiIndex M m n j - M 0 1 * (m + (j : ℤ)) := by
  have hr := (modularPhiResidue_permutation M hM m n).1 j
  have hci : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.le
  have hrnat : ((modularPhiResidue M m n j).toNat : ℤ) =
      modularPhiResidue M m n j := Int.toNat_of_nonneg hr.1
  have hj' : (j : ℤ) < M 1 0 := by
    have := Finset.mem_range.mp hj
    omega
  have hcomp : (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℤ) =
      M 1 0 - 1 - modularPhiResidue M m n j := by omega
  unfold modularPhiIndex
  rw [hc, hd, hcomp]
  apply (Int.ediv_eq_iff_of_pos hM).mpr
  have hnum : M 0 0 * (1 - n + (M 1 0 - 1 - modularPhiResidue M m n j)) - (1 - m) =
      (M 0 0 - 1 + M 0 0 * ((M 1 1 * (m + (j : ℤ)) - n) / M 1 0) -
        M 0 1 * (m + (j : ℤ))) * M 1 0 + (M 1 0 - 1 - (j : ℤ)) := by
    unfold modularPhiResidue modularPhiIndex
    linear_combination -(m + (j : ℤ)) * det_coe_int M
  rw [hnum]
  constructor <;> omega

lemma prod_inverse_reflection_reindex (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (g : ℕ → ℂ) :
    (∏ j ∈ Finset.range (M 1 0).toNat,
      g ((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat)) =
    ∏ j ∈ Finset.range (M 1 0).toNat, g j := by
  classical
  obtain ⟨_, himage, hinj⟩ := modularPhiResidue_permutation M hM m n
  calc
    _ = ∏ j ∈ (Finset.range (M 1 0).toNat).image
        (fun j => (modularPhiResidue M m n j).toNat), g ((M 1 0).toNat - 1 - j) :=
      (Finset.prod_image hinj).symm
    _ = ∏ j ∈ Finset.range (M 1 0).toNat, g ((M 1 0).toNat - 1 - j) := by rw [himage]
    _ = _ := Finset.prod_range_reflect g _

lemma inverse_reflection_input (M N : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : N 1 0 = M 1 0) (hd : N 1 1 = M 0 0)
    (m n : ℤ) (j : ℕ) (hj : j ∈ Finset.range (M 1 0).toNat)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    modularPhiFactorInput N (1 - n) (1 - m)
      ((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat)
      (z / etaDenom M τ) (-etaMobius M τ) =
      (modularPhiFactorInput M m n j z τ + 1) / etaDenom M τ - 1 := by
  have hr := (modularPhiResidue_permutation M hM m n).1 j
  have hci : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.le
  have hrnat : ((modularPhiResidue M m n j).toNat : ℤ) =
      modularPhiResidue M m n j := Int.toNat_of_nonneg hr.1
  have hcomp : (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℤ) =
      M 1 0 - 1 - modularPhiResidue M m n j := by omega
  have hcompC : (((M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat : ℕ) : ℂ) =
      (M 1 0 : ℂ) - 1 - (modularPhiResidue M m n j : ℂ) := by
    exact_mod_cast hcomp
  have hidx := inverse_reflection_index M N hM hc hd m n j hj
  have hT := etaDenom_ne_zero_of_mem M hτ
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by
    exact_mod_cast det_coe_int M
  simp only [modularPhiFactorInput, hidx, hcompC]
  unfold modularPhiResidue
  push_cast
  unfold etaMobius
  field_simp [hT]
  unfold etaDenom
  linear_combination (((m : ℂ) + (j : ℂ)) * τ +
    (modularPhiIndex M m n j : ℂ) + 1) * hdet

lemma inverse_reflection_pointwise (M N : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hc : N 1 0 = M 1 0) (hd : N 1 1 = M 0 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hT : etaDenom N (-etaMobius M τ) = (etaDenom M τ)⁻¹)
    (hN : -etaMobius M τ ∈ modularPhiDomain N) :
    modularPhi N (1 - n) (1 - m) (z / etaDenom M τ) (-etaMobius M τ) =
      modularPhi M m n z τ := by
  have hb := modularPhi_sqrt_admissible M τ hτ
  have hsq : Complex.sqrt (etaDenom N (-etaMobius M τ)) =
      (Complex.sqrt (etaDenom M τ))⁻¹ := by
    rw [hT]
    apply sqrt_inv_of_mem_slitPlane hτ
    rw [← hT]
    exact hN
  let f : ℕ → ℕ := fun j =>
    (M 1 0).toNat - 1 - (modularPhiResidue M m n j).toNat
  have hfac : ∀ j ∈ Finset.range (M 1 0).toNat,
      phiExtended (modularPhiFactorPoint N (1 - n) (1 - m) (f j)
          (z / etaDenom M τ) (-etaMobius M τ)).1
        (modularPhiFactorPoint N (1 - n) (1 - m) (f j)
          (z / etaDenom M τ) (-etaMobius M τ)).2 =
      phiExtended (modularPhiFactorPoint M m n j z τ).1
        (modularPhiFactorPoint M m n j z τ).2 := by
    intro j hj
    have hinput := inverse_reflection_input M N hM hc hd m n j hj z τ hτ
    have harg : (modularPhiFactorPoint N (1 - n) (1 - m) (f j)
          (z / etaDenom M τ) (-etaMobius M τ)).2 =
        (modularPhiFactorPoint M m n j z τ).2 := by
      simp only [modularPhiFactorPoint, modularPhiSArgument, hsq, f, hinput]
      field_simp [hb.2.2, etaDenom_ne_zero_of_mem M hτ]
      linear_combination (2 * (modularPhiFactorInput M m n j z τ + 1)) * hb.2.1
    rw [harg]
    change phiExtended (Complex.sqrt (etaDenom N (-etaMobius M τ))) _ =
      phiExtended (Complex.sqrt (etaDenom M τ)) _
    rw [hsq]
    exact (phiExtended_self_dual _ _ hb.1).symm
  unfold modularPhi
  rw [hc]
  rw [← prod_inverse_reflection_reindex M hM m n
    (fun j => phiExtended
      (modularPhiFactorPoint N (1 - n) (1 - m) j
        (z / etaDenom M τ) (-etaMobius M τ)).1
      (modularPhiFactorPoint N (1 - n) (1 - m) j
        (z / etaDenom M τ) (-etaMobius M τ)).2)]
  exact Finset.prod_congr rfl hfac

lemma e_neg_conj (z : ℂ) : e (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (e z) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma qPochhammer_conj (a q : ℂ) :
    qPochhammer ((starRingEnd ℂ) a) ((starRingEnd ℂ) q) =
      (starRingEnd ℂ) (qPochhammer a q) := by
  unfold qPochhammer
  rw [Function.LeftInverse.map_tprod (fun n : ℕ => 1 - a * q ^ n)
    Complex.continuous_conj Complex.continuous_conj
    (fun z : ℂ => Complex.conj_conj z)]
  simp only [map_sub, map_one, map_mul, map_pow]

lemma eta_neg_conj (z : ℂ) :
    ModularForm.eta (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (ModularForm.eta z) := by
  rw [eta_eq_e_mul_qPochhammer, eta_eq_e_mul_qPochhammer, map_mul,
    e_neg_conj, qPochhammer_conj]
  congr 1
  rw [← e_neg_conj]
  congr 1
  simp only [map_div₀, map_ofNat, neg_div]

lemma sqrt_inv_conj {T : ℂ} (hT : T ∈ Complex.slitPlane)
    (hi : ((starRingEnd ℂ) T)⁻¹ ∈ Complex.slitPlane) :
    Complex.sqrt ((starRingEnd ℂ) T)⁻¹ =
      ((starRingEnd ℂ) (Complex.sqrt T))⁻¹ := by
  have hs : Complex.sqrt T ^ 2 = T := by
    simpa [sq] using EtaMultiplierAux.sqrt_mul_self T
  have hsi : Complex.sqrt ((starRingEnd ℂ) T)⁻¹ ^ 2 = ((starRingEnd ℂ) T)⁻¹ := by
    simpa [sq] using EtaMultiplierAux.sqrt_mul_self ((starRingEnd ℂ) T)⁻¹
  have he : Complex.sqrt ((starRingEnd ℂ) T)⁻¹ ^ 2 =
      (((starRingEnd ℂ) (Complex.sqrt T))⁻¹) ^ 2 := by
    rw [inv_pow, ← map_pow, hs, hsi]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact h
  · have ha := sqrt_re_pos_of_mem_slitPlane hi
    have hb := admissibleB_inv ((starRingEnd ℂ) (Complex.sqrt T))
      (by simpa only [AdmissibleB, Complex.conj_re] using
        sqrt_re_pos_of_mem_slitPlane hT)
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re] at hr
    dsimp [AdmissibleB] at hb
    linarith

lemma etaDenom_conj (M : SL(2, ℤ)) (z : ℂ) :
    etaDenom M ((starRingEnd ℂ) z) = (starRingEnd ℂ) (etaDenom M z) := by
  simp only [etaDenom, map_add, map_mul, map_intCast]

lemma etaMobius_conj (M : SL(2, ℤ)) (z : ℂ) :
    etaMobius M ((starRingEnd ℂ) z) = (starRingEnd ℂ) (etaMobius M z) := by
  simp only [etaMobius, etaDenom_conj, map_div₀, map_add, map_mul, map_intCast]

lemma etaMultiplier_inverse_reflection_of_matrix (M N : SL(2, ℤ)) (hM : 0 < M 1 0)
    (hmat : (N : Matrix (Fin 2) (Fin 2) ℤ) = !![M 1 1, M 0 1; M 1 0, M 0 0]) :
    etaMultiplier N = etaMultiplier M := by
  have hN : 0 < N 1 0 := by simpa [hmat] using hM
  let τ : ℍ := M • UpperHalfPlane.I
  let ρ : ℍ := ⟨-(starRingEnd ℂ) (τ : ℂ), by simpa using τ.im_pos⟩
  have hτ : (τ : ℂ) = etaMobius M UpperHalfPlane.I := coe_smul_eq_etaMobius M _
  have hden0 : etaDenom M ((starRingEnd ℂ) (UpperHalfPlane.I : ℂ)) ≠ 0 := by
    rw [etaDenom_conj]
    exact (map_ne_zero (starRingEnd ℂ)).mpr (etaDenom_ne_zero M hM _)
  have hpair := ModularCocycleMatrixAux.inverse_reflection_denom M N hmat
    ((starRingEnd ℂ) (UpperHalfPlane.I : ℂ)) hden0
  have hden : etaDenom N (ρ : ℂ) =
      ((starRingEnd ℂ) (etaDenom M UpperHalfPlane.I))⁻¹ := by
    simpa only [ρ, hτ, etaMobius_conj, etaDenom_conj] using hpair.1
  have hact : etaMobius N (ρ : ℂ) = -(starRingEnd ℂ) (UpperHalfPlane.I : ℂ) := by
    simpa only [ρ, hτ, etaMobius_conj] using hpair.2
  have hs : Complex.sqrt (etaDenom N (ρ : ℂ)) =
      ((starRingEnd ℂ) (Complex.sqrt (etaDenom M UpperHalfPlane.I)))⁻¹ := by
    rw [hden]
    apply sqrt_inv_conj (etaDenom_mem_slitPlane M hM _)
    rw [← hden]
    exact etaDenom_mem_slitPlane N hN ρ
  have hformula := eta_smul_eq N hN ρ
  rw [coe_smul_eq_etaMobius, hact, eta_neg_conj, hs] at hformula
  have hη : ModularForm.eta (ρ : ℂ) = (starRingEnd ℂ) (ModularForm.eta (τ : ℂ)) :=
    eta_neg_conj (τ : ℂ)
  rw [hη] at hformula
  have hMformula := congrArg (starRingEnd ℂ) (eta_smul_eq M hM UpperHalfPlane.I)
  simp only [map_mul] at hMformula
  change (starRingEnd ℂ) (ModularForm.eta (τ : ℂ)) = _ at hMformula
  rw [hMformula] at hformula
  have hηne : (starRingEnd ℂ) (ModularForm.eta (UpperHalfPlane.I : ℂ)) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr (ModularForm.eta_ne_zero UpperHalfPlane.I.im_pos)
  have hsne : (starRingEnd ℂ) (Complex.sqrt (etaDenom M UpperHalfPlane.I)) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr
      (sqrt_ne_zero_of_mem_slitPlane (etaDenom_mem_slitPlane M hM _))
  have hprod : etaMultiplier N * (starRingEnd ℂ) (etaMultiplier M) = 1 := by
    apply mul_right_cancel₀ hηne
    calc
      (etaMultiplier N * (starRingEnd ℂ) (etaMultiplier M)) *
          (starRingEnd ℂ) (ModularForm.eta (UpperHalfPlane.I : ℂ)) =
        etaMultiplier N * ((starRingEnd ℂ)
          (Complex.sqrt (etaDenom M UpperHalfPlane.I)))⁻¹ *
          ((starRingEnd ℂ) (etaMultiplier M) *
            (starRingEnd ℂ) (Complex.sqrt (etaDenom M UpperHalfPlane.I)) *
            (starRingEnd ℂ) (ModularForm.eta (UpperHalfPlane.I : ℂ))) := by
          field_simp [hsne]
      _ = (starRingEnd ℂ) (ModularForm.eta (UpperHalfPlane.I : ℂ)) := hformula.symm
      _ = 1 * (starRingEnd ℂ) (ModularForm.eta (UpperHalfPlane.I : ℂ)) := by ring
  rw [← Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one
    (etaMultiplier_pow_twentyFour M hM) (by norm_num))] at hprod
  exact (mul_inv_eq_one₀ (etaMultiplier_ne_zero M hM)).mp hprod

/-- The explicit exponential obtained by finite Faddeev inversion. -/
def reflectionExponent (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (M 1 0).toNat,
    (Complex.I * (Real.pi : ℂ) * (modularPhiFactorPoint M r n j z τ).2 ^ 2 +
      Complex.I * (Real.pi : ℂ) *
        (Complex.sqrt (etaDenom M τ) ^ 2 + ((Complex.sqrt (etaDenom M τ))⁻¹) ^ 2) / 12)

lemma reflection_index (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (j : ℕ) (hj : j ∈ Finset.range (M 1 0).toNat) :
    modularPhiIndex M (1 - r) (1 - n) ((M 1 0).toNat - 1 - j) =
      M 1 1 - 1 - modularPhiIndex M r n j := by
  have hr := (modularPhiResidue_permutation M hM r n).1 j
  have hci : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.le
  have hcomp : (((M 1 0).toNat - 1 - j : ℕ) : ℤ) = M 1 0 - 1 - (j : ℤ) := by
    have := Finset.mem_range.mp hj
    omega
  unfold modularPhiIndex
  rw [hcomp, Int.ediv_eq_iff_of_pos hM]
  have hnum : M 1 1 * (1 - r + (M 1 0 - 1 - (j : ℤ))) - (1 - n) =
      (M 1 1 - 1 - ((M 1 1 * (r + (j : ℤ)) - n) / M 1 0)) * M 1 0 +
        (M 1 0 - 1 - modularPhiResidue M r n j) := by
    unfold modularPhiResidue modularPhiIndex
    ring
  rw [hnum]
  constructor <;> omega

lemma reflection_argument (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (j : ℕ) (hj : j ∈ Finset.range (M 1 0).toNat)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (modularPhiFactorPoint M (1 - r) (1 - n) ((M 1 0).toNat - 1 - j) (-z) τ).2 =
      -(modularPhiFactorPoint M r n j z τ).2 := by
  have hci : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.le
  have hcomp : (((M 1 0).toNat - 1 - j : ℕ) : ℤ) = M 1 0 - 1 - (j : ℤ) := by
    have := Finset.mem_range.mp hj
    omega
  have hcompC : (((M 1 0).toNat - 1 - j : ℕ) : ℂ) = (M 1 0 : ℂ) - 1 - (j : ℂ) := by
    exact_mod_cast hcomp
  have hidx := reflection_index M hM r n j hj
  have hinput : modularPhiFactorInput M (1 - r) (1 - n)
      ((M 1 0).toNat - 1 - j) (-z) τ = etaDenom M τ - 1 -
      modularPhiFactorInput M r n j z τ := by
    simp only [modularPhiFactorInput, hidx, hcompC, etaDenom]
    push_cast
    ring
  have hb := modularPhi_sqrt_admissible M τ hτ
  simp only [modularPhiFactorPoint, modularPhiSArgument, hinput]
  field_simp [hb.2.2]
  linear_combination -2 * hb.2.1

lemma reflection_exponential_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M r n w τ * modularPhi M (1 - r) (1 - n) (-w) τ)
      =ᶠ[𝓝[≠] z] (fun w => Complex.exp (reflectionExponent M r n w τ)) := by
  classical
  have hb := modularPhi_sqrt_admissible M τ hτ
  let A : ℕ → ℂ → ℂ := fun j w => (modularPhiFactorPoint M r n j w τ).2
  have hfac : ∀ j ∈ Finset.range (M 1 0).toNat,
      ∀ᶠ w : ℂ in 𝓝[≠] z,
      phiExtended (Complex.sqrt (etaDenom M τ)) (A j w) *
        phiExtended (Complex.sqrt (etaDenom M τ)) (-A j w) =
      Complex.exp (Complex.I * (Real.pi : ℂ) * A j w ^ 2 +
        Complex.I * (Real.pi : ℂ) *
          (Complex.sqrt (etaDenom M τ) ^ 2 + ((Complex.sqrt (etaDenom M τ))⁻¹) ^ 2) / 12) := by
    intro j _
    have hlin (w : ℂ) : A j w = Complex.I / Complex.sqrt (etaDenom M τ) * w + A j 0 := by
      dsimp [A, modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput]
      ring
    have hinj : Function.Injective (A j) := by
      intro x y h
      rw [hlin x, hlin y] at h
      exact mul_left_cancel₀ (div_ne_zero Complex.I_ne_zero hb.2.2) (add_right_cancel h)
    have ht : Tendsto (A j) (𝓝[≠] z) (𝓝[≠] A j z) := by
      have hcont : ContinuousAt (A j) z := by
        have heq : A j = fun w => Complex.I / Complex.sqrt (etaDenom M τ) * w + A j 0 := funext hlin
        rw [heq]
        fun_prop
      apply hcont.continuousWithinAt.tendsto_nhdsWithin
      intro w hw h
      exact hw (hinj h)
    exact ht.eventually (phiExtended_inversion _ (A j z) hb.1)
  have hall : ∀ᶠ w : ℂ in 𝓝[≠] z,
      ∀ j ∈ Finset.range (M 1 0).toNat,
      phiExtended (Complex.sqrt (etaDenom M τ)) (A j w) *
        phiExtended (Complex.sqrt (etaDenom M τ)) (-A j w) =
      Complex.exp (Complex.I * (Real.pi : ℂ) * A j w ^ 2 +
        Complex.I * (Real.pi : ℂ) *
          (Complex.sqrt (etaDenom M τ) ^ 2 + ((Complex.sqrt (etaDenom M τ))⁻¹) ^ 2) / 12) :=
    ((Finset.range (M 1 0).toNat).finite_toSet.eventually_all.mpr hfac)
  filter_upwards [hall] with w hw
  have hprod : modularPhi M (1 - r) (1 - n) (-w) τ =
      ∏ j ∈ Finset.range (M 1 0).toNat,
        phiExtended (Complex.sqrt (etaDenom M τ)) (-A j w) := by
    unfold modularPhi
    rw [← Finset.prod_range_reflect
      (fun j => phiExtended (modularPhiFactorPoint M (1 - r) (1 - n) j (-w) τ).1
        (modularPhiFactorPoint M (1 - r) (1 - n) j (-w) τ).2) (M 1 0).toNat]
    apply Finset.prod_congr rfl
    intro j hj
    rw [reflection_argument M hM r n j hj w τ hτ]
    rfl
  rw [hprod]
  change (∏ j ∈ Finset.range (M 1 0).toNat,
    phiExtended (Complex.sqrt (etaDenom M τ)) (A j w)) * _ = _
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl hw, ← Complex.exp_sum]
  rfl

lemma sum_range_natCast (N : ℕ) :
    (∑ j ∈ Finset.range N, (j : ℂ)) = (N : ℂ) * ((N : ℂ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_index (M : SL(2, ℤ)) (hM : 0 < M 1 0) (r n : ℤ) :
    (∑ j ∈ Finset.range (M 1 0).toNat, (modularPhiIndex M r n j : ℂ)) =
      (M 1 1 : ℂ) * (r : ℂ) - (n : ℂ) +
        ((M 1 1 : ℂ) - 1) * ((M 1 0 : ℂ) - 1) / 2 := by
  classical
  obtain ⟨hr, himage, hinj⟩ := modularPhiResidue_permutation M hM r n
  have hc : ((M 1 0).toNat : ℂ) = (M 1 0 : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hM.le
  have hsumres : (∑ j ∈ Finset.range (M 1 0).toNat,
      (modularPhiResidue M r n j : ℂ)) =
      ∑ j ∈ Finset.range (M 1 0).toNat, (j : ℂ) := by
    calc
      _ = ∑ j ∈ Finset.range (M 1 0).toNat,
          ((modularPhiResidue M r n j).toNat : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _
        exact_mod_cast (Int.toNat_of_nonneg (hr j).1).symm
      _ = ∑ j ∈ (Finset.range (M 1 0).toNat).image
          (fun j => (modularPhiResidue M r n j).toNat), (j : ℂ) :=
        (Finset.sum_image hinj).symm
      _ = _ := by rw [himage]
  have hsumid : (∑ j ∈ Finset.range (M 1 0).toNat,
      (modularPhiResidue M r n j : ℂ)) =
      (M 1 1 : ℂ) * ((M 1 0 : ℂ) * (r : ℂ) +
        ∑ j ∈ Finset.range (M 1 0).toNat, (j : ℂ)) -
      (M 1 0 : ℂ) * (∑ j ∈ Finset.range (M 1 0).toNat,
        (modularPhiIndex M r n j : ℂ)) - (M 1 0 : ℂ) * (n : ℂ) := by
    simp only [modularPhiResidue, Int.cast_sub, Int.cast_mul, Int.cast_add,
      Int.cast_natCast, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc]
  rw [sum_range_natCast, hc] at hsumid hsumres
  have hcne : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  apply mul_left_cancel₀ hcne
  linear_combination hsumid - hsumres

lemma reflection_chart_cross_mul_of_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (κ κ' : ℕ → ℤ) (p : ℂ × ℂ)
    (hp : p ∈ modularPhiChartDomain M r n κ)
    (hp' : (-p.1, p.2) ∈ modularPhiChartDomain M (1 - r) (1 - n) κ')
    (F : ℂ → ℂ) (hF : ContinuousAt F p.1)
    (hfg : (fun w => modularPhi M r n w p.2 *
      modularPhi M (1 - r) (1 - n) (-w) p.2) =ᶠ[𝓝[≠] p.1] F) :
    modularPhiChartNumerator M r n κ p.1 p.2 *
        modularPhiChartNumerator M (1 - r) (1 - n) κ' (-p.1) p.2 =
      F p.1 * modularPhiChartDenominator M r n κ p.1 p.2 *
        modularPhiChartDenominator M (1 - r) (1 - n) κ' (-p.1) p.2 := by
  have hA := modularPhiChart_analytic M hM r n κ
  have hA' := modularPhiChart_analytic M hM (1 - r) (1 - n) κ'
  have he : AnalyticAt ℂ (fun w : ℂ => (w, p.2)) p.1 := analyticAt_id.prod analyticAt_const
  have he' : AnalyticAt ℂ (fun w : ℂ => (-w, p.2)) p.1 :=
    analyticAt_id.neg.prod analyticAt_const
  have hN := (hA.1 p hp).comp he
  have hD := (hA.2 p hp).comp he
  have hN' := (hA'.1 (-p.1, p.2) hp').comp (f := fun w : ℂ => (-w, p.2)) (x := p.1) he'
  have hD' := (hA'.2 (-p.1, p.2) hp').comp (f := fun w : ℂ => (-w, p.2)) (x := p.1) he'
  have hFreq := modularPhiChartDenominator_frequently_ne_zero M hM r n κ p hp
  have hFreq' : ∃ᶠ w : ℂ in 𝓝 p.1,
      modularPhiChartDenominator M (1 - r) (1 - n) κ' (-w) p.2 ≠ 0 := by
    have hf := frequently_ne_zero_comp_affine (α := (-1 : ℂ)) (β := 0)
      (z₀ := p.1) (a := -p.1) (by norm_num : (-1 : ℂ) ≠ 0)
      (modularPhiChartDenominator_frequently_ne_zero M hM (1 - r) (1 - n) κ'
        (-p.1, p.2) hp') (by ring)
    simpa only [neg_one_mul, add_zero] using hf
  have hDev : ∀ᶠ w : ℂ in 𝓝[≠] p.1,
      modularPhiChartDenominator M r n κ w p.2 ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hD.meromorphicAt).mp
      (meromorphicOrderAt_ne_top_of_analytic_frequently_ne_zero hD hFreq)
  have hD'ev : ∀ᶠ w : ℂ in 𝓝[≠] p.1,
      modularPhiChartDenominator M (1 - r) (1 - n) κ' (-w) p.2 ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hD'.meromorphicAt).mp
      (meromorphicOrderAt_ne_top_of_analytic_frequently_ne_zero hD' hFreq')
  have hchart : ∀ᶠ w : ℂ in 𝓝[≠] p.1, (w, p.2) ∈ modularPhiChartDomain M r n κ :=
    nhdsWithin_le_nhds (he.continuousAt.preimage_mem_nhds
      ((modularPhiChartDomain_isOpen M r n κ).mem_nhds hp))
  have hchart' : ∀ᶠ w : ℂ in 𝓝[≠] p.1,
      (-w, p.2) ∈ modularPhiChartDomain M (1 - r) (1 - n) κ' :=
    nhdsWithin_le_nhds (he'.continuousAt.preimage_mem_nhds
      ((modularPhiChartDomain_isOpen M (1 - r) (1 - n) κ').mem_nhds hp'))
  have hcleared : (fun w => modularPhiChartNumerator M r n κ w p.2 *
      modularPhiChartNumerator M (1 - r) (1 - n) κ' (-w) p.2) =ᶠ[𝓝[≠] p.1]
      (fun w => F w * modularPhiChartDenominator M r n κ w p.2 *
        modularPhiChartDenominator M (1 - r) (1 - n) κ' (-w) p.2) := by
    filter_upwards [hfg, hDev, hD'ev, hchart, hchart'] with w hw hDw hD'w hκw hκ'w
    rw [modularPhi_eq_chart M hM r n κ (w, p.2) hκw,
      modularPhi_eq_chart M hM (1 - r) (1 - n) κ' (-w, p.2) hκ'w] at hw
    change modularPhiChartNumerator M r n κ w p.2 /
      modularPhiChartDenominator M r n κ w p.2 *
      (modularPhiChartNumerator M (1 - r) (1 - n) κ' (-w) p.2 /
        modularPhiChartDenominator M (1 - r) (1 - n) κ' (-w) p.2) = F w at hw
    field_simp [hDw, hD'w] at hw
    linear_combination hw
  exact ModularCocycleAux.eq_of_germ (hN.mul hN').continuousAt
    ((hF.mul hD.continuousAt).mul hD'.continuousAt) hcleared

lemma reflectionExponent_analytic (M : SL(2, ℤ)) (r n : ℤ) (z : ℂ) :
    AnalyticOnNhd ℂ (fun τ => reflectionExponent M r n z τ) (modularPhiDomain M) := by
  intro τ hτ
  have hb := modularPhi_sqrt_admissible M τ hτ
  have hd : AnalyticAt ℂ (fun τ => etaDenom M τ) τ := by
    unfold etaDenom
    fun_prop
  have hs : AnalyticAt ℂ (fun τ => Complex.sqrt (etaDenom M τ)) τ :=
    ((Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane)
      (etaDenom M τ) hτ).comp hd
  have he : AnalyticAt ℂ (fun τ : ℂ => (z, τ)) τ := analyticAt_const.prod analyticAt_id
  unfold reflectionExponent
  apply Finset.analyticAt_fun_sum
  intro j _
  have hpoint := ((modularPhiFactorPoint_analytic M r n j) (z, τ) hτ).comp
    (f := fun τ : ℂ => (z, τ)) (x := τ) he
  have harg : AnalyticAt ℂ (fun τ => (modularPhiFactorPoint M r n j z τ).2) τ :=
    analyticAt_snd.comp hpoint
  exact ((analyticAt_const.mul analyticAt_const).mul (harg.pow 2)).add
    (((analyticAt_const.mul analyticAt_const).mul
      ((hs.pow 2).add ((hs.inv hb.2.2).pow 2))).div_const (c := 12))

lemma exp_reflectionExponent_analytic (M : SL(2, ℤ)) (r n : ℤ) (z : ℂ) :
    AnalyticOnNhd ℂ (fun τ => Complex.exp (reflectionExponent M r n z τ))
      (modularPhiDomain M) := by
  intro τ hτ
  exact (reflectionExponent_analytic M r n z τ hτ).cexp

end SICLean.L4.ModularCocycleReflectionAux
