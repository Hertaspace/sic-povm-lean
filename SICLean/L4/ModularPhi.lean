import SICLean.L4.FaddeevProduct
import SICLean.L4.EtaMultiplier
import SICLean.L4.ModularPhiAux

set_option autoImplicit false

/-!
# Positive-c modular Φ

All definitions have explicit bodies. No structure field postulates joint
meromorphy. The same `phiExtended` is used in the finite product,
with the principal `Complex.sqrt`.

All statements in this file are proved, including the index shifts
`modularPhi_index_m_germ` and `modularPhi_index_n_germ`.
Only theorems with `0 < M 1 0` identify this product with [RW26]'s Φ.
The empty product for nonpositive c is merely Lean's total definition.

[RW26, p. 2, p. 5, p. 6, §2.2, (1), (9), (19), Prop. 2(i)]. Integer division is floor division with
c>0.
Identity (19) is applied for c > 0. [RW26, (19)].

The S substitution uses `i(1/2-n)/b`, in agreement with `z+mτ-n` and [RW26, (9)].
`modularPhi_S_argument` records this substitution.

Two-variable charts use `(z,τ)`, whereas φ charts use `(b,argument)`.
Their indices are fixed on a neighborhood. Slice nontriviality of the
pulled-back denominator is a conclusion, not an assumption: the argument
has nonzero z slope `i/sqrt(T)`. Joint comparisons are cross products of
analytic chart numerators and denominators, not punctured-ℂ² pointwise
equalities. The six shifts are fixed-τ meromorphic germs. Point values at
common zeros are not assigned by the raw q quotient.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4

/-- Same slit-plane preimage as `etaPhaseDomain`; includes open complex
neighborhoods of every real τ with cτ+d>0. -/
def modularPhiDomain (M : SL(2, ℤ)) : Set ℂ :=
  {τ | etaDenom M τ ∈ Complex.slitPlane}

/-- [RW26, p. 5] unambiguous m=n=0 substitution. -/
def modularPhiSArgument (σ ζ : ℂ) : ℂ :=
  Complex.I * ζ / Complex.sqrt σ - Complex.I * Complex.sqrt σ / 2 +
    Complex.I / (2 * Complex.sqrt σ)

/-- The single S factor, constructed from the already proved continuation. -/
def modularPhiS (ζ σ : ℂ) : ℂ :=
  phiExtended (Complex.sqrt σ) (modularPhiSArgument σ ζ)

/-- [RW26, (19)] Euclidean integer division is downward floor when c>0. -/
def modularPhiIndex (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) : ℤ :=
  (M 1 1 * (m + (j : ℤ)) - n) / M 1 0

/-- Remaining denominator residue. `modularPhiResidue_permutation` shows that these residues permute
`0,...,c-1`. -/
def modularPhiResidue (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) : ℤ :=
  M 1 1 * (m + (j : ℤ)) - M 1 0 * modularPhiIndex M m n j - n

/-- The affine input of the j-th S factor in [RW26, (19)]. -/
def modularPhiFactorInput (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) (z τ : ℂ) : ℂ :=
  z + ((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ)

/-- Explicit pullback to φ's two complex variables. -/
def modularPhiFactorPoint (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) (z τ : ℂ) : ℂ × ℂ :=
  (Complex.sqrt (etaDenom M τ),
    modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ))

/--
Actual finite product definition, [RW26, (19), Prop. 2(i)] c>0.
No q product on the real axis, meromorphy witness or function choice appears.
-/
def modularPhi (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℂ :=
  ∏ j ∈ Finset.range (M 1 0).toNat,
    phiExtended (modularPhiFactorPoint M m n j z τ).1
      (modularPhiFactorPoint M m n j z τ).2

/-- Numerator of a fixed vector of continuation charts. -/
def modularPhiChartNumerator (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ)
    (z τ : ℂ) : ℂ :=
  ∏ j ∈ Finset.range (M 1 0).toNat,
    continuationNumerator (modularPhiFactorPoint M m n j z τ).1
      (modularPhiFactorPoint M m n j z τ).2 (κ j)

def modularPhiChartDenominator (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ)
    (z τ : ℂ) : ℂ :=
  ∏ j ∈ Finset.range (M 1 0).toNat,
    continuationDenominator (modularPhiFactorPoint M m n j z τ).1
      (modularPhiFactorPoint M m n j z τ).2 (κ j)

def modularPhiChart (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ) (z τ : ℂ) : ℂ :=
  modularPhiChartNumerator M m n κ z τ / modularPhiChartDenominator M m n κ z τ

/-- Validity of a fixed-index vector, written with the original strip only. -/
def modularPhiChartDomain (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ) : Set (ℂ × ℂ) :=
  {p | p.2 ∈ modularPhiDomain M ∧
    ∀ j ∈ Finset.range (M 1 0).toNat,
      InStrip (modularPhiFactorPoint M m n j p.1 p.2).1
        (shiftedArgument (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 (κ j))}

/--
An explicit sufficient regular locus: every individual factor is away
from its poles. Zeros are allowed. No claim that this is the full Φ regular
locus is included in this definition or needed.
-/
def modularPhiRegularDomain (M : SL(2, ℤ)) (m n : ℤ) : Set (ℂ × ℂ) :=
  {p | p.2 ∈ modularPhiDomain M ∧
    ∀ j ∈ Finset.range (M 1 0).toNat,
      phiPoleMultiplicity (modularPhiFactorPoint M m n j p.1 p.2).1
        (modularPhiFactorPoint M m n j p.1 p.2).2 = 0}

/-- [RW26, (1)] numerator, with integer exponent (including negative m). -/
def modularPhiQNumerator (m : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammer ((e τ) ^ m * e z) (e τ)

/-- [RW26, (1)] denominator, using the same Möbius action as η. -/
def modularPhiQDenominator (M : SL(2, ℤ)) (n : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammer ((e (etaMobius M τ)) ^ n * e (z / etaDenom M τ))
    (e (etaMobius M τ))

/-- Raw upper-half-plane q quotient, not a definition of the continuation. -/
def modularPhiQProduct (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℂ :=
  modularPhiQNumerator m z τ / modularPhiQDenominator M n z τ

/--
[RW26] continuation domain, [RW26, p. 2]. Mathlib
`Complex.isOpen_slitPlane`; also `etaPhaseDomain_isOpen`.
-/
theorem modularPhiDomain_isOpen (M : SL(2, ℤ)) : IsOpen (modularPhiDomain M) := by
  exact Complex.isOpen_slitPlane.preimage (by unfold etaDenom; fun_prop)

/--
Real parameters are interior points when cτ₀+d>0, not boundary points; `real_mem_etaPhaseDomain`.
-/
theorem real_mem_modularPhiDomain (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hT : 0 < (M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) :
    (τ₀ : ℂ) ∈ modularPhiDomain M :=
  real_mem_etaPhaseDomain M τ₀ hT

/-- Upper-half-plane domain check, using `etaDenom_mem_slitPlane`. -/
theorem upper_mem_modularPhiDomain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℍ) : (τ : ℂ) ∈ modularPhiDomain M :=
  etaDenom_mem_slitPlane M hM τ

/-- Principal-branch obligations for every factor. Source: Mathlib
`Complex.sqrt` (principal cpow), `Complex.cpow_nat_inv_pow`,
`Complex.mem_slitPlane_iff_arg`, and `EtaMultiplierAux.sqrt_mul_self`. -/
theorem modularPhi_sqrt_admissible (M : SL(2, ℤ)) (τ : ℂ)
    (hτ : τ ∈ modularPhiDomain M) :
    AdmissibleB (Complex.sqrt (etaDenom M τ)) ∧
      Complex.sqrt (etaDenom M τ) ^ 2 = etaDenom M τ ∧
      Complex.sqrt (etaDenom M τ) ≠ 0 := by
  refine ⟨sqrt_re_pos_of_mem_slitPlane hτ, ?_, sqrt_ne_zero_of_mem_slitPlane hτ⟩
  have h := EtaMultiplierAux.sqrt_mul_self (etaDenom M τ)
  simpa [sq] using h

/--
[RW26, p. 6, (19)] exact real-floor meaning of integer `/`.
The proof uses Mathlib's `Int.ediv` and floor inequalities.
-/
theorem modularPhiIndex_eq_floor (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) :
    modularPhiIndex M m n j =
      ⌊((M 1 1 : ℝ) * ((m : ℝ) + (j : ℝ)) - (n : ℝ)) / (M 1 0 : ℝ)⌋ := by
  set c : ℤ := M 1 0 with hcdef
  set b : ℤ := M 1 1 * (m + (j : ℤ)) - n with hbdef
  have hc : 0 < c := hM
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hbR : (b : ℝ) = (M 1 1 : ℝ) * ((m : ℝ) + (j : ℝ)) - (n : ℝ) := by
    simp only [hbdef]
    push_cast
    ring
  have hkey : modularPhiIndex M m n j = b / c := by
    simp only [modularPhiIndex, hcdef, hbdef]
  rw [hkey, ← hbR, eq_comm, Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hcR]
    have h1 : b / c * c ≤ b := Int.ediv_mul_le b hc.ne'
    have h1R : ((b / c : ℤ) : ℝ) * (c : ℝ) ≤ (b : ℝ) := by exact_mod_cast h1
    simpa [mul_comm] using h1R
  · rw [div_lt_iff₀ hcR]
    have h2 : b < (b / c + 1) * c := Int.lt_ediv_add_one_mul_self b hc
    have h2R : (b : ℝ) < (((b / c + 1 : ℤ)) : ℝ) * (c : ℝ) := by exact_mod_cast h2
    push_cast at h2R
    linarith

/--
Residues used by the denominator grouping.
The determinant-one hypothesis is supplied by the existing SL₂ type.
-/
theorem modularPhiResidue_permutation (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ) :
    (∀ j : ℕ, 0 ≤ modularPhiResidue M m n j ∧
      modularPhiResidue M m n j < M 1 0) ∧
    (Finset.range (M 1 0).toNat).image (fun j => (modularPhiResidue M m n j).toNat) =
      Finset.range (M 1 0).toNat ∧
    Set.InjOn (fun j : ℕ => (modularPhiResidue M m n j).toNat)
      (↑(Finset.range (M 1 0).toNat) : Set ℕ) := by
  classical
  set c : ℤ := M 1 0 with hcdef
  set d : ℤ := M 1 1 with hddef
  set B : ℕ → ℤ := fun j => d * (m + (j : ℤ)) - n with hBdef
  have hc : 0 < c := hM
  have hne : c ≠ 0 := hc.ne'
  have hres : ∀ j, modularPhiResidue M m n j = B j % c := by
    intro j
    have h1 : modularPhiResidue M m n j = B j - c * (B j / c) := by
      simp only [modularPhiResidue, modularPhiIndex, B, hcdef, hddef]
      ring
    rw [h1, Int.emod_def]
  have hBdiff : ∀ i j : ℕ, (B i - B j : ℤ) = d * ((i : ℤ) - (j : ℤ)) := by
    intro i j
    simp only [B]
    ring
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := M.2
    rwa [Matrix.det_fin_two] at h
  have hcop : IsCoprime c d := by
    refine ⟨-(M 0 1), M 0 0, ?_⟩
    simp only [hcdef, hddef]
    linarith
  have hr_nonneg : ∀ j, 0 ≤ modularPhiResidue M m n j := by
    intro j; rw [hres j]; exact Int.emod_nonneg _ hne
  have hr_lt : ∀ j, modularPhiResidue M m n j < c := by
    intro j; rw [hres j]; exact Int.emod_lt_of_pos _ hc
  have hinj : Set.InjOn (fun j : ℕ => (modularPhiResidue M m n j).toNat)
      (↑(Finset.range c.toNat) : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < c.toNat := Finset.mem_range.mp hi
    have hj' : j < c.toNat := Finset.mem_range.mp hj
    have hci : (i : ℤ) < c := by
      have h1 : (i : ℤ) < (c.toNat : ℤ) := by exact_mod_cast hi'
      rwa [Int.toNat_of_nonneg hc.le] at h1
    have hcj : (j : ℤ) < c := by
      have h1 : (j : ℤ) < (c.toNat : ℤ) := by exact_mod_cast hj'
      rwa [Int.toNat_of_nonneg hc.le] at h1
    have hrr : modularPhiResidue M m n i = modularPhiResidue M m n j := by
      have h1 := hr_nonneg i
      have h2 := hr_nonneg j
      have h3 : ((modularPhiResidue M m n i).toNat : ℤ) =
          ((modularPhiResidue M m n j).toNat : ℤ) := by exact_mod_cast hij
      rwa [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at h3
    have hdvd : c ∣ B i - B j := by
      have hmod : B i % c = B j % c := by rw [← hres i, ← hres j]; exact hrr
      have h0 : (B i - B j) % c = 0 :=
        (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hmod
      exact Int.dvd_of_emod_eq_zero h0
    rw [hBdiff i j] at hdvd
    have hdvd2 : c ∣ (i : ℤ) - (j : ℤ) := hcop.dvd_of_dvd_mul_left hdvd
    have hlt : |((i : ℤ) - (j : ℤ))| < c := by
      rw [abs_lt]
      constructor <;> omega
    have hzero : (i : ℤ) - (j : ℤ) = 0 := by
      by_contra hne0
      have hk : 0 < |((i : ℤ) - (j : ℤ))| := abs_pos.mpr hne0
      have hle : c ≤ |((i : ℤ) - (j : ℤ))| := by
        obtain ⟨t, ht⟩ := hdvd2
        have hk : (i : ℤ) - (j : ℤ) = c * t := ht
        have htne : t ≠ 0 := by
          intro h0
          rw [hk, h0, mul_zero] at hne0
          exact hne0 rfl
        have ht1 : 1 ≤ |t| := by
          have := abs_pos.mpr htne
          omega
        rw [hk, abs_mul, abs_of_pos hc]
        nlinarith [hc]
      omega
    omega
  refine ⟨fun j => ⟨by simpa [hcdef] using hr_nonneg j, by simpa [hcdef] using hr_lt j⟩, ?_, ?_⟩
  · have hsub : (Finset.range c.toNat).image
        (fun j => (modularPhiResidue M m n j).toNat) ⊆ Finset.range c.toNat := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨j, _, rfl⟩ := hx
      rw [Finset.mem_range]
      exact (Int.toNat_lt_toNat hc).mpr (hr_lt j)
    have hcard : ((Finset.range c.toNat).image
        (fun j => (modularPhiResidue M m n j).toNat)).card = (Finset.range c.toNat).card := by
      rw [Finset.card_image_of_injOn hinj]
    exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  · simpa [hcdef] using hinj

/--
Exact affine identity for denominator residue classes, including its
integer exponential phase. Same labels as the permutation theorem.
-/
theorem modularPhiFactorInput_div (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) (τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ)) / etaDenom M τ =
      ((n : ℂ) + (modularPhiResidue M m n j : ℂ)) * etaMobius M τ +
        (M 0 0 : ℂ) * (modularPhiIndex M m n j : ℂ) -
        (M 0 1 : ℂ) * ((m : ℂ) + (j : ℂ)) := by
  have hT : etaDenom M τ ≠ 0 := Complex.slitPlane_ne_zero hτ
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by
    have h := M.2
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hnr : (n : ℂ) + (modularPhiResidue M m n j : ℂ) =
      (M 1 1 : ℂ) * ((m : ℂ) + (j : ℂ)) -
        (M 1 0 : ℂ) * (modularPhiIndex M m n j : ℂ) := by
    have h : n + modularPhiResidue M m n j =
        M 1 1 * (m + (j : ℤ)) - M 1 0 * modularPhiIndex M m n j := by
      simp only [modularPhiResidue]
      ring
    have h' := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at h'
    exact h'
  have key : ((M 1 1 : ℂ) * ((m : ℂ) + (j : ℂ)) -
        (M 1 0 : ℂ) * (modularPhiIndex M m n j : ℂ)) *
        ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) +
      ((M 0 0 : ℂ) * (modularPhiIndex M m n j : ℂ) -
        (M 0 1 : ℂ) * ((m : ℂ) + (j : ℂ))) *
        ((M 1 0 : ℂ) * τ + (M 1 1 : ℂ)) =
      ((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ) := by
    linear_combination ((((m : ℂ) + (j : ℂ)) * τ +
      (modularPhiIndex M m n j : ℂ))) * hdet
  have hT' : (M 1 0 : ℂ) * τ + (M 1 1 : ℂ) ≠ 0 := hT
  have hdenEq : etaDenom M τ = (M 1 0 : ℂ) * τ + (M 1 1 : ℂ) := rfl
  have hmobEq : etaMobius M τ =
      ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) / ((M 1 0 : ℂ) * τ + (M 1 1 : ℂ)) := rfl
  rw [hdenEq, div_eq_iff hT', hnr, hmobEq]
  conv_rhs => rw [sub_mul, add_mul, mul_assoc, div_mul_cancel₀ _ hT']
  rw [add_sub_assoc, ← sub_mul]
  exact key.symm

/--
Genuine two-variable analytic pullback, [RW26, (19)].
Mathlib `Complex.differentiableAt_sqrt` and analytic composition.
-/
theorem modularPhiFactorPoint_analytic (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiFactorPoint M m n j p.1 p.2)
      {p | p.2 ∈ modularPhiDomain M} := by
  intro p hp
  have hT : etaDenom M p.2 ∈ Complex.slitPlane := hp
  have hden : AnalyticAt ℂ (fun q : ℂ × ℂ => etaDenom M q.2) p := by
    unfold etaDenom
    exact (analyticAt_const.mul analyticAt_snd).add analyticAt_const
  have hs : AnalyticAt ℂ (fun q : ℂ × ℂ => Complex.sqrt (etaDenom M q.2)) p := by
    have hsq : AnalyticAt ℂ Complex.sqrt (etaDenom M p.2) :=
      (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane)
        (etaDenom M p.2) hT
    have := hsq.comp (x := p) hden
    simpa [Function.comp_def] using this
  have hsne : Complex.sqrt (etaDenom M p.2) ≠ 0 := sqrt_ne_zero_of_mem_slitPlane hT
  have hζ : AnalyticAt ℂ (fun q : ℂ × ℂ => modularPhiFactorInput M m n j q.1 q.2) p := by
    unfold modularPhiFactorInput
    exact ((analyticAt_fst.add (analyticAt_const.mul analyticAt_snd)).add analyticAt_const)
  have harg : AnalyticAt ℂ (fun q : ℂ × ℂ =>
      modularPhiSArgument (etaDenom M q.2) (modularPhiFactorInput M m n j q.1 q.2)) p := by
    have hmain : AnalyticAt ℂ (fun q : ℂ × ℂ =>
        Complex.I * modularPhiFactorInput M m n j q.1 q.2 /
          Complex.sqrt (etaDenom M q.2)) p :=
      (analyticAt_const.mul hζ).div hs hsne
    have hmid : AnalyticAt ℂ (fun q : ℂ × ℂ =>
        -(Complex.I * Complex.sqrt (etaDenom M q.2) / 2)) p :=
      AnalyticAt.neg (AnalyticAt.div_const (c := 2) ((analyticAt_const (v := Complex.I)).mul hs))
    have h2 : AnalyticAt ℂ (fun q : ℂ × ℂ =>
        2 * Complex.sqrt (etaDenom M q.2)) p := analyticAt_const.mul hs
    have hlast : AnalyticAt ℂ (fun q : ℂ × ℂ =>
        Complex.I / (2 * Complex.sqrt (etaDenom M q.2))) p :=
      AnalyticAt.div (analyticAt_const (v := Complex.I)) h2 (by simp [hsne])
    have hsum := (hmain.add hmid).add hlast
    have heq : ((fun q : ℂ × ℂ =>
          Complex.I * modularPhiFactorInput M m n j q.1 q.2 /
            Complex.sqrt (etaDenom M q.2)) +
        (fun q => -(Complex.I * Complex.sqrt (etaDenom M q.2) / 2)) +
        (fun q => Complex.I / (2 * Complex.sqrt (etaDenom M q.2)))) =
        fun q => modularPhiSArgument (etaDenom M q.2)
          (modularPhiFactorInput M m n j q.1 q.2) := by
      funext q
      simp only [Pi.add_apply, modularPhiSArgument, sub_eq_add_neg]
    rw [heq] at hsum
    exact hsum
  exact hs.prod harg

/--
Nondegeneracy needed for pulled-back denominator nontriviality: the explicit affine argument
has the nonzero slope `I / sqrt (etaDenom M τ)` in `z`.
-/
theorem modularPhiFactorPoint_z_slope (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ)
    (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    HasDerivAt (fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2)
      (Complex.I / Complex.sqrt (etaDenom M τ)) z ∧
      Complex.I / Complex.sqrt (etaDenom M τ) ≠ 0 := by
  have hsne : Complex.sqrt (etaDenom M τ) ≠ 0 := sqrt_ne_zero_of_mem_slitPlane hτ
  constructor
  · have hc : (fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2) =
        fun w : ℂ => (Complex.I / Complex.sqrt (etaDenom M τ)) * w +
          (modularPhiSArgument (etaDenom M τ)
            (((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ))) := by
      funext w
      simp only [modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput]
      field_simp
      ring
    rw [hc]
    simpa using ((hasDerivAt_id z).const_mul
      (Complex.I / Complex.sqrt (etaDenom M τ))).add_const
      (modularPhiSArgument (etaDenom M τ)
        (((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ)))
  · exact div_ne_zero Complex.I_ne_zero hsne

/-- Open validity set for a vector of fixed charts. Source:
`isOpen_parameterDomain`, square-root pullback, and finite intersections. -/
theorem modularPhiChartDomain_isOpen (M : SL(2, ℤ)) (m n : ℤ) (κ : ℕ → ℤ) :
    IsOpen (modularPhiChartDomain M m n κ) := by
  classical
  have h0 : IsOpen {p : ℂ × ℂ | p.2 ∈ modularPhiDomain M} :=
    (modularPhiDomain_isOpen M).preimage continuous_snd
  have hA : ∀ j : ℕ, IsOpen {p : ℂ × ℂ | p.2 ∈ modularPhiDomain M ∧
      InStrip (modularPhiFactorPoint M m n j p.1 p.2).1
        (shiftedArgument (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 (κ j))} := by
    intro j
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨hpdom, hpj⟩
    have hcont : ContinuousAt (fun p : ℂ × ℂ =>
        modularPhiFactorPoint M m n j p.1 p.2) p :=
      ((modularPhiFactorPoint_analytic M m n j) p hpdom).continuousAt
    exact Filter.inter_mem (h0.mem_nhds hpdom)
      (hcont.preimage_mem_nhds ((isOpen_inStrip_joint (κ j)).mem_nhds hpj))
  have hEq : modularPhiChartDomain M m n κ =
      {p : ℂ × ℂ | p.2 ∈ modularPhiDomain M} ∩
        ⋂ j ∈ Finset.range (M 1 0).toNat, {p : ℂ × ℂ | p.2 ∈ modularPhiDomain M ∧
          InStrip (modularPhiFactorPoint M m n j p.1 p.2).1
            (shiftedArgument (modularPhiFactorPoint M m n j p.1 p.2).1
              (modularPhiFactorPoint M m n j p.1 p.2).2 (κ j))} := by
    ext p
    simp only [modularPhiChartDomain, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => ⟨h1, h2 j hj⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => (h2 j hj).2⟩
  rw [hEq]
  exact h0.inter (isOpen_biInter_finset fun j _ => hA j)

/-- Each explicit chart consists of two joint analytic finite products.
Source: `analyticAt_continuationNumerator_joint`,
`analyticAt_continuationDenominator_joint`, `Finset.analyticAt_fun_prod`. -/
theorem modularPhiChart_analytic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (κ : ℕ → ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiChartNumerator M m n κ p.1 p.2)
      (modularPhiChartDomain M m n κ) ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiChartDenominator M m n κ p.1 p.2)
      (modularPhiChartDomain M m n κ) := by
  constructor
  · apply Finset.analyticOnNhd_fun_prod
    intro j hj p hp
    have hpdom : p.2 ∈ modularPhiDomain M := hp.1
    have hb := (modularPhi_sqrt_admissible M p.2 hpdom).1
    have hstrip : InStrip (modularPhiFactorPoint M m n j p.1 p.2).1
        (shiftedArgument (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 (κ j)) := hp.2 j hj
    have hF := (modularPhiFactorPoint_analytic M m n j) p hpdom
    exact (analyticAt_continuationNumerator_joint
      (modularPhiFactorPoint M m n j p.1 p.2) (κ j) hb hstrip).comp (x := p) hF
  · apply Finset.analyticOnNhd_fun_prod
    intro j hj p hp
    have hpdom : p.2 ∈ modularPhiDomain M := hp.1
    have hF := (modularPhiFactorPoint_analytic M m n j) p hpdom
    exact (analyticAt_continuationDenominator_joint
      (modularPhiFactorPoint M m n j p.1 p.2) (κ j)).comp (x := p) hF

/-- The product denominator is not locally identically zero on any fixed-τ
slice of a valid chart, including slices through the real axis.
Source: `continuationDenominator_frequently_ne_zero`, the nonzero affine
z slope, and finite products of one-variable analytic functions. -/
theorem modularPhiChartDenominator_frequently_ne_zero (M : SL(2, ℤ))
    (hM : 0 < M 1 0) (m n : ℤ) (κ : ℕ → ℤ) (p : ℂ × ℂ)
    (hp : p ∈ modularPhiChartDomain M m n κ) :
    ∃ᶠ w : ℂ in 𝓝 p.1, modularPhiChartDenominator M m n κ w p.2 ≠ 0 := by
  classical
  have hpdom : p.2 ∈ modularPhiDomain M := hp.1
  set b : ℂ := Complex.sqrt (etaDenom M p.2) with hbdef
  have hb : AdmissibleB b := (modularPhi_sqrt_admissible M p.2 hpdom).1
  have hbne : b ≠ 0 := sqrt_ne_zero_of_mem_slitPlane hpdom
  set α : ℂ := Complex.I / b with hαdef
  have hα : α ≠ 0 := div_ne_zero Complex.I_ne_zero hbne
  set βfun : ℕ → ℂ := fun j => modularPhiSArgument (etaDenom M p.2)
    (((m : ℂ) + (j : ℂ)) * p.2 + (modularPhiIndex M m n j : ℂ)) with hβdef
  have harg : ∀ j : ℕ,
      (fun w : ℂ => (modularPhiFactorPoint M m n j w p.2).2) =
        fun w => α * w + βfun j := by
    intro j
    funext w
    simp only [modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput,
      hαdef, hβdef, b]
    field_simp
    ring
  have hfun : (fun w : ℂ => modularPhiChartDenominator M m n κ w p.2) =
      fun a => ∏ j ∈ Finset.range (M 1 0).toNat,
        continuationDenominator b (α * a + βfun j) (κ j) := by
    funext a
    apply Finset.prod_congr rfl
    intro j hj
    have h1 : (modularPhiFactorPoint M m n j a p.2).2 = α * a + βfun j :=
      congrFun (harg j) a
    have h2 : (modularPhiFactorPoint M m n j a p.2).1 = b := rfl
    rw [h2, h1]
  have hz : ∀ j ∈ Finset.range (M 1 0).toNat,
      InStrip b (shiftedArgument b (α * p.1 + βfun j) (κ j)) := by
    intro j hj
    have h1 : (modularPhiFactorPoint M m n j p.1 p.2).2 = α * p.1 + βfun j :=
      congrFun (harg j) p.1
    have h2 : (modularPhiFactorPoint M m n j p.1 p.2).1 = b := rfl
    have hpj := hp.2 j hj
    rwa [h1, h2] at hpj
  have hmer : MeromorphicAt (fun w : ℂ => modularPhiChartDenominator M m n κ w p.2) p.1 := by
    rw [hfun]
    apply MeromorphicAt.fun_prod
    intro j hj
    exact (analyticAt_continuationDenominator_affine b (κ j) α (βfun j) p.1).meromorphicAt
  have hnt : meromorphicOrderAt (fun w : ℂ => modularPhiChartDenominator M m n κ w p.2) p.1 ≠ ⊤ := by
    rw [hfun, meromorphicOrderAt_fun_prod (fun j hj =>
      (analyticAt_continuationDenominator_affine b (κ j) α (βfun j) p.1).meromorphicAt)]
    exact WithTop.sum_ne_top.mpr (fun j hj =>
      meromorphicOrderAt_continuationDenominator_affine_ne_top b hb (κ j) α (βfun j) p.1
        hα (hz j hj))
  exact ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp hnt).frequently
    |>.filter_mono nhdsWithin_le_nhds

/-- Compatibility with the concrete product, including its assigned pole
values. This asserts equality of total representatives of the same valid
finite chart, not equality with a canceled/removable q quotient.
Source: `phiExtended_eq_phiChart` (point values) and finite product/division. -/
theorem modularPhi_eq_chart (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (κ : ℕ → ℤ) (p : ℂ × ℂ)
    (hp : p ∈ modularPhiChartDomain M m n κ) :
    modularPhi M m n p.1 p.2 = modularPhiChart M m n κ p.1 p.2 := by
  have hpdom : p.2 ∈ modularPhiDomain M := hp.1
  have hb : AdmissibleB (Complex.sqrt (etaDenom M p.2)) :=
    (modularPhi_sqrt_admissible M p.2 hpdom).1
  have hfac : ∀ j ∈ Finset.range (M 1 0).toNat,
      phiExtended (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 =
        continuationNumerator (modularPhiFactorPoint M m n j p.1 p.2).1
            (modularPhiFactorPoint M m n j p.1 p.2).2 (κ j) /
          continuationDenominator (modularPhiFactorPoint M m n j p.1 p.2).1
            (modularPhiFactorPoint M m n j p.1 p.2).2 (κ j) := by
    intro j hj
    exact phiExtended_eq_phiChart _ _ _ hb (hp.2 j hj)
  simp only [modularPhi, modularPhiChart, modularPhiChartNumerator, modularPhiChartDenominator]
  rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib]

/-- Joint analytic chart compatibility at every overlap point, without
division and without deleting only a single point of ℂ².
Source: `phiChart_pointwise`, `phiChart_overlap`, and the explicit finite product charts. -/
theorem modularPhiChart_overlap_cross_mul (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (κ κ' : ℕ → ℤ) (p : ℂ × ℂ)
    (hκ : p ∈ modularPhiChartDomain M m n κ)
    (hκ' : p ∈ modularPhiChartDomain M m n κ') :
    modularPhiChartNumerator M m n κ p.1 p.2 *
        modularPhiChartDenominator M m n κ' p.1 p.2 =
      modularPhiChartNumerator M m n κ' p.1 p.2 *
        modularPhiChartDenominator M m n κ p.1 p.2 := by
  have hpdom : p.2 ∈ modularPhiDomain M := hκ.1
  have hb : AdmissibleB (Complex.sqrt (etaDenom M p.2)) :=
    (modularPhi_sqrt_admissible M p.2 hpdom).1
  have hfac : ∀ j ∈ Finset.range (M 1 0).toNat,
      continuationNumerator (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 (κ j) *
        continuationDenominator (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 (κ' j) =
      continuationNumerator (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 (κ' j) *
        continuationDenominator (modularPhiFactorPoint M m n j p.1 p.2).1
          (modularPhiFactorPoint M m n j p.1 p.2).2 (κ j) := by
    intro j hj
    exact continuationNumerator_mul_denominator_comm _ _ _ _ hb
      (hκ.2 j hj) (hκ'.2 j hj)
  simp only [modularPhiChartNumerator, modularPhiChartDenominator]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl hfac

/--
Explicit joint local quotient for the actual Φ, with indices fixed by
the center's rounding operation. Slice nontriviality is a conclusion.
`phiExtended_joint_local_quotient`; [RW26, p. 2, (19), Prop. 2(i)]. This is the interface, rather
than a “joint meromorphic” structure assumption.
-/
theorem modularPhi_joint_local_quotient (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (p : ℂ × ℂ) (hp : p.2 ∈ modularPhiDomain M) :
    let κ : ℕ → ℤ := fun j =>
      continuationIndex (modularPhiFactorPoint M m n j p.1 p.2).1
        (modularPhiFactorPoint M m n j p.1 p.2).2
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ p ∈ U ∧ U ⊆ modularPhiChartDomain M m n κ ∧
      AnalyticOnNhd ℂ (fun q : ℂ × ℂ => modularPhiChartNumerator M m n κ q.1 q.2) U ∧
      AnalyticOnNhd ℂ (fun q : ℂ × ℂ => modularPhiChartDenominator M m n κ q.1 q.2) U ∧
      (∀ q ∈ U, ∃ᶠ w : ℂ in 𝓝 q.1, modularPhiChartDenominator M m n κ w q.2 ≠ 0) ∧
      (∀ q ∈ U, modularPhiChartDenominator M m n κ q.1 q.2 ≠ 0 →
        modularPhi M m n q.1 q.2 =
          modularPhiChartNumerator M m n κ q.1 q.2 /
            modularPhiChartDenominator M m n κ q.1 q.2) := by
  dsimp only
  set κ : ℕ → ℤ := fun j =>
    continuationIndex (modularPhiFactorPoint M m n j p.1 p.2).1
      (modularPhiFactorPoint M m n j p.1 p.2).2 with hκdef
  have hb : AdmissibleB (Complex.sqrt (etaDenom M p.2)) :=
    (modularPhi_sqrt_admissible M p.2 hp).1
  have hpU : p ∈ modularPhiChartDomain M m n κ := by
    refine ⟨hp, ?_⟩
    intro j hj
    exact shiftedArgument_inStrip _ _ hb
  obtain ⟨hAn, hAd⟩ := modularPhiChart_analytic M hM m n κ
  exact ⟨modularPhiChartDomain M m n κ, modularPhiChartDomain_isOpen M m n κ,
    hpU, subset_rfl, hAn, hAd,
    fun q hq => modularPhiChartDenominator_frequently_ne_zero M hM m n κ q hq,
    fun q hq _ => modularPhi_eq_chart M hM m n κ q hq⟩

/--
Fixed-τ meromorphy follows from the explicit charts, not vice versa.
[RW26, p. 6] `MeromorphicAt.div`, analytic affine composition.
-/
theorem modularPhi_meromorphic (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    MeromorphicOn (fun z => modularPhi M m n z τ) Set.univ := by
  intro z _
  have hb : AdmissibleB (Complex.sqrt (etaDenom M τ)) :=
    (modularPhi_sqrt_admissible M τ hτ).1
  have hfun : (fun w : ℂ => modularPhi M m n w τ) =
      fun a => ∏ j ∈ Finset.range (M 1 0).toNat,
        (fun w => phiExtended (Complex.sqrt (etaDenom M τ))
          ((modularPhiFactorPoint M m n j w τ).2)) a := rfl
  rw [hfun]
  apply MeromorphicAt.fun_prod
  intro j hj
  have hmer : MeromorphicAt (fun ζ : ℂ => phiExtended (Complex.sqrt (etaDenom M τ)) ζ)
      ((modularPhiFactorPoint M m n j z τ).2) :=
    (phiExtended_meromorphic (Complex.sqrt (etaDenom M τ)) hb)
      ((modularPhiFactorPoint M m n j z τ).2) (Set.mem_univ _)
  have hg : AnalyticAt ℂ (fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2) z := by
    have harg : (fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2) =
        fun w => (Complex.I / Complex.sqrt (etaDenom M τ)) * w +
          (modularPhiSArgument (etaDenom M τ)
            (((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ))) := by
      funext w
      simp only [modularPhiFactorPoint, modularPhiSArgument, modularPhiFactorInput]
      field_simp
      ring
    rw [harg]
    fun_prop
  have := MeromorphicAt.comp_analyticAt (f := fun ζ : ℂ =>
    phiExtended (Complex.sqrt (etaDenom M τ)) ζ)
    (g := fun w : ℂ => (modularPhiFactorPoint M m n j w τ).2) (x := z) hmer hg
  simpa [Function.comp_def] using this

/--
Joint regularity on the explicit factor-regular locus, allowing zeros.
It uses `phiExtended_joint_holomorphic` and the actual analytic local charts. No complete divisor
theorem
is assumed.
-/
theorem modularPhi_joint_analytic_regular (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhi M m n p.1 p.2)
      (modularPhiRegularDomain M m n) := by
  intro p hp
  have hpdom : p.2 ∈ modularPhiDomain M := hp.1
  have hb : AdmissibleB (Complex.sqrt (etaDenom M p.2)) :=
    (modularPhi_sqrt_admissible M p.2 hpdom).1
  have hfun : (fun q : ℂ × ℂ => modularPhi M m n q.1 q.2) =
      fun q => ∏ j ∈ Finset.range (M 1 0).toNat,
        (fun q => phiExtended (modularPhiFactorPoint M m n j q.1 q.2).1
          (modularPhiFactorPoint M m n j q.1 q.2).2) q := rfl
  rw [hfun]
  apply Finset.analyticAt_fun_prod
  intro j hj
  have hF := (modularPhiFactorPoint_analytic M m n j) p hpdom
  have hmem : modularPhiFactorPoint M m n j p.1 p.2 ∈ phiRegularDomain :=
    ⟨hb, hp.2 j hj⟩
  have := (analyticAt_phiExtended_joint hmem).comp (x := p) hF
  simpa [Function.comp_def] using this

/--
S specialization of the literal finite product. [RW26, p. 5, p. 6, (19)]
-/
theorem modularPhi_S (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    modularPhi ModularGroup.S m n z τ =
      modularPhiS (z + (m : ℂ) * τ - (n : ℂ)) τ := by
  simp only [modularPhi, ModularGroup.coe_S, etaDenom, modularPhiFactorPoint,
    modularPhiIndex, modularPhiFactorInput, modularPhiS]
  norm_num
  congr 1

/--
The S substitution uses the factor `i(1/2 - n)/b`. [RW26, p. 5, (9)].
-/
theorem modularPhi_S_argument (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    modularPhi ModularGroup.S m n z τ =
      phiExtended (Complex.sqrt τ)
        (Complex.I * z / Complex.sqrt τ +
          Complex.I * ((m : ℂ) - 1 / 2) * Complex.sqrt τ +
          Complex.I * (1 / 2 - (n : ℂ)) / Complex.sqrt τ) := by
  rw [modularPhi_S m n z τ hτ]
  have hsne : Complex.sqrt τ ≠ 0 := sqrt_ne_zero_of_mem_slitPlane hτ
  have hsq : Complex.sqrt τ * Complex.sqrt τ = τ := EtaMultiplierAux.sqrt_mul_self τ
  simp only [modularPhiS]
  congr 1
  simp only [modularPhiSArgument]
  field_simp
  rw [show Complex.sqrt τ ^ 2 = τ by rw [sq]; exact hsq]
  ring

/-! ## Explicit evaluation of the product factors in [RW26, (1)] -/

lemma det_coe_int (M : SL(2, ℤ)) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  have h := M.2
  rwa [Matrix.det_fin_two] at h

lemma etaDenom_ne_zero_of_mem (M : SL(2, ℤ)) {τ : ℂ}
    (hτ : τ ∈ modularPhiDomain M) : etaDenom M τ ≠ 0 :=
  Complex.slitPlane_ne_zero hτ

lemma e_etaDenom_eq_pow (M : SL(2, ℤ)) (hM : 0 ≤ M 1 0) (τ : ℂ) :
    e (etaDenom M τ) = e τ ^ (M 1 0).toNat := by
  have hcast : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg hM
  have h2 : e (etaDenom M τ) = e ((M 1 0 : ℂ) * τ) * e ((M 1 1 : ℂ)) := by
    rw [etaDenom, e_add']
  rw [h2, e_intCast, mul_one]
  have hcastC : (M 1 0 : ℂ) = (((M 1 0).toNat : ℕ) : ℂ) := by
    exact_mod_cast (Int.toNat_of_nonneg hM).symm
  rw [hcastC, ← e_nat_mul]

lemma e_neg_inv_etaDenom_eq_pow (M : SL(2, ℤ)) (hM : 0 < M 1 0) (τ : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    e (-(etaDenom M τ)⁻¹) = e (etaMobius M τ) ^ (M 1 0).toNat := by
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by
    exact_mod_cast det_coe_int M
  have hkey : -(etaDenom M τ)⁻¹ =
      (M 1 0 : ℂ) * etaMobius M τ - (M 0 0 : ℂ) := by
    have hT' : (M 1 0 : ℂ) * τ + (M 1 1 : ℂ) ≠ 0 := hT
    rw [etaMobius]
    rw [show etaDenom M τ = (M 1 0 : ℂ) * τ + (M 1 1 : ℂ) from rfl]
    field_simp
    linear_combination hdet
  rw [hkey, sub_eq_add_neg, e_add', e_neg', e_intCast, inv_one, mul_one]
  have hcastC : (M 1 0 : ℂ) = (((M 1 0).toNat : ℕ) : ℂ) := by
    exact_mod_cast (Int.toNat_of_nonneg hM.le).symm
  rw [hcastC, ← e_nat_mul]

lemma e_factorInput_eq (M : SL(2, ℤ)) (m n : ℤ) (j : ℕ) (z τ : ℂ) :
    e (modularPhiFactorInput M m n j z τ) = e z * e τ ^ (m + (j : ℤ)) := by
  have hcast : ((m : ℂ) + (j : ℂ)) = ((m + (j : ℤ) : ℤ) : ℂ) := by push_cast; ring
  rw [modularPhiFactorInput, hcast]
  rw [show z + ((m + (j : ℤ) : ℤ) : ℂ) * τ + (modularPhiIndex M m n j : ℂ) =
      (z + ((m + (j : ℤ) : ℤ) : ℂ) * τ) + (modularPhiIndex M m n j : ℂ) from by ring]
  rw [e_add', e_add']
  rw [e_intCast, mul_one]
  rw [← e_int_mul τ (m + (j : ℤ))]

lemma e_factorInput_div_etaDenom (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    e (modularPhiFactorInput M m n j z τ / etaDenom M τ) =
      e (z / etaDenom M τ) * e (etaMobius M τ) ^ (n + modularPhiResidue M m n j) := by
  have hT : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hτ
  rw [modularPhiFactorInput]
  rw [show (z + ((m : ℂ) + (j : ℂ)) * τ + (modularPhiIndex M m n j : ℂ)) /
      etaDenom M τ =
      z / etaDenom M τ + (((m : ℂ) + (j : ℂ)) * τ +
        (modularPhiIndex M m n j : ℂ)) / etaDenom M τ from by field_simp; ring]
  rw [e_add']
  congr 1
  rw [modularPhiFactorInput_div M hM m n j τ hτ]
  have hint : ((n : ℂ) + (modularPhiResidue M m n j : ℂ)) * etaMobius M τ +
      (M 0 0 : ℂ) * (modularPhiIndex M m n j : ℂ) -
      (M 0 1 : ℂ) * ((m : ℂ) + (j : ℂ)) =
      ((n + modularPhiResidue M m n j : ℤ) : ℂ) * etaMobius M τ +
        ((M 0 0 * modularPhiIndex M m n j - M 0 1 * (m + (j : ℤ)) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hint, e_add', e_intCast, mul_one, ← e_int_mul]

/-- Explicit numerator phase, with the square root introduced as a variable. -/
lemma phiProductNumerator_phase (b T ζ : ℂ) (hbne : b ≠ 0) (hb2 : b ^ 2 = T)
    (harg : modularPhiSArgument T ζ = Complex.I * ζ / b - Complex.I * b / 2 +
      Complex.I / (2 * b)) :
    -Complex.exp (Real.pi * Complex.I * b ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * b * modularPhiSArgument T ζ) = e ζ := by
  have hkey : 2 * (Real.pi : ℂ) * b *
      (Complex.I * ζ / b - Complex.I * b / 2 + Complex.I / (2 * b)) =
      2 * (Real.pi : ℂ) * Complex.I * ζ - Real.pi * Complex.I * b ^ 2 +
        Real.pi * Complex.I := by
    field_simp
  have hsum : Real.pi * Complex.I * b ^ 2 +
      2 * (Real.pi : ℂ) * b *
        (Complex.I * ζ / b - Complex.I * b / 2 + Complex.I / (2 * b)) =
      2 * (Real.pi : ℂ) * Complex.I * ζ + Real.pi * Complex.I := by
    linear_combination hkey
  rw [harg]
  calc -Complex.exp (Real.pi * Complex.I * b ^ 2) *
        Complex.exp (2 * (Real.pi : ℂ) * b *
          (Complex.I * ζ / b - Complex.I * b / 2 + Complex.I / (2 * b)))
      = -Complex.exp (Real.pi * Complex.I * b ^ 2 +
          2 * (Real.pi : ℂ) * b *
            (Complex.I * ζ / b - Complex.I * b / 2 + Complex.I / (2 * b))) := by
        rw [Complex.exp_add]; ring
    _ = -Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ζ + Real.pi * Complex.I) := by
        rw [hsum]
    _ = e ζ := by
        rw [Complex.exp_add, Complex.exp_pi_mul_I]
        simp only [e]
        ring

/-- Explicit denominator phase, with the square root introduced as a variable. -/
lemma phiProductDenominator_phase (b T ζ : ℂ) (hbne : b ≠ 0) (hb2 : b ^ 2 = T)
    (harg : modularPhiSArgument T ζ = Complex.I * ζ / b - Complex.I * b / 2 +
      Complex.I / (2 * b)) :
    -Complex.exp (-(Real.pi * Complex.I / b ^ 2)) *
      Complex.exp (2 * (Real.pi : ℂ) * modularPhiSArgument T ζ / b) = e (ζ / T) := by
  have hT : T ≠ 0 := by
    rw [← hb2]
    exact pow_ne_zero 2 hbne
  have hkey : 2 * (Real.pi : ℂ) *
      (Complex.I * ζ / b - Complex.I * b / 2 + Complex.I / (2 * b)) / b =
      2 * (Real.pi : ℂ) * Complex.I * ζ / b ^ 2 - Real.pi * Complex.I +
        Real.pi * Complex.I / b ^ 2 := by
    field_simp
  rw [harg]
  rw [hb2] at hkey ⊢
  have hsum : -(Real.pi * Complex.I / T) +
      2 * (Real.pi : ℂ) *
        (Complex.I * ζ / b - Complex.I * b / 2 + Complex.I / (2 * b)) / b =
      2 * (Real.pi : ℂ) * Complex.I * (ζ / T) - Real.pi * Complex.I := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (ζ / T) =
      2 * (Real.pi : ℂ) * Complex.I * ζ / T from by ring]
    linear_combination hkey
  calc -Complex.exp (-(Real.pi * Complex.I / T)) *
        Complex.exp (2 * (Real.pi : ℂ) *
          (Complex.I * ζ / b - Complex.I * b / 2 + Complex.I / (2 * b)) / b)
      = -Complex.exp (-(Real.pi * Complex.I / T) +
          2 * (Real.pi : ℂ) *
            (Complex.I * ζ / b - Complex.I * b / 2 + Complex.I / (2 * b)) / b) := by
        rw [Complex.exp_add]; ring
    _ = -Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ζ / T) - Real.pi * Complex.I) := by
        rw [hsum]
    _ = e (ζ / T) := by
        rw [Complex.exp_sub, Complex.exp_pi_mul_I]
        simp only [e]
        ring

lemma phiProductNumerator_sqrt_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    phiProductNumerator (Complex.sqrt (etaDenom M τ))
        (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ)) =
      qPochhammer (e z * e τ ^ (m + (j : ℤ))) (e τ ^ (M 1 0).toNat) := by
  have hbne : Complex.sqrt (etaDenom M τ) ≠ 0 := sqrt_ne_zero_of_mem_slitPlane hτ
  have hb2 : Complex.sqrt (etaDenom M τ) ^ 2 = etaDenom M τ := by
    have h := EtaMultiplierAux.sqrt_mul_self (etaDenom M τ)
    simpa [sq] using h
  have hphase := phiProductNumerator_phase (Complex.sqrt (etaDenom M τ)) (etaDenom M τ)
    (modularPhiFactorInput M m n j z τ) hbne hb2 rfl
  simp only [phiProductNumerator, phiProductQ]
  rw [hphase]
  rw [show e ((Complex.sqrt (etaDenom M τ)) ^ 2) = e (etaDenom M τ) by rw [hb2]]
  rw [e_etaDenom_eq_pow M hM.le τ, e_factorInput_eq]

lemma phiProductDenominator_sqrt_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (j : ℕ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    phiProductDenominator (Complex.sqrt (etaDenom M τ))
        (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ)) =
      qPochhammer
        (e (z / etaDenom M τ) * e (etaMobius M τ) ^ (n + modularPhiResidue M m n j))
        (e (etaMobius M τ) ^ (M 1 0).toNat) := by
  have hbne : Complex.sqrt (etaDenom M τ) ≠ 0 := sqrt_ne_zero_of_mem_slitPlane hτ
  have hb2 : Complex.sqrt (etaDenom M τ) ^ 2 = etaDenom M τ := by
    have h := EtaMultiplierAux.sqrt_mul_self (etaDenom M τ)
    simpa [sq] using h
  have hT : etaDenom M τ ≠ 0 := etaDenom_ne_zero_of_mem M hτ
  have hphase := phiProductDenominator_phase (Complex.sqrt (etaDenom M τ)) (etaDenom M τ)
    (modularPhiFactorInput M m n j z τ) hbne hb2 rfl
  have hbdual : -((Complex.sqrt (etaDenom M τ))⁻¹) ^ 2 = -((etaDenom M τ)⁻¹) := by
    rw [show ((Complex.sqrt (etaDenom M τ))⁻¹) ^ 2 =
      ((Complex.sqrt (etaDenom M τ)) ^ 2)⁻¹ from by rw [inv_pow]]
    rw [hb2]
  have hconv : -Complex.exp (-(Real.pi : ℂ) * Complex.I *
        (Complex.sqrt (etaDenom M τ))⁻¹ ^ 2) *
      Complex.exp (2 * (Real.pi : ℂ) * (Complex.sqrt (etaDenom M τ))⁻¹ *
        modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ)) =
      -Complex.exp (-(Real.pi * Complex.I /
          (Complex.sqrt (etaDenom M τ)) ^ 2)) *
        Complex.exp (2 * (Real.pi : ℂ) *
          modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ) /
          Complex.sqrt (etaDenom M τ)) := by
    rw [show -(Real.pi : ℂ) * Complex.I * (Complex.sqrt (etaDenom M τ))⁻¹ ^ 2 =
        -(Real.pi * Complex.I / (Complex.sqrt (etaDenom M τ)) ^ 2) from by
      rw [show ((Complex.sqrt (etaDenom M τ))⁻¹) ^ 2 =
        ((Complex.sqrt (etaDenom M τ)) ^ 2)⁻¹ from by rw [inv_pow]]
      ring]
    rw [show 2 * (Real.pi : ℂ) * (Complex.sqrt (etaDenom M τ))⁻¹ *
        modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ) =
        2 * (Real.pi : ℂ) * modularPhiSArgument (etaDenom M τ)
          (modularPhiFactorInput M m n j z τ) /
          Complex.sqrt (etaDenom M τ) from by ring]
  simp only [phiProductDenominator, phiProductQDual]
  rw [hconv, hbdual, hphase, e_neg_inv_etaDenom_eq_pow M hM τ hT,
    e_factorInput_div_etaDenom M hM m n j z τ hτ]

lemma im_etaDenom_pos_of_im_pos (M : SL(2, ℤ)) (hM : 0 < M 1 0) {τ : ℂ}
    (hτ : 0 < τ.im) : 0 < (etaDenom M τ).im := by
  have h : (etaDenom M τ).im = (M 1 0 : ℝ) * τ.im := by
    simp [etaDenom]
  rw [h]
  have : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  exact mul_pos this hτ

lemma mem_modularPhiDomain_of_im_pos (M : SL(2, ℤ)) (hM : 0 < M 1 0) {τ : ℂ}
    (hτ : 0 < τ.im) : τ ∈ modularPhiDomain M :=
  Or.inr (ne_of_gt (im_etaDenom_pos_of_im_pos M hM hτ))

/-- Residue-class grouping of the numerator factors. -/
lemma prod_phiProductNumerator_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (z τ : ℂ) (hτ : 0 < τ.im) :
    (∏ j ∈ Finset.range (M 1 0).toNat,
      phiProductNumerator (Complex.sqrt (etaDenom M τ))
        (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ))) =
      modularPhiQNumerator m z τ := by
  set c : ℕ := (M 1 0).toNat with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    omega
  have hτdom : τ ∈ modularPhiDomain M := mem_modularPhiDomain_of_im_pos M hM hτ
  have hq0 : 0 < ‖e τ‖ := norm_pos_iff.mpr (e_ne_zero τ)
  have hq1 : ‖e τ‖ < 1 := norm_e_lt_one ⟨τ, hτ⟩
  have hfac : ∀ j ∈ Finset.range c,
      phiProductNumerator (Complex.sqrt (etaDenom M τ))
        (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ)) =
      qPochhammer (e z * e τ ^ (m + (j : ℤ))) ((e τ) ^ c) := by
    intro j hj
    rw [phiProductNumerator_sqrt_eq M hM m n j z τ hτdom]
  have hstep : (∏ j ∈ Finset.range c,
      phiProductNumerator (Complex.sqrt (etaDenom M τ))
        (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ))) =
      ∏ j ∈ Finset.range c,
        qPochhammer ((e z * e τ ^ m) * (e τ) ^ j) ((e τ) ^ c) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hfac j hj]
    rw [show e z * e τ ^ (m + (j : ℤ)) = (e z * e τ ^ m) * (e τ) ^ j from by
      rw [zpow_add₀ (e_ne_zero τ), zpow_natCast]
      ring]
  rw [hstep]
  have hres := qPochhammer_residue_classes (e z * e τ ^ m) (e τ) c hcpos hq0 hq1
  rw [← hres]
  rw [modularPhiQNumerator]
  rw [mul_comm (e z) (e τ ^ m)]

/-- Residue-class grouping of the denominator factors, using the floor
permutation of `modularPhiResidue_permutation`. -/
lemma prod_phiProductDenominator_eq (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n : ℤ)
    (z τ : ℂ) (hτ : 0 < τ.im) :
    (∏ j ∈ Finset.range (M 1 0).toNat,
      phiProductDenominator (Complex.sqrt (etaDenom M τ))
        (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ))) =
      modularPhiQDenominator M n z τ := by
  set c : ℕ := (M 1 0).toNat with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    omega
  have hτdom : τ ∈ modularPhiDomain M := mem_modularPhiDomain_of_im_pos M hM hτ
  have hηim : 0 < (etaMobius M τ).im := by
    have h := coe_smul_eq_etaMobius M (⟨τ, hτ⟩ : ℍ)
    rw [← h]
    simpa using (M • (⟨τ, hτ⟩ : ℍ)).im_pos
  have hq0 : 0 < ‖e (etaMobius M τ)‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hq1 : ‖e (etaMobius M τ)‖ < 1 := norm_e_lt_one ⟨_, hηim⟩
  have hperm := modularPhiResidue_permutation M hM m n
  have hr0 : ∀ j, 0 ≤ modularPhiResidue M m n j := fun j => (hperm.1 j).1
  have himg := hperm.2.1
  have hinj := hperm.2.2
  have hstep : (∏ j ∈ Finset.range c,
      phiProductDenominator (Complex.sqrt (etaDenom M τ))
        (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ))) =
      ∏ j ∈ Finset.range c,
        qPochhammer (e (z / etaDenom M τ) * e (etaMobius M τ) ^ n *
          (e (etaMobius M τ)) ^ (modularPhiResidue M m n j).toNat)
          ((e (etaMobius M τ)) ^ c) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [phiProductDenominator_sqrt_eq M hM m n j z τ hτdom]
    rw [show e (z / etaDenom M τ) * e (etaMobius M τ) ^ (n + modularPhiResidue M m n j) =
        e (z / etaDenom M τ) * e (etaMobius M τ) ^ n *
          (e (etaMobius M τ)) ^ (modularPhiResidue M m n j).toNat from by
      rw [show n + modularPhiResidue M m n j =
          n + ((modularPhiResidue M m n j).toNat : ℤ) from by
        rw [Int.toNat_of_nonneg (hr0 j)]]
      rw [← zpow_natCast]
      rw [zpow_add₀ (e_ne_zero (etaMobius M τ))]
      ring]
  rw [hstep]
  have hres := qPochhammer_residue_classes
    (e (z / etaDenom M τ) * e (etaMobius M τ) ^ n) (e (etaMobius M τ)) c hcpos hq0 hq1
  rw [modularPhiQDenominator, mul_comm ((e (etaMobius M τ)) ^ n) (e (z / etaDenom M τ))]
  rw [hres]
  have himg' : (Finset.range c).image (fun j => (modularPhiResidue M m n j).toNat) =
      Finset.range c := by simpa [hcdef] using himg
  have hinj' : Set.InjOn (fun j => (modularPhiResidue M m n j).toNat)
      (↑(Finset.range c) : Set ℕ) := by simpa [hcdef] using hinj
  conv_rhs => rw [← himg']
  conv_rhs => rw [Finset.prod_image hinj']

lemma modularPhiChart_qProduct_cross_mul_aux (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (κ : ℕ → ℤ) (p : ℂ × ℂ)
    (hp : p ∈ modularPhiChartDomain M m n κ) (hτ : 0 < p.2.im) :
    modularPhiChartNumerator M m n κ p.1 p.2 * modularPhiQDenominator M n p.1 p.2 =
      modularPhiQNumerator m p.1 p.2 * modularPhiChartDenominator M m n κ p.1 p.2  := by
  have hpdom : p.2 ∈ modularPhiDomain M := hp.1
  have hb : AdmissibleB (Complex.sqrt (etaDenom M p.2)) :=
    (modularPhi_sqrt_admissible M p.2 hpdom).1
  have hb2 : Complex.sqrt (etaDenom M p.2) ^ 2 = etaDenom M p.2 := by
    have h := EtaMultiplierAux.sqrt_mul_self (etaDenom M p.2)
    simpa [sq] using h
  have hupper : Complex.sqrt (etaDenom M p.2) ∈ phiUpperParameterDomain := by
    refine ⟨hb, ?_⟩
    rw [hb2]
    exact im_etaDenom_pos_of_im_pos M hM hτ
  have hfac : ∀ j ∈ Finset.range (M 1 0).toNat,
      continuationNumerator (Complex.sqrt (etaDenom M p.2))
          (modularPhiSArgument (etaDenom M p.2) (modularPhiFactorInput M m n j p.1 p.2)) (κ j) *
        phiProductDenominator (Complex.sqrt (etaDenom M p.2))
          (modularPhiSArgument (etaDenom M p.2) (modularPhiFactorInput M m n j p.1 p.2)) =
      phiProductNumerator (Complex.sqrt (etaDenom M p.2))
          (modularPhiSArgument (etaDenom M p.2) (modularPhiFactorInput M m n j p.1 p.2)) *
        continuationDenominator (Complex.sqrt (etaDenom M p.2))
          (modularPhiSArgument (etaDenom M p.2) (modularPhiFactorInput M m n j p.1 p.2)) (κ j) := by
    intro j hj
    have := phiChart_product_cross_mul (Complex.sqrt (etaDenom M p.2))
      (modularPhiSArgument (etaDenom M p.2) (modularPhiFactorInput M m n j p.1 p.2))
      (κ j) hupper (hp.2 j hj)
    simpa [modularPhiFactorPoint] using this
  simp only [modularPhiChartNumerator, modularPhiChartDenominator]
  rw [← prod_phiProductDenominator_eq M hM m n p.1 p.2 hτ,
    ← prod_phiProductNumerator_eq M hM m n p.1 p.2 hτ]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl hfac


/--
[RW26, p. 2, (1)] as a fixed-τ germ including common zeros.
Depends on `qPochhammer_residue_classes`, not on G1 integrals.
-/
theorem modularPhi_eq_qProduct_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    (fun w => modularPhi M m n w τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhiQProduct M m n w τ) := by
  have hpdom : τ ∈ modularPhiDomain M := mem_modularPhiDomain_of_im_pos M hM hτ
  let κ : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M m n j z τ).1 (modularPhiFactorPoint M m n j z τ).2
  have hb : AdmissibleB (Complex.sqrt (etaDenom M τ)) :=
    (modularPhi_sqrt_admissible M τ hpdom).1
  have hpU : (z, τ) ∈ modularPhiChartDomain M m n κ := by
    refine ⟨hpdom, ?_⟩
    intro j hj
    exact shiftedArgument_inStrip _ _ hb
  have hU : IsOpen (modularPhiChartDomain M m n κ) :=
    modularPhiChartDomain_isOpen M m n κ
  -- the chart denominator is nonzero eventually on the punctured neighborhood
  have hcDan : AnalyticAt ℂ (fun w : ℂ => modularPhiChartDenominator M m n κ w τ) z := by
    have hjoint := (modularPhiChart_analytic M hM m n κ).2 (z, τ) hpU
    have hemb : AnalyticAt ℂ (fun w : ℂ => (w, τ)) z := by fun_prop
    have := hjoint.comp (x := z) hemb
    simpa [Function.comp_def] using this
  have hcDnt : meromorphicOrderAt
      (fun w : ℂ => modularPhiChartDenominator M m n κ w τ) z ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_analytic_frequently_ne_zero hcDan
      (modularPhiChartDenominator_frequently_ne_zero M hM m n κ (z, τ) hpU)
  have hcDev : ∀ᶠ w : ℂ in 𝓝[≠] z,
      modularPhiChartDenominator M m n κ w τ ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hcDan.meromorphicAt).mp hcDnt
  -- the q denominator is analytic in the argument everywhere
  have hqDan : ∀ w : ℂ, AnalyticAt ℂ
      (fun v : ℂ => modularPhiQDenominator M n v τ) w := by
    intro w
    have hq1 : ‖e (etaMobius M τ)‖ < 1 := by
      have hηim : 0 < (etaMobius M τ).im := by
        have h := coe_smul_eq_etaMobius M (⟨τ, hτ⟩ : ℍ)
        rw [← h]
        simpa using (M • (⟨τ, hτ⟩ : ℍ)).im_pos
      exact norm_e_lt_one ⟨_, hηim⟩
    have hq0 : 0 < ‖e (etaMobius M τ)‖ := norm_pos_iff.mpr (e_ne_zero _)
    have hP : AnalyticAt ℂ (fun p : ℂ × ℂ => qPochhammer p.1 p.2)
        ((e (etaMobius M τ)) ^ n * e (w / etaDenom M τ), e (etaMobius M τ)) :=
      analyticOnNhd_qPochhammer_joint _ ⟨hq0, hq1⟩
    have hx : AnalyticAt ℂ (fun v : ℂ =>
        (e (etaMobius M τ)) ^ n * e (v / etaDenom M τ)) w := by
      have : AnalyticAt ℂ (fun v : ℂ => e (v / etaDenom M τ)) w := by
        unfold e
        fun_prop
      exact analyticAt_const.mul this
    have hpair : AnalyticAt ℂ (fun v : ℂ =>
        ((e (etaMobius M τ)) ^ n * e (v / etaDenom M τ), e (etaMobius M τ))) w :=
      hx.prod analyticAt_const
    have := hP.comp (x := w) hpair
    simpa [modularPhiQDenominator, Function.comp_def] using this
  -- a point where the q denominator does not vanish
  set w0 : ℂ := (1 - (n : ℂ)) * ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) with hw0def
  have hw0val : modularPhiQDenominator M n w0 τ =
      qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ)) := by
    unfold modularPhiQDenominator
    have hw0div : w0 / etaDenom M τ = (1 - (n : ℂ)) * etaMobius M τ := by
      rw [hw0def, etaMobius]
      field_simp
    rw [hw0div]
    have hsplit : e ((1 - (n : ℂ)) * etaMobius M τ) =
        e (etaMobius M τ) * (e (etaMobius M τ)) ^ (-n) := by
      rw [show (1 - (n : ℂ)) * etaMobius M τ =
          etaMobius M τ + (-n : ℤ) * etaMobius M τ from by push_cast; ring]
      rw [e_add', ← e_int_mul]
    rw [hsplit]
    have hcancel : (e (etaMobius M τ)) ^ n * (e (etaMobius M τ)) ^ (-n) = 1 := by
      rw [← zpow_add₀ (e_ne_zero (etaMobius M τ))]
      simp
    have hre : (e (etaMobius M τ)) ^ n *
        (e (etaMobius M τ) * (e (etaMobius M τ)) ^ (-n)) =
        ((e (etaMobius M τ)) ^ n * (e (etaMobius M τ)) ^ (-n)) *
          e (etaMobius M τ) := by ring
    rw [hre, hcancel, one_mul]
  have hq0η : 0 < ‖e (etaMobius M τ)‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hq1η : ‖e (etaMobius M τ)‖ < 1 := by
    have hηim : 0 < (etaMobius M τ).im := by
      have h := coe_smul_eq_etaMobius M (⟨τ, hτ⟩ : ℍ)
      rw [← h]
      simpa using (M • (⟨τ, hτ⟩ : ℍ)).im_pos
    exact norm_e_lt_one ⟨_, hηim⟩
  have hw0ne : modularPhiQDenominator M n w0 τ ≠ 0 := by
    rw [hw0val]
    exact qPochhammer_q_ne_zero _ hq0η hq1η
  have hw0nt : meromorphicOrderAt (fun w : ℂ => modularPhiQDenominator M n w τ) w0 ≠ ⊤ := by
    have h1 : meromorphicOrderAt (fun w : ℂ => modularPhiQDenominator M n w τ) w0 =
        ENat.map Nat.cast (analyticOrderAt (fun w : ℂ => modularPhiQDenominator M n w τ) w0) :=
      (hqDan w0).meromorphicOrderAt_eq
    have h2 : analyticOrderAt (fun w : ℂ => modularPhiQDenominator M n w τ) w0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hw0ne)
    rw [h1, h2]
    exact WithTop.zero_ne_top
  have hqDmer : MeromorphicOn (fun w : ℂ => modularPhiQDenominator M n w τ) Set.univ :=
    fun w _ => (hqDan w).meromorphicAt
  have hqDnt : meromorphicOrderAt (fun w : ℂ => modularPhiQDenominator M n w τ) z ≠ ⊤ := by
    intro htop
    exact (hqDmer.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ w0) (Set.mem_univ z) hw0nt) htop
  have hqDev : ∀ᶠ w : ℂ in 𝓝[≠] z, modularPhiQDenominator M n w τ ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero ((hqDan z).meromorphicAt)).mp hqDnt
  have hchartEv : ∀ᶠ w : ℂ in 𝓝[≠] z, (w, τ) ∈ modularPhiChartDomain M m n κ := by
    have hopen : IsOpen {w : ℂ | (w, τ) ∈ modularPhiChartDomain M m n κ} :=
      hU.preimage (by fun_prop)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (hopen.mem_nhds hpU)
  filter_upwards [hcDev, hqDev, hchartEv] with w hcDw hqDw hchartw
  rw [modularPhi_eq_chart M hM m n κ (w, τ) hchartw]
  simp only [modularPhiChart, modularPhiQProduct]
  rw [div_eq_div_iff hcDw hqDw]
  exact modularPhiChart_qProduct_cross_mul_aux M hM m n κ (w, τ) hchartw hτ

/-- Pointwise [RW26, (1)] nonzero product denominator. Same sources. -/
theorem modularPhi_eq_qProduct (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im)
    (hd : modularPhiQDenominator M n z τ ≠ 0) :
    modularPhi M m n z τ = modularPhiQProduct M m n z τ := by
  have hpdom : τ ∈ modularPhiDomain M := mem_modularPhiDomain_of_im_pos M hM hτ
  let κ : ℕ → ℤ := fun j => continuationIndex
    (modularPhiFactorPoint M m n j z τ).1 (modularPhiFactorPoint M m n j z τ).2
  have hb : AdmissibleB (Complex.sqrt (etaDenom M τ)) :=
    (modularPhi_sqrt_admissible M τ hpdom).1
  have hpU : (z, τ) ∈ modularPhiChartDomain M m n κ := by
    refine ⟨hpdom, ?_⟩
    intro j hj
    exact shiftedArgument_inStrip _ _ hb
  have hchart := modularPhi_eq_chart M hM m n κ (z, τ) hpU
  have hcross := modularPhiChart_qProduct_cross_mul_aux M hM m n κ (z, τ) hpU hτ
  -- the chart denominator cannot vanish here, else the q denominator would
  have hDne : modularPhiChartDenominator M m n κ z τ ≠ 0 := by
    intro hD
    have hz : (∏ j ∈ Finset.range (M 1 0).toNat,
        continuationDenominator (Complex.sqrt (etaDenom M τ))
          (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ)) (κ j)) = 0 := by
      simpa [modularPhiChartDenominator, modularPhiFactorPoint] using hD
    obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp hz
    have hDj : phiProductDenominator (Complex.sqrt (etaDenom M τ))
        (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ)) = 0 := by
      by_cases hk : 0 ≤ κ j
      · have hcN : continuationNumerator (Complex.sqrt (etaDenom M τ))
            (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ)) (κ j) ≠ 0 := by
          rw [continuationNumerator, if_pos hk]
          exact phi_ne_zero _ _ hb (hpU.2 j hj)
        have hcr := phiChart_product_cross_mul (Complex.sqrt (etaDenom M τ))
          (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ))
          (κ j) (by
            refine ⟨hb, ?_⟩
            rw [show (Complex.sqrt (etaDenom M τ)) ^ 2 = etaDenom M τ from by
              have h := EtaMultiplierAux.sqrt_mul_self (etaDenom M τ)
              simpa [sq] using h]
            exact im_etaDenom_pos_of_im_pos M hM hτ) (hpU.2 j hj)
        rw [hj0, mul_zero] at hcr
        rcases mul_eq_zero.mp hcr with h | h
        · exact absurd h hcN
        · exact h
      · have h1 : continuationDenominator (Complex.sqrt (etaDenom M τ))
            (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j z τ)) (κ j) = 1 := by
          simp [continuationDenominator, hk]
        rw [h1] at hj0
        exact absurd hj0 one_ne_zero
    have hqprod : modularPhiQDenominator M n z τ = 0 := by
      have := prod_phiProductDenominator_eq M hM m n z τ hτ
      rw [← this]
      exact Finset.prod_eq_zero hj hDj
    exact hd hqprod
  rw [hchart, modularPhiQProduct]
  simp only [modularPhiChart]
  rw [div_eq_div_iff hDne hd]
  simpa [modularPhiFactorPoint] using hcross

/--
Joint version of the upper product comparison, valid on common-zero
curves through a center. No 0/0 point value is inferred. [RW26, (1), (19)].
The proof uses `phiChart_product_cross_mul`.
-/
theorem modularPhiChart_qProduct_cross_mul (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (κ : ℕ → ℤ) (p : ℂ × ℂ)
    (hp : p ∈ modularPhiChartDomain M m n κ) (hτ : 0 < p.2.im) :
    modularPhiChartNumerator M m n κ p.1 p.2 * modularPhiQDenominator M n p.1 p.2 =
      modularPhiQNumerator m p.1 p.2 * modularPhiChartDenominator M m n κ p.1 p.2  := by
  exact modularPhiChart_qProduct_cross_mul_aux M hM m n κ p hp hτ

/--
[RW26, p. 6, §2.2] first variable shift. Stated as a germ even at
poles and removable q-product centers.
-/
theorem modularPhi_shift_aτb_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M m n (w + (M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhi M (m + M 0 0) (n + 1) w τ) := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := det_coe_int M
  have hc : M 1 0 ≠ 0 := hM.ne'
  have hk : ∀ j : ℕ, modularPhiIndex M (m + M 0 0) (n + 1) j =
      modularPhiIndex M m n j + M 0 1 := by
    intro j
    simp only [modularPhiIndex]
    rw [show M 1 1 * (m + M 0 0 + (j : ℤ)) - (n + 1) =
        (M 1 1 * (m + (j : ℤ)) - n) + M 0 1 * M 1 0 from by
      linarith]
    rw [Int.add_mul_ediv_right _ _ hc]
  refine Filter.EventuallyEq.of_eq (funext fun w => ?_)
  simp only [modularPhi, modularPhiFactorPoint, modularPhiFactorInput, modularPhiSArgument]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  rw [hk j]
  push_cast
  ring

/-- [RW26, p. 6, §2.2] second variable shift. -/
theorem modularPhi_shift_τ_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M m n (w + τ) τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhi M (m + 1) (n + M 1 1) w τ) := by
  have hk : ∀ j : ℕ, modularPhiIndex M (m + 1) (n + M 1 1) j =
      modularPhiIndex M m n j := by
    intro j
    simp only [modularPhiIndex]
    congr 1
    ring
  refine Filter.EventuallyEq.of_eq (funext fun w => ?_)
  simp only [modularPhi, modularPhiFactorPoint, modularPhiFactorInput, modularPhiSArgument]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  rw [hk j]
  push_cast
  ring

/-- [RW26, p. 6, §2.2] first variable shift. -/
theorem modularPhi_shift_T_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M m n (w + etaDenom M τ) τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhi M (m + M 1 0) n w τ) := by
  have hc : M 1 0 ≠ 0 := hM.ne'
  have hk : ∀ j : ℕ, modularPhiIndex M (m + M 1 0) n j =
      modularPhiIndex M m n j + M 1 1 := by
    intro j
    simp only [modularPhiIndex]
    rw [show M 1 1 * (m + M 1 0 + (j : ℤ)) - n =
        (M 1 1 * (m + (j : ℤ)) - n) + M 1 1 * M 1 0 from by ring]
    rw [Int.add_mul_ediv_right _ _ hc]
  refine Filter.EventuallyEq.of_eq (funext fun w => ?_)
  simp only [modularPhi, modularPhiFactorPoint, modularPhiFactorInput, modularPhiSArgument,
    etaDenom]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  rw [hk j]
  push_cast
  ring

/-- [RW26, p. 6, §2.2] second variable shift. -/
theorem modularPhi_shift_one_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M m n (w + 1) τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhi M m (n - M 1 0) w τ) := by
  have hc : M 1 0 ≠ 0 := hM.ne'
  have hk : ∀ j : ℕ, modularPhiIndex M m (n - M 1 0) j =
      modularPhiIndex M m n j + 1 := by
    intro j
    simp only [modularPhiIndex]
    rw [show M 1 1 * (m + (j : ℤ)) - (n - M 1 0) =
        (M 1 1 * (m + (j : ℤ)) - n) + 1 * M 1 0 from by ring]
    rw [Int.add_mul_ediv_right _ _ hc]
  refine Filter.EventuallyEq.of_eq (funext fun w => ?_)
  simp only [modularPhi, modularPhiFactorPoint, modularPhiFactorInput, modularPhiSArgument]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  rw [hk j]
  push_cast
  ring

/--
[RW26, p. 6, §2.2] m-index shift, with division only in the germ.
The denominator factor can vanish at the center.

Write `A j` and `B j` for the `j`-th
factors of the products for `(m,n)` and `(m+1,n)`. Since
`modularPhiIndex M (m+1) n j = modularPhiIndex M m n (j+1)`, the factor sets
overlap in `c-1` factors: `A (j+1) = B j` identically for `j < c`. The two
extra factors are `A 0` and `B (c-1)`, whose affine inputs differ by
`i (c τ + d) / sqrt(c τ + d) = i sqrt(c τ + d)`, i.e. by one half-period step
of `phiExtended_difference_b`. That one-step germ identity reads
`phiExtended b (w - i b / 2) = (1 + exp (2 π b w)) * phiExtended b (w + i b / 2)`,
and its scalar factor at this input is `1 - (e τ)^m * e w` by
`e_factorInput_eq`. Hence `Phi_mn = (1 - (e τ)^m e w) * Phi_(m+1)n` as germs.
Dividing by the non-identically-zero germ `1 - (e τ)^m e w` gives the claim.
The argument uses the `Finset.range` reindexing
(`Finset.prod_range_succ`/`prod_range_succ'` with `c = (c-1)+1`) together with
the transfer of the half-period germ through the affine map `w ↦ arg 0 w`;
neither uses any new analysis.
-/
theorem modularPhi_index_m_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M (m + 1) n w τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhi M m n w τ / (1 - (e τ) ^ m * e w)) := by
  let b := Complex.sqrt (etaDenom M τ)
  have hb : AdmissibleB b := (modularPhi_sqrt_admissible M τ hτ).1
  have hbne : b ≠ 0 := (modularPhi_sqrt_admissible M τ hτ).2.2
  have hb2 : b ^ 2 = etaDenom M τ := (modularPhi_sqrt_admissible M τ hτ).2.1
  let c := (M 1 0).toNat
  have hc : (c : ℤ) = M 1 0 := Int.toNat_of_nonneg hM.le
  obtain ⟨k, hk⟩ : ∃ k : ℕ, c = k + 1 := ⟨c - 1, by dsimp [c]; omega⟩
  let A := fun (j : ℕ) (w : ℂ) => phiExtended b
    (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j w τ))
  have hindex (j : ℕ) : modularPhiIndex M (m + 1) n j =
      modularPhiIndex M m n (j + 1) := by
    unfold modularPhiIndex
    congr 1
    push_cast
    ring
  have hshift (j : ℕ) (w : ℂ) :
      phiExtended (modularPhiFactorPoint M (m + 1) n j w τ).1
        (modularPhiFactorPoint M (m + 1) n j w τ).2 = A (j + 1) w := by
    dsimp [A, modularPhiFactorPoint]
    congr 2
    simp only [modularPhiFactorInput, hindex, Nat.cast_add, Nat.cast_one, Int.cast_add,
      Int.cast_one]
    ring
  have hprod (w : ℂ) : modularPhi M m n w τ =
      (∏ j ∈ Finset.range k, A (j + 1) w) * A 0 w := by
    change (∏ j ∈ Finset.range c, A j w) = _
    rw [hk, Finset.prod_range_succ']
  have hprod' (w : ℂ) : modularPhi M (m + 1) n w τ =
      (∏ j ∈ Finset.range k, A (j + 1) w) * A c w := by
    have h : modularPhi M (m + 1) n w τ = ∏ j ∈ Finset.range c, A (j + 1) w := by
      apply Finset.prod_congr rfl
      intro j _
      exact hshift j w
    rw [h, hk, Finset.prod_range_succ]
  have hindexc : modularPhiIndex M m n c = modularPhiIndex M m n 0 + M 1 1 := by
    simp only [modularPhiIndex, hc, Nat.cast_zero, add_zero]
    rw [show M 1 1 * (m + M 1 0) - n =
      (M 1 1 * m - n) + M 1 1 * M 1 0 by ring]
    exact Int.add_mul_ediv_right _ _ hM.ne'
  have hinputc (w : ℂ) : modularPhiFactorInput M m n c w τ =
      modularPhiFactorInput M m n 0 w τ + etaDenom M τ := by
    have hcC : (c : ℂ) = (M 1 0 : ℂ) := by exact_mod_cast hc
    simp only [modularPhiFactorInput, hcC, hindexc, Nat.cast_zero, Int.cast_add, etaDenom]
    ring
  let u := fun w : ℂ => modularPhiSArgument (etaDenom M τ)
    (modularPhiFactorInput M m n 0 w τ) + Complex.I * b / 2
  have hu (w : ℂ) : u w = Complex.I / b * w + u 0 := by
    dsimp [u, modularPhiSArgument, modularPhiFactorInput, b]
    ring
  have huinj : Function.Injective u := by
    intro x y h
    rw [hu x, hu y] at h
    exact mul_left_cancel₀ (div_ne_zero Complex.I_ne_zero hbne) (add_right_cancel h)
  have ht : Tendsto u (𝓝[≠] z) (𝓝[≠] u z) := by
    have hcont : ContinuousAt u z := by
      have heq : u = fun w => Complex.I / b * w + u 0 := funext hu
      rw [heq]
      fun_prop
    apply hcont.continuousWithinAt.tendsto_nhdsWithin
    intro w hw
    exact fun h => hw (huinj h)
  have hminus (w : ℂ) : u w - Complex.I * b / 2 =
      modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n 0 w τ) := by
    dsimp [u]
    ring
  have hplus (w : ℂ) : u w + Complex.I * b / 2 =
      modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n c w τ) := by
    rw [hinputc]
    change (Complex.I * modularPhiFactorInput M m n 0 w τ / b - Complex.I * b / 2 +
      Complex.I / (2 * b) + Complex.I * b / 2) + Complex.I * b / 2 =
      Complex.I * (modularPhiFactorInput M m n 0 w τ + etaDenom M τ) / b -
        Complex.I * b / 2 + Complex.I / (2 * b)
    rw [← hb2]
    field_simp
    ring
  have hphase (w : ℂ) : continuationFactor b (u w) = 1 - (e τ) ^ m * e w := by
    have hexp : 2 * (Real.pi : ℂ) * b * u w =
        2 * (Real.pi : ℂ) * Complex.I * modularPhiFactorInput M m n 0 w τ +
          Real.pi * Complex.I := by
      change 2 * (Real.pi : ℂ) * b *
          (Complex.I * modularPhiFactorInput M m n 0 w τ / b - Complex.I * b / 2 +
            Complex.I / (2 * b) + Complex.I * b / 2) = _
      field_simp
      ring
    rw [continuationFactor, hexp, Complex.exp_add, Complex.exp_pi_mul_I]
    change 1 + e (modularPhiFactorInput M m n 0 w τ) * (-1) = _
    rw [e_factorInput_eq]
    simp only [Nat.cast_zero, add_zero]
    ring
  have hnt : meromorphicOrderAt (continuationFactor b) (u z) ≠ ⊤ := by
    have h := meromorphicOrderAt_continuationFactor_add b 0 (u z) hbne
    simp only [add_zero] at h
    rw [h]
    split_ifs <;> simp
  have hne : ∀ᶠ v : ℂ in 𝓝[≠] u z, continuationFactor b v ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (analyticAt_continuationFactor b (u z)).meromorphicAt).mp hnt
  filter_upwards [ht.eventually (phiExtended_difference_b b (u z) hb),
    ht.eventually hne] with w hw hn
  rw [hminus w, hplus w] at hw
  change A 0 w = continuationFactor b (u w) * A c w at hw
  rw [hprod w, hprod' w, ← hphase w]
  apply (eq_div_iff hn).2
  rw [hw]
  ring

/--
[RW26, p. 6, §2.2] n-index shift. Even this multiplied
identity is a germ, not an unconditional identity of assigned pole values.

Passing from `n` to `n+1` lowers the
integer quotient `modularPhiIndex M m n j` by one exactly at the unique `j`
with `modularPhiResidue M m n j = 0` (existence and uniqueness are
`modularPhiResidue_permutation`), and leaves every other factor unchanged.
The two products therefore differ in a single factor, whose affine input
changes by `-i / sqrt(c τ + d)`, i.e. by two half-period steps of the dual
difference equation `phiExtended_difference_inv_b`. Applying that germ
identity twice gives the scalar `1 - e(η)^n e(w / etaDenom)` with
`η = etaMobius M τ`, using `e_factorInput_div_etaDenom` at the zero residue.
The argument is the identification of the unique zero residue and
the two-step germ transfer; the single-factor comparison avoids every
`Finset` reindexing.
-/
theorem modularPhi_index_n_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M m (n + 1) w τ) =ᶠ[𝓝[≠] z]
      (fun w => (1 - (e (etaMobius M τ)) ^ n * e (w / etaDenom M τ)) *
        modularPhi M m n w τ) := by
  classical
  let b := Complex.sqrt (etaDenom M τ)
  have hb : AdmissibleB b := (modularPhi_sqrt_admissible M τ hτ).1
  have hbne : b ≠ 0 := (modularPhi_sqrt_admissible M τ hτ).2.2
  have hb2 : b ^ 2 = etaDenom M τ := (modularPhi_sqrt_admissible M τ hτ).2.1
  let c := (M 1 0).toNat
  have hp := modularPhiResidue_permutation M hM m n
  have hmem : (0 : ℕ) ∈ Finset.range c := by dsimp [c]; simp only [Finset.mem_range]; omega
  rw [← hp.2.1] at hmem
  obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp hmem
  have hrzero : modularPhiResidue M m n j = 0 := by
    have := (hp.1 j).1
    omega
  have hindex (i : ℕ) : modularPhiIndex M m (n + 1) i =
      if modularPhiResidue M m n i = 0 then modularPhiIndex M m n i - 1
      else modularPhiIndex M m n i := by
    have hres := hp.1 i
    have hdef : M 1 1 * (m + (i : ℤ)) - n =
        M 1 0 * modularPhiIndex M m n i + modularPhiResidue M m n i := by
      unfold modularPhiResidue
      ring
    change (M 1 1 * (m + (i : ℤ)) - (n + 1)) / M 1 0 = _
    by_cases hr : modularPhiResidue M m n i = 0
    · rw [if_pos hr, Int.ediv_eq_iff_of_pos hM]
      constructor <;> nlinarith
    · have hpos : 0 < modularPhiResidue M m n i := by omega
      rw [if_neg hr, Int.ediv_eq_iff_of_pos hM]
      constructor <;> nlinarith
  let A := fun (i : ℕ) (w : ℂ) => phiExtended b
    (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n i w τ))
  let B := fun (i : ℕ) (w : ℂ) => phiExtended b
    (modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m (n + 1) i w τ))
  have hsame (i : ℕ) (hi : i ∈ Finset.range c) (hij : i ≠ j) (w : ℂ) : B i w = A i w := by
    have hr : modularPhiResidue M m n i ≠ 0 := by
      intro hzero
      apply hij
      apply hp.2.2 hi hj
      change (modularPhiResidue M m n i).toNat = (modularPhiResidue M m n j).toNat
      rw [hzero, hrzero]
    dsimp [A, B, modularPhiFactorInput]
    rw [hindex i, if_neg hr]
  have hinput (w : ℂ) : modularPhiFactorInput M m (n + 1) j w τ =
      modularPhiFactorInput M m n j w τ - 1 := by
    simp only [modularPhiFactorInput, hindex j, if_pos hrzero, Int.cast_sub, Int.cast_one]
    ring
  let u := fun w : ℂ => modularPhiSArgument (etaDenom M τ)
    (modularPhiFactorInput M m n j w τ) - Complex.I * b⁻¹ / 2
  have hu (w : ℂ) : u w = Complex.I / b * w + u 0 := by
    dsimp [u, modularPhiSArgument, modularPhiFactorInput, b]
    ring
  have huinj : Function.Injective u := by
    intro x y h
    rw [hu x, hu y] at h
    exact mul_left_cancel₀ (div_ne_zero Complex.I_ne_zero hbne) (add_right_cancel h)
  have ht : Tendsto u (𝓝[≠] z) (𝓝[≠] u z) := by
    have hcont : ContinuousAt u z := by
      have heq : u = fun w => Complex.I / b * w + u 0 := funext hu
      rw [heq]
      fun_prop
    apply hcont.continuousWithinAt.tendsto_nhdsWithin
    intro w hw
    exact fun h => hw (huinj h)
  have hminus (w : ℂ) : u w - Complex.I * b⁻¹ / 2 =
      modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m (n + 1) j w τ) := by
    rw [hinput]
    change (Complex.I * modularPhiFactorInput M m n j w τ / b - Complex.I * b / 2 +
      Complex.I / (2 * b) - Complex.I * b⁻¹ / 2) - Complex.I * b⁻¹ / 2 =
      Complex.I * (modularPhiFactorInput M m n j w τ - 1) / b -
        Complex.I * b / 2 + Complex.I / (2 * b)
    ring
  have hplus (w : ℂ) : u w + Complex.I * b⁻¹ / 2 =
      modularPhiSArgument (etaDenom M τ) (modularPhiFactorInput M m n j w τ) := by
    dsimp [u]
    ring
  have hphase (w : ℂ) : continuationFactor b⁻¹ (u w) =
      1 - (e (etaMobius M τ)) ^ n * e (w / etaDenom M τ) := by
    have hexp : 2 * (Real.pi : ℂ) * b⁻¹ * u w =
        2 * (Real.pi : ℂ) * Complex.I *
          (modularPhiFactorInput M m n j w τ / etaDenom M τ) - Real.pi * Complex.I := by
      change 2 * (Real.pi : ℂ) * b⁻¹ *
          (Complex.I * modularPhiFactorInput M m n j w τ / b - Complex.I * b / 2 +
            Complex.I / (2 * b) - Complex.I * b⁻¹ / 2) = _
      rw [← hb2]
      field_simp
      ring
    rw [continuationFactor, hexp, Complex.exp_sub, Complex.exp_pi_mul_I]
    change 1 + e (modularPhiFactorInput M m n j w τ / etaDenom M τ) / (-1) = _
    rw [e_factorInput_div_etaDenom M hM m n j w τ hτ, hrzero, add_zero]
    ring
  filter_upwards [ht.eventually (phiExtended_difference_inv_b b (u z) hb)] with w hw
  rw [hminus w, hplus w, hphase w] at hw
  change B j w = (1 - (e (etaMobius M τ)) ^ n * e (w / etaDenom M τ)) * A j w at hw
  have hrest : (∏ i ∈ (Finset.range c).erase j, B i w) =
      ∏ i ∈ (Finset.range c).erase j, A i w := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hsame i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1 w
  change (∏ i ∈ Finset.range c, B i w) =
    (1 - (e (etaMobius M τ)) ^ n * e (w / etaDenom M τ)) * ∏ i ∈ Finset.range c, A i w
  rw [← Finset.mul_prod_erase _ (fun i => B i w) hj,
    ← Finset.mul_prod_erase _ (fun i => A i w) hj, hw, hrest]
  ring

#check Complex.slitPlane
#check Complex.cpow_nat_inv_pow
#check EtaMultiplierAux.sqrt_mul_self
#check Complex.differentiableAt_sqrt
#check etaDenom_mem_slitPlane
#check phiExtended_joint_local_quotient
#check phiExtended_eq_phiChart
#check phiChart_pointwise
#check continuationDenominator_frequently_ne_zero
#check qPochhammer_residue_classes
#check Finset.analyticAt_fun_prod
#print modularPhiIndex
#print modularPhi
#print modularPhi_joint_local_quotient
#print modularPhi_S_argument
#print axioms modularPhi
#print axioms modularPhiChartNumerator
#print axioms modularPhi_joint_local_quotient

end SICLean.L4
