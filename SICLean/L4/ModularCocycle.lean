import SICLean.L4.ModularPhi
import SICLean.L4.ModularCocycleAux
import SICLean.L4.ModularCocycleMatrixAux
import SICLean.L4.ModularCocycleUpperAux
import SICLean.L4.ModularCocycleUnitAux
import SICLean.L4.ModularCocycleReflectionAux
import SICLean.L4.ModularCocycleReflectionPhaseAux
import SICLean.L4.ModularCocycleContinuationAux

set_option autoImplicit false

/-!
# Local cocycles, positive iterates and modular reflection

The file has 20 concrete definitions. Auxiliary
modules supply the finite algebra, analytic charts and phase normalization.
No definition selects a function satisfying the desired laws.

[RW26, p. 2, p. 6, p. 14, (1), (16)--(18), Prop. 1, Prop. 8].

The positive-c matrices do not form a group or a multiplicative semigroup.
Translations have a separate finite rational definition. The wrapper
`modularPhiConstructed` is interpreted only under `ModularPhiSupported`.
In particular it never interprets the empty product at c≤0 as the Φ of [RW26].
All three supported-matrix hypotheses in a cocycle are explicit.

Germs mean eventual equality on `𝓝[≠] z` in one complex z variable.
Two-variable identities are analytic-chart cross products, including their
centers, rather than equality away from just one point of ℂ². Pointwise
corollaries require continuity of the specified representatives at the
center. Nonnegative meromorphic order alone does not supply that continuity.
The integer-translation identity is stronger: its finite factors have
identical arguments, so it respects even the prescribed pole values.

There are no Fourier or pentagon assertions here. Divisor avoidance and
fixed-point removable values remain, quotient-group special values and
their separately normalized zero class remain. The inverse-reflection
interface constructs δM⁻¹δ with positive c and never constructs Φ for M⁻¹.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane

namespace SICLean.L4

open ModularCocycleUpperAux

/--
[RW26, p. 2, (1)] cancelled using Appendix A.1 (50)--(52),
[RW26, p. 28]. For every translation T^k the result is independent
of k. This is a finite integer q symbol, including negative n-m.
-/
def modularPhiTranslation (m n : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammerInt ((e τ) ^ m * e z) (e τ) (n - m)

/-- Explicit numerator of the translation chart; same source as above. -/
def modularPhiTranslationNumerator (m n : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammerIntNumerator ((e τ) ^ m * e z) (e τ) (n - m)

/-- Explicit denominator, not an infinite product at real τ. Same source. -/
def modularPhiTranslationDenominator (m n : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammerIntDenominator ((e τ) ^ m * e z) (e τ) (n - m)

/--
A condition on matrix entries, not an assumed cocycle or meromorphy law.
-/
def ModularPhiSupported (M : SL(2, ℤ)) : Prop :=
  0 < M 1 0 ∨ ∃ k : ℤ, M = ModularGroup.T ^ k

/-- The positive-c finite product defined above, or the separately defined finite
translation expression. Meaning is asserted only for supported matrices. -/
def modularPhiConstructed (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℂ :=
  if 0 < M 1 0 then modularPhi M m n z τ
  else modularPhiTranslation m n z τ

/--
Concrete chart numerator for the above wrapper. No analytic property
is built into this definition. [RW26, (19), (50)--(52)].
-/
def modularPhiConstructedNumerator (M : SL(2, ℤ)) (m n : ℤ)
    (κ : ℕ → ℤ) (z τ : ℂ) : ℂ :=
  if 0 < M 1 0 then modularPhiChartNumerator M m n κ z τ
  else modularPhiTranslationNumerator m n z τ

/-- Concrete chart denominator; sources as for its numerator. -/
def modularPhiConstructedDenominator (M : SL(2, ℤ)) (m n : ℤ)
    (κ : ℕ → ℤ) (z τ : ℂ) : ℂ :=
  if 0 < M 1 0 then modularPhiChartDenominator M m n κ z τ
  else modularPhiTranslationDenominator m n z τ

/-- Fixed-index chart domain. The translation chart is valid everywhere,
including its denominator zeros, as a meromorphic quotient chart. -/
def modularPhiConstructedChartDomain (M : SL(2, ℤ)) (m n : ℤ)
    (κ : ℕ → ℤ) : Set (ℂ × ℂ) :=
  if 0 < M 1 0 then modularPhiChartDomain M m n κ else Set.univ

/--
[RW26, p. 6] actual action on (z,τ), with total division only
outside the declared domain.
-/
def modularCocyclePullback (M : SL(2, ℤ)) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1 / etaDenom M p.2, etaMobius M p.2)

/-- All three constructed parameter domains in (17), with the order M*N.
Matrix support is a separate hypothesis, not part of this open set. -/
def modularCocycleDomain (M N : SL(2, ℤ)) : Set ℂ :=
  {τ | τ ∈ modularPhiDomain N ∧
    etaMobius N τ ∈ modularPhiDomain M ∧ τ ∈ modularPhiDomain (M * N)}

/--
[RW26, p. 6, (18)]. The chain has initial index ι 0 and final
index ι r. In particular its adjacent indices match, without an implicit
choice of intermediate integers. The r=0 product is empty.
-/
def modularPhiIterationProduct (M : SL(2, ℤ)) (ι : ℕ → ℤ) (r : ℕ)
    (z τ : ℂ) : ℂ :=
  ∏ j ∈ Finset.range r,
    modularPhiConstructed M (ι j) (ι (j + 1))
      (z / etaDenom (M ^ j) τ) (etaMobius (M ^ j) τ)

/-- Explicit finite list of parameter-domain checks needed by (18). -/
def modularPhiIterationDomain (M : SL(2, ℤ)) (r : ℕ) : Set ℂ :=
  {τ | τ ∈ modularPhiDomain (M ^ r) ∧
    ∀ j ∈ Finset.range r, τ ∈ modularPhiDomain (M ^ j) ∧
      etaMobius (M ^ j) τ ∈ modularPhiDomain M}

/-- [RW26, p. 6, Prop. 1]. -/
def modularBernoulliTwo (x : ℂ) : ℂ := x ^ 2 - x + 1 / 6

/--
[RW26, p. 6, Prop. 1] r=m+1, n=n_old+1.
This includes the non-fixed-point term.
-/
def modularReflectionPolynomial (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * ((M 1 0 : ℂ) * z ^ 2 / etaDenom M τ +
    (2 * (r : ℂ) - 1 - (2 * (n : ℂ) - 1) / etaDenom M τ) * z +
    modularBernoulliTwo (r : ℂ) * τ -
    modularBernoulliTwo (n : ℂ) * etaMobius M τ)

/-- The exponent r+n is an integer power,
including negative indices; μ is the already defined actual eta quotient.
-/
def modularReflectionFactor (M : SL(2, ℤ)) (r n : ℤ) (z τ : ℂ) : ℂ :=
  (etaMultiplier M) ^ (-2 : ℤ) * (-1 : ℂ) ^ (r + n) *
    e (modularReflectionPolynomial M r n z τ)

/--
Explicit matrix δM⁻¹δ, δ=diag(1,-1); its lower left entry is c_M.
-/
def modularInverseReflectionMatrix (M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![M 1 1, M 0 1; M 1 0, M 0 0]

/--
Determinant bookkeeping for the preceding concrete matrix, using det M = 1.
-/
theorem modularInverseReflectionMatrix_det (M : SL(2, ℤ)) :
    (modularInverseReflectionMatrix M).det = 1 := by
  have h := det_coe_int M
  simpa [modularInverseReflectionMatrix, Matrix.det_fin_two, mul_comm] using h

/-- Determinant-one packaging of the explicit matrix, with no function
choice and no analytic property in its definition. -/
def modularInverseReflection (M : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨modularInverseReflectionMatrix M, modularInverseReflectionMatrix_det M⟩

/--
[RW26, p. 2, (2)]. This is only the argument used by later
special values; no F function or zero-class normalization is defined here.
-/
def modularPhiSpecialArgument (M : SL(2, ℤ)) (u : Fin 2 → ℤ) (τ : ℂ) : ℂ :=
  ((u 0 : ℂ) * τ + (u 1 : ℂ)) / ((etaDenom M τ)⁻¹ - 1)

/--
Original factors for Prop. 8 [RW26, p. 14]: chain (u₁,0...,0)
for Γ=M^r. The indices are those of the base matrix M, not Γ's trivial action.
-/
def modularPhiUnitFactor (M : SL(2, ℤ)) (r : ℕ) (u : Fin 2 → ℤ)
    (j : ℕ) (τ : ℂ) : ℂ :=
  modularPhi M (if j = 0 then u 0 else 0) 0
    (modularPhiSpecialArgument (M ^ r) u τ / etaDenom M τ ^ j) τ

/-- Cycled chain ((uM)₁,u₁,0,...,0), valid for r≥2 in Prop. 8.
This is an explicit list of factors, not an assumed invariant product. -/
def modularPhiCycledUnitFactor (M : SL(2, ℤ)) (r : ℕ) (u : Fin 2 → ℤ)
    (j : ℕ) (τ : ℂ) : ℂ :=
  modularPhi M
    (if j = 0 then (Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) 0
      else if j = 1 then u 0 else 0)
    (if j = 0 then u 0 else 0)
    (modularPhiSpecialArgument (M ^ r)
      (Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) τ / etaDenom M τ ^ j) τ

/-! ## Separate translations and their concrete charts -/

/--
Translation numerator and denominator are jointly analytic, even at a
real root of unity q. [RW26, p. 28, (50)--(51)]. This does not assert regularity of a quotient.
-/
theorem modularPhiTranslation_joint_analytic (m n : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiTranslationNumerator m n p.1 p.2)
      Set.univ ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => modularPhiTranslationDenominator m n p.1 p.2)
      Set.univ := by
  exact finite_symbol_joint_analytic m (n - m)

/--
Nontriviality is a conclusion about the finite denominator, not a field
of a meromorphy structure. [RW26, p. 28, (50)--(51)].
-/
theorem modularPhiTranslationDenominator_frequently_ne_zero (m n : ℤ) (z τ : ℂ) :
    ∃ᶠ w : ℂ in 𝓝 z, modularPhiTranslationDenominator m n w τ ≠ 0 := by
  exact (finite_denominator_eventually_ne_zero m (n - m) z τ).frequently.filter_mono
    nhdsWithin_le_nhds

/--
Fixed-τ meromorphy and the exact diagonal value, including the center
where the raw infinite q quotient is 0/0. [RW26, p. 2, p. 28, (1), (50)--(52)].
-/
theorem modularPhiTranslation_meromorphic (m n : ℤ) (τ : ℂ) :
    MeromorphicOn (fun z => modularPhiTranslation m n z τ) Set.univ ∧
    (∀ z : ℂ, modularPhiTranslation m m z τ = 1) := by
  constructor
  · intro z hz
    have hn := (finite_symbol_joint_analytic m (n - m)).1 (z, τ) (Set.mem_univ _)
    have hd := (finite_symbol_joint_analytic m (n - m)).2 (z, τ) (Set.mem_univ _)
    have hemb : AnalyticAt ℂ (fun w : ℂ => (w, τ)) z := by fun_prop
    exact (hn.comp (x := z) hemb).meromorphicAt.div
      (hd.comp (x := z) hemb).meromorphicAt
  · intro z
    simp [modularPhiTranslation, qPochhammerInt, qPochhammerIntNumerator,
      qPochhammerIntDenominator, qPochhammerNat]

/--
Identification with [RW26, (1)] T^k, as a punctured z germ only.
[RW26, p. 2, p. 28, (52)].
-/
theorem modularPhiTranslation_eq_qProduct_germ (k m n : ℤ) (z τ : ℂ)
    (hτ : 0 < τ.im) :
    (fun w => modularPhiTranslation m n w τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhiQProduct (ModularGroup.T ^ k) m n w τ) := by
  exact finite_symbol_eq_qProduct_germ k m n z τ hτ

/--
The positive-c branch reuses the modular product. [RW26, p. 6, (19)].
-/
theorem modularPhiConstructed_of_pos (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) :
    modularPhiConstructed M m n z τ = modularPhi M m n z τ := by
  simp [modularPhiConstructed, hM]

/--
Translations use their separate finite definition, including k=0.
[RW26, p. 2, p. 28, (1), (50)--(52)].
-/
theorem modularPhiConstructed_translation (k m n : ℤ) (z τ : ℂ) :
    modularPhiConstructed (ModularGroup.T ^ k) m n z τ =
      modularPhiTranslation m n z τ := by
  simp [modularPhiConstructed, ModularGroup.coe_T_zpow]

/-! ## Local cocycle, with all support and domain checks explicit -/

/--
Algebra behind [RW26, p. 6, (17)]: no action law at a zero
denominator is claimed. It also checks the product's automorphy factor.
-/
theorem modularCocycle_automorphy (M N : SL(2, ℤ)) (τ : ℂ)
    (hN : etaDenom N τ ≠ 0) (hM : etaDenom M (etaMobius N τ) ≠ 0) :
    etaDenom (M * N) τ = etaDenom M (etaMobius N τ) * etaDenom N τ ∧
    etaDenom (M * N) τ ≠ 0 ∧
    etaMobius (M * N) τ = etaMobius M (etaMobius N τ) := by
  exact ModularCocycleMatrixAux.automorphy M N τ hN hM

/--
Open common domain for (17); its nonzero N denominator is already
forced by N's slit-plane condition. [RW26, p. 2].
-/
theorem modularCocycleDomain_isOpen (M N : SL(2, ℤ)) :
    IsOpen (modularCocycleDomain M N) := by
  exact ModularCocycleMatrixAux.cocycleDomain_isOpen M N

/--
Upper-half-plane (17), including either/both translation factors.
There is no implicit claim that support is closed under multiplication.
[RW26, p. 6].
-/
theorem modularPhi_cocycle_upper_germ (M N : SL(2, ℤ))
    (hM : ModularPhiSupported M) (hN : ModularPhiSupported N)
    (hMN : ModularPhiSupported (M * N)) (m k n : ℤ) (z τ : ℂ)
    (hτ : 0 < τ.im) :
    (fun w => modularPhiConstructed (M * N) m n w τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhiConstructed M k n (w / etaDenom N τ) (etaMobius N τ) *
        modularPhiConstructed N m k w τ) := by
  have hNne := etaDenom_ne_zero_upper N hτ
  have hNim := etaMobius_im_pos N hτ
  have hMne := etaDenom_ne_zero_upper M hNim
  obtain ⟨hden, hMNne, hmob⟩ := modularCocycle_automorphy M N τ hNne hMne
  have hL := constructed_eq_qProduct_germ (M * N) hMN m n z τ hτ
  have hR₁ := (constructed_eq_qProduct_germ M hM k n
    (z / etaDenom N τ) (etaMobius N τ) hNim).comp_tendsto
      (tendsto_div_nhdsNE _ _ hNne)
  have hR₂ := constructed_eq_qProduct_germ N hN m k z τ hτ
  exact hL.trans ((qProduct_cocycle_germ M N m k n z τ hτ hden hmob).trans
    (hR₁.mul hR₂).symm)

/--
Positive real factors checked individually. Product positivity is a
conclusion. The ball meets both sides of the real axis.
[RW26, p. 6, (17)].
-/
theorem modularCocycle_real_neighborhood (M N : SL(2, ℤ)) (τ₀ : ℝ)
    (hN : 0 < (etaDenom N (τ₀ : ℂ)).re)
    (hM : 0 < (etaDenom M (etaMobius N (τ₀ : ℂ))).re) :
    0 < (etaDenom (M * N) (τ₀ : ℂ)).re ∧
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (τ₀ : ℂ) δ ⊆ modularCocycleDomain M N := by
  exact ModularCocycleMatrixAux.cocycle_real_neighborhood M N τ₀ hN hM

/--
Joint, denominator-cleared version of local (17), for any valid
fixed chart vectors, including the finite translation charts. This is the
interface for moving parameters. No punctured-ℂ² assertion.
[RW26, p. 6, (17)]; explicit joint charts.
-/
theorem modularPhi_cocycle_real_chart_cross_mul (M N : SL(2, ℤ))
    (hM : ModularPhiSupported M) (hN : ModularPhiSupported N)
    (hMN : ModularPhiSupported (M * N)) (m k n : ℤ) (τ₀ : ℝ)
    (hTN : 0 < (etaDenom N (τ₀ : ℂ)).re)
    (hTM : 0 < (etaDenom M (etaMobius N (τ₀ : ℂ))).re) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (τ₀ : ℂ) δ ⊆ modularCocycleDomain M N ∧
      ∀ (κMN κM κN : ℕ → ℤ) (p : ℂ × ℂ), p.2 ∈ Metric.ball (τ₀ : ℂ) δ →
        p ∈ modularPhiConstructedChartDomain (M * N) m n κMN →
        modularCocyclePullback N p ∈ modularPhiConstructedChartDomain M k n κM →
        p ∈ modularPhiConstructedChartDomain N m k κN →
        modularPhiConstructedNumerator (M * N) m n κMN p.1 p.2 *
            modularPhiConstructedDenominator M k n κM
              (modularCocyclePullback N p).1 (modularCocyclePullback N p).2 *
            modularPhiConstructedDenominator N m k κN p.1 p.2 =
          modularPhiConstructedNumerator M k n κM
              (modularCocyclePullback N p).1 (modularCocyclePullback N p).2 *
            modularPhiConstructedNumerator N m k κN p.1 p.2 *
            modularPhiConstructedDenominator (M * N) m n κMN p.1 p.2 := by
  exact ModularCocycleContinuationAux.real_chart_cross_mul M N hM hN hMN m k n τ₀ hTN hTM
    (fun z τ hτ => modularPhi_cocycle_upper_germ M N hM hN hMN m k n z τ hτ)

/--
Local continued cocycle on the entire common small complex ball, not
just an upper limit. [RW26, p. 6, (17)].
The positive conditions concern j_N(τ₀) and j_M(Nτ₀), in that order.
-/
theorem modularPhi_cocycle_real_germ (M N : SL(2, ℤ))
    (hM : ModularPhiSupported M) (hN : ModularPhiSupported N)
    (hMN : ModularPhiSupported (M * N)) (m k n : ℤ) (τ₀ : ℝ)
    (hTN : 0 < (etaDenom N (τ₀ : ℂ)).re)
    (hTM : 0 < (etaDenom M (etaMobius N (τ₀ : ℂ))).re) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (τ₀ : ℂ) δ ⊆ modularCocycleDomain M N ∧
      ∀ τ ∈ Metric.ball (τ₀ : ℂ) δ, ∀ z : ℂ,
        (fun w => modularPhiConstructed (M * N) m n w τ) =ᶠ[𝓝[≠] z]
          (fun w => modularPhiConstructed M k n
              (w / etaDenom N τ) (etaMobius N τ) *
            modularPhiConstructed N m k w τ) := by
  exact ModularCocycleContinuationAux.real_germ M N hM hN hMN m k n τ₀ hTN hTM
    (fun z τ hτ => modularPhi_cocycle_upper_germ M N hM hN hMN m k n z τ hτ)

/--
Center-value corollary only for the specified continuous representatives.
No 0/0 center is filled by a germ. [RW26, p. 6, (17)]
explains why this restriction matters.
-/
theorem modularPhi_cocycle_real (M N : SL(2, ℤ))
    (hM : ModularPhiSupported M) (hN : ModularPhiSupported N)
    (hMN : ModularPhiSupported (M * N)) (m k n : ℤ) (z : ℂ) (τ₀ : ℝ)
    (hTN : 0 < (etaDenom N (τ₀ : ℂ)).re)
    (hTM : 0 < (etaDenom M (etaMobius N (τ₀ : ℂ))).re)
    (hL : ContinuousAt (fun w => modularPhiConstructed (M * N) m n w (τ₀ : ℂ)) z)
    (hR₁ : ContinuousAt (fun w => modularPhiConstructed M k n
      (w / etaDenom N (τ₀ : ℂ)) (etaMobius N (τ₀ : ℂ))) z)
    (hR₂ : ContinuousAt (fun w => modularPhiConstructed N m k w (τ₀ : ℂ)) z) :
    modularPhiConstructed (M * N) m n z (τ₀ : ℂ) =
      modularPhiConstructed M k n (z / etaDenom N (τ₀ : ℂ))
          (etaMobius N (τ₀ : ℂ)) * modularPhiConstructed N m k z (τ₀ : ℂ) := by
  obtain ⟨δ, hδ, hdom, heq⟩ := modularPhi_cocycle_real_germ M N hM hN hMN m k n τ₀ hTN hTM
  exact ModularCocycleAux.eq_of_germ hL (hR₁.mul hR₂)
    (heq (τ₀ : ℂ) (Metric.mem_ball_self hδ) z)

/--
Domain certificate for both factorizations A*M=(A*M*A⁻¹)*A.
The two composite lower-left entries are proved positive here; they are
not inferred from a fictitious closure of positive c. At the center the
two outer automorphy factors equal the original positive factors.
[RW26, p. 6, (17)].
-/
theorem modularPhi_basis_change_domain (M A : SL(2, ℤ))
    (hM : 0 < M 1 0) (hA : ModularPhiSupported A)
    (hC : 0 < (A * M * A⁻¹) 1 0) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hTM : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hTA : 0 < (etaDenom A (τ₀ : ℂ)).re) :
    0 < (A * M) 1 0 ∧ 0 < ((A * M * A⁻¹) * A) 1 0 ∧
    etaMobius (A * M * A⁻¹) (etaMobius A (τ₀ : ℂ)) = etaMobius A (τ₀ : ℂ) ∧
    etaDenom (A * M * A⁻¹) (etaMobius A (τ₀ : ℂ)) = etaDenom M (τ₀ : ℂ) ∧
    etaDenom A (etaMobius M (τ₀ : ℂ)) = etaDenom A (τ₀ : ℂ) ∧
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (τ₀ : ℂ) δ ⊆
      modularCocycleDomain A M ∩ modularCocycleDomain (A * M * A⁻¹) A := by
  have hA0 : 0 ≤ A 1 0 := by
    rcases hA with hA | ⟨k, rfl⟩
    · exact hA.le
    · simp [ModularGroup.coe_T_zpow]
  have hAM := ModularCocycleMatrixAux.c_mul_pos_fixedPoint M A hM hA0 τ₀ hfix hTM hTA
  have hmat : (A * M * A⁻¹) * A = A * M := by group
  have hcf := ModularCocycleMatrixAux.conjugate_fixedPoint M A (τ₀ : ℂ) hfix
    (ModularCocycleMatrixAux.denom_ne_zero_of_re_pos M _ hTM)
    (ModularCocycleMatrixAux.denom_ne_zero_of_re_pos A _ hTA)
  refine ⟨hAM, by simpa only [hmat] using hAM, hcf.1, hcf.2, by rw [hfix], ?_⟩
  obtain ⟨δ₁, hδ₁, hball₁⟩ :=
    (ModularCocycleMatrixAux.cocycle_real_neighborhood A M τ₀ hTM (by
      rw [hfix]; exact hTA)).2
  obtain ⟨δ₂, hδ₂, hball₂⟩ :=
    (ModularCocycleMatrixAux.cocycle_real_neighborhood (A * M * A⁻¹) A τ₀ hTA (by
      rw [hcf.2]; exact hTM)).2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro τ hτ
  exact ⟨hball₁ (Metric.ball_subset_ball (min_le_left _ _) hτ),
    hball₂ (Metric.ball_subset_ball (min_le_right _ _) hτ)⟩

/--
The actual crossed basis-change formula needed. No Φ for A⁻¹
appears. The four domain conditions, including Mτ∈D_A, are in the result.
Here t=d_A*m-c_A*n. [RW26, p. 6, (17)] and the four shifts.
At the center c_(A*M)=c_A/j_M+c_M*j_A>0 when c_A>0; for A=T^k it is c_M.
Cancellation of the A factor at a nonzero class remains.
-/
theorem modularPhi_basis_change_real_germ (M A : SL(2, ℤ))
    (hM : 0 < M 1 0) (hA : ModularPhiSupported A)
    (hC : 0 < (A * M * A⁻¹) 1 0) (m n : ℤ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hTM : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hTA : 0 < (etaDenom A (τ₀ : ℂ)).re) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ τ ∈ Metric.ball (τ₀ : ℂ) δ,
        τ ∈ modularPhiDomain M ∧ τ ∈ modularPhiDomain A ∧
        etaMobius M τ ∈ modularPhiDomain A ∧
        etaMobius A τ ∈ modularPhiDomain (A * M * A⁻¹)) ∧
      ∀ τ ∈ Metric.ball (τ₀ : ℂ) δ, ∀ z : ℂ,
        (fun w => modularPhi (A * M * A⁻¹) (A 1 1 * m - A 1 0 * n) 0
            (w / etaDenom A τ) (etaMobius A τ) *
          modularPhiConstructed A 0 0 (w + (m : ℂ) * τ + (n : ℂ)) τ) =ᶠ[𝓝[≠] z]
        (fun w => modularPhi M m 0 w τ *
          modularPhiConstructed A 0 0 (w / etaDenom M τ) (etaMobius M τ)) := by
  obtain ⟨hAM, hCA, hfixC, hTC, hTAfix, δd, hδd, hdomd⟩ :=
    modularPhi_basis_change_domain M A hM hA hC τ₀ hfix hTM hTA
  have hprod : (A * M * A⁻¹) * A = A * M := by simp [mul_assoc]
  have htC : 0 < (etaDenom (A * M * A⁻¹) (etaMobius A (τ₀ : ℂ))).re := by
    rw [hTC]
    exact hTM
  obtain ⟨δ₁, hδ₁, hdom₁, hger₁⟩ := modularPhi_cocycle_real_germ A M hA (Or.inl hM)
    (Or.inl hAM) m 0 0 τ₀ hTM (by rw [hfix]; exact hTA)
  obtain ⟨δ₂, hδ₂, hdom₂, hger₂⟩ := modularPhi_cocycle_real_germ
    (A * M * A⁻¹) A (Or.inl hC) hA (Or.inl hCA)
    m (A 1 1 * m - A 1 0 * n) 0 τ₀ hTA htC
  have hshift (w τ : ℂ) :
      modularPhiConstructed A m (A 1 1 * m - A 1 0 * n) w τ =
        modularPhiConstructed A 0 0 (w + (m : ℂ) * τ + (n : ℂ)) τ := by
    rcases hA with ha | ⟨k, rfl⟩
    · rw [modularPhiConstructed_of_pos A ha, modularPhiConstructed_of_pos A ha]
      simpa using (ModularCocycleUnitAux.shift_integer A ha 0 0 m n w τ).symm
    · simp [modularPhiConstructed_translation, ModularGroup.coe_T_zpow,
        modularPhiTranslation, qPochhammerInt, qPochhammerIntNumerator,
        qPochhammerIntDenominator, qPochhammerNat]
  refine ⟨min δd (min δ₁ δ₂), lt_min hδd (lt_min hδ₁ hδ₂), ?_, ?_⟩
  · intro τ hτ
    have hd := hdomd (Metric.ball_subset_ball (min_le_left _ _) hτ)
    exact ⟨hd.1.1, hd.2.1, hd.1.2.1, hd.2.2.1⟩
  · intro τ hτ z
    have hτ₁ := Metric.ball_subset_ball ((min_le_right δd (min δ₁ δ₂)).trans
      (min_le_left δ₁ δ₂)) hτ
    have hτ₂ := Metric.ball_subset_ball ((min_le_right δd (min δ₁ δ₂)).trans
      (min_le_right δ₁ δ₂)) hτ
    filter_upwards [hger₁ τ hτ₁ z, hger₂ τ hτ₂ z] with w hw₁ hw₂
    rw [hprod, modularPhiConstructed_of_pos (A * M * A⁻¹) hC,
      hshift] at hw₂
    rw [modularPhiConstructed_of_pos M hM] at hw₁
    rw [← hw₂, hw₁, mul_comm]

/--
Basis-change cancellation at the actual regular centers, including the
actual eta multipliers already proved conjugation-invariant.
The relation z/j_M=z+mτ₀+n makes the two A factors identical at the center;
their nonzero value is an explicit hypothesis supplied later.
This is the matrix-level interface for basis-independent E values.
[RW26, p. 6, (17)]. No hypothesis of factor algebraicity.
-/
theorem modularPhi_basis_change_fixedPoint (M A : SL(2, ℤ))
    (hM : 0 < M 1 0) (hA : ModularPhiSupported A)
    (hC : 0 < (A * M * A⁻¹) 1 0) (m n : ℤ) (z : ℂ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hTM : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hTA : 0 < (etaDenom A (τ₀ : ℂ)).re)
    (harg : z / etaDenom M (τ₀ : ℂ) = z + (m : ℂ) * (τ₀ : ℂ) + (n : ℂ))
    (hMval : ContinuousAt (fun w => modularPhi M m 0 w (τ₀ : ℂ)) z)
    (hCval : ContinuousAt (fun w => modularPhi (A * M * A⁻¹)
      (A 1 1 * m - A 1 0 * n) 0 w (etaMobius A (τ₀ : ℂ)))
      (z / etaDenom A (τ₀ : ℂ)))
    (hAval : ContinuousAt (fun w => modularPhiConstructed A 0 0 w (τ₀ : ℂ))
      (z + (m : ℂ) * (τ₀ : ℂ) + (n : ℂ)))
    (hAne : modularPhiConstructed A 0 0
      (z + (m : ℂ) * (τ₀ : ℂ) + (n : ℂ)) (τ₀ : ℂ) ≠ 0) :
    etaMultiplier (A * M * A⁻¹) *
        modularPhi (A * M * A⁻¹) (A 1 1 * m - A 1 0 * n) 0
          (z / etaDenom A (τ₀ : ℂ)) (etaMobius A (τ₀ : ℂ)) =
      etaMultiplier M * modularPhi M m 0 z (τ₀ : ℂ) := by
  obtain ⟨δ, hδ, hdom, hger⟩ := modularPhi_basis_change_real_germ M A hM hA hC
    m n τ₀ hfix hTM hTA
  have hAv : ContinuousAt (fun w => modularPhiConstructed A 0 0 w (τ₀ : ℂ))
      (z / etaDenom M (τ₀ : ℂ)) := by
    simpa only [harg] using hAval
  have hleft : ContinuousAt (fun w => modularPhi (A * M * A⁻¹)
      (A 1 1 * m - A 1 0 * n) 0 (w / etaDenom A (τ₀ : ℂ))
        (etaMobius A (τ₀ : ℂ)) *
      modularPhiConstructed A 0 0 (w + (m : ℂ) * (τ₀ : ℂ) + (n : ℂ)) (τ₀ : ℂ)) z :=
    (hCval.comp (f := fun w : ℂ => w / etaDenom A (τ₀ : ℂ)) (show ContinuousAt (fun w : ℂ => w / etaDenom A (τ₀ : ℂ)) z
      by fun_prop)).mul
      (hAval.comp (f := fun w : ℂ => w + (m : ℂ) * (τ₀ : ℂ) + (n : ℂ)) (show ContinuousAt
        (fun w : ℂ => w + (m : ℂ) * (τ₀ : ℂ) + (n : ℂ)) z by fun_prop))
  have hright : ContinuousAt (fun w => modularPhi M m 0 w (τ₀ : ℂ) *
      modularPhiConstructed A 0 0 (w / etaDenom M (τ₀ : ℂ))
        (etaMobius M (τ₀ : ℂ))) z := by
    rw [hfix]
    exact hMval.mul (hAv.comp (f := fun w : ℂ => w / etaDenom M (τ₀ : ℂ)) (show ContinuousAt
      (fun w : ℂ => w / etaDenom M (τ₀ : ℂ)) z by fun_prop))
  have hc := ModularCocycleAux.eq_of_germ hleft hright
    (hger (τ₀ : ℂ) (Metric.mem_ball_self hδ) z)
  simp only [hfix, harg] at hc
  have heq := mul_right_cancel₀ hAne hc
  rw [etaMultiplier_conjugate M A τ₀ hM hA hfix
    (by simpa [etaDenom] using hTM) (by simpa [etaDenom] using hTA) hC, heq]

/-! ## Positive powers, explicit integer shifts and the diagonal index shift -/

/--
Positive powers for trace>2 matrices, not closure of
the positive-c set. [RW26, p. 6, p. 14, (18), Prop. 8].
The positive-c assertion is elementary determinant-one recurrence bookkeeping.
-/
theorem modularPhi_pow_pos_c (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (r : ℕ) (hr : 0 < r) :
    0 < (M ^ r) 1 0 := by
  exact ModularCocycleMatrixAux.pow_pos_c M hM htrace r hr

/--
Fixed point and every intermediate real automorphy factor are checked.
r=0 gives j_I=1. [RW26, p. 6, (18)].
-/
theorem modularPhi_pow_fixedPoint_domain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) (r : ℕ) :
    etaMobius (M ^ r) (τ₀ : ℂ) = (τ₀ : ℂ) ∧
    etaDenom (M ^ r) (τ₀ : ℂ) = etaDenom M (τ₀ : ℂ) ^ r ∧
    (∀ j : ℕ, 0 < (etaDenom (M ^ j) (τ₀ : ℂ)).re) ∧
    (τ₀ : ℂ) ∈ modularPhiIterationDomain M r := by
  have hpow := ModularCocycleMatrixAux.pow_fixedPoint M τ₀ hfix hT
  refine ⟨(hpow r).1, (hpow r).2.1, fun j => (hpow j).2.2, ?_⟩
  refine ⟨ModularCocycleMatrixAux.domain_of_re_pos _ _ (hpow r).2.2, ?_⟩
  intro j hj
  refine ⟨ModularCocycleMatrixAux.domain_of_re_pos _ _ (hpow j).2.2, ?_⟩
  rw [(hpow j).1]
  exact ModularCocycleMatrixAux.domain_of_re_pos M _ hT

/--
[RW26, (18)] upper half plane, arbitrary matching integer chain. The
identity case r=0 uses the separate translation definition, never an empty
positive-c product interpreted as Φ. [RW26, p. 6].
-/
theorem modularPhi_iterate_upper_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (ι : ℕ → ℤ) (r : ℕ) (z τ : ℂ)
    (hτ : 0 < τ.im) :
    (fun w => modularPhiConstructed (M ^ r) (ι 0) (ι r) w τ) =ᶠ[𝓝[≠] z]
      (fun w => modularPhiIterationProduct M ι r w τ) := by
  have hsupp (j : ℕ) : ModularPhiSupported (M ^ j) := by
    by_cases hj : j = 0
    · right
      exact ⟨0, by simp [hj]⟩
    · exact Or.inl (modularPhi_pow_pos_c M hM htrace j (Nat.pos_of_ne_zero hj))
  induction r with
  | zero =>
      apply Filter.EventuallyEq.of_eq
      funext w
      simp [modularPhiIterationProduct, modularPhiConstructed, modularPhiTranslation,
        qPochhammerInt, qPochhammerIntNumerator, qPochhammerIntDenominator, qPochhammerNat]
  | succ r ih =>
      have heq := modularPhi_cocycle_upper_germ M (M ^ r) (Or.inl hM) (hsupp r)
        (by simpa [← pow_succ'] using hsupp (r + 1)) (ι 0) (ι r) (ι (r + 1)) z τ hτ
      rw [← pow_succ'] at heq
      refine heq.trans ?_
      filter_upwards [ih] with w hw
      rw [hw]
      simp only [modularPhiIterationProduct, Finset.prod_range_succ]
      ring

/--
Continued (18) on a common ball checking all intermediate powers.
[RW26, p. 6].
The radius may depend on r; no uniform-in-all-powers neighborhood is claimed.
-/
theorem modularPhi_iterate_real_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (ι : ℕ → ℤ) (r : ℕ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (τ₀ : ℂ) δ ⊆ modularPhiIterationDomain M r ∧
      ∀ τ ∈ Metric.ball (τ₀ : ℂ) δ, ∀ z : ℂ,
        (fun w => modularPhiConstructed (M ^ r) (ι 0) (ι r) w τ) =ᶠ[𝓝[≠] z]
          (fun w => modularPhiIterationProduct M ι r w τ) := by
  have hsupp (j : ℕ) : ModularPhiSupported (M ^ j) := by
    by_cases hj : j = 0
    · right
      exact ⟨0, by simp [hj]⟩
    · exact Or.inl (modularPhi_pow_pos_c M hM htrace j (Nat.pos_of_ne_zero hj))
  have hp := modularPhi_pow_fixedPoint_domain M hM htrace τ₀ hfix hT
  induction r with
  | zero =>
      refine ⟨1, zero_lt_one, ?_, ?_⟩
      · intro τ hτ
        simp [modularPhiIterationDomain, modularPhiDomain, etaDenom,
          Complex.mem_slitPlane_iff]
      · intro τ hτ z
        apply Filter.EventuallyEq.of_eq
        funext w
        simp [modularPhiIterationProduct, modularPhiConstructed, modularPhiTranslation,
          qPochhammerInt, qPochhammerIntNumerator, qPochhammerIntDenominator, qPochhammerNat]
  | succ r ih =>
      obtain ⟨δr, hδr, hdomr, hger⟩ := ih
      have hTM : 0 < (etaDenom M (etaMobius (M ^ r) (τ₀ : ℂ))).re := by
        rw [(hp r).1]
        exact hT
      obtain ⟨δc, hδc, hdomc, hgec⟩ := modularPhi_cocycle_real_germ M (M ^ r)
        (Or.inl hM) (hsupp r) (by simpa [← pow_succ'] using hsupp (r + 1))
        (ι 0) (ι r) (ι (r + 1)) τ₀ ((hp r).2.2.1 r) hTM
      refine ⟨min δr δc, lt_min hδr hδc, ?_, ?_⟩
      · intro τ hτ
        have hτr := hdomr (Metric.ball_subset_ball (min_le_left _ _) hτ)
        have hτc := hdomc (Metric.ball_subset_ball (min_le_right _ _) hτ)
        refine ⟨?_, ?_⟩
        · simpa [pow_succ'] using hτc.2.2
        · intro j hj
          by_cases hjr : j < r
          · exact hτr.2 j (Finset.mem_range.mpr hjr)
          · have hj_eq : j = r := by have := Finset.mem_range.mp hj; omega
            subst j
            exact ⟨hτc.1, hτc.2.1⟩
      · intro τ hτ z
        have heq := hgec τ (Metric.ball_subset_ball (min_le_right _ _) hτ) z
        rw [← pow_succ'] at heq
        refine heq.trans ?_
        filter_upwards [hger τ (Metric.ball_subset_ball (min_le_left _ _) hτ) z] with w hw
        rw [hw]
        simp only [modularPhiIterationProduct, Finset.prod_range_succ]
        ring

/--
Fixed-point form actually called: the arguments are z/ε^j,
all parameters are the same real τ₀. [RW26, p. 6, p. 14, (18), Prop. 8].
-/
theorem modularPhi_iterate_fixedPoint_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (ι : ℕ → ℤ) (r : ℕ) (z : ℂ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) :
    (fun w => modularPhiConstructed (M ^ r) (ι 0) (ι r) w (τ₀ : ℂ)) =ᶠ[𝓝[≠] z]
      (fun w => ∏ j ∈ Finset.range r,
        modularPhi M (ι j) (ι (j + 1))
          (w / etaDenom M (τ₀ : ℂ) ^ j) (τ₀ : ℂ)) := by
  obtain ⟨δ, hδ, hdom, heq⟩ := modularPhi_iterate_real_germ M hM htrace ι r τ₀ hfix hT
  have hp := modularPhi_pow_fixedPoint_domain M hM htrace τ₀ hfix hT
  have hprod : (fun w => modularPhiIterationProduct M ι r w (τ₀ : ℂ)) =
      (fun w => ∏ j ∈ Finset.range r, modularPhi M (ι j) (ι (j + 1))
        (w / etaDenom M (τ₀ : ℂ) ^ j) (τ₀ : ℂ)) := by
    funext w
    apply Finset.prod_congr rfl
    intro j hj
    rw [modularPhiConstructed_of_pos M hM, (hp j).1, (hp j).2.1]
  exact (heq (τ₀ : ℂ) (Metric.mem_ball_self hδ) z).trans
    (Filter.EventuallyEq.of_eq hprod)

/--
Point values after the later regularity checks, also at r=0.
[RW26, p. 6, p. 14, (18), Prop. 8].
Continuity is about the actual finite-product representatives.
-/
theorem modularPhi_iterate_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (ι : ℕ → ℤ) (r : ℕ) (z : ℂ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hL : ContinuousAt
      (fun w => modularPhiConstructed (M ^ r) (ι 0) (ι r) w (τ₀ : ℂ)) z)
    (hR : ∀ j ∈ Finset.range r, ContinuousAt
      (fun w => modularPhi M (ι j) (ι (j + 1))
        (w / etaDenom M (τ₀ : ℂ) ^ j) (τ₀ : ℂ)) z) :
    modularPhiConstructed (M ^ r) (ι 0) (ι r) z (τ₀ : ℂ) =
      ∏ j ∈ Finset.range r, modularPhi M (ι j) (ι (j + 1))
        (z / etaDenom M (τ₀ : ℂ) ^ j) (τ₀ : ℂ) := by
  apply ModularCocycleAux.eq_of_germ hL
    (show ContinuousAt (fun w => ∏ j ∈ Finset.range r, modularPhi M (ι j) (ι (j + 1))
      (w / etaDenom M (τ₀ : ℂ) ^ j) (τ₀ : ℂ)) z from
      tendsto_finsetProd _ fun j hj => hR j hj)
  exact modularPhi_iterate_fixedPoint_germ M hM htrace ι r z τ₀ hfix hT

/--
All integer variable shifts in one usable pointwise statement.
The j-th finite factor is literally identical after Euclidean floor
translation, including its prescribed pole value. [RW26, p. 6, (19), Prop. 2(i)].
-/
theorem modularPhi_shift_integer (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k l : ℤ) (z τ : ℂ) :
    modularPhi M m n (z + (k : ℂ) * τ + (l : ℂ)) τ =
      modularPhi M (m + k) (n + M 1 1 * k - M 1 0 * l) z τ := by
  exact ModularCocycleUnitAux.shift_integer M hM m n k l z τ

/--
[RW26, p. 6, (16)] safe point-value form required
for reflection and the r=1 unit action. The balanced phase is a center
condition, so the conclusion is not a z-germ equality. Explicit avoidance
keeps every finite index-shift factor nonzero.
-/
theorem modularPhi_diagonal_index_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k : ℤ) (z : ℂ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hphase : (e (τ₀ : ℂ)) ^ m * e z =
      (e (τ₀ : ℂ)) ^ n * e (z / etaDenom M (τ₀ : ℂ)))
    (havoid : ∀ j : ℤ, 1 - (e (τ₀ : ℂ)) ^ (m + j) * e z ≠ 0)
    (hL : ContinuousAt (fun w => modularPhi M (m + k) (n + k) w (τ₀ : ℂ)) z)
    (hR : ContinuousAt (fun w => modularPhi M m n w (τ₀ : ℂ)) z) :
    modularPhi M (m + k) (n + k) z (τ₀ : ℂ) =
      modularPhi M m n z (τ₀ : ℂ) := by
  exact ModularCocycleUnitAux.diagonal_index_fixedPoint M hM m n k z τ₀ hfix hT hphase havoid hL hR

/-! ## Modular reflection and the dedicated positive-c inverse reflection -/

/--
[RW26, p. 6, Prop. 1] shifted indices. Full slit-domain
z-germ identity for the same finite product.
This is the analytic input to Theorem2 (5), before special-value packaging.
-/
theorem modularPhi_reflection_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi M r n w τ * modularPhi M (1 - r) (1 - n) (-w) τ)
      =ᶠ[𝓝[≠] z] (fun w => modularReflectionFactor M r n w τ) := by
  filter_upwards [ModularCocycleReflectionAux.reflection_exponential_germ M hM r n z τ hτ]
    with w hw
  rw [hw]
  simpa only [ModularCocycleReflectionPhaseAux.normalizedFactor,
    ModularCocycleReflectionPhaseAux.polynomial, modularReflectionFactor,
    modularReflectionPolynomial, modularBernoulliTwo] using
    ModularCocycleReflectionPhaseAux.reflection_exponent_normalized M hM r n w τ hτ

/--
Joint reflection after clearing the two explicit chart denominators.
This retains the center even when a zero and a pole cancel. [RW26, p. 6, Prop. 1], and joint charts.
-/
theorem modularPhi_reflection_chart_cross_mul (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (κ κ' : ℕ → ℤ) (p : ℂ × ℂ)
    (hp : p ∈ modularPhiChartDomain M r n κ)
    (hp' : (-p.1, p.2) ∈ modularPhiChartDomain M (1 - r) (1 - n) κ') :
    modularPhiChartNumerator M r n κ p.1 p.2 *
        modularPhiChartNumerator M (1 - r) (1 - n) κ' (-p.1) p.2 =
      modularReflectionFactor M r n p.1 p.2 *
        modularPhiChartDenominator M r n κ p.1 p.2 *
        modularPhiChartDenominator M (1 - r) (1 - n) κ' (-p.1) p.2 := by
  apply ModularCocycleReflectionAux.reflection_chart_cross_mul_of_germ M hM r n κ κ' p hp hp'
    (fun w => modularReflectionFactor M r n w p.2)
  · unfold modularReflectionFactor modularReflectionPolynomial modularBernoulliTwo e
    fun_prop
  · exact modularPhi_reflection_germ M hM r n p.1 p.2 hp.1

/--
Normalized pointwise reflection, directly usable with later μΦ special
values. Assumptions concern the actual centers, not just their germ orders.
[RW26, p. 6, p. 3, (5), Prop. 1, Theorem 2].
-/
theorem modularPhi_reflection_normalized (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (r n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hL : ContinuousAt (fun w => modularPhi M r n w τ) z)
    (hR : ContinuousAt (fun w => modularPhi M (1 - r) (1 - n) (-w) τ) z) :
    (etaMultiplier M * modularPhi M r n z τ) *
        (etaMultiplier M * modularPhi M (1 - r) (1 - n) (-z) τ) =
      (-1 : ℂ) ^ (r + n) * e (modularReflectionPolynomial M r n z τ) := by
  have hcont : ContinuousAt (fun w => modularReflectionFactor M r n w τ) z := by
    unfold modularReflectionFactor modularReflectionPolynomial modularBernoulliTwo e
    fun_prop
  have heq := ModularCocycleAux.eq_of_germ (hL.mul hR) hcont
    (modularPhi_reflection_germ M hM r n z τ hτ)
  change modularPhi M r n z τ * modularPhi M (1 - r) (1 - n) (-z) τ =
    modularReflectionFactor M r n z τ at heq
  have hμ := etaMultiplier_ne_zero M hM
  calc
    _ = etaMultiplier M ^ 2 *
      (modularPhi M r n z τ * modularPhi M (1 - r) (1 - n) (-z) τ) := by ring
    _ = _ := by
      rw [heq, modularReflectionFactor]
      simp only [zpow_neg, zpow_ofNat]
      field_simp [hμ]

/--
Dedicated inverse-reflection domain checks: c is preserved and the
new automorphy factor is 1/j_M. No closure under inverse is asserted; [RW26, p. 6].
-/
theorem modularInverseReflection_domain (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    0 < modularInverseReflection M 1 0 ∧
    etaDenom (modularInverseReflection M) (-etaMobius M τ) = (etaDenom M τ)⁻¹ ∧
    -etaMobius M τ ∈ modularPhiDomain (modularInverseReflection M) ∧
    etaMobius (modularInverseReflection M) (-etaMobius M τ) = -τ := by
  have hR : ((modularInverseReflection M) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![M 1 1, M 0 1; M 1 0, M 0 0] := rfl
  have h := ModularCocycleMatrixAux.inverse_reflection_denom M
    (modularInverseReflection M) hR τ (Complex.slitPlane_ne_zero hτ)
  refine ⟨?_, h.1, ?_, h.2⟩
  · simpa [modularInverseReflection, modularInverseReflectionMatrix] using hM
  · change etaDenom (modularInverseReflection M) (-etaMobius M τ) ∈ Complex.slitPlane
    rw [h.1]
    exact ModularCocycleMatrixAux.inv_mem_slitPlane _ hτ

/--
Direct positive-c identity, avoiding an unconstructed negative-c inverse.
Its full-domain form follows the dedicated δM⁻¹δ transformation; at a real
fixed point the second parameter is -τ₀. [RW26, p. 6]. Germ only at possible cancellations.
-/
theorem modularPhi_inverse_reflection_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M) :
    (fun w => modularPhi (modularInverseReflection M) (1 - n) (1 - m)
      (w / etaDenom M τ) (-etaMobius M τ)) =ᶠ[𝓝[≠] z]
    (fun w => modularPhi M m n w τ) := by
  have hd := modularInverseReflection_domain M hM τ hτ
  exact Filter.Eventually.of_forall fun w =>
    ModularCocycleReflectionAux.inverse_reflection_pointwise M (modularInverseReflection M) hM
      (by rfl) (by rfl) m n w τ hτ hd.2.1 hd.2.2.1

/--
Exact equality of the actual eta multipliers for δM⁻¹δ.
[RW26, p. 3]. This is a phase identity, not a norm-one surrogate.
-/
theorem etaMultiplier_inverse_reflection (M : SL(2, ℤ)) (hM : 0 < M 1 0) :
    etaMultiplier (modularInverseReflection M) = etaMultiplier M := by
  apply ModularCocycleReflectionAux.etaMultiplier_inverse_reflection_of_matrix M _ hM
  rfl

/--
Pointwise fixed-point interface for attracting/repelling transfer.
Positive ε and positive ε⁻¹ are both conclusions/conditions of the explicit
domain check above; centers still require continuity. [RW26, p. 6].
-/
theorem modularPhi_inverse_reflection_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (z : ℂ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hL : ContinuousAt (fun w => modularPhi (modularInverseReflection M)
      (1 - n) (1 - m) (w / etaDenom M (τ₀ : ℂ)) (-(τ₀ : ℂ))) z)
    (hR : ContinuousAt (fun w => modularPhi M m n w (τ₀ : ℂ)) z) :
    etaMobius (modularInverseReflection M) (-(τ₀ : ℂ)) = -(τ₀ : ℂ) ∧
    0 < (etaDenom (modularInverseReflection M) (-(τ₀ : ℂ))).re ∧
    modularPhi (modularInverseReflection M) (1 - n) (1 - m)
      (z / etaDenom M (τ₀ : ℂ)) (-(τ₀ : ℂ)) = modularPhi M m n z (τ₀ : ℂ) := by
  have hτ : (τ₀ : ℂ) ∈ modularPhiDomain M :=
    ModularCocycleMatrixAux.domain_of_re_pos M _ hT
  have hdom := modularInverseReflection_domain M hM (τ₀ : ℂ) hτ
  rw [hfix] at hdom
  refine ⟨hdom.2.2.2, ?_, ?_⟩
  · rw [hdom.2.1, Complex.inv_re]
    exact div_pos hT (Complex.normSq_pos.mpr (etaDenom_ne_zero_of_mem M hτ))
  · apply ModularCocycleAux.eq_of_germ hL hR
    simpa only [hfix] using modularPhi_inverse_reflection_germ M hM m n z (τ₀ : ℂ) hτ

/-! ## The factor cycle needed by Proposition 8's second identity -/

/--
The base action u↦uM scales the Γ=M^r special argument by ε.
The base is not Γ. [RW26, p. 14, Prop. 8, p. 2, (2)].
-/
theorem modularPhiSpecialArgument_unit (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (r : ℕ) (hr : 0 < r)
    (u : Fin 2 → ℤ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 1 < (etaDenom M (τ₀ : ℂ)).re) :
    modularPhiSpecialArgument (M ^ r)
        (Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) (τ₀ : ℂ) =
      etaDenom M (τ₀ : ℂ) * modularPhiSpecialArgument (M ^ r) u (τ₀ : ℂ) := by
  have hTne : etaDenom M (τ₀ : ℂ) ≠ 0 := by
    intro hzero
    norm_num [hzero] at hT
  unfold modularPhiSpecialArgument
  rw [ModularCocycleUnitAux.row_fixedPoint M u (τ₀ : ℂ) hfix hTne]
  ring

/--
The precise one-step cyclic permutation. It is valid even for prescribed
pole values, since its wraparound uses `modularPhi_shift_integer` with
identical finite-factor arguments. No factor algebraicity or nonzero factor
is assumed. r≥2 is essential for the chosen cycled index chain.
[RW26, p. 14, p. 6, (18), Prop. 8], used for the later special-value normalization.
-/
theorem modularPhi_unit_factor_cycle (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (r : ℕ) (hr : 2 ≤ r)
    (u : Fin 2 → ℤ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 1 < (etaDenom M (τ₀ : ℂ)).re) (j : ℕ) (hj : j < r) :
    modularPhiCycledUnitFactor M r u j (τ₀ : ℂ) =
      modularPhiUnitFactor M r u ((j + r - 1) % r) (τ₀ : ℂ) := by
  let ε := etaDenom M (τ₀ : ℂ)
  let Z := modularPhiSpecialArgument (M ^ r) u (τ₀ : ℂ)
  let v := Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)
  have hr0 : 0 < r := by omega
  have hε : ε ≠ 0 := by
    intro h
    have : 1 < (0 : ℝ) := by simpa [ε, h] using hT
    norm_num at this
  have hscale : modularPhiSpecialArgument (M ^ r) v (τ₀ : ℂ) = ε * Z :=
    modularPhiSpecialArgument_unit M hM htrace r hr0 u τ₀ hfix hT
  have hpow := (modularPhi_pow_fixedPoint_domain M hM htrace τ₀ hfix
    (by linarith : 0 < (etaDenom M (τ₀ : ℂ)).re) r).2.1
  have hrow : (v 0 : ℂ) * (τ₀ : ℂ) + (v 1 : ℂ) =
      ε * ((u 0 : ℂ) * (τ₀ : ℂ) + (u 1 : ℂ)) :=
    ModularCocycleUnitAux.row_fixedPoint M u (τ₀ : ℂ) hfix hε
  have hv : M 1 1 * v 0 - M 1 0 * v 1 = u 0 :=
    ModularCocycleUnitAux.row_second_index M u
  have harg : Z / ε ^ (r - 1) = ε * Z + (v 0 : ℂ) * (τ₀ : ℂ) + (v 1 : ℂ) := by
    have hw := ModularCocycleUnitAux.power_wrap ε
      ((u 0 : ℂ) * (τ₀ : ℂ) + (u 1 : ℂ)) r hr0
      (lt_of_lt_of_le hT (Complex.re_le_norm ε))
    change etaDenom (M ^ r) (τ₀ : ℂ) = ε ^ r at hpow
    have hZ : Z = ((u 0 : ℂ) * (τ₀ : ℂ) + (u 1 : ℂ)) / ((ε ^ r)⁻¹ - 1) := by
      dsimp [Z, modularPhiSpecialArgument]
      rw [hpow]
    rw [← hZ, ← hrow] at hw
    exact hw.trans (by ring)
  change modularPhi M (if j = 0 then v 0 else if j = 1 then u 0 else 0)
    (if j = 0 then u 0 else 0)
    (modularPhiSpecialArgument (M ^ r) v (τ₀ : ℂ) / ε ^ j) (τ₀ : ℂ) =
    modularPhi M (if (j + r - 1) % r = 0 then u 0 else 0) 0
      (Z / ε ^ ((j + r - 1) % r)) (τ₀ : ℂ)
  by_cases hj0 : j = 0
  · subst j
    have hmod : (0 + r - 1) % r = r - 1 := by
      simpa only [zero_add] using (Nat.mod_eq_of_lt (show r - 1 < r by omega))
    have hlast : r - 1 ≠ 0 := by omega
    simp only [hmod, if_neg hlast, pow_zero, div_one, hscale]
    have hs := modularPhi_shift_integer M hM 0 0 (v 0) (v 1) (ε * Z) (τ₀ : ℂ)
    simp only [zero_add, hv] at hs
    rw [← harg] at hs
    exact hs.symm
  · have hmod : (j + r - 1) % r = j - 1 := by
      have heq : j + r - 1 = j - 1 + r := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hdiv : ε * Z / ε ^ j = Z / ε ^ (j - 1) := by
      rw [← pow_sub_one_mul hj0 ε]
      field_simp
    simp only [if_neg hj0,
      hmod, hscale, hdiv]
    by_cases hj1 : j = 1
    · subst j
      norm_num
    · have hprev : j - 1 ≠ 0 := by omega
      simp only [if_neg hj1, if_neg hprev]

/--
Actual finite products are invariant under that permutation.
[RW26, p. 14, p. 6, (18)]. This alone does not identify
their centers with the Γ functions when internal poles cancel.
-/
theorem modularPhi_unit_product_cycle (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (r : ℕ) (hr : 2 ≤ r)
    (u : Fin 2 → ℤ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 1 < (etaDenom M (τ₀ : ℂ)).re) :
    (∏ j ∈ Finset.range r, modularPhiCycledUnitFactor M r u j (τ₀ : ℂ)) =
      ∏ j ∈ Finset.range r, modularPhiUnitFactor M r u j (τ₀ : ℂ) := by
  calc
    (∏ j ∈ Finset.range r, modularPhiCycledUnitFactor M r u j (τ₀ : ℂ)) =
        ∏ j ∈ Finset.range r, modularPhiUnitFactor M r u ((j + r - 1) % r) (τ₀ : ℂ) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact modularPhi_unit_factor_cycle M hM htrace r hr u τ₀ hfix hT j
        (Finset.mem_range.mp hj)
    _ = ∏ j ∈ Finset.range r, modularPhiUnitFactor M r u j (τ₀ : ℂ) :=
      ModularCocycleUnitAux.prod_range_cyclic_pred
        (fun j => modularPhiUnitFactor M r u j (τ₀ : ℂ)) r (by omega)

/--
Φ-level Prop. 8, in the form used for nonzero classes. All regularity
inputs refer to the actual Γ representatives and the two explicit chains.
Multiplication by the common μ_Γ then gives the desired F equality.
For r=1, uM≡u in the quotient of M-I. That case is handled after descent,
or by the integer shift together with `modularPhi_diagonal_index_fixedPoint`. The zero
class uses its separately defined constant, including every positive r.
[RW26, p. 14, Prop. 8].
-/
theorem modularPhi_unit_action (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (htrace : 2 < M 0 0 + M 1 1) (r : ℕ) (hr : 2 ≤ r)
    (u : Fin 2 → ℤ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 1 < (etaDenom M (τ₀ : ℂ)).re)
    (hΓ : ∀ v ∈ ({u, Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)} : Set (Fin 2 → ℤ)),
      ContinuousAt (fun w => modularPhi (M ^ r) (v 0) 0 w (τ₀ : ℂ))
        (modularPhiSpecialArgument (M ^ r) v (τ₀ : ℂ)))
    (hFactors : ∀ j ∈ Finset.range r,
      ContinuousAt (fun w => modularPhi M (if j = 0 then u 0 else 0) 0 w (τ₀ : ℂ))
        (modularPhiSpecialArgument (M ^ r) u (τ₀ : ℂ) / etaDenom M (τ₀ : ℂ) ^ j))
    (hCycled : ∀ j ∈ Finset.range r,
      ContinuousAt (fun w => modularPhi M
        (if j = 0 then (Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) 0
          else if j = 1 then u 0 else 0) (if j = 0 then u 0 else 0) w (τ₀ : ℂ))
        (modularPhiSpecialArgument (M ^ r)
          (Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) (τ₀ : ℂ) /
            etaDenom M (τ₀ : ℂ) ^ j)) :
    modularPhi (M ^ r) ((Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) 0) 0
        (modularPhiSpecialArgument (M ^ r)
          (Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) (τ₀ : ℂ)) (τ₀ : ℂ) =
      modularPhi (M ^ r) (u 0) 0
        (modularPhiSpecialArgument (M ^ r) u (τ₀ : ℂ)) (τ₀ : ℂ) := by
  let v := Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)
  let Z := modularPhiSpecialArgument (M ^ r) u (τ₀ : ℂ)
  let W := modularPhiSpecialArgument (M ^ r) v (τ₀ : ℂ)
  let ι : ℕ → ℤ := fun j => if j = 0 then u 0 else 0
  let κ : ℕ → ℤ := fun j => if j = 0 then v 0 else if j = 1 then u 0 else 0
  have hr0 : 0 < r := by omega
  have hrne : r ≠ 0 := by omega
  have hr1 : r ≠ 1 := by omega
  have hpos : 0 < (M ^ r) 1 0 := modularPhi_pow_pos_c M hM htrace r hr0
  have hT0 : 0 < (etaDenom M (τ₀ : ℂ)).re := by linarith
  have hι (j : ℕ) : ι (j + 1) = 0 := by simp [ι]
  have hκ (j : ℕ) : κ (j + 1) = if j = 0 then u 0 else 0 := by
    by_cases hj : j = 0
    · subst j; simp [κ]
    · have hj1 : j + 1 ≠ 1 := by omega
      simp [κ, hj]
  have ho := modularPhi_iterate_fixedPoint M hM htrace ι r Z τ₀ hfix hT0
    (by simpa only [modularPhiConstructed, if_pos hpos, ι, if_pos rfl, if_neg hrne, Z] using
      hΓ u (by simp))
    (by
      intro j hj
      have ht : ContinuousAt (fun w : ℂ => w / etaDenom M (τ₀ : ℂ) ^ j) Z :=
        continuousAt_id.div_const _
      have hc := (hFactors j hj).comp (f := fun w : ℂ => w / etaDenom M (τ₀ : ℂ) ^ j) ht
      simpa only [hι, ι, Z, Function.comp_def] using hc)
  have hc := modularPhi_iterate_fixedPoint M hM htrace κ r W τ₀ hfix hT0
    (by simpa only [modularPhiConstructed, if_pos hpos, κ, if_pos rfl, if_neg hrne, if_neg hr1, W] using
      hΓ v (by simp [v]))
    (by
      intro j hj
      have ht : ContinuousAt (fun w : ℂ => w / etaDenom M (τ₀ : ℂ) ^ j) W :=
        continuousAt_id.div_const _
      have hf := (hCycled j hj).comp (f := fun w : ℂ => w / etaDenom M (τ₀ : ℂ) ^ j) ht
      simpa only [hκ, κ, W, v, Function.comp_def] using hf)
  have horig : modularPhi (M ^ r) (u 0) 0 Z (τ₀ : ℂ) =
      ∏ j ∈ Finset.range r, modularPhiUnitFactor M r u j (τ₀ : ℂ) := by
    simpa only [modularPhiConstructed, if_pos hpos, ι, if_pos rfl, if_neg hrne,
      hι, modularPhiUnitFactor, Z] using ho
  have hcycled : modularPhi (M ^ r) (v 0) 0 W (τ₀ : ℂ) =
      ∏ j ∈ Finset.range r, modularPhiCycledUnitFactor M r u j (τ₀ : ℂ) := by
    simpa only [modularPhiConstructed, if_pos hpos, κ, if_pos rfl,
      if_neg hrne, if_neg hr1, hκ, modularPhiCycledUnitFactor, W, v] using hc
  exact hcycled.trans ((modularPhi_unit_product_cycle M hM htrace r hr u τ₀ hfix hT).trans horig.symm)

end SICLean.L4

-- Actual APIs of the pinned Mathlib and already proved.
#check Filter.EventuallyEq
#check ContinuousAt.congr_of_eventuallyEq
#check MeromorphicAt.comp_analyticAt
#check AnalyticAt.continuousAt
#check Matrix.vecMul
#check ModularGroup.coe_T_zpow
#check SICLean.L4.modularPhi_joint_local_quotient
#check SICLean.L4.modularPhi_index_m_germ
#check SICLean.L4.modularPhi_index_n_germ
#check SICLean.L4.qPochhammerInt_add_cleared
#check SICLean.L4.phiExtended_inversion
#check SICLean.L4.etaMultiplier_conjugate
#print SICLean.L4.modularPhiTranslation
#print SICLean.L4.modularCocycleDomain
#print SICLean.L4.modularReflectionPolynomial
#print SICLean.L4.modularPhi_cocycle_real_germ
#print SICLean.L4.modularPhi_unit_factor_cycle
