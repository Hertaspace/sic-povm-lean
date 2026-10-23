import SICLean.L5.FiniteTranslationRatio
import SICLean.L5.FiniteAlgebraicTransportAux

set_option autoImplicit false

/-!
# The same finite identities in the fixed algebraic closure

These are finite-algebra statements. [RW-rec, Prop. 1] and [RW-rec, §4]
are transported through `Galois.embed`. Each preimage is
`Galois.algebraicLift` of the corresponding complex value.
Algebraicity is taken from the M78/FinalAssembly chain.
See [RW26, Thm. 1, p. 3] and [RW26, (36), p. 18].
-/

noncomputable section

open Classical
open scoped BigOperators MatrixGroups

namespace SICLean.L5.FiniteAlgebraicTransport

open L4

/-- Algebraicity of every matrix value.
[RW-rec, Prop. 1]; [RW26, Thm. 1, p. 3].
The argument uses `PeriodDataExistence`, `chosenPseudolatticeFamily`,
`M78.specialValues_isAlgebraic`, and `familyPentagon_of_G1 g1RealConclusion`. -/
theorem actual_value_isAlgebraic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) :
    IsAlgebraic ℚ (specialValuePlus M hM x) := by
  have hN : 0 < (specialValueOrder M).toNat := by
    have := specialValueOrder_pos M hM
    omega
  obtain ⟨K, hK, hNF, P, hP⟩ :=
    L3.PeriodDataExistence.exists_periodData (specialValueOrder M).toNat hN
  let : Field K := hK
  let : NumberField K := hNF
  let F := L3.chosenPseudolatticeFamily P
  have horder : specialValueOrder M = (P.N : ℤ) := by
    rw [hP, Int.toNat_of_nonneg (specialValueOrder_pos M hM).le]
  exact (L3.M78.Transport.specialValues_isAlgebraic F
    (FinalAssembly.familyPentagon_of_G1 g1RealConclusion F) M hM horder x).1

/-- All finite coefficients have algebraic preimages.
[RW-rec, Prop. 1]; [RW26, (3), p. 3].
`sqrt(N)` satisfies `X^2 - N = 0`.
No valuation or class-field-theoretic assertion is part of this statement. -/
theorem coefficients_isAlgebraic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x y : SpecialValueGroup M) :
    IsAlgebraic ℚ (specialValueGaussian M hM x) ∧
      IsAlgebraic ℚ (specialValuePairing M hM x y) ∧
      IsAlgebraic ℚ (etaMultiplier M) ∧
      IsAlgebraic ℚ (FiniteFourier.sqrtOrder M) := by
  exact FiniteAlgebraicTransportAux.coefficients_isAlgebraic M hM x y

/-- Canonical preimage of the same plus value. -/
def value (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) : Galois.Qbar :=
  Galois.algebraicLift (specialValuePlus M hM x) (actual_value_isAlgebraic M hM x)

/-- Canonical algebraic image of the Gaussian. -/
def gaussian (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : SpecialValueGroup M) : Galois.Qbar :=
  Galois.algebraicLift (specialValueGaussian M hM x) (coefficients_isAlgebraic M hM x 0).1

/-- Canonical preimage of the positive-sign pairing. -/
def pairing (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x y : SpecialValueGroup M) : Galois.Qbar :=
  Galois.algebraicLift (specialValuePairing M hM x y) (coefficients_isAlgebraic M hM x y).2.1

/-- Canonical preimage of etaMultiplier M, independent of the label. -/
def multiplier (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) : Galois.Qbar :=
  Galois.algebraicLift (etaMultiplier M) (coefficients_isAlgebraic M hM 0 0).2.2.1

/-- The algebraic square root is the positive real value. -/
def sqrtOrder (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) : Galois.Qbar :=
  Galois.algebraicLift (FiniteFourier.sqrtOrder M) (coefficients_isAlgebraic M hM 0 0).2.2.2

/-- Algebraic zero indicator. -/
def delta (M : SL(2, ℤ)) (x : SpecialValueGroup M) : Galois.Qbar :=
  if x = 0 then 1 else 0

/-- Concrete normalized finite sum in Qbar; no choice of an embedding here. -/
def normalizedSum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : SpecialValueGroup M → Galois.Qbar) : Galois.Qbar :=
  letI : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  letI : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  (sqrtOrder M hM)⁻¹ * ∑ t, f t

/-- The negative kernel is preserved on the algebraic side. -/
def fourier (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (f : SpecialValueGroup M → Galois.Qbar) (y : SpecialValueGroup M) : Galois.Qbar :=
  normalizedSum M hM (fun t => f t * pairing M hM t (-y))

/-- The literal algebraic translation quotient. -/
def ratio (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (h t : SpecialValueGroup M) : Galois.Qbar :=
  value M hM (t + h) / value M hM t

variable (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)

/-- Image under the fixed embedding. [RW-rec, Prop. 1]. -/
theorem embed_value (x : SpecialValueGroup M) :
    Galois.embed (value M hM x) = specialValuePlus M hM x := by
  exact Galois.embed_algebraicLift _ _

/-- Image under the fixed embedding. [RW-rec]; [RW26, (3), p. 3]. -/
theorem embed_gaussian (x : SpecialValueGroup M) :
    Galois.embed (gaussian M hM x) = specialValueGaussian M hM x := by
  exact Galois.embed_algebraicLift _ _

/-- Image under the fixed embedding. [RW-rec]; [RW26, (3), p. 3]. -/
theorem embed_pairing (x y : SpecialValueGroup M) :
    Galois.embed (pairing M hM x y) = specialValuePairing M hM x y := by
  exact Galois.embed_algebraicLift _ _

/-- Image under the fixed embedding of the eta multiplier. [RW-rec]; [RW26, p. 3]. -/
theorem embed_multiplier : Galois.embed (multiplier M hM) = etaMultiplier M := by
  exact Galois.embed_algebraicLift _ _

/-- The sign of `sqrt(N)` is the one whose complex image is the positive square root.
[RW-rec]; [RW26, p. 15]. -/
theorem embed_sqrtOrder :
    Galois.embed (sqrtOrder M hM) = FiniteFourier.sqrtOrder M := by
  exact Galois.embed_algebraicLift _ _

/-- Image under the fixed embedding. [RW-rec]; [RW26, p. 15].
Both finite sums use the same labels and the same negative kernel. -/
theorem embed_fourier (f : SpecialValueGroup M → Galois.Qbar)
    (y : SpecialValueGroup M) :
    Galois.embed (fourier M hM f y) =
      FiniteFourier.fourier M hM (fun t => Galois.embed (f t)) y := by
  let : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  let : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  simp only [fourier, normalizedSum, FiniteFourier.fourier,
    G2.SpecialValueBridge.normalizedValueSum, map_mul, map_inv₀, map_sum,
    embed_sqrtOrder, embed_pairing, FiniteFourier.sqrtOrder]

/-- Image under the fixed embedding of the quotient. [RW-rec, §4]. -/
theorem embed_ratio (h t : SpecialValueGroup M) :
    Galois.embed (ratio M hM h t) = FiniteTranslationRatio.ratio M hM h t := by
  simp only [ratio, map_div₀, embed_value, FiniteTranslationRatio.ratio]

/-- A nonzero complex value has a nonzero algebraic preimage.
[RW-rec, (4)]; [RW26, (5), p. 3]. -/
theorem value_ne_zero (x : SpecialValueGroup M) : value M hM x ≠ 0 := by
  intro hx
  apply specialValuePlus_ne_zero M hM x
  rw [← embed_value M hM x, hx, map_zero]

/-- [RW-rec, (5)] in `Qbar`. [RW26, (6), p. 3]. -/
theorem actual_fourier (y : SpecialValueGroup M) :
    fourier M hM (value M hM) y =
      multiplier M hM * gaussian M hM y * value M hM y := by
  apply (show Function.Injective Galois.embed from Galois.embed.injective)
  simpa only [embed_fourier, embed_value, map_mul, embed_multiplier,
    embed_gaussian] using FiniteFourier.actual_fourier M hM y

/-- [RW-rec, §7] in the same `Qbar`. The final term is constant.
[RW26, (5)--(6), p. 3]. -/
theorem actual_inverse_fourier (y : SpecialValueGroup M) :
    fourier M hM (fun t => (value M hM t)⁻¹) y =
      (multiplier M hM)⁻¹ * value M hM y - 1 := by
  apply (show Function.Injective Galois.embed from Galois.embed.injective)
  simpa only [embed_fourier, map_inv₀, embed_value, map_sub, map_mul,
    map_one, embed_multiplier] using FiniteFourier.actual_inverse_fourier M hM y

/-- The product identity in the common algebraic model.
[RW-rec, Prop. 1, (6)]; [RW26, (36), p. 18]. -/
theorem actual_product (x y : SpecialValueGroup M) :
    normalizedSum M hM (fun t => value M hM t * gaussian M hM t *
      value M hM (x - t) * pairing M hM t y) =
      gaussian M hM (x + y) * value M hM (-x - y) * value M hM x * value M hM y -
      (specialValueOrder M : Galois.Qbar) * value M hM 0 * delta M x * delta M y := by
  let : Finite (SpecialValueGroup M) := specialValueGroup_finite M hM
  let : Fintype (SpecialValueGroup M) := Fintype.ofFinite (SpecialValueGroup M)
  apply (show Function.Injective Galois.embed from Galois.embed.injective)
  simpa only [normalizedSum, FiniteProductPentagon.productSum,
    G2.SpecialValueBridge.normalizedValueSum, map_mul, map_inv₀, map_sum,
    embed_sqrtOrder, embed_value, embed_gaussian, embed_pairing, map_sub,
    map_intCast, delta, FiniteFourier.delta, apply_ite, map_one, map_zero,
    FiniteFourier.sqrtOrder] using FiniteProductPentagon.actual_product M hM x y

/-- [RW-rec, (15)] in `Qbar`, with the same origin term and labels.
[RW26, (36), p. 18]. -/
theorem ratio_fourier (h t : SpecialValueGroup M) :
    fourier M hM (ratio M hM h) t =
      value M hM h * ((ratio M hM h t)⁻¹ - 1) +
      sqrtOrder M hM * (gaussian M hM h)⁻¹ * delta M (t + h) := by
  apply (show Function.Injective Galois.embed from Galois.embed.injective)
  simpa only [embed_fourier, embed_ratio, map_add, map_mul, embed_value,
    map_sub, map_inv₀, map_one, embed_sqrtOrder, embed_gaussian,
    delta, FiniteFourier.delta, apply_ite, map_zero] using
    FiniteTranslationRatio.ratio_fourier M hM h t

/-- Fourier of the pointwise inverse, in `Qbar`.
[RW-rec, §4, §7]; [RW26, (36), p. 18]. -/
theorem ratio_inverse_fourier (h t : SpecialValueGroup M) :
    fourier M hM (fun u => (ratio M hM h u)⁻¹) t =
      ratio M hM h (-t) / value M hM h + sqrtOrder M hM * delta M t -
      ((gaussian M hM h)⁻¹ * pairing M hM h t) / value M hM h := by
  apply (show Function.Injective Galois.embed from Galois.embed.injective)
  simpa only [embed_fourier, map_inv₀, embed_ratio, map_sub, map_add,
    map_div₀, embed_value, map_mul, embed_sqrtOrder, embed_gaussian,
    embed_pairing, delta, FiniteFourier.delta, apply_ite, map_one, map_zero] using
    FiniteTranslationRatio.ratio_inverse_fourier M hM h t

#print value
#print fourier
#check @Galois.embed
#check @embed_value
#check @actual_product
#check @ratio_inverse_fourier

end SICLean.L5.FiniteAlgebraicTransport
