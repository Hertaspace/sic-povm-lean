import SICLean.L5.FiniteCosetMoments
import SICLean.L5.FiniteInterpolation

/-!
# From small-coset moments to finite polynomial consequences

This bridge identifies the `Fin p` digits in the coset formulas of
[RW-rec, Lemma 1] with the `ZMod p` arguments used for interpolation.
The conclusions concern the selected coset. They contain no valuation
hypothesis and do not state the local Fourier lemma.
-/

set_option autoImplicit false

noncomputable section

namespace SICLean.L5.FiniteMomentConsequences

open SICLean.L5.FiniteCosetMoments
open SICLean.L5.FiniteInterpolation

/-- The canonical equivalence between a bounded digit and a prime-field element. -/
def finPrimeEquiv (p : ℕ) [Fact p.Prime] : Fin p ≃ ZMod p :=
  (ZMod.finEquiv p).toEquiv

/-- Apply the canonical digit equivalence in each coordinate. -/
def coordinateEquiv (p d : ℕ) [Fact p.Prime] :
    CosetCoordinate p d ≃ (Fin d → ZMod p) :=
  Equiv.piCongrRight (fun _ => finPrimeEquiv p)

/-- A function on bounded digits, transported to the prime field. -/
def finFunctionLift {p : ℕ} [Fact p.Prime] {k : Type*}
    (g : Fin p → k) : ZMod p → k :=
  fun t => g ((finPrimeEquiv p).symm t)

/-- The selected small-coset point, with prime-field rather than `Fin` coordinates. -/
def primeCosetPoint {p s d : ℕ} [Fact p.Prime]
    (b : CosetBase p s d) (u : Fin d → ZMod p) : Point p s d :=
  cosetPoint b ((coordinateEquiv p d).symm u)

/-- Restrict a function to the selected coset and use prime-field coordinates. -/
def cosetFunction {p s d : ℕ} [Fact p.Prime] {k : Type*}
    (f : Point p s d → k) (b : CosetBase p s d) : (Fin d → ZMod p) → k :=
  fun u => f (primeCosetPoint b u)

/-- The one-coordinate version expected by `FiniteInterpolation.moment`. -/
def lineFunction {p s : ℕ} [Fact p.Prime] {k : Type*}
    (f : Point p s 1 → k) (b : CosetBase p s 1) : ZMod p → k :=
  fun t => cosetFunction f b (fun _ => t)

/-- The two-coordinate version expected by `FiniteInterpolation.planeMoment`. -/
def planeFunction {p s : ℕ} [Fact p.Prime] {k : Type*}
    (f : Point p s 2 → k) (b : CosetBase p s 2) : ZMod p × ZMod p → k :=
  fun u => cosetFunction f b ![u.1, u.2]

/-- The exact global low-binomial hypothesis supplied to `FiniteCosetMoments`. -/
def GlobalLowBinomialVanishing {p s d : ℕ} [Fact p.Prime]
    {k : Type*} [CommRing k] (f : Point p s d → k) : Prop :=
  ∀ j : Fin d → ℕ,
    2 * totalDegree j < d * (p ^ s - 1) → globalBinomialMoment f j = 0

variable {p s : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p]

/-- Coordinate helper for [RW-rec, Lemma 1]: the canonical digit maps
to the same scalar in any coefficient field of characteristic `p`. -/
theorem primeField_finPrimeEquiv (u : Fin p) :
    primeField p k (finPrimeEquiv p u) = (u.val : k) := by
  cases p with
  | zero => exact Fin.elim0 u
  | succ n => rfl

/-- Coordinate helper for [RW-rec, Lemma 1]: the transported coset point has
the same lower-plus-upper-digit formula on canonical representatives. -/
theorem primeCosetPoint_apply {d : ℕ} (b : CosetBase p s d)
    (u : Fin d → ZMod p) (i : Fin d) :
    primeCosetPoint b u i =
      (((b i).val + p ^ (s - 1) * (u i).val : ℕ) : ZMod (p ^ s)) := by
  cases p with
  | zero => exact ((Fact.out : Nat.Prime 0).ne_zero rfl).elim
  | succ n => rfl

/-- Helper for [RW-rec, Lemma 1]: the line moment equals the rank-one coset
monomial moment after the canonical coordinate conversion. -/
theorem line_moment_eq_cosetMonomialMoment (f : Point p s 1 → k)
    (b : CosetBase p s 1) (r : ℕ) :
    moment p k (lineFunction f b) r =
      cosetMonomialMoment f b (fun _ => r) := by
  classical
  let e : CosetCoordinate p 1 ≃ ZMod p :=
    (coordinateEquiv p 1).trans (Equiv.funUnique (Fin 1) (ZMod p))
  have hpoint (u : CosetCoordinate p 1) :
      lineFunction f b (e u) = f (cosetPoint b u) := by
    have hu : (fun _ : Fin 1 => e u) = coordinateEquiv p 1 u := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    simp only [lineFunction, cosetFunction, primeCosetPoint, hu, Equiv.symm_apply_apply]
  unfold moment cosetMonomialMoment
  symm
  refine Fintype.sum_equiv e _ _ ?_
  intro u
  rw [hpoint]
  simp only [monomialWeight, Fin.prod_univ_one]
  change f (cosetPoint b u) * (↑(u 0).val : k) ^ r =
    (primeField p k (finPrimeEquiv p (u 0))) ^ r * f (cosetPoint b u)
  rw [primeField_finPrimeEquiv, mul_comm]

/-- Helper for [RW-rec, Lemma 1]: the plane moment equals the rank-two coset
monomial moment after the canonical coordinate conversion. -/
theorem plane_moment_eq_cosetMonomialMoment (f : Point p s 2 → k)
    (b : CosetBase p s 2) (a c : ℕ) :
    planeMoment p k (planeFunction f b) a c =
      cosetMonomialMoment f b ![a, c] := by
  classical
  let e : CosetCoordinate p 2 ≃ ZMod p × ZMod p :=
    (coordinateEquiv p 2).trans (finTwoArrowEquiv (ZMod p))
  have hpoint (u : CosetCoordinate p 2) :
      planeFunction f b (e u) = f (cosetPoint b u) := by
    have hu : ![(e u).1, (e u).2] = coordinateEquiv p 2 u := by
      exact (finTwoArrowEquiv (ZMod p)).symm_apply_apply (coordinateEquiv p 2 u)
    simp only [planeFunction, cosetFunction, primeCosetPoint, hu, Equiv.symm_apply_apply]
  unfold planeMoment cosetMonomialMoment
  symm
  refine Fintype.sum_equiv e _ _ ?_
  intro u
  rw [hpoint]
  simp only [monomialWeight, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  change f (cosetPoint b u) * ((↑(u 0).val : k) ^ a * (↑(u 1).val : k) ^ c) =
    (primeField p k (finPrimeEquiv p (u 0))) ^ a *
      (primeField p k (finPrimeEquiv p (u 1))) ^ c * f (cosetPoint b u)
  rw [primeField_finPrimeEquiv, primeField_finPrimeEquiv, mul_comm]

/-- Coordinate helper for [RW-rec, Lemma 1]: a factorization on this coset in
bounded digits is exactly a separable prime-field function after transport. -/
theorem plane_factorization_iff (f : Point p s 2 → k)
    (b : CosetBase p s 2) (g h : Fin p → k) :
    planeFunction f b = separableFunction p k (finFunctionLift g) (finFunctionLift h) ↔
      ∀ u : CosetCoordinate p 2, f (cosetPoint b u) = g (u 0) * h (u 1) := by
  constructor
  · intro hfactor u
    have hu : ![finPrimeEquiv p (u 0), finPrimeEquiv p (u 1)] =
        coordinateEquiv p 2 u := by
      ext i
      fin_cases i <;> rfl
    have heq := congrFun hfactor (finPrimeEquiv p (u 0), finPrimeEquiv p (u 1))
    simpa only [planeFunction, cosetFunction, primeCosetPoint, hu,
      Equiv.symm_apply_apply, separableFunction, finFunctionLift] using heq
  · intro hfactor
    funext u
    have hu : ((coordinateEquiv p 2).symm ![u.1, u.2]) 0 =
        (finPrimeEquiv p).symm u.1 := rfl
    have hv : ((coordinateEquiv p 2).symm ![u.1, u.2]) 1 =
        (finPrimeEquiv p).symm u.2 := rfl
    simpa only [planeFunction, cosetFunction, primeCosetPoint, separableFunction,
      finFunctionLift, hu, hv] using hfactor ((coordinateEquiv p 2).symm ![u.1, u.2])

/-- [RW-rec, Lemma 1]: global low binomial vanishing supplies the precise
rank-one moment predicate consumed by finite interpolation. -/
theorem line_lowMoments_of_global (hs : 1 ≤ s) (f : Point p s 1 → k)
    (hglobal : GlobalLowBinomialVanishing f) (b : CosetBase p s 1) :
    HasVanishingLowMoments p k (lineFunction f b) := by
  intro r hr
  rw [line_moment_eq_cosetMonomialMoment]
  apply cosetMonomialMoment_eq_zero hs (Or.inl rfl) f hglobal
  simpa only [totalDegree, Fin.sum_univ_one, one_mul] using hr

/-- [RW-rec, Lemma 1]: global low binomial vanishing supplies the precise
rank-two total-degree moment predicate consumed by finite interpolation. -/
theorem plane_lowMoments_of_global (hs : 1 ≤ s) (f : Point p s 2 → k)
    (hglobal : GlobalLowBinomialVanishing f) (b : CosetBase p s 2) :
    HasVanishingPlaneMoments p k (planeFunction f b) := by
  intro a c hac
  rw [plane_moment_eq_cosetMonomialMoment]
  apply cosetMonomialMoment_eq_zero hs (Or.inr rfl) f hglobal
  simpa only [totalDegree, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] using (Nat.mul_lt_mul_left (by decide : 0 < 2)).mpr hac

/-- [RW-rec, Lemma 1]: the polynomial representing this rank-one coset has
degree at most half the prime-field degree range. -/
theorem line_interpolant_natDegree_le_half_of_global (hs : 1 ≤ s)
    (f : Point p s 1 → k) (hglobal : GlobalLowBinomialVanishing f)
    (b : CosetBase p s 1) :
    (interpolant p k (lineFunction f b)).natDegree ≤ (p - 1) / 2 := by
  exact natDegree_interpolant_le_half_of_lowMoments p k (lineFunction f b)
    (line_lowMoments_of_global hs f hglobal b)

/-- [RW-rec, Lemma 1]: on a chosen rank-one coset, either all values vanish or
strictly more than half of the original bounded-digit coordinates are nonzero. -/
theorem coset_eq_zero_or_support_large_of_global (hs : 1 ≤ s)
    (f : Point p s 1 → k) (hglobal : GlobalLowBinomialVanishing f)
    (b : CosetBase p s 1) :
    (∀ u : CosetCoordinate p 1, f (cosetPoint b u) = 0) ∨
      p < 2 * Nat.card {u : CosetCoordinate p 1 // f (cosetPoint b u) ≠ 0} := by
  classical
  let e : CosetCoordinate p 1 ≃ ZMod p :=
    (coordinateEquiv p 1).trans (Equiv.funUnique (Fin 1) (ZMod p))
  have hpoint (u : CosetCoordinate p 1) :
      lineFunction f b (e u) = f (cosetPoint b u) := by
    have hu : (fun _ : Fin 1 => e u) = coordinateEquiv p 1 u := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    simp only [lineFunction, cosetFunction, primeCosetPoint, hu, Equiv.symm_apply_apply]
  rcases eq_zero_or_support_large_of_lowMoments p k (lineFunction f b)
    (line_lowMoments_of_global hs f hglobal b) with hzero | hlarge
  · left
    intro u
    rw [← hpoint u, hzero]
    rfl
  · right
    have hcard : Nat.card {u : CosetCoordinate p 1 // f (cosetPoint b u) ≠ 0} =
        Nat.card {t : ZMod p // lineFunction f b t ≠ 0} :=
      Nat.card_congr (e.subtypeEquiv (fun u => by rw [hpoint]))
    rwa [hcard]

/-- [RW-rec, Lemma 1]: global moments for the function and its pointwise inverse
force its values on a nowhere-zero rank-one coset to be constant. -/
theorem coset_constant_of_global_and_reciprocal (hs : 1 ≤ s)
    (f : Point p s 1 → k) (b : CosetBase p s 1)
    (hnonzero : ∀ u : CosetCoordinate p 1, f (cosetPoint b u) ≠ 0)
    (hglobal : GlobalLowBinomialVanishing f)
    (hinverse : GlobalLowBinomialVanishing (fun x => (f x)⁻¹)) :
    ∃ c : k, c ≠ 0 ∧ ∀ u : CosetCoordinate p 1, f (cosetPoint b u) = c := by
  have hline : ∀ t : ZMod p, lineFunction f b t ≠ 0 := by
    intro t
    exact hnonzero ((coordinateEquiv p 1).symm (fun _ => t))
  obtain ⟨c, hc, hconstant⟩ := eq_const_of_lowMoments_and_reciprocal p k
    (lineFunction f b) hline (line_lowMoments_of_global hs f hglobal b)
      (line_lowMoments_of_global hs (fun x => (f x)⁻¹) hinverse b)
  refine ⟨c, hc, fun u => ?_⟩
  have hu : (fun _ : Fin 1 => finPrimeEquiv p (u 0)) = coordinateEquiv p 1 u := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  simpa only [lineFunction, cosetFunction, primeCosetPoint, hu, Equiv.symm_apply_apply]
    using hconstant (finPrimeEquiv p (u 0))

/-- [RW-rec, Lemma 1]: for the displayed factorization on this single rank-two
coset, global moments of the function and its reciprocal force one factor
to be constant. No factorization on any other coset is assumed. -/
theorem coset_one_factor_constant_of_global_and_reciprocal (hs : 1 ≤ s)
    (f : Point p s 2 → k) (b : CosetBase p s 2) (g h : Fin p → k)
    (hfactor : ∀ u : CosetCoordinate p 2,
      f (cosetPoint b u) = g (u 0) * h (u 1))
    (hnonzero : ∀ u : CosetCoordinate p 2, f (cosetPoint b u) ≠ 0)
    (hglobal : GlobalLowBinomialVanishing f)
    (hinverse : GlobalLowBinomialVanishing (fun x => (f x)⁻¹)) :
    (∃ c : k, c ≠ 0 ∧ ∀ t : Fin p, g t = c) ∨
      (∃ c : k, c ≠ 0 ∧ ∀ t : Fin p, h t = c) := by
  have hfactor' : ∀ u : ZMod p × ZMod p,
      planeFunction f b u = finFunctionLift g u.1 * finFunctionLift h u.2 :=
    congrFun ((plane_factorization_iff f b g h).mpr hfactor)
  have hplane : ∀ u : ZMod p × ZMod p, planeFunction f b u ≠ 0 := by
    intro u
    exact hnonzero ((coordinateEquiv p 2).symm ![u.1, u.2])
  rcases one_factor_constant_of_factorization p k (planeFunction f b)
    (finFunctionLift g) (finFunctionLift h) hfactor' hplane
      (plane_lowMoments_of_global hs f hglobal b)
      (plane_lowMoments_of_global hs (fun x => (f x)⁻¹) hinverse b) with hg | hh
  · left
    obtain ⟨c, hc, hg⟩ := hg
    refine ⟨c, hc, fun t => ?_⟩
    simpa only [finFunctionLift, Equiv.symm_apply_apply] using hg (finPrimeEquiv p t)
  · right
    obtain ⟨c, hc, hh⟩ := hh
    refine ⟨c, hc, fun t => ?_⟩
    simpa only [finFunctionLift, Equiv.symm_apply_apply] using hh (finPrimeEquiv p t)

end SICLean.L5.FiniteMomentConsequences
