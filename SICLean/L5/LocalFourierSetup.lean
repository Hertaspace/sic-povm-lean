import SICLean.L5.FiniteMomentConsequences
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

set_option autoImplicit false

/-!
# Local Lemma 1: concrete objects and reduction

[RW-rec, §4, pp. 4--6]. In particular the field in [RW-rec] is Qbar, not Q. An additive
valuation with values in `WithTop ℝ` covers that model and normalized valuations on
finite extensions. Discreteness is not required. `Residue v` is the actual residue field
of the valuation subring. `reduce` is extended by zero outside the valuation ring for a
total API. Every reduction assertion below or downstream has explicit integrality
hypotheses. Neither integrality nor any moment conclusion is built into a function,
pairing, coordinate system, or Fourier transform. In [RW26], Lemma 1 is the analytic
asymptotic. The finite Fourier convention is that of [RW26, p. 15]. All local results here
are attributed to [RW-rec].
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalFourierSetup

open FiniteCosetMoments FiniteMomentConsequences

variable {L : Type*} [Field L]

/-- [RW-rec]: the subring `{a | 0 ≤ v a}`. -/
abbrev integers (v : AddValuation L (WithTop ℝ)) : ValuationSubring L :=
  v.toValuation.valuationSubring

/-- [RW-rec]: the quotient by the actual maximal ideal. -/
abbrev Residue (v : AddValuation L (WithTop ℝ)) :=
  IsLocalRing.ResidueField (integers v)

/-- Total extension of the quotient map, used only on integral inputs. -/
def reduce (v : AddValuation L (WithTop ℝ)) (a : L) : Residue v :=
  if ha : 0 ≤ v a then IsLocalRing.residue (integers v) ⟨a, ha⟩ else 0

/-- [RW-rec]: pointwise integrality; this does not mention Fourier transforms. -/
def Integral {ι : Type*} (v : AddValuation L (WithTop ℝ)) (f : ι → L) : Prop :=
  ∀ x, 0 ≤ v (f x)

/-- [RW-rec]: valuation zero at every input, including nonvanishing. -/
def UnitValued {ι : Type*} (v : AddValuation L (WithTop ℝ)) (f : ι → L) : Prop :=
  ∀ x, v (f x) = 0

/-- Pointwise reduction. This is not a germ or a limiting value. -/
def reduction {ι : Type*} (v : AddValuation L (WithTop ℝ)) (f : ι → L) : ι → Residue v :=
  fun x => reduce v (f x)

variable {G : Type*} [AddCommGroup G]

/-- Literal nonzero bicharacter laws. No symmetry is required for Lemma 1. -/
def IsBicharacter (B : G → G → L) : Prop :=
  (∀ x y, B x y ≠ 0) ∧
  (∀ x x' y, B (x + x') y = B x y * B x' y) ∧
  (∀ x y y', B x (y + y') = B x y * B x y')

/-- Nondegeneracy in both variables, displayed rather than hidden in a transform. -/
def Nondegenerate (B : G → G → L) : Prop :=
  (∀ x, (∀ y, B x y = 1) → x = 0) ∧
  (∀ y, (∀ x, B x y = 1) → y = 0)

/-- [RW-rec]: negative-kernel normalized Fourier transform. The condition `r^2 = |G|` is a theorem
hypothesis, not part of this definition. -/
def fourier [Fintype G] (B : G → G → L) (r : L) (f : G → L) (y : G) : L :=
  r⁻¹ * ∑ x, f x * B x (-y)

/-- The same negative kernel without normalization. -/
def rawFourier [Fintype G] (B : G → G → L) (f : G → L) (y : G) : L :=
  ∑ x, f x * B x (-y)

/-- The actual `G[p]`; for the decompositions below it equals `H[p]`. -/
def pTorsion (p : ℕ) : AddSubgroup G :=
  (nsmulAddMonoidHom p : G →+ G).ker

/-- [RW-rec]: embed an upper prime-field digit in `Z/p^s`. -/
def topDigit (p s d : ℕ) (u : Fin d → ZMod p) : Point p s d :=
  fun i => ((p ^ (s - 1) * (u i).val : ℕ) : ZMod (p ^ s))

/-- Affine bijections of the prime-field coordinate space, with its usual pointwise module structure
fixed before importing the analytic modules. -/
abbrev AffineCoordinates (p d : ℕ) :=
  (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p)

/-- A chart on `x+H[p]`, allowing any affine prime-field coordinates. `e` supplies the full primary
decomposition, with a separate prime-to-p `C`. -/
def cosetChart {p s d : ℕ} {C : Type*} [AddCommGroup C]
    (e : (Point p s d × C) ≃+ G) (x : G)
    (a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p))
    (u : Fin d → ZMod p) : G :=
  x + e (topDigit p s d (a u), 0)

/-- One coordinate, in the call shape of `FiniteInterpolation`. -/
def lineRestriction {p s : ℕ} {C : Type*} [AddCommGroup C]
    (e : (Point p s 1 × C) ≃+ G) (v : AddValuation L (WithTop ℝ))
    (f : G → L) (x : G)
    (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) : ZMod p → Residue v :=
  fun t => reduce v (f (cosetChart e x a (fun _ => t)))

/-- Two coordinates, in the call shape of `FiniteInterpolation`. -/
def planeRestriction {p s : ℕ} {C : Type*} [AddCommGroup C]
    (e : (Point p s 2 × C) ≃+ G) (v : AddValuation L (WithTop ℝ))
    (f : G → L) (x : G)
    (a : (Fin 2 → ZMod p) ≃ᵃ[ZMod p] (Fin 2 → ZMod p)) :
    ZMod p × ZMod p → Residue v :=
  fun u => reduce v (f (cosetChart e x a ![u.1, u.2]))

variable (v : AddValuation L (WithTop ℝ))

/-- [RW-rec, p. 4]: normalization determines residue characteristic. This theorem serves as a local
instance when the finite tools are applied. -/
theorem residue_charP [CharZero L] {p : ℕ} [Fact p.Prime]
    (hp : v (p : L) = 1) : CharP (Residue v) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  have hval : v.toValuation ((p : integers v) : L) < 1 := by
    change (0 : WithTop ℝ) < v (p : L)
    rw [hp]
    norm_num
  have hzero := (IsLocalRing.residue_eq_zero_iff (p : integers v)).mpr
    ((v.toValuation.mem_maximalIdeal_iff).mpr hval)
  simpa only [map_natCast] using hzero

/-- Definition helper for [RW-rec]. -/
theorem reduce_eq_residue (a : L) (ha : 0 ≤ v a) :
    reduce v a = IsLocalRing.residue (integers v) ⟨a, ha⟩ := by
  simp only [reduce, dite_eq_left ha]

/-- [RW-rec]: the kernel of reduction on integral elements. -/
theorem reduce_eq_zero_iff (a : L) (ha : 0 ≤ v a) :
    reduce v a = 0 ↔ 0 < v a := by
  rw [reduce_eq_residue v a ha, IsLocalRing.residue_eq_zero_iff,
    v.toValuation.mem_maximalIdeal_iff]
  rfl

/-- [RW-rec]: nonzero residue means valuation zero, for integral elements. -/
theorem reduce_ne_zero_iff (a : L) (ha : 0 ≤ v a) :
    reduce v a ≠ 0 ↔ v a = 0 := by
  rw [ne_eq, reduce_eq_zero_iff v a ha]
  exact ⟨fun h => le_antisymm (le_of_not_gt h) ha, fun h => by simp [h]⟩

/-- Reduction is additive on its genuine domain, [RW-rec]. -/
theorem reduce_add (a b : L) (ha : 0 ≤ v a) (hb : 0 ≤ v b) :
    reduce v (a + b) = reduce v a + reduce v b := by
  rw [reduce_eq_residue v (a + b) (v.map_le_add ha hb),
    reduce_eq_residue v a ha, reduce_eq_residue v b hb]
  exact map_add (IsLocalRing.residue (integers v)) ⟨a, ha⟩ ⟨b, hb⟩

/-- Reduction is multiplicative on its genuine domain, [RW-rec]. -/
theorem reduce_mul (a b : L) (ha : 0 ≤ v a) (hb : 0 ≤ v b) :
    reduce v (a * b) = reduce v a * reduce v b := by
  rw [reduce_eq_residue v (a * b) (by rw [v.map_mul]; exact add_nonneg ha hb),
    reduce_eq_residue v a ha, reduce_eq_residue v b hb]
  exact map_mul (IsLocalRing.residue (integers v)) ⟨a, ha⟩ ⟨b, hb⟩

/-- Pointwise reciprocal, not inverse Fourier; [RW-rec]. -/
theorem reduce_inv (a : L) (ha : v a = 0) :
    reduce v a⁻¹ = (reduce v a)⁻¹ := by
  have hnonzero : a ≠ 0 := by
    intro hzero
    simp [hzero] at ha
  have hainv : v a⁻¹ = 0 := by rw [v.map_inv, ha, neg_zero]
  apply eq_inv_of_mul_eq_one_left
  rw [mul_comm, ← reduce_mul v a a⁻¹ (le_of_eq ha.symm) (le_of_eq hainv.symm),
    mul_inv_cancel₀ hnonzero]
  simp only [reduce, v.map_one, le_refl, dite_true]
  exact map_one (IsLocalRing.residue (integers v))

/-- [RW-rec]: congruence in the maximal ideal, with integral endpoints. -/
theorem reduce_eq_iff (a b : L) (ha : 0 ≤ v a) (hb : 0 ≤ v b) :
    reduce v a = reduce v b ↔ 0 < v (a - b) := by
  have hab : 0 ≤ v (a - b) := v.map_le_sub ha hb
  rw [← reduce_eq_zero_iff v (a - b) hab, reduce_eq_residue v a ha,
    reduce_eq_residue v b hb, reduce_eq_residue v (a - b) hab]
  change IsLocalRing.residue (integers v) ⟨a, ha⟩ =
    IsLocalRing.residue (integers v) ⟨b, hb⟩ ↔
      IsLocalRing.residue (integers v) (⟨a, ha⟩ - ⟨b, hb⟩) = 0
  rw [map_sub, sub_eq_zero]

/-- [RW-rec]: unit-valued inputs are integral. -/
theorem integral_of_unitValued {ι : Type*} (f : ι → L) (hf : UnitValued v f) :
    Integral v f := by
  intro x
  exact le_of_eq (hf x).symm

/-- [RW-rec]: a unit-valued input has a unit-valued reciprocal. -/
theorem unitValued_inverse {ι : Type*} (f : ι → L) (hf : UnitValued v f) :
    UnitValued v (fun x => (f x)⁻¹) := by
  intro x
  rw [v.map_inv, hf x, neg_zero]

/-- [RW-rec]: every bicharacter coefficient is a valuation unit. -/
theorem bicharacter_value_zero [Fintype G] (B : G → G → L)
    (hB : IsBicharacter B) (x y : G) : v (B x y) = 0 := by
  have hzero : B 0 y = 1 := by
    apply mul_left_cancel₀ (hB.1 0 y)
    simpa only [zero_add, mul_one] using (hB.2.1 0 0 y).symm
  have hsmul (n : ℕ) : B (n • x) y = B x y ^ n := by
    induction n with
    | zero => simpa only [zero_nsmul, pow_zero] using hzero
    | succ n ih => rw [succ_nsmul, hB.2.1, ih, pow_succ]
  have hroot : B x y ^ Fintype.card G = 1 := by
    rw [← hsmul, card_nsmul_eq_zero, hzero]
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr (hB.1 x y))
  have hv : Fintype.card G • v (B x y) = 0 := by
    rw [← v.map_pow, hroot, v.map_one]
  rw [← ht, ← WithTop.coe_nsmul, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hv
  have htzero := (nsmul_eq_zero_iff.mp hv).resolve_right
    (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  rw [← ht, htzero, WithTop.coe_zero]

/-- [RW-rec]: `H[p]` is the kernel of `p`, in the actual group. -/
theorem cosetChart_range {p s d : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    {C : Type*} [AddCommGroup C] [Fintype C]
    (hC : Nat.Coprime p (Fintype.card C))
    (e : (Point p s d × C) ≃+ G) (x : G)
    (a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p)) :
    Set.range (cosetChart e x a) = {y | p • (y - x) = 0} := by
  let b : CosetBase p s d := fun _ => ⟨0, pow_pos (Fact.out : p.Prime).pos _⟩
  have hbase : cosetBasePoint b = 0 := by
    ext i
    simp [cosetBasePoint, b]
  have htop (u : Fin d → ZMod p) :
      topDigit p s d u = primeCosetPoint b u := by
    ext i
    rw [primeCosetPoint_apply]
    simp [topDigit, b]
  have hrange : Set.range (topDigit p s d) = {z : Point p s d | p • z = 0} := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      have hmem : primeCosetPoint b u ∈ Set.range (cosetPoint b) :=
        ⟨(coordinateEquiv p d).symm u, rfl⟩
      rw [cosetPoint_range_eq_pTorsion_coset hs b] at hmem
      simpa only [htop, hbase, sub_zero, FiniteCosetMoments.pTorsion,
        AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] using hmem
    · intro hz
      have hmem : z ∈ Set.range (cosetPoint b) := by
        rw [cosetPoint_range_eq_pTorsion_coset hs b]
        simpa only [hbase, sub_zero, FiniteCosetMoments.pTorsion,
          AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] using hz
      obtain ⟨u, hu⟩ := hmem
      refine ⟨coordinateEquiv p d u, ?_⟩
      rw [htop]
      simpa only [primeCosetPoint, Equiv.symm_apply_apply] using hu
  have hCinj : Function.Injective (fun c : C => p • c) :=
    (Nat.Coprime.nsmul_right_bijective
      (by simpa only [Nat.card_eq_fintype_card] using hC.symm)).injective
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    change p • (x + e (topDigit p s d (a u), 0) - x) = 0
    rw [add_sub_cancel_left, ← map_nsmul e]
    have hu : p • topDigit p s d (a u) = 0 := by
      exact (Set.ext_iff.mp hrange _).mp ⟨a u, rfl⟩
    simp only [Prod.smul_mk, hu, smul_zero, Prod.mk_zero_zero]
    exact e.map_zero
  · intro hy
    have hz : p • e.symm (y - x) = 0 := by
      rw [← map_nsmul e.symm, hy, e.symm.map_zero]
    have hfirst : p • (e.symm (y - x)).1 = 0 :=
      congrArg Prod.fst hz
    have hsecond : (e.symm (y - x)).2 = 0 := by
      apply hCinj
      simpa only [Prod.smul_snd, Prod.snd_zero, smul_zero] using congrArg Prod.snd hz
    obtain ⟨u, hu⟩ := (Set.ext_iff.mp hrange _).mpr hfirst
    refine ⟨a.symm u, ?_⟩
    rw [cosetChart, a.apply_symm_apply, hu]
    have hpair : ((e.symm (y - x)).1, (0 : C)) = e.symm (y - x) :=
      Prod.ext rfl hsecond.symm
    rw [hpair, e.apply_symm_apply, add_sub_cancel]

#print fourier
#print reduce
#print cosetChart
#check @residue_charP

end SICLean.L5.LocalFourierSetup
