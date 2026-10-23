import SICLean.L5.LocalFourierSetup
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Complement
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Complex.Basic
import SICLean.L5.SplitGroupRingAux

set_option autoImplicit false

/-!
# Integer group-ring counting

[RW-rec, Lemma 6]. [RW-rec, pp. 11--12] is the source of every assertion below. The common
finite-group dictionary is [RW26, Lemma 2, p. 12]. The
function g is arbitrary. `multiplicativeEval` is a homomorphism from the additive free
abelian group to the target multiplicative group, not a ring homomorphism. Negative
coefficients are evaluated using integer powers. Summands are counted as subgroups,
never repeatedly as their generators. Oddness is not needed for Lemma 6 itself.
-/

noncomputable section
open scoped BigOperators Classical

namespace SICLean.L5.SplitGroupRing

open FiniteCosetMoments

abbrev Plane (p s : ℕ) := Point p s 2

variable {H : Type*} [AddCommGroup H] [Fintype H]

/-- Explicit basis condition on H[p], not on H. -/
def IsPTorsionBasis (p : ℕ) (a b : H) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ Disjoint (AddSubgroup.zmultiples a) (AddSubgroup.zmultiples b) ∧
    AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b = LocalFourierSetup.pTorsion p

/-- A cyclic direct summand of the full prescribed order. -/
def FullCyclicSummand (p s : ℕ) (L : AddSubgroup H) : Prop :=
  IsAddCyclic L ∧ Nat.card L = p ^ s ∧ ∃ T : AddSubgroup H, IsCompl L T

/-- The actual finite set of noncharacteristic summands. -/
def noncharacteristicSummands (p s : ℕ) (a b : H) : Finset (AddSubgroup H) :=
  (Finset.univ.image fun x : H => AddSubgroup.zmultiples x).filter fun L =>
    FullCyclicSummand p s L ∧
    L ⊓ LocalFourierSetup.pTorsion p ≠ AddSubgroup.zmultiples a ∧
    L ⊓ LocalFourierSetup.pTorsion p ≠ AddSubgroup.zmultiples b

def subgroupSum (L : AddSubgroup H) : AddMonoidAlgebra ℤ H :=
  letI : Fintype L := Fintype.ofFinite L
  ∑ l : L, AddMonoidAlgebra.single l.val 1

def mixedDifference (a b : H) : AddMonoidAlgebra ℤ H :=
  (AddMonoidAlgebra.single a 1 - AddMonoidAlgebra.single 0 1) *
    (AddMonoidAlgebra.single b 1 - AddMonoidAlgebra.single 0 1)

def multiplicativeEval {A : Type*} [CommGroup A] (g : H → A)
    (w : AddMonoidAlgebra ℤ H) : A :=
  w.coeff.prod fun x n => g x ^ n

def characterEval (χ : AddChar H ℂ) (w : AddMonoidAlgebra ℤ H) : ℂ :=
  w.coeff.sum fun x n => (n : ℂ) * χ x

def cosetProduct {A : Type*} [CommGroup A] (g : H → A)
    (L : AddSubgroup H) (x : H) : A :=
  letI : Fintype L := Fintype.ofFinite L
  ∏ l : L, g (x + l.val)

def ProductsInvariant {A : Type*} [CommGroup A] (p s : ℕ) (a b : H)
    (g : H → A) : Prop :=
  ∀ L ∈ noncharacteristicSummands p s a b, ∀ x u : H,
    p • u = 0 → cosetProduct g L (x + u) = cosetProduct g L x

/-- [RW-rec]: a delta coefficient evaluates to the specified value. -/
theorem eval_single {A : Type*} [CommGroup A] (g : H → A) (x : H) (n : ℤ) :
    multiplicativeEval g (AddMonoidAlgebra.single x n) = g x ^ n := by
  simp [multiplicativeEval]

/-- [RW-rec]: addition of exponent vectors is multiplication of values. -/
theorem eval_add {A : Type*} [CommGroup A] (g : H → A)
    (v w : AddMonoidAlgebra ℤ H) :
    multiplicativeEval g (v + w) = multiplicativeEval g v * multiplicativeEval g w := by
  exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ => zpow_add _)

/-- [RW-rec]: the negative exponents in the mixed difference are genuine inverses. -/
theorem eval_neg {A : Type*} [CommGroup A] (g : H → A) (w : AddMonoidAlgebra ℤ H) :
    multiplicativeEval g (-w) = (multiplicativeEval g w)⁻¹ := by
  calc
    multiplicativeEval g (-w) =
        (multiplicativeEval g w)⁻¹ * (multiplicativeEval g w * multiplicativeEval g (-w)) := by
      group
    _ = (multiplicativeEval g w)⁻¹ := by
      rw [← eval_add]
      simp [multiplicativeEval]

/-- [RW-rec]: scalar multiplication of exponents becomes a power. -/
theorem eval_smul {A : Type*} [CommGroup A] (g : H → A)
    (w : AddMonoidAlgebra ℤ H) (n : ℤ) :
    multiplicativeEval g (n • w) = multiplicativeEval g w ^ n := by
  let f : AddMonoidAlgebra ℤ H →+ Additive A :=
    { toFun := fun v => Additive.ofMul (multiplicativeEval g v)
      map_zero' := by simp [multiplicativeEval]
      map_add' := fun v w => eval_add g v w }
  exact congrArg Additive.toMul (map_zsmul f n w)

/-- [RW-rec]: convolution with a delta translates g. This does not claim multiplicativity with
respect to arbitrary convolutions. -/
theorem eval_translate {A : Type*} [CommGroup A] (g : H → A)
    (w : AddMonoidAlgebra ℤ H) (x : H) :
    multiplicativeEval g (AddMonoidAlgebra.single x 1 * w) =
      multiplicativeEval (fun y => g (x + y)) w := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp [multiplicativeEval]
  | add v w hv hw => simp only [mul_add, eval_add, hv, hw]
  | single y n => simp [AddMonoidAlgebra.single_mul_single, eval_single]

/-- [RW-rec]: precisely one noncharacteristic summand is the kernel of a character nontrivial on
both selected p-torsion generators. -/
theorem unique_character_kernel {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : Plane p s ≃+ H) (a b : H) (hb : IsPTorsionBasis p a b)
    (χ : AddChar H ℂ) (ha : χ a ≠ 1) (hbc : χ b ≠ 1) :
    ∃! L : AddSubgroup H, L ∈ noncharacteristicSummands p s a b ∧
      ∀ l : L, χ l.val = 1 := by
  have hat : p • a = 0 := by
    have hmem : a ∈ LocalFourierSetup.pTorsion p := by
      rw [← hb.2.2.2]
      exact AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples a)
    exact hmem
  obtain ⟨L, hL, huniq⟩ :=
    SplitGroupRingAux.unique_character_kernel_expanded hs e a b hat χ ha hbc
  refine ⟨L, ⟨?_, hL.2⟩, ?_⟩
  · apply Finset.mem_filter.mpr
    exact Finset.mem_filter.mp hL.1
  · intro M hM
    apply huniq M
    refine ⟨?_, hM.2⟩
    apply Finset.mem_filter.mpr
    exact Finset.mem_filter.mp hM.1

/-- [RW-rec] auxiliary count: distinct subgroups, not generators. -/
theorem noncharacteristic_count {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : Plane p s ≃+ H) (a b : H) (hb : IsPTorsionBasis p a b) :
    (noncharacteristicSummands p s a b).card = (p - 1) * p ^ (s - 1) := by
  have hA : AddSubgroup.zmultiples a ≤ LocalFourierSetup.pTorsion p := by
    rw [← hb.2.2.2]
    exact le_sup_left
  have hB : AddSubgroup.zmultiples b ≤ LocalFourierSetup.pTorsion p := by
    rw [← hb.2.2.2]
    exact le_sup_right
  have hat : p • a = 0 := hA (AddSubgroup.mem_zmultiples a)
  have hbt : p • b = 0 := hB (AddSubgroup.mem_zmultiples b)
  have haord : addOrderOf a = p := addOrderOf_eq_prime hat hb.1
  have hbord : addOrderOf b = p := addOrderOf_eq_prime hbt hb.2.1
  apply SplitGroupRingAux.cyclic_summands_count_of_generator_iff hs e
    (AddSubgroup.zmultiples a) (AddSubgroup.zmultiples b) hA hB hb.2.2.1
    (by rw [Nat.card_zmultiples, haord]) (by rw [Nat.card_zmultiples, hbord])
    (noncharacteristicSummands p s a b)
  · intro L hL
    exact ⟨(Finset.mem_filter.mp hL).2.1.1, (Finset.mem_filter.mp hL).2.1.2.1⟩
  · intro x
    have hgen :=
      SplitGroupRingAux.noncharacteristic_generator_iff_expanded hs e a b hb.1 hb.2.1 hat hbt x
    constructor
    · intro hx
      apply hgen.mp
      apply Finset.mem_filter.mpr
      exact Finset.mem_filter.mp hx
    · intro hx
      apply Finset.mem_filter.mpr
      exact Finset.mem_filter.mp (hgen.mpr hx)

/-- [RW-rec]: the literal integer group-ring identity. The coefficient p^s is not the number of
summands. -/
theorem counting_identity {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (e : Plane p s ≃+ H) (a b : H) (hb : IsPTorsionBasis p a b) :
    mixedDifference a b *
        (∑ L ∈ noncharacteristicSummands p s a b, subgroupSum L) =
      (p ^ s : ℤ) • mixedDifference a b := by
  apply SplitGroupRingAux.characterHom_ext
  intro χ
  let F := SplitGroupRingAux.characterHom χ
  have hm : F (mixedDifference a b) = (χ a - 1) * (χ b - 1) := by
    simp [F, mixedDifference]
  have hsub (L : AddSubgroup H) :
      F (subgroupSum L) =
        if ∀ l : L, χ l.val = 1 then (Nat.card L : ℂ) else 0 := by
    simp only [subgroupSum, map_sum, F, SplitGroupRingAux.characterHom_single,
      Int.cast_one, one_mul]
    letI : Fintype L := Fintype.ofFinite L
    by_cases hc : ∀ l : L, χ l.val = 1
    · simpa only [ite_eq_left hc] using SplitGroupRingAux.character_sum χ L
    · simpa only [ite_eq_right hc] using SplitGroupRingAux.character_sum χ L
  change F _ = F _
  rw [map_mul, map_zsmul, hm]
  by_cases ha : χ a = 1
  · simp [ha]
  by_cases hbc : χ b = 1
  · simp [hbc]
  obtain ⟨L, ⟨hL, hχL⟩, huniq⟩ := unique_character_kernel hs e a b hb χ ha hbc
  have hcard : Nat.card L = p ^ s := (Finset.mem_filter.mp hL).2.1.2.1
  have hsum : F (∑ L ∈ noncharacteristicSummands p s a b, subgroupSum L) =
      (p ^ s : ℂ) := by
    rw [map_sum, Finset.sum_eq_single L]
    · rw [hsub, ite_eq_left hχL, hcard, Nat.cast_pow]
    · intro M hM hne
      rw [hsub, ite_eq_right]
      intro hχM
      exact hne (huniq M ⟨hM, hχM⟩)
    · intro hnot
      exact (hnot hL).elim
  rw [hsum]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
  ring

/-- [RW-rec]: characteristic p gives absence of p-power torsion in k^×. -/
theorem units_no_p_power_torsion {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
    [CharP k p] (s : ℕ) (z : kˣ) (hz : z ^ (p ^ s) = 1) : z = 1 := by
  apply Units.ext
  have hz' : (z.val - 1) ^ (p ^ s) = 0 := by
    rw [sub_pow_char_pow, one_pow]
    exact sub_eq_zero.mpr (congrArg Units.val hz)
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz')

/-- [RW-rec]: the group-ring step before cancellation in the target. -/
theorem mixed_ratio_power {A : Type*} [CommGroup A] {p s : ℕ} [Fact p.Prime]
    (hs : 1 ≤ s) (e : Plane p s ≃+ H) (a b : H) (hb : IsPTorsionBasis p a b)
    (g : H → A) (hg : ProductsInvariant p s a b g) (x : H) :
    (g (x + a + b) * g x / (g (x + a) * g (x + b))) ^ (p ^ s) = 1 := by
  have esub (q : H → A) (v w : AddMonoidAlgebra ℤ H) :
      multiplicativeEval q (v - w) = multiplicativeEval q v / multiplicativeEval q w := by
    simp only [sub_eq_add_neg, eval_add, eval_neg, div_eq_mul_inv]
  have ec (L : AddSubgroup H) (y : H) :
      multiplicativeEval (fun t => g (x + t))
          (AddMonoidAlgebra.single y 1 * subgroupSum L) = cosetProduct g L (x + y) := by
    rw [eval_translate]
    letI : Fintype L := Fintype.ofFinite L
    change SplitGroupRingAux.exponentEval (fun t => g (x + (y + t)))
        (∑ l : L, AddMonoidAlgebra.single l.val 1) = _
    rw [SplitGroupRingAux.exponent_sum]
    simp only [SplitGroupRingAux.exponent_single, zpow_one, cosetProduct, add_assoc]
  have ha : p • a = 0 := by
    have hmem : a ∈ LocalFourierSetup.pTorsion p := by
      rw [← hb.2.2.2]
      exact AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples a)
    exact hmem
  have hterm (L : AddSubgroup H) (hL : L ∈ noncharacteristicSummands p s a b) :
      multiplicativeEval (fun t => g (x + t)) (mixedDifference a b * subgroupSum L) = 1 := by
    have hdiff : mixedDifference a b * subgroupSum L =
        (AddMonoidAlgebra.single (a + b) 1 * subgroupSum L -
          AddMonoidAlgebra.single a 1 * subgroupSum L) -
        (AddMonoidAlgebra.single b 1 * subgroupSum L -
          AddMonoidAlgebra.single 0 1 * subgroupSum L) := by
      simp only [mixedDifference, sub_mul, mul_sub, mul_assoc,
        AddMonoidAlgebra.single_mul_single, one_mul, add_zero, zero_add]
      abel
    rw [hdiff, esub, esub, esub, ec, ec, ec, ec]
    have hxa := hg L hL x a ha
    have hxab := hg L hL (x + b) a ha
    rw [show x + (a + b) = x + b + a by abel, hxab, hxa, add_zero]
    simp [div_eq_mul_inv]
  have hprod : multiplicativeEval (fun t => g (x + t))
      (mixedDifference a b *
        (∑ L ∈ noncharacteristicSummands p s a b, subgroupSum L)) = 1 := by
    rw [Finset.mul_sum]
    change SplitGroupRingAux.exponentEval _ _ = _
    rw [SplitGroupRingAux.exponent_sum]
    exact Finset.prod_eq_one hterm
  rw [counting_identity hs e a b hb, eval_smul] at hprod
  have hm : multiplicativeEval (fun t => g (x + t)) (mixedDifference a b) =
      g (x + a + b) * g x / (g (x + a) * g (x + b)) := by
    simp only [mixedDifference, mul_sub, sub_mul, AddMonoidAlgebra.single_mul_single,
      one_mul, add_zero, zero_add, esub, eval_single, zpow_one]
    simp [add_assoc, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hm] at hprod
  exact_mod_cast hprod

/-- [RW-rec, Lemma 6]: general target with the exact torsion hypothesis. -/
theorem lemma6 {A : Type*} [CommGroup A] {p s : ℕ} [Fact p.Prime]
    (hs : 1 ≤ s) (e : Plane p s ≃+ H) (a b : H) (hb : IsPTorsionBasis p a b)
    (hA : ∀ z : A, z ^ (p ^ s) = 1 → z = 1)
    (g : H → A) (hg : ProductsInvariant p s a b g) :
    ∀ x : H, g (x + a + b) * g x = g (x + a) * g (x + b) := by
  intro x
  exact div_eq_one.mp (hA _ (mixed_ratio_power hs e a b hb g hg x))

/-- [RW-rec, Lemma 6] specialized to the actual residue-field target. -/
theorem lemma6_residue {k : Type*} [Field k] {p s : ℕ} [Fact p.Prime] [CharP k p]
    (hs : 1 ≤ s) (e : Plane p s ≃+ H) (a b : H) (hb : IsPTorsionBasis p a b)
    (g : H → kˣ) (hg : ProductsInvariant p s a b g) :
    ∀ x : H, g (x + a + b) * g x = g (x + a) * g (x + b) := by
  exact lemma6 hs e a b hb (fun z => units_no_p_power_torsion s z) g hg

/-- [RW-rec]: explicit separation on each p-torsion coset, for all digits. -/
theorem coordinate_factorization {A : Type*} [CommGroup A] (g : H → A) (a b : H)
    (hmix : ∀ x : H, g (x + a + b) * g x = g (x + a) * g (x + b))
    (x : H) (u w : ℕ) :
    g (x + u • a + w • b) = g (x + u • a) * g (x + w • b) / g x := by
  have step (y : H) : g (y + a + b) = g (y + a) * g (y + b) / g y :=
    eq_div_iff_mul_eq'.mpr (hmix y)
  have along (y : H) (n : ℕ) :
      g (y + n • a + b) = g (y + n • a) * g (y + b) / g y := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        g (y + (n + 1) • a + b) = g (y + n • a + a + b) := by
          simp [succ_nsmul, add_assoc]
        _ = g (y + n • a + a) * g (y + n • a + b) / g (y + n • a) := step _
        _ = g (y + (n + 1) • a) * g (y + b) / g y := by
          rw [ih]
          simp only [succ_nsmul, add_assoc, div_eq_mul_inv, mul_assoc]
          rw [mul_left_comm (g (y + n • a)) (g (y + b)),
            mul_left_comm (g (y + n • a)) ((g y)⁻¹)]
          simp
  induction w with
  | zero => simp
  | succ w ih =>
    calc
      g (x + u • a + (w + 1) • b) = g (x + w • b + u • a + b) := by
        congr 1
        simp only [succ_nsmul]
        abel
      _ = g (x + w • b + u • a) * g (x + w • b + b) / g (x + w • b) := along _ _
      _ = g (x + u • a) * g (x + (w + 1) • b) / g x := by
        rw [show x + w • b + u • a = x + u • a + w • b by abel, ih]
        simp only [succ_nsmul, add_assoc, div_eq_mul_inv, mul_assoc]
        rw [mul_left_comm (g (x + w • b)) ((g x)⁻¹),
          mul_left_comm (g (x + w • b)) (g (x + (w • b + b)))]
        simp [mul_comm]


end SICLean.L5.SplitGroupRing
