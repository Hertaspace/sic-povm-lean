import SICLean.L5.LocalFourierSetup
import Mathlib.Algebra.BigOperators.Pi

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalFourierRestrictionAux

open FiniteCosetMoments LocalFourierSetup

variable {L G : Type*} [Field L] [AddCommGroup G]

theorem bicharacter_zero_left (B : G → G → L) (hB : IsBicharacter B) (y : G) :
    B 0 y = 1 := by
  apply mul_left_cancel₀ (hB.1 0 y)
  simpa only [zero_add, mul_one] using (hB.2.1 0 0 y).symm

theorem bicharacter_zero_right (B : G → G → L) (hB : IsBicharacter B) (x : G) :
    B x 0 = 1 := by
  apply mul_left_cancel₀ (hB.1 x 0)
  simpa only [zero_add, mul_one] using (hB.2.2 x 0 0).symm

theorem bicharacter_nsmul_left (B : G → G → L) (hB : IsBicharacter B)
    (n : ℕ) (x y : G) : B (n • x) y = B x y ^ n := by
  induction n with
  | zero => simp [bicharacter_zero_left B hB]
  | succ n ih => simp only [succ_nsmul, hB.2.1, ih, pow_succ]

theorem bicharacter_nsmul_right (B : G → G → L) (hB : IsBicharacter B)
    (n : ℕ) (x y : G) : B x (n • y) = B x y ^ n := by
  induction n with
  | zero => simp [bicharacter_zero_right B hB]
  | succ n ih => simp only [succ_nsmul, hB.2.2, ih, pow_succ]

theorem bicharacter_sum_left {ι : Type*} (B : G → G → L) (hB : IsBicharacter B)
    (t : Finset ι) (x : ι → G) (y : G) : B (∑ i ∈ t, x i) y = ∏ i ∈ t, B (x i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [bicharacter_zero_left B hB]
  | @insert i t hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, hB.2.1, ih]

variable {n d : ℕ} [NeZero n]

def coordinate (i : Fin d) : Fin d → ZMod n := Pi.single i 1

omit [NeZero n] in
theorem exponent_nsmul_eq_zero (x : Fin d → ZMod n) : n • x = 0 := by
  ext i
  simp [nsmul_eq_mul]

omit [NeZero n] in
theorem bicharacter_pow_eq_one (B : (Fin d → ZMod n) → (Fin d → ZMod n) → L)
    (hB : IsBicharacter B) (x y : Fin d → ZMod n) : B x y ^ n = 1 := by
  rw [← bicharacter_nsmul_left B hB, exponent_nsmul_eq_zero,
    bicharacter_zero_left B hB]

theorem coordinate_decomposition (x : Fin d → ZMod n) :
    (∑ i, (x i).val • coordinate i) = x := by
  classical
  ext j
  rw [Finset.sum_apply]
  change (∑ i, (x i).val • coordinate i j) = x j
  simp [coordinate, Pi.single_apply, nsmul_eq_mul]

/-- A character detecting a nonzero element of order `p` has full `p^s`-order when evaluated on a
lift of that element. -/
theorem primitive_root_of_nondegenerate {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (hd : 0 < d) (B : Point p s d → Point p s d → L)
    (hB : IsBicharacter B) (hnd : Nondegenerate B) :
    ∃ z : L, IsPrimitiveRoot z (p ^ s) := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let i : Fin d := ⟨0, hd⟩
  let e : Point p s d := coordinate i
  have hkpos : 0 < p ^ (s - 1) := pow_pos hp.pos _
  have hklt : p ^ (s - 1) < p ^ s :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hknz : ((p ^ (s - 1) : ℕ) : ZMod (p ^ s)) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hklt, ZMod.val_zero] at hh
    omega
  have henz : p ^ (s - 1) • e ≠ 0 := by
    intro h
    apply hknz
    have hh := congrFun h i
    simpa [e, coordinate, nsmul_eq_mul] using hh
  obtain ⟨y, hy⟩ : ∃ y, B (p ^ (s - 1) • e) y ≠ 1 := by
    by_contra h
    push Not at h
    exact henz (hnd.1 _ h)
  refine ⟨B e y, IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  have hnot : B e y ^ p ^ (s - 1) ≠ 1 := by
    rwa [← bicharacter_nsmul_left B hB]
  have hfin : B e y ^ p ^ ((s - 1) + 1) = 1 := by
    simpa only [Nat.sub_add_cancel hs] using bicharacter_pow_eq_one B hB e y
  simpa only [Nat.sub_add_cancel hs] using orderOf_eq_prime_pow hnot hfin

theorem pow_val_injective {z : L} (hz : IsPrimitiveRoot z n) :
    Function.Injective (fun a : ZMod n => z ^ a.val) := by
  intro a b hab
  exact ZMod.val_injective n (hz.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab)

theorem pow_val_add {z : L} (hz : IsPrimitiveRoot z n) (a b : ZMod n) :
    z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hz.pow_eq_one, pow_add]

def logarithm {z : L} (hz : IsPrimitiveRoot z n) (a : L) (ha : a ^ n = 1) : ZMod n :=
  (Classical.choose (hz.eq_pow_of_pow_eq_one ha) : ℕ)

theorem logarithm_spec {z : L} (hz : IsPrimitiveRoot z n) (a : L) (ha : a ^ n = 1) :
    z ^ (logarithm hz a ha).val = a := by
  unfold logarithm
  rw [ZMod.val_natCast_of_lt (Classical.choose_spec (hz.eq_pow_of_pow_eq_one ha)).1]
  exact (Classical.choose_spec (hz.eq_pow_of_pow_eq_one ha)).2

/-- Discrete logarithms of the characters of the fixed domain basis. -/
def frequencyMap {z : L} (hz : IsPrimitiveRoot z n)
    (B : (Fin d → ZMod n) → (Fin d → ZMod n) → L) (hB : IsBicharacter B) :
    (Fin d → ZMod n) →+ (Fin d → ZMod n) where
  toFun y i := logarithm hz (B (coordinate i) y)
    (bicharacter_pow_eq_one B hB (coordinate i) y)
  map_zero' := by
    ext i
    apply pow_val_injective hz
    dsimp only [Pi.zero_apply]
    rw [logarithm_spec, bicharacter_zero_right B hB]
    simp
  map_add' y y' := by
    ext i
    apply pow_val_injective hz
    dsimp only [Pi.add_apply]
    rw [pow_val_add hz, logarithm_spec, logarithm_spec, logarithm_spec]
    exact hB.2.2 _ _ _

theorem frequencyMap_spec {z : L} (hz : IsPrimitiveRoot z n)
    (B : (Fin d → ZMod n) → (Fin d → ZMod n) → L) (hB : IsBicharacter B)
    (y : Fin d → ZMod n) (i : Fin d) :
    z ^ (frequencyMap hz B hB y i).val = B (coordinate i) y :=
  logarithm_spec hz _ (bicharacter_pow_eq_one B hB (coordinate i) y)

theorem bicharacter_coordinates {z : L} (hz : IsPrimitiveRoot z n)
    (B : (Fin d → ZMod n) → (Fin d → ZMod n) → L) (hB : IsBicharacter B)
    (x y : Fin d → ZMod n) :
    B x y = z ^ (∑ i, (x i).val * (frequencyMap hz B hB y i).val) := by
  conv_lhs => rw [← coordinate_decomposition x]
  rw [bicharacter_sum_left B hB]
  simp_rw [bicharacter_nsmul_left B hB, ← frequencyMap_spec hz B hB y]
  simp_rw [← pow_mul]
  simp_rw [Nat.mul_comm (frequencyMap hz B hB y _).val]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem frequencyMap_injective {z : L} (hz : IsPrimitiveRoot z n)
    (B : (Fin d → ZMod n) → (Fin d → ZMod n) → L) (hB : IsBicharacter B)
    (hnd : Nondegenerate B) : Function.Injective (frequencyMap hz B hB) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  apply hnd.2 y
  intro x
  rw [bicharacter_coordinates hz B hB, hy]
  simp

/-- A nondegenerate pairing becomes the standard dot-product kernel after changing only the
frequency coordinates. The root is derived from the pairing. -/
theorem standard_kernel {p s d : ℕ} [Fact p.Prime] [CharZero L]
    (hs : 1 ≤ s) (hd : d = 1 ∨ d = 2) (B : Point p s d → Point p s d → L)
    (hB : IsBicharacter B) (hnd : Nondegenerate B) :
    ∃ z : L, IsPrimitiveRoot z (p ^ s) ∧
      ∃ T : Point p s d ≃+ Point p s d,
        ∀ x y, B x (T y) = z ^ (∑ i, (x i).val * (y i).val) := by
  classical
  have : NeZero (p ^ s) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> omega
  obtain ⟨z, hz⟩ := primitive_root_of_nondegenerate hs hdpos B hB hnd
  let F : Point p s d ≃+ Point p s d :=
    AddEquiv.ofBijective (frequencyMap hz B hB)
      ⟨frequencyMap_injective hz B hB hnd,
        (Finite.injective_iff_surjective).mp (frequencyMap_injective hz B hB hnd)⟩
  refine ⟨z, hz, F.symm, ?_⟩
  intro x y
  rw [bicharacter_coordinates hz B hB]
  have hy : frequencyMap hz B hB (F.symm y) = y := F.apply_symm_apply y
  rw [hy]

end SICLean.L5.LocalFourierRestrictionAux
