import SICLean.L5.LocalFourierSetup
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false

/-!
# Additive coordinates on the prime torsion subgroup

The upper-digit embedding is additive and injective. A chosen additive basis of the
actual prime torsion subgroup therefore determines a linear change of the prime-field
coordinates, and hence an affine chart of the form used by the local Fourier lemmas.
-/

noncomputable section

namespace SICLean.L5.SplitUniformDirectionAux

open FiniteCosetMoments LocalFourierSetup

theorem topDigit_add {p s d : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (u v : Fin d → ZMod p) :
    LocalFourierSetup.topDigit p s d (u + v) =
      LocalFourierSetup.topDigit p s d u + LocalFourierSetup.topDigit p s d v := by
  have hpow : p ^ (s - 1) * p = p ^ s := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  have hzero : ((p ^ (s - 1) : ℕ) : ZMod (p ^ s)) * (p : ZMod (p ^ s)) = 0 := by
    rw [← Nat.cast_mul, hpow, ZMod.natCast_self]
  funext i
  change ((p ^ (s - 1) * (u i + v i).val : ℕ) : ZMod (p ^ s)) = _
  rw [ZMod.val_add]
  have hdiv := Nat.mod_add_div ((u i).val + (v i).val) p
  have hcast := congrArg
    (fun n : ℕ => ((p ^ (s - 1) * n : ℕ) : ZMod (p ^ s))) hdiv
  simp only [Nat.mul_add, Nat.cast_add, ← Nat.mul_assoc] at hcast
  simp only [Nat.cast_mul, hzero, zero_mul, add_zero] at hcast
  simpa only [Pi.add_apply, LocalFourierSetup.topDigit, Nat.cast_mul,
    Nat.cast_add, mul_add] using hcast

theorem topDigit_injective {p s d : ℕ} [Fact p.Prime] (hs : 1 ≤ s) :
    Function.Injective (LocalFourierSetup.topDigit p s d) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < p ^ (s - 1) := pow_pos hp _
  have hpow : p ^ (s - 1) * p = p ^ s := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  have hbound (u : Fin d → ZMod p) (i : Fin d) :
      p ^ (s - 1) * (u i).val < p ^ s := by
    rw [← hpow]
    exact Nat.mul_lt_mul_of_pos_left (u i).val_lt hq
  intro u v h
  funext i
  apply ZMod.val_injective
  have hi := congrArg ZMod.val (congrFun h i)
  change ((p ^ (s - 1) * (u i).val : ℕ) : ZMod (p ^ s)).val =
    ((p ^ (s - 1) * (v i).val : ℕ) : ZMod (p ^ s)).val at hi
  rw [ZMod.val_natCast_of_lt (hbound u i), ZMod.val_natCast_of_lt (hbound v i)] at hi
  exact Nat.eq_of_mul_eq_mul_left hq hi

theorem topDigit_nsmul {p s d : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (u : Fin d → ZMod p) : p • LocalFourierSetup.topDigit p s d u = 0 := by
  have hpow : p * p ^ (s - 1) = p ^ s := by
    rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel hs]
  funext i
  change p • ((p ^ (s - 1) * (u i).val : ℕ) : ZMod (p ^ s)) = 0
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.mul_assoc, hpow, Nat.cast_mul,
    ZMod.natCast_self, zero_mul]

variable {G : Type*} [AddCommGroup G]

/-- A chosen split torsion basis is realized by one of the existing affine charts. -/
theorem adapted_coordinates {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    {C : Type*} [AddCommGroup C] [Fintype C]
    (_hC : Nat.Coprime p (Fintype.card C))
    (e : (Point p s 2 × C) ≃+ G)
    (c : (ZMod p × ZMod p) ≃+ LocalFourierSetup.pTorsion p (G := G)) :
    ∃ a : AffineCoordinates p 2, ∀ u w : ZMod p,
      e (LocalFourierSetup.topDigit p s 2 (a ![u, w]), 0) = (c (u, w)).val := by
  let t : (Fin 2 → ZMod p) →+ LocalFourierSetup.pTorsion p (G := G) :=
    { toFun := fun u => ⟨e (LocalFourierSetup.topDigit p s 2 u, 0), by
        change p • e (LocalFourierSetup.topDigit p s 2 u, 0) = 0
        rw [← map_nsmul]
        simp [topDigit_nsmul hs u]⟩
      map_zero' := by
        apply Subtype.ext
        change e (LocalFourierSetup.topDigit p s 2 0, 0) = 0
        have h0 : LocalFourierSetup.topDigit p s 2 0 = 0 := by
          funext i
          simp [LocalFourierSetup.topDigit]
        simp [h0]
      map_add' := by
        intro u v
        apply Subtype.ext
        change e (LocalFourierSetup.topDigit p s 2 (u + v), 0) =
          e (LocalFourierSetup.topDigit p s 2 u, 0) +
            e (LocalFourierSetup.topDigit p s 2 v, 0)
        rw [topDigit_add hs, ← map_add]
        simp }
  have ht : Function.Injective t := by
    intro u v huv
    apply topDigit_injective hs
    have h := e.injective (congrArg Subtype.val huv)
    exact congrArg Prod.fst h
  let b : (Fin 2 → ZMod p) ≃+ LocalFourierSetup.pTorsion p (G := G) :=
    (LinearEquiv.finTwoArrow (ZMod p) (ZMod p)).toAddEquiv.trans c
  have hsurj : Function.Surjective t :=
    (Finite.injective_iff_surjective_of_equiv b.toEquiv).mp ht
  let te : (Fin 2 → ZMod p) ≃+ LocalFourierSetup.pTorsion p (G := G) :=
    AddEquiv.ofBijective t ⟨ht, hsurj⟩
  let aAdd : (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod p) := b.trans te.symm
  let aLin : (Fin 2 → ZMod p) ≃ₗ[ZMod p] (Fin 2 → ZMod p) :=
    aAdd.toLinearEquiv (ZMod.map_smul aAdd)
  refine ⟨aLin.toAffineEquiv, ?_⟩
  intro u w
  change (t (aAdd ![u, w])).val = (c (u, w)).val
  apply congrArg Subtype.val
  change te (te.symm (b ![u, w])) = c (u, w)
  rw [te.apply_symm_apply]
  rfl

end SICLean.L5.SplitUniformDirectionAux
