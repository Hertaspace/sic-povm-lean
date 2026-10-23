import SICLean.L5.OddPrimeValues
import SICLean.L5.LocalActualFourier
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false

noncomputable section
open scoped Classical BigOperators MatrixGroups

namespace SICLean.L5.OddPrimeCyclicAux

open LocalFourierSetup

theorem primary_decomposition {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (hc : IsAddCyclic (AddCommGroup.primaryComponent G p))
    (hn : Nontrivial (AddCommGroup.primaryComponent G p)) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ C : AddSubgroup G,
      Nat.Coprime p (Nat.card C) ∧
      Nonempty ((FiniteCosetMoments.Point p s 1 × C) ≃+ G) := by
  let A : AddSubgroup G := AddCommGroup.primaryComponent G p
  let Q : Subgroup (Multiplicative G) := A.toSubgroup
  have hQ : IsPGroup p Q := by
    intro x
    obtain ⟨k, hk⟩ := x.property
    exact ⟨k, Subtype.ext hk⟩
  let P : Sylow p (Multiplicative G) :=
    { Q with
      isPGroup' := hQ
      is_maximal' := by
        intro R hR hQR
        apply le_antisymm ?_ hQR
        intro x hx
        obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
        exact ⟨k, congrArg Subtype.val hk⟩ }
  have hP : Subgroup.normalizer (P : Set (Multiplicative G)) ≤
      Subgroup.centralizer (P : Set (Multiplicative G)) := by
    intro x _
    exact Subgroup.mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
  let C : AddSubgroup G := (MonoidHom.transferSylow P hP).ker.toAddSubgroup
  have hC : Nat.Coprime p (Nat.card C) :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hP)
  let f : A × C →+ G := A.subtype.coprod C.subtype
  have hf : Function.Bijective f := (MonoidHom.ker_transferSylow_isComplement' P hP).symm
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hQ
  have hcard : Nat.card A = p ^ s := hs
  have hspos : 1 ≤ s := by
    letI : Nontrivial A := hn
    have hnontriv : 1 < Nat.card A := Finite.one_lt_card
    by_contra h
    have hs0 : s = 0 := by omega
    simp only [hs0, pow_zero] at hcard
    omega
  have eA : ZMod (p ^ s) ≃+ A :=
    (ZMod.ringEquivCongr hcard.symm).toAddEquiv.trans
      (zmodAddCyclicAddEquiv (G := A) hc)
  let e0 : FiniteCosetMoments.Point p s 1 ≃+ A :=
    (AddEquiv.funUnique (Fin 1) (ZMod (p ^ s))).trans eA
  exact ⟨s, hspos, C, hC,
    ⟨(e0.prodCongr (AddEquiv.refl C)).trans (AddEquiv.ofBijective f hf)⟩⟩

theorem diameter_attained {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) (w : G → ℝ) :
    (∃ x y : G, p • (x - y) = 0 ∧
      sSup {d : ℝ | ∃ x y : G, p • (x - y) = 0 ∧ d = w x - w y} = w x - w y) ∧
    ∀ x y : G, p • (x - y) = 0 →
      w x - w y ≤ sSup {d : ℝ | ∃ x y : G, p • (x - y) = 0 ∧ d = w x - w y} := by
  let S := {d : ℝ | ∃ x y : G, p • (x - y) = 0 ∧ d = w x - w y}
  have hS : S.Finite := by
    apply (Set.finite_range (fun xy : G × G => w xy.1 - w xy.2)).subset
    rintro d ⟨x, y, _, rfl⟩
    exact ⟨(x, y), rfl⟩
  have hne : S.Nonempty := ⟨0, 0, 0, by simp⟩
  exact ⟨hne.csSup_mem hS, fun x y hxy => le_csSup hS.bddAbove ⟨x, y, hxy, rfl⟩⟩

theorem map_mul_coe {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℝ)) {x y : L} {a b : ℝ}
    (hx : v x = (a : WithTop ℝ)) (hy : v y = (b : WithTop ℝ)) :
    v (x * y) = ((a + b : ℝ) : WithTop ℝ) := by
  rw [v.map_mul, hx, hy, WithTop.coe_add]

theorem map_div_coe {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℝ)) {x y : L} {a b : ℝ}
    (hx : v x = (a : WithTop ℝ)) (hy : v y = (b : WithTop ℝ)) :
    v (x / y) = ((a - b : ℝ) : WithTop ℝ) := by
  rw [v.map_div, hx, hy]
  rfl

theorem map_inv_coe {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℝ)) {x : L} {a : ℝ}
    (hx : v x = (a : WithTop ℝ)) : v x⁻¹ = ((-a : ℝ) : WithTop ℝ) := by
  rw [v.map_inv, hx]
  rfl

theorem fourier_comp {G H L : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] [Field L]
    (e : G ≃+ H) (B : H → H → L) (r : L) (f : H → L) (y : G) :
    fourier (fun x y => B (e x) (e y)) r (fun x => f (e x)) y =
      fourier B r f (e y) := by
  unfold LocalFourierSetup.fourier
  simp only [map_neg]
  congr 1
  exact e.toEquiv.sum_comp (fun x => f x * B x (-e y))

theorem bicharacter_comp {G H L : Type*} [AddCommGroup G] [AddCommGroup H] [Field L]
    (e : G ≃+ H) (B : H → H → L) (hB : IsBicharacter B) :
    IsBicharacter (fun x y => B (e x) (e y)) := by
  exact ⟨fun x y => hB.1 _ _,
    fun x x' y => by simpa only [map_add] using hB.2.1 (e x) (e x') (e y),
    fun x y y' => by simpa only [map_add] using hB.2.2 (e x) (e y) (e y')⟩

theorem nondegenerate_comp {G H L : Type*} [AddCommGroup G] [AddCommGroup H] [Field L]
    (e : G ≃+ H) (B : H → H → L) (hB : Nondegenerate B) :
    Nondegenerate (fun x y => B (e x) (e y)) := by
  constructor
  · intro x hx
    apply e.injective
    rw [map_zero]
    exact hB.1 (e x) (fun y => by simpa using hx (e.symm y))
  · intro y hy
    apply e.injective
    rw [map_zero]
    exact hB.2 (e y) (fun x => by simpa using hy (e.symm x))

theorem actual_fourier_transfer {G : Type*} [AddCommGroup G] [Fintype G]
    (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
    (e : G ≃+ L4.SpecialValueGroup M) (v : AddValuation Galois.Qbar (WithTop ℝ))
    (f : G → Galois.Qbar) (f' : L4.SpecialValueGroup M → Galois.Qbar)
    (hf : ∀ x, f x = f' (e x))
    (hF : Integral v (FiniteAlgebraicTransport.fourier M hM f')) :
    Integral v (fourier (fun x y => FiniteAlgebraicTransport.pairing M hM (e x) (e y))
      (FiniteAlgebraicTransport.sqrtOrder M hM) f) := by
  letI := L4.specialValueGroup_finite M hM
  letI := Fintype.ofFinite (L4.SpecialValueGroup M)
  have hfun : f = fun x => f' (e x) := funext hf
  intro y
  rw [hfun, fourier_comp, LocalActualFourier.generic_fourier_eq]
  exact hF (e y)

theorem fourier_mul_const {G L : Type*} [AddCommGroup G] [Fintype G] [Field L]
    (B : G → G → L) (r a : L) (f : G → L) (y : G) :
    fourier B r (fun x => a * f x) y = a * fourier B r f y := by
  simp only [LocalFourierSetup.fourier, mul_assoc, ← Finset.mul_sum]
  ring

theorem integral_fourier_inv_of_div {G L : Type*} [AddCommGroup G] [Fintype G] [Field L]
    (v : AddValuation L (WithTop ℝ)) (B : G → G → L) (r a : L) (f : G → L)
    (ha : v a = 0) (hF : Integral v (fourier B r (fun x => a / f x))) :
    Integral v (fourier B r (fun x => (f x)⁻¹)) := by
  intro y
  have := hF y
  simp only [div_eq_mul_inv] at this
  rw [fourier_mul_const, v.map_mul, ha, zero_add] at this
  exact this

theorem translationRatio_product {G L : Type*} [AddCommGroup G] [Field L]
    (E : G → L) (hE : ∀ x, E x ≠ 0) (h t : G) (n : ℕ) (hn : n • h = 0) :
    (∏ j : Fin n, LocalLemmaOne.translationRatio E h (t + j.val • h)) = 1 := by
  have htel (m : ℕ) :
      (∏ j : Fin m, LocalLemmaOne.translationRatio E h (t + j.val • h)) =
        E (t + m • h) / E t := by
    induction m with
    | zero => simp [hE]
    | succ m ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      simp only [LocalLemmaOne.translationRatio, succ_nsmul', ← add_assoc]
      field_simp [hE]
      congr 1
      abel
  rw [htel, hn, add_zero, div_self (hE t)]

end SICLean.L5.OddPrimeCyclicAux
