import SICLean.L5.LocalCosetDegree

set_option autoImplicit false

/-!
# Strict-majority intersections on a finite torsion coset

A strict majority of a finite set meets its image under any permutation. For an additive
torsion coset, translation by a torsion element preserves the coset and gives the
consecutive pair needed by the local lemma.
-/

noncomputable section

namespace SICLean.L5.LocalLemmaOneAux

open FiniteCosetMoments LocalFourierSetup

/-- A one-dimensional affine chart parametrizes its actual torsion coset. The forward map is the
chart evaluated on a constant function on `Fin 1`. -/
def lineChartEquiv {p s : ℕ} [Fact p.Prime]
    {G C : Type*} [AddCommGroup G] [AddCommGroup C] [Fintype C]
    (hs : 1 ≤ s) (hC : Nat.Coprime p (Fintype.card C))
    (e : (Point p s 1 × C) ≃+ G) (x : G)
    (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) :
    ZMod p ≃ {y : G // p • (y - x) = 0} := by
  let : Fintype G := Fintype.ofEquiv (Point p s 1 × C) e.toEquiv
  refine Equiv.ofBijective
    (fun t : ZMod p => ⟨cosetChart e x a (fun _ => t), ?_⟩) ?_
  · have hmem : cosetChart e x a (fun _ => t) ∈ Set.range (cosetChart e x a) :=
      ⟨_, rfl⟩
    rw [cosetChart_range hs hC e x a] at hmem
    exact hmem
  · constructor
    · intro t u htu
      have hfun := LocalFourierRestriction.cosetChart_injective hs e x a
        (congrArg Subtype.val htu)
      exact congrFun hfun 0
    · intro y
      have hy : y.val ∈ Set.range (cosetChart e x a) := by
        rw [cosetChart_range hs hC e x a]
        exact y.property
      obtain ⟨u, hu⟩ := hy
      refine ⟨u 0, ?_⟩
      apply Subtype.ext
      change cosetChart e x a (fun _ => u 0) = y.val
      have huconst : (fun _ : Fin 1 => u 0) = u := by
        funext i
        exact congrArg u (Subsingleton.elim 0 i)
      rw [huconst, hu]

@[simp]
theorem lineChartEquiv_val {p s : ℕ} [Fact p.Prime]
    {G C : Type*} [AddCommGroup G] [AddCommGroup C] [Fintype C]
    (hs : 1 ≤ s) (hC : Nat.Coprime p (Fintype.card C))
    (e : (Point p s 1 × C) ≃+ G) (x : G)
    (a : (Fin 1 → ZMod p) ≃ᵃ[ZMod p] (Fin 1 → ZMod p)) (t : ZMod p) :
    (lineChartEquiv hs hC e x a t).val = cosetChart e x a (fun _ => t) := rfl

/-- An injective self-map of a finite type carries some member of any strict majority back into that
majority. -/
theorem exists_pair_of_strict_majority {α : Type*} [Finite α]
    (e : α → α) (he : Function.Injective e) (P : α → Prop)
    (hmajority : Nat.card α < 2 * Nat.card {a : α // P a}) :
    ∃ a : α, P a ∧ P (e a) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  by_contra h
  push Not at h
  let f : {a : α // P a} → {a : α // ¬ P a} :=
    fun a => ⟨e a, h a a.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact he (congrArg Subtype.val hab)
  have hle := Fintype.card_le_of_injective f hf
  rw [Fintype.card_subtype_compl] at hle
  have hsub := Fintype.card_subtype_le P
  simp only [Nat.card_eq_fintype_card] at hmajority
  omega

/-- A strict majority of a finite affine `p`-torsion coset contains two points separated by any
element killed by `p`. -/
theorem exists_adjacent_of_strict_majority {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) (x h : G) (P : G → Prop)
    (hph : p • h = 0)
    (hcard : Nat.card {t : G // p • (t - x) = 0} = p)
    (hmajority : p < 2 * Nat.card {t : G // p • (t - x) = 0 ∧ P t}) :
    ∃ t : G, p • (t - x) = 0 ∧ P t ∧ P (t + h) := by
  classical
  let A := {t : G // p • (t - x) = 0}
  let e : A → A := fun t => ⟨t.val + h, by
    rw [add_sub_right_comm, nsmul_add, t.property, hph, zero_add]⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val hab)
  let k : {a : A // P a.val} ≃ {t : G // p • (t - x) = 0 ∧ P t} :=
    { toFun := fun a => ⟨a.val.val, a.val.property, a.property⟩
      invFun := fun t => ⟨⟨t.val, t.property.1⟩, t.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmajorityA : Nat.card A < 2 * Nat.card {a : A // P a.val} := by
    rw [Nat.card_congr k, hcard]
    exact hmajority
  obtain ⟨t, ht, hnext⟩ :=
    exists_pair_of_strict_majority e he (fun a : A => P a.val) hmajorityA
  exact ⟨t.val, t.property, ht, hnext⟩

end SICLean.L5.LocalLemmaOneAux
