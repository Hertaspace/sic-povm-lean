import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Lattice-index support for the actual distribution group

An invertible additive map sends `f⁻¹(I)/I` to `I/f(I)`. The latter index is the absolute
determinant of its integral matrix on a basis of `I`. This file uses only additive groups and
integer bases, so it can be imported before the concrete distribution lattice is defined.
-/

noncomputable section

open Module

namespace SICLean.L4.DistributionLatticeAux2

/-- Compute the index of the inverse image of a lattice from the action of an invertible additive
map on an integer basis. -/
theorem card_comap_quotient_of_basis
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : AddSubgroup G) (f : G →+ G) (hf : Function.Bijective f)
    (b : Basis ι ℤ I) (hI : I ≤ I.comap f) :
    Nat.card (I.comap f ⧸ I.addSubgroupOf (I.comap f)) =
      (b.det (fun i => (⟨f (b i), hI (b i).property⟩ : I))).natAbs := by
  have hmap : I.map f ≤ I := by
    rintro _ ⟨x, hx, rfl⟩
    exact hI hx
  let bmap : Basis ι ℤ (I.map f) :=
    b.map (I.equivMapOfInjective f hf.1).toIntLinearEquiv
  change I.relIndex (I.comap f) = _
  rw [← AddSubgroup.relIndex_map_map_of_injective I (I.comap f) hf.1,
    AddSubgroup.map_comap_eq_self_of_surjective hf.2 I,
    AddSubgroup.relIndex_eq_natAbs_det (I.map f) I hmap bmap b]
  rfl

/-- The two-generator form of the index formula, with all coordinates specified by the two images of
the generators. -/
theorem card_comap_quotient_pair
    {G : Type*} [AddCommGroup G] (I : AddSubgroup G) (v w : G)
    (hspan : ∀ x : G, x ∈ I ↔ ∃ u : Fin 2 → ℤ, x = u 0 • v + u 1 • w)
    (hinj : Function.Injective (fun u : Fin 2 → ℤ => u 0 • v + u 1 • w))
    (f : G →+ G) (hf : Function.Bijective f) (hI : I ≤ I.comap f)
    (a b c d : ℤ) (hv : f v = a • v + c • w) (hw : f w = b • v + d • w) :
    Nat.card (I.comap f ⧸ I.addSubgroupOf (I.comap f)) = (a * d - b * c).natAbs := by
  let g : (Fin 2 → ℤ) →+ I :=
    { toFun := fun u => ⟨u 0 • v + u 1 • w, (hspan _).2 ⟨u, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by
        intros
        apply Subtype.ext
        simp only [AddSubgroup.coe_add, Pi.add_apply, add_zsmul]
        abel }
  have hg : Function.Bijective g := by
    constructor
    · intro u t h
      exact hinj (congrArg Subtype.val h)
    · intro x
      obtain ⟨u, hu⟩ := (hspan x.val).1 x.property
      exact ⟨u, Subtype.ext hu.symm⟩
  let e : (Fin 2 → ℤ) ≃+ I := AddEquiv.ofBijective g hg
  let basis : Basis (Fin 2) ℤ I :=
    (Pi.basisFun ℤ (Fin 2)).map e.toIntLinearEquiv
  have hb0 : (basis 0 : G) = v := by simp [basis, e, g, Pi.basisFun_apply]
  have hb1 : (basis 1 : G) = w := by simp [basis, e, g, Pi.basisFun_apply]
  have hv' : (⟨f (basis 0), hI (basis 0).property⟩ : I) =
      a • basis 0 + c • basis 1 := by
    apply Subtype.ext
    simpa only [AddSubgroup.coe_add, AddSubgroup.coe_zsmul, hb0, hb1] using hv
  have hw' : (⟨f (basis 1), hI (basis 1).property⟩ : I) =
      b • basis 0 + d • basis 1 := by
    apply Subtype.ext
    simpa only [AddSubgroup.coe_add, AddSubgroup.coe_zsmul, hb0, hb1] using hw
  rw [card_comap_quotient_of_basis I f hf basis hI]
  congr 1
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply, hv', hw']

end SICLean.L4.DistributionLatticeAux2
