import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false

/-!
# Finite character extension and orthogonality lemmas

Characters compatible with a homomorphism are a translate of the dual of its cokernel.
This gives extension existence, the extension count, off-range orthogonality, and the
fibre identity when the groups have equal cardinality.
-/

noncomputable section
open scoped Classical BigOperators

namespace SICLean.L5.OddPrimeCharacterAverageAux

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H]

lemma extend_subgroup (R : AddSubgroup H) (ψ : AddChar R ℂ) :
    ∃ χ : AddChar H ℂ, ∀ x : R, χ x.val = ψ x := by
  let ρ : R.toSubgroup →* ℂˣ := ψ.toMonoidHom.toHomUnits
  obtain ⟨χ, hχ⟩ := MonoidHom.domRestrict_surjective ℂ R.toSubgroup ρ
  refine ⟨AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp χ), ?_⟩
  intro x
  have hx := congrArg (fun f : R.toSubgroup →* ℂˣ => (f x : ℂ)) hχ
  exact hx

lemma extension_nonempty_iff (φ : G →+ H) (θ : AddChar G ℂ) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => ∀ x : G, χ (φ x) = θ x)).Nonempty ↔
      ∀ x ∈ φ.ker, θ x = 1 := by
  constructor
  · rintro ⟨χ, hχ⟩ x hx
    have h := (Finset.mem_filter.mp hχ).2 x
    simpa only [AddMonoidHom.mem_ker.mp hx, AddChar.map_zero_eq_one] using h.symm
  · intro hθ
    let θq : AddChar (G ⧸ φ.ker) ℂ := AddChar.toAddMonoidHomEquiv.symm
      (QuotientAddGroup.lift φ.ker θ.toAddMonoidHom (fun x hx => hθ x hx))
    let e := QuotientAddGroup.quotientKerEquivRange φ
    let θr : AddChar φ.range ℂ := θq.compAddMonoidHom e.symm.toAddMonoidHom
    obtain ⟨χ, hχ⟩ := extend_subgroup φ.range θr
    refine ⟨χ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro x
    have he : e.symm (φ.rangeRestrict x) = (QuotientAddGroup.mk x : G ⧸ φ.ker) := by
      apply e.injective
      rw [e.apply_symm_apply]
      rfl
    change χ (φ.rangeRestrict x).val = θ x
    rw [hχ]
    change θq (e.symm (φ.rangeRestrict x)) = θ x
    rw [he]
    rfl

/-- Pullback from the quotient parametrizes all extensions of one fixed character. -/
def extensionParam (φ : G →+ H) (θ : AddChar G ℂ) (χ₀ : AddChar H ℂ)
    (hχ₀ : ∀ x : G, χ₀ (φ x) = θ x) :
    AddChar (H ⧸ φ.range) ℂ → {χ : AddChar H ℂ // ∀ x : G, χ (φ x) = θ x} :=
  fun ψ => ⟨χ₀ + ψ.compAddMonoidHom (QuotientAddGroup.mk' φ.range), by
    intro x
    have hx : (QuotientAddGroup.mk' φ.range) (φ x) = 0 := by
      exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨x, rfl⟩
    simp only [AddChar.add_apply, AddChar.compAddMonoidHom_apply, hx,
      AddChar.map_zero_eq_one, mul_one, hχ₀]⟩

omit [Fintype G] [Fintype H] in
lemma extensionParam_bijective (φ : G →+ H) (θ : AddChar G ℂ) (χ₀ : AddChar H ℂ)
    (hχ₀ : ∀ x : G, χ₀ (φ x) = θ x) :
    Function.Bijective (extensionParam φ θ χ₀ hχ₀) := by
  constructor
  · intro ψ₁ ψ₂ h
    apply AddChar.compAddMonoidHom_injective_left (QuotientAddGroup.mk' φ.range)
      (QuotientAddGroup.mk'_surjective φ.range)
    exact add_left_cancel (congrArg Subtype.val h)
  · intro χ
    have hk : φ.range ≤ (χ.val - χ₀).toAddMonoidHom.ker := by
      rintro y ⟨x, rfl⟩
      change (χ.val - χ₀) (φ x) = 1
      rw [AddChar.sub_apply', χ.property x, hχ₀ x]
      exact div_self (AddChar.val_isUnit θ x).ne_zero
    let ψ : AddChar (H ⧸ φ.range) ℂ := AddChar.toAddMonoidHomEquiv.symm
      (QuotientAddGroup.lift φ.range (χ.val - χ₀).toAddMonoidHom hk)
    refine ⟨ψ, Subtype.ext ?_⟩
    change χ₀ + ψ.compAddMonoidHom (QuotientAddGroup.mk' φ.range) = χ.val
    have hp : ψ.compAddMonoidHom (QuotientAddGroup.mk' φ.range) = χ.val - χ₀ := by
      ext y
      rfl
    rw [hp, add_comm, sub_add_cancel]

lemma extension_card (φ : G →+ H) (θ : AddChar G ℂ)
    (hθ : ∀ x ∈ φ.ker, θ x = 1) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => ∀ x : G, χ (φ x) = θ x)).card =
      φ.range.index := by
  obtain ⟨χ₀, hχ₀⟩ := (extension_nonempty_iff φ θ).mpr hθ
  have hc := Fintype.card_congr (Equiv.ofBijective
    (extensionParam φ θ χ₀ (Finset.mem_filter.mp hχ₀).2)
    (extensionParam_bijective φ θ χ₀ (Finset.mem_filter.mp hχ₀).2))
  rw [AddChar.card_eq, Fintype.card_subtype] at hc
  rw [← hc, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]

lemma extension_sum_reindex (φ : G →+ H) (θ : AddChar G ℂ) (χ₀ : AddChar H ℂ)
    (hχ₀ : ∀ x : G, χ₀ (φ x) = θ x) (f : AddChar H ℂ → ℂ) :
    (∑ χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => ∀ x : G, χ (φ x) = θ x), f χ) =
      ∑ ψ : AddChar (H ⧸ φ.range) ℂ,
        f (χ₀ + ψ.compAddMonoidHom (QuotientAddGroup.mk' φ.range)) := by
  symm
  apply Finset.sum_bij (fun ψ _ => (extensionParam φ θ χ₀ hχ₀ ψ).val)
  · intro ψ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (extensionParam φ θ χ₀ hχ₀ ψ).property⟩
  · intro ψ₁ _ ψ₂ _ h
    exact (extensionParam_bijective φ θ χ₀ hχ₀).injective (Subtype.ext h)
  · intro χ hχ
    obtain ⟨ψ, hψ⟩ := (extensionParam_bijective φ θ χ₀ hχ₀).surjective
      ⟨χ, (Finset.mem_filter.mp hχ).2⟩
    exact ⟨ψ, Finset.mem_univ _, congrArg Subtype.val hψ⟩
  · intro ψ _
    rfl

lemma extension_sum_off_range (φ : G →+ H) (θ : AddChar G ℂ)
    (hθ : ∀ x ∈ φ.ker, θ x = 1) (y : H) (hy : y ∉ φ.range) :
    ∑ χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => ∀ x : G, χ (φ x) = θ x),
      (χ y)⁻¹ = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := (extension_nonempty_iff φ θ).mpr hθ
  rw [extension_sum_reindex φ θ χ₀ (Finset.mem_filter.mp hχ₀).2]
  simp only [AddChar.add_apply, AddChar.compAddMonoidHom_apply, mul_inv_rev]
  rw [← Finset.sum_mul]
  have hsum : ∑ ψ : AddChar (H ⧸ φ.range) ℂ,
      (ψ ((QuotientAddGroup.mk' φ.range) y))⁻¹ = 0 := by
    simp_rw [← AddChar.map_neg_eq_inv]
    apply (AddChar.sum_apply_eq_zero_iff_ne_zero).mpr
    exact neg_ne_zero.mpr (mt (QuotientAddGroup.eq_zero_iff y).mp hy)
  rw [hsum, zero_mul]

omit [Fintype G] in
lemma range_index_eq_card_ker (φ : G →+ H) (hcard : Nat.card G = Nat.card H) :
    φ.range.index = Nat.card φ.ker := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card φ.range from Nat.card_pos)
  calc
    Nat.card φ.range * φ.range.index = Nat.card H := φ.range.card_mul_index
    _ = Nat.card G := hcard.symm
    _ = Nat.card φ.ker * φ.ker.index := φ.ker.card_mul_index.symm
    _ = Nat.card φ.range * Nat.card φ.ker := by rw [AddSubgroup.index_ker, mul_comm]

omit [Fintype H] in
lemma fibre_card (φ : G →+ H) (x : G) :
    (Finset.univ.filter (fun z : G => φ z = φ x)).card = Nat.card φ.ker := by
  calc
    _ = (Finset.univ.filter (fun z : G => φ z = 0)).card :=
      AddMonoidHom.card_fiber_eq_of_mem_range φ ⟨x, rfl⟩ ⟨0, map_zero φ⟩
    _ = Fintype.card φ.ker := (Fintype.card_subtype _).symm
    _ = Nat.card φ.ker := Nat.card_eq_fintype_card.symm

lemma extension_sum_on_range (φ : G →+ H) (θ : AddChar G ℂ)
    (hθ : ∀ x ∈ φ.ker, θ x = 1) (x : G) :
    (∑ χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => ∀ z : G, χ (φ z) = θ z),
      (χ (φ x))⁻¹) = (φ.range.index : ℂ) * (θ x)⁻¹ := by
  calc
    _ = ∑ _χ ∈ Finset.univ.filter
        (fun χ : AddChar H ℂ => ∀ z : G, χ (φ z) = θ z), (θ x)⁻¹ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [(Finset.mem_filter.mp hχ).2 x]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, extension_card φ θ hθ]

lemma fibre_sum (φ : G →+ H) (θ : AddChar G ℂ)
    (hθ : ∀ x ∈ φ.ker, θ x = 1) (x : G) :
    (∑ z ∈ Finset.univ.filter (fun z : G => φ z = φ x), (θ z)⁻¹) =
      (Nat.card φ.ker : ℂ) * (θ x)⁻¹ := by
  obtain ⟨χ₀, hχ₀⟩ := (extension_nonempty_iff φ θ).mpr hθ
  have hχ : ∀ z : G, χ₀ (φ z) = θ z := (Finset.mem_filter.mp hχ₀).2
  calc
    _ = ∑ _z ∈ Finset.univ.filter (fun z : G => φ z = φ x), (θ x)⁻¹ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [← hχ z, (Finset.mem_filter.mp hz).2, hχ x]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, fibre_card]

lemma extension_sum_fibre (φ : G →+ H) (θ : AddChar G ℂ)
    (hcard : Nat.card G = Nat.card H) (hθ : ∀ x ∈ φ.ker, θ x = 1) (y : H) :
    (∑ χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => ∀ x : G, χ (φ x) = θ x),
      (χ y)⁻¹) =
      ∑ x ∈ Finset.univ.filter (fun x : G => φ x = y), (θ x)⁻¹ := by
  by_cases hy : y ∈ φ.range
  · obtain ⟨x, rfl⟩ := hy
    rw [extension_sum_on_range φ θ hθ, fibre_sum φ θ hθ,
      range_index_eq_card_ker φ hcard]
  · rw [extension_sum_off_range φ θ hθ y hy]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    exact False.elim (hy ⟨x, (Finset.mem_filter.mp hx).2⟩)

/-- A sum over a finite type is independent of the chosen enumeration instance. -/
lemma sum_univ_eq {R : Type*} [AddCommMonoid R]
    (α : Type*) (i j : Fintype α) (f : α → R) :
    @Finset.sum α R _ (@Finset.univ α i) f =
      @Finset.sum α R _ (@Finset.univ α j) f := by
  have hij : i = j := Subsingleton.elim i j
  cases hij
  rfl

/-- A product over a finite type is independent of the chosen enumeration instance. -/
lemma prod_univ_eq {R : Type*} [CommMonoid R]
    (α : Type*) (i j : Fintype α) (f : α → R) :
    @Finset.prod α R _ (@Finset.univ α i) f =
      @Finset.prod α R _ (@Finset.univ α j) f := by
  have hij : i = j := Subsingleton.elim i j
  cases hij
  rfl

end SICLean.L5.OddPrimeCharacterAverageAux
