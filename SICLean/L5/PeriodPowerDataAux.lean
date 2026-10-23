import SICLean.L4.PseudolatticeMatrixValues

set_option autoImplicit false

/-!
Elementary lattice and quotient lemmas for positive powers of a period. All maps in the
quotient transport preserve the representative in the field.
-/

noncomputable section

namespace SICLean.L5.PeriodPowerDataAux

open L3

universe u
variable {K : Type u} [Field K] [NumberField K]

theorem epsilon_mul_mem (P : PeriodData K) (I : StablePseudolattice P)
    {x : K} (hx : x ∈ I.val) : P.epsilon * x ∈ I.val := by
  rw [← I.property.2]
  exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩

theorem epsilon_inv_scale (P : PeriodData K) (I : StablePseudolattice P) :
    pseudolatticeScale P.epsilon⁻¹ I.val = I.val := by
  calc
    pseudolatticeScale P.epsilon⁻¹ I.val =
        pseudolatticeScale P.epsilon⁻¹ (pseudolatticeScale P.epsilon I.val) :=
      congrArg (pseudolatticeScale P.epsilon⁻¹) I.property.2.symm
    _ = I.val := (pseudolatticeScale_inv _ P.epsilon_ne_zero I.val).1

theorem epsilon_inv_mul_mem (P : PeriodData K) (I : StablePseudolattice P)
    {x : K} (hx : x ∈ I.val) : P.epsilon⁻¹ * x ∈ I.val := by
  rw [← epsilon_inv_scale P I]
  exact (pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩

theorem epsilon_pow_scale (P : PeriodData K) (I : StablePseudolattice P) (n : ℕ) :
    pseudolatticeScale (P.epsilon ^ n) I.val = I.val := by
  induction n with
  | zero => simp [pseudolatticeScale_one]
  | succ n ih =>
    rw [pow_succ, pseudolatticeScale_mul, I.property.2, ih]

omit [NumberField K] in
theorem pow_sub_one_mul_mem (I : Submodule ℤ K) (a : K)
    (ha : ∀ y ∈ I, a * y ∈ I) (x : K) (hx : (a - 1) * x ∈ I) (n : ℕ) :
    (a ^ n - 1) * x ∈ I := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := I.add_mem (ha _ ih) hx
    convert h using 1
    ring

omit [NumberField K] in
theorem quotient_transport_mk (I H J : AddSubgroup K) (h : H = J)
    (x : K) (hx : x ∈ H) :
    (Eq.ndrec (motive := fun (J : AddSubgroup K) =>
      (H ⧸ I.addSubgroupOf H) ≃+ (J ⧸ I.addSubgroupOf J)) (AddEquiv.refl _) h)
        (QuotientAddGroup.mk (⟨x, hx⟩ : H)) =
      QuotientAddGroup.mk (⟨x, h.le hx⟩ : J) := by
  cases h
  rfl

end SICLean.L5.PeriodPowerDataAux
