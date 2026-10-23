import SICLean.L4.PseudolatticeValues

set_option autoImplicit false

noncomputable section

namespace SICLean.L4.PseudolatticeHomothetyAux

open SICLean.L3

universe u
variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
theorem scale_mem (I J : Submodule ℤ K) (lam : K)
    (hJ : J = pseudolatticeScale lam I) (x : K) (hx : x ∈ I) :
    lam * x ∈ J := by
  rw [hJ]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

omit [NumberField K] in
theorem inverse_mem (I J : Submodule ℤ K) (lam : K) (hlam : lam ≠ 0)
    (hJ : J = pseudolatticeScale lam I) (y : K) (hy : y ∈ J) :
    lam⁻¹ * y ∈ I := by
  rw [hJ] at hy
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  change lam * x = y at hxy
  rw [← hxy]
  simpa [← mul_assoc, hlam] using hx

theorem mk_eq_iff (P : PeriodData K) (I : StablePseudolattice P)
    (x y : K) (hx : x ∈ pseudolatticePeriodPoints P I)
    (hy : y ∈ pseudolatticePeriodPoints P I) :
    pseudolatticeMk P I x hx = pseudolatticeMk P I y hy ↔ x - y ∈ I.val := by
  exact QuotientAddGroup.eq_iff_sub_mem

theorem embedding_mul (P : PeriodData K) (lam x : K) :
    pseudolatticeEmbedding P (lam * x) =
      distributionHomothety (pseudolatticeScales P lam) (pseudolatticeEmbedding P x) := by
  ext <;> simp [pseudolatticeEmbedding, distributionHomothety, pseudolatticeScales]

theorem embedding_inverse_mul (P : PeriodData K) (lam x : K) :
    pseudolatticeEmbedding P (lam⁻¹ * x) =
      distributionHomothety ((pseudolatticeScales P lam).1⁻¹,
        (pseudolatticeScales P lam).2⁻¹) (pseudolatticeEmbedding P x) := by
  ext <;> simp [pseudolatticeEmbedding, distributionHomothety, pseudolatticeScales]

end SICLean.L4.PseudolatticeHomothetyAux
