import SICLean.L3.PseudolatticePresentation

set_option autoImplicit false

/-! Arithmetic embedding facts used only by the downstream transports. -/

noncomputable section

namespace SICLean.L4.PseudolatticeDownstreamAux

open SICLean.L3

universe u
variable {K : Type u} [Field K] [NumberField K]

theorem embeddingImage_injective (P : PeriodData K) :
    Function.Injective (pseudolatticeEmbeddingImage P) := by
  intro I J h
  ext x
  have hf : Function.Injective (pseudolatticeEmbedding P) := by
    intro a b hab
    exact P.sigma₁.injective (congrArg Prod.fst hab)
  have hmem (L : Submodule ℤ K) :
      pseudolatticeEmbedding P x ∈ pseudolatticeEmbeddingImage P L ↔ x ∈ L :=
    AddSubgroup.mem_map_iff_mem hf
  rw [← hmem I, ← hmem J, h]

theorem embedding_inverse_scale (P : PeriodData K) (lam x : K) :
    pseudolatticeEmbedding P (lam⁻¹ * x) =
      distributionHomothety
        ((pseudolatticeScales P lam).1⁻¹, (pseudolatticeScales P lam).2⁻¹)
        (pseudolatticeEmbedding P x) := by
  ext <;> simp [pseudolatticeEmbedding, pseudolatticeScales, distributionHomothety]

end SICLean.L4.PseudolatticeDownstreamAux
