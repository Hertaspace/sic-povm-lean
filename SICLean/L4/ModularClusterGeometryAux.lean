import SICLean.L4.ModularDivisor

set_option autoImplicit false

/-!
# Auxiliary lemmas for `ModularClusterGeometry`

Only the two facts that do not mention the local `KernelData`/`Label`
vocabulary live here, so that this file can be imported by the
file before those definitions. The affine facts about `branchPoint` are
proved directly inside `ModularClusterGeometry.lean`.
-/

noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.ModularCluster

lemma isOpen_modularPhiDomain (M : SL(2, ℤ)) : IsOpen (modularPhiDomain M) := by
  have h : modularPhiDomain M = etaDenom M ⁻¹' Complex.slitPlane := rfl
  rw [h]
  exact Complex.isOpen_slitPlane.preimage (by unfold etaDenom; fun_prop)

lemma exists_pos_le_of_finset {α : Type*} (s : Finset α) (f : α → ℝ)
    (h : ∀ x ∈ s, 0 < f x) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ε ≤ f x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
      obtain ⟨ε, hε, hle⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      have ha_pos : 0 < f a := h a (Finset.mem_insert_self a s)
      refine ⟨min ε (f a / 2), lt_min hε (by linarith), ?_⟩
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact le_trans (min_le_right _ _) (by linarith)
      · exact le_trans (min_le_left _ _) (hle x hx)

end SICLean.L4.ModularCluster
