import SICLean.Inputs
import SICLean.LowDim
import SICLean.CoreGalois
import SICLean.CoreOrbit
import SICLean.CoreRankOne
import SICLean.CoreComplement

/-!
# Main theorems

The reductions below assume the hypotheses of `SICLean.Inputs`. The final theorems, without
hypotheses, are `SICLean.FinalAssembly.zaunerExistence` and `SICLean.FinalAssembly.hasRSIC`.
`#print axioms zaunerExistence_of_inputs` shows only `propext`, `Classical.choice`, and
`Quot.sound`.
-/

noncomputable section

open Matrix OpenQuantumProblem23

namespace SICLean

/-- Core reduction, rank `r` (the argument of [AFK25, Thm. 1.46]): a ghost together with a ring
endomorphism of `ℂ` that puts its overlaps on the r-SIC circle yields an r-SIC. -/
theorem hasRSIC_of_ghost_flip {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r < d)
    {G : Matrix (Fin d) (Fin d) ℂ} (hG : IsGhost d r G) {σ : ℂ →+* ℂ}
    (hσ : UnimodularFlip d r G σ) : HasRSIC d r := by
  obtain ⟨hH, hP, ht, hov⟩ := map_fiducial_of_ghost_flip hd hr hrd hG hσ
  exact hasRSIC_of_fiducial hd hr hrd hH hP ht hov

/-- Rank one: the same data yield a SIC-POVM in the sense of Open Quantum Problem 23. -/
theorem hasSICPOVM_of_ghost_flip {d : ℕ} (hd : 2 ≤ d)
    {G : Matrix (Fin d) (Fin d) ℂ} (hG : IsGhost d 1 G) {σ : ℂ →+* ℂ}
    (hσ : UnimodularFlip d 1 G σ) : HasSICPOVM d := by
  obtain ⟨hH, hP, ht, hov⟩ :=
    map_fiducial_of_ghost_flip hd (by omega) (by omega) hG hσ
  exact hasSICPOVM_of_fiducial hd hH hP (by simpa using ht) hov

/-- **Zauner existence from the inputs.** For `d ≥ 4` the hypothesis is supplied by
[RW26, Thm. 7] with [AFK25, Thm. 1.45] and [RW-rec, Prop. 7]. Dimensions 1–3 are explicit. -/
theorem zaunerExistence_of_inputs (H : ∀ d : ℕ, 4 ≤ d → GhostGaloisInput d 1) :
    ZaunerExistence := by
  intro d hd
  by_cases h4 : 4 ≤ d
  · obtain ⟨G, hG, σ, hσ⟩ := H d h4
    exact hasSICPOVM_of_ghost_flip (by omega) hG hσ
  · interval_cases d
    · exact hasSICPOVM_one
    · exact hasSICPOVM_two
    · exact hasSICPOVM_three

/-- Complement: `Π ↦ 1 - Π` turns an r-SIC into a `(d-r)`-SIC. -/
theorem hasRSIC_compl {d r : ℕ} (hr0 : 0 < r) (hrd : r < d) (h : HasRSIC d r) :
    HasRSIC d (d - r) := by
  exact hasRSIC_complement hr0 hrd h

/-- **Generalized existence from the inputs**, for parameters
`r < (d-1)/2` and `r(d-r) ∣ d²-1`. -/
theorem hasRSIC_of_inputs
    (H : ∀ d r : ℕ, 1 ≤ r → 2 * r + 1 < d → r * (d - r) ∣ d ^ 2 - 1 → GhostGaloisInput d r) :
    ∀ d r : ℕ, 1 ≤ r → 2 * r + 1 < d → r * (d - r) ∣ d ^ 2 - 1 → HasRSIC d r := by
  intro d r hr hdr hdiv
  obtain ⟨G, hG, σ, hσ⟩ := H d r hr hdr hdiv
  exact hasRSIC_of_ghost_flip (by omega) hr (by omega) hG hσ

end SICLean
