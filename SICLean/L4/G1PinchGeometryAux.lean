import SICLean.L4.G1RealInterface

set_option autoImplicit false

/-! Real-coordinate identities for the existing G1 divisor branches. -/

noncomputable section

open Complex
open scoped MatrixGroups

namespace SICLean.L4.G1PinchGeometryAux

lemma etaDenom_ofReal (M : SL(2, ℤ)) (τ : ℝ) :
    etaDenom M (τ : ℂ) = (g1T M τ : ℂ) := by
  simp [etaDenom, g1T]

lemma polePoint_ofReal (M : SL(2, ℤ)) (τ : ℝ) (r n : ℤ) (K J : ℕ) :
    modularPhiPolePoint M r n (τ : ℂ) K J =
      ((((n : ℝ) - ((r : ℝ) - 1) * g1T M τ +
        (K : ℝ) * g1T M τ + (J : ℝ)) / (M 1 0 : ℝ) : ℝ) : ℂ) := by
  simp [modularPhiPolePoint, etaDenom_ofReal]

lemma polePoint_succ_ofReal (M : SL(2, ℤ)) (τ : ℝ) (m n : ℤ) (K J : ℕ) :
    modularPhiPolePoint M (m + 1) n (τ : ℂ) K J =
      ((((n : ℝ) - (m : ℝ) * g1T M τ +
        (K : ℝ) * g1T M τ + (J : ℝ)) / (M 1 0 : ℝ) : ℝ) : ℂ) := by
  rw [polePoint_ofReal]
  push_cast
  ring

lemma zeroPoint_ofReal (M : SL(2, ℤ)) (τ : ℝ) (r n : ℤ) (K J : ℕ) :
    modularPhiZeroPoint M r n (τ : ℂ) K J =
      ((((n : ℝ) - 1 - (r : ℝ) * g1T M τ -
        (K : ℝ) * g1T M τ - (J : ℝ)) / (M 1 0 : ℝ) : ℝ) : ℂ) := by
  simp [modularPhiZeroPoint, etaDenom_ofReal]

lemma disjoint_iff_no_collision (M : SL(2, ℤ)) (τ y : ℝ) (n p m : ℤ) :
    Disjoint (g1NumeratorPoles M τ n m) (g1InversePoles M τ y n p m) ↔
      ∀ K J K' J' : ℕ,
        (K, J) ∈ modularPhiPoleLabels M (m + 1) n →
        (K', J') ∈ modularPhiZeroLabels M (m + p) n →
        modularPhiPolePoint M (m + 1) n (τ : ℂ) K J ≠
          modularPhiZeroPoint M (m + p) n (τ : ℂ) K' J' - (y : ℂ) := by
  constructor
  · intro hd K J K' J' hP hZ heq
    let x : ℝ := ((n : ℝ) - (m : ℝ) * g1T M τ +
      (K : ℝ) * g1T M τ + (J : ℝ)) / (M 1 0 : ℝ)
    have hx : (x : ℂ) = modularPhiPolePoint M (m + 1) n (τ : ℂ) K J :=
      (polePoint_succ_ofReal M τ m n K J).symm
    exact Set.disjoint_left.mp hd ⟨K, J, hP, hx⟩ ⟨K', J', hZ, hx.trans heq⟩
  · intro hn
    rw [Set.disjoint_left]
    rintro x ⟨K, J, hP, hxP⟩ ⟨K', J', hZ, hxZ⟩
    exact hn K J K' J' hP hZ (hxP.symm.trans hxZ)

end SICLean.L4.G1PinchGeometryAux
