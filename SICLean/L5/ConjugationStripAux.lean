import SICLean.L4.Faddeev

set_option autoImplicit false

noncomputable section

namespace SICLean.L5.ConjugationStripAux

open Complex SICLean.L4

/-- Reflection of the actual logarithmic kernel. The odd factor `w` in
the denominator contributes the minus sign, including at total-division values. -/
theorem kernel_conj_neg (b : ℝ) (z w : ℂ) :
    (starRingEnd ℂ) (kernel (b : ℂ) z w) =
      -kernel (b : ℂ) ((starRingEnd ℂ) z) (-((starRingEnd ℂ) w)) := by
  unfold kernel
  simp only [map_div₀, map_mul, ← Complex.exp_conj, ← Complex.sinh_conj,
    map_neg, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_inv₀,
    mul_neg, Complex.sinh_neg, neg_mul, neg_neg, div_neg]

end SICLean.L5.ConjugationStripAux
