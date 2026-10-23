import SICLean.L2r.Convolution

/-! # Rank-r phase, coefficient, and projector definitions -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SICLean.L2r

def phaseSignExponent (d : ℕ) (p : ℤ × ℤ) : ℤ :=
  (d : ℤ) + ((d : ℤ) + 1) * (1 + p.1) * (1 + p.2)

def phase (d r : ℕ) (p : ℤ × ℤ) : ℂ :=
  (-1 : ℂ) ^ phaseSignExponent d p * xi d ^ (-(r : ℤ) * quadraticForm d r p)

/-- Includes the auxiliary ν₀=-A⁻¹; this is not the trace coefficient μ₀=r. -/
def nu (d r : ℕ) (F : Values d) (p : ℤ × ℤ) : ℂ := phase d r p / valueAt F p

def coefficient (d r : ℕ) (F : Values d) (p : ℤ × ℤ) : ℂ :=
  if IsZeroLabel d p then (r : ℂ) else nu d r F p / rootLevel d r

/-- Actual integer U=G⁻¹=diag(1,c_tw) is used inside D before reduction. -/
def ghostProjector (d r : ℕ) [Fact (Admissible d r)] (F : Values d) :
    Matrix (Fin d) (Fin d) ℂ :=
  letI : NeZero d := admissibleDimensionNeZero d r
  ((r : ℂ) / d) • (1 : Matrix (Fin d) (Fin d) ℂ) +
    ((d : ℂ) * rootLevel d r)⁻¹ •
      ∑ p : Index d,
        if p = 0 then 0 else nu d r F (lift p) • D d (twistInverseLift d r (lift p))

end SICLean.L2r
