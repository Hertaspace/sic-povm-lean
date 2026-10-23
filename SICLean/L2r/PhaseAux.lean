import SICLean.L2r.Convolution

set_option autoImplicit false
noncomputable section
namespace SICLean.L2r

/-- The main range is strong enough for the existing integer phase lemmas. -/
theorem phaseAux_dimension_ge_four {d r : ℕ} (h : Admissible d r) : 4 ≤ d := by
  have := h.rank_pos
  have := h.main_range
  omega

/-- The conic supplies the parity needed for changes of integer lift. -/
theorem phaseAux_parity_ell {d r : ℕ} (h : Admissible d r) :
    (2 : ℤ) ∣ ((d : ℤ) + 1) * ((d : ℤ) + (r : ℤ) * ell d r - 1) := by
  obtain ⟨t, ht⟩ := Int.two_dvd_mul_add_one (r : ℤ)
  have hc := principal_conic h
  refine ⟨(d : ℤ) * r - (r : ℤ) ^ 2 + (ell d r : ℤ) * d * r +
    (ell d r : ℤ) * r - (ell d r : ℤ) * t, ?_⟩
  linear_combination hc - (ell d r : ℤ) * ht

theorem phaseAux_parity_rank {d r : ℕ} (h : Admissible d r) :
    (2 : ℤ) ∣ ((d : ℤ) + 1) * ((r : ℤ) + 1) := by
  have he := phaseAux_parity_ell h
  have hd := Int.two_dvd_mul_add_one (d : ℤ)
  have hr := Int.two_dvd_mul_add_one (r : ℤ)
  have hexp : ((d : ℤ) + 1) * ((r : ℤ) + 1) =
      -(((d : ℤ) + 1) * ((d : ℤ) + (r : ℤ) * ell d r - 1) * ((r : ℤ) + 1)) +
      (d : ℤ) * ((d : ℤ) + 1) * ((r : ℤ) + 1) +
      (ell d r : ℤ) * ((d : ℤ) + 1) * ((r : ℤ) * ((r : ℤ) + 1)) := by ring
  rw [hexp]
  exact dvd_add (dvd_add
    (dvd_neg.mpr (dvd_mul_of_dvd_left he ((r : ℤ) + 1)))
    (dvd_mul_of_dvd_left hd ((r : ℤ) + 1)))
    (dvd_mul_of_dvd_right hr ((ell d r : ℤ) * ((d : ℤ) + 1)))

theorem phaseAux_parity_twist {d r : ℕ} (h : Admissible d r) :
    (2 : ℤ) ∣ ((d : ℤ) + 1) * (twistScalar d r + 1) := by
  have he := phaseAux_parity_ell h
  have hd := Int.two_dvd_mul_add_one (d : ℤ)
  have hn : (level d r : ℤ) = (ell d r : ℤ) + 2 := by
    have hl := level_ge_five h
    simp only [ell]
    omega
  have hexp : ((d : ℤ) + 1) * (twistScalar d r + 1) =
      (d : ℤ) * ((d : ℤ) + 1) * ((r : ℤ) + 1) -
        2 * (((d : ℤ) + 1) * r) -
      ((d : ℤ) + 1) * ((d : ℤ) + (r : ℤ) * ell d r - 1) := by
    unfold twistScalar
    rw [hn]
    ring
  rw [hexp]
  exact dvd_sub
    (dvd_sub (dvd_mul_of_dvd_left hd ((r : ℤ) + 1))
      (dvd_mul_right (2 : ℤ) (((d : ℤ) + 1) * r))) he

/-- Polynomial phases may be evaluated on any integer representative. -/
theorem phaseAux_torsionGaussian_lift (d r : ℕ) [Fact (Admissible d r)] (p : ℤ × ℤ) :
    torsionGaussian d r (label d p) = L2a.e d ((r : ℤ) * quadraticForm d r p) := by
  have : NeZero d := ⟨by
    have hd := phaseAux_dimension_ge_four (Fact.out : Admissible d r)
    omega⟩
  unfold torsionGaussian
  apply L2a.e_eq_of_dvd
  have hx : (d : ℤ) ∣ (lift (label d p)).1 - p.1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
    simp [lift, label]
  have hy : (d : ℤ) ∣ (lift (label d p)).2 - p.2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
    simp [lift, label]
  have hq : (d : ℤ) ∣ quadraticForm d r (lift (label d p)) - quadraticForm d r p := by
    have hexp : quadraticForm d r (lift (label d p)) - quadraticForm d r p =
        ((lift (label d p)).1 - p.1) * ((lift (label d p)).1 + p.1) -
          ((ell d r : ℤ) * p.2 * ((lift (label d p)).1 - p.1) +
            (ell d r : ℤ) * (lift (label d p)).1 * ((lift (label d p)).2 - p.2)) +
          ((lift (label d p)).2 - p.2) * ((lift (label d p)).2 + p.2) := by
      unfold quadraticForm
      ring
    rw [hexp]
    exact dvd_add (dvd_sub
      (dvd_mul_of_dvd_left hx ((lift (label d p)).1 + p.1))
      (dvd_add (dvd_mul_of_dvd_right hx ((ell d r : ℤ) * p.2))
        (dvd_mul_of_dvd_right hy ((ell d r : ℤ) * (lift (label d p)).1))))
      (dvd_mul_of_dvd_left hy ((lift (label d p)).2 + p.2))
  have hexp : (r : ℤ) * quadraticForm d r (lift (label d p)) -
      (r : ℤ) * quadraticForm d r p =
      (r : ℤ) * (quadraticForm d r (lift (label d p)) - quadraticForm d r p) := by ring
  rw [hexp]
  exact dvd_mul_of_dvd_right hq (r : ℤ)

end SICLean.L2r
