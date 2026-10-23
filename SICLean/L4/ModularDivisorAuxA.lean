import SICLean.L4.ModularPhi

set_option autoImplicit false

noncomputable section

namespace SICLean.L4.ModularDivisorAuxA

/-- A positive lower bound for the first coefficient of the cone generated
by `T` and `1`, uniform on a neighborhood of a slit-plane parameter. -/
theorem nat_pair_coercive_nhds (T₀ : ℂ) (hT₀ : T₀ ∈ Complex.slitPlane) :
    ∃ a : ℝ, 0 < a ∧ ∃ U : Set ℂ, U ∈ nhds T₀ ∧
      ∀ T ∈ U, ∀ K J : ℕ, (K : ℝ) * a ≤ ‖(K : ℂ) * T + (J : ℂ)‖ := by
  by_cases hpos : 0 < T₀.re
  · let a := T₀.re / 2
    have ha : 0 < a := half_pos hpos
    refine ⟨a, ha, {T | a < T.re}, ?_, ?_⟩
    · exact continuousAt_const.eventually_lt Complex.continuous_re.continuousAt
        (by dsimp [a]; linarith)
    · intro T hT K J
      change a < T.re at hT
      calc
        (K : ℝ) * a ≤ (K : ℝ) * T.re + (J : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hT.le (Nat.cast_nonneg K),
            (Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
        _ = ((K : ℂ) * T + (J : ℂ)).re := by simp
        _ ≤ ‖(K : ℂ) * T + (J : ℂ)‖ := Complex.re_le_norm _
  · have him : T₀.im ≠ 0 := (Complex.mem_slitPlane_iff.mp hT₀).resolve_left hpos
    let a := |T₀.im| / 2
    have ha : 0 < a := half_pos (abs_pos.mpr him)
    refine ⟨a, ha, {T | a < |T.im|}, ?_, ?_⟩
    · exact continuousAt_const.eventually_lt
        Complex.continuous_im.continuousAt.abs (by dsimp [a] at ha ⊢; linarith)
    · intro T hT K J
      change a < |T.im| at hT
      calc
        (K : ℝ) * a ≤ (K : ℝ) * |T.im| :=
          mul_le_mul_of_nonneg_left hT.le (Nat.cast_nonneg K)
        _ = |((K : ℂ) * T + (J : ℂ)).im| := by
          simp [abs_mul, abs_of_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
        _ ≤ ‖(K : ℂ) * T + (J : ℂ)‖ := Complex.abs_im_le_norm _

/-- Uniformly bounded nonnegative combinations in a slit-plane cone have
only finitely many natural-number labels. -/
theorem bounded_nat_pairs_near (T₀ : ℂ) (hT₀ : T₀ ∈ Complex.slitPlane) (R : ℝ) :
    ∃ U : Set ℂ, U ∈ nhds T₀ ∧
      {p : ℕ × ℕ | ∃ T ∈ U, ‖(p.1 : ℂ) * T + (p.2 : ℂ)‖ ≤ R}.Finite := by
  obtain ⟨a, ha, U, hU, hcoef⟩ := nat_pair_coercive_nhds T₀ hT₀
  let B := ‖T₀‖ + 1
  let V := U ∩ {T : ℂ | ‖T‖ < B}
  have hV : V ∈ nhds T₀ := Filter.inter_mem hU
    (continuousAt_id.norm.eventually_lt continuousAt_const (by dsimp [B]; linarith))
  obtain ⟨M, hM⟩ := exists_nat_gt (R / a)
  obtain ⟨N, hN⟩ := exists_nat_gt (R + (M : ℝ) * B)
  refine ⟨V, hV, ((Set.finite_lt_nat M).prod (Set.finite_lt_nat N)).subset ?_⟩
  rintro ⟨K, J⟩ ⟨T, hT, hbound⟩
  have hK : (K : ℝ) < M := by
    apply lt_of_le_of_lt ?_ hM
    exact (le_div_iff₀ ha).mpr ((hcoef T hT.1 K J).trans hbound)
  have hJnorm : (J : ℝ) ≤ R + (K : ℝ) * ‖T‖ := by
    have htri := norm_sub_le ((K : ℂ) * T + (J : ℂ)) ((K : ℂ) * T)
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_natCast] at htri
    linarith
  have hprod : (K : ℝ) * ‖T‖ ≤ (M : ℝ) * B :=
    mul_le_mul hK.le hT.2.le (norm_nonneg _) (Nat.cast_nonneg M)
  have hJ : (J : ℝ) < N := by linarith
  exact ⟨by exact_mod_cast hK, by exact_mod_cast hJ⟩

/-- Bounded windows meet only finitely many labels of either signed
affine family, uniformly in a sufficiently small parameter ball. -/
theorem affine_divisors_uniform (D : Set ℂ) (hD : IsOpen D)
    (T A B : ℂ → ℂ) (c τ₀ : ℂ) (hc : c ≠ 0) (hτ₀ : τ₀ ∈ D)
    (hT : ContinuousAt T τ₀) (hA : ContinuousAt A τ₀) (hB : ContinuousAt B τ₀)
    (hslit : T τ₀ ∈ Complex.slitPlane) (R : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ (∀ τ : ℂ, dist τ τ₀ < ρ → τ ∈ D) ∧
      {p : ℕ × ℕ | ∃ τ : ℂ, dist τ τ₀ < ρ ∧
        ‖(A τ + (p.1 : ℂ) * T τ + (p.2 : ℂ)) / c‖ ≤ R}.Finite ∧
      {p : ℕ × ℕ | ∃ τ : ℂ, dist τ τ₀ < ρ ∧
        ‖(B τ - (p.1 : ℂ) * T τ - (p.2 : ℂ)) / c‖ ≤ R}.Finite := by
  let L := ‖c‖ * R + max (‖A τ₀‖ + 1) (‖B τ₀‖ + 1)
  obtain ⟨U, hU, hfinite⟩ := bounded_nat_pairs_near (T τ₀) hslit L
  have hAnorm : {τ | ‖A τ‖ < ‖A τ₀‖ + 1} ∈ nhds τ₀ :=
    hA.norm.eventually_lt continuousAt_const (by linarith)
  have hBnorm : {τ | ‖B τ‖ < ‖B τ₀‖ + 1} ∈ nhds τ₀ :=
    hB.norm.eventually_lt continuousAt_const (by linarith)
  have hnear : {τ | τ ∈ D ∧ T τ ∈ U ∧
      ‖A τ‖ < ‖A τ₀‖ + 1 ∧ ‖B τ‖ < ‖B τ₀‖ + 1} ∈ nhds τ₀ := by
    filter_upwards [hD.mem_nhds hτ₀, hT hU, hAnorm, hBnorm] with τ hDτ hUτ hAτ hBτ
    exact ⟨hDτ, hUτ, hAτ, hBτ⟩
  obtain ⟨ρ, hρ, hρnear⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ρ, hρ, fun τ hτρ => (hρnear hτρ).1,
    hfinite.subset ?_, hfinite.subset ?_⟩
  · rintro ⟨K, J⟩ ⟨τ, hτρ, hpoint⟩
    have hnearτ := hρnear hτρ
    refine ⟨T τ, hnearτ.2.1, ?_⟩
    have hid : (K : ℂ) * T τ + (J : ℂ) =
        c * ((A τ + (K : ℂ) * T τ + (J : ℂ)) / c) - A τ := by
      field_simp
      ring
    calc
      ‖(K : ℂ) * T τ + (J : ℂ)‖ =
          ‖c * ((A τ + (K : ℂ) * T τ + (J : ℂ)) / c) - A τ‖ := congrArg norm hid
      _ ≤ ‖c * ((A τ + (K : ℂ) * T τ + (J : ℂ)) / c)‖ + ‖A τ‖ := norm_sub_le _ _
      _ = ‖c‖ * ‖(A τ + (K : ℂ) * T τ + (J : ℂ)) / c‖ + ‖A τ‖ := by rw [norm_mul]
      _ ≤ ‖c‖ * R + (‖A τ₀‖ + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hpoint (norm_nonneg c)) hnearτ.2.2.1.le
      _ ≤ L := by dsimp [L]; gcongr; exact le_max_left _ _
  · rintro ⟨K, J⟩ ⟨τ, hτρ, hpoint⟩
    have hnearτ := hρnear hτρ
    refine ⟨T τ, hnearτ.2.1, ?_⟩
    have hid : (K : ℂ) * T τ + (J : ℂ) =
        B τ - c * ((B τ - (K : ℂ) * T τ - (J : ℂ)) / c) := by
      field_simp
      ring
    calc
      ‖(K : ℂ) * T τ + (J : ℂ)‖ =
          ‖B τ - c * ((B τ - (K : ℂ) * T τ - (J : ℂ)) / c)‖ := congrArg norm hid
      _ ≤ ‖B τ‖ + ‖c * ((B τ - (K : ℂ) * T τ - (J : ℂ)) / c)‖ := norm_sub_le _ _
      _ = ‖B τ‖ + ‖c‖ * ‖(B τ - (K : ℂ) * T τ - (J : ℂ)) / c‖ := by rw [norm_mul]
      _ ≤ (‖B τ₀‖ + 1) + ‖c‖ * R :=
        add_le_add hnearτ.2.2.2.le (mul_le_mul_of_nonneg_left hpoint (norm_nonneg c))
      _ ≤ L := by dsimp [L]; linarith [le_max_right (‖A τ₀‖ + 1) (‖B τ₀‖ + 1)]

end SICLean.L4.ModularDivisorAuxA
