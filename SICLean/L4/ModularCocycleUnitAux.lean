import SICLean.L4.ModularPhi

set_option autoImplicit false
noncomputable section
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups UpperHalfPlane
namespace SICLean.L4

namespace ModularCocycleUnitAux

lemma shift_integer (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k l : ℤ) (z τ : ℂ) :
    modularPhi M m n (z + (k : ℂ) * τ + (l : ℂ)) τ =
      modularPhi M (m + k) (n + M 1 1 * k - M 1 0 * l) z τ := by
  have hk (j : ℕ) :
      modularPhiIndex M (m + k) (n + M 1 1 * k - M 1 0 * l) j =
        modularPhiIndex M m n j + l := by
    unfold modularPhiIndex
    rw [show M 1 1 * (m + k + (j : ℤ)) -
      (n + M 1 1 * k - M 1 0 * l) =
      (M 1 1 * (m + (j : ℤ)) - n) + l * M 1 0 by ring]
    exact Int.add_mul_ediv_right _ _ hM.ne'
  unfold modularPhi
  apply Finset.prod_congr rfl
  intro j hj
  simp only [modularPhiFactorPoint, modularPhiFactorInput, hk]
  congr 2
  push_cast
  ring

lemma phase_shift (q A B : ℂ) (hq : q ≠ 0) (m n k : ℤ)
    (h : q ^ m * A = q ^ n * B) :
    q ^ (m + k) * A = q ^ (n + k) * B := by
  rw [zpow_add₀ hq, zpow_add₀ hq]
  calc
    q ^ m * q ^ k * A = q ^ k * (q ^ m * A) := by ring
    _ = q ^ k * (q ^ n * B) := by rw [h]
    _ = q ^ n * q ^ k * B := by ring

lemma diagonal_nat_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (k : ℕ) (z τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hfix : etaMobius M τ = τ)
    (hphase : (e τ) ^ m * e z = (e τ) ^ n * e (z / etaDenom M τ))
    (havoid : ∀ j : ℤ, 1 - (e τ) ^ (m + j) * e z ≠ 0) :
    ∃ c : ℂ → ℂ, ContinuousAt c z ∧ c z = 1 ∧
      (fun w => modularPhi M (m + k) (n + k) w τ) =ᶠ[𝓝[≠] z]
        (fun w => c w * modularPhi M m n w τ) := by
  induction k with
  | zero =>
      refine ⟨fun _ => 1, continuousAt_const, rfl, ?_⟩
      simp
  | succ k ih =>
      obtain ⟨c, hc, hcz, heq⟩ := ih
      let A : ℂ → ℂ := fun w => 1 - (e τ) ^ (m + (k : ℤ)) * e w
      let B : ℂ → ℂ := fun w =>
        1 - (e τ) ^ (n + (k : ℤ)) * e (w / etaDenom M τ)
      have hAc : ContinuousAt A z := by dsimp [A, e]; fun_prop
      have hBc : ContinuousAt B z := by dsimp [B, e]; fun_prop
      have hAz : A z ≠ 0 := havoid k
      have hBA : B z = A z := by
        dsimp [A, B]
        rw [phase_shift (e τ) (e z) (e (z / etaDenom M τ))
          (e_ne_zero τ) m n k hphase]
      refine ⟨fun w => (B w / A w) * c w, (hBc.div hAc hAz).mul hc, ?_, ?_⟩
      · simp only [hBA, div_self hAz, hcz, mul_one]
      · have hm := modularPhi_index_m_germ M hM (m + (k : ℤ))
          (n + (k : ℤ)) z τ hτ
        have hn := modularPhi_index_n_germ M hM (m + (k : ℤ) + 1)
          (n + (k : ℤ)) z τ hτ
        rw [hfix] at hn
        filter_upwards [hm, hn, heq] with w hmw hnw heqw
        have hmk : m + (↑(k + 1) : ℤ) = m + (k : ℤ) + 1 := by omega
        have hnk : n + (↑(k + 1) : ℤ) = n + (k : ℤ) + 1 := by omega
        rw [hmk, hnk, hnw, hmw, heqw]
        dsimp [A, B]
        ring

lemma center_eq_of_germ_multiplier (f g c : ℂ → ℂ) (z : ℂ)
    (hf : ContinuousAt f z) (hg : ContinuousAt g z) (hc : ContinuousAt c z)
    (hcz : c z = 1) (heq : f =ᶠ[𝓝[≠] z] (fun w => c w * g w)) :
    f z = g z := by
  have ht : Tendsto (fun w => c w * g w) (𝓝[≠] z) (𝓝 (g z)) := by
    have hcc : ContinuousAt (fun w : ℂ => c w * g w) z := hc.mul hg
    have ht' : Tendsto (fun w : ℂ => c w * g w) (𝓝[≠] z) (𝓝 (c z * g z)) :=
      hcc.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [hcz, one_mul] using ht'
  exact tendsto_nhds_unique hf.continuousWithinAt.tendsto (ht.congr' heq.symm)

lemma diagonal_index_fixedPoint (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n k : ℤ) (z : ℂ) (τ₀ : ℝ)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (hphase : (e (τ₀ : ℂ)) ^ m * e z =
      (e (τ₀ : ℂ)) ^ n * e (z / etaDenom M (τ₀ : ℂ)))
    (havoid : ∀ j : ℤ, 1 - (e (τ₀ : ℂ)) ^ (m + j) * e z ≠ 0)
    (hL : ContinuousAt (fun w => modularPhi M (m + k) (n + k) w (τ₀ : ℂ)) z)
    (hR : ContinuousAt (fun w => modularPhi M m n w (τ₀ : ℂ)) z) :
    modularPhi M (m + k) (n + k) z (τ₀ : ℂ) =
      modularPhi M m n z (τ₀ : ℂ) := by
  have hτ : (τ₀ : ℂ) ∈ modularPhiDomain M := by
    apply real_mem_modularPhiDomain
    simpa [etaDenom] using hT
  rcases le_total 0 k with hk | hk
  · lift k to ℕ using hk
    obtain ⟨c, hc, hcz, heq⟩ := diagonal_nat_germ M hM m n k z τ₀ hτ hfix hphase havoid
    exact center_eq_of_germ_multiplier _ _ c z hL hR hc hcz heq
  · have hnonneg : 0 ≤ -k := by omega
    lift -k to ℕ using hnonneg with l hl
    have hm : m + k + (l : ℤ) = m := by omega
    have hn : n + k + (l : ℤ) = n := by omega
    have hp := phase_shift (e (τ₀ : ℂ)) (e z)
      (e (z / etaDenom M (τ₀ : ℂ))) (e_ne_zero _) m n k hphase
    have ha : ∀ j : ℤ, 1 - (e (τ₀ : ℂ)) ^ (m + k + j) * e z ≠ 0 := by
      intro j
      simpa only [add_assoc] using havoid (k + j)
    obtain ⟨c, hc, hcz, heq⟩ := diagonal_nat_germ M hM (m + k) (n + k) l
      z τ₀ hτ hfix hp ha
    rw [hm, hn] at heq
    exact (center_eq_of_germ_multiplier _ _ c z hR hL hc hcz heq).symm

lemma row_fixedPoint (M : SL(2, ℤ)) (u : Fin 2 → ℤ) (τ : ℂ)
    (hfix : etaMobius M τ = τ) (hT : etaDenom M τ ≠ 0) :
    ((Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) 0 : ℂ) * τ +
      ((Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) 1 : ℂ) =
        etaDenom M τ * ((u 0 : ℂ) * τ + (u 1 : ℂ)) := by
  have hf : (M 0 0 : ℂ) * τ + (M 0 1 : ℂ) = τ * etaDenom M τ :=
    (div_eq_iff hT).mp hfix
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  push_cast
  calc
    ((u 0 : ℂ) * (M 0 0 : ℂ) + (u 1 : ℂ) * (M 1 0 : ℂ)) * τ +
        ((u 0 : ℂ) * (M 0 1 : ℂ) + (u 1 : ℂ) * (M 1 1 : ℂ)) =
      (u 0 : ℂ) * ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) +
        (u 1 : ℂ) * etaDenom M τ := by unfold etaDenom; ring
    _ = etaDenom M τ * ((u 0 : ℂ) * τ + (u 1 : ℂ)) := by rw [hf]; ring

lemma row_second_index (M : SL(2, ℤ)) (u : Fin 2 → ℤ) :
    M 1 1 * (Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) 0 -
      M 1 0 * (Matrix.vecMul u (M : Matrix (Fin 2) (Fin 2) ℤ)) 1 = u 0 := by
  have hdet := det_coe_int M
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  calc
    M 1 1 * (u 0 * M 0 0 + u 1 * M 1 0) -
        M 1 0 * (u 0 * M 0 1 + u 1 * M 1 1) =
      u 0 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by ring
    _ = u 0 := by rw [hdet]; ring

lemma power_wrap (ε L : ℂ) (r : ℕ) (hr : 0 < r) (hε : 1 < ‖ε‖) :
    (L / ((ε ^ r)⁻¹ - 1)) / ε ^ (r - 1) =
      ε * (L / ((ε ^ r)⁻¹ - 1)) + ε * L := by
  have hεne : ε ≠ 0 := by intro h; norm_num [h] at hε
  have hp : ε ^ r ≠ 1 := by
    intro h
    have hnorm : 1 < ‖ε ^ r‖ := by simpa only [norm_pow] using one_lt_pow₀ hε hr.ne'
    norm_num [h] at hnorm
  have hden : (ε ^ r)⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (inv_ne_one.mpr hp)
  have hbalance : (L / ((ε ^ r)⁻¹ - 1)) / ε ^ r -
      L / ((ε ^ r)⁻¹ - 1) = L := by
    field_simp
  have hstep : ε * ((L / ((ε ^ r)⁻¹ - 1)) / ε ^ r) =
      (L / ((ε ^ r)⁻¹ - 1)) / ε ^ (r - 1) := by
    rw [← pow_sub_one_mul hr.ne' ε]
    field_simp
  rw [← hstep]
  linear_combination ε * hbalance

lemma cyclic_pred_eq (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    (j + r - 1) % r = if j = 0 then r - 1 else j - 1 := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [zero_add, ite_true] using
      (Nat.mod_eq_of_lt (show r - 1 < r by omega))
  · rw [if_neg hj0]
    have heq : j + r - 1 = j - 1 + r := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma prod_range_cyclic_pred (f : ℕ → ℂ) (r : ℕ) (hr : 0 < r) :
    (∏ j ∈ Finset.range r, f ((j + r - 1) % r)) =
      ∏ j ∈ Finset.range r, f j := by
  apply Finset.prod_bij (fun j _ => (j + r - 1) % r)
  · intro j hj
    exact Finset.mem_range.mpr (Nat.mod_lt _ hr)
  · intro a ha b hb hab
    rw [cyclic_pred_eq r a hr (Finset.mem_range.mp ha),
      cyclic_pred_eq r b hr (Finset.mem_range.mp hb)] at hab
    split_ifs at hab <;> simp only [Finset.mem_range] at ha hb <;> omega
  · intro b hb
    have hbr : b < r := Finset.mem_range.mp hb
    by_cases hlast : b = r - 1
    · refine ⟨0, Finset.mem_range.mpr hr, ?_⟩
      rw [cyclic_pred_eq r 0 hr hr]
      simp [hlast]
    · have hsucc : b + 1 < r := by omega
      refine ⟨b + 1, Finset.mem_range.mpr hsucc, ?_⟩
      rw [cyclic_pred_eq r (b + 1) hr hsucc]
      simp
  · intro a ha
    rfl

end ModularCocycleUnitAux
end SICLean.L4
