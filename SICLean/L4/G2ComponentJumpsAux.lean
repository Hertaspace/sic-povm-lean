import SICLean.L4.G2CombResidues
import SICLean.L4.G2StripCounting

set_option autoImplicit false

/-! Integer row coordinates and actual center values used in the component ledger. -/

noncomputable section
open Classical Complex Set
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.G2ComponentJumpsAux

open G2 G2.CombResidues

lemma sIndex_add (M : SL(2, ℤ)) (x y : ℤ × ℤ) :
    sIndex M (x + y) = sIndex M x + sIndex M y := by
  simp only [sIndex, Prod.fst_add, Prod.snd_add]
  ring

lemma sIndex_shift (M : SL(2, ℤ)) (m k : ℤ) :
    sIndex M (m, k - specialValueOrder M) =
      sIndex M (m, k) - M 1 0 * specialValueOrder M := by
  simp only [sIndex]
  ring

lemma coordinate_eq_iff (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x v : ℤ × ℤ) (j : ℤ) :
    combCoordinate M x.1 x.2 = -inverseOffset M v + (j : ℝ) * length M ↔
      sIndex M x + sIndex M v = specialValueOrder M * j := by
  rw [G2ContourChainAux.length_eq_scale_mul M hM]
  change scale M * (sIndex M x : ℝ) =
    -(scale M * (sIndex M v : ℝ)) + (j : ℝ) * (scale M * (specialValueOrder M : ℝ)) ↔ _
  constructor
  · intro h
    have hr : ((sIndex M x + sIndex M v : ℤ) : ℝ) =
        ((specialValueOrder M * j : ℤ) : ℝ) := by
      push_cast
      nlinarith [(scale_identities M hM).1]
    exact_mod_cast hr
  · intro h
    have hr : (sIndex M x : ℝ) + (sIndex M v : ℝ) =
        (specialValueOrder M : ℝ) * (j : ℝ) := by exact_mod_cast h
    linear_combination scale M * hr

lemma lattice_index (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (j : ℤ) (hx : specialValueMk M x = 0)
    (hs : sIndex M x = specialValueOrder M * j) :
    ∃ q : ℤ, x.1 = (M 0 0 - 1) * j + M 1 0 * q ∧
      x.2 = M 0 1 * j + (M 1 1 - 1) * q := by
  obtain ⟨p, q, hp, hq⟩ := G2RepellingPointValuesAux.lattice_coordinates M x
    ((QuotientAddGroup.eq_zero_iff x).mp hx)
  have hsp : sIndex M x = specialValueOrder M * p := by
    simp only [sIndex, hp, hq, specialValueOrder]
    linear_combination -p * det_coe_int M
  have hpj : p = j := by
    exact mul_left_cancel₀ (specialValueOrder_pos M hM).ne' (hsp.symm.trans hs)
  subst p
  exact ⟨q, by nlinarith [hp], by nlinarith [hq]⟩

lemma label_spec (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (j : ℤ) :
    let m := ((M 0 0 - 1) * j - v.1) % M 1 0
    let k := (specialValueOrder M * j - sIndex M v - (1 - M 1 1) * m) / M 1 0
    0 ≤ m ∧ m < M 1 0 ∧ specialValueMk M ((m, k) + v) = 0 ∧
      sIndex M (m, k) + sIndex M v = specialValueOrder M * j := by
  dsimp only
  let a := (M 0 0 - 1) * j - v.1
  let m := a % M 1 0
  let q := -(a / M 1 0)
  have hm : m = (M 0 0 - 1) * j + M 1 0 * q - v.1 := by
    have := Int.emod_add_mul_ediv a (M 1 0)
    dsimp [m, q, a] at *
    nlinarith
  have hnum : specialValueOrder M * j - sIndex M v - (1 - M 1 1) * m =
      M 1 0 * (M 0 1 * j + (M 1 1 - 1) * q - v.2) := by
    rw [hm]
    dsimp [specialValueOrder, sIndex]
    linear_combination j * det_coe_int M
  have hk : (specialValueOrder M * j - sIndex M v - (1 - M 1 1) * m) / M 1 0 =
      M 0 1 * j + (M 1 1 - 1) * q - v.2 := by
    rw [hnum, Int.mul_ediv_cancel_left _ hM.1.ne']
  change 0 ≤ m ∧ m < M 1 0 ∧ _
  refine ⟨Int.emod_nonneg _ hM.1.ne', Int.emod_lt_of_pos _ hM.1, ?_, ?_⟩
  · rw [hk]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    change ∃ x, L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) x = _
    refine ⟨(j, q), ?_⟩
    apply Prod.ext
    · have he : j * (M 0 0 - 1) + q * M 1 0 = m + v.1 := by
        linear_combination -hm
      simpa [L2r.rowAction, Matrix.sub_apply] using he
    · simp [L2r.rowAction, Matrix.sub_apply]
      ring
  · rw [hk]
    change (1 - M 1 1) * m + M 1 0 * _ + sIndex M v = _
    linear_combination -hnum

lemma label_unique (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (j m k : ℤ) (hm : 0 ≤ m) (hmc : m < M 1 0) :
    (specialValueMk M ((m, k) + v) = 0 ∧
      sIndex M (m, k) + sIndex M v = specialValueOrder M * j) ↔
    (m, k) =
      (((M 0 0 - 1) * j - v.1) % M 1 0,
        (specialValueOrder M * j - sIndex M v -
          (1 - M 1 1) * (((M 0 0 - 1) * j - v.1) % M 1 0)) / M 1 0) := by
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨q, hq, _⟩ := lattice_index M hM ((m, k) + v) j hx
      (by simpa only [sIndex_add] using hs)
    have hm' : ((M 0 0 - 1) * j - v.1) % M 1 0 = m := by
      have heq : (M 0 0 - 1) * j - v.1 = m - M 1 0 * q := by
        change m + v.1 = _ at hq
        linarith
      rw [heq, Int.sub_mul_emod_self_left, Int.emod_eq_of_lt hm hmc]
    rw [hm']
    congr 1
    have heq : specialValueOrder M * j - sIndex M v - (1 - M 1 1) * m =
        M 1 0 * k := by change (1 - M 1 1) * m + M 1 0 * k + sIndex M v = _ at hs; linarith
    rw [heq, Int.mul_ediv_cancel_left _ hM.1.ne']
  · intro h
    have hs := label_spec M hM v j
    simpa only [← h] using hs.2.2

lemma plusLift_eq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x y : ℤ × ℤ) (hxy : specialValueMk M x = specialValueMk M y) :
    SpecialValueBridge.repellingPlusLift M x = SpecialValueBridge.repellingPlusLift M y := by
  rw [← (SpecialValueBridge.repellingValues_mk M hM x).1,
    ← (SpecialValueBridge.repellingValues_mk M hM y).1, hxy]

lemma pairing_eq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x y u : ℤ × ℤ) (hxy : specialValueMk M x = specialValueMk M y) :
    specialValuePairingLift M x u = specialValuePairingLift M y u := by
  rw [← specialValuePairing_mk M hM x u, ← specialValuePairing_mk M hM y u, hxy]

lemma phiDenominator_eq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m k : ℤ) :
    phiDenominator M v m k =
      modularPhi M ((m, k) + v).1 0 (argument M ((m, k) + v) : ℂ) (repellingTau M : ℂ) := by
  rw [phiDenominator, root_eq_argument M hM, Evaluation.argument_add]
  push_cast
  rfl

lemma normalized_phi_nonzero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x ≠ 0) :
    etaMultiplier M * modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ) =
      SpecialValueBridge.repellingPlusLift M x := by
  have hmem : x ∉ specialValueLattice M := fun h => hx ((QuotientAddGroup.eq_zero_iff x).mpr h)
  simp only [SpecialValueBridge.repellingPlusLift, if_neg hmem, RepellingPointValues.repellingRaw]

lemma phi_nonzero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x ≠ 0) :
    modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ) =
      (etaMultiplier M)⁻¹ * SpecialValueBridge.repellingPlusLift M x := by
  rw [← normalized_phi_nonzero M hM x hx]
  rw [← mul_assoc, inv_mul_cancel₀ (etaMultiplier_ne_zero M hM.1), one_mul]

lemma phi_zero_index (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x = 0) (j : ℤ)
    (hs : sIndex M x = specialValueOrder M * j) :
    modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ) =
      if j < 0 then (etaMultiplier M)⁻¹ / (Real.sqrt (epsilon M) : ℂ)
      else (etaMultiplier M)⁻¹ * (Real.sqrt (epsilon M) : ℂ) := by
  have he := Evaluation.zero_class_phi_value M hM x hx 0
  simp only [add_zero, Evaluation.commonExponent, hs,
    Int.mul_ediv_cancel_left _ (specialValueOrder_pos M hM).ne', zero_sub] at he
  simpa only [show (1 ≤ -j) ↔ j < 0 by omega] using he

lemma phi_zero_sign (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x = 0) :
    modularPhi M x.1 0 (argument M x : ℂ) (repellingTau M : ℂ) =
      if sIndex M x < 0 then (etaMultiplier M)⁻¹ / (Real.sqrt (epsilon M) : ℂ)
      else (etaMultiplier M)⁻¹ * (Real.sqrt (epsilon M) : ℂ) := by
  obtain ⟨j, hj⟩ := Evaluation.zero_class_sIndex_dvd M hM x hx
  have hn := specialValueOrder_pos M hM
  have hiff : sIndex M x < 0 ↔ j < 0 := by rw [hj]; constructor <;> intro h <;> nlinarith
  simp only [hiff]
  exact phi_zero_index M hM x hx j hj

lemma phi_shift_eq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m k : ℤ)
    (h : ¬ (specialValueMk M (m, k) = 0 ∧
      0 ≤ sIndex M (m, k) ∧ sIndex M (m, k) < M 1 0 * specialValueOrder M)) :
    modularPhi M m 0 (argument M (m, k) : ℂ) (repellingTau M : ℂ) =
      modularPhi M m 0 (argument M (m, k - specialValueOrder M) : ℂ) (repellingTau M : ℂ) := by
  have hshift := (StripCounting.subtract_vertical_period M hM m k).2.1
  by_cases hx : specialValueMk M (m, k) = 0
  · have hx' := hshift.trans hx
    rw [phi_zero_sign M hM (m, k) hx, phi_zero_sign M hM (m, k - specialValueOrder M) hx',
      sIndex_shift]
    have hcn := mul_pos hM.1 (specialValueOrder_pos M hM)
    have he : (sIndex M (m, k) < 0) ↔
        sIndex M (m, k) - M 1 0 * specialValueOrder M < 0 := by
      constructor
      · intro hs; linarith
      · intro hs
        by_contra hn
        exact h ⟨hx, by omega, by omega⟩
    simp only [he]
  · rw [phi_nonzero M hM (m, k) hx,
      phi_nonzero M hM (m, k - specialValueOrder M) (by rwa [hshift]),
      plusLift_eq M hM _ _ hshift]

lemma jump_index (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (x : ℤ × ℤ) (hx : specialValueMk M x = 0)
    (hs : 0 ≤ sIndex M x) (hsc : sIndex M x < M 1 0 * specialValueOrder M) :
    ∃ j : Fin (M 1 0).toNat, sIndex M x = specialValueOrder M * (j : ℤ) := by
  obtain ⟨j, hj⟩ := Evaluation.zero_class_sIndex_dvd M hM x hx
  have hn := specialValueOrder_pos M hM
  have hj0 : 0 ≤ j := by nlinarith
  have hjc : j < M 1 0 := by nlinarith
  refine ⟨⟨j.toNat, by omega⟩, ?_⟩
  simpa only [Int.toNat_of_nonneg hj0] using hj

lemma winding_iff_center (M : SL(2, ℤ)) (_hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (x : ℝ) (hx : x ∈ guardSet M v) :
    g1CircleWinding D x ≠ 0 ↔ x ∈ D.centers := by
  constructor
  · intro hw
    by_contra hc
    apply hw
    apply G2ContourChainAux.winding_zero
    intro r hr
    exact (hD.2.2.2.2.2.2 r hr).2.2 x hx (by intro h; exact hc (h ▸ hr))
  · intro hc
    rw [G2ContourChainAux.winding_one D x hc (hD.2.2.2.2.2.2 x hc).1
      (fun r hr hxr => (hD.2.2.2.2.2.2 r hr).2.2 x hx hxr)]
    norm_num

lemma phiNumerator_shift_eq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (m k : ℤ)
    (h : ¬ (specialValueMk M (m, k) = 0 ∧
      0 ≤ sIndex M (m, k) ∧ sIndex M (m, k) < M 1 0 * specialValueOrder M)) :
    phiNumerator M m k = phiNumerator M m (k - specialValueOrder M) := by
  simp only [phiNumerator, root_eq_argument M hM]
  exact phi_shift_eq M hM m k h

lemma phiDenominator_shift_eq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (v : ℤ × ℤ) (m k : ℤ)
    (h : ¬ (specialValueMk M ((m, k) + v) = 0 ∧
      0 ≤ sIndex M ((m, k) + v) ∧
      sIndex M ((m, k) + v) < M 1 0 * specialValueOrder M)) :
    phiDenominator M v m k = phiDenominator M v m (k - specialValueOrder M) := by
  rw [phiDenominator_eq M hM, phiDenominator_eq M hM]
  have hpair : (m, k - specialValueOrder M) + v =
      (m + v.1, k + v.2 - specialValueOrder M) := by ext <;> simp <;> ring
  rw [hpair]
  exact phi_shift_eq M hM (m + v.1) (k + v.2) h

lemma rho_shift_eq (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ)
    (hn : ¬ (specialValueMk M (m, k) = 0 ∧
      0 ≤ sIndex M (m, k) ∧ sIndex M (m, k) < M 1 0 * specialValueOrder M))
    (hd : ¬ (specialValueMk M ((m, k) + v) = 0 ∧
      0 ≤ sIndex M ((m, k) + v) ∧
      sIndex M ((m, k) + v) < M 1 0 * specialValueOrder M)) :
    rho M u v m k = rho M u v m (k - specialValueOrder M) := by
  rw [rho, rho, phiNumerator_shift_eq M hM m k hn,
    phiDenominator_shift_eq M hM v m k hd,
    pairing_eq M hM (m, k - specialValueOrder M) (m, k) u
      (StripCounting.subtract_vertical_period M hM m k).2.1]

end SICLean.L4.G2ComponentJumpsAux
