import SICLean.Galois.Reciprocity
import SICLean.L2c.Main
import SICLean.L2r.Main
import SICLean.L2rc.Main

set_option autoImplicit false

/-!
# [RW-rec, Prop. 7] supplies the original and rank-r inputs B

`Prop7Input` carries [RW-rec, Prop. 7] as an explicit hypothesis, which the final assembly
discharges. The coordinate
maps are those already defined, so the analytic, algebraic, and unit-circle
values agree. Zero-class algebraicity is read off the explicit real radicals
and does not use [RW-rec, Prop. 7].
-/

noncomputable section

namespace SICLean.Galois

/-- Original version with the chosen σ visible in the conclusion. -/
theorem unitCircleInput_original_of_sigma {M : ℕ} (F : L2a.Values M)
    (hAlg : ∀ x, IsAlgebraic ℚ (F x)) (σ : QbarAut)
    (h7 : Prop7Conclusion (fun x => algebraicLift (F x) (hAlg x)) σ) :
    ∃ T : ℂ ≃ₐ[ℚ] ℂ, Extends σ T ∧
      L2a.RWUnitCircleInput M F T.toAlgHom.toRingHom := by
  obtain ⟨T, hT, hnorm⟩ := unitCircle_of_sigma F hAlg σ h7
  exact ⟨T, hT, ⟨fun h hh => hnorm h hh⟩⟩

/-- Rank-r version with exactly the same restriction equation on ℚbar. -/
theorem unitCircleInput_rank_of_sigma {d r : ℕ} [Fact (L2r.Admissible d r)]
    (F : L2r.Values d) (hAlg : ∀ x, IsAlgebraic ℚ (F x)) (σ : QbarAut)
    (h7 : Prop7Conclusion (fun x => algebraicLift (F x) (hAlg x)) σ) :
    ∃ T : ℂ ≃ₐ[ℚ] ℂ, Extends σ T ∧
      L2r.RWUnitCircleInput d r F T.toAlgHom.toRingHom := by
  obtain ⟨T, hT, hnorm⟩ := unitCircle_of_sigma F hAlg σ h7
  exact ⟨T, hT, ⟨fun h hh => hnorm h hh⟩⟩

theorem unitCircleInput_original {M : ℕ} (F : L2a.Values M)
    (h : Prop7Input F) : ∃ τ : ℂ →+* ℂ, L2a.RWUnitCircleInput M F τ := by
  obtain ⟨τ, hτ⟩ := unitCircle_of_prop7 F h
  exact ⟨τ, ⟨fun x hx => hτ x hx⟩⟩

theorem unitCircleInput_rank {d r : ℕ} [Fact (L2r.Admissible d r)]
    (F : L2r.Values d) (h : Prop7Input F) :
    ∃ τ : ℂ →+* ℂ, L2r.RWUnitCircleInput d r F τ := by
  obtain ⟨τ, hτ⟩ := unitCircle_of_prop7 F h
  exact ⟨τ, ⟨fun x hx => hτ x hx⟩⟩

/-- Directly matches the unit-circle conjunct of zaunerExistence_of_theorem2. -/
theorem unitCircleInput_L2c {M : ℕ} [Fact (4 ≤ M)]
    (Fplus : L2c.RWGroup M → ℂ) (h : Prop7Input Fplus) :
    ∃ τ : ℂ →+* ℂ,
      L2a.RWUnitCircleInput M (L2b.restrict M (L2c.smithValues M Fplus)) τ := by
  obtain ⟨τ, hτ⟩ := unitCircle_of_prop7 Fplus h
  refine ⟨τ, ⟨fun p hp => ?_⟩⟩
  refine hτ _ ?_
  intro hz
  have h1 : L2b.iota M p = 0 := (L2c.fromSmith_eq_zero M _).mp hz
  exact hp (L2b.iota_injective M (by simp [h1]))

/-- The finite-quantum-dilogarithm rank-r interface. -/
theorem unitCircleInput_L2r {d r : ℕ} [Fact (L2r.Admissible d r)]
    (E : L2r.G d r → ℂ) (h : Prop7Input E) :
    ∃ τ : ℂ →+* ℂ, L2r.RWUnitCircleInput d r (L2r.restrict d r E) τ := by
  obtain ⟨τ, hτ⟩ := unitCircle_of_prop7 E h
  refine ⟨τ, ⟨fun p hp => ?_⟩⟩
  refine hτ _ ?_
  intro h0
  exact hp (L2r.iota_injective d r (by simp [h0]))

/-- Directly matches the B used by ghostGaloisInput_of_theorem2_rank. -/
theorem unitCircleInput_L2rc {d r : ℕ} [Fact (L2r.Admissible d r)]
    (Fplus : L2rc.RWGroup d r → ℂ) (h : Prop7Input Fplus) :
    ∃ τ : ℂ →+* ℂ, L2r.RWUnitCircleInput d r
      (L2r.restrict d r (L2rc.concreteValues d r Fplus)) τ := by
  obtain ⟨τ, hτ⟩ := unitCircle_of_prop7 Fplus h
  refine ⟨τ, ⟨fun p hp => ?_⟩⟩
  refine hτ _ ?_
  intro h0
  have hi : L2r.iota d r p = 0 :=
    (L2r.rwIndexMap_bijective d r).1 (by rw [h0, map_zero])
  exact hp (L2r.iota_injective d r (by simpa using hi))

/-- Every Galois image of a root of unity has norm 1. No phase-fixing
hypothesis occurs in any of the preceding interfaces. -/
theorem norm_map_rootOfUnity (τ : ℂ →+* ℂ) (ζ : ℂ) (n : ℕ)
    (hn : 0 < n) (hζ : ζ ^ n = 1) : ‖τ ζ‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one ?_ hn.ne'
  rw [← map_pow, hζ, map_one]

/-- A rational square has only the two possible square roots after mapping.
This does not choose a positive sign for an arbitrary Galois image. -/
theorem map_rational_sqrt (τ : ℂ →+* ℂ) (a : ℚ) (s : ℂ)
    (hs : s ^ 2 = (a : ℂ)) : τ s = s ∨ τ s = -s := by
  have hsq : (τ s) ^ 2 = s ^ 2 := by
    rw [← map_pow, hs]
    simp
  have hzero : (τ s - s) * (τ s + s) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hzero with h | h
  · left; linear_combination h
  · right; linear_combination h

/-! ### Algebraicity of the explicitly defined real square roots

Every zero-class value below is a real square root of an expression built from
natural-number casts, the field operations, and further real square roots.
The next three lemmas record the corresponding closure steps in `ℝ` and the
transport of the result to `ℂ` along `algebraMap ℝ ℂ`. -/

private lemma isAlgebraic_sqrt_real {r : ℝ} (hr : IsAlgebraic ℚ r) :
    IsAlgebraic ℚ (Real.sqrt r) := by
  rcases le_or_gt 0 r with h | h
  · refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
    rwa [Real.sq_sqrt h]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt h)]
    exact isAlgebraic_zero

private lemma isAlgebraic_sqrt_real_complex {r : ℝ} (hr : IsAlgebraic ℚ r) :
    IsAlgebraic ℚ ((Real.sqrt r : ℝ) : ℂ) :=
  (isAlgebraic_sqrt_real hr).algebraMap

private lemma isAlgebraic_originCore (N ε : ℝ) (hN : IsAlgebraic ℚ N)
    (hε : IsAlgebraic ℚ ε) :
    IsAlgebraic ℚ ((N + 2 + ε * Real.sqrt (N ^ 2 + 4 * N)) / 2) := by
  have h2 : IsAlgebraic ℚ ((2 : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) 2
  have h4 : IsAlgebraic ℚ ((4 : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) 4
  have hs : IsAlgebraic ℚ (Real.sqrt (N ^ 2 + 4 * N)) :=
    isAlgebraic_sqrt_real ((hN.pow 2).add (h4.mul hN))
  rw [div_eq_mul_inv]
  exact ((hN.add h2).add (hε.mul hs)).mul h2.inv

/-- Zero-class values are algebraic, without a unit-circle claim at zero. -/
theorem isAlgebraic_sqrtEpsilon (M : ℕ) :
    IsAlgebraic ℚ (L2a.sqrtEpsilon M) := by
  have hM : IsAlgebraic ℚ ((M : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) M
  have h1 : IsAlgebraic ℚ ((M : ℝ) - 1) :=
    hM.sub (isAlgebraic_one (R := ℚ) (A := ℝ))
  have h4 : IsAlgebraic ℚ ((4 : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) 4
  have h2 : IsAlgebraic ℚ ((2 : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) 2
  have heps : IsAlgebraic ℚ (L2a.epsilon M) := by
    have h2' : IsAlgebraic ℚ (((M : ℝ) - 1) ^ 2 - 4) := (h1.pow 2).sub h4
    have h3 : IsAlgebraic ℚ (Real.sqrt (((M : ℝ) - 1) ^ 2 - 4)) :=
      isAlgebraic_sqrt_real h2'
    have hc : IsAlgebraic ℚ (((M : ℝ) - 1 + Real.sqrt (((M : ℝ) - 1) ^ 2 - 4)) / 2) := by
      rw [div_eq_mul_inv]
      exact (h1.add h3).mul h2.inv
    simpa [L2a.epsilon] using hc
  simpa [L2a.sqrtEpsilon] using isAlgebraic_sqrt_real_complex heps

theorem isAlgebraic_originPlus (M : ℕ) : IsAlgebraic ℚ (L2c.originPlus M) := by
  have hN : IsAlgebraic ℚ ((L2b.groupOrder M : ℝ)) :=
    isAlgebraic_natCast (R := ℚ) (A := ℝ) (L2b.groupOrder M)
  have hcore : IsAlgebraic ℚ (((L2b.groupOrder M : ℝ) + 2 +
      Real.sqrt ((L2b.groupOrder M : ℝ) ^ 2 + 4 * (L2b.groupOrder M : ℝ))) / 2) := by
    have h := isAlgebraic_originCore ((L2b.groupOrder M : ℝ)) 1 hN
      (isAlgebraic_one (R := ℚ) (A := ℝ))
    simpa using h
  simpa [L2c.originPlus] using isAlgebraic_sqrt_real_complex hcore

theorem isAlgebraic_originMinus (M : ℕ) : IsAlgebraic ℚ (L2c.originMinus M) := by
  have hN : IsAlgebraic ℚ ((L2b.groupOrder M : ℝ)) :=
    isAlgebraic_natCast (R := ℚ) (A := ℝ) (L2b.groupOrder M)
  have hcore : IsAlgebraic ℚ (((L2b.groupOrder M : ℝ) + 2 -
      Real.sqrt ((L2b.groupOrder M : ℝ) ^ 2 + 4 * (L2b.groupOrder M : ℝ))) / 2) := by
    have h := isAlgebraic_originCore ((L2b.groupOrder M : ℝ)) (-1) hN
      ((isAlgebraic_one (R := ℚ) (A := ℝ)).neg : IsAlgebraic ℚ (-1 : ℝ))
    simpa [sub_eq_add_neg] using h
  simpa [L2c.originMinus] using isAlgebraic_sqrt_real_complex hcore

theorem isAlgebraic_originValue_rank (d r : ℕ) :
    IsAlgebraic ℚ (L2r.originValue d r) := by
  have hd : IsAlgebraic ℚ ((d : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) d
  have hr : IsAlgebraic ℚ ((r : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) r
  have hell : IsAlgebraic ℚ ((L2r.ell d r : ℝ)) :=
    isAlgebraic_natCast (R := ℚ) (A := ℝ) (L2r.ell d r)
  have h4 : IsAlgebraic ℚ ((4 : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) 4
  have h2 : IsAlgebraic ℚ ((2 : ℝ)) := isAlgebraic_natCast (R := ℚ) (A := ℝ) 2
  have hunit : IsAlgebraic ℚ (L2r.unit d r) := by
    have hs : IsAlgebraic ℚ (Real.sqrt ((L2r.ell d r : ℝ) ^ 2 - 4)) :=
      isAlgebraic_sqrt_real ((hell.pow 2).sub h4)
    have hc : IsAlgebraic ℚ
        (((L2r.ell d r : ℝ) + Real.sqrt ((L2r.ell d r : ℝ) ^ 2 - 4)) / 2) := by
      rw [div_eq_mul_inv]
      exact (hell.add hs).mul h2.inv
    simpa [L2r.unit] using hc
  have heta : IsAlgebraic ℚ (L2r.eta d r) := by
    have hdiv : IsAlgebraic ℚ ((r : ℝ) / L2r.unit d r) := by
      rw [div_eq_mul_inv]
      exact hr.mul hunit.inv
    have hinner : IsAlgebraic ℚ ((d : ℝ) - r - (r : ℝ) / L2r.unit d r) :=
      (hd.sub hr).sub hdiv
    have := hunit.mul (hinner.pow 2)
    simpa [L2r.eta] using this
  simpa [L2r.originValue] using isAlgebraic_sqrt_real_complex heta

theorem isAlgebraic_originPlus_rank (d r : ℕ) :
    IsAlgebraic ℚ (L2rc.originPlus d r) := by
  have hN : IsAlgebraic ℚ ((L2r.groupOrder d r : ℝ)) :=
    isAlgebraic_natCast (R := ℚ) (A := ℝ) (L2r.groupOrder d r)
  have hcore : IsAlgebraic ℚ (((L2r.groupOrder d r : ℝ) + 2 +
      Real.sqrt ((L2r.groupOrder d r : ℝ) ^ 2 + 4 * (L2r.groupOrder d r : ℝ))) / 2) := by
    have h := isAlgebraic_originCore ((L2r.groupOrder d r : ℝ)) 1 hN
      (isAlgebraic_one (R := ℚ) (A := ℝ))
    simpa using h
  simpa [L2rc.originPlus] using isAlgebraic_sqrt_real_complex hcore

theorem isAlgebraic_originMinus_rank (d r : ℕ) :
    IsAlgebraic ℚ (L2rc.originMinus d r) := by
  have hN : IsAlgebraic ℚ ((L2r.groupOrder d r : ℝ)) :=
    isAlgebraic_natCast (R := ℚ) (A := ℝ) (L2r.groupOrder d r)
  have hcore : IsAlgebraic ℚ (((L2r.groupOrder d r : ℝ) + 2 -
      Real.sqrt ((L2r.groupOrder d r : ℝ) ^ 2 + 4 * (L2r.groupOrder d r : ℝ))) / 2) := by
    have h := isAlgebraic_originCore ((L2r.groupOrder d r : ℝ)) (-1) hN
      ((isAlgebraic_one (R := ℚ) (A := ℝ)).neg : IsAlgebraic ℚ (-1 : ℝ))
    simpa [sub_eq_add_neg] using h
  simpa [L2rc.originMinus] using isAlgebraic_sqrt_real_complex hcore

end SICLean.Galois

-- These are checks, not extra assumptions.
#check @SICLean.L2a.map_denominator_eq_or_neg
#check @SICLean.L2a.map_theta_norm
#check @SICLean.L2r.ghostProof_map_rootLevel_eq_or_neg
#check @SICLean.L2r.ghostProof_map_phase_norm
#check @SICLean.Galois.unitCircleInput_L2c
#check @SICLean.Galois.unitCircleInput_L2r
#check @SICLean.Galois.unitCircleInput_L2rc
#print SICLean.Galois.unitCircleInput_original_of_sigma
#print SICLean.Galois.unitCircleInput_rank_of_sigma
