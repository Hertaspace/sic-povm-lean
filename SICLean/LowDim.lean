import SICLean.Statement

/-!
# Dimensions 1, 2, 3

In dimensions 2 and 3 the witnesses are the tetrahedral and Hesse families. They and their
definitions follow google-deepmind/formal-conjectures,
`FormalConjectures/OpenQuantumProblems/23.lean`, at commit
90d18f666eb98adec4eee4d12f1d37e30b4eb204 (Copyright 2026 The Formal Conjectures Authors,
licensed under the Apache License, Version 2.0).
-/

noncomputable section

namespace OpenQuantumProblem23

/- ## Dimension 1 -/

theorem hasSICPOVM_one : HasSICPOVM 1 := by
  refine ⟨fun _ => EuclideanSpace.single 0 1, fun _ => ?_, fun i j hij => ?_⟩
  · simp [IsNormalized]
  · have : Subsingleton (Fin (1 ^ 2)) := Fin.subsingleton_one
    exact absurd (Subsingleton.elim i j) hij

/- ## Explicit witnesses -/

/-- The standard algebraic primitive cube root of unity. -/
private def ω : ℂ :=
  ((-(1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

/-- The first real amplitude used in the tetrahedral qubit SIC. -/
private def tetraA : ℝ := Real.sqrt (1 / 3)

/-- The second real amplitude used in the tetrahedral qubit SIC. -/
private def tetraB : ℝ := Real.sqrt (2 / 3)

/-- The common scale used in the Hesse qutrit SIC. -/
private def hesseS : ℝ := Real.sqrt (1 / 2)

/-- A convenient constructor for qubit state vectors. -/
private def vec2 (z₀ z₁ : ℂ) : StateVector 2 := mkStateVector ![z₀, z₁]

/-- A convenient constructor for qutrit state vectors. -/
private def vec3 (z₀ z₁ z₂ : ℂ) : StateVector 3 := mkStateVector ![z₀, z₁, z₂]

/-- The tetrahedral qubit SIC family: the same vectors as `qubitSICFamily` in
google-deepmind/formal-conjectures, re-indexed arithmetically (rather than by
constructor patterns) so that `fin_cases` reduces cleanly. -/
private def qubitSICFamily : Fin 4 → StateVector 2 := fun i =>
  if (i : ℕ) = 0 then vec2 1 0
  else vec2 (tetraA : ℝ) (((tetraB : ℝ) : ℂ) * ω ^ ((i : ℕ) - 1))

/-- The Hesse qutrit SIC family: the same vectors as `hesseFamily` in
google-deepmind/formal-conjectures, re-indexed arithmetically. Index `i` has
block `i / 3` and offset `i % 3`; block `b`, offset `t` is `√(1/2)` times
`(0, 1, -ω^t)`, `(-ω^t, 0, 1)`, `(1, -ω^t, 0)` for `b = 0, 1, 2`. -/
private def hesseFamily : Fin 9 → StateVector 3 := fun i =>
  if (i : ℕ) < 3 then
    vec3 0 (hesseS : ℝ) (-((hesseS : ℝ) : ℂ) * ω ^ (i : ℕ))
  else if (i : ℕ) < 6 then
    vec3 (-((hesseS : ℝ) : ℂ) * ω ^ ((i : ℕ) - 3)) 0 (hesseS : ℝ)
  else
    vec3 (hesseS : ℝ) (-((hesseS : ℝ) : ℂ) * ω ^ ((i : ℕ) - 6)) 0

/- ## Algebra of the cube root `ω` -/

private lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

private lemma omega_re : ω.re = -(1 : ℝ) / 2 := by
  simp [ω]

private lemma omega_im : ω.im = Real.sqrt 3 / 2 := by
  simp [ω]

private lemma omega_normSq : Complex.normSq ω = 1 := by
  rw [Complex.normSq_apply, omega_re, omega_im]
  field_simp
  nlinarith [sqrt3_sq]

private lemma star_re (z : ℂ) : (star z).re = z.re := rfl

private lemma star_im (z : ℂ) : (star z).im = -z.im := rfl

private lemma star_ofReal (x : ℝ) : star ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) :=
  Complex.conj_ofReal x

private lemma omega_two : ω ^ 2 = ω * ω := pow_two ω

private lemma star_omega : star ω = ω * ω := by
  rw [Complex.ext_iff]
  simp only [star_re, star_im, Complex.mul_re, Complex.mul_im, omega_re, omega_im]
  constructor
  · field_simp; nlinarith [sqrt3_sq]
  · field_simp; nlinarith [sqrt3_sq]

private lemma star_omega_pow : star ω = ω ^ 2 := by rw [omega_two]; exact star_omega

private lemma omega_star : ω * star ω = 1 := by
  rw [Complex.ext_iff]
  simp only [star_re, star_im, Complex.mul_re, Complex.mul_im, omega_re, omega_im,
    Complex.one_re, Complex.one_im]
  constructor
  · field_simp; nlinarith [sqrt3_sq]
  · field_simp; ring

private lemma omega_cube : ω * ω * ω = 1 := by
  rw [← star_omega, mul_comm]
  exact omega_star

private lemma omega_add_omega_sq : ω + ω * ω = -1 := by
  rw [Complex.ext_iff]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    omega_re, omega_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
  constructor
  · field_simp; nlinarith [sqrt3_sq]
  · field_simp; linarith

private lemma star_omega_two : star (ω ^ 2) = ω := by
  rw [omega_two, star_mul, star_omega]
  calc ω * ω * (ω * ω) = (ω * ω * ω) * ω := by ring
    _ = 1 * ω := by rw [omega_cube]
    _ = ω := by ring

private lemma omega_two_normSq : Complex.normSq (ω ^ 2) = 1 := by
  rw [omega_two, Complex.normSq_mul, omega_normSq]; norm_num

/-- Workhorse: decide `normSq z = c` by proving the complex identity `z * star z = ↑c`. -/
private lemma normSq_eq {z : ℂ} {c : ℝ} (h : z * star z = ((c : ℝ) : ℂ)) :
    Complex.normSq z = c := by
  have hn := Complex.normSq_eq_conj_mul_self (z := z)
  simp only [starRingEnd_apply] at hn
  rw [mul_comm (star z) z, h] at hn
  exact Complex.ofReal_inj.mp hn

/- ## Overlap squares of explicit vectors -/

private lemma overlapSq_vec2 (a₀ a₁ b₀ b₁ : ℂ) :
    overlapSq (vec2 a₀ a₁) (vec2 b₀ b₁) =
      Complex.normSq (star a₀ * b₀ + star a₁ * b₁) := by
  simp [overlapSq, vec2, mkStateVector, Fin.sum_univ_two]

private lemma overlapSq_vec3 (a₀ a₁ a₂ b₀ b₁ b₂ : ℂ) :
    overlapSq (vec3 a₀ a₁ a₂) (vec3 b₀ b₁ b₂) =
      Complex.normSq (star a₀ * b₀ + star a₁ * b₁ + star a₂ * b₂) := by
  simp [overlapSq, vec3, mkStateVector, Fin.sum_univ_three]

private lemma omega_cube_pow : ω ^ 3 = 1 := by
  rw [pow_three, ← mul_assoc]; exact omega_cube

private lemma omega_pow_succ_three (n : ℕ) : ω ^ (n + 3) = ω ^ n := by
  rw [pow_add, omega_cube_pow, mul_one]

private lemma omega_pow_four : ω ^ 4 = ω := by
  show ω ^ (3 + 1) = ω
  rw [pow_add, omega_cube_pow, one_mul, pow_one]

private lemma omega_pow_five : ω ^ 5 = ω ^ 2 := by
  show ω ^ (3 + 2) = ω ^ 2
  rw [pow_add, omega_cube_pow, one_mul]

private lemma omega_pow_six : ω ^ 6 = 1 := by
  show ω ^ (3 + 3) = 1
  rw [pow_add, omega_cube_pow, one_mul]

private lemma omega_pow_twelve : ω ^ 12 = 1 := by
  show ω ^ (6 + 6) = 1
  rw [pow_add, omega_pow_six, one_mul]

/- ## Dimension 2: the tetrahedral family -/

private lemma sicOverlapSq_two : sicOverlapSq 2 = 1 / 3 := by
  simp [sicOverlapSq]; norm_num

private lemma tetraA_sq : ((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ) = ((1 / 3 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, tetraA, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3)]

private lemma tetraB_sq : ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) = ((2 / 3 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, tetraB, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3)]

private lemma omega_norm : ‖ω‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply, omega_re, omega_im]
  have h : (-1 / 2 : ℝ) * (-1 / 2 : ℝ) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 := by
    field_simp; nlinarith [sqrt3_sq]
  rw [h]
  simp

private lemma qubitSICFamily_normalized (i : Fin 4) :
    IsNormalized (qubitSICFamily i) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have omega2_norm : ‖ω ^ 2‖ = 1 := by rw [norm_pow, omega_norm]; ring
  fin_cases i <;>
    simp [IsNormalized, qubitSICFamily, vec2, mkStateVector,
      EuclideanSpace.norm_eq, Fin.sum_univ_two, tetraA, tetraB,
      omega_norm, omega2_norm, abs_of_pos sqrt2_pos, abs_of_pos sqrt3_pos]
  all_goals (try (field_simp; linarith [h2, h3]))

/-- Master identity for the off-diagonal tetrahedral overlaps:
`(A + B ω) (A + B ω̄) = A² - A B + B²` because `ω + ω̄ = -1` and `ω ω̄ = 1`, with
`A = ↑tetraA * ↑tetraA = 1/3`, `B = ↑tetraB * ↑tetraB = 2/3`. -/
private lemma tetra_master :
    (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
        + ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) * ω)
      * (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
        + ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) * ω ^ 2)
      = ((1 / 3 : ℝ) : ℂ) := by
  have hw2 : ω ^ 2 = star ω := by rw [omega_two, star_omega]
  have h1 : ω + star ω = -1 := by rw [star_omega]; exact omega_add_omega_sq
  rw [hw2]
  have hkey :
      (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
          + ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) * ω)
        * (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
          + ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) * star ω)
      = (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ))
          * (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ))
        - (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ))
          * (((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ))
        + (((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ))
          * (((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)) := by
    linear_combination
      (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
        * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)) * h1
      + (((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ))
        * (((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)) * omega_star
  rw [hkey, tetraA_sq, tetraB_sq]
  push_cast
  norm_num

set_option maxHeartbeats 1000000 in
private lemma qubitSICFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily := by
  intro i j hij
  rw [sicOverlapSq_two]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [qubitSICFamily, overlapSq_vec2]
      first
      | rw [tetraA, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3)]
        norm_num
      | refine normSq_eq ?_
        rw [← one_div (3 : ℝ)]
        simp only [starRingEnd_apply, star_add, star_mul, star_pow,
          star_ofReal, star_omega_pow]
        -- The star-normalization sends `star ω` to `ω ^ 2`, so the six off-diagonal
        -- goals present as `(a² + b² ω^k) (a² + b² ω^(2k))` for `k = 1, 2, 4, 5`;
        -- reduce each to `tetra_master` by the identities `ω³ = ω⁶ = ω¹² = 1`,
        -- `ω⁴ = ω`, `ω⁵ = ω²`.
        first
        | linear_combination tetra_master
        | linear_combination tetra_master
            + ((((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
                * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) * ω)
              - ((tetraB : ℝ) : ℂ) ^ 2 * ((tetraB : ℝ) : ℂ) ^ 2) * omega_cube_pow
            + ((tetraB : ℝ) : ℂ) ^ 2 * ((tetraB : ℝ) : ℂ) ^ 2 * omega_pow_six
        | linear_combination tetra_master
            + (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
              * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)) * omega_pow_four
            + (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
              * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) * ω ^ 2) * omega_pow_six
            + (((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)
              * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)) * omega_pow_twelve
            - (((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)
              * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)) * omega_cube_pow
        | linear_combination tetra_master
            + (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
              * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)) * omega_pow_five
            + (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
              * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)) * omega_pow_four
            + (((tetraA : ℝ) : ℂ) * ((tetraA : ℝ) : ℂ)
              * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) * ω ^ 4) * omega_pow_six
            + (((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ)
              * ((tetraB : ℝ) : ℂ) * ((tetraB : ℝ) : ℂ) * ω ^ 3) * omega_pow_twelve

theorem hasSICPOVM_two : HasSICPOVM 2 :=
  ⟨qubitSICFamily, qubitSICFamily_normalized, qubitSICFamily_pairwise⟩

/- ## Dimension 3: the Hesse family -/

private lemma sicOverlapSq_three : sicOverlapSq 3 = 1 / 4 := by
  simp [sicOverlapSq]; norm_num

private lemma hesseS_sq : ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, hesseS, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- `S² = 1/4` for `S = ↑hesseS * ↑hesseS = 1/2`. -/
private lemma hesseS_four :
    (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ))
      * (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) = ((1 / 4 : ℝ) : ℂ) := by
  rw [hesseS_sq]
  push_cast
  norm_num

/-- Master identity for the same-block Hesse overlaps:
`(S + S ω) (S + S ω²) = S S` because `(1 + ω)(1 + ω²) = 1`. -/
private lemma hesse_master :
    (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
        + ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ) * ω)
      * (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
        + ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ) * ω ^ 2)
      = (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ))
        * (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) := by
  linear_combination
    ((((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ))
      * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) * omega_add_omega_sq
    + ((((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ))
      * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) * omega_cube_pow

private lemma hesseFamily_normalized (i : Fin 9) :
    IsNormalized (hesseFamily i) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqrt2_inv_sq : (Real.sqrt 2)⁻¹ ^ 2 = (2 : ℝ)⁻¹ := by rw [inv_pow, h2]
  have sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have omega2_norm : ‖ω ^ 2‖ = 1 := by rw [norm_pow, omega_norm]; ring
  fin_cases i <;>
    simp [IsNormalized, hesseFamily, vec3, mkStateVector,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, hesseS,
      omega_norm, omega2_norm, abs_of_pos sqrt2_pos]
  all_goals (try (field_simp; linarith [h2]))

set_option maxHeartbeats 40000000 in
/-- Same-block Hesse overlaps present (after star-normalization) as
`(S + S ω^k) (S + S ω^(2k)) = 1/4` for `S = ↑hesseS * ↑hesseS` and `k ∈ {1, 2, 4, 5}`;
cross-block ones reduce to `1/2 * (1/2 * normSq ω^k) = 1/4`. -/
private lemma hesseFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 3) hesseFamily := by
  intro i j hij
  rw [sicOverlapSq_three]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [hesseFamily, overlapSq_vec3]
      -- A `norm_num` that merely simplifies without closing counts as success for
      -- `first`, poisoning the goal state for later alternatives, so every
      -- alternative except the last must either close or fail to match;
      -- hence the fully specified rewrites come first.
      first
      | rw [hesseS, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2), omega_normSq]
        norm_num
      | rw [hesseS, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2),
          omega_two_normSq]
        norm_num
      | rw [hesseS, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num
      | refine normSq_eq ?_
        rw [← one_div (4 : ℝ)]
        simp only [starRingEnd_apply, star_add, star_mul, star_pow,
          star_ofReal, star_omega_pow]
        -- Reduce `(S + S ω^k) (S + S ω^(2k))` to `hesse_master` by
        -- `ω³ = ω⁶ = ω¹² = 1`, `ω⁴ = ω`, `ω⁵ = ω²`.
        first
        | linear_combination hesse_master + hesseS_four
        | linear_combination hesse_master + hesseS_four
            + ((((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ) * ω)
              - (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
                * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ))) * omega_cube_pow
            + (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) * omega_pow_six
        | linear_combination hesse_master + hesseS_four
            + (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) * omega_pow_four
            + (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ) * ω ^ 2) * omega_pow_six
            + (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) * omega_pow_twelve
            - (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) * omega_cube_pow
        | linear_combination hesse_master + hesseS_four
            + (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) * omega_pow_five
            + (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)) * omega_pow_four
            + (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ) * ω ^ 4) * omega_pow_six
            + (((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ)
              * ((hesseS : ℝ) : ℂ) * ((hesseS : ℝ) : ℂ) * ω ^ 3) * omega_pow_twelve

theorem hasSICPOVM_three : HasSICPOVM 3 :=
  ⟨hesseFamily, hesseFamily_normalized, hesseFamily_pairwise⟩

end OpenQuantumProblem23
