import SICLean.L4.SpecialValueReflectionAux

set_option autoImplicit false

/-!
# The reflection identities (3)--(5) of [RW26]

Sources: [RW26, p. 3, p. 6, p. 12, Prop. 1], and the explicit reflection substitution. The
pairing has the positive sign of [RW26].

Reflection first uses the existing punctured-germ identity, then the
joint regularity supplies both centers. The statement
with raw μΦ excludes Λ; the quotient statement handles zero separately.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4

/-- The alternating integer form in [RW26, (3)] row vectors. -/
def specialValueOmega (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

/-- Literal [RW26, (3)] Gaussian before descent, [RW26, p. 3]. -/
def specialValueGaussianLift (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℂ :=
  (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) *
    e ((specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u : ℂ) /
      (2 * (specialValueOrder M : ℂ)))

/-- Literal positive-sign [RW26, (3)] pairing, independent of polarization. -/
def specialValuePairingLift (M : SL(2, ℤ)) (u v : ℤ × ℤ) : ℂ :=
  e ((specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u - u) v : ℂ) /
    (specialValueOrder M : ℂ))

/-!
## Elementary computations for the two finite symbols

The descent of [RW26, (3)] needs the integer algebra of the quadratic
refinement: the sign `(-1)^(u₁+u₂+u₁u₂)` together with `e(ω(uM,u)/2N)`.
We write the product as one exponential phase. This keeps every
intermediate step integral.
-/

/-- The Gaussian exponent as a single phase; the sign is absorbed exactly. -/
private def specialValueGaussianPhase (M : SL(2, ℤ)) (u : ℤ × ℤ) : ℂ :=
  (specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u : ℂ) /
      (2 * (specialValueOrder M : ℂ)) + ((u.1 + u.2 + u.1 * u.2 : ℤ) : ℂ) / 2

private lemma e_add_three (a b c : ℂ) : e (a + b + c) = e a * e b * e c := by
  rw [e_add', e_add', mul_assoc]

/-- Equal exponentials when the integer numerators differ by a multiple of `N`. -/
private lemma e_div_eq_of_int_sub (N : ℂ) (hN : N ≠ 0) {x y : ℤ}
    (h : ∃ k : ℤ, ((x : ℂ) - (y : ℂ)) = N * (k : ℂ)) :
    e ((x : ℂ) / N) = e ((y : ℂ) / N) := by
  obtain ⟨k, hk⟩ := h
  have harg : (x : ℂ) / N = (y : ℂ) / N + (k : ℂ) := by
    field_simp
    linear_combination hk
  rw [harg, e_add', e_intCast, mul_one]

private lemma order_cast_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (specialValueOrder M : ℂ) ≠ 0 := by
  have h := specialValueOrder_pos M hM
  exact_mod_cast ne_of_gt h

private lemma two_order_cast_ne_zero (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    (2 * (specialValueOrder M : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (order_cast_ne_zero M hM)

lemma specialValueGaussianLift_eq_exp (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    specialValueGaussianLift M u = e (specialValueGaussianPhase M u) := by
  unfold specialValueGaussianLift specialValueGaussianPhase
  rw [← e_half_int, ← e_add']
  ring

/-- Integer form of the periodicity exponent identity. -/
private lemma gaussian_int_step (M : SL(2, ℤ)) (u v w : ℤ × ℤ)
    (hv : v = L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w) :
    specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (u + v)) (u + v) +
      specialValueOrder M * ((u + v).1 + (u + v).2 + (u + v).1 * (u + v).2)
    = specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u +
      specialValueOrder M * (u.1 + u.2 + u.1 * u.2) +
      2 * specialValueOrder M * (u.2 * v.1 - specialValueOmega u w) +
      specialValueOrder M * (v.1 + v.2 + v.1 * v.2 -
        specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w) w) := by
  subst hv
  set v : ℤ × ℤ := L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w with hvdef
  have hE2 : specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (u + v)) (u + v) -
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u =
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) v) v +
        2 * specialValueOmega (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u) v -
        specialValueOrder M * specialValueOmega u v := by
    simp [specialValueOmega, L2r.rowAction, specialValueOrder, Matrix.sub_apply,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  have hMv : specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) v) v =
      -(specialValueOrder M) *
        specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w) w := by
    have happ : L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) v =
        L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
          (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w) := by
      rw [hvdef]
      exact rowAction_apply_sub_one (M : Matrix (Fin 2) (Fin 2) ℤ) w
    rw [happ, hvdef]
    have halt := alt_rowAction_rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
      (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w) w
    simp only [specialValueOmega] at halt ⊢
    rw [halt, det_sub_one]
  have hC : specialValueOmega (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u) v =
      -(specialValueOrder M) * specialValueOmega u w := by
    rw [hvdef]
    have halt := alt_rowAction_rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u w
    simp only [specialValueOmega] at halt ⊢
    rw [halt, det_sub_one]
  have hq : ((u + v).1 + (u + v).2 + (u + v).1 * (u + v).2) - (u.1 + u.2 + u.1 * u.2) =
      (v.1 + v.2 + v.1 * v.2) + (u.1 * v.2 + u.2 * v.1) := by
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  simp only [specialValueOmega] at hE2 hMv hC hq ⊢
  linear_combination hE2 + hMv + 2 * hC + (specialValueOrder M : ℤ) * hq

/-- The phase form of the periodicity step. -/
private lemma gaussian_phase_step (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v w : ℤ × ℤ)
    (hv : v = L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w) :
    specialValueGaussianPhase M (u + v) = specialValueGaussianPhase M u +
      ((u.2 * v.1 - specialValueOmega u w : ℤ) : ℂ) +
      (((v.1 + v.2 + v.1 * v.2 -
        specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w) w : ℤ)) : ℂ) / 2 := by
  have hN := order_cast_ne_zero M hM
  have h2N := two_order_cast_ne_zero M hM
  have hkey := gaussian_int_step M u v w hv
  have hcast : ((specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (u + v))
        (u + v) : ℤ) : ℂ) +
        (specialValueOrder M : ℂ) * (((u + v).1 + (u + v).2 +
          (u + v).1 * (u + v).2 : ℤ) : ℂ)
      = ((specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u : ℤ) : ℂ) +
        (specialValueOrder M : ℂ) * ((u.1 + u.2 + u.1 * u.2 : ℤ) : ℂ) +
        2 * (specialValueOrder M : ℂ) * ((u.2 * v.1 - specialValueOmega u w : ℤ) : ℂ) +
        (specialValueOrder M : ℂ) * ((v.1 + v.2 + v.1 * v.2 -
          specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w) w : ℤ) : ℂ) := by
    exact_mod_cast hkey
  unfold specialValueGaussianPhase
  field_simp
  linear_combination hcast

/-- The Gaussian is trivial on the lattice, and periodic for the same reason. -/
private lemma gaussian_lattice_periodic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hv : v ∈ specialValueLattice M) :
    specialValueGaussianLift M (u + v) = specialValueGaussianLift M u := by
  rw [specialValueLattice, L2r.rowLattice] at hv
  rw [AddMonoidHom.mem_range] at hv
  obtain ⟨w, hw⟩ := hv
  have hw' : L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w = v := hw
  rw [← hw', specialValueGaussianLift_eq_exp, specialValueGaussianLift_eq_exp,
    gaussian_phase_step M hM u _ w rfl]
  have hmm : Even ((L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w).1 +
      (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w).2 +
      (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w).1 *
      (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) w).2 -
      specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) w) w) := by
    have hdet := det_coe_int M
    have hkey := even_parity_key ((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
      ((M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
      ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1) w.1 w.2 (by simpa [Matrix.det_fin_two] using hdet)
    simpa [specialValueOmega, L2r.rowAction, Matrix.sub_apply, Matrix.one_apply,
      mul_comm, mul_left_comm, mul_assoc] using hkey
  rw [e_add_three, e_intCast, e_half_int, hmm.neg_one_zpow]
  ring



private lemma omega_add_fst (x y z : ℤ × ℤ) :
    specialValueOmega (x + y) z = specialValueOmega x z + specialValueOmega y z := by
  simp only [specialValueOmega, Prod.fst_add, Prod.snd_add]
  ring

private lemma omega_add_snd (x y z : ℤ × ℤ) :
    specialValueOmega x (y + z) = specialValueOmega x y + specialValueOmega x z := by
  simp only [specialValueOmega, Prod.fst_add, Prod.snd_add]
  ring

private lemma omega_mem_lattice (M : SL(2, ℤ)) (x y : ℤ × ℤ) :
    specialValueOmega (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) x)
        (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) y) =
      -(specialValueOrder M) * specialValueOmega x y := by
  have halt := alt_rowAction_rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) x y
  simp only [specialValueOmega] at halt ⊢
  rw [halt, det_sub_one]

private lemma omega_sub_one_sq (M : SL(2, ℤ)) (α v : ℤ × ℤ) :
    specialValueOmega
        (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
          (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) α)) v =
      (specialValueOrder M) * specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) α) v := by
  rw [reflAux_rowAction_sub_one_sq]
  simp only [specialValueOmega, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring


/-- Periodicity of the positive-sign pairing in both variables. -/
private lemma pairing_lattice_periodic (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v a b : ℤ × ℤ) (ha : a ∈ specialValueLattice M) (hb : b ∈ specialValueLattice M) :
    specialValuePairingLift M (u + a) (v + b) = specialValuePairingLift M u v := by
  rw [specialValueLattice, L2r.rowLattice] at ha hb
  rw [AddMonoidHom.mem_range] at ha hb
  obtain ⟨α, hα⟩ := ha
  obtain ⟨β, hβ⟩ := hb
  have hα' : L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) α = a := hα
  have hβ' : L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) β = b := hβ
  rw [← hα', ← hβ']
  unfold specialValuePairingLift
  rw [← rowAction_sub_one_apply M (u + L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) α),
    ← rowAction_sub_one_apply M u]
  have hsplit1 : L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
      (u + L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) α) =
      L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) u +
      L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1)
        (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) α) := by
    ext <;> simp [L2r.rowAction] <;> ring
  rw [hsplit1, omega_add_fst, omega_add_snd, omega_add_snd]
  rw [omega_mem_lattice M u β, omega_sub_one_sq M α v,
    omega_mem_lattice M (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) α) β]
  apply e_div_eq_of_int_sub (specialValueOrder M : ℂ) (order_cast_ne_zero M hM)
  refine ⟨-specialValueOmega u β +
    specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) α) v -
    specialValueOmega (L2r.rowAction ((M : Matrix (Fin 2) (Fin 2) ℤ) - 1) α) β, ?_⟩
  push_cast
  ring


/-- The algebraic core of the reflection phase. All hypotheses are the
concrete relations satisfied by `τ`, `ε`, the fixed point quadratic and the
special argument; no analytic input is used. -/
private lemma phase_algebra (a b c d r s N A τ ε z : ℂ)
    (hN : N = a + d - 2)
    (hε : ε = c * τ + d)
    (hchar : ε ^ 2 - (a + d) * ε + 1 = 0)
    (hquad : c * τ ^ 2 + (d - a) * τ - b = 0)
    (hA : A = r * s * (a - d) + c * s ^ 2 - b * r ^ 2)
    (hz : z * (1 - ε) = ε * (r * τ + s))
    (hε1 : 1 - ε ≠ 0) (hε0 : ε ≠ 0) (hNe : N ≠ 0) :
    c * z ^ 2 / ε + 2 * r * z + r ^ 2 * τ = A / N - r * s := by
  have hz1 : z = ε * (r * τ + s) / (1 - ε) := by
    rw [eq_div_iff hε1]
    linear_combination hz
  have hF : c * (r * τ + s) ^ 2 + 2 * r * (r * τ + s) * (1 - ε) +
      N * r ^ 2 * τ - A + N * r * s = 0 := by
    subst hN
    subst hε
    subst hA
    linear_combination -(r ^ 2) * hquad
  have hsq : (1 - ε) ^ 2 = N * ε := by
    subst hN
    linear_combination hchar
  have hz2 : z ^ 2 = ε * (r * τ + s) ^ 2 / N := by
    have h := congrArg (fun t => t * t) hz
    have h2 : z ^ 2 * (1 - ε) ^ 2 = ε ^ 2 * (r * τ + s) ^ 2 := by
      linear_combination h
    rw [hsq] at h2
    rw [eq_div_iff hNe]
    have h3 : z ^ 2 * N * ε = ε * (r * τ + s) ^ 2 * ε := by linear_combination h2
    exact mul_right_cancel₀ hε0 h3
  have hD : c * z ^ 2 / ε + 2 * r * z + r ^ 2 * τ = A / N - r * s +
      (c * (r * τ + s) ^ 2 + 2 * r * ε * (r * τ + s) * N / (1 - ε) +
        N * r ^ 2 * τ - A + N * r * s) / N := by
    rw [hz2, hz1]
    field_simp
    ring
  have hF2 : c * (r * τ + s) ^ 2 + 2 * r * ε * (r * τ + s) * N / (1 - ε) +
      N * r ^ 2 * τ - A + N * r * s = 0 := by
    have h1 : (1 - ε) = N * ε / (1 - ε) := by
      rw [eq_div_iff hε1]
      linear_combination hsq
    rw [h1] at hF
    linear_combination hF
  rw [hD, hF2]
  ring

/-- Descent of the concrete Gaussian; its proof field is only well-definedness. -/
def specialValueGaussian (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    SpecialValueGroup M → ℂ :=
  Quotient.lift (specialValueGaussianLift M) (by
    intro a b hab
    have hba : b - a ∈ specialValueLattice M := by
      have hab' : QuotientAddGroup.leftRel (specialValueLattice M) a b := hab
      rw [QuotientAddGroup.leftRel_apply] at hab'
      rw [sub_eq_add_neg, show b + -a = -a + b by abel]
      exact hab'
    have h := gaussian_lattice_periodic M hM a (b - a) hba
    rw [show a + (b - a) = b by abel] at h
    exact h.symm)

/-- Descent of the concrete two-variable pairing. -/
def specialValuePairing (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    SpecialValueGroup M → SpecialValueGroup M → ℂ :=
  Quotient.lift (fun u => Quotient.lift (specialValuePairingLift M u) (by
    intro v w hvw
    have h : w - v ∈ specialValueLattice M := by
      have hvw' : QuotientAddGroup.leftRel (specialValueLattice M) v w := hvw
      rw [QuotientAddGroup.leftRel_apply] at hvw'
      rw [sub_eq_add_neg, show w + -v = -v + w by abel]
      exact hvw'
    have h0 : (0 : ℤ × ℤ) ∈ specialValueLattice M := zero_mem _
    have hp := pairing_lattice_periodic M hM u v 0 (w - v) h0 h
    simpa using hp.symm)) (by
    intro a b hab
    have hba : b - a ∈ specialValueLattice M := by
      have hab' : QuotientAddGroup.leftRel (specialValueLattice M) a b := hab
      rw [QuotientAddGroup.leftRel_apply] at hab'
      rw [sub_eq_add_neg, show b + -a = -a + b by abel]
      exact hab'
    funext x
    induction x using Quotient.inductionOn with
    | h c =>
      simp only [Quotient.lift_mk]
      have h0 : (0 : ℤ × ℤ) ∈ specialValueLattice M := zero_mem _
      have hp := pairing_lattice_periodic M hM a c (b - a) 0 hba h0
      rw [show a + (b - a) = b by abel] at hp
      simpa using hp.symm)

/-- [RW26, p. 3, (3)]. -/
theorem specialValueGaussianLift_ne_zero (M : SL(2, ℤ)) (u : ℤ × ℤ) :
    specialValueGaussianLift M u ≠ 0 := by
  unfold specialValueGaussianLift
  exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (e_ne_zero _)

/--
[RW26, p. 3, (3)].
-/
theorem specialValueGaussianLift_zero (M : SL(2, ℤ)) :
    specialValueGaussianLift M 0 = 1 := by
  simp [specialValueGaussianLift, specialValueOmega, e]

/--
[RW26, p. 3] polarization and row generators.
-/
theorem specialValueGaussianLift_periodic (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u v : ℤ × ℤ) (hv : v ∈ specialValueLattice M) :
    specialValueGaussianLift M (u + v) = specialValueGaussianLift M u := by
  exact gaussian_lattice_periodic M hM u v hv

/--
Both variables descend with the positive [RW26] sign. [RW26, p. 3, (3)] group/polarization argument.
-/
theorem specialValuePairingLift_periodic (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u v a b : ℤ × ℤ)
    (ha : a ∈ specialValueLattice M) (hb : b ∈ specialValueLattice M) :
    specialValuePairingLift M (u + a) (v + b) = specialValuePairingLift M u v := by
  exact pairing_lattice_periodic M hM u v a b ha hb

/--
Representative formula of [RW26, p. 3, (3)].
-/
theorem specialValueGaussian_mk (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) :
    specialValueGaussian M hM (specialValueMk M u) = specialValueGaussianLift M u := by
  simp [specialValueGaussian, specialValueMk, Quotient.lift_mk]

/--
Two-representative formula of [RW26, p. 3, (3)].
-/
theorem specialValuePairing_mk (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) :
    specialValuePairing M hM (specialValueMk M u) (specialValueMk M v) =
      specialValuePairingLift M u v := by
  simp [specialValuePairing, specialValueMk, Quotient.lift_mk]

/--
The index exchange from Prop. 1 to (5), after regularity and
nonzero shift factors. [RW26, p. 6, p. 12, Prop. 1]. Not asserted at zero-class crossings.
-/
theorem specialValue_reflection_index (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    modularPhi M (1 - u.1) 1 (-specialValueArgument M u) (specialValueTau M : ℂ) =
      modularPhi M (-u.1) 0 (specialValueArgument M (-u)) (specialValueTau M : ℂ) := by
  have hnu : -u ∉ specialValueLattice M := by
    intro h
    exact hu (by simpa using neg_mem h)
  have hargneg : specialValueArgument M (-u) = -specialValueArgument M u := by
    simp only [specialValueArgument, modularPhiSpecialArgument, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Prod.fst_neg, Prod.snd_neg,
      Int.cast_neg]
    ring
  have hT : 0 < (etaDenom M (specialValueTau M : ℂ)).re := by
    rw [specialValue_etaDenom, Complex.ofReal_re]
    exact lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)
  have hfix := specialValueTau_fixedPoint M hM
  have hεne : (specialValueEpsilon M : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < specialValueEpsilon M :=
      lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)
    exact_mod_cast ne_of_gt h
  have hεne1 : (specialValueEpsilon M : ℂ) ≠ 1 := by
    have h : (1 : ℝ) < specialValueEpsilon M := specialValueEpsilon_gt_one M hM
    exact_mod_cast ne_of_gt h
  have hden : ((specialValueEpsilon M : ℂ)⁻¹ - 1) ≠ 0 := by
    intro h
    have h1 : (specialValueEpsilon M : ℂ)⁻¹ = 1 := by linear_combination h
    have h2 : (specialValueEpsilon M : ℂ) = 1 := by
      calc (specialValueEpsilon M : ℂ) = ((specialValueEpsilon M : ℂ)⁻¹)⁻¹ := (inv_inv _).symm
        _ = (1 : ℂ)⁻¹ := by rw [h1]
        _ = 1 := inv_one
    exact hεne1 h2
  have hz : specialValueArgument M u * ((specialValueEpsilon M : ℂ)⁻¹ - 1)
      = (u.1 : ℂ) * (specialValueTau M : ℂ) + (u.2 : ℂ) := by
    simp only [specialValueArgument, modularPhiSpecialArgument, specialValue_etaDenom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val']
    field_simp
  have hphase : (e (specialValueTau M : ℂ)) ^ ((1 - u.1) : ℤ) * e (-specialValueArgument M u) =
      (e (specialValueTau M : ℂ)) ^ (1 : ℤ) *
        e ((-specialValueArgument M u) / etaDenom M (specialValueTau M : ℂ)) := by
    have hA : (e (specialValueTau M : ℂ)) ^ ((1 - u.1) : ℤ) =
        e ((((1 - u.1 : ℤ)) : ℂ) * (specialValueTau M : ℂ)) := by rw [e_int_mul]
    have hC : (e (specialValueTau M : ℂ)) ^ (1 : ℤ) =
        e (((1 : ℤ) : ℂ) * (specialValueTau M : ℂ)) := by rw [e_int_mul]
    rw [hA, hC, ← e_add', ← e_add', specialValue_etaDenom]
    have hz2 : specialValueArgument M u * (1 - (specialValueEpsilon M : ℂ))
        = (specialValueEpsilon M : ℂ) *
            ((u.1 : ℂ) * (specialValueTau M : ℂ) + (u.2 : ℂ)) := by
      have h := congrArg (fun t => t * (specialValueEpsilon M : ℂ)) hz
      rw [mul_assoc] at h
      have h2 : ((specialValueEpsilon M : ℂ)⁻¹ - 1) * (specialValueEpsilon M : ℂ) =
          1 - (specialValueEpsilon M : ℂ) := by
        field_simp
      rw [h2, mul_comm ((u.1 : ℂ) * (specialValueTau M : ℂ) + (u.2 : ℂ))
        (specialValueEpsilon M : ℂ)] at h
      exact h
    have hexp : ((((1 - u.1 : ℤ)) : ℂ) * (specialValueTau M : ℂ) + (-specialValueArgument M u))
        = (((1 : ℤ) : ℂ) * (specialValueTau M : ℂ) +
            (-specialValueArgument M u) / (specialValueEpsilon M : ℂ)) + (u.2 : ℂ) := by
      have hdiv : (-specialValueArgument M u) / (specialValueEpsilon M : ℂ)
          = ((((1 - u.1 : ℤ)) : ℂ) * (specialValueTau M : ℂ) + (-specialValueArgument M u)) -
            (((1 : ℤ) : ℂ) * (specialValueTau M : ℂ)) - (u.2 : ℂ) := by
        rw [div_eq_iff hεne]
        push_cast
        linear_combination -hz2
      rw [hdiv]
      ring
    rw [hexp, e_add', e_intCast, mul_one]
  have havoid : ∀ j : ℤ, 1 - (e (specialValueTau M : ℂ)) ^ ((1 - u.1) + j) *
      e (-specialValueArgument M u) ≠ 0 := by
    intro j hj
    have hA : (e (specialValueTau M : ℂ)) ^ ((1 - u.1) + j) *
        e (-specialValueArgument M u) = 1 := by linear_combination -hj
    have hz1 : e (((((1 - u.1) + j : ℤ)) : ℂ) * (specialValueTau M : ℂ) +
        (-specialValueArgument M u)) = 1 := by
      rw [e_add', ← e_int_mul]
      exact hA
    obtain ⟨l, hl⟩ := e_eq_one_iff_int hz1
    have hpseudo : -specialValueArgument M u ∈ modularPhiPseudoLattice (specialValueTau M : ℂ) := by
      refine ⟨-((1 - u.1) + j), l, ?_⟩
      simp only [Int.cast_neg]
      linear_combination hl
    have hargpseudo : specialValueArgument M u ∈ modularPhiPseudoLattice (specialValueTau M : ℂ) := by
      obtain ⟨k, l, hkl⟩ := hpseudo
      refine ⟨-k, -l, ?_⟩
      push_cast
      linear_combination -hkl
    exact hu ((specialValueArgument_mem_lattice_iff M hM u).mp hargpseudo)
  have hL : ContinuousAt (fun w => modularPhi M ((1 - u.1) + (-1)) (1 + (-1)) w
      (specialValueTau M : ℂ)) (-specialValueArgument M u) := by
    have hidx1 : ((1 - u.1) + (-1)) = -u.1 := by ring
    have hidx2 : ((1 : ℤ) + (-1)) = 0 := by ring
    rw [hidx1, hidx2]
    have hreg := (specialValuePhi_joint_regular M hM (-u) hnu 0).1
    rw [hargneg] at hreg
    have hidx : (-u).1 + 0 = -u.1 := by simp
    rw [hidx] at hreg
    have h := hreg.continuousAt
    have hmap : ContinuousAt (fun w : ℂ => (w, (specialValueTau M : ℂ)))
        (-specialValueArgument M u) := by fun_prop
    have hcomp := ContinuousAt.comp (f := fun w : ℂ => (w, (specialValueTau M : ℂ))) h hmap
    simpa [Function.comp_def] using hcomp
  have hR : ContinuousAt (fun w => modularPhi M (1 - u.1) 1 w (specialValueTau M : ℂ))
      (-specialValueArgument M u) := by
    have hreg := (specialValuePhi_joint_regular M hM (-u) hnu 1).1
    rw [hargneg] at hreg
    have hidx : (-u).1 + 1 = 1 - u.1 := by
      simp only [Prod.fst_neg]
      ring
    rw [hidx] at hreg
    have h := hreg.continuousAt
    have hmap : ContinuousAt (fun w : ℂ => (w, (specialValueTau M : ℂ)))
        (-specialValueArgument M u) := by fun_prop
    have hcomp := ContinuousAt.comp (f := fun w : ℂ => (w, (specialValueTau M : ℂ))) h hmap
    simpa [Function.comp_def] using hcomp
  have hdiag := modularPhi_diagonal_index_fixedPoint M hM.1 (1 - u.1) 1 (-1)
    (-specialValueArgument M u) (specialValueTau M) hfix hT hphase havoid hL hR
  simp only [show ((1 - u.1) + (-1)) = -u.1 from by ring,
    show ((1 : ℤ) + (-1)) = 0 from by ring] at hdiag
  rw [hargneg]
  exact hdiag.symm

/--
Exact phase simplification, not an approximate phase match. [RW26, p. 6, p. 3, (3), Prop. 1].
-/
theorem specialValue_reflection_phase (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) (u : ℤ × ℤ) :
    (-1 : ℂ) ^ u.1 * e (modularReflectionPolynomial M u.1 0
      (specialValueArgument M u) (specialValueTau M : ℂ)) =
      (specialValueGaussianLift M u)⁻¹ := by
  set τ : ℂ := (specialValueTau M : ℂ) with hτdef
  set ε : ℂ := (specialValueEpsilon M : ℂ) with hεdef
  set N : ℂ := (specialValueOrder M : ℂ) with hNdef
  set z : ℂ := specialValueArgument M u with hzdef
  set r : ℂ := (u.1 : ℂ) with hrdef
  set s : ℂ := (u.2 : ℂ) with hsdef
  set A : ℂ := ((specialValueOmega (L2r.rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) u) u : ℤ) : ℂ)
    with hAdef
  have hεne : ε ≠ 0 := by
    rw [hεdef]
    have h : (0 : ℝ) < specialValueEpsilon M :=
      lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)
    exact_mod_cast ne_of_gt h
  have hεne1 : 1 - ε ≠ 0 := by
    have hgt : (1 : ℂ) ≠ ε := by
      rw [hεdef]
      intro hc
      have hc' : (1 : ℝ) = specialValueEpsilon M := by exact_mod_cast hc
      linarith [specialValueEpsilon_gt_one M hM]
    exact sub_ne_zero.mpr hgt
  have hNne : N ≠ 0 := by
    rw [hNdef]
    have h := specialValueOrder_pos M hM
    exact_mod_cast ne_of_gt h
  have hNad : N = (M 0 0 : ℂ) + (M 1 1 : ℂ) - 2 := by
    rw [hNdef]
    simp [specialValueOrder]
  have hεlin : ε = (M 1 0 : ℂ) * τ + (M 1 1 : ℂ) := by
    rw [hεdef, hτdef]
    simp [specialValueEpsilon]
  have hfix : etaMobius M (specialValueTau M : ℂ) = (specialValueTau M : ℂ) :=
    specialValueTau_fixedPoint M hM
  have hquad : (M 1 0 : ℂ) * τ ^ 2 + ((M 1 1 : ℂ) - (M 0 0 : ℂ)) * τ - (M 0 1 : ℂ) = 0 := by
    have hden : etaDenom M (specialValueTau M : ℂ) ≠ 0 := by
      rw [specialValue_etaDenom]
      exact hεne
    have hεd : etaDenom M (specialValueTau M : ℂ) = ε := by
      rw [specialValue_etaDenom, hεdef]
    have h := congrArg (fun t => t * etaDenom M (specialValueTau M : ℂ)) hfix
    rw [etaMobius, div_mul_cancel₀ _ hden, hεd] at h
    rw [← hτdef] at h
    linear_combination -h - τ * hεlin
  have hchar : ε ^ 2 - ((M 0 0 : ℂ) + (M 1 1 : ℂ)) * ε + 1 = 0 := by
    rw [hεdef]
    have h := congrArg (fun t : ℝ => (t : ℂ)) (specialValueEpsilon_characteristic M hM)
    push_cast at h
    have hNad2 : (specialValueOrder M : ℂ) + 2 = (M 0 0 : ℂ) + (M 1 1 : ℂ) := by
      simp [specialValueOrder]
    rw [hNad2] at h
    exact h
  have hdivne : ε⁻¹ - 1 ≠ 0 := by
    rw [show ε⁻¹ - 1 = (1 - ε) / ε by field_simp]
    exact div_ne_zero hεne1 hεne
  have hz0 : z * (ε⁻¹ - 1) = r * τ + s := by
    rw [hzdef, hτdef, hrdef, hsdef]
    simp only [specialValueArgument, modularPhiSpecialArgument, specialValue_etaDenom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Prod.fst, Prod.snd]
    exact div_mul_cancel₀ _ hdivne
  have hz : z * (1 - ε) = ε * (r * τ + s) := by
    have hmul : ε * (ε⁻¹ - 1) = 1 - ε := by field_simp
    calc z * (1 - ε) = z * (ε * (ε⁻¹ - 1)) := by rw [hmul]
      _ = ε * (z * (ε⁻¹ - 1)) := by ring
      _ = ε * (r * τ + s) := by rw [hz0]
  have hAeq : A = r * s * ((M 0 0 : ℂ) - (M 1 1 : ℂ)) + (M 1 0 : ℂ) * s ^ 2 -
      (M 0 1 : ℂ) * r ^ 2 := by
    rw [hAdef, hrdef, hsdef]
    simp only [specialValueOmega, L2r.rowAction]
    push_cast
    ring
  have halg := phase_algebra (M 0 0 : ℂ) (M 0 1 : ℂ) (M 1 0 : ℂ) (M 1 1 : ℂ) r s N A τ ε z
    hNad hεlin hchar hquad hAeq hz hεne1 hεne hNne
  have hpseudo : z * (ε⁻¹ - 1) = r * τ + s := hz0
  have hpoly : modularReflectionPolynomial M u.1 0 z τ =
      -(A / (2 * N)) + (((u.1 * u.2 - u.2 : ℤ)) : ℂ) / 2 := by
    have hη : etaMobius M (specialValueTau M : ℂ) = τ := by rw [hfix, hτdef]
    have hεd : etaDenom M (specialValueTau M : ℂ) = ε := by rw [specialValue_etaDenom, hεdef]
    have hsh : modularReflectionPolynomial M u.1 0 z τ =
        -(1 / 2) * ((M 1 0 : ℂ) * z ^ 2 / ε + (2 * r - 1 + ε⁻¹) * z + (r ^ 2 - r) * τ) := by
      unfold modularReflectionPolynomial modularBernoulliTwo
      rw [hη, hεd]
      push_cast
      simp only [div_eq_mul_inv]
      ring
    rw [hsh]
    have hsplit : (M 1 0 : ℂ) * z ^ 2 / ε + (2 * r - 1 + ε⁻¹) * z + (r ^ 2 - r) * τ =
        A / N - r * s + (r * τ + s) - r * τ := by
      linear_combination halg + hz0
    rw [hsplit]
    push_cast
    ring
  rw [hpoly, specialValueGaussianLift]
  have hR : (((-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2)) * e (A / (2 * N)))⁻¹ =
      (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) * e (-(A / (2 * N))) := by
    rw [mul_inv]
    have hself : ((-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2)) *
        ((-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2)) = 1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      exact (show Even ((u.1 + u.2 + u.1 * u.2) + (u.1 + u.2 + u.1 * u.2)) from
        ⟨u.1 + u.2 + u.1 * u.2, by ring⟩).neg_one_zpow
    rw [show (e (A / (2 * N)))⁻¹ = e (-(A / (2 * N))) by rw [e_neg'],
      show (((-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2)))⁻¹ = (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) from
        inv_eq_of_mul_eq_one_right hself]
  rw [hR]
  have hsign : (-1 : ℂ) ^ u.1 * (-1 : ℂ) ^ ((u.1 * u.2 - u.2 : ℤ)) =
      (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) := by
    have hq : u.1 + u.2 + u.1 * u.2 = u.1 + (u.1 * u.2 - u.2) + 2 * u.2 := by ring
    rw [hq, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      show (-1 : ℂ) ^ (2 * u.2 : ℤ) = 1 from
        (show Even (2 * u.2 : ℤ) from ⟨u.2, by ring⟩).neg_one_zpow,
      mul_one, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [e_add', e_half_int]
  calc (-1 : ℂ) ^ u.1 * (e (-(A / (2 * N))) * (-1 : ℂ) ^ (u.1 * u.2 - u.2))
      = ((-1 : ℂ) ^ u.1 * (-1 : ℂ) ^ (u.1 * u.2 - u.2)) * e (-(A / (2 * N))) := by ring
    _ = (-1 : ℂ) ^ (u.1 + u.2 + u.1 * u.2) * e (-(A / (2 * N))) := by rw [hsign]

/--
The nonlattice point-value reflection for the actual raw expressions.
[RW26, p. 3, p. 12, (5)].
-/
theorem specialValueRaw_reflection (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : ℤ × ℤ) (hu : u ∉ specialValueLattice M) :
    specialValueRaw M u * specialValueRaw M (-u) = (specialValueGaussianLift M u)⁻¹ := by
  have hnu : -u ∉ specialValueLattice M := by
    intro h
    exact hu (by simpa using neg_mem h)
  have hτ : (specialValueTau M : ℂ) ∈ modularPhiDomain M := specialValueTau_mem_domain M hM
  have hargneg : specialValueArgument M (-u) = -specialValueArgument M u := by
    simp only [specialValueArgument, modularPhiSpecialArgument, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Prod.fst_neg, Prod.snd_neg,
      Int.cast_neg]
    ring
  have hL : ContinuousAt (fun w => modularPhi M u.1 0 w (specialValueTau M : ℂ))
      (specialValueArgument M u) := by
    have h := (specialValuePhi_joint_regular M hM u hu 0).1.continuousAt
    have hmap : ContinuousAt (fun w : ℂ => (w, (specialValueTau M : ℂ)))
        (specialValueArgument M u) := by fun_prop
    have hcomp := ContinuousAt.comp (f := fun w : ℂ => (w, (specialValueTau M : ℂ))) h hmap
    simpa [Function.comp_def, Int.add_zero] using hcomp
  have hR : ContinuousAt
      (fun w => modularPhi M (1 - u.1) 1 (-w) (specialValueTau M : ℂ))
      (specialValueArgument M u) := by
    have hreg := (specialValuePhi_joint_regular M hM (-u) hnu 1).1
    rw [hargneg] at hreg
    have hidx : (-u).1 + 1 = 1 - u.1 := by
      simp only [Prod.fst_neg]
      ring
    rw [hidx] at hreg
    have h := hreg.continuousAt
    have hmap : ContinuousAt (fun w : ℂ => (-w, (specialValueTau M : ℂ)))
        (specialValueArgument M u) := by fun_prop
    have hcomp := ContinuousAt.comp (f := fun w : ℂ => (-w, (specialValueTau M : ℂ))) h hmap
    simpa [Function.comp_def] using hcomp
  have hrefl := modularPhi_reflection_normalized M hM.1 u.1 0 (specialValueArgument M u)
    (specialValueTau M : ℂ) hτ hL hR
  simp only [sub_zero] at hrefl
  have hidx := specialValue_reflection_index M hM u hu
  rw [hidx, hargneg] at hrefl
  have hmain : specialValueRaw M u * specialValueRaw M (-u) =
      (-1 : ℂ) ^ u.1 * e (modularReflectionPolynomial M u.1 0
        (specialValueArgument M u) (specialValueTau M : ℂ)) := by
    simpa [specialValueRaw, hargneg, Prod.fst_neg, add_zero] using hrefl
  rw [hmain, specialValue_reflection_phase M hM u]

/--
Literal [RW26, Thm. 2] (5), including zero. No Fourier or five-term input.
[RW26, p. 3, p. 12]. The zero case uses sqrt(ε) times its inverse.
-/
theorem specialValue_mixed_reflection (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u : SpecialValueGroup M) :
    specialValuePlus M hM u * specialValueMinus M hM (-u) =
      (specialValueGaussian M hM u)⁻¹ := by
  induction u using Quotient.inductionOn with
  | h x =>
    change specialValuePlus M hM (specialValueMk M x) *
        specialValueMinus M hM (specialValueMk M (-x)) =
      (specialValueGaussian M hM (specialValueMk M x))⁻¹
    rw [specialValuePlus_mk, specialValueMinus_mk, specialValueGaussian_mk]
    by_cases hx : x ∈ specialValueLattice M
    · have hnx : -x ∈ specialValueLattice M := neg_mem hx
      rw [specialValuePlusLift, specialValueMinusLift, if_pos hx, if_pos hnx]
      have hG : specialValueGaussianLift M x = 1 := by
        have h := gaussian_lattice_periodic M hM 0 x hx
        rw [zero_add, specialValueGaussianLift_zero] at h
        exact h
      rw [hG, inv_one]
      have hεpos : (0 : ℝ) < specialValueEpsilon M :=
        lt_trans zero_lt_one (specialValueEpsilon_gt_one M hM)
      have hsqrt : (Real.sqrt (specialValueEpsilon M) : ℂ) ≠ 0 := by
        have h : (0 : ℝ) < Real.sqrt (specialValueEpsilon M) := Real.sqrt_pos.mpr hεpos
        exact_mod_cast ne_of_gt h
      exact mul_inv_cancel₀ hsqrt
    · have hnx : -x ∉ specialValueLattice M := by
        intro h
        exact hx (by simpa using neg_mem h)
      rw [specialValuePlusLift, specialValueMinusLift, if_neg hx, if_neg hnx]
      exact specialValueRaw_reflection M hM x hx

/--
The plus sign in literal Theorem 2 (4), [RW26, p. 3].
-/
theorem specialValuePlus_origin_formula (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) :
    specialValuePlus M hM 0 =
      (Real.sqrt (((specialValueOrder M : ℝ) + 2 +
        Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2) : ℂ) := by
  rw [← map_zero (specialValueMk M), specialValuePlus_mk, specialValuePlusLift,
    if_pos (zero_mem (specialValueLattice M)), specialValueEpsilon_formula M hM]

/--
The minus sign in literal Theorem 2 (4), [RW26, p. 3]. The inner
minus and the outer positive root are both retained, as required by L2.
-/
theorem specialValueMinus_origin_formula (M : SL(2, ℤ))
    (hM : SpecialValueAdmissible M) :
    specialValueMinus M hM 0 =
      (Real.sqrt (((specialValueOrder M : ℝ) + 2 -
        Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2) : ℂ) := by
  rw [← map_zero (specialValueMk M), specialValueMinus_mk, specialValueMinusLift,
    if_pos (zero_mem (specialValueLattice M)), specialValueEpsilon_formula M hM]
  have hNnonneg : (0 : ℝ) ≤ (specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ) := by
    have h := specialValueOrder_pos M hM
    have : (0 : ℝ) < (specialValueOrder M : ℝ) := by exact_mod_cast h
    positivity
  have hs : (Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) ^ 2
      = (specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ) :=
    Real.sq_sqrt hNnonneg
  have hmul : (((specialValueOrder M : ℝ) + 2 +
        Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2) *
      (((specialValueOrder M : ℝ) + 2 -
        Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2) = 1 := by
    nlinarith [hs]
  have hPnonneg : (0 : ℝ) ≤ ((specialValueOrder M : ℝ) + 2 +
      Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2 := by
    have h := specialValueOrder_pos M hM
    have : (0 : ℝ) < (specialValueOrder M : ℝ) := by exact_mod_cast h
    have := Real.sqrt_nonneg ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))
    positivity
  have hPQ : Real.sqrt (((specialValueOrder M : ℝ) + 2 +
        Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2) *
      Real.sqrt (((specialValueOrder M : ℝ) + 2 -
        Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2) = 1 := by
    rw [← Real.sqrt_mul hPnonneg, hmul, Real.sqrt_one]
  have hcast : ((Real.sqrt (((specialValueOrder M : ℝ) + 2 +
        Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2) : ℂ)) *
      ((Real.sqrt (((specialValueOrder M : ℝ) + 2 -
        Real.sqrt ((specialValueOrder M : ℝ) ^ 2 + 4 * (specialValueOrder M : ℝ))) / 2) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, hPQ, Complex.ofReal_one]
  exact inv_eq_of_mul_eq_one_right hcast

#check @modularPhi_reflection_normalized
#print specialValueGaussianLift
#print specialValuePairingLift
#check specialValue_mixed_reflection
#check specialValueMinus_origin_formula

end SICLean.L4
