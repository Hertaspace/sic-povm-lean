import SICLean.L2b.FiniteQDDefs

set_option autoImplicit false

/-!
# The first six finite quantum dilogarithm consequences

The abstract steps of [RW26, Thm. 5], from (31) through (34) and the nonzero
Fourier product relation. The finite support argument uses the translation
stabilizer of the Fourier zero set. No lower bound on the group order is
needed here.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L2b

variable {A : Type*} [AddCommGroup A] [Fintype A]

local instance finiteQDCoreDecidableEq : DecidableEq A := Classical.decEq A

theorem core_pairing_ne_zero {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q x y ≠ 0 :=
  div_ne_zero (hq.nonzero _) (mul_ne_zero (hq.nonzero _) (hq.nonzero _))

@[simp] theorem core_pairing_zero_left {q : A → ℂ} (hq : IsMetricGaussian q) (y : A) :
    metricPairing q 0 y = 1 := by
  simp [metricPairing, metric_zero hq, hq.nonzero y]

@[simp] theorem core_pairing_zero_right {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) :
    metricPairing q x 0 = 1 := by
  simp [metricPairing, metric_zero hq, hq.nonzero x]

theorem core_pairing_neg_left {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q (-x) y = (metricPairing q x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hq.add_left, neg_add_cancel, core_pairing_zero_left hq]

theorem core_pairing_neg_right {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q x (-y) = (metricPairing q x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hq.add_right, neg_add_cancel, core_pairing_zero_right hq]

theorem core_pairing_neg_neg {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q (-x) (-y) = metricPairing q x y := by
  rw [core_pairing_neg_left hq, core_pairing_neg_right hq, inv_inv]

theorem core_pairing_sub_left {q : A → ℂ} (hq : IsMetricGaussian q) (x y z : A) :
    metricPairing q (x - y) z = metricPairing q x z / metricPairing q y z := by
  rw [sub_eq_add_neg, hq.add_left, core_pairing_neg_left hq, div_eq_mul_inv]

theorem core_pairing_sub_right {q : A → ℂ} (hq : IsMetricGaussian q) (x y z : A) :
    metricPairing q x (y - z) = metricPairing q x y / metricPairing q x z := by
  rw [sub_eq_add_neg, hq.add_right, core_pairing_neg_right hq, div_eq_mul_inv]

theorem core_gaussian_add {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    q (x + y) = metricPairing q x y * q x * q y := by
  dsimp [metricPairing]
  field_simp [hq.nonzero x, hq.nonzero y]

theorem core_sqrtCard_sq : sqrtCard A ^ 2 = (Fintype.card A : ℂ) := by
  unfold sqrtCard
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rfl

theorem core_normalizedSum_congr {f g : A → ℂ} (h : ∀ x, f x = g x) :
    normalizedSum f = normalizedSum g := by
  unfold normalizedSum
  congr 1
  exact Finset.sum_congr rfl fun x _ => h x

@[simp] theorem core_normalizedSum_zero : normalizedSum (fun _ : A => (0 : ℂ)) = 0 := by
  simp [normalizedSum]

theorem core_normalizedSum_add (f g : A → ℂ) :
    normalizedSum (fun x => f x + g x) = normalizedSum f + normalizedSum g := by
  simp [normalizedSum, Finset.sum_add_distrib, add_div]

theorem core_normalizedSum_mul_left (c : ℂ) (f : A → ℂ) :
    normalizedSum (fun x => c * f x) = c * normalizedSum f := by
  unfold normalizedSum
  rw [← Finset.mul_sum]
  ring

theorem core_normalizedSum_mul_right (f : A → ℂ) (c : ℂ) :
    normalizedSum (fun x => f x * c) = normalizedSum f * c := by
  simp only [mul_comm _ c, core_normalizedSum_mul_left]

theorem core_normalizedSum_swap (f : A → A → ℂ) :
    normalizedSum (fun x => normalizedSum (fun y => f x y)) =
      normalizedSum (fun y => normalizedSum (fun x => f x y)) := by
  unfold normalizedSum
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]

theorem core_normalizedSum_translate (f : A → ℂ) (a : A) :
    normalizedSum (fun x => f (x + a)) = normalizedSum f := by
  unfold normalizedSum
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

theorem core_normalizedSum_neg (f : A → ℂ) :
    normalizedSum (fun x => f (-x)) = normalizedSum f := by
  unfold normalizedSum
  congr 1
  exact Fintype.sum_equiv (Equiv.neg A) _ _ (fun _ => rfl)

theorem core_normalizedSum_sub (f : A → ℂ) (a : A) :
    normalizedSum (fun x => f (a - x)) = normalizedSum f := by
  unfold normalizedSum
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)

theorem core_fourier_zero {q : A → ℂ} (hq : IsMetricGaussian q) (f : A → ℂ) :
    fourier q f 0 = normalizedSum f := by
  simp [fourier, core_pairing_zero_right hq]

theorem core_character_normalizedSum {q : A → ℂ} (hq : IsMetricGaussian q) (w : A) :
    normalizedSum (fun y => metricPairing q y (-w)) =
      sqrtCard A * (if w = 0 then 1 else 0) := by
  rw [normalizedSum, character_sum hq]
  by_cases hw : w = 0
  · subst w
    simp only [neg_zero, ↓reduceIte, mul_one]
    apply (div_eq_iff sqrtCard_ne_zero).2
    simpa [pow_two] using (core_sqrtCard_sq (A := A)).symm
  · simp [hw]

theorem core_fourier_convolution {q : A → ℂ} (hq : IsMetricGaussian q)
    (f g : A → ℂ) (w : A) :
    fourier q (fun y => normalizedSum (fun z => f (y - z) * g z)) w =
      fourier q f w * fourier q g w := by
  unfold fourier
  calc
    _ = normalizedSum (fun y => normalizedSum (fun z =>
        f (y - z) * g z * metricPairing q y (-w))) := by
      apply core_normalizedSum_congr
      intro y
      rw [core_normalizedSum_mul_right]
    _ = normalizedSum (fun z => normalizedSum (fun y =>
        f (y - z) * g z * metricPairing q y (-w))) := core_normalizedSum_swap _
    _ = normalizedSum (fun z => normalizedSum (fun y =>
        f y * g z * metricPairing q (y + z) (-w))) := by
      apply core_normalizedSum_congr
      intro z
      symm
      simpa only [add_sub_cancel_right] using
        core_normalizedSum_translate (fun y =>
          f (y - z) * g z * metricPairing q y (-w)) z
    _ = normalizedSum (fun z =>
        normalizedSum (fun y => f y * metricPairing q y (-w)) *
          (g z * metricPairing q z (-w))) := by
      apply core_normalizedSum_congr
      intro z
      rw [← core_normalizedSum_mul_right]
      apply core_normalizedSum_congr
      intro y
      rw [hq.add_left]
      ring
    _ = _ := core_normalizedSum_mul_left _ _

theorem transformed_pentagon_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) (x w : A) :
    E x * fourier q E (w - x) =
      C * sqrtCard A * (if w = 0 then 1 else 0) +
        fourier q E w * fourier q (pentagonKernel q E x) w := by
  have hp := congrArg (fun f : A → ℂ => fourier q f w) (funext (hE x))
  calc
    E x * fourier q E (w - x) =
        fourier q (fun y => metricPairing q x y * E x * E y) w := by
      unfold fourier
      rw [← core_normalizedSum_mul_left]
      apply core_normalizedSum_congr
      intro y
      dsimp only
      rw [metric_pairing_symmetric q x y]
      have hz : -(w - x) = x + -w := by abel
      rw [hz, hq.add_right]
      ring
    _ = fourier q (fun y => C + normalizedSum (fun z =>
        E (y - z) * E z * q z * E (x - z))) w := hp
    _ = _ := by
      unfold fourier
      simp_rw [add_mul]
      rw [core_normalizedSum_add]
      congr 1
      · rw [core_normalizedSum_mul_left, core_character_normalizedSum hq]
        ring
      · change fourier q (fun y => normalizedSum (fun z =>
            E (y - z) * E z * q z * E (x - z))) w =
          fourier q E w * fourier q (pentagonKernel q E x) w
        rw [← core_fourier_convolution hq E (pentagonKernel q E x) w]
        congr 1
        funext y
        apply core_normalizedSum_congr
        intro z
        unfold pentagonKernel
        ring

/-- The support argument in [RW26, Thm. 5], including finite-set reversibility of translations. -/
theorem fourier_everywhere_ne_zero_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (w : A) :
    fourier q E w ≠ 0 := by
  obtain ⟨C, hC, hP⟩ := hE
  have hzero : fourier q E 0 ≠ 0 := by
    intro hz
    have hp := transformed_pentagon_core hq hC hP 0 0
    simp only [sub_self, hz, mul_zero, zero_mul, ite_true, mul_one, add_zero] at hp
    exact (mul_ne_zero hC sqrtCard_ne_zero) hp.symm
  have hforward : ∀ x, E x ≠ 0 → ∀ v,
      fourier q E v = 0 → fourier q E (v - x) = 0 := by
    intro x hx v hv
    have hv0 : v ≠ 0 := by
      intro h
      subst v
      exact hzero hv
    have hp := transformed_pentagon_core hq hC hP x v
    simp only [hv, if_neg hv0, mul_zero, zero_mul, add_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_left hx
  let H : AddSubgroup A :=
    { carrier := {x | ∀ v, fourier q E v = 0 ↔ fourier q E (v - x) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy v
        have hs : v - (x + y) = (v - x) - y := by abel
        rw [hs]
        exact (hx v).trans (hy (v - x))
      neg_mem' := by
        intro x hx v
        have hs : (v - -x) - x = v := by abel
        simpa only [hs] using (hx (v - -x)).symm }
  have hsupport : ∀ x, E x ≠ 0 → x ∈ H := by
    intro x hx v
    constructor
    · exact hforward x hx v
    · intro hv
      let f : {v : A // fourier q E v = 0} → {v : A // fourier q E v = 0} :=
        fun z => ⟨z.val - x, hforward x hx z.val z.property⟩
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        have ht := congrArg Subtype.val hab
        exact sub_left_inj.mp ht
      obtain ⟨z, hz⟩ := Finite.surjective_of_injective hf ⟨v - x, hv⟩
      have hzv : z.val = v := by
        have ht := congrArg Subtype.val hz
        exact sub_left_inj.mp ht
      simpa only [hzv] using z.property
  have hall : ∀ x : A, x ∈ H := by
    intro x
    by_contra hx
    have hex : E x = 0 := by
      by_contra he
      exact hx (hsupport x he)
    have hsum : normalizedSum (fun z => E (x - z) * E z * q z * E (x - z)) = 0 := by
      calc
        _ = normalizedSum (fun _ : A => (0 : ℂ)) := by
          apply core_normalizedSum_congr
          intro z
          by_cases hz : E z = 0
          · simp only [hz, mul_zero, zero_mul]
          · have hxz : E (x - z) = 0 := by
              by_contra he
              have ht := H.add_mem (hsupport (x - z) he) (hsupport z hz)
              exact hx (by simpa only [sub_add_cancel] using ht)
            simp only [hxz, zero_mul]
        _ = 0 := core_normalizedSum_zero
    have hp := hP x x
    simp only [hex, mul_zero, hsum, add_zero] at hp
    exact hC hp.symm
  intro hw
  have hz := (hall w w).mp hw
  exact hzero (by simpa only [sub_self] using hz)

theorem core_fourier_const {q : A → ℂ} (hq : IsMetricGaussian q) (c : ℂ) (w : A) :
    fourier q (fun _ => c) w = c * sqrtCard A * (if w = 0 then 1 else 0) := by
  unfold fourier
  rw [core_normalizedSum_mul_left, core_character_normalizedSum hq]
  ring

theorem core_fourier_delta {q : A → ℂ} (hq : IsMetricGaussian q) (c : ℂ) (w : A) :
    fourier q (fun x => if x = 0 then c else 0) w = c / sqrtCard A := by
  unfold fourier normalizedSum
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [core_pairing_zero_left hq]

theorem core_fourier_sub_distrib (q f g : A → ℂ) (w : A) :
    fourier q (fun x => f x - g x) w = fourier q f w - fourier q g w := by
  unfold fourier normalizedSum
  simp only [sub_mul, Finset.sum_sub_distrib, sub_div]

/-- [RW26, (34)], obtained by Fourier inversion before determining the constant. -/
theorem reflection_with_constant_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) (u : A) :
    E u * E (-u) * q u =
      sqrtCard A * E 0 * (if u = 0 then 1 else 0) - C / fourier q E 0 := by
  have hhat := fourier_everywhere_ne_zero_core hq ⟨C, hC, hE⟩
  have hker : ∀ w, fourier q (pentagonKernel q E 0) w =
      E 0 - if w = 0 then C * sqrtCard A / fourier q E 0 else 0 := by
    intro w
    have hp := transformed_pentagon_core hq hC hE 0 w
    simp only [sub_zero] at hp
    by_cases hw : w = 0
    · subst w
      simp only [ite_true]
      simp only [ite_true, mul_one] at hp
      field_simp [hhat 0]
      linear_combination -hp
    · simp only [if_neg hw, mul_zero, zero_add] at hp ⊢
      exact (mul_left_cancel₀ (hhat w)) (by linear_combination -hp)
  have hi : fourier q (fourier q (pentagonKernel q E 0)) (-u) =
      pentagonKernel q E 0 u := by
    simpa only [neg_neg] using fourier_twice hq (pentagonKernel q E 0) (-u)
  rw [funext hker, core_fourier_sub_distrib, core_fourier_const hq,
    core_fourier_delta hq] at hi
  have hs : C * sqrtCard A / fourier q E 0 / sqrtCard A = C / fourier q E 0 := by
    field_simp [sqrtCard_ne_zero]
  rw [hs] at hi
  simpa only [pentagonKernel, zero_sub, hq.even u, neg_eq_zero, mul_comm] using hi.symm


theorem fqd_everywhere_ne_zero_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (u : A) : E u ≠ 0 := by
  obtain ⟨C, hC, hP⟩ := hE
  have hhat := fourier_everywhere_ne_zero_core hq ⟨C, hC, hP⟩ 0
  intro hu
  have hp := reflection_with_constant_core hq hC hP u
  by_cases h0 : u = 0
  · subst u
    simp only [hu, zero_mul, mul_zero, zero_sub] at hp
    exact (div_ne_zero hC hhat) (neg_eq_zero.mp hp.symm)
  · simp only [hu, zero_mul, if_neg h0, mul_zero, zero_sub] at hp
    exact (div_ne_zero hC hhat) (neg_eq_zero.mp hp.symm)

theorem core_gaussian_sub {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    q (x - y) = metricPairing q x (-y) * q x * q y := by
  rw [sub_eq_add_neg, core_gaussian_add hq, hq.even]

theorem core_kernel_phase {q : A → ℂ} (hq : IsMetricGaussian q) (x w z : A) :
    q (x - z) * metricPairing q (x - z) (-w) =
      q (x - w) / q w * q z * metricPairing q z (-(x - w)) := by
  have hb : metricPairing q (x - z) (-w) =
      metricPairing q x (-w) * metricPairing q z w := by
    rw [sub_eq_add_neg, hq.add_left, core_pairing_neg_neg hq]
  have hs : metricPairing q x (-z) = metricPairing q z (-x) := by
    rw [core_pairing_neg_right hq, core_pairing_neg_right hq,
      metric_pairing_symmetric q x z]
  have hn : -(x - w) = -x + w := by abel
  rw [core_gaussian_sub hq, hb, core_gaussian_sub hq, hs, hn, hq.add_right]
  field_simp [hq.nonzero w]

theorem kernel_fourier_symmetry_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    (x w : A) :
    fourier q (pentagonKernel q E x) w =
      q (x - w) / q w * fourier q (pentagonKernel q E x) (x - w) := by
  unfold fourier
  calc
    _ = normalizedSum (fun z => pentagonKernel q E x (x - z) *
        metricPairing q (x - z) (-w)) :=
      (core_normalizedSum_sub (fun z => pentagonKernel q E x z *
        metricPairing q z (-w)) x).symm
    _ = q (x - w) / q w * normalizedSum (fun z =>
        pentagonKernel q E x z * metricPairing q z (-(x - w))) := by
      rw [← core_normalizedSum_mul_left]
      apply core_normalizedSum_congr
      intro z
      dsimp only [pentagonKernel]
      rw [sub_sub_cancel]
      linear_combination E (x - z) * E z * core_kernel_phase hq x w z


theorem core_fourier_product_relation {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (u v : A) (hu : u ≠ 0) (hv : v ≠ 0) :
    fourier q E u * fourier q E (-u) * q v =
      fourier q E v * fourier q E (-v) * q u := by
  obtain ⟨C, hC, hP⟩ := hE
  have hp1 := transformed_pentagon_core hq hC hP (u + v) v
  have hp2 := transformed_pentagon_core hq hC hP (u + v) u
  have he := fqd_everywhere_ne_zero_core hq ⟨C, hC, hP⟩ (u + v)
  have h1 : v - (u + v) = -u := by abel
  have h2 : u - (u + v) = -v := by abel
  have h3 : u + v - v = u := by abel
  simp only [h1, if_neg hv, mul_zero, zero_add] at hp1
  simp only [h2, if_neg hu, mul_zero, zero_add] at hp2
  rw [kernel_fourier_symmetry_core hq (u + v) v, h3] at hp1
  field_simp [hq.nonzero v] at hp1
  apply mul_left_cancel₀ he
  linear_combination fourier q E u * hp1 - (fourier q E v * q u) * hp2

theorem fourier_product_off_zero_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ u : A, u ≠ 0 →
      fourier q E u * fourier q E (-u) = d * q u := by
  by_cases hnontrivial : ∃ v : A, v ≠ 0
  · obtain ⟨v, hv⟩ := hnontrivial
    refine ⟨fourier q E v * fourier q E (-v) / q v,
      div_ne_zero (mul_ne_zero (fourier_everywhere_ne_zero_core hq hE v)
        (fourier_everywhere_ne_zero_core hq hE (-v))) (hq.nonzero v), ?_⟩
    intro u hu
    have hp := core_fourier_product_relation hq hE u v hu hv
    apply (mul_right_cancel₀ (hq.nonzero v))
    field_simp [hq.nonzero v]
    exact hp
  · refine ⟨1, one_ne_zero, ?_⟩
    intro u hu
    exact (hnontrivial ⟨u, hu⟩).elim

end SICLean.L2b
