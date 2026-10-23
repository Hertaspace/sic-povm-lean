import SICLean.L4.UpperContourGeometry
import SICLean.L4.UpperContourShiftsAux

set_option autoImplicit false

/-!
# Exact integer shifts, first as punctured germs

A common q-product zero does not license a
pointwise quotient identity. The first two shift identities are z-germs;
the last two apply only on the existing divisor-free templates, where the
two finite denominator products are separately nonzero. Integer shifts are formalized here. [RW26,
pp. 28--29].
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval BigOperators MatrixGroups Classical

namespace SICLean.L4.UpperContour

def triangular (N : ℕ) : ℕ := N * (N + 1) / 2

def translate (M : SL(2, ℤ)) (τ z : ℂ) (j k : ℕ) : ℂ :=
  z + (j : ℂ) * etaDenom M τ + (k : ℂ)

/-- Literal right-hand multiplier. -/
def ratioShift (M : SL(2, ℤ)) (m n h ℓ p : ℤ) (x : UpperWindow.Parameters)
    (z : ℂ) (j k : ℕ) : ℂ :=
  UpperWindow.A ℓ x.1 x.2.1 ^ ((M 1 0).toNat * j) *
    UpperWindow.B M h x.1 x.2.1 x.2.2 ^ ((M 1 0).toNat * k) *
    (qPochhammerNat (UpperWindow.bArg m p x.1 x.2.2 z) (e x.1) ((M 1 0).toNat * j) /
      qPochhammerNat (UpperWindow.aArg m x.1 z) (e x.1) ((M 1 0).toNat * j)) *
    (qPochhammerNat (e (etaMobius M x.1) / UpperWindow.cArg M n x.1 x.2.2 z)
        (e (etaMobius M x.1)) ((M 1 0).toNat * k) /
      qPochhammerNat (e (etaMobius M x.1) / UpperWindow.dArg M n x.1 z)
        (e (etaMobius M x.1)) ((M 1 0).toNat * k))

/-- Literal right-hand multiplier; triangular exponent is natural. -/
def singleShift (M : SL(2, ℤ)) (m n h ℓ : ℤ) (x : UpperWindow.Parameters)
    (z : ℂ) (j k : ℕ) : ℂ :=
  UpperWindow.A ℓ x.1 x.2.1 ^ ((M 1 0).toNat * j) *
    (UpperWindow.C M h x.1 x.2.1 ^ ((M 1 0).toNat * k) *
      (-UpperWindow.dArg M n x.1 z) ^ (-(((M 1 0).toNat * k : ℕ) : ℤ)) *
      e (etaMobius M x.1) ^ triangular ((M 1 0).toNat * k)) /
    (qPochhammerNat (UpperWindow.aArg m x.1 z) (e x.1) ((M 1 0).toNat * j) *
      qPochhammerNat (e (etaMobius M x.1) / UpperWindow.dArg M n x.1 z)
        (e (etaMobius M x.1)) ((M 1 0).toNat * k))

/--
No floor error in ck(ck+1)/2; [RW26, pp. 28--29].
-/
theorem triangular_twice (N : ℕ) : 2 * triangular N = N * (N + 1) := by
  exact UpperContourShiftsAux.triangular_twice N

/--
The kernel exponent has exactly the existing slope s/T; [RW26, p. 29].
-/
theorem phase_affine (M : SL(2, ℤ)) (m n h ℓ : ℤ) (τ w z u : ℂ)
    (hT : etaDenom M τ ≠ 0) :
    UpperWindow.phase M m n h ℓ τ w (z + u) =
      UpperWindow.phase M m n h ℓ τ w z + UpperWindow.upperSlope M h ℓ τ w * u := by
  unfold UpperWindow.phase UpperWindow.upperSlope UpperWindow.s
  field_simp
  ring

/--
Integer phase discrepancies disappear only after e; [RW26, p. 29].
-/
theorem exponential_shift (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n h ℓ : ℤ)
    (τ w z : ℂ) (hT : etaDenom M τ ≠ 0) (j k : ℕ) :
    e (UpperWindow.phase M m n h ℓ τ w (translate M τ z j k)) =
      e (UpperWindow.phase M m n h ℓ τ w z) *
        UpperWindow.A ℓ τ w ^ ((M 1 0).toNat * j) *
        UpperWindow.C M h τ w ^ ((M 1 0).toNat * k) := by
  rw [translate, show z + (j : ℂ) * etaDenom M τ + (k : ℂ) =
    z + ((j : ℂ) * etaDenom M τ + (k : ℂ)) by ring,
    phase_affine M m n h ℓ τ w z _ hT, e_add', mul_add,
    show UpperWindow.upperSlope M h ℓ τ w * ((j : ℂ) * etaDenom M τ) =
      (j : ℂ) * (UpperWindow.upperSlope M h ℓ τ w * etaDenom M τ) by ring,
    show UpperWindow.upperSlope M h ℓ τ w * (k : ℂ) =
      (k : ℂ) * UpperWindow.upperSlope M h ℓ τ w by ring,
    e_add', ← e_nat_mul, ← e_nat_mul,
    UpperContourShiftsAux.e_slope_T M hM h ℓ τ w hT,
    UpperContourShiftsAux.e_slope_one M hM h ℓ τ w hT,
    ← pow_mul, ← pow_mul, mul_assoc]

/--
Four raw arguments, including the negative Q exponent; [RW26, pp. 28--29].
-/
theorem arguments_shift (M : SL(2, ℤ)) (hM : 0 < M 1 0) (m n p : ℤ)
    (τ y z : ℂ) (hT : etaDenom M τ ≠ 0) (j k : ℕ) :
    UpperWindow.aArg m τ (translate M τ z j k) =
        UpperWindow.aArg m τ z * (e τ) ^ ((M 1 0).toNat * j) ∧
    UpperWindow.bArg m p τ y (translate M τ z j k) =
        UpperWindow.bArg m p τ y z * (e τ) ^ ((M 1 0).toNat * j) ∧
    UpperWindow.dArg M n τ (translate M τ z j k) =
        UpperWindow.dArg M n τ z * (e (etaMobius M τ)) ^ (-(((M 1 0).toNat * k : ℕ) : ℤ)) ∧
    UpperWindow.cArg M n τ y (translate M τ z j k) =
        UpperWindow.cArg M n τ y z * (e (etaMobius M τ)) ^ (-(((M 1 0).toNat * k : ℕ) : ℤ)) := by
  have he := UpperContourShiftsAux.e_translate M hM τ z j k
  have hey := UpperContourShiftsAux.e_translate M hM τ (z + y) j k
  have hd := UpperContourShiftsAux.e_translate_div M hM τ z hT j k
  have hdy := UpperContourShiftsAux.e_translate_div M hM τ (z + y) hT j k
  simp only [translate, UpperWindow.aArg, UpperWindow.bArg, UpperWindow.dArg,
    UpperWindow.cArg]
  rw [show z + (j : ℂ) * etaDenom M τ + (k : ℂ) + y =
    (z + y) + (j : ℂ) * etaDenom M τ + (k : ℂ) by ring]
  rw [he, hey, hd, hdy]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/--
Cleared backward product identity, valid even at zeros of the infinite
products; d,Q themselves are nonzero; [RW26, pp. 28--29, (50)--(51)] (application).
-/
theorem qPochhammer_backward_cleared (d Q : ℂ) (hd : d ≠ 0)
    (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) (N : ℕ) :
    qPochhammer (d * Q ^ (-(N : ℤ))) Q =
      (-d) ^ N * Q ^ (-(triangular N : ℤ)) *
        qPochhammerNat (Q / d) Q N * qPochhammer d Q := by
  exact UpperContourShiftsAux.backward_cleared d Q hd hQ0 hQ1 N

/--
Meromorphic identity, with no claim about the raw center value; [RW26, pp. 28--29].
-/
theorem ratio_shift_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n h ℓ p : ℤ) (x : UpperWindow.Parameters) (hτ : 0 < x.1.im)
    (z : ℂ) (j k : ℕ) :
    (fun u => kernel .ratio M m n h ℓ p x (translate M x.1 u j k)) =ᶠ[𝓝[≠] z]
      (fun u => kernel .ratio M m n h ℓ p x u * ratioShift M m n h ℓ p x u j k) := by
  have hT := etaDenom_ne_zero_of_mem M (mem_modularPhiDomain_of_im_pos M hM hτ)
  have hq0 : 0 < ‖e x.1‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hq1 : ‖e x.1‖ < 1 := norm_e_lt_one ⟨_, hτ⟩
  have hQ0 : 0 < ‖e (etaMobius M x.1)‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hQ1 : ‖e (etaMobius M x.1)‖ < 1 :=
    norm_e_lt_one ⟨_, m37c_upper_mobius M x.1 hτ⟩
  have ht : Tendsto (fun u => translate M x.1 u j k) (𝓝[≠] z)
      (𝓝[≠] (translate M x.1 z j k)) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin
      (show ContinuousAt (fun u => translate M x.1 u j k) z by
        unfold translate; fun_prop).continuousWithinAt
    intro u hu heq
    exact hu (add_right_cancel (add_right_cancel heq))
  have hty := (UpperContourShiftsAux.tendsto_add_const_nhdsNE x.2.2
    (translate M x.1 z j k)).comp ht
  have hn := modularPhi_eq_qProduct_germ M hM (m + 1) n z x.1 hτ
  have hd := (UpperContourShiftsAux.tendsto_add_const_nhdsNE x.2.2 z).eventually
    (modularPhi_eq_qProduct_germ M hM (m + p) n (z + x.2.2) x.1 hτ)
  have hns := ht.eventually
    (modularPhi_eq_qProduct_germ M hM (m + 1) n (translate M x.1 z j k) x.1 hτ)
  have hds := hty.eventually
    (modularPhi_eq_qProduct_germ M hM (m + p) n
      (translate M x.1 z j k + x.2.2) x.1 hτ)
  have ha : ∀ᶠ u in 𝓝[≠] z,
      qPochhammerNat (UpperWindow.aArg m x.1 u) (e x.1) ((M 1 0).toNat * j) ≠ 0 := by
    simpa only [UpperWindow.aArg, one_mul] using
      UpperContourShiftsAux.finite_exp_eventually_ne_zero (e x.1 ^ (m + 1)) 1
        (e x.1) z (zpow_ne_zero _ (e_ne_zero _)) one_ne_zero hq0 hq1 ((M 1 0).toNat * j)
  have hb : ∀ᶠ u in 𝓝[≠] z,
      qPochhammerNat (UpperWindow.bArg m p x.1 x.2.2 u) (e x.1)
        ((M 1 0).toNat * j) ≠ 0 := by
    simpa only [UpperWindow.bArg, one_mul, mul_one, e_add', mul_assoc, mul_left_comm, mul_comm] using
      UpperContourShiftsAux.finite_exp_eventually_ne_zero (e x.1 ^ (m + p) * e x.2.2) 1
        (e x.1) z (mul_ne_zero (zpow_ne_zero _ (e_ne_zero _)) (e_ne_zero _))
        one_ne_zero hq0 hq1 ((M 1 0).toNat * j)
  filter_upwards [hn, hd, hns, hds, ha, hb] with u hnu hdu hnsu hdsu hau hbu
  dsimp only [Function.comp_def] at hdsu
  change (modularPhi M (m + 1) n (translate M x.1 u j k) x.1 /
      modularPhi M (m + p) n (translate M x.1 u j k + x.2.2) x.1) *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 (translate M x.1 u j k)) =
    (modularPhi M (m + 1) n u x.1 / modularPhi M (m + p) n (u + x.2.2) x.1) *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 u) * ratioShift M m n h ℓ p x u j k
  rw [hnu, hdu, hnsu, hdsu]
  change (qPochhammer (UpperWindow.aArg m x.1 (translate M x.1 u j k)) (e x.1) /
      qPochhammer (UpperWindow.dArg M n x.1 (translate M x.1 u j k)) (e (etaMobius M x.1))) /
      (qPochhammer (UpperWindow.bArg m p x.1 x.2.2 (translate M x.1 u j k)) (e x.1) /
      qPochhammer (UpperWindow.cArg M n x.1 x.2.2 (translate M x.1 u j k))
        (e (etaMobius M x.1))) *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 (translate M x.1 u j k)) =
    ((qPochhammer (UpperWindow.aArg m x.1 u) (e x.1) /
      qPochhammer (UpperWindow.dArg M n x.1 u) (e (etaMobius M x.1))) /
      (qPochhammer (UpperWindow.bArg m p x.1 x.2.2 u) (e x.1) /
      qPochhammer (UpperWindow.cArg M n x.1 x.2.2 u) (e (etaMobius M x.1)))) *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 u) * ratioShift M m n h ℓ p x u j k
  obtain ⟨haa, hbb, hdd, hcc⟩ := arguments_shift M hM m n p x.1 x.2.2 u hT j k
  rw [haa, hbb, hdd, hcc,
    UpperContourShiftsAux.q_ratio_shift _ _ _ _ _ _
      (UpperContourShiftsAux.cArg_ne_zero M n x.1 x.2.2 u)
      (UpperContourShiftsAux.dArg_ne_zero M n x.1 u)
      hq0 hq1 hQ0 hQ1 _ _ hau hbu,
    UpperContourShiftsAux.cArg_div_dArg M n x.1 x.2.2 u,
    exponential_shift M hM m n h ℓ x.1 x.2.1 u hT j k]
  unfold ratioShift UpperWindow.B
  rw [mul_pow]
  ring

/--
Single function is proved independently, not by an uncontrolled y limit; [RW26, pp. 28--29].
-/
theorem single_shift_germ (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n h ℓ p : ℤ) (x : UpperWindow.Parameters) (hτ : 0 < x.1.im)
    (z : ℂ) (j k : ℕ) :
    (fun u => kernel .single M m n h ℓ p x (translate M x.1 u j k)) =ᶠ[𝓝[≠] z]
      (fun u => kernel .single M m n h ℓ p x u * singleShift M m n h ℓ x u j k) := by
  have hT := etaDenom_ne_zero_of_mem M (mem_modularPhiDomain_of_im_pos M hM hτ)
  have hq0 : 0 < ‖e x.1‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hq1 : ‖e x.1‖ < 1 := norm_e_lt_one ⟨_, hτ⟩
  have hQ0 : 0 < ‖e (etaMobius M x.1)‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hQ1 : ‖e (etaMobius M x.1)‖ < 1 :=
    norm_e_lt_one ⟨_, m37c_upper_mobius M x.1 hτ⟩
  have ht : Tendsto (fun u => translate M x.1 u j k) (𝓝[≠] z)
      (𝓝[≠] (translate M x.1 z j k)) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin
      (show ContinuousAt (fun u => translate M x.1 u j k) z by
        unfold translate; fun_prop).continuousWithinAt
    intro u hu heq
    exact hu (add_right_cancel (add_right_cancel heq))
  have hn := modularPhi_eq_qProduct_germ M hM (m + 1) n z x.1 hτ
  have hns := ht.eventually
    (modularPhi_eq_qProduct_germ M hM (m + 1) n (translate M x.1 z j k) x.1 hτ)
  have ha : ∀ᶠ u in 𝓝[≠] z,
      qPochhammerNat (UpperWindow.aArg m x.1 u) (e x.1) ((M 1 0).toNat * j) ≠ 0 := by
    simpa only [UpperWindow.aArg, one_mul] using
      UpperContourShiftsAux.finite_exp_eventually_ne_zero (e x.1 ^ (m + 1)) 1
        (e x.1) z (zpow_ne_zero _ (e_ne_zero _)) one_ne_zero hq0 hq1 ((M 1 0).toNat * j)
  filter_upwards [hn, hns, ha] with u hnu hnsu hau
  change modularPhi M (m + 1) n (translate M x.1 u j k) x.1 *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 (translate M x.1 u j k)) =
    modularPhi M (m + 1) n u x.1 *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 u) * singleShift M m n h ℓ x u j k
  rw [hnu, hnsu]
  change (qPochhammer (UpperWindow.aArg m x.1 (translate M x.1 u j k)) (e x.1) /
      qPochhammer (UpperWindow.dArg M n x.1 (translate M x.1 u j k)) (e (etaMobius M x.1))) *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 (translate M x.1 u j k)) =
    (qPochhammer (UpperWindow.aArg m x.1 u) (e x.1) /
      qPochhammer (UpperWindow.dArg M n x.1 u) (e (etaMobius M x.1))) *
      e (UpperWindow.phase M m n h ℓ x.1 x.2.1 u) * singleShift M m n h ℓ x u j k
  obtain ⟨haa, _, hdd, _⟩ := arguments_shift M hM m n p x.1 x.2.2 u hT j k
  rw [haa, hdd,
    UpperContourShiftsAux.q_single_shift _ _ _ _
      (UpperContourShiftsAux.dArg_ne_zero M n x.1 u) hq0 hq1 hQ0 hQ1 _ _ hau,
    exponential_shift M hM m n h ℓ x.1 x.2.1 u hT j k]
  unfold singleShift triangular
  ring

/--
Precisely the two finite denominator products; no assertion that the
raw infinite product denominator is nonzero on every grid edge; [RW26, pp. 28--29].
-/
theorem template_denominators_ne_zero (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ)
    (z : ℂ) (hz : z ∈ UpperWindow.templates M m n δ x.1) (j k : ℕ) :
    qPochhammerNat (UpperWindow.aArg m x.1 z) (e x.1) ((M 1 0).toNat * j) ≠ 0 ∧
      qPochhammerNat (e (etaMobius M x.1) / UpperWindow.dArg M n x.1 z)
        (e (etaMobius M x.1)) ((M 1 0).toNat * k) ≠ 0 := by
  have hτ : 0 < x.1.im := hx.1.1
  have hq0 : 0 < ‖e x.1‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hq1 : ‖e x.1‖ < 1 := norm_e_lt_one ⟨_, hτ⟩
  have hQ0 : 0 < ‖e (etaMobius M x.1)‖ := norm_pos_iff.mpr (e_ne_zero _)
  have hQ1 : ‖e (etaMobius M x.1)‖ < 1 :=
    norm_e_lt_one ⟨_, m37c_upper_mobius M x.1 hτ⟩
  obtain ⟨ha, hd⟩ := UpperWindow.template_q_bounds M h ℓ p m n ψ σ ρ δ hc x hx z hz
  exact ⟨UpperContourShiftsAux.finite_ne_zero_of_norm_lt_one _ _ ha hq0 hq1 _,
    UpperContourShiftsAux.finite_ne_zero_of_norm_lt_one _ _ hd hQ0 hQ1 _⟩

/--
Safe pointwise specialization of the germ using grid regularity and
continuity at the actual center; [RW26, pp. 28--29].
-/
theorem ratio_shift_on_templates (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ)
    (z : ℂ) (hz : z ∈ UpperWindow.templates M m n δ x.1) (j k : ℕ) :
    kernel .ratio M m n h ℓ p x (translate M x.1 z j k) =
      kernel .ratio M m n h ℓ p x z * ratioShift M m n h ℓ p x z j k := by
  have hτ : 0 < x.1.im := hx.1.1
  have hu0 := UpperWindow.grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx z hz 0 0
  simp only [Nat.cast_zero, zero_mul, add_zero] at hu0
  have hu := UpperWindow.grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx z hz j k
  have hf := UpperContourShiftsAux.kernel_continuousAt .ratio M hc.1 m n h ℓ p x z
    hu0.1 hu0.2
  have hfs := UpperContourShiftsAux.kernel_continuousAt .ratio M hc.1 m n h ℓ p x
    (translate M x.1 z j k) hu.1 hu.2
  have ht : ContinuousAt (fun u => translate M x.1 u j k) z := by
    unfold translate
    fun_prop
  have hleft : ContinuousAt (fun u => kernel .ratio M m n h ℓ p x
      (translate M x.1 u j k)) z :=
    ContinuousAt.comp (f := fun u : ℂ => translate M x.1 u j k) hfs ht
  have hqa := ((UpperContourShiftsAux.continuous_finite (e x.1) ((M 1 0).toNat * j)).comp
    (UpperContourShiftsAux.continuous_aArg m x.1)).continuousAt (x := z)
  have hqb := ((UpperContourShiftsAux.continuous_finite (e x.1) ((M 1 0).toNat * j)).comp
    (UpperContourShiftsAux.continuous_bArg m p x.1 x.2.2)).continuousAt (x := z)
  have hqd := (UpperContourShiftsAux.continuous_dFinite M n x.1
    ((M 1 0).toNat * k)).continuousAt (x := z)
  have hqc := (UpperContourShiftsAux.continuous_cFinite M n x.1 x.2.2
    ((M 1 0).toNat * k)).continuousAt (x := z)
  have hne := template_denominators_ne_zero M h ℓ p m n ψ σ ρ δ hc x hx z hz j k
  have hmult : ContinuousAt (fun u => ratioShift M m n h ℓ p x u j k) z := by
    unfold ratioShift
    exact ((continuousAt_const.mul continuousAt_const).mul (hqb.div hqa hne.1)).mul
      (hqc.div hqd hne.2)
  exact ModularCocycleAux.eq_of_germ hleft (hf.mul hmult)
    (ratio_shift_germ M hc.1 m n h ℓ p x hτ z j k)

/--
Safe pointwise single shift on the same templates; [RW26, pp. 28--29].
-/
theorem single_shift_on_templates (M : SL(2, ℤ)) (h ℓ p m n : ℤ)
    (ψ σ ρ δ : ℝ) (hc : UpperWindow.Choices M ψ σ ρ δ) (x : UpperWindow.Parameters)
    (hx : x ∈ UpperWindow.domain M h ℓ p ψ σ ρ δ)
    (z : ℂ) (hz : z ∈ UpperWindow.templates M m n δ x.1) (j k : ℕ) :
    kernel .single M m n h ℓ p x (translate M x.1 z j k) =
      kernel .single M m n h ℓ p x z * singleShift M m n h ℓ x z j k := by
  have hτ : 0 < x.1.im := hx.1.1
  have hu0 := UpperWindow.grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx z hz 0 0
  simp only [Nat.cast_zero, zero_mul, add_zero] at hu0
  have hu := UpperWindow.grid_divisor_free M h ℓ p m n ψ σ ρ δ hc x hx z hz j k
  have hf := UpperContourShiftsAux.kernel_continuousAt .single M hc.1 m n h ℓ p x z
    hu0.1 hu0.2
  have hfs := UpperContourShiftsAux.kernel_continuousAt .single M hc.1 m n h ℓ p x
    (translate M x.1 z j k) hu.1 hu.2
  have ht : ContinuousAt (fun u => translate M x.1 u j k) z := by
    unfold translate
    fun_prop
  have hleft : ContinuousAt (fun u => kernel .single M m n h ℓ p x
      (translate M x.1 u j k)) z :=
    ContinuousAt.comp (f := fun u : ℂ => translate M x.1 u j k) hfs ht
  have hqa := ((UpperContourShiftsAux.continuous_finite (e x.1) ((M 1 0).toNat * j)).comp
    (UpperContourShiftsAux.continuous_aArg m x.1)).continuousAt (x := z)
  have hqd := (UpperContourShiftsAux.continuous_dFinite M n x.1
    ((M 1 0).toNat * k)).continuousAt (x := z)
  have hpow := (UpperContourShiftsAux.continuous_dArg M n x.1).continuousAt.neg.zpow₀
    (-(((M 1 0).toNat * k : ℕ) : ℤ))
    (Or.inl (neg_ne_zero.mpr (UpperContourShiftsAux.dArg_ne_zero M n x.1 z)))
  have hne := template_denominators_ne_zero M h ℓ p m n ψ σ ρ δ hc x hx z hz j k
  have hmult : ContinuousAt (fun u => singleShift M m n h ℓ x u j k) z := by
    unfold singleShift
    exact (continuousAt_const.mul ((continuousAt_const.mul hpow).mul continuousAt_const)).div
      (hqa.mul hqd) (mul_ne_zero hne.1 hne.2)
  exact ModularCocycleAux.eq_of_germ hleft (hf.mul hmult)
    (single_shift_germ M hc.1 m n h ℓ p x hτ z j k)

#print singleShift
#check ratio_shift_germ
#check template_denominators_ne_zero
#check single_shift_on_templates

end SICLean.L4.UpperContour
