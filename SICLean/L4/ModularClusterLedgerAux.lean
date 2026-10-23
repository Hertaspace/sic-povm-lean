import SICLean.L4.ModularClusterIntegrals

set_option autoImplicit false

/-!
# Auxiliary analytic and finite-ledger lemmas
The kernel-specific bridges translate labeled centers into regular slices.
The generic lemmas then supply two independent analytic steps: extracting
a finite principal part from a meromorphic order bound, and subtracting
prescribed local principal parts to obtain one analytic remainder on an
entire closed disk. Neither step prescribes the raw value at a pole.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L4.ModularCluster

lemma poleBudget_single (M : SL(2, ℤ)) (k : KernelData)
    (hsingle : k.ratio = false) (a τ : ℂ) :
    poleBudget M k a τ = modularPhiPoleMultiplicity M (k.m + 1) k.n a τ := by
  let eqv : fiber M k a τ ≃ modularPhiPoleIndices M (k.m + 1) k.n a τ :=
    { toFun := fun b => ⟨b.1.2, by
        rcases b with ⟨⟨t, p⟩, hb⟩
        cases t
        · simp [fiber, labels, hsingle] at hb
        · have hb' : p ∈ modularPhiPoleLabels M (k.m + 1) k.n ∧
              modularPhiPolePoint M (k.m + 1) k.n τ p.1 p.2 = a := by
            simpa [fiber, labels, branchPoint] using hb
          exact ⟨hb'.1, hb'.2.symm⟩⟩
      invFun := fun p => ⟨(true, p.1), by
        exact ⟨p.2.1, p.2.2.symm⟩⟩
      left_inv := by
        rintro ⟨⟨t, p⟩, hb⟩
        apply Subtype.ext
        cases t
        · simp [fiber, labels, hsingle] at hb
        · rfl
      right_inv := by intro p; rfl }
  exact Nat.card_congr eqv

lemma zeroMultiplicity_eq_zero_of_pole (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (m n : ℤ) (a τ : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hp : 0 < modularPhiPoleMultiplicity M m n a τ) :
    modularPhiZeroMultiplicity M m n a τ = 0 := by
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_pos_iff.mp hp).1
  have hempty : modularPhiZeroIndices M m n a τ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact Set.disjoint_left.mp (modularPhiDivisor_disjoint M hM m n τ hτ)
      ⟨p, hp.1, hp.2.symm⟩ ⟨q, hq.1, hq.2.symm⟩
  simp [modularPhiZeroMultiplicity, hempty]

lemma kernel_analyticAt_of_no_labels (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ z : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (hz : ∀ b ∈ labels M k, z ≠ branchPoint M k τ b) :
    AnalyticAt ℂ (fun w => kernel M k w τ) z := by
  have hreg := (regularDomain_iff_no_labels M hM k z τ).2 ⟨hτ, hz⟩
  exact (kernel_joint_analytic M hM k (z, τ) hreg).comp (f := fun w : ℂ => (w, τ))
    (show AnalyticAt ℂ (fun w : ℂ => (w, τ)) z by fun_prop)

lemma sphere_regular_of_isolated (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (r : ℝ) (hr : 0 < r)
    (hiso : ∀ b ∈ labels M k, dist (branchPoint M k τ b) a ≤ r →
      branchPoint M k τ b = a) :
    ∀ z ∈ Metric.sphere a r, (z, τ) ∈ regularDomain M k := by
  intro z hz
  apply (regularDomain_iff_no_labels M hM k z τ).2
  refine ⟨hτ, fun b hb hzb => ?_⟩
  have hdist : dist z a = r := Metric.mem_sphere.mp hz
  have hza := hiso b hb (by simpa [← hzb] using hdist.le)
  rw [← hzb] at hza
  rw [hza, dist_self] at hdist
  linarith

lemma kernel_analytic_on_isolated_disk (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M) (r : ℝ)
    (hiso : ∀ b ∈ labels M k, dist (branchPoint M k τ b) a ≤ r →
      branchPoint M k τ b = a) :
    ∀ z ∈ Metric.closedBall a r, z ≠ a → AnalyticAt ℂ (fun w => kernel M k w τ) z := by
  intro z hz hza
  apply kernel_analyticAt_of_no_labels M hM k τ z hτ
  intro b hb hzb
  exact hza (hzb.trans (hiso b hb (by simpa [← hzb] using hz)))

lemma movingCenters_finite (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (r : ℝ) (hr : 0 < r) : (movingCenters M k τ a r).Finite := by
  apply (boundedCenters_finite M hM k τ hτ (r + ‖a‖)
    (by positivity)).subset
  intro z hz
  refine ⟨?_, hz.2⟩
  calc
    ‖z‖ = ‖(z - a) + a‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - a‖ + ‖a‖ := norm_add_le _ _
    _ ≤ r + ‖a‖ := by
      gcongr
      simpa [dist_eq_norm] using hz.1.le

lemma kernel_analyticOn_closedBall_off_centers (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ a : ℂ) (hτ : τ ∈ modularPhiDomain M)
    (r : ℝ) (P : Finset ℂ) (hP : (P : Set ℂ) = movingCenters M k τ a r)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ) ∈ regularDomain M k) :
    AnalyticOnNhd ℂ (fun w => kernel M k w τ)
      (Metric.closedBall a r \ (P : Set ℂ)) := by
  intro z hz
  apply kernel_analyticAt_of_no_labels M hM k τ z hτ
  intro b hb hzb
  have hle : dist z a ≤ r := Metric.mem_closedBall.mp hz.1
  by_cases heq : dist z a = r
  · exact ((regularDomain_iff_no_labels M hM k z τ).1
      (hsafe z (Metric.mem_sphere.mpr heq))).2 b hb hzb
  · have hzin : z ∈ (P : Set ℂ) := by
      rw [hP]
      exact ⟨lt_of_le_of_ne hle heq, b, hb, hzb.symm⟩
    exact hz.2 hzin

lemma eventually_regular_sphere (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (k : KernelData) (τ₀ a : ℂ) (hτ₀ : τ₀ ∈ modularPhiDomain M) (r : ℝ)
    (hsafe : ∀ z ∈ Metric.sphere a r, (z, τ₀) ∈ regularDomain M k) :
    ∀ᶠ τ in 𝓝 τ₀, τ ∈ modularPhiDomain M ∧
      ∀ z ∈ Metric.sphere a r, (z, τ) ∈ regularDomain M k := by
  let C : Circles := ⟨{a}, fun _ => r⟩
  have hsafeC : ∀ z ∈ boundaries C, (z, τ₀) ∈ regularDomain M k := by
    rintro z ⟨b, hb, hz⟩
    have hba : b = a := Finset.mem_singleton.mp hb
    subst b
    exact hsafe z hz
  obtain ⟨ρ, hρ, hdom, hreg⟩ := exists_regular_boundary_tube M hM k τ₀ hτ₀ C hsafeC
  filter_upwards [Metric.closedBall_mem_nhds τ₀ hρ] with τ hτ
  exact ⟨hdom hτ, fun z hz => hreg τ hτ z ⟨a, by simp [C], hz⟩⟩

namespace LedgerAux

/-! ## Finite outer-circle ledger from prescribed local germs -/

theorem principalPart_continuousOn (p : ℂ) (N : ℕ) (A : ℕ → ℂ)
    {t : Set ℂ} (ht : ∀ w ∈ t, w ≠ p) :
    ContinuousOn (FinitePrincipalParts.principalPart p N A) t := by
  apply continuousOn_finsetSum
  intro j hj
  exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
    (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (ht w hw)))

theorem circleIntegral_principalPart (a p : ℂ) (r : ℝ) (N : ℕ) (A : ℕ → ℂ)
    (hr : 0 < r) (hp : dist p a < r) :
    (∮ w in C(a, r), FinitePrincipalParts.principalPart p N A w) =
      2 * (Real.pi : ℂ) * I * FinitePrincipalParts.residueCoefficient N A := by
  unfold FinitePrincipalParts.principalPart
  rw [circleIntegral.integral_fun_sum]
  · have hb (j : ℕ) :
        (∮ w in C(a, r), A j / (w - p) ^ (j + 1)) =
          A j * (if j = 0 then 2 * (Real.pi : ℂ) * I else 0) := by
      have heq : (fun w : ℂ => A j / (w - p) ^ (j + 1)) =
          (fun w : ℂ => A j * (1 / (w - p) ^ (j + 1))) := by
        ext w
        simp [div_eq_mul_inv]
      rw [heq, circleIntegral.integral_const_mul]
      congr 1
      by_cases hj : j = 0
      · simpa [hj] using (circleIntegral.integral_sub_inv_of_mem_ball hp)
      · rw [if_neg hj]
        have hn : -(↑(j + 1) : ℤ) ≠ -1 := by omega
        simpa only [zpow_neg, zpow_natCast, one_div] using
          circleIntegral.integral_sub_zpow_of_ne hn a p r
    simp_rw [hb]
    cases N with
    | zero => simp [FinitePrincipalParts.residueCoefficient]
    | succ n =>
      rw [Finset.sum_eq_single 0]
      · simp [FinitePrincipalParts.residueCoefficient, mul_comm]
      · intro b hb hb0
        simp [hb0]
      · simp
  · intro j hj
    apply ContinuousOn.circleIntegrable hr.le
    exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
      (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (by
        intro he
        subst w
        exact (ne_of_lt hp) (Metric.mem_sphere.mp hw))))

theorem outer_circle_finite_principal_parts (f g : ℂ → ℂ) (a : ℂ) (r : ℝ)
    (P : Finset ℂ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (hr : 0 < r)
    (hinside : ∀ z ∈ P, dist z a < r)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall a r))
    (hfg : ∀ z ∈ Metric.closedBall a r, z ∉ P →
      f z = FinitePrincipalParts.finitePrincipalPart P id N A z + g z) :
    FinitePrincipalParts.circleCCW a r f = 2 * (Real.pi : ℂ) * I *
      ∑ z ∈ P, FinitePrincipalParts.residueCoefficient (N z) (A z) := by
  rw [FinitePrincipalParts.circleCCW_eq_circleIntegral a r _ hr]
  have hn (w : ℂ) (hw : w ∈ Metric.sphere a r) : w ∉ P := by
    intro hwp
    exact (ne_of_lt (hinside w hwp)) (Metric.mem_sphere.mp hw)
  have hPP (z : ℂ) (hz : z ∈ P) :
      CircleIntegrable (FinitePrincipalParts.principalPart z (N z) (A z)) a r := by
    apply (principalPart_continuousOn z (N z) (A z) ?_).circleIntegrable hr.le
    intro w hw hwe
    subst w
    exact hn z hw hz
  have hFP : CircleIntegrable (FinitePrincipalParts.finitePrincipalPart P id N A) a r := by
    apply ContinuousOn.circleIntegrable hr.le
    apply continuousOn_finsetSum
    intro z hz
    exact principalPart_continuousOn z (N z) (A z) (fun w hw hwe => by
      subst w
      exact hn z hw hz)
  have hgp : CircleIntegrable g a r :=
    (hg.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hr.le
  have hgz : (∮ w in C(a, r), g w) = 0 := by
    apply DiffContOnCl.circleIntegral_eq_zero hr.le
    apply DifferentiableOn.diffContOnCl
    exact hg.differentiableOn.mono Metric.closure_ball_subset_closedBall
  calc
    _ = ∮ w in C(a, r), FinitePrincipalParts.finitePrincipalPart P id N A w + g w := by
      apply circleIntegral.integral_congr hr.le
      intro w hw
      exact hfg w (Metric.sphere_subset_closedBall hw) (hn w hw)
    _ = (∮ w in C(a, r), FinitePrincipalParts.finitePrincipalPart P id N A w) +
        ∮ w in C(a, r), g w := circleIntegral.integral_add hFP hgp
    _ = (∮ w in C(a, r), FinitePrincipalParts.finitePrincipalPart P id N A w) := by
      rw [hgz, add_zero]
    _ = _ := by
      unfold FinitePrincipalParts.finitePrincipalPart
      simp only [id_eq]
      rw [circleIntegral.integral_fun_sum hPP, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      exact circleIntegral_principalPart a z r (N z) (A z) hr (hinside z hz)

theorem principalPart_analyticAt (p : ℂ) (N : ℕ) (A : ℕ → ℂ) {w : ℂ}
    (hw : w ≠ p) : AnalyticAt ℂ (FinitePrincipalParts.principalPart p N A) w := by
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

theorem exists_regularized_remainder (f : ℂ → ℂ) (a : ℂ) (r : ℝ)
    (P : Finset ℂ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a r \ (P : Set ℂ)))
    (hA : ∀ z ∈ P, AnalyticAt ℂ (g z) z ∧
      f =ᶠ[𝓝[≠] z] (fun w => FinitePrincipalParts.principalPart z (N z) (A z) w + g z w)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (Metric.closedBall a r) ∧
      ∀ w ∈ Metric.closedBall a r, w ∉ P →
        f w = FinitePrincipalParts.finitePrincipalPart P id N A w + H w := by
  classical
  let q : ℂ → ℂ := fun w => f w - FinitePrincipalParts.finitePrincipalPart P id N A w
  let H : ℂ → ℂ := fun w => if w ∈ P then limUnder (𝓝[≠] w) q else q w
  have hHoff (w : ℂ) (hw : w ∉ P) : H w = q w := by simp [H, hw]
  have hHcenter (z : ℂ) (hz : z ∈ P) : AnalyticAt ℂ H z := by
    let L : ℂ → ℂ := fun w => g z w -
      ∑ j ∈ P.erase z, FinitePrincipalParts.principalPart j (N j) (A j) w
    have hLana : AnalyticAt ℂ L z := by
      apply (hA z hz).1.sub
      apply Finset.analyticAt_fun_sum
      intro j hj
      exact principalPart_analyticAt j (N j) (A j) (Ne.symm (Finset.mem_erase.mp hj).1)
    have hqL : q =ᶠ[𝓝[≠] z] L := by
      filter_upwards [(hA z hz).2] with w hw
      dsimp only [q, L, FinitePrincipalParts.finitePrincipalPart, id_eq]
      rw [hw, ← Finset.sum_erase_add P
        (fun j => FinitePrincipalParts.principalPart j (N j) (A j) w) hz]
      ring
    have hlim : Tendsto q (𝓝[≠] z) (𝓝 (L z)) :=
      (hLana.continuousAt.tendsto.mono_left inf_le_left).congr' hqL.symm
    have hvalue : H z = L z := by
      dsimp only [H]
      rw [if_pos hz]
      exact hlim.limUnder_eq
    have havoid : ∀ᶠ w in 𝓝 z, w ∉ P.erase z :=
      (P.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    apply hLana.congr
    filter_upwards [havoid, eventually_nhdsWithin_iff.mp hqL] with w hw hqLw
    by_cases he : w = z
    · simpa only [he] using hvalue.symm
    · have hwp : w ∉ P := by
        intro hwp
        exact hw (Finset.mem_erase.mpr ⟨he, hwp⟩)
      rw [hHoff w hwp, hqLw he]
  refine ⟨H, ?_, ?_⟩
  · intro w hw
    by_cases hwp : w ∈ P
    · exact hHcenter w hwp
    · have hqana : AnalyticAt ℂ q w := by
        apply (hf w ⟨hw, hwp⟩).sub
        apply Finset.analyticAt_fun_sum
        intro z hz
        apply principalPart_analyticAt
        intro he
        exact hwp (he ▸ hz)
      apply hqana.congr
      filter_upwards [P.finite_toSet.isClosed.isOpen_compl.mem_nhds hwp] with z hz
      exact (hHoff z hz).symm
  · intro w hw hwp
    rw [hHoff w hwp]
    dsimp [q]
    ring

theorem circle_finite_prescribed_germs (f : ℂ → ℂ) (a : ℂ) (r : ℝ)
    (P : Finset ℂ) (N : ℂ → ℕ) (A : ℂ → ℕ → ℂ) (g : ℂ → ℂ → ℂ)
    (hr : 0 < r) (hinside : ∀ z ∈ P, dist z a < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a r \ (P : Set ℂ)))
    (hA : ∀ z ∈ P, AnalyticAt ℂ (g z) z ∧
      f =ᶠ[𝓝[≠] z] (fun w => FinitePrincipalParts.principalPart z (N z) (A z) w + g z w)) :
    FinitePrincipalParts.circleCCW a r f = 2 * (Real.pi : ℂ) * I *
      ∑ z ∈ P, FinitePrincipalParts.residueCoefficient (N z) (A z) := by
  obtain ⟨H, hH, hfH⟩ := exists_regularized_remainder f a r P N A g hf hA
  exact outer_circle_finite_principal_parts f H a r P N A hr hinside hH hfH

/-! ## Principal-part extraction with a sharp leading coefficient -/

open FinitePrincipalParts

theorem analytic_dslope_at {h : ℂ → ℂ} {a : ℂ} (hh : AnalyticAt ℂ h a) :
    AnalyticAt ℂ (dslope h a) a := by
  obtain ⟨p, hp⟩ := hh
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem analytic_quotient_principalPart (h : ℂ → ℂ) (a : ℂ) (N : ℕ)
    (hh : AnalyticAt ℂ h a) :
    ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g a ∧
      (0 < N → A (N - 1) = h a) ∧
      ∀ z : ℂ, z ≠ a → h z / (z - a) ^ N = principalPart a N A z + g z := by
  induction N generalizing h with
  | zero =>
      exact ⟨fun _ => 0, h, hh, by simp, by simp [principalPart]⟩
  | succ N ih =>
      obtain ⟨B, g, hg, hB, hEq⟩ := ih (dslope h a) (analytic_dslope_at hh)
      let A : ℕ → ℂ := fun j => if j = N then h a else B j
      refine ⟨A, g, hg, ?_, ?_⟩
      · simp [A]
      · intro z hz
        have hpp : principalPart a (N + 1) A z =
            principalPart a N B z + h a / (z - a) ^ (N + 1) := by
          simp only [principalPart, Finset.sum_range_succ]
          have hs : (∑ j ∈ Finset.range N, A j / (z - a) ^ (j + 1)) =
              ∑ j ∈ Finset.range N, B j / (z - a) ^ (j + 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjN : j ≠ N := Nat.ne_of_lt (Finset.mem_range.mp hj)
            simp [A, hjN]
          rw [hs]
          simp [A]
        rw [hpp, add_right_comm, ← hEq z hz]
        have hd : (z - a) * dslope h a z = h z - h a := by
          simpa only [smul_eq_mul] using sub_smul_dslope h a z
        have hnz : z - a ≠ 0 := sub_ne_zero.mpr hz
        rw [pow_succ]
        field_simp
        linear_combination -hd

theorem regularized_numerator (f : ℂ → ℂ) (a : ℂ) (N : ℕ) (n : ℤ)
    (hf : MeromorphicAt f a) (ho : meromorphicOrderAt f a = (n : WithTop ℤ))
    (hbound : -(N : ℤ) ≤ n) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      ((fun z => (z - a) ^ N * f z) =ᶠ[𝓝[≠] a] h) ∧
      (n = -(N : ℤ) → h a ≠ 0) := by
  let F : ℂ → ℂ := fun z => (z - a) ^ N * f z
  have hF : MeromorphicAt F a := by
    exact ((analyticAt_id.sub analyticAt_const).pow N).meromorphicAt.fun_mul hf
  have hFo : meromorphicOrderAt F a = ((N : ℤ) + n : ℤ) := by
    change meromorphicOrderAt (((fun z : ℂ => z - a) ^ N) * f) a = _
    rw [meromorphicOrderAt_mul (by fun_prop) hf, meromorphicOrderAt_pow_id_sub_const, ho]
    simp
  have hnonneg : 0 ≤ meromorphicOrderAt F a := by
    rw [hFo]
    exact WithTop.coe_nonneg.mpr (by omega)
  obtain ⟨h, hh, hFh⟩ := hF.meromorphicOrderAt_nonneg_iff.mp hnonneg
  refine ⟨h, hh, hFh, ?_⟩
  intro hn
  have hhorder : meromorphicOrderAt h a = 0 := by
    rw [← meromorphicOrderAt_congr hFh, hFo, hn]
    simp
  rw [← hh.analyticOrderAt_eq_zero, ← ENat.map_natCast_eq_zero (α := ℤ),
    ← hh.meromorphicOrderAt_eq]
  exact hhorder

theorem extend_remainder (f : ℂ → ℂ) (a : ℂ) (N : ℕ) (A : ℕ → ℂ)
    (g₀ : ℂ → ℂ) (hg₀ : AnalyticAt ℂ g₀ a)
    (hfg₀ : f =ᶠ[𝓝[≠] a] fun z => principalPart a N A z + g₀ z)
    (s : Set ℂ) (hf : ∀ z ∈ s, z ≠ a → AnalyticAt ℂ f z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g s ∧
      ∀ z ∈ s, z ≠ a → f z = principalPart a N A z + g z := by
  let g : ℂ → ℂ := fun z => if z = a then g₀ a else f z - principalPart a N A z
  have hgg₀ : g =ᶠ[𝓝 a] g₀ := by
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · filter_upwards [hfg₀, self_mem_nhdsWithin] with z hz hza
      have hne : z ≠ a := by simpa using hza
      simp [g, hne, hz]
    · simp [g]
  refine ⟨g, ?_, ?_⟩
  · intro z hzs
    by_cases hza : z = a
    · subst z
      exact hg₀.congr hgg₀.symm
    · apply ((hf z hzs hza).sub (principalPart_analyticAt a N A hza)).congr
      filter_upwards [eventually_ne_nhds hza] with w hw
      simp [g, hw]
  · intro z hzs hza
    simp [g, hza]

theorem principalPart_extraction (f : ℂ → ℂ) (a : ℂ) (N : ℕ) (n : ℤ)
    (hf : MeromorphicAt f a) (ho : meromorphicOrderAt f a = (n : WithTop ℤ))
    (hbound : -(N : ℤ) ≤ n) (s : Set ℂ)
    (hs : ∀ z ∈ s, z ≠ a → AnalyticAt ℂ f z) :
    ∃ (A : ℕ → ℂ) (g : ℂ → ℂ),
      (n = -(N : ℤ) → 0 < N → A (N - 1) ≠ 0) ∧
      AnalyticOnNhd ℂ g s ∧
      ∀ z ∈ s, z ≠ a → f z = principalPart a N A z + g z := by
  obtain ⟨h, hh, hFh, hhne⟩ := regularized_numerator f a N n hf ho hbound
  obtain ⟨A, g₀, hg₀, hA, hEq⟩ := analytic_quotient_principalPart h a N hh
  have hfg₀ : f =ᶠ[𝓝[≠] a] fun z => principalPart a N A z + g₀ z := by
    filter_upwards [hFh, self_mem_nhdsWithin] with z hz hza
    have hne : z ≠ a := by simpa using hza
    calc
      f z = h z / (z - a) ^ N := by
        rw [← hz]
        field_simp
      _ = principalPart a N A z + g₀ z := hEq z hne
  obtain ⟨g, hg, hfg⟩ := extend_remainder f a N A g₀ hg₀ hfg₀ s hs
  refine ⟨A, g, ?_, hg, hfg⟩
  intro hn hN
  rw [hA hN]
  exact hhne hn

theorem principalPart_germ (f : ℂ → ℂ) (a : ℂ) (N : ℕ) (n : ℤ)
    (hf : MeromorphicAt f a) (ho : meromorphicOrderAt f a = (n : WithTop ℤ))
    (hbound : -(N : ℤ) ≤ n) :
    ∃ (A : ℕ → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g a ∧
      f =ᶠ[𝓝[≠] a] (fun z => principalPart a N A z + g z) := by
  obtain ⟨h, hh, hFh, _⟩ := regularized_numerator f a N n hf ho hbound
  obtain ⟨A, g, hg, _, hEq⟩ := analytic_quotient_principalPart h a N hh
  refine ⟨A, g, hg, ?_⟩
  filter_upwards [hFh, self_mem_nhdsWithin] with z hz hza
  have hne : z ≠ a := by simpa using hza
  calc
    f z = h z / (z - a) ^ N := by rw [← hz]; field_simp
    _ = principalPart a N A z + g z := hEq z hne

end LedgerAux

end SICLean.L4.ModularCluster
