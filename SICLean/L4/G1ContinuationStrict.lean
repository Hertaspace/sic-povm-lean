import SICLean.L4.G1ContinuationHolomorphy
import SICLean.L4.G1ContinuationEndRotation
import SICLean.L4.G1ContinuationStrictAux

set_option autoImplicit false

/-!
# Upper-half-plane identities on every strict target window

The theorems identify the strict-window integrals and their joint charts. The comparison
statements retain their explicitly divisor-free loci. There is no limUnder, removable-value
declaration, or claim of G1RealConclusion in this block. Joint ordinary-neighborhood exports include
targets on apparent RHS divisors; only the comparison points are required to be divisor-free.

[RW26, p. 28, (55), (56), (58), p. 29]. The topological, joint-holomorphy, and chain-assignment
steps are proved in this file.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G1Continuation

def singleGood (M : SL(2, ℤ)) (h ell : ℤ) : Set (ℂ × ℂ) :=
  {u | (u.2, u.1) ∈ modularPhiNonvanishingDomain M ell (1 - h)}

def ratioGood (M : SL(2, ℤ)) (h ell p : ℤ) : Set Parameters :=
  {x | (x.2.1 + x.2.2, x.1) ∈ modularPhiNonvanishingDomain M (p + ell) (-h) ∧
    (x.2.2, x.1) ∈ modularPhiNonvanishingDomain M p 0 ∧
    (x.2.1, x.1) ∈ modularPhiNonvanishingDomain M ell (1 - h)}

def singleRaw (M : SL(2, ℤ)) (h ell : ℤ) (u : ℂ × ℂ) : ℂ :=
  (modularPhi M ell (1 - h) u.2 u.1)⁻¹

def ratioRaw (M : SL(2, ℤ)) (h ell p : ℤ) (x : Parameters) : ℂ :=
  modularPhi M (p + ell) (-h) (x.2.1 + x.2.2) x.1 /
    (modularPhi M p 0 x.2.2 x.1 * modularPhi M ell (1 - h) x.2.1 x.1)

def singleBentSum (M : SL(2, ℤ)) (x : Fin (M 1 0).toNat → ℝ)
    (n h ell : ℤ) (ψ : ℝ) (u : ℂ × ℂ) : ℂ :=
  ∑ m : Fin (M 1 0).toNat, singleBentValue M n h ell (m : ℤ) (x m) ψ u

/-- S01. Fixed-τ density is needed even when an entire τ fiber is singular. [RW26, p. 29]. Density
is not a premise of continuation. -/
theorem single_good_open_dense_fibers (M : SL(2, ℤ)) (hM : 0 < M 1 0) (h ell : ℤ) :
    IsOpen (singleGood M h ell) ∧ ∀ τ ∈ modularPhiDomain M,
      Dense {w : ℂ | (τ, w) ∈ singleGood M h ell} := by
  constructor
  · exact ((modularPhiDivisor_domains_isOpen M hM ell (1 - h)).2).preimage
      (show Continuous (fun u : ℂ × ℂ => (u.2, u.1)) by fun_prop)
  · intro τ hτ
    exact G1ContinuationStrictAux.unitFiber_dense M ell (1 - h) τ hτ

/-- S02. The three affine Φ factors have a dense common fixed-τ unit locus. [RW26, p. 29]. No ℂ²
puncture is substituted for divisor exclusion. -/
theorem ratio_good_open_dense_fibers (M : SL(2, ℤ)) (hM : 0 < M 1 0) (h ell p : ℤ) :
    IsOpen (ratioGood M h ell p) ∧ ∀ τ ∈ modularPhiDomain M,
      Dense {v : ℂ × ℂ | (τ, v) ∈ ratioGood M h ell p} := by
  constructor
  · change IsOpen
      ((fun x : Parameters => (x.2.1 + x.2.2, x.1)) ⁻¹'
        modularPhiNonvanishingDomain M (p + ell) (-h) ∩
      ((fun x : Parameters => (x.2.2, x.1)) ⁻¹'
        modularPhiNonvanishingDomain M p 0 ∩
      (fun x : Parameters => (x.2.1, x.1)) ⁻¹'
        modularPhiNonvanishingDomain M ell (1 - h)))
    exact (((modularPhiDivisor_domains_isOpen M hM (p + ell) (-h)).2).preimage
      (by fun_prop)).inter
      ((((modularPhiDivisor_domains_isOpen M hM p 0).2).preimage
        (by fun_prop)).inter
        (((modularPhiDivisor_domains_isOpen M hM ell (1 - h)).2).preimage
          (by fun_prop)))
  · intro τ hτ
    let S : ℤ → ℤ → Set ℂ := fun m n =>
      {z | (z, τ) ∈ modularPhiNonvanishingDomain M m n}
    have hd (m n : ℤ) : Dense (S m n) :=
      G1ContinuationStrictAux.unitFiber_dense M m n τ hτ
    have ho (m n : ℤ) : IsOpen (S m n) :=
      ((modularPhiDivisor_domains_isOpen M hM m n).2).preimage
        (show Continuous (fun z : ℂ => (z, τ)) by fun_prop)
    have hsum : IsOpenMap (fun v : ℂ × ℂ => v.1 + v.2) := by
      simpa [Function.comp_def] using
        isOpenMap_snd.comp (Homeomorph.shearAddRight ℂ).isOpenMap
    have h₁ : Dense
        ((fun v : ℂ × ℂ => v.1 + v.2) ⁻¹' S (p + ell) (-h)) :=
      (hd _ _).preimage hsum
    have h₂ : Dense ((Prod.snd : ℂ × ℂ → ℂ) ⁻¹' S p 0) :=
      (hd _ _).preimage isOpenMap_snd
    have h₃ : Dense ((Prod.fst : ℂ × ℂ → ℂ) ⁻¹' S ell (1 - h)) :=
      (hd _ _).preimage isOpenMap_fst
    exact h₁.inter_of_isOpen_left
      (h₂.inter_of_isOpen_left h₃ ((ho _ _).preimage continuous_snd))
      ((ho _ _).preimage (by fun_prop))

/-- S03. The rotated seed agrees as an ordinary joint germ, not a z-punctured germ. [RW26, p. 28,
(55), (56), p. 29]. -/
theorem single_rotated_seed_germ (M : SL(2, ℤ)) (n h ell : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (u : ℂ × ℂ)
    (hu : u ∈ UpperIntegralIdentities.singleDomain M h ell ψ σ ρ δ) :
    ∃ x : Fin (M 1 0).toNat → ℝ,
      (∀ m : Fin (M 1 0).toNat, u ∈ singleAdmissible M n h ell (m : ℤ) (x m) ψ) ∧
      singleBentSum M x n h ell ψ =ᶠ[𝓝 u]
        (fun v => UpperResidueParameters.prefactor M v.1 * singleRaw M h ell v) := by
  obtain ⟨x, hx, _⟩ := single_seed_end_rotation M n h ell ψ σ ρ δ hc u hu
  have hutube : u ∈ singleTube M h ell ψ :=
    ⟨hu.1, (initial_fibers_inside_target M n h ell 0 ψ σ ρ δ hc u.1 hu.1).2.1 u.2 hu⟩
  have hτ := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 u.1 hu.1
  have hreg : ∀ m : Fin (M 1 0).toNat,
      u ∈ singleAdmissible M n h ell (m : ℤ) (x m) ψ := by
    intro m
    refine ⟨hτ.1, hτ.2.2.1, hc.2.1, hc.2.2.1, ?_, hutube.2, hx m⟩
    rw [abs_of_pos hu.1.2.1]
    exact hu.1.2.2
  refine ⟨x, hreg, ?_⟩
  have hAd : (⋂ m : Fin (M 1 0).toNat,
      singleAdmissible M n h ell (m : ℤ) (x m) ψ) ∈ 𝓝 u := by
    exact Filter.iInter_mem.mpr fun (m : Fin (M 1 0).toNat) =>
      (single_bent_joint_analytic M hc.1 n h ell (m : ℤ) (x m) ψ).1.mem_nhds (hreg m)
  filter_upwards [(UpperIntegralIdentities.initial_domains_open_nonempty
    M h ell 0 ψ σ ρ δ hc).1.mem_nhds hu, hAd] with v hv hvAd
  have hvtube : v ∈ singleTube M h ell ψ :=
    ⟨hv.1, (initial_fibers_inside_target M n h ell 0 ψ σ ρ δ hc v.1 hv.1).2.1 v.2 hv⟩
  obtain ⟨x₁, hx₁, hval⟩ := single_seed_end_rotation M n h ell ψ σ ρ δ hc v hv
  exact (G1ContinuationStrictAux.single_bent_crossing_invariance M hc.1 n h ell ψ
    hc.2.1 hc.2.2.1 v hvtube x x₁
    (fun m => (mem_iInter.mp hvAd m).2.2.2.2.2.2) hx₁).trans
      (hval.trans (UpperIntegralIdentities.upper_single M n h ell ψ σ ρ δ hc v hv).2)

/-- S04. Same seed-germ identification after both ratio rotations. [RW26, p. 28, (58), p. 29]. -/
theorem ratio_rotated_seed_germ (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (x : Parameters)
    (hx : x ∈ UpperWindow.domain M h ell p ψ σ ρ δ) :
    ∃ D : Fin (M 1 0).toNat → CircleExtension,
      (∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) ∧
      ratioExtensionSum M D n h ell p =ᶠ[𝓝 x]
        (fun v => UpperResidueParameters.prefactor M v.1 * ratioRaw M h ell p v) := by
  simpa only [singleRaw, ratioRaw, G1ContinuationStrictAux.ratioExpression] using
    G1ContinuationStrictAux.ratio_rotated_seed_germ M n h ell p ψ σ ρ δ hc x hx

/-- S05. Single contours with the same right-hand pole allocation agree. [RW26, p. 29]. The lower
connectors are translations of bent tails, not vertical rays. -/
theorem single_bent_crossing_invariance (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hu : u ∈ singleTube M h ell ψ)
    (x₀ x₁ : Fin (M 1 0).toNat → ℝ)
    (h₀ : ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x₀ m) ψ)
    (h₁ : ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x₁ m) ψ) :
    singleBentSum M x₀ n h ell ψ u = singleBentSum M x₁ n h ell ψ u := by
  exact G1ContinuationStrictAux.single_bent_crossing_invariance
    M hM n h ell ψ hψ hψ' u hu x₀ x₁ h₀ h₁

/-- S06. Joint single-valued analytic gluing, with no one-family pinches. [RW26, p. 29]. -/
theorem single_global_analytic_value (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4) :
    ∃ F : (ℂ × ℂ) → ℂ, AnalyticOnNhd ℂ F (singleTube M h ell ψ) ∧
      ∀ u ∈ singleTube M h ell ψ,
        (∃ x : Fin (M 1 0).toNat → ℝ, ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x m) ψ) ∧
        ∀ x : Fin (M 1 0).toNat → ℝ,
          (∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x m) ψ) →
            singleBentSum M x n h ell ψ u = F u := by
  have hcR : (0 : ℝ) < M 1 0 := by exact_mod_cast hM
  let δ : ℝ := 1 / (8 * (M 1 0 : ℝ))
  have hc : UpperWindow.Choices M ψ (1 / 4) (1 / 4) δ := by
    refine ⟨hM, hψ, hψ', by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · dsimp [δ]; positivity
    · dsimp [δ]
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * (M 1 0 : ℝ)) hcR]
      nlinarith
  have hex : ∀ u ∈ singleTube M h ell ψ,
      ∃ x : Fin (M 1 0).toNat → ℝ,
        ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x m) ψ := by
    intro u hu
    obtain ⟨w, hw⟩ := (initial_fibers_inside_target M n h ell 0 ψ (1/4) (1/4) δ hc u.1 hu.1).1
    obtain ⟨x, hx, _⟩ := single_seed_end_rotation M n h ell ψ (1/4) (1/4) δ hc (u.1, w) hw
    exact ⟨x, hx⟩
  let crosses : (ℂ × ℂ) → (Fin (M 1 0).toNat → ℝ) := fun u =>
    if hu : u ∈ singleTube M h ell ψ then (hex u hu).choose else fun _ => 0
  have hcrosses (u : ℂ × ℂ) (hu : u ∈ singleTube M h ell ψ) :
      ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (crosses u m) ψ := by
    simpa only [crosses, dif_pos hu] using (hex u hu).choose_spec
  let F : (ℂ × ℂ) → ℂ := fun u => singleBentSum M (crosses u) n h ell ψ u
  have hvalue (u : ℂ × ℂ) (hu : u ∈ singleTube M h ell ψ)
      (x : Fin (M 1 0).toNat → ℝ)
      (hx : ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x m) ψ) :
      singleBentSum M x n h ell ψ u = F u :=
    single_bent_crossing_invariance M hM n h ell ψ hψ hψ' u hu x (crosses u) hx (hcrosses u hu)
  refine ⟨F, ?_, fun u hu => ⟨hex u hu, hvalue u hu⟩⟩
  intro u hu
  let x := crosses u
  have hreg : ∀ m : Fin (M 1 0).toNat, u ∈ singleAdmissible M n h ell (m : ℤ) (x m) ψ := by
    intro m
    have hτ := UpperWindow.tauRegion_properties M hM ψ hψ' u.1 hu.1
    refine ⟨hτ.1, hτ.2.2.1, hψ, hψ', ?_, hu.2, hcrosses u hu m⟩
    rw [abs_of_pos hu.1.2.1]
    exact hu.1.2.2
  let U : Set (ℂ × ℂ) := singleTube M h ell ψ ∩
    ⋂ m : Fin (M 1 0).toNat, singleAdmissible M n h ell (m : ℤ) (x m) ψ
  have hU : U ∈ 𝓝 u := by
    have htube : singleTube M h ell ψ ∈ 𝓝 u := by
      have hτopen : IsOpen {v : ℂ × ℂ | v.1 ∈ UpperWindow.tauRegion M ψ} :=
        (UpperWindow.tauRegion_isOpen M hM ψ).preimage continuous_fst
      have hAd := (single_bent_joint_analytic M hM n h ell (0 : ℤ) (x ⟨0, by omega⟩) ψ).1
      have hm0 := hreg ⟨0, by omega⟩
      filter_upwards [hτopen.mem_nhds hu.1, hAd.mem_nhds hm0] with v hvτ hvAd
      exact ⟨hvτ, hvAd.2.2.2.2.2.1⟩
    apply Filter.inter_mem htube
    exact Filter.mem_of_superset (Filter.iInter_mem.mpr fun (m : Fin (M 1 0).toNat) =>
      (single_bent_joint_analytic M hM n h ell (m : ℤ) (x m) ψ).1.mem_nhds (hreg m)) (by exact fun _ hv => hv)
  have hsum : AnalyticAt ℂ (singleBentSum M x n h ell ψ) u := by
    unfold singleBentSum
    apply Finset.analyticAt_fun_sum
    intro m hm
    exact (single_bent_joint_analytic M hM n h ell (m : ℤ) (x m) ψ).2.1 u (hreg m)
  apply hsum.congr
  filter_upwards [hU] with v hv
  exact hvalue v hv.1 x (fun m => (mem_iInter.mp hv.2 m).2.2.2.2.2.2)

/-- S07. All strict w, arbitrary integers, same upper_single RHS and q-prefactor. [RW26, p. 28,
(55), (56), p. 29]. -/
theorem upper_single_all_strict (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hu : u ∈ singleTube M h ell ψ) (hgood : u ∈ singleGood M h ell)
    (x : Fin (M 1 0).toNat → ℝ)
    (hx : ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x m) ψ) :
    (∀ m : Fin (M 1 0).toNat,
      G1BentIntegrable (UpperWindow.singleKernel M (m : ℤ) n h ell u.1 u.2) (x m) ψ) ∧
      singleBentSum M x n h ell ψ u =
        UpperResidueParameters.prefactor M u.1 * singleRaw M h ell u := by
  have hτ := UpperWindow.tauRegion_properties M hM ψ hψ' u.1 hu.1
  have hreg : ∀ m : Fin (M 1 0).toNat,
      u ∈ singleAdmissible M n h ell (m : ℤ) (x m) ψ := by
    intro m
    refine ⟨hτ.1, hτ.2.2.1, hψ, hψ', ?_, hu.2, hx m⟩
    rw [abs_of_pos hu.1.2.1]
    exact hu.1.2.2
  refine ⟨fun m => (single_bent_joint_analytic M hM n h ell (m : ℤ) (x m) ψ).2.2 u (hreg m), ?_⟩
  let δ : ℝ := 1 / (8 * (M 1 0 : ℝ))
  have hc := G1ContinuationStrictAux.canonical_choices M hM ψ hψ hψ'
  have hR : AnalyticOnNhd ℂ
      (fun w : ℂ => UpperResidueParameters.prefactor M u.1 *
        (modularPhi M ell (1 - h) w u.1)⁻¹) (singleWindow M u.1 h ell) := by
    intro w hw
    exact analyticAt_const.mul (G1ContinuationStrictAux.single_raw_slice_analytic
      M hM h ell u.1 hgood.1 hτ.2.2.1 w hw)
  have hcross : ∀ v ∈ singleTube M h ell ψ,
      ∀ x₀ x₁ : Fin (M 1 0).toNat → ℝ,
      (∀ m : Fin (M 1 0).toNat, BentClear M v.1 n (m : ℤ) (x₀ m) ψ) →
      (∀ m : Fin (M 1 0).toNat, BentClear M v.1 n (m : ℤ) (x₁ m) ψ) →
      G1ContinuationStrictAux.singleSum M x₀ n h ell ψ v =
        G1ContinuationStrictAux.singleSum M x₁ n h ell ψ v := by
    intro v hv x₀ x₁ hx₀ hx₁
    exact single_bent_crossing_invariance M hM n h ell ψ hψ hψ' v hv x₀ x₁ hx₀ hx₁
  have he := G1ContinuationStrictAux.single_continuation_unique_of_crossing M n h ell ψ
    (1/4) (1/4) δ hc hcross u.1 hu.1
    (fun w : ℂ => UpperResidueParameters.prefactor M u.1 * (modularPhi M ell (1-h) w u.1)⁻¹)
    hR (fun _ _ => rfl) u.2 hu.2 x hx
  exact he.symm

/-- S08. All strict no-pinch (w,y), arbitrary indices, every pole allocation representative. [RW26,
p. 28, (58), p. 29]. -/
theorem upper_ratio_all_strict (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (hgood : x ∈ ratioGood M h ell p)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    (∀ m, ExtensionIntegrable (D m)
      (UpperWindow.ratioKernel M (m : ℤ) n h ell p x.1 x.2.1 x.2.2)) ∧
      ratioExtensionSum M D n h ell p x =
        UpperResidueParameters.prefactor M x.1 * ratioRaw M h ell p x := by
  refine ⟨ratio_extension_integrable M hM n h ell p ψ hψ hψ' x hx D hD, ?_⟩
  exact G1ContinuationStrictAux.upper_ratio_all_strict_value M hM n h ell p ψ hψ hψ' x hx D hD

/-- S09. Joint ordinary-neighborhood comparison even at an apparent RHS divisor. Only comparison
points are on singleGood. [RW26, p. 29]. Removable values remain separate. -/
theorem single_strict_joint_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (u : ℂ × ℂ) (hu : u ∈ singleTube M h ell ψ)
    (x : Fin (M 1 0).toNat → ℝ)
    (hx : ∀ m : Fin (M 1 0).toNat, BentClear M u.1 n (m : ℤ) (x m) ψ) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ u ∈ U ∧ U ⊆ singleTube M h ell ψ ∧
      AnalyticOnNhd ℂ (singleBentSum M x n h ell ψ) U ∧
      ∀ v ∈ U ∩ singleGood M h ell,
        singleBentSum M x n h ell ψ v =
          UpperResidueParameters.prefactor M v.1 * singleRaw M h ell v := by
  have hτ := UpperWindow.tauRegion_properties M hM ψ hψ' u.1 hu.1
  have hreg : ∀ m : Fin (M 1 0).toNat, u ∈ singleAdmissible M n h ell (m : ℤ) (x m) ψ := by
    intro m
    refine ⟨hτ.1, hτ.2.2.1, hψ, hψ', ?_, hu.2, hx m⟩
    rw [abs_of_pos hu.1.2.1]
    exact hu.1.2.2
  let U : Set (ℂ × ℂ) := {v | v.1 ∈ UpperWindow.tauRegion M ψ} ∩
    ⋂ m : Fin (M 1 0).toNat, singleAdmissible M n h ell (m : ℤ) (x m) ψ
  have hU : IsOpen U :=
    ((UpperWindow.tauRegion_isOpen M hM ψ).preimage continuous_fst).inter
      (isOpen_iInter_of_finite fun m => (single_bent_joint_analytic M hM n h ell (m : ℤ) (x m) ψ).1)
  have hsub : U ⊆ singleTube M h ell ψ := by
    intro v hv
    exact ⟨hv.1, (mem_iInter.mp hv.2 (⟨0, by omega⟩ : Fin (M 1 0).toNat)).2.2.2.2.2.1⟩
  refine ⟨U, hU, ⟨hu.1, mem_iInter.mpr hreg⟩, hsub, ?_, ?_⟩
  · intro v hv
    unfold singleBentSum
    apply Finset.analyticAt_fun_sum
    intro m hm
    exact (single_bent_joint_analytic M hM n h ell (m : ℤ) (x m) ψ).2.1 v (mem_iInter.mp hv.2 m)
  · intro v hv
    exact (upper_single_all_strict M hM n h ell ψ hψ hψ' v (hsub hv.1) hv.2 x
      (fun m => (mem_iInter.mp hv.1.2 m).2.2.2.2.2.2)).2

/-- S10. Corresponding joint chart for a fixed transported ratio chain. [RW26, p. 29]. No fixed-τ
meromorphy is substituted for joint holomorphy. -/
theorem ratio_strict_joint_neighborhood (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ∃ U : Set Parameters, IsOpen U ∧ x ∈ U ∧ U ⊆ ratioTube M n h ell p ψ ∧
      AnalyticOnNhd ℂ (ratioExtensionSum M D n h ell p) U ∧
      ∀ v ∈ U ∩ ratioGood M h ell p,
        ratioExtensionSum M D n h ell p v =
          UpperResidueParameters.prefactor M v.1 * ratioRaw M h ell p v := by
  obtain ⟨U, hU, hxU, hsub, hA, hsep⟩ :=
    ratio_extension_joint_analytic M hM n h ell p ψ hψ hψ' x hx D hD
  exact ⟨U, hU, hxU, hsub, hA, fun v hv =>
    (upper_ratio_all_strict M hM n h ell p ψ hψ hψ' v (hsub hv.1) hv.2 D (hsep v hv.1)).2⟩

/-- S11. The initial nonempty fiber determines the single continuation uniquely. [RW26, p. 29]. -/
theorem single_continuation_unique (M : SL(2, ℤ)) (n h ell : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (τ : ℂ)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F (singleWindow M τ h ell))
    (hseed : ∀ w, (τ, w) ∈ UpperIntegralIdentities.singleDomain M h ell ψ σ ρ δ →
      F w = UpperResidueParameters.prefactor M τ * singleRaw M h ell (τ, w)) :
    ∀ w ∈ singleWindow M τ h ell, ∀ x : Fin (M 1 0).toNat → ℝ,
      (∀ m : Fin (M 1 0).toNat, BentClear M τ n (m : ℤ) (x m) ψ) →
        F w = singleBentSum M x n h ell ψ (τ, w) := by
  intro w hw x hx
  have hτprop := UpperWindow.tauRegion_properties M hc.1 ψ hc.2.2.1 τ hτ
  have hG : AnalyticOnNhd ℂ (fun z : ℂ => singleBentSum M x n h ell ψ (τ, z))
      (singleWindow M τ h ell) := by
    intro z hz
    unfold singleBentSum
    apply Finset.analyticAt_fun_sum
    intro m hm
    have hreg : (τ, z) ∈ singleAdmissible M n h ell (m : ℤ) (x m) ψ := by
      refine ⟨hτprop.1, hτprop.2.2.1, hc.2.1, hc.2.2.1, ?_, hz, hx m⟩
      rw [abs_of_pos hτ.2.1]
      exact hτ.2.2
    exact ((single_bent_joint_analytic M hc.1 n h ell (m : ℤ) (x m) ψ).2.1 _ hreg).comp
      (f := fun z : ℂ => (τ, z)) (x := z) (analyticAt_const.prod analyticAt_id)
  obtain ⟨U, hU, ⟨z₀, hz₀⟩, hUseed⟩ :=
    (UpperIntegralIdentities.initial_fibers M h ell 0 ψ σ ρ δ hc τ hτ).1
  have hEqSeed : ∀ z ∈ U, F z = singleBentSum M x n h ell ψ (τ, z) := by
    intro z hz
    have hzseed := hUseed z hz
    have hztube : (τ, z) ∈ singleTube M h ell ψ :=
      ⟨hτ, (initial_fibers_inside_target M n h ell 0 ψ σ ρ δ hc τ hτ).2.1 z hzseed⟩
    obtain ⟨x₀, hx₀, hval⟩ := single_seed_end_rotation M n h ell ψ σ ρ δ hc (τ, z) hzseed
    have hcross := single_bent_crossing_invariance M hc.1 n h ell ψ hc.2.1 hc.2.2.1
      (τ, z) hztube x x₀ hx hx₀
    exact (hseed z hzseed).trans
      (((UpperIntegralIdentities.upper_single M n h ell ψ σ ρ δ hc (τ, z) hzseed).2).symm.trans
        (hval.symm.trans hcross.symm))
  apply hF.eqOn_of_preconnected_of_eventuallyEq hG
    (single_window_open_convex M τ h ell).2.isPreconnected
    ((initial_fibers_inside_target M n h ell 0 ψ σ ρ δ hc τ hτ).2.1 z₀ (hUseed z₀ hz₀))
    (Filter.mem_of_superset (hU.mem_nhds hz₀) fun z hz => hEqSeed z hz) hw

/-- S12. Uniqueness after detours: no chosen path or branch is a premise. [RW26, p. 29]. -/
theorem ratio_continuation_unique (M : SL(2, ℤ)) (n h ell p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : UpperWindow.Choices M ψ σ ρ δ) (τ : ℂ)
    (hτ : τ ∈ UpperWindow.tauRegion M ψ) (F : (ℂ × ℂ) → ℂ)
    (hF : AnalyticOnNhd ℂ F (ratioFiber M τ n h ell p))
    (hseed : ∀ v, (τ, v) ∈ UpperWindow.domain M h ell p ψ σ ρ δ →
      F v = UpperResidueParameters.prefactor M τ * ratioRaw M h ell p (τ, v)) :
    ∀ v ∈ ratioFiber M τ n h ell p,
      ∀ D : Fin (M 1 0).toNat → CircleExtension,
      (∀ m, SeparatesExtension (D m) M τ v.2 n p (m : ℤ)) →
        F v = ratioExtensionSum M D n h ell p (τ, v) := by
  exact G1ContinuationStrictAux.ratio_continuation_unique M n h ell p ψ σ ρ δ hc τ hτ F hF hseed

/-- S13. A true pinch admits no ordinary separating representative. [RW26, p. 29]. -/
theorem pinch_prevents_separator (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (τ w y : ℂ) (n p : ℤ)
    (hp : ∃ k ∈ pinchLabels M p, (w, y) ∈ pinchHyperplane M τ p k) :
    ¬ ∃ D : Fin (M 1 0).toNat → CircleExtension,
      ∀ m, SeparatesExtension (D m) M τ y n p (m : ℤ) := by
  rintro ⟨D, hD⟩
  have hsep : ∀ m : Fin (M 1 0).toNat,
      ModularCluster.crossSeparated M (G1Pinch.ratioData w y n 0 0 p (m : ℤ)) τ := by
    intro m b hb b' hb' heq
    have hb0 : b ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p (m : ℤ)) := hb
    have hb0' : b' ∈ ModularCluster.labels M (G1Pinch.ratioData 0 y n 0 0 p (m : ℤ)) := hb'
    have h₀ := ((hD m).2.2 b hb0).2
    have h₁ := ((hD m).2.2 b' hb0').2
    have heq' : ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p (m : ℤ)) τ b =
        ModularCluster.branchPoint M (G1Pinch.ratioData 0 y n 0 0 p (m : ℤ)) τ b' := heq
    rw [heq'] at h₀
    cases hbt : b.1 <;> cases hbt' : b'.1 <;>
      simp_all
  obtain ⟨k, hk, hkp⟩ := hp
  exact ((crossSeparated_iff_deleted_hyperplanes M hM τ w y n 0 0 p).mp hsep k hk) hkp

/-- S14. A cleared joint analytic chart is available without assigning a raw value on the divisor.
N,D come from actual Φ charts. Nontriviality is slice-wise. [RW26, p. 29]. This is not the
fixed-real-τ removable-value contract. -/
theorem ratio_joint_cleared_chart (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (n h ell p : ℤ) (ψ : ℝ) (hψ : 0 < ψ) (hψ' : ψ < Real.pi / 4)
    (x : Parameters) (hx : x ∈ ratioTube M n h ell p ψ)
    (D : Fin (M 1 0).toNat → CircleExtension)
    (hD : ∀ m, SeparatesExtension (D m) M x.1 x.2.2 n p (m : ℤ)) :
    ∃ (U : Set Parameters) (N Q : Parameters → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ ratioTube M n h ell p ψ ∧ AnalyticOnNhd ℂ N U ∧ AnalyticOnNhd ℂ Q U ∧
      (∀ v ∈ U, ∃ᶠ z : ℂ × ℂ in 𝓝 v.2, Q (v.1, z) ≠ 0) ∧
      (∀ v ∈ U ∩ ratioGood M h ell p, Q v ≠ 0 → ratioRaw M h ell p v = N v / Q v) ∧
      ∀ v ∈ U, ratioExtensionSum M D n h ell p v * Q v =
        UpperResidueParameters.prefactor M v.1 * N v := by
  obtain ⟨U, hU, hxU, hsub, _, hsep⟩ :=
    ratio_extension_joint_analytic M hM n h ell p ψ hψ hψ' x hx D hD
  refine ⟨U, ratioRaw M h ell p, fun _ => 1, hU, hxU, hsub, ?_,
    analyticOnNhd_const, ?_, ?_, ?_⟩
  · exact (G1ContinuationStrictAux.ratio_raw_joint_analytic M hM n h ell p ψ hψ').mono hsub
  · intro v hv
    exact (Filter.Eventually.of_forall (fun _ : ℂ × ℂ => (one_ne_zero : (1 : ℂ) ≠ 0))).frequently
  · intro v hv hQ
    exact (div_one _).symm
  · intro v hv
    simpa only [mul_one, ratioRaw, G1ContinuationStrictAux.ratioExpression] using
      G1ContinuationStrictAux.upper_ratio_all_strict_value M hM n h ell p ψ hψ hψ' v
        (hsub hv) D (hsep v hv)

#check @UpperIntegralIdentities.upper_single
#check @UpperIntegralIdentities.upper_ratio
#check @upper_single_all_strict
#check @upper_ratio_all_strict
#print singleGood
#print ratioGood
#print ratioRaw

end SICLean.L4.G1Continuation
