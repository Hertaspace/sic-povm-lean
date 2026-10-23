import SICLean.L4.UpperWindowGeometry
import SICLean.L4.ModularPhi
import SICLean.L4.UpperWindowParametersAux

set_option autoImplicit false

/-!
# An explicit common open box about the upper-plane center

The proofs use the upstream geometry interfaces.
`Choices` contains only
the input numerical choices.
`domain` is an explicit coordinate box, not a set defined by pole
separation, product convergence, decay, or the window inequalities.
The tuple convention is x=(τ,w,y), i.e. ℂ × (ℂ × ℂ).

[RW26, p. 28, Appendix A.2].
The radius and the common domain are recorded here.
All Φ/square-root/η conventions are inherited from ModularPhi, unchanged.
-/

noncomputable section
open Complex Set
open scoped Topology MatrixGroups

namespace SICLean.L4.UpperWindow

abbrev Parameters := ℂ × ℂ × ℂ

/-- Exactly the numerical input assumptions, with c>0; no desired conclusion. -/
def Choices (M : SL(2, ℤ)) (ψ σ ρ δ : ℝ) : Prop :=
  0 < M 1 0 ∧ 0 < ψ ∧ ψ < Real.pi / 4 ∧ 0 < σ ∧ 0 < ρ ∧
    σ + ρ < 1 ∧ 0 < δ ∧ δ < ρ / (M 1 0 : ℝ)

/-- Explicit box half-width. It is positive only under Choices. -/
def radius (M : SL(2, ℤ)) (σ ρ δ : ℝ) : ℝ :=
  min σ (min (ρ - (M 1 0 : ℝ) * δ) (1 - σ - ρ)) / 4

def s (M : SL(2, ℤ)) (h ℓ : ℤ) (τ w : ℂ) : ℂ :=
  (M 1 0 : ℂ) * w + (h : ℂ) + (ℓ : ℂ) * etaDenom M τ

def height (M : SL(2, ℤ)) (p : ℤ) (τ y : ℂ) : ℂ :=
  1 + (p : ℂ) * etaDenom M τ + (M 1 0 : ℂ) * y

def centerW (M : SL(2, ℤ)) (h ℓ : ℤ) (σ : ℝ) (τ : ℂ) : ℂ :=
  ((σ : ℂ) * (etaDenom M τ + 1) - (h : ℂ) -
    (ℓ : ℂ) * etaDenom M τ) / (M 1 0 : ℂ)

def centerY (M : SL(2, ℤ)) (p : ℤ) (ρ : ℝ) (τ : ℂ) : ℂ :=
  ((ρ : ℂ) * (etaDenom M τ + 1) - 1 -
    (p : ℂ) * etaDenom M τ) / (M 1 0 : ℂ)

def tauRegion (M : SL(2, ℤ)) (ψ : ℝ) : Set ℂ :=
  {τ | 0 < τ.im ∧ 0 < (etaDenom M τ).arg ∧ (etaDenom M τ).arg < ψ}

/-- The four real coordinates are the coordinates of s and H, not w and y. -/
def domain (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ) : Set Parameters :=
  {x | x.1 ∈ tauRegion M ψ ∧
    |(coords (etaDenom M x.1) (s M h ℓ x.1 x.2.1)).1 - σ| < radius M σ ρ δ ∧
    |(coords (etaDenom M x.1) (s M h ℓ x.1 x.2.1)).2 - σ| < radius M σ ρ δ ∧
    |(coords (etaDenom M x.1) (height M p x.1 x.2.2)).1 - ρ| < radius M σ ρ δ ∧
    |(coords (etaDenom M x.1) (height M p x.1 x.2.2)).2 - ρ| < radius M σ ρ δ}

def A (ℓ : ℤ) (τ w : ℂ) : ℂ := (e τ) ^ ℓ * e w

def C (M : SL(2, ℤ)) (h : ℤ) (τ w : ℂ) : ℂ :=
  (e (etaMobius M τ)) ^ (-h) * e (w / etaDenom M τ)

def B (M : SL(2, ℤ)) (h : ℤ) (τ w y : ℂ) : ℂ :=
  e (y / etaDenom M τ) * C M h τ w

def upperSlope (M : SL(2, ℤ)) (h ℓ : ℤ) (τ w : ℂ) : ℂ :=
  s M h ℓ τ w / etaDenom M τ

def lowerSlope (M : SL(2, ℤ)) (h ℓ p : ℤ) (τ w y : ℂ) : ℂ :=
  (s M h ℓ τ w + height M p τ y - (etaDenom M τ + 1)) / etaDenom M τ

/--
Explicit radius margins.
[RW26, p. 28, Appendix A.2].
-/
theorem radius_margins (M : SL(2, ℤ)) (ψ σ ρ δ : ℝ) (hc : Choices M ψ σ ρ δ) :
    0 < radius M σ ρ δ ∧ 4 * radius M σ ρ δ ≤ σ ∧
      4 * radius M σ ρ δ ≤ ρ - (M 1 0 : ℝ) * δ ∧
      4 * radius M σ ρ δ ≤ 1 - σ - ρ ∧ 0 < (M 1 0 : ℝ) * δ ∧
      (M 1 0 : ℝ) * δ < 1 := by
  rcases hc with ⟨hM, hψ, hψ', hσ, hρ, hsum, hδ, hδρ⟩
  have hcR : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hM
  have hχρ : (M 1 0 : ℝ) * δ < ρ := by
    have := (lt_div_iff₀ hcR).mp hδρ
    nlinarith
  have hχ : 0 < (M 1 0 : ℝ) * δ := mul_pos hcR hδ
  have hmin : 0 < min σ (min (ρ - (M 1 0 : ℝ) * δ) (1 - σ - ρ)) :=
    lt_min hσ (lt_min (by linarith) (by linarith))
  have hσbound := min_le_left σ (min (ρ - (M 1 0 : ℝ) * δ) (1 - σ - ρ))
  have hρbound := (min_le_right σ (min (ρ - (M 1 0 : ℝ) * δ)
    (1 - σ - ρ))).trans (min_le_left _ _)
  have hsumbound := (min_le_right σ (min (ρ - (M 1 0 : ℝ) * δ)
    (1 - σ - ρ))).trans (min_le_right _ _)
  dsimp [radius]
  exact ⟨by linarith, by linarith, by linarith, by linarith, hχ, by linarith⟩

/--
Open τ wedge, wholly inside Im τ>0.
[RW26, p. 28, Appendix A.2].
-/
theorem tauRegion_isOpen (M : SL(2, ℤ)) (hM : 0 < M 1 0) (ψ : ℝ) :
    IsOpen (tauRegion M ψ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro τ hτ
  have hT : 0 < (etaDenom M τ).im := im_etaDenom_pos_of_im_pos M hM hτ.1
  have hden : Continuous (etaDenom M) := by unfold etaDenom; fun_prop
  have ha : ContinuousAt (fun z => (etaDenom M z).arg) τ :=
    (Complex.continuousAt_arg (Or.inr hT.ne')).comp hden.continuousAt
  have hi : ∀ᶠ z in 𝓝 τ, 0 < z.im :=
    continuous_im.continuousAt.eventually (lt_mem_nhds hτ.1)
  have hlo : ∀ᶠ z in 𝓝 τ, 0 < (etaDenom M z).arg :=
    ha.eventually (lt_mem_nhds hτ.2.1)
  have hhi : ∀ᶠ z in 𝓝 τ, (etaDenom M z).arg < ψ :=
    ha.eventually (gt_mem_nhds hτ.2.2)
  filter_upwards [hi, hlo, hhi] with z hz hzlo hzhi
  exact ⟨hz, hzlo, hzhi⟩

/--
Existing slit-plane branch and strict q,Q bases. No replacement of
modularPhi/phiExtended/etaMultiplier.
[RW26, p. 28, Appendix A.2].
-/
theorem tauRegion_properties (M : SL(2, ℤ)) (hM : 0 < M 1 0) (ψ : ℝ)
    (hψ : ψ < Real.pi / 4) (τ : ℂ) (hτ : τ ∈ tauRegion M ψ) :
    τ ∈ modularPhiDomain M ∧ 0 < (etaDenom M τ).im ∧
      0 < (etaDenom M τ).re ∧ etaDenom M τ ≠ 0 ∧
      0 < ‖e τ‖ ∧ ‖e τ‖ < 1 ∧
      0 < ‖e (etaMobius M τ)‖ ∧ ‖e (etaMobius M τ)‖ < 1 := by
  have hi := im_etaDenom_pos_of_im_pos M hM hτ.1
  have hne : etaDenom M τ ≠ 0 := by
    intro hz
    simp [hz] at hi
  have hre : 0 < (etaDenom M τ).re := by
    have ha : (etaDenom M τ).arg < Real.pi / 2 := by
      linarith [Real.pi_pos, hτ.2.2]
    rcases Complex.arg_lt_pi_div_two_iff.mp ha with hr | hr | hz
    · exact hr
    · linarith
    · exact (hne hz).elim
  have hη : 0 < (etaMobius M τ).im := by
    rw [← coe_smul_eq_etaMobius M (⟨τ, hτ.1⟩ : UpperHalfPlane)]
    exact (M • (⟨τ, hτ.1⟩ : UpperHalfPlane)).im_pos
  exact ⟨mem_modularPhiDomain_of_im_pos M hM hτ.1, hi, hre, hne,
    norm_pos_iff.mpr (e_ne_zero _), norm_e_lt_one ⟨τ, hτ.1⟩,
    norm_pos_iff.mpr (e_ne_zero _), norm_e_lt_one ⟨_, hη⟩⟩

/--
Exact prescribed center.
[RW26, p. 28, Appendix A.2].
-/
theorem center_equations (M : SL(2, ℤ)) (hM : 0 < M 1 0)
    (h ℓ p : ℤ) (σ ρ : ℝ) (τ : ℂ) :
    s M h ℓ τ (centerW M h ℓ σ τ) = (σ : ℂ) * (etaDenom M τ + 1) ∧
      height M p τ (centerY M p ρ τ) = (ρ : ℂ) * (etaDenom M τ + 1) := by
  have hc : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  constructor <;> dsimp [s, height, centerW, centerY] <;> field_simp [hc] <;> ring

/--
The explicit box is open jointly in (τ,w,y).
[RW26, p. 28, Appendix A.2].
-/
theorem domain_isOpen (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) : IsOpen (domain M h ℓ p ψ σ ρ δ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hT : (etaDenom M x.1).im ≠ 0 :=
    (im_etaDenom_pos_of_im_pos M hc.1 hx.1.1).ne'
  have hden : ContinuousAt (fun z : Parameters => etaDenom M z.1) x := by
    unfold etaDenom
    fun_prop
  have hS : ContinuousAt (fun z : Parameters => s M h ℓ z.1 z.2.1) x := by
    unfold s etaDenom
    fun_prop
  have hH : ContinuousAt (fun z : Parameters => height M p z.1 z.2.2) x := by
    unfold height etaDenom
    fun_prop
  have hcoords (f : Parameters → ℂ) (hf : ContinuousAt f x) :
      ContinuousAt (fun z => coords (etaDenom M z.1) (f z)) x := by
    unfold coords
    have hfim := continuous_im.continuousAt.comp hf
    have hfre := continuous_re.continuousAt.comp hf
    have hdim := continuous_im.continuousAt.comp hden
    have hdre := continuous_re.continuousAt.comp hden
    exact (hfim.div hdim hT).prodMk (hfre.sub ((hfim.div hdim hT).mul hdre))
  have hSc := hcoords _ hS
  have hHc := hcoords _ hH
  have hτ : ∀ᶠ z in 𝓝 x, z.1 ∈ tauRegion M ψ :=
    ((tauRegion_isOpen M hc.1 ψ).preimage continuous_fst).mem_nhds hx.1
  have hS1 := ((hSc.fst.sub continuousAt_const).abs).eventually
    (gt_mem_nhds hx.2.1)
  have hS2 := ((hSc.snd.sub continuousAt_const).abs).eventually
    (gt_mem_nhds hx.2.2.1)
  have hH1 := ((hHc.fst.sub continuousAt_const).abs).eventually
    (gt_mem_nhds hx.2.2.2.1)
  have hH2 := ((hHc.snd.sub continuousAt_const).abs).eventually
    (gt_mem_nhds hx.2.2.2.2)
  filter_upwards [hτ, hS1, hS2, hH1, hH2] with z hz hzS1 hzS2 hzH1 hzH2
  exact ⟨hz, hzS1, hzS2, hzH1, hzH2⟩

/--
The box contains the prescribed center for every allowed τ.
[RW26, p. 28, Appendix A.2].
-/
theorem center_mem_domain (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (τ : ℂ) (hτ : τ ∈ tauRegion M ψ) :
    (τ, centerW M h ℓ σ τ, centerY M p ρ τ) ∈ domain M h ℓ p ψ σ ρ δ := by
  obtain ⟨hs, hH⟩ := center_equations M hc.1 h ℓ p σ ρ τ
  have hT : (etaDenom M τ).im ≠ 0 :=
    (im_etaDenom_pos_of_im_pos M hc.1 hτ.1).ne'
  have hSc : coords (etaDenom M τ) ((σ : ℂ) * (etaDenom M τ + 1)) = (σ, σ) := by
    simpa only [mul_add, mul_one] using coords_real_combination (etaDenom M τ) hT σ σ
  have hHc : coords (etaDenom M τ) ((ρ : ℂ) * (etaDenom M τ + 1)) = (ρ, ρ) := by
    simpa only [mul_add, mul_one] using coords_real_combination (etaDenom M τ) hT ρ ρ
  have hr := (radius_margins M ψ σ ρ δ hc).1
  refine ⟨hτ, ?_, ?_, ?_, ?_⟩ <;>
    simpa only [hs, hH, hSc, hHc, sub_self, abs_zero] using hr

/--
A nonempty complex (w,y) window at fixed τ.
[RW26, p. 28, Appendix A.2].
-/
theorem fiber_open_nonempty (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (τ : ℂ) (hτ : τ ∈ tauRegion M ψ) :
    IsOpen {v : ℂ × ℂ | (τ, v) ∈ domain M h ℓ p ψ σ ρ δ} ∧
      {v : ℂ × ℂ | (τ, v) ∈ domain M h ℓ p ψ σ ρ δ}.Nonempty := by
  refine ⟨(domain_isOpen M h ℓ p ψ σ ρ δ hc).preimage (by fun_prop), ?_⟩
  exact ⟨(centerW M h ℓ σ τ, centerY M p ρ τ),
    center_mem_domain M h ℓ p ψ σ ρ δ hc τ hτ⟩

/--
Six simultaneous inequalities, derived from the box (not its definition).
[RW26, p. 28, Appendix A.2].
-/
theorem coordinate_inequalities (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    let S := coords (etaDenom M x.1) (s M h ℓ x.1 x.2.1)
    let H := coords (etaDenom M x.1) (height M p x.1 x.2.2)
    0 < S.1 ∧ 0 < S.2 ∧ (M 1 0 : ℝ) * δ < H.1 ∧
      (M 1 0 : ℝ) * δ < H.2 ∧ S.1 + H.1 < 1 ∧ S.2 + H.2 < 1 := by
  obtain ⟨hr, hσ, hρ, hsum, hχ, hχ1⟩ := radius_margins M ψ σ ρ δ hc
  obtain ⟨hτ, hS1, hS2, hH1, hH2⟩ := hx
  rw [abs_lt] at hS1 hS2 hH1 hH2
  dsimp only
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/--
General-coordinate modulus identities.
[RW26, p. 28, Appendix A.2].
-/
theorem ABC_norms (M : SL(2, ℤ)) (hM : 0 < M 1 0) (h ℓ p : ℤ)
    (ψ : ℝ) (τ w y : ℂ) (hτ : τ ∈ tauRegion M ψ) :
    ‖A ℓ τ w‖ = Real.rpow ‖e τ‖ (coords (etaDenom M τ) (s M h ℓ τ w)).1 ∧
      ‖C M h τ w‖ = Real.rpow ‖e (etaMobius M τ)‖
        (-(coords (etaDenom M τ) (s M h ℓ τ w)).2) ∧
      ‖B M h τ w y‖ = Real.rpow ‖e (etaMobius M τ)‖
        (1 - (coords (etaDenom M τ) (s M h ℓ τ w)).2 -
          (coords (etaDenom M τ) (height M p τ y)).2) := by
  simpa only [A, B, C, s, height] using ABC_norms_aux M hM h ℓ p τ w y hτ.1

/--
Exactly the two center equalities.
[RW26, p. 28, Appendix A.2].
-/
theorem center_AB_norms (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (τ : ℂ) (hτ : τ ∈ tauRegion M ψ) :
    ‖A ℓ τ (centerW M h ℓ σ τ)‖ = Real.rpow ‖e τ‖ σ ∧
      ‖B M h τ (centerW M h ℓ σ τ) (centerY M p ρ τ)‖ =
        Real.rpow ‖e (etaMobius M τ)‖ (1 - σ - ρ) := by
  obtain ⟨hs, hH⟩ := center_equations M hc.1 h ℓ p σ ρ τ
  have hT : (etaDenom M τ).im ≠ 0 :=
    (im_etaDenom_pos_of_im_pos M hc.1 hτ.1).ne'
  have hSc : coords (etaDenom M τ) ((σ : ℂ) * (etaDenom M τ + 1)) = (σ, σ) := by
    simpa only [mul_add, mul_one] using coords_real_combination (etaDenom M τ) hT σ σ
  have hHc : coords (etaDenom M τ) ((ρ : ℂ) * (etaDenom M τ + 1)) = (ρ, ρ) := by
    simpa only [mul_add, mul_one] using coords_real_combination (etaDenom M τ) hT ρ ρ
  have hn := ABC_norms M hc.1 h ℓ p ψ τ (centerW M h ℓ σ τ) (centerY M p ρ τ) hτ
  simpa only [hs, hH, hSc, hHc] using And.intro hn.1 hn.2.2

/--
Both residue-sum ratios are strict on the same domain.
[RW26, p. 28, Appendix A.2].
-/
theorem AB_norm_lt_one (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    0 < ‖A ℓ x.1 x.2.1‖ ∧ ‖A ℓ x.1 x.2.1‖ < 1 ∧
      0 < ‖B M h x.1 x.2.1 x.2.2‖ ∧ ‖B M h x.1 x.2.1 x.2.2‖ < 1 := by
  have hτ := tauRegion_properties M hc.1 ψ hc.2.2.1 x.1 hx.1
  have hi := coordinate_inequalities M h ℓ p ψ σ ρ δ hc x hx
  have hn := ABC_norms M hc.1 h ℓ p ψ x.1 x.2.1 x.2.2 hx.1
  rw [hn.1, hn.2.2]
  exact ⟨Real.rpow_pos_of_pos hτ.2.2.2.2.1 _,
    Real.rpow_lt_one hτ.2.2.2.2.1.le hτ.2.2.2.2.2.1 hi.1,
    Real.rpow_pos_of_pos hτ.2.2.2.2.2.2.1 _,
    Real.rpow_lt_one hτ.2.2.2.2.2.2.1.le hτ.2.2.2.2.2.2.2 (by linarith [hi.2.2.2.2.2])⟩

/--
Both arc linear coefficients are positive on their full closed intervals; no arc integral is
asserted here.
[RW26, p. 28, Appendix A.2].
-/
theorem arc_linear_pos (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    (∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      0 < (upperSlope M h ℓ x.1 x.2.1 * rotation θ).im) ∧
    (∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      0 < (lowerSlope M h ℓ p x.1 x.2.1 x.2.2 * rotation θ).im) := by
  have hτ := hx.1
  have hT : (etaDenom M x.1).im ≠ 0 :=
    (im_etaDenom_pos_of_im_pos M hc.1 hτ.1).ne'
  have hTne : etaDenom M x.1 ≠ 0 := by
    intro hz
    exact hT (by rw [hz]; simp)
  have hi := coordinate_inequalities M h ℓ p ψ σ ρ δ hc x hx
  let S := coords (etaDenom M x.1) (s M h ℓ x.1 x.2.1)
  let H := coords (etaDenom M x.1) (height M p x.1 x.2.2)
  have hs := coords_reconstruct (etaDenom M x.1) (s M h ℓ x.1 x.2.1) hT
  have hh := coords_reconstruct (etaDenom M x.1) (height M p x.1 x.2.2) hT
  have hu : upperSlope M h ℓ x.1 x.2.1 = (S.1 : ℂ) + (S.2 : ℂ) / etaDenom M x.1 := by
    unfold upperSlope
    calc
      _ = ((S.1 : ℂ) * etaDenom M x.1 + (S.2 : ℂ)) / etaDenom M x.1 :=
        congrArg (fun z => z / etaDenom M x.1) hs.symm
      _ = _ := by field_simp [hTne]
  have hnum : s M h ℓ x.1 x.2.1 + height M p x.1 x.2.2 - (etaDenom M x.1 + 1) =
      ((S.1 + H.1 - 1 : ℝ) : ℂ) * etaDenom M x.1 + ((S.2 + H.2 - 1 : ℝ) : ℂ) := by
    calc
      _ = ((S.1 : ℂ) * etaDenom M x.1 + (S.2 : ℂ)) +
          ((H.1 : ℂ) * etaDenom M x.1 + (H.2 : ℂ)) - (etaDenom M x.1 + 1) := by
        rw [hs, hh]
      _ = _ := by push_cast; ring
  have hl : lowerSlope M h ℓ p x.1 x.2.1 x.2.2 =
      ((S.1 + H.1 - 1 : ℝ) : ℂ) + ((S.2 + H.2 - 1 : ℝ) : ℂ) / etaDenom M x.1 := by
    unfold lowerSlope
    rw [hnum]
    field_simp [hTne]
  constructor
  · intro θ hθ
    rw [hu]
    exact upper_linear_pos _ ψ S.1 S.2 θ hτ.2.1 hτ.2.2 hc.2.2.1 hi.1 hi.2.1 hθ
  · intro θ hθ
    rw [hl]
    apply lower_linear_pos _ ψ _ _ θ hτ.2.1 hτ.2.2 hc.2.2.1 _ _ hθ
    · linarith [hi.2.2.2.2.1]
    · linarith [hi.2.2.2.2.2]

/--
Exact center slopes used to check the endpoint signs. Uses the same T and the same s,H as all other
definitions.
[RW26, p. 28, Appendix A.2].
-/
theorem center_slopes (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (τ : ℂ) (hτ : τ ∈ tauRegion M ψ) :
    upperSlope M h ℓ τ (centerW M h ℓ σ τ) = (σ : ℂ) * (1 + 1 / etaDenom M τ) ∧
      lowerSlope M h ℓ p τ (centerW M h ℓ σ τ) (centerY M p ρ τ) =
        -((1 - σ - ρ : ℝ) : ℂ) * (1 + 1 / etaDenom M τ) := by
  obtain ⟨hs, hH⟩ := center_equations M hc.1 h ℓ p σ ρ τ
  have hTne := (tauRegion_properties M hc.1 ψ hc.2.2.1 τ hτ).2.2.2.1
  constructor
  · unfold upperSlope
    rw [hs]
    field_simp [hTne]
  · unfold lowerSlope
    rw [hs, hH]
    push_cast
    field_simp [hTne]
    ring

#print Choices
#print radius
#print domain
#check center_mem_domain
#check fiber_open_nonempty
#check ABC_norms
#check arc_linear_pos
#check modularPhi
#check phiExtended
#check etaMultiplier

end SICLean.L4.UpperWindow
