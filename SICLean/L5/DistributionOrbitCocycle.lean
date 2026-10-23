import SICLean.L5.PeriodPowerMatrix
import SICLean.L5.DistributionHermite
import SICLean.L5.DistributionOrbitCocycleAux

set_option autoImplicit false

/-!
# Inverse-ε orbit telescoping and the separate zero orbit

[RW-rec, Appendix A, pp. 19--20]. The cocycle uses [RW26, p. 2, (1)],
[RW26, p. 3], [RW26, p. 6, (16)--(18)], [RW26, p. 12], and
[RW26, p. 14, Prop. 8].

Orbit geometry may be enumerated forward, but the cocycle chain here is
ordered by ε⁻¹. Both integer shift coordinates p and q are kept.
The assumptions are the coordinate and index equations. Telescoping,
regularity, diagonal-index normalization, and the zero values are
conclusions. Diagonal-index normalization is an equality at the center.
-/

noncomputable section
open SICLean.L4
open Complex Set Filter
open scoped Topology BigOperators MatrixGroups Classical

namespace SICLean.L5.DistributionOrbitCocycle

def orbitArgument (M : SL(2, ℤ)) (τ₀ : ℝ) (y : ℕ → ℂ) (j : ℕ) (w : ℂ) : ℂ :=
  y j + (w - y 0) / etaDenom M (τ₀ : ℂ) ^ j

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6].
The second integer translation coordinate is part of the identity. -/
theorem orbit_coordinate_step (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hc : 0 < M 1 0) (htr : 2 < M 0 0 + M 1 1)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
    (z y y' : ℂ) (j : ℕ) (p q p' q' h l : ℤ)
    (hrep : z / etaDenom M (τ₀ : ℂ) ^ j = y + (p : ℂ) * (τ₀ : ℂ) + (q : ℂ))
    (hrep' : z / etaDenom M (τ₀ : ℂ) ^ (j + 1) =
      y' + (p' : ℂ) * (τ₀ : ℂ) + (q' : ℂ))
    (hstep : y / etaDenom M (τ₀ : ℂ) = y' + (h : ℂ) * (τ₀ : ℂ) + (l : ℂ)) :
    M 1 1 * p - M 1 0 * q = p' - h := by
  have hτ : (τ₀ : ℂ) ∈ modularPhiDomain M :=
    ModularCocycleMatrixAux.domain_of_re_pos M _ hT
  have hirr := modularPhi_real_fixedPoint_irrational M hc htr τ₀
    (by simpa [etaDenom] using hT) hfix
  have hscaled : ((p : ℂ) * (τ₀ : ℂ) + (q : ℂ)) / etaDenom M (τ₀ : ℂ) =
      ((p' - h : ℤ) : ℂ) * (τ₀ : ℂ) + ((q' - l : ℤ) : ℂ) := by
    calc
      _ = (z / etaDenom M (τ₀ : ℂ) ^ j) / etaDenom M (τ₀ : ℂ) -
          y / etaDenom M (τ₀ : ℂ) := by rw [hrep]; ring
      _ = _ := by
        rw [div_div, ← pow_succ, hrep', hstep]
        push_cast
        ring
  have hlattice := modularPhi_lattice_mobius M p q (τ₀ : ℂ) hτ
  rw [hfix] at hlattice
  have hrel : (((M 1 1 * p - M 1 0 * q) - (p' - h) : ℤ) : ℂ) * (τ₀ : ℂ) +
      (((M 0 0 * q - M 0 1 * p) - (q' - l) : ℤ) : ℂ) = 0 := by
    push_cast at hlattice hscaled ⊢
    linear_combination hscaled - hlattice
  have hz := (m37b_irrational_relation τ₀ hirr _ _ hrel).1
  omega

section Chain

variable (M : SL(2, ℤ)) (τ₀ : ℝ) (r : ℕ)
variable (y : ℕ → ℂ) (A B p q h : ℕ → ℤ)
variable (hr : 0 < r) (hc : 0 < M 1 0) (htr : 2 < M 0 0 + M 1 1)
variable (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
variable (hT : 0 < (etaDenom M (τ₀ : ℂ)).re)
variable (hp0 : p 0 = 0) (hAr : A r = A 0)
variable (hrep : ∀ j, j < r → y 0 / etaDenom M (τ₀ : ℂ) ^ j =
  y j + (p j : ℂ) * (τ₀ : ℂ) + (q j : ℂ))
variable (hindex : ∀ j, j < r → A (j + 1) = B j + h j)
variable (hcoord : ∀ j, j < r → M 1 1 * p j - M 1 0 * q j = p (j + 1) - h j)

include hr hc htr hfix hT hp0 hAr hrep hindex hcoord

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6].
Integer argument shifts for the finite-product representatives. -/
theorem orbit_rewrite_factor (j : ℕ) (hj : j < r) (w : ℂ) :
    modularPhi M (A j) (B j) (orbitArgument M τ₀ y j w) (τ₀ : ℂ) =
      modularPhi M (A j - p j) (A (j + 1) - p (j + 1))
        (w / etaDenom M (τ₀ : ℂ) ^ j) (τ₀ : ℂ) := by
  have harg : orbitArgument M τ₀ y j w = w / etaDenom M (τ₀ : ℂ) ^ j +
      ((-p j : ℤ) : ℂ) * (τ₀ : ℂ) + ((-q j : ℤ) : ℂ) := by
    unfold orbitArgument
    rw [sub_div, hrep j hj]
    push_cast
    ring
  rw [harg, modularPhi_shift_integer M hc]
  have hi := hindex j hj
  have hco := hcoord j hj
  congr 1
  simp only [mul_neg]
  omega

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6, (18)].
Neither a closed orbit nor a nonzero center is assumed here. -/
theorem orbit_telescoping_germ :
    (fun w => ∏ j ∈ Finset.range r,
      modularPhi M (A j) (B j) (orbitArgument M τ₀ y j w) (τ₀ : ℂ)) =ᶠ[𝓝[≠] (y 0)]
      (fun w => modularPhi (M ^ r) (A 0) (A 0 - p r) w (τ₀ : ℂ)) := by
  have heq := modularPhi_iterate_fixedPoint_germ M hc htr
    (fun j => A j - p j) r (y 0) τ₀ hfix hT
  simp only [modularPhiConstructed_of_pos _ (modularPhi_pow_pos_c M hc htr r hr)] at heq
  simp only [hp0, sub_zero, hAr] at heq
  refine (Filter.EventuallyEq.of_eq ?_).trans heq.symm
  funext w
  exact Finset.prod_congr rfl fun j hj =>
    orbit_rewrite_factor M τ₀ r y A B p q h hr hc htr hfix hT hp0 hAr hrep hindex hcoord
      j (Finset.mem_range.mp hj) w

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6].
Exclusion of the divisor locus gives the center regularity used below. -/
theorem orbit_centers_nonvanishing (hy : y 0 ∉ modularPhiPseudoLattice (τ₀ : ℂ)) :
    (∀ j, j < r → (y j, (τ₀ : ℂ)) ∈ modularPhiNonvanishingDomain M (A j) (B j)) ∧
      (y 0, (τ₀ : ℂ)) ∈ modularPhiNonvanishingDomain (M ^ r) (A 0) (A 0 - p r) := by
  have hpow := modularPhi_pow_fixedPoint_domain M hc htr τ₀ hfix hT
  have hyj (j : ℕ) (hj : j < r) : y j ∉ modularPhiPseudoLattice (τ₀ : ℂ) := by
    rintro ⟨k, l, hkl⟩
    apply hy
    have hden : etaDenom (M ^ j) (τ₀ : ℂ) ≠ 0 :=
      ModularCocycleMatrixAux.denom_ne_zero_of_re_pos _ _ ((hpow j).2.2.1 j)
    have hmul := (div_eq_iff hden).mp (hpow j).1
    have hrepr : y 0 / etaDenom M (τ₀ : ℂ) ^ j =
        ((k + p j : ℤ) : ℂ) * (τ₀ : ℂ) + ((l + q j : ℤ) : ℂ) := by
      rw [hrep j hj, hkl]
      push_cast
      ring
    have hy0 : y 0 =
        (((k + p j : ℤ) : ℂ) * (τ₀ : ℂ) + ((l + q j : ℤ) : ℂ)) *
          etaDenom (M ^ j) (τ₀ : ℂ) := by
      apply (div_eq_iff hden).mp
      rw [(hpow j).2.1]
      exact hrepr
    refine ⟨(M ^ j) 0 0 * (k + p j) + (M ^ j) 1 0 * (l + q j),
      (M ^ j) 0 1 * (k + p j) + (M ^ j) 1 1 * (l + q j), ?_⟩
    rw [hy0]
    unfold etaDenom at hmul ⊢
    push_cast
    linear_combination -((k : ℂ) + (p j : ℂ)) * hmul
  constructor
  · intro j hj
    exact modularPhi_real_off_lattice M hc (A j) (B j) τ₀
      (by simpa [etaDenom] using hT) (y j) (hyj j hj)
  · exact modularPhi_real_off_lattice (M ^ r) (modularPhi_pow_pos_c M hc htr r hr)
      (A 0) (A 0 - p r) τ₀ (by simpa [etaDenom] using (hpow r).2.2.1 r) (y 0) hy

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6, (18)].
The representatives are regular at the centers. -/
theorem orbit_telescoping_value
    (hcenters : ∀ j, j < r → (y j, (τ₀ : ℂ)) ∈ modularPhiHolomorphicDomain M (A j) (B j))
    (htarget : (y 0, (τ₀ : ℂ)) ∈ modularPhiHolomorphicDomain (M ^ r) (A 0) (A 0 - p r)) :
    (∏ j ∈ Finset.range r, modularPhi M (A j) (B j) (y j) (τ₀ : ℂ)) =
      modularPhi (M ^ r) (A 0) (A 0 - p r) (y 0) (τ₀ : ℂ) := by
  have hleft : ContinuousAt (fun w => ∏ j ∈ Finset.range r,
      modularPhi M (A j) (B j) (orbitArgument M τ₀ y j w) (τ₀ : ℂ)) (y 0) := by
    apply tendsto_finsetProd
    intro j hj
    have hcont : ContinuousAt (fun z : ℂ × ℂ => modularPhi M (A j) (B j) z.1 z.2)
        (orbitArgument M τ₀ y j (y 0), (τ₀ : ℂ)) := by
      simpa only [orbitArgument, sub_self, zero_div, add_zero] using
        (modularPhi_joint_analytic_no_poles M hc (A j) (B j)
          (y j, (τ₀ : ℂ)) (hcenters j (Finset.mem_range.mp hj))).continuousAt
    exact hcont.comp (f := fun w : ℂ => (orbitArgument M τ₀ y j w, (τ₀ : ℂ)))
      (show ContinuousAt
        (fun w : ℂ => (orbitArgument M τ₀ y j w, (τ₀ : ℂ))) (y 0) by
        unfold orbitArgument
        fun_prop)
  have hright : ContinuousAt
      (fun w => modularPhi (M ^ r) (A 0) (A 0 - p r) w (τ₀ : ℂ)) (y 0) :=
    ((modularPhi_joint_analytic_no_poles (M ^ r)
      (modularPhi_pow_pos_c M hc htr r hr) (A 0) (A 0 - p r)
      (y 0, (τ₀ : ℂ)) htarget).continuousAt).comp (f := fun w : ℂ => (w, (τ₀ : ℂ)))
        (show ContinuousAt (fun w : ℂ => (w, (τ₀ : ℂ))) (y 0) by fun_prop)
  have heq := ModularCocycleAux.eq_of_germ hleft hright
    (orbit_telescoping_germ M τ₀ r y A B p q h hr hc htr hfix hT hp0 hAr hrep hindex hcoord)
  simpa only [orbitArgument, sub_self, zero_div, add_zero] using heq

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6].
The nonzero-orbit value, with regularity included. -/
theorem orbit_telescoping_off_lattice (hy : y 0 ∉ modularPhiPseudoLattice (τ₀ : ℂ)) :
    (∏ j ∈ Finset.range r, modularPhi M (A j) (B j) (y j) (τ₀ : ℂ)) =
      modularPhi (M ^ r) (A 0) (A 0 - p r) (y 0) (τ₀ : ℂ) := by
  obtain ⟨hcenters, htarget⟩ := orbit_centers_nonvanishing M τ₀ r y A B p q h
    hr hc htr hfix hT hp0 hAr hrep hindex hcoord hy
  exact orbit_telescoping_value M τ₀ r y A B p q h hr hc htr hfix hT hp0 hAr
    hrep hindex hcoord (fun j hj => ⟨(hcenters j hj).1, (hcenters j hj).2.1⟩)
      ⟨htarget.1, htarget.2.1⟩

/-- [RW-rec, Appendix A, p. 19]. The endpoint relation giving the phase
balance for the next center equality. -/
theorem orbit_closure_balance
    (hrep_r : y 0 / etaDenom M (τ₀ : ℂ) ^ r =
      y r + (p r : ℂ) * (τ₀ : ℂ) + (q r : ℂ)) (hclosed : y r = y 0) :
    y 0 / etaDenom M (τ₀ : ℂ) ^ r - y 0 =
      (p r : ℂ) * (τ₀ : ℂ) + (q r : ℂ) := by
  rw [hrep_r, hclosed]
  ring

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6, (16)].
A point equality off the lattice. The zero orbit is not moved across the
common zero by this index shift. -/
theorem orbit_index_normalize_off_lattice
    (hy : y 0 ∉ modularPhiPseudoLattice (τ₀ : ℂ))
    (hbalance : y 0 / etaDenom M (τ₀ : ℂ) ^ r - y 0 =
      (p r : ℂ) * (τ₀ : ℂ) + (q r : ℂ)) :
    modularPhi (M ^ r) (A 0) (A 0 - p r) (y 0) (τ₀ : ℂ) =
      modularPhi (M ^ r) (p r) 0 (y 0) (τ₀ : ℂ) := by
  have hpow := modularPhi_pow_fixedPoint_domain M hc htr τ₀ hfix hT r
  have hcR := modularPhi_pow_pos_c M hc htr r hr
  have hTR : 0 < (etaDenom (M ^ r) (τ₀ : ℂ)).re := hpow.2.2.1 r
  have hreal : 0 < ((M ^ r) 1 0 : ℝ) * τ₀ + ((M ^ r) 1 1 : ℝ) := by
    simpa [etaDenom] using hTR
  have hz : y 0 / etaDenom (M ^ r) (τ₀ : ℂ) =
      y 0 + (p r : ℂ) * (τ₀ : ℂ) + (q r : ℂ) := by
    rw [hpow.2.1]
    linear_combination hbalance
  have hphase : (e (τ₀ : ℂ)) ^ (p r) * e (y 0) =
      (e (τ₀ : ℂ)) ^ (0 : ℤ) * e (y 0 / etaDenom (M ^ r) (τ₀ : ℂ)) := by
    rw [hz, zpow_zero, one_mul, e_add', e_add',
      e_intCast, ← e_int_mul]
    ring
  have havoid : ∀ j : ℤ, 1 - (e (τ₀ : ℂ)) ^ (p r + j) * e (y 0) ≠ 0 := by
    intro j hj
    have heq : e (((p r + j : ℤ) : ℂ) * (τ₀ : ℂ) + y 0) = 1 := by
      rw [e_add', ← e_int_mul]
      exact (sub_eq_zero.mp hj).symm
    obtain ⟨k, hk⟩ := e_eq_one_iff_int heq
    apply hy
    refine ⟨-(p r + j), k, ?_⟩
    push_cast at hk ⊢
    linear_combination hk
  have hleft := (modularPhi_joint_analytic_no_poles (M ^ r) hcR
    (p r + (A 0 - p r)) (0 + (A 0 - p r)) (y 0, (τ₀ : ℂ))
      (show (y 0, (τ₀ : ℂ)) ∈ modularPhiHolomorphicDomain (M ^ r)
        (p r + (A 0 - p r)) (0 + (A 0 - p r)) from
          let hn := modularPhi_real_off_lattice (M ^ r) hcR _ _ τ₀ hreal (y 0) hy
          ⟨hn.1, hn.2.1⟩)).continuousAt
  have hright := (modularPhi_joint_analytic_no_poles (M ^ r) hcR (p r) 0
    (y 0, (τ₀ : ℂ)) (show (y 0, (τ₀ : ℂ)) ∈
      modularPhiHolomorphicDomain (M ^ r) (p r) 0 from
        let hn := modularPhi_real_off_lattice (M ^ r) hcR (p r) 0 τ₀ hreal (y 0) hy
        ⟨hn.1, hn.2.1⟩)).continuousAt
  have heq := modularPhi_diagonal_index_fixedPoint (M ^ r) hcR (p r) 0 (A 0 - p r)
    (y 0) τ₀ hpow.1 hTR hphase havoid
    (hleft.comp (f := fun w : ℂ => (w, (τ₀ : ℂ)))
      (show ContinuousAt (fun w : ℂ => (w, (τ₀ : ℂ))) (y 0) by fun_prop))
    (hright.comp (f := fun w : ℂ => (w, (τ₀ : ℂ)))
      (show ContinuousAt (fun w : ℂ => (w, (τ₀ : ℂ))) (y 0) by fun_prop))
  simpa only [add_sub_cancel, zero_add] using heq

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 6, (16), (18)].
The endpoint indices are in special-value form. -/
theorem orbit_product_off_lattice
    (hy : y 0 ∉ modularPhiPseudoLattice (τ₀ : ℂ))
    (hbalance : y 0 / etaDenom M (τ₀ : ℂ) ^ r - y 0 =
      (p r : ℂ) * (τ₀ : ℂ) + (q r : ℂ)) :
    (∏ j ∈ Finset.range r, modularPhi M (A j) (B j) (y j) (τ₀ : ℂ)) =
      modularPhi (M ^ r) (p r) 0 (y 0) (τ₀ : ℂ) := by
  exact (orbit_telescoping_off_lattice M τ₀ r y A B p q h hr hc htr hfix hT hp0 hAr
    hrep hindex hcoord hy).trans
      (orbit_index_normalize_off_lattice M τ₀ r y A B p q h hr hc htr hfix hT hp0 hAr
        hrep hindex hcoord hy hbalance)

/-- [RW-rec, Appendix A, pp. 19--20]; [RW26, p. 6, (18)]; [RW26, p. 14, Prop. 8].
The orbitwise weighted identity. -/
theorem orbit_weighted_product_off_lattice
    (hy : y 0 ∉ modularPhiPseudoLattice (τ₀ : ℂ))
    (hbalance : y 0 / etaDenom M (τ₀ : ℂ) ^ r - y 0 =
      (p r : ℂ) * (τ₀ : ℂ) + (q r : ℂ)) :
    (∏ j ∈ Finset.range r, etaMultiplier M * modularPhi M (A j) (B j) (y j) (τ₀ : ℂ)) =
      etaMultiplier (M ^ r) * modularPhi (M ^ r) (p r) 0 (y 0) (τ₀ : ℂ) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    orbit_product_off_lattice M τ₀ r y A B p q h hr hc htr hfix hT hp0 hAr
      hrep hindex hcoord hy hbalance,
    DistributionOrbitCocycleAux.etaMultiplier_pow_fixedPoint M τ₀ r hr hc htr hfix hT]

end Chain

/-- [RW-rec, Appendix A, pp. 19--20]; [RW26, p. 3]; [RW26, p. 6, (17)].
Positive automorphy factors multiply with the principal square-root sign. -/
theorem etaMultiplier_pow_fixedPoint (M : SL(2, ℤ)) (τ₀ : ℝ) (r : ℕ)
    (hr : 0 < r) (hc : 0 < M 1 0) (htr : 2 < M 0 0 + M 1 1)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) :
    etaMultiplier (M ^ r) = etaMultiplier M ^ r := by
  exact DistributionOrbitCocycleAux.etaMultiplier_pow_fixedPoint M τ₀ r hr hc htr hfix hT

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 2, (1)]; [RW26, p. 3].
The deleted-zero limit of the raw q quotient. -/
theorem modularPhi_zero_upper_tendsto (M : SL(2, ℤ)) (hc : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Tendsto (fun z => modularPhiQProduct M 0 0 z τ) (𝓝[≠] (0 : ℂ))
      (𝓝 (etaDenom M τ *
        (qPochhammer (e τ) (e τ) /
          qPochhammer (e (etaMobius M τ)) (e (etaMobius M τ))))) := by
  exact DistributionOrbitCocycleAux.modularPhi_zero_upper_tendsto M hc τ hτ

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 12].
The value of `modularPhi` at the zero center. -/
theorem modularPhi_zero_upper_value (M : SL(2, ℤ)) (hc : 0 < M 1 0)
    (τ : ℂ) (hτ : 0 < τ.im) : modularPhi M 0 0 0 τ = etaPhase M τ := by
  exact DistributionOrbitCocycleAux.modularPhi_zero_upper_value M hc τ hτ

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 12]; [RW26, p. 3].
The joint limit of `modularPhi` in the two variables. -/
theorem modularPhi_zero_fixedPoint_tendsto (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hc : 0 < M 1 0) (htr : 2 < M 0 0 + M 1 1)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) :
    Tendsto (fun z : ℂ × ℂ => modularPhi M 0 0 z.1 z.2)
      (𝓝 ((0 : ℂ), (τ₀ : ℂ)))
      (𝓝 ((etaMultiplier M)⁻¹ *
        (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ))) := by
  exact DistributionOrbitCocycleAux.modularPhi_zero_fixedPoint_tendsto M τ₀ hc htr hfix hT

/-- [RW-rec, Appendix A, p. 19]; [RW26, p. 3, (4)]; [RW26, p. 3, footnote 2];
[RW26, p. 12]. The singleton zero orbit uses this unshifted value. -/
theorem modularPhi_zero_fixedPoint_value (M : SL(2, ℤ)) (τ₀ : ℝ)
    (hc : 0 < M 1 0) (htr : 2 < M 0 0 + M 1 1)
    (hfix : etaMobius M (τ₀ : ℂ) = (τ₀ : ℂ))
    (hT : 0 < (etaDenom M (τ₀ : ℂ)).re) :
    modularPhi M 0 0 0 (τ₀ : ℂ) = (etaMultiplier M)⁻¹ *
      (Real.sqrt ((M 1 0 : ℝ) * τ₀ + (M 1 1 : ℝ)) : ℂ) := by
  exact DistributionOrbitCocycleAux.modularPhi_zero_fixedPoint_value M τ₀ hc htr hfix hT

#print orbitArgument
#check orbit_telescoping_germ
#check orbit_telescoping_off_lattice
#check @modularPhi_iterate_fixedPoint
#check @modularPhi_fixedPoint_lattice_tendsto
#check modularPhi_zero_fixedPoint_tendsto

end SICLean.L5.DistributionOrbitCocycle
