import SICLean.L4.UpperWindowCompactAux

set_option autoImplicit false

/-!
# Common compact margins

Compactness and common-margin theorems, with no new definitions.
Every compact set below is a subset of the same explicit open `domain`.
In particular it stays inside Im τ>0. Constants precede all parameter,
residue-class, template-point and angle quantifiers. Empty compact sets
are allowed; no minimum of an empty set is used in a definition.

[RW26, p. 28, p. 29, Appendix A.2].
Quantitative compact-parameter margins are formalized here.

No translated-kernel decay, remote-side integral limit, arc integral
limit, residue theorem or contour equality is asserted in this file.
The last theorem packages simultaneous input margins
without making those conclusions assumptions of a new domain.
-/

noncomputable section
open Complex Set
open scoped Topology BigOperators MatrixGroups

namespace SICLean.L4.UpperWindow

open CompactAux

/--
A genuinely small compact neighborhood stays in the initial window, as a closed ball.
[RW26, p. 28, Appendix A.2].
-/
theorem exists_closedBall (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (x : Parameters) (hx : x ∈ domain M h ℓ p ψ σ ρ δ) :
    ∃ r : ℝ, 0 < r ∧ IsCompact (Metric.closedBall x r) ∧
      Metric.closedBall x r ⊆ domain M h ℓ p ψ σ ρ δ := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((domain_isOpen M h ℓ p ψ σ ρ δ hc).mem_nhds hx)
  refine ⟨r / 2, half_pos hr, isCompact_closedBall _ _, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hsub

/--
Strict upper-plane, angle, norm and base margins, including lower
bounds for q,Q; not uniform at Im τ=0.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_parameter_bounds (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ η R r : ℝ, 0 < η ∧ 0 < R ∧ 0 < r ∧ r < 1 ∧ ∀ x ∈ K,
      η ≤ x.1.im ∧ η ≤ (etaDenom M x.1).im ∧
      η ≤ (etaDenom M x.1).arg ∧ (etaDenom M x.1).arg ≤ ψ - η ∧
      η ≤ ‖etaDenom M x.1‖ ∧ ‖etaDenom M x.1‖ ≤ R ∧
      η ≤ ‖e x.1‖ ∧ ‖e x.1‖ ≤ r ∧
      η ≤ ‖e (etaMobius M x.1)‖ ∧ ‖e (etaMobius M x.1)‖ ≤ r ∧
      ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R := by
  have ht (x : Parameters) (hx : x ∈ K) := tau_facts M h ℓ p ψ σ ρ δ hc (hKU hx)
  let f : Parameters → ℝ := fun x =>
    min x.1.im (min (etaDenom M x.1).im
      (min (etaDenom M x.1).arg (min (ψ - (etaDenom M x.1).arg)
        (min ‖etaDenom M x.1‖ (min ‖e x.1‖ ‖e (etaMobius M x.1)‖)))))
  have hfc : ContinuousOn f K := by
    intro x hx
    have hT := ht x hx
    have harg : ContinuousAt (fun x : Parameters => (etaDenom M x.1).arg) x :=
      (Complex.continuousAt_arg (Or.inl hT.2.2.1)).comp
        (f := fun x : Parameters => etaDenom M x.1) (by fun_prop)
    apply ContinuousAt.continuousWithinAt
    dsimp [f]
    fun_prop (disch := exact hT.2.2.2.1)
  obtain ⟨η, hη, hf⟩ := positive_minimum hK hfc (by
    intro x hx
    have hh := (hKU hx).1
    have hT := ht x hx
    simp only [f, lt_min_iff]
    exact ⟨hh.1, hT.2.1, hh.2.1, sub_pos.mpr hh.2.2,
      norm_pos_iff.mpr hT.2.2.2.1, hT.2.2.2.2.1, hT.2.2.2.2.2.2.1⟩)
  obtain ⟨R, hR, hb⟩ := positive_bound hK (f := fun x =>
    max ‖etaDenom M x.1‖ (max ‖x.2.1‖ ‖x.2.2‖)) (by fun_prop)
  obtain ⟨r, hr, hr1, hq⟩ := strict_upper_bound hK
    (f := fun x => max ‖e x.1‖ ‖e (etaMobius M x.1)‖) (by
      intro x hx
      have hT := (ht x hx).2.2.2.1
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)) (by
      intro x hx
      exact max_lt (ht x hx).2.2.2.2.2.1 (ht x hx).2.2.2.2.2.2.2)
  refine ⟨η, R, r, hη, hR, hr, hr1, ?_⟩
  intro x hx
  have hf' := hf x hx
  dsimp [f] at hf'
  simp only [le_min_iff] at hf'
  have hb' := hb x hx
  have hq' := hq x hx
  simp only [max_le_iff] at hb' hq'
  exact ⟨hf'.1, hf'.2.1, hf'.2.2.1, by linarith [hf'.2.2.2.1],
    hf'.2.2.2.2.1, hb'.1, hf'.2.2.2.2.2.1, hq'.1,
    hf'.2.2.2.2.2.2, hq'.2, hb'.2.1, hb'.2.2⟩

/--
All six coordinate margins hold with one η on K.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_coordinate_margin (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K,
      let S := coords (etaDenom M x.1) (s M h ℓ x.1 x.2.1)
      let H := coords (etaDenom M x.1) (height M p x.1 x.2.2)
      η ≤ S.1 ∧ η ≤ S.2 ∧ (M 1 0 : ℝ) * δ + η ≤ H.1 ∧
        (M 1 0 : ℝ) * δ + η ≤ H.2 ∧ S.1 + H.1 ≤ 1 - η ∧ S.2 + H.2 ≤ 1 - η := by
  obtain ⟨hε, hεσ, hερ, hεsum, _, _⟩ := radius_margins M ψ σ ρ δ hc
  refine ⟨radius M σ ρ δ, hε, ?_⟩
  intro x hx
  have hx' := hKU hx
  obtain ⟨hτ, hS₁, hS₂, hH₁, hH₂⟩ := hx'
  obtain ⟨hS₁l, hS₁r⟩ := abs_lt.mp hS₁
  obtain ⟨hS₂l, hS₂r⟩ := abs_lt.mp hS₂
  obtain ⟨hH₁l, hH₁r⟩ := abs_lt.mp hH₁
  obtain ⟨hH₂l, hH₂r⟩ := abs_lt.mp hH₂
  dsimp only
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> linarith

/--
The geometric rates used by the integer-shift templates.
No bound on an actual translated kernel is asserted here.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_AB_rates (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ rA rB : ℝ, 0 < rA ∧ rA < 1 ∧ 0 < rB ∧ rB < 1 ∧ ∀ x ∈ K,
      ‖A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat ≤ rA ∧
        ‖B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat ≤ rB := by
  have hn : (M 1 0).toNat ≠ 0 := by
    have hcZ : 0 < M 1 0 := hc.1
    omega
  obtain ⟨r, hr, hr1, hb⟩ := strict_upper_bound hK
    (f := fun x => max (‖A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat)
      (‖B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat)) (by
      intro x hx
      have hT := (tau_facts M h ℓ p ψ σ ρ δ hc (hKU hx)).2.2.2.1
      apply ContinuousAt.continuousWithinAt
      unfold A B C
      fun_prop (disch := simp [e_ne_zero])) (by
      intro x hx
      obtain ⟨_, hA, _, hB⟩ := AB_norm_lt_one M h ℓ p ψ σ ρ δ hc x (hKU hx)
      exact max_lt (pow_lt_one₀ (norm_nonneg _) hA hn)
        (pow_lt_one₀ (norm_nonneg _) hB hn))
  refine ⟨r, r, hr, hr1, hr, hr1, ?_⟩
  intro x hx
  exact max_le_iff.mp (hb x hx)

/--
One strict modulus bound for all eight original/reflected vertex
arguments and all residue classes.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_vertex_margin (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      let z := base M (m : ℤ) n δ x.1
      ‖aArg (m : ℤ) x.1 z‖ ≤ r ∧ ‖bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ r ∧
      ‖dArg M n x.1 z‖ ≤ r ∧ ‖cArg M n x.1 x.2.2 z‖ ≤ r ∧
      ‖e x.1 / aArg (m : ℤ) x.1 z‖ ≤ r ∧
      ‖e (etaMobius M x.1) / dArg M n x.1 z‖ ≤ r ∧
      ‖e x.1 / bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ r ∧
      ‖e (etaMobius M x.1) / cArg M n x.1 x.2.2 z‖ ≤ r := by
  obtain ⟨r, hr, hr1, hb⟩ := finite_strict_upper_bound
    ((Finset.range (M 1 0).toNat) ×ˢ (Finset.univ : Finset (Fin 8))) hK
    (f := fun i x => ‖vertexArguments M (i.1 : ℤ) n p δ x i.2‖) (by
      intro i hi x hx
      exact (vertexArguments_continuousAt M (i.1 : ℤ) n p δ x
        (tau_facts M h ℓ p ψ σ ρ δ hc (hKU hx)).2.2.2.1 i.2).norm.continuousWithinAt) (by
      intro i hi x hx
      exact vertexArguments_lt_one M h ℓ p (i.1 : ℤ) n ψ σ ρ δ hc x (hKU hx) i.2)
  refine ⟨r, hr, hr1, ?_⟩
  intro x hx m hm
  have hh (i : Fin 8) := hb (m, i) (by simp [hm]) x hx
  exact ⟨hh 0, hh 1, hh 2, hh 3, hh 4, hh 5, hh 6, hh 7⟩

/--
Shift-product denominator arguments are <1, numerator arguments and
C/d are merely bounded. These bounds are an input to the product bounds,
not their conclusion.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_template_arguments (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ r D : ℝ, 0 < r ∧ r < 1 ∧ 0 < D ∧
      ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ z ∈ templates M (m : ℤ) n δ x.1,
        ‖aArg (m : ℤ) x.1 z‖ ≤ r ∧
        ‖e (etaMobius M x.1) / dArg M n x.1 z‖ ≤ r ∧
        ‖bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ D ∧
        ‖e (etaMobius M x.1) / cArg M n x.1 x.2.2 z‖ ≤ D ∧
        ‖C M h x.1 x.2.1 / dArg M n x.1 z‖ ≤ D := by
  let S (m : ℕ) : Set (Parameters × ℂ) :=
    {q | q.1 ∈ K ∧ q.2 ∈ templates M (m : ℤ) n δ q.1.1}
  have hS (m : ℕ) : IsCompact (S m) := compact_template_set M (m : ℤ) n δ K hK
  have hEachRate (m : ℕ) : ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ x ∈ K, ∀ z ∈ templates M (m : ℤ) n δ x.1,
        ‖aArg (m : ℤ) x.1 z‖ ≤ r ∧
        ‖e (etaMobius M x.1) / dArg M n x.1 z‖ ≤ r := by
    obtain ⟨r, hr, hr1, hb⟩ := strict_upper_bound (hS m)
      (f := fun q => max ‖aArg (m : ℤ) q.1.1 q.2‖
        ‖e (etaMobius M q.1.1) / dArg M n q.1.1 q.2‖) (by
        intro q hq
        have hT := (tau_facts M h ℓ p ψ σ ρ δ hc (hKU hq.1)).2.2.2.1
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := first | assumption | exact dArg_ne_zero _ _ _ _)) (by
        intro q hq
        exact max_lt_iff.mpr
          (template_q_bounds M h ℓ p (m : ℤ) n ψ σ ρ δ hc q.1 (hKU hq.1) q.2 hq.2))
    exact ⟨r, hr, hr1, fun x hx z hz => max_le_iff.mp (hb (x, z) ⟨hx, hz⟩)⟩
  obtain ⟨r, hr, hr1, hb⟩ := finite_rates (Finset.range (M 1 0).toNat)
    (fun m r => ∀ x ∈ K, ∀ z ∈ templates M (m : ℤ) n δ x.1,
      ‖aArg (m : ℤ) x.1 z‖ ≤ r ∧
      ‖e (etaMobius M x.1) / dArg M n x.1 z‖ ≤ r)
    (by
      intro m a b hab hb x hx z hz
      exact ⟨(hb x hx z hz).1.trans hab, (hb x hx z hz).2.trans hab⟩)
    (fun m _ => hEachRate m)
  have hEachBound (m : ℕ) : ∃ D : ℝ, ∀ x ∈ K,
      ∀ z ∈ templates M (m : ℤ) n δ x.1,
        ‖bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ D ∧
        ‖e (etaMobius M x.1) / cArg M n x.1 x.2.2 z‖ ≤ D ∧
        ‖C M h x.1 x.2.1 / dArg M n x.1 z‖ ≤ D := by
    obtain ⟨D, _, hb⟩ := positive_bound (hS m)
      (f := fun q => max ‖bArg (m : ℤ) p q.1.1 q.1.2.2 q.2‖
        (max ‖e (etaMobius M q.1.1) / cArg M n q.1.1 q.1.2.2 q.2‖
          ‖C M h q.1.1 q.1.2.1 / dArg M n q.1.1 q.2‖)) (by
        intro q hq
        have hT := (tau_facts M h ℓ p ψ σ ρ δ hc (hKU hq.1)).2.2.2.1
        apply ContinuousAt.continuousWithinAt
        unfold C
        fun_prop (disch := first
          | assumption
          | exact dArg_ne_zero _ _ _ _
          | exact cArg_ne_zero _ _ _ _ _
          | simp [e_ne_zero]))
    refine ⟨D, ?_⟩
    intro x hx z hz
    simpa only [max_le_iff] using hb (x, z) ⟨hx, hz⟩
  choose D hD using hEachBound
  obtain ⟨D', hD'⟩ := ((Finset.range (M 1 0).toNat).image D).exists_le
  refine ⟨r, max 1 D', hr, hr1, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx m hm z hz
  have hd : D m ≤ max 1 D' := (hD' _ (Finset.mem_image_of_mem D hm)).trans (le_max_right _ _)
  exact ⟨(hb m hm x hx z hz).1, (hb m hm x hx z hz).2,
    (hD m x hx z hz).1.trans hd, (hD m x hx z hz).2.1.trans hd,
    (hD m x hx z hz).2.2.trans hd⟩

/--
All four original product arguments are uniformly <1 on the full
unbounded upper sector. Not an estimate on Φ itself.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_upper_arguments (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ r' : ℝ, 0 ≤ r' → ∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
      let z := base M (m : ℤ) n δ x.1 + (r' : ℂ) * rotation θ
      ‖aArg (m : ℤ) x.1 z‖ ≤ r ∧ ‖bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ r ∧
        ‖dArg M n x.1 z‖ ≤ r ∧ ‖cArg M n x.1 x.2.2 z‖ ≤ r := by
  obtain ⟨r, hr, hr1, hb⟩ := compact_vertex_margin M h ℓ p n ψ σ ρ δ hc K hK hKU
  refine ⟨r, hr, hr1, ?_⟩
  intro x hx m hm r' hr' θ hθ
  obtain ⟨ha, hb', hd, he⟩ := upper_arguments_le_vertex M (m : ℤ) n p x.1 x.2.2
    (base M (m : ℤ) n δ x.1) ψ r' θ hr'
    (hKU hx).1.2.1 (hKU hx).1.2.2 hc.2.2.1 hθ
  have hv := hb x hx m hm
  exact ⟨ha.trans hv.1, hb'.trans hv.2.1, hd.trans hv.2.2.1, he.trans hv.2.2.2.1⟩

/--
The four reflected arguments on the full lower sector. Not a lower-arc integral limit.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_lower_reflected_arguments (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ r' : ℝ, 0 ≤ r' → ∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
      let z := base M (m : ℤ) n δ x.1 + (r' : ℂ) * rotation θ
      ‖e x.1 / aArg (m : ℤ) x.1 z‖ ≤ r ∧
        ‖e (etaMobius M x.1) / dArg M n x.1 z‖ ≤ r ∧
        ‖e x.1 / bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ r ∧
        ‖e (etaMobius M x.1) / cArg M n x.1 x.2.2 z‖ ≤ r := by
  obtain ⟨r, hr, hr1, hb⟩ := compact_vertex_margin M h ℓ p n ψ σ ρ δ hc K hK hKU
  refine ⟨r, hr, hr1, ?_⟩
  intro x hx m hm r' hr' θ hθ
  obtain ⟨ha, hd, hb', he⟩ := lower_arguments_le_vertex M (m : ℤ) n p x.1 x.2.2
    (base M (m : ℤ) n δ x.1) ψ r' θ hr'
    (hKU hx).1.2.1 (hKU hx).1.2.2 hc.2.2.1 hθ
  have hv := hb x hx m hm
  exact ⟨ha.trans hv.2.2.2.2.1, hd.trans hv.2.2.2.2.2.1,
    hb'.trans hv.2.2.2.2.2.2.1, he.trans hv.2.2.2.2.2.2.2⟩

/--
One linear decay margin for both closed angle intervals, uniform
also in τ∈K.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_arc_linear_margin (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ K,
      (∀ θ ∈ Icc (etaDenom M x.1).arg (Real.pi / 2 + ψ),
        lam ≤ (upperSlope M h ℓ x.1 x.2.1 * rotation θ).im) ∧
      (∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
        lam ≤ (lowerSlope M h ℓ p x.1 x.2.1 x.2.2 * rotation θ).im) := by
  let U : Set (Parameters × ℝ) :=
    {q | q ∈ K ×ˢ Icc 0 (Real.pi / 2 + ψ) ∧ (etaDenom M q.1.1).arg ≤ q.2}
  have harg : ContinuousOn (fun x : Parameters => (etaDenom M x.1).arg) K := by
    intro x hx
    have ht := tau_facts M h ℓ p ψ σ ρ δ hc (hKU hx)
    exact ((Complex.continuousAt_arg (Or.inl ht.2.2.1)).comp
      (f := fun x : Parameters => etaDenom M x.1) (by fun_prop)).continuousWithinAt
  have hUK : IsCompact U := by
    apply (hK.prod isCompact_Icc).of_isClosed_subset
    · exact (hK.prod isCompact_Icc).isClosed.isClosed_le
        (harg.comp continuousOn_fst (fun _ hx => hx.1)) continuousOn_snd
    · exact fun _ hx => hx.1
  obtain ⟨a, ha, hUa⟩ := positive_minimum hUK
    (f := fun q => (upperSlope M h ℓ q.1.1 q.1.2.1 * rotation q.2).im) (by
      intro q hq
      have hT := (tau_facts M h ℓ p ψ σ ρ δ hc (hKU hq.1.1)).2.2.2.1
      apply ContinuousAt.continuousWithinAt
      unfold upperSlope s
      fun_prop (disch := assumption)) (by
      intro q hq
      exact (arc_linear_pos M h ℓ p ψ σ ρ δ hc q.1 (hKU hq.1.1)).1 q.2
        ⟨hq.2, hq.1.2.2⟩)
  obtain ⟨b, hb, hLb⟩ := positive_minimum (hK.prod (isCompact_Icc (a := -Real.pi / 2 + ψ) (b := 0)))
    (f := fun q : Parameters × ℝ =>
      (lowerSlope M h ℓ p q.1.1 q.1.2.1 q.1.2.2 * rotation q.2).im) (by
      intro q hq
      have hT := (tau_facts M h ℓ p ψ σ ρ δ hc (hKU hq.1)).2.2.2.1
      apply ContinuousAt.continuousWithinAt
      unfold lowerSlope s height
      fun_prop (disch := assumption)) (by
      intro q hq
      exact (arc_linear_pos M h ℓ p ψ σ ρ δ hc q.1 (hKU hq.1)).2 q.2 hq.2)
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro x hx
  constructor
  · intro θ hθ
    apply (min_le_left _ _).trans (hUa (x, θ) ?_)
    exact ⟨⟨hx, le_trans (hKU hx).1.2.1.le hθ.1, hθ.2⟩, hθ.1⟩
  · intro θ hθ
    exact (min_le_right _ _).trans (hLb (x, θ) ⟨hx, hθ⟩)

/--
Both continuous and discrete quadratic coefficients have a common
strict sign margin on K. It necessarily depends
on K staying away from Im τ=0.
[RW26, p. 28, Appendix A.2].
-/
theorem compact_quadratic_margin (M : SL(2, ℤ)) (h ℓ p : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K,
      ((M 1 0 : ℝ) ^ 2 / 2) * Real.log ‖e (etaMobius M x.1)‖ ≤ -a ∧
      (∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
        a ≤ -(Real.pi * (M 1 0 : ℝ) / ‖etaDenom M x.1‖) *
          Real.sin (2 * θ - (etaDenom M x.1).arg)) := by
  have hcR : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hc.1
  have hθ0 : (0 : ℝ) ∈ Icc (-Real.pi / 2 + ψ) 0 := by
    constructor <;> linarith [hc.2.2.1, Real.pi_pos]
  have hsin (x : Parameters) (hx : x ∈ K) :=
    lower_quadratic_margin (etaDenom M x.1) ψ 0
      (hKU hx).1.2.1 (hKU hx).1.2.2 hc.2.2.1 hθ0
  let f : Parameters → ℝ := fun x =>
    min (-(((M 1 0 : ℝ) ^ 2 / 2) * Real.log ‖e (etaMobius M x.1)‖))
      ((Real.pi * (M 1 0 : ℝ) / ‖etaDenom M x.1‖) * Real.sin (etaDenom M x.1).arg)
  obtain ⟨a, ha, hf⟩ := positive_minimum hK (f := f) (by
    intro x hx
    have ht := tau_facts M h ℓ p ψ σ ρ δ hc (hKU hx)
    have harg : ContinuousAt (fun x : Parameters => (etaDenom M x.1).arg) x :=
      (Complex.continuousAt_arg (Or.inl ht.2.2.1)).comp
        (f := fun x : Parameters => etaDenom M x.1) (by fun_prop)
    have hT : etaDenom M x.1 ≠ 0 := ht.2.2.2.1
    have hq : ‖e (etaMobius M x.1)‖ ≠ 0 := ne_of_gt ht.2.2.2.2.2.2.1
    have hnorm : ‖etaDenom M x.1‖ ≠ 0 := norm_ne_zero_iff.mpr ht.2.2.2.1
    apply ContinuousAt.continuousWithinAt
    dsimp [f]
    fun_prop (disch := assumption)) (by
    intro x hx
    have ht := tau_facts M h ℓ p ψ σ ρ δ hc (hKU hx)
    dsimp [f]
    apply lt_min
    · exact neg_pos.mpr (mul_neg_of_pos_of_neg (by positivity)
        (Real.log_neg ht.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2))
    · exact mul_pos (div_pos (mul_pos Real.pi_pos hcR)
        (norm_pos_iff.mpr ht.2.2.2.1)) (hsin x hx).1)
  refine ⟨a, ha, ?_⟩
  intro x hx
  have hh := le_min_iff.mp (hf x hx)
  constructor
  · linarith [hh.1]
  · intro θ hθ
    have hq := lower_quadratic_margin (etaDenom M x.1) ψ θ
      (hKU hx).1.2.1 (hKU hx).1.2.2 hc.2.2.1 hθ
    have hcoeff : 0 ≤ Real.pi * (M 1 0 : ℝ) / ‖etaDenom M x.1‖ := by positivity
    have hm := mul_le_mul_of_nonneg_left hq.2 hcoeff
    exact hh.2.trans (by simpa only [mul_neg, neg_mul] using hm)

/--
The specified actual kernels, with pointwise division, are uniformly
bounded on the compact template family. Unit-domain membership, not
germ equality, justifies this statement.
[RW26, p. 6, p. 28, Appendix A.2].
-/
theorem compact_template_kernel_bounds (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ x ∈ K, ∀ m ∈ Finset.range (M 1 0).toNat,
      ∀ z ∈ templates M (m : ℤ) n δ x.1,
        ‖singleKernel M (m : ℤ) n h ℓ x.1 x.2.1 z‖ ≤ M₀ ∧
        ‖ratioKernel M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2 z‖ ≤ M₀ := by
  have hEach (m : ℕ) : ∃ B : ℝ, ∀ x ∈ K,
      ∀ z ∈ templates M (m : ℤ) n δ x.1,
        ‖singleKernel M (m : ℤ) n h ℓ x.1 x.2.1 z‖ ≤ B ∧
        ‖ratioKernel M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2 z‖ ≤ B := by
    let S : Set (Parameters × ℂ) :=
      {q | q.1 ∈ K ∧ q.2 ∈ templates M (m : ℤ) n δ q.1.1}
    have hS : IsCompact S := compact_template_set M (m : ℤ) n δ K hK
    have hS_mem (q : Parameters × ℂ) :
        q ∈ S ↔ q.1 ∈ K ∧ q.2 ∈ templates M (m : ℤ) n δ q.1.1 := Iff.rfl
    let F : Parameters × ℂ → ℂ × ℂ := fun q =>
      (singleKernel M (m : ℤ) n h ℓ q.1.1 q.1.2.1 q.2,
       ratioKernel M (m : ℤ) n h ℓ p q.1.1 q.1.2.1 q.1.2.2 q.2)
    have hF : ContinuousOn F S := by
      intro q hq
      obtain ⟨hx, hz⟩ := (hS_mem q).mp hq
      have hdiv := grid_divisor_free M h ℓ p (m : ℤ) n ψ σ ρ δ hc q.1 (hKU hx) q.2 hz 0 0
      simp only [Nat.cast_zero, zero_mul, add_zero] at hdiv
      obtain ⟨U₁, hU₁, hp₁, hsub₁, ha₁, hn₁⟩ :=
        modularPhi_joint_unit_neighborhood M hc.1 ((m : ℤ) + 1) n (q.2, q.1.1) hdiv.1
      obtain ⟨U₂, hU₂, hp₂, hsub₂, ha₂, hn₂⟩ :=
        modularPhi_joint_unit_neighborhood M hc.1 ((m : ℤ) + p) n
          (q.2 + q.1.2.2, q.1.1) hdiv.2
      have hΦ₁ : ContinuousAt
          (fun r : Parameters × ℂ => modularPhi M ((m : ℤ) + 1) n r.2 r.1.1) q :=
        ContinuousAt.comp (f := fun r : Parameters × ℂ => (r.2, r.1.1))
          (ha₁ _ hp₁).continuousAt (by fun_prop)
      have hΦ₂ : ContinuousAt
          (fun r : Parameters × ℂ => modularPhi M ((m : ℤ) + p) n
            (r.2 + r.1.2.2) r.1.1) q :=
        ContinuousAt.comp (f := fun r : Parameters × ℂ => (r.2 + r.1.2.2, r.1.1))
          (ha₂ _ hp₂).continuousAt (by fun_prop)
      have hT : etaDenom M q.1.1 ≠ 0 :=
        (tauRegion_properties M hc.1 ψ hc.2.2.1 q.1.1 (hKU hx).1).2.2.2.1
      have hdenom : ContinuousAt (fun r : Parameters × ℂ => etaDenom M r.1.1) q := by
        dsimp [etaDenom]
        fun_prop
      have hmobius : ContinuousAt (fun r : Parameters × ℂ => etaMobius M r.1.1) q := by
        unfold etaMobius
        apply ContinuousAt.div _ hdenom hT
        fun_prop
      have hphase : ContinuousAt
          (fun r : Parameters × ℂ => e (phase M (m : ℤ) n h ℓ r.1.1 r.1.2.1 r.2)) q := by
        unfold phase e
        fun_prop
      have hnPhi₂ : modularPhi M ((m : ℤ) + p) n (q.2 + q.1.2.2) q.1.1 ≠ 0 :=
        hn₂ (q.2 + q.1.2.2, q.1.1) hp₂
      have hratio := (hΦ₁.div hΦ₂ hnPhi₂).mul hphase
      have hsingle := hΦ₁.mul hphase
      have hpair := hsingle.prodMk hratio
      simpa only [F, singleKernel, ratioKernel, Pi.mul_apply, Pi.div_apply]
        using hpair.continuousWithinAt (s := S)
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hF
    refine ⟨B, ?_⟩
    intro x hx z hz
    have hb := hB (x, z) ((hS_mem (x, z)).mpr ⟨hx, hz⟩)
    exact ⟨(norm_fst_le (F (x, z))).trans hb, (norm_snd_le (F (x, z))).trans hb⟩
  choose B hB using hEach
  obtain ⟨C, hC⟩ := ((Finset.range (M 1 0).toNat).image B).exists_le
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx m hm z hz
  have hmC : B m ≤ max C 1 := (hC _ (Finset.mem_image_of_mem B hm)).trans (le_max_left _ _)
  exact ⟨((hB m x hx z hz).1).trans hmC, ((hB m x hx z hz).2).trans hmC⟩

/--
Simultaneous entry point: one set K, one collection of constants,
before τ,w,y,m,z,θ. This combines the strict-domain shrink, shift-template input, and arc input.
It makes no assertion as Im τ tends to 0 and no assertion of the actual
integral identities.
[RW26, p. 28, p. 29, Appendix A.2].
-/
theorem compact_common_margins (M : SL(2, ℤ)) (h ℓ p n : ℤ) (ψ σ ρ δ : ℝ)
    (hc : Choices M ψ σ ρ δ) (K : Set Parameters) (hK : IsCompact K)
    (hKU : K ⊆ domain M h ℓ p ψ σ ρ δ) :
    ∃ η r lam a D M₀ R : ℝ,
      0 < η ∧ 0 < r ∧ r < 1 ∧ 0 < lam ∧ 0 < a ∧ 0 < D ∧ 0 < M₀ ∧ 0 < R ∧
      ∀ x ∈ K,
      let T := etaDenom M x.1
      let S := coords T (s M h ℓ x.1 x.2.1)
      let H := coords T (height M p x.1 x.2.2)
      η ≤ x.1.im ∧ η ≤ T.im ∧ η ≤ ‖T‖ ∧ ‖T‖ ≤ R ∧
      η ≤ ‖e x.1‖ ∧ ‖e x.1‖ ≤ r ∧
      η ≤ ‖e (etaMobius M x.1)‖ ∧ ‖e (etaMobius M x.1)‖ ≤ r ∧
      η ≤ S.1 ∧ η ≤ S.2 ∧ (M 1 0 : ℝ) * δ + η ≤ H.1 ∧
      (M 1 0 : ℝ) * δ + η ≤ H.2 ∧ S.1 + H.1 ≤ 1 - η ∧ S.2 + H.2 ≤ 1 - η ∧
      ‖A ℓ x.1 x.2.1‖ ^ (M 1 0).toNat ≤ r ∧
      ‖B M h x.1 x.2.1 x.2.2‖ ^ (M 1 0).toNat ≤ r ∧
      (∀ θ ∈ Icc T.arg (Real.pi / 2 + ψ),
        lam ≤ (upperSlope M h ℓ x.1 x.2.1 * rotation θ).im) ∧
      (∀ θ ∈ Icc (-Real.pi / 2 + ψ) 0,
        lam ≤ (lowerSlope M h ℓ p x.1 x.2.1 x.2.2 * rotation θ).im ∧
        a ≤ -(Real.pi * (M 1 0 : ℝ) / ‖T‖) * Real.sin (2 * θ - T.arg)) ∧
      ((M 1 0 : ℝ) ^ 2 / 2) * Real.log ‖e (etaMobius M x.1)‖ ≤ -a ∧
      (∀ m ∈ Finset.range (M 1 0).toNat,
        (let z := base M (m : ℤ) n δ x.1;
          ‖aArg (m : ℤ) x.1 z‖ ≤ r ∧ ‖bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ r ∧
          ‖dArg M n x.1 z‖ ≤ r ∧ ‖cArg M n x.1 x.2.2 z‖ ≤ r ∧
          ‖e x.1 / aArg (m : ℤ) x.1 z‖ ≤ r ∧
          ‖e (etaMobius M x.1) / dArg M n x.1 z‖ ≤ r ∧
          ‖e x.1 / bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ r ∧
          ‖e (etaMobius M x.1) / cArg M n x.1 x.2.2 z‖ ≤ r) ∧
        (∀ z ∈ templates M (m : ℤ) n δ x.1,
          ‖aArg (m : ℤ) x.1 z‖ ≤ r ∧
          ‖e (etaMobius M x.1) / dArg M n x.1 z‖ ≤ r ∧
          ‖bArg (m : ℤ) p x.1 x.2.2 z‖ ≤ D ∧
          ‖e (etaMobius M x.1) / cArg M n x.1 x.2.2 z‖ ≤ D ∧
          ‖C M h x.1 x.2.1 / dArg M n x.1 z‖ ≤ D ∧
          ‖singleKernel M (m : ℤ) n h ℓ x.1 x.2.1 z‖ ≤ M₀ ∧
          ‖ratioKernel M (m : ℤ) n h ℓ p x.1 x.2.1 x.2.2 z‖ ≤ M₀)) := by
  obtain ⟨ηp, R, rp, hηp, hR, hrp, hrp1, hp⟩ :=
    compact_parameter_bounds M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨ηc, hηc, hcoord⟩ := compact_coordinate_margin M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨rA, rB, hrA, hrA1, hrB, hrB1, hAB⟩ :=
    compact_AB_rates M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨rv, hrv, hrv1, hv⟩ := compact_vertex_margin M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨rt, D, hrt, hrt1, hD, ht⟩ :=
    compact_template_arguments M h ℓ p n ψ σ ρ δ hc K hK hKU
  obtain ⟨lam, hlam, hlinear⟩ := compact_arc_linear_margin M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨a, ha, hquadratic⟩ := compact_quadratic_margin M h ℓ p ψ σ ρ δ hc K hK hKU
  obtain ⟨M₀, hM₀, hkernel⟩ := compact_template_kernel_bounds M h ℓ p n ψ σ ρ δ hc K hK hKU
  let r := max rp (max rA (max rB (max rv rt)))
  have hpr : rp ≤ r := le_max_left _ _
  have hAr : rA ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hBr : rB ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hvr : rv ≤ r := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have htr : rt ≤ r := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨min ηp ηc, r, lam, a, D, M₀, R, lt_min hηp hηc,
    hrp.trans_le hpr, max_lt hrp1 (max_lt hrA1 (max_lt hrB1 (max_lt hrv1 hrt1))),
    hlam, ha, hD, hM₀, hR, ?_⟩
  intro x hx
  obtain ⟨hτi, hTi, _, _, hTn, hTnR, hq0, hqr, hQ0, hQr, _, _⟩ := hp x hx
  obtain ⟨hS₁, hS₂, hH₁, hH₂, hsum₁, hsum₂⟩ := hcoord x hx
  have hηp' := min_le_left ηp ηc
  have hηc' := min_le_right ηp ηc
  refine ⟨hηp'.trans hτi, hηp'.trans hTi, hηp'.trans hTn, hTnR,
    hηp'.trans hq0, hqr.trans hpr, hηp'.trans hQ0, hQr.trans hpr,
    hηc'.trans hS₁, hηc'.trans hS₂,
    (by linarith), (by linarith),
    hsum₁.trans (by linarith), hsum₂.trans (by linarith),
    (hAB x hx).1.trans hAr, (hAB x hx).2.trans hBr,
    (hlinear x hx).1, ?_, (hquadratic x hx).1, ?_⟩
  · intro θ hθ
    exact ⟨(hlinear x hx).2 θ hθ, (hquadratic x hx).2 θ hθ⟩
  · intro m hm
    obtain ⟨hva, hvb, hvd, hvc, hvqa, hvQd, hvqb, hvQc⟩ := hv x hx m hm
    refine ⟨⟨hva.trans hvr, hvb.trans hvr, hvd.trans hvr, hvc.trans hvr,
      hvqa.trans hvr, hvQd.trans hvr, hvqb.trans hvr, hvQc.trans hvr⟩, ?_⟩
    intro z hz
    obtain ⟨hta, htQd, htb, htQc, htCd⟩ := ht x hx m hm z hz
    exact ⟨hta.trans htr, htQd.trans htr, htb, htQc, htCd,
      (hkernel x hx m hm z hz).1, (hkernel x hx m hm z hz).2⟩

#check exists_closedBall
#check compact_parameter_bounds
#check compact_common_margins
#print axioms compact_common_margins

end SICLean.L4.UpperWindow
