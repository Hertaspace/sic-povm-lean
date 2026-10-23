import SICLean.L4.G2KernelConvergence
import SICLean.L4.G2ExactTelescopingAux

set_option autoImplicit false

/-!
Exact chain equalities and Euclidean reindexing. [RW26, pp. 12--13]. The actual chains and the two
substitutions are formalized here. No homotopy or residue theorem is used for this reindexing.
Auxiliary definitions belong to this file's own namespace Telescoping.
-/

noncomputable section
open Classical Complex Set Filter MeasureTheory
open scoped Topology BigOperators Interval MatrixGroups

namespace SICLean.L4.G2
namespace Telescoping

/-- Translation of all chain data, including the radius function. -/
def translateChain (D : G1VerticalChain) (q : ℝ) : G1VerticalChain where
  crossing := D.crossing + q
  centers := D.centers.image (fun r => r + q)
  radius := fun r => D.radius (r - q)

def newIndex (M : SL(2, ℤ)) (r : ℤ) : ℤ := (r + M 0 0 - 1) % M 1 0

def integerQuotient (M : SL(2, ℤ)) (r : ℤ) : ℤ := (r + M 0 0 - 1) / M 1 0

def differenceKernel (M : SL(2, ℤ)) (u v : ℤ × ℤ) (m : ℤ) (z : ℂ) : ℂ :=
  rawF M u v m z - rawF M u v (m + 1 - M 0 0) (z + (translate M : ℂ))

/-- The raw integral, summed over m. The terminal index c means D_m-L₂. -/
def rawIntegral (M : SL(2, ℤ)) (u v : ℤ × ℤ) (D : G1VerticalChain) : ℂ :=
  ∑ m : Fin (M 1 0).toNat,
    (g1ChainIntegral (componentChain M D (m : ℤ) 0) (rawF M u v (m : ℤ)) -
      g1ChainIntegral (componentChain M D (m : ℤ) (M 1 0)) (rawF M u v (m : ℤ)))

/-- Translating a parametrized chain translates its integral exactly; [RW26, p. 13]. -/
theorem translateChain_integral (D : G1VerticalChain) (q : ℝ) (f : ℂ → ℂ) :
    g1ChainIntegral (translateChain D q) f =
      g1ChainIntegral D (fun z => f (z + (q : ℂ))) := by
  simp only [g1ChainIntegral, translateChain]
  rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h)]
  congr 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      dsimp [g1VerticalPullback]
      congr 1
      simp only [g1VerticalPoint, Complex.ofReal_add]
      ring
  · apply Finset.sum_congr rfl
    intro r hr
    apply intervalIntegral.integral_congr
    intro θ hθ
    simp only [g1CirclePullback, add_sub_cancel_right]
    have hc : circleMap ((r + q : ℝ) : ℂ) (D.radius r) θ =
        circleMap (r : ℂ) (D.radius r) θ + (q : ℂ) := by
      simp only [circleMap, Complex.ofReal_add]
      ring
    rw [hc]
    congr 1
    push_cast
    ring

/-- D_{m+c}-jΔ=(D_m-jΔ)-ε as actual chain data; [RW26, p. 12]. -/
theorem componentChain_period (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j : ℤ) :
    componentChain M D (m + M 1 0) j =
      translateChain (componentChain M D m j) (-epsilon M) := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  simp only [componentChain, translateChain, Finset.image_image]
  congr 1
  · push_cast
    field_simp
    <;> ring
  · apply congrArg (fun f : ℝ → ℝ => Finset.image f D.centers)
    funext r
    dsimp
    push_cast
    field_simp
    <;> ring
  · funext r
    congr 2
    push_cast
    ring

/-- D_{m+1-a}-(j+1)Δ=(D_m-jΔ)+(aτ+b), with no deformation; [RW26, pp. 12--13]. -/
theorem componentChain_fixed_translate (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j : ℤ) :
    componentChain M D (m + 1 - M 0 0) (j + 1) =
      translateChain (componentChain M D m j) (translate M) := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  have ht := fixedPoint_translate M hM
  change (M 1 0 : ℝ) * translate M = (M 0 0 : ℝ) * epsilon M - 1 at ht
  simp only [componentChain, translateChain, Finset.image_image]
  congr 1
  · push_cast
    apply (div_eq_iff hc).2
    simp only [add_mul, div_mul_cancel₀ _ hc]
    dsimp [length]
    nlinarith [ht]
  · apply congrArg (fun f : ℝ → ℝ => Finset.image f D.centers)
    funext r
    dsimp
    push_cast
    apply (div_eq_iff hc).2
    simp only [add_mul, div_mul_cancel₀ _ hc]
    dsimp [length]
    nlinarith [ht]
  · funext r
    congr 2
    push_cast
    dsimp [length]
    nlinarith [ht]

/-- Arbitrary positive or negative integer quotient k, not only k=1. [RW26, p. 12]. -/
theorem componentChain_integer_period (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (m j k : ℤ) :
    componentChain M D (m + M 1 0 * k) j =
      translateChain (componentChain M D m j) (-(k : ℝ) * epsilon M) := by
  have hc : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM.1
  simp only [componentChain, translateChain, Finset.image_image]
  congr 1
  · push_cast
    field_simp
    <;> ring
  · apply congrArg (fun f : ℝ → ℝ => Finset.image f D.centers)
    funext r
    dsimp
    push_cast
    field_simp
    <;> ring
  · funext r
    congr 2
    push_cast
    ring

/-- Companion exact point identity for both raw functions and any k; [RW26, p. 13]. -/
theorem raw_integer_period (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m k : ℤ) (z : ℂ) :
    rawF M u v (m + M 1 0 * k) (z - (k : ℂ) * (epsilon M : ℂ)) = rawF M u v m z ∧
    rawG M u (m + M 1 0 * k) (z - (k : ℂ) * (epsilon M : ℂ)) = rawG M u m z := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    constructor
    · convert (rawF_period M hM u v (m + M 1 0 * (k : ℤ))
        (z - (k : ℂ) * (epsilon M : ℂ))).trans ih.1 using 1 <;>
        push_cast <;> ring
    · convert (rawG_period M hM u (m + M 1 0 * (k : ℤ))
        (z - (k : ℂ) * (epsilon M : ℂ))).trans ih.2 using 1 <;>
        push_cast <;> ring
  | pred k ih =>
    constructor
    · calc
        _ = rawF M u v (m + M 1 0 * (-(k : ℤ)))
            (z - ((-(k : ℤ) : ℤ) : ℂ) * (epsilon M : ℂ)) := by
          convert (rawF_period M hM u v (m + M 1 0 * (-(k : ℤ) - 1))
            (z - ((-(k : ℤ) - 1 : ℤ) : ℂ) * (epsilon M : ℂ))).symm using 1 <;>
            push_cast <;> ring
        _ = _ := ih.1
    · calc
        _ = rawG M u (m + M 1 0 * (-(k : ℤ)))
            (z - ((-(k : ℤ) : ℤ) : ℂ) * (epsilon M : ℂ)) := by
          convert (rawG_period M hM u (m + M 1 0 * (-(k : ℤ) - 1))
            (z - ((-(k : ℤ) - 1 : ℤ) : ℂ) * (epsilon M : ℂ))).symm using 1 <;>
            push_cast <;> ring
        _ = _ := ih.2

/-- The two actual substitutions z'=z+kε and z'=z''+A both have Jacobian 1. [RW26, p. 13]. -/
theorem reindexing_jacobians (M : SL(2, ℤ)) (k : ℤ) (z : ℂ) :
    HasDerivAt (fun ζ : ℂ => ζ + (k : ℂ) * (epsilon M : ℂ)) 1 z ∧
    HasDerivAt (fun ζ : ℂ => ζ + (translate M : ℂ)) 1 z := by
  exact ⟨(hasDerivAt_id z).add_const _, (hasDerivAt_id z).add_const _⟩

/-- Explicit Euclidean division, r=m+1-a+ck, 0≤m<c. [RW26, p. 12]. -/
theorem reindexing_divmod (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) (r : ℤ) :
    0 ≤ newIndex M r ∧ newIndex M r < M 1 0 ∧
      r = newIndex M r + 1 - M 0 0 + M 1 0 * integerQuotient M r := by
  refine ⟨Int.emod_nonneg _ (ne_of_gt hM.1), Int.emod_lt_of_pos _ hM.1, ?_⟩
  have h := Int.mul_ediv_add_emod (r + M 0 0 - 1) (M 1 0)
  dsimp [newIndex, integerQuotient]
  omega

/-- The finite permutation is on integer representatives, not on a presumed cyclic SIC quotient
group. [RW26, p. 12]. -/
theorem reindexing_bijOn (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M) :
    Set.BijOn (newIndex M) (Ico 0 (M 1 0)) (Ico 0 (M 1 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact ⟨(reindexing_divmod M hM r).1, (reindexing_divmod M hM r).2.1⟩
  · intro r hr s hs hrs
    have he : r ≡ s [ZMOD M 1 0] :=
      Int.ModEq.add_right_cancel' (M 0 0 - 1) (by
        simpa only [Int.ModEq, newIndex, sub_eq_add_neg, add_assoc] using hrs)
    have hr' := Int.emod_eq_of_lt hr.1 hr.2
    have hs' := Int.emod_eq_of_lt hs.1 hs.2
    simpa only [Int.ModEq, hr', hs'] using he
  · intro m hm
    refine ⟨(m + 1 - M 0 0) % M 1 0,
      ⟨Int.emod_nonneg _ (ne_of_gt hM.1), Int.emod_lt_of_pos _ hM.1⟩, ?_⟩
    dsimp [newIndex]
    have he : (m + 1 - M 0 0) % M 1 0 + M 0 0 - 1 ≡ m [ZMOD M 1 0] := by
      convert (Int.mod_modEq (m + 1 - M 0 0) (M 1 0)).add_right (M 0 0 - 1) using 1 <;>
        ring
    exact he.eq.trans (Int.emod_eq_of_lt hm.1 hm.2)

/-- The first substitution translates the old negative chain by +kε; the second subtracts A from the
resulting chain. Both equalities retain centers, radii and orientation. [RW26, p. 13]. -/
theorem negative_chain_substitutions (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (D : G1VerticalChain) (r j : ℤ) :
    translateChain (componentChain M D r (j + 1))
        ((integerQuotient M r : ℝ) * epsilon M) =
      componentChain M D (newIndex M r + 1 - M 0 0) (j + 1) ∧
    translateChain (componentChain M D (newIndex M r + 1 - M 0 0) (j + 1))
        (-translate M) = componentChain M D (newIndex M r) j := by
  have hcancel (E : G1VerticalChain) (q : ℝ) :
      translateChain (translateChain E q) (-q) = E := by
    cases E
    simp only [translateChain, Finset.image_image, Function.comp_def, add_neg_cancel_right,
      sub_neg_eq_add, add_sub_cancel_right, Finset.image_id']
  constructor
  · nth_rw 1 [(reindexing_divmod M hM r).2.2]
    rw [componentChain_integer_period M hM]
    simpa only [neg_mul, neg_neg] using
      hcancel (componentChain M D (newIndex M r + 1 - M 0 0) (j + 1))
        (-(integerQuotient M r : ℝ) * epsilon M)
  · rw [componentChain_fixed_translate M hM]
    exact hcancel _ _

/-- Integral form of those same two substitutions, with integrability already supplied by
G2KernelConvergence. [RW26, p. 13]. -/
theorem negative_integral_substitutions (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (r j : Fin (M 1 0).toNat) :
    g1ChainIntegral (componentChain M D (r : ℤ) ((j : ℤ) + 1)) (rawF M u v (r : ℤ)) =
      g1ChainIntegral
        (componentChain M D (newIndex M (r : ℤ) + 1 - M 0 0) ((j : ℤ) + 1))
        (rawF M u v (newIndex M (r : ℤ) + 1 - M 0 0)) ∧
    g1ChainIntegral
        (componentChain M D (newIndex M (r : ℤ) + 1 - M 0 0) ((j : ℤ) + 1))
        (rawF M u v (newIndex M (r : ℤ) + 1 - M 0 0)) =
      g1ChainIntegral (componentChain M D (newIndex M (r : ℤ)) (j : ℤ))
        (fun z => rawF M u v (newIndex M (r : ℤ) + 1 - M 0 0) (z + (translate M : ℂ))) := by
  constructor
  · have hr := (reindexing_divmod M hM (r : ℤ)).2.2
    have hchain : componentChain M D (r : ℤ) ((j : ℤ) + 1) =
        translateChain
          (componentChain M D (newIndex M (r : ℤ) + 1 - M 0 0) ((j : ℤ) + 1))
          (-(integerQuotient M (r : ℤ) : ℝ) * epsilon M) := by
      nth_rw 1 [hr]
      exact componentChain_integer_period M hM D _ _ _
    rw [hchain, translateChain_integral]
    congr 1
    funext z
    have hp := (raw_integer_period M hM u v
      (newIndex M (r : ℤ) + 1 - M 0 0) (integerQuotient M (r : ℤ)) z).1
    rw [← hr] at hp
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_intCast,
      neg_mul, ← sub_eq_add_neg] using hp
  · rw [componentChain_fixed_translate M hM, translateChain_integral]

/-- First finite telescope: D_m-(D_m-L₂) split into c adjacent pairs; [RW26, p. 13]. -/
theorem finite_telescope (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (D : G1VerticalChain) :
    rawIntegral M u v D =
      ∑ j : Fin (M 1 0).toNat, ∑ m : Fin (M 1 0).toNat,
        (g1ChainIntegral (componentChain M D (m : ℤ) (j : ℤ)) (rawF M u v (m : ℤ)) -
          g1ChainIntegral (componentChain M D (m : ℤ) ((j : ℤ) + 1)) (rawF M u v (m : ℤ))) := by
  unfold rawIntegral
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  let f : ℕ → ℂ := fun j =>
    g1ChainIntegral (componentChain M D (m : ℤ) (j : ℤ)) (rawF M u v (m : ℤ))
  have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg (le_of_lt hM.1)
  have hs := Fin.sum_univ_eq_sum_range (fun j => f j - f (j + 1)) (M 1 0).toNat
  rw [Finset.sum_range_sub'] at hs
  simpa only [f, Nat.cast_add, Nat.cast_one, Nat.cast_zero, hc] using hs.symm

/-- Sum form of the explicit finite permutation and its two substitutions; [RW26, p. 13]. -/
theorem reindexed_negative_sum (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D)
    (j : Fin (M 1 0).toNat) :
    (∑ r : Fin (M 1 0).toNat,
      g1ChainIntegral (componentChain M D (r : ℤ) ((j : ℤ) + 1)) (rawF M u v (r : ℤ))) =
    ∑ m : Fin (M 1 0).toNat,
      g1ChainIntegral (componentChain M D (m : ℤ) (j : ℤ))
        (fun z => rawF M u v ((m : ℤ) + 1 - M 0 0) (z + (translate M : ℂ))) := by
  have hc : ((M 1 0).toNat : ℤ) = M 1 0 := Int.toNat_of_nonneg (le_of_lt hM.1)
  have hrange (r : Fin (M 1 0).toNat) : (r : ℤ) ∈ Ico 0 (M 1 0) := by
    have h := r.isLt
    constructor <;> omega
  let idx : Fin (M 1 0).toNat → Fin (M 1 0).toNat := fun r =>
    ⟨(newIndex M (r : ℤ)).toNat, by
      have h := reindexing_divmod M hM (r : ℤ)
      omega⟩
  have hidx (r : Fin (M 1 0).toNat) : (idx r : ℤ) = newIndex M (r : ℤ) := by
    exact Int.toNat_of_nonneg (reindexing_divmod M hM (r : ℤ)).1
  have hbij : Function.Bijective idx := by
    constructor
    · intro r s hrs
      have h := (reindexing_bijOn M hM).2.1 (hrange r) (hrange s)
        (by rw [← hidx r, ← hidx s, hrs])
      exact Fin.ext (by exact_mod_cast h)
    · intro m
      obtain ⟨r, hr, he⟩ := (reindexing_bijOn M hM).2.2 (hrange m)
      have hr0 : 0 ≤ r := hr.1
      have hrlt : r < M 1 0 := hr.2
      let r' : Fin (M 1 0).toNat := ⟨r.toNat, by omega⟩
      refine ⟨r', ?_⟩
      apply Fin.ext
      have hr' : (r' : ℤ) = r := Int.toNat_of_nonneg hr.1
      have h : (idx r' : ℤ) = (m : ℤ) := by rw [hidx, hr', he]
      exact_mod_cast h
  apply Fintype.sum_bijective idx hbij
  intro r
  have h := negative_integral_substitutions M hM u v hwin δ D hD r j
  simpa only [hidx] using h.1.trans h.2

/-- Exact reindexing, with no analytic deformation between the chains; [RW26, p. 13]. -/
theorem exact_telescope (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    rawIntegral M u v D =
      ∑ j : Fin (M 1 0).toNat, ∑ m : Fin (M 1 0).toNat,
        g1ChainIntegral (componentChain M D (m : ℤ) (j : ℤ))
          (differenceKernel M u v (m : ℤ)) := by
  rw [finite_telescope M hM u v D]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_sub_distrib, reindexed_negative_sum M hM u v hwin δ D hD j,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hj0 : (j : ℕ) < (M 1 0).toNat + 1 := by omega
  have hj1 : (j : ℕ) + 1 < (M 1 0).toNat + 1 := by omega
  have hf := rawF_chain_integrable M hM u v hwin δ D hD (m : ℤ)
    (⟨(j : ℕ), hj0⟩ : Fin ((M 1 0).toNat + 1))
  have hg := rawF_chain_integrable M hM u v hwin δ D hD ((m : ℤ) + 1 - M 0 0)
    (⟨(j : ℕ) + 1, hj1⟩ : Fin ((M 1 0).toNat + 1))
  have hg' : G1ChainIntegrable
      (translateChain (componentChain M D (m : ℤ) (j : ℤ)) (translate M))
      (rawF M u v ((m : ℤ) + 1 - M 0 0)) := by
    convert hg using 1
    simp only [Nat.cast_add, Nat.cast_one]
    exact (componentChain_fixed_translate M hM D (m : ℤ) (j : ℤ)).symm
  have htrans := (G2ExactTelescopingAux.chain_integrable_translate_iff
    (componentChain M D (m : ℤ) (j : ℤ)) (translate M)
    (rawF M u v ((m : ℤ) + 1 - M 0 0))).1 hg'
  exact (G2ExactTelescopingAux.chain_integral_sub _ _ _ hf htrans).symm

/-- Germ-to-integral bridge: the only real parameter exceptions on a line or nondegenerate circle
are null. No nonvanishing demand at denominator poles is added; [RW26, p. 13]. -/
theorem difference_pullbacks_ae (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (m : ℤ) (x r ρ : ℝ) (hρ : 0 < ρ) :
    (g1VerticalPullback (differenceKernel M u v m) x) =ᵐ[volume]
      (fun t => (1 - phaseT M v) * g1VerticalPullback (ratioKernel M u v m) x t) ∧
    (g1CirclePullback (differenceKernel M u v m) r ρ) =ᵐ[volume]
      (fun θ => (1 - phaseT M v) * g1CirclePullback (ratioKernel M u v m) r ρ θ) := by
  have hfg : ∀ z : ℂ, z.im ≠ 0 →
      differenceKernel M u v m z = (1 - phaseT M v) * ratioKernel M u v m z :=
    rawF_difference_nonreal M hM u v m
  exact ⟨G2ExactTelescopingAux.vertical_pullback_ae_of_off_real _ _ _ hfg x,
    G2ExactTelescopingAux.circle_pullback_ae_of_off_real _ _ _ hfg r ρ hρ⟩

/-- Ready for the c separate G1 calls. [RW26, p. 13]. -/
theorem telescope_to_ratio (M : SL(2, ℤ)) (hM : SpecialValueAdmissible M)
    (u v : ℤ × ℤ) (hwin : RepresentativeWindow M u v)
    (δ : ℝ) (D : G1VerticalChain) (hD : CommonChain M v δ D) :
    rawIntegral M u v D = (1 - phaseT M v) *
      ∑ j : Fin (M 1 0).toNat, ∑ m : Fin (M 1 0).toNat,
        g1ChainIntegral (componentChain M D (m : ℤ) (j : ℤ)) (ratioKernel M u v (m : ℤ)) := by
  rw [exact_telescope M hM u v hwin δ D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro m hm
  have hs := componentChain_g1_separates M hM u v hwin δ D hD (m : ℤ) j
  apply G2ExactTelescopingAux.chain_integral_eq_const_mul_of_pullbacks_ae
  · exact (difference_pullbacks_ae M hM u v (m : ℤ)
      (componentChain M D (m : ℤ) (j : ℤ)).crossing 0 1 (by norm_num)).1
  · intro r hr
    exact (difference_pullbacks_ae M hM u v (m : ℤ)
      (componentChain M D (m : ℤ) (j : ℤ)).crossing r
      ((componentChain M D (m : ℤ) (j : ℤ)).radius r) (hs.1 r hr)).2

#print integerQuotient
#print negative_chain_substitutions
#check difference_pullbacks_ae
#check telescope_to_ratio

end Telescoping
end SICLean.L4.G2
