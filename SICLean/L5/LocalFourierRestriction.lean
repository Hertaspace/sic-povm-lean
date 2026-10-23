import SICLean.L5.LocalFourierSetup
import SICLean.L5.LocalFourierRestrictionAux

set_option autoImplicit false

/-!
# Local Fourier restriction to the primary part

[RW-rec, Lemma 1, p. 5] with the geometric identification in (p. 6). The raw restriction
formula avoids assuming separate square roots of `|H|` and `|C|`. Its factor is `r/|C|`.
No symmetric pairing or Fourier-square identity is assumed.
-/

noncomputable section

open scoped BigOperators

namespace SICLean.L5.LocalFourierRestriction

open FiniteCosetMoments LocalFourierSetup

variable {p s d : ℕ} [Fact p.Prime]
variable {L G C : Type*} [Field L] [CharZero L]
variable [AddCommGroup G] [Fintype G] [AddCommGroup C] [Fintype C]

/-- [RW-rec]: the literal slice at a complementary component. -/
def primarySlice (e : (Point p s d × C) ≃+ G) (f : G → L) (c : C) :
    Point p s d → L := fun h => f (e (h, c))

/-- Restrict the actual bicharacter, rather than replacing its values. -/
def primaryPairing (e : (Point p s d × C) ≃+ G) (B : G → G → L) :
    Point p s d → Point p s d → L := fun x y => B (e (x, 0)) (e (y, 0))

/-- [RW-rec]: coprime primary summands are orthogonal in both directions. -/
theorem cross_pairing_eq_one (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s d × C) ≃+ G)
    (B : G → G → L) (hB : IsBicharacter B) (h : Point p s d) (c : C) :
    B (e (h, 0)) (e (0, c)) = 1 ∧ B (e (0, c)) (e (h, 0)) = 1 := by
  have hzeroL (y : G) : B 0 y = 1 := by
    apply mul_left_cancel₀ (hB.1 0 y)
    simpa only [zero_add, mul_one] using (hB.2.1 0 0 y).symm
  have hzeroR (x : G) : B x 0 = 1 := by
    apply mul_left_cancel₀ (hB.1 x 0)
    simpa only [zero_add, mul_one] using (hB.2.2 x 0 0).symm
  let left (y : G) : AddChar G L := ⟨fun x => B x y, hzeroL y, fun x x' => hB.2.1 x x' y⟩
  let right (x : G) : AddChar G L := ⟨B x, hzeroR x, hB.2.2 x⟩
  have hH : (p ^ s) • e (h, 0) = 0 := by
    rw [← map_nsmul, ← e.map_zero]
    congr 1
    ext i
    · change (p ^ s) • h i = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    · simp
  have hcomp : Fintype.card C • e (0, c) = 0 := by
    rw [← map_nsmul, ← e.map_zero]
    congr 1
    simp
  have hcop := hC.pow_left s
  constructor
  · apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hcop
    · apply orderOf_dvd_of_pow_eq_one
      change (left (e (0, c))) (e (h, 0)) ^ (p ^ s) = 1
      rw [← AddChar.map_nsmul_eq_pow, hH, AddChar.map_zero_eq_one]
    · apply orderOf_dvd_of_pow_eq_one
      change (right (e (h, 0))) (e (0, c)) ^ Fintype.card C = 1
      rw [← AddChar.map_nsmul_eq_pow, hcomp, AddChar.map_zero_eq_one]
  · apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hcop
    · apply orderOf_dvd_of_pow_eq_one
      change (right (e (0, c))) (e (h, 0)) ^ (p ^ s) = 1
      rw [← AddChar.map_nsmul_eq_pow, hH, AddChar.map_zero_eq_one]
    · apply orderOf_dvd_of_pow_eq_one
      change (left (e (h, 0))) (e (0, c)) ^ Fintype.card C = 1
      rw [← AddChar.map_nsmul_eq_pow, hcomp, AddChar.map_zero_eq_one]

/-- [RW-rec]: restriction preserves the character laws and nondegeneracy. -/
theorem primaryPairing_nondegenerate (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s d × C) ≃+ G)
    (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B) :
    IsBicharacter (primaryPairing e B) ∧ Nondegenerate (primaryPairing e B) := by
  have headd (x y : Point p s d) : e (x + y, 0) = e (x, 0) + e (y, 0) := by
    rw [← e.map_add]
    simp
  refine ⟨⟨fun x y => hB.1 _ _, ?_, ?_⟩, ?_, ?_⟩
  · intro x x' y
    exact (congrArg (fun t => B t (e (y, 0))) (headd x x')).trans (hB.2.1 _ _ _)
  · intro x y y'
    exact (congrArg (B (e (x, 0))) (headd y y')).trans (hB.2.2 _ _ _)
  · intro x hx
    change ∀ y, B (e (x, 0)) (e (y, 0)) = 1 at hx
    have hz : e (x, 0) = 0 := hnd.1 _ (by
      intro y
      obtain ⟨⟨h, c⟩, rfl⟩ := e.surjective y
      have he : e (h, c) = e (h, 0) + e (0, c) := by
        rw [← e.map_add]
        simp
      rw [he, hB.2.2, hx h, (cross_pairing_eq_one hs hC e B hB x c).1, mul_one])
    exact congrArg Prod.fst (e.injective (hz.trans e.map_zero.symm))
  · intro y hy
    change ∀ x, B (e (x, 0)) (e (y, 0)) = 1 at hy
    have hz : e (y, 0) = 0 := hnd.2 _ (by
      intro x
      obtain ⟨⟨h, c⟩, rfl⟩ := e.surjective x
      have he : e (h, c) = e (h, 0) + e (0, c) := by
        rw [← e.map_add]
        simp
      rw [he, hB.2.1, hy h, (cross_pairing_eq_one hs hC e B hB y c).2, mul_one])
    exact congrArg Prod.fst (e.injective (hz.trans e.map_zero.symm))

/-- [RW-rec]: change frequency coordinates only; domain coordinates stay fixed for the later coset
charts. No symmetry of `B` is needed. -/
theorem exists_standard_primary_kernel (hs : 1 ≤ s) (hd : d = 1 ∨ d = 2)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s d × C) ≃+ G)
    (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B) :
    ∃ z : L, IsPrimitiveRoot z (p ^ s) ∧
      ∃ T : Point p s d ≃+ Point p s d,
        ∀ x y, primaryPairing e B x (T y) = z ^ (∑ i, (x i).val * (y i).val) := by
  obtain ⟨hBP, hndP⟩ := primaryPairing_nondegenerate hs hC e B hB hnd
  exact LocalFourierRestrictionAux.standard_kernel hs hd (primaryPairing e B) hBP hndP

/-- Cardinality helper of [RW-rec]. -/
theorem card_decomposition (e : (Point p s d × C) ≃+ G) :
    Fintype.card G = (p ^ s) ^ d * Fintype.card C := by
  rw [← Fintype.card_congr e.toEquiv, Fintype.card_prod]
  simp only [Point, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- [RW-rec]: integers prime to p are units for the normalized valuation. -/
theorem coprime_card_value (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hC : Nat.Coprime p (Fintype.card C)) :
    v (Fintype.card C : L) = 0 := by
  haveI := residue_charP v hp
  have hn : 0 ≤ v (Fintype.card C : L) := natCast_mem (integers v) _
  apply (reduce_ne_zero_iff v _ hn).mp
  rw [reduce_eq_residue v _ hn]
  change IsLocalRing.residue (integers v) (Fintype.card C : integers v) ≠ 0
  rw [map_natCast]
  intro h
  have hdiv := (CharP.cast_eq_zero_iff (Residue v) p _).mp h
  exact (Fact.out : p.Prime).ne_one (Nat.eq_one_of_dvd_coprimes hC dvd_rfl hdiv)

/-- [RW-rec]: any root normalizing the full Fourier sum has the right valuation. For actual E the
root is the existing positive-root algebraic lift. -/
theorem normalization_value (v : AddValuation L (WithTop ℝ))
    (hp : v (p : L) = 1) (hC : Nat.Coprime p (Fintype.card C))
    (e : (Point p s d × C) ≃+ G) (r : L) (hr : r ^ 2 = (Fintype.card G : L)) :
    v r = (((((d * s : ℕ) : ℝ) / 2) : ℝ) : WithTop ℝ) := by
  have hr0 : r ≠ 0 := by
    intro h
    have hcard : (Fintype.card G : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    apply hcard
    simpa [h] using hr.symm
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hr0)
  have hv := congrArg v hr
  rw [v.map_pow, card_decomposition e, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    v.map_mul, v.map_pow, v.map_pow, hp, coprime_card_value v hp hC, add_zero,
    ← ht] at hv
  have htval : 2 * t = (d : ℝ) * (s : ℝ) := by
    have hcoe : ((2 • t : ℝ) : WithTop ℝ) = ((d • (s • (1 : ℝ)) : ℝ) : WithTop ℝ) := by
      simpa only [WithTop.coe_nsmul, WithTop.coe_one] using hv
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] using WithTop.coe_eq_coe.mp hcoe
  rw [← ht]
  apply congrArg (fun a : ℝ => (a : WithTop ℝ))
  push_cast
  linarith

/-- [RW-rec] with raw H-transform: no additional square-root choices. -/
theorem raw_primarySlice_fourier (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s d × C) ≃+ G)
    (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B)
    (r : L) (hr : r ^ 2 = (Fintype.card G : L)) (f : G → L)
    (c : C) (a : Point p s d) :
    rawFourier (primaryPairing e B) (primarySlice e f c) a =
      (r / (Fintype.card C : L)) *
        ∑ b : C, B (e (0, c)) (e (0, b)) * fourier B r f (e (a, b)) := by
  classical
  have hzeroL (y : G) : B 0 y = 1 := by
    apply mul_left_cancel₀ (hB.1 0 y)
    simpa only [zero_add, mul_one] using (hB.2.1 0 0 y).symm
  have hzeroR (x : G) : B x 0 = 1 := by
    apply mul_left_cancel₀ (hB.1 x 0)
    simpa only [zero_add, mul_one] using (hB.2.2 x 0 0).symm
  let left (y : G) : AddChar G L := ⟨fun x => B x y, hzeroL y, fun x x' => hB.2.1 x x' y⟩
  let right (x : G) : AddChar G L := ⟨B x, hzeroR x, hB.2.2 x⟩
  have hneg (x y : G) : B x (-y) = B (-x) y :=
    ((right x).map_neg_eq_inv y).trans ((left y).map_neg_eq_inv x).symm
  have hezero : e (0, 0) = 0 := e.map_zero
  have heneg (b : C) : e (0, -b) = -e (0, b) := by
    rw [← e.map_neg]
    simp only [Prod.neg_mk, neg_zero]
  have he (h : Point p s d) (b : C) : e (h, b) = e (h, 0) + e (0, b) := by
    rw [← e.map_add]
    simp
  have hsplit (h k : Point p s d) (b b' : C) :
      B (e (h, b)) (e (k, b')) =
        B (e (h, 0)) (e (k, 0)) * B (e (0, b)) (e (0, b')) := by
    rw [he h b, he k b', hB.2.1, hB.2.2, hB.2.2,
      (cross_pairing_eq_one hs hC e B hB h b').1,
      (cross_pairing_eq_one hs hC e B hB k b).2]
    ring
  have hndC (z : C) (hz : ∀ b, B (e (0, z)) (e (0, b)) = 1) : z = 0 := by
    have hzero : e (0, z) = 0 := hnd.1 _ (by
      intro y
      obtain ⟨⟨h, b⟩, rfl⟩ := e.surjective y
      rw [he h b, hB.2.2, (cross_pairing_eq_one hs hC e B hB h z).2, hz, one_mul])
    exact congrArg Prod.snd (e.injective (hzero.trans e.map_zero.symm))
  let chi (z : C) : AddChar C L :=
    ⟨fun b => B (e (0, z)) (e (0, b)), by rw [hezero, hzeroR], by
      intro b b'
      change B (e (0, z)) (e (0, b + b')) = _
      rw [show e (0, b + b') = e (0, b) + e (0, b') by
        rw [← e.map_add]; simp]
      exact hB.2.2 _ _ _⟩
  have horth (b' : C) :
      (∑ b : C, B (e (0, c - b')) (e (0, b))) =
        if b' = c then (Fintype.card C : L) else 0 := by
    change (∑ b : C, chi (c - b') b) = _
    by_cases h : b' = c
    · subst b'
      simp [chi, hezero, hzeroL]
    · rw [ite_eq_right h]
      apply AddChar.sum_eq_zero_iff_ne_zero.mpr
      intro hchi
      apply h
      have hz : c - b' = 0 := hndC _ (by
        intro b
        have hh := DFunLike.congr_fun hchi b
        simpa only [chi, AddChar.coe_mk, AddChar.zero_apply] using hh)
      exact (sub_eq_zero.mp hz).symm
  have hkernel (h : Point p s d) (b' b : C) :
      B (e (0, c)) (e (0, b)) *
          (f (e (h, b')) * B (e (h, b')) (-e (a, b))) =
        (f (e (h, b')) * B (e (h, 0)) (e (-a, 0))) *
          B (e (0, c - b')) (e (0, b)) := by
    rw [show -e (a, b) = e (-a, -b) by rw [← e.map_neg]; rfl,
      hsplit h (-a) b' (-b)]
    have hh : B (e (0, b')) (e (0, -b)) = B (e (0, -b')) (e (0, b)) := by
      simpa only [heneg] using hneg (e (0, b')) (e (0, b))
    rw [hh, show e (0, c - b') = e (0, c) + e (0, -b') by
      rw [← e.map_add]; simp [sub_eq_add_neg], hB.2.1]
    ring
  have hsumG (g : G → L) : (∑ x : G, g x) =
      ∑ h : Point p s d, ∑ b' : C, g (e (h, b')) := by
    simpa only [Fintype.sum_prod_type] using
      (Fintype.sum_equiv e.toEquiv (fun hc => g (e hc)) g (fun _ => rfl)).symm
  have hsum : (∑ b : C, B (e (0, c)) (e (0, b)) * fourier B r f (e (a, b))) =
      r⁻¹ * ((Fintype.card C : L) *
        rawFourier (primaryPairing e B) (primarySlice e f c) a) := by
    unfold fourier
    simp_rw [hsumG]
    have hreorder :
        (∑ b : C, B (e (0, c)) (e (0, b)) *
          (r⁻¹ * ∑ h : Point p s d, ∑ b' : C,
            f (e (h, b')) * B (e (h, b')) (-e (a, b)))) =
        r⁻¹ * ∑ h : Point p s d, ∑ b' : C, ∑ b : C,
          B (e (0, c)) (e (0, b)) *
            (f (e (h, b')) * B (e (h, b')) (-e (a, b))) := by
      calc
        _ = r⁻¹ * ∑ b : C, ∑ h : Point p s d, ∑ b' : C,
            B (e (0, c)) (e (0, b)) *
              (f (e (h, b')) * B (e (h, b')) (-e (a, b))) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro h _
          apply Finset.sum_congr rfl
          intro b' _
          ring
        _ = _ := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h _
          rw [Finset.sum_comm]
    rw [hreorder]
    simp_rw [hkernel, ← Finset.mul_sum, horth]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    unfold rawFourier primaryPairing primarySlice
    simp only [← Finset.sum_mul]
    ring
  rw [hsum]
  have hr0 : r ≠ 0 := by
    intro h
    have hcard : (Fintype.card G : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    apply hcard
    simpa [h] using hr.symm
  have hcardC : (Fintype.card C : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- [RW-rec]: integrality of the full transform gives the raw H bound. -/
theorem raw_primarySlice_value_ge (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s d × C) ≃+ G)
    (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B)
    (r : L) (hr : r ^ 2 = (Fintype.card G : L))
    (v : AddValuation L (WithTop ℝ)) (hp : v (p : L) = 1)
    (f : G → L) (hF : Integral v (fourier B r f)) (c : C) (a : Point p s d) :
    (((((d * s : ℕ) : ℝ) / 2) : ℝ) : WithTop ℝ) ≤
      v (rawFourier (primaryPairing e B) (primarySlice e f c) a) := by
  rw [raw_primarySlice_fourier hs hC e B hB hnd r hr, v.map_mul, v.map_div,
    coprime_card_value v hp hC, sub_zero, normalization_value v hp hC e r hr]
  have hsum : (0 : WithTop ℝ) ≤
      v (∑ b : C, B (e (0, c)) (e (0, b)) * fourier B r f (e (a, b))) := by
    apply v.map_le_sum
    intro b _
    rw [v.map_mul, bicharacter_value_zero v B hB, zero_add]
    exact hF _
  simpa only [add_zero, zero_add] using add_le_add_right hsum
    (((((d * s : ℕ) : ℝ) / 2) : ℝ) : WithTop ℝ)

/-- [RW-rec] applied after a translation. A positive shift produces the positive character, as in
existing `FiniteFourier.fourier_translate`. -/
theorem fourier_translate (B : G → G → L) (hB : IsBicharacter B)
    (r : L) (f : G → L) (x y : G) :
    fourier B r (fun t => f (x + t)) y = B x y * fourier B r f y := by
  classical
  have hz : B x 0 = 1 := by
    apply mul_left_cancel₀ (hB.1 x 0)
    simpa only [zero_add, mul_one] using (hB.2.2 x 0 0).symm
  have hinv : B x y * B x (-y) = 1 := by
    rw [← hB.2.2, add_neg_cancel, hz]
  unfold fourier
  have hs : (∑ t, f (x + t) * B t (-y)) =
      ∑ t, B x y * (f (x + t) * B (x + t) (-y)) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [hB.2.1]
    linear_combination -(f (x + t) * B t (-y)) * hinv
  have hshift : (∑ t, f (x + t) * B (x + t) (-y)) =
      ∑ t, f t * B t (-y) :=
    Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
  rw [hs, ← Finset.mul_sum, hshift]
  ring

/-- [RW-rec]: shifted functions retain the transform hypothesis. -/
theorem integral_fourier_translate (B : G → G → L) (hB : IsBicharacter B)
    (r : L) (v : AddValuation L (WithTop ℝ)) (f : G → L)
    (hF : Integral v (fourier B r f)) (x : G) :
    Integral v (fourier B r (fun t => f (x + t))) := by
  intro y
  rw [fourier_translate B hB, v.map_mul, bicharacter_value_zero v B hB, zero_add]
  exact hF y

/-- [RW-rec]: each coordinate chart is one-to-one. -/
theorem cosetChart_injective (hs : 1 ≤ s) (e : (Point p s d × C) ≃+ G)
    (x : G) (a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p)) :
    Function.Injective (cosetChart e x a) := by
  intro u w huw
  apply a.injective
  have htop := congrArg Prod.fst (e.injective (add_left_cancel huw))
  have hq : 0 < p ^ (s - 1) := pow_pos (Fact.out : p.Prime).pos _
  have hpow : p ^ (s - 1) * p = p ^ s := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  funext i
  apply ZMod.val_injective
  have hi := congrArg (fun t => (t i).val) htop
  change (((p ^ (s - 1) * (a u i).val : ℕ) : ZMod (p ^ s))).val =
    (((p ^ (s - 1) * (a w i).val : ℕ) : ZMod (p ^ s))).val at hi
  rw [ZMod.val_natCast_of_lt (by
    rw [← hpow]
    exact Nat.mul_lt_mul_of_pos_left (a u i).val_lt hq),
    ZMod.val_natCast_of_lt (by
      rw [← hpow]
      exact Nat.mul_lt_mul_of_pos_left (a w i).val_lt hq)] at hi
  exact Nat.eq_of_mul_eq_mul_left hq hi

/-- [RW-rec]: cardinality of the actual small coset. -/
theorem card_pTorsion_coset (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s d × C) ≃+ G) (x : G) :
    Nat.card {y : G // p • (y - x) = 0} = p ^ d := by
  let a : (Fin d → ZMod p) ≃ᵃ[ZMod p] (Fin d → ZMod p) := AffineEquiv.refl _ _
  have hr := cosetChart_range hs hC e x a
  let chart : (Fin d → ZMod p) ≃ {y : G // p • (y - x) = 0} :=
    Equiv.ofBijective (fun u => ⟨cosetChart e x a u, by
      have : cosetChart e x a u ∈ Set.range (cosetChart e x a) := ⟨u, rfl⟩
      rwa [hr] at this⟩) ⟨by
        intro u w h
        exact cosetChart_injective hs e x a (congrArg Subtype.val h), by
        intro y
        have hy : (y : G) ∈ Set.range (cosetChart e x a) := by
          rw [hr]
          exact y.property
        obtain ⟨u, hu⟩ := hy
        exact ⟨u, Subtype.ext hu⟩⟩
  rw [← Nat.card_congr chart, Nat.card_eq_fintype_card]
  simp

#check @raw_primarySlice_fourier
#check @exists_standard_primary_kernel

end SICLean.L5.LocalFourierRestriction
