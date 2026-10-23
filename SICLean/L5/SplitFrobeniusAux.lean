import SICLean.L5.SplitPrimeValues
import SICLean.L5.DistributionGeneralValues
import SICLean.L5.OddPrimeUnits

set_option autoImplicit false

noncomputable section
open scoped NumberField BigOperators Classical

namespace SICLean.L5.SplitFrobeniusAux

open L3 SplitPrimeLattice SplitPrimeGeometry DistributionOrbitGeometry

variable {K : Type} [Field K] [NumberField K]

def residueOrder (P : PeriodData K) (r : FinitePlace.Prime K) : ℕ :=
  orderOf (Ideal.Quotient.mk r.asIdeal (epsilonInteger P))

theorem residueOrder_pos (P : PeriodData K) (r : FinitePlace.Prime K) :
    0 < residueOrder P r := by
  have hu := (OddPrimeUnits.epsilonInteger_isUnit P).map (Ideal.Quotient.mk r.asIdeal)
  exact hu.isOfFinOrder.orderOf_pos

/-- Coordinates preserve the order of the actual residue, since their kernel is precisely the chosen
prime. -/
theorem residueOrder_eq_coordinateOrder (P : PeriodData K) {p : ℕ}
    [Fact p.Prime] (r : FinitePlace.Prime K) (f : 𝓞 K →+* ZMod p)
    (hf : ∀ a : 𝓞 K, f a = 0 ↔ a ∈ r.asIdeal) :
    residueOrder P r = orderOf (f (epsilonInteger P)) := by
  let g : FinitePlace.Residue r →+* ZMod p :=
    Ideal.Quotient.lift r.asIdeal f (fun a ha => (hf a).2 ha)
  exact (orderOf_injective g.toMonoidHom g.injective
    (Ideal.Quotient.mk r.asIdeal (epsilonInteger P))).symm

theorem residueOrder_dvd_sub_one (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    residueOrder P r ∣ p - 1 := by
  letI : Fintype (FinitePlace.Residue r) := Fintype.ofFinite _
  have hu := (OddPrimeUnits.epsilonInteger_isUnit P).map (Ideal.Quotient.mk r.asIdeal)
  have he := FiniteField.pow_card_sub_one_eq_one
    (Ideal.Quotient.mk r.asIdeal (epsilonInteger P)) hu.ne_zero
  have hd := orderOf_dvd_of_pow_eq_one he
  have hcard := (split_residue_cards P hp h).1
  rw [Nat.card_eq_fintype_card] at hcard
  simpa only [residueOrder, hcard] using hd

theorem residueOrder_common_of_coordinates (P : PeriodData K) {p : ℕ}
    (hp : p.Prime) {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (ρ : 𝓞 K →+* ZMod p × ZMod p) (hρ : ResidueCoordinates p r q ρ)
    (hmul : (ρ (epsilonInteger P)).1 * (ρ (epsilonInteger P)).2 = 1) :
    residueOrder P r = residueOrder P q ∧ residueOrder P r ∣ p - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hx : (ρ (epsilonInteger P)).1 ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hmul
    exact zero_ne_one hmul
  have hinv : (ρ (epsilonInteger P)).2 = ((ρ (epsilonInteger P)).1)⁻¹ := by
    apply mul_left_cancel₀ hx
    rw [hmul, mul_inv_cancel₀ hx]
  refine ⟨?_, residueOrder_dvd_sub_one P hp h⟩
  rw [residueOrder_eq_coordinateOrder P r
      ((RingHom.fst (ZMod p) (ZMod p)).comp ρ) hρ.2.1,
    residueOrder_eq_coordinateOrder P q
      ((RingHom.snd (ZMod p) (ZMod p)).comp ρ) hρ.2.2]
  change orderOf (ρ (epsilonInteger P)).1 = orderOf (ρ (epsilonInteger P)).2
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  rw [hinv, inv_pow, inv_eq_one]

/-- Any two roots of a monic quadratic with constant coefficient one are equal or are multiplicative
inverses. -/
theorem quadratic_roots_eq_or_mul_eq_one {F : Type} [Field F]
    (a b T : F) (ha : a ^ 2 - T * a + 1 = 0)
    (hb : b ^ 2 - T * b + 1 = 0) : a = b ∨ a * b = 1 := by
  have hab : (a - b) * (a * b - 1) = 0 := by
    linear_combination b * ha - a * hb
  rcases mul_eq_zero.mp hab with hab | hab
  · exact Or.inl (sub_eq_zero.mp hab)
  · exact Or.inr (sub_eq_zero.mp hab)

theorem residueOrder_common (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    residueOrder P r = residueOrder P q ∧ residueOrder P r ∣ p - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ, hρ⟩ := exists_residueCoordinates P hp h
  have hpO : epsilonInteger P ^ 2 - ((P.N : 𝓞 K) + 2) * epsilonInteger P + 1 = 0 := by
    apply Subtype.ext
    exact P.epsilon_polynomial
  let f : 𝓞 K →+* ZMod p := (RingHom.fst (ZMod p) (ZMod p)).comp ρ
  let g : 𝓞 K →+* ZMod p := (RingHom.snd (ZMod p) (ZMod p)).comp ρ
  have hf : f (epsilonInteger P) ^ 2 - ((P.N : ZMod p) + 2) *
      f (epsilonInteger P) + 1 = 0 := by
    have he := congrArg f hpO
    rw [map_add, map_sub, map_pow, map_mul, map_add, map_natCast,
      map_ofNat, map_one, map_zero] at he
    exact he
  have hg : g (epsilonInteger P) ^ 2 - ((P.N : ZMod p) + 2) *
      g (epsilonInteger P) + 1 = 0 := by
    have he := congrArg g hpO
    rw [map_add, map_sub, map_pow, map_mul, map_add, map_natCast,
      map_ofNat, map_one, map_zero] at he
    exact he
  rcases quadratic_roots_eq_or_mul_eq_one (f (epsilonInteger P))
    (g (epsilonInteger P)) ((P.N : ZMod p) + 2) hf hg with hfg | hfg
  · refine ⟨?_, residueOrder_dvd_sub_one P hp h⟩
    rw [residueOrder_eq_coordinateOrder P r f hρ.2.1,
      residueOrder_eq_coordinateOrder P q g hρ.2.2, hfg]
  · exact residueOrder_common_of_coordinates P hp h ρ hρ hfg

theorem powerPeriod_oneMod_of_common (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (hc : residueOrder P r = residueOrder P q) :
    PeriodOneMod (PeriodPower.powPeriod P (residueOrder P r) (residueOrder_pos P r)) p := by
  have hr : epsilonInteger P ^ residueOrder P r - 1 ∈ r.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_pow, map_one]
    exact sub_eq_zero.mpr (pow_orderOf_eq_one _)
  have hq : epsilonInteger P ^ residueOrder P r - 1 ∈ q.asIdeal := by
    rw [hc]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_pow, map_one]
    exact sub_eq_zero.mpr (pow_orderOf_eq_one _)
  have hne : r.asIdeal ≠ q.asIdeal := by
    intro heq
    apply h.1
    exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective heq
  have hcop := Ideal.isCoprime_of_isMaximal hne
  change epsilonInteger (PeriodPower.powPeriod P (residueOrder P r)
    (residueOrder_pos P r)) - 1 ∈ Ideal.span {(p : 𝓞 K)}
  have heps : epsilonInteger (PeriodPower.powPeriod P (residueOrder P r)
      (residueOrder_pos P r)) = epsilonInteger P ^ residueOrder P r := by
    apply NumberField.RingOfIntegers.coe_injective
    rfl
  rw [heps, ← h.2, ← Ideal.inf_eq_mul_of_isCoprime hcop]
  exact ⟨hr, hq⟩

theorem powerPeriod_oneMod (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    PeriodOneMod (PeriodPower.powPeriod P (residueOrder P r) (residueOrder_pos P r)) p := by
  exact powerPeriod_oneMod_of_common P hp h (residueOrder_common P hp h).1

theorem ambientUnit_iterate_mk (P : PeriodData K) (I : StablePseudolattice P)
    (x : K) (n : ℕ) :
    (ambientUnit P I)^[n] (ambientMk I.val x) =
      ambientMk I.val (P.epsilon ^ n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change ambientMk I.val (P.epsilon * (P.epsilon ^ n * x)) = _
    congr 1
    ring

/-- Only elements of the multiplier order are used to act on I. -/
theorem epsilon_pow_sub_nat_preserves (P : PeriodData K)
    (I : StablePseudolattice P) (n a : ℕ) :
    ∀ z ∈ I.val, (P.epsilon ^ n - (a : K)) * z ∈ I.val := by
  intro z hz
  apply periodStable_order_smul P I _ _ ?_ hz
  exact (epsilonOrder P).sub_mem
    ((epsilonOrder P).pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) n)
    ((epsilonOrder P).natCast_mem a)

/-- On the colon line, epsilon acts by its residue coordinate. The integer representative is
legitimate because it is in the multiplier order. -/
theorem line_iterate_eq_nsmul (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (r : FinitePlace.Prime K)
    (f : 𝓞 K →+* ZMod p)
    (hf : ∀ a : 𝓞 K, f a = 0 ↔ a ∈ r.asIdeal)
    (y : primeLine P I r) (n : ℕ) :
    (ambientUnit P I)^[n] y.val =
      (f (epsilonInteger P) ^ n).val • y.val := by
  let a := (f (epsilonInteger P) ^ n).val
  have hzero : epsilonInteger P ^ n - (a : 𝓞 K) ∈ r.asIdeal := by
    apply (hf _).1
    rw [map_sub, map_pow, map_natCast]
    exact sub_eq_zero.mpr (ZMod.natCast_zmod_val _).symm
  obtain ⟨x, hx, hxy⟩ := AddSubgroup.mem_map.mp y.property
  have hmul : (P.epsilon ^ n - (a : K)) * x ∈ I.val := by
    apply (mem_inversePrimeCarrier P I r x).1 hx
      (epsilonInteger P ^ n - (a : 𝓞 K)) hzero
    intro z hz
    change (algebraMap (𝓞 K) K (epsilonInteger P ^ n - (a : 𝓞 K))) * z ∈ I.val
    rw [map_sub, map_pow, map_natCast]
    exact epsilon_pow_sub_nat_preserves P I n a z hz
  rw [← hxy, ambientUnit_iterate_mk, ← map_nsmul]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change P.epsilon ^ n * x - a • x ∈ I.val
  simpa only [nsmul_eq_mul, sub_mul] using hmul

theorem line_exact_period (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (y : primeLine P I r) (hy : y.val ≠ 0) (n : ℕ) :
    (ambientUnit P I)^[n] y.val = y.val ↔ residueOrder P r ∣ n := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ, hρ⟩ := exists_residueCoordinates P hp h
  let f := (RingHom.fst (ZMod p) (ZMod p)).comp ρ
  have hf : ∀ a : 𝓞 K, f a = 0 ↔ a ∈ r.asIdeal := hρ.2.1
  have hcard : Nat.card (primeLine P I r) = p := (primeLine_cards P I hp hm h).1
  have hord : addOrderOf y = p := by
    apply addOrderOf_eq_prime
    · apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
      rw [← hcard]
      exact addOrderOf_dvd_natCard y
    · intro hz
      exact hy (congrArg Subtype.val hz)
  have hordval : addOrderOf y.val = p := by
    exact (addOrderOf_injective (primeLine P I r).subtype Subtype.coe_injective y).trans hord
  rw [line_iterate_eq_nsmul P I r f hf y n,
    residueOrder_eq_coordinateOrder P r f hf, orderOf_dvd_iff_pow_eq_one]
  let a := (f (epsilonInteger P) ^ n).val
  change a • y.val = y.val ↔ f (epsilonInteger P) ^ n = 1
  have hsmul : a • y.val = y.val ↔ (a : ZMod p) = 1 := by
    rw [← sub_eq_zero, ← natCast_sub_one_zsmul,
      ← addOrderOf_dvd_iff_zsmul_eq_zero,
      hordval]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_one, sub_eq_zero]
  simpa only [a, ZMod.natCast_zmod_val] using hsmul

end SICLean.L5.SplitFrobeniusAux

namespace SICLean.L5.SplitFrobeniusAux

open L3 SplitPrimeValues DistributionOrbitGeometry PeriodPower DistributionGeneral

variable {K : Type} [Field K] [NumberField K]

theorem sf_equiv_zpow {A B : Type*} (e : A → B)
    (f : Equiv.Perm A) (g : Equiv.Perm B) (h : ∀ a, e (f a) = g (e a))
    (n : ℤ) (a : A) : e ((f ^ n) a) = (g ^ n) (e a) := by
  have hi (a : A) : e (f⁻¹ a) = g⁻¹ (e a) := by
    apply g.injective
    simpa using (h (f⁻¹ a)).symm
  induction n using Int.induction_on generalizing a with
  | zero => simp
  | succ n ih =>
    simp only [zpow_add_one, Equiv.Perm.mul_apply]
    rw [ih, h]
  | pred n ih =>
    simp only [zpow_sub_one, Equiv.Perm.mul_apply]
    rw [ih, hi]

theorem sf_sameCycle_period {A : Type*} [Finite A] (f : Equiv.Perm A)
    {a b : A} (h : f.SameCycle a b) :
    Function.minimalPeriod f a = Function.minimalPeriod f b := by
  let := Fintype.ofFinite A
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  exact (Function.minimalPeriod_apply_iterate (f.injective.mem_periodicPts a) n).symm

theorem sf_equiv_period {A B : Type*} (e : A ≃ B)
    (f : Equiv.Perm A) (g : Equiv.Perm B) (h : ∀ a, e (f a) = g (e a)) (a : A) :
    Function.minimalPeriod f a = Function.minimalPeriod g (e a) := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change (f^[n] a = a) ↔ (g^[n] (e a) = e a)
  have hc : e (f^[n] a) = g^[n] (e a) :=
    (show Function.Semiconj e f g from h).iterate_right n a
  constructor
  · intro hn
    exact hc.symm.trans (congrArg e hn)
  · intro hn
    exact e.injective (hc.trans hn)

theorem sf_project_ambient (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I) :
    ambientProject I.val J.val hIJ (toAmbient P I x) =
      toAmbient P J (periodProject P I J hIJ x) := by
  induction x using Quotient.inductionOn with
  | h z => rfl

def sf_fibreTranslate (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I) :
    Fibre P I J hIJ 0 ≃ Fibre P I J hIJ (periodProject P I J hIJ x) where
  toFun y := ⟨toAmbient P I x + y.val, by
    rw [map_add, sf_project_ambient, y.property, map_zero, add_zero]⟩
  invFun y := ⟨y.val - toAmbient P I x, by
    rw [map_sub, y.property, sf_project_ambient, sub_self, map_zero]⟩
  left_inv y := by apply Subtype.ext; exact add_sub_cancel_left _ _
  right_inv y := by apply Subtype.ext; exact add_sub_cancel _ _

theorem sf_fibreTranslate_comm (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I)
    (y : Fibre P I J hIJ 0) :
    sf_fibreTranslate P I J hIJ x (fibrePerm P I J hIJ 0 y) =
      fibrePerm P I J hIJ (periodProject P I J hIJ x)
        (sf_fibreTranslate P I J hIJ x y) := by
  apply Subtype.ext
  change toAmbient P I x + ambientUnit P I y.val =
    ambientUnit P I (toAmbient P I x + y.val)
  rw [map_add, (mem_range_toAmbient_iff P I _).mp ⟨x, rfl⟩]

theorem sf_fibreTranslate_rel (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I)
    (a b : Fibre P I J hIJ 0) :
    (orbitSetoid P I J hIJ 0).r a b ↔
      (orbitSetoid P I J hIJ (periodProject P I J hIJ x)).r
        (sf_fibreTranslate P I J hIJ x a) (sf_fibreTranslate P I J hIJ x b) := by
  let e := sf_fibreTranslate P I J hIJ x
  have hc := sf_equiv_zpow e (fibrePerm P I J hIJ 0)
    (fibrePerm P I J hIJ (periodProject P I J hIJ x))
    (sf_fibreTranslate_comm P I J hIJ x)
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (hc n a).symm.trans (congrArg e hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, e.injective ((hc n a).trans hn)⟩

def sf_orbitTranslate (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I) :
    Orbit P I J hIJ 0 ≃ Orbit P I J hIJ (periodProject P I J hIJ x) :=
  Quotient.congr (sf_fibreTranslate P I J hIJ x) (sf_fibreTranslate_rel P I J hIJ x)

theorem sf_orbitTranslate_sameCycle (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I)
    (o : Orbit P I J hIJ 0) :
    (fibrePerm P I J hIJ (periodProject P I J hIJ x)).SameCycle
      (sf_fibreTranslate P I J hIJ x (orbitRepresentative P I J hIJ 0 o))
      (orbitRepresentative P I J hIJ (periodProject P I J hIJ x)
        (sf_orbitTranslate P I J hIJ x o)) := by
  change (orbitSetoid P I J hIJ (periodProject P I J hIJ x)).r _ _
  apply Quotient.exact
  calc
    Quotient.mk _ (sf_fibreTranslate P I J hIJ x (orbitRepresentative P I J hIJ 0 o)) =
        sf_orbitTranslate P I J hIJ x o := by
      exact congrArg (sf_orbitTranslate P I J hIJ x) (Quotient.out_eq o)
    _ = _ := (Quotient.out_eq _).symm

theorem sf_orbitTranslate_length (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I)
    (o : Orbit P I J hIJ 0) :
    orbitLength P I J hIJ (periodProject P I J hIJ x)
      (sf_orbitTranslate P I J hIJ x o) = orbitLength P I J hIJ 0 o := by
  exact (sf_sameCycle_period _ (sf_orbitTranslate_sameCycle P I J hIJ x o)).symm.trans
    (sf_equiv_period (sf_fibreTranslate P I J hIJ x)
      (fibrePerm P I J hIJ 0) (fibrePerm P I J hIJ (periodProject P I J hIJ x))
      (sf_fibreTranslate_comm P I J hIJ x) (orbitRepresentative P I J hIJ 0 o)).symm


theorem sf_toAmbient_inclusion (P : PeriodData K) (I : StablePseudolattice P)
    (d : ℕ) (hd : 0 < d) (x : PseudolatticeGroup P I) :
    toAmbient (powPeriod P d hd) (powLattice P I d hd)
      (periodPowerInclusion P I d hd x) = toAmbient P I x := by
  induction x using Quotient.inductionOn with
  | h z => rfl

theorem sf_orbitTranslate_ambient (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I)
    (o : Orbit P I J hIJ 0) :
    ∃ a : ℤ, ((ambientUnit P I).toEquiv ^ a)
      (toAmbient P I x + (orbitRepresentative P I J hIJ 0 o).val) =
      (orbitRepresentative P I J hIJ (periodProject P I J hIJ x)
        (sf_orbitTranslate P I J hIJ x o)).val := by
  obtain ⟨a, ha⟩ := sf_orbitTranslate_sameCycle P I J hIJ x o
  refine ⟨a, ?_⟩
  have hc := sf_equiv_zpow
    (Subtype.val : Fibre P I J hIJ (periodProject P I J hIJ x) → AmbientGroup I.val)
    (fibrePerm P I J hIJ (periodProject P I J hIJ x)) (ambientUnit P I).toEquiv
    (fun _ => rfl) a
    (sf_fibreTranslate P I J hIJ x (orbitRepresentative P I J hIJ 0 o))
  exact hc.symm.trans (congrArg Subtype.val ha)

theorem sf_orbitValue_label (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (t : PseudolatticeGroup P J)
    (o : Orbit P I J hIJ t) (d : ℕ) (hd : 0 < d)
    (hlen : orbitLength P I J hIJ t o = d)
    (z : PseudolatticeGroup (powPeriod P d hd) (powLattice P I d hd))
    (ho : ∃ a : ℤ, ((ambientUnit P I).toEquiv ^ a)
      (toAmbient (powPeriod P d hd) (powLattice P I d hd) z) =
      (orbitRepresentative P I J hIJ t o).val) :
    orbitValue P I J hIJ t o = M72.value (powPeriod P d hd) (powLattice P I d hd) z := by
  subst d
  induction z using Quotient.inductionOn with
  | h z =>
    exact (orbitValue_representative P I J hIJ t o z.val z.property ho).symm

theorem sf_orbitTranslate_value (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I)
    (o : Orbit P I J hIJ 0) (d : ℕ) (hd : 0 < d)
    (hlen : orbitLength P I J hIJ 0 o = d)
    (z : PseudolatticeGroup (powPeriod P d hd) (powLattice P I d hd))
    (hz : toAmbient (powPeriod P d hd) (powLattice P I d hd) z =
      (orbitRepresentative P I J hIJ 0 o).val) :
    orbitValue P I J hIJ (periodProject P I J hIJ x) (sf_orbitTranslate P I J hIJ x o) =
      M72.value (powPeriod P d hd) (powLattice P I d hd)
        (periodPowerInclusion P I d hd x + z) := by
  refine sf_orbitValue_label P I J hIJ _ _ d hd
    ((sf_orbitTranslate_length P I J hIJ x o).trans hlen)
    (periodPowerInclusion P I d hd x + z) ?_
  rw [map_add, sf_toAmbient_inclusion, hz]
  exact sf_orbitTranslate_ambient P I J hIJ x o


theorem sf_orbitTranslate_zeroValue (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I)
    (o : Orbit P I J hIJ 0) (ho : (orbitRepresentative P I J hIJ 0 o).val = 0) :
    orbitValue P I J hIJ (periodProject P I J hIJ x)
      (sf_orbitTranslate P I J hIJ x o) = M72.value P I x := by
  calc
    _ = M72.value (powPeriod P 1 Nat.one_pos) (powLattice P I 1 Nat.one_pos)
        (periodPowerInclusion P I 1 Nat.one_pos x + 0) :=
      sf_orbitTranslate_value P I J hIJ x o 1 Nat.one_pos
        (zero_orbit_length P I J hIJ 0 o ho) 0 (by
          rw [map_zero]
          change (0 : AmbientGroup I.val) = _
          exact ho.symm)
    _ = M72.value P I x := by
      simpa only [add_zero, pow_one] using value_pow P I 1 Nat.one_pos x

theorem sf_zeroOrbit_unique (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (o z : Orbit P I J hIJ 0)
    (ho : (orbitRepresentative P I J hIJ 0 o).val = 0)
    (hz : (orbitRepresentative P I J hIJ 0 z).val = 0) : o = z := by
  have he : orbitRepresentative P I J hIJ 0 o = orbitRepresentative P I J hIJ 0 z :=
    Subtype.ext (ho.trans hz.symm)
  calc
    o = Quotient.mk _ (orbitRepresentative P I J hIJ 0 o) := (Quotient.out_eq o).symm
    _ = Quotient.mk _ (orbitRepresentative P I J hIJ 0 z) := congrArg (Quotient.mk _) he
    _ = z := Quotient.out_eq z

theorem sf_distribution_ratio (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (x : PseudolatticeGroup P I) :
    M72.value P J (periodProject P I J hIJ x) / M72.value P J 0 =
      ∏ o : Orbit P I J hIJ 0,
        orbitValue P I J hIJ (periodProject P I J hIJ x) (sf_orbitTranslate P I J hIJ x o) /
          orbitValue P I J hIJ 0 o := by
  calc
    _ = orbitProduct P I J hIJ (periodProject P I J hIJ x) / orbitProduct P I J hIJ 0 := by
      rw [← distribution_general P I J hIJ (periodProject P I J hIJ x),
        ← distribution_general P I J hIJ 0,
        mul_div_mul_left _ _ (distributionFactor_ne_zero P I J)]
    _ = _ := by
      rw [Finset.prod_div_distrib]
      unfold orbitProduct
      rw [(sf_orbitTranslate P I J hIJ x).prod_comp]


theorem sf_normalized_distribution_complex (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (d : ℕ) (hd : 0 < d)
    (hlength : ∀ o : {o : Orbit P I J hIJ 0 //
        (orbitRepresentative P I J hIJ 0 o).val ≠ 0}, orbitLength P I J hIJ 0 o.val = d)
    (shifts : {o : Orbit P I J hIJ 0 // (orbitRepresentative P I J hIJ 0 o).val ≠ 0} →
      PseudolatticeGroup (powPeriod P d hd) (powLattice P I d hd))
    (hshifts : ∀ o, toAmbient (powPeriod P d hd) (powLattice P I d hd) (shifts o) =
      (orbitRepresentative P I J hIJ 0 o.val).val)
    (x : PseudolatticeGroup P I) :
    M72.value P J (periodProject P I J hIJ x) / M72.value P J 0 =
      (M72.value P I x / M72.value P I 0) *
        ∏ o : {o : Orbit P I J hIJ 0 // (orbitRepresentative P I J hIJ 0 o).val ≠ 0},
          M72.value (powPeriod P d hd) (powLattice P I d hd)
              (periodPowerInclusion P I d hd x + shifts o) /
            M72.value (powPeriod P d hd) (powLattice P I d hd) (shifts o) := by
  obtain ⟨z, hz⟩ := (zero_orbit P I J hIJ 0).mpr rfl
  have hpred (o : Orbit P I J hIJ 0) :
      (orbitRepresentative P I J hIJ 0 o).val ≠ 0 ↔ o ≠ z := by
    constructor
    · intro ho he
      subst o
      exact ho hz
    · intro ho he
      exact ho (sf_zeroOrbit_unique P I J hIJ o z he hz)
  let e := Equiv.subtypeEquivRight hpred
  rw [sf_distribution_ratio, Fintype.prod_eq_mul_prod_subtype_ne _ z,
    sf_orbitTranslate_zeroValue P I J hIJ x z hz, orbitValue_zero P I J hIJ 0 z hz,
    ← M72.value_zero P I]
  congr 1
  calc
    _ = ∏ o : {o : Orbit P I J hIJ 0 // (orbitRepresentative P I J hIJ 0 o).val ≠ 0},
        orbitValue P I J hIJ (periodProject P I J hIJ x) (sf_orbitTranslate P I J hIJ x o.val) /
          orbitValue P I J hIJ 0 o.val := (e.prod_comp _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro o _
      rw [sf_orbitTranslate_value P I J hIJ x o.val d hd (hlength o) (shifts o) (hshifts o)]
      congr 1
      exact sf_orbitValue_label P I J hIJ 0 o.val d hd (hlength o) (shifts o)
        ⟨0, by
          change toAmbient (powPeriod P d hd) (powLattice P I d hd) (shifts o) = _
          exact hshifts o⟩

theorem normalized_orbit_distribution_aux (P : PeriodData K) (I J : StablePseudolattice P)
    (hIJ : I.val ≤ J.val) (d : ℕ) (hd : 0 < d)
    (hlength : ∀ o : {o : Orbit P I J hIJ 0 //
        (orbitRepresentative P I J hIJ 0 o).val ≠ 0}, orbitLength P I J hIJ 0 o.val = d)
    (shifts : {o : Orbit P I J hIJ 0 // (orbitRepresentative P I J hIJ 0 o).val ≠ 0} →
      PseudolatticeGroup (powPeriod P d hd) (powLattice P I d hd))
    (hshifts : ∀ o, toAmbient (powPeriod P d hd) (powLattice P I d hd) (shifts o) =
      (orbitRepresentative P I J hIJ 0 o.val).val)
    (x : PseudolatticeGroup P I) :
    normalizedLift P J (periodProject P I J hIJ x) = normalizedLift P I x *
      ∏ o : {o : Orbit P I J hIJ 0 // (orbitRepresentative P I J hIJ 0 o).val ≠ 0},
        valueLift (powPeriod P d hd) (powLattice P I d hd)
            (periodPowerInclusion P I d hd x + shifts o) /
          valueLift (powPeriod P d hd) (powLattice P I d hd) (shifts o) := by
  have hE (Q : PeriodData K) (L : StablePseudolattice Q) (z : PseudolatticeGroup Q L) :
      Galois.embed.toRingHom (valueLift Q L z) = M72.value Q L z :=
    embed_valueLift Q L z
  apply Galois.embed.injective
  simp only [normalizedLift, map_div₀, map_mul, map_prod, hE]
  exact sf_normalized_distribution_complex P I J hIJ d hd hlength shifts hshifts x

end SICLean.L5.SplitFrobeniusAux
