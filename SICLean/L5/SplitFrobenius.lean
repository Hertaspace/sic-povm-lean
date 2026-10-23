import SICLean.L5.SplitPrimeValues
import SICLean.L5.SplitFrobeniusAux
import SICLean.L5.OddPrimeUnits

set_option autoImplicit false

/-!
# [RW-rec, Thm. 8] with a single direction for the entire value family

[RW-rec, pp. 12--13] is the orbit argument. The distribution input is
[RW-rec, Prop. 3(i), Appendix A, p. 4, pp. 19--20], already `distribution_general`.
Related statements are [RW26, (4), p. 3], [RW26, footnote 2], [RW26, Prop. 8, p. 14],
and [RW26, (37), p. 20]. Theorem 8 in this file is [RW-rec, Thm. 8, pp. 12--13].
[RW26, Thm. 8, p. 22] is the algebraicity statement. All maps below preserve the literal
K-representative. Original-period labels
are included into the higher period by `periodPowerInclusion`. The fibre need not lie in
the original period group. Even a nonzero label that becomes zero in the overlattice
remains in every assertion.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace SICLean.L5.SplitFrobenius

open L3 SplitPrimeLattice SplitPrimeValues DistributionOrbitGeometry LocalFourierSetup

variable {K : Type} [Field K] [NumberField K]

/-- Order of the actual residue of epsilon; no choice of generator of F_p^×. -/
def residueOrder (P : PeriodData K) (r : FinitePlace.Prime K) : ℕ :=
  orderOf (Ideal.Quotient.mk r.asIdeal (epsilonInteger P))

/-- The already defined identity-on-representatives period projection. -/
def projectInverse (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) :
    PseudolatticeGroup P I →+ PseudolatticeGroup P (inversePrimeLattice P I r) :=
  periodProject P I (inversePrimeLattice P I r) (le_inversePrime P I r)

/-- Nonzero epsilon orbits of J/I, defined inside the existing zero fibre. -/
abbrev NonzeroOrbit (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) :=
  {o : Orbit P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0 //
    (orbitRepresentative P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0 o).val ≠ 0}

/-- [RW-rec]: epsilon is a residue unit, so its order is positive. The case d=1 is included. -/
theorem residueOrder_pos (P : PeriodData K) (r : FinitePlace.Prime K) :
    0 < residueOrder P r := by
  exact SplitFrobeniusAux.residueOrder_pos P r

/-- [RW-rec]: inverse residues have the same order dividing p-1. -/
theorem residueOrder_common (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    residueOrder P r = residueOrder P q ∧ residueOrder P r ∣ p - 1 := by
  exact SplitFrobeniusAux.residueOrder_common P hp h

/-- [RW-rec]: the higher period is 1 mod pO_K, so Theorem 7 applies. -/
theorem powerPeriod_oneMod (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    PeriodOneMod (PeriodPower.powPeriod P (residueOrder P r) (residueOrder_pos P r)) p := by
  exact SplitFrobeniusAux.powerPeriod_oneMod P hp h

/-- [RW-rec]: every nonzero point on either selected kernel line has exact return time d. This is an
orbit assertion in K/I, not in G_(I,epsilon). -/
theorem line_exact_period (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (y : primeLine P I r) (hy : y.val ≠ 0) (n : ℕ) :
    (ambientUnit P I)^[n] y.val = y.val ↔ residueOrder P r ∣ n := by
  exact SplitFrobeniusAux.line_exact_period P I hp hm h y hy n

/-- [RW-rec]: exactly one zero orbit is removed from the orbit product. -/
theorem unique_zero_orbit (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) :
    ∃! o : Orbit P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0,
      (orbitRepresentative P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0 o).val = 0 := by
  obtain ⟨o, ho⟩ := (zero_orbit P I (inversePrimeLattice P I r)
    (le_inversePrime P I r) 0).mpr rfl
  refine ⟨o, ho, ?_⟩
  intro o' ho'
  have he : orbitRepresentative P I (inversePrimeLattice P I r)
      (le_inversePrime P I r) 0 o' =
      orbitRepresentative P I (inversePrimeLattice P I r)
        (le_inversePrime P I r) 0 o := Subtype.ext (ho'.trans ho.symm)
  exact (Quotient.out_eq o').symm.trans
    ((congrArg (Quotient.mk _) he).trans (Quotient.out_eq o))

/-- [RW-rec]: every remaining orbit has length d, including when d=1. -/
theorem nonzero_orbit_length (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (o : NonzeroOrbit P I r) :
    orbitLength P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0 o.val =
      residueOrder P r := by
  let J := inversePrimeLattice P I r
  let hIJ := le_inversePrime P I r
  let y := orbitRepresentative P I J hIJ 0 o.val
  have hy : y.val ∈ primeLine P I r := by
    let z : K := Quotient.out y.val
    have hz : ambientMk I.val z = y.val := Quotient.out_eq y.val
    have hzJ : z ∈ J.val := by
      have hyJ := y.property
      rw [← hz] at hyJ
      change (QuotientAddGroup.mk z : AmbientGroup J.val) = toAmbient P J 0 at hyJ
      exact (QuotientAddGroup.eq_zero_iff z).mp (by simpa only [map_zero] using hyJ)
    exact AddSubgroup.mem_map.mpr ⟨z, hzJ, hz⟩
  have hsemi : Function.Semiconj (Subtype.val : Fibre P I J hIJ 0 → AmbientGroup I.val)
      (fibrePerm P I J hIJ 0) (ambientUnit P I) := fun _ => rfl
  have hreturn (n : ℕ) : orbitLength P I J hIJ 0 o.val ∣ n ↔ residueOrder P r ∣ n := by
    rw [orbitLength_dvd_iff]
    change (fibrePerm P I J hIJ 0 ^ n) y = y ↔ _
    rw [← Subtype.val_injective.eq_iff]
    change ((fibrePerm P I J hIJ 0)^[n] y).val = y.val ↔ _
    rw [hsemi.iterate_right n y]
    exact line_exact_period P I hp hm h ⟨y.val, hy⟩ o.property n
  exact Nat.dvd_antisymm ((hreturn _).mpr (dvd_refl _))
    ((hreturn _).mp (dvd_refl _))

/-- [RW-rec]: integer orbit counting, without a possibly truncated division. -/
theorem nonzero_orbit_count (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    residueOrder P r * Nat.card (NonzeroOrbit P I r) = p - 1 := by
  let J := inversePrimeLattice P I r
  let hIJ := le_inversePrime P I r
  obtain ⟨o₀, ho₀, hu₀⟩ := unique_zero_orbit P I r
  have heq (o : Orbit P I J hIJ 0) :
      (orbitRepresentative P I J hIJ 0 o).val ≠ 0 ↔ o ≠ o₀ := by
    constructor
    · intro hn he
      exact hn (he ▸ ho₀)
    · intro hn hz
      exact hn (hu₀ o hz)
  have he : NonzeroOrbit P I r ≃ {o : Orbit P I J hIJ 0 // o ≠ o₀} :=
    { toFun := fun o => ⟨o.val, (heq o.val).mp o.property⟩
      invFun := fun o => ⟨o.val, (heq o.val).mpr o.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsum := sum_orbitLength P I J hIJ 0
  rw [Fintype.sum_eq_add_sum_subtype_ne _ o₀,
    zero_orbit_length P I J hIJ 0 o₀ ho₀] at hsum
  have hc : (∑ o : {o : Orbit P I J hIJ 0 // o ≠ o₀},
      orbitLength P I J hIJ 0 o.val) =
      Nat.card (NonzeroOrbit P I r) * residueOrder P r := by
    calc
      _ = ∑ _o : {o : Orbit P I J hIJ 0 // o ≠ o₀}, residueOrder P r := by
        apply Finset.sum_congr rfl
        intro o _
        exact nonzero_orbit_length P I hp hm h ⟨o.val, (heq o.val).mpr o.property⟩
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          ← Fintype.card_congr he, ← Nat.card_eq_fintype_card]
  rw [hc, (inversePrime_index P I hp hm h).1] at hsum
  rw [Nat.mul_comm] at hsum
  omega

/-- [RW-rec]: representatives of the kernel orbits lift to the higher period group. Their ambient
classes are the original zero-fibre representatives. -/
theorem exists_orbit_shifts (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    let d := residueOrder P r
    let hd := residueOrder_pos P r
    ∃ shifts : NonzeroOrbit P I r →
      PseudolatticeGroup (PeriodPower.powPeriod P d hd) (PeriodPower.powLattice P I d hd),
      ∀ o, toAmbient (PeriodPower.powPeriod P d hd) (PeriodPower.powLattice P I d hd) (shifts o) =
        (orbitRepresentative P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0 o.val).val := by
  dsimp only
  let d := residueOrder P r
  let hd := residueOrder_pos P r
  let Q := PeriodPower.powPeriod P d hd
  let L := PeriodPower.powLattice P I d hd
  have hex (o : NonzeroOrbit P I r) : ∃ a : PseudolatticeGroup Q L,
      toAmbient Q L a =
        (orbitRepresentative P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0 o.val).val := by
    let z := orbitLift P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0 o.val
    have hz : z ∈ pseudolatticePeriodPoints Q L := by
      have hz := orbitLift_mem P I (inversePrimeLattice P I r)
        (le_inversePrime P I r) 0 o.val
      have hlen : orbitLength P I (inversePrimeLattice P I r)
          (le_inversePrime P I r) 0 o.val = d := nonzero_orbit_length P I hp hm h o
      change ((P.epsilon ^ d)⁻¹ - 1) * z ∈ I.val
      change ((P.epsilon ^ orbitLength P I (inversePrimeLattice P I r)
        (le_inversePrime P I r) 0 o.val)⁻¹ - 1) * z ∈ I.val at hz
      simpa only [hlen] using hz
    exact ⟨pseudolatticeMk Q L z hz, Quotient.out_eq _⟩
  exact ⟨fun o => Classical.choose (hex o), fun o => Classical.choose_spec (hex o)⟩

/-- [RW-rec]: divide the two existing general orbit-distribution formulas. Actual eta multipliers
cancel only in this ratio. This is an equality in Qbar before any reduction, for all original
labels. -/
theorem normalized_orbit_distribution (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (shifts : NonzeroOrbit P I r → PseudolatticeGroup
      (PeriodPower.powPeriod P (residueOrder P r) (residueOrder_pos P r))
      (PeriodPower.powLattice P I (residueOrder P r) (residueOrder_pos P r)))
    (hshifts : ∀ o, toAmbient _ _ (shifts o) =
      (orbitRepresentative P I (inversePrimeLattice P I r) (le_inversePrime P I r) 0 o.val).val)
    (x : PseudolatticeGroup P I) :
    normalizedLift P (inversePrimeLattice P I r) (projectInverse P I r x) =
      normalizedLift P I x * ∏ o : NonzeroOrbit P I r,
        valueLift _ _ (PeriodPower.periodPowerInclusion P I (residueOrder P r)
          (residueOrder_pos P r) x + shifts o) / valueLift _ _ (shifts o) := by
  exact SplitFrobeniusAux.normalized_orbit_distribution_aux P I
    (inversePrimeLattice P I r) (le_inversePrime P I r)
    (residueOrder P r) (residueOrder_pos P r)
    (nonzero_orbit_length P I hp hm h) shifts hshifts x

/-- [RW-rec]: uniform invariance at eta turns each nonzero-orbit quotient into U_I(x)^d. The same
selected prime r is retained throughout. -/
theorem orbit_quotient_congruence (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hdir : ∀ (z : PseudolatticeGroup
        (PeriodPower.powPeriod P (residueOrder P r) (residueOrder_pos P r))
        (PeriodPower.powLattice P I (residueOrder P r) (residueOrder_pos P r)))
      (a : periodLine _ _ r),
      reduce v (valueLift _ _ (z + a.val)) = reduce v (valueLift _ _ z))
    (x : PseudolatticeGroup P I)
    (a : periodLine (PeriodPower.powPeriod P (residueOrder P r) (residueOrder_pos P r))
      (PeriodPower.powLattice P I (residueOrder P r) (residueOrder_pos P r)) r) :
    reduce v (valueLift _ _ (PeriodPower.periodPowerInclusion P I (residueOrder P r)
      (residueOrder_pos P r) x + a.val) / valueLift _ _ a.val) =
        reduce v (normalizedLift P I x) ^ residueOrder P r := by
  let d := residueOrder P r
  let hd := residueOrder_pos P r
  let Q := PeriodPower.powPeriod P d hd
  let L := PeriodPower.powLattice P I d hd
  let ix := PeriodPower.periodPowerInclusion P I d hd x
  have hv (R : PeriodData K) (J : StablePseudolattice R) (z : PseudolatticeGroup R J) :
      v (valueLift R J z) = 0 := by
    rw [OddPrimeValues.lift_of_embed R J z _ (embed_valueLift R J z)]
    exact OddPrimeUnits.odd_prime_valuation_zero R J p hodd v hp z
  have hdiv (a b : Galois.Qbar) (ha : v a = 0) (hb : v b = 0) :
      reduce v (a / b) = reduce v a / reduce v b := by
    rw [div_eq_mul_inv, reduce_mul v a b⁻¹ (by rw [ha])
      (by simp only [v.map_inv, hb, neg_zero, le_refl]), reduce_inv v b hb,
      div_eq_mul_inv]
  have hpow (a : Galois.Qbar) (ha : v a = 0) (n : ℕ) :
      reduce v (a ^ n) = reduce v a ^ n := by
    induction n with
    | zero =>
      simp only [pow_zero]
      rw [reduce_eq_residue v 1 (by simp)]
      change (IsLocalRing.residue (integers v)) 1 = 1
      exact map_one _
    | succ n ih =>
      rw [pow_succ, reduce_mul v (a ^ n) a (by simp [ha]) (by rw [ha]), ih,
        pow_succ]
  have ha : reduce v (valueLift Q L a.val) = reduce v (valueLift Q L 0) := by
    simpa only [zero_add] using hdir 0 a
  calc
    _ = reduce v (valueLift Q L (ix + a.val)) / reduce v (valueLift Q L a.val) :=
      hdiv _ _ (hv Q L _) (hv Q L _)
    _ = reduce v (valueLift Q L ix) / reduce v (valueLift Q L 0) := by
      rw [hdir ix a, ha]
    _ = reduce v (normalizedLift Q L ix) := (hdiv _ _ (hv Q L _) (hv Q L _)).symm
    _ = reduce v (normalizedLift P I x ^ d) :=
      congrArg (reduce v) (normalizedLift_power P I d hd x)
    _ = _ := hpow _ (by simp [normalizedLift, hv]) d

/-- [RW-rec]: the final exponent is exactly p. -/
theorem frobenius_exponent (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    1 + residueOrder P r * Nat.card (NonzeroOrbit P I r) = p := by
  rw [nonzero_orbit_count P I hp hm h]
  exact Nat.add_sub_of_le hp.one_le

/-- [RW-rec]: conditional assembly preserving the direction supplied by Theorem 7 at eta. No
direction is reselected for any label. -/
theorem theorem8_same_direction (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1)
    (hdir : ∀ (z : PseudolatticeGroup
        (PeriodPower.powPeriod P (residueOrder P r) (residueOrder_pos P r))
        (PeriodPower.powLattice P I (residueOrder P r) (residueOrder_pos P r)))
      (a : periodLine _ _ r),
      reduce v (valueLift _ _ (z + a.val)) = reduce v (valueLift _ _ z)) :
    ∀ x : PseudolatticeGroup P I,
      reduce v (normalizedLift P (inversePrimeLattice P I r) (projectInverse P I r x)) =
        reduce v (normalizedLift P I x) ^ p := by
  intro x
  let d := residueOrder P r
  let hd := residueOrder_pos P r
  let Q := PeriodPower.powPeriod P d hd
  let L := PeriodPower.powLattice P I d hd
  obtain ⟨shifts, hshifts⟩ := exists_orbit_shifts P I (Fact.out : p.Prime) hm h
  let f : NonzeroOrbit P I r → Galois.Qbar := fun o =>
    valueLift Q L (PeriodPower.periodPowerInclusion P I d hd x + shifts o) /
      valueLift Q L (shifts o)
  have hv (R : PeriodData K) (J : StablePseudolattice R) (z : PseudolatticeGroup R J) :
      v (valueLift R J z) = 0 := by
    rw [OddPrimeValues.lift_of_embed R J z _ (embed_valueLift R J z)]
    exact OddPrimeUnits.odd_prime_valuation_zero R J p hodd v hp z
  have hf (o : NonzeroOrbit P I r) : v (f o) = 0 := by
    simp [f, hv]
  have hprod (s : Finset (NonzeroOrbit P I r)) :
      v (∏ o ∈ s, f o) = 0 ∧
      reduce v (∏ o ∈ s, f o) = ∏ o ∈ s, reduce v (f o) := by
    induction s using Finset.induction_on with
    | empty =>
      constructor
      · simp
      · simp only [Finset.prod_empty]
        rw [reduce_eq_residue v 1 (by simp)]
        change (IsLocalRing.residue (integers v)) 1 = 1
        exact map_one _
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      constructor
      · rw [v.map_mul, hf, ih.1, zero_add]
      · rw [reduce_mul v _ _ (by rw [hf]) (by rw [ih.1]), ih.2]
  have hcong (o : NonzeroOrbit P I r) :
      reduce v (f o) = reduce v (normalizedLift P I x) ^ d := by
    have ha : shifts o ∈ periodLine Q L r := by
      change toAmbient Q L (shifts o) ∈ primeLine Q L r
      rw [hshifts o]
      let J := inversePrimeLattice P I r
      let hIJ := le_inversePrime P I r
      let y := orbitRepresentative P I J hIJ 0 o.val
      let z : K := Quotient.out y.val
      have hz : ambientMk I.val z = y.val := Quotient.out_eq y.val
      have hzJ : z ∈ J.val := by
        have hyJ := y.property
        rw [← hz] at hyJ
        change (QuotientAddGroup.mk z : AmbientGroup J.val) = toAmbient P J 0 at hyJ
        exact (QuotientAddGroup.eq_zero_iff z).mp (by simpa only [map_zero] using hyJ)
      exact AddSubgroup.mem_map.mpr ⟨z, hzJ, hz⟩
    exact orbit_quotient_congruence P I hodd hm h v hp hdir x ⟨shifts o, ha⟩
  calc
    _ = reduce v (normalizedLift P I x * ∏ o : NonzeroOrbit P I r, f o) :=
      congrArg (reduce v) (normalized_orbit_distribution P I (Fact.out : p.Prime) hm h
        shifts hshifts x)
    _ = reduce v (normalizedLift P I x) * ∏ o : NonzeroOrbit P I r, reduce v (f o) := by
      rw [reduce_mul v _ _ (by simp [normalizedLift, hv]) (by rw [(hprod _).1]),
        (hprod _).2]
    _ = reduce v (normalizedLift P I x) *
        ∏ _o : NonzeroOrbit P I r, reduce v (normalizedLift P I x) ^ d := by
      congr 1
      exact Finset.prod_congr rfl (fun o _ => hcong o)
    _ = reduce v (normalizedLift P I x) ^
        (1 + d * Nat.card (NonzeroOrbit P I r)) := by
      simp only [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card,
        pow_add, pow_one, pow_mul]
    _ = _ := by rw [frobenius_exponent P I (Fact.out : p.Prime) hm h]

/-- [RW-rec, Thm. 8]. Public Qbar statement: one prime for all labels, including zero and labels
that become zero. There is no p∤N input. -/
theorem theorem8 (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (v : AddValuation Galois.Qbar (WithTop ℝ)) (hp : v (p : Galois.Qbar) = 1) :
    ∃ t : FinitePlace.Prime K, (t = r ∨ t = q) ∧
      ∀ x : PseudolatticeGroup P I,
        reduce v (normalizedLift P (inversePrimeLattice P I t) (projectInverse P I t x)) =
          reduce v (normalizedLift P I x) ^ p := by
  let d := residueOrder P r
  let hd := residueOrder_pos P r
  let Q := PeriodPower.powPeriod P d hd
  let L := PeriodPower.powLattice P I d hd
  have hm' : LocallyMaximal Q L p := hm
  obtain ⟨t, ht, hdir⟩ := theorem7 Q L hodd hm' h
    (powerPeriod_oneMod P (Fact.out : p.Prime) h) v hp
  refine ⟨t, ht, ?_⟩
  rcases ht with ht | ht
  · subst t
    exact theorem8_same_direction P I hodd hm h v hp hdir
  · subst t
    have horder : residueOrder P r = residueOrder P q :=
      (residueOrder_common P (Fact.out : p.Prime) h).1
    let direction : {n : ℕ // 0 < n} → Prop := fun n =>
      ∀ (z : PseudolatticeGroup (PeriodPower.powPeriod P n.val n.property)
          (PeriodPower.powLattice P I n.val n.property))
        (a : periodLine _ _ q),
        reduce v (valueLift _ _ (z + a.val)) = reduce v (valueLift _ _ z)
    have hrdir : direction ⟨d, hd⟩ := hdir
    have hsame : (⟨d, hd⟩ : {n : ℕ // 0 < n}) =
        ⟨residueOrder P q, residueOrder_pos P q⟩ := Subtype.ext horder
    have hdir' : direction ⟨residueOrder P q, residueOrder_pos P q⟩ :=
      Eq.mp (congrArg direction hsame) hrdir
    exact theorem8_same_direction P I hodd hm (SplitPrimeGeometry.splitPair_symm h)
      v hp hdir'


end SICLean.L5.SplitFrobenius
