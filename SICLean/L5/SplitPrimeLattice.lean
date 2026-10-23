import SICLean.L3.PseudolatticeIdeal
import SICLean.L5.DistributionNormalized
import SICLean.L5.PrimeSpecialization
import SICLean.L5.LocalFourierSetup
import SICLean.L5.SplitPrimeLatticeAux

set_option autoImplicit false

/-!
# The actual split-prime overlattices

[RW-rec, §7, p. 11] with the local-maximality dictionary on p. 9. [RW26, Lemma 2, p. 12,
p. 20, (37)]. The local statements follow [RW-rec]. The inverse carrier is the colon by
the contraction of a maximal-order prime to the multiplier order of I. It does not
replace I by O_K I. Local maximality is the explicit prime-to-p saturation-index
condition. No cardinality, direct-sum property, or E-congruence is a part of the
definition.
-/

noncomputable section
open scoped NumberField

namespace SICLean.L5.SplitPrimeLattice

open L3 DistributionOrbitGeometry

variable {K : Type} [Field K] [NumberField K]

/-- [RW-rec]: p does not divide [O_K I:I]. -/
def LocallyMaximal (P : PeriodData K) (I : StablePseudolattice P) (p : ℕ) : Prop :=
  Nat.Coprime p (inclusionIndex I.val
    (fractionalIdealCarrier (pseudolatticeSaturation P I)))

/-- [RW-rec]: two distinct maximal-order primes factor the rational prime. The corresponding order
primes are their contractions, not these ideals. -/
def IsSplitPair (p : ℕ) (r q : FinitePlace.Prime K) : Prop :=
  r ≠ q ∧ r.asIdeal * q.asIdeal = Ideal.span {(p : 𝓞 K)}

/-- Literal colon `(r_K ∩ (I:I))⁻¹ I`. The indexing condition is just membership in the contracted
ideal, expressed without a second order definition. -/
def inversePrimeCarrier (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) : Submodule ℤ K :=
  ⨅ a : {a : 𝓞 K // a ∈ r.asIdeal ∧ ∀ y ∈ I.val, (a : K) * y ∈ I.val},
    I.val.comap (LinearMap.mulLeft ℤ (a.val : K))

/-- `r⁻¹ I/I` inside the existing ambient K/I. -/
def primeLine (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) : AddSubgroup (AmbientGroup I.val) :=
  (inversePrimeCarrier P I r).toAddSubgroup.map (ambientMk I.val)

/-- The same subgroup restricted to the existing period group. It has order p only when the period
fixes the whole line. -/
def periodLine (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) : AddSubgroup (PseudolatticeGroup P I) :=
  (primeLine P I r).comap (toAmbient P I)

/-- [RW-rec]: the integral period itself is 1 modulo the rational prime. -/
def PeriodOneMod (P : PeriodData K) (p : ℕ) : Prop :=
  epsilonInteger P - 1 ∈ Ideal.span {(p : 𝓞 K)}

/-- [RW-rec]; only for K and I. -/
theorem split_residue_characteristics (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    FinitePlace.residueChar r = p ∧ FinitePlace.residueChar q = p := by
  have hmem : ∀ s : FinitePlace.Prime K, (p : 𝓞 K) ∈ s.asIdeal →
      FinitePlace.residueChar s = p := by
    intro s hs
    apply CharP.ringChar_of_prime_eq_zero hp
    change (p : 𝓞 K ⧸ s.asIdeal) = 0
    rw [← map_natCast (Ideal.Quotient.mk s.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hs
  have hpq : (p : 𝓞 K) ∈ r.asIdeal * q.asIdeal := by
    rw [h.2]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact ⟨hmem r (Ideal.mul_le_left hpq), hmem q (Ideal.mul_le_right hpq)⟩

/-- [RW-rec]: these two residue fields are prime fields. -/
theorem split_residue_cards (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    Nat.card (FinitePlace.Residue r) = p ∧ Nat.card (FinitePlace.Residue q) = p := by
  have hchars := split_residue_characteristics P hp h
  have hnorm : Nat.card (FinitePlace.Residue r) *
      Nat.card (FinitePlace.Residue q) = p ^ 2 := by
    change Ideal.absNorm r.asIdeal * Ideal.absNorm q.asIdeal = p ^ 2
    rw [← map_mul Ideal.absNorm, h.2, Ideal.absNorm_span_natCast,
      NumberField.RingOfIntegers.rank, P.finrank_eq_two]
  rw [FinitePlace.residue_card r, FinitePlace.residue_card q,
    hchars.1, hchars.2, ← pow_add] at hnorm
  have hdeg : FinitePlace.absoluteResidueDegree r +
      FinitePlace.absoluteResidueDegree q = 2 :=
    Nat.pow_right_injective hp.one_lt hnorm
  have hrdeg := FinitePlace.absoluteResidueDegree_pos r
  have hqdeg := FinitePlace.absoluteResidueDegree_pos q
  have hr : FinitePlace.absoluteResidueDegree r = 1 := by omega
  have hq : FinitePlace.absoluteResidueDegree q = 1 := by omega
  rw [FinitePlace.residue_card r, FinitePlace.residue_card q,
    hr, hq, pow_one, pow_one, hchars.1, hchars.2]
  exact ⟨rfl, rfl⟩

/-- The index used in LocallyMaximal is an actual positive finite index. -/
theorem saturation_index_pos (P : PeriodData K) (I : StablePseudolattice P) :
    0 < inclusionIndex I.val (fractionalIdealCarrier (pseudolatticeSaturation P I)) := by
  exact DistributionOrbitGeometryAux.lattice_relIndex_pos I.val
    (fractionalIdealCarrier (pseudolatticeSaturation P I)) I.property.1
    (fractionalIdealCarrier_isLattice _ (pseudolatticeSaturation_ne_zero P I))
    (pseudolatticeSaturation_contains P I)

/-- A nonoptimal conductor bound suffices; it is not defined as the true conductor. -/
theorem locallyMaximal_of_bound (P : PeriodData K) (I : StablePseudolattice P)
    {p C : ℕ} (hp : p.Prime) (hC : 0 < C) (hpc : ¬ p ∣ C)
    (hbound : pseudolatticeScale (C : K)
      (fractionalIdealCarrier (pseudolatticeSaturation P I)) ≤ I.val) :
    LocallyMaximal P I p := by
  exact SplitPrimeLatticeAux.coprime_relIndex_of_scale_le I.val _ I.property.1
    (fractionalIdealCarrier_isLattice _ (pseudolatticeSaturation_ne_zero P I))
    (pseudolatticeSaturation_contains P I) hp hpc hbound

/-- [RW-rec] with the existing uniform conductor sandwich; no equality with the true conductor is
asserted. -/
theorem locallyMaximal_of_uniform_conductor (P : PeriodData K)
    (I : StablePseudolattice P) {p : ℕ} (hp : p.Prime)
    (hc : ¬ p ∣ pseudolatticeConductor P) : LocallyMaximal P I p := by
  exact locallyMaximal_of_bound P I hp (pseudolatticeConductor_pos P) hc
    (pseudolatticeSaturation_conductor_le P I)

/-- [RW-rec]: the explicit colon membership rule. -/
theorem mem_inversePrimeCarrier (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) (x : K) :
    x ∈ inversePrimeCarrier P I r ↔
      ∀ a : 𝓞 K, a ∈ r.asIdeal →
        (∀ y ∈ I.val, (a : K) * y ∈ I.val) → (a : K) * x ∈ I.val := by
  simp only [inversePrimeCarrier, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mulLeft_apply]
  exact ⟨fun h a ha hI => h ⟨a, ha, hI⟩, fun h a => h a.val a.property.1 a.property.2⟩

/-- [RW-rec]; a nonzero rational integer in r bounds the colon. -/
theorem inversePrime_isLattice (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) : Submodule.IsLattice ℚ (inversePrimeCarrier P I r) := by
  let n := FinitePlace.residueChar r
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (FinitePlace.residueChar_prime r).ne_zero
  have hnr : (n : 𝓞 K) ∈ r.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (n : FinitePlace.Residue r) = 0
    exact CharP.cast_eq_zero (FinitePlace.Residue r) n
  have hlow : I.val ≤ inversePrimeCarrier P I r := by
    intro x hx
    exact (mem_inversePrimeCarrier P I r x).mpr (fun _ _ ha => ha x hx)
  have hup : inversePrimeCarrier P I r ≤ pseudolatticeScale (n : K)⁻¹ I.val := by
    intro x hx
    have hxI := (mem_inversePrimeCarrier P I r x).mp hx (n : 𝓞 K) hnr (by
      intro y hy
      simpa using I.val.smul_mem (n : ℤ) hy)
    exact (pseudolatticeScale_mem_iff _ _ _).mpr
      ⟨(n : K) * x, hxI, by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]⟩
  constructor
  · exact ((pseudolatticeScale_isLattice I.val I.property.1 _ (inv_ne_zero hn)).fg).of_le hup
  · apply top_unique
    rw [← I.property.1.span_eq_top]
    exact Submodule.span_mono hlow

/-- [RW-rec]; epsilon and epsilon inverse preserve the colon. -/
theorem inversePrime_periodStable (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) : PeriodStable P (inversePrimeCarrier P I r) := by
  have hmul (x : K) (hx : x ∈ inversePrimeCarrier P I r) :
      P.epsilon * x ∈ inversePrimeCarrier P I r := by
    rw [mem_inversePrimeCarrier] at hx ⊢
    intro a ha hI
    rw [mul_left_comm]
    exact (DistributionOrbitGeometryAux.epsilon_mul_mem_iff P I _).mpr (hx a ha hI)
  have hinv (x : K) (hx : x ∈ inversePrimeCarrier P I r) :
      P.epsilon⁻¹ * x ∈ inversePrimeCarrier P I r := by
    rw [mem_inversePrimeCarrier] at hx ⊢
    intro a ha hI
    apply (DistributionOrbitGeometryAux.epsilon_mul_mem_iff P I _).mp
    rw [mul_left_comm P.epsilon (a : K), mul_inv_cancel_left₀ P.epsilon_ne_zero]
    exact hx a ha hI
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
    exact hmul y hy
  · intro x hx
    exact (pseudolatticeScale_mem_iff _ _ _).mpr
      ⟨P.epsilon⁻¹ * x, hinv x hx, by
        rw [← mul_assoc, mul_inv_cancel₀ P.epsilon_ne_zero, one_mul]⟩

/-- Same actual carrier and period, packaged using the preceding obligations. -/
def inversePrimeLattice (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) : StablePseudolattice P :=
  ⟨inversePrimeCarrier P I r, inversePrime_isLattice P I r,
    inversePrime_periodStable P I r⟩

/-- This containment holds even before local maximality. -/
theorem le_inversePrime (P : PeriodData K) (I : StablePseudolattice P)
    (r : FinitePlace.Prime K) : I.val ≤ (inversePrimeLattice P I r).val := by
  intro x hx
  exact (mem_inversePrimeCarrier P I r x).mpr (fun _ _ ha => ha x hx)

/-- [RW-rec]: p belongs to the contracted order prime, giving the other half of I ≤ r⁻¹I ≤ p⁻¹I
without a global O_K-action on I. -/
theorem inversePrime_le_pDivision (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (r : FinitePlace.Prime K)
    (hr : FinitePlace.residueChar r = p) :
    inversePrimeCarrier P I r ≤ pseudolatticeScale (p : K)⁻¹ I.val := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpr : (p : 𝓞 K) ∈ r.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (p : FinitePlace.Residue r) = 0
    rw [← hr]
    exact CharP.cast_eq_zero (FinitePlace.Residue r) (FinitePlace.residueChar r)
  intro x hx
  have hxI := (mem_inversePrimeCarrier P I r x).mp hx (p : 𝓞 K) hpr (by
    intro y hy
    simpa using I.val.smul_mem (p : ℤ) hy)
  exact (pseudolatticeScale_mem_iff _ _ _).mpr
    ⟨(p : K) * x, hxI, by rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul]⟩

/-- [RW-rec]: the order-prime inverse has exactly index p. -/
theorem inversePrime_index (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    inclusionIndex I.val (inversePrimeLattice P I r).val = p ∧
      inclusionIndex I.val (inversePrimeLattice P I q).val = p := by
  let S := pseudolatticeSaturation P I
  let c := inclusionIndex I.val (fractionalIdealCarrier S)
  have hIS : I.val ≤ S.coeToSubmodule.restrictScalars ℤ :=
    pseudolatticeSaturation_contains P I
  have hbound : ∀ x ∈ S.coeToSubmodule, (c : K) * x ∈ I.val := by
    intro x hx
    exact SplitPrimeLatticeAux.inclusionIndex_scale_le I.val (fractionalIdealCarrier S)
      ((pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩)
  have hi (t : FinitePlace.Prime K) (ht : (p : 𝓞 K) ∈ t.asIdeal) :
      inclusionIndex I.val (inversePrimeLattice P I t).val =
        Nat.card (FinitePlace.Residue t) := by
    calc
      inclusionIndex I.val (inversePrimeLattice P I t).val =
          inclusionIndex (fractionalIdealCarrier S)
            ((SplitPrimeLatticeAux.fullColon S.coeToSubmodule t.asIdeal).restrictScalars ℤ) :=
        SplitPrimeLatticeAux.colon_index_eq_full I.val S.coeToSubmodule hIS hm hbound
          t.asIdeal ht
      _ = Nat.card (FinitePlace.Residue t) := by
        simpa only [SplitPrimeLatticeAux.fullColon] using
          SplitPrimeLatticeAux.primeColon_index S (pseudolatticeSaturation_ne_zero P I) t
  have hpq : (p : 𝓞 K) ∈ r.asIdeal * q.asIdeal := by
    rw [h.2]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact ⟨(hi r (Ideal.mul_le_left hpq)).trans (split_residue_cards P hp h).1,
    (hi q (Ideal.mul_le_right hpq)).trans (split_residue_cards P hp h).2⟩

/-- [RW-rec]: both concrete lines have p elements. -/
theorem primeLine_cards (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    Nat.card (primeLine P I r) = p ∧ Nat.card (primeLine P I q) = p := by
  have hker : (ambientMk I.val).ker = I.val.toAddSubgroup :=
    QuotientAddGroup.ker_mk' _
  have hc (t : FinitePlace.Prime K) :
      Nat.card (primeLine P I t) = inclusionIndex I.val (inversePrimeLattice P I t).val := by
    rw [primeLine, ← AddSubgroup.relIndex_ker, hker]
    rfl
  simpa only [hc] using inversePrime_index P I hp hm h

/-- [RW-rec]: p⁻¹I/I is the direct sum of the two lines. -/
theorem primeLine_decomposition (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    primeLine P I r ⊔ primeLine P I q =
        LocalFourierSetup.pTorsion p (G := AmbientGroup I.val) ∧
      Disjoint (primeLine P I r) (primeLine P I q) := by
  let S : Submodule (𝓞 K) K := (pseudolatticeSaturation P I : Submodule (𝓞 K) K)
  let c := inclusionIndex I.val (S.restrictScalars ℤ)
  have hIS : I.val ≤ S.restrictScalars ℤ := pseudolatticeSaturation_contains P I
  have hbound : ∀ x ∈ S, (c : K) * x ∈ I.val := by
    intro x hx
    exact SplitPrimeLatticeAux.inclusionIndex_scale_le I.val (S.restrictScalars ℤ)
      ((pseudolatticeScale_mem_iff _ _ _).mpr ⟨x, hx, rfl⟩)
  have hcop : r.asIdeal ⊔ q.asIdeal = ⊤ := (r.isCoprime_of_ne q h.1).sup_eq
  simpa only [primeLine, inversePrimeCarrier, SplitPrimeLatticeAux.colon] using
    SplitPrimeLatticeAux.colon_crt_decomposition I.val S hIS hm hbound
      r.asIdeal q.asIdeal hcop h.2

/-- [RW-rec]: eta=1 mod p makes both inverse carriers period points. -/
theorem inversePrime_le_periodPoints (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p) :
    (inversePrimeCarrier P I r).toAddSubgroup ≤ pseudolatticePeriodPoints P I ∧
      (inversePrimeCarrier P I q).toAddSubgroup ≤ pseudolatticePeriodPoints P I := by
  have hpr : Ideal.span {(p : 𝓞 K)} ≤ r.asIdeal :=
    h.2 ▸ Ideal.mul_le_left
  have hpq : Ideal.span {(p : 𝓞 K)} ≤ q.asIdeal :=
    h.2 ▸ Ideal.mul_le_right
  have hstable : ∀ y ∈ I.val, ((epsilonInteger P - 1 : 𝓞 K) : K) * y ∈ I.val := by
    intro y hy
    change (P.epsilon - 1) * y ∈ I.val
    rw [sub_mul, one_mul]
    exact I.val.sub_mem
      ((DistributionOrbitGeometryAux.epsilon_mul_mem_iff P I y).mpr hy) hy
  constructor
  · intro x hx
    apply (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I x).mpr
    exact (mem_inversePrimeCarrier P I r x).mp hx _ (hpr hη) hstable
  · intro x hx
    apply (DistributionOrbitGeometryAux.periodPoints_iff_mul_sub_mem P I x).mpr
    exact (mem_inversePrimeCarrier P I q x).mp hx _ (hpq hη) hstable

/-- [RW-rec]: the same direct sum inside G_(I,eta), with its actual cardinalities. -/
theorem periodLine_decomposition (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p) :
    periodLine P I r ⊔ periodLine P I q = LocalFourierSetup.pTorsion p ∧
      Disjoint (periodLine P I r) (periodLine P I q) ∧
      Nat.card (periodLine P I r) = p ∧ Nat.card (periodLine P I q) = p := by
  obtain ⟨hsup, hdisj⟩ := primeLine_decomposition P I hp hm h
  obtain ⟨hrP, hqP⟩ := inversePrime_le_periodPoints P I hp hm h hη
  have hrange (t : FinitePlace.Prime K)
      (ht : (inversePrimeCarrier P I t).toAddSubgroup ≤ pseudolatticePeriodPoints P I) :
      primeLine P I t ≤ (toAmbient P I).range := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨pseudolatticeMk P I z (ht hz), rfl⟩
  have hr := hrange r hrP
  have hq := hrange q hqP
  have hinj := toAmbient_injective P I
  have htor : (LocalFourierSetup.pTorsion p (G := AmbientGroup I.val)).comap
      (toAmbient P I) = LocalFourierSetup.pTorsion p := by
    ext x
    change p • toAmbient P I x = 0 ↔ p • x = 0
    rw [← map_nsmul]
    exact ⟨fun hx => hinj (hx.trans (map_zero _).symm), fun hx => by rw [hx, map_zero]⟩
  have hc (t : FinitePlace.Prime K) (ht : primeLine P I t ≤ (toAmbient P I).range) :
      Nat.card (periodLine P I t) = Nat.card (primeLine P I t) := by
    calc
      Nat.card (periodLine P I t) =
          Nat.card ((periodLine P I t).map (toAmbient P I)) :=
        Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ hinj).toEquiv
      _ = Nat.card (primeLine P I t) := by
        rw [periodLine, AddSubgroup.map_comap_eq, inf_eq_right.mpr ht]
  refine ⟨?_, ?_, (hc r hr).trans (primeLine_cards P I hp hm h).1,
    (hc q hq).trans (primeLine_cards P I hp hm h).2⟩
  · change (primeLine P I r).comap (toAmbient P I) ⊔
        (primeLine P I q).comap (toAmbient P I) = _
    rw [AddSubgroup.comap_sup_eq_of_le_range _ hr hq, hsup, htor]
  · rw [disjoint_iff_inf_le]
    intro x hx
    apply (show x = 0 from hinj ?_)
    have hzero : toAmbient P I x = 0 := by
      exact (show toAmbient P I x ∈ (⊥ : AddSubgroup (AmbientGroup I.val)) from
        (disjoint_iff_inf_le.mp hdisj) hx)
    exact hzero.trans (map_zero _).symm


end SICLean.L5.SplitPrimeLattice
