import SICLean.L5.SplitPrimeLattice
import SICLean.L5.SplitGroupRing
import SICLean.L5.SplitPrimeGeometryAux
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Split local geometry and noncharacteristic cyclicization

[RW-rec, §7, pp. 11--12]. The local matrix calculation is [RW-rec, §6, p. 10]. Objects:
[RW26, p. 12, p. 20]. Maximal-order residue coordinates act on the saturation modulo p
and are transported to I/pI. No O_K-action on the original I is assumed. In particular a
leading term B in O_K is not assumed to preserve I globally.
-/

noncomputable section
open scoped NumberField Matrix

namespace SICLean.L5.SplitPrimeGeometry

open L3 SplitPrimeLattice DistributionOrbitGeometry DistributionSubgroups SplitPrimeGeometryAux

variable {K : Type} [Field K] [NumberField K]

/-- [RW-rec]: a field element, before asserting its integrality. -/
def leadingTerm (P : PeriodData K) (p s : ℕ) : K :=
  (P.epsilon - 1) / (p : K) ^ s

/-- Raw residue-coordinate compatibility, just the two kernels of the maps. -/
def ResidueCoordinates (p : ℕ) (r q : FinitePlace.Prime K)
    (ρ : 𝓞 K →+* ZMod p × ZMod p) : Prop :=
  Function.Surjective ρ ∧
    (∀ a : 𝓞 K, (ρ a).1 = 0 ↔ a ∈ r.asIdeal) ∧
    (∀ a : 𝓞 K, (ρ a).2 = 0 ↔ a ∈ q.asIdeal)

/-- [RW-rec]: swapping the two primes changes no arithmetic hypotheses. -/
theorem splitPair_symm {p : ℕ} {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    IsSplitPair p q r := by
  exact ⟨h.1.symm, (mul_comm _ _).trans h.2⟩

/-- [RW-rec]: actual CRT residue coordinates, independent of a period basis. -/
theorem exists_residueCoordinates (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) :
    ∃ ρ : 𝓞 K →+* ZMod p × ZMod p, ResidueCoordinates p r q ρ := by
  classical
  letI : Fintype (FinitePlace.Residue r) := Fintype.ofFinite _
  letI : Fintype (FinitePlace.Residue q) := Fintype.ofFinite _
  let er : FinitePlace.Residue r ≃+* ZMod p :=
    (ZMod.ringEquivOfPrime _ hp (by
      simpa only [Nat.card_eq_fintype_card] using (split_residue_cards P hp h).1)).symm
  let eq : FinitePlace.Residue q ≃+* ZMod p :=
    (ZMod.ringEquivOfPrime _ hp (by
      simpa only [Nat.card_eq_fintype_card] using (split_residue_cards P hp h).2)).symm
  have hcop : IsCoprime r.asIdeal q.asIdeal :=
    Ideal.isCoprime_of_isMaximal (fun he => h.1 (IsDedekindDomain.HeightOneSpectrum.ext he))
  let e := (Ideal.quotientInfEquivQuotientProd r.asIdeal q.asIdeal hcop).trans
    (er.prodCongr eq)
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk _), ?_, ?_, ?_⟩
  · exact e.surjective.comp Ideal.Quotient.mk_surjective
  · intro a
    change er (Ideal.Quotient.mk r.asIdeal a) = 0 ↔ _
    rw [map_eq_zero_iff er er.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro a
    change eq (Ideal.Quotient.mk q.asIdeal a) = 0 ↔ _
    rw [map_eq_zero_iff eq eq.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- [RW-rec]: equal positive valuations give a common exact p-power. The unit condition is a
conclusion, not part of the definition of B. -/
theorem exists_exact_leadingTerm (P : PeriodData K) {p : ℕ} (hp : p.Prime)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ hB : IsIntegral ℤ (leadingTerm P p s),
      (⟨leadingTerm P p s, hB⟩ : 𝓞 K) ∉ r.asIdeal ∧
      (⟨leadingTerm P p s, hB⟩ : 𝓞 K) ∉ q.asIdeal := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ, hρ⟩ := exists_residueCoordinates P hp h
  have hpnu : ¬ IsUnit (p : 𝓞 K) := by
    intro hu
    have hu' := hu.map ((RingHom.fst (ZMod p) (ZMod p)).comp ρ)
    simp at hu'
  have heps : epsilonInteger P - 1 ≠ 0 := by
    intro hz
    have he : P.epsilon = 1 := by
      have he := congrArg (algebraMap (𝓞 K) K) hz
      simp only [map_sub, map_one, map_zero, epsilonInteger,
        NumberField.RingOfIntegers.map_mk] at he
      exact sub_eq_zero.mp he
    have he' := P.epsilon_gt_one
    simp [he] at he'
  have hfin : FiniteMultiplicity (p : 𝓞 K) (epsilonInteger P - 1) :=
    FiniteMultiplicity.of_not_isUnit hpnu heps
  let s : ℕ := multiplicity (p : 𝓞 K) (epsilonInteger P - 1)
  obtain ⟨B, heq, hnB⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hs : 1 ≤ s :=
    multiplicity_pos_of_dvd (Ideal.mem_span_singleton.mp hη) hfin
  have hlead : leadingTerm P p s = (B : K) := by
    unfold leadingTerm
    apply (div_eq_iff (pow_ne_zero s (Nat.cast_ne_zero.mpr hp.ne_zero))).mpr
    have heqK : P.epsilon - 1 = (p : K) ^ s * (B : K) := by
      have heqK := congrArg (algebraMap (𝓞 K) K) heq
      simpa only [s, map_sub, map_one, map_mul, map_pow, map_natCast,
        epsilonInteger, NumberField.RingOfIntegers.map_mk,
        NumberField.RingOfIntegers.coe_eq_algebraMap] using heqK
    exact heqK.trans (mul_comm _ _)
  have hB : IsIntegral ℤ (leadingTerm P p s) := by
    rw [hlead]
    exact B.property
  have hBeq : (⟨leadingTerm P p s, hB⟩ : 𝓞 K) = B :=
    NumberField.RingOfIntegers.ext hlead
  have hopp : (ρ B).2 = -(ρ B).1 := period_div_opposite P hs ρ hρ.1 B hlead.symm
  have hcop : r.asIdeal ⊔ q.asIdeal = ⊤ := by
    apply Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance
    intro he
    exact h.1 (IsDedekindDomain.HeightOneSpectrum.ext he)
  have hinf : r.asIdeal ⊓ q.asIdeal = Ideal.span {(p : 𝓞 K)} :=
    (Ideal.mul_eq_inf_of_coprime hcop).symm.trans h.2
  have hnotboth : ¬ (B ∈ r.asIdeal ∧ B ∈ q.asIdeal) := by
    intro hBboth
    have hmem : B ∈ r.asIdeal ⊓ q.asIdeal := hBboth
    rw [hinf, Ideal.mem_span_singleton] at hmem
    exact hnB hmem
  refine ⟨s, hs, hB, ?_, ?_⟩
  · rw [hBeq]
    intro hr
    have hz : (ρ B).1 = 0 := (hρ.2.1 B).mpr hr
    have hq : B ∈ q.asIdeal := (hρ.2.2 B).mp (calc
      (ρ B).2 = -(ρ B).1 := hopp
      _ = -(0 : ZMod p) := congrArg Neg.neg hz
      _ = 0 := neg_zero)
    exact hnotboth ⟨hr, hq⟩
  · rw [hBeq]
    intro hq
    have hz : (ρ B).2 = 0 := (hρ.2.2 B).mpr hq
    have hr : B ∈ r.asIdeal := (hρ.2.1 B).mp (by
      have hn : -(ρ B).1 = 0 := hopp.symm.trans hz
      exact neg_eq_zero.mp hn)
    exact hnotboth ⟨hr, hq⟩

/-- [RW-rec]: the literal trace identity. -/
theorem leadingTerm_trace (P : PeriodData K) {p s : ℕ} (hp : p.Prime) :
    Algebra.trace ℚ K (leadingTerm P p s) =
      -(p : ℚ) ^ s * Algebra.norm ℚ (leadingTerm P p s) := by
  simpa only [leadingTerm, Rat.cast_pow, Rat.cast_natCast] using
    SplitPrimeGeometryAux.trace_div_period_sub_one P ((p : ℚ) ^ s)
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))

/-- [RW-rec]: the two residues are opposite and nonzero; oddness then makes them distinct.
Integrality and the two unit facts are explicit inputs. -/
theorem leadingTerm_residues (P : PeriodData K) {p s : ℕ} [Fact p.Prime]
    (hodd : p ≠ 2) (hs : 1 ≤ s) {r q : FinitePlace.Prime K}
    (ρ : 𝓞 K →+* ZMod p × ZMod p) (hρ : ResidueCoordinates p r q ρ)
    (hB : IsIntegral ℤ (leadingTerm P p s))
    (hr : (⟨leadingTerm P p s, hB⟩ : 𝓞 K) ∉ r.asIdeal)
    (hq : (⟨leadingTerm P p s, hB⟩ : 𝓞 K) ∉ q.asIdeal) :
    ∃ b : ZMod p, b ≠ 0 ∧ b ≠ -b ∧
      ρ ⟨leadingTerm P p s, hB⟩ = (b, -b) := by
  let B : 𝓞 K := ⟨leadingTerm P p s, hB⟩
  have hfirst : (ρ B).1 ≠ 0 := fun hz => hr ((hρ.2.1 B).mp hz)
  have hopp : (ρ B).2 = -(ρ B).1 := period_div_opposite P hs ρ hρ.1 B rfl
  refine ⟨(ρ B).1, hfirst, ?_, Prod.ext rfl hopp⟩
  intro hb
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (fun hd => hodd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
        Nat.prime_two).mp hd))
  apply hfirst
  exact (mul_eq_zero.mp (show (2 : ZMod p) * (ρ B).1 = 0 by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hb)).resolve_left htwo

/-- [RW-rec]: a full equal-exponent primary decomposition, together with the prime-to-p complement
required by the existing local Lemma 1. -/
theorem primary_decomposition (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p) :
    ∃ (s : ℕ) (C : AddSubgroup (PseudolatticeGroup P I)),
      1 ≤ s ∧ Nat.Coprime p (Nat.card C) ∧
      Nonempty ((FiniteCosetMoments.Point p s 2 × C) ≃+ PseudolatticeGroup P I) := by
  obtain ⟨s, hs, hB, hr, hq⟩ := exists_exact_leadingTerm P hp h hη
  let H := AddCommGroup.primaryComponent (PseudolatticeGroup P I) p
  let f := toAmbient P I
  have hmap : H.map f = LocalFourierSetup.pTorsion (p ^ s) :=
    primary_ambient_image_of_division P I hp hs hm h hB hr hq
  let u : H ≃+ H.map f := H.equivMapOfInjective f (toAmbient_injective P I)
  let v : H.map f ≃+ LocalFourierSetup.pTorsion (p ^ s) := by
    rw [hmap]
  obtain ⟨w⟩ := ambient_division_equiv P I (p ^ s) (pow_ne_zero _ hp.ne_zero)
  let d : H ≃+ FiniteCosetMoments.Point p s 2 := (u.trans v).trans w
  obtain ⟨C, hC, ⟨e⟩⟩ := finite_primary_splitting (G := PseudolatticeGroup P I) p hp
  exact ⟨s, C, hs, hC, ⟨(d.symm.prodCongr (AddEquiv.refl C)).trans e⟩⟩

/-- [RW-rec]: choose generators of the actual two lines as the two coordinates of G[p]; the choice
concerns coordinates, not a direction. -/
theorem exists_split_coordinates (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} [Fact p.Prime] (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q) (hη : PeriodOneMod P p) :
    ∃ c : (ZMod p × ZMod p) ≃+
      LocalFourierSetup.pTorsion p (G := PseudolatticeGroup P I),
      AddSubgroup.zmultiples (c (1, 0)).val = periodLine P I r ∧
        AddSubgroup.zmultiples (c (0, 1)).val = periodLine P I q := by
  obtain ⟨hs, hd, hr, hq⟩ := periodLine_decomposition P I (Fact.out : p.Prime) hm h hη
  exact coordinates_of_prime_order _ _ _ hd hs hr hq

/-- [RW-rec]: the primary component has the actual p-division carrier inside K/I. This also fixes
the exponent used in cyclicization. -/
theorem primary_ambient_image (P : PeriodData K) (I : StablePseudolattice P)
    {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s) (hm : LocallyMaximal P I p)
    {r q : FinitePlace.Prime K} (h : IsSplitPair p r q)
    (hB : IsIntegral ℤ (leadingTerm P p s))
    (hr : (⟨leadingTerm P p s, hB⟩ : 𝓞 K) ∉ r.asIdeal)
    (hq : (⟨leadingTerm P p s, hB⟩ : 𝓞 K) ∉ q.asIdeal) :
    (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p).map (toAmbient P I) =
      LocalFourierSetup.pTorsion (p ^ s) (G := AmbientGroup I.val) := by
  exact primary_ambient_image_of_division P I hp hs hm h hB hr hq

/-- [RW-rec]: the distinct diagonal eigenvalues preserve exactly two lines. These are additive
F_p-lines, not arbitrary subgroups of K/I. -/
theorem only_two_invariant_lines {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (b : ZMod p) (hb : b ≠ 0) (L : AddSubgroup (ZMod p × ZMod p))
    (hL : Nat.card L = p)
    (hstable : ∀ z ∈ L, (b * z.1, -b * z.2) ∈ L) :
    L = (⊤ : AddSubgroup (ZMod p)).prod ⊥ ∨
      L = (⊥ : AddSubgroup (ZMod p)).prod ⊤ := by
  exact only_two_invariant_lines_of_stable hodd b hb L hL hstable

/-- [RW-rec]: in coordinates whose first vector spans a non-eigenline, the lower-left matrix entry
is nonzero modulo p. -/
theorem non_eigen_lower_left {p : ℕ} [Fact p.Prime]
    (B S T : Matrix (Fin 2) (Fin 2) (ZMod p)) (hST : S * T = 1) (hTS : T * S = 1)
    (hline : ¬ ∃ c : ZMod p, B.mulVec (fun i => S i 0) = c • (fun i => S i 0)) :
    (T * B * S) 1 0 ≠ 0 := by
  intro hzero
  apply hline
  refine ⟨(T * B * S) 0 0, ?_⟩
  have hv : (T * B * S).mulVec (Pi.single 0 1) =
      (T * B * S) 0 0 • (Pi.single 0 1 : Fin 2 → ZMod p) := by
    ext i
    fin_cases i <;> simp [Matrix.col_apply, hzero]
  have h := congrArg S.mulVec hv
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
  simp only [← Matrix.mul_assoc, hST, Matrix.one_mul, Matrix.mulVec_single_one,
    Matrix.col_mul_eq_mulVec_col] at h
  change B.mulVec (fun i => S i 0) = (T * B * S) 0 0 • (fun i => S i 0) at h
  exact h

/-- [RW-rec]. This is the substantive noncharacteristic-overlattice cyclicization statement. -/
theorem noncharacteristic_cyclic (P : PeriodData K) (I : StablePseudolattice P)
    {p s : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hs : 1 ≤ s)
    (hm : LocallyMaximal P I p) {r q : FinitePlace.Prime K}
    (h : IsSplitPair p r q) (hη : PeriodOneMod P p)
    (C : AddSubgroup (PseudolatticeGroup P I)) (hC : Nat.Coprime p (Nat.card C))
    (e : (FiniteCosetMoments.Point p s 2 × C) ≃+ PseudolatticeGroup P I)
    (L : AddSubgroup (PseudolatticeGroup P I))
    (hL : SplitGroupRing.FullCyclicSummand p s L)
    (hr : L ⊓ LocalFourierSetup.pTorsion p ≠ periodLine P I r)
    (hq : L ⊓ LocalFourierSetup.pTorsion p ≠ periodLine P I q) :
    IsAddCyclic (AddCommGroup.primaryComponent
      (PseudolatticeGroup P (subgroupLattice P I L)) p) := by
  obtain ⟨t, ht, hB, hrB, hqB⟩ := exists_exact_leadingTerm P (Fact.out : p.Prime) h hη
  have hmap := primary_ambient_image P I (Fact.out : p.Prime) ht hm h hB hrB hqB
  let u := subgroupEquivOfMapEq (toAmbient P I) (toAmbient_injective P I)
    (AddCommGroup.primaryComponent (PseudolatticeGroup P I) p)
    (LocalFourierSetup.pTorsion (p ^ t)) hmap
  obtain ⟨w⟩ := ambient_division_equiv P I (p ^ t)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hst : s = t := plane_exponent_unique (Fact.out : p.Prime) hC e (u.trans w)
  subst t
  apply primary_cyclic_of_not_mul_sub_one_le_pScale P (subgroupLattice P I L)
  let B : 𝓞 K := ⟨leadingTerm P p s, hB⟩
  have hp : p.Prime := Fact.out
  have heq : (p : K) ^ s * (B : K) = P.epsilon - 1 := by
    dsimp [B, leadingTerm]
    exact mul_div_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))
  obtain ⟨ρ, hρ⟩ := exists_residueCoordinates P hp h
  obtain ⟨b, hb, _, hρB⟩ := leadingTerm_residues P hodd hs ρ hρ hB hrB hqB
  exact noncharacteristic_not_containment_of_leading_data P I hodd hs hm h hη
    B heq ρ hρ b hb hρB L hL.1 hL.2.1 hr hq

/-- [RW-rec]: the old p-torsion translations map into the cyclic primary group of J, so Theorem 4
applies to every one of them. -/
theorem projected_pTorsion (P : PeriodData K) (I : StablePseudolattice P)
    {p : ℕ} (hp : p.Prime) (L : AddSubgroup (PseudolatticeGroup P I))
    (u : PseudolatticeGroup P I) (hu : p • u = 0) :
    periodProject P I (subgroupLattice P I L) (le_overlattice P I L) u ∈
      AddCommGroup.primaryComponent (PseudolatticeGroup P (subgroupLattice P I L)) p := by
  apply AddCommGroup.mem_primaryComponent.mpr
  refine ⟨1, ?_⟩
  simpa only [pow_one, ← map_nsmul, hu, map_zero]


end SICLean.L5.SplitPrimeGeometry
