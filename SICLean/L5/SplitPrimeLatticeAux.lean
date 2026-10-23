import SICLean.L3.PseudolatticeIdeal
import SICLean.L5.DistributionNormalized
import SICLean.L5.PrimeSpecialization
import SICLean.L5.LocalFourierSetup

set_option autoImplicit false

/-!
Auxiliary arithmetic for the split-prime colon. The finite index kills the saturation
quotient; a prime-to-p bound then permits Bezout descent from the maximal-order lattice
to the original integer lattice.
-/

noncomputable section
open scoped NumberField nonZeroDivisors

namespace SICLean.L5.SplitPrimeLatticeAux

open L3 DistributionOrbitGeometry

variable {K : Type} [Field K] [NumberField K]

theorem inclusionIndex_scale_le (I J : Submodule ℤ K) :
    pseudolatticeScale (inclusionIndex I J : K) J ≤ I := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (pseudolatticeScale_mem_iff _ _ _).mp hx
  change (inclusionIndex I J : K) * y ∈ I.toAddSubgroup
  simpa only [inclusionIndex, nsmul_eq_mul] using
    I.toAddSubgroup.nsmul_relIndex_mem (K := J.toAddSubgroup) hy

theorem coprime_relIndex_of_scale_le (I J : Submodule ℤ K)
    (hI : Submodule.IsLattice ℚ I) (hJ : Submodule.IsLattice ℚ J) (hIJ : I ≤ J)
    {p C : ℕ} (hp : p.Prime) (hpc : ¬ p ∣ C)
    (hbound : pseudolatticeScale (C : K) J ≤ I) :
    Nat.Coprime p (inclusionIndex I J) := by
  let N : Submodule ℤ J := I.submoduleOf J
  let : Finite (J ⧸ N) :=
    DistributionOrbitGeometryAux.lattice_quotient_finite I J hI hJ hIJ
  let : Fact p.Prime := ⟨hp⟩
  change Nat.Coprime p (Nat.card (J ⧸ N))
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := J ⧸ N) p hdiv
  have hc : C • x = 0 := by
    refine Quotient.inductionOn' x (fun y => ?_)
    change N.mkQ (C • y) = 0
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change C • (y : K) ∈ I
    simpa only [nsmul_eq_mul] using
      hbound ((pseudolatticeScale_mem_iff _ _ _).mpr ⟨y.val, y.property, rfl⟩)
  exact hpc (hx ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hc)

def colon (I : Submodule ℤ K) (r : Ideal (𝓞 K)) : Submodule ℤ K :=
  ⨅ a : {a : 𝓞 K // a ∈ r ∧ ∀ y ∈ I, (a : K) * y ∈ I},
    I.comap (LinearMap.mulLeft ℤ (a.val : K))

theorem mem_colon (I : Submodule ℤ K) (r : Ideal (𝓞 K)) (x : K) :
    x ∈ colon I r ↔ ∀ a : 𝓞 K, a ∈ r →
      (∀ y ∈ I, (a : K) * y ∈ I) → (a : K) * x ∈ I := by
  simp only [colon, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply]
  constructor
  · intro h a ha hI
    exact h ⟨a, ha, hI⟩
  · intro h a
    exact h a.val a.property.1 a.property.2

theorem bezout_mem (I : Submodule ℤ K) {p c : ℕ} (hc : Nat.Coprime p c)
    {x : K} (hcx : (c : K) * x ∈ I) (hpx : (p : K) * x ∈ I) : x ∈ I := by
  obtain ⟨u, v, huv⟩ := hc.symm.isCoprime
  have hcast : (u : K) * (c : K) + (v : K) * (p : K) = 1 := by
    exact_mod_cast huv
  have hh := I.add_mem (I.smul_mem u hcx) (I.smul_mem v hpx)
  simpa only [zsmul_eq_mul, ← mul_assoc, ← add_mul, hcast, one_mul] using hh

theorem contracted_multiple (I : Submodule ℤ K) (S : Submodule (𝓞 K) K)
    (hIS : I ≤ S.restrictScalars ℤ) {c : ℕ}
    (hc : ∀ x ∈ S, (c : K) * x ∈ I) (a : 𝓞 K) :
    ∀ y ∈ I, (((c : 𝓞 K) * a : 𝓞 K) : K) * y ∈ I := by
  intro y hy
  have has : (a : K) * y ∈ S := by
    simpa only [Algebra.smul_def] using S.smul_mem a (hIS hy)
  simpa only [map_mul, map_natCast, mul_assoc] using hc _ has

theorem colon_le_pdivision (I : Submodule ℤ K) (r : Ideal (𝓞 K)) {p : ℕ}
    (hp : (p : 𝓞 K) ∈ r) {x : K} (hx : x ∈ colon I r) :
    (p : K) * x ∈ I := by
  apply (mem_colon I r x).mp hx (p : 𝓞 K) hp
  intro y hy
  simpa only [zsmul_eq_mul, Int.cast_natCast, map_natCast] using I.smul_mem (p : ℤ) hy

theorem colon_crt_inf (I : Submodule ℤ K) (S : Submodule (𝓞 K) K)
    (hIS : I ≤ S.restrictScalars ℤ) {p c : ℕ} (hc : Nat.Coprime p c)
    (hbound : ∀ x ∈ S, (c : K) * x ∈ I)
    (r q : Ideal (𝓞 K)) (hcop : r ⊔ q = ⊤)
    (hr : (p : 𝓞 K) ∈ r) : colon I r ⊓ colon I q = I := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Ideal.isCoprime_iff_sup_eq.mpr hcop).exists
    have hca := (mem_colon I r x).mp hx.1 ((c : 𝓞 K) * a)
      (r.mul_mem_left _ ha) (contracted_multiple I S hIS hbound a)
    have hcb := (mem_colon I q x).mp hx.2 ((c : 𝓞 K) * b)
      (q.mul_mem_left _ hb) (contracted_multiple I S hIS hbound b)
    have habK : (a : K) + (b : K) = 1 := by exact_mod_cast hab
    have hcx := I.add_mem hca hcb
    change (c : K) * (a : K) * x + (c : K) * (b : K) * x ∈ I at hcx
    rw [← add_mul, ← mul_add, habK, mul_one] at hcx
    exact bezout_mem I hc hcx (colon_le_pdivision I r hr hx.1)
  · intro x hx
    constructor <;> apply (mem_colon I _ x).mpr <;> intro a ha hmul <;> exact hmul x hx

theorem colon_crt_components (I : Submodule ℤ K) (S : Submodule (𝓞 K) K)
    (hIS : I ≤ S.restrictScalars ℤ) {p c : ℕ} (hc : Nat.Coprime p c)
    (hbound : ∀ x ∈ S, (c : K) * x ∈ I)
    (r q : Ideal (𝓞 K)) (hcop : r ⊔ q = ⊤)
    (hprod : r * q = Ideal.span {(p : 𝓞 K)})
    {x : K} (hx : (p : K) * x ∈ I) :
    ∃ y ∈ colon I r, ∃ z ∈ colon I q, y + z - x ∈ I := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Ideal.isCoprime_iff_sup_eq.mpr hcop).exists
  obtain ⟨u, v, huv⟩ := hc.symm.isCoprime
  have huvK : (u : K) * (c : K) + (v : K) * (p : K) = 1 := by
    exact_mod_cast huv
  have habK : (a : K) + (b : K) = 1 := by exact_mod_cast hab
  have hcomponent (r q : Ideal (𝓞 K)) (b : 𝓞 K) (hb : b ∈ q)
      (hprod : r * q = Ideal.span {(p : 𝓞 K)}) :
      (u : K) * (c : K) * (b : K) * x ∈ colon I r := by
    apply (mem_colon I r _).mpr
    intro d hd _
    have hdb : d * b ∈ Ideal.span {(p : 𝓞 K)} :=
      hprod ▸ Ideal.mul_mem_mul hd hb
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hdb
    have htK : (d : K) * (b : K) = (p : K) * (t : K) := by exact_mod_cast ht
    have htx : (t : K) * ((p : K) * x) ∈ S := by
      simpa only [Algebra.smul_def] using S.smul_mem t (hIS hx)
    have hct := I.smul_mem u (hbound _ htx)
    convert hct using 1 <;> simp only [zsmul_eq_mul]
    · change (d : K) * ((u : K) * (c : K) * (b : K) * x) = _
      calc
        _ = (u : K) * (c : K) * ((d : K) * (b : K)) * x := by ring
        _ = _ := by rw [htK]; ring
  refine ⟨_, hcomponent r q b hb hprod, _,
    hcomponent q r a ha (by simpa only [mul_comm] using hprod), ?_⟩
  have hv := I.smul_mem (-v) hx
  convert hv using 1 <;> simp only [zsmul_eq_mul, Int.cast_neg]
  calc
    (u : K) * (c : K) * (b : K) * x + (u : K) * (c : K) * (a : K) * x - x =
        ((u : K) * (c : K) * ((a : K) + (b : K)) - 1) * x := by ring
    _ = - (v : K) * ((p : K) * x) := by rw [habK, mul_one]; linear_combination huvK * x

def fullColon (S : Submodule (𝓞 K) K) (r : Ideal (𝓞 K)) : Submodule (𝓞 K) K :=
  ⨅ a : {a : 𝓞 K // a ∈ r},
    S.comap (LinearMap.mulLeft (𝓞 K) (a.val : K))

theorem mem_fullColon (S : Submodule (𝓞 K) K) (r : Ideal (𝓞 K)) (x : K) :
    x ∈ fullColon S r ↔ ∀ a : 𝓞 K, a ∈ r → (a : K) * x ∈ S := by
  simp only [fullColon, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply]
  constructor
  · intro h a ha
    exact h ⟨a, ha⟩
  · intro h a
    exact h a.val a.property

theorem le_fullColon (S : Submodule (𝓞 K) K) (r : Ideal (𝓞 K)) :
    S ≤ fullColon S r := by
  intro x hx
  apply (mem_fullColon S r x).mpr
  intro a _
  simpa only [Algebra.smul_def] using S.smul_mem a hx

theorem colon_le_fullColon (I : Submodule ℤ K) (S : Submodule (𝓞 K) K)
    (hIS : I ≤ S.restrictScalars ℤ) {p c : ℕ} (hc : Nat.Coprime p c)
    (hbound : ∀ x ∈ S, (c : K) * x ∈ I)
    (r : Ideal (𝓞 K)) (hr : (p : 𝓞 K) ∈ r) :
    colon I r ≤ (fullColon S r).restrictScalars ℤ := by
  intro x hx
  apply (mem_fullColon S r x).mpr
  intro a ha
  have hcax := (mem_colon I r x).mp hx ((c : 𝓞 K) * a)
    (r.mul_mem_left _ ha) (contracted_multiple I S hIS hbound a)
  have hpx := colon_le_pdivision I r hr hx
  have hpax : (p : K) * ((a : K) * x) ∈ S := by
    have ht := S.smul_mem a (hIS hpx)
    simpa only [Algebra.smul_def, mul_left_comm] using ht
  apply bezout_mem (S.restrictScalars ℤ) hc _ hpax
  simpa only [map_mul, map_natCast, mul_assoc] using hIS hcax

theorem colon_inf_sat (I : Submodule ℤ K) (S : Submodule (𝓞 K) K)
    (hIS : I ≤ S.restrictScalars ℤ) {p c : ℕ} (hc : Nat.Coprime p c)
    (hbound : ∀ x ∈ S, (c : K) * x ∈ I)
    (r : Ideal (𝓞 K)) (hr : (p : 𝓞 K) ∈ r) :
    colon I r ⊓ S.restrictScalars ℤ = I := by
  apply le_antisymm
  · intro x hx
    exact bezout_mem I hc (hbound x hx.2) (colon_le_pdivision I r hr hx.1)
  · intro x hx
    exact ⟨(mem_colon I r x).mpr (fun a _ hmul => hmul x hx), hIS hx⟩

theorem colon_sup_sat (I : Submodule ℤ K) (S : Submodule (𝓞 K) K)
    (hIS : I ≤ S.restrictScalars ℤ) {p c : ℕ} (hc : Nat.Coprime p c)
    (hbound : ∀ x ∈ S, (c : K) * x ∈ I)
    (r : Ideal (𝓞 K)) (hr : (p : 𝓞 K) ∈ r) :
    colon I r ⊔ S.restrictScalars ℤ = (fullColon S r).restrictScalars ℤ := by
  apply le_antisymm
  · exact sup_le (colon_le_fullColon I S hIS hc hbound r hr) (le_fullColon S r)
  · intro x hx
    obtain ⟨u, v, huv⟩ := hc.symm.isCoprime
    have huvK : (u : K) * (c : K) + (v : K) * (p : K) = 1 := by
      exact_mod_cast huv
    have hcx : (c : K) * x ∈ colon I r := by
      apply (mem_colon I r _).mpr
      intro a ha _
      have hax := (mem_fullColon S r x).mp hx a ha
      simpa only [mul_left_comm] using hbound _ hax
    have hpx : (p : K) * x ∈ S := by
      simpa only [map_natCast] using (mem_fullColon S r x).mp hx (p : 𝓞 K) hr
    refine Submodule.mem_sup.mpr ⟨u • ((c : K) * x), (colon I r).smul_mem u hcx,
      v • ((p : K) * x), (S.restrictScalars ℤ).smul_mem v hpx, ?_⟩
    simp only [zsmul_eq_mul, ← mul_assoc, ← add_mul, huvK, one_mul]

theorem colon_index_eq_full (I : Submodule ℤ K) (S : Submodule (𝓞 K) K)
    (hIS : I ≤ S.restrictScalars ℤ) {p c : ℕ} (hc : Nat.Coprime p c)
    (hbound : ∀ x ∈ S, (c : K) * x ∈ I)
    (r : Ideal (𝓞 K)) (hr : (p : 𝓞 K) ∈ r) :
    inclusionIndex I (colon I r) =
      inclusionIndex (S.restrictScalars ℤ) ((fullColon S r).restrictScalars ℤ) := by
  have hinf := congrArg Submodule.toAddSubgroup (colon_inf_sat I S hIS hc hbound r hr)
  have hsup := congrArg Submodule.toAddSubgroup (colon_sup_sat I S hIS hc hbound r hr)
  change ((colon I r).toAddSubgroup ⊓ (S.restrictScalars ℤ).toAddSubgroup) =
    I.toAddSubgroup at hinf
  have hsup' : (colon I r ⊔ S.restrictScalars ℤ).toAddSubgroup =
      (colon I r).toAddSubgroup ⊔ (S.restrictScalars ℤ).toAddSubgroup := by
    ext x
    change x ∈ colon I r ⊔ S.restrictScalars ℤ ↔ _
    rw [Submodule.mem_sup, AddSubgroup.mem_sup]
    rfl
  rw [hsup'] at hsup
  unfold inclusionIndex
  rw [← hinf, AddSubgroup.inf_relIndex_left, ← hsup, AddSubgroup.relIndex_sup_right]

theorem mem_pTorsion_ambient (I : Submodule ℤ K) (p : ℕ) (x : K) :
    ambientMk I x ∈ LocalFourierSetup.pTorsion p ↔ (p : K) * x ∈ I := by
  change p • ambientMk I x = 0 ↔ _
  rw [← map_nsmul]
  change (QuotientAddGroup.mk (p • x) : AmbientGroup I) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  simp only [nsmul_eq_mul]
  rfl

theorem colon_crt_decomposition (I : Submodule ℤ K) (S : Submodule (𝓞 K) K)
    (hIS : I ≤ S.restrictScalars ℤ) {p c : ℕ} (hc : Nat.Coprime p c)
    (hbound : ∀ x ∈ S, (c : K) * x ∈ I)
    (r q : Ideal (𝓞 K)) (hcop : r ⊔ q = ⊤)
    (hprod : r * q = Ideal.span {(p : 𝓞 K)}) :
    (colon I r).toAddSubgroup.map (ambientMk I) ⊔
        (colon I q).toAddSubgroup.map (ambientMk I) =
          LocalFourierSetup.pTorsion p ∧
      Disjoint ((colon I r).toAddSubgroup.map (ambientMk I))
        ((colon I q).toAddSubgroup.map (ambientMk I)) := by
  have hp_prod : (p : 𝓞 K) ∈ r * q := by
    rw [hprod]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hr := Ideal.mul_le_left hp_prod
  have hq := Ideal.mul_le_right hp_prod
  constructor
  · apply le_antisymm
    · apply sup_le
      · rintro g ⟨x, hx, rfl⟩
        exact (mem_pTorsion_ambient I p x).mpr (colon_le_pdivision I r hr hx)
      · rintro g ⟨x, hx, rfl⟩
        exact (mem_pTorsion_ambient I p x).mpr (colon_le_pdivision I q hq hx)
    · intro g hg
      induction g using QuotientAddGroup.induction_on with
      | H x =>
        have hpx := (mem_pTorsion_ambient I p x).mp hg
        obtain ⟨y, hy, z, hz, hsum⟩ :=
          colon_crt_components I S hIS hc hbound r q hcop hprod hpx
        apply AddSubgroup.mem_sup.mpr
        refine ⟨ambientMk I y, ⟨y, hy, rfl⟩, ambientMk I z, ⟨z, hz, rfl⟩, ?_⟩
        rw [← map_add]
        exact QuotientAddGroup.eq_iff_sub_mem.mpr hsum
  · rw [AddSubgroup.disjoint_def]
    intro g hg₁ hg₂
    obtain ⟨x, hx, rfl⟩ := hg₁
    obtain ⟨y, hy, hyx⟩ := hg₂
    have hxy : x - y ∈ I := by
      simpa only [neg_sub] using I.neg_mem (QuotientAddGroup.eq_iff_sub_mem.mp hyx)
    have hIcolon : I ≤ colon I q := by
      intro z hz
      exact (mem_colon I q z).mpr (fun a _ hmul => hmul z hz)
    have hxq : x ∈ colon I q := by
      simpa only [sub_add_cancel] using (colon I q).add_mem (hIcolon hxy) hy
    have hxI : x ∈ I := by
      rw [← colon_crt_inf I S hIS hc hbound r q hcop hr]
      exact ⟨hx, hxq⟩
    exact (QuotientAddGroup.eq_zero_iff x).mpr hxI

abbrev FIdeal (K : Type) [Field K] := FractionalIdeal (𝓞 K)⁰ K

def integerEquivOne : 𝓞 K ≃ₗ[𝓞 K] (1 : FIdeal K) :=
  LinearEquiv.ofBijective
    { toFun := fun a => ⟨algebraMap (𝓞 K) K a, FractionalIdeal.coe_mem_one _ a⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp [Algebra.smul_def] }
    ⟨by
        intro a b h
        have hab : algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b :=
          congrArg (fun x : (1 : FIdeal K) => (x : K)) h
        exact IsFractionRing.injective (𝓞 K) K hab,
      by
        intro x
        obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp x.property
        exact ⟨a, Subtype.ext ha⟩⟩

def quotientOneEquiv (r : FinitePlace.Prime K) :
    ((1 : FIdeal K) ⧸ (r.asIdeal : FIdeal K).coeToSubmodule.comap
      (1 : FIdeal K).coeToSubmodule.subtype) ≃ₗ[𝓞 K] FinitePlace.Residue r := by
  apply LinearEquiv.symm
  apply Submodule.Quotient.equiv r.asIdeal _ integerEquivOne
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ ha
  · intro hx
    obtain ⟨a, ha, heq⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
    exact ⟨a, ha, Subtype.ext heq⟩

theorem mem_inversePrime_mul (S : FIdeal K) (r : FinitePlace.Prime K) (x : K) :
    x ∈ (r.asIdeal : FIdeal K)⁻¹ * S ↔
      ∀ a : 𝓞 K, a ∈ r.asIdeal → (a : K) * x ∈ S := by
  have hr : (r.asIdeal : FIdeal K) ≠ 0 := by simpa using r.ne_bot
  rw [mul_comm, ← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hr]
  constructor
  · intro hx a ha
    simpa [mul_comm] using hx (a : K) (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ ha)
  · intro hx y hy
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
    simpa [mul_comm] using hx a ha

theorem inversePrime_mul_index (S : FIdeal K) (hS : S ≠ 0)
    (r : FinitePlace.Prime K) :
    inclusionIndex (fractionalIdealCarrier S)
      (fractionalIdealCarrier ((r.asIdeal : FIdeal K)⁻¹ * S)) =
        Nat.card (FinitePlace.Residue r) := by
  let R : FIdeal K := r.asIdeal
  have hr : R ≠ 0 := by simpa [R] using r.ne_bot
  have hrle : R ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hle : S ≤ R⁻¹ * S := by
    intro x hx
    apply (mem_inversePrime_mul S r x).mpr
    intro a _ha
    simpa [Algebra.smul_def] using S.coeToSubmodule.smul_mem a hx
  have heq : (R⁻¹ * S) * R = (1 : FIdeal K) * S := by
    rw [mul_right_comm, inv_mul_cancel₀ hr, one_mul]
  let e := FractionalIdeal.quotientEquiv (R⁻¹ * S) S 1 R heq hle hrle hr
    (mul_ne_zero (inv_ne_zero hr) hS)
  change Nat.card ((R⁻¹ * S) ⧸ S.coeToSubmodule.comap
    (R⁻¹ * S).coeToSubmodule.subtype) = _
  exact Nat.card_congr (e.trans (quotientOneEquiv r)).toEquiv

theorem primeColon_eq_inverse_mul (S : FIdeal K) (r : FinitePlace.Prime K) :
    (⨅ a : {a : 𝓞 K // a ∈ r.asIdeal},
      S.coeToSubmodule.comap (LinearMap.mulLeft (𝓞 K) (a.val : K))) =
        ((r.asIdeal : FIdeal K)⁻¹ * S).coeToSubmodule := by
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply]
  constructor
  · intro hx
    apply (mem_inversePrime_mul S r x).mpr
    intro a ha
    exact hx ⟨a, ha⟩
  · intro hx a
    exact (mem_inversePrime_mul S r x).mp hx a.val a.property

theorem primeColon_index (S : FIdeal K) (hS : S ≠ 0) (r : FinitePlace.Prime K) :
    inclusionIndex (fractionalIdealCarrier S)
      ((⨅ a : {a : 𝓞 K // a ∈ r.asIdeal},
        S.coeToSubmodule.comap (LinearMap.mulLeft (𝓞 K) (a.val : K))).restrictScalars ℤ) =
          Nat.card (FinitePlace.Residue r) := by
  rw [primeColon_eq_inverse_mul]
  exact inversePrime_mul_index S hS r

end SICLean.L5.SplitPrimeLatticeAux
