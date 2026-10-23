import SICLean.L5.SplitGroupRing
import SICLean.L5.LocalLemmaOne
import SICLean.L5.SplitUniformDirectionAux

set_option autoImplicit false

/-!
# From one direction on each coset to one direction everywhere

[RW-rec, p. 12] especially the second use of Lemma 1(iii) on the literal translation
quotient is the source. Its finite Fourier inputs are [RW26, p. 3, p. 18, (6), (36)].
These generic statements reuse `LocalLemmaOne`. Constant cosets are retained. No choice
depending on a coset is promoted to a uniform choice without the explicit
no-opposite-cosets step.
-/

noncomputable section

namespace SICLean.L5.SplitUniformDirection

open LocalFourierSetup FiniteCosetMoments

variable {G : Type*} [AddCommGroup G]

abbrev Coordinates (p : ℕ) := (ZMod p × ZMod p) ≃+ LocalFourierSetup.pTorsion p (G := G)

def coordinate {p : ℕ} (c : Coordinates (G := G) p) (u w : ZMod p) : G :=
  (c (u, w)).val

def AlongFirst {k : Type*} {p : ℕ} (g : G → k) (c : Coordinates (G := G) p)
    (x : G) : Prop :=
  ∀ u w t : ZMod p, g (x + coordinate c (u + t) w) = g (x + coordinate c u w)

def AlongSecond {k : Type*} {p : ℕ} (g : G → k) (c : Coordinates (G := G) p)
    (x : G) : Prop :=
  ∀ u w t : ZMod p, g (x + coordinate c u (w + t)) = g (x + coordinate c u w)

def ConstantCoset {k : Type*} {p : ℕ} (g : G → k) (c : Coordinates (G := G) p)
    (x : G) : Prop :=
  ∀ u w : ZMod p, g (x + coordinate c u w) = g x

/-- [RW-rec]: the generators used by Lemma 6 are the two coordinate axes. -/
theorem coordinate_basis {p : ℕ} [Fact p.Prime] [Fintype G]
    (c : Coordinates (G := G) p) :
    SplitGroupRing.IsPTorsionBasis p (coordinate c 1 0) (coordinate c 0 1) := by
  let φ : (ZMod p × ZMod p) →+ G :=
    (LocalFourierSetup.pTorsion p).subtype.comp c.toAddMonoidHom
  have hinj : Function.Injective φ := fun _ _ h => c.injective (Subtype.ext h)
  have hzero : coordinate c 0 0 = 0 := congrArg Subtype.val c.map_zero
  have hsmul1 (n : ℤ) : n • coordinate c 1 0 = coordinate c n 0 := by
    change n • φ (1, 0) = φ (n, 0)
    rw [← map_zsmul]
    congr 1
    ext <;> simp [zsmul_eq_mul]
  have hsmul2 (n : ℤ) : n • coordinate c 0 1 = coordinate c 0 n := by
    change n • φ (0, 1) = φ (0, n)
    rw [← map_zsmul]
    congr 1
    ext <;> simp [zsmul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hh : ((1, 0) : ZMod p × ZMod p) = (0, 0) :=
      hinj (h.trans hzero.symm)
    exact one_ne_zero (congrArg Prod.fst hh)
  · intro h
    have hh : ((0, 1) : ZMod p × ZMod p) = (0, 0) :=
      hinj (h.trans hzero.symm)
    exact one_ne_zero (congrArg Prod.snd hh)
  · apply AddSubgroup.disjoint_def.mpr
    intro y hy hz
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    have hh : (((n : ZMod p), 0) : ZMod p × ZMod p) = (0, (m : ZMod p)) := by
      apply hinj
      change coordinate c n 0 = coordinate c 0 m
      rw [← hsmul1, ← hsmul2, hn, hm]
    have hn0 : (n : ZMod p) = 0 := congrArg Prod.fst hh
    rw [← hn, hsmul1, hn0, hzero]
  · apply le_antisymm
    · exact sup_le (AddSubgroup.zmultiples_le.mpr (c (1, 0)).property)
        (AddSubgroup.zmultiples_le.mpr (c (0, 1)).property)
    · intro y hy
      let z := c.symm ⟨y, hy⟩
      have hz : coordinate c z.1 z.2 = y :=
        congrArg Subtype.val (c.apply_symm_apply ⟨y, hy⟩)
      have hadd : coordinate c z.1 z.2 = coordinate c z.1 0 + coordinate c 0 z.2 := by
        change φ (z.1, z.2) = φ (z.1, 0) + φ (0, z.2)
        rw [← map_add]
        simp
      rw [← hz, hadd]
      apply AddSubgroup.add_mem_sup
      · exact AddSubgroup.mem_zmultiples_iff.mpr
          ⟨(z.1.val : ℤ), by
            simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
              (hsmul1 (z.1.val : ℤ))⟩
      · exact AddSubgroup.mem_zmultiples_iff.mpr
          ⟨(z.2.val : ℤ), by
            simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
              (hsmul2 (z.2.val : ℤ))⟩

/-- [RW-rec]: transport the chosen split axes to the affine coordinates of the existing local Lemma
1, rather than changing its chart definition. -/
theorem adapted_coordinates {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    {C : Type*} [AddCommGroup C] [Fintype C] (hC : Nat.Coprime p (Fintype.card C))
    (e : (Point p s 2 × C) ≃+ G) (c : Coordinates (G := G) p) :
    ∃ a : AffineCoordinates p 2, ∀ u w : ZMod p,
      e (topDigit p s 2 (a ![u, w]), 0) = coordinate c u w := by
  exact SplitUniformDirectionAux.adapted_coordinates hs hC e c

/-- [RW-rec]: the explicit separated product on every coset. -/
theorem factorization_of_mixed {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
    (g : G → kˣ) (c : Coordinates (G := G) p)
    (hmix : ∀ x : G,
      g (x + coordinate c 1 0 + coordinate c 0 1) * g x =
        g (x + coordinate c 1 0) * g (x + coordinate c 0 1)) :
    ∀ (x : G) (u w : ZMod p),
      g (x + coordinate c u w) =
        g (x + coordinate c u 0) * g (x + coordinate c 0 w) / g x := by
  intro x u w
  let φ : (ZMod p × ZMod p) →+ G :=
    (LocalFourierSetup.pTorsion p).subtype.comp c.toAddMonoidHom
  have hφ (u w : ZMod p) : φ (u, w) = coordinate c u w := rfl
  let g' : ZMod p × ZMod p → kˣ := fun z => g (x + φ z)
  have hmix' : ∀ z : ZMod p × ZMod p,
      g' (z + (1, 0) + (0, 1)) * g' z = g' (z + (1, 0)) * g' (z + (0, 1)) := by
    intro z
    dsimp only [g']
    simp only [map_add]
    simpa only [hφ, add_assoc] using hmix (x + φ z)
  have h := SplitGroupRing.coordinate_factorization g'
    (1, 0) (0, 1) hmix' 0 u.val w.val
  simpa [g', φ, coordinate, nsmul_eq_mul] using h

variable {L : Type*} [Field L] [CharZero L] [Fintype G]
variable {p s : ℕ} [Fact p.Prime]
variable {C : Type*} [AddCommGroup C] [Fintype C]
variable (v : AddValuation L (WithTop ℝ))

/-- [RW-rec]: only a single selected coset is considered here. -/
theorem local_direction (hp : v (p : L) = 1) (hodd : p ≠ 2) (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s 2 × C) ≃+ G)
    (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B)
    (r0 : L) (hr0 : r0 ^ 2 = (Fintype.card G : L))
    (f : G → L) (hu : UnitValued v f)
    (hF : Integral v (fourier B r0 f))
    (hFi : Integral v (fourier B r0 (fun x => (f x)⁻¹)))
    (c : Coordinates (G := G) p) (x : G) (A D : ZMod p → Residue v)
    (hfactor : ∀ u w, reduce v (f (x + coordinate c u w)) = A u * D w) :
    AlongFirst (reduction v f) c x ∨ AlongSecond (reduction v f) c x := by
  obtain ⟨a, ha⟩ := adapted_coordinates hs hC e c
  have hchart (u w : ZMod p) :
      planeRestriction e v f x a (u, w) = reduce v (f (x + coordinate c u w)) := by
    simp only [planeRestriction, cosetChart, ha]
  have hfactor' : ∀ u : ZMod p × ZMod p,
      planeRestriction e v f x a u = A u.1 * D u.2 := by
    rintro ⟨u, w⟩
    rw [hchart, hfactor]
  have h := LocalLemmaOne.lemma1_iii_coordinate_invariance v hp hodd hs hC B hB hnd
    r0 hr0 f hF e hu hFi x a A D hfactor'
  simpa only [AlongFirst, AlongSecond, reduction, hchart] using h

/-- [RW-rec]: a constant coset admits both directions; it is not discarded. -/
theorem constant_iff_both {k : Type*} (g : G → k) (c : Coordinates (G := G) p) (x : G) :
    ConstantCoset g c x ↔ AlongFirst g c x ∧ AlongSecond g c x := by
  have hzero : coordinate c 0 0 = 0 := by
    exact congrArg Subtype.val c.map_zero
  constructor
  · intro h
    exact ⟨fun u w t => (h (u + t) w).trans (h u w).symm,
      fun u w t => (h u (w + t)).trans (h u w).symm⟩
  · rintro ⟨hfirst, hsecond⟩ u w
    calc
      g (x + coordinate c u w) = g (x + coordinate c 0 w) := by
        simpa only [zero_add] using hfirst 0 w u
      _ = g (x + coordinate c 0 0) := by
        simpa only [zero_add] using hsecond 0 0 w
      _ = g x := by rw [hzero, add_zero]

/-- [RW-rec]: the quotient on a pair of opposite-direction cosets uses the actual shift h=x2-x1,
including its sign. -/
theorem opposite_ratio_factorization (f : G → L) (hu : UnitValued v f)
    (c : Coordinates (G := G) p) (x1 x2 : G)
    (h1 : AlongSecond (reduction v f) c x1) (h2 : AlongFirst (reduction v f) c x2) :
    ∀ u w : ZMod p,
      reduce v (LocalLemmaOne.translationRatio f (x2 - x1) (x1 + coordinate c u w)) =
        (reduce v (f (x1 + coordinate c u 0)))⁻¹ *
          reduce v (f (x2 + coordinate c 0 w)) := by
  intro u w
  have hden : reduce v (f (x1 + coordinate c u w)) =
      reduce v (f (x1 + coordinate c u 0)) := by
    simpa only [zero_add, reduction] using h1 u 0 w
  have hnum : reduce v (f (x2 + coordinate c u w)) =
      reduce v (f (x2 + coordinate c 0 w)) := by
    simpa only [zero_add, reduction] using h2 0 w u
  have hshift : x1 + coordinate c u w + (x2 - x1) = x2 + coordinate c u w := by
    abel
  unfold LocalLemmaOne.translationRatio
  rw [hshift, div_eq_mul_inv,
    reduce_mul v _ _ (by rw [hu])
      (by rw [AddValuation.map_inv, hu]; simp),
    reduce_inv v _ (hu _), hden, hnum, mul_comm]

/-- [RW-rec]: the two quotient factors remain nonconstant, since the original values are units.
Constancy of the reciprocal is not assumed. -/
theorem opposite_ratio_nonconstant (f : G → L) (hu : UnitValued v f)
    (c : Coordinates (G := G) p) (x1 x2 : G)
    (h1 : AlongSecond (reduction v f) c x1) (h2 : AlongFirst (reduction v f) c x2)
    (hn1 : ¬ ConstantCoset (reduction v f) c x1)
    (hn2 : ¬ ConstantCoset (reduction v f) c x2) :
    (∃ u w : ZMod p,
      (reduce v (f (x1 + coordinate c u 0)))⁻¹ ≠
        (reduce v (f (x1 + coordinate c w 0)))⁻¹) ∧
      (∃ u w : ZMod p,
        reduce v (f (x2 + coordinate c 0 u)) ≠ reduce v (f (x2 + coordinate c 0 w))) := by
  classical
  have hzero : coordinate c 0 0 = 0 :=
    congrArg Subtype.val c.map_zero
  constructor
  · by_contra h
    push Not at h
    apply hn1
    intro u w
    have haxis : reduce v (f (x1 + coordinate c u 0)) =
        reduce v (f (x1 + coordinate c 0 0)) := by
      exact inv_injective (h u 0)
    change reduce v (f (x1 + coordinate c u w)) = reduce v (f x1)
    calc
      _ = reduce v (f (x1 + coordinate c u 0)) := by
        simpa only [zero_add, reduction] using h1 u 0 w
      _ = reduce v (f x1) := by simpa only [hzero, add_zero] using haxis
  · by_contra h
    push Not at h
    apply hn2
    intro u w
    change reduce v (f (x2 + coordinate c u w)) = reduce v (f x2)
    calc
      _ = reduce v (f (x2 + coordinate c 0 w)) := by
        simpa only [zero_add, reduction] using h2 0 w u
      _ = reduce v (f x2) := by simpa only [hzero, add_zero] using h w 0

/-- [RW-rec]. A second Lemma 1(iii) call on R_h rules out two nonconstant cosets with opposite
surviving directions. -/
theorem no_opposite_nonconstant (hp : v (p : L) = 1) (hodd : p ≠ 2) (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s 2 × C) ≃+ G)
    (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B)
    (r0 : L) (hr0 : r0 ^ 2 = (Fintype.card G : L))
    (f : G → L) (hu : UnitValued v f)
    (hR : ∀ h, Integral v (fourier B r0 (LocalLemmaOne.translationRatio f h)))
    (hRi : ∀ h, Integral v (fourier B r0 (fun x => (LocalLemmaOne.translationRatio f h x)⁻¹)))
    (c : Coordinates (G := G) p) (x1 x2 : G)
    (h1 : AlongSecond (reduction v f) c x1) (h2 : AlongFirst (reduction v f) c x2)
    (hn1 : ¬ ConstantCoset (reduction v f) c x1)
    (hn2 : ¬ ConstantCoset (reduction v f) c x2) : False := by
  obtain ⟨a, ha⟩ := adapted_coordinates hs hC e c
  let R := LocalLemmaOne.translationRatio f (x2 - x1)
  let A : ZMod p → Residue v := fun u => (reduce v (f (x1 + coordinate c u 0)))⁻¹
  let D : ZMod p → Residue v := fun w => reduce v (f (x2 + coordinate c 0 w))
  have hfactor : ∀ u : ZMod p × ZMod p,
      planeRestriction e v R x1 a u = A u.1 * D u.2 := by
    intro u
    simp only [planeRestriction, cosetChart, ha]
    exact opposite_ratio_factorization v f hu c x1 x2 h1 h2 u.1 u.2
  obtain ⟨hA, hD⟩ := opposite_ratio_nonconstant v f hu c x1 x2 h1 h2 hn1 hn2
  have hRu : UnitValued v R := by
    intro t
    change v (f (t + (x2 - x1)) / f t) = 0
    rw [div_eq_mul_inv, AddValuation.map_mul, AddValuation.map_inv, hu, hu]
    simp
  exact LocalLemmaOne.lemma1_iii_no_two_nonconstant v hp hodd hs hC B hB hnd r0 hr0
    R (hR (x2 - x1)) e hRu (hRi (x2 - x1)) x1 a A D hfactor hA hD

/-- [RW-rec]: a nonconstant coset cannot admit both directions. -/
theorem nonconstant_direction_unique {k : Type*} (g : G → k)
    (c : Coordinates (G := G) p) (x : G) (hn : ¬ ConstantCoset g c x) :
    ¬ (AlongFirst g c x ∧ AlongSecond g c x) := by
  exact fun h => hn ((constant_iff_both g c x).mpr h)

/-- [RW-rec]: purely logical global choice, explicitly retaining the case where every coset is
constant. -/
theorem uniform_of_no_opposite {k : Type*} (g : G → k) (c : Coordinates (G := G) p)
    (hlocal : ∀ x, AlongFirst g c x ∨ AlongSecond g c x)
    (hno : ∀ x1 x2, AlongSecond g c x1 → AlongFirst g c x2 →
      ¬ ConstantCoset g c x1 → ¬ ConstantCoset g c x2 → False) :
    (∀ x, AlongFirst g c x) ∨ (∀ x, AlongSecond g c x) := by
  classical
  by_cases hfirst : ∀ x, AlongFirst g c x
  · exact Or.inl hfirst
  · right
    obtain ⟨x1, hx1⟩ := not_forall.mp hfirst
    have h1 := (hlocal x1).resolve_left hx1
    have hn1 : ¬ ConstantCoset g c x1 :=
      fun h => hx1 ((constant_iff_both g c x1).mp h).1
    intro x2
    by_cases h2 : AlongSecond g c x2
    · exact h2
    · have hfirst2 := (hlocal x2).resolve_right h2
      have hn2 : ¬ ConstantCoset g c x2 :=
        fun h => h2 ((constant_iff_both g c x2).mp h).2
      exact (hno x1 x2 h1 hfirst2 hn1 hn2).elim

/-- [RW-rec]: generic Fourier statement. The disjunction is outside ∀x. -/
theorem uniform_direction (hp : v (p : L) = 1) (hodd : p ≠ 2) (hs : 1 ≤ s)
    (hC : Nat.Coprime p (Fintype.card C)) (e : (Point p s 2 × C) ≃+ G)
    (B : G → G → L) (hB : IsBicharacter B) (hnd : Nondegenerate B)
    (r0 : L) (hr0 : r0 ^ 2 = (Fintype.card G : L))
    (f : G → L) (hu : UnitValued v f)
    (hF : Integral v (fourier B r0 f))
    (hFi : Integral v (fourier B r0 (fun x => (f x)⁻¹)))
    (hR : ∀ h, Integral v (fourier B r0 (LocalLemmaOne.translationRatio f h)))
    (hRi : ∀ h, Integral v (fourier B r0 (fun x => (LocalLemmaOne.translationRatio f h x)⁻¹)))
    (c : Coordinates (G := G) p)
    (hfactor : ∀ x, ∃ A D : ZMod p → Residue v, ∀ u w,
      reduce v (f (x + coordinate c u w)) = A u * D w) :
    (∀ x, AlongFirst (reduction v f) c x) ∨
      (∀ x, AlongSecond (reduction v f) c x) := by
  apply uniform_of_no_opposite (reduction v f) c
  · intro x
    obtain ⟨A, D, hAD⟩ := hfactor x
    exact local_direction v hp hodd hs hC e B hB hnd r0 hr0 f hu hF hFi c x A D hAD
  · intro x1 x2 h1 h2 hn1 hn2
    exact no_opposite_nonconstant v hp hodd hs hC e B hB hnd r0 hr0
      f hu hR hRi c x1 x2 h1 h2 hn1 hn2

/-- [RW-rec]: translation form, using the same chosen axis at every point, rather than one choice
per representative. -/
theorem uniform_translation (f : G → L) (c : Coordinates (G := G) p)
    (h : (∀ x, AlongFirst (reduction v f) c x) ∨
      (∀ x, AlongSecond (reduction v f) c x)) :
    (∀ (x : G) (u : ZMod p), reduce v (f (x + coordinate c u 0)) = reduce v (f x)) ∨
      (∀ (x : G) (u : ZMod p), reduce v (f (x + coordinate c 0 u)) = reduce v (f x)) := by
  have hzero : coordinate c 0 0 = 0 :=
    congrArg Subtype.val c.map_zero
  rcases h with hfirst | hsecond
  · left
    intro x u
    simpa only [zero_add, hzero, add_zero, reduction] using hfirst x 0 0 u
  · right
    intro x u
    simpa only [zero_add, hzero, add_zero, reduction] using hsecond x 0 0 u


end SICLean.L5.SplitUniformDirection
