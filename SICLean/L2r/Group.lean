import SICLean.L2r.Arithmetic

set_option autoImplicit false

/-!
# The ideal model of Gγ in rectangular coordinates

G = Z/d × Z/(d(n-4)) with n = `level d r`, and z(x,y)=x/d+y/(d(u-1)). Since
η-1=d u^m(u-1), its image is exactly (η-1)⁻¹Z[u]/Z[u].
No group identification, automorphism, or embedding is an input.
-/

noncomputable section

namespace SICLean.L2r

abbrev Index (d : ℕ) := ZMod d × ZMod d
abbrev Values (d : ℕ) := Index d → ℂ
abbrev G (d r : ℕ) := ZMod d × ZMod (longModulus d r)

instance admissibleGFintype (d r : ℕ) [Fact (Admissible d r)] : Fintype (G d r) :=
  letI : NeZero d := admissibleDimensionNeZero d r
  inferInstanceAs (Fintype (ZMod d × ZMod (longModulus d r)))
abbrev RationalTorus := L2b.RationalTorus
abbrev QuadraticCoordinates := L2b.QuadraticCoordinates

def coordinate (d r : ℕ) (x y : ℤ) : G d r := (x, y)
def label (d : ℕ) (p : ℤ × ℤ) : Index d := (p.1, p.2)
def lift {d : ℕ} (p : Index d) : ℤ × ℤ := (p.1.val, p.2.val)

def symplectic (p q : ℤ × ℤ) : ℤ := -p.1 * q.2 + p.2 * q.1

def shiftedAlpha (d r : ℕ) (q : ℤ × ℤ) : ℤ × ℤ :=
  ((shift d r + (ell d r : ℤ)) * q.1 - q.2, q.1 + shift d r * q.2)

def pointLift (d r : ℕ) (x y : ℤ) : QuadraticCoordinates :=
  ((y : ℚ) / longModulus d r,
    ((cofactor d r : ℚ) * x - ((ell d r : ℚ) - 1) * y) / longModulus d r)

/-- Row coordinates in the oriented basis (u,1). -/
def actOnCoordinates (M : Matrix (Fin 2) (Fin 2) ℤ)
    (z : QuadraticCoordinates) : QuadraticCoordinates :=
  (z.1 * (M 0 0 : ℚ) + z.2 * (M 1 0 : ℚ),
    z.1 * (M 0 1 : ℚ) + z.2 * (M 1 1 : ℚ))

def rowAction (M : Matrix (Fin 2) (Fin 2) ℤ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 * M 0 0 + z.2 * M 1 0, z.1 * M 0 1 + z.2 * M 1 1)

def rowActionHom (M : Matrix (Fin 2) (Fin 2) ℤ) : (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun := rowAction M
  map_zero' := by simp [rowAction]
  map_add' := by
    intro a b
    ext <;> simp [rowAction] <;> ring

def rowLattice (M : Matrix (Fin 2) (Fin 2) ℤ) : AddSubgroup (ℤ × ℤ) :=
  ({ toFun := rowAction M, map_zero' := by exact (rowActionHom M).map_zero,
      map_add' := by exact (rowActionHom M).map_add } :
    (ℤ × ℤ) →+ (ℤ × ℤ)).range

private lemma hcoZ {d r : ℕ} (h : Admissible d r) :
    (cofactor d r : ℤ) = (ell d r : ℤ) - 2 := by
  have hlev : 5 ≤ level d r := level_ge_five h
  have h1 : (cofactor d r : ℤ) = (level d r : ℤ) - 4 := by
    simp only [cofactor]
    exact Nat.cast_sub (by omega)
  have h2 : (ell d r : ℤ) = (level d r : ℤ) - 2 := by
    simp only [ell]
    exact Nat.cast_sub (by omega)
  omega

private lemma hlongZ (d r : ℕ) :
    (longModulus d r : ℤ) = (d : ℤ) * (cofactor d r : ℤ) := by
  simp only [longModulus, Nat.cast_mul]

/-- The row quotient of [RW26]. -/
abbrev RWGroup (d r : ℕ) := (ℤ × ℤ) ⧸ rowLattice (gamma d r - 1)

def rwIndexMatrix (d r : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-gap d r, ((ell d r : ℤ) - 1) * ((d : ℤ) - r) - r;
    (d : ℤ) - r, (r : ℤ) - (ell d r : ℤ) * ((d : ℤ) - r)]

def rwNumerator (d r : ℕ) (x y : ℤ) : ℤ × ℤ :=
  rowAction (rwIndexMatrix d r) (x, y)

theorem rwIndexMatrix_det {d r : ℕ} (h : Admissible d r) :
    (rwIndexMatrix d r).det = 1 := by
  have hcon := principal_conic h
  simp only [rwIndexMatrix, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, gap]
  nlinarith

private lemma rowAction_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    rowAction (M * N) v = rowAction N (rowAction M v) := by
  ext <;> simp [rowAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma rowAction_surjective (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.det = 1) : Function.Surjective (rowAction M) := by
  intro v
  refine ⟨rowAction M.adjugate v, ?_⟩
  rw [← rowAction_mul, Matrix.adjugate_mul, hM, one_smul]
  simp [rowAction]

private lemma rowLattice_mul (M N : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.det = 1) : rowLattice (M * N) = rowLattice N := by
  ext v
  change (∃ w, rowAction (M * N) w = v) ↔ ∃ w, rowAction N w = v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨rowAction M w, (rowAction_mul M N w).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := rowAction_surjective M hM w
    exact ⟨z, by rw [rowAction_mul, hz]⟩

private lemma rowLattice_mem_iff {d r : ℕ} (h : Admissible d r) (v : ℤ × ℤ) :
    v ∈ rowLattice (gamma d r - 1) ↔
      (d : ℤ) ∣ v.1 ∧ (longModulus d r : ℤ) ∣ v.1 + v.2 := by
  rw [gamma_sub_one h, ← Matrix.mul_smul,
    rowLattice_mul _ _ (gamma_arithmetic h).2.1]
  have hrow (k : ℤ × ℤ) :
      rowAction ((d : ℤ) • (alpha d r - 1)) k =
        ((d : ℤ) * (((ell d r : ℤ) - 1) * k.1 + k.2),
          (longModulus d r : ℤ) * k.1 -
            (d : ℤ) * (((ell d r : ℤ) - 1) * k.1 + k.2)) := by
    ext <;> simp [rowAction, alpha, Matrix.sub_apply, Matrix.smul_apply,
      hlongZ, hcoZ h] <;> ring
  change (∃ k, rowAction ((d : ℤ) • (alpha d r - 1)) k = v) ↔ _
  constructor
  · rintro ⟨k, rfl⟩
    rw [hrow]
    exact ⟨⟨((ell d r : ℤ) - 1) * k.1 + k.2, rfl⟩, ⟨k.1, by simp⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨(y, x - ((ell d r : ℤ) - 1) * y), ?_⟩
    rw [hrow]
    ext <;> dsimp
    · linear_combination -hx
    · linear_combination hx - hy

private lemma rwNumerator_mem_iff {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    rwNumerator d r x y ∈ rowLattice (gamma d r - 1) ↔
      (d : ℤ) ∣ x ∧ (longModulus d r : ℤ) ∣ y := by
  rw [rowLattice_mem_iff h]
  have hco := hcoZ h
  have hlong := hlongZ d r
  have hnum : rwNumerator d r x y =
      (-gap d r * x + ((d : ℤ) - r) * y,
        (((ell d r : ℤ) - 1) * ((d : ℤ) - r) - r) * x +
          ((r : ℤ) - (ell d r : ℤ) * ((d : ℤ) - r)) * y) := by
    ext <;> simp [rwNumerator, rwIndexMatrix, rowAction] <;> ring
  have hinv : rowAction (rwIndexMatrix d r).adjugate (rwNumerator d r x y) = (x, y) := by
    rw [rwNumerator, ← rowAction_mul, Matrix.mul_adjugate,
      rwIndexMatrix_det h, one_smul]
    simp [rowAction]
  have hinv1 : x =
      ((r : ℤ) - ((ell d r : ℤ) - 1) * ((d : ℤ) - r)) *
          (rwNumerator d r x y).1 - ((d : ℤ) - r) *
          ((rwNumerator d r x y).1 + (rwNumerator d r x y).2) := by
    have hh := congrArg Prod.fst hinv
    simp [rowAction, rwIndexMatrix, Matrix.adjugate_fin_two] at hh
    linear_combination -hh
  have hinv2 : y =
      -(cofactor d r : ℤ) * ((d : ℤ) - r) * (rwNumerator d r x y).1 -
        gap d r * ((rwNumerator d r x y).1 + (rwNumerator d r x y).2) := by
    have hh := congrArg Prod.snd hinv
    simp [rowAction, rwIndexMatrix, Matrix.adjugate_fin_two] at hh
    rw [hco]
    simp only [gap] at hh ⊢
    linear_combination -hh
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨t, ht⟩⟩
    constructor
    · refine ⟨((r : ℤ) - ((ell d r : ℤ) - 1) * ((d : ℤ) - r)) * k -
        ((d : ℤ) - r) * (cofactor d r : ℤ) * t, ?_⟩
      rw [hinv1, ht, hk, hlong]
      ring
    · refine ⟨-((d : ℤ) - r) * k - gap d r * t, ?_⟩
      rw [hinv2, ht, hk, hlong]
      ring
  · rintro ⟨⟨k, rfl⟩, ⟨t, rfl⟩⟩
    rw [hnum]
    dsimp
    constructor
    · refine ⟨-gap d r * k + ((d : ℤ) - r) * (cofactor d r : ℤ) * t, ?_⟩
      rw [hlong]
      ring
    · refine ⟨((d : ℤ) - r) * k +
        ((r : ℤ) - ((ell d r : ℤ) - 1) * ((d : ℤ) - r)) * t, ?_⟩
      rw [hlong, hco]
      simp only [gap]
      ring

private lemma rwNumerator_sub (d r : ℕ) (x y X Y : ℤ) :
    rwNumerator d r (x - X) (y - Y) =
      rwNumerator d r x y - rwNumerator d r X Y := by
  exact (rowActionHom (rwIndexMatrix d r)).map_sub (x, y) (X, Y)

def rwIndexMap (d r : ℕ) [Fact (Admissible d r)] : G d r →+ RWGroup d r where
  toFun g := QuotientAddGroup.mk (rwNumerator d r g.1.val g.2.val)
  map_zero' := by
    letI : NeZero d := admissibleDimensionNeZero d r
    letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
    change QuotientAddGroup.mk (rwNumerator d r (0 : ZMod d).val
      (0 : ZMod (longModulus d r)).val) = 0
    simp [rwNumerator, rowAction]
    exact (rowLattice (gamma d r - 1)).zero_mem
  map_add' := by
    intro g k
    letI : NeZero d := admissibleDimensionNeZero d r
    letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
    change QuotientAddGroup.mk (rwNumerator d r (g + k).1.val (g + k).2.val) =
      QuotientAddGroup.mk (rwNumerator d r g.1.val g.2.val) +
        QuotientAddGroup.mk (rwNumerator d r k.1.val k.2.val)
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem]
    have hadd : rwNumerator d r g.1.val g.2.val + rwNumerator d r k.1.val k.2.val =
        rwNumerator d r ((g.1.val : ℤ) + k.1.val) ((g.2.val : ℤ) + k.2.val) :=
      ((rowActionHom (rwIndexMatrix d r)).map_add _ _).symm
    rw [hadd, ← rwNumerator_sub, rwNumerator_mem_iff (Fact.out : Admissible d r)]
    constructor
    · refine ⟨-(((g.1.val : ℤ) + k.1.val) / d), ?_⟩
      have hval : ((g + k).1.val : ℤ) = ((g.1.val : ℤ) + k.1.val) % d := by
        exact_mod_cast ZMod.val_add g.1 k.1
      rw [hval]
      linear_combination Int.mul_ediv_add_emod ((g.1.val : ℤ) + k.1.val) (d : ℤ)
    · refine ⟨-(((g.2.val : ℤ) + k.2.val) / longModulus d r), ?_⟩
      have hval : ((g + k).2.val : ℤ) =
          ((g.2.val : ℤ) + k.2.val) % longModulus d r := by
        exact_mod_cast ZMod.val_add g.2 k.2
      rw [hval]
      linear_combination Int.mul_ediv_add_emod ((g.2.val : ℤ) + k.2.val)
        (longModulus d r : ℤ)

def actOnCoordinatesHom (M : Matrix (Fin 2) (Fin 2) ℤ) :
    QuadraticCoordinates →+ QuadraticCoordinates where
  toFun := actOnCoordinates M
  map_zero' := by simp [actOnCoordinates]
  map_add' := by
    intro a b
    ext <;> simp [actOnCoordinates] <;> ring

private lemma actOnCoordinates_preserves (M : Matrix (Fin 2) (Fin 2) ℤ) :
    L2b.integerLattice ≤ L2b.integerLattice.comap (actOnCoordinatesHom M) := by
  intro z hz
  rw [AddSubgroup.mem_comap]
  obtain ⟨k, rfl⟩ := AddMonoidHom.mem_range.mp hz
  refine AddMonoidHom.mem_range.mpr
    ⟨((k.1 * M 0 0 + k.2 * M 1 0), (k.1 * M 0 1 + k.2 * M 1 1)), ?_⟩
  ext <;> simp [L2b.integerCoordinates, actOnCoordinatesHom, actOnCoordinates]

def torusAction (M : Matrix (Fin 2) (Fin 2) ℤ) : RationalTorus →+ RationalTorus where
  toFun := QuotientAddGroup.map L2b.integerLattice L2b.integerLattice
    { toFun := actOnCoordinates M,
      map_zero' := by exact (actOnCoordinatesHom M).map_zero,
      map_add' := by exact (actOnCoordinatesHom M).map_add }
    (by exact actOnCoordinates_preserves M)
  map_zero' := map_zero _
  map_add' := by
    intro a b
    exact map_add _ a b

/-- Explicit admissibility binder: this is not an automorphism for invalid parameters. -/
def epsilonOnTorus (d r : ℕ) [Fact (Admissible d r)] : RationalTorus →+ RationalTorus :=
  torusAction (alpha d r)

def fixedTorus (d r : ℕ) [Fact (Admissible d r)] : AddSubgroup RationalTorus :=
  (torusAction (gamma d r) - AddMonoidHom.id RationalTorus).ker

private lemma pointLift_mul_one {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    ((longModulus d r : ℚ)) * (pointLift d r x y).1 = (y : ℚ) := by
  have hN : ((longModulus d r : ℚ)) ≠ 0 := by
    have : 0 < longModulus d r := Nat.pos_of_ne_zero (by
      have hd : 2 * r + 1 < d := h.main_range
      have hco : 0 < cofactor d r := by
        have := level_ge_five h
        simp only [cofactor]; omega
      exact Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast (ne_of_gt this)
  simp only [pointLift]
  rw [mul_comm, div_mul_cancel₀ _ hN]

private lemma pointLift_mul_two {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    ((longModulus d r : ℚ)) * (pointLift d r x y).2 =
      (cofactor d r : ℚ) * (x : ℚ) - ((ell d r : ℚ) - 1) * (y : ℚ) := by
  have hN : ((longModulus d r : ℚ)) ≠ 0 := by
    have : 0 < longModulus d r := Nat.pos_of_ne_zero (by
      have hd : 2 * r + 1 < d := h.main_range
      have hco : 0 < cofactor d r := by
        have := level_ge_five h
        simp only [cofactor]; omega
      exact Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast (ne_of_gt this)
  simp only [pointLift]
  rw [mul_comm, div_mul_cancel₀ _ hN]

private theorem nat_eq_of_modEq_lt (n a b : ℕ) (h : a ≡ b [MOD n]) (ha : a < n) (hb : b < n) :
    a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · rw [Nat.modEq_iff_dvd' (Nat.le_of_lt hab)] at h
    obtain ⟨k, hk⟩ := h
    match k with
    | 0 => omega
    | k + 1 =>
      have hge : n ≤ n * (k + 1) := Nat.le_mul_of_pos_right n (by omega)
      omega
  · exact hab
  · have h2 := h.symm
    rw [Nat.modEq_iff_dvd' (Nat.le_of_lt hab)] at h2
    obtain ⟨k, hk⟩ := h2
    match k with
    | 0 => omega
    | k + 1 =>
      have hge : n ≤ n * (k + 1) := Nat.le_mul_of_pos_right n (by omega)
      omega

private theorem zmod_nsmul_eq_zero_iff (M N : ℕ) (x : ℤ) :
    M • ((x : ZMod N)) = 0 ↔ ((N : ℤ)) ∣ ((M : ℤ)) * x := by
  constructor
  · intro h
    have eM : ((M : ZMod N)) = ((((M : ℤ)) : ZMod N)) := by push_cast; rfl
    rw [nsmul_eq_mul, eM, ← Int.cast_mul] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  · intro h
    have key : ((((M : ℤ) * x : ℤ)) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    have eM : ((M : ZMod N)) = ((((M : ℤ)) : ZMod N)) := by push_cast; rfl
    rw [nsmul_eq_mul, eM, ← Int.cast_mul]
    exact key

private lemma coordinate_eq_of_dvd {d r : ℕ} {a a' b b' : ℤ}
    (ha : ((d : ℤ)) ∣ a - a') (hb : ((longModulus d r : ℤ)) ∣ b - b') :
    coordinate d r a b = coordinate d r a' b' := by
  have ha' : ((d : ℤ)) ∣ a' - a := by rw [← neg_sub]; exact Int.dvd_neg.mpr ha
  have hb' : ((longModulus d r : ℤ)) ∣ b' - b := by rw [← neg_sub]; exact Int.dvd_neg.mpr hb
  simp only [coordinate, Prod.ext_iff]
  exact ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub a a' d).mpr ha',
    (ZMod.intCast_eq_intCast_iff_dvd_sub b b' (longModulus d r)).mpr hb'⟩

private lemma coordinate_val (d r : ℕ) [Fact (Admissible d r)] (g : G d r) :
    coordinate d r (g.1.val : ℤ) (g.2.val : ℤ) = g := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  refine Prod.ext ?_ ?_
  · simp only [coordinate]
    push_cast
    exact ZMod.natCast_zmod_val g.1
  · simp only [coordinate]
    push_cast
    exact ZMod.natCast_zmod_val g.2

private lemma coordinate_add (d r : ℕ) [Fact (Admissible d r)] (a b c e : ℤ) :
    coordinate d r a b + coordinate d r c e = coordinate d r (a + c) (b + e) := by
  simp only [coordinate, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  constructor <;> push_cast <;> ring

private lemma coordinate_sub (d r : ℕ) [Fact (Admissible d r)] (a b c e : ℤ) :
    coordinate d r a b - coordinate d r c e = coordinate d r (a - c) (b - e) := by
  simp only [coordinate, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
  constructor <;> push_cast <;> ring

private lemma coordinate_fst_val (d r : ℕ) [Fact (Admissible d r)] (a b : ℤ) :
    ((coordinate d r a b).1.val : ℤ) = a % (d : ℤ) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  simp only [coordinate]
  exact ZMod.val_intCast a

private lemma coordinate_snd_val (d r : ℕ) [Fact (Admissible d r)] (a b : ℤ) :
    ((coordinate d r a b).2.val : ℤ) = b % (longModulus d r : ℤ) := by
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  simp only [coordinate]
  exact ZMod.val_intCast b

def torusPoint (d r : ℕ) [Fact (Admissible d r)] : G d r →+ RationalTorus where
  toFun g := QuotientAddGroup.mk (pointLift d r g.1.val g.2.val)
  map_zero' := by
    show QuotientAddGroup.mk (pointLift d r (0 : ZMod d).val (0 : ZMod (longModulus d r)).val) = 0
    simp only [pointLift, ZMod.val_zero]
    push_cast
    norm_num
    exact (L2b.integerLattice).zero_mem
  map_add' := by
    intro g₁ g₂
    letI : NeZero d := admissibleDimensionNeZero d r
    letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
    have h := (Fact.out : Admissible d r)
    have hlong := hlongZ d r
    have hN : ((longModulus d r : ℚ)) ≠ 0 := by
      have : 0 < longModulus d r := Nat.pos_of_ne_zero (NeZero.ne _)
      exact_mod_cast (ne_of_gt this)
    set x₁ : ℤ := (g₁.1.val : ℤ) with hx₁
    set x₂ : ℤ := (g₂.1.val : ℤ) with hx₂
    set y₁ : ℤ := (g₁.2.val : ℤ) with hy₁
    set y₂ : ℤ := (g₂.2.val : ℤ) with hy₂
    set rx : ℤ := ((g₁ + g₂).1.val : ℤ) with hrx
    set ry : ℤ := ((g₁ + g₂).2.val : ℤ) with hry
    set qx : ℤ := (x₁ + x₂) / (d : ℤ) with hqx
    set qy : ℤ := (y₁ + y₂) / (longModulus d r : ℤ) with hqy
    have e1 : rx = (x₁ + x₂) % (d : ℤ) := by
      rw [hrx, hx₁, hx₂]
      rw [Prod.fst_add]
      exact_mod_cast ZMod.val_add g₁.1 g₂.1
    have e2 : ry = (y₁ + y₂) % (longModulus d r : ℤ) := by
      rw [hry, hy₁, hy₂]
      rw [Prod.snd_add]
      exact_mod_cast ZMod.val_add g₁.2 g₂.2
    have hA : (d : ℤ) * qx + rx = x₁ + x₂ := by
      rw [hqx, e1]
      exact Int.mul_ediv_add_emod _ _
    have hB : (longModulus d r : ℤ) * qy + ry = y₁ + y₂ := by
      rw [hqy, e2]
      exact Int.mul_ediv_add_emod _ _
    have hAq : ((d : ℚ)) * (qx : ℚ) + (rx : ℚ) = (x₁ : ℚ) + (x₂ : ℚ) := by exact_mod_cast hA
    have hBq : ((longModulus d r : ℚ)) * (qy : ℚ) + (ry : ℚ) = (y₁ : ℚ) + (y₂ : ℚ) := by
      exact_mod_cast hB
    have hlongQ : ((longModulus d r : ℚ)) = (d : ℚ) * (cofactor d r : ℚ) := by
      exact_mod_cast hlong
    have hp1 := pointLift_mul_one h
    have hp2 := pointLift_mul_two h
    change QuotientAddGroup.mk (pointLift d r ((g₁ + g₂).1.val) ((g₁ + g₂).2.val))
      = QuotientAddGroup.mk (pointLift d r g₁.1.val g₁.2.val) +
        QuotientAddGroup.mk (pointLift d r g₂.1.val g₂.2.val)
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem,
      L2b.integerLattice, AddMonoidHom.mem_range]
    refine ⟨(-qy, -qx + ((ell d r : ℤ) - 1) * qy), ?_⟩
    refine Prod.ext ?_ ?_
    · change ((-qy : ℤ) : ℚ) =
        (pointLift d r ((g₁ + g₂).1.val) ((g₁ + g₂).2.val)).1 -
          ((pointLift d r g₁.1.val g₁.2.val).1 +
            (pointLift d r g₂.1.val g₂.2.val).1)
      simp only [pointLift]
      field_simp [hN]
      push_cast
      linear_combination -hBq
    · change ((-qx + ((ell d r : ℤ) - 1) * qy : ℤ) : ℚ) =
        (pointLift d r ((g₁ + g₂).1.val) ((g₁ + g₂).2.val)).2 -
          ((pointLift d r g₁.1.val g₁.2.val).2 +
            (pointLift d r g₂.1.val g₂.2.val).2)
      simp only [pointLift]
      field_simp [hN]
      push_cast
      linear_combination -(cofactor d r : ℚ) * hAq + ((ell d r : ℚ) - 1) * hBq
        - (qx : ℚ) * hlongQ

private lemma epsAut_on_coordinate {d r : ℕ} [Fact (Admissible d r)] (x y : ℤ) :
    coordinate d r (((ell d r : ℤ) - 1) * ((coordinate d r x y).1.val : ℤ) +
        ((coordinate d r x y).2.val : ℤ))
        ((cofactor d r : ℤ) * ((coordinate d r x y).1.val : ℤ) +
          ((coordinate d r x y).2.val : ℤ))
      = coordinate d r (((ell d r : ℤ) - 1) * x + y) ((cofactor d r : ℤ) * x + y) := by
  have hlong := hlongZ d r
  have h1 := Int.mul_ediv_add_emod (x : ℤ) ((d : ℤ))
  have h2 := Int.mul_ediv_add_emod (y : ℤ) ((longModulus d r : ℤ))
  have hf := coordinate_fst_val d r x y
  have hs := coordinate_snd_val d r x y
  refine coordinate_eq_of_dvd (d := d) (r := r) ?_ ?_
  · refine ⟨-(((ell d r : ℤ) - 1) * (x / (d : ℤ))
      + (cofactor d r : ℤ) * (y / (longModulus d r : ℤ))), ?_⟩
    rw [hf, hs]
    linear_combination ((ell d r : ℤ) - 1) * h1 + h2
      - (y / (longModulus d r : ℤ)) * hlong
  · refine ⟨-((x / (d : ℤ)) + (y / (longModulus d r : ℤ))), ?_⟩
    rw [hf, hs]
    linear_combination (cofactor d r : ℤ) * h1 + h2
      + (x / (d : ℤ)) * hlong

private lemma epsAutInv_on_coordinate {d r : ℕ} [Fact (Admissible d r)] (x y : ℤ) :
    coordinate d r (((coordinate d r x y).1.val : ℤ) - ((coordinate d r x y).2.val : ℤ))
        (-(cofactor d r : ℤ) * ((coordinate d r x y).1.val : ℤ) +
          ((ell d r : ℤ) - 1) * ((coordinate d r x y).2.val : ℤ))
      = coordinate d r (x - y) (-(cofactor d r : ℤ) * x + ((ell d r : ℤ) - 1) * y) := by
  have hlong := hlongZ d r
  have h1 := Int.mul_ediv_add_emod (x : ℤ) ((d : ℤ))
  have h2 := Int.mul_ediv_add_emod (y : ℤ) ((longModulus d r : ℤ))
  have hf := coordinate_fst_val d r x y
  have hs := coordinate_snd_val d r x y
  refine coordinate_eq_of_dvd (d := d) (r := r) ?_ ?_
  · refine ⟨-((x / (d : ℤ)) - (cofactor d r : ℤ) * (y / (longModulus d r : ℤ))), ?_⟩
    rw [hf, hs]
    linear_combination h1 - h2 + (y / (longModulus d r : ℤ)) * hlong
  · refine ⟨(x / (d : ℤ)) - ((ell d r : ℤ) - 1) * (y / (longModulus d r : ℤ)), ?_⟩
    rw [hf, hs]
    linear_combination -(cofactor d r : ℤ) * h1 + ((ell d r : ℤ) - 1) * h2
      - (x / (d : ℤ)) * hlong

private lemma torusPoint_coordinate (d r : ℕ) [Fact (Admissible d r)] (x y : ℤ) :
    torusPoint d r (coordinate d r x y) = QuotientAddGroup.mk (pointLift d r x y) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  have h := (Fact.out : Admissible d r)
  have hlong := hlongZ d r
  have hN : ((longModulus d r : ℚ)) ≠ 0 := by
    have : 0 < longModulus d r := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast (ne_of_gt this)
  set qx : ℤ := x / (d : ℤ) with hqx
  set qy : ℤ := y / (longModulus d r : ℤ) with hqy
  have hA : (d : ℤ) * qx + x % (d : ℤ) = x := by
    rw [hqx]; exact Int.mul_ediv_add_emod x (d : ℤ)
  have hB : (longModulus d r : ℤ) * qy + y % (longModulus d r : ℤ) = y := by
    rw [hqy]; exact Int.mul_ediv_add_emod y (longModulus d r : ℤ)
  have hAq : ((d : ℚ)) * (qx : ℚ) + ((x % (d : ℤ) : ℤ) : ℚ) = (x : ℚ) := by exact_mod_cast hA
  have hBq : ((longModulus d r : ℚ)) * (qy : ℚ) +
      ((y % (longModulus d r : ℤ) : ℤ) : ℚ) = (y : ℚ) := by exact_mod_cast hB
  have hlongQ : ((longModulus d r : ℚ)) = (d : ℚ) * (cofactor d r : ℚ) := by
    exact_mod_cast hlong
  have hf := coordinate_fst_val d r x y
  have hs := coordinate_snd_val d r x y
  change QuotientAddGroup.mk (pointLift d r ((coordinate d r x y).1.val : ℤ)
    ((coordinate d r x y).2.val : ℤ)) = QuotientAddGroup.mk (pointLift d r x y)
  rw [QuotientAddGroup.eq_iff_sub_mem, L2b.integerLattice, AddMonoidHom.mem_range]
  refine ⟨(-qy, -qx + ((ell d r : ℤ) - 1) * qy), ?_⟩
  refine Prod.ext ?_ ?_
  · change ((-qy : ℤ) : ℚ) =
      (pointLift d r ((coordinate d r x y).1.val : ℤ) ((coordinate d r x y).2.val : ℤ)).1 -
        (pointLift d r x y).1
    rw [hf, hs]
    simp only [pointLift]
    field_simp [hN]
    push_cast
    linear_combination -hBq
  · change ((-qx + ((ell d r : ℤ) - 1) * qy : ℤ) : ℚ) =
      (pointLift d r ((coordinate d r x y).1.val : ℤ) ((coordinate d r x y).2.val : ℤ)).2 -
        (pointLift d r x y).2
    rw [hf, hs]
    simp only [pointLift]
    field_simp [hN]
    push_cast
    linear_combination -(cofactor d r : ℚ) * hAq + ((ell d r : ℚ) - 1) * hBq
      - (qx : ℚ) * hlongQ

def epsilonAut (d r : ℕ) [Fact (Admissible d r)] : G d r ≃+ G d r where
  toFun g := coordinate d r (((ell d r : ℤ) - 1) * g.1.val + g.2.val)
    ((cofactor d r : ℤ) * g.1.val + g.2.val)
  invFun g := coordinate d r ((g.1.val : ℤ) - g.2.val)
    (-(cofactor d r : ℤ) * g.1.val + ((ell d r : ℤ) - 1) * g.2.val)
  left_inv := by
    intro g
    rw [← coordinate_val d r g]
    have hco : (cofactor d r : ℤ) = (ell d r : ℤ) - 2 := hcoZ (Fact.out : Admissible d r)
    have hA : (fun g' : G d r => coordinate d r
        (((ell d r : ℤ) - 1) * g'.1.val + g'.2.val)
        ((cofactor d r : ℤ) * g'.1.val + g'.2.val))
        (coordinate d r ((g.1.val : ℤ)) ((g.2.val : ℤ)))
        = coordinate d r (((ell d r : ℤ) - 1) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          ((cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))) :=
      epsAut_on_coordinate ((g.1.val : ℤ)) ((g.2.val : ℤ))
    rw [hA]
    have hB : (fun g' : G d r => coordinate d r
        ((g'.1.val : ℤ) - g'.2.val)
        (-(cofactor d r : ℤ) * g'.1.val + ((ell d r : ℤ) - 1) * g'.2.val))
        (coordinate d r (((ell d r : ℤ) - 1) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          ((cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))))
        = coordinate d r
          ((((ell d r : ℤ) - 1) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))) -
            ((cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))))
          (-(cofactor d r : ℤ) * (((ell d r : ℤ) - 1) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))) +
            ((ell d r : ℤ) - 1) *
              ((cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))) :=
      epsAutInv_on_coordinate
        (((ell d r : ℤ) - 1) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))
        ((cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))
    rw [hB, hco]
    exact coordinate_eq_of_dvd (d := d) (r := r) ⟨0, by ring⟩ ⟨0, by ring⟩
  right_inv := by
    intro g
    rw [← coordinate_val d r g]
    have hco : (cofactor d r : ℤ) = (ell d r : ℤ) - 2 := hcoZ (Fact.out : Admissible d r)
    have hA : (fun g' : G d r => coordinate d r
        ((g'.1.val : ℤ) - g'.2.val)
        (-(cofactor d r : ℤ) * g'.1.val + ((ell d r : ℤ) - 1) * g'.2.val))
        (coordinate d r ((g.1.val : ℤ)) ((g.2.val : ℤ)))
        = coordinate d r (((g.1.val : ℤ)) - ((g.2.val : ℤ)))
          (-(cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((ell d r : ℤ) - 1) * ((g.2.val : ℤ))) :=
      epsAutInv_on_coordinate ((g.1.val : ℤ)) ((g.2.val : ℤ))
    rw [hA]
    have hB : (fun g' : G d r => coordinate d r
        (((ell d r : ℤ) - 1) * g'.1.val + g'.2.val)
        ((cofactor d r : ℤ) * g'.1.val + g'.2.val))
        (coordinate d r (((g.1.val : ℤ)) - ((g.2.val : ℤ)))
          (-(cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((ell d r : ℤ) - 1) * ((g.2.val : ℤ))))
        = coordinate d r
          (((ell d r : ℤ) - 1) * (((g.1.val : ℤ)) - ((g.2.val : ℤ))) +
            (-(cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((ell d r : ℤ) - 1) * ((g.2.val : ℤ))))
          ((cofactor d r : ℤ) * (((g.1.val : ℤ)) - ((g.2.val : ℤ))) +
            (-(cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((ell d r : ℤ) - 1) * ((g.2.val : ℤ)))) :=
      epsAut_on_coordinate (((g.1.val : ℤ)) - ((g.2.val : ℤ)))
        (-(cofactor d r : ℤ) * ((g.1.val : ℤ)) + ((ell d r : ℤ) - 1) * ((g.2.val : ℤ)))
    rw [hB, hco]
    exact coordinate_eq_of_dvd (d := d) (r := r) ⟨0, by ring⟩ ⟨0, by ring⟩
  map_add' := by
    intro g₁ g₂
    rw [show g₁ = coordinate d r ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ)) from (coordinate_val d r g₁).symm,
      show g₂ = coordinate d r ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ)) from (coordinate_val d r g₂).symm,
      show coordinate d r ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))
          + coordinate d r ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))
        = coordinate d r (((g₁.1.val : ℤ)) + (g₂.1.val : ℤ))
          (((g₁.2.val : ℤ)) + (g₂.2.val : ℤ))
        from coordinate_add d r ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))
          ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))]
    rw [epsAut_on_coordinate (((g₁.1.val : ℤ)) + (g₂.1.val : ℤ))
        (((g₁.2.val : ℤ)) + (g₂.2.val : ℤ)),
      epsAut_on_coordinate ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ)),
      epsAut_on_coordinate ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ)), coordinate_add]
    exact coordinate_eq_of_dvd (d := d) (r := r) ⟨0, by ring⟩ ⟨0, by ring⟩

/-- p ↦ x_p=(p₂u-p₁)/d, in the label order of [AFK25]. -/
def iota (d r : ℕ) [Fact (Admissible d r)] : Index d →+ G d r where
  toFun p := coordinate d r (((ell d r : ℤ) - 1) * p.2.val - p.1.val)
    ((cofactor d r : ℤ) * p.2.val)
  map_zero' := by
    simp [coordinate]
  map_add' := by
    intro a b
    letI : NeZero d := admissibleDimensionNeZero d r
    letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
    have hlong := hlongZ d r
    have hm1 := Int.mul_ediv_add_emod ((a.1.val : ℤ) + b.1.val) ((d : ℤ))
    have hm2 := Int.mul_ediv_add_emod ((a.2.val : ℤ) + b.2.val) ((d : ℤ))
    have hL : coordinate d r
        (((ell d r : ℤ) - 1) * ((a + b).2.val : ℤ) - ((a + b).1.val : ℤ))
        ((cofactor d r : ℤ) * ((a + b).2.val : ℤ))
        = coordinate d r
          (((ell d r : ℤ) - 1) * (((a.2.val : ℤ) + b.2.val) % (d : ℤ)) -
            (((a.1.val : ℤ) + b.1.val) % (d : ℤ)))
          ((cofactor d r : ℤ) * (((a.2.val : ℤ) + b.2.val) % (d : ℤ))) := by
      simp only [Prod.fst_add, Prod.snd_add, ZMod.val_add]
      push_cast
      rfl
    have hR : coordinate d r (((ell d r : ℤ) - 1) * (a.2.val : ℤ) - (a.1.val : ℤ))
          ((cofactor d r : ℤ) * (a.2.val : ℤ))
        + coordinate d r (((ell d r : ℤ) - 1) * (b.2.val : ℤ) - (b.1.val : ℤ))
          ((cofactor d r : ℤ) * (b.2.val : ℤ))
        = coordinate d r
          (((ell d r : ℤ) - 1) * (a.2.val : ℤ) - (a.1.val : ℤ)
            + (((ell d r : ℤ) - 1) * (b.2.val : ℤ) - (b.1.val : ℤ)))
          ((cofactor d r : ℤ) * (a.2.val : ℤ) + (cofactor d r : ℤ) * (b.2.val : ℤ)) :=
      coordinate_add d r _ _ _ _
    rw [hL, hR]
    refine coordinate_eq_of_dvd (d := d) (r := r) ?_ ?_
    · refine ⟨(((a.1.val : ℤ) + b.1.val) / (d : ℤ)) -
          ((ell d r : ℤ) - 1) * (((a.2.val : ℤ) + b.2.val) / (d : ℤ)), ?_⟩
      linear_combination ((ell d r : ℤ) - 1) * hm2 - hm1
    · refine ⟨-((((a.2.val : ℤ) + b.2.val) / (d : ℤ))), ?_⟩
      linear_combination (cofactor d r : ℤ) * hm2
        + (((a.2.val : ℤ) + b.2.val) / (d : ℤ)) * hlong

def torsionSubgroup (d r : ℕ) [Fact (Admissible d r)] : AddSubgroup (G d r) :=
  (iota d r).range

/-- This generates the small annihilator, not the quotient by that annihilator. -/
def annihilatorGenerator (d r : ℕ) : G d r := coordinate d r 0 d

def smallSubgroup (d r : ℕ) : AddSubgroup (G d r) :=
  AddSubgroup.zmultiples (annihilatorGenerator d r)

def witnessY (d r : ℕ) (p : Index d) : G d r :=
  coordinate d r p.2.val ((p.2.val : ℤ) - p.1.val)

def twistInverseLift (d r : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1, twistScalar d r * p.2)

def twistInverseScalar (d r : ℕ) : ℤ :=
  (((twistScalar d r : ZMod (phaseModulus d))⁻¹).val : ℤ)

def twistLift (d r : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1, twistInverseScalar d r * p.2)

/-- G and G⁻¹ act modulo d; integer lifts used by D are kept separately. -/
private lemma twist_mul_mod_d {d r : ℕ} (h : Admissible d r) :
    (d : ℤ) ∣ twistScalar d r * twistInverseScalar d r - 1 := by
  have hd : 0 < d := by have := h.main_range; omega
  haveI : NeZero (phaseModulus d) := ⟨by
    simp only [phaseModulus]
    split <;> omega⟩
  have hcop : IsCoprime (twistScalar d r) ((phaseModulus d : ℕ) : ℤ) :=
    twistScalar_coprime h
  have hprod : ((twistScalar d r * twistInverseScalar d r : ℤ) : ZMod (phaseModulus d)) = 1 := by
    dsimp only [twistInverseScalar]
    push_cast
    simpa using (ZMod.coe_int_mul_val_inv hcop)
  have hdvdM : ((phaseModulus d : ℕ) : ℤ) ∣
      twistScalar d r * twistInverseScalar d r - 1 := by
    have hprod' : ((twistScalar d r * twistInverseScalar d r : ℤ) : ZMod (phaseModulus d)) =
        (((1 : ℤ)) : ZMod (phaseModulus d)) := by simpa using hprod
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub
      (twistScalar d r * twistInverseScalar d r) 1 (phaseModulus d)).mp hprod'
    rw [← neg_sub]
    exact Int.dvd_neg.mpr h
  have hdvd : ((d : ℤ)) ∣ ((phaseModulus d : ℕ) : ℤ) := by
    by_cases hEven : Even d
    · simp [phaseModulus, hEven]
    · simp [phaseModulus, hEven]
  exact hdvd.trans hdvdM

private lemma zmod_mul_val_eq_of_dvd {d : ℕ} [NeZero d] {c u q : ℤ}
    (h : (d : ℤ) ∣ c * u - 1) :
    ((c * ((((u * q : ℤ) : ZMod d).val : ℤ)) : ℤ) : ZMod d) = (q : ZMod d) := by
  have hx : ((d : ℤ)) ∣ (u * q) - ((((u * q : ℤ) : ZMod d).val : ℤ)) := by
    rw [ZMod.val_intCast]
    refine ⟨(u * q) / (d : ℤ), ?_⟩
    have := Int.mul_ediv_add_emod (u * q) (d : ℤ)
    linarith
  obtain ⟨k, hk⟩ := hx
  have h1 : ((d : ℤ)) ∣ c * (u * q) - c * ((((u * q : ℤ) : ZMod d).val : ℤ)) :=
    ⟨c * k, by linear_combination c * hk⟩
  obtain ⟨m, hm⟩ := h
  have h2 : ((d : ℤ)) ∣ c * u * q - q :=
    ⟨m * q, by linear_combination q * hm⟩
  have h3 : ((d : ℤ)) ∣ c * ((((u * q : ℤ) : ZMod d).val : ℤ)) - q := by
    refine ⟨m * q - c * k, ?_⟩
    linear_combination -c * hk + q * hm
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub
    (c * ((((u * q : ℤ) : ZMod d).val : ℤ))) q d).mpr (by
      rw [← neg_sub]
      exact Int.dvd_neg.mpr h3)

def twistEquiv (d r : ℕ) [Fact (Admissible d r)] : Index d ≃+ Index d where
  toFun p := label d (twistLift d r (lift p))
  invFun p := label d (twistInverseLift d r (lift p))
  left_inv := by
    intro p
    letI : NeZero d := admissibleDimensionNeZero d r
    have h := twist_mul_mod_d (Fact.out : Admissible d r)
    change label d (twistInverseLift d r (lift (label d (twistLift d r (lift p))))) = p
    refine Prod.ext ?_ ?_
    · simp [label, lift, twistLift, twistInverseLift]
    · simp only [label, lift, twistLift, twistInverseLift]
      have hp := zmod_mul_val_eq_of_dvd (d := d) (c := twistScalar d r)
        (u := twistInverseScalar d r) (q := (p.2.val : ℤ)) h
      simpa [ZMod.natCast_zmod_val p.2] using hp
  right_inv := by
    intro p
    letI : NeZero d := admissibleDimensionNeZero d r
    have h := twist_mul_mod_d (Fact.out : Admissible d r)
    change label d (twistLift d r (lift (label d (twistInverseLift d r (lift p))))) = p
    refine Prod.ext ?_ ?_
    · simp [label, lift, twistLift, twistInverseLift]
    · simp only [label, lift, twistLift, twistInverseLift]
      have hp := zmod_mul_val_eq_of_dvd (d := d) (c := twistInverseScalar d r)
        (u := twistScalar d r) (q := (p.2.val : ℤ)) (by
          rwa [mul_comm] at h)
      simpa [ZMod.natCast_zmod_val p.2] using hp
  map_add' := by
    intro p q
    letI : NeZero d := admissibleDimensionNeZero d r
    change label d (twistLift d r (lift (p + q))) =
      label d (twistLift d r (lift p)) + label d (twistLift d r (lift q))
    refine Prod.ext ?_ ?_
    · simp only [label, lift, twistLift, Prod.fst_add]
      push_cast
      rw [ZMod.natCast_zmod_val (p.1 + q.1), ZMod.natCast_zmod_val p.1,
        ZMod.natCast_zmod_val q.1]
    · simp only [label, lift, twistLift, Prod.snd_add]
      push_cast
      rw [ZMod.natCast_zmod_val (p.2 + q.2), ZMod.natCast_zmod_val p.2,
        ZMod.natCast_zmod_val q.2]
      ring
theorem pointLift_evaluate {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    (pointLift d r x y).1 * (unit d r : ℝ) + (pointLift d r x y).2 =
      (x : ℝ) / d + (y : ℝ) / ((d : ℝ) * (unit d r - 1)) := by
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hlev : 5 ≤ level d r := level_ge_five h
  have hell : 3 ≤ ell d r := by simp only [ell]; omega
  have hcoZ : (cofactor d r : ℤ) = (ell d r : ℤ) - 2 := by
    have : (cofactor d r : ℤ) = (level d r : ℤ) - 4 := by
      simp only [cofactor]
      exact Nat.cast_sub (by omega)
    have : (ell d r : ℤ) = (level d r : ℤ) - 2 := by
      simp only [ell]
      exact Nat.cast_sub (by omega)
    omega
  have hcoR : (cofactor d r : ℝ) = (ell d r : ℝ) - 2 := by exact_mod_cast hcoZ
  have hlongR : (longModulus d r : ℝ) = (d : ℝ) * (cofactor d r : ℝ) := by
    simp only [longModulus, Nat.cast_mul]
  have hN : (longModulus d r : ℝ) ≠ 0 := by
    rw [hlongR]
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      have : 0 < d := by omega
      exact_mod_cast this
    have ha0 : (0 : ℝ) < (cofactor d r : ℝ) := by
      have : 0 < cofactor d r := by simp only [cofactor]; omega
      exact_mod_cast this
    positivity
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < d := by omega
    exact_mod_cast (ne_of_gt this)
  have hu1 : 1 < unit d r := (unit_properties h).1
  have hu := (unit_properties h).2.1
  have hu10 : (unit d r - 1) ≠ 0 := by linarith
  unfold pointLift
  push_cast
  field_simp [hN, hd0, hu10]
  rw [hlongR]
  have hscalar : (unit d r - (ell d r : ℝ) + 1) * (unit d r - 1) =
      (cofactor d r : ℝ) := by
    rw [hcoR]
    nlinarith [hu]
  linear_combination ((y : ℝ) * (d : ℝ)) * hscalar

theorem card_G (d r : ℕ) [Fact (Admissible d r)] :
    Fintype.card (G d r) = groupOrder d r := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  change Fintype.card (ZMod d × ZMod (longModulus d r)) = groupOrder d r
  rw [Fintype.card_prod, ZMod.card, ZMod.card]
  simp only [groupOrder, longModulus]
  ring

theorem card_G_gt_four (d r : ℕ) [Fact (Admissible d r)] :
    4 < Fintype.card (G d r) := by
  have h := (Fact.out : Admissible d r)
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hlev : 5 ≤ level d r := level_ge_five h
  rw [card_G]
  have ha : 1 ≤ cofactor d r := by simp only [cofactor]; omega
  have hd3 : 3 ≤ d := by omega
  have hd2 : 9 ≤ d ^ 2 := by nlinarith
  simp only [groupOrder]
  nlinarith

theorem sqrtCard_G (d r : ℕ) [Fact (Admissible d r)] :
    L2b.sqrtCard (G d r) = (d : ℂ) * (Real.sqrt (cofactor d r) : ℂ) := by
  have h := (Fact.out : Admissible d r)
  have hr : 1 ≤ r := h.rank_pos
  have hd : 2 * r + 1 < d := h.main_range
  have hlev : 5 ≤ level d r := level_ge_five h
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ (cofactor d r : ℝ) := by
    have : 0 < cofactor d r := by simp only [cofactor]; omega
    exact_mod_cast (le_of_lt this)
  have hcast : ((groupOrder d r : ℕ) : ℝ) = (d : ℝ) ^ 2 * (cofactor d r : ℝ) := by
    simp only [groupOrder, Nat.cast_mul, Nat.cast_pow]
  rw [L2b.sqrtCard, card_G, hcast, Real.sqrt_mul (sq_nonneg (d : ℝ)),
    Real.sqrt_sq hd0]
  simp [Complex.ofReal_mul]

theorem torusPoint_injective (d r : ℕ) [Fact (Admissible d r)] :
    Function.Injective (torusPoint d r) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  have h := (Fact.out : Admissible d r)
  have hlong := hlongZ d r
  have hN : ((longModulus d r : ℚ)) ≠ 0 := by
    have : 0 < longModulus d r := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast (ne_of_gt this)
  have hco_nat : 0 < cofactor d r := by
    have := level_ge_five h
    simp only [cofactor]; omega
  have ha0 : (cofactor d r : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hco_nat)
  intro g₁ g₂ hq
  rw [← coordinate_val d r g₁, ← coordinate_val d r g₂] at hq
  rw [torusPoint_coordinate, torusPoint_coordinate, QuotientAddGroup.eq_iff_sub_mem,
    L2b.integerLattice, AddMonoidHom.mem_range] at hq
  obtain ⟨k, hk⟩ := hq
  have hfst : ((k.1 : ℤ) : ℚ) =
      (pointLift d r ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))).1 -
        (pointLift d r ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))).1 := by
    simpa [L2b.integerCoordinates] using congrArg Prod.fst hk
  have hsnd : ((k.2 : ℤ) : ℚ) =
      (pointLift d r ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))).2 -
        (pointLift d r ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))).2 := by
    simpa [L2b.integerCoordinates] using congrArg Prod.snd hk
  have hyQ : ((g₁.2.val : ℤ) : ℚ) - ((g₂.2.val : ℤ) : ℚ) =
      ((longModulus d r : ℤ) : ℚ) * (k.1 : ℚ) := by
    have h1 := pointLift_mul_one h ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))
    have h2 := pointLift_mul_one h ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))
    have h1' : (pointLift d r ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))).1 *
        ((longModulus d r : ℚ)) = ((g₁.2.val : ℤ) : ℚ) := by
      rw [mul_comm]; exact h1
    have h2' : (pointLift d r ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))).1 *
        ((longModulus d r : ℚ)) = ((g₂.2.val : ℤ) : ℚ) := by
      rw [mul_comm]; exact h2
    have hmul := congrArg (fun t : ℚ => t * ((longModulus d r : ℚ))) hfst
    rw [sub_mul, h1', h2', mul_comm] at hmul
    exact hmul.symm
  have hyDvd : ((longModulus d r : ℤ)) ∣ (g₁.2.val : ℤ) - (g₂.2.val : ℤ) := by
    refine ⟨k.1, ?_⟩
    exact_mod_cast hyQ
  have hyEq : ((g₁.2.val : ℤ)) = ((g₂.2.val : ℤ)) := by
    have hb1 : ((g₁.2.val : ℤ)) < (longModulus d r : ℤ) := by exact_mod_cast ZMod.val_lt g₁.2
    have hb2 : ((g₂.2.val : ℤ)) < (longModulus d r : ℤ) := by exact_mod_cast ZMod.val_lt g₂.2
    have hb1' : 0 ≤ ((g₁.2.val : ℤ)) := by positivity
    have hb2' : 0 ≤ ((g₂.2.val : ℤ)) := by positivity
    have habs : (((g₁.2.val : ℤ) - (g₂.2.val : ℤ))).natAbs <
        ((longModulus d r : ℤ)).natAbs := by
      rw [Int.natAbs_natCast]
      rcases Int.natAbs_eq ((g₁.2.val : ℤ) - (g₂.2.val : ℤ)) with hh | hh <;>
        rw [hh] <;> omega
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hyDvd habs
    omega
  have hxEq : ((longModulus d r : ℤ)) * k.2 =
      (cofactor d r : ℤ) * (((g₁.1.val : ℤ)) - ((g₂.1.val : ℤ))) := by
    have h1 := pointLift_mul_two h ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))
    have h2 := pointLift_mul_two h ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))
    have h1' : (pointLift d r ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))).2 *
        ((longModulus d r : ℚ)) = (cofactor d r : ℚ) * ((g₁.1.val : ℤ) : ℚ) -
          ((ell d r : ℚ) - 1) * ((g₁.2.val : ℤ) : ℚ) := by
      rw [mul_comm]; exact h1
    have h2' : (pointLift d r ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))).2 *
        ((longModulus d r : ℚ)) = (cofactor d r : ℚ) * ((g₂.1.val : ℤ) : ℚ) -
          ((ell d r : ℚ) - 1) * ((g₂.2.val : ℤ) : ℚ) := by
      rw [mul_comm]; exact h2
    have hmul := congrArg (fun t : ℚ => t * ((longModulus d r : ℚ))) hsnd
    rw [sub_mul, h1', h2'] at hmul
    push_cast at hmul ⊢
    have hyQeq : ((g₁.2.val : ℕ) : ℚ) = ((g₂.2.val : ℕ) : ℚ) := by exact_mod_cast hyEq
    rw [hyQeq] at hmul
    have hmul' : ((longModulus d r : ℤ) : ℚ) * (k.2 : ℚ) =
        (cofactor d r : ℚ) * (((g₁.1.val : ℕ) : ℚ) - ((g₂.1.val : ℕ) : ℚ)) := by
      linear_combination hmul
    exact_mod_cast hmul'
  have hxEq' : (cofactor d r : ℤ) * (((g₁.1.val : ℤ)) - ((g₂.1.val : ℤ))) =
      (cofactor d r : ℤ) * ((d : ℤ) * k.2) := by
    rw [← hxEq, hlong]
    ring
  have hxdvd : ((d : ℤ)) ∣ ((g₁.1.val : ℤ)) - ((g₂.1.val : ℤ)) := by
    refine ⟨k.2, ?_⟩
    exact mul_left_cancel₀ ha0 hxEq'
  have hxEqv : ((g₁.1.val : ℤ)) = ((g₂.1.val : ℤ)) := by
    have hb1 : ((g₁.1.val : ℤ)) < (d : ℤ) := by exact_mod_cast ZMod.val_lt g₁.1
    have hb2 : ((g₂.1.val : ℤ)) < (d : ℤ) := by exact_mod_cast ZMod.val_lt g₂.1
    have hb1' : 0 ≤ ((g₁.1.val : ℤ)) := by positivity
    have hb2' : 0 ≤ ((g₂.1.val : ℤ)) := by positivity
    have habs : (((g₁.1.val : ℤ) - (g₂.1.val : ℤ))).natAbs < ((d : ℤ)).natAbs := by
      rw [Int.natAbs_natCast]
      rcases Int.natAbs_eq ((g₁.1.val : ℤ) - (g₂.1.val : ℤ)) with hh | hh <;>
        rw [hh] <;> omega
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hxdvd habs
    omega
  refine Prod.ext ?_ ?_
  · exact ZMod.val_injective d (by omega)
  · exact ZMod.val_injective (longModulus d r) (by omega)

/-- (η⁻¹−1)z is the numerator in [RW26, (37)]. -/
theorem rwNumerator_evaluate {d r : ℕ} (h : Admissible d r) (x y : ℤ) :
    ((eta d r)⁻¹ - 1) *
        ((pointLift d r x y).1 * (unit d r : ℝ) + (pointLift d r x y).2) =
      (rwNumerator d r x y).1 * (unit d r : ℝ) + (rwNumerator d r x y).2 := by
  let u := unit d r
  let s : ℝ := (d : ℝ) - r
  let R : ℝ := r
  let L : ℝ := ell d r
  have hq : u ^ 2 - L * u + 1 = 0 := (unit_properties h).2.1
  have hc : R ^ 2 + s ^ 2 - L * R * s = 1 := by
    dsimp [R, s, L]
    exact_mod_cast principal_conic h
  have hu1 : 1 < u := (unit_properties h).1
  have hu0 : u ≠ 0 := by linarith
  have hu10 : unit d r - 1 ≠ 0 := by
    linarith [(unit_properties h).1]
  have hd0 : (d : ℝ) ≠ 0 := by
    have hd := h.main_range
    exact_mod_cast (show d ≠ 0 by omega)
  have hnorm : (s - R / u) * (s - R * u) = 1 := by
    field_simp [hu0]
    linear_combination u * hc - R * s * hq
  have hinv : (eta d r)⁻¹ = (s - R * u) ^ 2 / u := by
    apply inv_eq_of_mul_eq_one_right
    change u * (s - R / u) ^ 2 * ((s - R * u) ^ 2 / u) = 1
    calc
      _ = ((s - R / u) * (s - R * u)) ^ 2 := by field_simp [hu0]
      _ = 1 := by rw [hnorm]; norm_num
  have hlin : (s - R * u) ^ 2 / u - 1 =
      (s + R) * ((L - 1) * s - R - (s - R) * u) := by
    field_simp [hu0]
    linear_combination s ^ 2 * hq + u * hc
  have heta : (eta d r)⁻¹ - 1 =
      (d : ℝ) * (((ell d r : ℝ) - 1) * ((d : ℝ) - r) - r -
        ((d : ℝ) - 2 * r) * unit d r) := by
    rw [hinv]
    convert hlin using 1
    dsimp [u, s, R, L]
    ring
  have hfactor : ((L - 1) * s - R - (s - R) * u) =
      (u - 1) * (s * u + R - L * s) := by
    linear_combination -s * hq
  rw [pointLift_evaluate h, heta]
  simp only [rwNumerator, rowAction, rwIndexMatrix, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, gap]
  push_cast
  field_simp [hd0, hu10]
  dsimp [u, s, R, L] at hfactor
  linear_combination (y : ℝ) * hfactor

private lemma rwIndexMap_coordinate (d r : ℕ) [Fact (Admissible d r)] (x y : ℤ) :
    rwIndexMap d r (coordinate d r x y) = QuotientAddGroup.mk (rwNumerator d r x y) := by
  change QuotientAddGroup.mk (rwNumerator d r (coordinate d r x y).1.val
    (coordinate d r x y).2.val) = QuotientAddGroup.mk (rwNumerator d r x y)
  rw [QuotientAddGroup.eq_iff_sub_mem, ← rwNumerator_sub,
    rwNumerator_mem_iff (Fact.out : Admissible d r), coordinate_fst_val, coordinate_snd_val]
  constructor
  · refine ⟨-(x / d), ?_⟩
    linear_combination Int.mul_ediv_add_emod x (d : ℤ)
  · refine ⟨-(y / longModulus d r), ?_⟩
    linear_combination Int.mul_ediv_add_emod y (longModulus d r : ℤ)

theorem rwIndexMap_bijective (d r : ℕ) [Fact (Admissible d r)] :
    Function.Bijective (rwIndexMap d r) := by
  constructor
  · intro g k hgk
    change QuotientAddGroup.mk (rwNumerator d r g.1.val g.2.val) =
      QuotientAddGroup.mk (rwNumerator d r k.1.val k.2.val) at hgk
    rw [QuotientAddGroup.eq_iff_sub_mem, ← rwNumerator_sub,
      rwNumerator_mem_iff (Fact.out : Admissible d r)] at hgk
    rw [← coordinate_val d r g, ← coordinate_val d r k]
    exact coordinate_eq_of_dvd hgk.1 hgk.2
  · intro z
    refine QuotientAddGroup.induction_on z ?_
    intro v
    obtain ⟨w, hw⟩ := rowAction_surjective (rwIndexMatrix d r)
      (rwIndexMatrix_det (Fact.out : Admissible d r)) v
    refine ⟨coordinate d r w.1 w.2, ?_⟩
    rw [rwIndexMap_coordinate]
    change QuotientAddGroup.mk (rowAction (rwIndexMatrix d r) w) = QuotientAddGroup.mk v
    rw [hw]

private lemma fixedTorus_mk_iff (d r : ℕ) [Fact (Admissible d r)]
    (z : QuadraticCoordinates) :
    QuotientAddGroup.mk z ∈ fixedTorus d r ↔
      actOnCoordinates (gamma d r) z - z ∈ L2b.integerLattice := by
  change torusAction (gamma d r) (QuotientAddGroup.mk z) -
    QuotientAddGroup.mk z = 0 ↔ _
  change QuotientAddGroup.mk (actOnCoordinates (gamma d r) z) -
    QuotientAddGroup.mk z = 0 ↔ _
  rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]

private lemma gamma_defect_coordinates {d r : ℕ} (h : Admissible d r)
    (z : QuadraticCoordinates) :
    actOnCoordinates (gamma d r) z - z =
      (((d : ℚ) - r) * ((d : ℚ) * (((ell d r : ℚ) - 1) * z.1 + z.2)) +
          (r : ℚ) * ((d : ℚ) * (-z.1 - z.2)),
        -(r : ℚ) * ((d : ℚ) * (((ell d r : ℚ) - 1) * z.1 + z.2)) +
          ((d : ℚ) - r - (ell d r : ℚ) * r) * ((d : ℚ) * (-z.1 - z.2))) := by
  have he : actOnCoordinates (gamma d r) z - z =
      actOnCoordinates (gamma d r - 1) z := by
    ext <;> simp [actOnCoordinates, Matrix.sub_apply, Matrix.one_apply] <;> ring
  rw [he, gamma_sub_one h]
  ext <;>
    simp only [actOnCoordinates, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      beta, alpha, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons] <;>
    push_cast <;> norm_num <;> ring

private lemma fixedTorus_mk_iff_rect (d r : ℕ) [Fact (Admissible d r)]
    (z : QuadraticCoordinates) :
    QuotientAddGroup.mk z ∈ fixedTorus d r ↔
      ∃ a b : ℤ,
        (a : ℚ) = (d : ℚ) * (((ell d r : ℚ) - 1) * z.1 + z.2) ∧
        (b : ℚ) = (d : ℚ) * (-z.1 - z.2) := by
  have h := (Fact.out : Admissible d r)
  have hz : ((d : ℤ) - r) * ((d : ℤ) - r - (ell d r : ℤ) * r) +
      (r : ℤ) ^ 2 = 1 := by
    simpa [beta, Matrix.det_fin_two, pow_two] using (gamma_arithmetic h).2.1
  have hdet : ((d : ℚ) - r) * ((d : ℚ) - r - (ell d r : ℚ) * r) +
      (r : ℚ) ^ 2 = 1 := by exact_mod_cast hz
  rw [fixedTorus_mk_iff, gamma_defect_coordinates h,
    L2b.integerLattice, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    have hk1 : (k.1 : ℚ) =
        ((d : ℚ) - r) * ((d : ℚ) * (((ell d r : ℚ) - 1) * z.1 + z.2)) +
          (r : ℚ) * ((d : ℚ) * (-z.1 - z.2)) := congrArg Prod.fst hk
    have hk2 : (k.2 : ℚ) =
        -(r : ℚ) * ((d : ℚ) * (((ell d r : ℚ) - 1) * z.1 + z.2)) +
          ((d : ℚ) - r - (ell d r : ℚ) * r) * ((d : ℚ) * (-z.1 - z.2)) :=
      congrArg Prod.snd hk
    refine ⟨((d : ℤ) - r - (ell d r : ℤ) * r) * k.1 - (r : ℤ) * k.2,
      (r : ℤ) * k.1 + ((d : ℤ) - r) * k.2, ?_, ?_⟩
    · push_cast
      linear_combination ((d : ℚ) - r - (ell d r : ℚ) * r) * hk1 -
        (r : ℚ) * hk2 +
        ((d : ℚ) * (((ell d r : ℚ) - 1) * z.1 + z.2)) * hdet
    · push_cast
      linear_combination (r : ℚ) * hk1 + ((d : ℚ) - r) * hk2 +
        ((d : ℚ) * (-z.1 - z.2)) * hdet
  · rintro ⟨a, b, ha, hb⟩
    refine ⟨(((d : ℤ) - r) * a + (r : ℤ) * b,
      -(r : ℤ) * a + ((d : ℤ) - r - (ell d r : ℤ) * r) * b), ?_⟩
    refine Prod.ext ?_ ?_
    · change ((((d : ℤ) - r) * a + (r : ℤ) * b : ℤ) : ℚ) = _
      push_cast
      linear_combination ((d : ℚ) - r) * ha + (r : ℚ) * hb
    · change ((-(r : ℤ) * a + ((d : ℤ) - r - (ell d r : ℤ) * r) * b : ℤ) : ℚ) = _
      push_cast
      linear_combination -(r : ℚ) * ha +
        ((d : ℚ) - r - (ell d r : ℚ) * r) * hb

theorem torusPoint_range (d r : ℕ) [Fact (Admissible d r)] :
    (torusPoint d r).range = fixedTorus d r := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  have h := (Fact.out : Admissible d r)
  have hN : (longModulus d r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hco : (cofactor d r : ℚ) = (ell d r : ℚ) - 2 := by exact_mod_cast hcoZ h
  have hlong : (longModulus d r : ℚ) =
      (d : ℚ) * (cofactor d r : ℚ) := by exact_mod_cast hlongZ d r
  have hC : (cofactor d r : ℚ) ≠ 0 := by
    have hpos : 0 < cofactor d r := by
      have := level_ge_five h
      simp only [cofactor]; omega
    exact_mod_cast (ne_of_gt hpos)
  apply le_antisymm
  · rintro z ⟨g, rfl⟩
    change QuotientAddGroup.mk
      (pointLift d r (g.1.val : ℤ) (g.2.val : ℤ)) ∈ fixedTorus d r
    rw [fixedTorus_mk_iff_rect]
    refine ⟨(g.1.val : ℤ), (g.2.val : ℤ) - g.1.val, ?_, ?_⟩
    · symm
      apply mul_left_cancel₀ hC
      have hp1 := pointLift_mul_one h (g.1.val : ℤ) (g.2.val : ℤ)
      have hp2 := pointLift_mul_two h (g.1.val : ℤ) (g.2.val : ℤ)
      rw [hlong] at hp1 hp2
      linear_combination ((ell d r : ℚ) - 1) * hp1 + hp2
    · symm
      apply mul_left_cancel₀ hC
      have hp1 := pointLift_mul_one h (g.1.val : ℤ) (g.2.val : ℤ)
      have hp2 := pointLift_mul_two h (g.1.val : ℤ) (g.2.val : ℤ)
      push_cast
      rw [hlong] at hp1 hp2
      rw [hco] at hp1 hp2 ⊢
      linear_combination -hp1 - hp2
  · intro z hz
    revert hz
    refine QuotientAddGroup.induction_on z ?_
    intro a ha
    rw [fixedTorus_mk_iff_rect] at ha
    obtain ⟨x, b, hx, hb⟩ := ha
    have hp : pointLift d r x (x + b) = a := by
      refine Prod.ext ?_ ?_
      · apply mul_left_cancel₀ hN
        rw [pointLift_mul_one h]
        push_cast
        rw [hlong, hco]
        linear_combination hx + hb
      · apply mul_left_cancel₀ hN
        rw [pointLift_mul_two h]
        push_cast
        rw [hlong, hco]
        linear_combination -hx - ((ell d r : ℚ) - 1) * hb
    exact AddMonoidHom.mem_range.mpr
      ⟨coordinate d r x (x + b), by rw [torusPoint_coordinate, hp]⟩

theorem torusPoint_epsilon (d r : ℕ) [Fact (Admissible d r)] (g : G d r) :
    torusPoint d r (epsilonAut d r g) = epsilonOnTorus d r (torusPoint d r g) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  have h := (Fact.out : Admissible d r)
  have hlong := hlongZ d r
  have hN : ((longModulus d r : ℚ)) ≠ 0 := by
    have : 0 < longModulus d r := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast (ne_of_gt this)
  have hlongQ : ((longModulus d r : ℚ)) = (d : ℚ) * (cofactor d r : ℚ) := by
    exact_mod_cast hlong
  have hco := hcoZ h
  have hcoQ : (cofactor d r : ℚ) = (ell d r : ℚ) - 2 := by exact_mod_cast hco
  have hT : epsilonAut d r g = coordinate d r
      (((ell d r : ℤ) - 1) * g.1.val + g.2.val)
      ((cofactor d r : ℤ) * g.1.val + g.2.val) := by
    change (fun g' : G d r => coordinate d r
      (((ell d r : ℤ) - 1) * g'.1.val + g'.2.val)
      ((cofactor d r : ℤ) * g'.1.val + g'.2.val)) g = _
    rfl
  rw [hT, torusPoint_coordinate]
  change QuotientAddGroup.mk (pointLift d r
      (((ell d r : ℤ) - 1) * g.1.val + g.2.val)
      ((cofactor d r : ℤ) * g.1.val + g.2.val)) =
    QuotientAddGroup.mk (actOnCoordinates (alpha d r) (pointLift d r g.1.val g.2.val))
  have hpl : pointLift d r
      (((ell d r : ℤ) - 1) * g.1.val + g.2.val)
      ((cofactor d r : ℤ) * g.1.val + g.2.val) =
      actOnCoordinates (alpha d r) (pointLift d r g.1.val g.2.val) := by
    refine Prod.ext ?_ ?_
    · simp only [pointLift, actOnCoordinates, alpha, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
      field_simp [hN]
      push_cast
      ring
    · simp only [pointLift, actOnCoordinates, alpha, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
      field_simp [hN]
      push_cast
      rw [hcoQ]
      ring
  rw [hpl]

theorem iota_torusPoint (d r : ℕ) [Fact (Admissible d r)] (p : Index d) :
    torusPoint d r (iota d r p) =
      QuotientAddGroup.mk (((p.2.val : ℚ) / d, -(p.1.val : ℚ) / d) :
        QuadraticCoordinates) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  have hlong := hlongZ d r
  have hN : ((longModulus d r : ℚ)) ≠ 0 := by
    have : 0 < longModulus d r := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast (ne_of_gt this)
  have ha0 : ((cofactor d r : ℚ)) ≠ 0 := by
    have : 0 < cofactor d r := by
      have := level_ge_five (Fact.out : Admissible d r)
      simp only [cofactor]; omega
    exact_mod_cast (ne_of_gt this)
  have hd0 : ((d : ℚ)) ≠ 0 := by
    have : 0 < d := by have := (Fact.out : Admissible d r).main_range; omega
    exact_mod_cast (ne_of_gt this)
  have hlongQ : ((longModulus d r : ℚ)) = (d : ℚ) * (cofactor d r : ℚ) := by
    exact_mod_cast hlong
  have hpl : pointLift d r
      (((ell d r : ℤ) - 1) * (p.2.val : ℤ) - (p.1.val : ℤ))
      ((cofactor d r : ℤ) * (p.2.val : ℤ)) =
      (((p.2.val : ℚ) / d, -(p.1.val : ℚ) / d) : QuadraticCoordinates) := by
    refine Prod.ext ?_ ?_
    · simp only [pointLift]
      field_simp [hN]
      rw [hlongQ]
      field_simp [ha0, hd0]
      push_cast
      ring
    · simp only [pointLift]
      field_simp [hN, hd0]
      rw [hlongQ]
      push_cast
      ring
  rw [show iota d r p = coordinate d r
      (((ell d r : ℤ) - 1) * (p.2.val : ℤ) - (p.1.val : ℤ))
      ((cofactor d r : ℤ) * (p.2.val : ℤ)) from rfl,
    torusPoint_coordinate, hpl]

theorem iota_injective (d r : ℕ) [Fact (Admissible d r)] :
    Function.Injective (iota d r) := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  intro a b hab
  have hco_nat : 0 < cofactor d r := by
    have := level_ge_five (Fact.out : Admissible d r)
    simp only [cofactor]; omega
  have hco0 : (cofactor d r : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hco_nat)
  have hlong := hlongZ d r
  have hab1 : ((iota d r a).1 : ZMod d) = ((iota d r b).1 : ZMod d) := congrArg Prod.fst hab
  have hab2 : ((iota d r a).2 : ZMod (longModulus d r)) =
      ((iota d r b).2 : ZMod (longModulus d r)) := congrArg Prod.snd hab
  have e1 : ((iota d r a).1 : ZMod d) =
      ((((ell d r : ℤ) - 1) * (a.2.val : ℤ) - (a.1.val : ℤ)) : ZMod d) := by
    simp [iota, coordinate]
  have e1' : ((iota d r b).1 : ZMod d) =
      ((((ell d r : ℤ) - 1) * (b.2.val : ℤ) - (b.1.val : ℤ)) : ZMod d) := by
    simp [iota, coordinate]
  have e2 : ((iota d r a).2 : ZMod (longModulus d r)) =
      ((((cofactor d r : ℤ) * (a.2.val : ℤ))) : ZMod (longModulus d r)) := by
    simp [iota, coordinate]
  have e2' : ((iota d r b).2 : ZMod (longModulus d r)) =
      ((((cofactor d r : ℤ) * (b.2.val : ℤ))) : ZMod (longModulus d r)) := by
    simp [iota, coordinate]
  rw [e1, e1'] at hab1
  rw [e2, e2'] at hab2
  have h1 : ((d : ℤ)) ∣
      ((((ell d r : ℤ) - 1) * (b.2.val : ℤ) - (b.1.val : ℤ)) -
        (((ell d r : ℤ) - 1) * (a.2.val : ℤ) - (a.1.val : ℤ))) := by
    have hZ : ((((ell d r : ℤ) - 1) * (a.2.val : ℤ) - (a.1.val : ℤ) : ℤ) : ZMod d) =
        ((((ell d r : ℤ) - 1) * (b.2.val : ℤ) - (b.1.val : ℤ) : ℤ) : ZMod d) := by
      simpa [iota, coordinate] using hab1
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ d).mp hZ
  have h2 : ((longModulus d r : ℤ)) ∣
      ((cofactor d r : ℤ) * (b.2.val : ℤ) - (cofactor d r : ℤ) * (a.2.val : ℤ)) := by
    have hZ : ((((cofactor d r : ℤ) * (a.2.val : ℤ) : ℤ) : ZMod (longModulus d r))) =
        ((((cofactor d r : ℤ) * (b.2.val : ℤ) : ℤ) : ZMod (longModulus d r))) := by
      simpa [iota, coordinate] using hab2
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (longModulus d r)).mp hZ
  rw [← mul_sub, hlong, mul_comm ((d : ℤ)) (cofactor d r : ℤ)] at h2
  have hs : ((d : ℤ)) ∣ ((b.2.val : ℤ) - (a.2.val : ℤ)) :=
    (Int.mul_dvd_mul_iff_left hco0).mp h2
  have hr : ((d : ℤ)) ∣ ((b.1.val : ℤ) - (a.1.val : ℤ)) := by
    obtain ⟨k1, hk1⟩ := hs
    obtain ⟨k2, hk2⟩ := h1
    refine ⟨((ell d r : ℤ) - 1) * k1 - k2, ?_⟩
    linear_combination ((ell d r : ℤ) - 1) * hk1 - hk2
  refine Prod.ext ?_ ?_
  · exact ZMod.val_injective d
      (nat_eq_of_modEq_lt d _ _ ((Nat.modEq_iff_dvd).mpr hr) (ZMod.val_lt _) (ZMod.val_lt _))
  · exact ZMod.val_injective d
      (nat_eq_of_modEq_lt d _ _ ((Nat.modEq_iff_dvd).mpr hs) (ZMod.val_lt _) (ZMod.val_lt _))

theorem iota_range_eq_torsion (d r : ℕ) [Fact (Admissible d r)] :
    (torsionSubgroup d r : Set (G d r)) = {g | d • g = 0} := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  have hlong := hlongZ d r
  have hd0 : ((d : ℤ)) ≠ 0 := by
    have : 0 < d := by have := (Fact.out : Admissible d r).main_range; omega
    exact_mod_cast (ne_of_gt this)
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    change (d • ((((ell d r : ℤ) - 1) * (p.2.val : ℤ) - (p.1.val : ℤ) : ℤ) : ZMod d),
      d • ((((cofactor d r : ℤ) * (p.2.val : ℤ) : ℤ)) : ZMod (longModulus d r))) = (0, 0)
    refine Prod.ext ?_ ?_
    · exact (zmod_nsmul_eq_zero_iff d d _).mpr (dvd_mul_right _ _)
    · exact (zmod_nsmul_eq_zero_iff d (longModulus d r) _).mpr (by
        refine ⟨(p.2.val : ℤ), ?_⟩
        rw [hlong]
        ring)
  · intro hg
    have hsn : d • (g.2 : ZMod (longModulus d r)) = 0 := congrArg Prod.snd hg
    have hgc : (g.2 : ZMod (longModulus d r)) =
        ((((g.2.val : ℤ)) : ZMod (longModulus d r))) := by
      rw [← ZMod.natCast_zmod_val g.2]
      simp
    rw [hgc] at hsn
    have hdvd := (zmod_nsmul_eq_zero_iff d (longModulus d r) ((g.2.val : ℤ))).mp hsn
    rw [hlong] at hdvd
    have hcov : ((cofactor d r : ℤ)) ∣ ((g.2.val : ℤ)) :=
      (Int.mul_dvd_mul_iff_left hd0).mp (by simpa [mul_comm] using hdvd)
    obtain ⟨k, hk⟩ := hcov
    have hk' : (g.2.val : ℤ) = (cofactor d r : ℤ) * k := hk
    let p2 : ZMod d := ((k : ℤ) : ZMod d)
    let p1 : ZMod d := ((((ell d r : ℤ) - 1) * k - (g.1.val : ℤ)) : ZMod d)
    refine AddMonoidHom.mem_range.mpr ⟨(p1, p2), ?_⟩
    have hp2 : ((d : ℤ)) ∣ (k - (p2.val : ℤ)) := by
      have hv : (p2.val : ℤ) = k % (d : ℤ) := by
        simpa [p2] using ZMod.val_intCast (n := d) k
      refine ⟨k / (d : ℤ), ?_⟩
      have := Int.mul_ediv_add_emod k (d : ℤ)
      rw [hv]
      linarith
    have hp1 : ((d : ℤ)) ∣
        ((((ell d r : ℤ) - 1) * k - (g.1.val : ℤ)) - (p1.val : ℤ)) := by
      have hv : (p1.val : ℤ) = (((ell d r : ℤ) - 1) * k - (g.1.val : ℤ)) % (d : ℤ) := by
        simpa [p1] using ZMod.val_intCast (n := d) (((ell d r : ℤ) - 1) * k - (g.1.val : ℤ))
      refine ⟨(((ell d r : ℤ) - 1) * k - (g.1.val : ℤ)) / (d : ℤ), ?_⟩
      have := Int.mul_ediv_add_emod (((ell d r : ℤ) - 1) * k - (g.1.val : ℤ)) (d : ℤ)
      rw [hv]
      linarith
    change coordinate d r
        (((ell d r : ℤ) - 1) * (p2.val : ℤ) - (p1.val : ℤ))
        ((cofactor d r : ℤ) * (p2.val : ℤ)) = g
    rw [← coordinate_val d r g]
    apply coordinate_eq_of_dvd (d := d) (r := r)
    · obtain ⟨k2, hk2⟩ := hp2
      obtain ⟨k1, hk1⟩ := hp1
      refine ⟨k1 - ((ell d r : ℤ) - 1) * k2, ?_⟩
      linear_combination hk1 - ((ell d r : ℤ) - 1) * hk2
    · obtain ⟨k2, hk2⟩ := hp2
      refine ⟨-k2, ?_⟩
      linear_combination -((cofactor d r : ℤ) * hk2) + k2 * hlong - hk'

private lemma epsilonAut_annihilator (d r : ℕ) [Fact (Admissible d r)] :
    epsilonAut d r (annihilatorGenerator d r) = annihilatorGenerator d r := by
  have h := epsAut_on_coordinate (d := d) (r := r) (0 : ℤ) (d : ℤ)
  have h2 : coordinate d r (((ell d r : ℤ) - 1) * 0 + (d : ℤ))
      ((cofactor d r : ℤ) * 0 + (d : ℤ)) = coordinate d r 0 (d : ℤ) := by
    apply coordinate_eq_of_dvd (d := d) (r := r)
    · refine ⟨1, by ring⟩
    · exact ⟨0, by ring⟩
  exact h.trans h2

theorem smallSubgroup_fixed (d r : ℕ) [Fact (Admissible d r)]
    (g : G d r) (hg : g ∈ smallSubgroup d r) : epsilonAut d r g = g := by
  rw [smallSubgroup, AddSubgroup.mem_zmultiples_iff] at hg
  obtain ⟨k, hk⟩ := hg
  rw [← hk, map_zsmul, epsilonAut_annihilator]

theorem annihilatorGenerator_order (d r : ℕ) [Fact (Admissible d r)] :
    addOrderOf (annihilatorGenerator d r) = cofactor d r := by
  simp only [annihilatorGenerator, coordinate, Prod.addOrderOf_mk]
  have hzero : addOrderOf (((0 : ℤ) : ZMod d)) = 1 := by simp
  rw [hzero, Nat.lcm_one_left]
  have hcast : ((((d : ℕ) : ℤ)) : ZMod (longModulus d r)) = ((d : ℕ) : ZMod (longModulus d r)) := by
    push_cast
    rfl
  rw [hcast, ZMod.addOrderOf_coe d (NeZero.ne (longModulus d r))]
  have hd : 0 < d := by have := (Fact.out : Admissible d r).main_range; omega
  simp only [longModulus]
  rw [Nat.gcd_comm, Nat.gcd_eq_left (dvd_mul_right d (cofactor d r)), Nat.mul_div_right _ hd]

theorem smallSubgroup_card (d r : ℕ) [Fact (Admissible d r)] :
    Nat.card (smallSubgroup d r) = cofactor d r := by
  rw [smallSubgroup, Nat.card_zmultiples, annihilatorGenerator_order]

theorem witnessY_epsilon (d r : ℕ) [Fact (Admissible d r)] (p : Index d) :
    epsilonAut d r (witnessY d r p) - witnessY d r p = iota d r p := by
  have hY : witnessY d r p = coordinate d r (p.2.val : ℤ) ((p.2.val : ℤ) - (p.1.val : ℤ)) := rfl
  have hI : iota d r p = coordinate d r (((ell d r : ℤ) - 1) * (p.2.val : ℤ) - (p.1.val : ℤ))
      ((cofactor d r : ℤ) * (p.2.val : ℤ)) := rfl
  rw [hY, hI]
  have hT : epsilonAut d r (coordinate d r (p.2.val : ℤ) ((p.2.val : ℤ) - (p.1.val : ℤ)))
      = coordinate d r
        (((ell d r : ℤ) - 1) * (p.2.val : ℤ) + ((p.2.val : ℤ) - (p.1.val : ℤ)))
        ((cofactor d r : ℤ) * (p.2.val : ℤ) + ((p.2.val : ℤ) - (p.1.val : ℤ))) := by
    change (fun g' : G d r => coordinate d r
      (((ell d r : ℤ) - 1) * g'.1.val + g'.2.val)
      ((cofactor d r : ℤ) * g'.1.val + g'.2.val))
      (coordinate d r (p.2.val : ℤ) ((p.2.val : ℤ) - (p.1.val : ℤ))) = _
    exact epsAut_on_coordinate _ _
  rw [hT, coordinate_sub]
  apply coordinate_eq_of_dvd (d := d) (r := r)
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩

theorem epsilon_sub_id_range (d r : ℕ) [Fact (Admissible d r)] :
    ((epsilonAut d r).toAddMonoidHom - AddMonoidHom.id (G d r)).range =
      torsionSubgroup d r := by
  apply le_antisymm
  · rintro z ⟨g, rfl⟩
    apply (Set.ext_iff.mp (iota_range_eq_torsion d r) _).mpr
    change d • (epsilonAut d r g - g) = 0
    have hsub : epsilonAut d r g - g = coordinate d r
        ((cofactor d r : ℤ) * g.1.val + g.2.val)
        ((cofactor d r : ℤ) * g.1.val) := by
      change coordinate d r
        (((ell d r : ℤ) - 1) * g.1.val + g.2.val)
        ((cofactor d r : ℤ) * g.1.val + g.2.val) - g = _
      calc
        _ = coordinate d r
            (((ell d r : ℤ) - 1) * g.1.val + g.2.val)
            ((cofactor d r : ℤ) * g.1.val + g.2.val) -
              coordinate d r g.1.val g.2.val := by rw [coordinate_val]
        _ = _ := by
          rw [coordinate_sub]
          congr 1 <;> rw [hcoZ (Fact.out : Admissible d r)] <;> ring
    rw [hsub]
    refine Prod.ext ?_ ?_
    · exact (zmod_nsmul_eq_zero_iff d d _).mpr (dvd_mul_right _ _)
    · apply (zmod_nsmul_eq_zero_iff d (longModulus d r) _).mpr
      exact ⟨g.1.val, by rw [hlongZ]; ring⟩
  · rintro z ⟨p, rfl⟩
    exact ⟨witnessY d r p, witnessY_epsilon d r p⟩

theorem shifted_witness_ne_zero (d r : ℕ) [Fact (Admissible d r)]
    (p : Index d) (hp : p ≠ 0) (g : G d r) (hg : g ∈ smallSubgroup d r) :
    g - witnessY d r p ≠ 0 ∧ g - witnessY d r p - iota d r p ≠ 0 := by
  letI : NeZero d := admissibleDimensionNeZero d r
  letI : NeZero (longModulus d r) := admissibleLongModulusNeZero d r
  have hlong := hlongZ d r
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
  have hg1 : g.1 = 0 := by
    rw [← hk]
    simp [annihilatorGenerator, coordinate]
  have hg2 : g.2 = (((k : ℤ) * (d : ℤ) : ℤ) : ZMod (longModulus d r)) := by
    rw [← hk]
    simp [annihilatorGenerator, coordinate]
  have hne1 : g - witnessY d r p ≠ 0 := by
    intro hzero
    have hfirst : p.2 = 0 := by
      have hh := congrArg Prod.fst hzero
      rw [Prod.fst_sub, hg1] at hh
      have hcast : (((p.2.val : ℤ)) : ZMod d) = 0 := by
        simpa [witnessY, coordinate] using hh
      exact (ZMod.val_eq_zero p.2).mp (by
        have := ZMod.val_intCast (n := d) (p.2.val : ℤ)
        have hv : ((p.2.val : ℤ) : ZMod d).val = 0 := by
          rw [hcast]; simp
        exact by simpa using hv)
    have hp2val : p.2.val = 0 := (ZMod.val_eq_zero p.2).mpr hfirst
    have hsecond : (((k : ℤ) * (d : ℤ) + (p.1.val : ℤ) : ℤ) : ZMod (longModulus d r)) = 0 := by
      have hh := congrArg Prod.snd hzero
      have hh' : g.2 - ((((p.2.val : ℤ) - (p.1.val : ℤ)) : ℤ) : ZMod (longModulus d r)) = 0 := by
        simpa [witnessY, coordinate] using hh
      rw [hg2, hp2val] at hh'
      push_cast at hh' ⊢
      simpa using hh'
    have hdvdN := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((k : ℤ) * (d : ℤ) + (p.1.val : ℤ)) (longModulus d r)).mp hsecond
    have hdd : (d : ℤ) ∣ ((k : ℤ) * (d : ℤ) + (p.1.val : ℤ)) := by
      exact dvd_trans (show (d : ℤ) ∣ (longModulus d r : ℤ) from
        ⟨cofactor d r, by rw [hlong]⟩) hdvdN
    have hdp1 : (d : ℤ) ∣ (p.1.val : ℤ) := by
      have hdkd : (d : ℤ) ∣ (k : ℤ) * (d : ℤ) := ⟨k, by ring⟩
      simpa using dvd_sub hdd hdkd
    have hp1val : p.1.val = 0 := by
      have hb : (p.1.val : ℤ) < (d : ℤ) := by exact_mod_cast ZMod.val_lt p.1
      have hb' : 0 ≤ (p.1.val : ℤ) := by positivity
      have habs : ((p.1.val : ℤ)).natAbs < ((d : ℤ)).natAbs := by
        rw [Int.natAbs_natCast, Int.natAbs_natCast]
        omega
      have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdp1 habs
      omega
    have hp1 : p.1 = 0 := (ZMod.val_eq_zero p.1).mp hp1val
    exact hp (Prod.ext hp1 hfirst)
  refine ⟨hne1, ?_⟩
  intro hzero2
  have hfix := smallSubgroup_fixed d r g hg
  have hwit := witnessY_epsilon d r p
  have hwit' : epsilonAut d r (witnessY d r p) = witnessY d r p + iota d r p := by
    rw [← hwit]
    abel
  have hT : epsilonAut d r (g - witnessY d r p) =
      g - witnessY d r p - iota d r p := by
    rw [map_sub, hfix, hwit']
    abel
  have hinj := (epsilonAut d r).injective
  have hsame : epsilonAut d r (g - witnessY d r p) = epsilonAut d r 0 := by
    rw [hT, hzero2]
    simp
  have := hinj hsame
  exact hne1 this

theorem twist_inverse_mod_phase {d r : ℕ} (h : Admissible d r) :
    (phaseModulus d : ℤ) ∣ twistScalar d r * twistInverseScalar d r - 1 := by
  have hd : 0 < d := by have := h.main_range; omega
  haveI : NeZero (phaseModulus d) := ⟨by
    simp only [phaseModulus]
    split <;> omega⟩
  have hcop : IsCoprime (twistScalar d r) ((phaseModulus d : ℕ) : ℤ) :=
    twistScalar_coprime h
  have hprod : ((twistScalar d r * twistInverseScalar d r : ℤ) : ZMod (phaseModulus d)) = 1 := by
    dsimp only [twistInverseScalar]
    push_cast
    simpa using (ZMod.coe_int_mul_val_inv hcop)
  have hprod' : ((twistScalar d r * twistInverseScalar d r : ℤ) : ZMod (phaseModulus d)) =
      (((1 : ℤ)) : ZMod (phaseModulus d)) := by simpa using hprod
  have h := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (twistScalar d r * twistInverseScalar d r) 1 (phaseModulus d)).mp hprod'
  rw [← neg_sub]
  exact Int.dvd_neg.mpr h

end SICLean.L2r
