import SICLean.L5.ActualQuadraticField
import SICLean.L5.RayArithmeticPlacesAux
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus

set_option autoImplicit false

/-!
# The two actual embeddings as real places

The literal trace-minus-identity conjugation and the two actual real places. Source:
[RW26, p. 20]. Real-place comparison is an arithmetic bridge to [RW-rec]. No analytic
value, germ, square root, Phi or eta is redefined here.
-/

noncomputable section
open scoped MatrixGroups NumberField Classical
open NumberField

namespace SICLean.L5.RayArithmeticPlaces

variable (M : SL(2, ℤ)) (hM : L4.SpecialValueAdmissible M)
local notation "K" => ActualField.baseField M hM

/-- Concrete quadratic conjugation, rather than a chosen automorphism. -/
def conjugation : K ≃ₐ[ℚ] K where
  toFun x := algebraMap ℚ K (Algebra.trace ℚ K x) - x
  invFun x := algebraMap ℚ K (Algebra.trace ℚ K x) - x
  left_inv := RayArithmeticPlacesAux.trace_sub_involutive
    (ActualField.baseField_isRealQuadratic M hM).degree_two
  right_inv := RayArithmeticPlacesAux.trace_sub_involutive
    (ActualField.baseField_isRealQuadratic M hM).degree_two
  map_mul' := RayArithmeticPlacesAux.trace_sub_mul
    (ActualField.baseField_isRealQuadratic M hM).degree_two
  map_add' := RayArithmeticPlacesAux.trace_sub_add
  commutes' := RayArithmeticPlacesAux.trace_sub_rat
    (ActualField.baseField_isRealQuadratic M hM).degree_two

def integerConjugation : 𝓞 K ≃+* 𝓞 K :=
  RingOfIntegers.mapRingEquiv (conjugation M hM).toRingEquiv

def complexEmbedding₁ : K →+* ℂ :=
  Complex.ofRealHom.comp (ActualField.sigma₁ M hM)

def complexEmbedding₂ : K →+* ℂ :=
  Complex.ofRealHom.comp (ActualField.sigma₂ M hM)

def infinitePlace₁ : InfinitePlace K := InfinitePlace.mk (complexEmbedding₁ M hM)
def infinitePlace₂ : InfinitePlace K := InfinitePlace.mk (complexEmbedding₂ M hM)

/-- Source: real-embedding bridge. [RW26, p. 20]. -/
theorem infinitePlace₁_isReal : (infinitePlace₁ M hM).IsReal := by
  exact InfinitePlace.isReal_mk_iff.mpr
    (RayArithmeticPlacesAux.ofReal_comp_isReal (ActualField.sigma₁ M hM))

/-- Source: same bridge for the specified second embedding. [RW26, p. 20]. -/
theorem infinitePlace₂_isReal : (infinitePlace₂ M hM).IsReal := by
  exact InfinitePlace.isReal_mk_iff.mpr
    (RayArithmeticPlacesAux.ofReal_comp_isReal (ActualField.sigma₂ M hM))

def realPlace₁ : ClassFieldTheory.RayClassRealPlace K :=
  ⟨infinitePlace₁ M hM, infinitePlace₁_isReal M hM⟩

def realPlace₂ : ClassFieldTheory.RayClassRealPlace K :=
  ⟨infinitePlace₂ M hM, infinitePlace₂_isReal M hM⟩

/-- Source: actual sigma_1 identification, via the InfinitePlace real embedding. [RW26, p. 20]. -/
theorem realPlace₁_embedding :
    (realPlace₁ M hM).1.embedding_of_isReal (realPlace₁ M hM).2 =
      ActualField.sigma₁ M hM := by
  exact RayArithmeticPlacesAux.embedding_of_mk_ofReal (ActualField.sigma₁ M hM)
    (infinitePlace₁_isReal M hM)

/-- Source: same comparison for sigma_2, not an arbitrary real place. [RW26, p. 20]. -/
theorem realPlace₂_embedding :
    (realPlace₂ M hM).1.embedding_of_isReal (realPlace₂ M hM).2 =
      ActualField.sigma₂ M hM := by
  exact RayArithmeticPlacesAux.embedding_of_mk_ofReal (ActualField.sigma₂ M hM)
    (infinitePlace₂_isReal M hM)

/-- Source: quadratic trace bridge; [RW-rec]. [RW26, p. 20]. -/
theorem conjugation_apply (x : K) :
    conjugation M hM x = algebraMap ℚ K (Algebra.trace ℚ K x) - x := by
  rfl

/-- Source: quadratic conjugation, same sources as conjugation_apply. [RW26, p. 20]. -/
theorem conjugation_involutive : Function.Involutive (conjugation M hM) := by
  exact RayArithmeticPlacesAux.trace_sub_involutive
    (ActualField.baseField_isRealQuadratic M hM).degree_two

/-- Source: two distinct embeddings. [RW26, p. 20]; [RW-rec]. -/
theorem conjugation_ne_one : conjugation M hM ≠ 1 := by
  intro h
  apply RayArithmeticPlacesAux.trace_sub_ne_id
    (ActualField.baseField_isRealQuadratic M hM).degree_two
  funext x
  change conjugation M hM x = x
  rw [h]
  rfl

/-- Source: exchange of the two real embeddings, [RW-rec]. [RW26, p. 20]. -/
theorem sigma₁_conjugation (x : K) :
    ActualField.sigma₁ M hM (conjugation M hM x) = ActualField.sigma₂ M hM x := by
  rw [conjugation_apply, map_sub, RingHom.map_rat_algebraMap]
  rfl

/-- Source: the same exchange, in the other direction. [RW26, p. 20]. -/
theorem sigma₂_conjugation (x : K) :
    ActualField.sigma₂ M hM (conjugation M hM x) = ActualField.sigma₁ M hM x := by
  rw [← sigma₁_conjugation M hM (conjugation M hM x), conjugation_involutive M hM x]

/-- Source: real quadratic degree and distinct embeddings. [RW26, p. 20]. -/
theorem realPlace_ne : realPlace₁ M hM ≠ realPlace₂ M hM := by
  intro h
  apply RayArithmeticPlacesAux.sigma₁_ne_sigma₂ M hM
  rw [← realPlace₁_embedding M hM, ← realPlace₂_embedding M hM]
  exact congrArg
    (fun v : ClassFieldTheory.RayClassRealPlace K => v.1.embedding_of_isReal v.2) h

/-- Source: exactly two real places, same sources as realPlace_ne. [RW26, p. 20]. -/
theorem infinitePlace_eq (v : InfinitePlace K) :
    v = infinitePlace₁ M hM ∨ v = infinitePlace₂ M hM := by
  have hcard : Nat.card (K →+* ℂ) = 2 := by
    rw [Nat.card_eq_fintype_card, Embeddings.card,
      (ActualField.baseField_isRealQuadratic M hM).degree_two]
  have hne : complexEmbedding₁ M hM ≠ complexEmbedding₂ M hM := by
    intro h
    apply realPlace_ne M hM
    exact Subtype.ext (congrArg InfinitePlace.mk h)
  by_cases h : v.embedding = complexEmbedding₁ M hM
  · left
    rw [← InfinitePlace.mk_embedding v, h]
    rfl
  · right
    have heq : v.embedding = complexEmbedding₂ M hM :=
      ExistsUnique.unique ((Nat.card_eq_two_iff' (complexEmbedding₁ M hM)).mp hcard)
        h (Ne.symm hne)
    rw [← InfinitePlace.mk_embedding v, heq]
    rfl

/-- Source: this is the real-place set, not an extra narrow modulus with finite part zero. [RW26, p.
20]. -/
theorem realPlace_pair_eq_univ :
    ({realPlace₁ M hM, realPlace₂ M hM} : Finset (ClassFieldTheory.RayClassRealPlace K)) =
      Finset.univ := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
  rcases infinitePlace_eq M hM v.1 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

#check @ClassFieldTheory.RayClassRealPlace
#check @InfinitePlace.mk
#check @RingOfIntegers.mapRingEquiv
#print conjugation
#print realPlace₁

end SICLean.L5.RayArithmeticPlaces
