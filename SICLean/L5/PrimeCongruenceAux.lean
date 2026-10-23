import SICLean.L5.PrimeReductionArithmetic

set_option autoImplicit false

/-!
# Local ideal powers and the integer order

The localization of a maximal-ideal power contracts to the corresponding global ideal
power (`IsLocalization.AtPrime.under_maximalIdeal_pow`). Clearing a denominator outside
the prime preserves both ideal membership and the integer order. This also covers the
zeroth ideal power and zero.
-/

noncomputable section

namespace SICLean.L5.PrimeCongruenceAux

open NumberField FinitePlace

variable {L : Type*} [Field L] [NumberField L]

/-- Local maximal-ideal powers are measured by the integer order, without a global integrality
hypothesis on the local-ring element. -/
theorem localRing_mem_maximal_pow_iff (P : Prime L) (n : ℕ) (a : LocalRing P) :
    a ∈ (IsLocalRing.maximalIdeal (LocalRing P)) ^ n ↔
      (n : WithTop ℤ) ≤ ord P (a : L) := by
  obtain ⟨⟨b, s⟩, has⟩ := IsLocalization.surj P.asIdeal.primeCompl a
  have hsU : IsUnit (algebraMap (𝓞 L) (LocalRing P) (s : 𝓞 L)) :=
    IsLocalization.map_units (LocalRing P) s
  have hs0 : ord P ((s : 𝓞 L) : L) = 0 :=
    (unitAt_iff_ord_zero P _).mp
      ((unitAt_integer_iff P (s : 𝓞 L)).mpr s.property)
  have hasL : (a : L) * ((s : 𝓞 L) : L) = (b : L) := by
    exact congrArg (fun z : LocalRing P => (z : L)) has
  have hord : ord P (a : L) = ord P (b : L) := by
    have h := congrArg (ord P) hasL
    rw [ord_mul, hs0, add_zero] at h
    exact h
  have hcomap :
      algebraMap (𝓞 L) (LocalRing P) b ∈
        (IsLocalRing.maximalIdeal (LocalRing P)) ^ n ↔ b ∈ P.asIdeal ^ n := by
    change b ∈ ((IsLocalRing.maximalIdeal (LocalRing P)) ^ n).under (𝓞 L) ↔
      b ∈ P.asIdeal ^ n
    rw [IsLocalization.AtPrime.under_maximalIdeal_pow P.asIdeal (LocalRing P) n]
  have hglob : (n : WithTop ℤ) ≤ ord P (b : L) ↔ b ∈ P.asIdeal ^ n := by
    simpa [CongruentPow] using congruentPow_integers_iff P n b 0
  calc
    a ∈ (IsLocalRing.maximalIdeal (LocalRing P)) ^ n ↔
        a * algebraMap (𝓞 L) (LocalRing P) (s : 𝓞 L) ∈
          (IsLocalRing.maximalIdeal (LocalRing P)) ^ n :=
      (Ideal.mul_unit_mem_iff_mem _ hsU).symm
    _ ↔ algebraMap (𝓞 L) (LocalRing P) b ∈
        (IsLocalRing.maximalIdeal (LocalRing P)) ^ n := by rw [has]
    _ ↔ b ∈ P.asIdeal ^ n := hcomap
    _ ↔ (n : WithTop ℤ) ≤ ord P (b : L) := hglob.symm
    _ ↔ (n : WithTop ℤ) ≤ ord P (a : L) := by rw [hord]

end SICLean.L5.PrimeCongruenceAux
