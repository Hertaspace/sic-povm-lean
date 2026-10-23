import SICLean.L2c.Inputs

set_option autoImplicit false

/-! Coordinate transport for the finite special-value identities. -/

noncomputable section

namespace SICLean.L2c

variable (M : ℕ) [Fact (4 ≤ M)]

@[simp] theorem fromSmith_zero : fromSmith M 0 = 0 :=
  (smithEquiv M).symm.map_zero

@[simp] theorem fromSmith_add (x y : L2b.G M) :
    fromSmith M (x + y) = fromSmith M x + fromSmith M y :=
  (smithEquiv M).symm.map_add x y

@[simp] theorem fromSmith_neg (x : L2b.G M) :
    fromSmith M (-x) = -fromSmith M x :=
  (smithEquiv M).symm.map_neg x

@[simp] theorem fromSmith_sub (x y : L2b.G M) :
    fromSmith M (x - y) = fromSmith M x - fromSmith M y :=
  (smithEquiv M).symm.map_sub x y

theorem fromSmith_injective : Function.Injective (fromSmith M) :=
  (smithEquiv M).symm.injective

@[simp] theorem fromSmith_eq_zero (x : L2b.G M) : fromSmith M x = 0 ↔ x = 0 := by
  rw [← fromSmith_zero M]
  exact (fromSmith_injective M).eq_iff

@[simp] theorem gaussian_fromSmith (x : L2b.G M) :
    gaussian M (fromSmith M x) = L2b.gaussian M x := by
  rw [gaussian_eq_smith, toSmith_fromSmith]

@[simp] theorem pairing_fromSmith (x y : L2b.G M) :
    pairing M (fromSmith M x) (fromSmith M y) =
      L2b.metricPairing (L2b.gaussian M) x y := by
  rw [pairing_eq_smith, toSmith_fromSmith, toSmith_fromSmith]

variable {M} {Fplus Fminus : RWGroup M → ℂ}

theorem smith_mixed_reflection (h : Theorem2Input M Fplus Fminus) (x : L2b.G M) :
    smithValues M Fplus x * smithValues M Fminus (-x) = (L2b.gaussian M x)⁻¹ := by
  simpa only [smithValues, Function.comp_apply, fromSmith_neg, gaussian_fromSmith]
    using h.mixed_reflection (fromSmith M x)

theorem smith_agree_off_zero (h : Theorem2Input M Fplus Fminus)
    (x : L2b.G M) (hx : x ≠ 0) : smithValues M Fplus x = smithValues M Fminus x := by
  exact h.agree_off_zero (fromSmith M x) (fun heq => hx ((fromSmith_eq_zero M x).mp heq))

theorem smith_ratio_sum (h : Theorem2Input M Fplus Fminus)
    (u v : L2b.G M) (huv : (u, v) ≠ (0, 0)) :
    L2b.normalizedSum (fun x => L2b.metricPairing (L2b.gaussian M) x u *
      (smithValues M Fplus x / smithValues M Fminus (x + v))) =
      smithValues M Fplus (u + v) /
        (smithValues M Fminus u * smithValues M Fminus v) := by
  have hpair : (fromSmith M u, fromSmith M v) ≠ (0, 0) := by
    intro heq
    apply huv
    apply Prod.ext
    · exact (fromSmith_eq_zero M u).mp (congrArg Prod.fst heq)
    · exact (fromSmith_eq_zero M v).mp (congrArg Prod.snd heq)
  have hr := h.ratio_sum (fromSmith M u) (fromSmith M v) hpair
  rw [normalizedSum_toSmith] at hr
  simpa only [smithValues, Function.comp_def, fromSmith_add, pairing_fromSmith] using hr

end SICLean.L2c
