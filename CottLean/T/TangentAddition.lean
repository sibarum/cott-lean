import CottLean.T.Recovery
import CottLean.T.Powers
import CottLean.T.Wheel

/-!
# `⊗` is the wheel's tangent addition, without the wheel's collapse

The two halves of T meet here. `⊗` adds angles, and the classical formula for adding angles is
`tan(α + β) = (tan α + tan β) / (1 − tan α · tan β)`. Written with the wheel's own operations -- the value
position's `+`, `*`, `-` and reciprocal -- that is `tanAdd` below, and it is `x ⊗ y` with both coordinates
multiplied by `x.q · y.q` (`tanAdd_eq`).

Where that factor is not zero, the two agree up to it. Where it is zero -- one of the angles is a quarter
turn, or `0ω` -- the wheel's formula lands on its bottom element `0ω` whatever the other angle was, while
`⊗` loses nothing: `ω ⊗ y` is a quarter turn of `y`, and `y` can be read back from it
(`quarterTurn_contrast`).

A quarter turn in the RESULT is not a problem for the wheel: `tanAdd 1 1` is `T(2,0)`, which is the
wheel's `2/0` and `⊗`'s answer too. The collapse is at a quarter turn in an ARGUMENT, where the classical
formula multiplies an infinite tangent by the other one.
-/

namespace T

/-- `(x + y) / (1 − x·y)`, in the value position's operations. -/
def tanAdd (x y : T) : T := (x + y) * reciprocal («1» + -(x * y))

/-- The wheel's tangent addition is `⊗` with both coordinates multiplied by `x.q · y.q`. -/
theorem tanAdd_eq (x y : T) : tanAdd x y = scale (x.q * y.q) (x ⊗ y) := by
  ext <;> simp only [tanAdd, add_def, mul_def, neg_def, reciprocal, scale, otimes, «1»] <;> ring

/-- Where the denominators multiply to one, they agree exactly. -/
theorem tanAdd_of_q_mul_eq_one {x y : T} (h : x.q * y.q = 1) : tanAdd x y = x ⊗ y := by
  rw [tanAdd_eq, h, scale_one]

/-! ## Where each lands on `0ω` -/

theorem scale_eq_zeroOmega_iff (k : ℤ) (z : T) : scale k z = «0ω» ↔ k = 0 ∨ z = «0ω» := by
  constructor
  · intro h
    have hp : k * z.p = 0 := congrArg T.p h
    have hq : k * z.q = 0 := congrArg T.q h
    by_cases hk : k = 0
    · exact Or.inl hk
    · right
      ext
      · exact (mul_eq_zero.mp hp).resolve_left hk
      · exact (mul_eq_zero.mp hq).resolve_left hk
  · rintro (rfl | rfl) <;> ext <;> simp [scale, «0ω»]

/-- `⊗` lands on `0ω` only from `0ω`: the exponent position has no zero divisors. -/
theorem otimes_eq_zeroOmega_iff (x y : T) : x ⊗ y = «0ω» ↔ x = «0ω» ∨ y = «0ω» := by
  constructor
  · intro h
    have := congrArg toGaussian h
    rw [toGaussian_otimes, toGaussian_zeroOmega] at this
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (toGaussian_injective (h.trans toGaussian_zeroOmega.symm))
    · exact Or.inr (toGaussian_injective (h.trans toGaussian_zeroOmega.symm))
  · rintro (rfl | rfl)
    · exact zeroOmega_otimes y
    · rw [otimes_comm]; exact zeroOmega_otimes x

/-- The wheel's formula lands on `0ω` exactly when a denominator is zero. -/
theorem tanAdd_eq_zeroOmega_iff (x y : T) : tanAdd x y = «0ω» ↔ x.q = 0 ∨ y.q = 0 := by
  rw [tanAdd_eq, scale_eq_zeroOmega_iff, otimes_eq_zeroOmega_iff, mul_eq_zero]
  constructor
  · rintro ((h | h) | (rfl | rfl))
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro h
    exact Or.inl h

/-! ## The contrast -/

/-- At a quarter turn, the wheel's formula forgets the other angle entirely, and `⊗` forgets nothing. -/
theorem quarterTurn_contrast {x : T} (hq : x.q = 0) (hx : x ≠ «0ω») :
    (∀ y, tanAdd x y = «0ω») ∧ (∀ y y', x ⊗ y = x ⊗ y' → y = y') := by
  refine ⟨fun y => (tanAdd_eq_zeroOmega_iff x y).mpr (Or.inl hq), fun y y' h => ?_⟩
  have hr := (otimes_recoverable_iff x).mpr hx
  exact hr y y' (by rw [otimes_comm y x, otimes_comm y' x]; exact h)

example : «ω» ⊗ «1» = «_1» := by decide
example : tanAdd «ω» «1» = «0ω» := by decide
/-- `tan(45° + 45°)`: the classical formula divides by zero, and the wheel and `⊗` both answer `T(2,0)`. -/
example : tanAdd «1» «1» = ⟨2, 0⟩ ∧ «1» ⊗ «1» = ⟨2, 0⟩ := by decide

/-! ## And the classical formula it is -/

/-- Over the rationals, where every denominator is nonzero, the tangent addition formula is the
coordinate formula of `⊗`. -/
theorem tan_add_classical {a b c d : ℚ} (hb : b ≠ 0) (hd : d ≠ 0) (h : b * d - a * c ≠ 0) :
    (a / b + c / d) / (1 - a / b * (c / d)) = (a * d + c * b) / (b * d - a * c) := by
  have h1 : 1 - a / b * (c / d) = (b * d - a * c) / (b * d) := by field_simp
  rw [h1, div_add_div _ _ hb hd, div_div_div_cancel_right₀ (mul_ne_zero hb hd)]
  ring

end T
