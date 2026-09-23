import CottLean.T.Quadratic
import CottLean.T.TangentAddition

/-!
# `⊚` is the wheel's velocity addition, without the wheel's collapse

`⊗` adds circular angles, and read as a ratio it is the tangent addition `(u + v) / (1 − uv)`.
`⊚` adds hyperbolic angles, which are rapidities, and read as a ratio it is relativistic velocity
addition:

```
velAdd(u, v) = (u + v) / (1 + u·v)
```

That is `tanh(φ + ψ)` from `tanh φ` and `tanh ψ`, with `1` as the speed of light. Written with the value
position's operations it is `x ⊚ y` with both coordinates multiplied by `x.q · y.q` (`velAdd_eq`), the
same factor as for `⊗` (`tanAdd_eq`).

## Three places the formula divides by zero

* **`uv = −1`: a pole, not a collapse.** `1 + uv = 0`, so the answer is on the axis, `T(k, 0)`. `⊚` and the
  wheel both answer it and agree, as `tan(45° + 45°)` does for `⊗`.
* **An argument with `q = 0`: the wheel's collapse.** The wheel's formula lands on `0ω` whatever the other
  argument was, and `⊚` loses nothing (`infinity_contrast`). This is `quarterTurn_contrast` again.
* **Opposite light lines: `⊚`'s own collapse.** Unlike `⊗`, `⊚` has zero divisors. In light-cone coordinates
  `(q + p, q − p)` it multiplies coordinatewise (`lightCone_splitTimes`). So `x ⊚ y = 0ω` exactly when each
  light-cone coordinate is zero in one of the two (`splitTimes_eq_zeroOmega_iff`), for example
  `1 ⊚ -1 = 0ω`. That is `c` plus `−c`, where the classical formula is `0/0` too. Here `⊚` agrees with the
  wheel, and the loss is real: `⊚` cannot be undone against a light-like pair (`splitTimes_recoverable_iff`).

`1` is the speed of light exactly: `1 ⊚ y` is a multiple of `1` for every `y` (`one_splitTimes`).
-/

namespace T

/-- `(x + y) / (1 + x·y)`, in the value position's operations. -/
def velAdd (x y : T) : T := (x + y) * reciprocal («1» + x * y)

/-- The wheel's velocity addition is `⊚` with both coordinates multiplied by `x.q · y.q`. -/
theorem velAdd_eq (x y : T) : velAdd x y = scale (x.q * y.q) (x ⊚ y) := by
  ext <;> simp only [velAdd, splitTimes, qtimes, add_def, mul_def, reciprocal, scale, «1»] <;> ring

/-- Where the denominators multiply to one, they agree exactly. -/
theorem velAdd_of_q_mul_eq_one {x y : T} (h : x.q * y.q = 1) : velAdd x y = x ⊚ y := by
  rw [velAdd_eq, h, scale_one]

/-! ## The light cone -/

/-- The light-cone coordinates `(q + p, q − p)`, where `⊚` is coordinatewise. -/
def lightCone (x : T) : ℤ × ℤ := (x.q + x.p, x.q - x.p)

theorem lightCone_splitTimes (x y : T) : lightCone (x ⊚ y) = lightCone x * lightCone y := by
  ext <;> simp [lightCone, splitTimes, qtimes] <;> ring

theorem lightCone_eq_zero_iff (z : T) : lightCone z = 0 ↔ z = «0ω» := by
  simp only [lightCone, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, T.ext_iff, «0ω»]
  omega

/-- `⊚` lands on `0ω` exactly when each light-cone coordinate is zero in one of the two. -/
theorem splitTimes_eq_zeroOmega_iff (x y : T) :
    x ⊚ y = «0ω» ↔ (x.q + x.p = 0 ∨ y.q + y.p = 0) ∧ (x.q = x.p ∨ y.q = y.p) := by
  rw [← lightCone_eq_zero_iff, lightCone_splitTimes, Prod.ext_iff]
  simp [lightCone, mul_eq_zero, sub_eq_zero]

/-- `c` and `−c`: the two light lines multiply to `0ω`. -/
example : «1» ⊚ «-1» = «0ω» := by decide

/-- The wheel's formula lands on `0ω` where a denominator is zero, and where `⊚` does. -/
theorem velAdd_eq_zeroOmega_iff (x y : T) : velAdd x y = «0ω» ↔
    x.q = 0 ∨ y.q = 0 ∨ ((x.q + x.p = 0 ∨ y.q + y.p = 0) ∧ (x.q = x.p ∨ y.q = y.p)) := by
  rw [velAdd_eq, scale_eq_zeroOmega_iff, splitTimes_eq_zeroOmega_iff, mul_eq_zero, or_assoc]

/-- `uv = −1` is a pole: `T(2,1)` and `T(-1,2)` give `T(3,0)` by `⊚`, and the wheel agrees up to `2`. -/
example : (⟨2, 1⟩ : T) ⊚ ⟨-1, 2⟩ = ⟨3, 0⟩ ∧ velAdd ⟨2, 1⟩ ⟨-1, 2⟩ = ⟨6, 0⟩ := by decide

/-! ## The speed of light -/

/-- `1 ⊚ y` is `1` scaled: adding any velocity to light gives light. -/
theorem one_splitTimes (y : T) : «1» ⊚ y = scale (y.q + y.p) «1» := by
  ext <;> simp [splitTimes, qtimes, scale, «1»]

/-- `ω ⊚ y` is the reciprocal of `y`, where `ω ⊗ y` is the reciprocal of `-y`
(`reciprocal_eq_omega_otimes_neg`). -/
theorem omega_splitTimes (y : T) : «ω» ⊚ y = reciprocal y := by
  ext <;> simp [splitTimes, qtimes, reciprocal, «ω»]

/-! ## What `⊚` can undo -/

/-- `-x` is the split conjugate too, and a pair against it is the split norm `q² − p²`. -/
theorem splitTimes_neg_self (x : T) : x ⊚ -x = ⟨0, x.q ^ 2 - x.p ^ 2⟩ := by
  ext <;> simp [splitTimes, qtimes]; ring

/-- The inverse up to the norm, as `otimes_otimes_neg` is for `⊗`. -/
theorem splitTimes_splitTimes_neg (a k : T) : (a ⊚ k) ⊚ -k = scale (k.q ^ 2 - k.p ^ 2) a := by
  ext <;> simp [splitTimes, qtimes, scale] <;> ring

/-- Against `k`, the other operand comes back exactly when `k` is not light-like. -/
theorem splitTimes_recoverable_iff (k : T) : Recoverable splitTimes k ↔ k.p ^ 2 ≠ k.q ^ 2 := by
  constructor
  · intro h hk
    -- On a light line, the pair on the other line takes `k` to `0ω`, as `0ω` does.
    have hk' : k.p = k.q ∨ k.p = -k.q := sq_eq_sq_iff_eq_or_eq_neg.mp hk
    rcases hk' with hk' | hk'
    · have := h «-1» «0ω» (by ext <;> simp [splitTimes, qtimes, «-1», «0ω», hk'])
      exact absurd this (by decide)
    · have := h «1» «0ω» (by ext <;> simp [splitTimes, qtimes, «1», «0ω», hk'])
      exact absurd this (by decide)
  · intro hk a a' h
    have hn : k.q ^ 2 - k.p ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
    have hs := congrArg (· ⊚ -k) h
    simp only [splitTimes_splitTimes_neg] at hs
    ext
    · exact mul_left_cancel₀ hn (congrArg T.p hs)
    · exact mul_left_cancel₀ hn (congrArg T.q hs)

/-! ## The contrast -/

/-- At infinite speed, the wheel's formula forgets the other velocity entirely, and `⊚` forgets nothing. -/
theorem infinity_contrast {x : T} (hq : x.q = 0) (hx : x ≠ «0ω») :
    (∀ y, velAdd x y = «0ω») ∧ (∀ y y', x ⊚ y = x ⊚ y' → y = y') := by
  refine ⟨fun y => (velAdd_eq_zeroOmega_iff x y).mpr (Or.inl hq), fun y y' h => ?_⟩
  have hp : x.p ≠ 0 := fun hp => hx (by ext <;> simp [hp, hq, «0ω»])
  have hr := (splitTimes_recoverable_iff x).mpr (by rw [hq]; simpa using hp)
  have comm : ∀ z, x ⊚ z = z ⊚ x := fun z => by
    ext <;> simp [splitTimes, qtimes] <;> ring
  exact hr y y' (by rw [← comm y, ← comm y']; exact h)

example : «ω» ⊚ «1» = «1» := by decide
example : velAdd «ω» «1» = «0ω» := by decide

/-! ## And the classical formula it is -/

/-- Over the rationals, where every denominator is nonzero, velocity addition is the coordinate formula
of `⊚`. -/
theorem velAdd_classical {a b c d : ℚ} (hb : b ≠ 0) (hd : d ≠ 0) (h : b * d + a * c ≠ 0) :
    (a / b + c / d) / (1 + a / b * (c / d)) = (a * d + c * b) / (b * d + a * c) := by
  have h1 : 1 + a / b * (c / d) = (b * d + a * c) / (b * d) := by field_simp
  rw [h1, div_add_div _ _ hb hd, div_div_div_cancel_right₀ (mul_ne_zero hb hd)]
  ring

end T
