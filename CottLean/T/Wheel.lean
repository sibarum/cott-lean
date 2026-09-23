import CottLean.T.ValuePosition
import CottLean.T.Gaussian

/-!
# The value position is a wheel

A wheel (Carlström, *Wheels -- On Division by Zero*, 2004) is a set with `0`, `1`, `+`, `·` and a unary
`/`, satisfying the eight axioms of `IsWheel` below, where `x / y` means `x · /y`. His standard example,
the wheel of fractions, is built on pairs with exactly T's value-position formulas:

```
(x,y) + (x',y') = (xy' + x'y, yy')      (x,y)·(x',y') = (xx', yy')      /(x,y) = (y,x)
```

and then takes a quotient, identifying `(x,y)` with `(sx,sy)`. T takes no quotient. The theorem here is
that none is needed: `(T, 0, 1, +, *, reciprocal)` satisfies every axiom at coordinate equality, with
`0 = T(0,1)` and `1 = T(1,1)`.

The wheel's bottom element is `0/0`, and in T that is `0ω`. So `0ω` is the wheel's `⊥` exactly, and
whatever wheel theory proves about `⊥` from the axioms holds of it. What wheel theory does not cover is
`⊕` and `⊗`, and the last section records what `0ω` does there, without reading anything into it.

The axiom list is checked against the statements on Wikipedia's "Wheel theory" and nLab's "wheel", which
agree with each other; nLab also lists `/1 = 1`, included here. Carlström's paper itself was not read.
-/

/-- The wheel axioms, for `x / y := x · /y`. -/
structure IsWheel {H : Type} (zero one : H) (add mul : H → H → H) (inv : H → H) : Prop where
  /-- `⟨H, 0, +⟩` is a commutative monoid. -/
  add_comm : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  zero_add : ∀ x, add zero x = x
  /-- `⟨H, 1, ·, /⟩` is a commutative monoid with an involution. -/
  mul_comm : ∀ x y, mul x y = mul y x
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x, mul one x = x
  inv_inv : ∀ x, inv (inv x) = x
  inv_mul : ∀ x y, inv (mul x y) = mul (inv x) (inv y)
  /-- `/1 = 1`, listed by nLab and not by Wikipedia. -/
  inv_one : inv one = one
  /-- `xz + yz = (x + y)z + 0z` -/
  distrib : ∀ x y z, add (mul x z) (mul y z) = add (mul (add x y) z) (mul zero z)
  /-- `x/y + z + 0y = (x + yz)/y` -/
  div_add : ∀ x y z,
    add (add (mul x (inv y)) z) (mul zero y) = mul (add x (mul y z)) (inv y)
  /-- `0·0 = 0` -/
  zero_mul_zero : mul zero zero = zero
  /-- `(x + 0y)z = xz + 0y` -/
  add_zero_mul : ∀ x y z, mul (add x (mul zero y)) z = add (mul x z) (mul zero y)
  /-- `/(x + 0y) = /x + 0y` -/
  inv_add_zero : ∀ x y, inv (add x (mul zero y)) = add (inv x) (mul zero y)
  /-- `0/0 + x = 0/0` -/
  bottom_add : ∀ x, add (mul zero (inv zero)) x = mul zero (inv zero)

namespace T

/-- The value position of T is a wheel, at coordinate equality. -/
theorem isWheel : IsWheel (0 : T) «1» (· + ·) (· * ·) reciprocal where
  add_comm := plus_comm
  add_assoc := plus_assoc
  zero_add x := by rw [plus_comm]; exact plus_zero x
  mul_comm := times_comm
  mul_assoc := times_assoc
  one_mul x := by rw [times_comm]; exact times_one x
  inv_inv := reciprocal_reciprocal
  inv_mul := reciprocal_times
  inv_one := rfl
  distrib x y z := by ext <;> simp <;> ring
  div_add x y z := by ext <;> simp only [add_def, mul_def, zero_def, reciprocal] <;> ring
  zero_mul_zero := by decide
  add_zero_mul x y z := by ext <;> simp <;> ring
  inv_add_zero x y := by ext <;> simp [reciprocal]
  bottom_add x := by ext <;> simp [reciprocal]

/-! ## The bottom element -/

/-- The wheel's `⊥ = 0/0` is `0ω`. -/
theorem bottom_eq : (0 : T) * reciprocal 0 = «0ω» := by decide

/-- And `0·ω` is the same element. -/
theorem zero_times_omega : (0 : T) * «ω» = «0ω» := by decide

theorem zeroOmega_plus (x : T) : «0ω» + x = «0ω» := by ext <;> simp [«0ω»]
theorem zeroOmega_times (x : T) : «0ω» * x = «0ω» := by ext <;> simp [«0ω»]

/-! ## What `0ω` does beyond the wheel

Recorded, not interpreted. -/

/-- Under `⊗` it absorbs, as it does under `+` and `*`. -/
theorem zeroOmega_otimes (x : T) : «0ω» ⊗ x = «0ω» := by ext <;> simp [otimes, «0ω»]

/-- Under `⊕` it is the identity. -/
theorem zeroOmega_oplus (x : T) : («0ω» ⊕ x) = x := by rw [oplus_comm]; exact oplus_zeroOmega x

/-- Every inverse leaves it where it is. -/
theorem zeroOmega_fixed :
    reciprocal «0ω» = «0ω» ∧ -«0ω» = «0ω» ∧ oplusInverse «0ω» = «0ω» := by decide

/-- And it is the only pair every inverse leaves where it is. -/
theorem fixed_by_all_inverses_iff (x : T) :
    (reciprocal x = x ∧ -x = x ∧ oplusInverse x = x) ↔ x = «0ω» := by
  constructor
  · rintro ⟨h1, h2, -⟩
    have hp := congrArg T.p h2
    have hq := congrArg T.p h1
    simp [reciprocal] at hp hq
    ext <;> simp [«0ω»] <;> omega
  · rintro rfl; exact zeroOmega_fixed

end T
