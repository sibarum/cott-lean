import CottLean.T.Fraction
import Mathlib.Algebra.Polynomial.Inductions

/-!
# A zero that adds a layer

The rule: when a component meets a zero, it gains a layer, and only that component does.

```
(a, b) · (0, 1) = ((0, a), b)
```

Read the inner pair `(x, y)` as `x + ε·y`, not as the fraction `x/y`. Then `(0, a)` is `a·ε`, `(0, (0, a))`
is `a·ε²`, and the layers are Horner form: `c₀ + ε(c₁ + ε(c₂ + …))`. So a coordinate is a polynomial in a
formal `ε`, and a pair is a fraction of two of them.

## The layers

* `Nest.eval_hold`: adding a layer to one component multiplies it by `ε`.
* `Nest.eval_hold_hold`: two layers are `ε²`, so the grade is the power of zero.
* `Nest.eval_hold_injective`: nothing held is lost.
* `Nest.eval_hold_zero`: but the literal `0` held this way is `0·ε`, the additive zero again. So the zero
  that is met has to start out held, as `ε` itself.

## Pairs over `ℤ[ε]`

`TE` is `T` with polynomial coordinates, under the same formulas.

* `of_plus`, `of_times`, `of_neg`: `T` sits inside exactly.
* `of_times_zero`: `x · 0` is the rule. Its numerator is `p` held one layer down.
* `times_omega`: `x · ω` gives the denominator the layer instead.
* `times_zero_injective`, `times_omega_injective`: neither loses anything, where in `T` `x · 0` loses `p`
  (`T.zero_times`).
* `times_injective`, `plus_injective`: nor does `·` by a pair with both coordinates non-zero, or `+` by a
  pair with a non-zero denominator.
* `zero_sq_not_equiv`: `0 · 0` and `0` are different values, so powers of zero are counted.
* `held_zero_not_equiv_zero`: and the held zero is not the additive zero `1 + (−1)` (`one_plus_neg_one`),
  which still erases (`additive_zero_times`).
* `additive_zero_erases`: that last is forced. In any ring, `a · 0 = b · 0`. Only the zero that is met can
  be held; the zero that `+` produces cannot.

## Resolving

* `times_zero_times_omega`, `release_example`: `x · 0 · ω` is `x` as a value. `((0,3),4) · ω = (3ε, 4ε)`,
  which is `(3, 4)`.
* `zero_div_zero`: with a single `ε`, `0/0 = 1`. Every zero met has the same size. Independent zeros would
  need one `ε` each.
* `cancel_step`: a common factor of `ε` cancels exactly, removing one layer from both components.
* `st`: once the denominator no longer vanishes at `ε = 0`, setting `ε = 0` is the standard part. It
  respects `+`, `·` and `−` (`st_plus`, `st_times`, `st_neg`), does not depend on the representative
  (`st_equiv`), and on `T` it is the classical value (`st_of`). A held zero resolves to `0` (`st_zero`).

This is the algebra of a formal infinitesimal, the field of rational functions `ℚ(ε)`, and the standard
part is the limit `ε → 0`. What is particular to the model is that its nested pairs, read by Horner, are
exactly the rule above.
-/

open Polynomial

namespace Epsilon

/-! ## The layers -/

/-- A coordinate built by nesting: an integer, or a pair `(x, y)` read as `x + ε·y`. -/
inductive Nest where
  | leaf (n : ℤ)
  | node (x y : Nest)

namespace Nest

/-- The Horner reading. -/
noncomputable def eval : Nest → ℤ[X]
  | leaf n => C n
  | node x y => x.eval + X * y.eval

/-- `a ↦ (0, a)`: the component that met a zero gains a layer. -/
def hold (a : Nest) : Nest := node (leaf 0) a

theorem eval_hold (a : Nest) : (hold a).eval = X * a.eval := by
  simp [hold, eval]

theorem eval_hold_hold (a : Nest) : (hold (hold a)).eval = X ^ 2 * a.eval := by
  rw [eval_hold, eval_hold]; ring

theorem eval_hold_injective {a b : Nest} (h : (hold a).eval = (hold b).eval) : a.eval = b.eval := by
  rw [eval_hold, eval_hold] at h
  exact mul_left_cancel₀ X_ne_zero h

/-- Holding the literal `0` gives the additive zero back. -/
theorem eval_hold_zero : (hold (leaf 0)).eval = 0 := by
  simp [eval_hold, eval]

end Nest

/-! ## Pairs over `ℤ[ε]` -/

/-- `T` with coordinates in `ℤ[ε]`. -/
@[ext]
structure TE where
  /-- The numerator. -/
  p : ℤ[X]
  /-- The denominator. -/
  q : ℤ[X]

namespace TE

noncomputable instance : Add TE := ⟨fun x y => ⟨x.p * y.q + y.p * x.q, x.q * y.q⟩⟩
noncomputable instance : Mul TE := ⟨fun x y => ⟨x.p * y.p, x.q * y.q⟩⟩
noncomputable instance : Neg TE := ⟨fun x => ⟨-x.p, x.q⟩⟩

@[simp] theorem add_def (x y : TE) : x + y = ⟨x.p * y.q + y.p * x.q, x.q * y.q⟩ := rfl
@[simp] theorem mul_def (x y : TE) : x * y = ⟨x.p * y.p, x.q * y.q⟩ := rfl
@[simp] theorem neg_def (x : TE) : -x = ⟨-x.p, x.q⟩ := rfl

/-- `T(q, p)`. -/
def reciprocal (x : TE) : TE := ⟨x.q, x.p⟩

/-- `1 = (1, 1)`. -/
noncomputable def one : TE := ⟨1, 1⟩
/-- The zero that is met, held: `(ε, 1)`, which is `((0, 1), 1)` by Horner. -/
noncomputable def zero : TE := ⟨X, 1⟩
/-- `ω = (1, ε)`, the reciprocal of the held zero. -/
noncomputable def omega : TE := ⟨1, X⟩

/-- `T(p, q) ↦ (p, q)` with constant coordinates. -/
noncomputable def of (x : T) : TE := ⟨C x.p, C x.q⟩

theorem of_plus (x y : T) : of (x + y) = of x + of y := by
  ext <;> simp [of]

theorem of_times (x y : T) : of (x * y) = of x * of y := by
  ext <;> simp [of]

theorem of_neg (x : T) : of (-x) = -of x := by
  ext <;> simp [of]

/-- `x · 0` is the rule: the numerator is `p` held one layer down. -/
theorem of_times_zero (x : T) : of x * zero = ⟨(Nest.hold (.leaf x.p)).eval, C x.q⟩ := by
  ext <;> simp [of, zero, Nest.eval_hold, Nest.eval, mul_comm]

/-- `x · ω` gives the denominator the layer instead. -/
theorem times_omega (x : TE) : x * omega = ⟨x.p, x.q * X⟩ := by
  ext <;> simp [omega]

theorem times_zero_injective : Function.Injective (· * zero) := by
  intro x y h
  simp only [mul_def, zero, mul_one, TE.mk.injEq] at h
  exact TE.ext (mul_right_cancel₀ X_ne_zero h.1) h.2

theorem times_omega_injective : Function.Injective (· * omega) := by
  intro x y h
  simp only [mul_def, omega, mul_one, TE.mk.injEq] at h
  exact TE.ext h.1 (mul_right_cancel₀ X_ne_zero h.2)

theorem times_injective {k : TE} (hp : k.p ≠ 0) (hq : k.q ≠ 0) : Function.Injective (· * k) := by
  intro x y h
  simp only [mul_def, TE.mk.injEq] at h
  exact TE.ext (mul_right_cancel₀ hp h.1) (mul_right_cancel₀ hq h.2)

theorem plus_injective {k : TE} (hq : k.q ≠ 0) : Function.Injective (· + k) := by
  intro x y h
  simp only [add_def, TE.mk.injEq] at h
  have hQ : x.q = y.q := mul_right_cancel₀ hq h.2
  rw [hQ] at h
  exact TE.ext (mul_right_cancel₀ hq (add_right_cancel h.1)) hQ

/-! ## Values -/

/-- `x` and `y` are the same fraction. -/
def Equiv (x y : TE) : Prop := x.p * y.q = y.p * x.q

/-- `0 · 0` is not `0`. -/
theorem zero_sq_not_equiv : ¬ Equiv (zero * zero) zero := by
  intro h
  have := congrArg (Polynomial.eval 2) h
  simp [zero] at this

theorem one_plus_neg_one : one + -one = ⟨0, 1⟩ := by
  ext <;> simp [one]

/-- The held zero is not the additive zero. -/
theorem held_zero_not_equiv_zero : ¬ Equiv zero (one + -one) := by
  rw [one_plus_neg_one]
  simp [Equiv, zero, X_ne_zero]

/-- The additive zero still erases the numerator. -/
theorem additive_zero_times (x : TE) : (one + -one) * x = ⟨0, x.q⟩ := by
  rw [one_plus_neg_one]; ext <;> simp

/-- In any ring the additive zero erases: `a · 0` does not depend on `a`. -/
theorem additive_zero_erases {R : Type*} [Ring R] (a b : R) : a * 0 = b * 0 := by
  simp

/-! ## Resolving -/

/-- `x · 0 · ω` is `x` as a value. -/
theorem times_zero_times_omega (x : TE) : Equiv (x * zero * omega) x := by
  simp [Equiv, zero, omega]; ring

/-- `((0,3),4) · ω = (3ε, 4ε)`, which is `(3, 4)`. -/
theorem release_example :
    (⟨3 * X, 4⟩ : TE) * omega = ⟨3 * X, 4 * X⟩ ∧ Equiv ⟨3 * X, 4 * X⟩ ⟨3, 4⟩ := by
  refine ⟨by ext <;> simp [omega], ?_⟩
  simp [Equiv]; ring

/-- With a single `ε`, `0/0 = 1`. -/
theorem zero_div_zero : Equiv (zero * reciprocal zero) one := by
  simp [Equiv, zero, reciprocal, one]

/-- A common factor of `ε` cancels, one layer off both components. -/
theorem cancel_step {f g : ℤ[X]} (hf : f.coeff 0 = 0) (hg : g.coeff 0 = 0) :
    f = X * divX f ∧ g = X * divX g ∧ Equiv ⟨f, g⟩ ⟨divX f, divX g⟩ := by
  have ef : f = X * divX f := by
    conv_lhs => rw [← X_mul_divX_add f]
    simp [hf]
  have eg : g = X * divX g := by
    conv_lhs => rw [← X_mul_divX_add g]
    simp [hg]
  refine ⟨ef, eg, ?_⟩
  simp only [Equiv]
  conv_lhs => rw [ef]
  conv_rhs => rw [eg]
  ring

/-! ## The standard part -/

/-- The denominator does not vanish at `ε = 0`. -/
def Finite (x : TE) : Prop := x.q.eval 0 ≠ 0

/-- Set `ε = 0`. -/
noncomputable def st (x : TE) : ℚ := ((x.p.eval 0 : ℤ) : ℚ) / ((x.q.eval 0 : ℤ) : ℚ)

theorem finite_plus {x y : TE} (hx : Finite x) (hy : Finite y) : Finite (x + y) := by
  simp only [Finite, add_def, eval_mul]; exact mul_ne_zero hx hy

theorem finite_times {x y : TE} (hx : Finite x) (hy : Finite y) : Finite (x * y) := by
  simp only [Finite, mul_def, eval_mul]; exact mul_ne_zero hx hy

theorem st_plus {x y : TE} (hx : Finite x) (hy : Finite y) : st (x + y) = st x + st y := by
  have hx' : ((x.q.eval 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : ((y.q.eval 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hy
  simp only [st, add_def, eval_add, eval_mul]
  push_cast
  field_simp

theorem st_times (x y : TE) : st (x * y) = st x * st y := by
  simp only [st, mul_def, eval_mul]
  push_cast
  rw [mul_div_mul_comm]

theorem st_neg (x : TE) : st (-x) = -st x := by
  simp [st, neg_div]

/-- The standard part is a property of the value, not of the representative. -/
theorem st_equiv {x y : TE} (hx : Finite x) (hy : Finite y) (h : Equiv x y) : st x = st y := by
  have hx' : ((x.q.eval 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : ((y.q.eval 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hy
  have h0 := congrArg (Polynomial.eval 0) h
  simp only [eval_mul] at h0
  have h0' : ((x.p.eval 0 : ℤ) : ℚ) * y.q.eval 0 = y.p.eval 0 * x.q.eval 0 := by exact_mod_cast h0
  simp only [st]
  rw [div_eq_div_iff hx' hy']
  linarith

/-- On `T`, it is the classical value. -/
theorem st_of (x : T) : st (of x) = (x.p : ℚ) / x.q := by
  simp [st, of]

/-- A held zero resolves to `0`. -/
theorem st_zero : st zero = 0 := by
  simp [st, zero]

end TE

end Epsilon
