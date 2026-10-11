import CottLean.T.ZeroAlgebra

/-!
# The residual of an exact cancellation

`Z(0, 0)` and `Q(0, 0)` are the absence of a value, and nothing should reach them. Here `Z`'s coefficient is
an unreduced ratio `a : b`, so a value is `Z(a : b, n) = (a/b)·0ⁿ`. A product multiplies the ratios and adds
the orders, so it never makes a coefficient `0` (`value_mul`). The one way in is an exact cancellation, and
there the rule acts on the operands, by distributing: `x − x = (1 − 1)·x = 0·x`, with `1 − 1 = Z(1 : 1, 1)`,
the `0` that has an inverse. So the residual keeps `x` as its coefficient and gains one order
(`add_neg_self`, `cancel_eq`).

| statement | Lean |
|---|---|
| a product never makes a coefficient `0`; it is the exponent law on values | `mul_coeff_ne_zero`, `value_mul` |
| `x − x` is the residual `0·x`, one order up with `x` kept | `add_neg_self`, `cancel_eq` |
| its value depends only on the value of `x`, not on how `x` is written | `value_cancel_congr` |
| the residual over what cancelled is the zero itself | `cancel_div_self` |
| `0/0` is the ratio of what cancelled: `(x − x)/(y − y) = x/y` | `cancel_div_cancel` |
| a sum without exact cancellation is the sum of values, at the same order | `value_add` |
| when two different pairs cancel, either one as coefficient gives the same value; the pair kept is history | `value_cancel_either` |

## Not the denominator

Reading the collapsed pair instead, `(a : b) − (a : b) = (0 : b²)` and `Q(0, n) ↦ Z(n, 1)`, puts the
denominator into the coefficient. Then `3` and `6/2` cancel to `1·0` and `4·0` (`denominator_rule_ne`): equal
inputs, unequal values.

## `+` counts exact cancellations

`(x + x) − x` cancels nothing exactly and gives `x`; `x + (x − x)` cancels once and leaves the residual
(`add_add_neg`, `add_neg_self`). So `+` is not associative: grouping changes how many exact cancellations
happen, and the residuals count them.
-/

namespace T.ZeroScale.Residual

open LaurentPolynomial

/-- `Z(a : b, n) = (a/b)·0ⁿ`, with the coefficient an unreduced ratio. -/
@[ext]
structure R where
  /-- The coefficient, kept unreduced. -/
  c : ℤ × ℤ
  /-- The order of zero. -/
  n : ℤ
  deriving DecidableEq

namespace R

/-- The value in `ℚ[0, 0⁻¹]`. -/
noncomputable def value (x : R) : LaurentPolynomial ℚ := C ((x.c.1 : ℚ) / x.c.2) * T x.n

/-- Ratios multiply and orders add. -/
def mul (x y : R) : R := ⟨(x.c.1 * y.c.1, x.c.2 * y.c.2), x.n + y.n⟩

/-- `(a : b)⁻¹ = (b : a)`, and the order negates. -/
def inv (x : R) : R := ⟨(x.c.2, x.c.1), -x.n⟩

def neg (x : R) : R := ⟨(-x.c.1, x.c.2), x.n⟩

/-- The `0` with an inverse, `Z(1 : 1, 1)`. -/
def zero : R := ⟨(1, 1), 1⟩

/-- `0·x`: the residual of cancelling `x`. -/
def cancel (x : R) : R := ⟨x.c, x.n + 1⟩

/-- `+` at `x`'s order. An exact cancellation leaves the residual `0·x`; otherwise fraction `+`. -/
def add (x y : R) : R :=
  if x.c.1 * y.c.2 + x.c.2 * y.c.1 = 0 then cancel x
  else ⟨(x.c.1 * y.c.2 + x.c.2 * y.c.1, x.c.2 * y.c.2), x.n⟩

theorem mul_coeff_ne_zero {x y : R} (hx : x.c.1 ≠ 0 ∧ x.c.2 ≠ 0) (hy : y.c.1 ≠ 0 ∧ y.c.2 ≠ 0) :
    (mul x y).c.1 ≠ 0 ∧ (mul x y).c.2 ≠ 0 :=
  ⟨mul_ne_zero hx.1 hy.1, mul_ne_zero hx.2 hy.2⟩

theorem value_mul (x y : R) : (mul x y).value = x.value * y.value := by
  simp only [value, mul, Int.cast_mul]
  rw [← div_mul_div_comm, map_mul, T_add]; ring

theorem add_neg_self (x : R) : add x (neg x) = cancel x := by
  unfold add; rw [if_pos (by simp [neg]; ring)]

/-- The residual is `0·x`. -/
theorem cancel_eq (x : R) : cancel x = mul zero x := by
  ext <;> simp [cancel, mul, zero, add_comm]

theorem value_cancel (x : R) : (cancel x).value = zero.value * x.value := by
  rw [cancel_eq, value_mul]

/-- Equal values cancel to equal residuals. -/
theorem value_cancel_congr {x y : R} (h : x.value = y.value) : (cancel x).value = (cancel y).value := by
  rw [value_cancel, value_cancel, h]

/-- The residual over what cancelled is the zero. -/
theorem cancel_div_self {x : R} (ha : x.c.1 ≠ 0) (hb : x.c.2 ≠ 0) :
    (mul (cancel x) (inv x)).value = zero.value := by
  simp only [value, mul, cancel, inv, zero, Int.cast_mul, Int.cast_one, div_one, map_one, one_mul]
  have : T (x.n + 1 + -x.n) = (T 1 : LaurentPolynomial ℚ) := by congr 1; ring
  rw [this]
  have ha' : (x.c.1 : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (x.c.2 : ℚ) ≠ 0 := by exact_mod_cast hb
  rw [show ((x.c.1 : ℚ) * x.c.2) / (x.c.2 * x.c.1) = 1 by field_simp, map_one, one_mul]

/-- `0/0` is the ratio of what cancelled. -/
theorem cancel_div_cancel (x y : R) :
    (mul (cancel x) (inv (cancel y))).value = (mul x (inv y)).value := by
  simp only [value, mul, cancel, inv]
  congr 2; ring

/-- Without an exact cancellation, `+` is the sum of values. -/
theorem value_add {x y : R} (hn : x.n = y.n) (hx : x.c.2 ≠ 0) (hy : y.c.2 ≠ 0)
    (h : x.c.1 * y.c.2 + x.c.2 * y.c.1 ≠ 0) : (add x y).value = x.value + y.value := by
  have hx' : (x.c.2 : ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y.c.2 : ℚ) ≠ 0 := by exact_mod_cast hy
  simp only [add, if_neg h, value, ← hn, ← add_mul, ← map_add, Int.cast_add, Int.cast_mul]
  congr 2; field_simp

/-- When `x` and `y` cancel exactly, the residual of `x` and of `−y` have the same value. -/
theorem value_cancel_either {x y : R} (hn : x.n = y.n) (hx : x.c.2 ≠ 0) (hy : y.c.2 ≠ 0)
    (h : x.c.1 * y.c.2 + x.c.2 * y.c.1 = 0) : (cancel x).value = (cancel (neg y)).value := by
  have hx' : (x.c.2 : ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y.c.2 : ℚ) ≠ 0 := by exact_mod_cast hy
  have h' : (x.c.1 : ℚ) * y.c.2 + x.c.2 * y.c.1 = 0 := by exact_mod_cast h
  simp only [value, cancel, neg, ← hn, Int.cast_neg]
  congr 2; field_simp; linarith

/-- `1 = Z(1 : 1, 0)`. -/
def one : R := ⟨(1, 1), 0⟩

/-- `(1 + 1) − 1` cancels nothing exactly. -/
theorem add_add_neg : add (add one one) (neg one) = ⟨(1, 1), 0⟩ := by decide

/-- `1 − 1` cancels once: the residual `0`. -/
theorem add_one_neg : add one (neg one) = zero := by decide

/-! ## Not the denominator -/

/-- The collapsed pair's reading: `(a : b) − (a : b) = (0 : b²) ↦ Z(b² : 1, 1)`. -/
def denominatorRule (x : R) : R := ⟨(x.c.2 * x.c.2, 1), x.n + 1⟩

/-- `3` and `6/2` have one value, and the denominator rule cancels them to `1·0` and `4·0`. -/
theorem denominator_rule_ne :
    (⟨(3, 1), 0⟩ : R).value = (⟨(6, 2), 0⟩ : R).value ∧
      (denominatorRule ⟨(3, 1), 0⟩).value ≠ (denominatorRule ⟨(6, 2), 0⟩).value := by
  refine ⟨by norm_num [value], ?_⟩
  simp only [value, denominatorRule, ← single_eq_C_mul_T]
  intro h
  have := congrArg (fun f : LaurentPolynomial ℚ => f.coeff 1) h
  norm_num [AddMonoidAlgebra.coeff_single, -single_eq_C_mul_T] at this

end R

end T.ZeroScale.Residual
