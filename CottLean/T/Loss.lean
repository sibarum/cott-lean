import CottLean.T.Projection

/-!
# What a product loses, exactly

`Norm` says when a product can be undone against `k`: exactly when `N(k) ≠ 0`. This file says what is
lost when it cannot. Against `k ≠ 0ω` with `N(k) = 0`, every product in the family keeps exactly one
integer of the other operand and loses the rest, and one more integer, kept beside the result, gives the
operand back.

For `ω² = a + b·ω`, the key identity (`numerator_determines`) is that every result `r = x · k` satisfies

```
k.p · r.q − k.q · r.p = −x.p · N(k)
```

So where `N(k) = 0` and `k ≠ 0ω`, which forces `k.p ≠ 0`, the result's denominator is fixed by its
numerator. The whole result is one integer, `r.p = x.p·k.q + k.p·x.q + b·x.p·k.p`, a linear form in `x`
(`qtimes_eq_qtimes_iff`). Two operands give the same result exactly when that form agrees, and keeping
`x.p` alongside the result is enough to recover `x` (`qtimes_recover_with_numerator`).

Read off for each product:

| product | loses against | keeps | lost, and what to keep |
|---|---|---|---|
| `⊗` | only `0ω` | everything else | -- |
| `+` | `T(c, 0)`, `c ≠ 0` | `x.q` | `x.p` (`plus_eq_plus_iff_of_q_eq_zero`) |
| `⊚` | `T(c, c)` | `x.q + x.p` | `x.q − x.p` (`splitTimes_eq_splitTimes_iff_of_p_eq_q`) |
| `⊚` | `T(c, −c)` | `x.q − x.p` | `x.q + x.p` (`splitTimes_eq_splitTimes_iff_of_p_eq_neg_q`) |
| `*` | `T(c, 0)` | `x.p` | `x.q` (`times_eq_times_iff_of_q_eq_zero`) |
| `*` | `T(0, c)` | `x.q` | `x.p` (`times_eq_times_iff_of_p_eq_zero`) |
| `∥` | `T(0, c)`, `c ≠ 0` | `x.p` | `x.q` (`par_eq_par_iff_of_p_eq_zero`) |

Under `⊚` the two light lines keep the two light-cone coordinates, so what one light line loses, the
other keeps. So a reversible use of any of these products, against anything but `0ω`, needs at most one
integer of state beyond the result. Against `0ω` every result is `0ω`, and both integers are lost.
-/

namespace T

/-! ## The whole family -/

/-- A result's denominator against `k` differs from what its numerator predicts by `x.p · N(k)`. -/
theorem numerator_determines (a b : ℤ) (x k : T) :
    k.p * (qtimes a b x k).q - k.q * (qtimes a b x k).p =
      -x.p * (k.q ^ 2 + b * k.p * k.q - a * k.p ^ 2) := by
  simp only [qtimes]; ring

/-- A pair of norm zero other than `0ω` has a non-zero numerator. -/
theorem p_ne_zero_of_norm_eq_zero {a b : ℤ} {k : T} (hN : k.q ^ 2 + b * k.p * k.q - a * k.p ^ 2 = 0)
    (hk : k ≠ «0ω») : k.p ≠ 0 := by
  intro hp
  apply hk
  have : k.q ^ 2 = 0 := by rw [hp] at hN; simpa using hN
  ext
  · exact hp
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- Against a zero divisor, the result is its numerator: two operands agree exactly when that does. -/
theorem qtimes_eq_qtimes_iff {a b : ℤ} {k : T} (hN : k.q ^ 2 + b * k.p * k.q - a * k.p ^ 2 = 0)
    (hk : k ≠ «0ω») (x x' : T) :
    qtimes a b x k = qtimes a b x' k ↔ (qtimes a b x k).p = (qtimes a b x' k).p := by
  refine ⟨congrArg T.p, fun h => ?_⟩
  have hp := p_ne_zero_of_norm_eq_zero hN hk
  have e := numerator_determines a b x k
  have e' := numerator_determines a b x' k
  rw [hN, mul_zero] at e e'
  ext
  · exact h
  · apply mul_left_cancel₀ hp
    linear_combination e - e' + k.q * h

/-- And the operand's numerator, kept beside the result, gives the operand back. -/
theorem qtimes_recover_with_numerator {a b : ℤ} {k : T}
    (hN : k.q ^ 2 + b * k.p * k.q - a * k.p ^ 2 = 0) (hk : k ≠ «0ω») {x x' : T}
    (h : qtimes a b x k = qtimes a b x' k) (hp : x.p = x'.p) : x = x' := by
  have hk' := p_ne_zero_of_norm_eq_zero hN hk
  have h1 := congrArg T.p h
  simp only [qtimes] at h1
  ext
  · exact hp
  · apply mul_left_cancel₀ hk'
    rw [hp] at h1
    linarith

/-! ## Read off for each product -/

/-- `+` against `T(c, 0)` keeps the denominator and loses the numerator. -/
theorem plus_eq_plus_iff_of_q_eq_zero {k : T} (hq : k.q = 0) (hp : k.p ≠ 0) (x x' : T) :
    x + k = x' + k ↔ x.q = x'.q := by
  simp only [add_def, hq, T.mk.injEq, mul_zero, zero_add, and_true]
  exact mul_right_inj' hp

/-- `⊚` against `T(c, c)` keeps the light-cone coordinate `q + p`. -/
theorem splitTimes_eq_splitTimes_iff_of_p_eq_q {k : T} (h : k.p = k.q) (hk : k ≠ «0ω») (x x' : T) :
    x ⊚ k = x' ⊚ k ↔ x.q + x.p = x'.q + x'.p := by
  have hN : k.q ^ 2 + 0 * k.p * k.q - 1 * k.p ^ 2 = 0 := by rw [h]; ring
  have hp := p_ne_zero_of_norm_eq_zero hN hk
  rw [splitTimes, splitTimes, qtimes_eq_qtimes_iff hN hk]
  simp only [qtimes, zero_mul, add_zero]
  rw [← h]
  constructor
  · intro e; apply mul_left_cancel₀ hp; linear_combination e
  · intro e; linear_combination k.p * e

/-- `⊚` against `T(c, −c)` keeps the other light-cone coordinate, `q − p`. -/
theorem splitTimes_eq_splitTimes_iff_of_p_eq_neg_q {k : T} (h : k.p = -k.q) (hk : k ≠ «0ω»)
    (x x' : T) : x ⊚ k = x' ⊚ k ↔ x.q - x.p = x'.q - x'.p := by
  have hN : k.q ^ 2 + 0 * k.p * k.q - 1 * k.p ^ 2 = 0 := by rw [h]; ring
  have hp := p_ne_zero_of_norm_eq_zero hN hk
  rw [splitTimes, splitTimes, qtimes_eq_qtimes_iff hN hk]
  simp only [qtimes, zero_mul, add_zero]
  have hq : k.q = -k.p := by rw [h]; ring
  rw [hq]
  constructor
  · intro e; apply mul_left_cancel₀ hp; linear_combination e
  · intro e; linear_combination k.p * e

/-- `∥` against `T(0, c)` keeps the numerator and loses the denominator. -/
theorem par_eq_par_iff_of_p_eq_zero {k : T} (hp : k.p = 0) (hq : k.q ≠ 0) (x x' : T) :
    x ∥ k = x' ∥ k ↔ x.p = x'.p := by
  simp only [par, hp, T.mk.injEq, mul_zero, zero_mul, add_zero, true_and]
  exact mul_left_inj' hq

end T
