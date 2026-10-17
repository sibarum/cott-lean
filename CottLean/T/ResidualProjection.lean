import CottLean.T.Residual

/-!
# The residual's laws, and the projection that restores them

`T/Residual.lean`'s `+` keeps what cancelled, and so loses laws. This file asks whether the loss is isolated
and comes back under a projection.

| statement | Lean |
|---|---|
| the standard part `st`, the coefficient at order `0`, carries `+` and `·` to `ℚ` on finite elements | `st_add`, `st_mul` |
| off an exact cancellation `+` is commutative, and at one order associative | `add_comm_of_noCancel`, `add_assoc_of_noCancel` |
| at an exact cancellation both fail: `1 − 1 = 0·1` but `−1 + 1 = 0·(−1)`, and `(1 + 1) − 2 = 0·2` but `1 + (1 − 2) = 0·1` | `add_not_comm`, `add_not_assoc` |
| the failures are invisible to `st` | `st_add_comm`, `st_add_assoc` |
| `·` distributes over `+` on values, exact cancellations included | `value_mul_add` |
| any projection carrying `+` to an associative operation sends `0·n` to `0·1` for every positive integer `n`, and to a commutative one sends `0·1` to `0·(−1)` | `forgets_cancelled`, `forgets_sign` |

So the loss is isolated and `st` restores the laws, but no lawful projection keeps what cancelled. What
the residual holds is visible only to readings that are themselves not associative.
-/

namespace T.ZeroScale.Residual

open LaurentPolynomial

namespace R

/-- Neither coordinate of the coefficient is `0`. -/
def WF (x : R) : Prop := x.c.1 ≠ 0 ∧ x.c.2 ≠ 0

theorem wf_neg {x : R} (h : x.WF) : (neg x).WF := ⟨by simpa [neg] using h.1, h.2⟩

theorem wf_cancel {x : R} (h : x.WF) : (cancel x).WF := h

theorem wf_mul {x y : R} (hx : x.WF) (hy : y.WF) : (mul x y).WF := mul_coeff_ne_zero hx hy

theorem wf_add {x y : R} (hx : x.WF) (hy : y.WF) : (add x y).WF := by
  unfold add; split_ifs with h1 h2 h3
  · exact hx
  · exact hy
  · exact hx
  · exact ⟨h3, mul_ne_zero hx.2 hy.2⟩

theorem n_add_nonneg {x y : R} (fx : 0 ≤ x.n) (fy : 0 ≤ y.n) : 0 ≤ (add x y).n := by
  rcases lt_trichotomy x.n y.n with h | hn | h
  · rw [add_of_lt h]; exact fx
  · by_cases hc : x.c.1 * y.c.2 + x.c.2 * y.c.1 = 0
    · rw [add_of_cancel hn hc]; simp only [cancel]; omega
    · rw [add_of_ne hn hc]; exact fx
  · rw [add_of_gt h]; exact fy

/-- The standard part: the coefficient at order `0`. Every residual reads `0`. -/
def st (x : R) : ℚ := if x.n = 0 then (x.c.1 : ℚ) / x.c.2 else 0

theorem st_add {x y : R} (hx : x.WF) (hy : y.WF) (fx : 0 ≤ x.n) (fy : 0 ≤ y.n) :
    st (add x y) = st x + st y := by
  have hx2 : (x.c.2 : ℚ) ≠ 0 := by exact_mod_cast hx.2
  have hy2 : (y.c.2 : ℚ) ≠ 0 := by exact_mod_cast hy.2
  rcases lt_trichotomy x.n y.n with h | hn | h
  · rw [add_of_lt h]; simp [st, show y.n ≠ 0 by omega]
  · by_cases hc : x.c.1 * y.c.2 + x.c.2 * y.c.1 = 0
    · rw [add_of_cancel hn hc]
      have hc' : (x.c.1 : ℚ) * y.c.2 + x.c.2 * y.c.1 = 0 := by exact_mod_cast hc
      simp only [st, cancel, show x.n + 1 ≠ 0 by omega, if_false, ← hn]
      split_ifs
      · rw [div_add_div _ _ hx2 hy2, hc', zero_div]
      · ring
    · rw [add_of_ne hn hc]
      simp only [st, ← hn]
      split_ifs
      · rw [div_add_div _ _ hx2 hy2]; push_cast; ring
      · ring
  · rw [add_of_gt h]; simp [st, show x.n ≠ 0 by omega]

theorem st_mul {x y : R} (fx : 0 ≤ x.n) (fy : 0 ≤ y.n) : st (mul x y) = st x * st y := by
  by_cases hx0 : x.n = 0 <;> by_cases hy0 : y.n = 0
  · simp [st, mul, hx0, hy0, div_mul_div_comm]
  · simp [st, mul, hx0, hy0]
  · simp [st, mul, hx0, hy0]
  · simp [st, mul, hx0, hy0, show x.n + y.n ≠ 0 by omega]

/-! ## Off an exact cancellation the laws hold -/

/-- `x + y` makes no exact cancellation. -/
def NoCancel (x y : R) : Prop := x.n = y.n → x.c.1 * y.c.2 + x.c.2 * y.c.1 ≠ 0

theorem add_comm_of_noCancel {x y : R} (h : NoCancel x y) : add x y = add y x := by
  rcases lt_trichotomy x.n y.n with hl | hn | hl
  · rw [add_of_lt hl, add_of_gt hl]
  · have hc := h hn
    have hc' : y.c.1 * x.c.2 + y.c.2 * x.c.1 ≠ 0 := by
      intro e; apply hc; linear_combination e
    rw [add_of_ne hn hc, add_of_ne hn.symm hc']
    ext <;> simp [hn] <;> ring
  · rw [add_of_gt hl, add_of_lt hl]

theorem add_assoc_of_noCancel {x y z : R} (hxy : x.n = y.n) (hyz : y.n = z.n)
    (h1 : x.c.1 * y.c.2 + x.c.2 * y.c.1 ≠ 0) (h2 : y.c.1 * z.c.2 + y.c.2 * z.c.1 ≠ 0)
    (h3 : (x.c.1 * y.c.2 + x.c.2 * y.c.1) * z.c.2 + x.c.2 * y.c.2 * z.c.1 ≠ 0) :
    add (add x y) z = add x (add y z) := by
  have h3' : x.c.1 * (y.c.2 * z.c.2) + x.c.2 * (y.c.1 * z.c.2 + y.c.2 * z.c.1) ≠ 0 := by
    intro e; apply h3; linear_combination e
  rw [add_of_ne hxy h1, add_of_ne hyz h2,
    add_of_ne (x := ⟨(x.c.1 * y.c.2 + x.c.2 * y.c.1, x.c.2 * y.c.2), x.n⟩) (y := z) (hxy.trans hyz) h3,
    add_of_ne (x := x) (y := ⟨(y.c.1 * z.c.2 + y.c.2 * z.c.1, y.c.2 * z.c.2), y.n⟩) hxy h3']
  ext <;> simp <;> ring

/-! ## At an exact cancellation they fail -/

/-- `2 = Z(2 : 1, 0)`. -/
def two : R := ⟨(2, 1), 0⟩

theorem value_cancel_ne {a b : ℤ} (h : a ≠ b) :
    (cancel ⟨(a, 1), 0⟩).value ≠ (cancel ⟨(b, 1), 0⟩).value := by
  simp only [value, cancel, Int.cast_one, div_one, ← single_eq_C_mul_T]
  intro e
  have := congrArg (fun f : LaurentPolynomial ℚ => f.coeff (0 + 1)) e
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at this
  exact h (by exact_mod_cast this)

/-- `1 − 1 = 0·1`, while `−1 + 1 = 0·(−1)`. -/
theorem add_not_comm :
    add one (neg one) = cancel one ∧ add (neg one) one = cancel (neg one) ∧
      (cancel one).value ≠ (cancel (neg one)).value :=
  ⟨by decide, by decide, value_cancel_ne (by decide)⟩

/-- `(1 + 1) − 2 = 0·2`, while `1 + (1 − 2) = 0·1`. -/
theorem add_not_assoc :
    add (add one one) (neg two) = cancel two ∧ add one (add one (neg two)) = cancel one ∧
      (cancel two).value ≠ (cancel one).value :=
  ⟨by decide, by decide, value_cancel_ne (by decide)⟩

/-! ## The projection does not see the failures -/

theorem st_add_comm {x y : R} (hx : x.WF) (hy : y.WF) (fx : 0 ≤ x.n) (fy : 0 ≤ y.n) :
    st (add x y) = st (add y x) := by
  rw [st_add hx hy fx fy, st_add hy hx fy fx, add_comm]

theorem st_add_assoc {x y z : R} (hx : x.WF) (hy : y.WF) (hz : z.WF)
    (fx : 0 ≤ x.n) (fy : 0 ≤ y.n) (fz : 0 ≤ z.n) :
    st (add (add x y) z) = st (add x (add y z)) := by
  rw [st_add (wf_add hx hy) hz (n_add_nonneg fx fy) fz, st_add hx hy fx fy,
    st_add hx (wf_add hy hz) fx (n_add_nonneg fy fz), st_add hy hz fy fz, add_assoc]

/-- `·` distributes over `+` on values, an exact cancellation included. -/
theorem value_mul_add {x y z : R} (hz : z.WF) (hx : x.c.2 ≠ 0) (hy : y.c.2 ≠ 0) :
    (mul z (add x y)).value = (add (mul z x) (mul z y)).value := by
  have hz1 : (z.c.1 : ℚ) ≠ 0 := by exact_mod_cast hz.1
  have hz2 : (z.c.2 : ℚ) ≠ 0 := by exact_mod_cast hz.2
  have hx2 : (x.c.2 : ℚ) ≠ 0 := by exact_mod_cast hx
  have hy2 : (y.c.2 : ℚ) ≠ 0 := by exact_mod_cast hy
  rcases lt_trichotomy x.n y.n with hl | hn | hl
  · rw [add_of_lt hl, add_of_lt (by simp only [mul]; omega)]
  · have hn' : (mul z x).n = (mul z y).n := by simp only [mul, hn]
    have key : (mul z x).c.1 * (mul z y).c.2 + (mul z x).c.2 * (mul z y).c.1 =
        z.c.1 * z.c.2 * (x.c.1 * y.c.2 + x.c.2 * y.c.1) := by simp only [mul]; ring
    by_cases hc : x.c.1 * y.c.2 + x.c.2 * y.c.1 = 0
    · rw [add_of_cancel hn hc, add_of_cancel hn' (by rw [key, hc, mul_zero])]
      congr 1; ext <;> simp [mul, cancel]; ring
    · rw [add_of_ne hn hc,
        add_of_ne hn' (by rw [key]; exact mul_ne_zero (mul_ne_zero hz.1 hz.2) hc)]
      simp only [value, mul, Int.cast_mul, Int.cast_add]
      congr 2; field_simp
  · rw [add_of_gt hl, add_of_gt (by simp only [mul]; omega)]

/-! ## No lawful projection keeps what cancelled -/

/-- The integer `n + 1` at order `0`. -/
def succInt (n : ℕ) : R := ⟨((n : ℤ) + 1, 1), 0⟩

/-- Any projection carrying `+` to an associative operation sends `0·n` to `0·1` for every positive
integer `n`: `(n + 1) − (n + 1)` regroups as `n + (1 − (n + 1)) = n − n`. -/
theorem forgets_cancelled {M : Type*} [Semigroup M] (f : R → M)
    (hf : ∀ x y, f (add x y) = f x * f y) (n : ℕ) :
    f (cancel (succInt n)) = f (cancel one) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [← ih]
    have e1 : add (succInt k) one = succInt (k + 1) := by
      rw [add_of_ne (x := succInt k) (y := one) rfl (by simp [succInt, one]; omega)]
      ext <;> simp [succInt, one]
    have e2 : add one (neg (succInt (k + 1))) = neg (succInt k) := by
      rw [add_of_ne (x := one) (y := neg (succInt (k + 1))) rfl (by simp [succInt, one, neg]; omega)]
      ext <;> simp [succInt, one, neg]
    calc f (cancel (succInt (k + 1)))
        = f (add (add (succInt k) one) (neg (succInt (k + 1)))) := by rw [e1, add_neg_self]
      _ = f (succInt k) * (f one * f (neg (succInt (k + 1)))) := by rw [hf, hf, mul_assoc]
      _ = f (add (succInt k) (neg (succInt k))) := by rw [← hf, e2, hf]
      _ = f (cancel (succInt k)) := by rw [add_neg_self]

/-- Any projection carrying `+` to a commutative operation sends `0·1` to `0·(−1)`. -/
theorem forgets_sign {M : Type*} [CommMagma M] (f : R → M)
    (hf : ∀ x y, f (add x y) = f x * f y) :
    f (cancel one) = f (cancel (neg one)) := by
  rw [← add_not_comm.1, ← add_not_comm.2.1, hf, hf, mul_comm]

end R

end T.ZeroScale.Residual
