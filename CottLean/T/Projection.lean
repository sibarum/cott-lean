import CottLean.T.Norm

/-!
# Complementary projections, and the one product that has them

A projection is an idempotent other than the ring's zero and unit: `e · e = e`. With its complement,
`1 − e`, it splits every element in two, `x = x·e + x·(1 − e)`, and each half alone loses the other.

Under `*`, `ω` and `0` are such a pair: `(x * ω) ⊕ (x * 0) = x` (`times_omega_oplus_times_zero`). This file
proves that `*` is the only one of T's products with a projection.

For the whole family `qtimes a b` the answer turns on the discriminant (`qtimes_idempotent_iff`). If
`e = q + p·ω` squares to itself with `p ≠ 0`, the `ω` coordinate forces `2q + b·p = 1`, and then the
other coordinate forces `p²·(b² + 4a) = 1`. So a projection exists exactly when `b² + 4a = 1`, and it
is then `p = ±1`, `q = (1 − b·p)/2`. That is the ring `ℤ × ℤ`, which is `*`'s ring. `⊗`, `+`, `⊚` and the
Eisenstein product have discriminants `−4`, `0`, `4` and `−3`, so their only idempotents are `0ω` and
`0` (`otimes_idempotent_iff`, `plus_idempotent_iff`, `splitTimes_idempotent_iff`). `∥`'s are `0ω` and
`ω` (`par_idempotent_iff`). `split_not_prod` is the case `a = 1`, `b = 0`.

Under `*` there are four idempotents: `0ω`, `0`, `ω` and `1` (`times_idempotent_iff`). And what `*` loses
against a pair on an axis is exactly one projection. Against `T(a, 0)` with `a ≠ 0`, two pairs give the
same result exactly when their `ω` projections agree (`times_eq_times_iff_of_q_eq_zero`), and against
`T(0, b)` with `b ≠ 0`, exactly when their `0` projections agree. So the complementary channel is what a
reversible use of `*` has to keep, and keeping it is enough.
-/

namespace T

/-! ## The whole family -/

/-- `e ⋅ e = e` in `ω² = a + b·ω` exactly at `0ω`, at `0`, and, when the discriminant is `1`, at the two
projections `p = ±1`, `2q = 1 − b·p`. -/
theorem qtimes_idempotent_iff (a b : ℤ) (x : T) :
    qtimes a b x x = x ↔
      x = «0ω» ∨ x = 0 ∨ (b ^ 2 + 4 * a = 1 ∧ (x.p = 1 ∨ x.p = -1) ∧ 2 * x.q = 1 - b * x.p) := by
  obtain ⟨p, q⟩ := x
  simp only [qtimes, T.mk.injEq, «0ω», zero_def]
  constructor
  · rintro ⟨hp, hq⟩
    by_cases h0 : p = 0
    · subst h0
      have : q * (q - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · left; exact ⟨rfl, h⟩
      · right; left; exact ⟨rfl, by linarith⟩
    · right; right
      have hlin : 2 * q + b * p = 1 := by
        have : p * (2 * q + b * p - 1) = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_left h0
        linarith
      have hn : (p * p) * (b ^ 2 + 4 * a) = 1 := by
        have : 4 * (q * q) - 4 * q + 4 * a * (p * p) = 0 := by linarith
        linear_combination this - (2 * q - 1 - b * p) * hlin
      have hpp : p * p = 1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one hn with h | h
        · exact h
        · nlinarith [mul_self_nonneg p]
      refine ⟨?_, Int.eq_one_or_neg_one_of_mul_eq_one hpp, by linarith⟩
      rw [hpp, one_mul] at hn; exact hn
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hd, hp, hq⟩)
    · simp
    · simp
    · have hpp : p * p = 1 := by rcases hp with rfl | rfl <;> norm_num
      constructor
      · -- `p·(2q + b·p) = p`, since `2q + b·p = 1`.
        have : 2 * q + b * p = 1 := by
          rcases hp with rfl | rfl <;> linarith
        linear_combination p * this
      · -- `4(q² − q + a·p²) = (2q − 1)² − 1 + 4a = b²p² − 1 + 4a = 0`.
        have h4 : 4 * (q * q + a * p * p - q) = 0 := by
          have : (2 * q - 1) ^ 2 = b ^ 2 * (p * p) := by rw [hq]; ring
          nlinarith [this, hpp, hd]
        linarith

/-! ## Each product's idempotents -/

theorem otimes_idempotent_iff (x : T) : x ⊗ x = x ↔ x = «0ω» ∨ x = 0 := by
  rw [otimes_eq_qtimes, qtimes_idempotent_iff]; norm_num

theorem plus_idempotent_iff (x : T) : x + x = x ↔ x = «0ω» ∨ x = 0 := by
  rw [plus_eq_qtimes, qtimes_idempotent_iff]; norm_num

theorem splitTimes_idempotent_iff (x : T) : x ⊚ x = x ↔ x = «0ω» ∨ x = 0 := by
  rw [splitTimes, qtimes_idempotent_iff]; norm_num

/-- The Eisenstein product, `ω² = −1 − ω`, has none either. -/
theorem eisenstein_idempotent_iff (x : T) : qtimes (-1) (-1) x x = x ↔ x = «0ω» ∨ x = 0 := by
  rw [qtimes_idempotent_iff]; norm_num

/-- Under `*` there are four: `0ω`, `0`, `ω` and `1`. -/
theorem times_idempotent_iff (x : T) : x * x = x ↔ x = «0ω» ∨ x = 0 ∨ x = «ω» ∨ x = «1» := by
  obtain ⟨p, q⟩ := x
  simp only [mul_def, T.mk.injEq, «0ω», zero_def, «ω», «1»]
  constructor
  · rintro ⟨hp, hq⟩
    have hp' : p * (p - 1) = 0 := by linarith
    have hq' : q * (q - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hp' with h1 | h1 <;> rcases mul_eq_zero.mp hq' with h2 | h2 <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- Under `∥` there are two: `0ω` and its unit `ω`. -/
theorem par_idempotent_iff (x : T) : x ∥ x = x ↔ x = «0ω» ∨ x = «ω» := by
  obtain ⟨p, q⟩ := x
  simp only [par, T.mk.injEq, «0ω», «ω»]
  constructor
  · rintro ⟨hp, hq⟩
    have hp' : p * (p - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hp' with h | h
    · subst h; left; exact ⟨rfl, by linarith⟩
    · have : p = 1 := by linarith
      subst this; right; exact ⟨rfl, by linarith⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-! ## The pair of projections under `*` -/

/-- `ω` and `0` are complementary: their product is `0ω` and their `⊕` is `1`. -/
theorem omega_zero_complementary : «ω» * 0 = «0ω» ∧ («ω» ⊕ 0) = «1» := by decide

/-- Against `T(a, 0)` with `a ≠ 0`, `*` keeps exactly the `ω` projection. -/
theorem times_eq_times_iff_of_q_eq_zero {k : T} (hq : k.q = 0) (hp : k.p ≠ 0) (x x' : T) :
    x * k = x' * k ↔ x * «ω» = x' * «ω» := by
  simp only [mul_def, «ω», T.mk.injEq, hq, mul_zero, mul_one, and_true]
  exact mul_left_inj' hp

/-- Against `T(0, b)` with `b ≠ 0`, `*` keeps exactly the `0` projection. -/
theorem times_eq_times_iff_of_p_eq_zero {k : T} (hp : k.p = 0) (hq : k.q ≠ 0) (x x' : T) :
    x * k = x' * k ↔ x * 0 = x' * 0 := by
  simp only [mul_def, zero_def, T.mk.injEq, hp, mul_zero, mul_one, true_and]
  exact mul_left_inj' hq

/-- So the projection `*` drops, kept alongside the result, gives the operand back exactly. -/
theorem times_recover_with_complement {k : T} (hq : k.q = 0) (hp : k.p ≠ 0) {x x' : T}
    (h : x * k = x' * k) (hc : x * 0 = x' * 0) : x = x' := by
  rw [← times_omega_oplus_times_zero x, ← times_omega_oplus_times_zero x',
    (times_eq_times_iff_of_q_eq_zero hq hp x x').mp h, hc]

end T
