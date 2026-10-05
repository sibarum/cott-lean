import CottLean.T.Dual
import CottLean.T.Fraction
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# An exponential carries `⊕` to `*`

`⊕` is `T(p + r, q + s)` and `*` is `T(pr, qs)`: one coordinatewise construction, over `(ℤ, +)` and
over `(ℤ, ·)`. `Dual` shows they make the ring `ℤ × ℤ` together. So the exponential, taken in each
coordinate, carries one to the other exactly as `b^(m + n) = b^m · b^n` does on `ℤ`. With a base pair
`b = T(b₁, b₂)`,

```
exp b T(p, q) = T(b₁^p, b₂^q)
```

| `⊕` side | `*` side | |
|---|---|---|
| `x ⊕ y` | `exp b x * exp b y` | `exp_oplus` |
| `0ω`, the `⊕` unit | `1`, the `*` unit | `exp_zeroOmega` |
| `scale n x`, `x` added `n` times | `power (exp b x) n` | `exp_scale` |
| the base `b * c` | `exp b x * exp c x` | `exp_times_base` |

* **The exponents are not negative.** A negative coordinate asks for `1/b`, which `ℤ` cannot hold, so
  `exp` reads it as `0` and the law fails there: `T(-1, 0) ⊕ T(1, 0) = 0ω`, and the product of the two
  exponentials is `T(2, 1)`, not `1` (`exp_oplus_fails`). The exponential carries the quadrant
  `0 ≤ p, 0 ≤ q`, where `⊕` is a monoid and not a group, as `*` is a monoid and not a group.
* **The logarithm goes back.** For a prime `ℓ`, `vlog ℓ T(p, q) = T(v_ℓ p, v_ℓ q)`, the `ℓ`-adic
  valuation in each coordinate. It carries `*` to `⊕` on pairs with no zero coordinate (`vlog_times`)
  and `1` to `0ω` (`vlog_one`), and it undoes the exponential of base `T(ℓ, ℓ)` on the quadrant
  (`vlog_exp`). So that exponential is injective there (`exp_injective`): the quadrant under `⊕` sits
  inside `T` under `*` exactly.
* **The ratio reading is the difference reading.** `*` keeps the ratio `p ÷ q`, which forgets a common
  factor; `⊕` keeps the difference `p − q`, which forgets a common shift. With one base `b ≥ 2` in both
  coordinates, `b^p ÷ b^q = b^(p − q)`, so two exponentials name one ratio exactly when the exponents
  have one difference (`exp_sameRatio_iff`).
-/

namespace T

/-- `T(b₁^p, b₂^q)`: the base `b` raised to `x` in each coordinate. A negative coordinate counts as `0`. -/
def exp (b x : T) : T := ⟨b.p ^ x.p.toNat, b.q ^ x.q.toNat⟩

/-- `⊕` is carried to `*`, on exponents that are not negative. -/
theorem exp_oplus (b : T) {x y : T} (hx : 0 ≤ x.p ∧ 0 ≤ x.q) (hy : 0 ≤ y.p ∧ 0 ≤ y.q) :
    exp b (x ⊕ y) = exp b x * exp b y := by
  ext <;> simp [exp, oplus, Int.toNat_add hx.1 hy.1,
    Int.toNat_add hx.2 hy.2, pow_add]

/-- The `⊕` unit goes to the `*` unit. -/
@[simp] theorem exp_zeroOmega (b : T) : exp b «0ω» = «1» := by
  ext <;> simp [exp, «0ω», «1»]

/-- `x` added to itself `n` times goes to `exp b x` multiplied by itself `n` times. -/
theorem exp_scale (b : T) (n : ℕ) {x : T} (hx : 0 ≤ x.p ∧ 0 ≤ x.q) :
    exp b (scale n x) = power (exp b x) n := by
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hx.1
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le hx.2
  ext <;> simp only [exp, scale, power, ha, hc] <;> norm_cast <;> rw [Int.toNat_natCast,
    Int.toNat_natCast, mul_comm, pow_mul]

/-- The base is multiplicative too, at every exponent. -/
theorem exp_times_base (b c x : T) : exp (b * c) x = exp b x * exp c x := by
  ext <;> simp [exp, mul_pow]

/-- Off the quadrant the law fails: `T(-1, 0) ⊕ T(1, 0) = 0ω` goes to `1`, the product to `T(2, 1)`. -/
theorem exp_oplus_fails :
    exp ⟨2, 2⟩ (⟨-1, 0⟩ ⊕ ⟨1, 0⟩) = «1» ∧ exp ⟨2, 2⟩ ⟨-1, 0⟩ * exp ⟨2, 2⟩ ⟨1, 0⟩ = ⟨2, 1⟩ := by
  decide

/-! ## The logarithm -/

/-- `T(v_ℓ p, v_ℓ q)`: the `ℓ`-adic valuation in each coordinate. -/
def vlog (ℓ : ℕ) (x : T) : T := ⟨padicValInt ℓ x.p, padicValInt ℓ x.q⟩

/-- `*` is carried to `⊕`, on pairs with no zero coordinate. -/
theorem vlog_times (ℓ : ℕ) [Fact ℓ.Prime] {x y : T} (hx : x.p ≠ 0 ∧ x.q ≠ 0)
    (hy : y.p ≠ 0 ∧ y.q ≠ 0) : vlog ℓ (x * y) = vlog ℓ x ⊕ vlog ℓ y := by
  ext <;> simp [vlog, oplus, padicValInt.mul hx.1 hy.1,
    padicValInt.mul hx.2 hy.2]

/-- The `*` unit goes to the `⊕` unit. -/
@[simp] theorem vlog_one (ℓ : ℕ) : vlog ℓ «1» = «0ω» := by
  ext <;> simp [vlog, «1», «0ω»]

/-- The logarithm undoes the exponential of base `T(ℓ, ℓ)`, on exponents that are not negative. -/
theorem vlog_exp (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {x : T} (hx : 0 ≤ x.p ∧ 0 ≤ x.q) :
    vlog ℓ (exp ⟨ℓ, ℓ⟩ x) = x := by
  have h (n : ℕ) : padicValInt ℓ ((ℓ : ℤ) ^ n) = n := by
    rw [← Nat.cast_pow, padicValInt.of_nat, padicValNat.prime_pow]
  ext <;> simp only [vlog, exp, h, Int.toNat_of_nonneg hx.1, Int.toNat_of_nonneg hx.2]

/-- So the exponential of base `T(ℓ, ℓ)` forgets nothing on the quadrant. -/
theorem exp_injective (ℓ : ℕ) [Fact ℓ.Prime] {x y : T} (hx : 0 ≤ x.p ∧ 0 ≤ x.q)
    (hy : 0 ≤ y.p ∧ 0 ≤ y.q) (h : exp ⟨ℓ, ℓ⟩ x = exp ⟨ℓ, ℓ⟩ y) : x = y := by
  rw [← vlog_exp ℓ hx, ← vlog_exp ℓ hy, h]

/-! ## The ratio reading is the difference reading -/

/-- With one base in both coordinates, `b^p ÷ b^q = b^(p − q)`: two exponentials name one ratio exactly
when the exponents have one difference. -/
theorem exp_sameRatio_iff {b : ℤ} (hb : 2 ≤ b) {x y : T} (hx : 0 ≤ x.p ∧ 0 ≤ x.q)
    (hy : 0 ≤ y.p ∧ 0 ≤ y.q) :
    sameRatio (exp ⟨b, b⟩ x) (exp ⟨b, b⟩ y) ↔ x.p - x.q = y.p - y.q := by
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hx.1
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le hx.2
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hy.1
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hy.2
  simp only [sameRatio, exp, ha, hc, hd, he, Int.toNat_natCast, ← pow_add,
    pow_right_inj₀ (by omega : (0 : ℤ) < b) (by omega : b ≠ 1)]
  omega

end T
