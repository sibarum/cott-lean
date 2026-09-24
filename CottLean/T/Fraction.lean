import CottLean.T.Basic

/-!
# The value position

`+` is the fraction sum, cross-multiplying always, and `*` is componentwise. Both are commutative and
associative exactly on the coordinates, with `0 = T(0,1)` and `1 = T(1,1)` as their units.

What they do not do is distribute on the coordinates. Traction-Model.md writes
`(x + y) * z = (x * z) + (y * z)`, and the exact statement is `distrib_scaled` below: the right side is the
left side with both coordinates multiplied by `z`'s denominator. So it holds as written where that
denominator is one, lands on the same ratio at other coordinates where it is anything else but zero, and
lands on `0ω` where it is zero -- which is `ω·(0+1)` against `ω·0 + ω·1`.

## Same ratio

Every pair is distinct, and not because an invariant has been removed: no invariant is specified by
default. Equality here is coordinate equality, which identifies nothing, and every theorem is stated at it.
An invariant -- the ratio, the ray, the angle, the norm -- is something a use of the pairs specifies, and a
fact about one is a corollary of the coordinate fact, not a replacement for it.

`sameRatio x y` is one such invariant: `p·q' = p'·q`. It is reflexive and symmetric, and it is not
transitive, because `0ω` has the same ratio as every pair. It is transitive through any other pair.
-/

namespace T

@[simp] theorem add_def (x y : T) : x + y = ⟨x.p * y.q + y.p * x.q, x.q * y.q⟩ := rfl
@[simp] theorem mul_def (x y : T) : x * y = ⟨x.p * y.p, x.q * y.q⟩ := rfl

/-! ## The laws that hold on the coordinates -/

theorem plus_comm (x y : T) : x + y = y + x := by ext <;> simp <;> ring
theorem plus_assoc (x y z : T) : x + y + z = x + (y + z) := by ext <;> simp <;> ring
theorem times_comm (x y : T) : x * y = y * x := by ext <;> simp <;> ring
theorem times_assoc (x y z : T) : x * y * z = x * (y * z) := by ext <;> simp <;> ring

/-- `0 = T(0,1)` is the unit of `+`, for every pair, `ω` and `0ω` included. -/
theorem plus_zero (x : T) : x + 0 = x := by ext <;> simp

/-- `1 = T(1,1)` is the unit of `*`. -/
theorem times_one (x : T) : x * «1» = x := by ext <;> simp [«1»]

/-! ## Minus and the reciprocal -/

theorem neg_plus (x y : T) : -(x + y) = -x + -y := by ext <;> simp; ring
theorem neg_times (x y : T) : -(x * y) = -x * y := by ext <;> simp

/-- The product forgets which factor carried the sign: `(-x) * (-y) = x * y` on the coordinates. -/
theorem neg_times_neg (x y : T) : -x * -y = x * y := by ext <;> simp

/-- A pair plus its negation is `T(0, q²)`: a zero-magnitude pair, at `0` only where `q² = 1`. -/
theorem plus_neg_self (x : T) : x + -x = ⟨0, x.q ^ 2⟩ := by ext <;> simp; ring

theorem reciprocal_reciprocal (x : T) : reciprocal (reciprocal x) = x := rfl

theorem reciprocal_times (x y : T) : reciprocal (x * y) = reciprocal x * reciprocal y := rfl

/-- `0` and `ω` are each other's reciprocal. -/
theorem reciprocal_zero : reciprocal 0 = «ω» := rfl

/-- A pair times its reciprocal is `T(pq, pq)`: the ratio one, at `1` only where `pq = 1`. -/
theorem times_reciprocal_self (x : T) : x * reciprocal x = ⟨x.p * x.q, x.p * x.q⟩ := by
  ext <;> simp [reciprocal]; ring

/-! ## Powers -/

theorem power_add (x : T) (m n : ℕ) : power x (m + n) = power x m * power x n := by
  ext <;> simp [power, pow_add]

theorem power_mul (x : T) (m n : ℕ) : power (power x m) n = power x (m * n) := by
  ext <;> simp [power, pow_mul]

theorem times_power (x y : T) (n : ℕ) : power (x * y) n = power x n * power y n := by
  ext <;> simp [power, mul_pow]

/-! ## Distributivity, exactly -/

/-- Both coordinates multiplied by `k`. -/
def scale (k : ℤ) (x : T) : T := ⟨k * x.p, k * x.q⟩

/-- `x * z + y * z` is `(x + y) * z` with both coordinates multiplied by `z`'s denominator. -/
theorem distrib_scaled (x y z : T) : x * z + y * z = scale z.q ((x + y) * z) := by
  ext <;> simp [scale] <;> ring

theorem distrib_scaled_left (x y z : T) : x * y + x * z = scale x.q (x * (y + z)) := by
  ext <;> simp [scale] <;> ring

/-- Where `z`'s denominator is one, the model's law holds as written. -/
theorem distrib_of_q_eq_one (x y z : T) (h : z.q = 1) : x * z + y * z = (x + y) * z := by
  rw [distrib_scaled, h]; ext <;> simp [scale]

/-- Where it is zero, the right side is `0ω`, whatever the left side is. -/
theorem distrib_of_q_eq_zero (x y z : T) (h : z.q = 0) : x * z + y * z = «0ω» := by
  rw [distrib_scaled, h]; ext <;> simp [scale, «0ω»]

/-- T-Design.md's example: `ω·(0+1)` is `ω`, and `ω·0 + ω·1` is `0ω`. -/
theorem not_distrib : «ω» * (0 + «1») ≠ «ω» * 0 + «ω» * «1» := by decide

example : «ω» * (0 + «1») = «ω» := by decide
example : «ω» * 0 + «ω» * «1» = «0ω» := by decide

/-! ## Same ratio -/

/-- `p ÷ q` and `p' ÷ q'` name one ratio: `p·q' = p'·q`. -/
def sameRatio (x y : T) : Prop := x.p * y.q = y.p * x.q

instance (x y : T) : Decidable (sameRatio x y) := inferInstanceAs (Decidable (_ = _))

theorem sameRatio_refl (x : T) : sameRatio x x := by simp [sameRatio]

theorem sameRatio_symm {x y : T} (h : sameRatio x y) : sameRatio y x := by
  unfold sameRatio at *; linarith

/-- `0ω` has the same ratio as everything. -/
theorem sameRatio_zeroOmega (x : T) : sameRatio x «0ω» := by simp [sameRatio, «0ω»]

/-- Scaling keeps the ratio, by any factor -- zero included, which is `0ω` again. -/
theorem sameRatio_scale (k : ℤ) (x : T) : sameRatio (scale k x) x := by
  simp [sameRatio, scale]; ring

/-- So it is not transitive: `1` and `0` both have `0ω`'s ratio, and not each other's. -/
theorem sameRatio_not_transitive :
    sameRatio «1» «0ω» ∧ sameRatio «0ω» 0 ∧ ¬ sameRatio «1» 0 := by decide

/-- And that is the only way it fails: through any pair but `0ω`, it is transitive. -/
theorem sameRatio_trans {x y z : T} (hy : y ≠ «0ω») (h₁ : sameRatio x y) (h₂ : sameRatio y z) :
    sameRatio x z := by
  unfold sameRatio at *
  have hq : (x.p * z.q - z.p * x.q) * y.q = 0 := by linear_combination z.q * h₁ + x.q * h₂
  have hp : (x.p * z.q - z.p * x.q) * y.p = 0 := by linear_combination x.p * h₂ + z.p * h₁
  have : y.p ≠ 0 ∨ y.q ≠ 0 := by
    by_contra hc
    simp only [ne_eq, not_or, not_not] at hc
    exact hy (T.ext hc.1 hc.2)
  rcases this with h | h
  · have := (mul_eq_zero.mp hp).resolve_right h; linarith
  · have := (mul_eq_zero.mp hq).resolve_right h; linarith

end T
