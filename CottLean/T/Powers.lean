import CottLean.T.Gaussian
import CottLean.T.Fraction

/-!
# The two exponent laws, at integer exponents

`otimesPower x m` is the angle scaled `m` times: the point raised to `m`, through the conjugate when `m` is
negative. Traction-Model.md states two laws for it.

* `(T^m)^n = T^(m·n)` holds exactly on the coordinates, for every pair and both signs.
* `T^(m+n) = T^m ⊗ T^n` holds exactly while `m` and `n` point the same way. Where they cancel, the left
  side is the right side with both coordinates multiplied by `(p² + q²)^min(|m|, |n|)`: one norm for each
  turn that went out and came back. So it is exact at every exponent for the four axis pairs, whose norm
  is one -- one reason TLawsTest finds more exact cases than same-sign ones.

Both are stated at coordinate equality, and the factor is given exactly rather than waved at as "the
same ratio". Nothing here removes it; whether it should stand is the model's question.
-/

namespace T

/-! ## The power, on the point -/

/-- The point raised to an integer, through the conjugate below zero. -/
def gpow (g : GaussianInt) (m : ℤ) : GaussianInt :=
  if 0 ≤ m then g ^ m.natAbs else star g ^ m.natAbs

theorem gpow_natCast (g : GaussianInt) (a : ℕ) : gpow g a = g ^ a := by simp [gpow]

theorem gpow_neg_natCast (g : GaussianInt) (a : ℕ) : gpow g (-(a : ℤ)) = star g ^ a := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · simp [gpow]
  · have : ¬ (0 ≤ -(a : ℤ)) := by omega
    unfold gpow; rw [if_neg this]; simp

theorem toGaussian_otimesPower (x : T) (m : ℤ) :
    toGaussian (otimesPower x m) = gpow (toGaussian x) m := by
  cases m with
  | ofNat n => exact (toGaussian_otimesPower_ofNat x n).trans (gpow_natCast _ n).symm
  | negSucc n =>
    rw [toGaussian_otimesPower_negSucc, show Int.negSucc n = -((n + 1 : ℕ) : ℤ) from rfl,
      gpow_neg_natCast]

theorem toGaussian_scale (k : ℤ) (y : T) : toGaussian (scale k y) = (k : GaussianInt) * toGaussian y := by
  ext <;> simp [scale]

theorem scale_one (y : T) : scale 1 y = y := by ext <;> simp [scale]

/-- The model's `z(T(a,b)) = T(2ab, b²−a²)` is the angle scaled twice. -/
theorem doubleAngle_eq (x : T) : doubleAngle x = ⟨2 * x.p * x.q, x.q ^ 2 - x.p ^ 2⟩ := by
  ext <;> simp [doubleAngle, otimes] <;> ring

theorem doubleAngle_eq_otimesPower (x : T) : doubleAngle x = otimesPower x 2 :=
  toGaussian_injective (by
    rw [doubleAngle, toGaussian_otimes, toGaussian_otimesPower,
      show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, gpow_natCast, sq])

/-! ## `(T^m)^n = T^(m·n)` -/

theorem otimesPower_otimesPower (x : T) (m n : ℤ) :
    otimesPower (otimesPower x m) n = otimesPower x (m * n) := by
  apply toGaussian_injective
  rw [toGaussian_otimesPower, toGaussian_otimesPower, toGaussian_otimesPower]
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg m <;> obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [gpow_natCast, gpow_natCast, ← Nat.cast_mul, gpow_natCast, pow_mul]
  · rw [gpow_natCast, gpow_neg_natCast, mul_neg, ← Nat.cast_mul, gpow_neg_natCast, star_pow,
      pow_mul]
  · rw [gpow_neg_natCast, gpow_natCast, neg_mul, ← Nat.cast_mul, gpow_neg_natCast, pow_mul]
  · rw [gpow_neg_natCast, gpow_neg_natCast, neg_mul_neg, ← Nat.cast_mul, gpow_natCast, star_pow,
      star_star, pow_mul]

/-! ## `T^(m+n) = T^m ⊗ T^n`, up to the turns that cancel -/

/-- How many turns went out and came back: none when `m` and `n` point the same way, and the smaller of
the two otherwise. -/
def turns (m n : ℤ) : ℕ := if (m < 0 ↔ n < 0) then 0 else min m.natAbs n.natAbs

/-- Going out `a` times and back `b` times leaves the norm `min a b` times, and the rest of the turn. -/
theorem pow_mul_star_pow (g : GaussianInt) (a b : ℕ) :
    g ^ a * star g ^ b
      = (g * star g) ^ min a b * (if b ≤ a then g ^ (a - b) else star g ^ (b - a)) := by
  rcases le_or_gt b a with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [if_pos h, show min (b + c) b = b by omega, show b + c - b = c by omega, mul_pow, pow_add]
    ring
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [if_neg (by omega), show min a (a + c + 1) = a by omega, show a + c + 1 - a = c + 1 by omega,
      mul_pow, pow_add (star g) (a + c) 1, pow_add (star g) a c]
    ring

/-- The norm, as the point times its conjugate. -/
theorem norm_eq_mul_star (x : T) :
    ((x.p ^ 2 + x.q ^ 2 : ℤ) : GaussianInt) = toGaussian x * star (toGaussian x) := by
  ext <;> simp [sq] <;> ring

theorem otimesPower_add (x : T) (m n : ℤ) :
    otimesPower x m ⊗ otimesPower x n
      = scale ((x.p ^ 2 + x.q ^ 2) ^ turns m n) (otimesPower x (m + n)) := by
  apply toGaussian_injective
  rw [toGaussian_otimes, toGaussian_scale, toGaussian_otimesPower, toGaussian_otimesPower,
    toGaussian_otimesPower, Int.cast_pow, norm_eq_mul_star]
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg m <;> obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have ht : turns a b = 0 := by
      unfold turns; rw [if_pos ⟨fun _ => by omega, fun _ => by omega⟩]
    rw [ht, pow_zero, one_mul, ← Nat.cast_add, gpow_natCast, gpow_natCast, gpow_natCast, pow_add]
  · have ht : turns a (-b) = min a b := by
      unfold turns
      split_ifs with h
      · have : b = 0 := by omega
        simp [this]
      · simp
    rw [ht, gpow_natCast, gpow_neg_natCast, pow_mul_star_pow]
    congr 1
    split_ifs with h
    · rw [show (a : ℤ) + -b = ((a - b : ℕ) : ℤ) by omega, gpow_natCast]
    · rw [show (a : ℤ) + -b = -((b - a : ℕ) : ℤ) by omega, gpow_neg_natCast]
  · have ht : turns (-a) b = min b a := by
      unfold turns
      split_ifs with h
      · have : a = 0 := by omega
        simp [this]
      · simp [min_comm]
    rw [ht, gpow_neg_natCast, gpow_natCast, mul_comm (star _ ^ a), pow_mul_star_pow]
    congr 1
    split_ifs with h
    · rw [show -(a : ℤ) + b = ((b - a : ℕ) : ℤ) by omega, gpow_natCast]
    · rw [show -(a : ℤ) + b = -((a - b : ℕ) : ℤ) by omega, gpow_neg_natCast]
  · have ht : turns (-a) (-b) = 0 := by
      unfold turns
      split_ifs with h
      · rfl
      · simp only [Int.natAbs_neg, Int.natAbs_natCast]
        omega
    rw [ht, pow_zero, one_mul, gpow_neg_natCast, gpow_neg_natCast, ← neg_add, ← Nat.cast_add,
      gpow_neg_natCast, pow_add]

/-- Where the exponents point the same way, the law holds as written. -/
theorem otimesPower_add_of_same_sign (x : T) {m n : ℤ} (h : m < 0 ↔ n < 0) :
    otimesPower x m ⊗ otimesPower x n = otimesPower x (m + n) := by
  rw [otimesPower_add, show turns m n = 0 by simp [turns, h], pow_zero, scale_one]

/-- And at every exponent for a pair whose norm is one -- the four axis pairs, `0`, `ω`, `_0`, `-ω`. -/
theorem otimesPower_add_of_norm_one (x : T) (h : x.p ^ 2 + x.q ^ 2 = 1) (m n : ℤ) :
    otimesPower x m ⊗ otimesPower x n = otimesPower x (m + n) := by
  rw [otimesPower_add, h, one_pow, scale_one]

/-- A turn out and back at `T(1,2)` lands on `0` with both coordinates multiplied by its norm, five. -/
example : otimesPower ⟨1, 2⟩ 1 ⊗ otimesPower ⟨1, 2⟩ (-1) = ⟨0, 5⟩ := by decide

end T
