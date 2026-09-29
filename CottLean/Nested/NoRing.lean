import Mathlib.Tactic

/-!
# Why `m · (n − n)` erases `m` in a ring, and which laws do it

The mandate: `n + (−n)` may erase `n`, but `m · (n − n)` must not erase `m`. These are the laws that stand
in the way, each isolated.

* `left_distrib_zero`: in an additive group, the one instance `m · (0 + 0) = m·0 + m·0` of left
  distributivity forces `m · 0 = 0`. Associativity of `+`, the identity `0` and inverses are all it uses.
* `cancel_sum`: avoiding `0 + 0` does not help. Distributing over any cancelling sum `n + (−n)`, together
  with the sign rule `m · (−n) = −(m · n)`, forces it too. So distributivity has to fail on every sum that
  cancels, or the sign rule does.
* `right_distrib_zero`: the other side. The additive zero has `z + z = z`, so distributing on the right
  gives `2 · z = 1 · z`, and `· z` cannot tell `2` from `1` (`right_distrib_zero_not_injective`).
* `field_no_room`: and the zeros need new room. If a multiplication agrees with a field's on the non-zero
  elements and multiplying by any fixed element is injective, then `0 · m = 0` for every `m ≠ 0`, so `0 ·`
  erases its partner (`field_no_room_const`). The field has no spare element for `0 · m` to be.
-/

namespace NoRing

/-- Left distributivity at `0 + 0` forces `m · 0 = 0`. -/
theorem left_distrib_zero {R : Type*} [AddGroup R] [Mul R]
    (hd : ∀ m : R, m * (0 + 0) = m * 0 + m * 0) (m : R) : m * 0 = 0 := by
  have h := hd m
  rw [add_zero] at h
  simpa using h

/-- Distributing over a cancelling sum, with the sign rule, forces it too. -/
theorem cancel_sum {R : Type*} [AddGroup R] [Mul R]
    (hd : ∀ m n : R, m * (n + -n) = m * n + m * -n) (hs : ∀ m n : R, m * -n = -(m * n)) (m : R) :
    m * 0 = 0 := by
  have h := hd m m
  rwa [add_neg_cancel, hs, add_neg_cancel] at h

/-- Right distributivity through the additive zero gives `2 · z = 1 · z`. -/
theorem right_distrib_zero {R : Type*} [Add R] [Mul R] [One R] (z : R) (hz : z + z = z)
    (hr : (1 + 1) * z = 1 * z + 1 * z) (h1 : ∀ x : R, 1 * x = x) : (1 + 1) * z = 1 * z := by
  rw [hr, h1, hz]

/-- So `· z` cannot tell `2` from `1`. -/
theorem right_distrib_zero_not_injective {R : Type*} [Add R] [Mul R] [One R] (z : R)
    (hz : z + z = z) (hr : (1 + 1) * z = 1 * z + 1 * z) (h1 : ∀ x : R, 1 * x = x)
    (h2 : (1 + 1 : R) ≠ 1) : ¬ Function.Injective (· * z) :=
  fun hinj => h2 (hinj (right_distrib_zero z hz hr h1))

/-- A multiplication that agrees with a field's away from `0`, and loses nothing, has `0 · m = 0`. -/
theorem field_no_room {K : Type*} [Field K] (mul' : K → K → K)
    (hagree : ∀ x y, x ≠ 0 → y ≠ 0 → mul' x y = x * y)
    (hinj : ∀ m, Function.Injective (fun x => mul' x m)) {m : K} (hm : m ≠ 0) : mul' 0 m = 0 := by
  by_contra ht
  have hx : mul' 0 m / m ≠ 0 := div_ne_zero ht hm
  have h : mul' (mul' 0 m / m) m = mul' 0 m := by
    rw [hagree _ _ hx hm, div_mul_cancel₀ _ hm]
  exact hx (hinj m h)

/-- So `0 ·` gives every non-zero partner the same answer. -/
theorem field_no_room_const {K : Type*} [Field K] (mul' : K → K → K)
    (hagree : ∀ x y, x ≠ 0 → y ≠ 0 → mul' x y = x * y)
    (hinj : ∀ m, Function.Injective (fun x => mul' x m)) {m m' : K} (hm : m ≠ 0) (hm' : m' ≠ 0) :
    mul' 0 m = mul' 0 m' := by
  rw [field_no_room mul' hagree hinj hm, field_no_room mul' hagree hinj hm']

end NoRing
