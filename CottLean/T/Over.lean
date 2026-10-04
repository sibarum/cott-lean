import CottLean.T.Basic

/-!
# `T` over any commutative ring

`T(p, q)` holds two integers. Nothing in the value-position formulas needs the integers in particular:

```
T(p,q) + T(r,s) = T(ps + rq, qs)      T(p,q) · T(r,s) = T(pr, qs)
−T(p,q) = T(−p, q)                    1 / T(p,q) = T(q, p)
```

are the same formulas over any commutative ring `R`. `TOver R` is that pair. Over ℤ it is `T` exactly
(`ofT`, which carries each operation across as `rfl`). Over the Gaussian integers it is a ratio of two
complex numbers, `T(C, C)` (`Nested.RatioPoint`).

The facts about the reciprocal that hold over ℤ hold over any ring, with the same proofs:

* `times_reciprocal_self`: `x · (1/x) = T(pq, pq)`, `1` with both coordinates scaled by one element `pq`.
* In a domain, `* k` can be undone exactly when neither coordinate of `k` is zero (`times_cancel_iff`),
  which is exactly when that residue `pq` is not zero (`residue_eq_zero_iff`).
-/

/-- A pair over a commutative ring, read as the ratio `p / q`. Nothing is reduced. -/
@[ext]
structure TOver (R : Type*) where
  /-- The numerator. -/
  p : R
  /-- The denominator. Zero here, as in `T`. -/
  q : R

namespace TOver

variable {R : Type*}

/-- `T(q, p)`. -/
def reciprocal (x : TOver R) : TOver R := ⟨x.q, x.p⟩

@[simp] theorem reciprocal_p (x : TOver R) : (reciprocal x).p = x.q := rfl
@[simp] theorem reciprocal_q (x : TOver R) : (reciprocal x).q = x.p := rfl

theorem reciprocal_reciprocal (x : TOver R) : reciprocal (reciprocal x) = x := rfl

variable [CommRing R]

instance : Add (TOver R) := ⟨fun x y => ⟨x.p * y.q + y.p * x.q, x.q * y.q⟩⟩
instance : Mul (TOver R) := ⟨fun x y => ⟨x.p * y.p, x.q * y.q⟩⟩
instance : Neg (TOver R) := ⟨fun x => ⟨-x.p, x.q⟩⟩

@[simp] theorem add_p (x y : TOver R) : (x + y).p = x.p * y.q + y.p * x.q := rfl
@[simp] theorem add_q (x y : TOver R) : (x + y).q = x.q * y.q := rfl
@[simp] theorem mul_p (x y : TOver R) : (x * y).p = x.p * y.p := rfl
@[simp] theorem mul_q (x y : TOver R) : (x * y).q = x.q * y.q := rfl
@[simp] theorem neg_p (x : TOver R) : (-x).p = -x.p := rfl
@[simp] theorem neg_q (x : TOver R) : (-x).q = x.q := rfl

/-! ## Over ℤ it is `T` -/

/-- `T` is `TOver ℤ`. -/
def ofT : T ≃ TOver ℤ where
  toFun x := ⟨x.p, x.q⟩
  invFun x := ⟨x.p, x.q⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ofT_plus (x y : T) : ofT (x + y) = ofT x + ofT y := rfl
theorem ofT_times (x y : T) : ofT (x * y) = ofT x * ofT y := rfl
theorem ofT_neg (x : T) : ofT (-x) = -ofT x := rfl
theorem ofT_reciprocal (x : T) : ofT (T.reciprocal x) = reciprocal (ofT x) := rfl

/-! ## The reciprocal leaves `pq` -/

/-- `x · (1/x) = T(pq, pq)`. -/
theorem times_reciprocal_self (x : TOver R) : x * reciprocal x = ⟨x.p * x.q, x.p * x.q⟩ := by
  ext <;> simp [mul_comm]

/-- In a domain the residue is zero exactly when a coordinate is: the value is `0` or it is infinite. -/
theorem residue_eq_zero_iff [IsDomain R] (x : TOver R) : x.p * x.q = 0 ↔ x.p = 0 ∨ x.q = 0 :=
  mul_eq_zero

/-- In a domain, `* k` can be undone exactly when neither coordinate of `k` is zero. -/
theorem times_cancel_iff [IsDomain R] (k : TOver R) :
    (∀ x x' : TOver R, x * k = x' * k → x = x') ↔ k.p ≠ 0 ∧ k.q ≠ 0 := by
  constructor
  · intro h
    refine ⟨fun hp => ?_, fun hq => ?_⟩
    · have := h ⟨1, 1⟩ ⟨0, 1⟩ (by ext <;> simp [hp])
      exact one_ne_zero (congrArg TOver.p this)
    · have := h ⟨1, 1⟩ ⟨1, 0⟩ (by ext <;> simp [hq])
      exact one_ne_zero (congrArg TOver.q this)
  · rintro ⟨hp, hq⟩ x x' h
    have h1 := congrArg TOver.p h
    have h2 := congrArg TOver.q h
    simp only [mul_p, mul_q] at h1 h2
    ext
    · exact mul_right_cancel₀ hp h1
    · exact mul_right_cancel₀ hq h2

/-- In a domain, `+ k` can be undone exactly when the denominator of `k` is not zero. -/
theorem plus_cancel_iff [IsDomain R] (k : TOver R) :
    (∀ x x' : TOver R, x + k = x' + k → x = x') ↔ k.q ≠ 0 := by
  constructor
  · intro h hq
    have := h ⟨1, 1⟩ ⟨0, 1⟩ (by ext <;> simp [hq])
    exact one_ne_zero (congrArg TOver.p this)
  · intro hq x x' h
    have h1 := congrArg TOver.p h
    have h2 := congrArg TOver.q h
    simp only [add_p, add_q] at h1 h2
    have hq' : x.q = x'.q := mul_right_cancel₀ hq h2
    rw [hq'] at h1
    ext
    · exact mul_right_cancel₀ hq (add_right_cancel h1)
    · exact hq'

end TOver
