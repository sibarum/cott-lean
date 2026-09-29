import CottLean.Float.Residue

/-!
# Adding residues: the grade is tropical

`Res.mul` adds grades. Addition takes the smaller one. `ε^k + ε^l` is dominated by the larger term,
and the larger term is the one with the lower grade, since `ε` is small. So grades form the tropical
semiring `(ℤ, min, +)`, with `min` for `+` and `+` for `·`.

```
Res k c + Res l d = Res k c              if k < l    (the term of grade l is below the value)
                  = Res l d              if l < k
                  = Res k (c + d)        if k = l
```

* `add_grade`: the grade of a sum is the `min`, when the sum is defined.
* `add_comm`, `add_of_lt`: `+` commutes, and the lower term is dropped whole, coefficient and all.
* `mul_add_grade`: `·` distributes over `+` at the level of grades, `k + min l m = min (k+l) (k+m)`.
  This is what makes the grades a semiring and not just two operations.
* `add_cancel`: equal grades whose coefficients sum to `0` have no defined sum. That is the additive
  zero, which is not the held zero `ε` (`Epsilon.held_zero_not_equiv_zero`), and it is still an
  erasure. `add` returns `none` there instead of writing a `0`.
-/

namespace Res

variable (r : NZRounding)

/-- Tropical addition. `none` exactly when equal grades cancel. -/
def add (x y : Res) : Option Res :=
  if x.k < y.k then some x
  else if y.k < x.k then some y
  else if h : r.rnd (x.c + y.c) = 0 then none
  else some ⟨x.k, r.rnd (x.c + y.c), h⟩

theorem add_of_lt {x y : Res} (h : x.k < y.k) : add r x y = some x := by
  simp [add, h]

theorem add_of_gt {x y : Res} (h : y.k < x.k) : add r x y = some y := by
  simp [add, h, not_lt.mpr h.le]

theorem add_comm (x y : Res) : add r x y = add r y x := by
  rcases lt_trichotomy x.k y.k with h | h | h
  · rw [add_of_lt r h, add_of_gt r h]
  · simp [add, h, _root_.add_comm]
  · rw [add_of_gt r h, add_of_lt r h]

/-- The grade of a defined sum is the smaller grade. -/
theorem add_grade {x y z : Res} (h : add r x y = some z) : z.k = min x.k y.k := by
  rcases lt_trichotomy x.k y.k with hk | hk | hk
  · rw [add_of_lt r hk] at h; cases h; simp [hk.le]
  · simp only [add, hk, lt_self_iff_false, if_false] at h
    split_ifs at h with h0
    cases h; simp [hk]
  · rw [add_of_gt r hk] at h; cases h; simp [hk.le]

/-- The lower term is invisible, and a sum with a term below the value keeps the value's coefficient. -/
theorem add_lt_coeff {x y z : Res} (hk : x.k < y.k) (h : add r x y = some z) : z.c = x.c := by
  rw [add_of_lt r hk] at h; cases h; rfl

/-- Equal grades whose coefficients cancel have no sum: the additive zero is not written. -/
theorem add_cancel (x y : Res) (hk : x.k = y.k) (hc : r.rnd (x.c + y.c) = 0) : add r x y = none := by
  simp [add, hk, hc]

/-- `(ε, 1) + (ε, −1)` under exact arithmetic. -/
theorem eps_minus_eps : add NZRounding.identity ⟨1, 1, one_ne_zero⟩ ⟨1, -1, by norm_num⟩ = none := by
  simp [add, NZRounding.identity]

/-- The grades are a tropical semiring: `·` distributes over `+`. -/
theorem mul_add_grade (k l m : ℤ) : k + min l m = min (k + l) (k + m) := by omega

/-- The same, for the operations on residues: the smaller grade of the products is the product of the
smaller grade. -/
theorem mul_add_distrib_grade {x y z w u : Res} (hyz : add r y z = some w)
    (hxy : add r (mul r x y) (mul r x z) = some u) : u.k = (mul r x w).k := by
  have h1 := add_grade r hxy
  have h2 := add_grade r hyz
  simp only [mul_grade] at *
  omega

end Res

namespace TR

/-- `T(a,b) + T(c,d) = T(ad + bc, bd)`, with tropical addition in the numerator. Undefined when the
numerator's two terms cancel. -/
def plus (r : NZRounding) (x y : TR) : Option TR :=
  (Res.add r (Res.mul r x.p y.q) (Res.mul r y.p x.q)).map fun p => ⟨p, Res.mul r x.q y.q⟩

theorem plus_comm (r : NZRounding) (x y : TR) : plus r x y = plus r y x := by
  simp only [plus, Res.add_comm r (Res.mul r x.p y.q), Res.mul_comm r x.q y.q]

end TR
