import CottLean.Float.Nested

/-!
# Two erasures

Both operations forget something at one place, and it is the same kind of place.

```
c + (−c)       = 0       the additive identity: the coefficient is forgotten
ε^n · ε^(−n)   = 1       the multiplicative identity: the grade is forgotten
```

* `add_erases_coefficient`: at equal grades, `Res k c + Res k (−c)` has no value, and it has none for
  every `c`. The pair `(k, c)` is not recoverable from the fact that it cancelled.
* `mul_erases_grade`: `Res n c · Res (−n) d` is the plain coordinate `c·d` for every `n`. The `n` is
  not recoverable from the fact that it cancelled.
* `erasure_dual`: the two are one shape. Each operation acts on one half of a residue, `add` on the
  coefficient and `mul` on the grade, and each erases exactly the half it acts on, exactly when it
  reaches that half's identity. The other half passes through untouched.
* `flatten_erases_grade`: at level two, `flatten` is a product, so it erases the grade wherever the two
  grades that meet sum to `0`.

So `Res.mul` is total but not injective, and `Res.add` is not even total. They fail in the same
way, at the two identities.
-/

namespace Res

/-- Multiplying a zero of any grade by a pole of the opposite grade gives the same plain coordinate. -/
theorem mul_erases_grade (r : NZRounding) (n m : ℤ) (c d : ℚ) (hc : c ≠ 0) (hd : d ≠ 0) :
    mul r ⟨n, c, hc⟩ ⟨-n, d, hd⟩ = mul r ⟨m, c, hc⟩ ⟨-m, d, hd⟩ := by
  ext <;> simp [mul]

/-- Adding a term to its negative gives no value, whatever the term was. -/
theorem add_erases_coefficient (k : ℤ) (c : ℚ) (hc : c ≠ 0) :
    add NZRounding.identity ⟨k, c, hc⟩ ⟨k, -c, neg_ne_zero.mpr hc⟩ = none := by
  simp [add, NZRounding.identity]

/-- Two different pairs of inputs, one output, in each operation. -/
theorem erasure_dual :
    (mul NZRounding.identity ⟨1, 2, by norm_num⟩ ⟨-1, 3, by norm_num⟩ =
      mul NZRounding.identity ⟨5, 2, by norm_num⟩ ⟨-5, 3, by norm_num⟩ ∧
      (⟨1, 2, by norm_num⟩ : Res) ≠ ⟨5, 2, by norm_num⟩) ∧
    (add NZRounding.identity ⟨0, 2, by norm_num⟩ ⟨0, -2, by norm_num⟩ =
      add NZRounding.identity ⟨0, 3, by norm_num⟩ ⟨0, -3, by norm_num⟩ ∧
      (⟨0, 2, by norm_num⟩ : Res) ≠ ⟨0, 3, by norm_num⟩) := by
  refine ⟨⟨mul_erases_grade _ 1 5 2 3 (by norm_num) (by norm_num), ?_⟩, ?_, ?_⟩
  · intro h; have := congrArg Res.k h; simp at this
  · rw [add_erases_coefficient 0 2 (by norm_num), add_erases_coefficient 0 3 (by norm_num)]
  · intro h; have := congrArg Res.c h; simp at this

end Res

namespace TR2

/-- `flatten` erases the grade of a coordinate when the two grades that meet cancel. -/
theorem flatten_erases_grade (r : NZRounding) (x : TR2) (h : x.p.p.k + x.q.q.k = 0) :
    (flatten r x).p.k = 0 := by
  simpa [flatten, TR.times, Res.mul, recip] using h

end TR2

/-! ## The converse: nowhere else

The erasures above are the whole loss. Under exact arithmetic (`NZRounding.identity`):

* `mul_plain_iff`: a product is plain exactly when the grades cancel. So a product that is not plain
  still shows that a residue was involved: nothing is hidden away from the identity.
* `mul_left_cancel`, `mul_right_cancel`, `mul_recover`: given a product and one factor, the other comes
  back exactly, whatever the grades, at the identity too. No `Res` has norm `0`, so unlike `T`, where
  `x · 0` loses `p`, no factor forgets its partner.
* `add_none_iff`: a sum has no value exactly when the grades are equal and the coefficients cancel.
* `add_recover`, `add_left_cancel_of_eq_grade`: at equal grades, given a sum and one term, the other
  comes back, whether the sum has a value or not.
* `add_drop`: at different grades the higher term is gone. This loss is real and is not at the identity;
  it is the price of keeping only the leading term. `Tail` is what keeps it.
-/

namespace Res

/-- The product is plain exactly when the grades cancel. -/
theorem mul_plain_iff (r : NZRounding) (x y : Res) : (mul r x y).k = 0 ↔ x.k + y.k = 0 := Iff.rfl

/-- Given the product and the left factor, the right factor is determined. -/
theorem mul_left_cancel {x y y' : Res} (h : mul NZRounding.identity x y = mul NZRounding.identity x y') :
    y = y' := by
  have hk := congrArg Res.k h
  have hc := congrArg Res.c h
  simp only [mul, NZRounding.identity, id] at hk hc
  ext
  · omega
  · exact mul_left_cancel₀ x.ne hc

theorem mul_right_cancel {x x' y : Res} (h : mul NZRounding.identity x y = mul NZRounding.identity x' y) :
    x = x' := by
  rw [mul_comm, mul_comm NZRounding.identity x'] at h
  exact mul_left_cancel h

/-- The partner of a factor, from the product. -/
theorem mul_recover (x z : Res) : mul NZRounding.identity x ⟨z.k - x.k, z.c / x.c, div_ne_zero z.ne x.ne⟩ = z := by
  ext
  · simp [mul]
  · simp only [mul, NZRounding.identity, id]; field_simp [x.ne]

/-- A sum has no value exactly when the grades are equal and the coefficients cancel. -/
theorem add_none_iff (x y : Res) :
    add NZRounding.identity x y = none ↔ x.k = y.k ∧ x.c + y.c = 0 := by
  unfold add
  simp only [NZRounding.identity, id]
  by_cases h1 : x.k < y.k
  · simp [h1]; intro h; omega
  by_cases h2 : y.k < x.k
  · simp [h1, h2]; intro h; omega
  have : x.k = y.k := by omega
  simp [h1, h2, this]

/-- At equal grades, the sum's coefficient is the total, and the other term is the difference. -/
theorem add_recover {x y z : Res} (hk : x.k = y.k) (h : add NZRounding.identity x y = some z) :
    z.k = x.k ∧ z.c = x.c + y.c := by
  unfold add at h
  simp only [NZRounding.identity, id] at h
  have h1 : ¬ x.k < y.k := by omega
  have h2 : ¬ y.k < x.k := by omega
  simp only [h1, h2, if_false] at h
  by_cases h0 : x.c + y.c = 0
  · simp [h0] at h
  · simp [h0] at h; cases h; exact ⟨rfl, rfl⟩

/-- At equal grades, a term is determined by the sum and the other term, cancelled or not. -/
theorem add_left_cancel_of_eq_grade {x y y' : Res} (hy : x.k = y.k) (hy' : x.k = y'.k)
    (h : add NZRounding.identity x y = add NZRounding.identity x y') : y = y' := by
  have hkk : y.k = y'.k := hy.symm.trans hy'
  by_cases hn : x.c + y.c = 0
  · have h1 : add NZRounding.identity x y = none := (add_none_iff x y).2 ⟨hy, hn⟩
    rw [h1] at h
    have h2 := ((add_none_iff x y').1 h.symm).2
    ext
    · exact hkk
    · linarith
  · obtain ⟨z, hz⟩ : ∃ z, add NZRounding.identity x y = some z := by
      cases hh : add NZRounding.identity x y with
      | none => exact absurd ((add_none_iff x y).1 hh).2 hn
      | some z => exact ⟨z, rfl⟩
    have hz' : add NZRounding.identity x y' = some z := h ▸ hz
    have e1 := (add_recover hy hz).2
    have e2 := (add_recover hy' hz').2
    ext
    · exact hkk
    · linarith

/-- Different grades: the higher term is dropped, so different terms give one sum. -/
theorem add_drop {x y y' : Res} (hy : x.k < y.k) (hy' : x.k < y'.k) :
    add NZRounding.identity x y = add NZRounding.identity x y' := by
  rw [add_of_lt _ hy, add_of_lt _ hy']

/-- ... including terms that really are different. -/
theorem add_drop_ne : ∃ x y y' : Res, y ≠ y' ∧
    add NZRounding.identity x y = add NZRounding.identity x y' :=
  ⟨⟨0, 1, one_ne_zero⟩, ⟨1, 1, one_ne_zero⟩, ⟨2, 1, one_ne_zero⟩,
    by intro h; have := congrArg Res.k h; simp at this,
    add_drop (by norm_num) (by norm_num)⟩

end Res
