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
