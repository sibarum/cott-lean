import CottLean.Float.Tropical

/-!
# `TZ(p,q,z) = (p/q)·0^z`: a zero in `p` or `q` moves the grade

A coordinate that is `0` is never stored. It is rewritten into the grade:

```
TZ(0,1,0) = TZ(1,1,1)     p = 0:  0   = 0^1
TZ(1,0,0) = TZ(1,1,-1)    q = 0:  1/0 = 0^(-1)
TZ(0,0,0) = TZ(1,1,0)     both:   0/0 = 0·0^(-1) = 0^0 = 1
```

`norm p q z` is that rewrite, into `Res`: the grade is `z` plus one for a zero in `p` and minus one for a
zero in `q`, and the coefficient is `p/q` with a zero coordinate read as `1`. So `0/0` is not a special
case. It is the grade cancelling, which is `mul_erases_grade` at the coefficients `1, 1`.

* `rewrite_p`, `rewrite_q`, `rewrite_pq`: the three rewrites.
* `line1`, `norm_grade_shift`, `line3`: `TZ(p,q,0)·TZ(0,0,0) = TZ(p,q,0)`, `TZ(p,q,0)·TZ(1,1,z) =
  TZ(p,q,z)`, and `TZ(p,q,0) + TZ(0,0,1) = TZ(p,q,0)` (for `p ≠ 0`, so the left term is below grade `1`).
* `norm_mul_of_ne`: away from zeros, `norm` is a homomorphism.

What `norm` is not:

* `raw_mul_forgets`, `raw_mul_counts_zeros`: it is not a homomorphism from the raw pair product. `0·3`
  in `ℚ` is `0`, and it has forgotten the `3` and that two zeros met. The product has to be taken after
  `norm`, where the `3` and the grades are still there.
* `raw_add_infinity`: nor from the raw pair sum. `∞ + ∞ = (1·0 + 0·1)/(0·0) = 0/0`, which `norm` reads as
  `1`, while the graded sum is `2·∞`. Addition has to be taken after `norm` too.
* `add` stays partial (`Res.add_cancel`): an exact zero from cancellation has no honest grade, so it is
  not rewritten to one.
-/

namespace TZ

/-- The rewrite: a zero coordinate becomes a grade, and is read as `1` in the coefficient. -/
def norm (p q : ℚ) (z : ℤ) : Res :=
  ⟨z + (Res.ofQ p).k - (Res.ofQ q).k, (Res.ofQ p).c / (Res.ofQ q).c,
    div_ne_zero (Res.ofQ p).ne (Res.ofQ q).ne⟩

/-- `T(p,q)` is the grade-`0` slice. -/
def T (p q : ℚ) : Res := norm p q 0

theorem ofQ_k_of_ne {x : ℚ} (hx : x ≠ 0) : (Res.ofQ x).k = 0 := by
  simp [Res.ofQ, hx, Res.plain]

theorem ofQ_k_nonneg (x : ℚ) : 0 ≤ (Res.ofQ x).k := by
  by_cases hx : x = 0
  · simp [Res.ofQ, hx, Res.zeroCoord]
  · simp [ofQ_k_of_ne hx]

theorem norm_of_ne {p q : ℚ} (hp : p ≠ 0) (hq : q ≠ 0) (z : ℤ) :
    norm p q z = ⟨z, p / q, div_ne_zero hp hq⟩ := by
  ext <;> simp [norm, Res.ofQ, Res.plain, hp, hq]

/-! ## The three rewrites -/

theorem rewrite_p : T 0 1 = ⟨1, 1, one_ne_zero⟩ := by
  ext <;> simp [T, norm, Res.ofQ, Res.zeroCoord, Res.plain]

theorem rewrite_q : T 1 0 = ⟨-1, 1, one_ne_zero⟩ := by
  ext <;> simp [T, norm, Res.ofQ, Res.zeroCoord, Res.plain]

theorem rewrite_pq : T 0 0 = ⟨0, 1, one_ne_zero⟩ := by
  ext <;> simp [T, norm, Res.ofQ, Res.zeroCoord]

/-- The rule for a zero numerator, for every `q` and `g`: `TZ(0,q,g) = TZ(1,q,g+1)`. -/
theorem rule_p (q : ℚ) (g : ℤ) : norm 0 q g = norm 1 q (g + 1) := by
  by_cases hq : q = 0 <;> ext <;> simp [norm, Res.ofQ, Res.zeroCoord, Res.plain, hq] <;> omega

/-- The rule for a zero denominator, for every `p` and `g`: `TZ(p,0,g) = TZ(p,1,g-1)`. -/
theorem rule_q (p : ℚ) (g : ℤ) : norm p 0 g = norm p 1 (g - 1) := by
  by_cases hp : p = 0 <;> ext <;> simp [norm, Res.ofQ, Res.zeroCoord, Res.plain, hp] <;> omega

/-- `0/0` at grade `z` is just the grade: `ε^z`. -/
theorem norm_zero_zero (z : ℤ) : norm 0 0 z = ⟨z, 1, one_ne_zero⟩ := by
  ext <;> simp [norm, Res.ofQ, Res.zeroCoord]

/-! ## The three lines -/

private theorem mul_one_res (x : Res) :
    Res.mul NZRounding.identity x ⟨0, 1, one_ne_zero⟩ = x := by
  ext <;> simp [Res.mul, NZRounding.identity]

/-- `TZ(p,q,0) · TZ(0,0,0) = TZ(p,q,0)`: `0/0` is the multiplicative identity, and erases nothing. -/
theorem line1 (p q : ℚ) :
    Res.mul NZRounding.identity (norm p q 0) (norm 0 0 0) = norm p q 0 := by
  rw [norm_zero_zero]; exact mul_one_res _

/-- `TZ(p,q,0) · TZ(1,1,z) = TZ(p,q,z)`; at `z = 1` this is the second line. -/
theorem norm_grade_shift (p q : ℚ) (z : ℤ) :
    Res.mul NZRounding.identity (norm p q 0) (norm 1 1 z) = norm p q z := by
  rw [norm_of_ne one_ne_zero one_ne_zero]
  ext
  · simp [Res.mul, norm]; omega
  · simp [Res.mul, norm, NZRounding.identity]

/-- `TZ(p,q,0) + TZ(0,0,1) = TZ(p,q,0)`: the grade-`1` zero is below the value. Needs `p ≠ 0`: at `p = 0`
the left term is itself a zero, of grade `≥ 1`. -/
theorem line3 {p : ℚ} (hp : p ≠ 0) (q : ℚ) :
    Res.add NZRounding.identity (norm p q 0) (norm 0 0 1) = some (norm p q 0) := by
  apply Res.add_of_lt
  have := ofQ_k_nonneg q
  simp [norm, ofQ_k_of_ne hp]
  omega

/-! ## Away from zeros, `norm` is a homomorphism -/

theorem norm_mul_of_ne {p q p' q' : ℚ} (hp : p ≠ 0) (hq : q ≠ 0) (hp' : p' ≠ 0) (hq' : q' ≠ 0)
    (z z' : ℤ) :
    Res.mul NZRounding.identity (norm p q z) (norm p' q' z') = norm (p * p') (q * q') (z + z') := by
  rw [norm_of_ne hp hq, norm_of_ne hp' hq', norm_of_ne (mul_ne_zero hp hp') (mul_ne_zero hq hq')]
  ext <;> simp [Res.mul, NZRounding.identity, mul_div_mul_comm]

/-! ## Where it is not: the raw pair operations forget -/

/-- `0·3 = 0` in `ℚ` has forgotten the `3`. After `norm` it is `3ε`. -/
theorem raw_mul_forgets :
    norm (0 * 3) (1 * 1) 0 ≠ Res.mul NZRounding.identity (norm 0 1 0) (norm 3 1 0) := by
  intro h
  have := congrArg Res.c h
  simp [norm, Res.mul, NZRounding.identity, Res.ofQ, Res.zeroCoord, Res.plain] at this

/-- `0·0 = 0` in `ℚ` has forgotten that two zeros met: grade `1`, where `ε·ε` has grade `2`. -/
theorem raw_mul_counts_zeros :
    (norm (0 * 0) (1 * 1) 0).k = 1 ∧
      (Res.mul NZRounding.identity (norm 0 1 0) (norm 0 1 0)).k = 2 := by
  simp [norm, Res.mul, Res.ofQ, Res.zeroCoord, Res.plain]

/-- `∞ + ∞`: the raw pair sum is `0/0`, read as `1`. The graded sum is `2·∞`. -/
theorem raw_add_infinity :
    norm (1 * 0 + 0 * 1) (0 * 0) 0 = ⟨0, 1, one_ne_zero⟩ ∧
      Res.add NZRounding.identity (norm 1 0 0) (norm 1 0 0) = some ⟨-1, 2, by norm_num⟩ := by
  have h : norm 1 0 0 = ⟨-1, 1, one_ne_zero⟩ := rewrite_q
  refine ⟨?_, ?_⟩
  · simpa [T] using rewrite_pq
  · rw [h]; simp [Res.add, NZRounding.identity]; norm_num

end TZ
