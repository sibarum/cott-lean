import CottLean.Float.Basic

/-!
# A zero that is never written

A rounded `TF` has to put something in a coordinate that came out `0`, and a float `0` forgets the
factor it came from. Here a coordinate is never `0`. It is a `Res`: a nonzero coefficient `c` and a
grade `k`, read as `c·ε^k`, where `ε` is the zero that was met.

```
Res 0 c          a plain coordinate, the number c
Res 1 c          a zero that remembers c
Res (-1) c       a pole that remembers c
Res a b * Res c d = Res (a + c) (b * d)
```

The grade adds and the coefficient multiplies, so a zero and a pole meet and the residue comes back as
a plain coordinate: `Res 1 1 * Res (-1) 3 = Res 0 3`.

* `mul_grade`: the grade of a product is the sum of the grades, whatever the rounding does to the
  coefficients. The bookkeeping never rounds.
* `mul_zero_cancel`: a zero and a pole cancel and leave the product of their coefficients.
* `st_eq_of_grade_ne`: while the grade is not `0` the coefficient cannot be seen in the value (`st`).
* `residue_visible_after_cancel`: but it is still there. Two zeros that read the same differ once a
  pole cancels them.
* `zeroCoord`: `0` is written `Res 1 1`, and `hold_ne`: no zero written this way equals a plain one.
-/

/-- A rounding that never rounds a nonzero number to `0`, so a coefficient stays nonzero. -/
structure NZRounding extends TF.Rounding where
  ne_zero : ∀ x : ℚ, x ≠ 0 → rnd x ≠ 0

/-- The identity is a rounding with nothing lost: exact arithmetic. -/
def NZRounding.identity : NZRounding where
  rnd := id
  bound := 0
  exact := fun _ _ => rfl
  ne_zero := fun _ h => h

/-- `c · ε^k` with `c ≠ 0`. -/
@[ext] structure Res where
  k : ℤ
  c : ℚ
  ne : c ≠ 0

namespace Res

variable (r : NZRounding)

/-- The product: grades add, coefficients multiply and round. -/
def mul (x y : Res) : Res := ⟨x.k + y.k, r.rnd (x.c * y.c), r.ne_zero _ (mul_ne_zero x.ne y.ne)⟩

/-- A plain coordinate: grade `0`. -/
def plain (c : ℚ) (h : c ≠ 0) : Res := ⟨0, c, h⟩

/-- The zero that is met, `ε`: the only way a zero is written. -/
def zeroCoord : Res := ⟨1, 1, one_ne_zero⟩

/-- A coordinate from a number: `0` becomes `ε`, anything else is plain. -/
def ofQ (x : ℚ) : Res := if h : x = 0 then zeroCoord else plain x h

theorem mul_grade (x y : Res) : (mul r x y).k = x.k + y.k := rfl

theorem mul_comm (x y : Res) : mul r x y = mul r y x := by
  ext
  · simp [mul, _root_.add_comm]
  · simp [mul, _root_.mul_comm]

/-- Grades never suffer rounding, so they are associative even when the coefficients are not. -/
theorem mul_assoc_grade (x y z : Res) :
    (mul r (mul r x y) z).k = (mul r x (mul r y z)).k := by
  simp [mul, _root_.add_assoc]

/-- A zero and a pole cancel, and what is left is a plain coordinate holding both coefficients. -/
theorem mul_zero_cancel (x y : Res) (h : x.k + y.k = 0) :
    mul r x y = plain (r.rnd (x.c * y.c)) (r.ne_zero _ (mul_ne_zero x.ne y.ne)) := by
  ext
  · simpa [mul, plain] using h
  · rfl

/-- The example: `ε · (3/ε) = 3`. -/
theorem zero_times_pole :
    mul NZRounding.identity ⟨1, 1, one_ne_zero⟩ ⟨-1, 3, by norm_num⟩ = plain 3 (by norm_num) := by
  ext <;> simp [mul, plain, NZRounding.identity]

/-! ## What the value sees -/

/-- The standard part of a coordinate: `0`, a number, or a pole. -/
inductive Std where
  | zero
  | fin (c : ℚ)
  | pole
  deriving DecidableEq

def st (x : Res) : Std :=
  if x.k = 0 then .fin x.c else if 0 < x.k then .zero else .pole

/-- Away from grade `0` the coefficient does not show in the value. -/
theorem st_eq_of_grade_ne (x y : Res) (hk : x.k = y.k) (h0 : x.k ≠ 0) : st x = st y := by
  simp [st, hk] at *
  simp [h0]

/-- Two zeros with the same value and different coefficients: `ε` and `2ε`. -/
def e1 : Res := ⟨1, 1, one_ne_zero⟩
def e2 : Res := ⟨1, 2, by norm_num⟩
def pole : Res := ⟨-1, 1, one_ne_zero⟩

theorem residue_invisible : st e1 = st e2 := by decide +kernel

/-- Cancelled by the same pole, they are `1` and `2`: nothing about them was forgotten. -/
theorem residue_visible_after_cancel :
    st (mul NZRounding.identity e1 pole) ≠ st (mul NZRounding.identity e2 pole) := by
  simp [st, mul, e1, e2, pole, NZRounding.identity]

/-- Written this way, no zero equals a plain coordinate. -/
theorem zeroCoord_ne_plain (c : ℚ) (h : c ≠ 0) : zeroCoord ≠ plain c h := by
  intro e; have := congrArg Res.k e; simp [zeroCoord, plain] at this

end Res

/-- `T` whose coordinates are `Res`: no coordinate is ever `0`. -/
@[ext] structure TR where
  p : Res
  q : Res

namespace TR

/-- The value-position product, rounded. -/
def times (r : NZRounding) (x y : TR) : TR := ⟨Res.mul r x.p y.p, Res.mul r x.q y.q⟩

/-- `x · 0`: the numerator gains a layer, where in `T` it is erased. -/
theorem times_zero_grade (r : NZRounding) (x : TR) :
    (times r x ⟨Res.zeroCoord, Res.plain 1 one_ne_zero⟩).p.k = x.p.k + 1 := rfl

/-- Exactly, `· 0` loses nothing: two pairs with the same product by `0` are equal. -/
theorem times_zero_injective (x y : TR)
    (h : times NZRounding.identity x ⟨Res.zeroCoord, Res.plain 1 one_ne_zero⟩ =
         times NZRounding.identity y ⟨Res.zeroCoord, Res.plain 1 one_ne_zero⟩) : x = y := by
  have hp := congrArg (fun z => z.p) h
  have hq := congrArg (fun z => z.q) h
  simp only [times, Res.mul, Res.zeroCoord, Res.plain, NZRounding.identity, id] at hp hq
  obtain ⟨k, c, hc⟩ := x.p; obtain ⟨k', c', hc'⟩ := y.p
  obtain ⟨l, d, hd⟩ := x.q; obtain ⟨l', d', hd'⟩ := y.q
  simp only [Res.mk.injEq] at hp hq
  ext <;> simp_all

end TR
