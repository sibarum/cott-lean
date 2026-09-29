import CottLean.Float.Tropical

/-!
# `TR2(TR(a,b), TR(c,d))`: a pair of float pairs

`Nested.Basic` puts pairs inside pairs over `ℤ`. Here the coordinates are `TR`, whose own coordinates
are residues (`Res`), so no coordinate at any level is ever `0`. The operations are `T2`'s:

```
TR2(p₁,q₁) · TR2(p₂,q₂) = TR2(p₁·p₂, q₁·q₂)
TR2(p₁,q₁) + TR2(p₂,q₂) = TR2(p₁·q₂ + q₁·p₂, q₁·q₂)
flatten TR2(A, B)       = A · reciprocal B,   so TR2(T(a,b), T(c,d)) ↦ T(ad, bc)
```

* `flatten_grade`: `flatten` adds grades and does nothing else to them, at every rounding. `(a, d)` and
  `(b, c)` are the pairs that meet.
* `flatten_of`, `of_times`, `flatten_times`: with exact arithmetic the embedding is a section of
  `flatten`, and `flatten` respects `·`.
* `flatten` is total: it is a `TR.times`, and a product of residues is a residue. It is a product, and a product of residues is a residue. A
  quotient `A / B` that a float would turn into `0/0` or `x/0` is here always a pair of coordinates.
* `plus` is the only partial operation, and only where the additive zero appears (`plus_cancel`). The
  multiplicative zero has been written as `ε` all the way down.
-/

/-- A traction whose coordinates are residue-pairs. -/
@[ext] structure TR2 where
  p : TR
  q : TR

namespace TR2

variable (r : NZRounding)

/-- `T(b,a)`: swap the coordinates. -/
def recip (x : TR) : TR := ⟨x.q, x.p⟩

/-- `T(a,b)` as `TR2(T(a,1), T(b,1))`, with `1` the plain coordinate. -/
def one : Res := Res.plain 1 one_ne_zero

def of (x : TR) : TR2 := ⟨⟨x.p, one⟩, ⟨x.q, one⟩⟩

def times (x y : TR2) : TR2 := ⟨TR.times r x.p y.p, TR.times r x.q y.q⟩

/-- `A / B` as a pair: `A · reciprocal B`. -/
def flatten (x : TR2) : TR := TR.times r x.p (recip x.q)

/-- Inner `+`: cancels only when the additive zero appears. -/
def plus (x y : TR2) : Option TR2 :=
  (TR.plus r (TR.times r x.p y.q) (TR.times r x.q y.p)).map fun p => ⟨p, TR.times r x.q y.q⟩

/-! ## Grades -/

theorem flatten_grade (x : TR2) :
    (flatten r x).p.k = x.p.p.k + x.q.q.k ∧ (flatten r x).q.k = x.p.q.k + x.q.p.k := ⟨rfl, rfl⟩

/-! ## Exactly -/

private theorem mul_one_right (x : Res) : Res.mul NZRounding.identity x one = x := by
  ext <;> simp [Res.mul, one, Res.plain, NZRounding.identity]

private theorem mul_one_left (x : Res) : Res.mul NZRounding.identity one x = x := by
  ext <;> simp [Res.mul, one, Res.plain, NZRounding.identity]

private theorem mul_one_one : Res.mul NZRounding.identity one one = one := by
  ext <;> simp [Res.mul, one, Res.plain, NZRounding.identity]

theorem flatten_of (x : TR) : flatten NZRounding.identity (of x) = x := by
  ext <;> simp [flatten, of, recip, TR.times, mul_one_right, mul_one_left]

theorem of_injective : Function.Injective of := by
  intro x y h
  have hp := congrArg (fun z => z.p.p) h
  have hq := congrArg (fun z => z.q.p) h
  exact TR.ext hp hq

theorem of_times (x y : TR) :
    of (TR.times NZRounding.identity x y) = times NZRounding.identity (of x) (of y) := by
  ext <;> simp [of, times, TR.times, mul_one_one]

theorem flatten_times (x y : TR2) :
    flatten NZRounding.identity (times NZRounding.identity x y) =
      TR.times NZRounding.identity (flatten NZRounding.identity x) (flatten NZRounding.identity y) := by
  have key : ∀ a b c d : Res, Res.mul NZRounding.identity (Res.mul NZRounding.identity a b)
      (Res.mul NZRounding.identity c d) =
      Res.mul NZRounding.identity (Res.mul NZRounding.identity a c) (Res.mul NZRounding.identity b d) := by
    intro a b c d
    ext <;> simp [Res.mul, NZRounding.identity] <;> ring
  ext <;> simp [flatten, times, recip, TR.times, key]

/-! ## The one partial operation -/

/-- `1/1 + (−1)/1`: the additive zero, and the only place `plus` has no value. -/
theorem plus_cancel :
    plus NZRounding.identity
      (of ⟨Res.plain 1 one_ne_zero, Res.plain 1 one_ne_zero⟩)
      (of ⟨Res.plain (-1) (by norm_num), Res.plain 1 one_ne_zero⟩) = none := by
  simp [plus, of, one, TR.plus, TR.times, Res.add, Res.mul, Res.plain, NZRounding.identity]

end TR2
