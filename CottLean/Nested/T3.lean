import CottLean.Nested.Basic
import CottLean.T.Recovery

/-!
# `T3(P, Q)`: a pair of pairs of pairs

A traction whose two coordinates are `T2`s, combined with the value position's own operations, as `T2`
combines `T`s:

```
T3(P₁,Q₁) + T3(P₂,Q₂) = T3(P₁·Q₂ + Q₁·P₂, Q₁·Q₂)
T3(P₁,Q₁) · T3(P₂,Q₂) = T3(P₁·P₂, Q₁·Q₂)
```

`T2` sits inside as `X ↦ T3(T2(X.p, 1), T2(X.q, 1))`, and so `T` sits inside as `of ∘ T2.of`. The question
this file measures is the one in the design notes: whether a level that mirrors the level above it loses
the same thing again.

## The embedding

* `of_plus`, `of_times`, `of_neg`, `of_reciprocal`: the embedding of `T2` respects every operation exactly.
* `flatten_of`: `flatten` undoes it.
* `flatten2_of_of`: so does the composite down to `T`. A flat pair taken two levels up over unit
  denominators, computed there and brought back, is where the flat computation lands (`flatten2_plus_of_of`,
  `flatten2_times_of_of`). Nesting over `1` adds nothing, at every depth.

## The projection

`flatten : T3 → T2` reads `T3(P, Q)` as `P / Q`.

* `flatten_times`, `flatten_neg`, `flatten_reciprocal`: it respects every operation but `+`.
* `flatten_plus`: `+` survives up to the same law as one level down. There, `T2.flatten_plus` multiplies both
  coordinates of the `T` by the integer `x.q.q · y.q.q`. Here, both coordinates of the `T2` are multiplied by
  the pair `x.q.q · y.q.q`. The residue does not change shape; it moves up a level.
* `flatten2_plus`: into `T`, the two levels compound. The level-3 residue becomes a scale by
  `k.p · k.q` (`T2.flatten_mul_mul`), and the level-2 residue is added on top.
* `flatten_plus_not_exact`: and the compound residue is really there.

## The leaves

`flatten2 = T2.flatten ∘ flatten` reads the eight integers at once (`flatten2_def`). The numerator is the
product of the four leaves reached by an even number of denominator steps, and the denominator the product
of the four reached by an odd number. That is `T2.flatten_def`'s pattern one level deeper: `p/q` of `p/q` of
`p/q`, and each step into a denominator turns the leaf over.

## What the denominator erases

* `flatten_recoverable_iff`: with `Q` fixed, the numerator comes back exactly when all four integers of `Q`
  are non-zero. At level 2 the condition was two integers; each level doubles the ways a zero can erase.
-/

open T

/-- `T3(P, Q)`: a traction whose coordinates are `T2`s. -/
@[ext]
structure T3 where
  /-- The numerator, a pair of pairs. -/
  p : T2
  /-- The denominator, a pair of pairs. -/
  q : T2
  deriving DecidableEq, Repr

namespace T3

/-! ## The operations -/

/-- `T3(P₁,Q₁) + T3(P₂,Q₂) = T3(P₁·Q₂ + Q₁·P₂, Q₁·Q₂)`. -/
def plus (x y : T3) : T3 := ⟨x.p * y.q + x.q * y.p, x.q * y.q⟩

/-- `T3(P₁,Q₁) · T3(P₂,Q₂) = T3(P₁·P₂, Q₁·Q₂)`. -/
def times (x y : T3) : T3 := ⟨x.p * y.p, x.q * y.q⟩

instance : Add T3 := ⟨plus⟩
instance : Mul T3 := ⟨times⟩

/-- `-T3(P, Q) = T3(-P, Q)`. -/
instance : Neg T3 := ⟨fun x => ⟨-x.p, x.q⟩⟩

/-- `T3(Q, P)`. -/
def reciprocal (x : T3) : T3 := ⟨x.q, x.p⟩

@[simp] theorem add_def (x y : T3) : x + y = ⟨x.p * y.q + x.q * y.p, x.q * y.q⟩ := rfl
@[simp] theorem mul_def (x y : T3) : x * y = ⟨x.p * y.p, x.q * y.q⟩ := rfl
@[simp] theorem neg_def (x : T3) : -x = ⟨-x.p, x.q⟩ := rfl

/-! ## The embedding -/

/-- `X ↦ T3(T2(X.p, 1), T2(X.q, 1))`: each coordinate becomes its own unit-denominator pair. -/
def of (x : T2) : T3 := ⟨⟨x.p, T.«1»⟩, ⟨x.q, T.«1»⟩⟩

theorem of_injective : Function.Injective of := by
  intro x y h
  exact T2.ext (congrArg (fun z => z.p.p) h) (congrArg (fun z => z.q.p) h)

theorem of_plus (x y : T2) : of (x + y) = of x + of y := by
  ext <;> simp [of, T.«1»]

theorem of_times (x y : T2) : of (x * y) = of x * of y := by
  ext <;> simp [of, T.«1»]

theorem of_neg (x : T2) : of (-x) = -of x := by
  ext <;> simp [of]

theorem of_reciprocal (x : T2) : of (T2.reciprocal x) = reciprocal (of x) := rfl

/-! ## The projection -/

/-- `T3(P, Q) ↦ P / Q`. -/
def flatten (x : T3) : T2 := x.p * T2.reciprocal x.q

@[simp] theorem flatten_def (x : T3) : flatten x = ⟨x.p.p * x.q.q, x.p.q * x.q.p⟩ := rfl

theorem flatten_of (x : T2) : flatten (of x) = x := by
  ext <;> simp [of, T.«1»]

theorem flatten_surjective : Function.Surjective flatten := fun x => ⟨of x, flatten_of x⟩

theorem flatten_times (x y : T3) : flatten (x * y) = flatten x * flatten y := by
  ext <;> simp <;> ring

theorem flatten_neg (x : T3) : flatten (-x) = -flatten x := by
  ext <;> simp

theorem flatten_reciprocal (x : T3) : flatten (reciprocal x) = T2.reciprocal (flatten x) := by
  ext <;> simp [reciprocal, T2.reciprocal] <;> ring

/-- `+` survives up to one level-3 residue: both coordinates multiplied by the pair `x.q.q · y.q.q`. -/
theorem flatten_plus (x y : T3) :
    flatten (x + y) =
      ⟨(flatten x + flatten y).p * (x.q.q * y.q.q), (flatten x + flatten y).q * (x.q.q * y.q.q)⟩ := by
  ext <;> simp only [flatten_def, add_def, T2.add_def, T2.mul_def, T.add_def, T.mul_def] <;> ring

/-- On the image of `of`, `+` survives exactly. -/
theorem flatten_plus_of (x y : T2) : flatten (of x + of y) = flatten (of x) + flatten (of y) := by
  rw [← of_plus, flatten_of, flatten_of, flatten_of]

/-! ## Down to `T` -/

/-- `T3 → T2 → T`. -/
def flatten2 (x : T3) : T := T2.flatten (flatten x)

/-- Multiplying both coordinates of a `T2` by the pair `k` scales its projection by `k.p · k.q`. -/
theorem _root_.T2.flatten_mul_mul (A B k : T) :
    T2.flatten ⟨A * k, B * k⟩ = scale (k.p * k.q) (T2.flatten ⟨A, B⟩) := by
  ext <;> simp [scale] <;> ring

/-- Into `T`, the level-3 residue becomes a scale and the level-2 residue is added on top. -/
theorem flatten2_plus (x y : T3) :
    flatten2 (x + y) =
      scale ((x.q.q * y.q.q).p * (x.q.q * y.q.q).q)
        (flatten2 x + flatten2 y + residue ((flatten x).q.q * (flatten y).q.q)) := by
  rw [flatten2, flatten_plus, T2.flatten_mul_mul, T2.flatten_plus]
  rfl

/-- The compound residue is really there: `+` does not survive the two levels. -/
theorem flatten_plus_not_exact :
    flatten2 (⟨T2.«1», ⟨T.«1», ⟨1, 2⟩⟩⟩ + ⟨T2.«1», ⟨T.«1», ⟨1, 2⟩⟩⟩) ≠
      flatten2 ⟨T2.«1», ⟨T.«1», ⟨1, 2⟩⟩⟩ + flatten2 ⟨T2.«1», ⟨T.«1», ⟨1, 2⟩⟩⟩ := by
  decide

theorem flatten2_of_of (x : T) : flatten2 (of (T2.of x)) = x := by
  rw [flatten2, flatten_of, T2.flatten_of]

/-- Nesting two levels over `1` adds nothing: `+` comes back to the flat `+`. -/
theorem flatten2_plus_of_of (x y : T) : flatten2 (of (T2.of x) + of (T2.of y)) = x + y := by
  rw [← of_plus, ← T2.of_plus, flatten2_of_of]

theorem flatten2_times_of_of (x y : T) : flatten2 (of (T2.of x) * of (T2.of y)) = x * y := by
  rw [← of_times, ← T2.of_times, flatten2_of_of]

/-! ## The leaves -/

/-- The numerator is the product of the leaves an even number of denominator steps down, and the
denominator of those an odd number. -/
theorem flatten2_def (x : T3) :
    flatten2 x =
      ⟨x.p.p.p * x.p.q.q * x.q.p.q * x.q.q.p, x.p.p.q * x.p.q.p * x.q.p.p * x.q.q.q⟩ := by
  ext <;> simp [flatten2] <;> ring

/-! ## What the denominator erases -/

/-- The numerator comes back exactly when all four integers of the denominator are non-zero. -/
theorem flatten_recoverable_iff (Q : T2) :
    (∀ P P', flatten ⟨P, Q⟩ = flatten ⟨P', Q⟩ → P = P') ↔
      Q.p.p ≠ 0 ∧ Q.p.q ≠ 0 ∧ Q.q.p ≠ 0 ∧ Q.q.q ≠ 0 := by
  rw [← and_assoc, and_comm (a := Q.p.p ≠ 0 ∧ Q.p.q ≠ 0),
    ← times_recoverable_iff, ← times_recoverable_iff]
  constructor
  · intro h
    refine ⟨fun a a' ha => ?_, fun a a' ha => ?_⟩
    · have := h ⟨a, T.«1»⟩ ⟨a', T.«1»⟩ (by ext <;> simp_all [T.«1»])
      exact congrArg T2.p this
    · have := h ⟨T.«1», a⟩ ⟨T.«1», a'⟩ (by ext <;> simp_all [T.«1»])
      exact congrArg T2.q this
  · rintro ⟨h₁, h₂⟩ P P' h
    have hp := congrArg T2.p h
    have hq := congrArg T2.q h
    simp only [flatten_def] at hp hq
    exact T2.ext (h₁ _ _ hp) (h₂ _ _ hq)

end T3
