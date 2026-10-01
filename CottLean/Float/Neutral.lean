import Mathlib

/-!
# A neutral element for both operations

`0` is additively invariant and `1` is multiplicatively invariant. `e` is both: `a ⊕ e = a` and
`a ⊗ e = a`. It is one element with two readings, chosen by the operation it sits in:

```
πA e = 0        read inside ⊕
πM e = 1        read inside ⊗
```

`πA` and `πM` are the two projections to `ℚ`. They agree everywhere except at `e`. Each is a homomorphism
for its own operation, so the classical equations hold after projection. Nothing else is required:
associativity, commutativity and distributivity are not assumed.

* `Neutral`: the structure. No reversibility yet.
* `Neutral.Reversible`: uniform cancellation. Operands that agree at one partner agree at every partner.
  This is not injectivity: many routes may reach one value, but a value lost at one partner and kept at
  another is erasure.
* `Reversible.add_fixes_all`, `add_eq_self`: in a reversible structure, fixing one element fixes all of
  them, and then the fixer is `e`. A classical `0` or `1` that is not `e` moves every element, and is
  invisible only after projection (`zero_moves`, `one_moves`).
* `interchange_collapse`: Eckmann–Hilton. A shared unit plus the interchange law makes `⊕` and `⊗` one
  commutative operation. So interchange is the one law that must not be added.
* `interchange_degenerate`: and the projections then force `x + y = x · y` on every pair, which is false
  in `ℚ`.
-/

/-- Two total operations with a common identity `e`, and two projections to `ℚ` that read `e` as `0` and `1`
and agree elsewhere. -/
structure Neutral (S : Type*) where
  add : S → S → S
  mul : S → S → S
  e : S
  add_e : ∀ a, add a e = a
  e_add : ∀ a, add e a = a
  mul_e : ∀ a, mul a e = a
  e_mul : ∀ a, mul e a = a
  πA : S → ℚ
  πM : S → ℚ
  πA_e : πA e = 0
  πM_e : πM e = 1
  agree : ∀ x, x ≠ e → πA x = πM x
  πA_add : ∀ a b, πA (add a b) = πA a + πA b
  πM_mul : ∀ a b, πM (mul a b) = πM a * πM b

namespace Neutral

variable {S : Type*} (N : Neutral S)

/-- Totality is built in. Reversibility is *uniform cancellation*, not injectivity: operands that agree
at one partner agree at every partner. Many routes to one value are allowed (`x ⊕ 0 = x ⊕ e`); a value
that is lost at one partner and kept at another (`0 · 3 = 0 · 5`, but `1 · 3 ≠ 1 · 5`) is not. -/
structure Reversible : Prop where
  add_left : ∀ a b b', N.add a b = N.add a b' → ∀ c, N.add c b = N.add c b'
  add_right : ∀ a a' b, N.add a b = N.add a' b → ∀ c, N.add a c = N.add a' c
  mul_left : ∀ a b b', N.mul a b = N.mul a b' → ∀ c, N.mul c b = N.mul c b'
  mul_right : ∀ a a' b, N.mul a b = N.mul a' b → ∀ c, N.mul a c = N.mul a' c

/-! ## Fixing one element fixes all of them -/

/-- If `x` leaves one element alone under `⊕`, it leaves every element alone. -/
theorem Reversible.add_fixes_all {N : Neutral S} (h : N.Reversible) {a x : S} (hx : N.add a x = a) (c : S) :
    N.add c x = c :=
  (h.add_left a x N.e (hx.trans (N.add_e a).symm) c).trans (N.add_e c)

theorem Reversible.mul_fixes_all {N : Neutral S} (h : N.Reversible) {a x : S} (hx : N.mul a x = a) (c : S) :
    N.mul c x = c :=
  (h.mul_left a x N.e (hx.trans (N.mul_e a).symm) c).trans (N.mul_e c)

/-- Fixing everything forces `x = e`: the left identity gives `e ⊕ x = x`. -/
theorem Reversible.add_eq_self {N : Neutral S} (h : N.Reversible) {a x : S} (hx : N.add a x = a) :
    x = N.e := by
  have := h.add_fixes_all hx N.e
  rwa [N.e_add] at this

theorem Reversible.mul_eq_self {N : Neutral S} (h : N.Reversible) {a x : S} (hx : N.mul a x = a) :
    x = N.e := by
  have := h.mul_fixes_all hx N.e
  rwa [N.e_mul] at this

/-- A reversible structure cannot let a second element behave as `0`, even at a single element. Anything
other than `e` that projects to `0` additively moves every element, so `a ⊕ z ≠ a`, though
`πA (a ⊕ z) = πA a`. The classical `0` leaves a trace, and is `0` only after projection. -/
theorem Reversible.zero_moves {N : Neutral S} (h : N.Reversible) {z : S} (hz : z ≠ N.e) (a : S) :
    N.add a z ≠ a := fun hx => hz (h.add_eq_self hx)

theorem Reversible.one_moves {N : Neutral S} (h : N.Reversible) {u : S} (hu : u ≠ N.e) (a : S) :
    N.mul a u ≠ a := fun hx => hu (h.mul_eq_self hx)

/-! ## The one law to avoid: interchange -/

/-- The interchange law `(a ⊕ b) ⊗ (c ⊕ d) = (a ⊗ c) ⊕ (b ⊗ d)`. -/
def Interchange : Prop :=
  ∀ a b c d, N.mul (N.add a b) (N.add c d) = N.add (N.mul a c) (N.mul b d)

/-- Eckmann–Hilton: with a common unit, interchange makes `⊗` equal `⊕`. -/
theorem interchange_collapse (hI : N.Interchange) (a b : S) : N.mul a b = N.add a b := by
  have := hI a N.e N.e b
  simpa [N.add_e, N.e_add, N.mul_e, N.e_mul] using this

/-- ... and commutative. -/
theorem interchange_comm (hI : N.Interchange) (a b : S) : N.add a b = N.add b a := by
  have h1 := hI N.e a b N.e
  simp only [N.add_e, N.e_add, N.mul_e, N.e_mul] at h1
  rw [← interchange_collapse N hI a b]
  exact h1

/-- Under interchange the projections force `x + y = x · y` on any two non-`e` elements whose sum is not
`e`. That fails in `ℚ` (`1 + 1 ≠ 1 · 1`). -/
theorem interchange_degenerate (hI : N.Interchange) {x y : S} (hx : x ≠ N.e) (hy : y ≠ N.e)
    (hxy : N.add x y ≠ N.e) : N.πM x + N.πM y = N.πM x * N.πM y := by
  have hz : N.mul x y = N.add x y := interchange_collapse N hI x y
  have hne : N.mul x y ≠ N.e := by rw [hz]; exact hxy
  have h := N.πA_add x y
  rw [← hz, N.agree _ hne, N.πM_mul, N.agree x hx, N.agree y hy] at h
  exact h.symm

end Neutral

/-! ## The classical shadow

`Option ℚ` with `none` as `e`. It is a `Neutral`, so the spec is not empty. It is not reversible: `a ⊕ e` and
`a ⊕ 0` both give `a`. That failure is the content of `Reversible.zero_moves`: reversibility needs `0` and
`1` to be different elements from `e`, and `ℚ` has no room for that. -/

def shadow : Neutral (Option ℚ) where
  add a b := match a, b with
    | some x, some y => some (x + y)
    | none, b => b
    | a, none => a
  mul a b := match a, b with
    | some x, some y => some (x * y)
    | none, b => b
    | a, none => a
  e := none
  add_e a := by cases a <;> rfl
  e_add a := by cases a <;> rfl
  mul_e a := by cases a <;> rfl
  e_mul a := by cases a <;> rfl
  πA a := a.getD 0
  πM a := a.getD 1
  πA_e := rfl
  πM_e := rfl
  agree x hx := by cases x <;> simp_all
  πA_add a b := by cases a <;> cases b <;> simp
  πM_mul a b := by cases a <;> cases b <;> simp

theorem shadow_not_reversible : ¬ shadow.Reversible := by
  intro h
  have := h.zero_moves (z := some 0) (by simp [shadow]) (some 3)
  simp [shadow] at this

/-- The failure is erasure: `0 · 3 = 0 · 5`, but `1 · 3 ≠ 1 · 5`. Uniform cancellation catches it. -/
theorem shadow_zero_erases : ¬ ∀ c, shadow.mul c (some 3) = shadow.mul c (some 5) := by
  intro h
  have := h (some 1)
  simp [shadow] at this

theorem shadow_zero_agrees : shadow.mul (some 0) (some 3) = shadow.mul (some 0) (some 5) := by
  simp [shadow]
