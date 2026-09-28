import CottLean.Nested.T3

/-!
# Starting from all ones

What erases information when the other operand is `1`, at each depth, and what `0` erases once it has
been reached.

## With `1`

* `T.times_one`, `T2.times_one`, `T3.times_one`: `· 1` is the identity at every depth.
* `plus_one_injective`: in `T`, `x + 1 = T(p + q, q)` loses nothing.
* `T2.plus_one`: in `T2`, `X + 1 = T2(X.p + X.q, X.q)`, and the inner `+` is `T`'s.
* `T2.plus_one_recoverable_iff`: so `X` comes back from `X + 1` exactly when `X.q.q ≠ 0`, that is when
  the denominator `X.q` is not on the axis of `ω`.
* `T2.held_plus_one`: in particular `a/ω + 1 = ω/ω` for every `a`. `a/ω` is `a · 0` held rather than
  taken, and adding `1` takes it.
* `T3.plus_one_not_injective`: in `T3`, `+ 1` erases too.

## Reaching `0`

* `one_plus_neg_one`, `T2.one_plus_neg_one`, `T3.one_plus_neg_one`: `1 + (−1) = 0` at every depth.
* `T.zero_times`, `T2.zero_times`, `T3.zero_times`: `0 ·` erases exactly one integer, the leaf reached by
  taking the numerator at every step. That is one of two in `T`, one of four in `T2`, one of eight in `T3`.

So `·`'s damage stays at one leaf while the leaves double, and `+`, which loses nothing against `1` in `T`,
loses against `1` from `T2` on.
-/

open T

namespace T

theorem plus_one_injective : Function.Injective (· + «1») := by
  intro x y h
  simp only [add_def, «1», T.mk.injEq, mul_one, one_mul] at h
  ext <;> omega

theorem one_plus_neg_one : «1» + -«1» = 0 := by decide

end T

namespace T2

theorem times_one (X : T2) : X * «1» = X := by
  ext <;> simp [«1», T.«1»]

theorem plus_one (X : T2) : X + «1» = ⟨X.p + X.q, X.q⟩ := by
  ext <;> simp [«1», T.«1»]

/-- `X` comes back from `X + 1` exactly when its denominator is off the axis of `ω`. -/
theorem plus_one_recoverable_iff (X : T2) : (∀ X', X' + «1» = X + «1» → X' = X) ↔ X.q.q ≠ 0 := by
  constructor
  · intro h hq
    have := congrArg (fun Z => Z.p.p) (h ⟨⟨X.p.p + 1, X.p.q⟩, X.q⟩ (by ext <;> simp [hq]))
    simp at this
  · intro hq X' h
    rw [plus_one, plus_one] at h
    have hQ : X'.q = X.q := by simpa using congrArg T2.q h
    have hp := congrArg (fun Z => Z.p.p) h
    have hr := congrArg (fun Z => Z.p.q) h
    simp only [T.add_def, hQ] at hp hr
    have hb : X'.p.q = X.p.q := mul_right_cancel₀ hq hr
    rw [hb] at hp
    have ha : X'.p.p = X.p.p := mul_right_cancel₀ hq (by linarith)
    exact T2.ext (T.ext ha hb) hQ

/-- `a/ω + 1 = ω/ω`: the held product is erased by adding `1`. -/
theorem held_plus_one (a : ℤ) : (⟨⟨a, 1⟩, T.«ω»⟩ : T2) + «1» = ⟨T.«ω», T.«ω»⟩ := by
  ext <;> simp [«1», T.«1», T.«ω»]

theorem one_plus_neg_one : «1» + -«1» = «0» := by decide

theorem zero_times (X : T2) : «0» * X = ⟨⟨0, X.p.q⟩, X.q⟩ := by
  ext <;> simp [«0», T.«1»]

end T2

namespace T3

theorem times_one (x : T3) : x * of T2.«1» = x := by
  ext <;> simp [of, T2.«1», T.«1»]

/-- In `T3`, `+ 1` erases too: two pairs differing in one leaf land together. -/
theorem plus_one_not_injective :
    (⟨⟨⟨1, 1⟩, T.«1»⟩, ⟨T.«1», T.«ω»⟩⟩ : T3) + of T2.«1» =
      (⟨⟨⟨1, 2⟩, T.«1»⟩, ⟨T.«1», T.«ω»⟩⟩ : T3) + of T2.«1» := by decide

theorem one_plus_neg_one : of T2.«1» + -of T2.«1» = of T2.«0» := by decide

theorem zero_times (x : T3) : of T2.«0» * x = ⟨⟨⟨0, x.p.p.q⟩, x.p.q⟩, x.q⟩ := by
  ext <;> simp [of, T2.«0», T.«1»]

end T3
