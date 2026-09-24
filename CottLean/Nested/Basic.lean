import CottLean.T.CommonMeadow
import CottLean.T.Residue
import CottLean.T.Transform

/-!
# `T2(p, q)`: a pair of pairs

A traction whose two coordinates are tractions, combined with the value position's own operations:

```
T2(p₁,q₁) + T2(p₂,q₂) = T2(p₁·q₂ + q₁·p₂, q₁·q₂)
T2(p₁,q₁) · T2(p₂,q₂) = T2(p₁·p₂, q₁·q₂)
```

The flat pairs sit inside as `T(a,b) ↦ T2(T(a,1), T(b,1))`, so `n = T2(T(n,1), T(1,1))`,
`1 = T2(1, 1)`, `0 = T2(0, 1)` and `ω = T2(1, 0)`.

## The projection

`flatten : T2 → T` reads `T2(A, B)` as `A / B`, taking `T2(T(a,b), T(c,d))` to `T(ad, bc)`. Composed with
`toQa`, it is the classical value `(a/b)/(c/d)` in the rational common meadow.

* `flatten_of`: `flatten` undoes the embedding, so it is onto, and `of` is a section of it.
* `of_plus`, `of_times`, `of_neg`, `of_reciprocal`: the embedding respects every operation exactly.
* `flatten_times`, `flatten_neg`, `flatten_reciprocal`: so does the projection, for all but `+`.
* `power` raises each coordinate by `T`'s `power`. It is repeated `·` (`power_zero`, `power_succ`), and
  the embedding and the projection both respect it (`of_power`, `flatten_power`).
* `flatten_plus`: `+` survives up to one residue, `T(0, x.q.q · y.q.q)`, the product of the inner
  denominators of the two outer denominators. It is exact on the image of `of`.
* `flatten_eq_act`: with the denominator `B` fixed, the projection is the Möbius transformation
  `[[B.q, 0], [0, B.p]]` of the numerator. So it respects `⊕` in the numerator (`flatten_oplus_numerator`),
  and its determinant is `B.p · B.q`, the norm of `B` under `*`.
* `flatten_recoverable_iff`: the numerator comes back from the classical value exactly when that
  determinant is non-zero, that is when `B` is off both axes.
* `toQa_flatten`: the classical value is `toQa A / toQa B` computed in the meadow, except where `B` is a
  quarter turn. There T answers `0` and the meadow answers `a`, as for flat pairs.
* `toQa_flatten_plus`: into `ℚₐ`, `+` survives exactly when neither outer denominator is a quarter turn,
  and `plus_quarterTurn` shows it fails when one is.
-/

open T

/-- `T2(p, q)`: a traction whose coordinates are tractions. -/
@[ext]
structure T2 where
  /-- The numerator, itself a pair. -/
  p : T
  /-- The denominator, itself a pair. -/
  q : T
  deriving DecidableEq, Repr

namespace T2

/-! ## The embedding and the named values -/

/-- `T(a,b) ↦ T2(T(a,1), T(b,1))`: each integer coordinate becomes its own unit-denominator pair. -/
def of (x : T) : T2 := ⟨⟨x.p, 1⟩, ⟨x.q, 1⟩⟩

/-- `0 = T2(0, 1)`. -/
def «0» : T2 := ⟨0, T.«1»⟩
/-- `1 = T2(1, 1)`. -/
def «1» : T2 := ⟨T.«1», T.«1»⟩
/-- `ω = T2(1, 0)`. -/
def «ω» : T2 := ⟨T.«1», 0⟩

theorem of_zero : of 0 = «0» := rfl
theorem of_one : of T.«1» = «1» := rfl
theorem of_omega : of T.«ω» = «ω» := rfl

theorem of_injective : Function.Injective of := by
  intro x y h
  have hp := congrArg (fun z => z.p.p) h
  have hq := congrArg (fun z => z.q.p) h
  exact T.ext hp hq

/-! ## The operations -/

/-- `T2(p₁,q₁) + T2(p₂,q₂) = T2(p₁·q₂ + q₁·p₂, q₁·q₂)`. -/
def plus (x y : T2) : T2 := ⟨x.p * y.q + x.q * y.p, x.q * y.q⟩

/-- `T2(p₁,q₁) · T2(p₂,q₂) = T2(p₁·p₂, q₁·q₂)`. -/
def times (x y : T2) : T2 := ⟨x.p * y.p, x.q * y.q⟩

instance : Add T2 := ⟨plus⟩
instance : Mul T2 := ⟨times⟩

/-- `-T2(p, q) = T2(-p, q)`. -/
instance : Neg T2 := ⟨fun x => ⟨-x.p, x.q⟩⟩

/-- `T2(q, p)`. -/
def reciprocal (x : T2) : T2 := ⟨x.q, x.p⟩

@[simp] theorem add_def (x y : T2) : x + y = ⟨x.p * y.q + x.q * y.p, x.q * y.q⟩ := rfl
@[simp] theorem mul_def (x y : T2) : x * y = ⟨x.p * y.p, x.q * y.q⟩ := rfl
@[simp] theorem neg_def (x : T2) : -x = ⟨-x.p, x.q⟩ := rfl

theorem of_plus (x y : T) : of (x + y) = of x + of y := by
  ext <;> simp [of]; ring

theorem of_times (x y : T) : of (x * y) = of x * of y := by
  ext <;> simp [of]

theorem of_neg (x : T) : of (-x) = -of x := by
  ext <;> simp [of]

theorem of_reciprocal (x : T) : of (T.reciprocal x) = reciprocal (of x) := rfl

/-! ## Powers -/

/-- `T2(p, q)ⁿ = T2(pⁿ, qⁿ)`, each coordinate raised by `T`'s own `power`. -/
def power (x : T2) (n : ℕ) : T2 := ⟨T.power x.p n, T.power x.q n⟩

@[simp] theorem power_def (x : T2) (n : ℕ) : power x n = ⟨T.power x.p n, T.power x.q n⟩ := rfl

/-- The zeroth power is `1`, for every pair, `0` and `ω` included. -/
theorem power_zero (x : T2) : power x 0 = «1» := by
  ext <;> simp [T.power, «1», T.«1»]

/-- So `power` is repeated `·`. -/
theorem power_succ (x : T2) (n : ℕ) : power x (n + 1) = power x n * x := by
  ext <;> simp [T.power, pow_succ]

theorem power_add (x : T2) (m n : ℕ) : power x (m + n) = power x m * power x n := by
  ext <;> simp [T.power, pow_add]

theorem of_power (x : T) (n : ℕ) : of (T.power x n) = power (of x) n := by
  ext <;> simp [of, T.power]

/-! ## The projection -/

/-- `T2(A, B) ↦ A / B`, so `T2(T(a,b), T(c,d)) ↦ T(ad, bc)`. -/
def flatten (x : T2) : T := x.p * T.reciprocal x.q

@[simp] theorem flatten_def (x : T2) : flatten x = ⟨x.p.p * x.q.q, x.p.q * x.q.p⟩ := rfl

theorem flatten_of (x : T) : flatten (of x) = x := by
  ext <;> simp [of]

theorem flatten_surjective : Function.Surjective flatten := fun x => ⟨of x, flatten_of x⟩

theorem flatten_times (x y : T2) : flatten (x * y) = flatten x * flatten y := by
  ext <;> simp <;> ring

theorem flatten_neg (x : T2) : flatten (-x) = -flatten x := by
  ext <;> simp

theorem flatten_reciprocal (x : T2) : flatten (reciprocal x) = T.reciprocal (flatten x) := by
  ext <;> simp [reciprocal, T.reciprocal] <;> ring

theorem flatten_power (x : T2) (n : ℕ) : flatten (power x n) = T.power (flatten x) n := by
  ext <;> simp [T.power, mul_pow]

/-- `+` survives the projection up to one residue: the inner denominators of the outer denominators. -/
theorem flatten_plus (x y : T2) :
    flatten (x + y) = flatten x + flatten y + residue (x.q.q * y.q.q) := by
  rw [plus_residue]
  ext <;> simp [scale] <;> ring

/-- On the image of `of`, `+` survives exactly. -/
theorem flatten_plus_of (x y : T) : flatten (of x + of y) = flatten (of x) + flatten (of y) := by
  rw [← of_plus, flatten_of, flatten_of, flatten_of]

/-! ## With the denominator fixed -/

/-- The projection is a Möbius transformation of the numerator, by the denominator. -/
theorem flatten_eq_act (A B : T) : flatten ⟨A, B⟩ = act !![B.q, 0; 0, B.p] A := by
  ext <;> simp [mul_comm]

theorem det_flatten_mat (B : T) : (!![B.q, 0; 0, B.p] : Matrix (Fin 2) (Fin 2) ℤ).det = B.p * B.q := by
  simp [Matrix.det_fin_two_of, mul_comm]

theorem flatten_oplus_numerator (A A' B : T) :
    flatten ⟨A ⊕ A', B⟩ = (flatten ⟨A, B⟩ ⊕ flatten ⟨A', B⟩) := by
  rw [flatten_eq_act, flatten_eq_act, flatten_eq_act, act_oplus]

/-- The numerator comes back from the projection exactly when the denominator is off both axes. -/
theorem flatten_recoverable_iff (B : T) :
    (∀ A A', flatten ⟨A, B⟩ = flatten ⟨A', B⟩ → A = A') ↔ B.p ≠ 0 ∧ B.q ≠ 0 :=
  (times_recoverable_iff (T.reciprocal B)).trans and_comm

/-! ## Into the common meadow -/

theorem toQa_scale {k : ℤ} (hk : k ≠ 0) (x : T) : toQa (scale k x) = toQa x := by
  by_cases hx : x.q = 0
  · simp [toQa, scale, hx]
  · have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    simp only [toQa, scale, mul_eq_zero, hk, hx, or_self, if_false]
    push_cast
    rw [mul_div_mul_left _ _ hk']

/-- The classical value is `A / B` in the meadow, except where `B` is a quarter turn. -/
theorem toQa_flatten {x : T2} (h : x.q.q ≠ 0 ∨ x.q.p = 0) :
    toQa (flatten x) = Qa.mul (toQa x.p) (Qa.inv (toQa x.q)) := by
  rw [flatten, toQa_times, toQa_reciprocal h]

/-- Where `B` is a quarter turn and `A` is finite, T answers `0` and the meadow answers `a`. -/
theorem toQa_flatten_quarterTurn {x : T2} (hq : x.q.q = 0) (hp : x.q.p ≠ 0) (ha : x.p.q ≠ 0) :
    toQa (flatten x) = some 0 ∧ Qa.mul (toQa x.p) (Qa.inv (toQa x.q)) = none := by
  refine ⟨?_, ?_⟩
  · simp [toQa, hq, ha, hp]
  · rcases h : toQa x.p <;> simp [Qa.mul, Qa.inv, toQa, hq]

/-- Into `ℚₐ`, `+` survives when neither outer denominator is a quarter turn. -/
theorem toQa_flatten_plus {x y : T2} (hx : x.q.q ≠ 0) (hy : y.q.q ≠ 0) :
    toQa (flatten (x + y)) = Qa.add (toQa (flatten x)) (toQa (flatten y)) := by
  rw [flatten_plus, plus_residue, toQa_scale (mul_ne_zero hx hy), toQa_plus]

/-- And fails when one is: `1/ω = 0` and `1/1 = 1`, but their sum projects to `a`. -/
theorem plus_quarterTurn :
    toQa (flatten (⟨T.«1», T.«ω»⟩ + «1»)) = none ∧
      Qa.add (toQa (flatten ⟨T.«1», T.«ω»⟩)) (toQa (flatten «1»)) = some 1 := by
  refine ⟨?_, ?_⟩ <;> simp [toQa, Qa.add, T.«1», T.«ω», «1»]

end T2
