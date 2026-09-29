import CottLean.T.Quadratic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

/-!
# `TF`: T over a rounded carrier

`T` holds integers. A floating-point `T` holds numbers a machine can hold, and every operation rounds its
result back onto them. This file states that once, for any rounding `f : ℚ → ℚ`, and proves what it costs.

The pair operations never divide, so a float `T` never makes a `NaN` or an `∞` on the way to a ratio:
`q = 0` is an ordinary pair, as it is over `ℤ`. Rounding is the only error there is.

* `TF`: the pairs, with `⊕`, `+`, `·` and `⊗` each rounded once per coordinate.
* `Rounding`: a rounding that is exact on the integers up to a bound `B`.
* `embed_*`: while every intermediate value stays within `B`, `TF` agrees with `T` exactly.
* `Toy`: a 3-significant-bit rounding, where the laws that hold over `ℤ` fail.
-/

/-- `T` with coordinates in `ℚ`, standing for the machine numbers a rounding lands on. -/
@[ext] structure TF where
  p : ℚ
  q : ℚ
  deriving DecidableEq

namespace TF

/-- The mediant, rounded. -/
def oplus (f : ℚ → ℚ) (x y : TF) : TF := ⟨f (x.p + y.p), f (x.q + y.q)⟩
/-- The value-position sum `T(ad+bc, bd)`, rounded. -/
def plus (f : ℚ → ℚ) (x y : TF) : TF := ⟨f (x.p * y.q + y.p * x.q), f (x.q * y.q)⟩
/-- The value-position product, rounded. -/
def times (f : ℚ → ℚ) (x y : TF) : TF := ⟨f (x.p * y.p), f (x.q * y.q)⟩
/-- Angle addition `⊗`, the Gaussian product, rounded. -/
def otimes (f : ℚ → ℚ) (x y : TF) : TF :=
  ⟨f (x.p * y.q + y.p * x.q), f (x.q * y.q - x.p * y.p)⟩

/-- The exact pair as a float pair. -/
def embed (x : T) : TF := ⟨x.p, x.q⟩

/-- No `NaN`: `0ω = T(0,0)` and `ω = T(1,0)` are pairs like any other, and stay distinct. -/
theorem embed_injective : Function.Injective embed := by
  intro x y h
  have hp := congrArg TF.p h
  have hq := congrArg TF.q h
  ext <;> simp_all [embed]

/-- A rounding: exact on the integers of magnitude at most `B`. -/
structure Rounding where
  rnd : ℚ → ℚ
  bound : ℤ
  exact : ∀ n : ℤ, |n| ≤ bound → rnd n = n

variable (r : Rounding)

theorem embed_oplus (x y : T) (hp : |x.p + y.p| ≤ r.bound) (hq : |x.q + y.q| ≤ r.bound) :
    oplus r.rnd (embed x) (embed y) = embed (T.oplus x y) := by
  simp only [oplus, embed, T.oplus]
  ext
  · simpa using r.exact _ hp
  · simpa using r.exact _ hq

theorem embed_times (x y : T) (hp : |x.p * y.p| ≤ r.bound) (hq : |x.q * y.q| ≤ r.bound) :
    times r.rnd (embed x) (embed y) = embed (x * y) := by
  have e : x * y = ⟨x.p * y.p, x.q * y.q⟩ := rfl
  rw [e]
  simp only [times, embed]
  ext
  · simpa using r.exact _ hp
  · simpa using r.exact _ hq

theorem embed_plus (x y : T) (hp : |x.p * y.q + y.p * x.q| ≤ r.bound) (hq : |x.q * y.q| ≤ r.bound) :
    plus r.rnd (embed x) (embed y) = embed (x + y) := by
  have e : x + y = ⟨x.p * y.q + y.p * x.q, x.q * y.q⟩ := rfl
  rw [e]
  simp only [plus, embed]
  ext
  · simpa using r.exact _ hp
  · simpa using r.exact _ hq

open T in
theorem embed_otimes (x y : T) (hp : |x.p * y.q + y.p * x.q| ≤ r.bound)
    (hq : |x.q * y.q - x.p * y.p| ≤ r.bound) :
    otimes r.rnd (embed x) (embed y) = embed (x ⊗ y) := by
  have e : x ⊗ y = ⟨x.p * y.q + y.p * x.q, x.q * y.q - x.p * y.p⟩ := rfl
  rw [e]
  simp only [otimes, embed]
  ext
  · simpa using r.exact _ hp
  · simpa using r.exact _ hq

end TF

/-! ## A toy format: 3 significant bits -/

namespace Toy

/-- `2^k` for an integer `k`, built from natural powers so that it evaluates. -/
def pow2 (k : ℤ) : ℚ := if 0 ≤ k then ((2 ^ k.toNat : ℕ) : ℚ) else 1 / ((2 ^ (-k).toNat : ℕ) : ℚ)

/-- The largest exponent `e` in `[-32, 32]` with `2^e ≤ (if x < 0 then -x else x)`. -/
def expo (x : ℚ) : ℤ :=
  (((List.range 65).map (fun i => (i : ℤ) - 32)).filter (fun e => pow2 e ≤ (if x < 0 then -x else x))).getLast?.getD (-32)

/-- Round to 3 significant bits, ties away from zero. Zero stays zero. -/
def rnd (x : ℚ) : ℚ :=
  if x = 0 then 0 else
    let u := pow2 (expo x - 2)
    let y := (if x < 0 then -x else x) / u + 1 / 2
    (if 0 ≤ x then 1 else -1) * ((y.num / y.den : ℤ) : ℚ) * u




example : rnd 9 = 10 ∧ rnd 11 = 12 ∧ rnd 5 = 5 ∧ rnd (1 / 3) = 5 / 16 := by decide +kernel

/-- Eight is exact but nine is not: the integers are exact only up to a bound (here `8`). -/
theorem nine_inexact : rnd 9 ≠ 9 := by decide +kernel

/-- The mediant `⊕` is associative over `ℤ`, and not once it rounds: `(8+1)+1 = 12`, `8+(1+1) = 10`. -/
theorem oplus_not_assoc :
    TF.oplus rnd (TF.oplus rnd ⟨8, 1⟩ ⟨1, 1⟩) ⟨1, 1⟩ ≠ TF.oplus rnd ⟨8, 1⟩ (TF.oplus rnd ⟨1, 1⟩ ⟨1, 1⟩) := by
  decide +kernel

/-- The same for the value-position sum `+`. -/
theorem plus_not_assoc :
    TF.plus rnd (TF.plus rnd ⟨8, 1⟩ ⟨1, 1⟩) ⟨1, 1⟩ ≠ TF.plus rnd ⟨8, 1⟩ (TF.plus rnd ⟨1, 1⟩ ⟨1, 1⟩) := by
  decide +kernel

end Toy
