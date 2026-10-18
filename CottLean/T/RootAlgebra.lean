import CottLean.T.ZeroAlgebra
import CottLean.T.Radians

/-!
# `X(p, q) = p·√q`

`p` is the coefficient and `q` the radicand. As with `Z`, nothing normalizes: `X(2, 1)` and `X(1, 4)` are
different elements with the same value (`two_one_ne`, `val_two_one`), as `Q` reads `6/2` and `3/1`.

## `√1 = −1`

`√` halves the turn. A positive number is taken at the full turn `1`, not at `0`, so a real radicand has its
turn in `(0, 1]`, and `√q = √|q|·1^(turn/2)` (`rt`). Then `√1 = 1^½ = −1` (`oneTurn_half`) and
`√−1 = 1^¼ = i` (`rt_one`, `rt_negOne`): `√q = −√|q|` for `q > 0` and `i·√|q|` for `q < 0`. Every root has its
turn in `(0, ½]`, the upper half-plane with `−1` and without `1`. `1` itself is `X(−1, 1)`.

## The product carries a sign, and the sign is a branch

`√m·√n` is `−√(mn)` except when both radicands are negative, where it is `√(mn)`: `(−1)·(−1) = 1 = −√1` and
`i·i = −1 = √1` (`rt_mul`). So the product that reads exactly multiplies coefficients and radicands and
carries that sign, `X(a, m)·X(b, n) = X(σ·ab, mn)` (`val_mul`), with `X(−1, 1)` its unit (`one_mul`). The
sign is the branch: the turn is defined modulo `1`, so its half only modulo `½`, and two halves summed can
leave `(0, ½]`.

The product commutes (`mul_comm`) and is associative on non-zero radicands (`mul_assoc_of_ne`). At a radicand
`0` it is not: `(X(1, 0)·i)·i = X(1, 0)` and `X(1, 0)·(i·i) = X(−1, 0)` (`mul_assoc_fails`). Both read `0`.
No choice of sign mends it: any product `X(σ(m, n)·ab, mn)` with `σ = ±1` that reads exactly fails
associativity (`no_exact_assoc`). `0` has no turn to halve, so the sign at `√0` has nowhere to come from.

## Radicand `0` evaluates `0·0 = 0`

`X(p, 0)` reads `0` for every `p`, and `X(−1, 0)`, the unit's coefficient on `√0`, is idempotent
(`zero_mul_zero`): traction's `0` under `*` (`T.zero_times_zero`). Read as `0^½`, `√0` would square to `0¹`
under `Z`'s exponent law. So `X` loses at its radicand what `Z` loses at its coefficient: the product
evaluates `0·0 = 0` in `ℤ`.

## Sums, and the rows of `qtimes`

`+` distributes on equal radicands, `X(a, n) + X(b, n) = X(a + b, n)` (`val_add_same`), and the sums over
the radicands `1` and `n` are the ring `ℤ[√n]`, the `QuadraticAlgebra ℤ n 0`, read into `ℂ` by `ω ↦ √n`
multiplicatively (`ofQuad_mul`, `ofQuad_omega`). So `ω` of the row `ω² = n` is `X(1, n)`, and traction's
`⊗`, `+` and `⊚` are the rows `√−1`, `√0` and `√1`. A pair read through its row's root:

| row | reading of `T(p, q)` | Lean |
|---|---|---|
| `⊗`, `ω = √−1 = i` | `q + i·p`, the complex reading `C` | `row_otimes` |
| `⊚`, `ω = √1 = −1` | `q − p`, the difference `D` | `row_split` |
| `+`, `ω = √0 = 0` | `q`, the denominator, with `p` lost | `row_plus` |

`√1 = −1` is what makes `⊚`'s reading `D` rather than `S`.

## Its logarithm, and `Z`

For positive `p` and `q`, the scale is `log_q (p·√|q|) = ½ + B(q, p)` (`logb_val`), and the value is that
scale with half a turn, `X(p, q) = q^(½ + B(q, p))·1^½` (`val_eq_rpow`). `Z(p, n) = p·0ⁿ` fixes the base at
`0` and moves the order; `X(p, q) = p·q^½` fixes the order at `½` and moves the base.
-/

namespace T.Root

open Complex T.Unquotiented

/-- The turn of a real number, in `(0, 1]`: a positive number is at the full turn. -/
noncomputable def turnOf (q : ℝ) : ℝ := if q < 0 then 1 / 2 else 1

/-- `√q = √|q|·1^(turn/2)`. -/
noncomputable def rt (q : ℝ) : ℂ := (Real.sqrt |q| : ℂ) * oneTurn (turnOf q / 2)

theorem rt_eq (q : ℝ) : rt q = (Real.sqrt |q| : ℂ) * (if q < 0 then I else -1) := by
  unfold rt turnOf
  split_ifs
  · rw [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num, oneTurn_quarter]
  · rw [oneTurn_half]

theorem rt_of_nonneg {q : ℝ} (hq : 0 ≤ q) : rt q = -Real.sqrt q := by
  simp [rt_eq, abs_of_nonneg hq, not_lt.mpr hq]

theorem rt_of_neg {q : ℝ} (hq : q < 0) : rt q = Real.sqrt (-q) * I := by
  simp [rt_eq, abs_of_neg hq, hq]

@[simp] theorem rt_zero : rt 0 = 0 := by simp [rt_eq]

/-- `√1 = −1`. -/
@[simp] theorem rt_one : rt 1 = -1 := by simp [rt_eq]

/-- `√−1 = i`. -/
theorem rt_negOne : rt (-1) = I := by simp [rt_eq]

theorem rt_sq (q : ℝ) : rt q ^ 2 = q := by
  rcases lt_or_ge q 0 with hq | hq
  · rw [rt_of_neg hq, mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  · rw [rt_of_nonneg hq, neg_sq, ← ofReal_pow, Real.sq_sqrt hq]

/-- The sign of `√m·√n` against `√(mn)`: `1` exactly when both radicands are negative. -/
def sgn (m n : ℤ) : ℤ := if m < 0 ∧ n < 0 then 1 else -1

private theorem rt_mul_real {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    rt a * rt b = (if a < 0 ∧ b < 0 then 1 else -1) * rt (a * b) := by
  simp only [rt_eq, abs_mul, Real.sqrt_mul (abs_nonneg a), ofReal_mul]
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
  · have h : ¬ a * b < 0 := not_lt.mpr (mul_pos_of_neg_of_neg ha hb).le
    simp only [ha, hb, h, and_self, if_true, if_false]; ring_nf; rw [I_sq]; ring
  · have h : a * b < 0 := mul_neg_of_neg_of_pos ha hb
    simp only [ha, not_lt.mpr hb.le, h, and_false, if_true, if_false]; ring
  · have h : a * b < 0 := mul_neg_of_pos_of_neg ha hb
    simp only [not_lt.mpr ha.le, hb, h, false_and, if_true, if_false]; ring
  · have h : ¬ a * b < 0 := not_lt.mpr (mul_pos ha hb).le
    simp only [not_lt.mpr ha.le, not_lt.mpr hb.le, h, false_and, if_false]; ring

theorem rt_mul (m n : ℤ) : rt m * rt n = (sgn m n : ℂ) * rt (m * n : ℤ) := by
  by_cases hm : m = 0
  · subst hm; simp
  by_cases hn : n = 0
  · subst hn; simp
  rw [rt_mul_real (by exact_mod_cast hm) (by exact_mod_cast hn), sgn]
  push_cast
  simp only [Int.cast_lt_zero]

/-- `X(p, q) = p·√q`, with `p` the coefficient and `q` the radicand. -/
@[ext]
structure X where
  /-- The coefficient. -/
  p : ℤ
  /-- The radicand. -/
  q : ℤ
  deriving DecidableEq

namespace X

/-- The value `p·√q`. -/
noncomputable def val (x : X) : ℂ := x.p * rt x.q

/-- Coefficients and radicands multiply, with the sign of `√m·√n`. -/
instance : Mul X := ⟨fun x y => ⟨sgn x.q y.q * x.p * y.p, x.q * y.q⟩⟩

theorem mul_def (x y : X) : x * y = ⟨sgn x.q y.q * x.p * y.p, x.q * y.q⟩ := rfl

/-- The product reads exactly. -/
theorem val_mul (x y : X) : (x * y).val = x.val * y.val := by
  simp only [val, mul_def]
  have := rt_mul x.q y.q
  push_cast at this ⊢
  rw [mul_mul_mul_comm, this]; ring

theorem val_sq (x : X) : x.val ^ 2 = x.p ^ 2 * x.q := by
  rw [val, mul_pow, rt_sq]; push_cast; ring

/-- `1 = X(−1, 1)` is the unit. -/
theorem val_one : (⟨-1, 1⟩ : X).val = 1 := by simp [val]

theorem one_mul (x : X) : ⟨-1, 1⟩ * x = x := by
  ext <;> simp [mul_def, sgn]

theorem mul_comm (x y : X) : x * y = y * x := by
  ext <;> simp only [mul_def, sgn]
  · by_cases h1 : x.q < 0 <;> by_cases h2 : y.q < 0 <;> simp [h1, h2] <;> ring
  · ring

theorem mul_assoc_of_ne {x y z : X} (hx : x.q ≠ 0) (hy : y.q ≠ 0) (hz : z.q ≠ 0) :
    x * y * z = x * (y * z) := by
  ext
  · simp only [mul_def, sgn]
    rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy <;>
      rcases lt_or_gt_of_ne hz with hz | hz <;>
      simp [hx, hy, hz, not_lt.mpr hx.le, not_lt.mpr hy.le, not_lt.mpr hz.le, mul_neg_iff] <;> ring
  · simp only [mul_def]; ring

/-- At a radicand `0`, grouping loses the sign of `i·i`. Both sides read `0`. -/
theorem mul_assoc_fails :
    (⟨1, 0⟩ * ⟨1, -1⟩ : X) * ⟨1, -1⟩ ≠ ⟨1, 0⟩ * ((⟨1, -1⟩ : X) * ⟨1, -1⟩) := by decide

/-- No sign makes an exact product associative. -/
theorem no_exact_assoc (σ : ℤ → ℤ → ℤ) (hσ : ∀ m n, σ m n = 1 ∨ σ m n = -1)
    (hexact : ∀ x y : X, (⟨σ x.q y.q * x.p * y.p, x.q * y.q⟩ : X).val = x.val * y.val) :
    ¬ ∀ x y z : X,
      (⟨σ (x.q * y.q) z.q * (σ x.q y.q * x.p * y.p) * z.p, x.q * y.q * z.q⟩ : X) =
        ⟨σ x.q (y.q * z.q) * x.p * (σ y.q z.q * y.p * z.p), x.q * (y.q * z.q)⟩ := by
  intro hassoc
  have h11 : σ 1 1 = -1 := by
    have := hexact ⟨1, 1⟩ ⟨1, 1⟩; simp [val] at this; norm_cast at this; omega
  have hnn : σ (-1) (-1) = 1 := by
    have := hexact ⟨1, -1⟩ ⟨1, -1⟩
    simp [val, rt_negOne] at this
    norm_cast at this
  have h01 : σ 0 1 = -1 := by
    have := congrArg X.p (hassoc ⟨1, 0⟩ ⟨1, 1⟩ ⟨1, 1⟩)
    rcases hσ 0 1 with h | h
    · simp [h, h11] at this
    · exact h
  have := congrArg X.p (hassoc ⟨1, 0⟩ ⟨1, -1⟩ ⟨1, -1⟩)
  rcases hσ 0 (-1) with h | h <;> simp [h, h01, hnn] at this

/-- `X(−1, 0)` is idempotent: the radicand evaluates `0·0 = 0`. -/
theorem zero_mul_zero : (⟨-1, 0⟩ * ⟨-1, 0⟩ : X) = ⟨-1, 0⟩ := by decide

theorem val_radicand_zero (p : ℤ) : (⟨p, 0⟩ : X).val = 0 := by simp [val]

/-- `+` on equal radicands. -/
theorem val_add_same (a b n : ℤ) : (⟨a + b, n⟩ : X).val = (⟨a, n⟩ : X).val + (⟨b, n⟩ : X).val := by
  simp [val]; ring

/-- Nothing normalizes: `X(2, 1)` is not `X(1, 4)`. -/
theorem two_one_ne : (⟨2, 1⟩ : X) ≠ ⟨1, 4⟩ := by decide

/-- But they read the same, `−2`. -/
theorem val_two_one : (⟨2, 1⟩ : X).val = (⟨1, 4⟩ : X).val := by
  have : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [val, rt_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num), this]

end X

/-! ## The rows of `qtimes` -/

/-- `ℤ[√n]` read into `ℂ` by `ω ↦ √n`. -/
noncomputable def ofQuad (n : ℤ) (z : QuadraticAlgebra ℤ n 0) : ℂ := z.re + z.im * rt n

theorem ofQuad_add (n : ℤ) (z w : QuadraticAlgebra ℤ n 0) : ofQuad n (z + w) = ofQuad n z + ofQuad n w := by
  simp [ofQuad]; ring

theorem ofQuad_mul (n : ℤ) (z w : QuadraticAlgebra ℤ n 0) : ofQuad n (z * w) = ofQuad n z * ofQuad n w := by
  have h := rt_sq n
  simp only [ofQuad, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination (-(z.im : ℂ) * w.im) * h

/-- `ω` of the row `ω² = n` reads `√n = X(1, n)`. -/
theorem ofQuad_omega (n : ℤ) : ofQuad n QuadraticAlgebra.omega = (⟨1, n⟩ : X).val := by
  simp [ofQuad, X.val]

/-- `T(p, q)` read through its row's root: `q + p·√n`. -/
theorem row (n : ℤ) (x : T) : ofQuad n (T.toQuad n 0 x) = x.q + x.p * rt n := by
  simp [ofQuad]

/-- Under `⊗` the root is `i`, and the reading is `C = q + i·p`. -/
theorem row_otimes (x : T) : ofQuad (-1) (T.toQuad (-1) 0 x) = x.q + x.p * I := by
  rw [row]; push_cast; rw [rt_negOne]

/-- Under `⊚` the root is `√1 = −1`, and the reading is `D = q − p`. -/
theorem row_split (x : T) : ofQuad 1 (T.toQuad 1 0 x) = ((x.q - x.p : ℤ) : ℂ) := by
  rw [row]; push_cast; simp; ring

/-- Under `+` the root is `0`, and the reading keeps only `q`. -/
theorem row_plus (x : T) : ofQuad 0 (T.toQuad 0 0 x) = x.q := by
  rw [row]; simp

/-! ## The logarithm in base `q` -/

/-- The scale: `log_q (p·√|q|) = ½ + B(q, p)`. -/
theorem logb_val {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hq1 : Real.log q ≠ 0) :
    Real.logb q (p * Real.sqrt q) = 1 / 2 + ZeroScale.B q p := by
  rw [ZeroScale.B, Real.logb, Real.logb, Real.log_mul hp.ne' (Real.sqrt_pos.mpr hq).ne', Real.log_sqrt hq.le]
  field_simp; ring

/-- `X(p, q) = q^(½ + B(q, p))·1^½`: the scale and half a turn. `Z` fixes the base at `0` and moves the
order, `X` fixes the order at `½` and moves the base. -/
theorem val_eq_rpow {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hq1 : q ≠ 1) :
    (p : ℂ) * rt q = ((q ^ (1 / 2 + ZeroScale.B q p) : ℝ) : ℂ) * oneTurn (1 / 2) := by
  rw [rt_of_nonneg hq.le, oneTurn_half, Real.rpow_add hq, ZeroScale.B, Real.rpow_logb hq hq1 hp,
    Real.sqrt_eq_rpow]
  push_cast; ring

end T.Root
