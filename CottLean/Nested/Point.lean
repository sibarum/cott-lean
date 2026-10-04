import CottLean.Nested.Basic
import CottLean.T.Readings
import CottLean.T.Recovery
import CottLean.T.Residue

/-!
# `T2` read as a point

A flat pair `T(p, q)` has two readings: the ratio `p/q`, and the point `q + p·i`. `Basic` gives `T2(A, B)`
the first, `A / B`. This file gives it the second: the point `B + A·i`, whose coordinates are ratios.

```
T2(A₁,B₁) ⊕ T2(A₂,B₂) = T2(A₁ + A₂, B₁ + B₂)
T2(A₁,B₁) ⊗ T2(A₂,B₂) = T2(A₁·B₂ + A₂·B₁, B₁·B₂ − A₁·A₂)
pointInv T2(A, B)     = T2(−A / N, B / N),   N = A·A + B·B
```

These are the flat formulas, with `T`'s `+`, `*` and `-` in place of the integers' own. The reason for the
level is the inverse. Over ℤ the complex reading has none, `1/(q + p·i) = (q − p·i)/(p² + q²)`, since that
needs the denominator `p² + q²` and a Gaussian integer has nowhere to keep one. With ratio coordinates each
coordinate keeps its own denominator, so the inverse is exact.

## The values

`val` reads `T2(A, B)` as the complex number `B + A·i`, each coordinate read as its ratio. Where the
coordinates have non-zero denominators (`Finite`):

* `val_oplus`, `val_otimes`: `⊕` and `⊗` are the sum and product of complex numbers.
* `val_pointInv`: `pointInv` is the complex inverse, at every point, `0` included, where both sides read
  `0` (Lean's `0⁻¹ = 0`).

So on values the level-two point reading is the field ℚ(i).

## The two flat readings inside it

* `ofPoint`: a flat point `T(p, q)` is `T2(p/1, q/1)`. `⊕` and `⊗` carry across exactly, at coordinate
  equality (`ofPoint_oplus`, `ofPoint_otimes`). The flat complex reading is the integer points,
  and there it gains the inverse it lacked: `(q − p·i) / (p² + q²)` (`pointInv_ofPoint`).
* `ofRatio`: a flat ratio `x` is the real point `T2(0, x)`. `+` carries to `⊕` exactly (`ofRatio_plus`).
  `*` carries to `⊗` with the imaginary part left as the residue `T(0, q₁·q₂)`, which reads as `0`
  (`ofRatio_times`).
* `pointInv_ofRatio`: the complex inverse of a real `x = T(p, q)` is `T`'s own reciprocal `T(q, p)`
  scaled by `p·q`, with the imaginary part the residue `T(0, p²)`. So the two inverses agree as values
  exactly where `p·q ≠ 0`. On the axes they split: `1/0` is `ω` in the ratio reading and `0ω` in the
  point reading (`pointInv_ofRatio_zero`), and `1/ω` is `0` in the ratio reading and `0ω` in the point
  reading (`pointInv_ofRatio_omega`).

## The split is the ambiguity

The factor `p·q` between the two inverses is the integer `*` loses on. The complex inverse of `x`
collapses to `0ω` exactly when `* x` cannot be undone in the ratio reading
(`pointInv_collapses_iff_times_ambiguous`), and the factor is the residue `x · (1/x)` leaves
(`pointInv_factor_is_residue`).
-/

open T

namespace T2

/-! ## The operations -/

/-- The sum of the points: each coordinate added as a ratio. -/
def oplus (x y : T2) : T2 := ⟨x.p + y.p, x.q + y.q⟩

/-- The product of the points, `(B₁ + A₁i)(B₂ + A₂i)`, with ratio coordinates. -/
def otimes (x y : T2) : T2 := ⟨x.p * y.q + y.p * x.q, x.q * y.q + -(x.p * y.p)⟩

/-- `A·A + B·B`, the squared length of the point, as a ratio. -/
def normSq (x : T2) : T := x.p * x.p + x.q * x.q

/-- The inverse of the point: `(B − A·i) / N`, with `N` the squared length. -/
def pointInv (x : T2) : T2 :=
  ⟨-x.p * T.reciprocal (normSq x), x.q * T.reciprocal (normSq x)⟩

/-! ## The values -/

/-- A flat pair read as its ratio, in ℝ. -/
noncomputable def rv (x : T) : ℝ := x.p / x.q

theorem rv_plus {x y : T} (hx : x.q ≠ 0) (hy : y.q ≠ 0) : rv (x + y) = rv x + rv y := by
  have hx' : (x.q : ℝ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y.q : ℝ) ≠ 0 := by exact_mod_cast hy
  simp only [rv, T.add_def]; push_cast
  rw [div_add_div _ _ hx' hy']; ring

theorem rv_times (x y : T) : rv (x * y) = rv x * rv y := by
  simp only [rv, T.mul_def]; push_cast
  rw [div_mul_div_comm]

theorem rv_neg (x : T) : rv (-x) = -rv x := by
  simp only [rv, T.neg_def]; push_cast; ring

theorem rv_reciprocal (x : T) : rv (T.reciprocal x) = (rv x)⁻¹ := by
  simp [rv, T.reciprocal]

/-- `T2(A, B)` as the complex number `B + A·i`. -/
noncomputable def val (x : T2) : ℂ := ⟨rv x.q, rv x.p⟩

/-- Both coordinates have non-zero denominators. -/
def Finite (x : T2) : Prop := x.p.q ≠ 0 ∧ x.q.q ≠ 0

theorem val_oplus {x y : T2} (hx : Finite x) (hy : Finite y) : val (oplus x y) = val x + val y := by
  apply Complex.ext
  · simp only [val, oplus, Complex.add_re]; exact rv_plus hx.2 hy.2
  · simp only [val, oplus, Complex.add_im]; exact rv_plus hx.1 hy.1

theorem val_otimes {x y : T2} (hx : Finite x) (hy : Finite y) : val (otimes x y) = val x * val y := by
  obtain ⟨hxp, hxq⟩ := hx
  obtain ⟨hyp, hyq⟩ := hy
  apply Complex.ext
  · simp only [val, otimes, Complex.mul_re]
    rw [rv_plus (by simp [hxq, hyq]) (by simp [hxp, hyp]), rv_neg, rv_times, rv_times]; ring
  · simp only [val, otimes, Complex.mul_im]
    rw [rv_plus (by simp [hxp, hyq]) (by simp [hyp, hxq]), rv_times, rv_times]; ring

theorem rv_normSq {x : T2} (hx : Finite x) : rv (normSq x) = Complex.normSq (val x) := by
  obtain ⟨hp, hq⟩ := hx
  simp only [normSq, Complex.normSq_apply, val]
  rw [rv_plus (by simp [hp]) (by simp [hq]), rv_times, rv_times]; ring

/-- The inverse is the complex inverse, for every finite point. -/
theorem val_pointInv {x : T2} (hx : Finite x) : val (pointInv x) = (val x)⁻¹ := by
  apply Complex.ext
  · simp only [val, pointInv, Complex.inv_re]
    rw [rv_times, rv_reciprocal, rv_normSq hx, div_eq_mul_inv]; rfl
  · simp only [val, pointInv, Complex.inv_im]
    rw [rv_times, rv_neg, rv_reciprocal, rv_normSq hx, div_eq_mul_inv]; rfl

/-! ## The inverse in integers

Write `T2(T(a,b), T(c,d))`, the point `c/d + (a/b)·i`, and `D = a²d² + b²c²`. `D` is the squared length
`(c/d)² + (a/b)²` with the denominators cleared, `b²d²` times it. Then

```
1 / T2(T(a,b), T(c,d)) = T2( T(−a·b²·d², b·D),  T(c·b²·d², d·D) )
```

and multiplying back gives `1` with both coordinates scaled by one integer `k = (b·d·D)²`, the
imaginary part left as the residue `T(0, k)`. That is the shape of `x · (1/x) = T(pq, pq)` one level
down: each inverse returns to `1` up to its own product's norm. `k` is `0` exactly when a coordinate has
a zero denominator or the point is zero.
-/

/-- `a²d² + b²c²`: the squared length of `c/d + (a/b)·i`, times `b²d²`. -/
def lenSq (a b c d : ℤ) : ℤ := a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2

/-- The inverse, coordinate by coordinate. -/
theorem pointInv_eq (a b c d : ℤ) :
    pointInv ⟨⟨a, b⟩, ⟨c, d⟩⟩ =
      ⟨⟨-a * b ^ 2 * d ^ 2, b * lenSq a b c d⟩, ⟨c * b ^ 2 * d ^ 2, d * lenSq a b c d⟩⟩ := by
  ext <;> simp only [pointInv, normSq, T.reciprocal, lenSq, T.mul_def, T.add_def, T.neg_def] <;> ring

/-- `z ⊗ (1/z)` is `1` with both coordinates scaled by `k = (b·d·D)²`, over the residue `T(0, k)`. -/
theorem otimes_pointInv (a b c d : ℤ) :
    otimes ⟨⟨a, b⟩, ⟨c, d⟩⟩ (pointInv ⟨⟨a, b⟩, ⟨c, d⟩⟩) =
      ⟨⟨0, (b * d * lenSq a b c d) ^ 2⟩,
        ⟨(b * d * lenSq a b c d) ^ 2, (b * d * lenSq a b c d) ^ 2⟩⟩ := by
  rw [pointInv_eq]; ext <;> simp [otimes, lenSq] <;> ring

theorem lenSq_eq_zero_iff (a b c d : ℤ) : lenSq a b c d = 0 ↔ a * d = 0 ∧ b * c = 0 := by
  have e : lenSq a b c d = (a * d) ^ 2 + (b * c) ^ 2 := by unfold lenSq; ring
  rw [e]
  constructor
  · intro h
    have h1 : (a * d) ^ 2 = 0 := by nlinarith [sq_nonneg (a * d), sq_nonneg (b * c)]
    have h2 : (b * c) ^ 2 = 0 := by nlinarith [sq_nonneg (a * d), sq_nonneg (b * c)]
    exact ⟨pow_eq_zero_iff two_ne_zero |>.mp h1, pow_eq_zero_iff two_ne_zero |>.mp h2⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]; norm_num

/-- The residue vanishes exactly when a coordinate has a zero denominator, or the point is zero. -/
theorem inverse_residue_eq_zero_iff (a b c d : ℤ) :
    b * d * lenSq a b c d = 0 ↔ b = 0 ∨ d = 0 ∨ (a = 0 ∧ c = 0) := by
  rw [mul_eq_zero, mul_eq_zero, lenSq_eq_zero_iff, mul_eq_zero, mul_eq_zero]
  tauto

/-! ## The flat point reading inside it -/

/-- A flat point `T(p, q)`, the Gaussian integer `q + p·i`, with each coordinate over `1`. -/
def ofPoint (z : T) : T2 := ⟨ratioInt z.p, ratioInt z.q⟩

theorem ofPoint_injective : Function.Injective ofPoint := fun _ _ h =>
  T.ext (ratioInt_injective (congrArg T2.p h)) (ratioInt_injective (congrArg T2.q h))

theorem ofPoint_oplus (x y : T) : ofPoint (x ⊕ y) = oplus (ofPoint x) (ofPoint y) := by
  simp only [ofPoint, oplus, T.oplus, ratioInt_plus]

theorem ofPoint_otimes (x y : T) : ofPoint (x ⊗ y) = otimes (ofPoint x) (ofPoint y) := by
  ext <;> simp [ofPoint, otimes, T.otimes, ratioInt]; ring

/-- A Gaussian integer `q + p·i`: the inverse is `(q − p·i) / (p² + q²)`. -/
theorem pointInv_ofPoint (z : T) :
    pointInv (ofPoint z) = ⟨⟨-z.p, z.p ^ 2 + z.q ^ 2⟩, ⟨z.q, z.p ^ 2 + z.q ^ 2⟩⟩ := by
  ext <;> simp only [ofPoint, ratioInt, pointInv, normSq, T.reciprocal, T.mul_def, T.add_def, T.neg_def] <;> ring

/-! ## The flat ratio reading inside it -/

/-- A flat ratio `x`, as the real point `x + 0·i`. -/
def ofRatio (x : T) : T2 := ⟨0, x⟩

theorem ofRatio_injective : Function.Injective ofRatio := fun _ _ h => congrArg T2.q h

theorem val_ofRatio (x : T) : val (ofRatio x) = rv x := by
  apply Complex.ext <;> simp [val, ofRatio, rv]

theorem ofRatio_plus (x y : T) : ofRatio (x + y) = oplus (ofRatio x) (ofRatio y) := by
  ext <;> simp [ofRatio, oplus]

/-- `*` carries to `⊗` with the imaginary part the residue of the two denominators. -/
theorem ofRatio_times (x y : T) :
    otimes (ofRatio x) (ofRatio y) = ⟨⟨0, x.q * y.q⟩, x * y⟩ := by
  ext <;> simp [ofRatio, otimes]; ring

/-- The complex inverse of a real `T(p, q)`: `T`'s reciprocal scaled by `p·q`, over a residue. -/
theorem pointInv_ofRatio (x : T) :
    pointInv (ofRatio x) = ⟨⟨0, x.p ^ 2⟩, scale (x.p * x.q) (T.reciprocal x)⟩ := by
  ext <;> simp [pointInv, ofRatio, normSq, T.reciprocal, scale] <;> ring

/-- `1/0`: the ratio reading gives `ω`, the point reading gives `0ω` in both coordinates. -/
theorem pointInv_ofRatio_zero :
    T.reciprocal 0 = T.«ω» ∧ pointInv (ofRatio 0) = ⟨T.«0ω», T.«0ω»⟩ := by decide

/-- `1/ω`: the ratio reading gives `0`, the point reading gives `0ω` as its real part. -/
theorem pointInv_ofRatio_omega :
    T.reciprocal T.«ω» = 0 ∧ pointInv (ofRatio T.«ω») = ⟨0, T.«0ω»⟩ := by decide

/-! ## The split is the ambiguity

The two inverses differ by the factor `p·q`. That integer is already the one `*` loses on: `* x` can be
undone exactly when `p·q ≠ 0` (`T.times_recoverable_iff`), and `x · (1/x)` is `1` plus the residue
`p·q` (`T.times_reciprocal_residue`). So the point reading's inverse collapses to `0ω` at exactly the
pairs where multiplying by them is ambiguous in the ratio reading.
-/

/-- The real part of the complex inverse is `0ω` exactly when `p·q = 0`. -/
theorem pointInv_ofRatio_q_eq_zeroOmega_iff (x : T) :
    (pointInv (ofRatio x)).q = T.«0ω» ↔ x.p * x.q = 0 := by
  rw [pointInv_ofRatio]
  constructor
  · intro h
    have h1 : x.p * x.q * x.q = 0 := congrArg T.p h
    have h2 : x.p * x.q * x.p = 0 := congrArg T.q h
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · rcases mul_eq_zero.mp h2 with h' | h'
      · exact h'
      · simp [h, h']
  · intro h; ext <;> simp [scale, T.reciprocal, h, T.«0ω»]

/-- The complex inverse of `x` collapses exactly where `* x` cannot be undone. -/
theorem pointInv_collapses_iff_times_ambiguous (x : T) :
    (pointInv (ofRatio x)).q = T.«0ω» ↔ ¬ Recoverable (· * ·) x := by
  rw [pointInv_ofRatio_q_eq_zeroOmega_iff, times_recoverable_iff, mul_eq_zero]; tauto

/-- And the factor between the two inverses is the residue `x · (1/x)` leaves. -/
theorem pointInv_factor_is_residue (x : T) :
    (pointInv (ofRatio x)).q = scale (x.p * x.q) (T.reciprocal x) ∧
      x * T.reciprocal x = T.«1» + residue (x.p * x.q) :=
  ⟨by rw [pointInv_ofRatio], times_reciprocal_residue x⟩

end T2
