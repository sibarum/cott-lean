import CottLean.Nested.Point
import CottLean.T.Norm

/-!
# Every quadratic ring, read as a point over ratios

`Point` reads `T2(A, B)` as the complex number `B + A·i` and gives it the exact inverse. This file does
the same for every product in `Quadratic`'s family: `T2(A, B)` is `B + A·ω` with `ω² = a + b·ω`, and its
coordinates are ratios.

Write `A = T(u, v)` and `B = T(s, t)`, the point `s/t + (u/v)·ω`. Everything is over the common
denominator, so the formulas are in integers.

```
qmul:   T2(A₁,B₁) · T2(A₂,B₂)
          = T2( T(u₁s₂v₂t₁ + u₂s₁v₁t₂ + b·u₁u₂t₁t₂,  v₁v₂t₁t₂),
                T(s₁s₂v₁v₂ + a·u₁u₂t₁t₂,           v₁v₂t₁t₂) )
qnorm:  M = s²v² + b·uvst − a·u²t²
qinv:   1 / T2(T(u,v), T(s,t)) = T2( T(−u·v²·t², v·M),  T((sv + but)·v·t², t·M) )
```

`M` is the ring's norm `B² + b·AB − a·A²` with the denominators cleared, `v²t²` times it. The inverse is
the conjugate `(B + b·A) − A·ω` over the norm.

* `qmul_gaussian`, `qinv_gaussian`: at `ω² = −1` these are `Point`'s `otimes` and `pointInv`, coordinate
  for coordinate.
* `qmul_ofPoint`: on integer points `qmul` is the flat `qtimes`, exactly.
* `qmul_qinv`: `z · (1/z)` is `1` with both coordinates scaled by one integer `k = (v·t·M)²`, the
  `ω` part the residue `T(0, k)`. That is `x · (1/x) = T(pq, pq)` one level down, for every ring of the
  family.
* `qinv_residue_eq_zero_iff`: `k` is `0` exactly when a coordinate has a zero denominator or the norm `M`
  is zero.
* `qinv_ofPoint_collapses_iff`: on an integer point `M` is the flat norm, so the inverse collapses
  exactly where the flat product cannot be undone (`T.recoverable_iff_norm`). Today's `Point` result,
  where the complex inverse collapses only at `0ω`, is the case `ω² = −1`. At `ω² = 1`, the split-complex
  product, it collapses on the light lines; at `ω² = 0`, the dual numbers, wherever `q = 0`.
* `qval_qmul`, `qval_qinv`: read into Mathlib's `QuadraticAlgebra ℚ a b`, `qmul` is its product and
  `qinv` is the inverse wherever the denominators and the norm are not zero.
-/

open T

namespace T2

variable (a b : ℤ)

/-! ## The product, the norm and the inverse -/

/-- `(B₁ + A₁ω)(B₂ + A₂ω)` with `ω² = a + b·ω`, over the common denominator. -/
def qmul (x y : T2) : T2 :=
  ⟨⟨x.p.p * y.q.p * y.p.q * x.q.q + y.p.p * x.q.p * x.p.q * y.q.q + b * x.p.p * y.p.p * x.q.q * y.q.q,
      x.p.q * y.p.q * x.q.q * y.q.q⟩,
    ⟨x.q.p * y.q.p * x.p.q * y.p.q + a * x.p.p * y.p.p * x.q.q * y.q.q,
      x.p.q * y.p.q * x.q.q * y.q.q⟩⟩

/-- `M = s²v² + b·uvst − a·u²t²`: the norm `B² + b·AB − a·A²`, times `v²t²`. -/
def qnorm (x : T2) : ℤ :=
  x.q.p ^ 2 * x.p.q ^ 2 + b * x.p.p * x.p.q * x.q.p * x.q.q - a * x.p.p ^ 2 * x.q.q ^ 2

/-- The inverse: the conjugate `(B + b·A) − A·ω` over the norm. -/
def qinv (x : T2) : T2 :=
  ⟨⟨-x.p.p * x.p.q ^ 2 * x.q.q ^ 2, x.p.q * qnorm a b x⟩,
    ⟨(x.q.p * x.p.q + b * x.p.p * x.q.q) * x.p.q * x.q.q ^ 2, x.q.q * qnorm a b x⟩⟩

/-! ## The complex case is `Point` -/

theorem qmul_gaussian (x y : T2) : qmul (-1) 0 x y = otimes x y := by
  ext <;> simp [qmul, otimes] <;> ring

theorem qinv_gaussian (x : T2) : qinv (-1) 0 x = pointInv x := by
  obtain ⟨⟨u, v⟩, ⟨s, t⟩⟩ := x
  rw [pointInv_eq]
  ext <;> simp only [qinv, qnorm, lenSq] <;> ring

/-! ## The flat product inside it -/

theorem qmul_ofPoint (x y : T) : qmul a b (ofPoint x) (ofPoint y) = ofPoint (qtimes a b x y) := by
  ext <;> simp [qmul, ofPoint, ratioInt, qtimes]

/-- On an integer point the norm is the flat norm `q² + b·pq − a·p²`. -/
theorem qnorm_ofPoint (z : T) : qnorm a b (ofPoint z) = (toQuad a b z).norm := by
  rw [norm_toQuad]; simp [qnorm, ofPoint, ratioInt]

/-! ## Back to `1`, up to one integer -/

/-- `z · (1/z) = T2(T(0, k), T(k, k))` with `k = (v·t·M)²`. -/
theorem qmul_qinv (x : T2) :
    qmul a b x (qinv a b x) =
      ⟨⟨0, (x.p.q * x.q.q * qnorm a b x) ^ 2⟩,
        ⟨(x.p.q * x.q.q * qnorm a b x) ^ 2, (x.p.q * x.q.q * qnorm a b x) ^ 2⟩⟩ := by
  ext <;> simp [qmul, qinv, qnorm] <;> ring

/-- The residue vanishes exactly when a coordinate has a zero denominator or the norm is zero. -/
theorem qinv_residue_eq_zero_iff (x : T2) :
    x.p.q * x.q.q * qnorm a b x = 0 ↔ x.p.q = 0 ∨ x.q.q = 0 ∨ qnorm a b x = 0 := by
  simp only [mul_eq_zero]; tauto

/-- On an integer point, the inverse collapses exactly where the flat product cannot be undone. -/
theorem qinv_ofPoint_collapses_iff (z : T) :
    (ofPoint z).p.q * (ofPoint z).q.q * qnorm a b (ofPoint z) = 0 ↔ ¬ Recoverable (qtimes a b) z := by
  rw [recoverable_iff_norm (qtimes a b) (toQuad a b) (toQuad_qtimes a b) z, ← qnorm_ofPoint]
  simp [ofPoint, ratioInt]

/-! ## The values -/

/-- A flat pair read as its ratio, in ℚ. -/
def rq (x : T) : ℚ := x.p / x.q

/-- `T2(A, B)` as `B + A·ω` in `QuadraticAlgebra ℚ a b`. -/
def qval (x : T2) : QuadraticAlgebra ℚ a b := ⟨rq x.q, rq x.p⟩

theorem qval_qmul {x y : T2} (hx : Finite x) (hy : Finite y) :
    qval a b (qmul a b x y) = qval a b x * qval a b y := by
  obtain ⟨hxp, hxq⟩ := hx
  obtain ⟨hyp, hyq⟩ := hy
  have h1 : (x.p.q : ℚ) ≠ 0 := by exact_mod_cast hxp
  have h2 : (x.q.q : ℚ) ≠ 0 := by exact_mod_cast hxq
  have h3 : (y.p.q : ℚ) ≠ 0 := by exact_mod_cast hyp
  have h4 : (y.q.q : ℚ) ≠ 0 := by exact_mod_cast hyq
  ext
  · simp [qval, qmul, rq]; field_simp
  · simp [qval, qmul, rq]; field_simp; ring

/-- Where the denominators and the norm are not zero, `qinv` is the inverse. -/
theorem qval_qinv {x : T2} (hx : Finite x) (hM : qnorm a b x ≠ 0) :
    qval a b x * qval a b (qinv a b x) = 1 := by
  have hi : Finite (qinv a b x) := ⟨mul_ne_zero hx.1 hM, mul_ne_zero hx.2 hM⟩
  rw [← qval_qmul a b hx hi, qmul_qinv]
  have hk : ((x.p.q * x.q.q * qnorm a b x) ^ 2 : ℚ) ≠ 0 := by
    have := mul_ne_zero (mul_ne_zero hx.1 hx.2) hM
    exact_mod_cast pow_ne_zero 2 this
  ext
  · simp only [qval, rq]; push_cast; rw [QuadraticAlgebra.re_one]; exact div_self hk
  · simp only [qval, rq]; push_cast; rw [QuadraticAlgebra.im_one]; simp

end T2
