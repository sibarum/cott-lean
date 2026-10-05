import CottLean.Nested.Bicomplex
import CottLean.Nested.RatioPoint

/-!
# `C(T(C, C), T(C, C))`: the bicomplex point over ratios of Gaussian integers

`C(C, C)` (`Bicomplex`) has no exact inverse: `1/(B + A·j) = (B − A·j) / (B² + A²)`, and the norm
`B² + A²` is a Gaussian integer with nowhere to be kept. `Point` met the same problem one corner over and
solved it by giving each coordinate its own denominator. This file does that here. Each coordinate is a
ratio of Gaussian integers, `T(C, C)` (`RatioPoint`), and the pair is read as the point `B + A·j`.

```
C(A₁,B₁) ⊕ C(A₂,B₂) = C(A₁ + A₂, B₁ + B₂)
C(A₁,B₁) ⊗ C(A₂,B₂) = C(A₁·B₂ + A₂·B₁, B₁·B₂ − A₁·A₂)
inv C(A, B)         = C(−A / N, B / N),   N = A·A + B·B
```

These are `Point`'s formulas word for word, with `T(C, C)`'s `+`, `·` and `−` in place of `T`'s.

## The inverse in Gaussian integers

Write `A = T(u, v)` and `B = T(s, t)`, the point `s/t + (u/v)·j` with `u, v, s, t ∈ ℤ[i]`, and
`D = u²t² + v²s²`. Then

```
inv C(T(u,v), T(s,t)) = C( T(−u·v²·t², v·D),  T(s·v²·t², t·D) )
```

(`inv_eq`), `Point`'s integer formula with Gaussian integers for integers.

* `otimes_inv`: `z ⊗ (1/z)` is `1` with both coordinates scaled by one Gaussian integer `k = (v·t·D)²`,
  the `j` part the residue `T(0, k)`. The third instance of `x · (1/x) = T(pq, pq)`.
* `inv_residue_eq_zero_iff`: `k` is zero exactly at a zero denominator or `D = 0`.
* `den_eq_zero_iff`: and `D = 0` exactly on the light lines, `v·s = ±i·u·t`, that is `B = ±i·A`. In
  `Point` the matching `D` is a sum of two integer squares and is zero only at the zero point. Here it
  factors, `D = (vs + i·ut)(vs − i·ut)` (`den_eq_mul`), and is zero on two whole lines.

## The corners inside it

* `ofCC`: a bicomplex integer `C(A, B)` is `C(A/1, B/1)`. `⊕` and `⊗` carry across exactly
  (`ofCC_oplus`, `ofCC_otimes`). Its inverse is `(B − A·j) / (B² + A²)` (`inv_ofCC`), the inverse
  `Bicomplex` could not write down, and `D` is `Bicomplex`'s norm (`den_ofCC`). So the inverse collapses
  exactly where `C(C, C)`'s `⊗` cannot be undone (`inv_ofCC_collapses_iff`).
* `ofT2`: a point of `C(T, T)` is the same point with real ratio coordinates. `⊕` and `⊗` carry across
  exactly (`ofT2_oplus`, `ofT2_otimes`), and so does the inverse: `inv (ofT2 X) = ofT2 (pointInv X)`
  (`inv_ofT2`). `Point`'s `i` is this file's `j`.
* `ofTC`: a ratio of Gaussian integers is the real point `C(0, x)`. Its inverse is `T(C, C)`'s own swap,
  scaled by its residue `z·w` (`inv_ofTC`), the same split `Point` found between its two inverses.
* `zeroDivisor_inv`: the zero divisor `1 + i·j` has the inverse `C(−i/0, 1/0)`, both coordinates
  infinite, and multiplying back gives `C(0/0, 0/0)` (`otimes_zeroDivisor_inv`).

## The values

`val` reads `C(A, B)` as `B + A·j` in `QuadraticAlgebra ℂ (−1) 0`, the bicomplex numbers. Where both
denominators are non-zero (`Finite`), `⊕` and `⊗` are their sum and product (`val_oplus`, `val_otimes`),
and where also `D ≠ 0`, `inv` is the inverse (`val_inv`).

The collapse on the light lines is not a defect of the encoding. A finite point is a unit of the
bicomplex numbers exactly when `D ≠ 0` (`isUnit_val_iff`). So the inverse exists wherever the value has
one, and on the light lines the value has none: it is a zero divisor, `z · conj z = 0`
(`val_otimes_conj`).
-/

open T

/-- `C(T(C, C), T(C, C))`: the point `B + A·j`, each coordinate a ratio of Gaussian integers. -/
@[ext]
structure CTC where
  /-- The `j` coordinate. -/
  p : TC
  /-- The real coordinate. -/
  q : TC

namespace CTC

open CC (gi gi_mul_gi)

/-! ## The operations -/

/-- The sum of the points: each coordinate added as a ratio. -/
def oplus (x y : CTC) : CTC := ⟨x.p + y.p, x.q + y.q⟩

/-- The product of the points, with `j² = −1`. -/
def otimes (x y : CTC) : CTC := ⟨x.p * y.q + y.p * x.q, x.q * y.q + -(x.p * y.p)⟩

/-- `B + A·j ↦ B − A·j`. -/
def conj (x : CTC) : CTC := ⟨-x.p, x.q⟩

/-- `A·A + B·B`, the norm of the point, as a ratio of Gaussian integers. -/
def nrm (x : CTC) : TC := x.p * x.p + x.q * x.q

/-- The inverse: `(B − A·j) / N`. -/
def inv (x : CTC) : CTC := ⟨-x.p * TOver.reciprocal (nrm x), x.q * TOver.reciprocal (nrm x)⟩

/-! ## The inverse in Gaussian integers -/

/-- `D = u²t² + v²s²`: the norm `(s/t)² + (u/v)²` with the denominators cleared. -/
def den (x : CTC) : GaussianInt := x.p.p ^ 2 * x.q.q ^ 2 + x.p.q ^ 2 * x.q.p ^ 2

theorem inv_eq (x : CTC) :
    inv x = ⟨⟨-x.p.p * x.p.q ^ 2 * x.q.q ^ 2, x.p.q * den x⟩,
      ⟨x.q.p * x.p.q ^ 2 * x.q.q ^ 2, x.q.q * den x⟩⟩ := by
  ext : 2 <;> simp only [inv, nrm, den, TOver.mul_p, TOver.mul_q, TOver.add_p, TOver.add_q, TOver.neg_p,
    TOver.neg_q, TOver.reciprocal_p, TOver.reciprocal_q] <;> ring

/-- `z ⊗ (1/z) = C(T(0, k), T(k, k))` with `k = (v·t·D)²`. -/
theorem otimes_inv (x : CTC) :
    otimes x (inv x) =
      ⟨⟨0, (x.p.q * x.q.q * den x) ^ 2⟩, ⟨(x.p.q * x.q.q * den x) ^ 2, (x.p.q * x.q.q * den x) ^ 2⟩⟩ := by
  rw [inv_eq]; ext : 2 <;> simp [otimes, den] <;> ring

/-- The residue vanishes exactly at a zero denominator or `D = 0`. -/
theorem inv_residue_eq_zero_iff (x : CTC) :
    x.p.q * x.q.q * den x = 0 ↔ x.p.q = 0 ∨ x.q.q = 0 ∨ den x = 0 := by
  simp only [mul_eq_zero]; tauto

/-- `D = (vs + i·ut)(vs − i·ut)`. -/
theorem den_eq_mul (x : CTC) :
    den x = (x.p.q * x.q.p + gi * (x.p.p * x.q.q)) * (x.p.q * x.q.p - gi * (x.p.p * x.q.q)) := by
  unfold den; linear_combination (x.p.p * x.q.q) ^ 2 * gi_mul_gi

/-- `D = 0` exactly on the light lines `v·s = ±i·u·t`. -/
theorem den_eq_zero_iff (x : CTC) :
    den x = 0 ↔ x.p.q * x.q.p = -(gi * (x.p.p * x.q.q)) ∨ x.p.q * x.q.p = gi * (x.p.p * x.q.q) := by
  rw [den_eq_mul, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero]

/-! ## The bicomplex integers inside it -/

/-- A bicomplex integer `C(A, B)`, with each coordinate over `1`. -/
def ofCC (z : CC) : CTC := ⟨⟨z.p, 1⟩, ⟨z.q, 1⟩⟩

theorem ofCC_injective : Function.Injective ofCC := fun x y h => by
  have h1 := congrArg (fun w : CTC => w.p.p) h
  have h2 := congrArg (fun w : CTC => w.q.p) h
  exact CC.ext h1 h2

theorem ofCC_oplus (x y : CC) : ofCC (CC.oplus x y) = oplus (ofCC x) (ofCC y) := by
  ext : 2 <;> simp [ofCC, oplus, CC.oplus]

theorem ofCC_otimes (x y : CC) : ofCC (CC.otimes x y) = otimes (ofCC x) (ofCC y) := by
  ext : 2 <;> simp [ofCC, otimes, CC.otimes]; ring

/-- On a bicomplex integer, `D` is `Bicomplex`'s norm `B² + A²`. -/
theorem den_ofCC (z : CC) : den (ofCC z) = CC.nrm z := by
  simp [den, ofCC, CC.nrm]; ring

/-- The inverse `Bicomplex` could not write down: `(B − A·j) / (B² + A²)`. -/
theorem inv_ofCC (z : CC) : inv (ofCC z) = ⟨⟨-z.p, CC.nrm z⟩, ⟨z.q, CC.nrm z⟩⟩ := by
  rw [inv_eq, den_ofCC]; ext : 2 <;> simp [ofCC]

/-- On a bicomplex integer, the inverse collapses exactly where `⊗` cannot be undone. -/
theorem inv_ofCC_collapses_iff (z : CC) :
    (ofCC z).p.q * (ofCC z).q.q * den (ofCC z) = 0 ↔
      ¬ ∀ x x' : CC, CC.otimes x z = CC.otimes x' z → x = x' := by
  rw [CC.otimes_cancel_iff, den_ofCC, not_not]
  simp [ofCC]

/-- The zero divisor `1 + i·j`. -/
def zeroDivisor : CTC := ofCC ⟨gi, 1⟩

/-- Its inverse has both coordinates infinite: `C(−i/0, 1/0)`. -/
theorem zeroDivisor_inv : inv zeroDivisor = ⟨⟨-gi, 0⟩, ⟨1, 0⟩⟩ := by
  rw [zeroDivisor, inv_ofCC]
  have h : CC.nrm ⟨gi, 1⟩ = 0 := by decide
  rw [h]

/-- And multiplying back gives `C(0/0, 0/0)`. -/
theorem otimes_zeroDivisor_inv : otimes zeroDivisor (inv zeroDivisor) = ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ := by
  rw [otimes_inv]
  have h : den zeroDivisor = 0 := by rw [zeroDivisor, den_ofCC]; decide
  simp [h]

/-! ## `C(T, T)` inside it -/

/-- A point of `C(T, T)`, its ratio coordinates read in the Gaussian integers. -/
def ofT2 (X : T2) : CTC := ⟨⟨X.p.p, X.p.q⟩, ⟨X.q.p, X.q.q⟩⟩

theorem ofT2_injective : Function.Injective ofT2 := fun X Y h => by
  have h1 := congrArg (fun w : CTC => w.p.p) h
  have h2 := congrArg (fun w : CTC => w.p.q) h
  have h3 := congrArg (fun w : CTC => w.q.p) h
  have h4 := congrArg (fun w : CTC => w.q.q) h
  simp only [ofT2, Int.cast_inj] at h1 h2 h3 h4
  exact T2.ext (T.ext h1 h2) (T.ext h3 h4)

theorem ofT2_oplus (X Y : T2) : ofT2 (T2.oplus X Y) = oplus (ofT2 X) (ofT2 Y) := by
  ext : 2 <;> simp [ofT2, oplus, T2.oplus, T.add_def]

theorem ofT2_otimes (X Y : T2) : ofT2 (T2.otimes X Y) = otimes (ofT2 X) (ofT2 Y) := by
  ext : 2 <;> simp [ofT2, otimes, T2.otimes, T.add_def, T.mul_def, T.neg_def]

/-- The inverse restricts to `Point`'s, coordinate for coordinate. -/
theorem inv_ofT2 (X : T2) : inv (ofT2 X) = ofT2 (T2.pointInv X) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := X
  rw [inv_eq, T2.pointInv_eq]
  ext : 2 <;> simp [ofT2, den, T2.lenSq]

/-! ## `T(C, C)` inside it -/

/-- A ratio of Gaussian integers, as the real point `C(0, x)`. -/
def ofTC (x : TC) : CTC := ⟨⟨0, 1⟩, x⟩

/-- The inverse of a real `z / w`: the swap `T(w, z)` scaled by `z·w`, with the `j` part `T(0, z²)`. -/
theorem inv_ofTC (x : TC) :
    inv (ofTC x) = ⟨⟨0, x.p ^ 2⟩, ⟨x.p * x.q * (TOver.reciprocal x).p,
      x.p * x.q * (TOver.reciprocal x).q⟩⟩ := by
  rw [inv_eq]; ext : 2 <;> simp [ofTC, den] <;> ring

/-! ## The values -/

/-- `C(A, B)` as the bicomplex number `B + A·j`. -/
noncomputable def val (x : CTC) : QuadraticAlgebra ℂ (-1) 0 := ⟨TC.val x.q, TC.val x.p⟩

/-- Both coordinates have non-zero denominators. -/
def Finite (x : CTC) : Prop := x.p.q ≠ 0 ∧ x.q.q ≠ 0

theorem val_neg (x : TC) : TC.val (-x) = -TC.val x := by
  simp [TC.val, neg_div]

theorem val_oplus {x y : CTC} (hx : Finite x) (hy : Finite y) : val (oplus x y) = val x + val y := by
  ext
  · exact TC.val_plus hx.2 hy.2
  · exact TC.val_plus hx.1 hy.1

theorem val_otimes {x y : CTC} (hx : Finite x) (hy : Finite y) : val (otimes x y) = val x * val y := by
  obtain ⟨hxp, hxq⟩ := hx
  obtain ⟨hyp, hyq⟩ := hy
  ext
  · simp only [val, otimes, QuadraticAlgebra.re_mul]
    rw [TC.val_plus (by simp [hxq, hyq]) (by simp [hxp, hyp]), val_neg, TC.val_times, TC.val_times]
    ring
  · simp only [val, otimes, QuadraticAlgebra.im_mul]
    rw [TC.val_plus (by simp [hxp, hyq]) (by simp [hyp, hxq]), TC.val_times, TC.val_times]
    ring

/-- Where the denominators and `D` are not zero, `inv` is the inverse. -/
theorem val_inv {x : CTC} (hx : Finite x) (hD : den x ≠ 0) : val x * val (inv x) = 1 := by
  have hi : Finite (inv x) := by
    rw [inv_eq]; exact ⟨mul_ne_zero hx.1 hD, mul_ne_zero hx.2 hD⟩
  rw [← val_otimes hx hi, otimes_inv]
  have hk : GaussianInt.toComplex ((x.p.q * x.q.q * den x) ^ 2) ≠ 0 :=
    TC.toComplex_ne_zero (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hx.1 hx.2) hD))
  ext
  · simp only [val, TC.val, QuadraticAlgebra.re_one]; exact div_self hk
  · simp [val, TC.val, QuadraticAlgebra.im_one]

/-- `z ⊗ conj z` leaves `D` in the real numerator and `0` in the `j` numerator. -/
theorem otimes_conj (x : CTC) :
    (otimes x (conj x)).p.p = 0 ∧ (otimes x (conj x)).q.p = den x := by
  exact ⟨by simp [otimes, conj], by simp [otimes, conj, den]; ring⟩

/-- On the light lines a finite point is a zero divisor: `z · conj z = 0`. -/
theorem val_otimes_conj {x : CTC} (hx : Finite x) (hD : den x = 0) : val x * val (conj x) = 0 := by
  have hc : Finite (conj x) := hx
  rw [← val_otimes hx hc]
  obtain ⟨h1, h2⟩ := otimes_conj x
  ext
  · simp [val, TC.val, h2, hD]
  · simp [val, TC.val, h1]

/-- A finite point is a unit of the bicomplex numbers exactly when `D ≠ 0`. -/
theorem isUnit_val_iff {x : CTC} (hx : Finite x) : IsUnit (val x) ↔ den x ≠ 0 := by
  constructor
  · intro hu hD
    have h0 := val_otimes_conj hx hD
    have hc : val (conj x) = 0 := (hu.mul_right_eq_zero).mp h0
    have hv : val x = 0 := by
      ext
      · have := congrArg QuadraticAlgebra.re hc; simpa [val, conj] using this
      · have := congrArg QuadraticAlgebra.im hc
        simp only [val, conj, val_neg, QuadraticAlgebra.im_zero, neg_eq_zero] at this
        simpa [val] using this
    rw [hv] at hu
    exact not_isUnit_zero hu
  · intro hD
    exact ⟨⟨val x, val (inv x), val_inv hx hD, by rw [mul_comm]; exact val_inv hx hD⟩, rfl⟩

end CTC
