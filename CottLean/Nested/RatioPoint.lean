import CottLean.T.Over
import CottLean.Nested.Point

/-!
# `T(C, C)`: a ratio of two complex numbers

`Point` builds ℚ(i) as a complex number with ratio coordinates, `C(T, T)`. This file builds it the
other way round, as a ratio of two Gaussian integers, `T(C, C) = z / w`: `TOver` over `ℤ[i]`, under
`T`'s own formulas. The two hold the same values and pay for division in opposite places.

| | `C(T, T)` (`Point`) | `T(C, C)` (here) |
|---|---|---|
| `+` | each coordinate, as a ratio | cross-multiplied, `T(z₁w₂ + z₂w₁, w₁w₂)` |
| `·` | the product of the points | each coordinate, `T(z₁z₂, w₁w₂)` |
| `1/x` | the conjugate over the norm | a swap, `T(w, z)` |
| `x · (1/x)` | `1` scaled by `(v·t·M)²` | `1` scaled by `z·w` |
| that residue is zero | at a zero denominator, or at `0` | at `z = 0` or `w = 0` |

## The values

`val` reads `T(z, w)` as `z / w` in ℂ. `·` and the reciprocal are the complex product and inverse for
every pair (`val_times`, `val_reciprocal`), and `+` is the complex sum where both denominators are non-zero
(`val_plus`).

## The two maps

* `rationalize : T(C, C) → C(T, T)` multiplies through by the conjugate of the denominator:
  `z / w = (z·w̄) / N(w)`, so the real and imaginary parts of `z·w̄`, each over `N(w)`.
* `combine : C(T, T) → T(C, C)` puts both coordinates over one denominator:
  `c/d + (a/b)·i = (cb + ad·i) / (bd)`.

Both keep the value wherever it is finite (`val_rationalize`, `val_combine`). Neither is the identity on
coordinates. Each round trip scales the coordinates by a residue:

* `combine_rationalize`: back in `T(C, C)`, both `z` and `w` are multiplied by `w̄·N(w)`.
* `rationalize_combine`: back in `C(T, T)`, the imaginary coordinate is scaled by `b·d²` and the real one
  by `b²·d`.

And the two inverses agree through the map: rationalizing the swap is the conjugate-over-norm inverse of
the rationalized point (`val_rationalize_reciprocal`).

## Where each keeps its infinities

The two have different points at infinity, and each map loses what the other keeps there.

* `T(C, C)` has a point at infinity for every direction: `T(z, 0)` for any `z`, unreduced. `rationalize`
  sends every one of them to `T2(0ω, 0ω)` (`rationalize_infinite`).
* `C(T, T)` has an infinity in each coordinate separately, and keeps the other coordinate finite beside it.
  `combine` sends exactly those points to a zero denominator (`combine_q_eq_zero_iff`), and an infinite
  imaginary part drops the real part (`combine_imag_infinite`).
-/

open T Complex

/-- `T(C, C)`: a ratio of two Gaussian integers, `z / w`. -/
abbrev TC := TOver GaussianInt

namespace TC

/-! ## The values -/

/-- `T(z, w)` as `z / w` in ℂ. -/
noncomputable def val (x : TC) : ℂ := GaussianInt.toComplex x.p / GaussianInt.toComplex x.q

theorem val_times (x y : TC) : val (x * y) = val x * val y := by
  simp only [val, TOver.mul_p, TOver.mul_q, map_mul, div_mul_div_comm]

theorem val_reciprocal (x : TC) : val (TOver.reciprocal x) = (val x)⁻¹ := by
  simp [val, inv_div]

theorem toComplex_re (w : GaussianInt) : (GaussianInt.toComplex w).re = w.re := by
  rw [show GaussianInt.toComplex w = ⟨w.re, w.im⟩ from GaussianInt.toComplex_def₂ w]

theorem toComplex_im (w : GaussianInt) : (GaussianInt.toComplex w).im = w.im := by
  rw [show GaussianInt.toComplex w = ⟨w.re, w.im⟩ from GaussianInt.toComplex_def₂ w]

theorem toComplex_ne_zero {w : GaussianInt} (hw : w ≠ 0) : GaussianInt.toComplex w ≠ 0 := by
  intro h; exact hw (GaussianInt.toComplex_eq_zero.mp h)

theorem val_plus {x y : TC} (hx : x.q ≠ 0) (hy : y.q ≠ 0) : val (x + y) = val x + val y := by
  simp only [val, TOver.add_p, TOver.add_q, map_add, map_mul]
  rw [div_add_div _ _ (toComplex_ne_zero hx) (toComplex_ne_zero hy)]; ring

/-! ## The residue of the reciprocal -/

/-- `x · (1/x) = T(zw, zw)`, and that residue is zero exactly at `z = 0` or `w = 0`. -/
theorem times_reciprocal_residue (x : TC) :
    x * TOver.reciprocal x = ⟨x.p * x.q, x.p * x.q⟩ ∧ (x.p * x.q = 0 ↔ x.p = 0 ∨ x.q = 0) :=
  ⟨TOver.times_reciprocal_self x, TOver.residue_eq_zero_iff x⟩

/-! ## The two maps -/

/-- The norm of a Gaussian integer, `re² + im²`. -/
def nrm (w : GaussianInt) : ℤ := w.re ^ 2 + w.im ^ 2

/-- `z / w = (z·w̄) / N(w)`: the real and imaginary parts, each over the norm. -/
def rationalize (x : TC) : T2 :=
  ⟨⟨(x.p * star x.q).im, nrm x.q⟩, ⟨(x.p * star x.q).re, nrm x.q⟩⟩

/-- `c/d + (a/b)·i = (cb + ad·i) / (bd)`. -/
def combine (X : T2) : TC := ⟨⟨X.q.p * X.p.q, X.p.p * X.q.q⟩, ⟨X.p.q * X.q.q, 0⟩⟩

theorem nrm_ne_zero {w : GaussianInt} (hw : w ≠ 0) : (nrm w : ℝ) ≠ 0 := by
  intro h
  have h' : w.re ^ 2 + w.im ^ 2 = 0 := by exact_mod_cast h
  have hr : w.re = 0 := by nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  have hi : w.im = 0 := by nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  exact hw (Zsqrtd.ext hr hi)

theorem val_rationalize {x : TC} (hx : x.q ≠ 0) : T2.val (rationalize x) = val x := by
  have hn := nrm_ne_zero hx
  simp only [nrm] at hn
  apply Complex.ext
  · simp [-GaussianInt.intCast_re, -GaussianInt.intCast_im, toComplex_re, toComplex_im, T2.val, T2.rv,
      val, Complex.div_re, Complex.normSq_apply, rationalize, nrm, Zsqrtd.re_mul, Zsqrtd.im_mul]
    field_simp
  · simp [-GaussianInt.intCast_re, -GaussianInt.intCast_im, toComplex_re, toComplex_im, T2.val, T2.rv,
      val, Complex.div_im, Complex.normSq_apply, rationalize, nrm, Zsqrtd.re_mul, Zsqrtd.im_mul]
    field_simp
    ring

theorem val_combine {X : T2} (hX : T2.Finite X) : val (combine X) = T2.val X := by
  obtain ⟨hb, hd⟩ := hX
  have hb' : (X.p.q : ℝ) ≠ 0 := by exact_mod_cast hb
  have hd' : (X.q.q : ℝ) ≠ 0 := by exact_mod_cast hd
  apply Complex.ext <;>
    simp [-GaussianInt.intCast_re, -GaussianInt.intCast_im, toComplex_re, toComplex_im, T2.val, T2.rv,
      val, Complex.div_re, Complex.div_im, Complex.normSq_apply, combine] <;>
    field_simp

/-! ## The round trips -/

/-- Back in `T(C, C)`, both coordinates are multiplied by `w̄·N(w)`. -/
theorem combine_rationalize (x : TC) :
    combine (rationalize x) =
      ⟨x.p * (star x.q * (x.q * star x.q)), x.q * (star x.q * (x.q * star x.q))⟩ := by
  ext <;> simp [combine, rationalize, nrm, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-- Back in `C(T, T)`, the imaginary coordinate is scaled by `b·d²` and the real one by `b²·d`. -/
theorem rationalize_combine (X : T2) :
    rationalize (combine X) =
      ⟨scale (X.p.q * X.q.q ^ 2) X.p, scale (X.p.q ^ 2 * X.q.q) X.q⟩ := by
  ext <;> simp [combine, rationalize, nrm, scale, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-! ## The inverses agree through the map -/

/-- Rationalizing the swap gives the conjugate-over-norm inverse, as a value. -/
theorem val_rationalize_reciprocal {x : TC} (hp : x.p ≠ 0) (hq : x.q ≠ 0) :
    T2.val (rationalize (TOver.reciprocal x)) = T2.val (T2.pointInv (rationalize x)) := by
  have hfin : T2.Finite (rationalize x) := by
    constructor <;> exact_mod_cast nrm_ne_zero hq
  rw [val_rationalize (x := TOver.reciprocal x) hp, T2.val_pointInv hfin, val_rationalize hq,
    val_reciprocal]

/-! ## The infinities -/

/-- Every point at infinity of `T(C, C)`, whatever its direction, goes to `T2(0ω, 0ω)`. -/
theorem rationalize_infinite (z : GaussianInt) : rationalize ⟨z, 0⟩ = ⟨T.«0ω», T.«0ω»⟩ := by
  ext <;> simp [rationalize, nrm, T.«0ω»]

/-- `combine` gives a zero denominator exactly at the points with an infinite coordinate. -/
theorem combine_q_eq_zero_iff (X : T2) : (combine X).q = 0 ↔ X.p.q = 0 ∨ X.q.q = 0 := by
  rw [← mul_eq_zero]
  constructor
  · intro h; exact congrArg Zsqrtd.re h
  · intro h; exact Zsqrtd.ext (by simp [combine, h]) (by simp [combine])

/-- An infinite imaginary part drops the real part: `c/d + (a/0)·i ↦ (a·d·i) / 0`. -/
theorem combine_imag_infinite (a c d : ℤ) :
    combine ⟨⟨a, 0⟩, ⟨c, d⟩⟩ = ⟨⟨0, a * d⟩, 0⟩ := by
  ext <;> simp [combine]

end TC
